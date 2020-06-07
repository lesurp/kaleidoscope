use llvm_sys;

use crate::parser::{AstNode, FnProto};
use log::debug;
use std::ffi::CString;

pub struct LlvmJit {
    execution: llvm_sys::execution_engine::LLVMExecutionEngineRef,
    fpm: *mut llvm_sys::LLVMPassManager,
}

impl LlvmJit {
    pub unsafe fn new(module: *mut llvm_sys::LLVMModule) -> Self {
        let mut execution = std::ptr::null_mut();
        let mut err = std::ptr::null_mut();
        let ok = llvm_sys::execution_engine::LLVMCreateExecutionEngineForModule(
            &mut execution,
            module,
            &mut err,
        );
        if ok != 0 {
            panic!("{:?}", CString::from_raw(err));
        }
        assert_eq!(ok, 0);

        llvm_sys::execution_engine::LLVMLinkInInterpreter();

        let module_provider = llvm_sys::core::LLVMCreateModuleProviderForExistingModule(module);
        let fpm = llvm_sys::core::LLVMCreateFunctionPassManager(module_provider);

        let target_data = llvm_sys::execution_engine::LLVMGetExecutionEngineTargetData(execution);
        llvm_sys::target::LLVMSetModuleDataLayout(module, target_data);
        llvm_sys::transforms::instcombine::LLVMAddInstructionCombiningPass(fpm);
        llvm_sys::transforms::scalar::LLVMAddReassociatePass(fpm);
        llvm_sys::transforms::scalar::LLVMAddGVNPass(fpm);
        llvm_sys::transforms::scalar::LLVMAddCFGSimplificationPass(fpm);

        llvm_sys::core::LLVMInitializeFunctionPassManager(fpm);

        LlvmJit { execution, fpm }
    }
}

pub struct LlvmStuff {
    context: *mut llvm_sys::LLVMContext,
    builder: *mut llvm_sys::LLVMBuilder,
    module: *mut llvm_sys::LLVMModule,
    variables: std::collections::HashMap<String, *mut llvm_sys::LLVMValue>,
    jit: LlvmJit,
}

impl LlvmStuff {
    pub fn new<S: AsRef<str>>(s: S) -> Self {
        let c = CString::new(s.as_ref().as_bytes()).unwrap();
        let context = unsafe { llvm_sys::core::LLVMContextCreate() };
        assert!(!context.is_null());
        let module =
            unsafe { llvm_sys::core::LLVMModuleCreateWithNameInContext(c.as_ptr(), context) };
        assert!(!module.is_null());
        let builder = unsafe { llvm_sys::core::LLVMCreateBuilderInContext(context) };
        assert!(!builder.is_null());

        let jit = unsafe { LlvmJit::new(module) };
        LlvmStuff {
            context,
            module,
            builder,
            variables: std::collections::HashMap::new(),
            jit,
        }
    }

    unsafe fn create_prototype(&mut self, proto: FnProto) -> *mut llvm_sys::LLVMValue {
        let mut args = vec![llvm_sys::core::LLVMDoubleTypeInContext(self.context); proto.1.len()];
        let fn_proto = llvm_sys::core::LLVMFunctionType(
            llvm_sys::core::LLVMDoubleTypeInContext(self.context),
            args.as_mut_ptr(),
            args.len() as u32,
            0,
        );
        use std::collections::hash_map::Entry;
        let fnc = match self.variables.entry(proto.0) {
            Entry::Occupied(already_existing) => {
                let fnc = *already_existing.get();
                let n_basic_blocks = llvm_sys::core::LLVMCountBasicBlocks(fnc);
                if n_basic_blocks != 0 {
                    panic!("Function {} was already defined", already_existing.key());
                }

                let n_params = llvm_sys::core::LLVMCountParams(fnc);
                if n_params != args.len() as u32 {
                    panic!(
                        "Wrong number of params for {}; expected {}, found {}",
                        already_existing.key(),
                        n_params,
                        args.len()
                    );
                }
                fnc
            }
            Entry::Vacant(not_yet) => {
                let c = CString::new(not_yet.key().as_bytes()).unwrap();
                let fnc = llvm_sys::core::LLVMAddFunction(self.module, c.as_ptr(), fn_proto);
                *not_yet.insert(fnc)
            }
        };
        assert!(!fnc.is_null());

        let mut args_fnc = vec![std::ptr::null_mut(); proto.1.len()];
        llvm_sys::core::LLVMGetParams(fnc, args_fnc.as_mut_ptr());

        for (arg, arg_name) in args_fnc.iter().zip(proto.1.iter()) {
            llvm_sys::core::LLVMSetValueName2(*arg, arg_name.as_ptr() as *const _, arg_name.len());
            self.variables.insert(arg_name.clone(), *arg);
        }

        fnc
    }

    unsafe fn ast_node_to_llvm_impl(&mut self, ast_node: AstNode) -> *mut llvm_sys::LLVMValue {
        debug!("ast_node_to_llvm");
        match ast_node {
            AstNode::Number(val) => {
                debug!("from number");
                let double = llvm_sys::core::LLVMDoubleTypeInContext(self.context);
                llvm_sys::core::LLVMConstReal(double, val)
            }
            AstNode::Binary(op, lhs, rhs) => {
                debug!("from binary");
                let fn_name;
                let builder_fn: unsafe extern "C" fn(_, _, _, _) -> _;
                match op {
                    '+' => {
                        builder_fn = llvm_sys::core::LLVMBuildFAdd;
                        fn_name = "sum\0";
                    }
                    '-' => {
                        builder_fn = llvm_sys::core::LLVMBuildFSub;
                        fn_name = "sub\0";
                    }
                    '*' => {
                        builder_fn = llvm_sys::core::LLVMBuildFMul;
                        fn_name = "mul\0";
                    }
                    '/' => {
                        builder_fn = llvm_sys::core::LLVMBuildFDiv;
                        fn_name = "div\0";
                    }
                    _ => todo!(),
                };

                builder_fn(
                    self.builder,
                    self.ast_node_to_llvm(*lhs),
                    self.ast_node_to_llvm(*rhs),
                    fn_name.as_ptr() as *const _,
                )
            }
            AstNode::FnDef(proto, def) => {
                debug!("from fndef");
                self.variables.clear();
                let fnc = self.create_prototype(proto);

                let bb = llvm_sys::core::LLVMAppendBasicBlockInContext(
                    self.context,
                    fnc,
                    "entry\0".as_ptr() as *const _,
                );
                llvm_sys::core::LLVMPositionBuilderAtEnd(self.builder, bb);

                let ret = self.ast_node_to_llvm(*def);
                llvm_sys::core::LLVMBuildRet(self.builder, ret);
                assert_eq!(
                    llvm_sys::analysis::LLVMVerifyFunction(
                        fnc,
                        llvm_sys::analysis::LLVMVerifierFailureAction::LLVMPrintMessageAction
                    ),
                    0
                );

                llvm_sys::core::LLVMRunFunctionPassManager(self.jit.fpm, fnc);


                fnc
            }
            AstNode::FnDec(proto) => {
                debug!("from fndec");
                self.create_prototype(proto)
            }
            AstNode::Ident(ident) => {
                debug!("from ident");
                *self.variables.get(&ident).expect("NOOO")
            }
            AstNode::Call(fnc, args) => {
                debug!("from call");
                let c = CString::new(fnc.as_bytes()).unwrap();
                let fnc_ptr = llvm_sys::core::LLVMGetNamedFunction(self.module, c.as_ptr());
                if fnc_ptr.is_null() {
                    panic!("Referred function was not defined: {}", fnc);
                }
                let n_params = llvm_sys::core::LLVMCountParams(fnc_ptr);
                if n_params != args.len() as u32 {
                    panic!(
                        "Wrong number of params for {}; expected {}, found {}",
                        fnc,
                        n_params,
                        args.len()
                    );
                }

                assert_eq!(llvm_sys::core::LLVMCountParams(fnc_ptr), args.len() as u32);
                let mut args: Vec<_> = args
                    .into_iter()
                    .map(|arg| self.ast_node_to_llvm(arg))
                    .collect();
                llvm_sys::core::LLVMBuildCall(
                    self.builder,
                    fnc_ptr,
                    args.as_mut_ptr(),
                    args.len() as u32,
                    "call\0".as_ptr() as *const _,
                )
            }
        }
    }

    pub fn ast_node_to_llvm(&mut self, ast_node: AstNode) -> *mut llvm_sys::LLVMValue {
        unsafe { self.ast_node_to_llvm_impl(ast_node) }
    }

    pub fn dump_value(value: *mut llvm_sys::LLVMValue) {
        unsafe { llvm_sys::core::LLVMDumpValue(value) }
    }
}
