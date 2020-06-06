#![feature(generators, generator_trait)]

mod lexer;
mod parser;

use lexer::{Lexer, LexingError, Newliner};
use llvm_sys;
use parser::{AstGenerator, AstNode, FnProto, ParsingError};
use std::io::Write;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering::Relaxed;

use log::debug;

struct ReplNewline(AtomicBool);
impl Newliner for ReplNewline {
    fn new_line(&self) {
        self.0.store(true, Relaxed);
    }
}
impl ReplNewline {
    fn new() -> Self {
        ReplNewline(AtomicBool::new(true))
    }

    fn print(&self) {
        if self.0.swap(false, Relaxed) {
            print!(">> ");
            std::io::stdout()
                .flush()
                .expect("I don't deal with stdout-writing problems");
        }
    }
}

struct NewlinerRepl<'a>(&'a ReplNewline);
impl<'a> Newliner for NewlinerRepl<'a> {
    fn new_line(&self) {
        self.0.new_line()
    }
}

struct LlvmStuff {
    context: *mut llvm_sys::LLVMContext,
    builder: *mut llvm_sys::LLVMBuilder,
    module: *mut llvm_sys::LLVMModule,
    variables: std::collections::HashMap<String, *mut llvm_sys::LLVMValue>,
}

impl LlvmStuff {
    fn new<S: AsRef<[u8]>>(s: S) -> Self {
        let context = unsafe { llvm_sys::core::LLVMContextCreate() };
        assert!(!context.is_null());
        let module =
            unsafe { llvm_sys::core::LLVMModuleCreateWithName(s.as_ref().as_ptr() as *const _) };
        assert!(!module.is_null());
        let builder = unsafe { llvm_sys::core::LLVMCreateBuilderInContext(context) };
        assert!(!builder.is_null());
        LlvmStuff {
            context,
            module,
            builder,
            variables: std::collections::HashMap::new(),
        }
    }

    unsafe fn create_prototype(&mut self, proto: FnProto) -> *mut llvm_sys::LLVMValue {
        //proto.
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
                let fnc = llvm_sys::core::LLVMAddFunction(
                    self.module,
                    not_yet.key().as_ptr() as *const _,
                    fn_proto,
                );
                *not_yet.insert(fnc)
            }
        };

        let args_fnc = std::ptr::null_mut();
        llvm_sys::core::LLVMGetParams(fnc, args_fnc);
        if args_fnc.is_null() {
            panic!("DUNNO");
        }
        for (i, arg_name) in proto.1.iter().enumerate() {
            let arg = args_fnc.add(i);
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
                let fn_name = match op {
                    '+' => "sum\0",
                    _ => todo!(),
                };

                llvm_sys::core::LLVMBuildFAdd(
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
                    1
                );

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
                let fnc_ptr =
                    llvm_sys::core::LLVMGetNamedFunction(self.module, fnc.as_ptr() as *const _);
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
                let params = std::ptr::null_mut();
                llvm_sys::core::LLVMGetParams(fnc_ptr, params);
                if params.is_null() {
                    panic!("NOOOOO CLUUUUUE");
                }
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
    fn ast_node_to_llvm(&mut self, ast_node: AstNode) -> *mut llvm_sys::LLVMValue {
        unsafe { self.ast_node_to_llvm_impl(ast_node) }
    }

    fn dump_value(value: *mut llvm_sys::LLVMValue) {
        unsafe { llvm_sys::core::LLVMDumpValue(value) }
    }
}

fn main() {
    env_logger::init();

    let stdin = std::io::stdin();
    let mut stdin = stdin.lock();

    let repl = ReplNewline::new();
    let newliner = NewlinerRepl(&repl);
    let mut lexer = Lexer::with_newliner(&mut stdin, newliner);

    let mut llvm = LlvmStuff::new("kaleidoscope");
    repl.print();
    for ast_node in AstGenerator(&mut lexer) {
        match ast_node {
            Ok(ast) => {
                println!("\t{:?}", ast);
                repl.print();
                let val = llvm.ast_node_to_llvm(ast);
                LlvmStuff::dump_value(val);
            }
            Err(ParsingError::LexingError(LexingError::IoError)) => panic!("Can't deal with that"),
            Err(ParsingError::LexingError(LexingError::IncompleteToken)) => break,

            Err(ParsingError::IncompleteAstError) => continue,
            Err(ParsingError::FatalError(e)) => panic!(
                "Something wrong, so I'm just gonna panic, whatever ({:?}",
                e
            ),
        }
    }
}
