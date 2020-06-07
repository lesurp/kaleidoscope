On link failure try:

```bash
export RUSTFLAGS='-C link-args=-lffi'
```

Can't define it in `build.rustflags` in `Cargo.toml`, probably because of
[this](https://doc.rust-lang.org/cargo/reference/config.html):

```
If the --target flag (or build.target) is used, then the flags will only be
passed to the compiler for the target. Things being built for the host, such as
build scripts or proc macros, will not receive the args. Without --target, the
flags will be passed to all compiler invocations (including build scripts and
proc macros) because dependencies are shared. If you have args that you do not
want to pass to build scripts or proc macros and are building for the host, pass
--target with the host triple
```
