# Types

```sh
$ ../src/exe-watsup/main.exe ../spec/wasm-3.0/*.watsup --parse-string Bnumtype "\7f"
I32_numtype
```

# Values

```sh
$ ../src/exe-watsup/main.exe ../spec/wasm-3.0/*.watsup --parse-string Bu32 "\00" "\80\00" "\80\80\80\80\00" "\80\80\80\80\80\00" "\81\03"
u32(0)
u32(0)
u32(0)
0: unexpected input
u32(385)
```

# Functions

```sh
$ ../src/exe-watsup/main.exe ../spec/wasm-3.0/*.watsup --parse-string Bfunc "\00\0B"
()
```

```sh
$ #../src/exe-watsup/main.exe ../spec/wasm-3.0/*.watsup --parse-string Bcode "\02\00\0B"
()
```

# Modules

```sh
$ #../src/exe-watsup/main.exe ../spec/wasm-3.0/*.watsup --parse-string Bmagic "\00\61\73\6D"
()
```

```sh
$ #../src/exe-watsup/main.exe ../spec/wasm-3.0/*.watsup --parse-string Bcustomsec "\00\00"
()
```

```sh
$ #../src/exe-watsup/main.exe ../spec/wasm-3.0/*.watsup --parse-string Bmodule "\00\61\73\6D\01\00\00\00"
MODULE_module
```
