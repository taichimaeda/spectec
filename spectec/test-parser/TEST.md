# Parser constructs

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Teps "" "\00"
42
0: end of input expected
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tbyte "\32" "\33" "" "\32\00"
50
0: unexpected input
0: unexpected end of input
1: end of input expected
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Ttext "AÄÜ" "AÄ\c3\9c" "AÄ\c3"
()
()
0: unexpected input
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bseq "\03\04\02"
11
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bseq "\02\04\02"
0: unexpected input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bseq "\03\02\02"
0: unexpected input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bseq "\03\04"
0: unexpected input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bseq "\03\04\02\00"
3: end of input expected
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tseq "ABCD"
()
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tseq "BCDA"
0: unexpected input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tseq "ABCE"
0: unexpected input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tseq "ABC"
0: unexpected input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tseq "ABCDE"
4: end of input expected
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Talt "A"
()
$ ../src/exe-watsup/main.exe test.watsup --parse-string Talt "BC"
()
$ ../src/exe-watsup/main.exe test.watsup --parse-string Talt "D"
()
$ ../src/exe-watsup/main.exe test.watsup --parse-string Talt "ABC"
1: end of input expected
$ ../src/exe-watsup/main.exe test.watsup --parse-string Talt ""
()
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tprod "A"
1
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tprod "BC"
2
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tprod "D"
3
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tprod "ABC"
1: end of input expected
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tprod ""
0
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Brng "\10"
16
$ ../src/exe-watsup/main.exe test.watsup --parse-string Brng "\18"
24
$ ../src/exe-watsup/main.exe test.watsup --parse-string Brng "\20"
32
$ ../src/exe-watsup/main.exe test.watsup --parse-string Brng "\0F"
0: unexpected input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Brng "\21"
0: unexpected input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Brng ""
0: unexpected end of input
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bstar ""
[]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bstar "\01"
[1]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bstar "\01\01\01"
[1 1 1]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bstar "\00"
0: end of input expected
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bstar2 ""
[]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bstar2 "\01"
[1]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bstar2 "\01\01\01"
[1 1 1]
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bstar3 ""
[]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bstar3 "\01"
[1]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bstar3 "\01\01\01"
[1 1 1]
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tstar ""
()
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tstar "AB"
()
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tstar "ABABAB"
()
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tstar "A"
0: end of input expected
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tstar "ABA"
0: end of input expected
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tstar "B"
0: end of input expected
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bplus ""
0: unexpected end of input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bplus "\01"
[1]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bplus "\01\01\01"
[1 1 1]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bplus "\00"
0: unexpected input
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bplus2 ""
0: unexpected end of input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bplus2 "\01"
[1]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bplus2 "\01\01\01"
[1 1 1]
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bplus3 ""
0: unexpected end of input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bplus3 "\01"
[1]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bplus3 "\01\01\01"
[1 1 1]
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tplus ""
0: unexpected end of input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tplus "ABC"
()
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tplus "ABCABCABC"
()
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tplus "BAC"
0: unexpected input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tplus "A"
0: unexpected input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tplus "AB"
0: unexpected input
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bquest ""
?()
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bquest "\01"
?(1)
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bquest "\01\01"
0: end of input expected
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bquest "\00"
0: end of input expected
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bquest2 ""
?()
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bquest2 "\01"
?(1)
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bquest3 ""
?()
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bquest3 "\01"
?(1)
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tquest ""
()
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tquest "ABCD"
()
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tquest "ABCDABCD"
0: end of input expected
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tquest "A"
0: end of input expected
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bnth "\01\01\01\01"
[1 1 1 1]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bnth ""
0: unexpected end of input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bnth "\01"
0: unexpected input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bnth "\01\01\01\01\01"
4: end of input expected
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bnth2 "\01\01\01\01"
[1 1 1 1]
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bnth3 "\01\01\01\01"
[1 1 1 1]
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tnth "ABCABCABC"
()
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tnth ""
0: unexpected end of input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tnth "ABC"
0: unexpected input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tnth "ABCABCABCA"
9: end of input expected
$ ../src/exe-watsup/main.exe test.watsup --parse-string Tnth "ABCABCABCABC"
9: end of input expected
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bvar "\01\03\04\10"
23
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bvar "\01"
0: unexpected input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Bvar "\01\03\04\10\00"
4: end of input expected
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Brec ""
[]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Brec "\01"
[1]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Brec "\01\01\01"
[1 1 1]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Brec "\01\00"
0: end of input expected
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Brec2 ""
[]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Brec2 "\01"
[1]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Brec2 "\01\01\01"
[1 1 1]
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Btest1 "\01\02"
[]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Btest1 "\01\10\12\10\02"
[16 18 16]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Btest1 "\01\10\12\10"
0: unexpected input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Btest1 ""
0: unexpected end of input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Btest1 "\01\10\12\10\02\02"
5: end of input expected
```

```sh
$ ../src/exe-watsup/main.exe test.watsup --parse-string Btest2 "\00"
[]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Btest2 "\11\12\13\00"
[17 18 19]
$ ../src/exe-watsup/main.exe test.watsup --parse-string Btest2 ""
0: unexpected end of input
$ ../src/exe-watsup/main.exe test.watsup --parse-string Btest2 "\00\00"
1: end of input expected
```


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
([], [])
```

```sh
$ ../src/exe-watsup/main.exe ../spec/wasm-3.0/*.watsup --parse-string Bcode "\02\00\0B"
([], [])
```

# Modules

```sh
$ ../src/exe-watsup/main.exe ../spec/wasm-3.0/*.watsup --parse-string Bmagic "\00\61\73\6D"
()
```

```sh
$ ../src/exe-watsup/main.exe ../spec/wasm-3.0/*.watsup --parse-string Bcustomsec "" # "\00\01\00" "\00\07\03boo\01\02\03"
()
()
()
```

```sh
$ ../src/exe-watsup/main.exe ../spec/wasm-3.0/*.watsup --parse-string Bmodule "\00\61\73\6D\01\00\00\00"
MODULE_module
```
