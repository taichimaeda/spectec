# Preview

```sh
$ dune exec ../src/exe-haskell/main.exe -- ../spec/*.watsup -o Test.hs
$ cat Test.hs
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DuplicateRecordFields #-}
module Test where
import Prelude (Bool, String, undefined, Maybe, fromIntegral, (+), (!!))
import Numeric.Natural (Natural)
{-
;; ../spec/1-syntax.watsup:3.1-3.15
syntax n = nat
-}
type N = Natural

{-
;; ../spec/1-syntax.watsup:9.1-9.37
syntax name = text
-}
type Name = String

{-
;; ../spec/1-syntax.watsup:14.1-14.36
syntax byte = nat
-}
type Byte = Natural

{-
;; ../spec/1-syntax.watsup:15.1-15.45
syntax u32 = nat
-}
type U32 = Natural

{-
;; ../spec/1-syntax.watsup:22.1-22.36
syntax idx = nat
-}
type Idx = Natural

{-
;; ../spec/1-syntax.watsup:23.1-23.49
syntax funcidx = idx
-}
type Funcidx = Idx

{-
;; ../spec/1-syntax.watsup:24.1-24.49
syntax globalidx = idx
-}
type Globalidx = Idx

{-
;; ../spec/1-syntax.watsup:25.1-25.47
syntax tableidx = idx
-}
type Tableidx = Idx

{-
;; ../spec/1-syntax.watsup:26.1-26.46
syntax memidx = idx
-}
type Memidx = Idx

{-
;; ../spec/1-syntax.watsup:27.1-27.45
syntax elemidx = idx
-}
type Elemidx = Idx

{-
;; ../spec/1-syntax.watsup:28.1-28.45
syntax dataidx = idx
-}
type Dataidx = Idx

{-
;; ../spec/1-syntax.watsup:29.1-29.47
syntax labelidx = idx
-}
type Labelidx = Idx

{-
;; ../spec/1-syntax.watsup:30.1-30.47
syntax localidx = idx
-}
type Localidx = Idx

{-
;; ../spec/1-syntax.watsup:39.1-40.22
syntax numtype =
  | I32
  | I64
  | F32
  | F64
-}
data Numtype
 = Numtype_I32
 | Numtype_I64
 | Numtype_F32
 | Numtype_F64

{-
;; ../spec/1-syntax.watsup:41.1-42.5
syntax vectype =
  | V128
-}
data Vectype
 = Vectype_V128

{-
;; ../spec/1-syntax.watsup:43.1-44.20
syntax reftype =
  | FUNCREF
  | EXTERNREF
-}
data Reftype
 = Reftype_FUNCREF
 | Reftype_EXTERNREF

{-
;; ../spec/1-syntax.watsup:45.1-46.34
syntax valtype =
  | numtype
  | vectype
  | reftype
  | BOT
-}
data Valtype
 = Valtype_of_Numtype Numtype
 | Valtype_of_Vectype Vectype
 | Valtype_of_Reftype Reftype
 | Valtype_BOT

{-
;; ../spec/1-syntax.watsup:48.1-48.39
syntax in =
  | I32
  | I64
-}
data In
 = In_I32
 | In_I64

{-
;; ../spec/1-syntax.watsup:49.1-49.39
syntax fn =
  | F32
  | F64
-}
data Fn
 = Fn_F32
 | Fn_F64

{-
;; ../spec/1-syntax.watsup:56.1-57.11
syntax resulttype = valtype*
-}
type Resulttype = [Valtype]

{-
;; ../spec/1-syntax.watsup:59.1-60.16
syntax limits = `[%..%]`(u32, u32)
-}
type Limits = {- mixop: `[%..%]` -} (U32, U32)

{-
;; ../spec/1-syntax.watsup:61.1-62.15
syntax globaltype = `MUT%?%`(()?, valtype)
-}
type Globaltype = {- mixop: `MUT%?%` -} ((Maybe ()), Valtype)

{-
;; ../spec/1-syntax.watsup:63.1-64.27
syntax functype = `%->%`(resulttype, resulttype)
-}
type Functype = {- mixop: `%->%` -} (Resulttype, Resulttype)

{-
;; ../spec/1-syntax.watsup:65.1-66.17
syntax tabletype = `%%`(limits, reftype)
-}
type Tabletype = {- mixop: `%%` -} (Limits, Reftype)

{-
;; ../spec/1-syntax.watsup:67.1-68.12
syntax memtype = `%I8`(limits)
-}
type Memtype = {- mixop: `%I8` -} Limits

{-
;; ../spec/1-syntax.watsup:69.1-70.10
syntax elemtype = reftype
-}
type Elemtype = Reftype

{-
;; ../spec/1-syntax.watsup:71.1-72.5
syntax datatype = OK
-}
type Datatype = {- mixop: OK -} ()

{-
;; ../spec/1-syntax.watsup:73.1-74.69
syntax externtype =
  | GLOBAL(globaltype)
  | FUNC(functype)
  | TABLE(tabletype)
  | MEMORY(memtype)
-}
data Externtype
 = Externtype_GLOBAL Globaltype
 | Externtype_FUNC Functype
 | Externtype_TABLE Tabletype
 | Externtype_MEMORY Memtype

{-
;; ../spec/1-syntax.watsup:86.1-86.44
syntax sx =
  | U
  | S
-}
data Sx
 = Sx_U
 | Sx_S

{-
;; ../spec/1-syntax.watsup:88.1-88.39
syntax unop_IXX =
  | CLZ
  | CTZ
  | POPCNT
-}
data Unop_IXX
 = Unop_IXX_CLZ
 | Unop_IXX_CTZ
 | Unop_IXX_POPCNT

{-
;; ../spec/1-syntax.watsup:89.1-89.70
syntax unop_FXX =
  | ABS
  | NEG
  | SQRT
  | CEIL
  | FLOOR
  | TRUNC
  | NEAREST
-}
data Unop_FXX
 = Unop_FXX_ABS
 | Unop_FXX_NEG
 | Unop_FXX_SQRT
 | Unop_FXX_CEIL
 | Unop_FXX_FLOOR
 | Unop_FXX_TRUNC
 | Unop_FXX_NEAREST

{-
;; ../spec/1-syntax.watsup:91.1-93.62
syntax binop_IXX =
  | ADD
  | SUB
  | MUL
  | DIV(sx)
  | REM(sx)
  | AND
  | OR
  | XOR
  | SHL
  | SHR(sx)
  | ROTL
  | ROTR
-}
data Binop_IXX
 = Binop_IXX_ADD
 | Binop_IXX_SUB
 | Binop_IXX_MUL
 | Binop_IXX_DIV Sx
 | Binop_IXX_REM Sx
 | Binop_IXX_AND
 | Binop_IXX_OR
 | Binop_IXX_XOR
 | Binop_IXX_SHL
 | Binop_IXX_SHR Sx
 | Binop_IXX_ROTL
 | Binop_IXX_ROTR

{-
;; ../spec/1-syntax.watsup:94.1-94.66
syntax binop_FXX =
  | ADD
  | SUB
  | MUL
  | DIV
  | MIN
  | MAX
  | COPYSIGN
-}
data Binop_FXX
 = Binop_FXX_ADD
 | Binop_FXX_SUB
 | Binop_FXX_MUL
 | Binop_FXX_DIV
 | Binop_FXX_MIN
 | Binop_FXX_MAX
 | Binop_FXX_COPYSIGN

{-
;; ../spec/1-syntax.watsup:96.1-96.26
syntax testop_IXX =
  | EQZ
-}
data Testop_IXX
 = Testop_IXX_EQZ

{-
;; ../spec/1-syntax.watsup:97.1-97.22
syntax testop_FXX =
  |
-}
data Testop_FXX

{-
;; ../spec/1-syntax.watsup:99.1-100.108
syntax relop_IXX =
  | EQ
  | NE
  | LT(sx)
  | GT(sx)
  | LE(sx)
  | GE(sx)
-}
data Relop_IXX
 = Relop_IXX_EQ
 | Relop_IXX_NE
 | Relop_IXX_LT Sx
 | Relop_IXX_GT Sx
 | Relop_IXX_LE Sx
 | Relop_IXX_GE Sx

{-
;; ../spec/1-syntax.watsup:101.1-101.49
syntax relop_FXX =
  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE
-}
data Relop_FXX
 = Relop_FXX_EQ
 | Relop_FXX_NE
 | Relop_FXX_LT
 | Relop_FXX_GT
 | Relop_FXX_LE
 | Relop_FXX_GE

{-
;; ../spec/1-syntax.watsup:103.1-103.50
syntax unop_numtype =
  | _I(unop_IXX)
  | _F(unop_FXX)
-}
data Unop_numtype
 = Unop_numtype_I Unop_IXX
 | Unop_numtype_F Unop_FXX

{-
;; ../spec/1-syntax.watsup:104.1-104.53
syntax binop_numtype =
  | _I(binop_IXX)
  | _F(binop_FXX)
-}
data Binop_numtype
 = Binop_numtype_I Binop_IXX
 | Binop_numtype_F Binop_FXX

{-
;; ../spec/1-syntax.watsup:105.1-105.56
syntax testop_numtype =
  | _I(testop_IXX)
  | _F(testop_FXX)
-}
data Testop_numtype
 = Testop_numtype_I Testop_IXX
 | Testop_numtype_F Testop_FXX

{-
;; ../spec/1-syntax.watsup:106.1-106.53
syntax relop_numtype =
  | _I(relop_IXX)
  | _F(relop_FXX)
-}
data Relop_numtype
 = Relop_numtype_I Relop_IXX
 | Relop_numtype_F Relop_FXX

{-
;; ../spec/1-syntax.watsup:107.1-107.39
syntax cvtop =
  | CONVERT
  | REINTERPRET
-}
data Cvtop
 = Cvtop_CONVERT
 | Cvtop_REINTERPRET

{-
;; ../spec/1-syntax.watsup:117.1-117.23
syntax c_numtype = nat
-}
type C_numtype = Natural

{-
;; ../spec/1-syntax.watsup:118.1-118.23
syntax c_vectype = nat
-}
type C_vectype = Natural

{-
;; ../spec/1-syntax.watsup:121.1-121.52
syntax blocktype = functype
-}
type Blocktype = Functype

{-
;; ../spec/1-syntax.watsup:156.1-177.55
rec {

;; ../spec/1-syntax.watsup:156.1-177.55
syntax instr =
  | UNREACHABLE
  | NOP
  | DROP
  | SELECT(valtype?)
  | BLOCK(blocktype, instr*)
  | LOOP(blocktype, instr*)
  | IF(blocktype, instr*, instr*)
  | BR(labelidx)
  | BR_IF(labelidx)
  | BR_TABLE(labelidx*, labelidx)
  | CALL(funcidx)
  | CALL_INDIRECT(tableidx, functype)
  | RETURN
  | CONST(numtype, c_numtype)
  | UNOP(numtype, unop_numtype)
  | BINOP(numtype, binop_numtype)
  | TESTOP(numtype, testop_numtype)
  | RELOP(numtype, relop_numtype)
  | EXTEND(numtype, n)
  | CVTOP(numtype, cvtop, numtype, sx?)
  | REF.NULL(reftype)
  | REF.FUNC(funcidx)
  | REF.IS_NULL
  | LOCAL.GET(localidx)
  | LOCAL.SET(localidx)
  | LOCAL.TEE(localidx)
  | GLOBAL.GET(globalidx)
  | GLOBAL.SET(globalidx)
  | TABLE.GET(tableidx)
  | TABLE.SET(tableidx)
  | TABLE.SIZE(tableidx)
  | TABLE.GROW(tableidx)
  | TABLE.FILL(tableidx)
  | TABLE.COPY(tableidx, tableidx)
  | TABLE.INIT(tableidx, elemidx)
  | ELEM.DROP(elemidx)
  | MEMORY.SIZE
  | MEMORY.GROW
  | MEMORY.FILL
  | MEMORY.COPY
  | MEMORY.INIT(dataidx)
  | DATA.DROP(dataidx)
  | LOAD(numtype, (n, sx)?, nat, nat)
  | STORE(numtype, n?, nat, nat)
}
-}
{-
;; ../spec/1-syntax.watsup:156.1-177.55
syntax instr =
  | UNREACHABLE
  | NOP
  | DROP
  | SELECT(valtype?)
  | BLOCK(blocktype, instr*)
  | LOOP(blocktype, instr*)
  | IF(blocktype, instr*, instr*)
  | BR(labelidx)
  | BR_IF(labelidx)
  | BR_TABLE(labelidx*, labelidx)
  | CALL(funcidx)
  | CALL_INDIRECT(tableidx, functype)
  | RETURN
  | CONST(numtype, c_numtype)
  | UNOP(numtype, unop_numtype)
  | BINOP(numtype, binop_numtype)
  | TESTOP(numtype, testop_numtype)
  | RELOP(numtype, relop_numtype)
  | EXTEND(numtype, n)
  | CVTOP(numtype, cvtop, numtype, sx?)
  | REF.NULL(reftype)
  | REF.FUNC(funcidx)
  | REF.IS_NULL
  | LOCAL.GET(localidx)
  | LOCAL.SET(localidx)
  | LOCAL.TEE(localidx)
  | GLOBAL.GET(globalidx)
  | GLOBAL.SET(globalidx)
  | TABLE.GET(tableidx)
  | TABLE.SET(tableidx)
  | TABLE.SIZE(tableidx)
  | TABLE.GROW(tableidx)
  | TABLE.FILL(tableidx)
  | TABLE.COPY(tableidx, tableidx)
  | TABLE.INIT(tableidx, elemidx)
  | ELEM.DROP(elemidx)
  | MEMORY.SIZE
  | MEMORY.GROW
  | MEMORY.FILL
  | MEMORY.COPY
  | MEMORY.INIT(dataidx)
  | DATA.DROP(dataidx)
  | LOAD(numtype, (n, sx)?, nat, nat)
  | STORE(numtype, n?, nat, nat)
-}
data Instr
 = Instr_UNREACHABLE
 | Instr_NOP
 | Instr_DROP
 | Instr_SELECT (Maybe Valtype)
 | Instr_BLOCK (Blocktype, [Instr])
 | Instr_LOOP (Blocktype, [Instr])
 | Instr_IF (Blocktype, [Instr], [Instr])
 | Instr_BR Labelidx
 | Instr_BR_IF Labelidx
 | Instr_BR_TABLE ([Labelidx], Labelidx)
 | Instr_CALL Funcidx
 | Instr_CALL_INDIRECT (Tableidx, Functype)
 | Instr_RETURN
 | Instr_CONST (Numtype, C_numtype)
 | Instr_UNOP (Numtype, Unop_numtype)
 | Instr_BINOP (Numtype, Binop_numtype)
 | Instr_TESTOP (Numtype, Testop_numtype)
 | Instr_RELOP (Numtype, Relop_numtype)
 | Instr_EXTEND (Numtype, N)
 | Instr_CVTOP (Numtype, Cvtop, Numtype, (Maybe Sx))
 | Instr_REF_NULL Reftype
 | Instr_REF_FUNC Funcidx
 | Instr_REF_IS_NULL
 | Instr_LOCAL_GET Localidx
 | Instr_LOCAL_SET Localidx
 | Instr_LOCAL_TEE Localidx
 | Instr_GLOBAL_GET Globalidx
 | Instr_GLOBAL_SET Globalidx
 | Instr_TABLE_GET Tableidx
 | Instr_TABLE_SET Tableidx
 | Instr_TABLE_SIZE Tableidx
 | Instr_TABLE_GROW Tableidx
 | Instr_TABLE_FILL Tableidx
 | Instr_TABLE_COPY (Tableidx, Tableidx)
 | Instr_TABLE_INIT (Tableidx, Elemidx)
 | Instr_ELEM_DROP Elemidx
 | Instr_MEMORY_SIZE
 | Instr_MEMORY_GROW
 | Instr_MEMORY_FILL
 | Instr_MEMORY_COPY
 | Instr_MEMORY_INIT Dataidx
 | Instr_DATA_DROP Dataidx
 | Instr_LOAD (Numtype, (Maybe (N, Sx)), Natural, Natural)
 | Instr_STORE (Numtype, (Maybe N), Natural, Natural)

{-
;; ../spec/1-syntax.watsup:179.1-180.9
syntax expr = instr*
-}
type Expr = [Instr]

{-
;; ../spec/1-syntax.watsup:185.1-185.50
syntax elemmode =
  | TABLE(tableidx, expr)
  | DECLARE
-}
data Elemmode
 = Elemmode_TABLE (Tableidx, Expr)
 | Elemmode_DECLARE

{-
;; ../spec/1-syntax.watsup:186.1-186.39
syntax datamode =
  | MEMORY(memidx, expr)
-}
data Datamode
 = Datamode_MEMORY (Memidx, Expr)

{-
;; ../spec/1-syntax.watsup:188.1-189.30
syntax func = FUNC(functype, valtype*, expr)
-}
type Func = {- mixop: FUNC -} (Functype, [Valtype], Expr)

{-
;; ../spec/1-syntax.watsup:190.1-191.25
syntax global = GLOBAL(globaltype, expr)
-}
type Global = {- mixop: GLOBAL -} (Globaltype, Expr)

{-
;; ../spec/1-syntax.watsup:192.1-193.18
syntax table = TABLE(tabletype)
-}
type Table = {- mixop: TABLE -} Tabletype

{-
;; ../spec/1-syntax.watsup:194.1-195.17
syntax mem = MEMORY(memtype)
-}
type Mem = {- mixop: MEMORY -} Memtype

{-
;; ../spec/1-syntax.watsup:196.1-197.31
syntax elem = ELEM(reftype, expr*, elemmode?)
-}
type Elem = {- mixop: ELEM -} (Reftype, [Expr], (Maybe Elemmode))

{-
;; ../spec/1-syntax.watsup:198.1-199.26
syntax data = DATA(byte**, datamode?)
-}
type Data = {- mixop: DATA -} ([[Byte]], (Maybe Datamode))

{-
;; ../spec/1-syntax.watsup:200.1-201.16
syntax start = START(funcidx)
-}
type Start = {- mixop: START -} Funcidx

{-
;; ../spec/1-syntax.watsup:203.1-204.65
syntax externuse =
  | FUNC(funcidx)
  | GLOBAL(globalidx)
  | TABLE(tableidx)
  | MEMORY(memidx)
-}
data Externuse
 = Externuse_FUNC Funcidx
 | Externuse_GLOBAL Globalidx
 | Externuse_TABLE Tableidx
 | Externuse_MEMORY Memidx

{-
;; ../spec/1-syntax.watsup:205.1-206.24
syntax export = EXPORT(name, externuse)
-}
type Export = {- mixop: EXPORT -} (Name, Externuse)

{-
;; ../spec/1-syntax.watsup:207.1-208.30
syntax import = IMPORT(name, name, externtype)
-}
type Import = {- mixop: IMPORT -} (Name, Name, Externtype)

{-
;; ../spec/1-syntax.watsup:210.1-211.70
syntax module = MODULE(import*, func*, global*, table*, mem*, elem*, data*, start*, export*)
-}
type Module = {- mixop: MODULE -} ([Import], [Func], [Global], [Table], [Mem], [Elem], [Data], [Start], [Export])

{-
;; ../spec/2-aux.watsup:5.1-5.55
def size : valtype -> nat
  ;; ../spec/2-aux.watsup:10.1-10.22
  def size(V128_valtype) = 128
  ;; ../spec/2-aux.watsup:9.1-9.20
  def size(F64_valtype) = 64
  ;; ../spec/2-aux.watsup:8.1-8.20
  def size(F32_valtype) = 32
  ;; ../spec/2-aux.watsup:7.1-7.20
  def size(I64_valtype) = 64
  ;; ../spec/2-aux.watsup:6.1-6.20
  def size(I32_valtype) = 32
-}
size :: Valtype -> Natural
size (Valtype_of_Vectype Vectype_V128) = 128
size (Valtype_of_Numtype Numtype_F64) = 64
size (Valtype_of_Numtype Numtype_F32) = 32
size (Valtype_of_Numtype Numtype_I64) = 64
size (Valtype_of_Numtype Numtype_I32) = 32

{-
;; ../spec/2-aux.watsup:15.1-15.40
def test_sub_ATOM_22 : n -> nat
  ;; ../spec/2-aux.watsup:16.1-16.38
  def {n_3_ATOM_y : n} test_sub_ATOM_22(n_3_ATOM_y) = 0
-}
test_sub_ATOM_22 :: N -> Natural
test_sub_ATOM_22 n_3_ATOM_y = 0

{-
;; ../spec/2-aux.watsup:18.1-18.26
def curried_ : (n, n) -> nat
  ;; ../spec/2-aux.watsup:19.1-19.39
  def {n_1 : n, n_2 : n} curried_(n_1, n_2) = (n_1 + n_2)
-}
curried_ :: (N, N) -> Natural
curried_ (n_1, n_2) = (n_1 + n_2)

{-
;; ../spec/2-aux.watsup:21.1-30.39
syntax testfuse =
  | AB_(nat, nat, nat)
  | CD(nat, nat, nat)
  | EF(nat, nat, nat)
  | GH(nat, nat, nat)
  | IJ(nat, nat, nat)
  | KL(nat, nat, nat)
  | MN(nat, nat, nat)
  | OP(nat, nat, nat)
  | QR(nat, nat, nat)
-}
data Testfuse
 = Testfuse_AB_ (Natural, Natural, Natural)
 | Testfuse_CD (Natural, Natural, Natural)
 | Testfuse_EF (Natural, Natural, Natural)
 | Testfuse_GH (Natural, Natural, Natural)
 | Testfuse_IJ (Natural, Natural, Natural)
 | Testfuse_KL (Natural, Natural, Natural)
 | Testfuse_MN (Natural, Natural, Natural)
 | Testfuse_OP (Natural, Natural, Natural)
 | Testfuse_QR (Natural, Natural, Natural)

{-
;; ../spec/3-typing.watsup:3.1-6.60
syntax context = {FUNC functype*, GLOBAL globaltype*, TABLE tabletype*, MEM memtype*, ELEM elemtype*, DATA datatype*, LOCAL valtype*, LABEL resulttype*, RETURN resulttype?}
-}
data Context = MkContext
 { fUNC :: [Functype]
 , gLOBAL :: [Globaltype]
 , tABLE :: [Tabletype]
 , mEM :: [Memtype]
 , eLEM :: [Elemtype]
 , dATA :: [Datatype]
 , lOCAL :: [Valtype]
 , lABEL :: [Resulttype]
 , rETURN :: (Maybe Resulttype)
 }

{-
;; ../spec/3-typing.watsup:14.1-14.66
relation Limits_ok: `|-%:%`(limits, nat)
  ;; ../spec/3-typing.watsup:22.1-24.24
  rule _ {k : nat, n_1 : n, n_2 : n}:
    `|-%:%`(`[%..%]`(n_1, n_2), k)
    -- if ((n_1 <= n_2) /\ (n_2 <= k))
-}


{-
;; ../spec/3-typing.watsup:15.1-15.64
relation Functype_ok: `|-%:OK`(functype)
  ;; ../spec/3-typing.watsup:26.1-27.13
  rule _ {ft : functype}:
    `|-%:OK`(ft)
-}


{-
;; ../spec/3-typing.watsup:16.1-16.66
relation Globaltype_ok: `|-%:OK`(globaltype)
  ;; ../spec/3-typing.watsup:29.1-30.13
  rule _ {gt : globaltype}:
    `|-%:OK`(gt)
-}


{-
;; ../spec/3-typing.watsup:17.1-17.65
relation Tabletype_ok: `|-%:OK`(tabletype)
  ;; ../spec/3-typing.watsup:32.1-34.35
  rule _ {lim : limits, rt : reftype}:
    `|-%:OK`(`%%`(lim, rt))
    -- Limits_ok: `|-%:%`(lim, ((2 ^ 32) - 1))
-}


{-
;; ../spec/3-typing.watsup:18.1-18.63
relation Memtype_ok: `|-%:OK`(memtype)
  ;; ../spec/3-typing.watsup:36.1-38.33
  rule _ {lim : limits}:
    `|-%:OK`(`%I8`(lim))
    -- Limits_ok: `|-%:%`(lim, (2 ^ 16))
-}


{-
;; ../spec/3-typing.watsup:19.1-19.66
relation Externtype_ok: `|-%:OK`(externtype)
  ;; ../spec/3-typing.watsup:53.1-55.33
  rule mem {memtype : memtype}:
    `|-%:OK`(MEMORY_externtype(memtype))
    -- Memtype_ok: `|-%:OK`(memtype)

  ;; ../spec/3-typing.watsup:49.1-51.37
  rule table {tabletype : tabletype}:
    `|-%:OK`(TABLE_externtype(tabletype))
    -- Tabletype_ok: `|-%:OK`(tabletype)

  ;; ../spec/3-typing.watsup:45.1-47.39
  rule global {globaltype : globaltype}:
    `|-%:OK`(GLOBAL_externtype(globaltype))
    -- Globaltype_ok: `|-%:OK`(globaltype)

  ;; ../spec/3-typing.watsup:41.1-43.35
  rule func {functype : functype}:
    `|-%:OK`(FUNC_externtype(functype))
    -- Functype_ok: `|-%:OK`(functype)
-}


{-
;; ../spec/3-typing.watsup:61.1-61.65
relation Valtype_sub: `|-%<:%`(valtype, valtype)
  ;; ../spec/3-typing.watsup:67.1-68.14
  rule bot {t : valtype}:
    `|-%<:%`(BOT_valtype, t)

  ;; ../spec/3-typing.watsup:64.1-65.12
  rule refl {t : valtype}:
    `|-%<:%`(t, t)
-}


{-
;; ../spec/3-typing.watsup:62.1-62.72
relation Resulttype_sub: `|-%<:%`(valtype*, valtype*)
  ;; ../spec/3-typing.watsup:70.1-72.35
  rule _ {t_1 : valtype, t_2 : valtype}:
    `|-%<:%`(t_1*, t_2*)
    -- (Valtype_sub: `|-%<:%`(t_1, t_2))*
-}


{-
;; ../spec/3-typing.watsup:75.1-75.75
relation Limits_sub: `|-%<:%`(limits, limits)
  ;; ../spec/3-typing.watsup:83.1-86.21
  rule _ {n_11 : n, n_12 : n, n_21 : n, n_22 : n}:
    `|-%<:%`(`[%..%]`(n_11, n_12), `[%..%]`(n_21, n_22))
    -- if (n_11 >= n_21)
    -- if (n_12 <= n_22)
-}


{-
;; ../spec/3-typing.watsup:76.1-76.73
relation Functype_sub: `|-%<:%`(functype, functype)
  ;; ../spec/3-typing.watsup:88.1-89.14
  rule _ {ft : functype}:
    `|-%<:%`(ft, ft)
-}


{-
;; ../spec/3-typing.watsup:77.1-77.75
relation Globaltype_sub: `|-%<:%`(globaltype, globaltype)
  ;; ../spec/3-typing.watsup:91.1-92.14
  rule _ {gt : globaltype}:
    `|-%<:%`(gt, gt)
-}


{-
;; ../spec/3-typing.watsup:78.1-78.74
relation Tabletype_sub: `|-%<:%`(tabletype, tabletype)
  ;; ../spec/3-typing.watsup:94.1-96.35
  rule _ {lim_1 : limits, lim_2 : limits, rt : reftype}:
    `|-%<:%`(`%%`(lim_1, rt), `%%`(lim_2, rt))
    -- Limits_sub: `|-%<:%`(lim_1, lim_2)
-}


{-
;; ../spec/3-typing.watsup:79.1-79.72
relation Memtype_sub: `|-%<:%`(memtype, memtype)
  ;; ../spec/3-typing.watsup:98.1-100.35
  rule _ {lim_1 : limits, lim_2 : limits}:
    `|-%<:%`(`%I8`(lim_1), `%I8`(lim_2))
    -- Limits_sub: `|-%<:%`(lim_1, lim_2)
-}


{-
;; ../spec/3-typing.watsup:80.1-80.75
relation Externtype_sub: `|-%<:%`(externtype, externtype)
  ;; ../spec/3-typing.watsup:115.1-117.34
  rule mem {mt_1 : memtype, mt_2 : memtype}:
    `|-%<:%`(MEMORY_externtype(mt_1), MEMORY_externtype(mt_2))
    -- Memtype_sub: `|-%<:%`(mt_1, mt_2)

  ;; ../spec/3-typing.watsup:111.1-113.36
  rule table {tt_1 : tabletype, tt_2 : tabletype}:
    `|-%<:%`(TABLE_externtype(tt_1), TABLE_externtype(tt_2))
    -- Tabletype_sub: `|-%<:%`(tt_1, tt_2)

  ;; ../spec/3-typing.watsup:107.1-109.37
  rule global {gt_1 : globaltype, gt_2 : globaltype}:
    `|-%<:%`(GLOBAL_externtype(gt_1), GLOBAL_externtype(gt_2))
    -- Globaltype_sub: `|-%<:%`(gt_1, gt_2)

  ;; ../spec/3-typing.watsup:103.1-105.35
  rule func {ft_1 : functype, ft_2 : functype}:
    `|-%<:%`(FUNC_externtype(ft_1), FUNC_externtype(ft_2))
    -- Functype_sub: `|-%<:%`(ft_1, ft_2)
-}


{-
;; ../spec/3-typing.watsup:172.1-172.76
relation Blocktype_ok: `%|-%:%`(context, blocktype, functype)
  ;; ../spec/3-typing.watsup:174.1-176.29
  rule _ {C : context, ft : functype}:
    `%|-%:%`(C, ft, ft)
    -- Functype_ok: `|-%:OK`(ft)
-}


{-
;; ../spec/3-typing.watsup:123.1-124.67
rec {

;; ../spec/3-typing.watsup:123.1-123.66
relation Instr_ok: `%|-%:%`(context, instr, functype)
  ;; ../spec/3-typing.watsup:357.1-362.32
  rule store {C : context, in : in, mt : memtype, n : n, n_A : n, n_O : n, nt : numtype, t : valtype}:
    `%|-%:%`(C, STORE_instr(nt, n?, n_A, n_O), `%->%`([I32_valtype (nt <: valtype)], []))
    -- if (C.MEM_context[0] = mt)
    -- if ((2 ^ n_A) <= ($size(t) / 8))
    -- (if (((2 ^ n_A) <= (n / 8)) /\ ((n / 8) < ($size(t) / 8))))?
    -- if ((n? = ?()) \/ (nt = (in <: numtype)))

  ;; ../spec/3-typing.watsup:350.1-355.32
  rule load {C : context, in : in, mt : memtype, n : n, n_A : n, n_O : n, nt : numtype, sx : sx, t : valtype}:
    `%|-%:%`(C, LOAD_instr(nt, ?((n, sx)), n_A, n_O), `%->%`([I32_valtype], [(nt <: valtype)]))
    -- if (C.MEM_context[0] = mt)
    -- if ((2 ^ n_A) <= ($size(t) / 8))
    -- (if (((2 ^ n_A) <= (n / 8)) /\ ((n / 8) < ($size(t) / 8))))?
    -- if ((n? = ?()) \/ (nt = (in <: numtype)))

  ;; ../spec/3-typing.watsup:346.1-348.23
  rule data.drop {C : context, x : idx}:
    `%|-%:%`(C, DATA.DROP_instr(x), `%->%`([], []))
    -- if (C.DATA_context[x] = OK)

  ;; ../spec/3-typing.watsup:341.1-344.23
  rule memory.init {C : context, mt : memtype, x : idx}:
    `%|-%:%`(C, MEMORY.INIT_instr(x), `%->%`([I32_valtype I32_valtype I32_valtype], [I32_valtype]))
    -- if (C.MEM_context[0] = mt)
    -- if (C.DATA_context[x] = OK)

  ;; ../spec/3-typing.watsup:337.1-339.22
  rule memory.copy {C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY.COPY_instr, `%->%`([I32_valtype I32_valtype I32_valtype], [I32_valtype]))
    -- if (C.MEM_context[0] = mt)

  ;; ../spec/3-typing.watsup:333.1-335.22
  rule memory.fill {C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY.FILL_instr, `%->%`([I32_valtype I32_valtype I32_valtype], [I32_valtype]))
    -- if (C.MEM_context[0] = mt)

  ;; ../spec/3-typing.watsup:329.1-331.22
  rule memory.grow {C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY.GROW_instr, `%->%`([I32_valtype], [I32_valtype]))
    -- if (C.MEM_context[0] = mt)

  ;; ../spec/3-typing.watsup:325.1-327.22
  rule memory.size {C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY.SIZE_instr, `%->%`([], [I32_valtype]))
    -- if (C.MEM_context[0] = mt)

  ;; ../spec/3-typing.watsup:320.1-322.23
  rule elem.drop {C : context, rt : reftype, x : idx}:
    `%|-%:%`(C, ELEM.DROP_instr(x), `%->%`([], []))
    -- if (C.ELEM_context[x] = rt)

  ;; ../spec/3-typing.watsup:315.1-318.25
  rule table.init {C : context, lim : limits, rt : reftype, x_1 : idx, x_2 : idx}:
    `%|-%:%`(C, TABLE.INIT_instr(x_1, x_2), `%->%`([I32_valtype I32_valtype I32_valtype], []))
    -- if (C.TABLE_context[x_1] = `%%`(lim, rt))
    -- if (C.ELEM_context[x_2] = rt)

  ;; ../spec/3-typing.watsup:310.1-313.32
  rule table.copy {C : context, lim_1 : limits, lim_2 : limits, rt : reftype, x_1 : idx, x_2 : idx}:
    `%|-%:%`(C, TABLE.COPY_instr(x_1, x_2), `%->%`([I32_valtype I32_valtype I32_valtype], []))
    -- if (C.TABLE_context[x_1] = `%%`(lim_1, rt))
    -- if (C.TABLE_context[x_2] = `%%`(lim_2, rt))

  ;; ../spec/3-typing.watsup:306.1-308.28
  rule table.fill {C : context, lim : limits, rt : reftype, x : idx}:
    `%|-%:%`(C, TABLE.FILL_instr(x), `%->%`([I32_valtype (rt <: valtype) I32_valtype], []))
    -- if (C.TABLE_context[x] = `%%`(lim, rt))

  ;; ../spec/3-typing.watsup:302.1-304.28
  rule table.grow {C : context, lim : limits, rt : reftype, x : idx}:
    `%|-%:%`(C, TABLE.GROW_instr(x), `%->%`([(rt <: valtype) I32_valtype], [I32_valtype]))
    -- if (C.TABLE_context[x] = `%%`(lim, rt))

  ;; ../spec/3-typing.watsup:298.1-300.24
  rule table.size {C : context, tt : tabletype, x : idx}:
    `%|-%:%`(C, TABLE.SIZE_instr(x), `%->%`([], [I32_valtype]))
    -- if (C.TABLE_context[x] = tt)

  ;; ../spec/3-typing.watsup:294.1-296.28
  rule table.set {C : context, lim : limits, rt : reftype, x : idx}:
    `%|-%:%`(C, TABLE.SET_instr(x), `%->%`([I32_valtype (rt <: valtype)], []))
    -- if (C.TABLE_context[x] = `%%`(lim, rt))

  ;; ../spec/3-typing.watsup:290.1-292.28
  rule table.get {C : context, lim : limits, rt : reftype, x : idx}:
    `%|-%:%`(C, TABLE.GET_instr(x), `%->%`([I32_valtype], [(rt <: valtype)]))
    -- if (C.TABLE_context[x] = `%%`(lim, rt))

  ;; ../spec/3-typing.watsup:285.1-287.28
  rule global.set {C : context, t : valtype, x : idx}:
    `%|-%:%`(C, GLOBAL.SET_instr(x), `%->%`([t], []))
    -- if (C.GLOBAL_context[x] = `MUT%?%`(?(()), t))

  ;; ../spec/3-typing.watsup:281.1-283.29
  rule global.get {C : context, t : valtype, x : idx}:
    `%|-%:%`(C, GLOBAL.GET_instr(x), `%->%`([], [t]))
    -- if (C.GLOBAL_context[x] = `MUT%?%`(?(()), t))

  ;; ../spec/3-typing.watsup:276.1-278.23
  rule local.tee {C : context, t : valtype, x : idx}:
    `%|-%:%`(C, LOCAL.TEE_instr(x), `%->%`([t], [t]))
    -- if (C.LOCAL_context[x] = t)

  ;; ../spec/3-typing.watsup:272.1-274.23
  rule local.set {C : context, t : valtype, x : idx}:
    `%|-%:%`(C, LOCAL.SET_instr(x), `%->%`([t], []))
    -- if (C.LOCAL_context[x] = t)

  ;; ../spec/3-typing.watsup:268.1-270.23
  rule local.get {C : context, t : valtype, x : idx}:
    `%|-%:%`(C, LOCAL.GET_instr(x), `%->%`([], [t]))
    -- if (C.LOCAL_context[x] = t)

  ;; ../spec/3-typing.watsup:264.1-265.31
  rule ref.is_null {C : context, rt : reftype}:
    `%|-%:%`(C, REF.IS_NULL_instr, `%->%`([(rt <: valtype)], [I32_valtype]))

  ;; ../spec/3-typing.watsup:260.1-262.23
  rule ref.func {C : context, ft : functype, x : idx}:
    `%|-%:%`(C, REF.FUNC_instr(x), `%->%`([], [FUNCREF_valtype]))
    -- if (C.FUNC_context[x] = ft)

  ;; ../spec/3-typing.watsup:257.1-258.35
  rule ref.null {C : context, rt : reftype}:
    `%|-%:%`(C, REF.NULL_instr(rt), `%->%`([], [(rt <: valtype)]))

  ;; ../spec/3-typing.watsup:252.1-254.22
  rule convert-f {C : context, fn_1 : fn, fn_2 : fn}:
    `%|-%:%`(C, CVTOP_instr((fn_1 <: numtype), CONVERT_cvtop, (fn_2 <: numtype), ?()), `%->%`([(fn_2 <: valtype)], [(fn_1 <: valtype)]))
    -- if (fn_1 =/= fn_2)

  ;; ../spec/3-typing.watsup:247.1-250.52
  rule convert-i {C : context, in_1 : in, in_2 : in, sx : sx}:
    `%|-%:%`(C, CVTOP_instr((in_1 <: numtype), CONVERT_cvtop, (in_2 <: numtype), sx?), `%->%`([(in_2 <: valtype)], [(in_1 <: valtype)]))
    -- if (in_1 =/= in_2)
    -- if ((sx? = ?()) <=> ($size(in_1 <: valtype) > $size(in_2 <: valtype)))

  ;; ../spec/3-typing.watsup:242.1-245.34
  rule reinterpret {C : context, nt_1 : numtype, nt_2 : numtype}:
    `%|-%:%`(C, CVTOP_instr(nt_1, REINTERPRET_cvtop, nt_2, ?()), `%->%`([(nt_2 <: valtype)], [(nt_1 <: valtype)]))
    -- if (nt_1 =/= nt_2)
    -- if ($size(nt_1 <: valtype) = $size(nt_2 <: valtype))

  ;; ../spec/3-typing.watsup:238.1-240.23
  rule extend {C : context, n : n, nt : numtype}:
    `%|-%:%`(C, EXTEND_instr(nt, n), `%->%`([(nt <: valtype)], [(nt <: valtype)]))
    -- if (n <= $size(nt <: valtype))

  ;; ../spec/3-typing.watsup:234.1-235.37
  rule relop {C : context, nt : numtype, relop : relop_numtype}:
    `%|-%:%`(C, RELOP_instr(nt, relop), `%->%`([(nt <: valtype) (nt <: valtype)], [I32_valtype]))

  ;; ../spec/3-typing.watsup:231.1-232.36
  rule testop {C : context, nt : numtype, testop : testop_numtype}:
    `%|-%:%`(C, TESTOP_instr(nt, testop), `%->%`([(nt <: valtype)], [I32_valtype]))

  ;; ../spec/3-typing.watsup:228.1-229.36
  rule binop {C : context, binop : binop_numtype, nt : numtype}:
    `%|-%:%`(C, BINOP_instr(nt, binop), `%->%`([(nt <: valtype) (nt <: valtype)], [(nt <: valtype)]))

  ;; ../spec/3-typing.watsup:225.1-226.31
  rule unop {C : context, nt : numtype, unop : unop_numtype}:
    `%|-%:%`(C, UNOP_instr(nt, unop), `%->%`([(nt <: valtype)], [(nt <: valtype)]))

  ;; ../spec/3-typing.watsup:222.1-223.37
  rule const {C : context, c_nt : c_numtype, nt : numtype}:
    `%|-%:%`(C, CONST_instr(nt, c_nt), `%->%`([], [(nt <: valtype)]))

  ;; ../spec/3-typing.watsup:216.1-219.26
  rule call_indirect {C : context, ft : functype, lim : limits, t_1 : valtype, t_2 : valtype, x : idx}:
    `%|-%:%`(C, CALL_INDIRECT_instr(x, ft), `%->%`(t_1* :: [I32_valtype], t_2*))
    -- if (C.TABLE_context[x] = `%%`(lim, FUNCREF_reftype))
    -- if (ft = `%->%`(t_1*, t_2*))

  ;; ../spec/3-typing.watsup:212.1-214.33
  rule call {C : context, t_1 : valtype, t_2 : valtype, x : idx}:
    `%|-%:%`(C, CALL_instr(x), `%->%`(t_1*, t_2*))
    -- if (C.FUNC_context[x] = `%->%`(t_1*, t_2*))

  ;; ../spec/3-typing.watsup:208.1-210.24
  rule return {C : context, t : valtype, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, RETURN_instr, `%->%`(t_1* :: t*, t_2*))
    -- if (C.RETURN_context = ?(t*))

  ;; ../spec/3-typing.watsup:203.1-206.42
  rule br_table {C : context, l : labelidx, l' : labelidx, t : valtype, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, BR_TABLE_instr(l*, l'), `%->%`(t_1* :: t*, t_2*))
    -- (Resulttype_sub: `|-%<:%`(t*, C.LABEL_context[l]))*
    -- Resulttype_sub: `|-%<:%`(t*, C.LABEL_context[l'])

  ;; ../spec/3-typing.watsup:199.1-201.24
  rule br_if {C : context, l : labelidx, t : valtype}:
    `%|-%:%`(C, BR_IF_instr(l), `%->%`(t* :: [I32_valtype], t*))
    -- if (C.LABEL_context[l] = t*)

  ;; ../spec/3-typing.watsup:195.1-197.24
  rule br {C : context, l : labelidx, t : valtype, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, BR_instr(l), `%->%`(t_1* :: t*, t_2*))
    -- if (C.LABEL_context[l] = t*)

  ;; ../spec/3-typing.watsup:188.1-192.59
  rule if {C : context, bt : blocktype, instr_1 : instr, instr_2 : instr, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, IF_instr(bt, instr_1*, instr_2*), `%->%`(t_1*, [t_2]))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*, [t_2]))
    -- InstrSeq_ok: `%|-%:%`(C ++ {FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2]*, RETURN ?()}, instr_1*, `%->%`(t_1*, t_2*))
    -- InstrSeq_ok: `%|-%:%`(C ++ {FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2]*, RETURN ?()}, instr_2*, `%->%`(t_1*, t_2*))

  ;; ../spec/3-typing.watsup:183.1-186.56
  rule loop {C : context, bt : blocktype, instr : instr, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, LOOP_instr(bt, instr*), `%->%`(t_1*, t_2*))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*, t_2*))
    -- InstrSeq_ok: `%|-%:%`(C ++ {FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_1]*, RETURN ?()}, instr*, `%->%`(t_1*, [t_2]))

  ;; ../spec/3-typing.watsup:178.1-181.57
  rule block {C : context, bt : blocktype, instr : instr, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, BLOCK_instr(bt, instr*), `%->%`(t_1*, t_2*))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*, t_2*))
    -- InstrSeq_ok: `%|-%:%`(C ++ {FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2]*, RETURN ?()}, instr*, `%->%`(t_1*, t_2*))

  ;; ../spec/3-typing.watsup:166.1-169.37
  rule select-impl {C : context, numtype : numtype, t : valtype, t' : valtype, vectype : vectype}:
    `%|-%:%`(C, SELECT_instr(?()), `%->%`([t t I32_valtype], [t]))
    -- Valtype_sub: `|-%<:%`(t, t')
    -- if ((t' = (numtype <: valtype)) \/ (t' = (vectype <: valtype)))

  ;; ../spec/3-typing.watsup:163.1-164.31
  rule select-expl {C : context, t : valtype}:
    `%|-%:%`(C, SELECT_instr(?(t)), `%->%`([t t I32_valtype], [t]))

  ;; ../spec/3-typing.watsup:159.1-160.27
  rule drop {C : context, t : valtype}:
    `%|-%:%`(C, DROP_instr, `%->%`([t], []))

  ;; ../spec/3-typing.watsup:156.1-157.32
  rule nop {C : context}:
    `%|-%:%`(C, NOP_instr, `%->%`([], []))

  ;; ../spec/3-typing.watsup:153.1-154.34
  rule unreachable {C : context, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, UNREACHABLE_instr, `%->%`(t_1*, t_2*))

;; ../spec/3-typing.watsup:124.1-124.67
relation InstrSeq_ok: `%|-%:%`(context, instr*, functype)
  ;; ../spec/3-typing.watsup:148.1-150.45
  rule frame {C : context, instr : instr, t : valtype, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, instr*, `%->%`(t* :: t_1*, t* :: t_2*))
    -- InstrSeq_ok: `%|-%:%`(C, instr*, `%->%`(t_1*, t_2*))

  ;; ../spec/3-typing.watsup:141.1-146.38
  rule weak {C : context, instr : instr, t'_1 : valtype, t'_2 : valtype, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, instr*, `%->%`([t'_1], t'_2*))
    -- InstrSeq_ok: `%|-%:%`(C, instr*, `%->%`(t_1*, t_2*))
    -- Resulttype_sub: `|-%<:%`(t'_1*, t_1*)
    -- Resulttype_sub: `|-%<:%`(t_2*, t'_2*)

  ;; ../spec/3-typing.watsup:136.1-139.46
  rule seq {C : context, instr_1 : instr, instr_2 : instr, t_1 : valtype, t_2 : valtype, t_3 : valtype}:
    `%|-%:%`(C, [instr_1] :: instr_2*, `%->%`(t_1*, t_3*))
    -- Instr_ok: `%|-%:%`(C, instr_1, `%->%`(t_1*, t_2*))
    -- InstrSeq_ok: `%|-%:%`(C, [instr_2], `%->%`(t_2*, t_3*))

  ;; ../spec/3-typing.watsup:133.1-134.36
  rule empty {C : context}:
    `%|-%:%`(C, [], `%->%`([], []))
}
-}
{-
;; ../spec/3-typing.watsup:123.1-123.66
relation Instr_ok: `%|-%:%`(context, instr, functype)
  ;; ../spec/3-typing.watsup:357.1-362.32
  rule store {C : context, in : in, mt : memtype, n : n, n_A : n, n_O : n, nt : numtype, t : valtype}:
    `%|-%:%`(C, STORE_instr(nt, n?, n_A, n_O), `%->%`([I32_valtype (nt <: valtype)], []))
    -- if (C.MEM_context[0] = mt)
    -- if ((2 ^ n_A) <= ($size(t) / 8))
    -- (if (((2 ^ n_A) <= (n / 8)) /\ ((n / 8) < ($size(t) / 8))))?
    -- if ((n? = ?()) \/ (nt = (in <: numtype)))

  ;; ../spec/3-typing.watsup:350.1-355.32
  rule load {C : context, in : in, mt : memtype, n : n, n_A : n, n_O : n, nt : numtype, sx : sx, t : valtype}:
    `%|-%:%`(C, LOAD_instr(nt, ?((n, sx)), n_A, n_O), `%->%`([I32_valtype], [(nt <: valtype)]))
    -- if (C.MEM_context[0] = mt)
    -- if ((2 ^ n_A) <= ($size(t) / 8))
    -- (if (((2 ^ n_A) <= (n / 8)) /\ ((n / 8) < ($size(t) / 8))))?
    -- if ((n? = ?()) \/ (nt = (in <: numtype)))

  ;; ../spec/3-typing.watsup:346.1-348.23
  rule data.drop {C : context, x : idx}:
    `%|-%:%`(C, DATA.DROP_instr(x), `%->%`([], []))
    -- if (C.DATA_context[x] = OK)

  ;; ../spec/3-typing.watsup:341.1-344.23
  rule memory.init {C : context, mt : memtype, x : idx}:
    `%|-%:%`(C, MEMORY.INIT_instr(x), `%->%`([I32_valtype I32_valtype I32_valtype], [I32_valtype]))
    -- if (C.MEM_context[0] = mt)
    -- if (C.DATA_context[x] = OK)

  ;; ../spec/3-typing.watsup:337.1-339.22
  rule memory.copy {C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY.COPY_instr, `%->%`([I32_valtype I32_valtype I32_valtype], [I32_valtype]))
    -- if (C.MEM_context[0] = mt)

  ;; ../spec/3-typing.watsup:333.1-335.22
  rule memory.fill {C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY.FILL_instr, `%->%`([I32_valtype I32_valtype I32_valtype], [I32_valtype]))
    -- if (C.MEM_context[0] = mt)

  ;; ../spec/3-typing.watsup:329.1-331.22
  rule memory.grow {C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY.GROW_instr, `%->%`([I32_valtype], [I32_valtype]))
    -- if (C.MEM_context[0] = mt)

  ;; ../spec/3-typing.watsup:325.1-327.22
  rule memory.size {C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY.SIZE_instr, `%->%`([], [I32_valtype]))
    -- if (C.MEM_context[0] = mt)

  ;; ../spec/3-typing.watsup:320.1-322.23
  rule elem.drop {C : context, rt : reftype, x : idx}:
    `%|-%:%`(C, ELEM.DROP_instr(x), `%->%`([], []))
    -- if (C.ELEM_context[x] = rt)

  ;; ../spec/3-typing.watsup:315.1-318.25
  rule table.init {C : context, lim : limits, rt : reftype, x_1 : idx, x_2 : idx}:
    `%|-%:%`(C, TABLE.INIT_instr(x_1, x_2), `%->%`([I32_valtype I32_valtype I32_valtype], []))
    -- if (C.TABLE_context[x_1] = `%%`(lim, rt))
    -- if (C.ELEM_context[x_2] = rt)

  ;; ../spec/3-typing.watsup:310.1-313.32
  rule table.copy {C : context, lim_1 : limits, lim_2 : limits, rt : reftype, x_1 : idx, x_2 : idx}:
    `%|-%:%`(C, TABLE.COPY_instr(x_1, x_2), `%->%`([I32_valtype I32_valtype I32_valtype], []))
    -- if (C.TABLE_context[x_1] = `%%`(lim_1, rt))
    -- if (C.TABLE_context[x_2] = `%%`(lim_2, rt))

  ;; ../spec/3-typing.watsup:306.1-308.28
  rule table.fill {C : context, lim : limits, rt : reftype, x : idx}:
    `%|-%:%`(C, TABLE.FILL_instr(x), `%->%`([I32_valtype (rt <: valtype) I32_valtype], []))
    -- if (C.TABLE_context[x] = `%%`(lim, rt))

  ;; ../spec/3-typing.watsup:302.1-304.28
  rule table.grow {C : context, lim : limits, rt : reftype, x : idx}:
    `%|-%:%`(C, TABLE.GROW_instr(x), `%->%`([(rt <: valtype) I32_valtype], [I32_valtype]))
    -- if (C.TABLE_context[x] = `%%`(lim, rt))

  ;; ../spec/3-typing.watsup:298.1-300.24
  rule table.size {C : context, tt : tabletype, x : idx}:
    `%|-%:%`(C, TABLE.SIZE_instr(x), `%->%`([], [I32_valtype]))
    -- if (C.TABLE_context[x] = tt)

  ;; ../spec/3-typing.watsup:294.1-296.28
  rule table.set {C : context, lim : limits, rt : reftype, x : idx}:
    `%|-%:%`(C, TABLE.SET_instr(x), `%->%`([I32_valtype (rt <: valtype)], []))
    -- if (C.TABLE_context[x] = `%%`(lim, rt))

  ;; ../spec/3-typing.watsup:290.1-292.28
  rule table.get {C : context, lim : limits, rt : reftype, x : idx}:
    `%|-%:%`(C, TABLE.GET_instr(x), `%->%`([I32_valtype], [(rt <: valtype)]))
    -- if (C.TABLE_context[x] = `%%`(lim, rt))

  ;; ../spec/3-typing.watsup:285.1-287.28
  rule global.set {C : context, t : valtype, x : idx}:
    `%|-%:%`(C, GLOBAL.SET_instr(x), `%->%`([t], []))
    -- if (C.GLOBAL_context[x] = `MUT%?%`(?(()), t))

  ;; ../spec/3-typing.watsup:281.1-283.29
  rule global.get {C : context, t : valtype, x : idx}:
    `%|-%:%`(C, GLOBAL.GET_instr(x), `%->%`([], [t]))
    -- if (C.GLOBAL_context[x] = `MUT%?%`(?(()), t))

  ;; ../spec/3-typing.watsup:276.1-278.23
  rule local.tee {C : context, t : valtype, x : idx}:
    `%|-%:%`(C, LOCAL.TEE_instr(x), `%->%`([t], [t]))
    -- if (C.LOCAL_context[x] = t)

  ;; ../spec/3-typing.watsup:272.1-274.23
  rule local.set {C : context, t : valtype, x : idx}:
    `%|-%:%`(C, LOCAL.SET_instr(x), `%->%`([t], []))
    -- if (C.LOCAL_context[x] = t)

  ;; ../spec/3-typing.watsup:268.1-270.23
  rule local.get {C : context, t : valtype, x : idx}:
    `%|-%:%`(C, LOCAL.GET_instr(x), `%->%`([], [t]))
    -- if (C.LOCAL_context[x] = t)

  ;; ../spec/3-typing.watsup:264.1-265.31
  rule ref.is_null {C : context, rt : reftype}:
    `%|-%:%`(C, REF.IS_NULL_instr, `%->%`([(rt <: valtype)], [I32_valtype]))

  ;; ../spec/3-typing.watsup:260.1-262.23
  rule ref.func {C : context, ft : functype, x : idx}:
    `%|-%:%`(C, REF.FUNC_instr(x), `%->%`([], [FUNCREF_valtype]))
    -- if (C.FUNC_context[x] = ft)

  ;; ../spec/3-typing.watsup:257.1-258.35
  rule ref.null {C : context, rt : reftype}:
    `%|-%:%`(C, REF.NULL_instr(rt), `%->%`([], [(rt <: valtype)]))

  ;; ../spec/3-typing.watsup:252.1-254.22
  rule convert-f {C : context, fn_1 : fn, fn_2 : fn}:
    `%|-%:%`(C, CVTOP_instr((fn_1 <: numtype), CONVERT_cvtop, (fn_2 <: numtype), ?()), `%->%`([(fn_2 <: valtype)], [(fn_1 <: valtype)]))
    -- if (fn_1 =/= fn_2)

  ;; ../spec/3-typing.watsup:247.1-250.52
  rule convert-i {C : context, in_1 : in, in_2 : in, sx : sx}:
    `%|-%:%`(C, CVTOP_instr((in_1 <: numtype), CONVERT_cvtop, (in_2 <: numtype), sx?), `%->%`([(in_2 <: valtype)], [(in_1 <: valtype)]))
    -- if (in_1 =/= in_2)
    -- if ((sx? = ?()) <=> ($size(in_1 <: valtype) > $size(in_2 <: valtype)))

  ;; ../spec/3-typing.watsup:242.1-245.34
  rule reinterpret {C : context, nt_1 : numtype, nt_2 : numtype}:
    `%|-%:%`(C, CVTOP_instr(nt_1, REINTERPRET_cvtop, nt_2, ?()), `%->%`([(nt_2 <: valtype)], [(nt_1 <: valtype)]))
    -- if (nt_1 =/= nt_2)
    -- if ($size(nt_1 <: valtype) = $size(nt_2 <: valtype))

  ;; ../spec/3-typing.watsup:238.1-240.23
  rule extend {C : context, n : n, nt : numtype}:
    `%|-%:%`(C, EXTEND_instr(nt, n), `%->%`([(nt <: valtype)], [(nt <: valtype)]))
    -- if (n <= $size(nt <: valtype))

  ;; ../spec/3-typing.watsup:234.1-235.37
  rule relop {C : context, nt : numtype, relop : relop_numtype}:
    `%|-%:%`(C, RELOP_instr(nt, relop), `%->%`([(nt <: valtype) (nt <: valtype)], [I32_valtype]))

  ;; ../spec/3-typing.watsup:231.1-232.36
  rule testop {C : context, nt : numtype, testop : testop_numtype}:
    `%|-%:%`(C, TESTOP_instr(nt, testop), `%->%`([(nt <: valtype)], [I32_valtype]))

  ;; ../spec/3-typing.watsup:228.1-229.36
  rule binop {C : context, binop : binop_numtype, nt : numtype}:
    `%|-%:%`(C, BINOP_instr(nt, binop), `%->%`([(nt <: valtype) (nt <: valtype)], [(nt <: valtype)]))

  ;; ../spec/3-typing.watsup:225.1-226.31
  rule unop {C : context, nt : numtype, unop : unop_numtype}:
    `%|-%:%`(C, UNOP_instr(nt, unop), `%->%`([(nt <: valtype)], [(nt <: valtype)]))

  ;; ../spec/3-typing.watsup:222.1-223.37
  rule const {C : context, c_nt : c_numtype, nt : numtype}:
    `%|-%:%`(C, CONST_instr(nt, c_nt), `%->%`([], [(nt <: valtype)]))

  ;; ../spec/3-typing.watsup:216.1-219.26
  rule call_indirect {C : context, ft : functype, lim : limits, t_1 : valtype, t_2 : valtype, x : idx}:
    `%|-%:%`(C, CALL_INDIRECT_instr(x, ft), `%->%`(t_1* :: [I32_valtype], t_2*))
    -- if (C.TABLE_context[x] = `%%`(lim, FUNCREF_reftype))
    -- if (ft = `%->%`(t_1*, t_2*))

  ;; ../spec/3-typing.watsup:212.1-214.33
  rule call {C : context, t_1 : valtype, t_2 : valtype, x : idx}:
    `%|-%:%`(C, CALL_instr(x), `%->%`(t_1*, t_2*))
    -- if (C.FUNC_context[x] = `%->%`(t_1*, t_2*))

  ;; ../spec/3-typing.watsup:208.1-210.24
  rule return {C : context, t : valtype, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, RETURN_instr, `%->%`(t_1* :: t*, t_2*))
    -- if (C.RETURN_context = ?(t*))

  ;; ../spec/3-typing.watsup:203.1-206.42
  rule br_table {C : context, l : labelidx, l' : labelidx, t : valtype, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, BR_TABLE_instr(l*, l'), `%->%`(t_1* :: t*, t_2*))
    -- (Resulttype_sub: `|-%<:%`(t*, C.LABEL_context[l]))*
    -- Resulttype_sub: `|-%<:%`(t*, C.LABEL_context[l'])

  ;; ../spec/3-typing.watsup:199.1-201.24
  rule br_if {C : context, l : labelidx, t : valtype}:
    `%|-%:%`(C, BR_IF_instr(l), `%->%`(t* :: [I32_valtype], t*))
    -- if (C.LABEL_context[l] = t*)

  ;; ../spec/3-typing.watsup:195.1-197.24
  rule br {C : context, l : labelidx, t : valtype, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, BR_instr(l), `%->%`(t_1* :: t*, t_2*))
    -- if (C.LABEL_context[l] = t*)

  ;; ../spec/3-typing.watsup:188.1-192.59
  rule if {C : context, bt : blocktype, instr_1 : instr, instr_2 : instr, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, IF_instr(bt, instr_1*, instr_2*), `%->%`(t_1*, [t_2]))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*, [t_2]))
    -- InstrSeq_ok: `%|-%:%`(C ++ {FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2]*, RETURN ?()}, instr_1*, `%->%`(t_1*, t_2*))
    -- InstrSeq_ok: `%|-%:%`(C ++ {FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2]*, RETURN ?()}, instr_2*, `%->%`(t_1*, t_2*))

  ;; ../spec/3-typing.watsup:183.1-186.56
  rule loop {C : context, bt : blocktype, instr : instr, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, LOOP_instr(bt, instr*), `%->%`(t_1*, t_2*))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*, t_2*))
    -- InstrSeq_ok: `%|-%:%`(C ++ {FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_1]*, RETURN ?()}, instr*, `%->%`(t_1*, [t_2]))

  ;; ../spec/3-typing.watsup:178.1-181.57
  rule block {C : context, bt : blocktype, instr : instr, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, BLOCK_instr(bt, instr*), `%->%`(t_1*, t_2*))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*, t_2*))
    -- InstrSeq_ok: `%|-%:%`(C ++ {FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2]*, RETURN ?()}, instr*, `%->%`(t_1*, t_2*))

  ;; ../spec/3-typing.watsup:166.1-169.37
  rule select-impl {C : context, numtype : numtype, t : valtype, t' : valtype, vectype : vectype}:
    `%|-%:%`(C, SELECT_instr(?()), `%->%`([t t I32_valtype], [t]))
    -- Valtype_sub: `|-%<:%`(t, t')
    -- if ((t' = (numtype <: valtype)) \/ (t' = (vectype <: valtype)))

  ;; ../spec/3-typing.watsup:163.1-164.31
  rule select-expl {C : context, t : valtype}:
    `%|-%:%`(C, SELECT_instr(?(t)), `%->%`([t t I32_valtype], [t]))

  ;; ../spec/3-typing.watsup:159.1-160.27
  rule drop {C : context, t : valtype}:
    `%|-%:%`(C, DROP_instr, `%->%`([t], []))

  ;; ../spec/3-typing.watsup:156.1-157.32
  rule nop {C : context}:
    `%|-%:%`(C, NOP_instr, `%->%`([], []))

  ;; ../spec/3-typing.watsup:153.1-154.34
  rule unreachable {C : context, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, UNREACHABLE_instr, `%->%`(t_1*, t_2*))
-}

{-
;; ../spec/3-typing.watsup:124.1-124.67
relation InstrSeq_ok: `%|-%:%`(context, instr*, functype)
  ;; ../spec/3-typing.watsup:148.1-150.45
  rule frame {C : context, instr : instr, t : valtype, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, instr*, `%->%`(t* :: t_1*, t* :: t_2*))
    -- InstrSeq_ok: `%|-%:%`(C, instr*, `%->%`(t_1*, t_2*))

  ;; ../spec/3-typing.watsup:141.1-146.38
  rule weak {C : context, instr : instr, t'_1 : valtype, t'_2 : valtype, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, instr*, `%->%`([t'_1], t'_2*))
    -- InstrSeq_ok: `%|-%:%`(C, instr*, `%->%`(t_1*, t_2*))
    -- Resulttype_sub: `|-%<:%`(t'_1*, t_1*)
    -- Resulttype_sub: `|-%<:%`(t_2*, t'_2*)

  ;; ../spec/3-typing.watsup:136.1-139.46
  rule seq {C : context, instr_1 : instr, instr_2 : instr, t_1 : valtype, t_2 : valtype, t_3 : valtype}:
    `%|-%:%`(C, [instr_1] :: instr_2*, `%->%`(t_1*, t_3*))
    -- Instr_ok: `%|-%:%`(C, instr_1, `%->%`(t_1*, t_2*))
    -- InstrSeq_ok: `%|-%:%`(C, [instr_2], `%->%`(t_2*, t_3*))

  ;; ../spec/3-typing.watsup:133.1-134.36
  rule empty {C : context}:
    `%|-%:%`(C, [], `%->%`([], []))
-}


{-
;; ../spec/3-typing.watsup:125.1-125.71
relation Expr_ok: `%|-%:%`(context, expr, resulttype)
  ;; ../spec/3-typing.watsup:128.1-130.46
  rule _ {C : context, instr : instr, t : valtype}:
    `%|-%:%`(C, instr*, t*)
    -- InstrSeq_ok: `%|-%:%`(C, instr*, `%->%`([], t*))
-}


{-
;; ../spec/3-typing.watsup:367.1-367.78
relation Instr_const: `%|-%CONST`(context, instr)
  ;; ../spec/3-typing.watsup:380.1-382.32
  rule global.get {C : context, t : valtype, x : idx}:
    `%|-%CONST`(C, GLOBAL.GET_instr(x))
    -- if (C.GLOBAL_context[x] = `MUT%?%`(?(), t))

  ;; ../spec/3-typing.watsup:377.1-378.26
  rule ref.func {C : context, x : idx}:
    `%|-%CONST`(C, REF.FUNC_instr(x))

  ;; ../spec/3-typing.watsup:374.1-375.27
  rule ref.null {C : context, rt : reftype}:
    `%|-%CONST`(C, REF.NULL_instr(rt))

  ;; ../spec/3-typing.watsup:371.1-372.26
  rule const {C : context, c : c_numtype, nt : numtype}:
    `%|-%CONST`(C, CONST_instr(nt, c))
-}


{-
;; ../spec/3-typing.watsup:368.1-368.77
relation Expr_const: `%|-%CONST`(context, expr)
  ;; ../spec/3-typing.watsup:385.1-386.38
  rule _ {C : context, instr : instr}:
    `%|-%CONST`(C, instr*)
    -- (Instr_const: `%|-%CONST`(C, instr))*
-}


{-
;; ../spec/3-typing.watsup:369.1-369.78
relation Expr_ok_const: `%|-%:%CONST`(context, expr, valtype)
  ;; ../spec/3-typing.watsup:389.1-392.33
  rule _ {C : context, expr : expr, t : valtype}:
    `%|-%:%CONST`(C, expr, t)
    -- Expr_ok: `%|-%:%`(C, expr, [t])
    -- Expr_const: `%|-%CONST`(C, expr)
-}


{-
;; ../spec/3-typing.watsup:397.1-397.73
relation Func_ok: `%|-%:%`(context, func, functype)
  ;; ../spec/3-typing.watsup:408.1-412.75
  rule _ {C : context, expr : expr, ft : functype, t : valtype, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, FUNC(ft, t*, expr), ft)
    -- if (ft = `%->%`(t_1*, t_2*))
    -- Functype_ok: `|-%:OK`(ft)
    -- Expr_ok: `%|-%:%`(C ++ {FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL t_1* :: t*, LABEL [], RETURN ?()} ++ {FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2*], RETURN ?()} ++ {FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [], RETURN ?(t_2*)}, expr, t_2*)
-}


{-
;; ../spec/3-typing.watsup:398.1-398.75
relation Global_ok: `%|-%:%`(context, global, globaltype)
  ;; ../spec/3-typing.watsup:414.1-418.40
  rule _ {C : context, expr : expr, gt : globaltype, t : valtype}:
    `%|-%:%`(C, GLOBAL(gt, expr), gt)
    -- Globaltype_ok: `|-%:OK`(gt)
    -- if (gt = `MUT%?%`(?(()), t))
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, t)
-}


{-
;; ../spec/3-typing.watsup:399.1-399.74
relation Table_ok: `%|-%:%`(context, table, tabletype)
  ;; ../spec/3-typing.watsup:420.1-422.30
  rule _ {C : context, tt : tabletype}:
    `%|-%:%`(C, TABLE(tt), tt)
    -- Tabletype_ok: `|-%:OK`(tt)
-}


{-
;; ../spec/3-typing.watsup:400.1-400.72
relation Mem_ok: `%|-%:%`(context, mem, memtype)
  ;; ../spec/3-typing.watsup:424.1-426.28
  rule _ {C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY(mt), mt)
    -- Memtype_ok: `|-%:OK`(mt)
-}


{-
;; ../spec/3-typing.watsup:403.1-403.77
relation Elemmode_ok: `%|-%:%`(context, elemmode, reftype)
  ;; ../spec/3-typing.watsup:443.1-444.20
  rule declare {C : context, rt : reftype}:
    `%|-%:%`(C, DECLARE_elemmode, rt)

  ;; ../spec/3-typing.watsup:438.1-441.45
  rule active {C : context, expr : expr, lim : limits, rt : reftype, x : idx}:
    `%|-%:%`(C, TABLE_elemmode(x, expr), rt)
    -- if (C.TABLE_context[x] = `%%`(lim, rt))
    -- (Expr_ok_const: `%|-%:%CONST`(C, expr, I32_valtype))*
-}


{-
;; ../spec/3-typing.watsup:401.1-401.73
relation Elem_ok: `%|-%:%`(context, elem, reftype)
  ;; ../spec/3-typing.watsup:428.1-431.40
  rule _ {C : context, elemmode : elemmode, expr : expr, rt : reftype}:
    `%|-%:%`(C, ELEM(rt, expr*, elemmode?), rt)
    -- (Expr_ok: `%|-%:%`(C, expr, [(rt <: valtype)]))*
    -- (Elemmode_ok: `%|-%:%`(C, elemmode, rt))?
-}


{-
;; ../spec/3-typing.watsup:404.1-404.77
relation Datamode_ok: `%|-%:OK`(context, datamode)
  ;; ../spec/3-typing.watsup:446.1-449.45
  rule _ {C : context, expr : expr, mt : memtype}:
    `%|-%:OK`(C, MEMORY_datamode(0, expr))
    -- if (C.MEM_context[0] = mt)
    -- (Expr_ok_const: `%|-%:%CONST`(C, expr, I32_valtype))*
-}


{-
;; ../spec/3-typing.watsup:402.1-402.73
relation Data_ok: `%|-%:OK`(context, data)
  ;; ../spec/3-typing.watsup:434.1-436.40
  rule _ {C : context, b : byte, datamode : datamode}:
    `%|-%:OK`(C, DATA(b**, datamode?))
    -- (Datamode_ok: `%|-%:OK`(C, datamode))?
-}


{-
;; ../spec/3-typing.watsup:405.1-405.74
relation Start_ok: `%|-%:OK`(context, start)
  ;; ../spec/3-typing.watsup:451.1-453.39
  rule _ {C : context, x : idx}:
    `%|-%:OK`(C, START(x))
    -- if (C.FUNC_context[x] = `%->%`([], []))
-}


{-
;; ../spec/3-typing.watsup:456.1-456.80
relation Import_ok: `%|-%:%`(context, import, externtype)
  ;; ../spec/3-typing.watsup:460.1-462.31
  rule _ {C : context, name_1 : name, name_2 : name, xt : externtype}:
    `%|-%:%`(C, IMPORT(name_1, name_2, xt), xt)
    -- Externtype_ok: `|-%:OK`(xt)
-}


{-
;; ../spec/3-typing.watsup:458.1-458.83
relation Externuse_ok: `%|-%:%`(context, externuse, externtype)
  ;; ../spec/3-typing.watsup:480.1-482.22
  rule mem {C : context, mt : memtype, x : idx}:
    `%|-%:%`(C, MEMORY_externuse(x), MEMORY_externtype(mt))
    -- if (C.MEM_context[x] = mt)

  ;; ../spec/3-typing.watsup:476.1-478.24
  rule table {C : context, tt : tabletype, x : idx}:
    `%|-%:%`(C, TABLE_externuse(x), TABLE_externtype(tt))
    -- if (C.TABLE_context[x] = tt)

  ;; ../spec/3-typing.watsup:472.1-474.25
  rule global {C : context, gt : globaltype, x : idx}:
    `%|-%:%`(C, GLOBAL_externuse(x), GLOBAL_externtype(gt))
    -- if (C.GLOBAL_context[x] = gt)

  ;; ../spec/3-typing.watsup:468.1-470.23
  rule func {C : context, ft : functype, x : idx}:
    `%|-%:%`(C, FUNC_externuse(x), FUNC_externtype(ft))
    -- if (C.FUNC_context[x] = ft)
-}


{-
;; ../spec/3-typing.watsup:457.1-457.80
relation Export_ok: `%|-%:%`(context, export, externtype)
  ;; ../spec/3-typing.watsup:464.1-466.39
  rule _ {C : context, externuse : externuse, name : name, xt : externtype}:
    `%|-%:%`(C, EXPORT(name, externuse), xt)
    -- Externuse_ok: `%|-%:%`(C, externuse, xt)
-}


{-
;; ../spec/3-typing.watsup:485.1-485.62
relation Module_ok: `|-%:OK`(module)
  ;; ../spec/3-typing.watsup:487.1-499.22
  rule _ {C : context, data : data, elem : elem, export : export, ft : functype, func : func, global : global, gt : globaltype, import : import, mem : mem, mt : memtype, n : n, rt : reftype, start : start, table : table, tt : tabletype}:
    `|-%:OK`(MODULE(import*, func*, global*, table*, mem*, elem*, data^n, start*, export*))
    -- (Func_ok: `%|-%:%`(C, func, ft))*
    -- (Global_ok: `%|-%:%`(C, global, gt))*
    -- (Table_ok: `%|-%:%`(C, table, tt))*
    -- (Mem_ok: `%|-%:%`(C, mem, mt))*
    -- (Elem_ok: `%|-%:%`(C, elem, rt))*
    -- (Data_ok: `%|-%:OK`(C, data))^n
    -- (Start_ok: `%|-%:OK`(C, start))*
    -- if (C = {FUNC ft*, GLOBAL gt*, TABLE tt*, MEM mt*, ELEM rt*, DATA OK^n, LOCAL [], LABEL [], RETURN ?()})
    -- if (|mem*| <= 1)
    -- if (|start*| <= 1)
-}


{-
;; ../spec/4-runtime.watsup:3.1-3.39
syntax addr = nat
-}
type Addr = Natural

{-
;; ../spec/4-runtime.watsup:4.1-4.53
syntax funcaddr = addr
-}
type Funcaddr = Addr

{-
;; ../spec/4-runtime.watsup:5.1-5.53
syntax globaladdr = addr
-}
type Globaladdr = Addr

{-
;; ../spec/4-runtime.watsup:6.1-6.51
syntax tableaddr = addr
-}
type Tableaddr = Addr

{-
;; ../spec/4-runtime.watsup:7.1-7.50
syntax memaddr = addr
-}
type Memaddr = Addr

{-
;; ../spec/4-runtime.watsup:8.1-8.49
syntax elemaddr = addr
-}
type Elemaddr = Addr

{-
;; ../spec/4-runtime.watsup:9.1-9.49
syntax dataaddr = addr
-}
type Dataaddr = Addr

{-
;; ../spec/4-runtime.watsup:10.1-10.51
syntax labeladdr = addr
-}
type Labeladdr = Addr

{-
;; ../spec/4-runtime.watsup:11.1-11.49
syntax hostaddr = addr
-}
type Hostaddr = Addr

{-
;; ../spec/4-runtime.watsup:24.1-25.24
syntax num =
  | CONST(numtype, c_numtype)
-}
data Num
 = Num_CONST (Numtype, C_numtype)

{-
;; ../spec/4-runtime.watsup:26.1-27.67
syntax ref =
  | REF.NULL(reftype)
  | REF.FUNC_ADDR(funcaddr)
  | REF.HOST_ADDR(hostaddr)
-}
data Ref
 = Ref_REF_NULL Reftype
 | Ref_REF_FUNC_ADDR Funcaddr
 | Ref_REF_HOST_ADDR Hostaddr

{-
;; ../spec/4-runtime.watsup:28.1-29.10
syntax val =
  | num
  | ref
-}
data Val
 = Val_of_Num Num
 | Val_of_Ref Ref

{-
;; ../spec/4-runtime.watsup:31.1-32.18
syntax result =
  | _VALS(val*)
  | TRAP
-}
data Result
 = Result_VALS [Val]
 | Result_TRAP

{-
;; ../spec/4-runtime.watsup:38.1-39.66
syntax externval =
  | FUNC(funcaddr)
  | GLOBAL(globaladdr)
  | TABLE(tableaddr)
  | MEM(memaddr)
-}
data Externval
 = Externval_FUNC Funcaddr
 | Externval_GLOBAL Globaladdr
 | Externval_TABLE Tableaddr
 | Externval_MEM Memaddr

{-
;; ../spec/4-runtime.watsup:44.1-44.44
def default_ : valtype -> val
  ;; ../spec/4-runtime.watsup:49.1-49.34
  def {rt : reftype} default_(rt <: valtype) = REF.NULL_val(rt)
  ;; ../spec/4-runtime.watsup:48.1-48.35
  def default_(F64_valtype) = CONST_val(F64_numtype, 0)
  ;; ../spec/4-runtime.watsup:47.1-47.35
  def default_(F32_valtype) = CONST_val(F32_numtype, 0)
  ;; ../spec/4-runtime.watsup:46.1-46.35
  def default_(I64_valtype) = CONST_val(I64_numtype, 0)
  ;; ../spec/4-runtime.watsup:45.1-45.35
  def default_(I32_valtype) = CONST_val(I32_numtype, 0)
-}
default_ :: Valtype -> Val
default_ (Valtype_of_Reftype rt) = (Val_of_Ref (Ref_REF_NULL rt))
default_ (Valtype_of_Numtype Numtype_F64) = (Val_of_Num (Num_CONST (Numtype_F64, 0)))
default_ (Valtype_of_Numtype Numtype_F32) = (Val_of_Num (Num_CONST (Numtype_F32, 0)))
default_ (Valtype_of_Numtype Numtype_I64) = (Val_of_Num (Num_CONST (Numtype_I64, 0)))
default_ (Valtype_of_Numtype Numtype_I32) = (Val_of_Num (Num_CONST (Numtype_I32, 0)))

{-
;; ../spec/4-runtime.watsup:60.1-60.71
syntax exportinst = EXPORT(name, externval)
-}
type Exportinst = {- mixop: EXPORT -} (Name, Externval)

{-
;; ../spec/4-runtime.watsup:70.1-77.25
syntax moduleinst = {FUNC funcaddr*, GLOBAL globaladdr*, TABLE tableaddr*, MEM memaddr*, ELEM elemaddr*, DATA dataaddr*, EXPORT exportinst*}
-}
data Moduleinst = MkModuleinst
 { fUNC :: [Funcaddr]
 , gLOBAL :: [Globaladdr]
 , tABLE :: [Tableaddr]
 , mEM :: [Memaddr]
 , eLEM :: [Elemaddr]
 , dATA :: [Dataaddr]
 , eXPORT :: [Exportinst]
 }

{-
;; ../spec/4-runtime.watsup:54.1-54.66
syntax funcinst = `%;%`(moduleinst, func)
-}
type Funcinst = {- mixop: `%;%` -} (Moduleinst, Func)

{-
;; ../spec/4-runtime.watsup:55.1-55.53
syntax globalinst = val
-}
type Globalinst = Val

{-
;; ../spec/4-runtime.watsup:56.1-56.52
syntax tableinst = ref*
-}
type Tableinst = [Ref]

{-
;; ../spec/4-runtime.watsup:57.1-57.52
syntax meminst = byte*
-}
type Meminst = [Byte]

{-
;; ../spec/4-runtime.watsup:58.1-58.53
syntax eleminst = ref*
-}
type Eleminst = [Ref]

{-
;; ../spec/4-runtime.watsup:59.1-59.51
syntax datainst = byte*
-}
type Datainst = [Byte]

{-
;; ../spec/4-runtime.watsup:62.1-68.21
syntax store = {FUNC funcinst*, GLOBAL globalinst*, TABLE tableinst*, MEM meminst*, ELEM eleminst*, DATA datainst*}
-}
data Store = MkStore
 { fUNC :: [Funcinst]
 , gLOBAL :: [Globalinst]
 , tABLE :: [Tableinst]
 , mEM :: [Meminst]
 , eLEM :: [Eleminst]
 , dATA :: [Datainst]
 }

{-
;; ../spec/4-runtime.watsup:79.1-81.24
syntax frame = {LOCAL val*, MODULE moduleinst}
-}
data Frame = MkFrame
 { lOCAL :: [Val]
 , mODULE :: Moduleinst
 }

{-
;; ../spec/4-runtime.watsup:82.1-82.47
syntax state = `%;%`(store, frame)
-}
type State = {- mixop: `%;%` -} (Store, Frame)

{-
;; ../spec/4-runtime.watsup:130.1-137.5
rec {

;; ../spec/4-runtime.watsup:130.1-137.5
syntax admininstr =
  | instr
  | REF.FUNC_ADDR(funcaddr)
  | REF.HOST_ADDR(hostaddr)
  | CALL_ADDR(funcaddr)
  | LABEL_(n, instr*, admininstr*)
  | FRAME_(n, frame, admininstr*)
  | TRAP
}
-}
{-
;; ../spec/4-runtime.watsup:130.1-137.5
syntax admininstr =
  | instr
  | REF.FUNC_ADDR(funcaddr)
  | REF.HOST_ADDR(hostaddr)
  | CALL_ADDR(funcaddr)
  | LABEL_(n, instr*, admininstr*)
  | FRAME_(n, frame, admininstr*)
  | TRAP
-}
data Admininstr
 = Admininstr_of_Instr Instr
 | Admininstr_REF_FUNC_ADDR Funcaddr
 | Admininstr_REF_HOST_ADDR Hostaddr
 | Admininstr_CALL_ADDR Funcaddr
 | Admininstr_LABEL_ (N, [Instr], [Admininstr])
 | Admininstr_FRAME_ (N, Frame, [Admininstr])
 | Admininstr_TRAP

{-
;; ../spec/4-runtime.watsup:83.1-83.62
syntax config = `%;%`(state, admininstr*)
-}
type Config = {- mixop: `%;%` -} (State, [Admininstr])

{-
;; ../spec/4-runtime.watsup:98.1-98.59
def funcaddr : state -> funcaddr*
  ;; ../spec/4-runtime.watsup:99.1-99.38
  def {f : frame, s : store} funcaddr(`%;%`(s, f)) = f.MODULE_frame.FUNC_moduleinst
-}
funcaddr :: State -> [Funcaddr]
funcaddr (s, f) = f.mODULE.fUNC

{-
;; ../spec/4-runtime.watsup:101.1-101.52
def funcinst : state -> funcinst*
  ;; ../spec/4-runtime.watsup:102.1-102.31
  def {f : frame, s : store} funcinst(`%;%`(s, f)) = s.FUNC_store
-}
funcinst :: State -> [Funcinst]
funcinst (s, f) = s.fUNC

{-
;; ../spec/4-runtime.watsup:104.1-104.61
def func : (state, funcidx) -> funcinst
  ;; ../spec/4-runtime.watsup:105.1-105.48
  def {f : frame, s : store, x : idx} func(`%;%`(s, f), x) = s.FUNC_store[f.MODULE_frame.FUNC_moduleinst[x]]
-}
func :: (State, Funcidx) -> Funcinst
func ((s, f), x) = (s.fUNC !! (fromIntegral (f.mODULE.fUNC !! (fromIntegral x))))

{-
;; ../spec/4-runtime.watsup:107.1-107.59
def local : (state, localidx) -> val
  ;; ../spec/4-runtime.watsup:108.1-108.35
  def {f : frame, s : store, x : idx} local(`%;%`(s, f), x) = f.LOCAL_frame[x]
-}
local :: (State, Localidx) -> Val
local ((s, f), x) = (f.lOCAL !! (fromIntegral x))

{-
;; ../spec/4-runtime.watsup:110.1-110.69
def global : (state, globalidx) -> globalinst
  ;; ../spec/4-runtime.watsup:111.1-111.54
  def {f : frame, s : store, x : idx} global(`%;%`(s, f), x) = s.GLOBAL_store[f.MODULE_frame.GLOBAL_moduleinst[x]]
-}
global :: (State, Globalidx) -> Globalinst
global ((s, f), x) = (s.gLOBAL !! (fromIntegral (f.mODULE.gLOBAL !! (fromIntegral x))))

{-
;; ../spec/4-runtime.watsup:113.1-113.65
def table : (state, tableidx) -> tableinst
  ;; ../spec/4-runtime.watsup:114.1-114.51
  def {f : frame, s : store, x : idx} table(`%;%`(s, f), x) = s.TABLE_store[f.MODULE_frame.TABLE_moduleinst[x]]
-}
table :: (State, Tableidx) -> Tableinst
table ((s, f), x) = (s.tABLE !! (fromIntegral (f.mODULE.tABLE !! (fromIntegral x))))

{-
;; ../spec/4-runtime.watsup:116.1-116.62
def elem : (state, tableidx) -> eleminst
  ;; ../spec/4-runtime.watsup:117.1-117.48
  def {f : frame, s : store, x : idx} elem(`%;%`(s, f), x) = s.ELEM_store[f.MODULE_frame.ELEM_moduleinst[x]]
-}
elem :: (State, Tableidx) -> Eleminst
elem ((s, f), x) = (s.eLEM !! (fromIntegral (f.mODULE.eLEM !! (fromIntegral x))))

{-
;; ../spec/4-runtime.watsup:119.1-119.76
def with_local : (state, localidx, val) -> state
  ;; ../spec/4-runtime.watsup:120.1-120.50
  def {f : frame, s : store, v : val, x : idx} with_local(`%;%`(s, f), x, v) = `%;%`(s, f[LOCAL[x] = v])
-}
with_local :: (State, Localidx, Val) -> State
with_local ((s, f), x, v) = (s, undefined {- f[LOCAL[x] = v] -})

{-
;; ../spec/4-runtime.watsup:122.1-122.79
def with_global : (state, globalidx, val) -> state
  ;; ../spec/4-runtime.watsup:123.1-123.69
  def {f : frame, s : store, v : val, x : idx} with_global(`%;%`(s, f), x, v) = `%;%`(s[GLOBAL[f.MODULE_frame.GLOBAL_moduleinst[x]] = v], f)
-}
with_global :: (State, Globalidx, Val) -> State
with_global ((s, f), x, v) = (undefined {- s[GLOBAL[f.MODULE_frame.GLOBAL_moduleinst[x]] = v] -}, f)

{-
;; ../spec/4-runtime.watsup:125.1-125.84
def with_table : (state, tableidx, n, ref) -> state
  ;; ../spec/4-runtime.watsup:126.1-126.72
  def {f : frame, i : nat, r : ref, s : store, x : idx} with_table(`%;%`(s, f), x, i, r) = `%;%`(s[TABLE[f.MODULE_frame.TABLE_moduleinst[x]][i] = r], f)
-}
with_table :: (State, Tableidx, N, Ref) -> State
with_table ((s, f), x, i, r) = (undefined {- s[TABLE[f.MODULE_frame.TABLE_moduleinst[x]][i] = r] -}, f)

{-
;; ../spec/4-runtime.watsup:139.1-142.21
rec {

;; ../spec/4-runtime.watsup:139.1-142.21
syntax E =
  | _HOLE
  | _SEQ(val*, E, instr*)
  | LABEL_(n, instr*, E)
}
-}
{-
;; ../spec/4-runtime.watsup:139.1-142.21
syntax E =
  | _HOLE
  | _SEQ(val*, E, instr*)
  | LABEL_(n, instr*, E)
-}
data E
 = E_HOLE
 | E_SEQ ([Val], E, [Instr])
 | E_LABEL_ (N, [Instr], E)

{-
;; ../spec/5-reduction.watsup:4.1-4.63
relation Step_pure: `%~>%`(admininstr*, admininstr*)
  ;; ../spec/5-reduction.watsup:86.1-88.18
  rule br_table-ge {i : nat, l : labelidx, l' : labelidx}:
    `%~>%`([CONST_admininstr(I32_numtype, i) BR_TABLE_admininstr(l*, l')], [BR_admininstr(l')])
    -- if (i >= |l*|)

  ;; ../spec/5-reduction.watsup:82.1-84.17
  rule br_table-lt {i : nat, l : labelidx, l' : labelidx}:
    `%~>%`([CONST_admininstr(I32_numtype, i) BR_TABLE_admininstr(l*, l')], [BR_admininstr(l*[i])])
    -- if (i < |l*|)

  ;; ../spec/5-reduction.watsup:77.1-79.14
  rule br_if-false {c : c_numtype, l : labelidx}:
    `%~>%`([CONST_admininstr(I32_numtype, c) BR_IF_admininstr(l)], [])
    -- if (c = 0)

  ;; ../spec/5-reduction.watsup:73.1-75.16
  rule br_if-true {c : c_numtype, l : labelidx}:
    `%~>%`([CONST_admininstr(I32_numtype, c) BR_IF_admininstr(l)], [BR_admininstr(l)])
    -- if (c =/= 0)

  ;; ../spec/5-reduction.watsup:69.1-70.65
  rule br-succ {instr : instr, instr' : instr, l : labelidx, n : n, val : val}:
    `%~>%`([LABEL__admininstr(n, instr'*, (val <: admininstr)* :: [BR_admininstr(l + 1)] :: (instr <: admininstr)*)], (val <: admininstr)* :: [BR_admininstr(l)])

  ;; ../spec/5-reduction.watsup:66.1-67.69
  rule br-zero {instr : instr, instr' : instr, n : n, val : val, val' : val}:
    `%~>%`([LABEL__admininstr(n, instr'*, (val' <: admininstr)* :: (val <: admininstr)^n :: [BR_admininstr(0)] :: (instr <: admininstr)*)], (val <: admininstr)^n :: (instr' <: admininstr)*)

  ;; ../spec/5-reduction.watsup:61.1-63.14
  rule if-false {bt : blocktype, c : c_numtype, instr_1 : instr, instr_2 : instr}:
    `%~>%`([CONST_admininstr(I32_numtype, c) IF_admininstr(bt, instr_1*, instr_2*)], [BLOCK_admininstr(bt, instr_2*)])
    -- if (c = 0)

  ;; ../spec/5-reduction.watsup:57.1-59.16
  rule if-true {bt : blocktype, c : c_numtype, instr_1 : instr, instr_2 : instr}:
    `%~>%`([CONST_admininstr(I32_numtype, c) IF_admininstr(bt, instr_1*, instr_2*)], [BLOCK_admininstr(bt, instr_1*)])
    -- if (c =/= 0)

  ;; ../spec/5-reduction.watsup:53.1-55.28
  rule loop {bt : blocktype, instr : instr, k : nat, n : n, t_1 : valtype, t_2 : valtype, val : val}:
    `%~>%`((val <: admininstr)^k :: [LOOP_admininstr(bt, instr*)], [LABEL__admininstr(n, [LOOP_instr(bt, instr*)], (val <: admininstr)^k :: (instr <: admininstr)*)])
    -- if (bt = `%->%`(t_1^k, t_2^n))

  ;; ../spec/5-reduction.watsup:49.1-51.28
  rule block {bt : blocktype, instr : instr, k : nat, n : n, t_1 : valtype, t_2 : valtype, val : val}:
    `%~>%`((val <: admininstr)^k :: [BLOCK_admininstr(bt, instr*)], [LABEL__admininstr(n, [], (val <: admininstr)^k :: (instr <: admininstr)*)])
    -- if (bt = `%->%`(t_1^k, t_2^n))

  ;; ../spec/5-reduction.watsup:46.1-47.47
  rule local.tee {val : val, x : idx}:
    `%~>%`([(val <: admininstr) LOCAL.TEE_admininstr(x)], [(val <: admininstr) (val <: admininstr) LOCAL.SET_admininstr(x)])

  ;; ../spec/5-reduction.watsup:42.1-44.14
  rule select-false {c : c_numtype, t : valtype, val_1 : val, val_2 : val}:
    `%~>%`([(val_1 <: admininstr) (val_2 <: admininstr) CONST_admininstr(I32_numtype, c) SELECT_admininstr(t?)], [(val_2 <: admininstr)])
    -- if (c = 0)

  ;; ../spec/5-reduction.watsup:38.1-40.16
  rule select-true {c : c_numtype, t : valtype, val_1 : val, val_2 : val}:
    `%~>%`([(val_1 <: admininstr) (val_2 <: admininstr) CONST_admininstr(I32_numtype, c) SELECT_admininstr(t?)], [(val_1 <: admininstr)])
    -- if (c =/= 0)

  ;; ../spec/5-reduction.watsup:35.1-36.24
  rule drop {val : val}:
    `%~>%`([(val <: admininstr) DROP_admininstr], [])

  ;; ../spec/5-reduction.watsup:32.1-33.19
  rule nop:
    `%~>%`([NOP_admininstr], [])

  ;; ../spec/5-reduction.watsup:29.1-30.24
  rule unreachable:
    `%~>%`([UNREACHABLE_admininstr], [TRAP_admininstr])

  ;; ../spec/5-reduction.watsup:25.1-27.15
  rule ref.is_null-false {val : val}:
    `%~>%`([(val <: admininstr) REF.IS_NULL_admininstr], [CONST_admininstr(I32_numtype, 0)])
    -- otherwise

  ;; ../spec/5-reduction.watsup:21.1-23.26
  rule ref.is_null-true {rt : reftype, val : val}:
    `%~>%`([(val <: admininstr) REF.IS_NULL_admininstr], [CONST_admininstr(I32_numtype, 1)])
    -- if (val = REF.NULL_val(rt))
-}


{-
;; ../spec/5-reduction.watsup:5.1-5.63
relation Step_read: `%~>%`(config, admininstr*)
  ;; ../spec/5-reduction.watsup:165.1-167.61
  rule call_addr {a : addr, instr : instr, k : nat, m : moduleinst, n : n, t : valtype, t_1 : valtype, t_2 : valtype, val : val, z : state}:
    `%~>%`(`%;%`(z, (val <: admininstr)^k :: [CALL_ADDR_admininstr(a)]), [FRAME__admininstr(n, {LOCAL val^k :: $default_(t)*, MODULE m}, [LABEL__admininstr(n, [], (instr <: admininstr)*)])])
    -- if ($funcinst(z)[a] = `%;%`(m, FUNC(`%->%`(t_1^k, t_2^n), t*, instr*)))

  ;; ../spec/5-reduction.watsup:161.1-163.15
  rule call_indirect-trap {ft : functype, i : nat, x : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST_admininstr(I32_numtype, i) CALL_INDIRECT_admininstr(x, ft)]), [TRAP_admininstr])
    -- otherwise

  ;; ../spec/5-reduction.watsup:156.1-159.34
  rule call_indirect-call {a : addr, ft : functype, func : func, i : nat, m : moduleinst, x : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST_admininstr(I32_numtype, i) CALL_INDIRECT_admininstr(x, ft)]), [CALL_ADDR_admininstr(a)])
    -- if ($table(z, x)[i] = REF.FUNC_ADDR_ref(a))
    -- if ($funcinst(z)[a] = `%;%`(m, func))

  ;; ../spec/5-reduction.watsup:153.1-154.47
  rule call {x : idx, z : state}:
    `%~>%`(`%;%`(z, [CALL_admininstr(x)]), [CALL_ADDR_admininstr($funcaddr(z)[x])])

  ;; ../spec/5-reduction.watsup:147.1-151.15
  rule table.init-le {i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, (n + 1)) TABLE.INIT_admininstr(x, y)]), [CONST_admininstr(I32_numtype, j) ($elem(z, y)[i] <: admininstr) TABLE.SET_admininstr(x) CONST_admininstr(I32_numtype, (j + 1)) CONST_admininstr(I32_numtype, (i + 1)) CONST_admininstr(I32_numtype, n) TABLE.INIT_admininstr(x, y)])
    -- otherwise

  ;; ../spec/5-reduction.watsup:144.1-146.15
  rule table.init-zero {i : nat, j : nat, x : idx, y : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, 0) TABLE.INIT_admininstr(x, y)]), [])
    -- otherwise

  ;; ../spec/5-reduction.watsup:141.1-143.62
  rule table.init-trap {i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, n) TABLE.INIT_admininstr(x, y)]), [TRAP_admininstr])
    -- if (((i + n) > |$elem(z, y)|) \/ ((j + n) > |$table(z, x)|))

  ;; ../spec/5-reduction.watsup:134.1-139.14
  rule table.copy-gt {i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, (n + 1)) TABLE.COPY_admininstr(x, y)]), [CONST_admininstr(I32_numtype, (j + n)) CONST_admininstr(I32_numtype, (i + n)) TABLE.GET_admininstr(y) TABLE.SET_admininstr(x) CONST_admininstr(I32_numtype, (j + 1)) CONST_admininstr(I32_numtype, (i + 1)) CONST_admininstr(I32_numtype, n) TABLE.COPY_admininstr(x, y)])
    -- if (i > i)

  ;; ../spec/5-reduction.watsup:128.1-133.15
  rule table.copy-le {i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, (n + 1)) TABLE.COPY_admininstr(x, y)]), [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) TABLE.GET_admininstr(y) TABLE.SET_admininstr(x) CONST_admininstr(I32_numtype, (j + 1)) CONST_admininstr(I32_numtype, (i + 1)) CONST_admininstr(I32_numtype, n) TABLE.COPY_admininstr(x, y)])
    -- if (j <= i)

  ;; ../spec/5-reduction.watsup:125.1-127.15
  rule table.copy-zero {i : nat, j : nat, x : idx, y : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, 0) TABLE.COPY_admininstr(x, y)]), [])
    -- otherwise

  ;; ../spec/5-reduction.watsup:122.1-124.63
  rule table.copy-trap {i : nat, j : nat, n : n, x : idx, y : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST_admininstr(I32_numtype, j) CONST_admininstr(I32_numtype, i) CONST_admininstr(I32_numtype, n) TABLE.COPY_admininstr(x, y)]), [TRAP_admininstr])
    -- if (((i + n) > |$table(z, y)|) \/ ((j + n) > |$table(z, x)|))

  ;; ../spec/5-reduction.watsup:117.1-120.15
  rule table.fill-succ {i : nat, n : n, val : val, x : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST_admininstr(I32_numtype, i) (val <: admininstr) CONST_admininstr(I32_numtype, (n + 1)) TABLE.FILL_admininstr(x)]), [CONST_admininstr(I32_numtype, i) (val <: admininstr) TABLE.SET_admininstr(x) CONST_admininstr(I32_numtype, (i + 1)) (val <: admininstr) CONST_admininstr(I32_numtype, n) TABLE.FILL_admininstr(x)])
    -- otherwise

  ;; ../spec/5-reduction.watsup:114.1-116.15
  rule table.fill-zero {i : nat, val : val, x : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST_admininstr(I32_numtype, i) (val <: admininstr) CONST_admininstr(I32_numtype, 0) TABLE.FILL_admininstr(x)]), [])
    -- otherwise

  ;; ../spec/5-reduction.watsup:111.1-113.34
  rule table.fill-trap {i : nat, n : n, val : val, x : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST_admininstr(I32_numtype, i) (val <: admininstr) CONST_admininstr(I32_numtype, n) TABLE.FILL_admininstr(x)]), [TRAP_admininstr])
    -- if ((i + n) > |$table(z, x)|)

  ;; ../spec/5-reduction.watsup:107.1-109.27
  rule table.size {n : n, x : idx, z : state}:
    `%~>%`(`%;%`(z, [TABLE.SIZE_admininstr(x)]), [CONST_admininstr(I32_numtype, n)])
    -- if (|$table(z, x)| = n)

  ;; ../spec/5-reduction.watsup:103.1-105.27
  rule table.get-lt {i : nat, x : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST_admininstr(I32_numtype, i) TABLE.GET_admininstr(x)]), [($table(z, x)[i] <: admininstr)])
    -- if (i < |$table(z, x)|)

  ;; ../spec/5-reduction.watsup:99.1-101.28
  rule table.get-ge {i : nat, x : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST_admininstr(I32_numtype, i) TABLE.GET_admininstr(x)]), [TRAP_admininstr])
    -- if (i >= |$table(z, x)|)

  ;; ../spec/5-reduction.watsup:96.1-97.37
  rule global.get {x : idx, z : state}:
    `%~>%`(`%;%`(z, [GLOBAL.GET_admininstr(x)]), [($global(z, x) <: admininstr)])

  ;; ../spec/5-reduction.watsup:93.1-94.35
  rule local.get {x : idx, z : state}:
    `%~>%`(`%;%`(z, [LOCAL.GET_admininstr(x)]), [($local(z, x) <: admininstr)])

  ;; ../spec/5-reduction.watsup:90.1-91.53
  rule ref.func {x : idx, z : state}:
    `%~>%`(`%;%`(z, [REF.FUNC_admininstr(x)]), [REF.FUNC_ADDR_admininstr($funcaddr(z)[x])])
-}


{-
;; ../spec/5-reduction.watsup:6.1-6.63
relation Step_write: `%~>%`(config, config)
  ;; ../spec/5-reduction.watsup:179.1-181.28
  rule table.set-ge {i : nat, ref : ref, x : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST_admininstr(I32_numtype, i) (ref <: admininstr) TABLE.GET_admininstr(x)]), `%;%`(z, [TRAP_admininstr]))
    -- if (i >= |$table(z, x)|)

  ;; ../spec/5-reduction.watsup:175.1-177.27
  rule table.set-lt {i : nat, ref : ref, x : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST_admininstr(I32_numtype, i) (ref <: admininstr) TABLE.GET_admininstr(x)]), `%;%`($with_table(z, x, i, ref), []))
    -- if (i < |$table(z, x)|)

  ;; ../spec/5-reduction.watsup:172.1-173.62
  rule global.set {val : val, x : idx, z : state}:
    `%~>%`(`%;%`(z, [(val <: admininstr) GLOBAL.SET_admininstr(x)]), `%;%`($with_global(z, x, val), []))

  ;; ../spec/5-reduction.watsup:169.1-170.60
  rule local.set {val : val, x : idx, z : state}:
    `%~>%`(`%;%`(z, [(val <: admininstr) LOCAL.SET_admininstr(x)]), `%;%`($with_local(z, x, val), []))
-}


{-
;; ../spec/5-reduction.watsup:3.1-3.63
relation Step: `%~>%`(config, config)
  ;; ../spec/5-reduction.watsup:16.1-18.42
  rule write {instr : instr, instr' : instr, z : state, z' : state}:
    `%~>%`(`%;%`(z, (instr <: admininstr)*), `%;%`(z', (instr' <: admininstr)*))
    -- Step_write: `%~>%`(`%;%`(z, (instr <: admininstr)*), `%;%`(z', (instr' <: admininstr)*))

  ;; ../spec/5-reduction.watsup:12.1-14.37
  rule read {instr : instr, instr' : instr, z : state}:
    `%~>%`(`%;%`(z, (instr <: admininstr)*), `%;%`(z, (instr' <: admininstr)*))
    -- Step_read: `%~>%`(`%;%`(z, (instr <: admininstr)*), (instr' <: admininstr)*)

  ;; ../spec/5-reduction.watsup:8.1-10.34
  rule pure {instr : instr, instr' : instr, z : state}:
    `%~>%`(`%;%`(z, (instr <: admininstr)*), `%;%`(z, (instr' <: admininstr)*))
    -- Step_pure: `%~>%`((instr <: admininstr)*, (instr' <: admininstr)*)
-}
$ ghc -c Test.hs
```
