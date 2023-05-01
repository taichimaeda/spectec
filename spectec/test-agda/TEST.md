# Preview

```sh
$ dune exec ../src/exe-watsup/main.exe -- --agda ../minispec/*.watsup -o output.agda
$ cat output.agda
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Unit

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

ty-n : Set
ty-n  = Nat

ty-name : Set
ty-name  = String

ty-byte : Set
ty-byte  = Nat

ty-u32 : Set
ty-u32  = Nat

ty-idx : Set
ty-idx  = Nat

ty-funcidx : Set
ty-funcidx  = ty-idx

ty-globalidx : Set
ty-globalidx  = ty-idx

ty-labelidx : Set
ty-labelidx  = ty-idx

ty-localidx : Set
ty-localidx  = ty-idx

data ty-numtype : Set
data ty-numtype where
  I32 :
    ⊤ ->
    ----------
    ty-numtype

data ty-valtype : Set
data ty-valtype where
  I32 :
    ⊤ ->
    ----------
    ty-valtype
  BOT :
    ⊤ ->
    ----------
    ty-valtype

data ty-in : Set
data ty-in where
  I32 :
    ⊤ ->
    -----
    ty-in

ty-resulttype : Set
ty-resulttype  = List ty-valtype

ty-globaltype : Set
ty-globaltype  = (Maybe ⊤ × ty-valtype)

ty-functype : Set
ty-functype  = (ty-resulttype × ty-resulttype)

data ty-sx : Set
data ty-sx where
  U :
    ⊤ ->
    -----
    ty-sx
  S :
    ⊤ ->
    -----
    ty-sx

data ty-unop-IXX : Set
data ty-unop-IXX where
  CLZ :
    ⊤ ->
    -----------
    ty-unop-IXX
  CTZ :
    ⊤ ->
    -----------
    ty-unop-IXX
  POPCNT :
    ⊤ ->
    -----------
    ty-unop-IXX

data ty-binop-IXX : Set
data ty-binop-IXX where
  ADD :
    ⊤ ->
    ------------
    ty-binop-IXX
  SUB :
    ⊤ ->
    ------------
    ty-binop-IXX
  MUL :
    ⊤ ->
    ------------
    ty-binop-IXX
  DIV :
    ty-sx ->
    ------------
    ty-binop-IXX
  REM :
    ty-sx ->
    ------------
    ty-binop-IXX
  AND :
    ⊤ ->
    ------------
    ty-binop-IXX
  OR :
    ⊤ ->
    ------------
    ty-binop-IXX
  XOR :
    ⊤ ->
    ------------
    ty-binop-IXX
  SHL :
    ⊤ ->
    ------------
    ty-binop-IXX
  SHR :
    ty-sx ->
    ------------
    ty-binop-IXX
  ROTL :
    ⊤ ->
    ------------
    ty-binop-IXX
  ROTR :
    ⊤ ->
    ------------
    ty-binop-IXX

data ty-testop-IXX : Set
data ty-testop-IXX where
  EQZ :
    ⊤ ->
    -------------
    ty-testop-IXX

data ty-relop-IXX : Set
data ty-relop-IXX where
  EQ :
    ⊤ ->
    ------------
    ty-relop-IXX
  NE :
    ⊤ ->
    ------------
    ty-relop-IXX
  LT :
    ty-sx ->
    ------------
    ty-relop-IXX
  GT :
    ty-sx ->
    ------------
    ty-relop-IXX
  LE :
    ty-sx ->
    ------------
    ty-relop-IXX
  GE :
    ty-sx ->
    ------------
    ty-relop-IXX

data ty-unop-numtype : Set
data ty-unop-numtype where
  -I :
    ty-unop-IXX ->
    ---------------
    ty-unop-numtype

data ty-binop-numtype : Set
data ty-binop-numtype where
  -I :
    ty-binop-IXX ->
    ----------------
    ty-binop-numtype

data ty-testop-numtype : Set
data ty-testop-numtype where
  -I :
    ty-testop-IXX ->
    -----------------
    ty-testop-numtype

data ty-relop-numtype : Set
data ty-relop-numtype where
  -I :
    ty-relop-IXX ->
    ----------------
    ty-relop-numtype

ty-c-numtype : Set
ty-c-numtype  = Nat

ty-blocktype : Set
ty-blocktype  = ty-functype

data ty-instr : Set
data ty-instr where
  UNREACHABLE :
    ⊤ ->
    --------
    ty-instr
  NOP :
    ⊤ ->
    --------
    ty-instr
  DROP :
    ⊤ ->
    --------
    ty-instr
  SELECT :
    Maybe ty-valtype ->
    --------
    ty-instr
  BLOCK :
    (ty-blocktype × List ty-instr) ->
    --------
    ty-instr
  LOOP :
    (ty-blocktype × List ty-instr) ->
    --------
    ty-instr
  IF :
    ((ty-blocktype × List ty-instr) × List ty-instr) ->
    --------
    ty-instr
  BR :
    ty-labelidx ->
    --------
    ty-instr
  BR-IF :
    ty-labelidx ->
    --------
    ty-instr
  CALL :
    ty-funcidx ->
    --------
    ty-instr
  RETURN :
    ⊤ ->
    --------
    ty-instr
  CONST :
    (ty-numtype × ty-c-numtype) ->
    --------
    ty-instr
  UNOP :
    (ty-numtype × ty-unop-numtype) ->
    --------
    ty-instr
  BINOP :
    (ty-numtype × ty-binop-numtype) ->
    --------
    ty-instr
  TESTOP :
    (ty-numtype × ty-testop-numtype) ->
    --------
    ty-instr
  RELOP :
    (ty-numtype × ty-relop-numtype) ->
    --------
    ty-instr
  LOCAL-GET :
    ty-localidx ->
    --------
    ty-instr
  LOCAL-SET :
    ty-localidx ->
    --------
    ty-instr
  LOCAL-TEE :
    ty-localidx ->
    --------
    ty-instr
  GLOBAL-GET :
    ty-globalidx ->
    --------
    ty-instr
  GLOBAL-SET :
    ty-globalidx ->
    --------
    ty-instr

ty-expr : Set
ty-expr  = List ty-instr

ty-func : Set
ty-func  = ((ty-functype × List ty-valtype) × ty-expr)

ty-global : Set
ty-global  = (ty-globaltype × ty-expr)

ty-start : Set
ty-start  = ty-funcidx

ty-module : Set
ty-module  = ((List ty-func × List ty-global) × List ty-start)

$Ki : ⊤ → Nat
$Ki _ = 1024

$min : (Nat × Nat) → Nat
$min ⟨ 0 , j ⟩ = 0
$min ⟨ i , 0 ⟩ = 0
$min ⟨ _ {- (i + 1) -} , _ {- (j + 1) -} ⟩ = ? {- $min(i, j) -}

$size : ty-valtype → Nat
$size _ {- I32_valtype -} = 32

$test-sub-ATOM-22 : ty-n → Nat
$test-sub-ATOM-22 n-3-ATOM-y = 0

$curried- : (ty-n × ty-n) → Nat
$curried- ⟨ n-1 , n-2 ⟩ = ? {- (n_1 + n_2) -}

data ty-testfuse : Set
data ty-testfuse where
  AB- :
    ((Nat × Nat) × Nat) ->
    -----------
    ty-testfuse
  CD :
    ((Nat × Nat) × Nat) ->
    -----------
    ty-testfuse
  EF :
    ((Nat × Nat) × Nat) ->
    -----------
    ty-testfuse
  GH :
    ((Nat × Nat) × Nat) ->
    -----------
    ty-testfuse
  IJ :
    ((Nat × Nat) × Nat) ->
    -----------
    ty-testfuse
  KL :
    ((Nat × Nat) × Nat) ->
    -----------
    ty-testfuse
  MN :
    ((Nat × Nat) × Nat) ->
    -----------
    ty-testfuse
  OP :
    ((Nat × Nat) × Nat) ->
    -----------
    ty-testfuse
  QR :
    ((Nat × Nat) × Nat) ->
    -----------
    ty-testfuse

record ty-context : Set
record ty-context where
  field
    FUNC : List ty-functype
    GLOBAL : List ty-globaltype
    LOCAL : List ty-valtype
    LABEL : List ty-resulttype
    RETURNS : Maybe ty-resulttype

data ty-Functype-ok : ty-functype → Set
data ty-Functype-ok where
  - :
    (ft : ty-functype) ->
    -----------------
    ty-Functype-ok ft

data ty-Globaltype-ok : ty-globaltype → Set
data ty-Globaltype-ok where
  - :
    (gt : ty-globaltype) ->
    -------------------
    ty-Globaltype-ok gt

data ty-Blocktype-ok : ((ty-context × ty-blocktype) × ty-functype) → Set
data ty-Blocktype-ok where
  - :
    (C : ty-context) (ft : ty-functype) ->
    ty-Functype-ok ft ->
    -------------------------------------------
    ty-Blocktype-ok ⟨ ⟨ C , ft ⟩ , ft ⟩

data ty-Instr-ok : ((ty-context × ty-instr) × ty-functype) → Set
data ty-InstrSeq-ok : ((ty-context × List ty-instr) × ty-functype) → Set
data ty-Instr-ok where
  unreachable :
    (C : ty-context) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ---------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- UNREACHABLE_instr -} ⟩ , ⟨ ? {- t_1*{t_1} -} , ? {- t_2*{t_2} -} ⟩ ⟩
  nop :
    (C : ty-context) ->
    -----------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- NOP_instr -} ⟩ , ⟨ ? {- [] -} , ? {- [] -} ⟩ ⟩
  drop :
    (C : ty-context) (t : ty-valtype) ->
    -------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- DROP_instr -} ⟩ , ⟨ ? {- [t] -} , ? {- [] -} ⟩ ⟩
  select-expl :
    (C : ty-context) (t : ty-valtype) ->
    ------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- SELECT_instr(?(t)) -} ⟩ , ⟨ ? {- [t t I32_valtype] -} , ? {- [t] -} ⟩ ⟩
  select-impl :
    (C : ty-context) (numtype : ty-numtype) (t : ty-valtype) ->
    ? {- PREM -} ->
    -----------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- SELECT_instr(?()) -} ⟩ , ⟨ ? {- [t t I32_valtype] -} , ? {- [t] -} ⟩ ⟩
  block :
    (C : ty-context) (bt : ty-blocktype) (instr : ty-instr) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ty-Blocktype-ok ⟨ ⟨ C , bt ⟩ , ⟨ ? {- t_1*{t_1} -} , ? {- t_2*{t_2} -} ⟩ ⟩ ->
    ty-InstrSeq-ok ⟨ ⟨ ? {- C ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2]*{t_2}, RETURNS ?()} -} , ? {- instr*{instr} -} ⟩ , ⟨ ? {- t_1*{t_1} -} , ? {- t_2*{t_2} -} ⟩ ⟩ ->
    ----------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- BLOCK_instr(bt, instr*{instr}) -} ⟩ , ⟨ ? {- t_1*{t_1} -} , ? {- t_2*{t_2} -} ⟩ ⟩
  loop :
    (C : ty-context) (bt : ty-blocktype) (instr : ty-instr) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ty-Blocktype-ok ⟨ ⟨ C , bt ⟩ , ⟨ ? {- t_1*{t_1} -} , ? {- t_2*{t_2} -} ⟩ ⟩ ->
    ty-InstrSeq-ok ⟨ ⟨ ? {- C ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_1]*{t_1}, RETURNS ?()} -} , ? {- instr*{instr} -} ⟩ , ⟨ ? {- t_1*{t_1} -} , ? {- t_2*{t_2} -} ⟩ ⟩ ->
    ---------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- LOOP_instr(bt, instr*{instr}) -} ⟩ , ⟨ ? {- t_1*{t_1} -} , ? {- t_2*{t_2} -} ⟩ ⟩
  if :
    (C : ty-context) (bt : ty-blocktype) (instr-1 : ty-instr) (instr-2 : ty-instr) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ty-Blocktype-ok ⟨ ⟨ C , bt ⟩ , ⟨ ? {- t_1*{t_1} -} , ? {- t_2*{t_2} -} ⟩ ⟩ ->
    ty-InstrSeq-ok ⟨ ⟨ ? {- C ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2]*{t_2}, RETURNS ?()} -} , ? {- instr_1*{instr_1} -} ⟩ , ⟨ ? {- t_1*{t_1} -} , ? {- t_2*{t_2} -} ⟩ ⟩ ->
    ty-InstrSeq-ok ⟨ ⟨ ? {- C ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2]*{t_2}, RETURNS ?()} -} , ? {- instr_2*{instr_2} -} ⟩ , ⟨ ? {- t_1*{t_1} -} , ? {- t_2*{t_2} -} ⟩ ⟩ ->
    ------------------------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- IF_instr(bt, instr_1*{instr_1}, instr_2*{instr_2}) -} ⟩ , ⟨ ? {- t_1*{t_1} -} , ? {- t_2*{t_2} -} ⟩ ⟩
  br :
    (C : ty-context) (l : ty-labelidx) (t : ty-valtype) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ? {- PREM -} ->
    ------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- BR_instr(l) -} ⟩ , ⟨ ? {- t_1*{t_1} :: t*{t} -} , ? {- t_2*{t_2} -} ⟩ ⟩
  br-if :
    (C : ty-context) (l : ty-labelidx) (t : ty-valtype) ->
    ? {- PREM -} ->
    ---------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- BR_IF_instr(l) -} ⟩ , ⟨ ? {- t*{t} :: [I32_valtype] -} , ? {- t*{t} -} ⟩ ⟩
  return :
    (C : ty-context) (t : ty-valtype) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ? {- PREM -} ->
    -------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- RETURN_instr -} ⟩ , ⟨ ? {- t_1*{t_1} :: t*{t} -} , ? {- t_2*{t_2} -} ⟩ ⟩
  call :
    (C : ty-context) (t-1 : ty-valtype) (t-2 : ty-valtype) (x : ty-idx) ->
    ? {- PREM -} ->
    -----------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- CALL_instr(x) -} ⟩ , ⟨ ? {- t_1*{t_1} -} , ? {- t_2*{t_2} -} ⟩ ⟩
  const :
    (C : ty-context) (c-nt : ty-c-numtype) (nt : ty-numtype) ->
    --------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- CONST_instr(nt, c_nt) -} ⟩ , ⟨ ? {- [] -} , ? {- [(nt <: valtype)] -} ⟩ ⟩
  unop :
    (C : ty-context) (nt : ty-numtype) (unop : ty-unop-numtype) ->
    ----------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- UNOP_instr(nt, unop) -} ⟩ , ⟨ ? {- [(nt <: valtype)] -} , ? {- [(nt <: valtype)] -} ⟩ ⟩
  binop :
    (C : ty-context) (binop : ty-binop-numtype) (nt : ty-numtype) ->
    ----------------------------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- BINOP_instr(nt, binop) -} ⟩ , ⟨ ? {- [(nt <: valtype) (nt <: valtype)] -} , ? {- [(nt <: valtype)] -} ⟩ ⟩
  testop :
    (C : ty-context) (nt : ty-numtype) (testop : ty-testop-numtype) ->
    ----------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- TESTOP_instr(nt, testop) -} ⟩ , ⟨ ? {- [(nt <: valtype)] -} , ? {- [I32_valtype] -} ⟩ ⟩
  relop :
    (C : ty-context) (nt : ty-numtype) (relop : ty-relop-numtype) ->
    ------------------------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- RELOP_instr(nt, relop) -} ⟩ , ⟨ ? {- [(nt <: valtype) (nt <: valtype)] -} , ? {- [I32_valtype] -} ⟩ ⟩
  local-get :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    ? {- PREM -} ->
    ---------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- LOCAL.GET_instr(x) -} ⟩ , ⟨ ? {- [] -} , ? {- [t] -} ⟩ ⟩
  local-set :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    ? {- PREM -} ->
    ---------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- LOCAL.SET_instr(x) -} ⟩ , ⟨ ? {- [t] -} , ? {- [] -} ⟩ ⟩
  local-tee :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    ? {- PREM -} ->
    ----------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- LOCAL.TEE_instr(x) -} ⟩ , ⟨ ? {- [t] -} , ? {- [t] -} ⟩ ⟩
  global-get :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    ? {- PREM -} ->
    ----------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- GLOBAL.GET_instr(x) -} ⟩ , ⟨ ? {- [] -} , ? {- [t] -} ⟩ ⟩
  global-set :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    ? {- PREM -} ->
    ----------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , ? {- GLOBAL.SET_instr(x) -} ⟩ , ⟨ ? {- [t] -} , ? {- [] -} ⟩ ⟩
data ty-InstrSeq-ok where
  empty :
    (C : ty-context) ->
    -------------------------------------------------------------------------------
    ty-InstrSeq-ok ⟨ ⟨ C , ? {- [] -} ⟩ , ⟨ ? {- [] -} , ? {- [] -} ⟩ ⟩
  seq :
    (C : ty-context) (instr-1 : ty-instr) (instr-2 : ty-instr) (t-1 : ty-valtype) (t-2 : ty-valtype) (t-3 : ty-valtype) ->
    ty-Instr-ok ⟨ ⟨ C , instr-1 ⟩ , ⟨ ? {- t_1*{t_1} -} , ? {- t_2*{t_2} -} ⟩ ⟩ ->
    ty-InstrSeq-ok ⟨ ⟨ C , ? {- [instr_2] -} ⟩ , ⟨ ? {- t_2*{t_2} -} , ? {- t_3*{t_3} -} ⟩ ⟩ ->
    ------------------------------------------------------------------------------------------------------------------
    ty-InstrSeq-ok ⟨ ⟨ C , ? {- [instr_1] :: instr_2*{} -} ⟩ , ⟨ ? {- t_1*{t_1} -} , ? {- t_3*{t_3} -} ⟩ ⟩
  weak :
    (C : ty-context) (instr : ty-instr) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ty-InstrSeq-ok ⟨ ⟨ C , ? {- instr*{instr} -} ⟩ , ⟨ ? {- t_1*{} -} , ? {- t_2*{t_2} -} ⟩ ⟩ ->
    ----------------------------------------------------------------------------------------------------
    ty-InstrSeq-ok ⟨ ⟨ C , ? {- instr*{instr} -} ⟩ , ⟨ ? {- [t_1] -} , ? {- t_2*{t_2} -} ⟩ ⟩
  frame :
    (C : ty-context) (instr : ty-instr) (t : ty-valtype) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ty-InstrSeq-ok ⟨ ⟨ C , ? {- instr*{instr} -} ⟩ , ⟨ ? {- t_1*{t_1} -} , ? {- t_2*{t_2} -} ⟩ ⟩ ->
    --------------------------------------------------------------------------------------------------------------------------
    ty-InstrSeq-ok ⟨ ⟨ C , ? {- instr*{instr} -} ⟩ , ⟨ ? {- t*{t} :: t_1*{t_1} -} , ? {- t*{t} :: t_2*{t_2} -} ⟩ ⟩

data ty-Expr-ok : ((ty-context × ty-expr) × ty-resulttype) → Set
data ty-Expr-ok where
  - :
    (C : ty-context) (instr : ty-instr) (t : ty-valtype) ->
    ty-InstrSeq-ok ⟨ ⟨ C , ? {- instr*{instr} -} ⟩ , ⟨ ? {- [] -} , ? {- t*{t} -} ⟩ ⟩ ->
    --------------------------------------------------------------------
    ty-Expr-ok ⟨ ⟨ C , ? {- instr*{instr} -} ⟩ , ? {- t*{t} -} ⟩

data ty-Instr-const : (ty-context × ty-instr) → Set
data ty-Instr-const where
  const :
    (C : ty-context) (c : ty-c-numtype) (nt : ty-numtype) ->
    -----------------------------------------------------
    ty-Instr-const ⟨ C , ? {- CONST_instr(nt, c) -} ⟩
  global-get :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    ? {- PREM -} ->
    ------------------------------------------------------
    ty-Instr-const ⟨ C , ? {- GLOBAL.GET_instr(x) -} ⟩

data ty-Expr-const : (ty-context × ty-expr) → Set
data ty-Expr-const where
  - :
    (C : ty-context) (instr : ty-instr) ->
    ? {- PREM -} ->
    -----------------------------------------------
    ty-Expr-const ⟨ C , ? {- instr*{instr} -} ⟩

data ty-Expr-ok-const : ((ty-context × ty-expr) × ty-valtype) → Set
data ty-Expr-ok-const where
  - :
    (C : ty-context) (expr : ty-expr) (t : ty-valtype) ->
    ty-Expr-ok ⟨ ⟨ C , expr ⟩ , ? {- [t] -} ⟩ ->
    ty-Expr-const ⟨ C , expr ⟩ ->
    ---------------------------------------------
    ty-Expr-ok-const ⟨ ⟨ C , expr ⟩ , t ⟩

data ty-Func-ok : ((ty-context × ty-func) × ty-functype) → Set
data ty-Func-ok where
  - :
    (C : ty-context) (expr : ty-expr) (ft : ty-functype) (t : ty-valtype) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ? {- PREM -} ->
    ty-Functype-ok ft ->
    ty-Expr-ok ⟨ ⟨ ? {- C ++ {FUNC [], GLOBAL [], LOCAL t_1*{t_1} :: t*{t}, LABEL [], RETURNS ?()} ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2*{t_2}], RETURNS ?()} ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [], RETURNS ?(t_2*{t_2})} -} , expr ⟩ , ? {- t_2*{t_2} -} ⟩ ->
    -----------------------------------------------------------------------------
    ty-Func-ok ⟨ ⟨ C , ⟨ ⟨ ft , ? {- t*{t} -} ⟩ , expr ⟩ ⟩ , ft ⟩

data ty-Global-ok : ((ty-context × ty-global) × ty-globaltype) → Set
data ty-Global-ok where
  - :
    (C : ty-context) (expr : ty-expr) (gt : ty-globaltype) (t : ty-valtype) ->
    ty-Globaltype-ok gt ->
    ? {- PREM -} ->
    ty-Expr-ok-const ⟨ ⟨ C , expr ⟩ , t ⟩ ->
    -------------------------------------------------------
    ty-Global-ok ⟨ ⟨ C , ⟨ gt , expr ⟩ ⟩ , gt ⟩

data ty-Start-ok : (ty-context × ty-start) → Set
data ty-Start-ok where
  - :
    (C : ty-context) (x : ty-idx) ->
    ? {- PREM -} ->
    -------------------------
    ty-Start-ok ⟨ C , x ⟩

data ty-Module-ok : ty-module → Set
data ty-Module-ok where
  - :
    (C : ty-context) (ft : ty-functype) (func : ty-func) (global : ty-global) (gt : ty-globaltype) (start : ty-start) ->
    ? {- PREM -} ->
    ? {- PREM -} ->
    ? {- PREM -} ->
    ? {- PREM -} ->
    ? {- PREM -} ->
    --------------------------------------------------------------------------------------------------
    ty-Module-ok ⟨ ⟨ ? {- func*{func} -} , ? {- global*{global} -} ⟩ , ? {- start*{start} -} ⟩

ty-addr : Set
ty-addr  = Nat

ty-funcaddr : Set
ty-funcaddr  = ty-addr

ty-globaladdr : Set
ty-globaladdr  = ty-addr

ty-labeladdr : Set
ty-labeladdr  = ty-addr

ty-hostaddr : Set
ty-hostaddr  = ty-addr

data ty-num : Set
data ty-num where
  CONST :
    (ty-numtype × ty-c-numtype) ->
    ------
    ty-num

data ty-val : Set
data ty-val where
  CONST :
    (ty-numtype × ty-c-numtype) ->
    ------
    ty-val

data ty-result : Set
data ty-result where
  -VALS :
    List ty-val ->
    ---------
    ty-result
  TRAP :
    ⊤ ->
    ---------
    ty-result

$default- : ty-valtype → ty-val
$default- _ {- I32_valtype -} = ? {- CONST_val(I32_numtype, 0) -}

record ty-moduleinst : Set
record ty-moduleinst where
  field
    FUNC : List ty-funcaddr
    GLOBAL : List ty-globaladdr

ty-funcinst : Set
ty-funcinst  = (ty-moduleinst × ty-func)

ty-globalinst : Set
ty-globalinst  = ty-val

record ty-store : Set
record ty-store where
  field
    FUNC : List ty-funcinst
    GLOBAL : List ty-globalinst

record ty-frame : Set
record ty-frame where
  field
    LOCAL : List ty-val
    MODULE : ty-moduleinst

ty-state : Set
ty-state  = (ty-store × ty-frame)

data ty-admininstr : Set
data ty-admininstr where
  UNREACHABLE :
    ⊤ ->
    -------------
    ty-admininstr
  NOP :
    ⊤ ->
    -------------
    ty-admininstr
  DROP :
    ⊤ ->
    -------------
    ty-admininstr
  SELECT :
    Maybe ty-valtype ->
    -------------
    ty-admininstr
  BLOCK :
    (ty-blocktype × List ty-instr) ->
    -------------
    ty-admininstr
  LOOP :
    (ty-blocktype × List ty-instr) ->
    -------------
    ty-admininstr
  IF :
    ((ty-blocktype × List ty-instr) × List ty-instr) ->
    -------------
    ty-admininstr
  BR :
    ty-labelidx ->
    -------------
    ty-admininstr
  BR-IF :
    ty-labelidx ->
    -------------
    ty-admininstr
  CALL :
    ty-funcidx ->
    -------------
    ty-admininstr
  RETURN :
    ⊤ ->
    -------------
    ty-admininstr
  CONST :
    (ty-numtype × ty-c-numtype) ->
    -------------
    ty-admininstr
  UNOP :
    (ty-numtype × ty-unop-numtype) ->
    -------------
    ty-admininstr
  BINOP :
    (ty-numtype × ty-binop-numtype) ->
    -------------
    ty-admininstr
  TESTOP :
    (ty-numtype × ty-testop-numtype) ->
    -------------
    ty-admininstr
  RELOP :
    (ty-numtype × ty-relop-numtype) ->
    -------------
    ty-admininstr
  LOCAL-GET :
    ty-localidx ->
    -------------
    ty-admininstr
  LOCAL-SET :
    ty-localidx ->
    -------------
    ty-admininstr
  LOCAL-TEE :
    ty-localidx ->
    -------------
    ty-admininstr
  GLOBAL-GET :
    ty-globalidx ->
    -------------
    ty-admininstr
  GLOBAL-SET :
    ty-globalidx ->
    -------------
    ty-admininstr
  CALL-ADDR :
    ty-funcaddr ->
    -------------
    ty-admininstr
  LABEL- :
    ((ty-n × List ty-instr) × List ty-admininstr) ->
    -------------
    ty-admininstr
  FRAME- :
    ((ty-n × ty-frame) × List ty-admininstr) ->
    -------------
    ty-admininstr
  TRAP :
    ⊤ ->
    -------------
    ty-admininstr

ty-config : Set
ty-config  = (ty-state × List ty-admininstr)

$funcaddr : ty-state → List ty-funcaddr
$funcaddr ⟨ s , f ⟩ = ? {- f.MODULE_frame.FUNC_moduleinst -}

$funcinst : ty-state → List ty-funcinst
$funcinst ⟨ s , f ⟩ = ? {- s.FUNC_store -}

$func : (ty-state × ty-funcidx) → ty-funcinst
$func ⟨ ⟨ s , f ⟩ , x ⟩ = ? {- s.FUNC_store[f.MODULE_frame.FUNC_moduleinst[x]] -}

$global : (ty-state × ty-globalidx) → ty-globalinst
$global ⟨ ⟨ s , f ⟩ , x ⟩ = ? {- s.GLOBAL_store[f.MODULE_frame.GLOBAL_moduleinst[x]] -}

$local : (ty-state × ty-localidx) → ty-val
$local ⟨ ⟨ s , f ⟩ , x ⟩ = ? {- f.LOCAL_frame[x] -}

$with-local : ((ty-state × ty-localidx) × ty-val) → ty-state
$with-local ⟨ ⟨ ⟨ s , f ⟩ , x ⟩ , v ⟩ = ⟨ s , ? {- f[LOCAL_frame[x] = v] -} ⟩

$with-global : ((ty-state × ty-globalidx) × ty-val) → ty-state
$with-global ⟨ ⟨ ⟨ s , f ⟩ , x ⟩ , v ⟩ = ⟨ ? {- s[GLOBAL_store[f.MODULE_frame.GLOBAL_moduleinst[x]] = v] -} , f ⟩

data ty-E : Set
data ty-E where
  -HOLE :
    ⊤ ->
    ----
    ty-E
  -SEQ :
    ((List ty-val × ty-E) × List ty-instr) ->
    ----
    ty-E
  LABEL- :
    ((ty-n × List ty-instr) × ty-E) ->
    ----
    ty-E

$unop : ((ty-unop-numtype × ty-numtype) × ty-c-numtype) → List ty-c-numtype
$unop  = ? {- TODO -}

$binop : (((ty-binop-numtype × ty-numtype) × ty-c-numtype) × ty-c-numtype) → List ty-c-numtype
$binop  = ? {- TODO -}

$testop : ((ty-testop-numtype × ty-numtype) × ty-c-numtype) → ty-c-numtype
$testop  = ? {- TODO -}

$relop : (((ty-relop-numtype × ty-numtype) × ty-c-numtype) × ty-c-numtype) → ty-c-numtype
$relop  = ? {- TODO -}

data ty-Step-pure : (List ty-admininstr × List ty-admininstr) → Set
data ty-Step-pure where
  unreachable :
    ---------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [UNREACHABLE_admininstr] -} , ? {- [TRAP_admininstr] -} ⟩
  nop :
    ----------------------------------------------------------
    ty-Step-pure ⟨ ? {- [NOP_admininstr] -} , ? {- [] -} ⟩
  drop :
    (val : ty-val) ->
    -------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [(val <: admininstr) DROP_admininstr] -} , ? {- [] -} ⟩
  select-true :
    (c : ty-c-numtype) (t : ty-valtype) (val-1 : ty-val) (val-2 : ty-val) ->
    ? {- PREM -} ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [(val_1 <: admininstr) (val_2 <: admininstr) CONST_admininstr(I32_numtype, c) SELECT_admininstr(t?{t})] -} , ? {- [(val_1 <: admininstr)] -} ⟩
  select-false :
    (c : ty-c-numtype) (t : ty-valtype) (val-1 : ty-val) (val-2 : ty-val) ->
    ? {- PREM -} ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [(val_1 <: admininstr) (val_2 <: admininstr) CONST_admininstr(I32_numtype, c) SELECT_admininstr(t?{t})] -} , ? {- [(val_2 <: admininstr)] -} ⟩
  block :
    (bt : ty-blocktype) (instr : ty-instr) (k : Nat) (n : ty-n) (t-1 : ty-valtype) (t-2 : ty-valtype) (val : ty-val) ->
    ? {- PREM -} ->
    --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- (val <: admininstr)^k{val} :: [BLOCK_admininstr(bt, instr*{instr})] -} , ? {- [LABEL__admininstr(n, [], (val <: admininstr)^k{val} :: (instr <: admininstr)*{instr})] -} ⟩
  loop :
    (bt : ty-blocktype) (instr : ty-instr) (k : Nat) (n : ty-n) (t-1 : ty-valtype) (t-2 : ty-valtype) (val : ty-val) ->
    ? {- PREM -} ->
    ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- (val <: admininstr)^k{val} :: [LOOP_admininstr(bt, instr*{instr})] -} , ? {- [LABEL__admininstr(n, [LOOP_instr(bt, instr*{instr})], (val <: admininstr)^k{val} :: (instr <: admininstr)*{instr})] -} ⟩
  if-true :
    (bt : ty-blocktype) (c : ty-c-numtype) (instr-1 : ty-instr) (instr-2 : ty-instr) ->
    ? {- PREM -} ->
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [CONST_admininstr(I32_numtype, c) IF_admininstr(bt, instr_1*{instr_1}, instr_2*{instr_2})] -} , ? {- [BLOCK_admininstr(bt, instr_1*{instr_1})] -} ⟩
  if-false :
    (bt : ty-blocktype) (c : ty-c-numtype) (instr-1 : ty-instr) (instr-2 : ty-instr) ->
    ? {- PREM -} ->
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [CONST_admininstr(I32_numtype, c) IF_admininstr(bt, instr_1*{instr_1}, instr_2*{instr_2})] -} , ? {- [BLOCK_admininstr(bt, instr_2*{instr_2})] -} ⟩
  label-vals :
    (instr : ty-instr) (n : ty-n) (val : ty-val) ->
    ---------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [LABEL__admininstr(n, instr*{instr}, (val <: admininstr)*{val})] -} , ? {- (val <: admininstr)*{val} -} ⟩
  br-zero :
    (instr : ty-instr) (instr' : ty-instr) (n : ty-n) (val : ty-val) (val' : ty-val) ->
    --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [LABEL__admininstr(n, instr'*{instr'}, (val' <: admininstr)*{val'} :: (val <: admininstr)^n{val} :: [BR_admininstr(0)] :: (instr <: admininstr)*{instr})] -} , ? {- (val <: admininstr)^n{val} :: (instr' <: admininstr)*{instr'} -} ⟩
  br-succ :
    (instr : ty-instr) (instr' : ty-instr) (l : ty-labelidx) (n : ty-n) (val : ty-val) ->
    --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [LABEL__admininstr(n, instr'*{instr'}, (val <: admininstr)*{val} :: [BR_admininstr(l + 1)] :: (instr <: admininstr)*{instr})] -} , ? {- (val <: admininstr)*{val} :: [BR_admininstr(l)] -} ⟩
  br-if-true :
    (c : ty-c-numtype) (l : ty-labelidx) ->
    ? {- PREM -} ->
    ----------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [CONST_admininstr(I32_numtype, c) BR_IF_admininstr(l)] -} , ? {- [BR_admininstr(l)] -} ⟩
  br-if-false :
    (c : ty-c-numtype) (l : ty-labelidx) ->
    ? {- PREM -} ->
    ------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [CONST_admininstr(I32_numtype, c) BR_IF_admininstr(l)] -} , ? {- [] -} ⟩
  frame-vals :
    (f : ty-frame) (n : ty-n) (val : ty-val) ->
    -----------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [FRAME__admininstr(n, f, (val <: admininstr)^n{val})] -} , ? {- (val <: admininstr)^n{val} -} ⟩
  return-frame :
    (f : ty-frame) (instr : ty-instr) (n : ty-n) (val : ty-val) (val' : ty-val) ->
    --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [FRAME__admininstr(n, f, (val' <: admininstr)*{val'} :: (val <: admininstr)^n{val} :: [RETURN_admininstr] :: (instr <: admininstr)*{instr})] -} , ? {- (val <: admininstr)^n{val} -} ⟩
  return-label :
    (instr : ty-instr) (instr' : ty-instr) (k : Nat) (val : ty-val) ->
    ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [LABEL__admininstr(k, instr'*{instr'}, (val <: admininstr)*{val} :: [RETURN_admininstr] :: (instr <: admininstr)*{instr})] -} , ? {- (val <: admininstr)*{val} :: [RETURN_admininstr] -} ⟩
  unop-val :
    (c : ty-c-numtype) (c-1 : ty-c-numtype) (nt : ty-numtype) (unop : ty-unop-numtype) ->
    ? {- PREM -} ->
    ----------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [CONST_admininstr(nt, c_1) UNOP_admininstr(nt, unop)] -} , ? {- [CONST_admininstr(nt, c)] -} ⟩
  unop-trap :
    (c-1 : ty-c-numtype) (nt : ty-numtype) (unop : ty-unop-numtype) ->
    ? {- PREM -} ->
    --------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [CONST_admininstr(nt, c_1) UNOP_admininstr(nt, unop)] -} , ? {- [TRAP_admininstr] -} ⟩
  binop-val :
    (binop : ty-binop-numtype) (c : ty-c-numtype) (c-1 : ty-c-numtype) (c-2 : ty-c-numtype) (nt : ty-numtype) ->
    ? {- PREM -} ->
    --------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [CONST_admininstr(nt, c_1) CONST_admininstr(nt, c_2) BINOP_admininstr(nt, binop)] -} , ? {- [CONST_admininstr(nt, c)] -} ⟩
  binop-trap :
    (binop : ty-binop-numtype) (c-1 : ty-c-numtype) (c-2 : ty-c-numtype) (nt : ty-numtype) ->
    ? {- PREM -} ->
    ------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [CONST_admininstr(nt, c_1) CONST_admininstr(nt, c_2) BINOP_admininstr(nt, binop)] -} , ? {- [TRAP_admininstr] -} ⟩
  testop :
    (c : ty-c-numtype) (c-1 : ty-c-numtype) (nt : ty-numtype) (testop : ty-testop-numtype) ->
    ? {- PREM -} ->
    -----------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [CONST_admininstr(nt, c_1) TESTOP_admininstr(nt, testop)] -} , ? {- [CONST_admininstr(I32_numtype, c)] -} ⟩
  relop :
    (c : ty-c-numtype) (c-1 : ty-c-numtype) (c-2 : ty-c-numtype) (nt : ty-numtype) (relop : ty-relop-numtype) ->
    ? {- PREM -} ->
    -----------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [CONST_admininstr(nt, c_1) CONST_admininstr(nt, c_2) RELOP_admininstr(nt, relop)] -} , ? {- [CONST_admininstr(I32_numtype, c)] -} ⟩
  local-tee :
    (val : ty-val) (x : ty-idx) ->
    ------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- [(val <: admininstr) LOCAL.TEE_admininstr(x)] -} , ? {- [(val <: admininstr) (val <: admininstr) LOCAL.SET_admininstr(x)] -} ⟩

data ty-Step-read : (ty-config × List ty-admininstr) → Set
data ty-Step-read where
  call :
    (x : ty-idx) (z : ty-state) ->
    ---------------------------------------------------------------------------------------------------------------
    ty-Step-read ⟨ ⟨ z , ? {- [CALL_admininstr(x)] -} ⟩ , ? {- [CALL_ADDR_admininstr($funcaddr(z)[x])] -} ⟩
  call-addr :
    (a : ty-addr) (f : ty-frame) (instr : ty-instr) (k : Nat) (m : ty-moduleinst) (n : ty-n) (t : ty-valtype) (t-1 : ty-valtype) (t-2 : ty-valtype) (val : ty-val) (z : ty-state) ->
    ? {- PREM -} ->
    ? {- PREM -} ->
    -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-read ⟨ ⟨ z , ? {- (val <: admininstr)^k{val} :: [CALL_ADDR_admininstr(a)] -} ⟩ , ? {- [FRAME__admininstr(n, f, [LABEL__admininstr(n, [], (instr <: admininstr)*{instr})])] -} ⟩
  local-get :
    (x : ty-idx) (z : ty-state) ->
    -----------------------------------------------------------------------------------------------------------
    ty-Step-read ⟨ ⟨ z , ? {- [LOCAL.GET_admininstr(x)] -} ⟩ , ? {- [($local(z, x) <: admininstr)] -} ⟩
  global-get :
    (x : ty-idx) (z : ty-state) ->
    -------------------------------------------------------------------------------------------------------------
    ty-Step-read ⟨ ⟨ z , ? {- [GLOBAL.GET_admininstr(x)] -} ⟩ , ? {- [($global(z, x) <: admininstr)] -} ⟩

data ty-Step : (ty-config × ty-config) → Set
data ty-Step where
  pure :
    (instr : ty-instr) (instr' : ty-instr) (z : ty-state) ->
    ty-Step-pure ⟨ ? {- (instr <: admininstr)*{instr} -} , ? {- (instr' <: admininstr)*{instr'} -} ⟩ ->
    -----------------------------------------------------------------------------------------------------------------------
    ty-Step ⟨ ⟨ z , ? {- (instr <: admininstr)*{instr} -} ⟩ , ⟨ z , ? {- (instr' <: admininstr)*{instr'} -} ⟩ ⟩
  read :
    (instr : ty-instr) (instr' : ty-instr) (z : ty-state) ->
    ty-Step-read ⟨ ⟨ z , ? {- (instr <: admininstr)*{instr} -} ⟩ , ? {- (instr' <: admininstr)*{instr'} -} ⟩ ->
    -----------------------------------------------------------------------------------------------------------------------
    ty-Step ⟨ ⟨ z , ? {- (instr <: admininstr)*{instr} -} ⟩ , ⟨ z , ? {- (instr' <: admininstr)*{instr'} -} ⟩ ⟩
  local-set :
    (val : ty-val) (x : ty-idx) (z : ty-state) ->
    ---------------------------------------------------------------------------------------------------------------------------------------
    ty-Step ⟨ ⟨ z , ? {- [(val <: admininstr) LOCAL.SET_admininstr(x)] -} ⟩ , ⟨ ? {- $with_local(z, x, val) -} , ? {- [] -} ⟩ ⟩
  global-set :
    (val : ty-val) (x : ty-idx) (z : ty-state) ->
    -----------------------------------------------------------------------------------------------------------------------------------------
    ty-Step ⟨ ⟨ z , ? {- [(val <: admininstr) GLOBAL.SET_admininstr(x)] -} ⟩ , ⟨ ? {- $with_global(z, x, val) -} , ? {- [] -} ⟩ ⟩
$ agda output.agda | sed -e "s/\/.*\/_build\///g"
Checking output (default/test-agda/output.agda).
Unsolved interaction metas at the following locations:
  default/test-agda/output.agda:325,46-47
  default/test-agda/output.agda:334,27-28
  default/test-agda/output.agda:412,25-26
  default/test-agda/output.agda:412,57-58
  default/test-agda/output.agda:412,77-78
  default/test-agda/output.agda:416,25-26
  default/test-agda/output.agda:416,49-50
  default/test-agda/output.agda:416,62-63
  default/test-agda/output.agda:420,25-26
  default/test-agda/output.agda:420,50-51
  default/test-agda/output.agda:420,64-65
  default/test-agda/output.agda:424,25-26
  default/test-agda/output.agda:424,58-59
  default/test-agda/output.agda:424,86-87
  default/test-agda/output.agda:427,5-6
  default/test-agda/output.agda:429,25-26
  default/test-agda/output.agda:429,57-58
  default/test-agda/output.agda:429,85-86
  default/test-agda/output.agda:432,38-39
  default/test-agda/output.agda:432,58-59
  default/test-agda/output.agda:433,24-25
  default/test-agda/output.agda:433,102-103
  default/test-agda/output.agda:433,130-131
  default/test-agda/output.agda:433,150-151
  default/test-agda/output.agda:435,25-26
  default/test-agda/output.agda:435,70-71
  default/test-agda/output.agda:435,90-91
  default/test-agda/output.agda:438,38-39
  default/test-agda/output.agda:438,58-59
  default/test-agda/output.agda:439,24-25
  default/test-agda/output.agda:439,102-103
  default/test-agda/output.agda:439,130-131
  default/test-agda/output.agda:439,150-151
  default/test-agda/output.agda:441,25-26
  default/test-agda/output.agda:441,69-70
  default/test-agda/output.agda:441,89-90
  default/test-agda/output.agda:444,38-39
  default/test-agda/output.agda:444,58-59
  default/test-agda/output.agda:445,24-25
  default/test-agda/output.agda:445,102-103
  default/test-agda/output.agda:445,134-135
  default/test-agda/output.agda:445,154-155
  default/test-agda/output.agda:446,24-25
  default/test-agda/output.agda:446,102-103
  default/test-agda/output.agda:446,134-135
  default/test-agda/output.agda:446,154-155
  default/test-agda/output.agda:448,25-26
  default/test-agda/output.agda:448,90-91
  default/test-agda/output.agda:448,110-111
  default/test-agda/output.agda:451,5-6
  default/test-agda/output.agda:453,25-26
  default/test-agda/output.agda:453,51-52
  default/test-agda/output.agda:453,80-81
  default/test-agda/output.agda:456,5-6
  default/test-agda/output.agda:458,25-26
  default/test-agda/output.agda:458,54-55
  default/test-agda/output.agda:458,87-88
  default/test-agda/output.agda:461,5-6
  default/test-agda/output.agda:463,25-26
  default/test-agda/output.agda:463,52-53
  default/test-agda/output.agda:463,81-82
  default/test-agda/output.agda:466,5-6
  default/test-agda/output.agda:468,25-26
  default/test-agda/output.agda:468,53-54
  default/test-agda/output.agda:468,73-74
  default/test-agda/output.agda:472,25-26
  default/test-agda/output.agda:472,61-62
  default/test-agda/output.agda:472,74-75
  default/test-agda/output.agda:476,25-26
  default/test-agda/output.agda:476,60-61
  default/test-agda/output.agda:476,88-89
  default/test-agda/output.agda:480,25-26
  default/test-agda/output.agda:480,62-63
  default/test-agda/output.agda:480,106-107
  default/test-agda/output.agda:484,25-26
  default/test-agda/output.agda:484,64-65
  default/test-agda/output.agda:484,92-93
  default/test-agda/output.agda:488,25-26
  default/test-agda/output.agda:488,62-63
  default/test-agda/output.agda:488,106-107
  default/test-agda/output.agda:491,5-6
  default/test-agda/output.agda:493,25-26
  default/test-agda/output.agda:493,58-59
  default/test-agda/output.agda:493,71-72
  default/test-agda/output.agda:496,5-6
  default/test-agda/output.agda:498,25-26
  default/test-agda/output.agda:498,58-59
  default/test-agda/output.agda:498,72-73
  default/test-agda/output.agda:501,5-6
  default/test-agda/output.agda:503,25-26
  default/test-agda/output.agda:503,58-59
  default/test-agda/output.agda:503,72-73
  default/test-agda/output.agda:506,5-6
  default/test-agda/output.agda:508,25-26
  default/test-agda/output.agda:508,59-60
  default/test-agda/output.agda:508,72-73
  default/test-agda/output.agda:511,5-6
  default/test-agda/output.agda:513,25-26
  default/test-agda/output.agda:513,59-60
  default/test-agda/output.agda:513,73-74
  default/test-agda/output.agda:518,28-29
  default/test-agda/output.agda:518,45-46
  default/test-agda/output.agda:518,58-59
  default/test-agda/output.agda:521,39-40
  default/test-agda/output.agda:521,59-60
  default/test-agda/output.agda:522,28-29
  default/test-agda/output.agda:522,52-53
  default/test-agda/output.agda:522,72-73
  default/test-agda/output.agda:524,28-29
  default/test-agda/output.agda:524,66-67
  default/test-agda/output.agda:524,86-87
  default/test-agda/output.agda:527,28-29
  default/test-agda/output.agda:527,56-57
  default/test-agda/output.agda:527,73-74
  default/test-agda/output.agda:529,28-29
  default/test-agda/output.agda:529,56-57
  default/test-agda/output.agda:529,72-73
  default/test-agda/output.agda:532,28-29
  default/test-agda/output.agda:532,56-57
  default/test-agda/output.agda:532,76-77
  default/test-agda/output.agda:534,28-29
  default/test-agda/output.agda:534,56-57
  default/test-agda/output.agda:534,85-86
  default/test-agda/output.agda:540,28-29
  default/test-agda/output.agda:540,56-57
  default/test-agda/output.agda:540,69-70
  default/test-agda/output.agda:542,24-25
  default/test-agda/output.agda:542,50-51
  default/test-agda/output.agda:549,26-27
  default/test-agda/output.agda:552,5-6
  default/test-agda/output.agda:554,26-27
  default/test-agda/output.agda:560,5-6
  default/test-agda/output.agda:562,25-26
  default/test-agda/output.agda:568,33-34
  default/test-agda/output.agda:577,5-6
  default/test-agda/output.agda:579,20-21
  default/test-agda/output.agda:579,246-247
  default/test-agda/output.agda:581,33-34
  default/test-agda/output.agda:588,5-6
  default/test-agda/output.agda:597,5-6
  default/test-agda/output.agda:605,5-6
  default/test-agda/output.agda:606,5-6
  default/test-agda/output.agda:607,5-6
  default/test-agda/output.agda:608,5-6
  default/test-agda/output.agda:609,5-6
  default/test-agda/output.agda:611,22-23
  default/test-agda/output.agda:611,44-45
  default/test-agda/output.agda:611,72-73
  default/test-agda/output.agda:654,33-34
  default/test-agda/output.agda:790,23-24
  default/test-agda/output.agda:793,23-24
  default/test-agda/output.agda:796,27-28
  default/test-agda/output.agda:799,29-30
  default/test-agda/output.agda:802,28-29
  default/test-agda/output.agda:805,47-48
  default/test-agda/output.agda:808,44-45
  default/test-agda/output.agda:826,10-11
  default/test-agda/output.agda:829,11-12
  default/test-agda/output.agda:832,12-13
  default/test-agda/output.agda:835,11-12
  default/test-agda/output.agda:841,20-21
  default/test-agda/output.agda:841,55-56
  default/test-agda/output.agda:844,20-21
  default/test-agda/output.agda:844,47-48
  default/test-agda/output.agda:848,20-21
  default/test-agda/output.agda:848,68-69
  default/test-agda/output.agda:851,5-6
  default/test-agda/output.agda:853,20-21
  default/test-agda/output.agda:853,134-135
  default/test-agda/output.agda:856,5-6
  default/test-agda/output.agda:858,20-21
  default/test-agda/output.agda:858,134-135
  default/test-agda/output.agda:861,5-6
  default/test-agda/output.agda:863,20-21
  default/test-agda/output.agda:863,98-99
  default/test-agda/output.agda:866,5-6
  default/test-agda/output.agda:868,20-21
  default/test-agda/output.agda:868,97-98
  default/test-agda/output.agda:871,5-6
  default/test-agda/output.agda:873,20-21
  default/test-agda/output.agda:873,121-122
  default/test-agda/output.agda:876,5-6
  default/test-agda/output.agda:878,20-21
  default/test-agda/output.agda:878,121-122
  default/test-agda/output.agda:882,20-21
  default/test-agda/output.agda:882,95-96
  default/test-agda/output.agda:886,20-21
  default/test-agda/output.agda:886,184-185
  default/test-agda/output.agda:890,20-21
  default/test-agda/output.agda:890,156-157
  default/test-agda/output.agda:893,5-6
  default/test-agda/output.agda:895,20-21
  default/test-agda/output.agda:895,85-86
  default/test-agda/output.agda:898,5-6
  default/test-agda/output.agda:900,20-21
  default/test-agda/output.agda:900,85-86
  default/test-agda/output.agda:904,20-21
  default/test-agda/output.agda:904,84-85
  default/test-agda/output.agda:908,20-21
  default/test-agda/output.agda:908,171-172
  default/test-agda/output.agda:912,20-21
  default/test-agda/output.agda:912,153-154
  default/test-agda/output.agda:915,5-6
  default/test-agda/output.agda:917,20-21
  default/test-agda/output.agda:917,84-85
  default/test-agda/output.agda:920,5-6
  default/test-agda/output.agda:922,20-21
  default/test-agda/output.agda:922,84-85
  default/test-agda/output.agda:925,5-6
  default/test-agda/output.agda:927,20-21
  default/test-agda/output.agda:927,112-113
  default/test-agda/output.agda:930,5-6
  default/test-agda/output.agda:932,20-21
  default/test-agda/output.agda:932,112-113
  default/test-agda/output.agda:935,5-6
  default/test-agda/output.agda:937,20-21
  default/test-agda/output.agda:937,88-89
  default/test-agda/output.agda:940,5-6
  default/test-agda/output.agda:942,20-21
  default/test-agda/output.agda:942,112-113
  default/test-agda/output.agda:946,20-21
  default/test-agda/output.agda:946,76-77
  default/test-agda/output.agda:953,26-27
  default/test-agda/output.agda:953,59-60
  default/test-agda/output.agda:956,5-6
  default/test-agda/output.agda:957,5-6
  default/test-agda/output.agda:959,26-27
  default/test-agda/output.agda:959,94-95
  default/test-agda/output.agda:963,26-27
  default/test-agda/output.agda:963,64-65
  default/test-agda/output.agda:967,26-27
  default/test-agda/output.agda:967,65-66
  default/test-agda/output.agda:973,20-21
  default/test-agda/output.agda:973,60-61
  default/test-agda/output.agda:975,21-22
  default/test-agda/output.agda:975,69-70
  default/test-agda/output.agda:978,26-27
  default/test-agda/output.agda:978,68-69
  default/test-agda/output.agda:980,21-22
  default/test-agda/output.agda:980,69-70
  default/test-agda/output.agda:984,21-22
  default/test-agda/output.agda:984,81-82
  default/test-agda/output.agda:984,114-115
  default/test-agda/output.agda:988,21-22
  default/test-agda/output.agda:988,82-83
  default/test-agda/output.agda:988,116-117
```

The `sed` incantation is needed to remove (user-specific) absolute paths in Agda output.
