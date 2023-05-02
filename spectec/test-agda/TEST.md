# Preview

```sh
$ patch -s -p0 -i ../spec/minispec.patch -d ../spec --read-only=ignore
$ dune exec ../src/exe-watsup/main.exe -- --agda ../spec/*.watsup -o output.agda
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
$min ⟨ i , j ⟩ = $min ⟨ ? {- BinE: (i - 1) -} , ? {- BinE: (j - 1) -} ⟩

$size : ty-valtype → Nat
$size _ {- CaseE: I32_valtype -} = 32

$test-sub-ATOM-22 : ty-n → Nat
$test-sub-ATOM-22 n-3-ATOM-y = 0

$curried- : (ty-n × ty-n) → Nat
$curried- ⟨ n-1 , n-2 ⟩ = ? {- BinE: (n_1 + n_2) -}

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
    --------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , UNREACHABLE record { } ⟩ , ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩
  nop :
    (C : ty-context) ->
    ----------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , NOP record { } ⟩ , ⟨ [] , [] ⟩ ⟩
  drop :
    (C : ty-context) (t : ty-valtype) ->
    -----------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , DROP record { } ⟩ , ⟨ t ∷ [] , [] ⟩ ⟩
  select-expl :
    (C : ty-context) (t : ty-valtype) ->
    ----------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , SELECT ? {- OptE: ?(t) -} ⟩ , ⟨ I32 record { } ∷ t ∷ t ∷ [] , t ∷ [] ⟩ ⟩
  select-impl :
    (C : ty-context) (numtype : ty-numtype) (t : ty-valtype) ->
    ? {- CmpE: (t = (numtype <: valtype)) -} ->
    ---------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , SELECT ? {- OptE: ?() -} ⟩ , ⟨ I32 record { } ∷ t ∷ t ∷ [] , t ∷ [] ⟩ ⟩
  block :
    (C : ty-context) (bt : ty-blocktype) (instr : ty-instr) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ty-Blocktype-ok ⟨ ⟨ C , bt ⟩ , ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩ ->
    ty-InstrSeq-ok ⟨ ⟨ ? {- CompE: C ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2]*{t_2}, RETURNS ?()} -} , ? {- IterE: instr*{instr} -} ⟩ , ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩ ->
    ---------------------------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , BLOCK ⟨ bt , ? {- IterE: instr*{instr} -} ⟩ ⟩ , ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩
  loop :
    (C : ty-context) (bt : ty-blocktype) (instr : ty-instr) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ty-Blocktype-ok ⟨ ⟨ C , bt ⟩ , ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩ ->
    ty-InstrSeq-ok ⟨ ⟨ ? {- CompE: C ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_1]*{t_1}, RETURNS ?()} -} , ? {- IterE: instr*{instr} -} ⟩ , ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩ ->
    --------------------------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , LOOP ⟨ bt , ? {- IterE: instr*{instr} -} ⟩ ⟩ , ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩
  if :
    (C : ty-context) (bt : ty-blocktype) (instr-1 : ty-instr) (instr-2 : ty-instr) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ty-Blocktype-ok ⟨ ⟨ C , bt ⟩ , ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩ ->
    ty-InstrSeq-ok ⟨ ⟨ ? {- CompE: C ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2]*{t_2}, RETURNS ?()} -} , ? {- IterE: instr_1*{instr_1} -} ⟩ , ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩ ->
    ty-InstrSeq-ok ⟨ ⟨ ? {- CompE: C ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2]*{t_2}, RETURNS ?()} -} , ? {- IterE: instr_2*{instr_2} -} ⟩ , ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩ ->
    -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , IF ⟨ ⟨ bt , ? {- IterE: instr_1*{instr_1} -} ⟩ , ? {- IterE: instr_2*{instr_2} -} ⟩ ⟩ , ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩
  br :
    (C : ty-context) (l : ty-labelidx) (t : ty-valtype) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ? {- CmpE: (C.LABEL_context[l] = t*{t}) -} ->
    ----------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , BR l ⟩ , ⟨ ? {- CatE: t_1*{t_1} :: t*{t} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩
  br-if :
    (C : ty-context) (l : ty-labelidx) (t : ty-valtype) ->
    ? {- CmpE: (C.LABEL_context[l] = t*{t}) -} ->
    -------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , BR-IF l ⟩ , ⟨ ? {- CatE: t*{t} :: [I32_valtype] -} , ? {- IterE: t*{t} -} ⟩ ⟩
  return :
    (C : ty-context) (t : ty-valtype) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ? {- CmpE: (C.RETURNS_context = ?(t*{t})) -} ->
    -----------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , RETURN record { } ⟩ , ⟨ ? {- CatE: t_1*{t_1} :: t*{t} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩
  call :
    (C : ty-context) (t-1 : ty-valtype) (t-2 : ty-valtype) (x : ty-idx) ->
    ? {- CmpE: (C.FUNC_context[x] = `%->%`(t_1*{t_1}, t_2*{t_2})) -} ->
    ----------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , CALL x ⟩ , ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩
  const :
    (C : ty-context) (c-nt : ty-c-numtype) (nt : ty-numtype) ->
    -----------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , CONST ⟨ nt , c-nt ⟩ ⟩ , ⟨ [] , ? {- SubE: (nt <: valtype) -} ∷ [] ⟩ ⟩
  unop :
    (C : ty-context) (nt : ty-numtype) (unop : ty-unop-numtype) ->
    --------------------------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , UNOP ⟨ nt , unop ⟩ ⟩ , ⟨ ? {- SubE: (nt <: valtype) -} ∷ [] , ? {- SubE: (nt <: valtype) -} ∷ [] ⟩ ⟩
  binop :
    (C : ty-context) (binop : ty-binop-numtype) (nt : ty-numtype) ->
    --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , BINOP ⟨ nt , binop ⟩ ⟩ , ⟨ ? {- SubE: (nt <: valtype) -} ∷ ? {- SubE: (nt <: valtype) -} ∷ [] , ? {- SubE: (nt <: valtype) -} ∷ [] ⟩ ⟩
  testop :
    (C : ty-context) (nt : ty-numtype) (testop : ty-testop-numtype) ->
    ---------------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , TESTOP ⟨ nt , testop ⟩ ⟩ , ⟨ ? {- SubE: (nt <: valtype) -} ∷ [] , I32 record { } ∷ [] ⟩ ⟩
  relop :
    (C : ty-context) (nt : ty-numtype) (relop : ty-relop-numtype) ->
    -----------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , RELOP ⟨ nt , relop ⟩ ⟩ , ⟨ ? {- SubE: (nt <: valtype) -} ∷ ? {- SubE: (nt <: valtype) -} ∷ [] , I32 record { } ∷ [] ⟩ ⟩
  local-get :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    ? {- CmpE: (C.LOCAL_context[x] = t) -} ->
    -------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , LOCAL-GET x ⟩ , ⟨ [] , t ∷ [] ⟩ ⟩
  local-set :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    ? {- CmpE: (C.LOCAL_context[x] = t) -} ->
    -------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , LOCAL-SET x ⟩ , ⟨ t ∷ [] , [] ⟩ ⟩
  local-tee :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    ? {- CmpE: (C.LOCAL_context[x] = t) -} ->
    -------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , LOCAL-TEE x ⟩ , ⟨ t ∷ [] , t ∷ [] ⟩ ⟩
  global-get :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    ? {- CmpE: (C.GLOBAL_context[x] = `MUT%?%`(()?{}, t)) -} ->
    --------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , GLOBAL-GET x ⟩ , ⟨ [] , t ∷ [] ⟩ ⟩
  global-set :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    ? {- CmpE: (C.GLOBAL_context[x] = `MUT%?%`(?(()), t)) -} ->
    --------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , GLOBAL-SET x ⟩ , ⟨ t ∷ [] , [] ⟩ ⟩
data ty-InstrSeq-ok where
  empty :
    (C : ty-context) ->
    -------------------------------------------------------
    ty-InstrSeq-ok ⟨ ⟨ C , [] ⟩ , ⟨ [] , [] ⟩ ⟩
  seq :
    (C : ty-context) (instr-1 : ty-instr) (instr-2 : ty-instr) (t-1 : ty-valtype) (t-2 : ty-valtype) (t-3 : ty-valtype) ->
    ty-Instr-ok ⟨ ⟨ C , instr-1 ⟩ , ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩ ->
    ty-InstrSeq-ok ⟨ ⟨ C , instr-2 ∷ [] ⟩ , ⟨ ? {- IterE: t_2*{t_2} -} , ? {- IterE: t_3*{t_3} -} ⟩ ⟩ ->
    --------------------------------------------------------------------------------------------------------------------------------------
    ty-InstrSeq-ok ⟨ ⟨ C , ? {- CatE: [instr_1] :: instr_2*{} -} ⟩ , ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_3*{t_3} -} ⟩ ⟩
  weak :
    (C : ty-context) (instr : ty-instr) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ty-InstrSeq-ok ⟨ ⟨ C , ? {- IterE: instr*{instr} -} ⟩ , ⟨ ? {- IterE: t_1*{} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩ ->
    ---------------------------------------------------------------------------------------------------------------
    ty-InstrSeq-ok ⟨ ⟨ C , ? {- IterE: instr*{instr} -} ⟩ , ⟨ t-1 ∷ [] , ? {- IterE: t_2*{t_2} -} ⟩ ⟩
  frame :
    (C : ty-context) (instr : ty-instr) (t : ty-valtype) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ty-InstrSeq-ok ⟨ ⟨ C , ? {- IterE: instr*{instr} -} ⟩ , ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩ ->
    ---------------------------------------------------------------------------------------------------------------------------------------------
    ty-InstrSeq-ok ⟨ ⟨ C , ? {- IterE: instr*{instr} -} ⟩ , ⟨ ? {- CatE: t*{t} :: t_1*{t_1} -} , ? {- CatE: t*{t} :: t_2*{t_2} -} ⟩ ⟩

data ty-Expr-ok : ((ty-context × ty-expr) × ty-resulttype) → Set
data ty-Expr-ok where
  - :
    (C : ty-context) (instr : ty-instr) (t : ty-valtype) ->
    ty-InstrSeq-ok ⟨ ⟨ C , ? {- IterE: instr*{instr} -} ⟩ , ⟨ [] , ? {- IterE: t*{t} -} ⟩ ⟩ ->
    ----------------------------------------------------------------------------------
    ty-Expr-ok ⟨ ⟨ C , ? {- IterE: instr*{instr} -} ⟩ , ? {- IterE: t*{t} -} ⟩

data ty-Instr-const : (ty-context × ty-instr) → Set
data ty-Instr-const where
  const :
    (C : ty-context) (c : ty-c-numtype) (nt : ty-numtype) ->
    -----------------------------------------------
    ty-Instr-const ⟨ C , CONST ⟨ nt , c ⟩ ⟩
  global-get :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    ? {- CmpE: (C.GLOBAL_context[x] = `MUT%?%`(?(), t)) -} ->
    ---------------------------------------
    ty-Instr-const ⟨ C , GLOBAL-GET x ⟩

data ty-Expr-const : (ty-context × ty-expr) → Set
data ty-Expr-const where
  - :
    (C : ty-context) (instr : ty-instr) ->
    ? {- IterPr: ITER -} ->
    ------------------------------------------------------
    ty-Expr-const ⟨ C , ? {- IterE: instr*{instr} -} ⟩

data ty-Expr-ok-const : ((ty-context × ty-expr) × ty-valtype) → Set
data ty-Expr-ok-const where
  - :
    (C : ty-context) (expr : ty-expr) (t : ty-valtype) ->
    ty-Expr-ok ⟨ ⟨ C , expr ⟩ , t ∷ [] ⟩ ->
    ty-Expr-const ⟨ C , expr ⟩ ->
    ---------------------------------------------
    ty-Expr-ok-const ⟨ ⟨ C , expr ⟩ , t ⟩

data ty-Func-ok : ((ty-context × ty-func) × ty-functype) → Set
data ty-Func-ok where
  - :
    (C : ty-context) (expr : ty-expr) (ft : ty-functype) (t : ty-valtype) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    ? {- CmpE: (ft = `%->%`(t_1*{t_1}, t_2*{t_2})) -} ->
    ty-Functype-ok ft ->
    ty-Expr-ok ⟨ ⟨ ? {- CompE: C ++ {FUNC [], GLOBAL [], LOCAL t_1*{t_1} :: t*{t}, LABEL [], RETURNS ?()} ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2*{t_2}], RETURNS ?()} ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [], RETURNS ?(t_2*{t_2})} -} , expr ⟩ , ? {- IterE: t_2*{t_2} -} ⟩ ->
    ------------------------------------------------------------------------------------
    ty-Func-ok ⟨ ⟨ C , ⟨ ⟨ ft , ? {- IterE: t*{t} -} ⟩ , expr ⟩ ⟩ , ft ⟩

data ty-Global-ok : ((ty-context × ty-global) × ty-globaltype) → Set
data ty-Global-ok where
  - :
    (C : ty-context) (expr : ty-expr) (gt : ty-globaltype) (t : ty-valtype) ->
    ty-Globaltype-ok gt ->
    ? {- CmpE: (gt = `MUT%?%`(()?{}, t)) -} ->
    ty-Expr-ok-const ⟨ ⟨ C , expr ⟩ , t ⟩ ->
    -------------------------------------------------------
    ty-Global-ok ⟨ ⟨ C , ⟨ gt , expr ⟩ ⟩ , gt ⟩

data ty-Start-ok : (ty-context × ty-start) → Set
data ty-Start-ok where
  - :
    (C : ty-context) (x : ty-idx) ->
    ? {- CmpE: (C.FUNC_context[x] = `%->%`([], [])) -} ->
    -------------------------
    ty-Start-ok ⟨ C , x ⟩

data ty-Module-ok : ty-module → Set
data ty-Module-ok where
  - :
    (C : ty-context) (ft : ty-functype) (func : ty-func) (global : ty-global) (gt : ty-globaltype) (start : ty-start) ->
    ? {- CmpE: (C = {FUNC ft*{ft}, GLOBAL gt*{gt}, LOCAL [], LABEL [], RETURNS ?()}) -} ->
    ? {- IterPr: ITER -} ->
    ? {- IterPr: ITER -} ->
    ? {- IterPr: ITER -} ->
    ? {- CmpE: (|start*{start}| <= 1) -} ->
    -----------------------------------------------------------------------------------------------------------------------
    ty-Module-ok ⟨ ⟨ ? {- IterE: func*{func} -} , ? {- IterE: global*{global} -} ⟩ , ? {- IterE: start*{start} -} ⟩

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
$default- _ {- CaseE: I32_valtype -} = CONST ⟨ I32 record { } , 0 ⟩

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
$funcaddr ⟨ s , f ⟩ = ? {- DotE: f.MODULE_frame.FUNC_moduleinst -}

$funcinst : ty-state → List ty-funcinst
$funcinst ⟨ s , f ⟩ = ? {- DotE: s.FUNC_store -}

$func : (ty-state × ty-funcidx) → ty-funcinst
$func ⟨ ⟨ s , f ⟩ , x ⟩ = ? {- IdxE: s.FUNC_store[f.MODULE_frame.FUNC_moduleinst[x]] -}

$global : (ty-state × ty-globalidx) → ty-globalinst
$global ⟨ ⟨ s , f ⟩ , x ⟩ = ? {- IdxE: s.GLOBAL_store[f.MODULE_frame.GLOBAL_moduleinst[x]] -}

$local : (ty-state × ty-localidx) → ty-val
$local ⟨ ⟨ s , f ⟩ , x ⟩ = ? {- IdxE: f.LOCAL_frame[x] -}

$with-local : ((ty-state × ty-localidx) × ty-val) → ty-state
$with-local ⟨ ⟨ ⟨ s , f ⟩ , x ⟩ , v ⟩ = ⟨ s , ? {- UpdE: f[LOCAL_frame[x] = v] -} ⟩

$with-global : ((ty-state × ty-globalidx) × ty-val) → ty-state
$with-global ⟨ ⟨ ⟨ s , f ⟩ , x ⟩ , v ⟩ = ⟨ ? {- UpdE: s[GLOBAL_store[f.MODULE_frame.GLOBAL_moduleinst[x]] = v] -} , f ⟩

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
    ---------------------------------------------------------------------------
    ty-Step-pure ⟨ UNREACHABLE record { } ∷ [] , TRAP record { } ∷ [] ⟩
  nop :
    -----------------------------------------------
    ty-Step-pure ⟨ NOP record { } ∷ [] , [] ⟩
  drop :
    (val : ty-val) ->
    --------------------------------------------------------------------------------------
    ty-Step-pure ⟨ DROP record { } ∷ ? {- SubE: (val <: admininstr) -} ∷ [] , [] ⟩
  select-true :
    (c : ty-c-numtype) (t : ty-valtype) (val-1 : ty-val) (val-2 : ty-val) ->
    ? {- CmpE: (c =/= 0) -} ->
    -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ SELECT ? {- IterE: t?{t} -} ∷ CONST ⟨ I32 record { } , c ⟩ ∷ ? {- SubE: (val_2 <: admininstr) -} ∷ ? {- SubE: (val_1 <: admininstr) -} ∷ [] , ? {- SubE: (val_1 <: admininstr) -} ∷ [] ⟩
  select-false :
    (c : ty-c-numtype) (t : ty-valtype) (val-1 : ty-val) (val-2 : ty-val) ->
    ? {- CmpE: (c = 0) -} ->
    -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ SELECT ? {- IterE: t?{t} -} ∷ CONST ⟨ I32 record { } , c ⟩ ∷ ? {- SubE: (val_2 <: admininstr) -} ∷ ? {- SubE: (val_1 <: admininstr) -} ∷ [] , ? {- SubE: (val_2 <: admininstr) -} ∷ [] ⟩
  block :
    (bt : ty-blocktype) (instr : ty-instr) (k : Nat) (n : ty-n) (t-1 : ty-valtype) (t-2 : ty-valtype) (val : ty-val) ->
    ? {- CmpE: (bt = `%->%`(t_1^k{t_1}, t_2^n{t_2})) -} ->
    -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- CatE: (val <: admininstr)^k{val} :: [BLOCK_admininstr(bt, instr*{instr})] -} , LABEL- ⟨ ⟨ n , [] ⟩ , ? {- CatE: (val <: admininstr)^k{val} :: (instr <: admininstr)*{instr} -} ⟩ ∷ [] ⟩
  loop :
    (bt : ty-blocktype) (instr : ty-instr) (k : Nat) (n : ty-n) (t-1 : ty-valtype) (t-2 : ty-valtype) (val : ty-val) ->
    ? {- CmpE: (bt = `%->%`(t_1^k{t_1}, t_2^n{t_2})) -} ->
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- CatE: (val <: admininstr)^k{val} :: [LOOP_admininstr(bt, instr*{instr})] -} , LABEL- ⟨ ⟨ n , LOOP ⟨ bt , ? {- IterE: instr*{instr} -} ⟩ ∷ [] ⟩ , ? {- CatE: (val <: admininstr)^k{val} :: (instr <: admininstr)*{instr} -} ⟩ ∷ [] ⟩
  if-true :
    (bt : ty-blocktype) (c : ty-c-numtype) (instr-1 : ty-instr) (instr-2 : ty-instr) ->
    ? {- CmpE: (c =/= 0) -} ->
    -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ IF ⟨ ⟨ bt , ? {- IterE: instr_1*{instr_1} -} ⟩ , ? {- IterE: instr_2*{instr_2} -} ⟩ ∷ CONST ⟨ I32 record { } , c ⟩ ∷ [] , BLOCK ⟨ bt , ? {- IterE: instr_1*{instr_1} -} ⟩ ∷ [] ⟩
  if-false :
    (bt : ty-blocktype) (c : ty-c-numtype) (instr-1 : ty-instr) (instr-2 : ty-instr) ->
    ? {- CmpE: (c = 0) -} ->
    -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ IF ⟨ ⟨ bt , ? {- IterE: instr_1*{instr_1} -} ⟩ , ? {- IterE: instr_2*{instr_2} -} ⟩ ∷ CONST ⟨ I32 record { } , c ⟩ ∷ [] , BLOCK ⟨ bt , ? {- IterE: instr_2*{instr_2} -} ⟩ ∷ [] ⟩
  label-vals :
    (instr : ty-instr) (n : ty-n) (val : ty-val) ->
    -------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ LABEL- ⟨ ⟨ n , ? {- IterE: instr*{instr} -} ⟩ , ? {- IterE: (val <: admininstr)*{val} -} ⟩ ∷ [] , ? {- IterE: (val <: admininstr)*{val} -} ⟩
  br-zero :
    (instr : ty-instr) (instr' : ty-instr) (n : ty-n) (val : ty-val) (val' : ty-val) ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ LABEL- ⟨ ⟨ n , ? {- IterE: instr'*{instr'} -} ⟩ , ? {- CatE: (val' <: admininstr)*{val'} :: (val <: admininstr)^n{val} :: [BR_admininstr(0)] :: (instr <: admininstr)*{instr} -} ⟩ ∷ [] , ? {- CatE: (val <: admininstr)^n{val} :: (instr' <: admininstr)*{instr'} -} ⟩
  br-succ :
    (instr : ty-instr) (instr' : ty-instr) (l : ty-labelidx) (n : ty-n) (val : ty-val) ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ LABEL- ⟨ ⟨ n , ? {- IterE: instr'*{instr'} -} ⟩ , ? {- CatE: (val <: admininstr)*{val} :: [BR_admininstr(l + 1)] :: (instr <: admininstr)*{instr} -} ⟩ ∷ [] , ? {- CatE: (val <: admininstr)*{val} :: [BR_admininstr(l)] -} ⟩
  br-if-true :
    (c : ty-c-numtype) (l : ty-labelidx) ->
    ? {- CmpE: (c =/= 0) -} ->
    --------------------------------------------------------------------------------------
    ty-Step-pure ⟨ BR-IF l ∷ CONST ⟨ I32 record { } , c ⟩ ∷ [] , BR l ∷ [] ⟩
  br-if-false :
    (c : ty-c-numtype) (l : ty-labelidx) ->
    ? {- CmpE: (c = 0) -} ->
    -----------------------------------------------------------------------------
    ty-Step-pure ⟨ BR-IF l ∷ CONST ⟨ I32 record { } , c ⟩ ∷ [] , [] ⟩
  frame-vals :
    (f : ty-frame) (n : ty-n) (val : ty-val) ->
    ------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ FRAME- ⟨ ⟨ n , f ⟩ , ? {- IterE: (val <: admininstr)^n{val} -} ⟩ ∷ [] , ? {- IterE: (val <: admininstr)^n{val} -} ⟩
  return-frame :
    (f : ty-frame) (instr : ty-instr) (n : ty-n) (val : ty-val) (val' : ty-val) ->
    --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ FRAME- ⟨ ⟨ n , f ⟩ , ? {- CatE: (val' <: admininstr)*{val'} :: (val <: admininstr)^n{val} :: [RETURN_admininstr] :: (instr <: admininstr)*{instr} -} ⟩ ∷ [] , ? {- IterE: (val <: admininstr)^n{val} -} ⟩
  return-label :
    (instr : ty-instr) (instr' : ty-instr) (k : Nat) (val : ty-val) ->
    --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ LABEL- ⟨ ⟨ k , ? {- IterE: instr'*{instr'} -} ⟩ , ? {- CatE: (val <: admininstr)*{val} :: [RETURN_admininstr] :: (instr <: admininstr)*{instr} -} ⟩ ∷ [] , ? {- CatE: (val <: admininstr)*{val} :: [RETURN_admininstr] -} ⟩
  unop-val :
    (c : ty-c-numtype) (c-1 : ty-c-numtype) (nt : ty-numtype) (unop : ty-unop-numtype) ->
    ? {- CmpE: ($unop(unop, nt, c_1) = [c]) -} ->
    -----------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ UNOP ⟨ nt , unop ⟩ ∷ CONST ⟨ nt , c-1 ⟩ ∷ [] , CONST ⟨ nt , c ⟩ ∷ [] ⟩
  unop-trap :
    (c-1 : ty-c-numtype) (nt : ty-numtype) (unop : ty-unop-numtype) ->
    ? {- CmpE: ($unop(unop, nt, c_1) = []) -} ->
    ------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ UNOP ⟨ nt , unop ⟩ ∷ CONST ⟨ nt , c-1 ⟩ ∷ [] , TRAP record { } ∷ [] ⟩
  binop-val :
    (binop : ty-binop-numtype) (c : ty-c-numtype) (c-1 : ty-c-numtype) (c-2 : ty-c-numtype) (nt : ty-numtype) ->
    ? {- CmpE: ($binop(binop, nt, c_1, c_2) = [c]) -} ->
    ----------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ BINOP ⟨ nt , binop ⟩ ∷ CONST ⟨ nt , c-2 ⟩ ∷ CONST ⟨ nt , c-1 ⟩ ∷ [] , CONST ⟨ nt , c ⟩ ∷ [] ⟩
  binop-trap :
    (binop : ty-binop-numtype) (c-1 : ty-c-numtype) (c-2 : ty-c-numtype) (nt : ty-numtype) ->
    ? {- CmpE: ($binop(binop, nt, c_1, c_2) = []) -} ->
    -----------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ BINOP ⟨ nt , binop ⟩ ∷ CONST ⟨ nt , c-2 ⟩ ∷ CONST ⟨ nt , c-1 ⟩ ∷ [] , TRAP record { } ∷ [] ⟩
  testop :
    (c : ty-c-numtype) (c-1 : ty-c-numtype) (nt : ty-numtype) (testop : ty-testop-numtype) ->
    ? {- CmpE: (c = $testop(testop, nt, c_1)) -} ->
    ---------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ TESTOP ⟨ nt , testop ⟩ ∷ CONST ⟨ nt , c-1 ⟩ ∷ [] , CONST ⟨ I32 record { } , c ⟩ ∷ [] ⟩
  relop :
    (c : ty-c-numtype) (c-1 : ty-c-numtype) (c-2 : ty-c-numtype) (nt : ty-numtype) (relop : ty-relop-numtype) ->
    ? {- CmpE: (c = $relop(relop, nt, c_1, c_2)) -} ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ RELOP ⟨ nt , relop ⟩ ∷ CONST ⟨ nt , c-2 ⟩ ∷ CONST ⟨ nt , c-1 ⟩ ∷ [] , CONST ⟨ I32 record { } , c ⟩ ∷ [] ⟩
  local-tee :
    (val : ty-val) (x : ty-idx) ->
    ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ LOCAL-TEE x ∷ ? {- SubE: (val <: admininstr) -} ∷ [] , LOCAL-SET x ∷ ? {- SubE: (val <: admininstr) -} ∷ ? {- SubE: (val <: admininstr) -} ∷ [] ⟩

data ty-Step-read : (ty-config × List ty-admininstr) → Set
data ty-Step-read where
  call :
    (x : ty-idx) (z : ty-state) ->
    -----------------------------------------------------------------------------------------------
    ty-Step-read ⟨ ⟨ z , CALL x ∷ [] ⟩ , CALL-ADDR ? {- IdxE: $funcaddr(z)[x] -} ∷ [] ⟩
  call-addr :
    (a : ty-addr) (f : ty-frame) (instr : ty-instr) (k : Nat) (m : ty-moduleinst) (n : ty-n) (t : ty-valtype) (t-1 : ty-valtype) (t-2 : ty-valtype) (val : ty-val) (z : ty-state) ->
    ? {- CmpE: ($funcinst(z)[a] = `%;%`(m, `FUNC%%*%`(`%->%`(t_1^k{t_1}, t_2^n{t_2}), t*{t}, instr*{instr}))) -} ->
    ? {- CmpE: (f = {LOCAL val^k{val} :: $default_(t)*{t}, MODULE m}) -} ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-read ⟨ ⟨ z , ? {- CatE: (val <: admininstr)^k{val} :: [CALL_ADDR_admininstr(a)] -} ⟩ , FRAME- ⟨ ⟨ n , f ⟩ , LABEL- ⟨ ⟨ n , [] ⟩ , ? {- IterE: (instr <: admininstr)*{instr} -} ⟩ ∷ [] ⟩ ∷ [] ⟩
  local-get :
    (x : ty-idx) (z : ty-state) ->
    -------------------------------------------------------------------------------------------------------
    ty-Step-read ⟨ ⟨ z , LOCAL-GET x ∷ [] ⟩ , ? {- SubE: ($local(z, x) <: admininstr) -} ∷ [] ⟩
  global-get :
    (x : ty-idx) (z : ty-state) ->
    ---------------------------------------------------------------------------------------------------------
    ty-Step-read ⟨ ⟨ z , GLOBAL-GET x ∷ [] ⟩ , ? {- SubE: ($global(z, x) <: admininstr) -} ∷ [] ⟩

data ty-Step : (ty-config × ty-config) → Set
data ty-Step where
  pure :
    (instr : ty-instr) (instr' : ty-instr) (z : ty-state) ->
    ty-Step-pure ⟨ ? {- IterE: (instr <: admininstr)*{instr} -} , ? {- IterE: (instr' <: admininstr)*{instr'} -} ⟩ ->
    -------------------------------------------------------------------------------------------------------------------------------------
    ty-Step ⟨ ⟨ z , ? {- IterE: (instr <: admininstr)*{instr} -} ⟩ , ⟨ z , ? {- IterE: (instr' <: admininstr)*{instr'} -} ⟩ ⟩
  read :
    (instr : ty-instr) (instr' : ty-instr) (z : ty-state) ->
    ty-Step-read ⟨ ⟨ z , ? {- IterE: (instr <: admininstr)*{instr} -} ⟩ , ? {- IterE: (instr' <: admininstr)*{instr'} -} ⟩ ->
    -------------------------------------------------------------------------------------------------------------------------------------
    ty-Step ⟨ ⟨ z , ? {- IterE: (instr <: admininstr)*{instr} -} ⟩ , ⟨ z , ? {- IterE: (instr' <: admininstr)*{instr'} -} ⟩ ⟩
  local-set :
    (val : ty-val) (x : ty-idx) (z : ty-state) ->
    -------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step ⟨ ⟨ z , LOCAL-SET x ∷ ? {- SubE: (val <: admininstr) -} ∷ [] ⟩ , ⟨ $with-local ⟨ ⟨ z , x ⟩ , val ⟩ , [] ⟩ ⟩
  global-set :
    (val : ty-val) (x : ty-idx) (z : ty-state) ->
    ---------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step ⟨ ⟨ z , GLOBAL-SET x ∷ ? {- SubE: (val <: admininstr) -} ∷ [] ⟩ , ⟨ $with-global ⟨ ⟨ z , x ⟩ , val ⟩ , [] ⟩ ⟩
$ agda output.agda | sed -e "s/\/.*\/_build\///g"
Checking output (default/test-agda/output.agda).
default/test-agda/output.agda:322,1-325,72
Termination checking failed for the following functions:
  $min
Problematic calls:
  $min ⟨ ?0 (i = i) (j = j) , ?1 (i = i) (j = j) ⟩
    (at default/test-agda/output.agda:325,18-22)
Unsolved interaction metas at the following locations:
  default/test-agda/output.agda:325,25-26
  default/test-agda/output.agda:325,49-50
  default/test-agda/output.agda:334,27-28
  default/test-agda/output.agda:412,54-55
  default/test-agda/output.agda:412,81-82
  default/test-agda/output.agda:424,32-33
  default/test-agda/output.agda:427,5-6
  default/test-agda/output.agda:429,32-33
  default/test-agda/output.agda:432,38-39
  default/test-agda/output.agda:432,65-66
  default/test-agda/output.agda:433,24-25
  default/test-agda/output.agda:433,109-110
  default/test-agda/output.agda:433,144-145
  default/test-agda/output.agda:433,171-172
  default/test-agda/output.agda:435,38-39
  default/test-agda/output.agda:435,75-76
  default/test-agda/output.agda:435,102-103
  default/test-agda/output.agda:438,38-39
  default/test-agda/output.agda:438,65-66
  default/test-agda/output.agda:439,24-25
  default/test-agda/output.agda:439,109-110
  default/test-agda/output.agda:439,144-145
  default/test-agda/output.agda:439,171-172
  default/test-agda/output.agda:441,37-38
  default/test-agda/output.agda:441,74-75
  default/test-agda/output.agda:441,101-102
  default/test-agda/output.agda:444,38-39
  default/test-agda/output.agda:444,65-66
  default/test-agda/output.agda:445,24-25
  default/test-agda/output.agda:445,109-110
  default/test-agda/output.agda:445,148-149
  default/test-agda/output.agda:445,175-176
  default/test-agda/output.agda:446,24-25
  default/test-agda/output.agda:446,109-110
  default/test-agda/output.agda:446,148-149
  default/test-agda/output.agda:446,175-176
  default/test-agda/output.agda:448,37-38
  default/test-agda/output.agda:448,74-75
  default/test-agda/output.agda:448,115-116
  default/test-agda/output.agda:448,142-143
  default/test-agda/output.agda:451,5-6
  default/test-agda/output.agda:453,36-37
  default/test-agda/output.agda:453,71-72
  default/test-agda/output.agda:456,5-6
  default/test-agda/output.agda:458,39-40
  default/test-agda/output.agda:458,78-79
  default/test-agda/output.agda:461,5-6
  default/test-agda/output.agda:463,49-50
  default/test-agda/output.agda:463,84-85
  default/test-agda/output.agda:466,5-6
  default/test-agda/output.agda:468,38-39
  default/test-agda/output.agda:468,65-66
  default/test-agda/output.agda:472,56-57
  default/test-agda/output.agda:476,50-51
  default/test-agda/output.agda:476,87-88
  default/test-agda/output.agda:480,52-53
  default/test-agda/output.agda:480,84-85
  default/test-agda/output.agda:480,121-122
  default/test-agda/output.agda:484,54-55
  default/test-agda/output.agda:488,52-53
  default/test-agda/output.agda:488,84-85
  default/test-agda/output.agda:491,5-6
  default/test-agda/output.agda:496,5-6
  default/test-agda/output.agda:501,5-6
  default/test-agda/output.agda:506,5-6
  default/test-agda/output.agda:511,5-6
  default/test-agda/output.agda:521,39-40
  default/test-agda/output.agda:521,66-67
  default/test-agda/output.agda:522,47-48
  default/test-agda/output.agda:522,74-75
  default/test-agda/output.agda:524,28-29
  default/test-agda/output.agda:524,72-73
  default/test-agda/output.agda:524,99-100
  default/test-agda/output.agda:527,28-29
  default/test-agda/output.agda:527,63-64
  default/test-agda/output.agda:527,87-88
  default/test-agda/output.agda:529,28-29
  default/test-agda/output.agda:529,74-75
  default/test-agda/output.agda:532,28-29
  default/test-agda/output.agda:532,63-64
  default/test-agda/output.agda:532,90-91
  default/test-agda/output.agda:534,28-29
  default/test-agda/output.agda:534,63-64
  default/test-agda/output.agda:534,98-99
  default/test-agda/output.agda:540,28-29
  default/test-agda/output.agda:540,68-69
  default/test-agda/output.agda:542,24-25
  default/test-agda/output.agda:542,57-58
  default/test-agda/output.agda:552,5-6
  default/test-agda/output.agda:560,5-6
  default/test-agda/output.agda:562,25-26
  default/test-agda/output.agda:577,5-6
  default/test-agda/output.agda:579,20-21
  default/test-agda/output.agda:579,253-254
  default/test-agda/output.agda:581,33-34
  default/test-agda/output.agda:588,5-6
  default/test-agda/output.agda:597,5-6
  default/test-agda/output.agda:605,5-6
  default/test-agda/output.agda:606,5-6
  default/test-agda/output.agda:607,5-6
  default/test-agda/output.agda:608,5-6
  default/test-agda/output.agda:609,5-6
  default/test-agda/output.agda:611,22-23
  default/test-agda/output.agda:611,51-52
  default/test-agda/output.agda:611,86-87
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
  default/test-agda/output.agda:848,38-39
  default/test-agda/output.agda:851,5-6
  default/test-agda/output.agda:853,27-28
  default/test-agda/output.agda:853,81-82
  default/test-agda/output.agda:853,119-120
  default/test-agda/output.agda:853,162-163
  default/test-agda/output.agda:856,5-6
  default/test-agda/output.agda:858,27-28
  default/test-agda/output.agda:858,81-82
  default/test-agda/output.agda:858,119-120
  default/test-agda/output.agda:858,162-163
  default/test-agda/output.agda:861,5-6
  default/test-agda/output.agda:863,20-21
  default/test-agda/output.agda:863,126-127
  default/test-agda/output.agda:866,5-6
  default/test-agda/output.agda:868,20-21
  default/test-agda/output.agda:868,130-131
  default/test-agda/output.agda:868,170-171
  default/test-agda/output.agda:871,5-6
  default/test-agda/output.agda:873,32-33
  default/test-agda/output.agda:873,69-70
  default/test-agda/output.agda:873,155-156
  default/test-agda/output.agda:876,5-6
  default/test-agda/output.agda:878,32-33
  default/test-agda/output.agda:878,69-70
  default/test-agda/output.agda:878,155-156
  default/test-agda/output.agda:882,35-36
  default/test-agda/output.agda:882,68-69
  default/test-agda/output.agda:882,118-119
  default/test-agda/output.agda:886,35-36
  default/test-agda/output.agda:886,70-71
  default/test-agda/output.agda:886,206-207
  default/test-agda/output.agda:890,35-36
  default/test-agda/output.agda:890,70-71
  default/test-agda/output.agda:890,178-179
  default/test-agda/output.agda:893,5-6
  default/test-agda/output.agda:898,5-6
  default/test-agda/output.agda:904,41-42
  default/test-agda/output.agda:904,92-93
  default/test-agda/output.agda:908,41-42
  default/test-agda/output.agda:908,178-179
  default/test-agda/output.agda:912,35-36
  default/test-agda/output.agda:912,70-71
  default/test-agda/output.agda:912,175-176
  default/test-agda/output.agda:915,5-6
  default/test-agda/output.agda:920,5-6
  default/test-agda/output.agda:925,5-6
  default/test-agda/output.agda:930,5-6
  default/test-agda/output.agda:935,5-6
  default/test-agda/output.agda:940,5-6
  default/test-agda/output.agda:946,34-35
  default/test-agda/output.agda:946,89-90
  default/test-agda/output.agda:946,125-126
  default/test-agda/output.agda:953,52-53
  default/test-agda/output.agda:956,5-6
  default/test-agda/output.agda:957,5-6
  default/test-agda/output.agda:959,26-27
  default/test-agda/output.agda:959,143-144
  default/test-agda/output.agda:963,47-48
  default/test-agda/output.agda:967,48-49
  default/test-agda/output.agda:973,20-21
  default/test-agda/output.agda:973,67-68
  default/test-agda/output.agda:975,21-22
  default/test-agda/output.agda:975,76-77
  default/test-agda/output.agda:978,26-27
  default/test-agda/output.agda:978,75-76
  default/test-agda/output.agda:980,21-22
  default/test-agda/output.agda:980,76-77
  default/test-agda/output.agda:984,35-36
  default/test-agda/output.agda:988,36-37
```

The `sed` incantation is needed to remove (user-specific) absolute paths in Agda output.
