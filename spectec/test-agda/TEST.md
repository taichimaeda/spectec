# Preview

```sh
$ patch -s -p0 -i ../spec/minispec.patch -d ../spec --read-only=ignore
$ dune exec ../src/exe-watsup/main.exe -- --agda ../spec/*.watsup -o output.agda
$ patch -R -s -p0 -i ../spec/minispec.patch -d ../spec --read-only=ignore
$ cat output.agda
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Unit

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B
data _===_ {A : Set} : A -> A -> Set where
data _=/=_ {A : Set} : A -> A -> Set where
data _<<_ {A : Set} : A -> A -> Set where
data _>_ {A : Set} : A -> A -> Set where
data _<=_ {A : Set} : A -> A -> Set where
data _>=_ {A : Set} : A -> A -> Set where

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
ty-globaltype  = ((Maybe (⊤)) × ty-valtype)

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
    (ty-blocktype × (List ty-instr)) ->
    --------
    ty-instr
  LOOP :
    (ty-blocktype × (List ty-instr)) ->
    --------
    ty-instr
  IF :
    ((ty-blocktype × (List ty-instr)) × (List ty-instr)) ->
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
ty-func  = ((ty-functype × (List ty-valtype)) × ty-expr)

ty-global : Set
ty-global  = (ty-globaltype × ty-expr)

ty-start : Set
ty-start  = ty-funcidx

ty-module : Set
ty-module  = (((List ty-func) × (List ty-global)) × (List ty-start))

$Ki : (⊤) → Nat
$Ki _ = 1024

$min : ((Nat × Nat)) → Nat
$min ⟨ 0 , j ⟩ = 0
$min ⟨ i , 0 ⟩ = 0
$min ⟨ i , j ⟩ = $min ⟨ (_-_ i) 1 , (_-_ j) 1 ⟩

$size : ty-valtype → Nat
$size (I32 _) = 32

$test-sub-ATOM-22 : ty-n → Nat
$test-sub-ATOM-22 n-3-ATOM-y = 0

$curried- : ((ty-n × ty-n)) → Nat
$curried- ⟨ n-1 , n-2 ⟩ = (_+_ n-1) n-2

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

data ty-Blocktype-ok : (((ty-context × ty-blocktype) × ty-functype)) → Set
data ty-Blocktype-ok where
  - :
    (C : ty-context) (ft : ty-functype) ->
    ty-Functype-ok ft ->
    -------------------------------------------
    ty-Blocktype-ok ⟨ ⟨ C , ft ⟩ , ft ⟩

data ty-Instr-ok : (((ty-context × ty-instr) × ty-functype)) → Set
data ty-InstrSeq-ok : (((ty-context × (List ty-instr)) × ty-functype)) → Set
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
    ------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , SELECT (just t) ⟩ , ⟨ t ∷ (t ∷ ((I32 record { }) ∷ [])) , t ∷ [] ⟩ ⟩
  select-impl :
    (C : ty-context) (numtype : ty-numtype) (t : ty-valtype) ->
    (_===_ t) ? {- SubE: (numtype <: valtype) -} ->
    -----------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , SELECT nothing ⟩ , ⟨ t ∷ (t ∷ ((I32 record { }) ∷ [])) , t ∷ [] ⟩ ⟩
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
    (_===_ ? {- IdxE: C.LABEL_context[l] -}) ? {- IterE: t*{t} -} ->
    ----------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , BR l ⟩ , ⟨ ? {- CatE: t_1*{t_1} :: t*{t} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩
  br-if :
    (C : ty-context) (l : ty-labelidx) (t : ty-valtype) ->
    (_===_ ? {- IdxE: C.LABEL_context[l] -}) ? {- IterE: t*{t} -} ->
    -------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , BR-IF l ⟩ , ⟨ ? {- CatE: t*{t} :: [I32_valtype] -} , ? {- IterE: t*{t} -} ⟩ ⟩
  return :
    (C : ty-context) (t : ty-valtype) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    (_===_ (ty-context.RETURNS C)) (just ? {- IterE: t*{t} -}) ->
    -----------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , RETURN record { } ⟩ , ⟨ ? {- CatE: t_1*{t_1} :: t*{t} -} , ? {- IterE: t_2*{t_2} -} ⟩ ⟩
  call :
    (C : ty-context) (t-1 : ty-valtype) (t-2 : ty-valtype) (x : ty-idx) ->
    (_===_ ? {- IdxE: C.FUNC_context[x] -}) ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_2*{t_2} -} ⟩ ->
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
    ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , BINOP ⟨ nt , binop ⟩ ⟩ , ⟨ ? {- SubE: (nt <: valtype) -} ∷ (? {- SubE: (nt <: valtype) -} ∷ []) , ? {- SubE: (nt <: valtype) -} ∷ [] ⟩ ⟩
  testop :
    (C : ty-context) (nt : ty-numtype) (testop : ty-testop-numtype) ->
    -----------------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , TESTOP ⟨ nt , testop ⟩ ⟩ , ⟨ ? {- SubE: (nt <: valtype) -} ∷ [] , (I32 record { }) ∷ [] ⟩ ⟩
  relop :
    (C : ty-context) (nt : ty-numtype) (relop : ty-relop-numtype) ->
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , RELOP ⟨ nt , relop ⟩ ⟩ , ⟨ ? {- SubE: (nt <: valtype) -} ∷ (? {- SubE: (nt <: valtype) -} ∷ []) , (I32 record { }) ∷ [] ⟩ ⟩
  local-get :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    (_===_ ? {- IdxE: C.LOCAL_context[x] -}) t ->
    -------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , LOCAL-GET x ⟩ , ⟨ [] , t ∷ [] ⟩ ⟩
  local-set :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    (_===_ ? {- IdxE: C.LOCAL_context[x] -}) t ->
    -------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , LOCAL-SET x ⟩ , ⟨ t ∷ [] , [] ⟩ ⟩
  local-tee :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    (_===_ ? {- IdxE: C.LOCAL_context[x] -}) t ->
    -------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , LOCAL-TEE x ⟩ , ⟨ t ∷ [] , t ∷ [] ⟩ ⟩
  global-get :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    (_===_ ? {- IdxE: C.GLOBAL_context[x] -}) ⟨ ? {- IterE: ()?{} -} , t ⟩ ->
    --------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , GLOBAL-GET x ⟩ , ⟨ [] , t ∷ [] ⟩ ⟩
  global-set :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    (_===_ ? {- IdxE: C.GLOBAL_context[x] -}) ⟨ just record { } , t ⟩ ->
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

data ty-Expr-ok : (((ty-context × ty-expr) × ty-resulttype)) → Set
data ty-Expr-ok where
  - :
    (C : ty-context) (instr : ty-instr) (t : ty-valtype) ->
    ty-InstrSeq-ok ⟨ ⟨ C , ? {- IterE: instr*{instr} -} ⟩ , ⟨ [] , ? {- IterE: t*{t} -} ⟩ ⟩ ->
    ----------------------------------------------------------------------------------
    ty-Expr-ok ⟨ ⟨ C , ? {- IterE: instr*{instr} -} ⟩ , ? {- IterE: t*{t} -} ⟩

data ty-Instr-const : ((ty-context × ty-instr)) → Set
data ty-Instr-const where
  const :
    (C : ty-context) (c : ty-c-numtype) (nt : ty-numtype) ->
    -----------------------------------------------
    ty-Instr-const ⟨ C , CONST ⟨ nt , c ⟩ ⟩
  global-get :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    (_===_ ? {- IdxE: C.GLOBAL_context[x] -}) ⟨ nothing , t ⟩ ->
    ---------------------------------------
    ty-Instr-const ⟨ C , GLOBAL-GET x ⟩

data ty-Expr-const : ((ty-context × ty-expr)) → Set
data ty-Expr-const where
  - :
    (C : ty-context) (instr : ty-instr) ->
    ? {- IterPr: ITER -} ->
    ------------------------------------------------------
    ty-Expr-const ⟨ C , ? {- IterE: instr*{instr} -} ⟩

data ty-Expr-ok-const : (((ty-context × ty-expr) × ty-valtype)) → Set
data ty-Expr-ok-const where
  - :
    (C : ty-context) (expr : ty-expr) (t : ty-valtype) ->
    ty-Expr-ok ⟨ ⟨ C , expr ⟩ , t ∷ [] ⟩ ->
    ty-Expr-const ⟨ C , expr ⟩ ->
    ---------------------------------------------
    ty-Expr-ok-const ⟨ ⟨ C , expr ⟩ , t ⟩

data ty-Func-ok : (((ty-context × ty-func) × ty-functype)) → Set
data ty-Func-ok where
  - :
    (C : ty-context) (expr : ty-expr) (ft : ty-functype) (t : ty-valtype) (t-1 : ty-valtype) (t-2 : ty-valtype) ->
    (_===_ ft) ⟨ ? {- IterE: t_1*{t_1} -} , ? {- IterE: t_2*{t_2} -} ⟩ ->
    ty-Functype-ok ft ->
    ty-Expr-ok ⟨ ⟨ ? {- CompE: C ++ {FUNC [], GLOBAL [], LOCAL t_1*{t_1} :: t*{t}, LABEL [], RETURNS ?()} ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2*{t_2}], RETURNS ?()} ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [], RETURNS ?(t_2*{t_2})} -} , expr ⟩ , ? {- IterE: t_2*{t_2} -} ⟩ ->
    ------------------------------------------------------------------------------------
    ty-Func-ok ⟨ ⟨ C , ⟨ ⟨ ft , ? {- IterE: t*{t} -} ⟩ , expr ⟩ ⟩ , ft ⟩

data ty-Global-ok : (((ty-context × ty-global) × ty-globaltype)) → Set
data ty-Global-ok where
  - :
    (C : ty-context) (expr : ty-expr) (gt : ty-globaltype) (t : ty-valtype) ->
    ty-Globaltype-ok gt ->
    (_===_ gt) ⟨ ? {- IterE: ()?{} -} , t ⟩ ->
    ty-Expr-ok-const ⟨ ⟨ C , expr ⟩ , t ⟩ ->
    -------------------------------------------------------
    ty-Global-ok ⟨ ⟨ C , ⟨ gt , expr ⟩ ⟩ , gt ⟩

data ty-Start-ok : ((ty-context × ty-start)) → Set
data ty-Start-ok where
  - :
    (C : ty-context) (x : ty-idx) ->
    (_===_ ? {- IdxE: C.FUNC_context[x] -}) ⟨ [] , [] ⟩ ->
    -------------------------
    ty-Start-ok ⟨ C , x ⟩

data ty-Module-ok : ty-module → Set
data ty-Module-ok where
  - :
    (C : ty-context) (ft : ty-functype) (func : ty-func) (global : ty-global) (gt : ty-globaltype) (start : ty-start) ->
    (_===_ C) ? {- StrE: {FUNC ft*{ft}, GLOBAL gt*{gt}, LOCAL [], LABEL [], RETURNS ?()} -} ->
    ? {- IterPr: ITER -} ->
    ? {- IterPr: ITER -} ->
    ? {- IterPr: ITER -} ->
    (_<=_ ? {- LenE: |start*{start}| -}) 1 ->
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
$default- (I32 _) = CONST ⟨ I32 record { } , 0 ⟩

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
    (ty-blocktype × (List ty-instr)) ->
    -------------
    ty-admininstr
  LOOP :
    (ty-blocktype × (List ty-instr)) ->
    -------------
    ty-admininstr
  IF :
    ((ty-blocktype × (List ty-instr)) × (List ty-instr)) ->
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
    ((ty-n × (List ty-instr)) × (List ty-admininstr)) ->
    -------------
    ty-admininstr
  FRAME- :
    ((ty-n × ty-frame) × (List ty-admininstr)) ->
    -------------
    ty-admininstr
  TRAP :
    ⊤ ->
    -------------
    ty-admininstr

ty-config : Set
ty-config  = (ty-state × (List ty-admininstr))

$funcaddr : ty-state → (List ty-funcaddr)
$funcaddr ⟨ s , f ⟩ = ty-moduleinst.FUNC (ty-frame.MODULE f)

$funcinst : ty-state → (List ty-funcinst)
$funcinst ⟨ s , f ⟩ = ty-store.FUNC s

$func : ((ty-state × ty-funcidx)) → ty-funcinst
$func ⟨ ⟨ s , f ⟩ , x ⟩ = ? {- IdxE: s.FUNC_store[f.MODULE_frame.FUNC_moduleinst[x]] -}

$global : ((ty-state × ty-globalidx)) → ty-globalinst
$global ⟨ ⟨ s , f ⟩ , x ⟩ = ? {- IdxE: s.GLOBAL_store[f.MODULE_frame.GLOBAL_moduleinst[x]] -}

$local : ((ty-state × ty-localidx)) → ty-val
$local ⟨ ⟨ s , f ⟩ , x ⟩ = ? {- IdxE: f.LOCAL_frame[x] -}

$with-local : (((ty-state × ty-localidx) × ty-val)) → ty-state
$with-local ⟨ ⟨ ⟨ s , f ⟩ , x ⟩ , v ⟩ = ⟨ s , ? {- UpdE: f[LOCAL_frame[x] = v] -} ⟩

$with-global : (((ty-state × ty-globalidx) × ty-val)) → ty-state
$with-global ⟨ ⟨ ⟨ s , f ⟩ , x ⟩ , v ⟩ = ⟨ ? {- UpdE: s[GLOBAL_store[f.MODULE_frame.GLOBAL_moduleinst[x]] = v] -} , f ⟩

data ty-E : Set
data ty-E where
  -HOLE :
    ⊤ ->
    ----
    ty-E
  -SEQ :
    (((List ty-val) × ty-E) × (List ty-instr)) ->
    ----
    ty-E
  LABEL- :
    ((ty-n × (List ty-instr)) × ty-E) ->
    ----
    ty-E

$unop : (((ty-unop-numtype × ty-numtype) × ty-c-numtype)) → (List ty-c-numtype)
$unop  = ? {- TODO -}

$binop : ((((ty-binop-numtype × ty-numtype) × ty-c-numtype) × ty-c-numtype)) → (List ty-c-numtype)
$binop  = ? {- TODO -}

$testop : (((ty-testop-numtype × ty-numtype) × ty-c-numtype)) → ty-c-numtype
$testop  = ? {- TODO -}

$relop : ((((ty-relop-numtype × ty-numtype) × ty-c-numtype) × ty-c-numtype)) → ty-c-numtype
$relop  = ? {- TODO -}

data ty-Step-pure : (((List ty-admininstr) × (List ty-admininstr))) → Set
data ty-Step-pure where
  unreachable :
    -------------------------------------------------------------------------------
    ty-Step-pure ⟨ (UNREACHABLE record { }) ∷ [] , (TRAP record { }) ∷ [] ⟩
  nop :
    -------------------------------------------------
    ty-Step-pure ⟨ (NOP record { }) ∷ [] , [] ⟩
  drop :
    (val : ty-val) ->
    ------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- SubE: (val <: admininstr) -} ∷ ((DROP record { }) ∷ []) , [] ⟩
  select-true :
    (c : ty-c-numtype) (t : ty-valtype) (val-1 : ty-val) (val-2 : ty-val) ->
    (_=/=_ c) 0 ->
    -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- SubE: (val_1 <: admininstr) -} ∷ (? {- SubE: (val_2 <: admininstr) -} ∷ ((CONST ⟨ I32 record { } , c ⟩) ∷ ((SELECT ? {- IterE: t?{t} -}) ∷ []))) , ? {- SubE: (val_1 <: admininstr) -} ∷ [] ⟩
  select-false :
    (c : ty-c-numtype) (t : ty-valtype) (val-1 : ty-val) (val-2 : ty-val) ->
    (_===_ c) 0 ->
    -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- SubE: (val_1 <: admininstr) -} ∷ (? {- SubE: (val_2 <: admininstr) -} ∷ ((CONST ⟨ I32 record { } , c ⟩) ∷ ((SELECT ? {- IterE: t?{t} -}) ∷ []))) , ? {- SubE: (val_2 <: admininstr) -} ∷ [] ⟩
  block :
    (bt : ty-blocktype) (instr : ty-instr) (k : Nat) (n : ty-n) (t-1 : ty-valtype) (t-2 : ty-valtype) (val : ty-val) ->
    (_===_ bt) ⟨ ? {- IterE: t_1^k{t_1} -} , ? {- IterE: t_2^n{t_2} -} ⟩ ->
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- CatE: (val <: admininstr)^k{val} :: [BLOCK_admininstr(bt, instr*{instr})] -} , (LABEL- ⟨ ⟨ n , [] ⟩ , ? {- CatE: (val <: admininstr)^k{val} :: (instr <: admininstr)*{instr} -} ⟩) ∷ [] ⟩
  loop :
    (bt : ty-blocktype) (instr : ty-instr) (k : Nat) (n : ty-n) (t-1 : ty-valtype) (t-2 : ty-valtype) (val : ty-val) ->
    (_===_ bt) ⟨ ? {- IterE: t_1^k{t_1} -} , ? {- IterE: t_2^n{t_2} -} ⟩ ->
    -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- CatE: (val <: admininstr)^k{val} :: [LOOP_admininstr(bt, instr*{instr})] -} , (LABEL- ⟨ ⟨ n , (LOOP ⟨ bt , ? {- IterE: instr*{instr} -} ⟩) ∷ [] ⟩ , ? {- CatE: (val <: admininstr)^k{val} :: (instr <: admininstr)*{instr} -} ⟩) ∷ [] ⟩
  if-true :
    (bt : ty-blocktype) (c : ty-c-numtype) (instr-1 : ty-instr) (instr-2 : ty-instr) ->
    (_=/=_ c) 0 ->
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ I32 record { } , c ⟩) ∷ ((IF ⟨ ⟨ bt , ? {- IterE: instr_1*{instr_1} -} ⟩ , ? {- IterE: instr_2*{instr_2} -} ⟩) ∷ []) , (BLOCK ⟨ bt , ? {- IterE: instr_1*{instr_1} -} ⟩) ∷ [] ⟩
  if-false :
    (bt : ty-blocktype) (c : ty-c-numtype) (instr-1 : ty-instr) (instr-2 : ty-instr) ->
    (_===_ c) 0 ->
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ I32 record { } , c ⟩) ∷ ((IF ⟨ ⟨ bt , ? {- IterE: instr_1*{instr_1} -} ⟩ , ? {- IterE: instr_2*{instr_2} -} ⟩) ∷ []) , (BLOCK ⟨ bt , ? {- IterE: instr_2*{instr_2} -} ⟩) ∷ [] ⟩
  label-vals :
    (instr : ty-instr) (n : ty-n) (val : ty-val) ->
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (LABEL- ⟨ ⟨ n , ? {- IterE: instr*{instr} -} ⟩ , ? {- IterE: (val <: admininstr)*{val} -} ⟩) ∷ [] , ? {- IterE: (val <: admininstr)*{val} -} ⟩
  br-zero :
    (instr : ty-instr) (instr' : ty-instr) (n : ty-n) (val : ty-val) (val' : ty-val) ->
    ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (LABEL- ⟨ ⟨ n , ? {- IterE: instr'*{instr'} -} ⟩ , ? {- CatE: (val' <: admininstr)*{val'} :: (val <: admininstr)^n{val} :: [BR_admininstr(0)] :: (instr <: admininstr)*{instr} -} ⟩) ∷ [] , ? {- CatE: (val <: admininstr)^n{val} :: (instr' <: admininstr)*{instr'} -} ⟩
  br-succ :
    (instr : ty-instr) (instr' : ty-instr) (l : ty-labelidx) (n : ty-n) (val : ty-val) ->
    ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (LABEL- ⟨ ⟨ n , ? {- IterE: instr'*{instr'} -} ⟩ , ? {- CatE: (val <: admininstr)*{val} :: [BR_admininstr(l + 1)] :: (instr <: admininstr)*{instr} -} ⟩) ∷ [] , ? {- CatE: (val <: admininstr)*{val} :: [BR_admininstr(l)] -} ⟩
  br-if-true :
    (c : ty-c-numtype) (l : ty-labelidx) ->
    (_=/=_ c) 0 ->
    ----------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ I32 record { } , c ⟩) ∷ ((BR-IF l) ∷ []) , (BR l) ∷ [] ⟩
  br-if-false :
    (c : ty-c-numtype) (l : ty-labelidx) ->
    (_===_ c) 0 ->
    -----------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ I32 record { } , c ⟩) ∷ ((BR-IF l) ∷ []) , [] ⟩
  frame-vals :
    (f : ty-frame) (n : ty-n) (val : ty-val) ->
    --------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (FRAME- ⟨ ⟨ n , f ⟩ , ? {- IterE: (val <: admininstr)^n{val} -} ⟩) ∷ [] , ? {- IterE: (val <: admininstr)^n{val} -} ⟩
  return-frame :
    (f : ty-frame) (instr : ty-instr) (n : ty-n) (val : ty-val) (val' : ty-val) ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (FRAME- ⟨ ⟨ n , f ⟩ , ? {- CatE: (val' <: admininstr)*{val'} :: (val <: admininstr)^n{val} :: [RETURN_admininstr] :: (instr <: admininstr)*{instr} -} ⟩) ∷ [] , ? {- IterE: (val <: admininstr)^n{val} -} ⟩
  return-label :
    (instr : ty-instr) (instr' : ty-instr) (k : Nat) (val : ty-val) ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (LABEL- ⟨ ⟨ k , ? {- IterE: instr'*{instr'} -} ⟩ , ? {- CatE: (val <: admininstr)*{val} :: [RETURN_admininstr] :: (instr <: admininstr)*{instr} -} ⟩) ∷ [] , ? {- CatE: (val <: admininstr)*{val} :: [RETURN_admininstr] -} ⟩
  unop-val :
    (c : ty-c-numtype) (c-1 : ty-c-numtype) (nt : ty-numtype) (unop : ty-unop-numtype) ->
    (_===_ ($unop ⟨ ⟨ unop , nt ⟩ , c-1 ⟩)) (c ∷ []) ->
    -------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ nt , c-1 ⟩) ∷ ((UNOP ⟨ nt , unop ⟩) ∷ []) , (CONST ⟨ nt , c ⟩) ∷ [] ⟩
  unop-trap :
    (c-1 : ty-c-numtype) (nt : ty-numtype) (unop : ty-unop-numtype) ->
    (_===_ ($unop ⟨ ⟨ unop , nt ⟩ , c-1 ⟩)) [] ->
    --------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ nt , c-1 ⟩) ∷ ((UNOP ⟨ nt , unop ⟩) ∷ []) , (TRAP record { }) ∷ [] ⟩
  binop-val :
    (binop : ty-binop-numtype) (c : ty-c-numtype) (c-1 : ty-c-numtype) (c-2 : ty-c-numtype) (nt : ty-numtype) ->
    (_===_ ($binop ⟨ ⟨ ⟨ binop , nt ⟩ , c-1 ⟩ , c-2 ⟩)) (c ∷ []) ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ nt , c-1 ⟩) ∷ ((CONST ⟨ nt , c-2 ⟩) ∷ ((BINOP ⟨ nt , binop ⟩) ∷ [])) , (CONST ⟨ nt , c ⟩) ∷ [] ⟩
  binop-trap :
    (binop : ty-binop-numtype) (c-1 : ty-c-numtype) (c-2 : ty-c-numtype) (nt : ty-numtype) ->
    (_===_ ($binop ⟨ ⟨ ⟨ binop , nt ⟩ , c-1 ⟩ , c-2 ⟩)) [] ->
    -----------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ nt , c-1 ⟩) ∷ ((CONST ⟨ nt , c-2 ⟩) ∷ ((BINOP ⟨ nt , binop ⟩) ∷ [])) , (TRAP record { }) ∷ [] ⟩
  testop :
    (c : ty-c-numtype) (c-1 : ty-c-numtype) (nt : ty-numtype) (testop : ty-testop-numtype) ->
    (_===_ c) ($testop ⟨ ⟨ testop , nt ⟩ , c-1 ⟩) ->
    -----------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ nt , c-1 ⟩) ∷ ((TESTOP ⟨ nt , testop ⟩) ∷ []) , (CONST ⟨ I32 record { } , c ⟩) ∷ [] ⟩
  relop :
    (c : ty-c-numtype) (c-1 : ty-c-numtype) (c-2 : ty-c-numtype) (nt : ty-numtype) (relop : ty-relop-numtype) ->
    (_===_ c) ($relop ⟨ ⟨ ⟨ relop , nt ⟩ , c-1 ⟩ , c-2 ⟩) ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ nt , c-1 ⟩) ∷ ((CONST ⟨ nt , c-2 ⟩) ∷ ((RELOP ⟨ nt , relop ⟩) ∷ [])) , (CONST ⟨ I32 record { } , c ⟩) ∷ [] ⟩
  local-tee :
    (val : ty-val) (x : ty-idx) ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ? {- SubE: (val <: admininstr) -} ∷ ((LOCAL-TEE x) ∷ []) , ? {- SubE: (val <: admininstr) -} ∷ (? {- SubE: (val <: admininstr) -} ∷ ((LOCAL-SET x) ∷ [])) ⟩

data ty-Step-read : ((ty-config × (List ty-admininstr))) → Set
data ty-Step-read where
  call :
    (x : ty-idx) (z : ty-state) ->
    ---------------------------------------------------------------------------------------------------
    ty-Step-read ⟨ ⟨ z , (CALL x) ∷ [] ⟩ , (CALL-ADDR ? {- IdxE: $funcaddr(z)[x] -}) ∷ [] ⟩
  call-addr :
    (a : ty-addr) (f : ty-frame) (instr : ty-instr) (k : Nat) (m : ty-moduleinst) (n : ty-n) (t : ty-valtype) (t-1 : ty-valtype) (t-2 : ty-valtype) (val : ty-val) (z : ty-state) ->
    (_===_ ? {- IdxE: $funcinst(z)[a] -}) ⟨ m , ⟨ ⟨ ⟨ ? {- IterE: t_1^k{t_1} -} , ? {- IterE: t_2^n{t_2} -} ⟩ , ? {- IterE: t*{t} -} ⟩ , ? {- IterE: instr*{instr} -} ⟩ ⟩ ->
    (_===_ f) ? {- StrE: {LOCAL val^k{val} :: $default_(t)*{t}, MODULE m} -} ->
    --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-read ⟨ ⟨ z , ? {- CatE: (val <: admininstr)^k{val} :: [CALL_ADDR_admininstr(a)] -} ⟩ , (FRAME- ⟨ ⟨ n , f ⟩ , (LABEL- ⟨ ⟨ n , [] ⟩ , ? {- IterE: (instr <: admininstr)*{instr} -} ⟩) ∷ [] ⟩) ∷ [] ⟩
  local-get :
    (x : ty-idx) (z : ty-state) ->
    ---------------------------------------------------------------------------------------------------------
    ty-Step-read ⟨ ⟨ z , (LOCAL-GET x) ∷ [] ⟩ , ? {- SubE: ($local(z, x) <: admininstr) -} ∷ [] ⟩
  global-get :
    (x : ty-idx) (z : ty-state) ->
    -----------------------------------------------------------------------------------------------------------
    ty-Step-read ⟨ ⟨ z , (GLOBAL-GET x) ∷ [] ⟩ , ? {- SubE: ($global(z, x) <: admininstr) -} ∷ [] ⟩

data ty-Step : ((ty-config × ty-config)) → Set
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
    -----------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step ⟨ ⟨ z , ? {- SubE: (val <: admininstr) -} ∷ ((LOCAL-SET x) ∷ []) ⟩ , ⟨ $with-local ⟨ ⟨ z , x ⟩ , val ⟩ , [] ⟩ ⟩
  global-set :
    (val : ty-val) (x : ty-idx) (z : ty-state) ->
    -------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step ⟨ ⟨ z , ? {- SubE: (val <: admininstr) -} ∷ ((GLOBAL-SET x) ∷ []) ⟩ , ⟨ $with-global ⟨ ⟨ z , x ⟩ , val ⟩ , [] ⟩ ⟩
$ agda output.agda | sed -e "s/\/.*\/_build\///g"
Checking output (default/test-agda/output.agda).
default/test-agda/output.agda:328,1-331,48
Termination checking failed for the following functions:
  $min
Problematic calls:
  $min ⟨ i - 1 , j - 1 ⟩
    (at default/test-agda/output.agda:331,18-22)
default/test-agda/output.agda:334,1-14
Incomplete pattern matching for $size. Missing cases:
  $size (BOT x)
when checking the definition of $size
default/test-agda/output.agda:660,1-18
Incomplete pattern matching for $default-. Missing cases:
  $default- (BOT x)
when checking the definition of $default-
Unsolved constraints
Unsolved metas at the following locations:
  default/test-agda/output.agda:457,6-11
  default/test-agda/output.agda:462,6-11
  default/test-agda/output.agda:472,45-100
  default/test-agda/output.agda:512,47-75
  default/test-agda/output.agda:517,49-53
  default/test-agda/output.agda:517,54-64
  default/test-agda/output.agda:558,49-56
  default/test-agda/output.agda:603,47-49
  default/test-agda/output.agda:603,52-54
  default/test-agda/output.agda:962,49-168
  default/test-agda/output.agda:962,51-135
  default/test-agda/output.agda:962,53-110
Unsolved interaction metas at the following locations:
  default/test-agda/output.agda:418,54-55
  default/test-agda/output.agda:418,81-82
  default/test-agda/output.agda:433,15-16
  default/test-agda/output.agda:438,38-39
  default/test-agda/output.agda:438,65-66
  default/test-agda/output.agda:439,24-25
  default/test-agda/output.agda:439,109-110
  default/test-agda/output.agda:439,144-145
  default/test-agda/output.agda:439,171-172
  default/test-agda/output.agda:441,38-39
  default/test-agda/output.agda:441,75-76
  default/test-agda/output.agda:441,102-103
  default/test-agda/output.agda:444,38-39
  default/test-agda/output.agda:444,65-66
  default/test-agda/output.agda:445,24-25
  default/test-agda/output.agda:445,109-110
  default/test-agda/output.agda:445,144-145
  default/test-agda/output.agda:445,171-172
  default/test-agda/output.agda:447,37-38
  default/test-agda/output.agda:447,74-75
  default/test-agda/output.agda:447,101-102
  default/test-agda/output.agda:450,38-39
  default/test-agda/output.agda:450,65-66
  default/test-agda/output.agda:451,24-25
  default/test-agda/output.agda:451,109-110
  default/test-agda/output.agda:451,148-149
  default/test-agda/output.agda:451,175-176
  default/test-agda/output.agda:452,24-25
  default/test-agda/output.agda:452,109-110
  default/test-agda/output.agda:452,148-149
  default/test-agda/output.agda:452,175-176
  default/test-agda/output.agda:454,37-38
  default/test-agda/output.agda:454,74-75
  default/test-agda/output.agda:454,115-116
  default/test-agda/output.agda:454,142-143
  default/test-agda/output.agda:457,12-13
  default/test-agda/output.agda:457,46-47
  default/test-agda/output.agda:459,36-37
  default/test-agda/output.agda:459,71-72
  default/test-agda/output.agda:462,12-13
  default/test-agda/output.agda:462,46-47
  default/test-agda/output.agda:464,39-40
  default/test-agda/output.agda:464,78-79
  default/test-agda/output.agda:467,42-43
  default/test-agda/output.agda:469,49-50
  default/test-agda/output.agda:469,84-85
  default/test-agda/output.agda:472,12-13
  default/test-agda/output.agda:472,47-48
  default/test-agda/output.agda:472,74-75
  default/test-agda/output.agda:474,38-39
  default/test-agda/output.agda:474,65-66
  default/test-agda/output.agda:478,56-57
  default/test-agda/output.agda:482,50-51
  default/test-agda/output.agda:482,87-88
  default/test-agda/output.agda:486,52-53
  default/test-agda/output.agda:486,85-86
  default/test-agda/output.agda:486,123-124
  default/test-agda/output.agda:490,54-55
  default/test-agda/output.agda:494,52-53
  default/test-agda/output.agda:494,85-86
  default/test-agda/output.agda:497,12-13
  default/test-agda/output.agda:502,12-13
  default/test-agda/output.agda:507,12-13
  default/test-agda/output.agda:512,12-13
  default/test-agda/output.agda:512,49-50
  default/test-agda/output.agda:517,12-13
  default/test-agda/output.agda:527,39-40
  default/test-agda/output.agda:527,66-67
  default/test-agda/output.agda:528,47-48
  default/test-agda/output.agda:528,74-75
  default/test-agda/output.agda:530,28-29
  default/test-agda/output.agda:530,72-73
  default/test-agda/output.agda:530,99-100
  default/test-agda/output.agda:533,28-29
  default/test-agda/output.agda:533,63-64
  default/test-agda/output.agda:533,87-88
  default/test-agda/output.agda:535,28-29
  default/test-agda/output.agda:535,74-75
  default/test-agda/output.agda:538,28-29
  default/test-agda/output.agda:538,63-64
  default/test-agda/output.agda:538,90-91
  default/test-agda/output.agda:540,28-29
  default/test-agda/output.agda:540,63-64
  default/test-agda/output.agda:540,98-99
  default/test-agda/output.agda:546,28-29
  default/test-agda/output.agda:546,68-69
  default/test-agda/output.agda:548,24-25
  default/test-agda/output.agda:548,57-58
  default/test-agda/output.agda:558,12-13
  default/test-agda/output.agda:566,5-6
  default/test-agda/output.agda:568,25-26
  default/test-agda/output.agda:583,18-19
  default/test-agda/output.agda:583,45-46
  default/test-agda/output.agda:585,20-21
  default/test-agda/output.agda:585,253-254
  default/test-agda/output.agda:587,33-34
  default/test-agda/output.agda:594,18-19
  default/test-agda/output.agda:603,12-13
  default/test-agda/output.agda:611,15-16
  default/test-agda/output.agda:612,5-6
  default/test-agda/output.agda:613,5-6
  default/test-agda/output.agda:614,5-6
  default/test-agda/output.agda:615,11-12
  default/test-agda/output.agda:617,22-23
  default/test-agda/output.agda:617,51-52
  default/test-agda/output.agda:617,86-87
  default/test-agda/output.agda:802,27-28
  default/test-agda/output.agda:805,29-30
  default/test-agda/output.agda:808,28-29
  default/test-agda/output.agda:811,47-48
  default/test-agda/output.agda:814,44-45
  default/test-agda/output.agda:832,10-11
  default/test-agda/output.agda:835,11-12
  default/test-agda/output.agda:838,12-13
  default/test-agda/output.agda:841,11-12
  default/test-agda/output.agda:854,20-21
  default/test-agda/output.agda:859,20-21
  default/test-agda/output.agda:859,59-60
  default/test-agda/output.agda:859,140-141
  default/test-agda/output.agda:859,172-173
  default/test-agda/output.agda:864,20-21
  default/test-agda/output.agda:864,59-60
  default/test-agda/output.agda:864,140-141
  default/test-agda/output.agda:864,172-173
  default/test-agda/output.agda:867,18-19
  default/test-agda/output.agda:867,46-47
  default/test-agda/output.agda:869,20-21
  default/test-agda/output.agda:869,127-128
  default/test-agda/output.agda:872,18-19
  default/test-agda/output.agda:872,46-47
  default/test-agda/output.agda:874,20-21
  default/test-agda/output.agda:874,132-133
  default/test-agda/output.agda:874,173-174
  default/test-agda/output.agda:879,67-68
  default/test-agda/output.agda:879,104-105
  default/test-agda/output.agda:879,162-163
  default/test-agda/output.agda:884,67-68
  default/test-agda/output.agda:884,104-105
  default/test-agda/output.agda:884,162-163
  default/test-agda/output.agda:888,36-37
  default/test-agda/output.agda:888,69-70
  default/test-agda/output.agda:888,120-121
  default/test-agda/output.agda:892,36-37
  default/test-agda/output.agda:892,71-72
  default/test-agda/output.agda:892,208-209
  default/test-agda/output.agda:896,36-37
  default/test-agda/output.agda:896,71-72
  default/test-agda/output.agda:896,180-181
  default/test-agda/output.agda:910,42-43
  default/test-agda/output.agda:910,94-95
  default/test-agda/output.agda:914,42-43
  default/test-agda/output.agda:914,180-181
  default/test-agda/output.agda:918,36-37
  default/test-agda/output.agda:918,71-72
  default/test-agda/output.agda:918,177-178
  default/test-agda/output.agda:952,20-21
  default/test-agda/output.agda:952,79-80
  default/test-agda/output.agda:952,116-117
  default/test-agda/output.agda:959,55-56
  default/test-agda/output.agda:962,12-13
  default/test-agda/output.agda:962,55-56
  default/test-agda/output.agda:962,83-84
  default/test-agda/output.agda:962,113-114
  default/test-agda/output.agda:962,138-139
  default/test-agda/output.agda:963,15-16
  default/test-agda/output.agda:965,26-27
  default/test-agda/output.agda:965,145-146
  default/test-agda/output.agda:969,49-50
  default/test-agda/output.agda:973,50-51
  default/test-agda/output.agda:979,20-21
  default/test-agda/output.agda:979,67-68
  default/test-agda/output.agda:981,21-22
  default/test-agda/output.agda:981,76-77
  default/test-agda/output.agda:984,26-27
  default/test-agda/output.agda:984,75-76
  default/test-agda/output.agda:986,21-22
  default/test-agda/output.agda:986,76-77
  default/test-agda/output.agda:990,21-22
  default/test-agda/output.agda:994,21-22
```

The `sed` incantation is needed to remove (user-specific) absolute paths in Agda output.
