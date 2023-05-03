# Preview

```sh
$ patch -s -p0 -i ../spec/minispec.patch -d ../spec --read-only=ignore
$ dune exec ../src/exe-watsup/main.exe -- --agda --sub ../spec/*.watsup -o output.agda
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
_++_ : {A : Set} -> List A -> List A -> List A
_ ++ _ = ?
maybeMap : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
maybeMap _ _ = ?
map : {A B : Set} -> (A -> B) -> List A -> List B
map _ _ = ?
length : {A : Set} -> List A -> Nat
length _ = ?

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

$valtype-numtype : ty-numtype → ty-valtype
$valtype-numtype (I32 _) = I32 (record { })

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
    (C : ty-context) (t-1 : List ty-valtype) (t-2 : List ty-valtype) ->
    ----------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , UNREACHABLE (record { }) ⟩ , ⟨ t-1 , t-2 ⟩ ⟩
  nop :
    (C : ty-context) ->
    ------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , NOP (record { }) ⟩ , ⟨ [] , [] ⟩ ⟩
  drop :
    (C : ty-context) (t : ty-valtype) ->
    -------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , DROP (record { }) ⟩ , ⟨ t ∷ [] , [] ⟩ ⟩
  select-expl :
    (C : ty-context) (t : ty-valtype) ->
    --------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , SELECT (just t) ⟩ , ⟨ t ∷ (t ∷ ((I32 (record { })) ∷ [])) , t ∷ [] ⟩ ⟩
  select-impl :
    (C : ty-context) (numtype : ty-numtype) (t : ty-valtype) ->
    (_===_ t) ($valtype-numtype numtype) ->
    -------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , SELECT nothing ⟩ , ⟨ t ∷ (t ∷ ((I32 (record { })) ∷ [])) , t ∷ [] ⟩ ⟩
  block :
    (C : ty-context) (bt : ty-blocktype) (instr : List ty-instr) (t-1 : List ty-valtype) (t-2 : List ty-valtype) ->
    ty-Blocktype-ok ⟨ ⟨ C , bt ⟩ , ⟨ t-1 , t-2 ⟩ ⟩ ->
    ty-InstrSeq-ok ⟨ ⟨ ? {- CompE: C ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2]*{t_2}, RETURNS ?()} -} , instr ⟩ , ⟨ t-1 , t-2 ⟩ ⟩ ->
    ----------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , BLOCK ⟨ bt , instr ⟩ ⟩ , ⟨ t-1 , t-2 ⟩ ⟩
  loop :
    (C : ty-context) (bt : ty-blocktype) (instr : List ty-instr) (t-1 : List ty-valtype) (t-2 : List ty-valtype) ->
    ty-Blocktype-ok ⟨ ⟨ C , bt ⟩ , ⟨ t-1 , t-2 ⟩ ⟩ ->
    ty-InstrSeq-ok ⟨ ⟨ ? {- CompE: C ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_1]*{t_1}, RETURNS ?()} -} , instr ⟩ , ⟨ t-1 , t-2 ⟩ ⟩ ->
    ---------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , LOOP ⟨ bt , instr ⟩ ⟩ , ⟨ t-1 , t-2 ⟩ ⟩
  if :
    (C : ty-context) (bt : ty-blocktype) (instr-1 : List ty-instr) (instr-2 : List ty-instr) (t-1 : List ty-valtype) (t-2 : List ty-valtype) ->
    ty-Blocktype-ok ⟨ ⟨ C , bt ⟩ , ⟨ t-1 , t-2 ⟩ ⟩ ->
    ty-InstrSeq-ok ⟨ ⟨ ? {- CompE: C ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2]*{t_2}, RETURNS ?()} -} , instr-1 ⟩ , ⟨ t-1 , t-2 ⟩ ⟩ ->
    ty-InstrSeq-ok ⟨ ⟨ ? {- CompE: C ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2]*{t_2}, RETURNS ?()} -} , instr-2 ⟩ , ⟨ t-1 , t-2 ⟩ ⟩ ->
    ---------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , IF ⟨ ⟨ bt , instr-1 ⟩ , instr-2 ⟩ ⟩ , ⟨ t-1 , t-2 ⟩ ⟩
  br :
    (C : ty-context) (l : ty-labelidx) (t : List ty-valtype) (t-1 : List ty-valtype) (t-2 : List ty-valtype) ->
    (_===_ ? {- IdxE: C.LABEL_context[l] -}) t ->
    -----------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , BR l ⟩ , ⟨ (_++_ t-1) t , t-2 ⟩ ⟩
  br-if :
    (C : ty-context) (l : ty-labelidx) (t : List ty-valtype) ->
    (_===_ ? {- IdxE: C.LABEL_context[l] -}) t ->
    ------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , BR-IF l ⟩ , ⟨ (_++_ t) ((I32 (record { })) ∷ []) , t ⟩ ⟩
  return :
    (C : ty-context) (t : List ty-valtype) (t-1 : List ty-valtype) (t-2 : List ty-valtype) ->
    (_===_ (ty-context.RETURNS C)) (just t) ->
    --------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , RETURN (record { }) ⟩ , ⟨ (_++_ t-1) t , t-2 ⟩ ⟩
  call :
    (C : ty-context) (t-1 : List ty-valtype) (t-2 : List ty-valtype) (x : ty-idx) ->
    (_===_ ? {- IdxE: C.FUNC_context[x] -}) ⟨ t-1 , t-2 ⟩ ->
    ----------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , CALL x ⟩ , ⟨ t-1 , t-2 ⟩ ⟩
  const :
    (C : ty-context) (c-nt : ty-c-numtype) (nt : ty-numtype) ->
    ---------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , CONST ⟨ nt , c-nt ⟩ ⟩ , ⟨ [] , ($valtype-numtype nt) ∷ [] ⟩ ⟩
  unop :
    (C : ty-context) (nt : ty-numtype) (unop : ty-unop-numtype) ->
    ----------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , UNOP ⟨ nt , unop ⟩ ⟩ , ⟨ ($valtype-numtype nt) ∷ [] , ($valtype-numtype nt) ∷ [] ⟩ ⟩
  binop :
    (C : ty-context) (binop : ty-binop-numtype) (nt : ty-numtype) ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , BINOP ⟨ nt , binop ⟩ ⟩ , ⟨ ($valtype-numtype nt) ∷ (($valtype-numtype nt) ∷ []) , ($valtype-numtype nt) ∷ [] ⟩ ⟩
  testop :
    (C : ty-context) (nt : ty-numtype) (testop : ty-testop-numtype) ->
    -----------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , TESTOP ⟨ nt , testop ⟩ ⟩ , ⟨ ($valtype-numtype nt) ∷ [] , (I32 (record { })) ∷ [] ⟩ ⟩
  relop :
    (C : ty-context) (nt : ty-numtype) (relop : ty-relop-numtype) ->
    -------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , RELOP ⟨ nt , relop ⟩ ⟩ , ⟨ ($valtype-numtype nt) ∷ (($valtype-numtype nt) ∷ []) , (I32 (record { })) ∷ [] ⟩ ⟩
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
    (_===_ ? {- IdxE: C.GLOBAL_context[x] -}) ⟨ just (record { }) , t ⟩ ->
    --------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , GLOBAL-GET x ⟩ , ⟨ [] , t ∷ [] ⟩ ⟩
  global-set :
    (C : ty-context) (t : ty-valtype) (x : ty-idx) ->
    (_===_ ? {- IdxE: C.GLOBAL_context[x] -}) ⟨ just (record { }) , t ⟩ ->
    --------------------------------------------------------------------
    ty-Instr-ok ⟨ ⟨ C , GLOBAL-SET x ⟩ , ⟨ t ∷ [] , [] ⟩ ⟩
data ty-InstrSeq-ok where
  empty :
    (C : ty-context) ->
    -------------------------------------------------------
    ty-InstrSeq-ok ⟨ ⟨ C , [] ⟩ , ⟨ [] , [] ⟩ ⟩
  seq :
    (C : ty-context) (instr-1 : ty-instr) (instr-2 : ty-instr) (t-1 : List ty-valtype) (t-2 : List ty-valtype) (t-3 : List ty-valtype) ->
    ty-Instr-ok ⟨ ⟨ C , instr-1 ⟩ , ⟨ t-1 , t-2 ⟩ ⟩ ->
    ty-InstrSeq-ok ⟨ ⟨ C , instr-2 ∷ [] ⟩ , ⟨ t-2 , t-3 ⟩ ⟩ ->
    -----------------------------------------------------------------------------------------------
    ty-InstrSeq-ok ⟨ ⟨ C , (_++_ (instr-1 ∷ [])) (instr-2 ∷ []) ⟩ , ⟨ t-1 , t-3 ⟩ ⟩
  weak :
    (C : ty-context) (instr : List ty-instr) (t-1 : ty-valtype) (t-2 : List ty-valtype) ->
    ty-InstrSeq-ok ⟨ ⟨ C , instr ⟩ , ⟨ t-1 ∷ [] , t-2 ⟩ ⟩ ->
    -------------------------------------------------------------------
    ty-InstrSeq-ok ⟨ ⟨ C , instr ⟩ , ⟨ t-1 ∷ [] , t-2 ⟩ ⟩
  frame :
    (C : ty-context) (instr : List ty-instr) (t : List ty-valtype) (t-1 : List ty-valtype) (t-2 : List ty-valtype) ->
    ty-InstrSeq-ok ⟨ ⟨ C , instr ⟩ , ⟨ t-1 , t-2 ⟩ ⟩ ->
    ------------------------------------------------------------------------------
    ty-InstrSeq-ok ⟨ ⟨ C , instr ⟩ , ⟨ (_++_ t) t-1 , (_++_ t) t-2 ⟩ ⟩

data ty-Expr-ok : (((ty-context × ty-expr) × ty-resulttype)) → Set
data ty-Expr-ok where
  - :
    (C : ty-context) (instr : List ty-instr) (t : List ty-valtype) ->
    ty-InstrSeq-ok ⟨ ⟨ C , instr ⟩ , ⟨ [] , t ⟩ ⟩ ->
    ----------------------------------------
    ty-Expr-ok ⟨ ⟨ C , instr ⟩ , t ⟩

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
    (C : ty-context) (instr : List ty-instr) ->
    ? {- IterPr: ITER -} ->
    -------------------------------
    ty-Expr-const ⟨ C , instr ⟩

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
    (C : ty-context) (expr : ty-expr) (ft : ty-functype) (t : List ty-valtype) (t-1 : List ty-valtype) (t-2 : List ty-valtype) ->
    (_===_ ft) ⟨ t-1 , t-2 ⟩ ->
    ty-Functype-ok ft ->
    ty-Expr-ok ⟨ ⟨ ? {- CompE: C ++ {FUNC [], GLOBAL [], LOCAL t_1*{t_1} :: t*{t}, LABEL [], RETURNS ?()} ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2*{t_2}], RETURNS ?()} ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [], RETURNS ?(t_2*{t_2})} -} , expr ⟩ , t-2 ⟩ ->
    -----------------------------------------------------------------
    ty-Func-ok ⟨ ⟨ C , ⟨ ⟨ ft , t ⟩ , expr ⟩ ⟩ , ft ⟩

data ty-Global-ok : (((ty-context × ty-global) × ty-globaltype)) → Set
data ty-Global-ok where
  - :
    (C : ty-context) (expr : ty-expr) (gt : ty-globaltype) (t : ty-valtype) ->
    ty-Globaltype-ok gt ->
    (_===_ gt) ⟨ just (record { }) , t ⟩ ->
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
    (C : ty-context) (ft : List ty-functype) (func : List ty-func) (global : List ty-global) (gt : List ty-globaltype) (start : List ty-start) ->
    (_===_ C) (record { FUNC = ft ; GLOBAL = gt ; LOCAL = [] ; LABEL = [] ; RETURNS = nothing }) ->
    ? {- IterPr: ITER -} ->
    ? {- IterPr: ITER -} ->
    ? {- IterPr: ITER -} ->
    (_<=_ (length start)) 1 ->
    --------------------------------------------------
    ty-Module-ok ⟨ ⟨ func , global ⟩ , start ⟩

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
$default- (I32 _) = CONST ⟨ I32 (record { }) , 0 ⟩

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

$admininstr-globalinst : ty-globalinst → ty-admininstr
$admininstr-globalinst (CONST x) = CONST x

$admininstr-instr : ty-instr → ty-admininstr
$admininstr-instr (UNREACHABLE _) = UNREACHABLE (record { })
$admininstr-instr (NOP _) = NOP (record { })
$admininstr-instr (DROP _) = DROP (record { })
$admininstr-instr (SELECT x) = SELECT x
$admininstr-instr (BLOCK x) = BLOCK x
$admininstr-instr (LOOP x) = LOOP x
$admininstr-instr (IF x) = IF x
$admininstr-instr (BR x) = BR x
$admininstr-instr (BR-IF x) = BR-IF x
$admininstr-instr (CALL x) = CALL x
$admininstr-instr (RETURN _) = RETURN (record { })
$admininstr-instr (CONST x) = CONST x
$admininstr-instr (UNOP x) = UNOP x
$admininstr-instr (BINOP x) = BINOP x
$admininstr-instr (TESTOP x) = TESTOP x
$admininstr-instr (RELOP x) = RELOP x
$admininstr-instr (LOCAL-GET x) = LOCAL-GET x
$admininstr-instr (LOCAL-SET x) = LOCAL-SET x
$admininstr-instr (LOCAL-TEE x) = LOCAL-TEE x
$admininstr-instr (GLOBAL-GET x) = GLOBAL-GET x
$admininstr-instr (GLOBAL-SET x) = GLOBAL-SET x

$admininstr-val : ty-val → ty-admininstr
$admininstr-val (CONST x) = CONST x

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
    -----------------------------------------------------------------------------------
    ty-Step-pure ⟨ (UNREACHABLE (record { })) ∷ [] , (TRAP (record { })) ∷ [] ⟩
  nop :
    ---------------------------------------------------
    ty-Step-pure ⟨ (NOP (record { })) ∷ [] , [] ⟩
  drop :
    (val : ty-val) ->
    --------------------------------------------------------------------------------
    ty-Step-pure ⟨ ($admininstr-val val) ∷ ((DROP (record { })) ∷ []) , [] ⟩
  select-true :
    (c : ty-c-numtype) (t : Maybe ty-valtype) (val-1 : ty-val) (val-2 : ty-val) ->
    (_=/=_ c) 0 ->
    ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ($admininstr-val val-1) ∷ (($admininstr-val val-2) ∷ ((CONST ⟨ I32 (record { }) , c ⟩) ∷ ((SELECT t) ∷ []))) , ($admininstr-val val-1) ∷ [] ⟩
  select-false :
    (c : ty-c-numtype) (t : Maybe ty-valtype) (val-1 : ty-val) (val-2 : ty-val) ->
    (_===_ c) 0 ->
    ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ($admininstr-val val-1) ∷ (($admininstr-val val-2) ∷ ((CONST ⟨ I32 (record { }) , c ⟩) ∷ ((SELECT t) ∷ []))) , ($admininstr-val val-2) ∷ [] ⟩
  block :
    (bt : ty-blocktype) (instr : List ty-instr) (k : Nat) (n : ty-n) (t-1 : List ty-valtype) (t-2 : List ty-valtype) (val : List ty-val) ->
    (_===_ bt) ⟨ t-1 , t-2 ⟩ ->
    -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (_++_ ((map (λ val -> ($admininstr-val val))) val)) ((BLOCK ⟨ bt , instr ⟩) ∷ []) , (LABEL- ⟨ ⟨ n , [] ⟩ , (_++_ ((map (λ val -> ($admininstr-val val))) val)) ((map (λ instr -> ($admininstr-instr instr))) instr) ⟩) ∷ [] ⟩
  loop :
    (bt : ty-blocktype) (instr : List ty-instr) (k : Nat) (n : ty-n) (t-1 : List ty-valtype) (t-2 : List ty-valtype) (val : List ty-val) ->
    (_===_ bt) ⟨ t-1 , t-2 ⟩ ->
    ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (_++_ ((map (λ val -> ($admininstr-val val))) val)) ((LOOP ⟨ bt , instr ⟩) ∷ []) , (LABEL- ⟨ ⟨ n , (LOOP ⟨ bt , instr ⟩) ∷ [] ⟩ , (_++_ ((map (λ val -> ($admininstr-val val))) val)) ((map (λ instr -> ($admininstr-instr instr))) instr) ⟩) ∷ [] ⟩
  if-true :
    (bt : ty-blocktype) (c : ty-c-numtype) (instr-1 : List ty-instr) (instr-2 : List ty-instr) ->
    (_=/=_ c) 0 ->
    --------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ I32 (record { }) , c ⟩) ∷ ((IF ⟨ ⟨ bt , instr-1 ⟩ , instr-2 ⟩) ∷ []) , (BLOCK ⟨ bt , instr-1 ⟩) ∷ [] ⟩
  if-false :
    (bt : ty-blocktype) (c : ty-c-numtype) (instr-1 : List ty-instr) (instr-2 : List ty-instr) ->
    (_===_ c) 0 ->
    --------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ I32 (record { }) , c ⟩) ∷ ((IF ⟨ ⟨ bt , instr-1 ⟩ , instr-2 ⟩) ∷ []) , (BLOCK ⟨ bt , instr-2 ⟩) ∷ [] ⟩
  label-vals :
    (instr : List ty-instr) (n : ty-n) (val : List ty-val) ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (LABEL- ⟨ ⟨ n , instr ⟩ , (map (λ val -> ($admininstr-val val))) val ⟩) ∷ [] , (map (λ val -> ($admininstr-val val))) val ⟩
  br-zero :
    (instr : List ty-instr) (instr' : List ty-instr) (n : ty-n) (val : List ty-val) (val' : List ty-val) ->
    -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (LABEL- ⟨ ⟨ n , instr' ⟩ , (_++_ ((map (λ val' -> ($admininstr-val val'))) val')) ((_++_ ((map (λ val -> ($admininstr-val val))) val)) ((_++_ ((BR 0) ∷ [])) ((map (λ instr -> ($admininstr-instr instr))) instr))) ⟩) ∷ [] , (_++_ ((map (λ val -> ($admininstr-val val))) val)) ((map (λ instr' -> ($admininstr-instr instr'))) instr') ⟩
  br-succ :
    (instr : List ty-instr) (instr' : List ty-instr) (l : ty-labelidx) (n : ty-n) (val : List ty-val) ->
    --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (LABEL- ⟨ ⟨ n , instr' ⟩ , (_++_ ((map (λ val -> ($admininstr-val val))) val)) ((_++_ ((BR ((_+_ l) 1)) ∷ [])) ((map (λ instr -> ($admininstr-instr instr))) instr)) ⟩) ∷ [] , (_++_ ((map (λ val -> ($admininstr-val val))) val)) ((BR l) ∷ []) ⟩
  br-if-true :
    (c : ty-c-numtype) (l : ty-labelidx) ->
    (_=/=_ c) 0 ->
    ------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ I32 (record { }) , c ⟩) ∷ ((BR-IF l) ∷ []) , (BR l) ∷ [] ⟩
  br-if-false :
    (c : ty-c-numtype) (l : ty-labelidx) ->
    (_===_ c) 0 ->
    -------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ I32 (record { }) , c ⟩) ∷ ((BR-IF l) ∷ []) , [] ⟩
  frame-vals :
    (f : ty-frame) (n : ty-n) (val : List ty-val) ->
    ------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (FRAME- ⟨ ⟨ n , f ⟩ , (map (λ val -> ($admininstr-val val))) val ⟩) ∷ [] , (map (λ val -> ($admininstr-val val))) val ⟩
  return-frame :
    (f : ty-frame) (instr : List ty-instr) (n : ty-n) (val : List ty-val) (val' : List ty-val) ->
    -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (FRAME- ⟨ ⟨ n , f ⟩ , (_++_ ((map (λ val' -> ($admininstr-val val'))) val')) ((_++_ ((map (λ val -> ($admininstr-val val))) val)) ((_++_ ((RETURN (record { })) ∷ [])) ((map (λ instr -> ($admininstr-instr instr))) instr))) ⟩) ∷ [] , (map (λ val -> ($admininstr-val val))) val ⟩
  return-label :
    (instr : List ty-instr) (instr' : List ty-instr) (k : Nat) (val : List ty-val) ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (LABEL- ⟨ ⟨ k , instr' ⟩ , (_++_ ((map (λ val -> ($admininstr-val val))) val)) ((_++_ ((RETURN (record { })) ∷ [])) ((map (λ instr -> ($admininstr-instr instr))) instr)) ⟩) ∷ [] , (_++_ ((map (λ val -> ($admininstr-val val))) val)) ((RETURN (record { })) ∷ []) ⟩
  unop-val :
    (c : ty-c-numtype) (c-1 : ty-c-numtype) (nt : ty-numtype) (unop : ty-unop-numtype) ->
    (_===_ ($unop ⟨ ⟨ unop , nt ⟩ , c-1 ⟩)) (c ∷ []) ->
    -------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ nt , c-1 ⟩) ∷ ((UNOP ⟨ nt , unop ⟩) ∷ []) , (CONST ⟨ nt , c ⟩) ∷ [] ⟩
  unop-trap :
    (c-1 : ty-c-numtype) (nt : ty-numtype) (unop : ty-unop-numtype) ->
    (_===_ ($unop ⟨ ⟨ unop , nt ⟩ , c-1 ⟩)) [] ->
    ----------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ nt , c-1 ⟩) ∷ ((UNOP ⟨ nt , unop ⟩) ∷ []) , (TRAP (record { })) ∷ [] ⟩
  binop-val :
    (binop : ty-binop-numtype) (c : ty-c-numtype) (c-1 : ty-c-numtype) (c-2 : ty-c-numtype) (nt : ty-numtype) ->
    (_===_ ($binop ⟨ ⟨ ⟨ binop , nt ⟩ , c-1 ⟩ , c-2 ⟩)) (c ∷ []) ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ nt , c-1 ⟩) ∷ ((CONST ⟨ nt , c-2 ⟩) ∷ ((BINOP ⟨ nt , binop ⟩) ∷ [])) , (CONST ⟨ nt , c ⟩) ∷ [] ⟩
  binop-trap :
    (binop : ty-binop-numtype) (c-1 : ty-c-numtype) (c-2 : ty-c-numtype) (nt : ty-numtype) ->
    (_===_ ($binop ⟨ ⟨ ⟨ binop , nt ⟩ , c-1 ⟩ , c-2 ⟩)) [] ->
    -------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ nt , c-1 ⟩) ∷ ((CONST ⟨ nt , c-2 ⟩) ∷ ((BINOP ⟨ nt , binop ⟩) ∷ [])) , (TRAP (record { })) ∷ [] ⟩
  testop :
    (c : ty-c-numtype) (c-1 : ty-c-numtype) (nt : ty-numtype) (testop : ty-testop-numtype) ->
    (_===_ c) ($testop ⟨ ⟨ testop , nt ⟩ , c-1 ⟩) ->
    -------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ nt , c-1 ⟩) ∷ ((TESTOP ⟨ nt , testop ⟩) ∷ []) , (CONST ⟨ I32 (record { }) , c ⟩) ∷ [] ⟩
  relop :
    (c : ty-c-numtype) (c-1 : ty-c-numtype) (c-2 : ty-c-numtype) (nt : ty-numtype) (relop : ty-relop-numtype) ->
    (_===_ c) ($relop ⟨ ⟨ ⟨ relop , nt ⟩ , c-1 ⟩ , c-2 ⟩) ->
    ------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ (CONST ⟨ nt , c-1 ⟩) ∷ ((CONST ⟨ nt , c-2 ⟩) ∷ ((RELOP ⟨ nt , relop ⟩) ∷ [])) , (CONST ⟨ I32 (record { }) , c ⟩) ∷ [] ⟩
  local-tee :
    (val : ty-val) (x : ty-idx) ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-pure ⟨ ($admininstr-val val) ∷ ((LOCAL-TEE x) ∷ []) , ($admininstr-val val) ∷ (($admininstr-val val) ∷ ((LOCAL-SET x) ∷ [])) ⟩

data ty-Step-read : ((ty-config × (List ty-admininstr))) → Set
data ty-Step-read where
  call :
    (x : ty-idx) (z : ty-state) ->
    ---------------------------------------------------------------------------------------------------
    ty-Step-read ⟨ ⟨ z , (CALL x) ∷ [] ⟩ , (CALL-ADDR ? {- IdxE: $funcaddr(z)[x] -}) ∷ [] ⟩
  call-addr :
    (a : ty-addr) (f : ty-frame) (instr : List ty-instr) (k : Nat) (m : ty-moduleinst) (n : ty-n) (t : List ty-valtype) (t-1 : List ty-valtype) (t-2 : List ty-valtype) (val : List ty-val) (z : ty-state) ->
    (_===_ ? {- IdxE: $funcinst(z)[a] -}) ⟨ m , ⟨ ⟨ ⟨ t-1 , t-2 ⟩ , t ⟩ , instr ⟩ ⟩ ->
    (_===_ f) (record { LOCAL = (_++_ val) ((map (λ t -> ($default- t))) t) ; MODULE = m }) ->
    ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step-read ⟨ ⟨ z , (_++_ ((map (λ val -> ($admininstr-val val))) val)) ((CALL-ADDR a) ∷ []) ⟩ , (FRAME- ⟨ ⟨ n , f ⟩ , (LABEL- ⟨ ⟨ n , [] ⟩ , (map (λ instr -> ($admininstr-instr instr))) instr ⟩) ∷ [] ⟩) ∷ [] ⟩
  local-get :
    (x : ty-idx) (z : ty-state) ->
    -------------------------------------------------------------------------------------------------------
    ty-Step-read ⟨ ⟨ z , (LOCAL-GET x) ∷ [] ⟩ , ($admininstr-val ($local ⟨ z , x ⟩)) ∷ [] ⟩
  global-get :
    (x : ty-idx) (z : ty-state) ->
    ----------------------------------------------------------------------------------------------------------------
    ty-Step-read ⟨ ⟨ z , (GLOBAL-GET x) ∷ [] ⟩ , ($admininstr-globalinst ($global ⟨ z , x ⟩)) ∷ [] ⟩

data ty-Step : ((ty-config × ty-config)) → Set
data ty-Step where
  pure :
    (instr : List ty-instr) (instr' : List ty-instr) (z : ty-state) ->
    ty-Step-pure ⟨ (map (λ instr -> ($admininstr-instr instr))) instr , (map (λ instr' -> ($admininstr-instr instr'))) instr' ⟩ ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step ⟨ ⟨ z , (map (λ instr -> ($admininstr-instr instr))) instr ⟩ , ⟨ z , (map (λ instr' -> ($admininstr-instr instr'))) instr' ⟩ ⟩
  read :
    (instr : List ty-instr) (instr' : List ty-instr) (z : ty-state) ->
    ty-Step-read ⟨ ⟨ z , (map (λ instr -> ($admininstr-instr instr))) instr ⟩ , (map (λ instr' -> ($admininstr-instr instr'))) instr' ⟩ ->
    ----------------------------------------------------------------------------------------------------------------------------------------------------
    ty-Step ⟨ ⟨ z , (map (λ instr -> ($admininstr-instr instr))) instr ⟩ , ⟨ z , (map (λ instr' -> ($admininstr-instr instr'))) instr' ⟩ ⟩
  local-set :
    (val : ty-val) (x : ty-idx) (z : ty-state) ->
    -----------------------------------------------------------------------------------------------------------------------------------
    ty-Step ⟨ ⟨ z , ($admininstr-val val) ∷ ((LOCAL-SET x) ∷ []) ⟩ , ⟨ $with-local ⟨ ⟨ z , x ⟩ , val ⟩ , [] ⟩ ⟩
  global-set :
    (val : ty-val) (x : ty-idx) (z : ty-state) ->
    -------------------------------------------------------------------------------------------------------------------------------------
    ty-Step ⟨ ⟨ z , ($admininstr-val val) ∷ ((GLOBAL-SET x) ∷ []) ⟩ , ⟨ $with-global ⟨ ⟨ z , x ⟩ , val ⟩ , [] ⟩ ⟩
$ agda output.agda | sed -e "s/\/.*\/_build\///g"
Checking output (default/test-agda/output.agda).
default/test-agda/output.agda:339,1-342,48
Termination checking failed for the following functions:
  $min
Problematic calls:
  $min ⟨ i - 1 , j - 1 ⟩
    (at default/test-agda/output.agda:342,18-22)
default/test-agda/output.agda:345,1-14
Incomplete pattern matching for $size. Missing cases:
  $size (BOT x)
when checking the definition of $size
default/test-agda/output.agda:671,1-18
Incomplete pattern matching for $default-. Missing cases:
  $default- (BOT x)
when checking the definition of $default-
Unsolved constraints
Unsolved metas at the following locations:
  default/test-agda/output.agda:523,49-53
  default/test-agda/output.agda:523,55-65
  default/test-agda/output.agda:528,49-53
  default/test-agda/output.agda:528,55-65
  default/test-agda/output.agda:569,49-56
  default/test-agda/output.agda:614,47-49
  default/test-agda/output.agda:614,52-54
Unsolved interaction metas at the following locations:
  default/test-agda/output.agda:17,10-11
  default/test-agda/output.agda:19,16-17
  default/test-agda/output.agda:21,11-12
  default/test-agda/output.agda:23,12-13
  default/test-agda/output.agda:450,24-25
  default/test-agda/output.agda:456,24-25
  default/test-agda/output.agda:462,24-25
  default/test-agda/output.agda:463,24-25
  default/test-agda/output.agda:468,12-13
  default/test-agda/output.agda:473,12-13
  default/test-agda/output.agda:483,12-13
  default/test-agda/output.agda:508,12-13
  default/test-agda/output.agda:513,12-13
  default/test-agda/output.agda:518,12-13
  default/test-agda/output.agda:523,12-13
  default/test-agda/output.agda:528,12-13
  default/test-agda/output.agda:569,12-13
  default/test-agda/output.agda:577,5-6
  default/test-agda/output.agda:596,20-21
  default/test-agda/output.agda:614,12-13
  default/test-agda/output.agda:623,5-6
  default/test-agda/output.agda:624,5-6
  default/test-agda/output.agda:625,5-6
  default/test-agda/output.agda:842,27-28
  default/test-agda/output.agda:845,29-30
  default/test-agda/output.agda:848,28-29
  default/test-agda/output.agda:851,47-48
  default/test-agda/output.agda:854,44-45
  default/test-agda/output.agda:872,10-11
  default/test-agda/output.agda:875,11-12
  default/test-agda/output.agda:878,12-13
  default/test-agda/output.agda:881,11-12
  default/test-agda/output.agda:999,55-56
  default/test-agda/output.agda:1002,12-13
```

The `sed` incantation is needed to remove (user-specific) absolute paths in Agda output.
