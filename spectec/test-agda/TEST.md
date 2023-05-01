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

n : Set
n = Nat

name : Set
name = String

byte : Set
byte = Nat

u32 : Set
u32 = Nat

idx : Set
idx = Nat

funcidx : Set
funcidx = idx

globalidx : Set
globalidx = idx

labelidx : Set
labelidx = idx

localidx : Set
localidx = idx

data numtype : Set where
  I32 : ⊤ -> numtype

data valtype : Set where
  I32 : ⊤ -> valtype
  BOT : ⊤ -> valtype

data in' : Set where
  I32 : ⊤ -> in'

resulttype : Set
resulttype = List valtype

globaltype = (Maybe ⊤ × valtype)

functype = (resulttype × resulttype)

data sx : Set where
  U : ⊤ -> sx
  S : ⊤ -> sx

data unop_IXX : Set where
  CLZ : ⊤ -> unop_IXX
  CTZ : ⊤ -> unop_IXX
  POPCNT : ⊤ -> unop_IXX

data binop_IXX : Set where
  ADD : ⊤ -> binop_IXX
  SUB : ⊤ -> binop_IXX
  MUL : ⊤ -> binop_IXX
  DIV : sx -> binop_IXX
  REM : sx -> binop_IXX
  AND : ⊤ -> binop_IXX
  OR : ⊤ -> binop_IXX
  XOR : ⊤ -> binop_IXX
  SHL : ⊤ -> binop_IXX
  SHR : sx -> binop_IXX
  ROTL : ⊤ -> binop_IXX
  ROTR : ⊤ -> binop_IXX

data testop_IXX : Set where
  EQZ : ⊤ -> testop_IXX

data relop_IXX : Set where
  EQ : ⊤ -> relop_IXX
  NE : ⊤ -> relop_IXX
  LT : sx -> relop_IXX
  GT : sx -> relop_IXX
  LE : sx -> relop_IXX
  GE : sx -> relop_IXX

data unop_numtype : Set where
  _I : unop_IXX -> unop_numtype

data binop_numtype : Set where
  _I : binop_IXX -> binop_numtype

data testop_numtype : Set where
  _I : testop_IXX -> testop_numtype

data relop_numtype : Set where
  _I : relop_IXX -> relop_numtype

c_numtype : Set
c_numtype = Nat

blocktype : Set
blocktype = functype

data instr : Set where
  UNREACHABLE : ⊤ -> instr
  NOP : ⊤ -> instr
  DROP : ⊤ -> instr
  SELECT : Maybe valtype -> instr
  BLOCK : (blocktype × List instr) -> instr
  LOOP : (blocktype × List instr) -> instr
  IF : ((blocktype × List instr) × List instr) -> instr
  BR : labelidx -> instr
  BR_IF : labelidx -> instr
  CALL : funcidx -> instr
  RETURN : ⊤ -> instr
  CONST : (numtype × c_numtype) -> instr
  UNOP : (numtype × unop_numtype) -> instr
  BINOP : (numtype × binop_numtype) -> instr
  TESTOP : (numtype × testop_numtype) -> instr
  RELOP : (numtype × relop_numtype) -> instr
  LOCAL-GET : localidx -> instr
  LOCAL-SET : localidx -> instr
  LOCAL-TEE : localidx -> instr
  GLOBAL-GET : globalidx -> instr
  GLOBAL-SET : globalidx -> instr

expr : Set
expr = List instr

func = ((functype × List valtype) × expr)

global = (globaltype × expr)

start = funcidx

module' = ((List func × List global) × List start)

{-
;; ../minispec/miniwasm.watsup:139.1-139.14
def Ki : nat
  ;; ../minispec/miniwasm.watsup:140.1-140.15
  def Ki = 1024
 -}

{-
;; ../minispec/miniwasm.watsup:145.1-145.25
def min : (nat, nat) -> nat
  ;; ../minispec/miniwasm.watsup:146.1-146.19
  def {j : nat} min(0, j) = 0
  ;; ../minispec/miniwasm.watsup:147.1-147.19
  def {i : nat} min(i, 0) = 0
  ;; ../minispec/miniwasm.watsup:148.1-148.38
  def {i : nat, j : nat} min((i + 1), (j + 1)) = $min(i, j)
 -}

{-
;; ../minispec/miniwasm.watsup:155.1-155.55
def size : valtype -> nat
  ;; ../minispec/miniwasm.watsup:156.1-156.20
  def size(I32_valtype) = 32
 -}

{-
;; ../minispec/miniwasm.watsup:161.1-161.40
def test_sub_ATOM_22 : n -> nat
  ;; ../minispec/miniwasm.watsup:162.1-162.38
  def {n_3_ATOM_y : n} test_sub_ATOM_22(n_3_ATOM_y) = 0
 -}

{-
;; ../minispec/miniwasm.watsup:164.1-164.26
def curried_ : (n, n) -> nat
  ;; ../minispec/miniwasm.watsup:165.1-165.39
  def {n_1 : n, n_2 : n} curried_(n_1, n_2) = (n_1 + n_2)
 -}

data testfuse : Set where
  AB_ : ((Nat × Nat) × Nat) -> testfuse
  CD : ((Nat × Nat) × Nat) -> testfuse
  EF : ((Nat × Nat) × Nat) -> testfuse
  GH : ((Nat × Nat) × Nat) -> testfuse
  IJ : ((Nat × Nat) × Nat) -> testfuse
  KL : ((Nat × Nat) × Nat) -> testfuse
  MN : ((Nat × Nat) × Nat) -> testfuse
  OP : ((Nat × Nat) × Nat) -> testfuse
  QR : ((Nat × Nat) × Nat) -> testfuse

record context : Set where
  field
    FUNC : List functype
    GLOBAL : List globaltype
    LOCAL : List valtype
    LABEL : List resulttype
    RETURNS : Maybe resulttype

{-
;; ../minispec/miniwasm.watsup:189.1-189.64
relation Functype_ok: `|-%:OK`(functype)
  ;; ../minispec/miniwasm.watsup:193.1-194.13
  rule _ {ft : functype}:
    `|-%:OK`(ft)
 -}

{-
;; ../minispec/miniwasm.watsup:190.1-190.66
relation Globaltype_ok: `|-%:OK`(globaltype)
  ;; ../minispec/miniwasm.watsup:196.1-197.13
  rule _ {gt : globaltype}:
    `|-%:OK`(gt)
 -}

{-
;; ../minispec/miniwasm.watsup:247.1-247.76
relation Blocktype_ok: `%|-%:%`(context, blocktype, functype)
  ;; ../minispec/miniwasm.watsup:249.1-251.29
  rule _ {C : context, ft : functype}:
    `%|-%:%`(C, ft, ft)
    -- Functype_ok: `|-%:OK`(ft)
 -}

{-
;; ../minispec/miniwasm.watsup:202.1-202.66
relation Instr_ok: `%|-%:%`(context, instr, functype)
  ;; ../minispec/miniwasm.watsup:229.1-230.34
  rule unreachable {C : context, t_1* : valtype*, t_2* : valtype*}:
    `%|-%:%`(C, UNREACHABLE_instr, `%->%`(t_1*{t_1}, t_2*{t_2}))

  ;; ../minispec/miniwasm.watsup:232.1-233.32
  rule nop {C : context}:
    `%|-%:%`(C, NOP_instr, `%->%`([], []))

  ;; ../minispec/miniwasm.watsup:235.1-236.27
  rule drop {C : context, t : valtype}:
    `%|-%:%`(C, DROP_instr, `%->%`([t], []))

  ;; ../minispec/miniwasm.watsup:239.1-240.31
  rule select-expl {C : context, t : valtype}:
    `%|-%:%`(C, SELECT_instr(?(t)), `%->%`([t t I32_valtype], [t]))

  ;; ../minispec/miniwasm.watsup:242.1-244.20
  rule select-impl {C : context, numtype : numtype, t : valtype}:
    `%|-%:%`(C, SELECT_instr(?()), `%->%`([t t I32_valtype], [t]))
    -- if (t = (numtype <: valtype))

  ;; ../minispec/miniwasm.watsup:253.1-256.57
  rule block {C : context, bt : blocktype, instr* : instr*, t_1* : valtype*, t_2* : valtype*}:
    `%|-%:%`(C, BLOCK_instr(bt, instr*{instr}), `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- InstrSeq_ok: `%|-%*:%`(C ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2]*{t_2}, RETURNS ?()}, instr*{instr}, `%->%`(t_1*{t_1}, t_2*{t_2}))

  ;; ../minispec/miniwasm.watsup:258.1-261.57
  rule loop {C : context, bt : blocktype, instr* : instr*, t_1* : valtype*, t_2* : valtype*}:
    `%|-%:%`(C, LOOP_instr(bt, instr*{instr}), `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- InstrSeq_ok: `%|-%*:%`(C ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_1]*{t_1}, RETURNS ?()}, instr*{instr}, `%->%`(t_1*{t_1}, t_2*{t_2}))

  ;; ../minispec/miniwasm.watsup:263.1-267.59
  rule if {C : context, bt : blocktype, instr_1* : instr*, instr_2* : instr*, t_1* : valtype*, t_2* : valtype*}:
    `%|-%:%`(C, IF_instr(bt, instr_1*{instr_1}, instr_2*{instr_2}), `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- InstrSeq_ok: `%|-%*:%`(C ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2]*{t_2}, RETURNS ?()}, instr_1*{instr_1}, `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- InstrSeq_ok: `%|-%*:%`(C ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2]*{t_2}, RETURNS ?()}, instr_2*{instr_2}, `%->%`(t_1*{t_1}, t_2*{t_2}))

  ;; ../minispec/miniwasm.watsup:270.1-272.24
  rule br {C : context, l : labelidx, t* : valtype*, t_1* : valtype*, t_2* : valtype*}:
    `%|-%:%`(C, BR_instr(l), `%->%`(t_1*{t_1} :: t*{t}, t_2*{t_2}))
    -- if (C.LABEL_context[l] = t*{t})

  ;; ../minispec/miniwasm.watsup:274.1-276.24
  rule br_if {C : context, l : labelidx, t* : valtype*}:
    `%|-%:%`(C, BR_IF_instr(l), `%->%`(t*{t} :: [I32_valtype], t*{t}))
    -- if (C.LABEL_context[l] = t*{t})

  ;; ../minispec/miniwasm.watsup:278.1-280.25
  rule return {C : context, t* : valtype*, t_1* : valtype*, t_2* : valtype*}:
    `%|-%:%`(C, RETURN_instr, `%->%`(t_1*{t_1} :: t*{t}, t_2*{t_2}))
    -- if (C.RETURNS_context = ?(t*{t}))

  ;; ../minispec/miniwasm.watsup:282.1-284.33
  rule call {C : context, t_1* : valtype*, t_2* : valtype*, x : idx}:
    `%|-%:%`(C, CALL_instr(x), `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- if (C.FUNC_context[x] = `%->%`(t_1*{t_1}, t_2*{t_2}))

  ;; ../minispec/miniwasm.watsup:287.1-288.37
  rule const {C : context, c_nt : c_numtype, nt : numtype}:
    `%|-%:%`(C, CONST_instr(nt, c_nt), `%->%`([], [(nt <: valtype)]))

  ;; ../minispec/miniwasm.watsup:290.1-291.31
  rule unop {C : context, nt : numtype, unop : unop_numtype}:
    `%|-%:%`(C, UNOP_instr(nt, unop), `%->%`([(nt <: valtype)], [(nt <: valtype)]))

  ;; ../minispec/miniwasm.watsup:293.1-294.36
  rule binop {C : context, binop : binop_numtype, nt : numtype}:
    `%|-%:%`(C, BINOP_instr(nt, binop), `%->%`([(nt <: valtype) (nt <: valtype)], [(nt <: valtype)]))

  ;; ../minispec/miniwasm.watsup:296.1-297.36
  rule testop {C : context, nt : numtype, testop : testop_numtype}:
    `%|-%:%`(C, TESTOP_instr(nt, testop), `%->%`([(nt <: valtype)], [I32_valtype]))

  ;; ../minispec/miniwasm.watsup:299.1-300.37
  rule relop {C : context, nt : numtype, relop : relop_numtype}:
    `%|-%:%`(C, RELOP_instr(nt, relop), `%->%`([(nt <: valtype) (nt <: valtype)], [I32_valtype]))

  ;; ../minispec/miniwasm.watsup:303.1-305.23
  rule local.get {C : context, t : valtype, x : idx}:
    `%|-%:%`(C, LOCAL.GET_instr(x), `%->%`([], [t]))
    -- if (C.LOCAL_context[x] = t)

  ;; ../minispec/miniwasm.watsup:307.1-309.23
  rule local.set {C : context, t : valtype, x : idx}:
    `%|-%:%`(C, LOCAL.SET_instr(x), `%->%`([t], []))
    -- if (C.LOCAL_context[x] = t)

  ;; ../minispec/miniwasm.watsup:311.1-313.23
  rule local.tee {C : context, t : valtype, x : idx}:
    `%|-%:%`(C, LOCAL.TEE_instr(x), `%->%`([t], [t]))
    -- if (C.LOCAL_context[x] = t)

  ;; ../minispec/miniwasm.watsup:316.1-318.29
  rule global.get {C : context, t : valtype, x : idx}:
    `%|-%:%`(C, GLOBAL.GET_instr(x), `%->%`([], [t]))
    -- if (C.GLOBAL_context[x] = `MUT%?%`(()?{}, t))

  ;; ../minispec/miniwasm.watsup:320.1-322.28
  rule global.set {C : context, t : valtype, x : idx}:
    `%|-%:%`(C, GLOBAL.SET_instr(x), `%->%`([t], []))
    -- if (C.GLOBAL_context[x] = `MUT%?%`(?(()), t))
 -}

{-
;; ../minispec/miniwasm.watsup:203.1-203.67
relation InstrSeq_ok: `%|-%*:%`(context, instr*, functype)
  ;; ../minispec/miniwasm.watsup:212.1-213.36
  rule empty {C : context}:
    `%|-%*:%`(C, [], `%->%`([], []))

  ;; ../minispec/miniwasm.watsup:215.1-218.46
  rule seq {C : context, instr_1 : instr, instr_2 : instr, t_1* : valtype*, t_2* : valtype*, t_3* : valtype*}:
    `%|-%*:%`(C, [instr_1] :: instr_2*{}, `%->%`(t_1*{t_1}, t_3*{t_3}))
    -- Instr_ok: `%|-%:%`(C, instr_1, `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- InstrSeq_ok: `%|-%*:%`(C, [instr_2], `%->%`(t_2*{t_2}, t_3*{t_3}))

  ;; ../minispec/miniwasm.watsup:220.1-222.45
  rule weak {C : context, instr* : instr*, t_1 : valtype, t_2* : valtype*}:
    `%|-%*:%`(C, instr*{instr}, `%->%`([t_1], t_2*{t_2}))
    -- InstrSeq_ok: `%|-%*:%`(C, instr*{instr}, `%->%`(t_1*{}, t_2*{t_2}))

  ;; ../minispec/miniwasm.watsup:224.1-226.45
  rule frame {C : context, instr* : instr*, t* : valtype*, t_1* : valtype*, t_2* : valtype*}:
    `%|-%*:%`(C, instr*{instr}, `%->%`(t*{t} :: t_1*{t_1}, t*{t} :: t_2*{t_2}))
    -- InstrSeq_ok: `%|-%*:%`(C, instr*{instr}, `%->%`(t_1*{t_1}, t_2*{t_2}))
 -}

{-
;; ../minispec/miniwasm.watsup:204.1-204.71
relation Expr_ok: `%|-%:%`(context, expr, resulttype)
  ;; ../minispec/miniwasm.watsup:207.1-209.46
  rule _ {C : context, instr* : instr*, t* : valtype*}:
    `%|-%:%`(C, instr*{instr}, t*{t})
    -- InstrSeq_ok: `%|-%*:%`(C, instr*{instr}, `%->%`([], t*{t}))
 -}

{-
;; ../minispec/miniwasm.watsup:327.1-327.78
relation Instr_const: `%|-%CONST`(context, instr)
  ;; ../minispec/miniwasm.watsup:331.1-332.26
  rule const {C : context, c : c_numtype, nt : numtype}:
    `%|-%CONST`(C, CONST_instr(nt, c))

  ;; ../minispec/miniwasm.watsup:334.1-336.32
  rule global.get {C : context, t : valtype, x : idx}:
    `%|-%CONST`(C, GLOBAL.GET_instr(x))
    -- if (C.GLOBAL_context[x] = `MUT%?%`(?(), t))
 -}

{-
;; ../minispec/miniwasm.watsup:328.1-328.77
relation Expr_const: `%|-%CONST`(context, expr)
  ;; ../minispec/miniwasm.watsup:339.1-340.38
  rule _ {C : context, instr* : instr*}:
    `%|-%CONST`(C, instr*{instr})
    -- (Instr_const: `%|-%CONST`(C, instr))*{instr}
 -}

{-
;; ../minispec/miniwasm.watsup:329.1-329.78
relation Expr_ok_const: `%|-%:%CONST`(context, expr, valtype)
  ;; ../minispec/miniwasm.watsup:343.1-346.33
  rule _ {C : context, expr : expr, t : valtype}:
    `%|-%:%CONST`(C, expr, t)
    -- Expr_ok: `%|-%:%`(C, expr, [t])
    -- Expr_const: `%|-%CONST`(C, expr)
 -}

{-
;; ../minispec/miniwasm.watsup:351.1-351.73
relation Func_ok: `%|-%:%`(context, func, functype)
  ;; ../minispec/miniwasm.watsup:356.1-360.76
  rule _ {C : context, expr : expr, ft : functype, t* : valtype*, t_1* : valtype*, t_2* : valtype*}:
    `%|-%:%`(C, `FUNC%%*%`(ft, t*{t}, expr), ft)
    -- if (ft = `%->%`(t_1*{t_1}, t_2*{t_2}))
    -- Functype_ok: `|-%:OK`(ft)
    -- Expr_ok: `%|-%:%`(C ++ {FUNC [], GLOBAL [], LOCAL t_1*{t_1} :: t*{t}, LABEL [], RETURNS ?()} ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [t_2*{t_2}], RETURNS ?()} ++ {FUNC [], GLOBAL [], LOCAL [], LABEL [], RETURNS ?(t_2*{t_2})}, expr, t_2*{t_2})
 -}

{-
;; ../minispec/miniwasm.watsup:352.1-352.75
relation Global_ok: `%|-%:%`(context, global, globaltype)
  ;; ../minispec/miniwasm.watsup:362.1-366.40
  rule _ {C : context, expr : expr, gt : globaltype, t : valtype}:
    `%|-%:%`(C, GLOBAL(gt, expr), gt)
    -- Globaltype_ok: `|-%:OK`(gt)
    -- if (gt = `MUT%?%`(()?{}, t))
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, t)
 -}

{-
;; ../minispec/miniwasm.watsup:353.1-353.74
relation Start_ok: `%|-%:OK`(context, start)
  ;; ../minispec/miniwasm.watsup:368.1-370.39
  rule _ {C : context, x : idx}:
    `%|-%:OK`(C, START(x))
    -- if (C.FUNC_context[x] = `%->%`([], []))
 -}

{-
;; ../minispec/miniwasm.watsup:373.1-373.62
relation Module_ok: `|-%:OK`(module)
  ;; ../minispec/miniwasm.watsup:375.1-385.18
  rule _ {C : context, ft* : functype*, func* : func*, global* : global*, gt* : globaltype*, start* : start*}:
    `|-%:OK`(`MODULE%*%*%*`(func*{func}, global*{global}, start*{start}))
    -- if (C = {FUNC ft*{ft}, GLOBAL gt*{gt}, LOCAL [], LABEL [], RETURNS ?()})
    -- (Func_ok: `%|-%:%`(C, func, ft))*{ft func}
    -- (Global_ok: `%|-%:%`(C, global, gt))*{global gt}
    -- (Start_ok: `%|-%:OK`(C, start))*{start}
    -- if (|start*{start}| <= 1)
 -}

addr : Set
addr = Nat

funcaddr : Set
funcaddr = addr

globaladdr : Set
globaladdr = addr

labeladdr : Set
labeladdr = addr

hostaddr : Set
hostaddr = addr

data num : Set where
  CONST : (numtype × c_numtype) -> num

data val : Set where
  CONST : (numtype × c_numtype) -> val

data result : Set where
  _VALS : List val -> result
  TRAP : ⊤ -> result

{-
;; ../minispec/miniwasm.watsup:414.1-414.44
def default_ : valtype -> val
  ;; ../minispec/miniwasm.watsup:415.1-415.35
  def default_(I32_valtype) = CONST_val(I32_numtype, 0)
 -}

record moduleinst : Set where
  field
    FUNC : List funcaddr
    GLOBAL : List globaladdr

funcinst = (moduleinst × func)

globalinst : Set
globalinst = val

record store : Set where
  field
    FUNC : List funcinst
    GLOBAL : List globalinst

record frame : Set where
  field
    LOCAL : List val
    MODULE : moduleinst

state = (store × frame)

data admininstr : Set where
  UNREACHABLE : ⊤ -> admininstr
  NOP : ⊤ -> admininstr
  DROP : ⊤ -> admininstr
  SELECT : Maybe valtype -> admininstr
  BLOCK : (blocktype × List instr) -> admininstr
  LOOP : (blocktype × List instr) -> admininstr
  IF : ((blocktype × List instr) × List instr) -> admininstr
  BR : labelidx -> admininstr
  BR_IF : labelidx -> admininstr
  CALL : funcidx -> admininstr
  RETURN : ⊤ -> admininstr
  CONST : (numtype × c_numtype) -> admininstr
  UNOP : (numtype × unop_numtype) -> admininstr
  BINOP : (numtype × binop_numtype) -> admininstr
  TESTOP : (numtype × testop_numtype) -> admininstr
  RELOP : (numtype × relop_numtype) -> admininstr
  LOCAL-GET : localidx -> admininstr
  LOCAL-SET : localidx -> admininstr
  LOCAL-TEE : localidx -> admininstr
  GLOBAL-GET : globalidx -> admininstr
  GLOBAL-SET : globalidx -> admininstr
  CALL_ADDR : funcaddr -> admininstr
  LABEL_ : ((n × List instr) × List admininstr) -> admininstr
  FRAME_ : ((n × frame) × List admininstr) -> admininstr
  TRAP : ⊤ -> admininstr

config = (state × List admininstr)

{-
;; ../minispec/miniwasm.watsup:448.1-448.59
def funcaddr : state -> funcaddr*
  ;; ../minispec/miniwasm.watsup:449.1-449.38
  def {f : frame, s : store} funcaddr(`%;%`(s, f)) = f.MODULE_frame.FUNC_moduleinst
 -}

{-
;; ../minispec/miniwasm.watsup:451.1-451.52
def funcinst : state -> funcinst*
  ;; ../minispec/miniwasm.watsup:452.1-452.31
  def {f : frame, s : store} funcinst(`%;%`(s, f)) = s.FUNC_store
 -}

{-
;; ../minispec/miniwasm.watsup:454.1-454.67
def func : (state, funcidx) -> funcinst
  ;; ../minispec/miniwasm.watsup:458.1-458.48
  def {f : frame, s : store, x : idx} func(`%;%`(s, f), x) = s.FUNC_store[f.MODULE_frame.FUNC_moduleinst[x]]
 -}

{-
;; ../minispec/miniwasm.watsup:455.1-455.69
def global : (state, globalidx) -> globalinst
  ;; ../minispec/miniwasm.watsup:459.1-459.54
  def {f : frame, s : store, x : idx} global(`%;%`(s, f), x) = s.GLOBAL_store[f.MODULE_frame.GLOBAL_moduleinst[x]]
 -}

{-
;; ../minispec/miniwasm.watsup:456.1-456.68
def local : (state, localidx) -> val
  ;; ../minispec/miniwasm.watsup:460.1-460.35
  def {f : frame, s : store, x : idx} local(`%;%`(s, f), x) = f.LOCAL_frame[x]
 -}

{-
;; ../minispec/miniwasm.watsup:463.1-463.78
def with_local : (state, localidx, val) -> state
  ;; ../minispec/miniwasm.watsup:466.1-466.52
  def {f : frame, s : store, v : val, x : idx} with_local(`%;%`(s, f), x, v) = `%;%`(s, f[LOCAL_frame[x] = v])
 -}

{-
;; ../minispec/miniwasm.watsup:464.1-464.79
def with_global : (state, globalidx, val) -> state
  ;; ../minispec/miniwasm.watsup:467.1-467.71
  def {f : frame, s : store, v : val, x : idx} with_global(`%;%`(s, f), x, v) = `%;%`(s[GLOBAL_store[f.MODULE_frame.GLOBAL_moduleinst[x]] = v], f)
 -}

data E : Set where
  _HOLE : ⊤ -> E
  _SEQ : ((List val × E) × List instr) -> E
  LABEL_ : ((n × List instr) × E) -> E

{-
;; ../minispec/miniwasm.watsup:485.1-485.79
def unop : (unop_numtype, numtype, c_numtype) -> c_numtype*
 -}

{-
;; ../minispec/miniwasm.watsup:486.1-486.80
def binop : (binop_numtype, numtype, c_numtype, c_numtype) -> c_numtype*
 -}

{-
;; ../minispec/miniwasm.watsup:487.1-487.79
def testop : (testop_numtype, numtype, c_numtype) -> c_numtype
 -}

{-
;; ../minispec/miniwasm.watsup:488.1-488.80
def relop : (relop_numtype, numtype, c_numtype, c_numtype) -> c_numtype
 -}

{-
;; ../minispec/miniwasm.watsup:493.1-493.63
relation Step_pure: `%*~>%*`(admininstr*, admininstr*)
  ;; ../minispec/miniwasm.watsup:505.1-506.24
  rule unreachable:
    `%*~>%*`([UNREACHABLE_admininstr], [TRAP_admininstr])

  ;; ../minispec/miniwasm.watsup:508.1-509.19
  rule nop:
    `%*~>%*`([NOP_admininstr], [])

  ;; ../minispec/miniwasm.watsup:511.1-512.24
  rule drop {val : val}:
    `%*~>%*`([(val <: admininstr) DROP_admininstr], [])

  ;; ../minispec/miniwasm.watsup:515.1-517.16
  rule select-true {c : c_numtype, t? : valtype?, val_1 : val, val_2 : val}:
    `%*~>%*`([(val_1 <: admininstr) (val_2 <: admininstr) CONST_admininstr(I32_numtype, c) SELECT_admininstr(t?{t})], [(val_1 <: admininstr)])
    -- if (c =/= 0)

  ;; ../minispec/miniwasm.watsup:519.1-521.14
  rule select-false {c : c_numtype, t? : valtype?, val_1 : val, val_2 : val}:
    `%*~>%*`([(val_1 <: admininstr) (val_2 <: admininstr) CONST_admininstr(I32_numtype, c) SELECT_admininstr(t?{t})], [(val_2 <: admininstr)])
    -- if (c = 0)

  ;; ../minispec/miniwasm.watsup:524.1-526.28
  rule block {bt : blocktype, instr* : instr*, k : nat, n : n, t_1^k : valtype^k, t_2^n : valtype^n, val^k : val^k}:
    `%*~>%*`((val <: admininstr)^k{val} :: [BLOCK_admininstr(bt, instr*{instr})], [LABEL__admininstr(n, [], (val <: admininstr)^k{val} :: (instr <: admininstr)*{instr})])
    -- if (bt = `%->%`(t_1^k{t_1}, t_2^n{t_2}))

  ;; ../minispec/miniwasm.watsup:528.1-530.28
  rule loop {bt : blocktype, instr* : instr*, k : nat, n : n, t_1^k : valtype^k, t_2^n : valtype^n, val^k : val^k}:
    `%*~>%*`((val <: admininstr)^k{val} :: [LOOP_admininstr(bt, instr*{instr})], [LABEL__admininstr(n, [LOOP_instr(bt, instr*{instr})], (val <: admininstr)^k{val} :: (instr <: admininstr)*{instr})])
    -- if (bt = `%->%`(t_1^k{t_1}, t_2^n{t_2}))

  ;; ../minispec/miniwasm.watsup:532.1-534.16
  rule if-true {bt : blocktype, c : c_numtype, instr_1* : instr*, instr_2* : instr*}:
    `%*~>%*`([CONST_admininstr(I32_numtype, c) IF_admininstr(bt, instr_1*{instr_1}, instr_2*{instr_2})], [BLOCK_admininstr(bt, instr_1*{instr_1})])
    -- if (c =/= 0)

  ;; ../minispec/miniwasm.watsup:536.1-538.14
  rule if-false {bt : blocktype, c : c_numtype, instr_1* : instr*, instr_2* : instr*}:
    `%*~>%*`([CONST_admininstr(I32_numtype, c) IF_admininstr(bt, instr_1*{instr_1}, instr_2*{instr_2})], [BLOCK_admininstr(bt, instr_2*{instr_2})])
    -- if (c = 0)

  ;; ../minispec/miniwasm.watsup:541.1-542.38
  rule label-vals {instr* : instr*, n : n, val* : val*}:
    `%*~>%*`([LABEL__admininstr(n, instr*{instr}, (val <: admininstr)*{val})], (val <: admininstr)*{val})

  ;; ../minispec/miniwasm.watsup:546.1-547.69
  rule br-zero {instr* : instr*, instr'* : instr*, n : n, val^n : val^n, val'* : val*}:
    `%*~>%*`([LABEL__admininstr(n, instr'*{instr'}, (val' <: admininstr)*{val'} :: (val <: admininstr)^n{val} :: [BR_admininstr(0)] :: (instr <: admininstr)*{instr})], (val <: admininstr)^n{val} :: (instr' <: admininstr)*{instr'})

  ;; ../minispec/miniwasm.watsup:549.1-550.65
  rule br-succ {instr* : instr*, instr'* : instr*, l : labelidx, n : n, val* : val*}:
    `%*~>%*`([LABEL__admininstr(n, instr'*{instr'}, (val <: admininstr)*{val} :: [BR_admininstr(l + 1)] :: (instr <: admininstr)*{instr})], (val <: admininstr)*{val} :: [BR_admininstr(l)])

  ;; ../minispec/miniwasm.watsup:553.1-555.16
  rule br_if-true {c : c_numtype, l : labelidx}:
    `%*~>%*`([CONST_admininstr(I32_numtype, c) BR_IF_admininstr(l)], [BR_admininstr(l)])
    -- if (c =/= 0)

  ;; ../minispec/miniwasm.watsup:557.1-559.14
  rule br_if-false {c : c_numtype, l : labelidx}:
    `%*~>%*`([CONST_admininstr(I32_numtype, c) BR_IF_admininstr(l)], [])
    -- if (c = 0)

  ;; ../minispec/miniwasm.watsup:571.1-572.35
  rule frame-vals {f : frame, n : n, val^n : val^n}:
    `%*~>%*`([FRAME__admininstr(n, f, (val <: admininstr)^n{val})], (val <: admininstr)^n{val})

  ;; ../minispec/miniwasm.watsup:574.1-575.55
  rule return-frame {f : frame, instr* : instr*, n : n, val^n : val^n, val'* : val*}:
    `%*~>%*`([FRAME__admininstr(n, f, (val' <: admininstr)*{val'} :: (val <: admininstr)^n{val} :: [RETURN_admininstr] :: (instr <: admininstr)*{instr})], (val <: admininstr)^n{val})

  ;; ../minispec/miniwasm.watsup:577.1-578.60
  rule return-label {instr* : instr*, instr'* : instr*, k : nat, val* : val*}:
    `%*~>%*`([LABEL__admininstr(k, instr'*{instr'}, (val <: admininstr)*{val} :: [RETURN_admininstr] :: (instr <: admininstr)*{instr})], (val <: admininstr)*{val} :: [RETURN_admininstr])

  ;; ../minispec/miniwasm.watsup:581.1-583.33
  rule unop-val {c : c_numtype, c_1 : c_numtype, nt : numtype, unop : unop_numtype}:
    `%*~>%*`([CONST_admininstr(nt, c_1) UNOP_admininstr(nt, unop)], [CONST_admininstr(nt, c)])
    -- if ($unop(unop, nt, c_1) = [c])

  ;; ../minispec/miniwasm.watsup:585.1-587.39
  rule unop-trap {c_1 : c_numtype, nt : numtype, unop : unop_numtype}:
    `%*~>%*`([CONST_admininstr(nt, c_1) UNOP_admininstr(nt, unop)], [TRAP_admininstr])
    -- if ($unop(unop, nt, c_1) = [])

  ;; ../minispec/miniwasm.watsup:590.1-592.40
  rule binop-val {binop : binop_numtype, c : c_numtype, c_1 : c_numtype, c_2 : c_numtype, nt : numtype}:
    `%*~>%*`([CONST_admininstr(nt, c_1) CONST_admininstr(nt, c_2) BINOP_admininstr(nt, binop)], [CONST_admininstr(nt, c)])
    -- if ($binop(binop, nt, c_1, c_2) = [c])

  ;; ../minispec/miniwasm.watsup:594.1-596.46
  rule binop-trap {binop : binop_numtype, c_1 : c_numtype, c_2 : c_numtype, nt : numtype}:
    `%*~>%*`([CONST_admininstr(nt, c_1) CONST_admininstr(nt, c_2) BINOP_admininstr(nt, binop)], [TRAP_admininstr])
    -- if ($binop(binop, nt, c_1, c_2) = [])

  ;; ../minispec/miniwasm.watsup:599.1-601.37
  rule testop {c : c_numtype, c_1 : c_numtype, nt : numtype, testop : testop_numtype}:
    `%*~>%*`([CONST_admininstr(nt, c_1) TESTOP_admininstr(nt, testop)], [CONST_admininstr(I32_numtype, c)])
    -- if (c = $testop(testop, nt, c_1))

  ;; ../minispec/miniwasm.watsup:603.1-605.40
  rule relop {c : c_numtype, c_1 : c_numtype, c_2 : c_numtype, nt : numtype, relop : relop_numtype}:
    `%*~>%*`([CONST_admininstr(nt, c_1) CONST_admininstr(nt, c_2) RELOP_admininstr(nt, relop)], [CONST_admininstr(I32_numtype, c)])
    -- if (c = $relop(relop, nt, c_1, c_2))

  ;; ../minispec/miniwasm.watsup:614.1-615.47
  rule local.tee {val : val, x : idx}:
    `%*~>%*`([(val <: admininstr) LOCAL.TEE_admininstr(x)], [(val <: admininstr) (val <: admininstr) LOCAL.SET_admininstr(x)])
 -}

{-
;; ../minispec/miniwasm.watsup:494.1-494.63
relation Step_read: `%~>%*`(config, admininstr*)
  ;; ../minispec/miniwasm.watsup:562.1-563.47
  rule call {x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [CALL_admininstr(x)]), [CALL_ADDR_admininstr($funcaddr(z)[x])])

  ;; ../minispec/miniwasm.watsup:565.1-568.52
  rule call_addr {a : addr, f : frame, instr* : instr*, k : nat, m : moduleinst, n : n, t* : valtype*, t_1^k : valtype^k, t_2^n : valtype^n, val^k : val^k, z : state}:
    `%~>%*`(`%;%*`(z, (val <: admininstr)^k{val} :: [CALL_ADDR_admininstr(a)]), [FRAME__admininstr(n, f, [LABEL__admininstr(n, [], (instr <: admininstr)*{instr})])])
    -- if ($funcinst(z)[a] = `%;%`(m, `FUNC%%*%`(`%->%`(t_1^k{t_1}, t_2^n{t_2}), t*{t}, instr*{instr})))
    -- if (f = {LOCAL val^k{val} :: $default_(t)*{t}, MODULE m})

  ;; ../minispec/miniwasm.watsup:608.1-609.37
  rule local.get {x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [LOCAL.GET_admininstr(x)]), [($local(z, x) <: admininstr)])

  ;; ../minispec/miniwasm.watsup:618.1-619.39
  rule global.get {x : idx, z : state}:
    `%~>%*`(`%;%*`(z, [GLOBAL.GET_admininstr(x)]), [($global(z, x) <: admininstr)])
 -}

{-
;; ../minispec/miniwasm.watsup:492.1-492.63
relation Step: `%~>%`(config, config)
  ;; ../minispec/miniwasm.watsup:496.1-498.34
  rule pure {instr* : instr*, instr'* : instr*, z : state}:
    `%~>%`(`%;%*`(z, (instr <: admininstr)*{instr}), `%;%*`(z, (instr' <: admininstr)*{instr'}))
    -- Step_pure: `%*~>%*`((instr <: admininstr)*{instr}, (instr' <: admininstr)*{instr'})

  ;; ../minispec/miniwasm.watsup:500.1-502.37
  rule read {instr* : instr*, instr'* : instr*, z : state}:
    `%~>%`(`%;%*`(z, (instr <: admininstr)*{instr}), `%;%*`(z, (instr' <: admininstr)*{instr'}))
    -- Step_read: `%~>%*`(`%;%*`(z, (instr <: admininstr)*{instr}), (instr' <: admininstr)*{instr'})

  ;; ../minispec/miniwasm.watsup:611.1-612.60
  rule local.set {val : val, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [(val <: admininstr) LOCAL.SET_admininstr(x)]), `%;%*`($with_local(z, x, val), []))

  ;; ../minispec/miniwasm.watsup:621.1-622.62
  rule global.set {val : val, x : idx, z : state}:
    `%~>%`(`%;%*`(z, [(val <: admininstr) GLOBAL.SET_admininstr(x)]), `%;%*`($with_global(z, x, val), []))
 -}
$ agda output.agda | sed -e "s/(.*\/_build\//(/g"
Checking output (default/test-agda/output.agda).
```

The `sed` incantation is needed to replace

    Checking output (/ABSOLUTE/PATH/TO/USER/FOLDER/spectec/_build/default/test-agda/output.agda).

with

    Checking output (default/test-agda/output.agda).
