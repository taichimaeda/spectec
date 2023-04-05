# Preview

```sh
$ dune exec ../src/exe-lean4/main.exe -- ../spec/*.watsup -o SpecTec.lean
$ cat SpecTec.lean
/- Lean 4 export -/

instance : Append (Option a) where
  append := fun o1 o2 => match o1 with | none => o2 | _ => o1

@[reducible] def N := Nat

@[reducible] def Name := String

@[reducible] def Byte := Nat

@[reducible] def U32 := Nat

@[reducible] def Idx := Nat

@[reducible] def Funcidx := Idx

@[reducible] def Globalidx := Idx

@[reducible] def Tableidx := Idx

@[reducible] def Memidx := Idx

@[reducible] def Elemidx := Idx

@[reducible] def Dataidx := Idx

@[reducible] def Labelidx := Idx

@[reducible] def Localidx := Idx

inductive Numtype where
 | I32 : Numtype
 | I64 : Numtype
 | F32 : Numtype
 | F64 : Numtype
  deriving Inhabited, BEq

inductive Vectype where
 | V128 : Vectype
  deriving Inhabited, BEq

inductive Reftype where
 | FUNCREF : Reftype
 | EXTERNREF : Reftype
  deriving Inhabited, BEq

inductive Valtype where
 | Numtype : Numtype -> Valtype
 | Vectype : Vectype -> Valtype
 | Reftype : Reftype -> Valtype
 | BOT : Valtype
  deriving Inhabited, BEq

inductive In where
 | I32 : In
 | I64 : In
  deriving Inhabited, BEq

inductive Fn where
 | F32 : Fn
 | F64 : Fn
  deriving Inhabited, BEq

@[reducible] def Resulttype := (List Valtype)

@[reducible] def Limits := /- mixop: `[%..%]` -/ (U32 × U32)

@[reducible] def Globaltype := /- mixop: `MUT%?%` -/ ((Option Unit) × Valtype)

@[reducible] def Functype := /- mixop: `%->%` -/ (Resulttype × Resulttype)

@[reducible] def Tabletype := /- mixop: `%%` -/ (Limits × Reftype)

@[reducible] def Memtype := /- mixop: `%I8` -/ Limits

@[reducible] def Elemtype := Reftype

@[reducible] def Datatype := /- mixop: OK -/ Unit

inductive Externtype where
 | GLOBAL : Globaltype -> Externtype
 | FUNC : Functype -> Externtype
 | TABLE : Tabletype -> Externtype
 | MEMORY : Memtype -> Externtype
  deriving Inhabited, BEq

inductive Sx where
 | U : Sx
 | S : Sx
  deriving Inhabited, BEq

inductive Unop_IXX where
 | CLZ : Unop_IXX
 | CTZ : Unop_IXX
 | POPCNT : Unop_IXX
  deriving Inhabited, BEq

inductive Unop_FXX where
 | ABS : Unop_FXX
 | NEG : Unop_FXX
 | SQRT : Unop_FXX
 | CEIL : Unop_FXX
 | FLOOR : Unop_FXX
 | TRUNC : Unop_FXX
 | NEAREST : Unop_FXX
  deriving Inhabited, BEq

inductive Binop_IXX where
 | ADD : Binop_IXX
 | SUB : Binop_IXX
 | MUL : Binop_IXX
 | DIV : Sx -> Binop_IXX
 | REM : Sx -> Binop_IXX
 | AND : Binop_IXX
 | OR : Binop_IXX
 | XOR : Binop_IXX
 | SHL : Binop_IXX
 | SHR : Sx -> Binop_IXX
 | ROTL : Binop_IXX
 | ROTR : Binop_IXX
  deriving Inhabited, BEq

inductive Binop_FXX where
 | ADD : Binop_FXX
 | SUB : Binop_FXX
 | MUL : Binop_FXX
 | DIV : Binop_FXX
 | MIN : Binop_FXX
 | MAX : Binop_FXX
 | COPYSIGN : Binop_FXX
  deriving Inhabited, BEq

inductive Testop_IXX where
 | EQZ : Testop_IXX
  deriving Inhabited, BEq

inductive Testop_FXX where
  deriving BEq

inductive Relop_IXX where
 | EQ : Relop_IXX
 | NE : Relop_IXX
 | LT : Sx -> Relop_IXX
 | GT : Sx -> Relop_IXX
 | LE : Sx -> Relop_IXX
 | GE : Sx -> Relop_IXX
  deriving Inhabited, BEq

inductive Relop_FXX where
 | EQ : Relop_FXX
 | NE : Relop_FXX
 | LT : Relop_FXX
 | GT : Relop_FXX
 | LE : Relop_FXX
 | GE : Relop_FXX
  deriving Inhabited, BEq

inductive Unop_numtype where
 | _I : Unop_IXX -> Unop_numtype
 | _F : Unop_FXX -> Unop_numtype
  deriving Inhabited, BEq

inductive Binop_numtype where
 | _I : Binop_IXX -> Binop_numtype
 | _F : Binop_FXX -> Binop_numtype
  deriving Inhabited, BEq

inductive Testop_numtype where
 | _I : Testop_IXX -> Testop_numtype
 | _F : Testop_FXX -> Testop_numtype
  deriving Inhabited, BEq

inductive Relop_numtype where
 | _I : Relop_IXX -> Relop_numtype
 | _F : Relop_FXX -> Relop_numtype
  deriving Inhabited, BEq

inductive Cvtop where
 | CONVERT : Cvtop
 | REINTERPRET : Cvtop
  deriving Inhabited, BEq

@[reducible] def C_numtype := Nat

@[reducible] def C_vectype := Nat

@[reducible] def Blocktype := Functype

inductive Instr where
 | UNREACHABLE : Instr
 | NOP : Instr
 | DROP : Instr
 | SELECT : (Option Valtype) -> Instr
 | BLOCK : (Blocktype × (List Instr)) -> Instr
 | LOOP : (Blocktype × (List Instr)) -> Instr
 | IF : (Blocktype × (List Instr) × (List Instr)) -> Instr
 | BR : Labelidx -> Instr
 | BR_IF : Labelidx -> Instr
 | BR_TABLE : ((List Labelidx) × Labelidx) -> Instr
 | CALL : Funcidx -> Instr
 | CALL_INDIRECT : (Tableidx × Functype) -> Instr
 | RETURN : Instr
 | CONST : (Numtype × C_numtype) -> Instr
 | UNOP : (Numtype × Unop_numtype) -> Instr
 | BINOP : (Numtype × Binop_numtype) -> Instr
 | TESTOP : (Numtype × Testop_numtype) -> Instr
 | RELOP : (Numtype × Relop_numtype) -> Instr
 | EXTEND : (Numtype × N) -> Instr
 | CVTOP : (Numtype × Cvtop × Numtype × (Option Sx)) -> Instr
 | REF_NULL : Reftype -> Instr
 | REF_FUNC : Funcidx -> Instr
 | REF_IS_NULL : Instr
 | LOCAL_GET : Localidx -> Instr
 | LOCAL_SET : Localidx -> Instr
 | LOCAL_TEE : Localidx -> Instr
 | GLOBAL_GET : Globalidx -> Instr
 | GLOBAL_SET : Globalidx -> Instr
 | TABLE_GET : Tableidx -> Instr
 | TABLE_SET : Tableidx -> Instr
 | TABLE_SIZE : Tableidx -> Instr
 | TABLE_GROW : Tableidx -> Instr
 | TABLE_FILL : Tableidx -> Instr
 | TABLE_COPY : (Tableidx × Tableidx) -> Instr
 | TABLE_INIT : (Tableidx × Elemidx) -> Instr
 | ELEM_DROP : Elemidx -> Instr
 | MEMORY_SIZE : Instr
 | MEMORY_GROW : Instr
 | MEMORY_FILL : Instr
 | MEMORY_COPY : Instr
 | MEMORY_INIT : Dataidx -> Instr
 | DATA_DROP : Dataidx -> Instr
 | LOAD : (Numtype × (Option (N × Sx)) × Nat × Nat) -> Instr
 | STORE : (Numtype × (Option N) × Nat × Nat) -> Instr
  deriving Inhabited, BEq

@[reducible] def Expr := (List Instr)

inductive Elemmode where
 | TABLE : (Tableidx × Expr) -> Elemmode
 | DECLARE : Elemmode
  deriving Inhabited, BEq

inductive Datamode where
 | MEMORY : (Memidx × Expr) -> Datamode
  deriving Inhabited, BEq

@[reducible] def Func := /- mixop: FUNC -/ (Functype × (List Valtype) × Expr)

@[reducible] def Global := /- mixop: GLOBAL -/ (Globaltype × Expr)

@[reducible] def Table := /- mixop: TABLE -/ Tabletype

@[reducible] def Mem := /- mixop: MEMORY -/ Memtype

@[reducible] def Elem := /- mixop: ELEM -/ (Reftype × (List Expr) × (Option Elemmode))

@[reducible] def Data := /- mixop: DATA -/ ((List (List Byte)) × (Option Datamode))

@[reducible] def Start := /- mixop: START -/ Funcidx

inductive Externuse where
 | FUNC : Funcidx -> Externuse
 | GLOBAL : Globalidx -> Externuse
 | TABLE : Tableidx -> Externuse
 | MEMORY : Memidx -> Externuse
  deriving Inhabited, BEq

@[reducible] def Export := /- mixop: EXPORT -/ (Name × Externuse)

@[reducible] def Import := /- mixop: IMPORT -/ (Name × Name × Externtype)

@[reducible] def Module := /- mixop: MODULE -/ ((List Import) × (List Func) × (List Global) × (List Table) × (List Mem) × (List Elem) × (List Data) × (List Start) × (List Export))

def size : Valtype -> Nat
  | (Valtype.Vectype Vectype.V128) => 128
  | (Valtype.Numtype Numtype.F64) => 64
  | (Valtype.Numtype Numtype.F32) => 32
  | (Valtype.Numtype Numtype.I64) => 64
  | (Valtype.Numtype Numtype.I32) => 32
  | _ => default

def test_sub_ATOM_22 : N -> Nat
  | n_3_ATOM_y => 0

def curried_ : (N × N) -> Nat
  | (n_1, n_2) => (n_1 + n_2)

inductive Testfuse where
 | AB_ : (Nat × Nat × Nat) -> Testfuse
 | CD : (Nat × Nat × Nat) -> Testfuse
 | EF : (Nat × Nat × Nat) -> Testfuse
 | GH : (Nat × Nat × Nat) -> Testfuse
 | IJ : (Nat × Nat × Nat) -> Testfuse
 | KL : (Nat × Nat × Nat) -> Testfuse
 | MN : (Nat × Nat × Nat) -> Testfuse
 | OP : (Nat × Nat × Nat) -> Testfuse
 | QR : (Nat × Nat × Nat) -> Testfuse
  deriving Inhabited, BEq

structure Context where
  FUNC : (List Functype)
  GLOBAL : (List Globaltype)
  TABLE : (List Tabletype)
  MEM : (List Memtype)
  ELEM : (List Elemtype)
  DATA : (List Datatype)
  LOCAL : (List Valtype)
  LABEL : (List Resulttype)
  RETURN : (Option Resulttype)
  deriving Inhabited, BEq
instance : Append Context where
  append := fun r1 r2 => {
    FUNC := r1.FUNC ++ r2.FUNC,
    GLOBAL := r1.GLOBAL ++ r2.GLOBAL,
    TABLE := r1.TABLE ++ r2.TABLE,
    MEM := r1.MEM ++ r2.MEM,
    ELEM := r1.ELEM ++ r2.ELEM,
    DATA := r1.DATA ++ r2.DATA,
    LOCAL := r1.LOCAL ++ r2.LOCAL,
    LABEL := r1.LABEL ++ r2.LABEL,
    RETURN := r1.RETURN ++ r2.RETURN,
  }

inductive Limits_ok : (Limits × Nat) -> Prop where
  | rule_0 (k : Nat) (n_1 : N) (n_2 : N) :
    ((n_1 <= n_2) && (n_2 <= k)) ->
    (Limits_ok ((n_1, n_2), k))

inductive Functype_ok : Functype -> Prop where
  | rule_0 (ft : Functype) :
    (Functype_ok ft)

inductive Globaltype_ok : Globaltype -> Prop where
  | rule_0 (gt : Globaltype) :
    (Globaltype_ok gt)

inductive Tabletype_ok : Tabletype -> Prop where
  | rule_0 (lim : Limits) (rt : Reftype) :
    (Limits_ok (lim, ((((Nat.pow 2) 32)) - 1))) ->
    (Tabletype_ok (lim, rt))

inductive Memtype_ok : Memtype -> Prop where
  | rule_0 (lim : Limits) :
    (Limits_ok (lim, (((Nat.pow 2) 16)))) ->
    (Memtype_ok lim)

inductive Externtype_ok : Externtype -> Prop where
  | mem (memtype : Memtype) :
    (Memtype_ok memtype) ->
    (Externtype_ok (Externtype.MEMORY memtype))
  | table (tabletype : Tabletype) :
    (Tabletype_ok tabletype) ->
    (Externtype_ok (Externtype.TABLE tabletype))
  | «global» (globaltype : Globaltype) :
    (Globaltype_ok globaltype) ->
    (Externtype_ok (Externtype.GLOBAL globaltype))
  | func (functype : Functype) :
    (Functype_ok functype) ->
    (Externtype_ok (Externtype.FUNC functype))

inductive Valtype_sub : (Valtype × Valtype) -> Prop where
  | bot (t : Valtype) :
    (Valtype_sub (Valtype.BOT, t))
  | refl (t : Valtype) :
    (Valtype_sub (t, t))

inductive Resulttype_sub : ((List Valtype) × (List Valtype)) -> Prop where
  | rule_0 (t_1 : (List Valtype)) (t_2 : (List Valtype)) :
    (Valtype_sub (t_1, t_2)) /- * -/ ->
    (Resulttype_sub (t_1, t_2))

inductive Limits_sub : (Limits × Limits) -> Prop where
  | rule_0 (n_11 : N) (n_12 : N) (n_21 : N) (n_22 : N) :
    (n_11 >= n_21) ->
    (n_12 <= n_22) ->
    (Limits_sub ((n_11, n_12), (n_21, n_22)))

inductive Functype_sub : (Functype × Functype) -> Prop where
  | rule_0 (ft : Functype) :
    (Functype_sub (ft, ft))

inductive Globaltype_sub : (Globaltype × Globaltype) -> Prop where
  | rule_0 (gt : Globaltype) :
    (Globaltype_sub (gt, gt))

inductive Tabletype_sub : (Tabletype × Tabletype) -> Prop where
  | rule_0 (lim_1 : Limits) (lim_2 : Limits) (rt : Reftype) :
    (Limits_sub (lim_1, lim_2)) ->
    (Tabletype_sub ((lim_1, rt), (lim_2, rt)))

inductive Memtype_sub : (Memtype × Memtype) -> Prop where
  | rule_0 (lim_1 : Limits) (lim_2 : Limits) :
    (Limits_sub (lim_1, lim_2)) ->
    (Memtype_sub (lim_1, lim_2))

inductive Externtype_sub : (Externtype × Externtype) -> Prop where
  | mem (mt_1 : Memtype) (mt_2 : Memtype) :
    (Memtype_sub (mt_1, mt_2)) ->
    (Externtype_sub ((Externtype.MEMORY mt_1), (Externtype.MEMORY mt_2)))
  | table (tt_1 : Tabletype) (tt_2 : Tabletype) :
    (Tabletype_sub (tt_1, tt_2)) ->
    (Externtype_sub ((Externtype.TABLE tt_1), (Externtype.TABLE tt_2)))
  | «global» (gt_1 : Globaltype) (gt_2 : Globaltype) :
    (Globaltype_sub (gt_1, gt_2)) ->
    (Externtype_sub ((Externtype.GLOBAL gt_1), (Externtype.GLOBAL gt_2)))
  | func (ft_1 : Functype) (ft_2 : Functype) :
    (Functype_sub (ft_1, ft_2)) ->
    (Externtype_sub ((Externtype.FUNC ft_1), (Externtype.FUNC ft_2)))

inductive Blocktype_ok : (Context × Blocktype × Functype) -> Prop where
  | rule_0 (C : Context) (ft : Functype) :
    (Functype_ok ft) ->
    (Blocktype_ok (C, ft, ft))

mutual
inductive Instr_ok : (Context × Instr × Functype) -> Prop where
  | store (C : Context) («in» : In) (mt : Memtype) (n : (Option N)) (n_A : N) (n_O : N) (nt : Numtype) (t : Valtype) :
    ((C.MEM.get! 0) == mt) ->
    ((((Nat.pow 2) n_A)) <= (((Nat.div (size t)) 8))) ->
    (((((Nat.pow 2) n_A)) <= (((Nat.div n) 8))) && ((((Nat.div n) 8)) < (((Nat.div (size t)) 8)))) ->
    ((n == none) || (nt == (Numtype.In «in»))) ->
    (Instr_ok (C, (Instr.STORE (nt, n, n_A, n_O)), ([(Valtype.Numtype Numtype.I32), (Valtype.Numtype nt)], [])))
  | load (C : Context) («in» : In) (mt : Memtype) (n : (Option N)) (n_A : N) (n_O : N) (nt : Numtype) (sx : (Option Sx)) (t : Valtype) :
    ((C.MEM.get! 0) == mt) ->
    ((((Nat.pow 2) n_A)) <= (((Nat.div (size t)) 8))) ->
    (((((Nat.pow 2) n_A)) <= (((Nat.div n) 8))) && ((((Nat.div n) 8)) < (((Nat.div (size t)) 8)))) ->
    ((n == none) || (nt == (Numtype.In «in»))) ->
    (Instr_ok (C, (Instr.LOAD (nt, (n, sx) /- ? -/, n_A, n_O)), ([(Valtype.Numtype Numtype.I32)], [(Valtype.Numtype nt)])))
  | data_drop (C : Context) (x : Idx) :
    ((C.DATA.get! x) == ()) ->
    (Instr_ok (C, (Instr.DATA_DROP x), ([], [])))
  | memory_init (C : Context) (mt : Memtype) (x : Idx) :
    ((C.MEM.get! 0) == mt) ->
    ((C.DATA.get! x) == ()) ->
    (Instr_ok (C, (Instr.MEMORY_INIT x), ([(Valtype.Numtype Numtype.I32), (Valtype.Numtype Numtype.I32), (Valtype.Numtype Numtype.I32)], [(Valtype.Numtype Numtype.I32)])))
  | memory_copy (C : Context) (mt : Memtype) :
    ((C.MEM.get! 0) == mt) ->
    (Instr_ok (C, Instr.MEMORY_COPY, ([(Valtype.Numtype Numtype.I32), (Valtype.Numtype Numtype.I32), (Valtype.Numtype Numtype.I32)], [(Valtype.Numtype Numtype.I32)])))
  | memory_fill (C : Context) (mt : Memtype) :
    ((C.MEM.get! 0) == mt) ->
    (Instr_ok (C, Instr.MEMORY_FILL, ([(Valtype.Numtype Numtype.I32), (Valtype.Numtype Numtype.I32), (Valtype.Numtype Numtype.I32)], [(Valtype.Numtype Numtype.I32)])))
  | memory_grow (C : Context) (mt : Memtype) :
    ((C.MEM.get! 0) == mt) ->
    (Instr_ok (C, Instr.MEMORY_GROW, ([(Valtype.Numtype Numtype.I32)], [(Valtype.Numtype Numtype.I32)])))
  | memory_size (C : Context) (mt : Memtype) :
    ((C.MEM.get! 0) == mt) ->
    (Instr_ok (C, Instr.MEMORY_SIZE, ([], [(Valtype.Numtype Numtype.I32)])))
  | elem_drop (C : Context) (rt : Reftype) (x : Idx) :
    ((C.ELEM.get! x) == rt) ->
    (Instr_ok (C, (Instr.ELEM_DROP x), ([], [])))
  | table_init (C : Context) (lim : Limits) (rt : Reftype) (x_1 : Idx) (x_2 : Idx) :
    ((C.TABLE.get! x_1) == (lim, rt)) ->
    ((C.ELEM.get! x_2) == rt) ->
    (Instr_ok (C, (Instr.TABLE_INIT (x_1, x_2)), ([(Valtype.Numtype Numtype.I32), (Valtype.Numtype Numtype.I32), (Valtype.Numtype Numtype.I32)], [])))
  | table_copy (C : Context) (lim_1 : Limits) (lim_2 : Limits) (rt : Reftype) (x_1 : Idx) (x_2 : Idx) :
    ((C.TABLE.get! x_1) == (lim_1, rt)) ->
    ((C.TABLE.get! x_2) == (lim_2, rt)) ->
    (Instr_ok (C, (Instr.TABLE_COPY (x_1, x_2)), ([(Valtype.Numtype Numtype.I32), (Valtype.Numtype Numtype.I32), (Valtype.Numtype Numtype.I32)], [])))
  | table_fill (C : Context) (lim : Limits) (rt : Reftype) (x : Idx) :
    ((C.TABLE.get! x) == (lim, rt)) ->
    (Instr_ok (C, (Instr.TABLE_FILL x), ([(Valtype.Numtype Numtype.I32), (Valtype.Reftype rt), (Valtype.Numtype Numtype.I32)], [])))
  | table_grow (C : Context) (lim : Limits) (rt : Reftype) (x : Idx) :
    ((C.TABLE.get! x) == (lim, rt)) ->
    (Instr_ok (C, (Instr.TABLE_GROW x), ([(Valtype.Reftype rt), (Valtype.Numtype Numtype.I32)], [(Valtype.Numtype Numtype.I32)])))
  | table_size (C : Context) (tt : Tabletype) (x : Idx) :
    ((C.TABLE.get! x) == tt) ->
    (Instr_ok (C, (Instr.TABLE_SIZE x), ([], [(Valtype.Numtype Numtype.I32)])))
  | table_set (C : Context) (lim : Limits) (rt : Reftype) (x : Idx) :
    ((C.TABLE.get! x) == (lim, rt)) ->
    (Instr_ok (C, (Instr.TABLE_SET x), ([(Valtype.Numtype Numtype.I32), (Valtype.Reftype rt)], [])))
  | table_get (C : Context) (lim : Limits) (rt : Reftype) (x : Idx) :
    ((C.TABLE.get! x) == (lim, rt)) ->
    (Instr_ok (C, (Instr.TABLE_GET x), ([(Valtype.Numtype Numtype.I32)], [(Valtype.Reftype rt)])))
  | global_set (C : Context) (t : Valtype) (x : Idx) :
    ((C.GLOBAL.get! x) == ((some ()), t)) ->
    (Instr_ok (C, (Instr.GLOBAL_SET x), ([t], [])))
  | global_get (C : Context) (t : Valtype) (x : Idx) :
    ((C.GLOBAL.get! x) == (() /- ? -/, t)) ->
    (Instr_ok (C, (Instr.GLOBAL_GET x), ([], [t])))
  | local_tee (C : Context) (t : Valtype) (x : Idx) :
    ((C.LOCAL.get! x) == t) ->
    (Instr_ok (C, (Instr.LOCAL_TEE x), ([t], [t])))
  | local_set (C : Context) (t : Valtype) (x : Idx) :
    ((C.LOCAL.get! x) == t) ->
    (Instr_ok (C, (Instr.LOCAL_SET x), ([t], [])))
  | local_get (C : Context) (t : Valtype) (x : Idx) :
    ((C.LOCAL.get! x) == t) ->
    (Instr_ok (C, (Instr.LOCAL_GET x), ([], [t])))
  | ref_is_null (C : Context) (rt : Reftype) :
    (Instr_ok (C, Instr.REF_IS_NULL, ([(Valtype.Reftype rt)], [(Valtype.Numtype Numtype.I32)])))
  | ref_func (C : Context) (ft : Functype) (x : Idx) :
    ((C.FUNC.get! x) == ft) ->
    (Instr_ok (C, (Instr.REF_FUNC x), ([], [(Valtype.Reftype Reftype.FUNCREF)])))
  | ref_null (C : Context) (rt : Reftype) :
    (Instr_ok (C, (Instr.REF_NULL rt), ([], [(Valtype.Reftype rt)])))
  | convert_f (C : Context) (fn_1 : Fn) (fn_2 : Fn) :
    (fn_1 != fn_2) ->
    (Instr_ok (C, (Instr.CVTOP ((Numtype.Fn fn_1), Cvtop.CONVERT, (Numtype.Fn fn_2), none)), ([(Valtype.Fn fn_2)], [(Valtype.Fn fn_1)])))
  | convert_i (C : Context) (in_1 : In) (in_2 : In) (sx : (Option Sx)) :
    (in_1 != in_2) ->
    ((sx == none) = ((size (Valtype.In in_1)) > (size (Valtype.In in_2)))) ->
    (Instr_ok (C, (Instr.CVTOP ((Numtype.In in_1), Cvtop.CONVERT, (Numtype.In in_2), sx)), ([(Valtype.In in_2)], [(Valtype.In in_1)])))
  | reinterpret (C : Context) (nt_1 : Numtype) (nt_2 : Numtype) :
    (nt_1 != nt_2) ->
    ((size (Valtype.Numtype nt_1)) == (size (Valtype.Numtype nt_2))) ->
    (Instr_ok (C, (Instr.CVTOP (nt_1, Cvtop.REINTERPRET, nt_2, none)), ([(Valtype.Numtype nt_2)], [(Valtype.Numtype nt_1)])))
  | extend (C : Context) (n : N) (nt : Numtype) :
    (n <= (size (Valtype.Numtype nt))) ->
    (Instr_ok (C, (Instr.EXTEND (nt, n)), ([(Valtype.Numtype nt)], [(Valtype.Numtype nt)])))
  | relop (C : Context) (nt : Numtype) (relop : Relop_numtype) :
    (Instr_ok (C, (Instr.RELOP (nt, relop)), ([(Valtype.Numtype nt), (Valtype.Numtype nt)], [(Valtype.Numtype Numtype.I32)])))
  | testop (C : Context) (nt : Numtype) (testop : Testop_numtype) :
    (Instr_ok (C, (Instr.TESTOP (nt, testop)), ([(Valtype.Numtype nt)], [(Valtype.Numtype Numtype.I32)])))
  | binop (C : Context) (binop : Binop_numtype) (nt : Numtype) :
    (Instr_ok (C, (Instr.BINOP (nt, binop)), ([(Valtype.Numtype nt), (Valtype.Numtype nt)], [(Valtype.Numtype nt)])))
  | unop (C : Context) (nt : Numtype) (unop : Unop_numtype) :
    (Instr_ok (C, (Instr.UNOP (nt, unop)), ([(Valtype.Numtype nt)], [(Valtype.Numtype nt)])))
  | const (C : Context) (c_nt : C_numtype) (nt : Numtype) :
    (Instr_ok (C, (Instr.CONST (nt, c_nt)), ([], [(Valtype.Numtype nt)])))
  | call_indirect (C : Context) (ft : Functype) (lim : Limits) (t_1 : (List Valtype)) (t_2 : (List Valtype)) (x : Idx) :
    ((C.TABLE.get! x) == (lim, Reftype.FUNCREF)) ->
    (ft == (t_1, t_2)) ->
    (Instr_ok (C, (Instr.CALL_INDIRECT (x, ft)), ((t_1 ++ [(Valtype.Numtype Numtype.I32)]), t_2)))
  | call (C : Context) (t_1 : (List Valtype)) (t_2 : (List Valtype)) (x : Idx) :
    ((C.FUNC.get! x) == (t_1, t_2)) ->
    (Instr_ok (C, (Instr.CALL x), (t_1, t_2)))
  | return (C : Context) (t : (List Valtype)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) :
    (C.RETURN == (some t)) ->
    (Instr_ok (C, Instr.RETURN, ((t_1 ++ t), t_2)))
  | br_table (C : Context) (l : (List Labelidx)) (l' : Labelidx) (t : (List Valtype)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) :
    (Resulttype_sub (t, (C.LABEL.get! l))) /- * -/ ->
    (Resulttype_sub (t, (C.LABEL.get! l'))) ->
    (Instr_ok (C, (Instr.BR_TABLE (l, l')), ((t_1 ++ t), t_2)))
  | br_if (C : Context) (l : Labelidx) (t : (List Valtype)) :
    ((C.LABEL.get! l) == t) ->
    (Instr_ok (C, (Instr.BR_IF l), ((t ++ [(Valtype.Numtype Numtype.I32)]), t)))
  | br (C : Context) (l : Labelidx) (t : (List Valtype)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) :
    ((C.LABEL.get! l) == t) ->
    (Instr_ok (C, (Instr.BR l), ((t_1 ++ t), t_2)))
  | if (C : Context) (bt : Blocktype) (instr_1 : (List Instr)) (instr_2 : (List Instr)) (t_1 : (List Valtype)) (t_2 : Valtype) :
    (Blocktype_ok (C, bt, (t_1, [t_2]))) ->
    (InstrSeq_ok ((C ++ {FUNC := [], GLOBAL := [], TABLE := [], MEM := [], ELEM := [], DATA := [], LOCAL := [], LABEL := [t_2] /- * -/, RETURN := none}), instr_1, (t_1, t_2))) ->
    (InstrSeq_ok ((C ++ {FUNC := [], GLOBAL := [], TABLE := [], MEM := [], ELEM := [], DATA := [], LOCAL := [], LABEL := [t_2] /- * -/, RETURN := none}), instr_2, (t_1, t_2))) ->
    (Instr_ok (C, (Instr.IF (bt, instr_1, instr_2)), (t_1, [t_2])))
  | loop (C : Context) (bt : Blocktype) (instr : (List Instr)) (t_1 : (List Valtype)) (t_2 : Valtype) :
    (Blocktype_ok (C, bt, (t_1, t_2))) ->
    (InstrSeq_ok ((C ++ {FUNC := [], GLOBAL := [], TABLE := [], MEM := [], ELEM := [], DATA := [], LOCAL := [], LABEL := [t_1] /- * -/, RETURN := none}), instr, (t_1, [t_2]))) ->
    (Instr_ok (C, (Instr.LOOP (bt, instr)), (t_1, t_2)))
  | block (C : Context) (bt : Blocktype) (instr : (List Instr)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) :
    (Blocktype_ok (C, bt, (t_1, t_2))) ->
    (InstrSeq_ok ((C ++ {FUNC := [], GLOBAL := [], TABLE := [], MEM := [], ELEM := [], DATA := [], LOCAL := [], LABEL := [t_2] /- * -/, RETURN := none}), instr, (t_1, t_2))) ->
    (Instr_ok (C, (Instr.BLOCK (bt, instr)), (t_1, t_2)))
  | select_impl (C : Context) (numtype : Numtype) (t : Valtype) (t' : Valtype) (vectype : Vectype) :
    (Valtype_sub (t, t')) ->
    ((t' == (Valtype.Numtype numtype)) || (t' == (Valtype.Vectype vectype))) ->
    (Instr_ok (C, (Instr.SELECT none), ([t, t, (Valtype.Numtype Numtype.I32)], [t])))
  | select_expl (C : Context) (t : Valtype) :
    (Instr_ok (C, (Instr.SELECT (some t)), ([t, t, (Valtype.Numtype Numtype.I32)], [t])))
  | drop (C : Context) (t : Valtype) :
    (Instr_ok (C, Instr.DROP, ([t], [])))
  | nop (C : Context) :
    (Instr_ok (C, Instr.NOP, ([], [])))
  | unreachable (C : Context) (t_1 : (List Valtype)) (t_2 : (List Valtype)) :
    (Instr_ok (C, Instr.UNREACHABLE, (t_1, t_2)))
inductive InstrSeq_ok : (Context × (List Instr) × Functype) -> Prop where
  | frame (C : Context) (instr : (List Instr)) (t : (List Valtype)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) :
    (InstrSeq_ok (C, instr, (t_1, t_2))) ->
    (InstrSeq_ok (C, instr, ((t ++ t_1), (t ++ t_2))))
  | weak (C : Context) (instr : (List Instr)) (t'_1 : Valtype) (t'_2 : (List Valtype)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) :
    (InstrSeq_ok (C, instr, (t_1, t_2))) ->
    (Resulttype_sub (t'_1, t_1)) ->
    (Resulttype_sub (t_2, t'_2)) ->
    (InstrSeq_ok (C, instr, ([t'_1], t'_2)))
  | seq (C : Context) (instr_1 : Instr) (instr_2 : Instr) (t_1 : (List Valtype)) (t_2 : (List Valtype)) (t_3 : (List Valtype)) :
    (Instr_ok (C, instr_1, (t_1, t_2))) ->
    (InstrSeq_ok (C, [instr_2], (t_2, t_3))) ->
    (InstrSeq_ok (C, ([instr_1] ++ instr_2), (t_1, t_3)))
  | empty (C : Context) :
    (InstrSeq_ok (C, [], ([], [])))end


inductive Expr_ok : (Context × Expr × Resulttype) -> Prop where
  | rule_0 (C : Context) (instr : (List Instr)) (t : (List Valtype)) :
    (InstrSeq_ok (C, instr, ([], t))) ->
    (Expr_ok (C, instr, t))

inductive Instr_const : (Context × Instr) -> Prop where
  | global_get (C : Context) (t : Valtype) (x : Idx) :
    ((C.GLOBAL.get! x) == (none, t)) ->
    (Instr_const (C, (Instr.GLOBAL_GET x)))
  | ref_func (C : Context) (x : Idx) :
    (Instr_const (C, (Instr.REF_FUNC x)))
  | ref_null (C : Context) (rt : Reftype) :
    (Instr_const (C, (Instr.REF_NULL rt)))
  | const (C : Context) (c : C_numtype) (nt : Numtype) :
    (Instr_const (C, (Instr.CONST (nt, c))))

inductive Expr_const : (Context × Expr) -> Prop where
  | rule_0 (C : Context) (instr : (List Instr)) :
    (Instr_const (C, instr)) /- * -/ ->
    (Expr_const (C, instr))

inductive Expr_ok_const : (Context × Expr × Valtype) -> Prop where
  | rule_0 (C : Context) (expr : Expr) (t : Valtype) :
    (Expr_ok (C, expr, [t])) ->
    (Expr_const (C, expr)) ->
    (Expr_ok_const (C, expr, t))

inductive Func_ok : (Context × Func × Functype) -> Prop where
  | rule_0 (C : Context) (expr : Expr) (ft : Functype) (t : (List Valtype)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) :
    (ft == (t_1, t_2)) ->
    (Functype_ok ft) ->
    (Expr_ok ((((C ++ {FUNC := [], GLOBAL := [], TABLE := [], MEM := [], ELEM := [], DATA := [], LOCAL := (t_1 ++ t), LABEL := [], RETURN := none}) ++ {FUNC := [], GLOBAL := [], TABLE := [], MEM := [], ELEM := [], DATA := [], LOCAL := [], LABEL := [t_2], RETURN := none}) ++ {FUNC := [], GLOBAL := [], TABLE := [], MEM := [], ELEM := [], DATA := [], LOCAL := [], LABEL := [], RETURN := (some t_2)}), expr, t_2)) ->
    (Func_ok (C, (ft, t, expr), ft))

inductive Global_ok : (Context × Global × Globaltype) -> Prop where
  | rule_0 (C : Context) (expr : Expr) (gt : Globaltype) (t : Valtype) :
    (Globaltype_ok gt) ->
    (gt == (() /- ? -/, t)) ->
    (Expr_ok_const (C, expr, t)) ->
    (Global_ok (C, (gt, expr), gt))

inductive Table_ok : (Context × Table × Tabletype) -> Prop where
  | rule_0 (C : Context) (tt : Tabletype) :
    (Tabletype_ok tt) ->
    (Table_ok (C, tt, tt))

inductive Mem_ok : (Context × Mem × Memtype) -> Prop where
  | rule_0 (C : Context) (mt : Memtype) :
    (Memtype_ok mt) ->
    (Mem_ok (C, mt, mt))

inductive Elemmode_ok : (Context × Elemmode × Reftype) -> Prop where
  | declare (C : Context) (rt : Reftype) :
    (Elemmode_ok (C, Elemmode.DECLARE, rt))
  | active (C : Context) (expr : Expr) (lim : Limits) (rt : Reftype) (x : Idx) :
    ((C.TABLE.get! x) == (lim, rt)) ->
    (Expr_ok_const (C, expr, (Valtype.Numtype Numtype.I32))) /- * -/ ->
    (Elemmode_ok (C, (Elemmode.TABLE (x, expr)), rt))

inductive Elem_ok : (Context × Elem × Reftype) -> Prop where
  | rule_0 (C : Context) (elemmode : (Option Elemmode)) (expr : (List Expr)) (rt : Reftype) :
    (Expr_ok (C, expr, [(Valtype.Reftype rt)])) /- * -/ ->
    (Elemmode_ok (C, elemmode, rt)) /- ? -/ ->
    (Elem_ok (C, (rt, expr, elemmode), rt))

inductive Datamode_ok : (Context × Datamode) -> Prop where
  | rule_0 (C : Context) (expr : Expr) (mt : Memtype) :
    ((C.MEM.get! 0) == mt) ->
    (Expr_ok_const (C, expr, (Valtype.Numtype Numtype.I32))) /- * -/ ->
    (Datamode_ok (C, (Datamode.MEMORY (0, expr))))

inductive Data_ok : (Context × Data) -> Prop where
  | rule_0 (C : Context) (b : (List (List Byte))) (datamode : (Option Datamode)) :
    (Datamode_ok (C, datamode)) /- ? -/ ->
    (Data_ok (C, (b /- * -/, datamode)))

inductive Start_ok : (Context × Start) -> Prop where
  | rule_0 (C : Context) (x : Idx) :
    ((C.FUNC.get! x) == ([], [])) ->
    (Start_ok (C, x))

inductive Import_ok : (Context × Import × Externtype) -> Prop where
  | rule_0 (C : Context) (name_1 : Name) (name_2 : Name) (xt : Externtype) :
    (Externtype_ok xt) ->
    (Import_ok (C, (name_1, name_2, xt), xt))

inductive Externuse_ok : (Context × Externuse × Externtype) -> Prop where
  | mem (C : Context) (mt : Memtype) (x : Idx) :
    ((C.MEM.get! x) == mt) ->
    (Externuse_ok (C, (Externuse.MEMORY x), (Externtype.MEMORY mt)))
  | table (C : Context) (tt : Tabletype) (x : Idx) :
    ((C.TABLE.get! x) == tt) ->
    (Externuse_ok (C, (Externuse.TABLE x), (Externtype.TABLE tt)))
  | «global» (C : Context) (gt : Globaltype) (x : Idx) :
    ((C.GLOBAL.get! x) == gt) ->
    (Externuse_ok (C, (Externuse.GLOBAL x), (Externtype.GLOBAL gt)))
  | func (C : Context) (ft : Functype) (x : Idx) :
    ((C.FUNC.get! x) == ft) ->
    (Externuse_ok (C, (Externuse.FUNC x), (Externtype.FUNC ft)))

inductive Export_ok : (Context × Export × Externtype) -> Prop where
  | rule_0 (C : Context) (externuse : Externuse) (name : Name) (xt : Externtype) :
    (Externuse_ok (C, externuse, xt)) ->
    (Export_ok (C, (name, externuse), xt))

inductive Module_ok : Module -> Prop where
  | rule_0 (C : Context) (data : (List Data)) (elem : (List Elem)) («export» : (List Export)) (ft : (List Functype)) (func : (List Func)) («global» : (List Global)) (gt : (List Globaltype)) («import» : (List Import)) (mem : (List Mem)) (mt : (List Memtype)) (n : N) (rt : (List Reftype)) (start : (List Start)) (table : (List Table)) (tt : (List Tabletype)) :
    (Func_ok (C, func, ft)) /- * -/ ->
    (Global_ok (C, «global», gt)) /- * -/ ->
    (Table_ok (C, table, tt)) /- * -/ ->
    (Mem_ok (C, mem, mt)) /- * -/ ->
    (Elem_ok (C, elem, rt)) /- * -/ ->
    (Data_ok (C, data)) /- ^n -/ ->
    (Start_ok (C, start)) /- * -/ ->
    (C == {FUNC := ft, GLOBAL := gt, TABLE := tt, MEM := mt, ELEM := rt, DATA := () /- ^n -/, LOCAL := [], LABEL := [], RETURN := none}) ->
    (mem.length <= 1) ->
    (start.length <= 1) ->
    (Module_ok («import», func, «global», table, mem, elem, data, start, «export»))

@[reducible] def Addr := Nat

@[reducible] def Funcaddr := Addr

@[reducible] def Globaladdr := Addr

@[reducible] def Tableaddr := Addr

@[reducible] def Memaddr := Addr

@[reducible] def Elemaddr := Addr

@[reducible] def Dataaddr := Addr

@[reducible] def Labeladdr := Addr

@[reducible] def Hostaddr := Addr

inductive Num where
 | CONST : (Numtype × C_numtype) -> Num
  deriving Inhabited, BEq

inductive Ref where
 | REF_NULL : Reftype -> Ref
 | REF_FUNC_ADDR : Funcaddr -> Ref
 | REF_HOST_ADDR : Hostaddr -> Ref
  deriving Inhabited, BEq

inductive Val where
 | Num : Num -> Val
 | Ref : Ref -> Val
  deriving Inhabited, BEq

inductive Result where
 | _VALS : (List Val) -> Result
 | TRAP : Result
  deriving Inhabited, BEq

inductive Externval where
 | FUNC : Funcaddr -> Externval
 | GLOBAL : Globaladdr -> Externval
 | TABLE : Tableaddr -> Externval
 | MEM : Memaddr -> Externval
  deriving Inhabited, BEq

def default_ : Valtype -> Val
  | (Valtype.Reftype rt) => (Val.Ref (Ref.REF_NULL rt))
  | (Valtype.Numtype Numtype.F64) => (Val.Num (Num.CONST (Numtype.F64, 0)))
  | (Valtype.Numtype Numtype.F32) => (Val.Num (Num.CONST (Numtype.F32, 0)))
  | (Valtype.Numtype Numtype.I64) => (Val.Num (Num.CONST (Numtype.I64, 0)))
  | (Valtype.Numtype Numtype.I32) => (Val.Num (Num.CONST (Numtype.I32, 0)))
  | _ => default

@[reducible] def Exportinst := /- mixop: EXPORT -/ (Name × Externval)

structure Moduleinst where
  FUNC : (List Funcaddr)
  GLOBAL : (List Globaladdr)
  TABLE : (List Tableaddr)
  MEM : (List Memaddr)
  ELEM : (List Elemaddr)
  DATA : (List Dataaddr)
  EXPORT : (List Exportinst)
  deriving Inhabited, BEq
instance : Append Moduleinst where
  append := fun r1 r2 => {
    FUNC := r1.FUNC ++ r2.FUNC,
    GLOBAL := r1.GLOBAL ++ r2.GLOBAL,
    TABLE := r1.TABLE ++ r2.TABLE,
    MEM := r1.MEM ++ r2.MEM,
    ELEM := r1.ELEM ++ r2.ELEM,
    DATA := r1.DATA ++ r2.DATA,
    EXPORT := r1.EXPORT ++ r2.EXPORT,
  }

@[reducible] def Funcinst := /- mixop: `%;%` -/ (Moduleinst × Func)

@[reducible] def Globalinst := Val

@[reducible] def Tableinst := (List Ref)

@[reducible] def Meminst := (List Byte)

@[reducible] def Eleminst := (List Ref)

@[reducible] def Datainst := (List Byte)

structure Store where
  FUNC : (List Funcinst)
  GLOBAL : (List Globalinst)
  TABLE : (List Tableinst)
  MEM : (List Meminst)
  ELEM : (List Eleminst)
  DATA : (List Datainst)
  deriving Inhabited, BEq
instance : Append Store where
  append := fun r1 r2 => {
    FUNC := r1.FUNC ++ r2.FUNC,
    GLOBAL := r1.GLOBAL ++ r2.GLOBAL,
    TABLE := r1.TABLE ++ r2.TABLE,
    MEM := r1.MEM ++ r2.MEM,
    ELEM := r1.ELEM ++ r2.ELEM,
    DATA := r1.DATA ++ r2.DATA,
  }

structure Frame where
  LOCAL : (List Val)
  MODULE : Moduleinst
  deriving Inhabited, BEq
instance : Append Frame where
  append := fun r1 r2 => {
    LOCAL := r1.LOCAL ++ r2.LOCAL,
    MODULE := r1.MODULE ++ r2.MODULE,
  }

@[reducible] def State := /- mixop: `%;%` -/ (Store × Frame)

inductive Admininstr where
 | Instr : Instr -> Admininstr
 | REF_FUNC_ADDR : Funcaddr -> Admininstr
 | REF_HOST_ADDR : Hostaddr -> Admininstr
 | CALL_ADDR : Funcaddr -> Admininstr
 | LABEL_ : (N × (List Instr) × (List Admininstr)) -> Admininstr
 | FRAME_ : (N × Frame × (List Admininstr)) -> Admininstr
 | TRAP : Admininstr
  deriving Inhabited, BEq

@[reducible] def Config := /- mixop: `%;%` -/ (State × (List Admininstr))

def funcaddr : State -> (List Funcaddr)
  | (s, f) => f.MODULE.FUNC

def funcinst : State -> (List Funcinst)
  | (s, f) => s.FUNC

def func : (State × Funcidx) -> Funcinst
  | ((s, f), x) => (s.FUNC.get! (f.MODULE.FUNC.get! x))

def local : (State × Localidx) -> Val
  | ((s, f), x) => (f.LOCAL.get! x)

def global : (State × Globalidx) -> Globalinst
  | ((s, f), x) => (s.GLOBAL.get! (f.MODULE.GLOBAL.get! x))

def table : (State × Tableidx) -> Tableinst
  | ((s, f), x) => (s.TABLE.get! (f.MODULE.TABLE.get! x))

def elem : (State × Tableidx) -> Eleminst
  | ((s, f), x) => (s.ELEM.get! (f.MODULE.ELEM.get! x))

def with_local : (State × Localidx × Val) -> State
  | ((s, f), x, v) => (s, default /- f[LOCAL[x] = v] -/)

def with_global : (State × Globalidx × Val) -> State
  | ((s, f), x, v) => (default /- s[GLOBAL[f.MODULE_frame.GLOBAL_moduleinst[x]] = v] -/, f)

def with_table : (State × Tableidx × N × Ref) -> State
  | ((s, f), x, i, r) => (default /- s[TABLE[f.MODULE_frame.TABLE_moduleinst[x]][i] = r] -/, f)

inductive E where
 | _HOLE : E
 | _SEQ : ((List Val) × E × (List Instr)) -> E
 | LABEL_ : (N × (List Instr) × E) -> E
  deriving Inhabited, BEq

inductive Step_pure : ((List Admininstr) × (List Admininstr)) -> Prop where
  | br_table_ge (i : Nat) (l : (List Labelidx)) (l' : Labelidx) :
    (i >= l.length) ->
    (Step_pure ([(Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Instr (Instr.BR_TABLE (l, l')))], [(Admininstr.Instr (Instr.BR l'))]))
  | br_table_lt (i : Nat) (l : (List Labelidx)) (l' : Labelidx) :
    (i < l.length) ->
    (Step_pure ([(Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Instr (Instr.BR_TABLE (l, l')))], [(Admininstr.Instr (Instr.BR (l.get! i)))]))
  | br_if_false (c : C_numtype) (l : Labelidx) :
    (c == 0) ->
    (Step_pure ([(Admininstr.Instr (Instr.CONST (Numtype.I32, c))), (Admininstr.Instr (Instr.BR_IF l))], []))
  | br_if_true (c : C_numtype) (l : Labelidx) :
    (c != 0) ->
    (Step_pure ([(Admininstr.Instr (Instr.CONST (Numtype.I32, c))), (Admininstr.Instr (Instr.BR_IF l))], [(Admininstr.Instr (Instr.BR l))]))
  | br_succ (instr : (List Instr)) (instr' : (List Instr)) (l : Labelidx) (n : N) (val : (List Val)) :
    (Step_pure ([(Admininstr.LABEL_ (n, instr', ((Admininstr.Val val) /- * -/ ++ ([(Admininstr.Instr (Instr.BR (l + 1)))] ++ (Admininstr.Instr instr) /- * -/))))], ((Admininstr.Val val) /- * -/ ++ [(Admininstr.Instr (Instr.BR l))])))
  | br_zero (instr : (List Instr)) (instr' : (List Instr)) (n : N) (val : (List Val)) (val' : (List Val)) :
    (Step_pure ([(Admininstr.LABEL_ (n, instr', ((Admininstr.Val val') /- * -/ ++ ((Admininstr.Val val) /- ^n -/ ++ ([(Admininstr.Instr (Instr.BR 0))] ++ (Admininstr.Instr instr) /- * -/)))))], ((Admininstr.Val val) /- ^n -/ ++ (Admininstr.Instr instr') /- * -/)))
  | if_false (bt : Blocktype) (c : C_numtype) (instr_1 : (List Instr)) (instr_2 : (List Instr)) :
    (c == 0) ->
    (Step_pure ([(Admininstr.Instr (Instr.CONST (Numtype.I32, c))), (Admininstr.Instr (Instr.IF (bt, instr_1, instr_2)))], [(Admininstr.Instr (Instr.BLOCK (bt, instr_2)))]))
  | if_true (bt : Blocktype) (c : C_numtype) (instr_1 : (List Instr)) (instr_2 : (List Instr)) :
    (c != 0) ->
    (Step_pure ([(Admininstr.Instr (Instr.CONST (Numtype.I32, c))), (Admininstr.Instr (Instr.IF (bt, instr_1, instr_2)))], [(Admininstr.Instr (Instr.BLOCK (bt, instr_1)))]))
  | loop (bt : Blocktype) (instr : (List Instr)) (k : Nat) (n : N) (t_1 : (List Valtype)) (t_2 : (List Valtype)) (val : (List Val)) :
    (bt == (t_1, t_2)) ->
    (Step_pure (((Admininstr.Val val) /- ^k -/ ++ [(Admininstr.Instr (Instr.LOOP (bt, instr)))]), [(Admininstr.LABEL_ (n, [(Instr.LOOP (bt, instr))], ((Admininstr.Val val) /- ^k -/ ++ (Admininstr.Instr instr) /- * -/)))]))
  | block (bt : Blocktype) (instr : (List Instr)) (k : Nat) (n : N) (t_1 : (List Valtype)) (t_2 : (List Valtype)) (val : (List Val)) :
    (bt == (t_1, t_2)) ->
    (Step_pure (((Admininstr.Val val) /- ^k -/ ++ [(Admininstr.Instr (Instr.BLOCK (bt, instr)))]), [(Admininstr.LABEL_ (n, [], ((Admininstr.Val val) /- ^k -/ ++ (Admininstr.Instr instr) /- * -/)))]))
  | local_tee (val : Val) (x : Idx) :
    (Step_pure ([(Admininstr.Val val), (Admininstr.Instr (Instr.LOCAL_TEE x))], [(Admininstr.Val val), (Admininstr.Val val), (Admininstr.Instr (Instr.LOCAL_SET x))]))
  | select_false (c : C_numtype) (t : (Option Valtype)) (val_1 : Val) (val_2 : Val) :
    (c == 0) ->
    (Step_pure ([(Admininstr.Val val_1), (Admininstr.Val val_2), (Admininstr.Instr (Instr.CONST (Numtype.I32, c))), (Admininstr.Instr (Instr.SELECT t))], [(Admininstr.Val val_2)]))
  | select_true (c : C_numtype) (t : (Option Valtype)) (val_1 : Val) (val_2 : Val) :
    (c != 0) ->
    (Step_pure ([(Admininstr.Val val_1), (Admininstr.Val val_2), (Admininstr.Instr (Instr.CONST (Numtype.I32, c))), (Admininstr.Instr (Instr.SELECT t))], [(Admininstr.Val val_1)]))
  | drop (val : Val) :
    (Step_pure ([(Admininstr.Val val), (Admininstr.Instr Instr.DROP)], []))
  | nop  :
    (Step_pure ([(Admininstr.Instr Instr.NOP)], []))
  | unreachable  :
    (Step_pure ([(Admininstr.Instr Instr.UNREACHABLE)], [Admininstr.TRAP]))
  | ref_is_null_false (val : Val) :
    True /- Else? -/ ->
    (Step_pure ([(Admininstr.Val val), (Admininstr.Instr Instr.REF_IS_NULL)], [(Admininstr.Instr (Instr.CONST (Numtype.I32, 0)))]))
  | ref_is_null_true (rt : Reftype) (val : Val) :
    (val == (Val.Ref (Ref.REF_NULL rt))) ->
    (Step_pure ([(Admininstr.Val val), (Admininstr.Instr Instr.REF_IS_NULL)], [(Admininstr.Instr (Instr.CONST (Numtype.I32, 1)))]))

inductive Step_read : (Config × (List Admininstr)) -> Prop where
  | call_addr (a : Addr) (instr : (List Instr)) (k : Nat) (m : Moduleinst) (n : N) (t : (List Valtype)) (t_1 : (List Valtype)) (t_2 : (List Valtype)) (val : (List Val)) (z : State) :
    (((funcinst z).get! a) == (m, ((t_1, t_2), t, instr))) ->
    (Step_read ((z, ((Admininstr.Val val) /- ^k -/ ++ [(Admininstr.CALL_ADDR a)])), [(Admininstr.FRAME_ (n, {LOCAL := (val ++ (default_ t) /- * -/), MODULE := m}, [(Admininstr.LABEL_ (n, [], (Admininstr.Instr instr) /- * -/))]))]))
  | call_indirect_trap (ft : Functype) (i : Nat) (x : Idx) (z : State) :
    True /- Else? -/ ->
    (Step_read ((z, [(Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Instr (Instr.CALL_INDIRECT (x, ft)))]), [Admininstr.TRAP]))
  | call_indirect_call (a : Addr) (ft : Functype) (func : Func) (i : Nat) (m : Moduleinst) (x : Idx) (z : State) :
    (((table (z, x)).get! i) == (Ref.REF_FUNC_ADDR a)) ->
    (((funcinst z).get! a) == (m, func)) ->
    (Step_read ((z, [(Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Instr (Instr.CALL_INDIRECT (x, ft)))]), [(Admininstr.CALL_ADDR a)]))
  | call (x : Idx) (z : State) :
    (Step_read ((z, [(Admininstr.Instr (Instr.CALL x))]), [(Admininstr.CALL_ADDR ((funcaddr z).get! x))]))
  | table_init_le (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) :
    True /- Else? -/ ->
    (Step_read ((z, [(Admininstr.Instr (Instr.CONST (Numtype.I32, j))), (Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Instr (Instr.CONST (Numtype.I32, (n + 1)))), (Admininstr.Instr (Instr.TABLE_INIT (x, y)))]), [(Admininstr.Instr (Instr.CONST (Numtype.I32, j))), (Admininstr.Ref ((elem (z, y)).get! i)), (Admininstr.Instr (Instr.TABLE_SET x)), (Admininstr.Instr (Instr.CONST (Numtype.I32, (j + 1)))), (Admininstr.Instr (Instr.CONST (Numtype.I32, (i + 1)))), (Admininstr.Instr (Instr.CONST (Numtype.I32, n))), (Admininstr.Instr (Instr.TABLE_INIT (x, y)))]))
  | table_init_zero (i : Nat) (j : Nat) (x : Idx) (y : Idx) (z : State) :
    True /- Else? -/ ->
    (Step_read ((z, [(Admininstr.Instr (Instr.CONST (Numtype.I32, j))), (Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Instr (Instr.CONST (Numtype.I32, 0))), (Admininstr.Instr (Instr.TABLE_INIT (x, y)))]), []))
  | table_init_trap (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) :
    (((i + n) > (elem (z, y)).length) || ((j + n) > (table (z, x)).length)) ->
    (Step_read ((z, [(Admininstr.Instr (Instr.CONST (Numtype.I32, j))), (Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Instr (Instr.CONST (Numtype.I32, n))), (Admininstr.Instr (Instr.TABLE_INIT (x, y)))]), [Admininstr.TRAP]))
  | table_copy_gt (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) :
    (j > i) ->
    (Step_read ((z, [(Admininstr.Instr (Instr.CONST (Numtype.I32, j))), (Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Instr (Instr.CONST (Numtype.I32, (n + 1)))), (Admininstr.Instr (Instr.TABLE_COPY (x, y)))]), [(Admininstr.Instr (Instr.CONST (Numtype.I32, (j + n)))), (Admininstr.Instr (Instr.CONST (Numtype.I32, (i + n)))), (Admininstr.Instr (Instr.TABLE_GET y)), (Admininstr.Instr (Instr.TABLE_SET x)), (Admininstr.Instr (Instr.CONST (Numtype.I32, (j + 1)))), (Admininstr.Instr (Instr.CONST (Numtype.I32, (i + 1)))), (Admininstr.Instr (Instr.CONST (Numtype.I32, n))), (Admininstr.Instr (Instr.TABLE_COPY (x, y)))]))
  | table_copy_le (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) :
    (j <= i) ->
    (Step_read ((z, [(Admininstr.Instr (Instr.CONST (Numtype.I32, j))), (Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Instr (Instr.CONST (Numtype.I32, (n + 1)))), (Admininstr.Instr (Instr.TABLE_COPY (x, y)))]), [(Admininstr.Instr (Instr.CONST (Numtype.I32, j))), (Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Instr (Instr.TABLE_GET y)), (Admininstr.Instr (Instr.TABLE_SET x)), (Admininstr.Instr (Instr.CONST (Numtype.I32, (j + 1)))), (Admininstr.Instr (Instr.CONST (Numtype.I32, (i + 1)))), (Admininstr.Instr (Instr.CONST (Numtype.I32, n))), (Admininstr.Instr (Instr.TABLE_COPY (x, y)))]))
  | table_copy_zero (i : Nat) (j : Nat) (x : Idx) (y : Idx) (z : State) :
    True /- Else? -/ ->
    (Step_read ((z, [(Admininstr.Instr (Instr.CONST (Numtype.I32, j))), (Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Instr (Instr.CONST (Numtype.I32, 0))), (Admininstr.Instr (Instr.TABLE_COPY (x, y)))]), []))
  | table_copy_trap (i : Nat) (j : Nat) (n : N) (x : Idx) (y : Idx) (z : State) :
    (((i + n) > (table (z, y)).length) || ((j + n) > (table (z, x)).length)) ->
    (Step_read ((z, [(Admininstr.Instr (Instr.CONST (Numtype.I32, j))), (Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Instr (Instr.CONST (Numtype.I32, n))), (Admininstr.Instr (Instr.TABLE_COPY (x, y)))]), [Admininstr.TRAP]))
  | table_fill_succ (i : Nat) (n : N) (val : Val) (x : Idx) (z : State) :
    True /- Else? -/ ->
    (Step_read ((z, [(Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Val val), (Admininstr.Instr (Instr.CONST (Numtype.I32, (n + 1)))), (Admininstr.Instr (Instr.TABLE_FILL x))]), [(Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Val val), (Admininstr.Instr (Instr.TABLE_SET x)), (Admininstr.Instr (Instr.CONST (Numtype.I32, (i + 1)))), (Admininstr.Val val), (Admininstr.Instr (Instr.CONST (Numtype.I32, n))), (Admininstr.Instr (Instr.TABLE_FILL x))]))
  | table_fill_zero (i : Nat) (val : Val) (x : Idx) (z : State) :
    True /- Else? -/ ->
    (Step_read ((z, [(Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Val val), (Admininstr.Instr (Instr.CONST (Numtype.I32, 0))), (Admininstr.Instr (Instr.TABLE_FILL x))]), []))
  | table_fill_trap (i : Nat) (n : N) (val : Val) (x : Idx) (z : State) :
    ((i + n) > (table (z, x)).length) ->
    (Step_read ((z, [(Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Val val), (Admininstr.Instr (Instr.CONST (Numtype.I32, n))), (Admininstr.Instr (Instr.TABLE_FILL x))]), [Admininstr.TRAP]))
  | table_size (n : N) (x : Idx) (z : State) :
    ((table (z, x)).length == n) ->
    (Step_read ((z, [(Admininstr.Instr (Instr.TABLE_SIZE x))]), [(Admininstr.Instr (Instr.CONST (Numtype.I32, n)))]))
  | table_get_lt (i : Nat) (x : Idx) (z : State) :
    (i < (table (z, x)).length) ->
    (Step_read ((z, [(Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Instr (Instr.TABLE_GET x))]), [(Admininstr.Ref ((table (z, x)).get! i))]))
  | table_get_ge (i : Nat) (x : Idx) (z : State) :
    (i >= (table (z, x)).length) ->
    (Step_read ((z, [(Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Instr (Instr.TABLE_GET x))]), [Admininstr.TRAP]))
  | global_get (x : Idx) (z : State) :
    (Step_read ((z, [(Admininstr.Instr (Instr.GLOBAL_GET x))]), [(Admininstr.Globalinst («global» (z, x)))]))
  | local_get (x : Idx) (z : State) :
    (Step_read ((z, [(Admininstr.Instr (Instr.LOCAL_GET x))]), [(Admininstr.Val («local» (z, x)))]))
  | ref_func (x : Idx) (z : State) :
    (Step_read ((z, [(Admininstr.Instr (Instr.REF_FUNC x))]), [(Admininstr.REF_FUNC_ADDR ((funcaddr z).get! x))]))

inductive Step_write : (Config × Config) -> Prop where
  | table_set_ge (i : Nat) (ref : Ref) (x : Idx) (z : State) :
    (i >= (table (z, x)).length) ->
    (Step_write ((z, [(Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Ref ref), (Admininstr.Instr (Instr.TABLE_GET x))]), (z, [Admininstr.TRAP])))
  | table_set_lt (i : Nat) (ref : Ref) (x : Idx) (z : State) :
    (i < (table (z, x)).length) ->
    (Step_write ((z, [(Admininstr.Instr (Instr.CONST (Numtype.I32, i))), (Admininstr.Ref ref), (Admininstr.Instr (Instr.TABLE_GET x))]), ((with_table (z, x, i, ref)), [])))
  | global_set (val : Val) (x : Idx) (z : State) :
    (Step_write ((z, [(Admininstr.Val val), (Admininstr.Instr (Instr.GLOBAL_SET x))]), ((with_global (z, x, val)), [])))
  | local_set (val : Val) (x : Idx) (z : State) :
    (Step_write ((z, [(Admininstr.Val val), (Admininstr.Instr (Instr.LOCAL_SET x))]), ((with_local (z, x, val)), [])))

inductive Step : (Config × Config) -> Prop where
  | write (instr : (List Instr)) (instr' : (List Instr)) (z : State) (z' : State) :
    (Step_write ((z, (Admininstr.Instr instr) /- * -/), (z', (Admininstr.Instr instr') /- * -/))) ->
    (Step ((z, (Admininstr.Instr instr) /- * -/), (z', (Admininstr.Instr instr') /- * -/)))
  | read (instr : (List Instr)) (instr' : (List Instr)) (z : State) :
    (Step_read ((z, (Admininstr.Instr instr) /- * -/), (Admininstr.Instr instr') /- * -/)) ->
    (Step ((z, (Admininstr.Instr instr) /- * -/), (z, (Admininstr.Instr instr') /- * -/)))
  | pure (instr : (List Instr)) (instr' : (List Instr)) (z : State) :
    (Step_pure ((Admininstr.Instr instr) /- * -/, (Admininstr.Instr instr') /- * -/)) ->
    (Step ((z, (Admininstr.Instr instr) /- * -/), (z, (Admininstr.Instr instr') /- * -/)))
$ lean SpecTec.lean 2>&1 | sed -e 's,/[^ ]*/toolchains,.../toolchains`,g' | sed -e 's,SpecTec.lean:[0-9]\+:[0-9]\+,SpecTec.lean,'
SpecTec.lean: warning: unused variable `n_3_ATOM_y` [linter.unusedVariables]
SpecTec.lean: error: application type mismatch
  Prod.mk t_1
argument
  t_1
has type
  List Valtype : Type
but is expected to have type
  Valtype : Type
SpecTec.lean: error: application type mismatch
  Nat.div n
argument
  n
has type
  Option N : Type
but is expected to have type
  Nat : Type
SpecTec.lean: error: application type mismatch
  Nat.div n
argument
  n
has type
  Option N : Type
but is expected to have type
  Nat : Type
SpecTec.lean: error: unknown constant 'Numtype.In'
SpecTec.lean: error: application type mismatch
  Nat.div n
argument
  n
has type
  Option N : Type
but is expected to have type
  Nat : Type
SpecTec.lean: error: application type mismatch
  Nat.div n
argument
  n
has type
  Option N : Type
but is expected to have type
  Nat : Type
SpecTec.lean: error: unknown constant 'Numtype.In'
SpecTec.lean: error: application type mismatch
  Prod.mk (n, sx)
argument
  (n, sx)
has type
  Option N × Option Sx : Type
but is expected to have type
  Option (N × Sx) : Type
SpecTec.lean: error: type mismatch
  ((), t)
has type
  Unit × Valtype : Type
but is expected to have type
  Globaltype : Type
SpecTec.lean: error: unknown constant 'Numtype.Fn'
SpecTec.lean: error: unknown constant 'Numtype.Fn'
SpecTec.lean: error: unknown constant 'Valtype.Fn'
SpecTec.lean: error: unknown constant 'Valtype.Fn'
SpecTec.lean: error: unknown constant 'Valtype.In'
SpecTec.lean: error: unknown constant 'Valtype.In'
SpecTec.lean: error: unknown constant 'Numtype.In'
SpecTec.lean: error: unknown constant 'Numtype.In'
SpecTec.lean: error: unknown constant 'Valtype.In'
SpecTec.lean: error: unknown constant 'Valtype.In'
SpecTec.lean: error: application type mismatch
  List.get! C.LABEL l
argument
  l
has type
  List Labelidx : Type
but is expected to have type
  Nat : Type
SpecTec.lean: error: application type mismatch
  (t_1, t_2)
argument
  t_2
has type
  Valtype : Type
but is expected to have type
  Resulttype : Type
SpecTec.lean: error: application type mismatch
  List.cons t_2
argument
  t_2
has type
  Valtype : Type
but is expected to have type
  Resulttype : Type
SpecTec.lean: error: application type mismatch
  (t_1, t_2)
argument
  t_2
has type
  Valtype : Type
but is expected to have type
  Resulttype : Type
SpecTec.lean: error: application type mismatch
  List.cons t_2
argument
  t_2
has type
  Valtype : Type
but is expected to have type
  Resulttype : Type
SpecTec.lean: error: application type mismatch
  (t_1, t_2)
argument
  t_2
has type
  Valtype : Type
but is expected to have type
  Resulttype : Type
SpecTec.lean: error: application type mismatch
  (t_1, t_2)
argument
  t_2
has type
  Valtype : Type
but is expected to have type
  Resulttype : Type
SpecTec.lean: error: application type mismatch
  Prod.mk t'_1
argument
  t'_1
has type
  Valtype : Type
but is expected to have type
  List Valtype : Type
SpecTec.lean: error: failed to synthesize instance
  HAppend (List Instr) Instr ?m.77841
SpecTec.lean: error: application type mismatch
  (C, instr)
argument
  instr
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: type mismatch
  ((), t)
has type
  Unit × Valtype : Type
but is expected to have type
  Globaltype : Type
SpecTec.lean: error: application type mismatch
  Prod.mk expr
argument
  expr
has type
  List Expr : Type
but is expected to have type
  Expr : Type
SpecTec.lean: error: application type mismatch
  Prod.mk elemmode
argument
  elemmode
has type
  Option Elemmode : Type
but is expected to have type
  Elemmode : Type
SpecTec.lean: error: application type mismatch
  (C, datamode)
argument
  datamode
has type
  Option Datamode : Type
but is expected to have type
  Datamode : Type
SpecTec.lean: error: application type mismatch
  Prod.mk func
argument
  func
has type
  List Func : Type
but is expected to have type
  Func : Type
SpecTec.lean: error: application type mismatch
  Prod.mk global
argument
  global
has type
  List Global : Type
but is expected to have type
  Global : Type
SpecTec.lean: error: application type mismatch
  Prod.mk table
argument
  table
has type
  List Table : Type
but is expected to have type
  Table : Type
SpecTec.lean: error: application type mismatch
  Prod.mk mem
argument
  mem
has type
  List Mem : Type
but is expected to have type
  Mem : Type
SpecTec.lean: error: application type mismatch
  Prod.mk elem
argument
  elem
has type
  List Elem : Type
but is expected to have type
  Elem : Type
SpecTec.lean: error: application type mismatch
  (C, data)
argument
  data
has type
  List Data : Type
but is expected to have type
  Data : Type
SpecTec.lean: error: application type mismatch
  (C, start)
argument
  start
has type
  List Start : Type
but is expected to have type
  Start : Type
SpecTec.lean: error: type mismatch
  ()
has type
  Unit : Type
but is expected to have type
  List Datatype : Type
SpecTec.lean: warning: unused variable `s` [linter.unusedVariables]
SpecTec.lean: warning: unused variable `f` [linter.unusedVariables]
SpecTec.lean: error: expected identifier
SpecTec.lean: error: expected 'elab', 'elab_rules', 'infix', 'infixl', 'infixr', 'instance', 'macro', 'macro_rules', 'notation', 'postfix', 'prefix', 'syntax' or 'unif_hint'
SpecTec.lean: warning: unused variable `f` [linter.unusedVariables]
SpecTec.lean: warning: unused variable `x` [linter.unusedVariables]
SpecTec.lean: warning: unused variable `v` [linter.unusedVariables]
SpecTec.lean: warning: unused variable `s` [linter.unusedVariables]
SpecTec.lean: warning: unused variable `x` [linter.unusedVariables]
SpecTec.lean: warning: unused variable `v` [linter.unusedVariables]
SpecTec.lean: warning: unused variable `s` [linter.unusedVariables]
SpecTec.lean: warning: unused variable `x` [linter.unusedVariables]
SpecTec.lean: warning: unused variable `i` [linter.unusedVariables]
SpecTec.lean: warning: unused variable `r` [linter.unusedVariables]
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr
argument
  instr
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: failed to synthesize instance
  HAppend (List Admininstr) Admininstr ?m.124169
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr
argument
  instr
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: failed to synthesize instance
  HAppend (List Admininstr) Admininstr ?m.124562
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr'
argument
  instr'
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr
argument
  instr
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr
argument
  instr
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: application type mismatch
  default_ t
argument
  t
has type
  List Valtype : Type
but is expected to have type
  Valtype : Type
SpecTec.lean: error: failed to synthesize instance
  HAppend (List Val) Val ?m.126855
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr
argument
  instr
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: unknown constant 'Admininstr.Ref'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Ref'
SpecTec.lean: error: unknown constant 'Admininstr.Globalinst'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Ref'
SpecTec.lean: error: unknown constant 'Admininstr.Ref'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: unknown constant 'Admininstr.Val'
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr
argument
  instr
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr'
argument
  instr'
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr
argument
  instr
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr'
argument
  instr'
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr
argument
  instr
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr'
argument
  instr'
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr
argument
  instr
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr'
argument
  instr'
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr
argument
  instr
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr'
argument
  instr'
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr
argument
  instr
has type
  List Instr : Type
but is expected to have type
  Instr : Type
SpecTec.lean: error: application type mismatch
  Admininstr.Instr instr'
argument
  instr'
has type
  List Instr : Type
but is expected to have type
  Instr : Type
```
