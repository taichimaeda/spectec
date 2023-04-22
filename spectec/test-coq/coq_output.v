(** Coq export **)

From Coq Require Import String List Unicode.Utf8.

Open Scope type_scope.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Auxiliary definitions **)

Class Append (T: Type) : Type :=
  append : T -> T -> T.

Definition option_zip {α β γ: Type} (f: α → β → γ) (x: option α) (y: option β): option γ := 
 match x, y with
  | Some x, Some y => Some (f x y)
  | _, _ => None
 end.

Definition option_to_list {α: Type} (x: option α): list α :=
 match x with
  | None => nil
  | Some x => (cons x nil)
 end.

Fixpoint list_update {α: Type} (l: list α) (n: nat) (y: α): list α :=
match l, n with
  | nil, _=> nil
  | x :: l', 0 => y :: l'
  | x :: l', S n => x :: list_update l' n y
end.


(** Generated code **)

(** Alias definition : N **)
Definition N := nat.

(** Alias definition : Name **)
Definition Name := string.

(** Alias definition : Byte **)
Definition Byte := nat.

(** Alias definition : U32 **)
Definition U32 := nat.

(** Alias definition : Idx **)
Definition Idx := nat.

(** Alias definition : Funcidx **)
Definition Funcidx := Idx.

(** Alias definition : Globalidx **)
Definition Globalidx := Idx.

(** Alias definition : Tableidx **)
Definition Tableidx := Idx.

(** Alias definition : Memidx **)
Definition Memidx := Idx.

(** Alias definition : Elemidx **)
Definition Elemidx := Idx.

(** Alias definition : Dataidx **)
Definition Dataidx := Idx.

(** Alias definition : Labelidx **)
Definition Labelidx := Idx.

(** Alias definition : Localidx **)
Definition Localidx := Idx.

(** Inductive definition : Numtype **)
Inductive Numtype : Type :=
 | Numtype_I32 : Numtype
 | Numtype_I64 : Numtype
 | Numtype_F32 : Numtype
 | Numtype_F64 : Numtype
.

(** Inductive definition : Vectype **)
Inductive Vectype : Type :=
 | Vectype_V128 : Vectype
.

(** Inductive definition : Reftype **)
Inductive Reftype : Type :=
 | Reftype_FUNCREF : Reftype
 | Reftype_EXTERNREF : Reftype
.

(** Inductive definition : Valtype **)
Inductive Valtype : Type :=
 | Valtype_I32 : Valtype
 | Valtype_I64 : Valtype
 | Valtype_F32 : Valtype
 | Valtype_F64 : Valtype
 | Valtype_V128 : Valtype
 | Valtype_FUNCREF : Valtype
 | Valtype_EXTERNREF : Valtype
 | Valtype_BOT : Valtype
.

(** Function definition : fun_valtype_numtype **)
Definition fun_valtype_numtype (arg: Numtype) : Valtype :=
  match arg with
  | Numtype_I32 => Valtype_I32
  | Numtype_I64 => Valtype_I64
  | Numtype_F32 => Valtype_F32
  | Numtype_F64 => Valtype_F64
end.

(** Function definition : fun_valtype_reftype **)
Definition fun_valtype_reftype (arg: Reftype) : Valtype :=
  match arg with
  | Reftype_FUNCREF => Valtype_FUNCREF
  | Reftype_EXTERNREF => Valtype_EXTERNREF
end.

(** Function definition : fun_valtype_vectype **)
Definition fun_valtype_vectype (arg: Vectype) : Valtype :=
  match arg with
  | Vectype_V128 => Valtype_V128
end.

(** Inductive definition : In **)
Inductive In : Type :=
 | In_I32 : In
 | In_I64 : In
.

(** Function definition : fun_numtype_in **)
Definition fun_numtype_in (arg: In) : Numtype :=
  match arg with
  | In_I32 => Numtype_I32
  | In_I64 => Numtype_I64
end.

(** Function definition : fun_valtype_in **)
Definition fun_valtype_in (arg: In) : Valtype :=
  match arg with
  | In_I32 => Valtype_I32
  | In_I64 => Valtype_I64
end.

(** Inductive definition : Fn **)
Inductive Fn : Type :=
 | Fn_F32 : Fn
 | Fn_F64 : Fn
.

(** Function definition : fun_numtype_fn **)
Definition fun_numtype_fn (arg: Fn) : Numtype :=
  match arg with
  | Fn_F32 => Numtype_F32
  | Fn_F64 => Numtype_F64
end.

(** Function definition : fun_valtype_fn **)
Definition fun_valtype_fn (arg: Fn) : Valtype :=
  match arg with
  | Fn_F32 => Valtype_F32
  | Fn_F64 => Valtype_F64
end.

(** Alias definition : Resulttype **)
Definition Resulttype := (list Valtype).

(** Notation definition : Limits **)
Definition Limits := (* mixop:  *) (U32 * U32).

(** Notation definition : Mutflag **)
Definition Mutflag := (* mixop:  *) unit.

(** Notation definition : Globaltype **)
Definition Globaltype := (* mixop:  *) ((option Mutflag) * Valtype).

(** Notation definition : Functype **)
Definition Functype := (* mixop:  *) (Resulttype * Resulttype).

(** Notation definition : Tabletype **)
Definition Tabletype := (* mixop:  *) (Limits * Reftype).

(** Notation definition : Memtype **)
Definition Memtype := (* mixop:  *) Limits.

(** Alias definition : Elemtype **)
Definition Elemtype := Reftype.

(** Notation definition : Datatype **)
Definition Datatype := (* mixop:  *) unit.

(** Inductive definition : Externtype **)
Inductive Externtype : Type :=
 | Externtype_GLOBAL : Globaltype -> Externtype
 | Externtype_FUNC : Functype -> Externtype
 | Externtype_TABLE : Tabletype -> Externtype
 | Externtype_MEMORY : Memtype -> Externtype
.

(** Inductive definition : Sx **)
Inductive Sx : Type :=
 | Sx_U : Sx
 | Sx_S : Sx
.

(** Inductive definition : Unop_IXX **)
Inductive Unop_IXX : Type :=
 | Unop_IXX_CLZ : Unop_IXX
 | Unop_IXX_CTZ : Unop_IXX
 | Unop_IXX_POPCNT : Unop_IXX
.

(** Inductive definition : Unop_FXX **)
Inductive Unop_FXX : Type :=
 | Unop_FXX_ABS : Unop_FXX
 | Unop_FXX_NEG : Unop_FXX
 | Unop_FXX_SQRT : Unop_FXX
 | Unop_FXX_CEIL : Unop_FXX
 | Unop_FXX_FLOOR : Unop_FXX
 | Unop_FXX_TRUNC : Unop_FXX
 | Unop_FXX_NEAREST : Unop_FXX
.

(** Inductive definition : Binop_IXX **)
Inductive Binop_IXX : Type :=
 | Binop_IXX_ADD : Binop_IXX
 | Binop_IXX_SUB : Binop_IXX
 | Binop_IXX_MUL : Binop_IXX
 | Binop_IXX_DIV : Sx -> Binop_IXX
 | Binop_IXX_REM : Sx -> Binop_IXX
 | Binop_IXX_AND : Binop_IXX
 | Binop_IXX_OR : Binop_IXX
 | Binop_IXX_XOR : Binop_IXX
 | Binop_IXX_SHL : Binop_IXX
 | Binop_IXX_SHR : Sx -> Binop_IXX
 | Binop_IXX_ROTL : Binop_IXX
 | Binop_IXX_ROTR : Binop_IXX
.

(** Inductive definition : Binop_FXX **)
Inductive Binop_FXX : Type :=
 | Binop_FXX_ADD : Binop_FXX
 | Binop_FXX_SUB : Binop_FXX
 | Binop_FXX_MUL : Binop_FXX
 | Binop_FXX_DIV : Binop_FXX
 | Binop_FXX_MIN : Binop_FXX
 | Binop_FXX_MAX : Binop_FXX
 | Binop_FXX_COPYSIGN : Binop_FXX
.

(** Inductive definition : Testop_IXX **)
Inductive Testop_IXX : Type :=
 | Testop_IXX_EQZ : Testop_IXX
.

(** Inductive definition : Testop_FXX **)
Inductive Testop_FXX : Type :=
.

(** Inductive definition : Relop_IXX **)
Inductive Relop_IXX : Type :=
 | Relop_IXX_EQ : Relop_IXX
 | Relop_IXX_NE : Relop_IXX
 | Relop_IXX_LT : Sx -> Relop_IXX
 | Relop_IXX_GT : Sx -> Relop_IXX
 | Relop_IXX_LE : Sx -> Relop_IXX
 | Relop_IXX_GE : Sx -> Relop_IXX
.

(** Inductive definition : Relop_FXX **)
Inductive Relop_FXX : Type :=
 | Relop_FXX_EQ : Relop_FXX
 | Relop_FXX_NE : Relop_FXX
 | Relop_FXX_LT : Relop_FXX
 | Relop_FXX_GT : Relop_FXX
 | Relop_FXX_LE : Relop_FXX
 | Relop_FXX_GE : Relop_FXX
.

(** Inductive definition : Unop_numtype **)
Inductive Unop_numtype : Type :=
 | Unop_numtype__I : Unop_IXX -> Unop_numtype
 | Unop_numtype__F : Unop_FXX -> Unop_numtype
.

(** Inductive definition : Binop_numtype **)
Inductive Binop_numtype : Type :=
 | Binop_numtype__I : Binop_IXX -> Binop_numtype
 | Binop_numtype__F : Binop_FXX -> Binop_numtype
.

(** Inductive definition : Testop_numtype **)
Inductive Testop_numtype : Type :=
 | Testop_numtype__I : Testop_IXX -> Testop_numtype
 | Testop_numtype__F : Testop_FXX -> Testop_numtype
.

(** Inductive definition : Relop_numtype **)
Inductive Relop_numtype : Type :=
 | Relop_numtype__I : Relop_IXX -> Relop_numtype
 | Relop_numtype__F : Relop_FXX -> Relop_numtype
.

(** Inductive definition : Cvtop **)
Inductive Cvtop : Type :=
 | Cvtop_CONVERT : Cvtop
 | Cvtop_REINTERPRET : Cvtop
.

(** Alias definition : C_numtype **)
Definition C_numtype := nat.

(** Alias definition : C_vectype **)
Definition C_vectype := nat.

(** Alias definition : Blocktype **)
Definition Blocktype := Functype.

(** Inductive definition : Instr **)
Inductive Instr : Type :=
 | Instr_UNREACHABLE : Instr
 | Instr_NOP : Instr
 | Instr_DROP : Instr
 | Instr_SELECT : (option Valtype) -> Instr
 | Instr_BLOCK : (Blocktype * (list Instr)) -> Instr
 | Instr_LOOP : (Blocktype * (list Instr)) -> Instr
 | Instr_IF : (Blocktype * (list Instr) * (list Instr)) -> Instr
 | Instr_BR : Labelidx -> Instr
 | Instr_BR_IF : Labelidx -> Instr
 | Instr_BR_TABLE : ((list Labelidx) * Labelidx) -> Instr
 | Instr_CALL : Funcidx -> Instr
 | Instr_CALL_INDIRECT : (Tableidx * Functype) -> Instr
 | Instr_RETURN : Instr
 | Instr_CONST : (Numtype * C_numtype) -> Instr
 | Instr_UNOP : (Numtype * Unop_numtype) -> Instr
 | Instr_BINOP : (Numtype * Binop_numtype) -> Instr
 | Instr_TESTOP : (Numtype * Testop_numtype) -> Instr
 | Instr_RELOP : (Numtype * Relop_numtype) -> Instr
 | Instr_EXTEND : (Numtype * N) -> Instr
 | Instr_CVTOP : (Numtype * Cvtop * Numtype * (option Sx)) -> Instr
 | Instr_REF_NULL : Reftype -> Instr
 | Instr_REF_FUNC : Funcidx -> Instr
 | Instr_REF_IS_NULL : Instr
 | Instr_LOCAL_GET : Localidx -> Instr
 | Instr_LOCAL_SET : Localidx -> Instr
 | Instr_LOCAL_TEE : Localidx -> Instr
 | Instr_GLOBAL_GET : Globalidx -> Instr
 | Instr_GLOBAL_SET : Globalidx -> Instr
 | Instr_TABLE_GET : Tableidx -> Instr
 | Instr_TABLE_SET : Tableidx -> Instr
 | Instr_TABLE_SIZE : Tableidx -> Instr
 | Instr_TABLE_GROW : Tableidx -> Instr
 | Instr_TABLE_FILL : Tableidx -> Instr
 | Instr_TABLE_COPY : (Tableidx * Tableidx) -> Instr
 | Instr_TABLE_INIT : (Tableidx * Elemidx) -> Instr
 | Instr_ELEM_DROP : Elemidx -> Instr
 | Instr_MEMORY_SIZE : Instr
 | Instr_MEMORY_GROW : Instr
 | Instr_MEMORY_FILL : Instr
 | Instr_MEMORY_COPY : Instr
 | Instr_MEMORY_INIT : Dataidx -> Instr
 | Instr_DATA_DROP : Dataidx -> Instr
 | Instr_LOAD : (Numtype * (option (N * Sx)) * nat * nat) -> Instr
 | Instr_STORE : (Numtype * (option N) * nat * nat) -> Instr
.

(** Alias definition : Expr **)
Definition Expr := (list Instr).

(** Inductive definition : Elemmode **)
Inductive Elemmode : Type :=
 | Elemmode_TABLE : (Tableidx * Expr) -> Elemmode
 | Elemmode_DECLARE : Elemmode
.

(** Inductive definition : Datamode **)
Inductive Datamode : Type :=
 | Datamode_MEMORY : (Memidx * Expr) -> Datamode
.

(** Notation definition : Func **)
Definition Func := (* mixop:  *) (Functype * (list Valtype) * Expr).

(** Notation definition : Global **)
Definition Global := (* mixop:  *) (Globaltype * Expr).

(** Notation definition : Table **)
Definition Table := (* mixop:  *) Tabletype.

(** Notation definition : Mem **)
Definition Mem := (* mixop:  *) Memtype.

(** Notation definition : Elem **)
Definition Elem := (* mixop:  *) (Reftype * (list Expr) * (option Elemmode)).

(** Notation definition : Data **)
Definition Data := (* mixop:  *) ((list (list Byte)) * (option Datamode)).

(** Notation definition : Start **)
Definition Start := (* mixop:  *) Funcidx.

(** Inductive definition : Externuse **)
Inductive Externuse : Type :=
 | Externuse_FUNC : Funcidx -> Externuse
 | Externuse_GLOBAL : Globalidx -> Externuse
 | Externuse_TABLE : Tableidx -> Externuse
 | Externuse_MEMORY : Memidx -> Externuse
.

(** Notation definition : Export **)
Definition Export := (* mixop:  *) (Name * Externuse).

(** Notation definition : Import **)
Definition Import := (* mixop:  *) (Name * Name * Externtype).

(** Notation definition : Module **)
Definition Module := (* mixop:  *) ((list Import) * (list Func) * (list Global) * (list Table) * (list Mem) * (list Elem) * (list Data) * (list Start) * (list Export)).

(** Function definition : fun_size **)
Definition fun_size (arg: Valtype) : (option nat) :=
  match arg with
  | Valtype_I32 => (Some 32)
  | Valtype_I64 => (Some 64)
  | Valtype_F32 => (Some 32)
  | Valtype_F64 => (Some 64)
  | Valtype_V128 => (Some 128)
  | x => None
end.

(** Function definition : fun_test_sub_ATOM_22 **)
Definition fun_test_sub_ATOM_22 (arg: N) : nat :=
  match arg with
  | n_3_ATOM_y => 0
end.

(** Function definition : fun_curried_ **)
Definition fun_curried_ (arg: (N * N)) : nat :=
  match arg with
  | (n_1, n_2) => (n_1 + n_2)
end.

(** Inductive definition : Testfuse **)
Inductive Testfuse : Type :=
 | Testfuse_AB_ : (nat * nat * nat) -> Testfuse
 | Testfuse_CD : (nat * nat * nat) -> Testfuse
 | Testfuse_EF : (nat * nat * nat) -> Testfuse
 | Testfuse_GH : (nat * nat * nat) -> Testfuse
 | Testfuse_IJ : (nat * nat * nat) -> Testfuse
 | Testfuse_KL : (nat * nat * nat) -> Testfuse
 | Testfuse_MN : (nat * nat * nat) -> Testfuse
 | Testfuse_OP : (nat * nat * nat) -> Testfuse
 | Testfuse_QR : (nat * nat * nat) -> Testfuse
.

(** Record definition : Context **)
Record Context : Type := {
  FUNC : (list Functype);
  GLOBAL : (list Globaltype);
  TABLE : (list Tabletype);
  MEM : (list Memtype);
  ELEM : (list Elemtype);
  DATA : (list Datatype);
  LOCAL : (list Valtype);
  LABEL : (list Resulttype);
  RETURN : (option Resulttype);
 } 
.

(** Relation definition : Limits_ok **)
Inductive Limits_ok : (Limits * nat) -> Prop := 
  | Limits_ok_rule_0 (k : nat) (n_1 : N) (n_2 : N) : 
    ((n_1 <= n_2) /\ (n_2 <= k)) -> 
    (Limits_ok ((n_1, n_2), k))
.

(** Relation definition : Functype_ok **)
Inductive Functype_ok : Functype -> Prop := 
  | Functype_ok_rule_0 (ft : Functype) : 
    (Functype_ok ft)
.

(** Relation definition : Globaltype_ok **)
Inductive Globaltype_ok : Globaltype -> Prop := 
  | Globaltype_ok_rule_0 (gt : Globaltype) : 
    (Globaltype_ok gt)
.

(** Relation definition : Tabletype_ok **)
Inductive Tabletype_ok : Tabletype -> Prop := 
  | Tabletype_ok_rule_0 (lim : Limits) (rt : Reftype) : 
    (Limits_ok (lim, ((((Nat.pow 2) 32)) - 1))) -> 
    (Tabletype_ok (lim, rt))
.

(** Relation definition : Memtype_ok **)
Inductive Memtype_ok : Memtype -> Prop := 
  | Memtype_ok_rule_0 (lim : Limits) : 
    (Limits_ok (lim, (((Nat.pow 2) 16)))) -> 
    (Memtype_ok lim)
.

(** Relation definition : Externtype_ok **)
Inductive Externtype_ok : Externtype -> Prop := 
  | Externtype_ok_func (functype : Functype) : 
    (Functype_ok functype) -> 
    (Externtype_ok (Externtype_FUNC functype))
  | Externtype_ok_global (globaltype : Globaltype) : 
    (Globaltype_ok globaltype) -> 
    (Externtype_ok (Externtype_GLOBAL globaltype))
  | Externtype_ok_table (tabletype : Tabletype) : 
    (Tabletype_ok tabletype) -> 
    (Externtype_ok (Externtype_TABLE tabletype))
  | Externtype_ok_mem (memtype : Memtype) : 
    (Memtype_ok memtype) -> 
    (Externtype_ok (Externtype_MEMORY memtype))
.

(** Relation definition : Valtype_sub **)
Inductive Valtype_sub : (Valtype * Valtype) -> Prop := 
  | Valtype_sub_refl (t : Valtype) : 
    (Valtype_sub (t, t))
  | Valtype_sub_bot (t : Valtype) : 
    (Valtype_sub (Valtype_BOT, t))
.

(** Relation definition : Resulttype_sub **)
Inductive Resulttype_sub : ((list Valtype) * (list Valtype)) -> Prop := 
  | Resulttype_sub_rule_0 (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (List.length (t_1) = List.length (t_2)) -> 
    (List.Forall2 (fun t_1 t_2 => (Valtype_sub (t_1, t_2))) t_1 t_2) -> 
    (Resulttype_sub (t_1, t_2))
.

(** Relation definition : Limits_sub **)
Inductive Limits_sub : (Limits * Limits) -> Prop := 
  | Limits_sub_rule_0 (n_11 : N) (n_12 : N) (n_21 : N) (n_22 : N) : 
    (n_11 >= n_21) -> 
    (n_12 <= n_22) -> 
    (Limits_sub ((n_11, n_12), (n_21, n_22)))
.

(** Relation definition : Functype_sub **)
Inductive Functype_sub : (Functype * Functype) -> Prop := 
  | Functype_sub_rule_0 (ft : Functype) : 
    (Functype_sub (ft, ft))
.

(** Relation definition : Globaltype_sub **)
Inductive Globaltype_sub : (Globaltype * Globaltype) -> Prop := 
  | Globaltype_sub_rule_0 (gt : Globaltype) : 
    (Globaltype_sub (gt, gt))
.

(** Relation definition : Tabletype_sub **)
Inductive Tabletype_sub : (Tabletype * Tabletype) -> Prop := 
  | Tabletype_sub_rule_0 (lim_1 : Limits) (lim_2 : Limits) (rt : Reftype) : 
    (Limits_sub (lim_1, lim_2)) -> 
    (Tabletype_sub ((lim_1, rt), (lim_2, rt)))
.

(** Relation definition : Memtype_sub **)
Inductive Memtype_sub : (Memtype * Memtype) -> Prop := 
  | Memtype_sub_rule_0 (lim_1 : Limits) (lim_2 : Limits) : 
    (Limits_sub (lim_1, lim_2)) -> 
    (Memtype_sub (lim_1, lim_2))
.

(** Relation definition : Externtype_sub **)
Inductive Externtype_sub : (Externtype * Externtype) -> Prop := 
  | Externtype_sub_func (ft_1 : Functype) (ft_2 : Functype) : 
    (Functype_sub (ft_1, ft_2)) -> 
    (Externtype_sub ((Externtype_FUNC ft_1), (Externtype_FUNC ft_2)))
  | Externtype_sub_global (gt_1 : Globaltype) (gt_2 : Globaltype) : 
    (Globaltype_sub (gt_1, gt_2)) -> 
    (Externtype_sub ((Externtype_GLOBAL gt_1), (Externtype_GLOBAL gt_2)))
  | Externtype_sub_table (tt_1 : Tabletype) (tt_2 : Tabletype) : 
    (Tabletype_sub (tt_1, tt_2)) -> 
    (Externtype_sub ((Externtype_TABLE tt_1), (Externtype_TABLE tt_2)))
  | Externtype_sub_mem (mt_1 : Memtype) (mt_2 : Memtype) : 
    (Memtype_sub (mt_1, mt_2)) -> 
    (Externtype_sub ((Externtype_MEMORY mt_1), (Externtype_MEMORY mt_2)))
.

(** Relation definition : Blocktype_ok **)
Inductive Blocktype_ok : (Context * Blocktype * Functype) -> Prop := 
  | Blocktype_ok_rule_0 (C : Context) (ft : Functype) : 
    (Functype_ok ft) -> 
    (Blocktype_ok (C, ft, ft))
.

(** Relation definition : Instr_ok **)
Inductive Instr_ok : (Context * Instr * Functype) -> Prop := 
  | Instr_ok_unreachable (C : Context) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (Instr_ok (C, Instr_UNREACHABLE, (t_1, t_2)))
  | Instr_ok_nop (C : Context) : 
    (Instr_ok (C, Instr_NOP, (nil, nil)))
  | Instr_ok_drop (C : Context) (t : Valtype) : 
    (Instr_ok (C, Instr_DROP, ([t], nil)))
  | Instr_ok_select_expl (C : Context) (t : Valtype) : 
    (Instr_ok (C, (Instr_SELECT (Some t)), ([t; t; Valtype_I32], [t])))
  | Instr_ok_select_impl (C : Context) (numtype : Numtype) (t : Valtype) (t' : Valtype) (vectype : Vectype) : 
    (Valtype_sub (t, t')) -> 
    ((t' = (fun_valtype_numtype numtype)) \/ (t' = (fun_valtype_vectype vectype))) -> 
    (Instr_ok (C, (Instr_SELECT None), ([t; t; Valtype_I32], [t])))
  | Instr_ok_block (C : Context) (bt : Blocktype) (instr : (list Instr)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (Blocktype_ok (C, bt, (t_1, t_2))) -> 
    (InstrSeq_ok (({|FUNC := nil; GLOBAL := nil; TABLE := nil; MEM := nil; ELEM := nil; DATA := nil; LOCAL := nil; LABEL := (List.map (fun t_2 => [t_2]) t_2); RETURN := None|} ++ C), instr, (t_1, t_2))) -> 
    (Instr_ok (C, (Instr_BLOCK (bt, instr)), (t_1, t_2)))
  | Instr_ok_loop (C : Context) (bt : Blocktype) (instr : (list Instr)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (Blocktype_ok (C, bt, (t_1, t_2))) -> 
    (InstrSeq_ok (({|FUNC := nil; GLOBAL := nil; TABLE := nil; MEM := nil; ELEM := nil; DATA := nil; LOCAL := nil; LABEL := (List.map (fun t_1 => [t_1]) t_1); RETURN := None|} ++ C), instr, (t_1, t_2))) -> 
    (Instr_ok (C, (Instr_LOOP (bt, instr)), (t_1, t_2)))
  | Instr_ok_if (C : Context) (bt : Blocktype) (instr_1 : (list Instr)) (instr_2 : (list Instr)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (Blocktype_ok (C, bt, (t_1, t_2))) -> 
    (InstrSeq_ok (({|FUNC := nil; GLOBAL := nil; TABLE := nil; MEM := nil; ELEM := nil; DATA := nil; LOCAL := nil; LABEL := (List.map (fun t_2 => [t_2]) t_2); RETURN := None|} ++ C), instr_1, (t_1, t_2))) -> 
    (InstrSeq_ok (({|FUNC := nil; GLOBAL := nil; TABLE := nil; MEM := nil; ELEM := nil; DATA := nil; LOCAL := nil; LABEL := (List.map (fun t_2 => [t_2]) t_2); RETURN := None|} ++ C), instr_2, (t_1, t_2))) -> 
    (Instr_ok (C, (Instr_IF (bt, instr_1, instr_2)), (t_1, t_2)))
  | Instr_ok_br (C : Context) (l : Labelidx) (t : (list Valtype)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (l < List.length (C.(LABEL))) -> 
    ((List.nth_error C.(LABEL) l) = Some t) -> 
    (Instr_ok (C, (Instr_BR l), ((t_1 ++ t), t_2)))
  | Instr_ok_br_if (C : Context) (l : Labelidx) (t : (list Valtype)) : 
    (l < List.length (C.(LABEL))) -> 
    ((List.nth_error C.(LABEL) l) = Some t) -> 
    (Instr_ok (C, (Instr_BR_IF l), ((t ++ [Valtype_I32]), t)))
  | Instr_ok_br_table (C : Context) (l : (list Labelidx)) (l' : Labelidx) (t : (list Valtype)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (List.Forall (fun l => (l < List.length (C.(LABEL)))) l) -> 
    (l' < List.length (C.(LABEL))) -> 
    (List.Forall (fun l => (Resulttype_sub (t, (List.nth_error C.(LABEL) l)))) l) -> 
    (Resulttype_sub (t, (List.nth_error C.(LABEL) l'))) -> 
    (Instr_ok (C, (Instr_BR_TABLE (l, l')), ((t_1 ++ t), t_2)))
  | Instr_ok_return (C : Context) (t : (list Valtype)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (C.(RETURN) = (Some t)) -> 
    (Instr_ok (C, Instr_RETURN, ((t_1 ++ t), t_2)))
  | Instr_ok_call (C : Context) (t_1 : (list Valtype)) (t_2 : (list Valtype)) (x : Idx) : 
    (x < List.length (C.(FUNC))) -> 
    ((List.nth_error C.(FUNC) x) = Some (t_1, t_2)) -> 
    (Instr_ok (C, (Instr_CALL x), (t_1, t_2)))
  | Instr_ok_call_indirect (C : Context) (ft : Functype) (lim : Limits) (t_1 : (list Valtype)) (t_2 : (list Valtype)) (x : Idx) : 
    (x < List.length (C.(TABLE))) -> 
    ((List.nth_error C.(TABLE) x) = Some (lim, Reftype_FUNCREF)) -> 
    (ft = (t_1, t_2)) -> 
    (Instr_ok (C, (Instr_CALL_INDIRECT (x, ft)), ((t_1 ++ [Valtype_I32]), t_2)))
  | Instr_ok_const (C : Context) (c_nt : C_numtype) (nt : Numtype) : 
    (Instr_ok (C, (Instr_CONST (nt, c_nt)), (nil, [(fun_valtype_numtype nt)])))
  | Instr_ok_unop (C : Context) (nt : Numtype) (unop : Unop_numtype) : 
    (Instr_ok (C, (Instr_UNOP (nt, unop)), ([(fun_valtype_numtype nt)], [(fun_valtype_numtype nt)])))
  | Instr_ok_binop (C : Context) (binop : Binop_numtype) (nt : Numtype) : 
    (Instr_ok (C, (Instr_BINOP (nt, binop)), ([(fun_valtype_numtype nt); (fun_valtype_numtype nt)], [(fun_valtype_numtype nt)])))
  | Instr_ok_testop (C : Context) (nt : Numtype) (testop : Testop_numtype) : 
    (Instr_ok (C, (Instr_TESTOP (nt, testop)), ([(fun_valtype_numtype nt)], [Valtype_I32])))
  | Instr_ok_relop (C : Context) (nt : Numtype) (relop : Relop_numtype) : 
    (Instr_ok (C, (Instr_RELOP (nt, relop)), ([(fun_valtype_numtype nt); (fun_valtype_numtype nt)], [Valtype_I32])))
  | Instr_ok_extend (C : Context) (n : N) (nt : Numtype) (o0 : nat) : 
    ((fun_size (fun_valtype_numtype nt)) = (Some o0)) -> 
    (n <= o0) -> 
    (Instr_ok (C, (Instr_EXTEND (nt, n)), ([(fun_valtype_numtype nt)], [(fun_valtype_numtype nt)])))
  | Instr_ok_reinterpret (C : Context) (nt_1 : Numtype) (nt_2 : Numtype) (o0 : nat) (o1 : nat) : 
    ((fun_size (fun_valtype_numtype nt_1)) = (Some o0)) -> 
    ((fun_size (fun_valtype_numtype nt_2)) = (Some o1)) -> 
    (nt_1 <> nt_2) -> 
    (o0 = o1) -> 
    (Instr_ok (C, (Instr_CVTOP (nt_1, Cvtop_REINTERPRET, nt_2, None)), ([(fun_valtype_numtype nt_2)], [(fun_valtype_numtype nt_1)])))
  | Instr_ok_convert_i (C : Context) (in_1 : In) (in_2 : In) (sx : (option Sx)) (o0 : nat) (o1 : nat) : 
    ((fun_size (fun_valtype_in in_1)) = (Some o0)) -> 
    ((fun_size (fun_valtype_in in_2)) = (Some o1)) -> 
    (in_1 <> in_2) -> 
    ((sx = None) = (o0 > o1)) -> 
    (Instr_ok (C, (Instr_CVTOP ((fun_numtype_in in_1), Cvtop_CONVERT, (fun_numtype_in in_2), sx)), ([(fun_valtype_in in_2)], [(fun_valtype_in in_1)])))
  | Instr_ok_convert_f (C : Context) (fn_1 : Fn) (fn_2 : Fn) : 
    (fn_1 <> fn_2) -> 
    (Instr_ok (C, (Instr_CVTOP ((fun_numtype_fn fn_1), Cvtop_CONVERT, (fun_numtype_fn fn_2), None)), ([(fun_valtype_fn fn_2)], [(fun_valtype_fn fn_1)])))
  | Instr_ok_ref_null (C : Context) (rt : Reftype) : 
    (Instr_ok (C, (Instr_REF_NULL rt), (nil, [(fun_valtype_reftype rt)])))
  | Instr_ok_ref_func (C : Context) (ft : Functype) (x : Idx) : 
    (x < List.length (C.(FUNC))) -> 
    ((List.nth_error C.(FUNC) x) = Some ft) -> 
    (Instr_ok (C, (Instr_REF_FUNC x), (nil, [Valtype_FUNCREF])))
  | Instr_ok_ref_is_null (C : Context) (rt : Reftype) : 
    (Instr_ok (C, Instr_REF_IS_NULL, ([(fun_valtype_reftype rt)], [Valtype_I32])))
  | Instr_ok_local_get (C : Context) (t : Valtype) (x : Idx) : 
    (x < List.length (C.(LOCAL))) -> 
    ((List.nth_error C.(LOCAL) x) = Some t) -> 
    (Instr_ok (C, (Instr_LOCAL_GET x), (nil, [t])))
  | Instr_ok_local_set (C : Context) (t : Valtype) (x : Idx) : 
    (x < List.length (C.(LOCAL))) -> 
    ((List.nth_error C.(LOCAL) x) = Some t) -> 
    (Instr_ok (C, (Instr_LOCAL_SET x), ([t], nil)))
  | Instr_ok_local_tee (C : Context) (t : Valtype) (x : Idx) : 
    (x < List.length (C.(LOCAL))) -> 
    ((List.nth_error C.(LOCAL) x) = Some t) -> 
    (Instr_ok (C, (Instr_LOCAL_TEE x), ([t], [t])))
  | Instr_ok_global_get (C : Context) (mut : (option Mutflag)) (t : Valtype) (x : Idx) : 
    (x < List.length (C.(GLOBAL))) -> 
    ((List.nth_error C.(GLOBAL) x) = Some (mut, t)) -> 
    (Instr_ok (C, (Instr_GLOBAL_GET x), (nil, [t])))
  | Instr_ok_global_set (C : Context) (t : Valtype) (x : Idx) : 
    (x < List.length (C.(GLOBAL))) -> 
    ((List.nth_error C.(GLOBAL) x) = Some ((Some ()), t)) -> 
    (Instr_ok (C, (Instr_GLOBAL_SET x), ([t], nil)))
  | Instr_ok_table_get (C : Context) (lim : Limits) (rt : Reftype) (x : Idx) : 
    (x < List.length (C.(TABLE))) -> 
    ((List.nth_error C.(TABLE) x) = Some (lim, rt)) -> 
    (Instr_ok (C, (Instr_TABLE_GET x), ([Valtype_I32], [(fun_valtype_reftype rt)])))
  | Instr_ok_table_set (C : Context) (lim : Limits) (rt : Reftype) (x : Idx) : 
    (x < List.length (C.(TABLE))) -> 
    ((List.nth_error C.(TABLE) x) = Some (lim, rt)) -> 
    (Instr_ok (C, (Instr_TABLE_SET x), ([Valtype_I32; (fun_valtype_reftype rt)], nil)))
  | Instr_ok_table_size (C : Context) (tt : Tabletype) (x : Idx) : 
    (x < List.length (C.(TABLE))) -> 
    ((List.nth_error C.(TABLE) x) = Some tt) -> 
    (Instr_ok (C, (Instr_TABLE_SIZE x), (nil, [Valtype_I32])))
  | Instr_ok_table_grow (C : Context) (lim : Limits) (rt : Reftype) (x : Idx) : 
    (x < List.length (C.(TABLE))) -> 
    ((List.nth_error C.(TABLE) x) = Some (lim, rt)) -> 
    (Instr_ok (C, (Instr_TABLE_GROW x), ([(fun_valtype_reftype rt); Valtype_I32], [Valtype_I32])))
  | Instr_ok_table_fill (C : Context) (lim : Limits) (rt : Reftype) (x : Idx) : 
    (x < List.length (C.(TABLE))) -> 
    ((List.nth_error C.(TABLE) x) = Some (lim, rt)) -> 
    (Instr_ok (C, (Instr_TABLE_FILL x), ([Valtype_I32; (fun_valtype_reftype rt); Valtype_I32], nil)))
  | Instr_ok_table_copy (C : Context) (lim_1 : Limits) (lim_2 : Limits) (rt : Reftype) (x_1 : Idx) (x_2 : Idx) : 
    (x_1 < List.length (C.(TABLE))) -> 
    (x_2 < List.length (C.(TABLE))) -> 
    ((List.nth_error C.(TABLE) x_1) = Some (lim_1, rt)) -> 
    ((List.nth_error C.(TABLE) x_2) = Some (lim_2, rt)) -> 
    (Instr_ok (C, (Instr_TABLE_COPY (x_1, x_2)), ([Valtype_I32; Valtype_I32; Valtype_I32], nil)))
  | Instr_ok_table_init (C : Context) (lim : Limits) (rt : Reftype) (x_1 : Idx) (x_2 : Idx) : 
    (x_1 < List.length (C.(TABLE))) -> 
    (x_2 < List.length (C.(ELEM))) -> 
    ((List.nth_error C.(TABLE) x_1) = Some (lim, rt)) -> 
    ((List.nth_error C.(ELEM) x_2) = Some rt) -> 
    (Instr_ok (C, (Instr_TABLE_INIT (x_1, x_2)), ([Valtype_I32; Valtype_I32; Valtype_I32], nil)))
  | Instr_ok_elem_drop (C : Context) (rt : Reftype) (x : Idx) : 
    (x < List.length (C.(ELEM))) -> 
    ((List.nth_error C.(ELEM) x) = Some rt) -> 
    (Instr_ok (C, (Instr_ELEM_DROP x), (nil, nil)))
  | Instr_ok_memory_size (C : Context) (mt : Memtype) : 
    (0 < List.length (C.(MEM))) -> 
    ((List.nth_error C.(MEM) 0) = Some mt) -> 
    (Instr_ok (C, Instr_MEMORY_SIZE, (nil, [Valtype_I32])))
  | Instr_ok_memory_grow (C : Context) (mt : Memtype) : 
    (0 < List.length (C.(MEM))) -> 
    ((List.nth_error C.(MEM) 0) = Some mt) -> 
    (Instr_ok (C, Instr_MEMORY_GROW, ([Valtype_I32], [Valtype_I32])))
  | Instr_ok_memory_fill (C : Context) (mt : Memtype) : 
    (0 < List.length (C.(MEM))) -> 
    ((List.nth_error C.(MEM) 0) = Some mt) -> 
    (Instr_ok (C, Instr_MEMORY_FILL, ([Valtype_I32; Valtype_I32; Valtype_I32], [Valtype_I32])))
  | Instr_ok_memory_copy (C : Context) (mt : Memtype) : 
    (0 < List.length (C.(MEM))) -> 
    ((List.nth_error C.(MEM) 0) = Some mt) -> 
    (Instr_ok (C, Instr_MEMORY_COPY, ([Valtype_I32; Valtype_I32; Valtype_I32], [Valtype_I32])))
  | Instr_ok_memory_init (C : Context) (mt : Memtype) (x : Idx) : 
    (0 < List.length (C.(MEM))) -> 
    (x < List.length (C.(DATA))) -> 
    ((List.nth_error C.(MEM) 0) = Some mt) -> 
    ((List.nth_error C.(DATA) x) = Some ()) -> 
    (Instr_ok (C, (Instr_MEMORY_INIT x), ([Valtype_I32; Valtype_I32; Valtype_I32], [Valtype_I32])))
  | Instr_ok_data_drop (C : Context) (x : Idx) : 
    (x < List.length (C.(DATA))) -> 
    ((List.nth_error C.(DATA) x) = Some ()) -> 
    (Instr_ok (C, (Instr_DATA_DROP x), (nil, nil)))
  | Instr_ok_load (C : Context) (reserved_in : In) (mt : Memtype) (n : (option N)) (n_A : N) (n_O : N) (nt : Numtype) (sx : (option Sx)) (o0 : nat) (o1 : (option nat)) : 
    (0 < List.length (C.(MEM))) -> 
    ((n = None) = (o1 = None)) -> 
    ((n = None) = (sx = None)) -> 
    ((fun_size (fun_valtype_numtype nt)) = (Some o0)) -> 
    (List.Forall (fun o1 => ((fun_size (fun_valtype_numtype nt)) = (Some o1))) o1.toList) -> 
    ((List.nth_error C.(MEM) 0) = Some mt) -> 
    ((((Nat.pow 2) n_A)) <= (((Nat.div o0) 8))) -> 
    (List.Forall2 (fun n o1 => (((((Nat.pow 2) n_A)) <= (((Nat.div n) 8))) /\ ((((Nat.div n) 8)) < (((Nat.div o1) 8))))) n.toList o1.toList) -> 
    ((n = None) \/ (nt = (fun_numtype_in reserved_in))) -> 
    (Instr_ok (C, (Instr_LOAD (nt, (option_zip (fun n sx => (n, sx)) n sx), n_A, n_O)), ([Valtype_I32], [(fun_valtype_numtype nt)])))
  | Instr_ok_store (C : Context) (reserved_in : In) (mt : Memtype) (n : (option N)) (n_A : N) (n_O : N) (nt : Numtype) (o0 : nat) (o1 : (option nat)) : 
    (0 < List.length (C.(MEM))) -> 
    ((n = None) = (o1 = None)) -> 
    ((fun_size (fun_valtype_numtype nt)) = (Some o0)) -> 
    (List.Forall (fun o1 => ((fun_size (fun_valtype_numtype nt)) = (Some o1))) o1.toList) -> 
    ((List.nth_error C.(MEM) 0) = Some mt) -> 
    ((((Nat.pow 2) n_A)) <= (((Nat.div o0) 8))) -> 
    (List.Forall2 (fun n o1 => (((((Nat.pow 2) n_A)) <= (((Nat.div n) 8))) /\ ((((Nat.div n) 8)) < (((Nat.div o1) 8))))) n.toList o1.toList) -> 
    ((n = None) \/ (nt = (fun_numtype_in reserved_in))) -> 
    (Instr_ok (C, (Instr_STORE (nt, n, n_A, n_O)), ([Valtype_I32; (fun_valtype_numtype nt)], nil)))

with (** Relation definition : InstrSeq_ok **)
InstrSeq_ok : (Context * (list Instr) * Functype) -> Prop := 
  | InstrSeq_ok_empty (C : Context) : 
    (InstrSeq_ok (C, nil, (nil, nil)))
  | InstrSeq_ok_seq (C : Context) (instr_1 : Instr) (instr_2 : Instr) (t_1 : (list Valtype)) (t_2 : (list Valtype)) (t_3 : (list Valtype)) : 
    (Instr_ok (C, instr_1, (t_1, t_2))) -> 
    (InstrSeq_ok (C, [instr_2], (t_2, t_3))) -> 
    (InstrSeq_ok (C, ([instr_1] ++ [instr_2]), (t_1, t_3)))
  | InstrSeq_ok_weak (C : Context) (instr : (list Instr)) (t'_1 : Valtype) (t'_2 : (list Valtype)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (InstrSeq_ok (C, instr, (t_1, t_2))) -> 
    (Resulttype_sub ([t'_1], t_1)) -> 
    (Resulttype_sub (t_2, t'_2)) -> 
    (InstrSeq_ok (C, instr, ([t'_1], t'_2)))
  | InstrSeq_ok_frame (C : Context) (instr : (list Instr)) (t : (list Valtype)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (InstrSeq_ok (C, instr, (t_1, t_2))) -> 
    (InstrSeq_ok (C, instr, ((t ++ t_1), (t ++ t_2))))
.

(** Relation definition : Expr_ok **)
Inductive Expr_ok : (Context * Expr * Resulttype) -> Prop := 
  | Expr_ok_rule_0 (C : Context) (instr : (list Instr)) (t : (list Valtype)) : 
    (InstrSeq_ok (C, instr, (nil, t))) -> 
    (Expr_ok (C, instr, t))
.

(** Relation definition : Instr_const **)
Inductive Instr_const : (Context * Instr) -> Prop := 
  | Instr_const_const (C : Context) (c : C_numtype) (nt : Numtype) : 
    (Instr_const (C, (Instr_CONST (nt, c))))
  | Instr_const_ref_null (C : Context) (rt : Reftype) : 
    (Instr_const (C, (Instr_REF_NULL rt)))
  | Instr_const_ref_func (C : Context) (x : Idx) : 
    (Instr_const (C, (Instr_REF_FUNC x)))
  | Instr_const_global_get (C : Context) (t : Valtype) (x : Idx) : 
    (x < List.length (C.(GLOBAL))) -> 
    ((List.nth_error C.(GLOBAL) x) = Some (None, t)) -> 
    (Instr_const (C, (Instr_GLOBAL_GET x)))
.

(** Relation definition : Expr_const **)
Inductive Expr_const : (Context * Expr) -> Prop := 
  | Expr_const_rule_0 (C : Context) (instr : (list Instr)) : 
    (List.Forall (fun instr => (Instr_const (C, instr))) instr) -> 
    (Expr_const (C, instr))
.

(** Relation definition : Expr_ok_const **)
Inductive Expr_ok_const : (Context * Expr * Valtype) -> Prop := 
  | Expr_ok_const_rule_0 (C : Context) (expr : Expr) (t : Valtype) : 
    (Expr_ok (C, expr, [t])) -> 
    (Expr_const (C, expr)) -> 
    (Expr_ok_const (C, expr, t))
.

(** Relation definition : Func_ok **)
Inductive Func_ok : (Context * Func * Functype) -> Prop := 
  | Func_ok_rule_0 (C : Context) (expr : Expr) (ft : Functype) (t : (list Valtype)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (ft = (t_1, t_2)) -> 
    (Functype_ok ft) -> 
    (Expr_ok (({|FUNC := nil; GLOBAL := nil; TABLE := nil; MEM := nil; ELEM := nil; DATA := nil; LOCAL := nil; LABEL := nil; RETURN := (Some t_2)|} ++ ({|FUNC := nil; GLOBAL := nil; TABLE := nil; MEM := nil; ELEM := nil; DATA := nil; LOCAL := nil; LABEL := [t_2]; RETURN := None|} ++ ({|FUNC := nil; GLOBAL := nil; TABLE := nil; MEM := nil; ELEM := nil; DATA := nil; LOCAL := (t_1 ++ t); LABEL := nil; RETURN := None|} ++ C))), expr, t_2)) -> 
    (Func_ok (C, (ft, t, expr), ft))
.

(** Relation definition : Global_ok **)
Inductive Global_ok : (Context * Global * Globaltype) -> Prop := 
  | Global_ok_rule_0 (C : Context) (expr : Expr) (gt : Globaltype) (t : Valtype) : 
    (Globaltype_ok gt) -> 
    (gt = ((Some ()), t)) -> 
    (Expr_ok_const (C, expr, t)) -> 
    (Global_ok (C, (gt, expr), gt))
.

(** Relation definition : Table_ok **)
Inductive Table_ok : (Context * Table * Tabletype) -> Prop := 
  | Table_ok_rule_0 (C : Context) (tt : Tabletype) : 
    (Tabletype_ok tt) -> 
    (Table_ok (C, tt, tt))
.

(** Relation definition : Mem_ok **)
Inductive Mem_ok : (Context * Mem * Memtype) -> Prop := 
  | Mem_ok_rule_0 (C : Context) (mt : Memtype) : 
    (Memtype_ok mt) -> 
    (Mem_ok (C, mt, mt))
.

(** Relation definition : Elemmode_ok **)
Inductive Elemmode_ok : (Context * Elemmode * Reftype) -> Prop := 
  | Elemmode_ok_active (C : Context) (expr : Expr) (lim : Limits) (rt : Reftype) (x : Idx) : 
    (x < List.length (C.(TABLE))) -> 
    ((List.nth_error C.(TABLE) x) = Some (lim, rt)) -> 
    (Expr_ok_const (C, expr, Valtype_I32))(* *{} *) -> 
    (Elemmode_ok (C, (Elemmode_TABLE (x, expr)), rt))
  | Elemmode_ok_declare (C : Context) (rt : Reftype) : 
    (Elemmode_ok (C, Elemmode_DECLARE, rt))
.

(** Relation definition : Elem_ok **)
Inductive Elem_ok : (Context * Elem * Reftype) -> Prop := 
  | Elem_ok_rule_0 (C : Context) (elemmode : (option Elemmode)) (expr : (list Expr)) (rt : Reftype) : 
    (List.Forall (fun expr => (Expr_ok (C, expr, [(fun_valtype_reftype rt)]))) expr) -> 
    (List.Forall (fun elemmode => (Elemmode_ok (C, elemmode, rt))) elemmode.toList) -> 
    (Elem_ok (C, (rt, expr, elemmode), rt))
.

(** Relation definition : Datamode_ok **)
Inductive Datamode_ok : (Context * Datamode) -> Prop := 
  | Datamode_ok_rule_0 (C : Context) (expr : Expr) (mt : Memtype) : 
    (0 < List.length (C.(MEM))) -> 
    ((List.nth_error C.(MEM) 0) = Some mt) -> 
    (Expr_ok_const (C, expr, Valtype_I32))(* *{} *) -> 
    (Datamode_ok (C, (Datamode_MEMORY (0, expr))))
.

(** Relation definition : Data_ok **)
Inductive Data_ok : (Context * Data) -> Prop := 
  | Data_ok_rule_0 (C : Context) (b : (list (list Byte))) (datamode : (option Datamode)) : 
    (List.Forall (fun datamode => (Datamode_ok (C, datamode))) datamode.toList) -> 
    (Data_ok (C, ((List.map (fun b => b) b), datamode)))
.

(** Relation definition : Start_ok **)
Inductive Start_ok : (Context * Start) -> Prop := 
  | Start_ok_rule_0 (C : Context) (x : Idx) : 
    (x < List.length (C.(FUNC))) -> 
    ((List.nth_error C.(FUNC) x) = Some (nil, nil)) -> 
    (Start_ok (C, x))
.

(** Relation definition : Import_ok **)
Inductive Import_ok : (Context * Import * Externtype) -> Prop := 
  | Import_ok_rule_0 (C : Context) (name_1 : Name) (name_2 : Name) (xt : Externtype) : 
    (Externtype_ok xt) -> 
    (Import_ok (C, (name_1, name_2, xt), xt))
.

(** Relation definition : Externuse_ok **)
Inductive Externuse_ok : (Context * Externuse * Externtype) -> Prop := 
  | Externuse_ok_func (C : Context) (ft : Functype) (x : Idx) : 
    (x < List.length (C.(FUNC))) -> 
    ((List.nth_error C.(FUNC) x) = Some ft) -> 
    (Externuse_ok (C, (Externuse_FUNC x), (Externtype_FUNC ft)))
  | Externuse_ok_global (C : Context) (gt : Globaltype) (x : Idx) : 
    (x < List.length (C.(GLOBAL))) -> 
    ((List.nth_error C.(GLOBAL) x) = Some gt) -> 
    (Externuse_ok (C, (Externuse_GLOBAL x), (Externtype_GLOBAL gt)))
  | Externuse_ok_table (C : Context) (tt : Tabletype) (x : Idx) : 
    (x < List.length (C.(TABLE))) -> 
    ((List.nth_error C.(TABLE) x) = Some tt) -> 
    (Externuse_ok (C, (Externuse_TABLE x), (Externtype_TABLE tt)))
  | Externuse_ok_mem (C : Context) (mt : Memtype) (x : Idx) : 
    (x < List.length (C.(MEM))) -> 
    ((List.nth_error C.(MEM) x) = Some mt) -> 
    (Externuse_ok (C, (Externuse_MEMORY x), (Externtype_MEMORY mt)))
.

(** Relation definition : Export_ok **)
Inductive Export_ok : (Context * Export * Externtype) -> Prop := 
  | Export_ok_rule_0 (C : Context) (externuse : Externuse) (name : Name) (xt : Externtype) : 
    (Externuse_ok (C, externuse, xt)) -> 
    (Export_ok (C, (name, externuse), xt))
.

(** Relation definition : Module_ok **)
Inductive Module_ok : Module -> Prop := 
  | Module_ok_rule_0 (C : Context) (data : (list Data)) (elem : (list Elem)) (export : (list Export)) (ft : (list Functype)) (func : (list Func)) (global : (list Global)) (gt : (list Globaltype)) (import : (list Import)) (mem : (list Mem)) (mt : (list Memtype)) (n : N) (rt : (list Reftype)) (start : (list Start)) (table : (list Table)) (tt : (list Tabletype)) : 
    (List.length (ft) = List.length (func)) -> 
    (List.length (global) = List.length (gt)) -> 
    (List.length (table) = List.length (tt)) -> 
    (List.length (mem) = List.length (mt)) -> 
    (List.length (elem) = List.length (rt)) -> 
    (List.length (data) = n) -> 
    (C = {|FUNC := ft; GLOBAL := gt; TABLE := tt; MEM := mt; ELEM := rt; DATA := [()]; LOCAL := nil; LABEL := nil; RETURN := None|}) -> 
    (List.Forall2 (fun ft func => (Func_ok (C, func, ft))) ft func) -> 
    (List.Forall2 (fun global gt => (Global_ok (C, global, gt))) global gt) -> 
    (List.Forall2 (fun table tt => (Table_ok (C, table, tt))) table tt) -> 
    (List.Forall2 (fun mem mt => (Mem_ok (C, mem, mt))) mem mt) -> 
    (List.Forall2 (fun elem rt => (Elem_ok (C, elem, rt))) elem rt) -> 
    (List.Forall (fun data => (Data_ok (C, data))) data) -> 
    (List.Forall (fun start => (Start_ok (C, start))) start) -> 
    (List.length (mem) <= 1) -> 
    (List.length (start) <= 1) -> 
    (Module_ok (import, func, global, table, mem, elem, data, start, export))
.

(** Alias definition : Addr **)
Definition Addr := nat.

(** Alias definition : Funcaddr **)
Definition Funcaddr := Addr.

(** Alias definition : Globaladdr **)
Definition Globaladdr := Addr.

(** Alias definition : Tableaddr **)
Definition Tableaddr := Addr.

(** Alias definition : Memaddr **)
Definition Memaddr := Addr.

(** Alias definition : Elemaddr **)
Definition Elemaddr := Addr.

(** Alias definition : Dataaddr **)
Definition Dataaddr := Addr.

(** Alias definition : Labeladdr **)
Definition Labeladdr := Addr.

(** Alias definition : Hostaddr **)
Definition Hostaddr := Addr.

(** Inductive definition : Num **)
Inductive Num : Type :=
 | Num_CONST : (Numtype * C_numtype) -> Num
.

(** Inductive definition : Ref **)
Inductive Ref : Type :=
 | Ref_REF_NULL : Reftype -> Ref
 | Ref_REF_FUNC_ADDR : Funcaddr -> Ref
 | Ref_REF_HOST_ADDR : Hostaddr -> Ref
.

(** Inductive definition : Val **)
Inductive Val : Type :=
 | Val_CONST : (Numtype * C_numtype) -> Val
 | Val_REF_NULL : Reftype -> Val
 | Val_REF_FUNC_ADDR : Funcaddr -> Val
 | Val_REF_HOST_ADDR : Hostaddr -> Val
.

(** Inductive definition : Result **)
Inductive Result : Type :=
 | Result__VALS : (list Val) -> Result
 | Result_TRAP : Result
.

(** Inductive definition : Externval **)
Inductive Externval : Type :=
 | Externval_FUNC : Funcaddr -> Externval
 | Externval_GLOBAL : Globaladdr -> Externval
 | Externval_TABLE : Tableaddr -> Externval
 | Externval_MEM : Memaddr -> Externval
.

(** Function definition : fun_default_ **)
Definition fun_default_ (arg: Valtype) : (option Val) :=
  match arg with
  | Valtype_I32 => (Some (Val_CONST (Numtype_I32, 0)))
  | Valtype_I64 => (Some (Val_CONST (Numtype_I64, 0)))
  | Valtype_F32 => (Some (Val_CONST (Numtype_F32, 0)))
  | Valtype_F64 => (Some (Val_CONST (Numtype_F64, 0)))
  | Valtype_FUNCREF => (Some (Val_REF_NULL Reftype_FUNCREF))
  | Valtype_EXTERNREF => (Some (Val_REF_NULL Reftype_EXTERNREF))
  | x => None
end.

(** Notation definition : Exportinst **)
Definition Exportinst := (* mixop:  *) (Name * Externval).

(** Record definition : Moduleinst **)
Record Moduleinst : Type := {
  FUNC : (list Funcaddr);
  GLOBAL : (list Globaladdr);
  TABLE : (list Tableaddr);
  MEM : (list Memaddr);
  ELEM : (list Elemaddr);
  DATA : (list Dataaddr);
  EXPORT : (list Exportinst);
 } 
.

(** Notation definition : Funcinst **)
Definition Funcinst := (* mixop:  *) (Moduleinst * Func).

(** Alias definition : Globalinst **)
Definition Globalinst := Val.

(** Alias definition : Tableinst **)
Definition Tableinst := (list Ref).

(** Alias definition : Meminst **)
Definition Meminst := (list Byte).

(** Alias definition : Eleminst **)
Definition Eleminst := (list Ref).

(** Alias definition : Datainst **)
Definition Datainst := (list Byte).

(** Record definition : Store **)
Record Store : Type := {
  FUNC : (list Funcinst);
  GLOBAL : (list Globalinst);
  TABLE : (list Tableinst);
  MEM : (list Meminst);
  ELEM : (list Eleminst);
  DATA : (list Datainst);
 } 
.

(** Record definition : Frame **)
Record Frame : Type := {
  LOCAL : (list Val);
  MODULE : Moduleinst;
 } 
.

(** Notation definition : State **)
Definition State := (* mixop:  *) (Store * Frame).

(** Inductive definition : Admininstr **)
Inductive Admininstr : Type :=
 | Admininstr_UNREACHABLE : Admininstr
 | Admininstr_NOP : Admininstr
 | Admininstr_DROP : Admininstr
 | Admininstr_SELECT : (option Valtype) -> Admininstr
 | Admininstr_BLOCK : (Blocktype * (list Instr)) -> Admininstr
 | Admininstr_LOOP : (Blocktype * (list Instr)) -> Admininstr
 | Admininstr_IF : (Blocktype * (list Instr) * (list Instr)) -> Admininstr
 | Admininstr_BR : Labelidx -> Admininstr
 | Admininstr_BR_IF : Labelidx -> Admininstr
 | Admininstr_BR_TABLE : ((list Labelidx) * Labelidx) -> Admininstr
 | Admininstr_CALL : Funcidx -> Admininstr
 | Admininstr_CALL_INDIRECT : (Tableidx * Functype) -> Admininstr
 | Admininstr_RETURN : Admininstr
 | Admininstr_CONST : (Numtype * C_numtype) -> Admininstr
 | Admininstr_UNOP : (Numtype * Unop_numtype) -> Admininstr
 | Admininstr_BINOP : (Numtype * Binop_numtype) -> Admininstr
 | Admininstr_TESTOP : (Numtype * Testop_numtype) -> Admininstr
 | Admininstr_RELOP : (Numtype * Relop_numtype) -> Admininstr
 | Admininstr_EXTEND : (Numtype * N) -> Admininstr
 | Admininstr_CVTOP : (Numtype * Cvtop * Numtype * (option Sx)) -> Admininstr
 | Admininstr_REF_NULL : Reftype -> Admininstr
 | Admininstr_REF_FUNC : Funcidx -> Admininstr
 | Admininstr_REF_IS_NULL : Admininstr
 | Admininstr_LOCAL_GET : Localidx -> Admininstr
 | Admininstr_LOCAL_SET : Localidx -> Admininstr
 | Admininstr_LOCAL_TEE : Localidx -> Admininstr
 | Admininstr_GLOBAL_GET : Globalidx -> Admininstr
 | Admininstr_GLOBAL_SET : Globalidx -> Admininstr
 | Admininstr_TABLE_GET : Tableidx -> Admininstr
 | Admininstr_TABLE_SET : Tableidx -> Admininstr
 | Admininstr_TABLE_SIZE : Tableidx -> Admininstr
 | Admininstr_TABLE_GROW : Tableidx -> Admininstr
 | Admininstr_TABLE_FILL : Tableidx -> Admininstr
 | Admininstr_TABLE_COPY : (Tableidx * Tableidx) -> Admininstr
 | Admininstr_TABLE_INIT : (Tableidx * Elemidx) -> Admininstr
 | Admininstr_ELEM_DROP : Elemidx -> Admininstr
 | Admininstr_MEMORY_SIZE : Admininstr
 | Admininstr_MEMORY_GROW : Admininstr
 | Admininstr_MEMORY_FILL : Admininstr
 | Admininstr_MEMORY_COPY : Admininstr
 | Admininstr_MEMORY_INIT : Dataidx -> Admininstr
 | Admininstr_DATA_DROP : Dataidx -> Admininstr
 | Admininstr_LOAD : (Numtype * (option (N * Sx)) * nat * nat) -> Admininstr
 | Admininstr_STORE : (Numtype * (option N) * nat * nat) -> Admininstr
 | Admininstr_REF_FUNC_ADDR : Funcaddr -> Admininstr
 | Admininstr_REF_HOST_ADDR : Hostaddr -> Admininstr
 | Admininstr_CALL_ADDR : Funcaddr -> Admininstr
 | Admininstr_LABEL_ : (N * (list Instr) * (list Admininstr)) -> Admininstr
 | Admininstr_FRAME_ : (N * Frame * (list Admininstr)) -> Admininstr
 | Admininstr_TRAP : Admininstr
.

(** Function definition : fun_admininstr_globalinst **)
Definition fun_admininstr_globalinst (arg: Globalinst) : Admininstr :=
  match arg with
  | (Val_CONST x) => (Admininstr_CONST x)
  | (Val_REF_NULL x) => (Admininstr_REF_NULL x)
  | (Val_REF_FUNC_ADDR x) => (Admininstr_REF_FUNC_ADDR x)
  | (Val_REF_HOST_ADDR x) => (Admininstr_REF_HOST_ADDR x)
end.

(** Function definition : fun_admininstr_instr **)
Definition fun_admininstr_instr (arg: Instr) : Admininstr :=
  match arg with
  | Instr_UNREACHABLE => Admininstr_UNREACHABLE
  | Instr_NOP => Admininstr_NOP
  | Instr_DROP => Admininstr_DROP
  | (Instr_SELECT x) => (Admininstr_SELECT x)
  | (Instr_BLOCK x) => (Admininstr_BLOCK x)
  | (Instr_LOOP x) => (Admininstr_LOOP x)
  | (Instr_IF x) => (Admininstr_IF x)
  | (Instr_BR x) => (Admininstr_BR x)
  | (Instr_BR_IF x) => (Admininstr_BR_IF x)
  | (Instr_BR_TABLE x) => (Admininstr_BR_TABLE x)
  | (Instr_CALL x) => (Admininstr_CALL x)
  | (Instr_CALL_INDIRECT x) => (Admininstr_CALL_INDIRECT x)
  | Instr_RETURN => Admininstr_RETURN
  | (Instr_CONST x) => (Admininstr_CONST x)
  | (Instr_UNOP x) => (Admininstr_UNOP x)
  | (Instr_BINOP x) => (Admininstr_BINOP x)
  | (Instr_TESTOP x) => (Admininstr_TESTOP x)
  | (Instr_RELOP x) => (Admininstr_RELOP x)
  | (Instr_EXTEND x) => (Admininstr_EXTEND x)
  | (Instr_CVTOP x) => (Admininstr_CVTOP x)
  | (Instr_REF_NULL x) => (Admininstr_REF_NULL x)
  | (Instr_REF_FUNC x) => (Admininstr_REF_FUNC x)
  | Instr_REF_IS_NULL => Admininstr_REF_IS_NULL
  | (Instr_LOCAL_GET x) => (Admininstr_LOCAL_GET x)
  | (Instr_LOCAL_SET x) => (Admininstr_LOCAL_SET x)
  | (Instr_LOCAL_TEE x) => (Admininstr_LOCAL_TEE x)
  | (Instr_GLOBAL_GET x) => (Admininstr_GLOBAL_GET x)
  | (Instr_GLOBAL_SET x) => (Admininstr_GLOBAL_SET x)
  | (Instr_TABLE_GET x) => (Admininstr_TABLE_GET x)
  | (Instr_TABLE_SET x) => (Admininstr_TABLE_SET x)
  | (Instr_TABLE_SIZE x) => (Admininstr_TABLE_SIZE x)
  | (Instr_TABLE_GROW x) => (Admininstr_TABLE_GROW x)
  | (Instr_TABLE_FILL x) => (Admininstr_TABLE_FILL x)
  | (Instr_TABLE_COPY x) => (Admininstr_TABLE_COPY x)
  | (Instr_TABLE_INIT x) => (Admininstr_TABLE_INIT x)
  | (Instr_ELEM_DROP x) => (Admininstr_ELEM_DROP x)
  | Instr_MEMORY_SIZE => Admininstr_MEMORY_SIZE
  | Instr_MEMORY_GROW => Admininstr_MEMORY_GROW
  | Instr_MEMORY_FILL => Admininstr_MEMORY_FILL
  | Instr_MEMORY_COPY => Admininstr_MEMORY_COPY
  | (Instr_MEMORY_INIT x) => (Admininstr_MEMORY_INIT x)
  | (Instr_DATA_DROP x) => (Admininstr_DATA_DROP x)
  | (Instr_LOAD x) => (Admininstr_LOAD x)
  | (Instr_STORE x) => (Admininstr_STORE x)
end.

(** Function definition : fun_admininstr_ref **)
Definition fun_admininstr_ref (arg: Ref) : Admininstr :=
  match arg with
  | (Ref_REF_NULL x) => (Admininstr_REF_NULL x)
  | (Ref_REF_FUNC_ADDR x) => (Admininstr_REF_FUNC_ADDR x)
  | (Ref_REF_HOST_ADDR x) => (Admininstr_REF_HOST_ADDR x)
end.

(** Function definition : fun_admininstr_val **)
Definition fun_admininstr_val (arg: Val) : Admininstr :=
  match arg with
  | (Val_CONST x) => (Admininstr_CONST x)
  | (Val_REF_NULL x) => (Admininstr_REF_NULL x)
  | (Val_REF_FUNC_ADDR x) => (Admininstr_REF_FUNC_ADDR x)
  | (Val_REF_HOST_ADDR x) => (Admininstr_REF_HOST_ADDR x)
end.

(** Notation definition : Config **)
Definition Config := (* mixop:  *) (State * (list Admininstr)).

(** Function definition : fun_funcaddr **)
Definition fun_funcaddr (arg: State) : (list Funcaddr) :=
  match arg with
  | (s, f) => f.(MODULE).(FUNC)
end.

(** Function definition : fun_funcinst **)
Definition fun_funcinst (arg: State) : (list Funcinst) :=
  match arg with
  | (s, f) => s.(FUNC)
end.

(** Function definition : fun_func **)
Definition fun_func (arg: (State * Funcidx)) : Funcinst :=
  match arg with
  | ((s, f), x) => (List.nth_error s.(FUNC) (List.nth_error f.(MODULE).(FUNC) x))
end.

(** Function definition : fun_global **)
Definition fun_global (arg: (State * Globalidx)) : Globalinst :=
  match arg with
  | ((s, f), x) => (List.nth_error s.(GLOBAL) (List.nth_error f.(MODULE).(GLOBAL) x))
end.

(** Function definition : fun_table **)
Definition fun_table (arg: (State * Tableidx)) : Tableinst :=
  match arg with
  | ((s, f), x) => (List.nth_error s.(TABLE) (List.nth_error f.(MODULE).(TABLE) x))
end.

(** Function definition : fun_mem **)
Definition fun_mem (arg: (State * Memidx)) : Meminst :=
  match arg with
  | ((s, f), x) => (List.nth_error s.(MEM) (List.nth_error f.(MODULE).(MEM) x))
end.

(** Function definition : fun_elem **)
Definition fun_elem (arg: (State * Tableidx)) : Eleminst :=
  match arg with
  | ((s, f), x) => (List.nth_error s.(ELEM) (List.nth_error f.(MODULE).(ELEM) x))
end.

(** Function definition : fun_data **)
Definition fun_data (arg: (State * Dataidx)) : Datainst :=
  match arg with
  | ((s, f), x) => (List.nth_error s.(DATA) (List.nth_error f.(MODULE).(DATA) x))
end.

(** Function definition : fun_local **)
Definition fun_local (arg: (State * Localidx)) : Val :=
  match arg with
  | ((s, f), x) => (List.nth_error f.(LOCAL) x)
end.

(** Function definition : fun_with_local **)
Definition fun_with_local (arg: (State * Localidx * Val)) : State :=
  match arg with
  | ((s, f), x, v) => (s, {f with LOCAL := (list_update f.(LOCAL) x v) })
end.

(** Function definition : fun_with_global **)
Definition fun_with_global (arg: (State * Globalidx * Val)) : State :=
  match arg with
  | ((s, f), x, v) => ({s with GLOBAL := (list_update s.(GLOBAL) (List.nth_error f.(MODULE).(GLOBAL) x) v) }, f)
end.

(** Function definition : fun_with_table **)
Definition fun_with_table (arg: (State * Tableidx * N * Ref)) : State :=
  match arg with
  | ((s, f), x, i, r) => ({s with TABLE := (list_update s.(TABLE) (List.nth_error f.(MODULE).(TABLE) x) (list_update (List.nth_error s.(TABLE) (List.nth_error f.(MODULE).(TABLE) x)) i r)) }, f)
end.

(** Function definition : fun_with_tableext **)
Definition fun_with_tableext (arg: (State * Tableidx * (list Ref))) : State :=
  match arg with
  | ((s, f), x, r) => ({s with TABLE := (list_update s.(TABLE) (List.nth_error f.(MODULE).(TABLE) x) (List.append (List.nth_error s.(TABLE) (List.nth_error f.(MODULE).(TABLE) x)) r)) }, f)
end.

(** Function definition : fun_with_elem **)
Definition fun_with_elem (arg: (State * Elemidx * (list Ref))) : State :=
  match arg with
  | ((s, f), x, r) => ({s with TABLE := (list_update s.(TABLE) (List.nth_error f.(MODULE).(TABLE) x) r) }, f)
end.

(** Inductive definition : E **)
Inductive E : Type :=
 | E__HOLE : E
 | E__SEQ : ((list Val) * E * (list Instr)) -> E
 | E_LABEL_ : (N * (list Instr) * E) -> E
.

(** Function definition : fun_unop **)
Definition fun_unop (arg: (Unop_numtype * Numtype * C_numtype)) : (list C_numtype) :=
  match arg with := default.

(** Function definition : fun_binop **)
Definition fun_binop (arg: (Binop_numtype * Numtype * C_numtype * C_numtype)) : (list C_numtype) :=
  match arg with := default.

(** Function definition : fun_testop **)
Definition fun_testop (arg: (Testop_numtype * Numtype * C_numtype)) : C_numtype :=
  match arg with := default.

(** Function definition : fun_relop **)
Definition fun_relop (arg: (Relop_numtype * Numtype * C_numtype * C_numtype)) : C_numtype :=
  match arg with := default.

(** Function definition : fun_ext **)
Definition fun_ext (arg: (nat * nat * Sx * C_numtype)) : C_numtype :=
  match arg with := default.

(** Function definition : fun_cvtop **)
Definition fun_cvtop (arg: (Numtype * Cvtop * Numtype * (option Sx) * C_numtype)) : (list C_numtype) :=
  match arg with := default.

(** Relation definition : Step_pure_before_ref_is_null_false **)
Inductive Step_pure_before_ref_is_null_false : (list Admininstr) -> Prop := 
  | Step_pure_before_ref_is_null_false_ref_is_null_true (rt : Reftype) (val : Val) : 
    (val = (Val_REF_NULL rt)) -> 
    (Step_pure_before_ref_is_null_false [(fun_admininstr_val val); Admininstr_REF_IS_NULL])
.

(** Relation definition : Step_pure **)
Inductive Step_pure : ((list Admininstr) * (list Admininstr)) -> Prop := 
  | Step_pure_unreachable  : 
    (Step_pure ([Admininstr_UNREACHABLE], [Admininstr_TRAP]))
  | Step_pure_nop  : 
    (Step_pure ([Admininstr_NOP], nil))
  | Step_pure_drop (val : Val) : 
    (Step_pure ([(fun_admininstr_val val); Admininstr_DROP], nil))
  | Step_pure_select_true (c : C_numtype) (t : (option Valtype)) (val_1 : Val) (val_2 : Val) : 
    (c <> 0) -> 
    (Step_pure ([(fun_admininstr_val val_1); (fun_admininstr_val val_2); (Admininstr_CONST (Numtype_I32, c)); (Admininstr_SELECT t)], [(fun_admininstr_val val_1)]))
  | Step_pure_select_false (c : C_numtype) (t : (option Valtype)) (val_1 : Val) (val_2 : Val) : 
    (c = 0) -> 
    (Step_pure ([(fun_admininstr_val val_1); (fun_admininstr_val val_2); (Admininstr_CONST (Numtype_I32, c)); (Admininstr_SELECT t)], [(fun_admininstr_val val_2)]))
  | Step_pure_block (bt : Blocktype) (instr : (list Instr)) (k : nat) (n : N) (t_1 : (list Valtype)) (t_2 : (list Valtype)) (val : (list Val)) : 
    (List.length (t_1) = k) -> 
    (List.length (t_2) = n) -> 
    (List.length (val) = k) -> 
    (bt = (t_1, t_2)) -> 
    (Step_pure (((List.map fun_admininstr_val val) ++ [(Admininstr_BLOCK (bt, instr))]), [(Admininstr_LABEL_ (n, nil, ((List.map fun_admininstr_val val) ++ (List.map fun_admininstr_instr instr))))]))
  | Step_pure_loop (bt : Blocktype) (instr : (list Instr)) (k : nat) (n : N) (t_1 : (list Valtype)) (t_2 : (list Valtype)) (val : (list Val)) : 
    (List.length (t_1) = k) -> 
    (List.length (t_2) = n) -> 
    (List.length (val) = k) -> 
    (bt = (t_1, t_2)) -> 
    (Step_pure (((List.map fun_admininstr_val val) ++ [(Admininstr_LOOP (bt, instr))]), [(Admininstr_LABEL_ (n, [(Instr_LOOP (bt, instr))], ((List.map fun_admininstr_val val) ++ (List.map fun_admininstr_instr instr))))]))
  | Step_pure_if_true (bt : Blocktype) (c : C_numtype) (instr_1 : (list Instr)) (instr_2 : (list Instr)) : 
    (c <> 0) -> 
    (Step_pure ([(Admininstr_CONST (Numtype_I32, c)); (Admininstr_IF (bt, instr_1, instr_2))], [(Admininstr_BLOCK (bt, instr_1))]))
  | Step_pure_if_false (bt : Blocktype) (c : C_numtype) (instr_1 : (list Instr)) (instr_2 : (list Instr)) : 
    (c = 0) -> 
    (Step_pure ([(Admininstr_CONST (Numtype_I32, c)); (Admininstr_IF (bt, instr_1, instr_2))], [(Admininstr_BLOCK (bt, instr_2))]))
  | Step_pure_label_vals (instr : (list Instr)) (n : N) (val : (list Val)) : 
    (Step_pure ([(Admininstr_LABEL_ (n, instr, (List.map fun_admininstr_val val)))], (List.map fun_admininstr_val val)))
  | Step_pure_br_zero (instr : (list Instr)) (instr' : (list Instr)) (n : N) (val : (list Val)) (val' : (list Val)) : 
    (List.length (val) = n) -> 
    (Step_pure ([(Admininstr_LABEL_ (n, instr', ((List.map fun_admininstr_val val') ++ ((List.map fun_admininstr_val val) ++ ([(Admininstr_BR 0)] ++ (List.map fun_admininstr_instr instr))))))], ((List.map fun_admininstr_val val) ++ (List.map fun_admininstr_instr instr'))))
  | Step_pure_br_succ (instr : (list Instr)) (instr' : (list Instr)) (l : Labelidx) (n : N) (val : (list Val)) : 
    (Step_pure ([(Admininstr_LABEL_ (n, instr', ((List.map fun_admininstr_val val) ++ ([(Admininstr_BR (l + 1))] ++ (List.map fun_admininstr_instr instr)))))], ((List.map fun_admininstr_val val) ++ [(Admininstr_BR l)])))
  | Step_pure_br_if_true (c : C_numtype) (l : Labelidx) : 
    (c <> 0) -> 
    (Step_pure ([(Admininstr_CONST (Numtype_I32, c)); (Admininstr_BR_IF l)], [(Admininstr_BR l)]))
  | Step_pure_br_if_false (c : C_numtype) (l : Labelidx) : 
    (c = 0) -> 
    (Step_pure ([(Admininstr_CONST (Numtype_I32, c)); (Admininstr_BR_IF l)], nil))
  | Step_pure_br_table_lt (i : nat) (l : (list Labelidx)) (l' : Labelidx) : 
    (i < List.length (l)) -> 
    (Step_pure ([(Admininstr_CONST (Numtype_I32, i)); (Admininstr_BR_TABLE (l, l'))], [(Admininstr_BR (List.nth_error l i))]))
  | Step_pure_br_table_ge (i : nat) (l : (list Labelidx)) (l' : Labelidx) : 
    (i >= List.length (l)) -> 
    (Step_pure ([(Admininstr_CONST (Numtype_I32, i)); (Admininstr_BR_TABLE (l, l'))], [(Admininstr_BR l')]))
  | Step_pure_frame_vals (f : Frame) (n : N) (val : (list Val)) : 
    (List.length (val) = n) -> 
    (Step_pure ([(Admininstr_FRAME_ (n, f, (List.map fun_admininstr_val val)))], (List.map fun_admininstr_val val)))
  | Step_pure_return_frame (f : Frame) (instr : (list Instr)) (n : N) (val : (list Val)) (val' : (list Val)) : 
    (List.length (val) = n) -> 
    (Step_pure ([(Admininstr_FRAME_ (n, f, ((List.map fun_admininstr_val val') ++ ((List.map fun_admininstr_val val) ++ ([Admininstr_RETURN] ++ (List.map fun_admininstr_instr instr))))))], (List.map fun_admininstr_val val)))
  | Step_pure_return_label (instr : (list Instr)) (instr' : (list Instr)) (k : nat) (val : (list Val)) : 
    (Step_pure ([(Admininstr_LABEL_ (k, instr', ((List.map fun_admininstr_val val) ++ ([Admininstr_RETURN] ++ (List.map fun_admininstr_instr instr)))))], ((List.map fun_admininstr_val val) ++ [Admininstr_RETURN])))
  | Step_pure_unop_val (c : C_numtype) (c_1 : C_numtype) (nt : Numtype) (unop : Unop_numtype) : 
    ((fun_unop (unop, nt, c_1)) = [c]) -> 
    (Step_pure ([(Admininstr_CONST (nt, c_1)); (Admininstr_UNOP (nt, unop))], [(Admininstr_CONST (nt, c))]))
  | Step_pure_unop_trap (c_1 : C_numtype) (nt : Numtype) (unop : Unop_numtype) : 
    ((fun_unop (unop, nt, c_1)) = nil) -> 
    (Step_pure ([(Admininstr_CONST (nt, c_1)); (Admininstr_UNOP (nt, unop))], [Admininstr_TRAP]))
  | Step_pure_binop_val (binop : Binop_numtype) (c : C_numtype) (c_1 : C_numtype) (c_2 : C_numtype) (nt : Numtype) : 
    ((fun_binop (binop, nt, c_1, c_2)) = [c]) -> 
    (Step_pure ([(Admininstr_CONST (nt, c_1)); (Admininstr_CONST (nt, c_2)); (Admininstr_BINOP (nt, binop))], [(Admininstr_CONST (nt, c))]))
  | Step_pure_binop_trap (binop : Binop_numtype) (c_1 : C_numtype) (c_2 : C_numtype) (nt : Numtype) : 
    ((fun_binop (binop, nt, c_1, c_2)) = nil) -> 
    (Step_pure ([(Admininstr_CONST (nt, c_1)); (Admininstr_CONST (nt, c_2)); (Admininstr_BINOP (nt, binop))], [Admininstr_TRAP]))
  | Step_pure_testop (c : C_numtype) (c_1 : C_numtype) (nt : Numtype) (testop : Testop_numtype) : 
    (c = (fun_testop (testop, nt, c_1))) -> 
    (Step_pure ([(Admininstr_CONST (nt, c_1)); (Admininstr_TESTOP (nt, testop))], [(Admininstr_CONST (Numtype_I32, c))]))
  | Step_pure_relop (c : C_numtype) (c_1 : C_numtype) (c_2 : C_numtype) (nt : Numtype) (relop : Relop_numtype) : 
    (c = (fun_relop (relop, nt, c_1, c_2))) -> 
    (Step_pure ([(Admininstr_CONST (nt, c_1)); (Admininstr_CONST (nt, c_2)); (Admininstr_RELOP (nt, relop))], [(Admininstr_CONST (Numtype_I32, c))]))
  | Step_pure_extend (c : C_numtype) (n : N) (nt : Numtype) (o0 : nat) : 
    ((fun_size (fun_valtype_numtype nt)) = (Some o0)) -> 
    (Step_pure ([(Admininstr_CONST (nt, c)); (Admininstr_EXTEND (nt, n))], [(Admininstr_CONST (nt, (fun_ext (n, o0, Sx_S, c))))]))
  | Step_pure_cvtop_val (c : C_numtype) (c_1 : C_numtype) (cvtop : Cvtop) (nt : Numtype) (nt_1 : Numtype) (nt_2 : Numtype) (sx : (option Sx)) : 
    ((fun_cvtop (nt_1, cvtop, nt_2, sx, c_1)) = [c]) -> 
    (Step_pure ([(Admininstr_CONST (nt, c_1)); (Admininstr_CVTOP (nt_1, cvtop, nt_2, sx))], [(Admininstr_CONST (nt, c))]))
  | Step_pure_cvtop_trap (c_1 : C_numtype) (cvtop : Cvtop) (nt : Numtype) (nt_1 : Numtype) (nt_2 : Numtype) (sx : (option Sx)) : 
    ((fun_cvtop (nt_1, cvtop, nt_2, sx, c_1)) = nil) -> 
    (Step_pure ([(Admininstr_CONST (nt, c_1)); (Admininstr_CVTOP (nt_1, cvtop, nt_2, sx))], [Admininstr_TRAP]))
  | Step_pure_ref_is_null_true (rt : Reftype) (val : Val) : 
    (val = (Val_REF_NULL rt)) -> 
    (Step_pure ([(fun_admininstr_val val); Admininstr_REF_IS_NULL], [(Admininstr_CONST (Numtype_I32, 1))]))
  | Step_pure_ref_is_null_false (val : Val) : 
    (Not (Step_pure_before_ref_is_null_false [(fun_admininstr_val val); Admininstr_REF_IS_NULL])) -> 
    (Step_pure ([(fun_admininstr_val val); Admininstr_REF_IS_NULL], [(Admininstr_CONST (Numtype_I32, 0))]))
  | Step_pure_local_tee (val : Val) (x : Idx) : 
    (Step_pure ([(fun_admininstr_val val); (Admininstr_LOCAL_TEE x)], [(fun_admininstr_val val); (fun_admininstr_val val); (Admininstr_LOCAL_SET x)]))
.

(** Relation definition : Step_read_before_call_indirect_trap **)
Inductive Step_read_before_call_indirect_trap : Config -> Prop := 
  | Step_read_before_call_indirect_trap_call_indirect_call (a : Addr) (ft : Functype) (func : Func) (i : nat) (m : Moduleinst) (x : Idx) (z : State) : 
    (i < List.length ((fun_table (z, x)))) -> 
    (a < List.length ((fun_funcinst z))) -> 
    ((List.nth_error (fun_table (z, x)) i) = Some (Ref_REF_FUNC_ADDR a)) -> 
    ((List.nth_error (fun_funcinst z) a) = Some (m, func)) -> 
    (Step_read_before_call_indirect_trap (z, [(Admininstr_CONST (Numtype_I32, i)); (Admininstr_CALL_INDIRECT (x, ft))]))
.

(** Relation definition : Step_read_before_table_fill_zero **)
Inductive Step_read_before_table_fill_zero : Config -> Prop := 
  | Step_read_before_table_fill_zero_table_fill_trap (i : nat) (n : N) (val : Val) (x : Idx) (z : State) : 
    ((i + n) > List.length ((fun_table (z, x)))) -> 
    (Step_read_before_table_fill_zero (z, [(Admininstr_CONST (Numtype_I32, i)); (fun_admininstr_val val); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_FILL x)]))
.

(** Relation definition : Step_read_before_table_fill_succ **)
Inductive Step_read_before_table_fill_succ : Config -> Prop := 
  | Step_read_before_table_fill_succ_table_fill_zero (i : nat) (n : N) (val : Val) (x : Idx) (z : State) : 
    (Not (Step_read_before_table_fill_zero (z, [(Admininstr_CONST (Numtype_I32, i)); (fun_admininstr_val val); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_FILL x)]))) -> 
    (n = 0) -> 
    (Step_read_before_table_fill_succ (z, [(Admininstr_CONST (Numtype_I32, i)); (fun_admininstr_val val); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_FILL x)]))
  | Step_read_before_table_fill_succ_table_fill_trap (i : nat) (n : N) (val : Val) (x : Idx) (z : State) : 
    ((i + n) > List.length ((fun_table (z, x)))) -> 
    (Step_read_before_table_fill_succ (z, [(Admininstr_CONST (Numtype_I32, i)); (fun_admininstr_val val); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_FILL x)]))
.

(** Relation definition : Step_read_before_table_copy_zero **)
Inductive Step_read_before_table_copy_zero : Config -> Prop := 
  | Step_read_before_table_copy_zero_table_copy_trap (i : nat) (j : nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_table (z, y)))) \/ ((j + n) > List.length ((fun_table (z, x))))) -> 
    (Step_read_before_table_copy_zero (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_COPY (x, y))]))
.

(** Relation definition : Step_read_before_table_copy_le **)
Inductive Step_read_before_table_copy_le : Config -> Prop := 
  | Step_read_before_table_copy_le_table_copy_zero (i : nat) (j : nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (Not (Step_read_before_table_copy_zero (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_COPY (x, y))]))) -> 
    (n = 0) -> 
    (Step_read_before_table_copy_le (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_COPY (x, y))]))
  | Step_read_before_table_copy_le_table_copy_trap (i : nat) (j : nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_table (z, y)))) \/ ((j + n) > List.length ((fun_table (z, x))))) -> 
    (Step_read_before_table_copy_le (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_COPY (x, y))]))
.

(** Relation definition : Step_read_before_table_copy_gt **)
Inductive Step_read_before_table_copy_gt : Config -> Prop := 
  | Step_read_before_table_copy_gt_table_copy_le (i : nat) (j : nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (Not (Step_read_before_table_copy_le (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_COPY (x, y))]))) -> 
    (j <= i) -> 
    (Step_read_before_table_copy_gt (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_COPY (x, y))]))
  | Step_read_before_table_copy_gt_table_copy_zero (i : nat) (j : nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (Not (Step_read_before_table_copy_zero (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_COPY (x, y))]))) -> 
    (n = 0) -> 
    (Step_read_before_table_copy_gt (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_COPY (x, y))]))
  | Step_read_before_table_copy_gt_table_copy_trap (i : nat) (j : nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_table (z, y)))) \/ ((j + n) > List.length ((fun_table (z, x))))) -> 
    (Step_read_before_table_copy_gt (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_COPY (x, y))]))
.

(** Relation definition : Step_read_before_table_init_zero **)
Inductive Step_read_before_table_init_zero : Config -> Prop := 
  | Step_read_before_table_init_zero_table_init_trap (i : nat) (j : nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_elem (z, y)))) \/ ((j + n) > List.length ((fun_table (z, x))))) -> 
    (Step_read_before_table_init_zero (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_INIT (x, y))]))
.

(** Relation definition : Step_read_before_table_init_succ **)
Inductive Step_read_before_table_init_succ : Config -> Prop := 
  | Step_read_before_table_init_succ_table_init_zero (i : nat) (j : nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (Not (Step_read_before_table_init_zero (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_INIT (x, y))]))) -> 
    (n = 0) -> 
    (Step_read_before_table_init_succ (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_INIT (x, y))]))
  | Step_read_before_table_init_succ_table_init_trap (i : nat) (j : nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_elem (z, y)))) \/ ((j + n) > List.length ((fun_table (z, x))))) -> 
    (Step_read_before_table_init_succ (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_INIT (x, y))]))
.

(** Relation definition : Step_read **)
Inductive Step_read : (Config * (list Admininstr)) -> Prop := 
  | Step_read_call (x : Idx) (z : State) : 
    (x < List.length ((fun_funcaddr z))) -> 
    (Step_read ((z, [(Admininstr_CALL x)]), [(Admininstr_CALL_ADDR (List.nth_error (fun_funcaddr z) x))]))
  | Step_read_call_indirect_call (a : Addr) (ft : Functype) (func : Func) (i : nat) (m : Moduleinst) (x : Idx) (z : State) : 
    (i < List.length ((fun_table (z, x)))) -> 
    (a < List.length ((fun_funcinst z))) -> 
    ((List.nth_error (fun_table (z, x)) i) = Some (Ref_REF_FUNC_ADDR a)) -> 
    ((List.nth_error (fun_funcinst z) a) = Some (m, func)) -> 
    (Step_read ((z, [(Admininstr_CONST (Numtype_I32, i)); (Admininstr_CALL_INDIRECT (x, ft))]), [(Admininstr_CALL_ADDR a)]))
  | Step_read_call_indirect_trap (ft : Functype) (i : nat) (x : Idx) (z : State) : 
    (Not (Step_read_before_call_indirect_trap (z, [(Admininstr_CONST (Numtype_I32, i)); (Admininstr_CALL_INDIRECT (x, ft))]))) -> 
    (Step_read ((z, [(Admininstr_CONST (Numtype_I32, i)); (Admininstr_CALL_INDIRECT (x, ft))]), [Admininstr_TRAP]))
  | Step_read_call_addr (a : Addr) (f : Frame) (instr : (list Instr)) (k : nat) (m : Moduleinst) (n : N) (t : (list Valtype)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) (val : (list Val)) (z : State) (o0 : (list Val)) : 
    (List.length (t) = List.length (o0)) -> 
    (a < List.length ((fun_funcinst z))) -> 
    (List.length (t_1) = k) -> 
    (List.length (t_2) = n) -> 
    (List.length (val) = k) -> 
    (List.Forall2 (fun t o0 => ((fun_default_ t) = (Some o0))) t o0) -> 
    ((List.nth_error (fun_funcinst z) a) = Some (m, ((t_1, t_2), t, instr))) -> 
    (f = {|LOCAL := (val ++ o0); MODULE := m|}) -> 
    (Step_read ((z, ((List.map fun_admininstr_val val) ++ [(Admininstr_CALL_ADDR a)])), [(Admininstr_FRAME_ (n, f, [(Admininstr_LABEL_ (n, nil, (List.map fun_admininstr_instr instr)))]))]))
  | Step_read_ref_func (x : Idx) (z : State) : 
    (x < List.length ((fun_funcaddr z))) -> 
    (Step_read ((z, [(Admininstr_REF_FUNC x)]), [(Admininstr_REF_FUNC_ADDR (List.nth_error (fun_funcaddr z) x))]))
  | Step_read_local_get (x : Idx) (z : State) : 
    (Step_read ((z, [(Admininstr_LOCAL_GET x)]), [(fun_admininstr_val (fun_local (z, x)))]))
  | Step_read_global_get (x : Idx) (z : State) : 
    (Step_read ((z, [(Admininstr_GLOBAL_GET x)]), [(fun_admininstr_globalinst (fun_global (z, x)))]))
  | Step_read_table_get_trap (i : nat) (x : Idx) (z : State) : 
    (i >= List.length ((fun_table (z, x)))) -> 
    (Step_read ((z, [(Admininstr_CONST (Numtype_I32, i)); (Admininstr_TABLE_GET x)]), [Admininstr_TRAP]))
  | Step_read_table_get_val (i : nat) (x : Idx) (z : State) : 
    (i < List.length ((fun_table (z, x)))) -> 
    (Step_read ((z, [(Admininstr_CONST (Numtype_I32, i)); (Admininstr_TABLE_GET x)]), [(fun_admininstr_ref (List.nth_error (fun_table (z, x)) i))]))
  | Step_read_table_set_trap (i : nat) (ref : Ref) (x : Idx) (z : State) : 
    (i >= List.length ((fun_table (z, x)))) -> 
    (Step_read ((z, [(Admininstr_CONST (Numtype_I32, i)); (fun_admininstr_ref ref); (Admininstr_TABLE_GET x)]), [Admininstr_TRAP]))
  | Step_read_table_size (n : N) (x : Idx) (z : State) : 
    (List.length ((fun_table (z, x))) = n) -> 
    (Step_read ((z, [(Admininstr_TABLE_SIZE x)]), [(Admininstr_CONST (Numtype_I32, n))]))
  | Step_read_table_grow_fail (n : N) (x : Idx) (z : State) : 
    (Step_read ((z, [(Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_GROW x)]), [(Admininstr_CONST (Numtype_I32, (0 - 1)))]))
  | Step_read_table_fill_trap (i : nat) (n : N) (val : Val) (x : Idx) (z : State) : 
    ((i + n) > List.length ((fun_table (z, x)))) -> 
    (Step_read ((z, [(Admininstr_CONST (Numtype_I32, i)); (fun_admininstr_val val); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_FILL x)]), [Admininstr_TRAP]))
  | Step_read_table_fill_zero (i : nat) (n : N) (val : Val) (x : Idx) (z : State) : 
    (Not (Step_read_before_table_fill_zero (z, [(Admininstr_CONST (Numtype_I32, i)); (fun_admininstr_val val); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_FILL x)]))) -> 
    (n = 0) -> 
    (Step_read ((z, [(Admininstr_CONST (Numtype_I32, i)); (fun_admininstr_val val); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_FILL x)]), nil))
  | Step_read_table_fill_succ (i : nat) (n : N) (val : Val) (x : Idx) (z : State) : 
    (Not (Step_read_before_table_fill_succ (z, [(Admininstr_CONST (Numtype_I32, i)); (fun_admininstr_val val); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_FILL x)]))) -> 
    (Step_read ((z, [(Admininstr_CONST (Numtype_I32, i)); (fun_admininstr_val val); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_FILL x)]), [(Admininstr_CONST (Numtype_I32, i)); (fun_admininstr_val val); (Admininstr_TABLE_SET x); (Admininstr_CONST (Numtype_I32, (i + 1))); (fun_admininstr_val val); (Admininstr_CONST (Numtype_I32, (n - 1))); (Admininstr_TABLE_FILL x)]))
  | Step_read_table_copy_trap (i : nat) (j : nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_table (z, y)))) \/ ((j + n) > List.length ((fun_table (z, x))))) -> 
    (Step_read ((z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_COPY (x, y))]), [Admininstr_TRAP]))
  | Step_read_table_copy_zero (i : nat) (j : nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (Not (Step_read_before_table_copy_zero (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_COPY (x, y))]))) -> 
    (n = 0) -> 
    (Step_read ((z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_COPY (x, y))]), nil))
  | Step_read_table_copy_le (i : nat) (j : nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (Not (Step_read_before_table_copy_le (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_COPY (x, y))]))) -> 
    (j <= i) -> 
    (Step_read ((z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_COPY (x, y))]), [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_TABLE_GET y); (Admininstr_TABLE_SET x); (Admininstr_CONST (Numtype_I32, (j + 1))); (Admininstr_CONST (Numtype_I32, (i + 1))); (Admininstr_CONST (Numtype_I32, (n - 1))); (Admininstr_TABLE_COPY (x, y))]))
  | Step_read_table_copy_gt (i : nat) (j : nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (Not (Step_read_before_table_copy_gt (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_COPY (x, y))]))) -> 
    (Step_read ((z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_COPY (x, y))]), [(Admininstr_CONST (Numtype_I32, ((j + n) - 1))); (Admininstr_CONST (Numtype_I32, ((i + n) - 1))); (Admininstr_TABLE_GET y); (Admininstr_TABLE_SET x); (Admininstr_CONST (Numtype_I32, (j + 1))); (Admininstr_CONST (Numtype_I32, (i + 1))); (Admininstr_CONST (Numtype_I32, (n - 1))); (Admininstr_TABLE_COPY (x, y))]))
  | Step_read_table_init_trap (i : nat) (j : nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_elem (z, y)))) \/ ((j + n) > List.length ((fun_table (z, x))))) -> 
    (Step_read ((z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_INIT (x, y))]), [Admininstr_TRAP]))
  | Step_read_table_init_zero (i : nat) (j : nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (Not (Step_read_before_table_init_zero (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_INIT (x, y))]))) -> 
    (n = 0) -> 
    (Step_read ((z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_INIT (x, y))]), nil))
  | Step_read_table_init_succ (i : nat) (j : nat) (n : N) (x : Idx) (y : Idx) (z : State) : 
    (i < List.length ((fun_elem (z, y)))) -> 
    (Not (Step_read_before_table_init_succ (z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_INIT (x, y))]))) -> 
    (Step_read ((z, [(Admininstr_CONST (Numtype_I32, j)); (Admininstr_CONST (Numtype_I32, i)); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_INIT (x, y))]), [(Admininstr_CONST (Numtype_I32, j)); (fun_admininstr_ref (List.nth_error (fun_elem (z, y)) i)); (Admininstr_TABLE_SET x); (Admininstr_CONST (Numtype_I32, (j + 1))); (Admininstr_CONST (Numtype_I32, (i + 1))); (Admininstr_CONST (Numtype_I32, (n - 1))); (Admininstr_TABLE_INIT (x, y))]))
.

(** Relation definition : Step **)
Inductive Step : (Config * Config) -> Prop := 
  | Step_pure (instr : (list Instr)) (instr' : (list Instr)) (z : State) : 
    (Step_pure ((List.map fun_admininstr_instr instr), (List.map fun_admininstr_instr instr'))) -> 
    (Step ((z, (List.map fun_admininstr_instr instr)), (z, (List.map fun_admininstr_instr instr'))))
  | Step_read (instr : (list Instr)) (instr' : (list Instr)) (z : State) : 
    (Step_read ((z, (List.map fun_admininstr_instr instr)), (List.map fun_admininstr_instr instr'))) -> 
    (Step ((z, (List.map fun_admininstr_instr instr)), (z, (List.map fun_admininstr_instr instr'))))
  | Step_local_set (val : Val) (x : Idx) (z : State) : 
    (Step ((z, [(fun_admininstr_val val); (Admininstr_LOCAL_SET x)]), ((fun_with_local (z, x, val)), nil)))
  | Step_global_set (val : Val) (x : Idx) (z : State) : 
    (Step ((z, [(fun_admininstr_val val); (Admininstr_GLOBAL_SET x)]), ((fun_with_global (z, x, val)), nil)))
  | Step_table_set_val (i : nat) (ref : Ref) (x : Idx) (z : State) : 
    (i < List.length ((fun_table (z, x)))) -> 
    (Step ((z, [(Admininstr_CONST (Numtype_I32, i)); (fun_admininstr_ref ref); (Admininstr_TABLE_GET x)]), ((fun_with_table (z, x, i, ref)), nil)))
  | Step_table_grow_succeed (n : N) (ref : Ref) (x : Idx) (z : State) : 
    (Step ((z, [(fun_admininstr_ref ref); (Admininstr_CONST (Numtype_I32, n)); (Admininstr_TABLE_GROW x)]), ((fun_with_tableext (z, x, [ref])), [(Admininstr_CONST (Numtype_I32, List.length ((fun_table (z, x)))))])))
  | Step_elem_drop (x : Idx) (z : State) : 
    (Step ((z, [(Admininstr_ELEM_DROP x)]), ((fun_with_elem (z, x, nil)), nil)))
.
