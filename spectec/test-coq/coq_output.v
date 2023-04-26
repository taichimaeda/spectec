(* Coq export *)

From Coq Require Import String List Unicode.Utf8.
Require Import NArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** * Auxiliary definitions **)

Declare Scope wasm_scope.

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

Class Append (α: Type) := _append : α -> α -> α.

Infix "++" := _append (right associativity, at level 60) : wasm_scope.

Global Instance Append_List_ {α: Type}: Append (list α) := { _append l1 l2 := List.app l1 l2 }.

Definition option_append {α: Type} (x y: option α) : option α :=
 match x with
  | Some _ => x
  | None => y
end.

Global Instance Append_Option {α: Type}: Append (option α) := { _append o1 o2 := option_append o1 o2 }.

Fixpoint list_update {α: Type} (l: list α) (n: nat) (y: α): list α :=
match l, n with
  | nil, _=> nil
  | x :: l', 0 => y :: l'
  | x :: l', S n => x :: list_update l' n y
end.

Class Inhabited (T: Type) := { default_val : T }.

Definition lookup_total {T: Type} {_: Inhabited T} (l: list T) (n: nat) : T :=
  List.nth n l default_val.

Global Instance Inh_unit : Inhabited unit := { default_val := tt }.

Global Instance Inh_nat : Inhabited nat := { default_val := O }.

Global Instance Inh_list {T: Type} : Inhabited (list T) := { default_val := nil }.

Global Instance Inh_option {T: Type} : Inhabited (option T) := { default_val := None }.

Global Instance Inh_prod {T1 T2: Type} {_: Inhabited T1} {_: Inhabited T2} : Inhabited (prod T1 T2) := { default_val := (default_val, default_val) }.

Open Scope wasm_scope.
Import ListNotations.

(** * Generated code **)

(** Alias definition : reserved__N **)
Definition reserved__N := nat.

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

(** Variant definition : Numtype **)
Inductive Numtype : Type :=
 | Numtype__I32 : Numtype
 | Numtype__I64 : Numtype
 | Numtype__F32 : Numtype
 | Numtype__F64 : Numtype
.
Global Instance Inhabited_Numtype : Inhabited Numtype := { default_val := Numtype__I32 }.

(** Variant definition : Vectype **)
Inductive Vectype : Type :=
 | Vectype__V128 : Vectype
.
Global Instance Inhabited_Vectype : Inhabited Vectype := { default_val := Vectype__V128 }.

(** Variant definition : Reftype **)
Inductive Reftype : Type :=
 | Reftype__FUNCREF : Reftype
 | Reftype__EXTERNREF : Reftype
.
Global Instance Inhabited_Reftype : Inhabited Reftype := { default_val := Reftype__FUNCREF }.

(** Variant definition : Valtype **)
Inductive Valtype : Type :=
 | Valtype__I32 : Valtype
 | Valtype__I64 : Valtype
 | Valtype__F32 : Valtype
 | Valtype__F64 : Valtype
 | Valtype__V128 : Valtype
 | Valtype__FUNCREF : Valtype
 | Valtype__EXTERNREF : Valtype
 | Valtype__BOT : Valtype
.
Global Instance Inhabited_Valtype : Inhabited Valtype := { default_val := Valtype__I32 }.

(** Function definition : fun_valtype_numtype **)
(* Dependencies:  *)
Definition fun_valtype_numtype (arg: Numtype) : Valtype :=
  match arg with
  | Numtype__I32 => Valtype__I32
  | Numtype__I64 => Valtype__I64
  | Numtype__F32 => Valtype__F32
  | Numtype__F64 => Valtype__F64
end.

(** Function definition : fun_valtype_reftype **)
(* Dependencies:  *)
Definition fun_valtype_reftype (arg: Reftype) : Valtype :=
  match arg with
  | Reftype__FUNCREF => Valtype__FUNCREF
  | Reftype__EXTERNREF => Valtype__EXTERNREF
end.

(** Function definition : fun_valtype_vectype **)
(* Dependencies:  *)
Definition fun_valtype_vectype (arg: Vectype) : Valtype :=
  match arg with
  | Vectype__V128 => Valtype__V128
end.

(** Variant definition : reserved__In **)
Inductive reserved__In : Type :=
 | reserved__In__I32 : reserved__In
 | reserved__In__I64 : reserved__In
.
Global Instance Inhabited_reserved__In : Inhabited reserved__In := { default_val := reserved__In__I32 }.

(** Function definition : fun_numtype_in **)
(* Dependencies:  *)
Definition fun_numtype_in (arg: reserved__In) : Numtype :=
  match arg with
  | reserved__In__I32 => Numtype__I32
  | reserved__In__I64 => Numtype__I64
end.

(** Function definition : fun_valtype_in **)
(* Dependencies:  *)
Definition fun_valtype_in (arg: reserved__In) : Valtype :=
  match arg with
  | reserved__In__I32 => Valtype__I32
  | reserved__In__I64 => Valtype__I64
end.

(** Variant definition : Fn **)
Inductive Fn : Type :=
 | Fn__F32 : Fn
 | Fn__F64 : Fn
.
Global Instance Inhabited_Fn : Inhabited Fn := { default_val := Fn__F32 }.

(** Function definition : fun_numtype_fn **)
(* Dependencies:  *)
Definition fun_numtype_fn (arg: Fn) : Numtype :=
  match arg with
  | Fn__F32 => Numtype__F32
  | Fn__F64 => Numtype__F64
end.

(** Function definition : fun_valtype_fn **)
(* Dependencies:  *)
Definition fun_valtype_fn (arg: Fn) : Valtype :=
  match arg with
  | Fn__F32 => Valtype__F32
  | Fn__F64 => Valtype__F64
end.

(** Alias definition : Resulttype **)
Definition Resulttype := (list Valtype).

(** Notation definition : Limits **)
Definition Limits := (* mixop:  *) (U32 * U32)%type.

(** Notation definition : Mutflag **)
Definition Mutflag := (* mixop:  *) unit.

(** Notation definition : Globaltype **)
Definition Globaltype := (* mixop:  *) ((option Mutflag) * Valtype)%type.

(** Notation definition : Functype **)
Definition Functype := (* mixop:  *) (Resulttype * Resulttype)%type.

(** Notation definition : Tabletype **)
Definition Tabletype := (* mixop:  *) (Limits * Reftype)%type.

(** Notation definition : Memtype **)
Definition Memtype := (* mixop:  *) Limits.

(** Alias definition : Elemtype **)
Definition Elemtype := Reftype.

(** Notation definition : Datatype **)
Definition Datatype := (* mixop:  *) unit.

(** Variant definition : Externtype **)
Inductive Externtype : Type :=
 | Externtype__GLOBAL : Globaltype -> Externtype
 | Externtype__FUNC : Functype -> Externtype
 | Externtype__TABLE : Tabletype -> Externtype
 | Externtype__MEMORY : Memtype -> Externtype
.
Global Instance Inhabited_Externtype : Inhabited Externtype(* FIXME: no inhabitant found! *) .
  Admitted.

(** Variant definition : Sx **)
Inductive Sx : Type :=
 | Sx__U : Sx
 | Sx__S : Sx
.
Global Instance Inhabited_Sx : Inhabited Sx := { default_val := Sx__U }.

(** Variant definition : Unop_IXX **)
Inductive Unop_IXX : Type :=
 | Unop_IXX__CLZ : Unop_IXX
 | Unop_IXX__CTZ : Unop_IXX
 | Unop_IXX__POPCNT : Unop_IXX
.
Global Instance Inhabited_Unop_IXX : Inhabited Unop_IXX := { default_val := Unop_IXX__CLZ }.

(** Variant definition : Unop_FXX **)
Inductive Unop_FXX : Type :=
 | Unop_FXX__ABS : Unop_FXX
 | Unop_FXX__NEG : Unop_FXX
 | Unop_FXX__SQRT : Unop_FXX
 | Unop_FXX__CEIL : Unop_FXX
 | Unop_FXX__FLOOR : Unop_FXX
 | Unop_FXX__TRUNC : Unop_FXX
 | Unop_FXX__NEAREST : Unop_FXX
.
Global Instance Inhabited_Unop_FXX : Inhabited Unop_FXX := { default_val := Unop_FXX__ABS }.

(** Variant definition : Binop_IXX **)
Inductive Binop_IXX : Type :=
 | Binop_IXX__ADD : Binop_IXX
 | Binop_IXX__SUB : Binop_IXX
 | Binop_IXX__MUL : Binop_IXX
 | Binop_IXX__DIV : Sx -> Binop_IXX
 | Binop_IXX__REM : Sx -> Binop_IXX
 | Binop_IXX__AND : Binop_IXX
 | Binop_IXX__OR : Binop_IXX
 | Binop_IXX__XOR : Binop_IXX
 | Binop_IXX__SHL : Binop_IXX
 | Binop_IXX__SHR : Sx -> Binop_IXX
 | Binop_IXX__ROTL : Binop_IXX
 | Binop_IXX__ROTR : Binop_IXX
.
Global Instance Inhabited_Binop_IXX : Inhabited Binop_IXX := { default_val := Binop_IXX__ADD }.

(** Variant definition : Binop_FXX **)
Inductive Binop_FXX : Type :=
 | Binop_FXX__ADD : Binop_FXX
 | Binop_FXX__SUB : Binop_FXX
 | Binop_FXX__MUL : Binop_FXX
 | Binop_FXX__DIV : Binop_FXX
 | Binop_FXX__MIN : Binop_FXX
 | Binop_FXX__MAX : Binop_FXX
 | Binop_FXX__COPYSIGN : Binop_FXX
.
Global Instance Inhabited_Binop_FXX : Inhabited Binop_FXX := { default_val := Binop_FXX__ADD }.

(** Variant definition : Testop_IXX **)
Inductive Testop_IXX : Type :=
 | Testop_IXX__EQZ : Testop_IXX
.
Global Instance Inhabited_Testop_IXX : Inhabited Testop_IXX := { default_val := Testop_IXX__EQZ }.

(** Variant definition : Testop_FXX **)
Inductive Testop_FXX : Type :=
.
Global Instance Inhabited_Testop_FXX : Inhabited Testop_FXX(* FIXME: no inhabitant found! *) .
  Admitted.

(** Variant definition : Relop_IXX **)
Inductive Relop_IXX : Type :=
 | Relop_IXX__EQ : Relop_IXX
 | Relop_IXX__NE : Relop_IXX
 | Relop_IXX__LT : Sx -> Relop_IXX
 | Relop_IXX__GT : Sx -> Relop_IXX
 | Relop_IXX__LE : Sx -> Relop_IXX
 | Relop_IXX__GE : Sx -> Relop_IXX
.
Global Instance Inhabited_Relop_IXX : Inhabited Relop_IXX := { default_val := Relop_IXX__EQ }.

(** Variant definition : Relop_FXX **)
Inductive Relop_FXX : Type :=
 | Relop_FXX__EQ : Relop_FXX
 | Relop_FXX__NE : Relop_FXX
 | Relop_FXX__LT : Relop_FXX
 | Relop_FXX__GT : Relop_FXX
 | Relop_FXX__LE : Relop_FXX
 | Relop_FXX__GE : Relop_FXX
.
Global Instance Inhabited_Relop_FXX : Inhabited Relop_FXX := { default_val := Relop_FXX__EQ }.

(** Variant definition : Unop_numtype **)
Inductive Unop_numtype : Type :=
 | Unop_numtype___I : Unop_IXX -> Unop_numtype
 | Unop_numtype___F : Unop_FXX -> Unop_numtype
.
Global Instance Inhabited_Unop_numtype : Inhabited Unop_numtype(* FIXME: no inhabitant found! *) .
  Admitted.

(** Variant definition : Binop_numtype **)
Inductive Binop_numtype : Type :=
 | Binop_numtype___I : Binop_IXX -> Binop_numtype
 | Binop_numtype___F : Binop_FXX -> Binop_numtype
.
Global Instance Inhabited_Binop_numtype : Inhabited Binop_numtype(* FIXME: no inhabitant found! *) .
  Admitted.

(** Variant definition : Testop_numtype **)
Inductive Testop_numtype : Type :=
 | Testop_numtype___I : Testop_IXX -> Testop_numtype
 | Testop_numtype___F : Testop_FXX -> Testop_numtype
.
Global Instance Inhabited_Testop_numtype : Inhabited Testop_numtype(* FIXME: no inhabitant found! *) .
  Admitted.

(** Variant definition : Relop_numtype **)
Inductive Relop_numtype : Type :=
 | Relop_numtype___I : Relop_IXX -> Relop_numtype
 | Relop_numtype___F : Relop_FXX -> Relop_numtype
.
Global Instance Inhabited_Relop_numtype : Inhabited Relop_numtype(* FIXME: no inhabitant found! *) .
  Admitted.

(** Variant definition : Cvtop **)
Inductive Cvtop : Type :=
 | Cvtop__CONVERT : Cvtop
 | Cvtop__REINTERPRET : Cvtop
.
Global Instance Inhabited_Cvtop : Inhabited Cvtop := { default_val := Cvtop__CONVERT }.

(** Alias definition : C_numtype **)
Definition C_numtype := nat.

(** Alias definition : C_vectype **)
Definition C_vectype := nat.

(** Alias definition : Blocktype **)
Definition Blocktype := Functype.

(** Variant definition : Instr **)
Inductive Instr : Type :=
 | Instr__UNREACHABLE : Instr
 | Instr__NOP : Instr
 | Instr__DROP : Instr
 | Instr__SELECT : (option Valtype) -> Instr
 | Instr__BLOCK : (Blocktype * (list Instr))%type -> Instr
 | Instr__LOOP : (Blocktype * (list Instr))%type -> Instr
 | Instr__IF : (Blocktype * (list Instr) * (list Instr))%type -> Instr
 | Instr__BR : Labelidx -> Instr
 | Instr__BR_IF : Labelidx -> Instr
 | Instr__BR_TABLE : ((list Labelidx) * Labelidx)%type -> Instr
 | Instr__CALL : Funcidx -> Instr
 | Instr__CALL_INDIRECT : (Tableidx * Functype)%type -> Instr
 | Instr__RETURN : Instr
 | Instr__CONST : (Numtype * C_numtype)%type -> Instr
 | Instr__UNOP : (Numtype * Unop_numtype)%type -> Instr
 | Instr__BINOP : (Numtype * Binop_numtype)%type -> Instr
 | Instr__TESTOP : (Numtype * Testop_numtype)%type -> Instr
 | Instr__RELOP : (Numtype * Relop_numtype)%type -> Instr
 | Instr__EXTEND : (Numtype * reserved__N)%type -> Instr
 | Instr__CVTOP : (Numtype * Cvtop * Numtype * (option Sx))%type -> Instr
 | Instr__REF_NULL : Reftype -> Instr
 | Instr__REF_FUNC : Funcidx -> Instr
 | Instr__REF_IS_NULL : Instr
 | Instr__LOCAL_GET : Localidx -> Instr
 | Instr__LOCAL_SET : Localidx -> Instr
 | Instr__LOCAL_TEE : Localidx -> Instr
 | Instr__GLOBAL_GET : Globalidx -> Instr
 | Instr__GLOBAL_SET : Globalidx -> Instr
 | Instr__TABLE_GET : Tableidx -> Instr
 | Instr__TABLE_SET : Tableidx -> Instr
 | Instr__TABLE_SIZE : Tableidx -> Instr
 | Instr__TABLE_GROW : Tableidx -> Instr
 | Instr__TABLE_FILL : Tableidx -> Instr
 | Instr__TABLE_COPY : (Tableidx * Tableidx)%type -> Instr
 | Instr__TABLE_INIT : (Tableidx * Elemidx)%type -> Instr
 | Instr__ELEM_DROP : Elemidx -> Instr
 | Instr__MEMORY_SIZE : Instr
 | Instr__MEMORY_GROW : Instr
 | Instr__MEMORY_FILL : Instr
 | Instr__MEMORY_COPY : Instr
 | Instr__MEMORY_INIT : Dataidx -> Instr
 | Instr__DATA_DROP : Dataidx -> Instr
 | Instr__LOAD : (Numtype * (option (reserved__N * Sx)%type) * U32 * U32)%type -> Instr
 | Instr__STORE : (Numtype * (option reserved__N) * U32 * U32)%type -> Instr
.
Global Instance Inhabited_Instr : Inhabited Instr := { default_val := Instr__UNREACHABLE }.

(** Alias definition : Expr **)
Definition Expr := (list Instr).

(** Variant definition : Elemmode **)
Inductive Elemmode : Type :=
 | Elemmode__TABLE : (Tableidx * Expr)%type -> Elemmode
 | Elemmode__DECLARE : Elemmode
.
Global Instance Inhabited_Elemmode : Inhabited Elemmode := { default_val := Elemmode__DECLARE }.

(** Variant definition : Datamode **)
Inductive Datamode : Type :=
 | Datamode__MEMORY : (Memidx * Expr)%type -> Datamode
.
Global Instance Inhabited_Datamode : Inhabited Datamode(* FIXME: no inhabitant found! *) .
  Admitted.

(** Notation definition : Func **)
Definition Func := (* mixop:  *) (Functype * (list Valtype) * Expr)%type.

(** Notation definition : Global **)
Definition Global := (* mixop:  *) (Globaltype * Expr)%type.

(** Notation definition : Table **)
Definition Table := (* mixop:  *) Tabletype.

(** Notation definition : Mem **)
Definition Mem := (* mixop:  *) Memtype.

(** Notation definition : Elem **)
Definition Elem := (* mixop:  *) (Reftype * (list Expr) * (option Elemmode))%type.

(** Notation definition : Data **)
Definition Data := (* mixop:  *) ((list (list Byte)) * (option Datamode))%type.

(** Notation definition : Start **)
Definition Start := (* mixop:  *) Funcidx.

(** Variant definition : Externuse **)
Inductive Externuse : Type :=
 | Externuse__FUNC : Funcidx -> Externuse
 | Externuse__GLOBAL : Globalidx -> Externuse
 | Externuse__TABLE : Tableidx -> Externuse
 | Externuse__MEMORY : Memidx -> Externuse
.
Global Instance Inhabited_Externuse : Inhabited Externuse(* FIXME: no inhabitant found! *) .
  Admitted.

(** Notation definition : reserved__Export **)
Definition reserved__Export := (* mixop:  *) (Name * Externuse)%type.

(** Notation definition : reserved__Import **)
Definition reserved__Import := (* mixop:  *) (Name * Name * Externtype)%type.

(** Notation definition : Module **)
Definition Module := (* mixop:  *) ((list reserved__Import) * (list Func) * (list Global) * (list Table) * (list Mem) * (list Elem) * (list Data) * (list Start) * (list reserved__Export))%type.

(** Function definition : fun_Ki **)
(* Dependencies:  *)
Definition fun_Ki (arg: unit) : nat :=
  match arg with
  | tt => 1024
end.

(** Function definition : fun_min **)
(* Dependencies: min *)
Fixpoint fun_min (arg: (nat * nat)%type) : nat.
(* FIXME: Generated fixpoint definitions are fragile and may not directly pass the termination check. The following code is an attempt at rendering:
  := match arg with
  | (0, j) => 0
  | (i, 0) => 0
  | ((S (i)), (S (j))) => (fun_min (i, j))
end *)
Admitted.

(** Function definition : fun_size **)
(* Dependencies:  *)
Definition fun_size (arg: Valtype) : (option nat) :=
  match arg with
  | Valtype__I32 => (Some 32)
  | Valtype__I64 => (Some 64)
  | Valtype__F32 => (Some 32)
  | Valtype__F64 => (Some 64)
  | Valtype__V128 => (Some 128)
  | x => None
end.

(** Function definition : fun_test_sub_ATOM_22 **)
(* Dependencies:  *)
Definition fun_test_sub_ATOM_22 (arg: reserved__N) : nat :=
  match arg with
  | n_3_ATOM_y => 0
end.

(** Function definition : fun_curried_ **)
(* Dependencies:  *)
Definition fun_curried_ (arg: (reserved__N * reserved__N)%type) : nat :=
  match arg with
  | (n_1, n_2) => (n_1 + n_2)
end.

(** Variant definition : Testfuse **)
Inductive Testfuse : Type :=
 | Testfuse__AB_ : (nat * nat * nat)%type -> Testfuse
 | Testfuse__CD : (nat * nat * nat)%type -> Testfuse
 | Testfuse__EF : (nat * nat * nat)%type -> Testfuse
 | Testfuse__GH : (nat * nat * nat)%type -> Testfuse
 | Testfuse__IJ : (nat * nat * nat)%type -> Testfuse
 | Testfuse__KL : (nat * nat * nat)%type -> Testfuse
 | Testfuse__MN : (nat * nat * nat)%type -> Testfuse
 | Testfuse__OP : (nat * nat * nat)%type -> Testfuse
 | Testfuse__QR : (nat * nat * nat)%type -> Testfuse
.
Global Instance Inhabited_Testfuse : Inhabited Testfuse(* FIXME: no inhabitant found! *) .
  Admitted.

(** Record definition : Context **)
Record Context : Type := {
  Context__FUNC : (list Functype);
  Context__GLOBAL : (list Globaltype);
  Context__TABLE : (list Tabletype);
  Context__MEM : (list Memtype);
  Context__ELEM : (list Elemtype);
  Context__DATA : (list Datatype);
  Context__LOCAL : (list Valtype);
  Context__LABEL : (list Resulttype);
  Context__RETURN : (option Resulttype);
 }. 

Global Instance Inhabited_Context : Inhabited Context.
(* TODO: add automatic record inhabitance proof *)
Admitted.

Definition _append_Context (r1 r2: Context) : Context :=
{|
  Context__FUNC := r1.(Context__FUNC) ++ r2.(Context__FUNC);
  Context__GLOBAL := r1.(Context__GLOBAL) ++ r2.(Context__GLOBAL);
  Context__TABLE := r1.(Context__TABLE) ++ r2.(Context__TABLE);
  Context__MEM := r1.(Context__MEM) ++ r2.(Context__MEM);
  Context__ELEM := r1.(Context__ELEM) ++ r2.(Context__ELEM);
  Context__DATA := r1.(Context__DATA) ++ r2.(Context__DATA);
  Context__LOCAL := r1.(Context__LOCAL) ++ r2.(Context__LOCAL);
  Context__LABEL := r1.(Context__LABEL) ++ r2.(Context__LABEL);
  Context__RETURN := r1.(Context__RETURN) ++ r2.(Context__RETURN);
|}. 

Global Instance Append_Context : Append Context := { _append arg1 arg2 := _append_Context arg1 arg2 }.

(** Relation definition : Limits_ok **)
Inductive Limits_ok : (Limits * nat)%type -> Prop := 
  | Limits_ok__rule_0 (k : nat) (n_1 : reserved__N) (n_2 : reserved__N) : 
    ((n_1 <= n_2) /\ (n_2 <= k)) -> 
    (Limits_ok ((n_1, n_2), k))
.

(** Relation definition : Functype_ok **)
Inductive Functype_ok : Functype -> Prop := 
  | Functype_ok__rule_0 (ft : Functype) : 
    (Functype_ok ft)
.

(** Relation definition : Globaltype_ok **)
Inductive Globaltype_ok : Globaltype -> Prop := 
  | Globaltype_ok__rule_0 (gt : Globaltype) : 
    (Globaltype_ok gt)
.

(** Relation definition : Tabletype_ok **)
Inductive Tabletype_ok : Tabletype -> Prop := 
  | Tabletype_ok__rule_0 (lim : Limits) (rt : Reftype) : 
    (Limits_ok (lim, ((((Nat.pow 2) 32)) - 1))) -> 
    (Tabletype_ok (lim, rt))
.

(** Relation definition : Memtype_ok **)
Inductive Memtype_ok : Memtype -> Prop := 
  | Memtype_ok__rule_0 (lim : Limits) : 
    (Limits_ok (lim, (((Nat.pow 2) 16)))) -> 
    (Memtype_ok lim)
.

(** Relation definition : Externtype_ok **)
Inductive Externtype_ok : Externtype -> Prop := 
  | Externtype_ok__func (functype : Functype) : 
    (Functype_ok functype) -> 
    (Externtype_ok (Externtype__FUNC functype))
  | Externtype_ok__global (globaltype : Globaltype) : 
    (Globaltype_ok globaltype) -> 
    (Externtype_ok (Externtype__GLOBAL globaltype))
  | Externtype_ok__table (tabletype : Tabletype) : 
    (Tabletype_ok tabletype) -> 
    (Externtype_ok (Externtype__TABLE tabletype))
  | Externtype_ok__mem (memtype : Memtype) : 
    (Memtype_ok memtype) -> 
    (Externtype_ok (Externtype__MEMORY memtype))
.

(** Relation definition : Valtype_sub **)
Inductive Valtype_sub : (Valtype * Valtype)%type -> Prop := 
  | Valtype_sub__refl (t : Valtype) : 
    (Valtype_sub (t, t))
  | Valtype_sub__bot (t : Valtype) : 
    (Valtype_sub (Valtype__BOT, t))
.

(** Relation definition : Resulttype_sub **)
Inductive Resulttype_sub : ((list Valtype) * (list Valtype))%type -> Prop := 
  | Resulttype_sub__rule_0 (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (List.length (t_1) = List.length (t_2)) -> 
    (List.Forall2 (fun t_1 t_2 => (Valtype_sub (t_1, t_2))) t_1 t_2) -> 
    (Resulttype_sub (t_1, t_2))
.

(** Relation definition : Limits_sub **)
Inductive Limits_sub : (Limits * Limits)%type -> Prop := 
  | Limits_sub__rule_0 (n_11 : reserved__N) (n_12 : reserved__N) (n_21 : reserved__N) (n_22 : reserved__N) : 
    (n_11 >= n_21) -> 
    (n_12 <= n_22) -> 
    (Limits_sub ((n_11, n_12), (n_21, n_22)))
.

(** Relation definition : Functype_sub **)
Inductive Functype_sub : (Functype * Functype)%type -> Prop := 
  | Functype_sub__rule_0 (ft : Functype) : 
    (Functype_sub (ft, ft))
.

(** Relation definition : Globaltype_sub **)
Inductive Globaltype_sub : (Globaltype * Globaltype)%type -> Prop := 
  | Globaltype_sub__rule_0 (gt : Globaltype) : 
    (Globaltype_sub (gt, gt))
.

(** Relation definition : Tabletype_sub **)
Inductive Tabletype_sub : (Tabletype * Tabletype)%type -> Prop := 
  | Tabletype_sub__rule_0 (lim_1 : Limits) (lim_2 : Limits) (rt : Reftype) : 
    (Limits_sub (lim_1, lim_2)) -> 
    (Tabletype_sub ((lim_1, rt), (lim_2, rt)))
.

(** Relation definition : Memtype_sub **)
Inductive Memtype_sub : (Memtype * Memtype)%type -> Prop := 
  | Memtype_sub__rule_0 (lim_1 : Limits) (lim_2 : Limits) : 
    (Limits_sub (lim_1, lim_2)) -> 
    (Memtype_sub (lim_1, lim_2))
.

(** Relation definition : Externtype_sub **)
Inductive Externtype_sub : (Externtype * Externtype)%type -> Prop := 
  | Externtype_sub__func (ft_1 : Functype) (ft_2 : Functype) : 
    (Functype_sub (ft_1, ft_2)) -> 
    (Externtype_sub ((Externtype__FUNC ft_1), (Externtype__FUNC ft_2)))
  | Externtype_sub__global (gt_1 : Globaltype) (gt_2 : Globaltype) : 
    (Globaltype_sub (gt_1, gt_2)) -> 
    (Externtype_sub ((Externtype__GLOBAL gt_1), (Externtype__GLOBAL gt_2)))
  | Externtype_sub__table (tt_1 : Tabletype) (tt_2 : Tabletype) : 
    (Tabletype_sub (tt_1, tt_2)) -> 
    (Externtype_sub ((Externtype__TABLE tt_1), (Externtype__TABLE tt_2)))
  | Externtype_sub__mem (mt_1 : Memtype) (mt_2 : Memtype) : 
    (Memtype_sub (mt_1, mt_2)) -> 
    (Externtype_sub ((Externtype__MEMORY mt_1), (Externtype__MEMORY mt_2)))
.

(** Relation definition : Blocktype_ok **)
Inductive Blocktype_ok : (Context * Blocktype * Functype)%type -> Prop := 
  | Blocktype_ok__rule_0 (C : Context) (ft : Functype) : 
    (Functype_ok ft) -> 
    (Blocktype_ok (C, ft, ft))
.

(** Relation definition : Instr_ok **)
Inductive Instr_ok : (Context * Instr * Functype)%type -> Prop := 
  | Instr_ok__unreachable (C : Context) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (Instr_ok (C, Instr__UNREACHABLE, (t_1, t_2)))
  | Instr_ok__nop (C : Context) : 
    (Instr_ok (C, Instr__NOP, (nil, nil)))
  | Instr_ok__drop (C : Context) (t : Valtype) : 
    (Instr_ok (C, Instr__DROP, ([t], nil)))
  | Instr_ok__select_expl (C : Context) (t : Valtype) : 
    (Instr_ok (C, (Instr__SELECT (Some t)), ([t; t; Valtype__I32], [t])))
  | Instr_ok__select_impl (C : Context) (numtype : Numtype) (t : Valtype) (t' : Valtype) (vectype : Vectype) : 
    (Valtype_sub (t, t')) -> 
    ((t' = (fun_valtype_numtype numtype)) \/ (t' = (fun_valtype_vectype vectype))) -> 
    (Instr_ok (C, (Instr__SELECT None), ([t; t; Valtype__I32], [t])))
  | Instr_ok__block (C : Context) (bt : Blocktype) (instr : (list Instr)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (Blocktype_ok (C, bt, (t_1, t_2))) -> 
    (InstrSeq_ok (({| Context__FUNC := nil; Context__GLOBAL := nil; Context__TABLE := nil; Context__MEM := nil; Context__ELEM := nil; Context__DATA := nil; Context__LOCAL := nil; Context__LABEL := (List.map (fun t_2 => [t_2]) t_2); Context__RETURN := None |} ++ C), instr, (t_1, t_2))) -> 
    (Instr_ok (C, (Instr__BLOCK (bt, instr)), (t_1, t_2)))
  | Instr_ok__loop (C : Context) (bt : Blocktype) (instr : (list Instr)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (Blocktype_ok (C, bt, (t_1, t_2))) -> 
    (InstrSeq_ok (({| Context__FUNC := nil; Context__GLOBAL := nil; Context__TABLE := nil; Context__MEM := nil; Context__ELEM := nil; Context__DATA := nil; Context__LOCAL := nil; Context__LABEL := (List.map (fun t_1 => [t_1]) t_1); Context__RETURN := None |} ++ C), instr, (t_1, t_2))) -> 
    (Instr_ok (C, (Instr__LOOP (bt, instr)), (t_1, t_2)))
  | Instr_ok__if (C : Context) (bt : Blocktype) (instr_1 : (list Instr)) (instr_2 : (list Instr)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (Blocktype_ok (C, bt, (t_1, t_2))) -> 
    (InstrSeq_ok (({| Context__FUNC := nil; Context__GLOBAL := nil; Context__TABLE := nil; Context__MEM := nil; Context__ELEM := nil; Context__DATA := nil; Context__LOCAL := nil; Context__LABEL := (List.map (fun t_2 => [t_2]) t_2); Context__RETURN := None |} ++ C), instr_1, (t_1, t_2))) -> 
    (InstrSeq_ok (({| Context__FUNC := nil; Context__GLOBAL := nil; Context__TABLE := nil; Context__MEM := nil; Context__ELEM := nil; Context__DATA := nil; Context__LOCAL := nil; Context__LABEL := (List.map (fun t_2 => [t_2]) t_2); Context__RETURN := None |} ++ C), instr_2, (t_1, t_2))) -> 
    (Instr_ok (C, (Instr__IF (bt, instr_1, instr_2)), (t_1, t_2)))
  | Instr_ok__br (C : Context) (l : Labelidx) (t : (list Valtype)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (l < List.length (C.(Context__LABEL))) -> 
    ((lookup_total C.(Context__LABEL) l) = t) -> 
    (Instr_ok (C, (Instr__BR l), ((t_1 ++ t), t_2)))
  | Instr_ok__br_if (C : Context) (l : Labelidx) (t : (list Valtype)) : 
    (l < List.length (C.(Context__LABEL))) -> 
    ((lookup_total C.(Context__LABEL) l) = t) -> 
    (Instr_ok (C, (Instr__BR_IF l), ((t ++ [Valtype__I32]), t)))
  | Instr_ok__br_table (C : Context) (l : (list Labelidx)) (l' : Labelidx) (t : (list Valtype)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (List.Forall (fun l => (l < List.length (C.(Context__LABEL)))) l) -> 
    (l' < List.length (C.(Context__LABEL))) -> 
    (List.Forall (fun l => (Resulttype_sub (t, (lookup_total C.(Context__LABEL) l)))) l) -> 
    (Resulttype_sub (t, (lookup_total C.(Context__LABEL) l'))) -> 
    (Instr_ok (C, (Instr__BR_TABLE (l, l')), ((t_1 ++ t), t_2)))
  | Instr_ok__return (C : Context) (t : (list Valtype)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (C.(Context__RETURN) = (Some t)) -> 
    (Instr_ok (C, Instr__RETURN, ((t_1 ++ t), t_2)))
  | Instr_ok__call (C : Context) (t_1 : (list Valtype)) (t_2 : (list Valtype)) (x : Idx) : 
    (x < List.length (C.(Context__FUNC))) -> 
    ((lookup_total C.(Context__FUNC) x) = (t_1, t_2)) -> 
    (Instr_ok (C, (Instr__CALL x), (t_1, t_2)))
  | Instr_ok__call_indirect (C : Context) (ft : Functype) (lim : Limits) (t_1 : (list Valtype)) (t_2 : (list Valtype)) (x : Idx) : 
    (x < List.length (C.(Context__TABLE))) -> 
    ((lookup_total C.(Context__TABLE) x) = (lim, Reftype__FUNCREF)) -> 
    (ft = (t_1, t_2)) -> 
    (Instr_ok (C, (Instr__CALL_INDIRECT (x, ft)), ((t_1 ++ [Valtype__I32]), t_2)))
  | Instr_ok__const (C : Context) (c_nt : C_numtype) (nt : Numtype) : 
    (Instr_ok (C, (Instr__CONST (nt, c_nt)), (nil, [(fun_valtype_numtype nt)])))
  | Instr_ok__unop (C : Context) (nt : Numtype) (unop : Unop_numtype) : 
    (Instr_ok (C, (Instr__UNOP (nt, unop)), ([(fun_valtype_numtype nt)], [(fun_valtype_numtype nt)])))
  | Instr_ok__binop (C : Context) (binop : Binop_numtype) (nt : Numtype) : 
    (Instr_ok (C, (Instr__BINOP (nt, binop)), ([(fun_valtype_numtype nt); (fun_valtype_numtype nt)], [(fun_valtype_numtype nt)])))
  | Instr_ok__testop (C : Context) (nt : Numtype) (testop : Testop_numtype) : 
    (Instr_ok (C, (Instr__TESTOP (nt, testop)), ([(fun_valtype_numtype nt)], [Valtype__I32])))
  | Instr_ok__relop (C : Context) (nt : Numtype) (relop : Relop_numtype) : 
    (Instr_ok (C, (Instr__RELOP (nt, relop)), ([(fun_valtype_numtype nt); (fun_valtype_numtype nt)], [Valtype__I32])))
  | Instr_ok__extend (C : Context) (n : reserved__N) (nt : Numtype) (o0 : nat) : 
    ((fun_size (fun_valtype_numtype nt)) = (Some o0)) -> 
    (n <= o0) -> 
    (Instr_ok (C, (Instr__EXTEND (nt, n)), ([(fun_valtype_numtype nt)], [(fun_valtype_numtype nt)])))
  | Instr_ok__reinterpret (C : Context) (nt_1 : Numtype) (nt_2 : Numtype) (o0 : nat) (o1 : nat) : 
    ((fun_size (fun_valtype_numtype nt_1)) = (Some o0)) -> 
    ((fun_size (fun_valtype_numtype nt_2)) = (Some o1)) -> 
    (nt_1 <> nt_2) -> 
    (o0 = o1) -> 
    (Instr_ok (C, (Instr__CVTOP (nt_1, Cvtop__REINTERPRET, nt_2, None)), ([(fun_valtype_numtype nt_2)], [(fun_valtype_numtype nt_1)])))
  | Instr_ok__convert_i (C : Context) (in_1 : reserved__In) (in_2 : reserved__In) (sx : (option Sx)) (o0 : nat) (o1 : nat) : 
    ((fun_size (fun_valtype_in in_1)) = (Some o0)) -> 
    ((fun_size (fun_valtype_in in_2)) = (Some o1)) -> 
    (in_1 <> in_2) -> 
    ((sx = None) = (o0 > o1)) -> 
    (Instr_ok (C, (Instr__CVTOP ((fun_numtype_in in_1), Cvtop__CONVERT, (fun_numtype_in in_2), sx)), ([(fun_valtype_in in_2)], [(fun_valtype_in in_1)])))
  | Instr_ok__convert_f (C : Context) (fn_1 : Fn) (fn_2 : Fn) : 
    (fn_1 <> fn_2) -> 
    (Instr_ok (C, (Instr__CVTOP ((fun_numtype_fn fn_1), Cvtop__CONVERT, (fun_numtype_fn fn_2), None)), ([(fun_valtype_fn fn_2)], [(fun_valtype_fn fn_1)])))
  | Instr_ok__ref_null (C : Context) (rt : Reftype) : 
    (Instr_ok (C, (Instr__REF_NULL rt), (nil, [(fun_valtype_reftype rt)])))
  | Instr_ok__ref_func (C : Context) (ft : Functype) (x : Idx) : 
    (x < List.length (C.(Context__FUNC))) -> 
    ((lookup_total C.(Context__FUNC) x) = ft) -> 
    (Instr_ok (C, (Instr__REF_FUNC x), (nil, [Valtype__FUNCREF])))
  | Instr_ok__ref_is_null (C : Context) (rt : Reftype) : 
    (Instr_ok (C, Instr__REF_IS_NULL, ([(fun_valtype_reftype rt)], [Valtype__I32])))
  | Instr_ok__local_get (C : Context) (t : Valtype) (x : Idx) : 
    (x < List.length (C.(Context__LOCAL))) -> 
    ((lookup_total C.(Context__LOCAL) x) = t) -> 
    (Instr_ok (C, (Instr__LOCAL_GET x), (nil, [t])))
  | Instr_ok__local_set (C : Context) (t : Valtype) (x : Idx) : 
    (x < List.length (C.(Context__LOCAL))) -> 
    ((lookup_total C.(Context__LOCAL) x) = t) -> 
    (Instr_ok (C, (Instr__LOCAL_SET x), ([t], nil)))
  | Instr_ok__local_tee (C : Context) (t : Valtype) (x : Idx) : 
    (x < List.length (C.(Context__LOCAL))) -> 
    ((lookup_total C.(Context__LOCAL) x) = t) -> 
    (Instr_ok (C, (Instr__LOCAL_TEE x), ([t], [t])))
  | Instr_ok__global_get (C : Context) (mut : (option Mutflag)) (t : Valtype) (x : Idx) : 
    (x < List.length (C.(Context__GLOBAL))) -> 
    ((lookup_total C.(Context__GLOBAL) x) = (mut, t)) -> 
    (Instr_ok (C, (Instr__GLOBAL_GET x), (nil, [t])))
  | Instr_ok__global_set (C : Context) (t : Valtype) (x : Idx) : 
    (x < List.length (C.(Context__GLOBAL))) -> 
    ((lookup_total C.(Context__GLOBAL) x) = ((Some tt), t)) -> 
    (Instr_ok (C, (Instr__GLOBAL_SET x), ([t], nil)))
  | Instr_ok__table_get (C : Context) (lim : Limits) (rt : Reftype) (x : Idx) : 
    (x < List.length (C.(Context__TABLE))) -> 
    ((lookup_total C.(Context__TABLE) x) = (lim, rt)) -> 
    (Instr_ok (C, (Instr__TABLE_GET x), ([Valtype__I32], [(fun_valtype_reftype rt)])))
  | Instr_ok__table_set (C : Context) (lim : Limits) (rt : Reftype) (x : Idx) : 
    (x < List.length (C.(Context__TABLE))) -> 
    ((lookup_total C.(Context__TABLE) x) = (lim, rt)) -> 
    (Instr_ok (C, (Instr__TABLE_SET x), ([Valtype__I32; (fun_valtype_reftype rt)], nil)))
  | Instr_ok__table_size (C : Context) (reserved__tt : Tabletype) (x : Idx) : 
    (x < List.length (C.(Context__TABLE))) -> 
    ((lookup_total C.(Context__TABLE) x) = reserved__tt) -> 
    (Instr_ok (C, (Instr__TABLE_SIZE x), (nil, [Valtype__I32])))
  | Instr_ok__table_grow (C : Context) (lim : Limits) (rt : Reftype) (x : Idx) : 
    (x < List.length (C.(Context__TABLE))) -> 
    ((lookup_total C.(Context__TABLE) x) = (lim, rt)) -> 
    (Instr_ok (C, (Instr__TABLE_GROW x), ([(fun_valtype_reftype rt); Valtype__I32], [Valtype__I32])))
  | Instr_ok__table_fill (C : Context) (lim : Limits) (rt : Reftype) (x : Idx) : 
    (x < List.length (C.(Context__TABLE))) -> 
    ((lookup_total C.(Context__TABLE) x) = (lim, rt)) -> 
    (Instr_ok (C, (Instr__TABLE_FILL x), ([Valtype__I32; (fun_valtype_reftype rt); Valtype__I32], nil)))
  | Instr_ok__table_copy (C : Context) (lim_1 : Limits) (lim_2 : Limits) (rt : Reftype) (x_1 : Idx) (x_2 : Idx) : 
    (x_1 < List.length (C.(Context__TABLE))) -> 
    (x_2 < List.length (C.(Context__TABLE))) -> 
    ((lookup_total C.(Context__TABLE) x_1) = (lim_1, rt)) -> 
    ((lookup_total C.(Context__TABLE) x_2) = (lim_2, rt)) -> 
    (Instr_ok (C, (Instr__TABLE_COPY (x_1, x_2)), ([Valtype__I32; Valtype__I32; Valtype__I32], nil)))
  | Instr_ok__table_init (C : Context) (lim : Limits) (rt : Reftype) (x_1 : Idx) (x_2 : Idx) : 
    (x_1 < List.length (C.(Context__TABLE))) -> 
    (x_2 < List.length (C.(Context__ELEM))) -> 
    ((lookup_total C.(Context__TABLE) x_1) = (lim, rt)) -> 
    ((lookup_total C.(Context__ELEM) x_2) = rt) -> 
    (Instr_ok (C, (Instr__TABLE_INIT (x_1, x_2)), ([Valtype__I32; Valtype__I32; Valtype__I32], nil)))
  | Instr_ok__elem_drop (C : Context) (rt : Reftype) (x : Idx) : 
    (x < List.length (C.(Context__ELEM))) -> 
    ((lookup_total C.(Context__ELEM) x) = rt) -> 
    (Instr_ok (C, (Instr__ELEM_DROP x), (nil, nil)))
  | Instr_ok__memory_size (C : Context) (mt : Memtype) : 
    (0 < List.length (C.(Context__MEM))) -> 
    ((lookup_total C.(Context__MEM) 0) = mt) -> 
    (Instr_ok (C, Instr__MEMORY_SIZE, (nil, [Valtype__I32])))
  | Instr_ok__memory_grow (C : Context) (mt : Memtype) : 
    (0 < List.length (C.(Context__MEM))) -> 
    ((lookup_total C.(Context__MEM) 0) = mt) -> 
    (Instr_ok (C, Instr__MEMORY_GROW, ([Valtype__I32], [Valtype__I32])))
  | Instr_ok__memory_fill (C : Context) (mt : Memtype) : 
    (0 < List.length (C.(Context__MEM))) -> 
    ((lookup_total C.(Context__MEM) 0) = mt) -> 
    (Instr_ok (C, Instr__MEMORY_FILL, ([Valtype__I32; Valtype__I32; Valtype__I32], [Valtype__I32])))
  | Instr_ok__memory_copy (C : Context) (mt : Memtype) : 
    (0 < List.length (C.(Context__MEM))) -> 
    ((lookup_total C.(Context__MEM) 0) = mt) -> 
    (Instr_ok (C, Instr__MEMORY_COPY, ([Valtype__I32; Valtype__I32; Valtype__I32], [Valtype__I32])))
  | Instr_ok__memory_init (C : Context) (mt : Memtype) (x : Idx) : 
    (0 < List.length (C.(Context__MEM))) -> 
    (x < List.length (C.(Context__DATA))) -> 
    ((lookup_total C.(Context__MEM) 0) = mt) -> 
    ((lookup_total C.(Context__DATA) x) = tt) -> 
    (Instr_ok (C, (Instr__MEMORY_INIT x), ([Valtype__I32; Valtype__I32; Valtype__I32], [Valtype__I32])))
  | Instr_ok__data_drop (C : Context) (x : Idx) : 
    (x < List.length (C.(Context__DATA))) -> 
    ((lookup_total C.(Context__DATA) x) = tt) -> 
    (Instr_ok (C, (Instr__DATA_DROP x), (nil, nil)))
  | Instr_ok__load (C : Context) (reserved__in : reserved__In) (mt : Memtype) (n : (option reserved__N)) (n_A : reserved__N) (n_O : reserved__N) (nt : Numtype) (sx : (option Sx)) (o0 : nat) (o1 : (option nat)) : 
    (0 < List.length (C.(Context__MEM))) -> 
    ((n = None) = (o1 = None)) -> 
    ((n = None) = (sx = None)) -> 
    ((fun_size (fun_valtype_numtype nt)) = (Some o0)) -> 
    (List.Forall (fun o1 => ((fun_size (fun_valtype_numtype nt)) = (Some o1))) (option_to_list o1)) -> 
    ((lookup_total C.(Context__MEM) 0) = mt) -> 
    ((((Nat.pow 2) n_A)) <= (((Nat.div o0) 8))) -> 
    (List.Forall2 (fun n o1 => (((((Nat.pow 2) n_A)) <= (((Nat.div n) 8))) /\ ((((Nat.div n) 8)) < (((Nat.div o1) 8))))) (option_to_list n) (option_to_list o1)) -> 
    ((n = None) \/ (nt = (fun_numtype_in reserved__in))) -> 
    (Instr_ok (C, (Instr__LOAD (nt, (option_zip (fun n sx => (n, sx)) n sx), n_A, n_O)), ([Valtype__I32], [(fun_valtype_numtype nt)])))
  | Instr_ok__store (C : Context) (reserved__in : reserved__In) (mt : Memtype) (n : (option reserved__N)) (n_A : reserved__N) (n_O : reserved__N) (nt : Numtype) (o0 : nat) (o1 : (option nat)) : 
    (0 < List.length (C.(Context__MEM))) -> 
    ((n = None) = (o1 = None)) -> 
    ((fun_size (fun_valtype_numtype nt)) = (Some o0)) -> 
    (List.Forall (fun o1 => ((fun_size (fun_valtype_numtype nt)) = (Some o1))) (option_to_list o1)) -> 
    ((lookup_total C.(Context__MEM) 0) = mt) -> 
    ((((Nat.pow 2) n_A)) <= (((Nat.div o0) 8))) -> 
    (List.Forall2 (fun n o1 => (((((Nat.pow 2) n_A)) <= (((Nat.div n) 8))) /\ ((((Nat.div n) 8)) < (((Nat.div o1) 8))))) (option_to_list n) (option_to_list o1)) -> 
    ((n = None) \/ (nt = (fun_numtype_in reserved__in))) -> 
    (Instr_ok (C, (Instr__STORE (nt, n, n_A, n_O)), ([Valtype__I32; (fun_valtype_numtype nt)], nil)))

with (** Relation definition : InstrSeq_ok **)
InstrSeq_ok : (Context * (list Instr) * Functype)%type -> Prop := 
  | InstrSeq_ok__empty (C : Context) : 
    (InstrSeq_ok (C, nil, (nil, nil)))
  | InstrSeq_ok__seq (C : Context) (instr_1 : Instr) (instr_2 : Instr) (t_1 : (list Valtype)) (t_2 : (list Valtype)) (t_3 : (list Valtype)) : 
    (Instr_ok (C, instr_1, (t_1, t_2))) -> 
    (InstrSeq_ok (C, [instr_2], (t_2, t_3))) -> 
    (InstrSeq_ok (C, ([instr_1] ++ [instr_2]), (t_1, t_3)))
  | InstrSeq_ok__weak (C : Context) (instr : (list Instr)) (t'_1 : Valtype) (t'_2 : (list Valtype)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (InstrSeq_ok (C, instr, (t_1, t_2))) -> 
    (Resulttype_sub ([t'_1], t_1)) -> 
    (Resulttype_sub (t_2, t'_2)) -> 
    (InstrSeq_ok (C, instr, ([t'_1], t'_2)))
  | InstrSeq_ok__frame (C : Context) (instr : (list Instr)) (t : (list Valtype)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (InstrSeq_ok (C, instr, (t_1, t_2))) -> 
    (InstrSeq_ok (C, instr, ((t ++ t_1), (t ++ t_2))))
.

(** Relation definition : Expr_ok **)
Inductive Expr_ok : (Context * Expr * Resulttype)%type -> Prop := 
  | Expr_ok__rule_0 (C : Context) (instr : (list Instr)) (t : (list Valtype)) : 
    (InstrSeq_ok (C, instr, (nil, t))) -> 
    (Expr_ok (C, instr, t))
.

(** Relation definition : Instr_const **)
Inductive Instr_const : (Context * Instr)%type -> Prop := 
  | Instr_const__const (C : Context) (c : C_numtype) (nt : Numtype) : 
    (Instr_const (C, (Instr__CONST (nt, c))))
  | Instr_const__ref_null (C : Context) (rt : Reftype) : 
    (Instr_const (C, (Instr__REF_NULL rt)))
  | Instr_const__ref_func (C : Context) (x : Idx) : 
    (Instr_const (C, (Instr__REF_FUNC x)))
  | Instr_const__global_get (C : Context) (t : Valtype) (x : Idx) : 
    (x < List.length (C.(Context__GLOBAL))) -> 
    ((lookup_total C.(Context__GLOBAL) x) = (None, t)) -> 
    (Instr_const (C, (Instr__GLOBAL_GET x)))
.

(** Relation definition : Expr_const **)
Inductive Expr_const : (Context * Expr)%type -> Prop := 
  | Expr_const__rule_0 (C : Context) (instr : (list Instr)) : 
    (List.Forall (fun instr => (Instr_const (C, instr))) instr) -> 
    (Expr_const (C, instr))
.

(** Relation definition : Expr_ok_const **)
Inductive Expr_ok_const : (Context * Expr * Valtype)%type -> Prop := 
  | Expr_ok_const__rule_0 (C : Context) (expr : Expr) (t : Valtype) : 
    (Expr_ok (C, expr, [t])) -> 
    (Expr_const (C, expr)) -> 
    (Expr_ok_const (C, expr, t))
.

(** Relation definition : Func_ok **)
Inductive Func_ok : (Context * Func * Functype)%type -> Prop := 
  | Func_ok__rule_0 (C : Context) (expr : Expr) (ft : Functype) (t : (list Valtype)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) : 
    (ft = (t_1, t_2)) -> 
    (Functype_ok ft) -> 
    (Expr_ok (({| Context__FUNC := nil; Context__GLOBAL := nil; Context__TABLE := nil; Context__MEM := nil; Context__ELEM := nil; Context__DATA := nil; Context__LOCAL := nil; Context__LABEL := nil; Context__RETURN := (Some t_2) |} ++ ({| Context__FUNC := nil; Context__GLOBAL := nil; Context__TABLE := nil; Context__MEM := nil; Context__ELEM := nil; Context__DATA := nil; Context__LOCAL := nil; Context__LABEL := [t_2]; Context__RETURN := None |} ++ ({| Context__FUNC := nil; Context__GLOBAL := nil; Context__TABLE := nil; Context__MEM := nil; Context__ELEM := nil; Context__DATA := nil; Context__LOCAL := (t_1 ++ t); Context__LABEL := nil; Context__RETURN := None |} ++ C))), expr, t_2)) -> 
    (Func_ok (C, (ft, t, expr), ft))
.

(** Relation definition : Global_ok **)
Inductive Global_ok : (Context * Global * Globaltype)%type -> Prop := 
  | Global_ok__rule_0 (C : Context) (expr : Expr) (gt : Globaltype) (t : Valtype) : 
    (Globaltype_ok gt) -> 
    (gt = ((Some tt), t)) -> 
    (Expr_ok_const (C, expr, t)) -> 
    (Global_ok (C, (gt, expr), gt))
.

(** Relation definition : Table_ok **)
Inductive Table_ok : (Context * Table * Tabletype)%type -> Prop := 
  | Table_ok__rule_0 (C : Context) (reserved__tt : Tabletype) : 
    (Tabletype_ok reserved__tt) -> 
    (Table_ok (C, reserved__tt, reserved__tt))
.

(** Relation definition : Mem_ok **)
Inductive Mem_ok : (Context * Mem * Memtype)%type -> Prop := 
  | Mem_ok__rule_0 (C : Context) (mt : Memtype) : 
    (Memtype_ok mt) -> 
    (Mem_ok (C, mt, mt))
.

(** Relation definition : Elemmode_ok **)
Inductive Elemmode_ok : (Context * Elemmode * Reftype)%type -> Prop := 
  | Elemmode_ok__active (C : Context) (expr : Expr) (lim : Limits) (rt : Reftype) (x : Idx) : 
    (x < List.length (C.(Context__TABLE))) -> 
    ((lookup_total C.(Context__TABLE) x) = (lim, rt)) -> 
    (Expr_ok_const (C, expr, Valtype__I32))(* *{} *) -> 
    (Elemmode_ok (C, (Elemmode__TABLE (x, expr)), rt))
  | Elemmode_ok__declare (C : Context) (rt : Reftype) : 
    (Elemmode_ok (C, Elemmode__DECLARE, rt))
.

(** Relation definition : Elem_ok **)
Inductive Elem_ok : (Context * Elem * Reftype)%type -> Prop := 
  | Elem_ok__rule_0 (C : Context) (elemmode : (option Elemmode)) (expr : (list Expr)) (rt : Reftype) : 
    (List.Forall (fun expr => (Expr_ok (C, expr, [(fun_valtype_reftype rt)]))) expr) -> 
    (List.Forall (fun elemmode => (Elemmode_ok (C, elemmode, rt))) (option_to_list elemmode)) -> 
    (Elem_ok (C, (rt, expr, elemmode), rt))
.

(** Relation definition : Datamode_ok **)
Inductive Datamode_ok : (Context * Datamode)%type -> Prop := 
  | Datamode_ok__rule_0 (C : Context) (expr : Expr) (mt : Memtype) : 
    (0 < List.length (C.(Context__MEM))) -> 
    ((lookup_total C.(Context__MEM) 0) = mt) -> 
    (Expr_ok_const (C, expr, Valtype__I32))(* *{} *) -> 
    (Datamode_ok (C, (Datamode__MEMORY (0, expr))))
.

(** Relation definition : Data_ok **)
Inductive Data_ok : (Context * Data)%type -> Prop := 
  | Data_ok__rule_0 (C : Context) (b : (list (list Byte))) (datamode : (option Datamode)) : 
    (List.Forall (fun datamode => (Datamode_ok (C, datamode))) (option_to_list datamode)) -> 
    (Data_ok (C, ((List.map (fun b => b) b), datamode)))
.

(** Relation definition : Start_ok **)
Inductive Start_ok : (Context * Start)%type -> Prop := 
  | Start_ok__rule_0 (C : Context) (x : Idx) : 
    (x < List.length (C.(Context__FUNC))) -> 
    ((lookup_total C.(Context__FUNC) x) = (nil, nil)) -> 
    (Start_ok (C, x))
.

(** Relation definition : Import_ok **)
Inductive Import_ok : (Context * reserved__Import * Externtype)%type -> Prop := 
  | Import_ok__rule_0 (C : Context) (name_1 : Name) (name_2 : Name) (xt : Externtype) : 
    (Externtype_ok xt) -> 
    (Import_ok (C, (name_1, name_2, xt), xt))
.

(** Relation definition : Externuse_ok **)
Inductive Externuse_ok : (Context * Externuse * Externtype)%type -> Prop := 
  | Externuse_ok__func (C : Context) (ft : Functype) (x : Idx) : 
    (x < List.length (C.(Context__FUNC))) -> 
    ((lookup_total C.(Context__FUNC) x) = ft) -> 
    (Externuse_ok (C, (Externuse__FUNC x), (Externtype__FUNC ft)))
  | Externuse_ok__global (C : Context) (gt : Globaltype) (x : Idx) : 
    (x < List.length (C.(Context__GLOBAL))) -> 
    ((lookup_total C.(Context__GLOBAL) x) = gt) -> 
    (Externuse_ok (C, (Externuse__GLOBAL x), (Externtype__GLOBAL gt)))
  | Externuse_ok__table (C : Context) (reserved__tt : Tabletype) (x : Idx) : 
    (x < List.length (C.(Context__TABLE))) -> 
    ((lookup_total C.(Context__TABLE) x) = reserved__tt) -> 
    (Externuse_ok (C, (Externuse__TABLE x), (Externtype__TABLE reserved__tt)))
  | Externuse_ok__mem (C : Context) (mt : Memtype) (x : Idx) : 
    (x < List.length (C.(Context__MEM))) -> 
    ((lookup_total C.(Context__MEM) x) = mt) -> 
    (Externuse_ok (C, (Externuse__MEMORY x), (Externtype__MEMORY mt)))
.

(** Relation definition : Export_ok **)
Inductive Export_ok : (Context * reserved__Export * Externtype)%type -> Prop := 
  | Export_ok__rule_0 (C : Context) (externuse : Externuse) (name : Name) (xt : Externtype) : 
    (Externuse_ok (C, externuse, xt)) -> 
    (Export_ok (C, (name, externuse), xt))
.

(** Relation definition : Module_ok **)
Inductive Module_ok : Module -> Prop := 
  | Module_ok__rule_0 (C : Context) (data : (list Data)) (elem : (list Elem)) (export : (list reserved__Export)) (ft : (list Functype)) (func : (list Func)) (global : (list Global)) (gt : (list Globaltype)) (import : (list reserved__Import)) (mem : (list Mem)) (mt : (list Memtype)) (n : reserved__N) (rt : (list Reftype)) (start : (list Start)) (table : (list Table)) (reserved__tt : (list Tabletype)) : 
    (List.length (ft) = List.length (func)) -> 
    (List.length (global) = List.length (gt)) -> 
    (List.length (table) = List.length (reserved__tt)) -> 
    (List.length (mem) = List.length (mt)) -> 
    (List.length (elem) = List.length (rt)) -> 
    (List.length (data) = n) -> 
    (C = {| Context__FUNC := ft; Context__GLOBAL := gt; Context__TABLE := reserved__tt; Context__MEM := mt; Context__ELEM := rt; Context__DATA := [tt]; Context__LOCAL := nil; Context__LABEL := nil; Context__RETURN := None |}) -> 
    (List.Forall2 (fun ft func => (Func_ok (C, func, ft))) ft func) -> 
    (List.Forall2 (fun global gt => (Global_ok (C, global, gt))) global gt) -> 
    (List.Forall2 (fun table reserved__tt => (Table_ok (C, table, reserved__tt))) table reserved__tt) -> 
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

(** Variant definition : Num **)
Inductive Num : Type :=
 | Num__CONST : (Numtype * C_numtype)%type -> Num
.
Global Instance Inhabited_Num : Inhabited Num(* FIXME: no inhabitant found! *) .
  Admitted.

(** Variant definition : Ref **)
Inductive Ref : Type :=
 | Ref__REF_NULL : Reftype -> Ref
 | Ref__REF_FUNC_ADDR : Funcaddr -> Ref
 | Ref__REF_HOST_ADDR : Hostaddr -> Ref
.
Global Instance Inhabited_Ref : Inhabited Ref(* FIXME: no inhabitant found! *) .
  Admitted.

(** Variant definition : Val **)
Inductive Val : Type :=
 | Val__CONST : (Numtype * C_numtype)%type -> Val
 | Val__REF_NULL : Reftype -> Val
 | Val__REF_FUNC_ADDR : Funcaddr -> Val
 | Val__REF_HOST_ADDR : Hostaddr -> Val
.
Global Instance Inhabited_Val : Inhabited Val(* FIXME: no inhabitant found! *) .
  Admitted.

(** Variant definition : Result **)
Inductive Result : Type :=
 | Result___VALS : (list Val) -> Result
 | Result__TRAP : Result
.
Global Instance Inhabited_Result : Inhabited Result := { default_val := Result__TRAP }.

(** Variant definition : Externval **)
Inductive Externval : Type :=
 | Externval__FUNC : Funcaddr -> Externval
 | Externval__GLOBAL : Globaladdr -> Externval
 | Externval__TABLE : Tableaddr -> Externval
 | Externval__MEM : Memaddr -> Externval
.
Global Instance Inhabited_Externval : Inhabited Externval(* FIXME: no inhabitant found! *) .
  Admitted.

(** Function definition : fun_default_ **)
(* Dependencies:  *)
Definition fun_default_ (arg: Valtype) : (option Val) :=
  match arg with
  | Valtype__I32 => (Some (Val__CONST (Numtype__I32, 0)))
  | Valtype__I64 => (Some (Val__CONST (Numtype__I64, 0)))
  | Valtype__F32 => (Some (Val__CONST (Numtype__F32, 0)))
  | Valtype__F64 => (Some (Val__CONST (Numtype__F64, 0)))
  | Valtype__FUNCREF => (Some (Val__REF_NULL Reftype__FUNCREF))
  | Valtype__EXTERNREF => (Some (Val__REF_NULL Reftype__EXTERNREF))
  | x => None
end.

(** Notation definition : Exportinst **)
Definition Exportinst := (* mixop:  *) (Name * Externval)%type.

(** Record definition : Moduleinst **)
Record Moduleinst : Type := {
  Moduleinst__FUNC : (list Funcaddr);
  Moduleinst__GLOBAL : (list Globaladdr);
  Moduleinst__TABLE : (list Tableaddr);
  Moduleinst__MEM : (list Memaddr);
  Moduleinst__ELEM : (list Elemaddr);
  Moduleinst__DATA : (list Dataaddr);
  Moduleinst__EXPORT : (list Exportinst);
 }. 

Global Instance Inhabited_Moduleinst : Inhabited Moduleinst.
(* TODO: add automatic record inhabitance proof *)
Admitted.

Definition _append_Moduleinst (r1 r2: Moduleinst) : Moduleinst :=
{|
  Moduleinst__FUNC := r1.(Moduleinst__FUNC) ++ r2.(Moduleinst__FUNC);
  Moduleinst__GLOBAL := r1.(Moduleinst__GLOBAL) ++ r2.(Moduleinst__GLOBAL);
  Moduleinst__TABLE := r1.(Moduleinst__TABLE) ++ r2.(Moduleinst__TABLE);
  Moduleinst__MEM := r1.(Moduleinst__MEM) ++ r2.(Moduleinst__MEM);
  Moduleinst__ELEM := r1.(Moduleinst__ELEM) ++ r2.(Moduleinst__ELEM);
  Moduleinst__DATA := r1.(Moduleinst__DATA) ++ r2.(Moduleinst__DATA);
  Moduleinst__EXPORT := r1.(Moduleinst__EXPORT) ++ r2.(Moduleinst__EXPORT);
|}. 

Global Instance Append_Moduleinst : Append Moduleinst := { _append arg1 arg2 := _append_Moduleinst arg1 arg2 }.

(** Notation definition : Funcinst **)
Definition Funcinst := (* mixop:  *) (Moduleinst * Func)%type.

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
  Store__FUNC : (list Funcinst);
  Store__GLOBAL : (list Globalinst);
  Store__TABLE : (list Tableinst);
  Store__MEM : (list Meminst);
  Store__ELEM : (list Eleminst);
  Store__DATA : (list Datainst);
 }. 

Global Instance Inhabited_Store : Inhabited Store.
(* TODO: add automatic record inhabitance proof *)
Admitted.

Definition _append_Store (r1 r2: Store) : Store :=
{|
  Store__FUNC := r1.(Store__FUNC) ++ r2.(Store__FUNC);
  Store__GLOBAL := r1.(Store__GLOBAL) ++ r2.(Store__GLOBAL);
  Store__TABLE := r1.(Store__TABLE) ++ r2.(Store__TABLE);
  Store__MEM := r1.(Store__MEM) ++ r2.(Store__MEM);
  Store__ELEM := r1.(Store__ELEM) ++ r2.(Store__ELEM);
  Store__DATA := r1.(Store__DATA) ++ r2.(Store__DATA);
|}. 

Global Instance Append_Store : Append Store := { _append arg1 arg2 := _append_Store arg1 arg2 }.

(** Record definition : Frame **)
Record Frame : Type := {
  Frame__LOCAL : (list Val);
  Frame__MODULE : Moduleinst;
 }. 

Global Instance Inhabited_Frame : Inhabited Frame.
(* TODO: add automatic record inhabitance proof *)
Admitted.

Definition _append_Frame (r1 r2: Frame) : Frame :=
{|
  Frame__LOCAL := r1.(Frame__LOCAL) ++ r2.(Frame__LOCAL);
  Frame__MODULE := r1.(Frame__MODULE) ++ r2.(Frame__MODULE);
|}. 

Global Instance Append_Frame : Append Frame := { _append arg1 arg2 := _append_Frame arg1 arg2 }.

(** Notation definition : State **)
Definition State := (* mixop:  *) (Store * Frame)%type.

(** Variant definition : Admininstr **)
Inductive Admininstr : Type :=
 | Admininstr__UNREACHABLE : Admininstr
 | Admininstr__NOP : Admininstr
 | Admininstr__DROP : Admininstr
 | Admininstr__SELECT : (option Valtype) -> Admininstr
 | Admininstr__BLOCK : (Blocktype * (list Instr))%type -> Admininstr
 | Admininstr__LOOP : (Blocktype * (list Instr))%type -> Admininstr
 | Admininstr__IF : (Blocktype * (list Instr) * (list Instr))%type -> Admininstr
 | Admininstr__BR : Labelidx -> Admininstr
 | Admininstr__BR_IF : Labelidx -> Admininstr
 | Admininstr__BR_TABLE : ((list Labelidx) * Labelidx)%type -> Admininstr
 | Admininstr__CALL : Funcidx -> Admininstr
 | Admininstr__CALL_INDIRECT : (Tableidx * Functype)%type -> Admininstr
 | Admininstr__RETURN : Admininstr
 | Admininstr__CONST : (Numtype * C_numtype)%type -> Admininstr
 | Admininstr__UNOP : (Numtype * Unop_numtype)%type -> Admininstr
 | Admininstr__BINOP : (Numtype * Binop_numtype)%type -> Admininstr
 | Admininstr__TESTOP : (Numtype * Testop_numtype)%type -> Admininstr
 | Admininstr__RELOP : (Numtype * Relop_numtype)%type -> Admininstr
 | Admininstr__EXTEND : (Numtype * reserved__N)%type -> Admininstr
 | Admininstr__CVTOP : (Numtype * Cvtop * Numtype * (option Sx))%type -> Admininstr
 | Admininstr__REF_NULL : Reftype -> Admininstr
 | Admininstr__REF_FUNC : Funcidx -> Admininstr
 | Admininstr__REF_IS_NULL : Admininstr
 | Admininstr__LOCAL_GET : Localidx -> Admininstr
 | Admininstr__LOCAL_SET : Localidx -> Admininstr
 | Admininstr__LOCAL_TEE : Localidx -> Admininstr
 | Admininstr__GLOBAL_GET : Globalidx -> Admininstr
 | Admininstr__GLOBAL_SET : Globalidx -> Admininstr
 | Admininstr__TABLE_GET : Tableidx -> Admininstr
 | Admininstr__TABLE_SET : Tableidx -> Admininstr
 | Admininstr__TABLE_SIZE : Tableidx -> Admininstr
 | Admininstr__TABLE_GROW : Tableidx -> Admininstr
 | Admininstr__TABLE_FILL : Tableidx -> Admininstr
 | Admininstr__TABLE_COPY : (Tableidx * Tableidx)%type -> Admininstr
 | Admininstr__TABLE_INIT : (Tableidx * Elemidx)%type -> Admininstr
 | Admininstr__ELEM_DROP : Elemidx -> Admininstr
 | Admininstr__MEMORY_SIZE : Admininstr
 | Admininstr__MEMORY_GROW : Admininstr
 | Admininstr__MEMORY_FILL : Admininstr
 | Admininstr__MEMORY_COPY : Admininstr
 | Admininstr__MEMORY_INIT : Dataidx -> Admininstr
 | Admininstr__DATA_DROP : Dataidx -> Admininstr
 | Admininstr__LOAD : (Numtype * (option (reserved__N * Sx)%type) * U32 * U32)%type -> Admininstr
 | Admininstr__STORE : (Numtype * (option reserved__N) * U32 * U32)%type -> Admininstr
 | Admininstr__REF_FUNC_ADDR : Funcaddr -> Admininstr
 | Admininstr__REF_HOST_ADDR : Hostaddr -> Admininstr
 | Admininstr__CALL_ADDR : Funcaddr -> Admininstr
 | Admininstr__LABEL_ : (reserved__N * (list Instr) * (list Admininstr))%type -> Admininstr
 | Admininstr__FRAME_ : (reserved__N * Frame * (list Admininstr))%type -> Admininstr
 | Admininstr__TRAP : Admininstr
.
Global Instance Inhabited_Admininstr : Inhabited Admininstr := { default_val := Admininstr__UNREACHABLE }.

(** Function definition : fun_admininstr_globalinst **)
(* Dependencies:  *)
Definition fun_admininstr_globalinst (arg: Globalinst) : Admininstr :=
  match arg with
  | (Val__CONST x) => (Admininstr__CONST x)
  | (Val__REF_NULL x) => (Admininstr__REF_NULL x)
  | (Val__REF_FUNC_ADDR x) => (Admininstr__REF_FUNC_ADDR x)
  | (Val__REF_HOST_ADDR x) => (Admininstr__REF_HOST_ADDR x)
end.

(** Function definition : fun_admininstr_instr **)
(* Dependencies:  *)
Definition fun_admininstr_instr (arg: Instr) : Admininstr :=
  match arg with
  | Instr__UNREACHABLE => Admininstr__UNREACHABLE
  | Instr__NOP => Admininstr__NOP
  | Instr__DROP => Admininstr__DROP
  | (Instr__SELECT x) => (Admininstr__SELECT x)
  | (Instr__BLOCK x) => (Admininstr__BLOCK x)
  | (Instr__LOOP x) => (Admininstr__LOOP x)
  | (Instr__IF x) => (Admininstr__IF x)
  | (Instr__BR x) => (Admininstr__BR x)
  | (Instr__BR_IF x) => (Admininstr__BR_IF x)
  | (Instr__BR_TABLE x) => (Admininstr__BR_TABLE x)
  | (Instr__CALL x) => (Admininstr__CALL x)
  | (Instr__CALL_INDIRECT x) => (Admininstr__CALL_INDIRECT x)
  | Instr__RETURN => Admininstr__RETURN
  | (Instr__CONST x) => (Admininstr__CONST x)
  | (Instr__UNOP x) => (Admininstr__UNOP x)
  | (Instr__BINOP x) => (Admininstr__BINOP x)
  | (Instr__TESTOP x) => (Admininstr__TESTOP x)
  | (Instr__RELOP x) => (Admininstr__RELOP x)
  | (Instr__EXTEND x) => (Admininstr__EXTEND x)
  | (Instr__CVTOP x) => (Admininstr__CVTOP x)
  | (Instr__REF_NULL x) => (Admininstr__REF_NULL x)
  | (Instr__REF_FUNC x) => (Admininstr__REF_FUNC x)
  | Instr__REF_IS_NULL => Admininstr__REF_IS_NULL
  | (Instr__LOCAL_GET x) => (Admininstr__LOCAL_GET x)
  | (Instr__LOCAL_SET x) => (Admininstr__LOCAL_SET x)
  | (Instr__LOCAL_TEE x) => (Admininstr__LOCAL_TEE x)
  | (Instr__GLOBAL_GET x) => (Admininstr__GLOBAL_GET x)
  | (Instr__GLOBAL_SET x) => (Admininstr__GLOBAL_SET x)
  | (Instr__TABLE_GET x) => (Admininstr__TABLE_GET x)
  | (Instr__TABLE_SET x) => (Admininstr__TABLE_SET x)
  | (Instr__TABLE_SIZE x) => (Admininstr__TABLE_SIZE x)
  | (Instr__TABLE_GROW x) => (Admininstr__TABLE_GROW x)
  | (Instr__TABLE_FILL x) => (Admininstr__TABLE_FILL x)
  | (Instr__TABLE_COPY x) => (Admininstr__TABLE_COPY x)
  | (Instr__TABLE_INIT x) => (Admininstr__TABLE_INIT x)
  | (Instr__ELEM_DROP x) => (Admininstr__ELEM_DROP x)
  | Instr__MEMORY_SIZE => Admininstr__MEMORY_SIZE
  | Instr__MEMORY_GROW => Admininstr__MEMORY_GROW
  | Instr__MEMORY_FILL => Admininstr__MEMORY_FILL
  | Instr__MEMORY_COPY => Admininstr__MEMORY_COPY
  | (Instr__MEMORY_INIT x) => (Admininstr__MEMORY_INIT x)
  | (Instr__DATA_DROP x) => (Admininstr__DATA_DROP x)
  | (Instr__LOAD x) => (Admininstr__LOAD x)
  | (Instr__STORE x) => (Admininstr__STORE x)
end.

(** Function definition : fun_admininstr_ref **)
(* Dependencies:  *)
Definition fun_admininstr_ref (arg: Ref) : Admininstr :=
  match arg with
  | (Ref__REF_NULL x) => (Admininstr__REF_NULL x)
  | (Ref__REF_FUNC_ADDR x) => (Admininstr__REF_FUNC_ADDR x)
  | (Ref__REF_HOST_ADDR x) => (Admininstr__REF_HOST_ADDR x)
end.

(** Function definition : fun_admininstr_val **)
(* Dependencies:  *)
Definition fun_admininstr_val (arg: Val) : Admininstr :=
  match arg with
  | (Val__CONST x) => (Admininstr__CONST x)
  | (Val__REF_NULL x) => (Admininstr__REF_NULL x)
  | (Val__REF_FUNC_ADDR x) => (Admininstr__REF_FUNC_ADDR x)
  | (Val__REF_HOST_ADDR x) => (Admininstr__REF_HOST_ADDR x)
end.

(** Notation definition : Config **)
Definition Config := (* mixop:  *) (State * (list Admininstr))%type.

(** Function definition : fun_funcaddr **)
(* Dependencies:  *)
Definition fun_funcaddr (arg: State) : (list Funcaddr) :=
  match arg with
  | (s, f) => f.(Frame__MODULE).(Moduleinst__FUNC)
end.

(** Function definition : fun_funcinst **)
(* Dependencies:  *)
Definition fun_funcinst (arg: State) : (list Funcinst) :=
  match arg with
  | (s, f) => s.(Store__FUNC)
end.

(** Function definition : fun_func **)
(* Dependencies:  *)
Definition fun_func (arg: (State * Funcidx)%type) : Funcinst :=
  match arg with
  | ((s, f), x) => (lookup_total s.(Store__FUNC) (lookup_total f.(Frame__MODULE).(Moduleinst__FUNC) x))
end.

(** Function definition : fun_global **)
(* Dependencies:  *)
Definition fun_global (arg: (State * Globalidx)%type) : Globalinst :=
  match arg with
  | ((s, f), x) => (lookup_total s.(Store__GLOBAL) (lookup_total f.(Frame__MODULE).(Moduleinst__GLOBAL) x))
end.

(** Function definition : fun_table **)
(* Dependencies:  *)
Definition fun_table (arg: (State * Tableidx)%type) : Tableinst :=
  match arg with
  | ((s, f), x) => (lookup_total s.(Store__TABLE) (lookup_total f.(Frame__MODULE).(Moduleinst__TABLE) x))
end.

(** Function definition : fun_mem **)
(* Dependencies:  *)
Definition fun_mem (arg: (State * Memidx)%type) : Meminst :=
  match arg with
  | ((s, f), x) => (lookup_total s.(Store__MEM) (lookup_total f.(Frame__MODULE).(Moduleinst__MEM) x))
end.

(** Function definition : fun_elem **)
(* Dependencies:  *)
Definition fun_elem (arg: (State * Tableidx)%type) : Eleminst :=
  match arg with
  | ((s, f), x) => (lookup_total s.(Store__ELEM) (lookup_total f.(Frame__MODULE).(Moduleinst__ELEM) x))
end.

(** Function definition : fun_data **)
(* Dependencies:  *)
Definition fun_data (arg: (State * Dataidx)%type) : Datainst :=
  match arg with
  | ((s, f), x) => (lookup_total s.(Store__DATA) (lookup_total f.(Frame__MODULE).(Moduleinst__DATA) x))
end.

(** Function definition : fun_local **)
(* Dependencies:  *)
Definition fun_local (arg: (State * Localidx)%type) : Val :=
  match arg with
  | ((s, f), x) => (lookup_total f.(Frame__LOCAL) x)
end.

(** Function definition : fun_with_local **)
(* Dependencies:  *)
Definition fun_with_local (arg: (State * Localidx * Val)%type) : State :=
  match arg with
  | ((s, f), x, v) => (s, (* TODO: Coq need a bit more help for dealing with records 
  {f with LOCAL := (list_update f.(LOCAL) x v) } *)f)
end.

(** Function definition : fun_with_global **)
(* Dependencies:  *)
Definition fun_with_global (arg: (State * Globalidx * Val)%type) : State :=
  match arg with
  | ((s, f), x, v) => ((* TODO: Coq need a bit more help for dealing with records 
  {s with GLOBAL := (list_update s.(GLOBAL) (lookup_total f.(Frame__MODULE).(Moduleinst__GLOBAL) x) v) } *)s, f)
end.

(** Function definition : fun_with_table **)
(* Dependencies:  *)
Definition fun_with_table (arg: (State * Tableidx * nat * Ref)%type) : State :=
  match arg with
  | ((s, f), x, i, r) => ((* TODO: Coq need a bit more help for dealing with records 
  {s with TABLE := (list_update s.(TABLE) (lookup_total f.(Frame__MODULE).(Moduleinst__TABLE) x) (list_update (lookup_total s.(TABLE) (lookup_total f.(Frame__MODULE).(Moduleinst__TABLE) x)) i r)) } *)s, f)
end.

(** Function definition : fun_with_tableext **)
(* Dependencies:  *)
Definition fun_with_tableext (arg: (State * Tableidx * (list Ref))%type) : State :=
  match arg with
  | ((s, f), x, r) => ((* TODO: Coq need a bit more help for dealing with records 
  {s with TABLE := (list_update s.(TABLE) (lookup_total f.(Frame__MODULE).(Moduleinst__TABLE) x) (List.app (lookup_total s.(TABLE) (lookup_total f.(Frame__MODULE).(Moduleinst__TABLE) x)) r)) } *)s, f)
end.

(** Function definition : fun_with_mem **)
(* Dependencies:  *)
Definition fun_with_mem (arg: (State * Tableidx * nat * nat * (list Byte))%type) : State :=
  match arg with
  | ((s, f), x, i, j, b) => (default_val (* TODO *), f)
end.

(** Function definition : fun_with_memext **)
(* Dependencies:  *)
Definition fun_with_memext (arg: (State * Tableidx * (list Byte))%type) : State :=
  match arg with
  | ((s, f), x, b) => ((* TODO: Coq need a bit more help for dealing with records 
  {s with MEM := (list_update s.(MEM) (lookup_total f.(Frame__MODULE).(Moduleinst__MEM) x) (List.app (lookup_total s.(MEM) (lookup_total f.(Frame__MODULE).(Moduleinst__MEM) x)) b)) } *)s, f)
end.

(** Function definition : fun_with_elem **)
(* Dependencies:  *)
Definition fun_with_elem (arg: (State * Elemidx * (list Ref))%type) : State :=
  match arg with
  | ((s, f), x, r) => ((* TODO: Coq need a bit more help for dealing with records 
  {s with TABLE := (list_update s.(TABLE) (lookup_total f.(Frame__MODULE).(Moduleinst__TABLE) x) r) } *)s, f)
end.

(** Function definition : fun_with_data **)
(* Dependencies:  *)
Definition fun_with_data (arg: (State * Dataidx * (list Byte))%type) : State :=
  match arg with
  | ((s, f), x, b) => ((* TODO: Coq need a bit more help for dealing with records 
  {s with MEM := (list_update s.(MEM) (lookup_total f.(Frame__MODULE).(Moduleinst__MEM) x) b) } *)s, f)
end.

(** Variant definition : E **)
Inductive E : Type :=
 | E___HOLE : E
 | E___SEQ : ((list Val) * E * (list Instr))%type -> E
 | E__LABEL_ : (reserved__N * (list Instr) * E)%type -> E
.
Global Instance Inhabited_E : Inhabited E := { default_val := E___HOLE }.

(** Function definition : fun_unop **)
(* Dependencies:  *)
Definition fun_unop (arg: (Unop_numtype * Numtype * C_numtype)%type) : (list C_numtype) :=
  match arg with
  | _ => default_val
end.

(** Function definition : fun_binop **)
(* Dependencies:  *)
Definition fun_binop (arg: (Binop_numtype * Numtype * C_numtype * C_numtype)%type) : (list C_numtype) :=
  match arg with
  | _ => default_val
end.

(** Function definition : fun_testop **)
(* Dependencies:  *)
Definition fun_testop (arg: (Testop_numtype * Numtype * C_numtype)%type) : C_numtype :=
  match arg with
  | _ => default_val
end.

(** Function definition : fun_relop **)
(* Dependencies:  *)
Definition fun_relop (arg: (Relop_numtype * Numtype * C_numtype * C_numtype)%type) : C_numtype :=
  match arg with
  | _ => default_val
end.

(** Function definition : fun_ext **)
(* Dependencies:  *)
Definition fun_ext (arg: (nat * nat * Sx * C_numtype)%type) : C_numtype :=
  match arg with
  | _ => default_val
end.

(** Function definition : fun_cvtop **)
(* Dependencies:  *)
Definition fun_cvtop (arg: (Numtype * Cvtop * Numtype * (option Sx) * C_numtype)%type) : (list C_numtype) :=
  match arg with
  | _ => default_val
end.

(** Function definition : fun_wrap_ **)
(* Dependencies:  *)
Definition fun_wrap_ (arg: ((nat * nat)%type * C_numtype)%type) : nat :=
  match arg with
  | _ => default_val
end.

(** Function definition : fun_bytes_ **)
(* Dependencies:  *)
Definition fun_bytes_ (arg: (nat * C_numtype)%type) : (list Byte) :=
  match arg with
  | _ => default_val
end.

(** Relation definition : Step_pure_before_ref_is_null_false **)
Inductive Step_pure_before_ref_is_null_false : (list Admininstr) -> Prop := 
  | Step_pure_before_ref_is_null_false__ref_is_null_true (rt : Reftype) (val : Val) : 
    (val = (Val__REF_NULL rt)) -> 
    (Step_pure_before_ref_is_null_false [(fun_admininstr_val val); Admininstr__REF_IS_NULL])
.

(** Relation definition : Step_pure **)
Inductive Step_pure : ((list Admininstr) * (list Admininstr))%type -> Prop := 
  | Step_pure__unreachable  : 
    (Step_pure ([Admininstr__UNREACHABLE], [Admininstr__TRAP]))
  | Step_pure__nop  : 
    (Step_pure ([Admininstr__NOP], nil))
  | Step_pure__drop (val : Val) : 
    (Step_pure ([(fun_admininstr_val val); Admininstr__DROP], nil))
  | Step_pure__select_true (c : C_numtype) (t : (option Valtype)) (val_1 : Val) (val_2 : Val) : 
    (c <> 0) -> 
    (Step_pure ([(fun_admininstr_val val_1); (fun_admininstr_val val_2); (Admininstr__CONST (Numtype__I32, c)); (Admininstr__SELECT t)], [(fun_admininstr_val val_1)]))
  | Step_pure__select_false (c : C_numtype) (t : (option Valtype)) (val_1 : Val) (val_2 : Val) : 
    (c = 0) -> 
    (Step_pure ([(fun_admininstr_val val_1); (fun_admininstr_val val_2); (Admininstr__CONST (Numtype__I32, c)); (Admininstr__SELECT t)], [(fun_admininstr_val val_2)]))
  | Step_pure__block (bt : Blocktype) (instr : (list Instr)) (k : nat) (n : reserved__N) (t_1 : (list Valtype)) (t_2 : (list Valtype)) (val : (list Val)) : 
    (List.length (t_1) = k) -> 
    (List.length (t_2) = n) -> 
    (List.length (val) = k) -> 
    (bt = (t_1, t_2)) -> 
    (Step_pure (((List.map fun_admininstr_val val) ++ [(Admininstr__BLOCK (bt, instr))]), [(Admininstr__LABEL_ (n, nil, ((List.map fun_admininstr_val val) ++ (List.map fun_admininstr_instr instr))))]))
  | Step_pure__loop (bt : Blocktype) (instr : (list Instr)) (k : nat) (n : reserved__N) (t_1 : (list Valtype)) (t_2 : (list Valtype)) (val : (list Val)) : 
    (List.length (t_1) = k) -> 
    (List.length (t_2) = n) -> 
    (List.length (val) = k) -> 
    (bt = (t_1, t_2)) -> 
    (Step_pure (((List.map fun_admininstr_val val) ++ [(Admininstr__LOOP (bt, instr))]), [(Admininstr__LABEL_ (n, [(Instr__LOOP (bt, instr))], ((List.map fun_admininstr_val val) ++ (List.map fun_admininstr_instr instr))))]))
  | Step_pure__if_true (bt : Blocktype) (c : C_numtype) (instr_1 : (list Instr)) (instr_2 : (list Instr)) : 
    (c <> 0) -> 
    (Step_pure ([(Admininstr__CONST (Numtype__I32, c)); (Admininstr__IF (bt, instr_1, instr_2))], [(Admininstr__BLOCK (bt, instr_1))]))
  | Step_pure__if_false (bt : Blocktype) (c : C_numtype) (instr_1 : (list Instr)) (instr_2 : (list Instr)) : 
    (c = 0) -> 
    (Step_pure ([(Admininstr__CONST (Numtype__I32, c)); (Admininstr__IF (bt, instr_1, instr_2))], [(Admininstr__BLOCK (bt, instr_2))]))
  | Step_pure__label_vals (instr : (list Instr)) (n : reserved__N) (val : (list Val)) : 
    (Step_pure ([(Admininstr__LABEL_ (n, instr, (List.map fun_admininstr_val val)))], (List.map fun_admininstr_val val)))
  | Step_pure__br_zero (instr : (list Instr)) (instr' : (list Instr)) (n : reserved__N) (val : (list Val)) (val' : (list Val)) : 
    (List.length (val) = n) -> 
    (Step_pure ([(Admininstr__LABEL_ (n, instr', ((List.map fun_admininstr_val val') ++ ((List.map fun_admininstr_val val) ++ ([(Admininstr__BR 0)] ++ (List.map fun_admininstr_instr instr))))))], ((List.map fun_admininstr_val val) ++ (List.map fun_admininstr_instr instr'))))
  | Step_pure__br_succ (instr : (list Instr)) (instr' : (list Instr)) (l : Labelidx) (n : reserved__N) (val : (list Val)) : 
    (Step_pure ([(Admininstr__LABEL_ (n, instr', ((List.map fun_admininstr_val val) ++ ([(Admininstr__BR (l + 1))] ++ (List.map fun_admininstr_instr instr)))))], ((List.map fun_admininstr_val val) ++ [(Admininstr__BR l)])))
  | Step_pure__br_if_true (c : C_numtype) (l : Labelidx) : 
    (c <> 0) -> 
    (Step_pure ([(Admininstr__CONST (Numtype__I32, c)); (Admininstr__BR_IF l)], [(Admininstr__BR l)]))
  | Step_pure__br_if_false (c : C_numtype) (l : Labelidx) : 
    (c = 0) -> 
    (Step_pure ([(Admininstr__CONST (Numtype__I32, c)); (Admininstr__BR_IF l)], nil))
  | Step_pure__br_table_lt (i : nat) (l : (list Labelidx)) (l' : Labelidx) : 
    (i < List.length (l)) -> 
    (Step_pure ([(Admininstr__CONST (Numtype__I32, i)); (Admininstr__BR_TABLE (l, l'))], [(Admininstr__BR (lookup_total l i))]))
  | Step_pure__br_table_ge (i : nat) (l : (list Labelidx)) (l' : Labelidx) : 
    (i >= List.length (l)) -> 
    (Step_pure ([(Admininstr__CONST (Numtype__I32, i)); (Admininstr__BR_TABLE (l, l'))], [(Admininstr__BR l')]))
  | Step_pure__frame_vals (f : Frame) (n : reserved__N) (val : (list Val)) : 
    (List.length (val) = n) -> 
    (Step_pure ([(Admininstr__FRAME_ (n, f, (List.map fun_admininstr_val val)))], (List.map fun_admininstr_val val)))
  | Step_pure__return_frame (f : Frame) (instr : (list Instr)) (n : reserved__N) (val : (list Val)) (val' : (list Val)) : 
    (List.length (val) = n) -> 
    (Step_pure ([(Admininstr__FRAME_ (n, f, ((List.map fun_admininstr_val val') ++ ((List.map fun_admininstr_val val) ++ ([Admininstr__RETURN] ++ (List.map fun_admininstr_instr instr))))))], (List.map fun_admininstr_val val)))
  | Step_pure__return_label (instr : (list Instr)) (instr' : (list Instr)) (k : nat) (val : (list Val)) : 
    (Step_pure ([(Admininstr__LABEL_ (k, instr', ((List.map fun_admininstr_val val) ++ ([Admininstr__RETURN] ++ (List.map fun_admininstr_instr instr)))))], ((List.map fun_admininstr_val val) ++ [Admininstr__RETURN])))
  | Step_pure__unop_val (c : C_numtype) (c_1 : C_numtype) (nt : Numtype) (unop : Unop_numtype) : 
    ((fun_unop (unop, nt, c_1)) = [c]) -> 
    (Step_pure ([(Admininstr__CONST (nt, c_1)); (Admininstr__UNOP (nt, unop))], [(Admininstr__CONST (nt, c))]))
  | Step_pure__unop_trap (c_1 : C_numtype) (nt : Numtype) (unop : Unop_numtype) : 
    ((fun_unop (unop, nt, c_1)) = nil) -> 
    (Step_pure ([(Admininstr__CONST (nt, c_1)); (Admininstr__UNOP (nt, unop))], [Admininstr__TRAP]))
  | Step_pure__binop_val (binop : Binop_numtype) (c : C_numtype) (c_1 : C_numtype) (c_2 : C_numtype) (nt : Numtype) : 
    ((fun_binop (binop, nt, c_1, c_2)) = [c]) -> 
    (Step_pure ([(Admininstr__CONST (nt, c_1)); (Admininstr__CONST (nt, c_2)); (Admininstr__BINOP (nt, binop))], [(Admininstr__CONST (nt, c))]))
  | Step_pure__binop_trap (binop : Binop_numtype) (c_1 : C_numtype) (c_2 : C_numtype) (nt : Numtype) : 
    ((fun_binop (binop, nt, c_1, c_2)) = nil) -> 
    (Step_pure ([(Admininstr__CONST (nt, c_1)); (Admininstr__CONST (nt, c_2)); (Admininstr__BINOP (nt, binop))], [Admininstr__TRAP]))
  | Step_pure__testop (c : C_numtype) (c_1 : C_numtype) (nt : Numtype) (testop : Testop_numtype) : 
    (c = (fun_testop (testop, nt, c_1))) -> 
    (Step_pure ([(Admininstr__CONST (nt, c_1)); (Admininstr__TESTOP (nt, testop))], [(Admininstr__CONST (Numtype__I32, c))]))
  | Step_pure__relop (c : C_numtype) (c_1 : C_numtype) (c_2 : C_numtype) (nt : Numtype) (relop : Relop_numtype) : 
    (c = (fun_relop (relop, nt, c_1, c_2))) -> 
    (Step_pure ([(Admininstr__CONST (nt, c_1)); (Admininstr__CONST (nt, c_2)); (Admininstr__RELOP (nt, relop))], [(Admininstr__CONST (Numtype__I32, c))]))
  | Step_pure__extend (c : C_numtype) (n : reserved__N) (nt : Numtype) (o0 : nat) : 
    ((fun_size (fun_valtype_numtype nt)) = (Some o0)) -> 
    (Step_pure ([(Admininstr__CONST (nt, c)); (Admininstr__EXTEND (nt, n))], [(Admininstr__CONST (nt, (fun_ext (n, o0, Sx__S, c))))]))
  | Step_pure__cvtop_val (c : C_numtype) (c_1 : C_numtype) (cvtop : Cvtop) (nt : Numtype) (nt_1 : Numtype) (nt_2 : Numtype) (sx : (option Sx)) : 
    ((fun_cvtop (nt_1, cvtop, nt_2, sx, c_1)) = [c]) -> 
    (Step_pure ([(Admininstr__CONST (nt, c_1)); (Admininstr__CVTOP (nt_1, cvtop, nt_2, sx))], [(Admininstr__CONST (nt, c))]))
  | Step_pure__cvtop_trap (c_1 : C_numtype) (cvtop : Cvtop) (nt : Numtype) (nt_1 : Numtype) (nt_2 : Numtype) (sx : (option Sx)) : 
    ((fun_cvtop (nt_1, cvtop, nt_2, sx, c_1)) = nil) -> 
    (Step_pure ([(Admininstr__CONST (nt, c_1)); (Admininstr__CVTOP (nt_1, cvtop, nt_2, sx))], [Admininstr__TRAP]))
  | Step_pure__ref_is_null_true (rt : Reftype) (val : Val) : 
    (val = (Val__REF_NULL rt)) -> 
    (Step_pure ([(fun_admininstr_val val); Admininstr__REF_IS_NULL], [(Admininstr__CONST (Numtype__I32, 1))]))
  | Step_pure__ref_is_null_false (val : Val) : 
    (~  (Step_pure_before_ref_is_null_false [(fun_admininstr_val val); Admininstr__REF_IS_NULL])) -> 
    (Step_pure ([(fun_admininstr_val val); Admininstr__REF_IS_NULL], [(Admininstr__CONST (Numtype__I32, 0))]))
  | Step_pure__local_tee (val : Val) (x : Idx) : 
    (Step_pure ([(fun_admininstr_val val); (Admininstr__LOCAL_TEE x)], [(fun_admininstr_val val); (fun_admininstr_val val); (Admininstr__LOCAL_SET x)]))
.

(** Relation definition : Step_read_before_call_indirect_trap **)
Inductive Step_read_before_call_indirect_trap : Config -> Prop := 
  | Step_read_before_call_indirect_trap__call_indirect_call (a : Addr) (ft : Functype) (func : Func) (i : nat) (m : Moduleinst) (x : Idx) (z : State) : 
    (i < List.length ((fun_table (z, x)))) -> 
    (a < List.length ((fun_funcinst z))) -> 
    ((lookup_total (fun_table (z, x)) i) = (Ref__REF_FUNC_ADDR a)) -> 
    ((lookup_total (fun_funcinst z) a) = (m, func)) -> 
    (Step_read_before_call_indirect_trap (z, [(Admininstr__CONST (Numtype__I32, i)); (Admininstr__CALL_INDIRECT (x, ft))]))
.

(** Relation definition : Step_read_before_table_fill_zero **)
Inductive Step_read_before_table_fill_zero : Config -> Prop := 
  | Step_read_before_table_fill_zero__table_fill_trap (i : nat) (n : reserved__N) (val : Val) (x : Idx) (z : State) : 
    ((i + n) > List.length ((fun_table (z, x)))) -> 
    (Step_read_before_table_fill_zero (z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_FILL x)]))
.

(** Relation definition : Step_read_before_table_fill_succ **)
Inductive Step_read_before_table_fill_succ : Config -> Prop := 
  | Step_read_before_table_fill_succ__table_fill_zero (i : nat) (n : reserved__N) (val : Val) (x : Idx) (z : State) : 
    (~  (Step_read_before_table_fill_zero (z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_FILL x)]))) -> 
    (n = 0) -> 
    (Step_read_before_table_fill_succ (z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_FILL x)]))
  | Step_read_before_table_fill_succ__table_fill_trap (i : nat) (n : reserved__N) (val : Val) (x : Idx) (z : State) : 
    ((i + n) > List.length ((fun_table (z, x)))) -> 
    (Step_read_before_table_fill_succ (z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_FILL x)]))
.

(** Relation definition : Step_read_before_table_copy_zero **)
Inductive Step_read_before_table_copy_zero : Config -> Prop := 
  | Step_read_before_table_copy_zero__table_copy_trap (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_table (z, y)))) \/ ((j + n) > List.length ((fun_table (z, x))))) -> 
    (Step_read_before_table_copy_zero (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_COPY (x, y))]))
.

(** Relation definition : Step_read_before_table_copy_le **)
Inductive Step_read_before_table_copy_le : Config -> Prop := 
  | Step_read_before_table_copy_le__table_copy_zero (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (~  (Step_read_before_table_copy_zero (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_COPY (x, y))]))) -> 
    (n = 0) -> 
    (Step_read_before_table_copy_le (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_COPY (x, y))]))
  | Step_read_before_table_copy_le__table_copy_trap (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_table (z, y)))) \/ ((j + n) > List.length ((fun_table (z, x))))) -> 
    (Step_read_before_table_copy_le (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_COPY (x, y))]))
.

(** Relation definition : Step_read_before_table_copy_gt **)
Inductive Step_read_before_table_copy_gt : Config -> Prop := 
  | Step_read_before_table_copy_gt__table_copy_le (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (~  (Step_read_before_table_copy_le (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_COPY (x, y))]))) -> 
    (j <= i) -> 
    (Step_read_before_table_copy_gt (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_COPY (x, y))]))
  | Step_read_before_table_copy_gt__table_copy_zero (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (~  (Step_read_before_table_copy_zero (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_COPY (x, y))]))) -> 
    (n = 0) -> 
    (Step_read_before_table_copy_gt (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_COPY (x, y))]))
  | Step_read_before_table_copy_gt__table_copy_trap (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_table (z, y)))) \/ ((j + n) > List.length ((fun_table (z, x))))) -> 
    (Step_read_before_table_copy_gt (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_COPY (x, y))]))
.

(** Relation definition : Step_read_before_table_init_zero **)
Inductive Step_read_before_table_init_zero : Config -> Prop := 
  | Step_read_before_table_init_zero__table_init_trap (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_elem (z, y)))) \/ ((j + n) > List.length ((fun_table (z, x))))) -> 
    (Step_read_before_table_init_zero (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_INIT (x, y))]))
.

(** Relation definition : Step_read_before_table_init_succ **)
Inductive Step_read_before_table_init_succ : Config -> Prop := 
  | Step_read_before_table_init_succ__table_init_zero (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (~  (Step_read_before_table_init_zero (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_INIT (x, y))]))) -> 
    (n = 0) -> 
    (Step_read_before_table_init_succ (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_INIT (x, y))]))
  | Step_read_before_table_init_succ__table_init_trap (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_elem (z, y)))) \/ ((j + n) > List.length ((fun_table (z, x))))) -> 
    (Step_read_before_table_init_succ (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_INIT (x, y))]))
.

(** Relation definition : Step_read_before_memory_fill_zero **)
Inductive Step_read_before_memory_fill_zero : Config -> Prop := 
  | Step_read_before_memory_fill_zero__memory_fill_trap (i : nat) (n : reserved__N) (val : Val) (z : State) : 
    ((i + n) > List.length ((fun_mem (z, 0)))) -> 
    (Step_read_before_memory_fill_zero (z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_FILL]))
.

(** Relation definition : Step_read_before_memory_fill_succ **)
Inductive Step_read_before_memory_fill_succ : Config -> Prop := 
  | Step_read_before_memory_fill_succ__memory_fill_zero (i : nat) (n : reserved__N) (val : Val) (z : State) : 
    (~  (Step_read_before_memory_fill_zero (z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_FILL]))) -> 
    (n = 0) -> 
    (Step_read_before_memory_fill_succ (z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_FILL]))
  | Step_read_before_memory_fill_succ__memory_fill_trap (i : nat) (n : reserved__N) (val : Val) (z : State) : 
    ((i + n) > List.length ((fun_mem (z, 0)))) -> 
    (Step_read_before_memory_fill_succ (z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_FILL]))
.

(** Relation definition : Step_read_before_memory_copy_zero **)
Inductive Step_read_before_memory_copy_zero : Config -> Prop := 
  | Step_read_before_memory_copy_zero__memory_copy_trap (i : nat) (j : nat) (n : reserved__N) (z : State) : 
    (((i + n) > List.length ((fun_table (z, 0)))) \/ ((j + n) > List.length ((fun_table (z, 0))))) -> 
    (Step_read_before_memory_copy_zero (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_COPY]))
.

(** Relation definition : Step_read_before_memory_copy_le **)
Inductive Step_read_before_memory_copy_le : Config -> Prop := 
  | Step_read_before_memory_copy_le__memory_copy_zero (i : nat) (j : nat) (n : reserved__N) (z : State) : 
    (~  (Step_read_before_memory_copy_zero (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_COPY]))) -> 
    (n = 0) -> 
    (Step_read_before_memory_copy_le (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_COPY]))
  | Step_read_before_memory_copy_le__memory_copy_trap (i : nat) (j : nat) (n : reserved__N) (z : State) : 
    (((i + n) > List.length ((fun_table (z, 0)))) \/ ((j + n) > List.length ((fun_table (z, 0))))) -> 
    (Step_read_before_memory_copy_le (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_COPY]))
.

(** Relation definition : Step_read_before_memory_copy_gt **)
Inductive Step_read_before_memory_copy_gt : Config -> Prop := 
  | Step_read_before_memory_copy_gt__memory_copy_le (i : nat) (j : nat) (n : reserved__N) (z : State) : 
    (~  (Step_read_before_memory_copy_le (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_COPY]))) -> 
    (j <= i) -> 
    (Step_read_before_memory_copy_gt (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_COPY]))
  | Step_read_before_memory_copy_gt__memory_copy_zero (i : nat) (j : nat) (n : reserved__N) (z : State) : 
    (~  (Step_read_before_memory_copy_zero (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_COPY]))) -> 
    (n = 0) -> 
    (Step_read_before_memory_copy_gt (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_COPY]))
  | Step_read_before_memory_copy_gt__memory_copy_trap (i : nat) (j : nat) (n : reserved__N) (z : State) : 
    (((i + n) > List.length ((fun_table (z, 0)))) \/ ((j + n) > List.length ((fun_table (z, 0))))) -> 
    (Step_read_before_memory_copy_gt (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_COPY]))
.

(** Relation definition : Step_read_before_memory_init_zero **)
Inductive Step_read_before_memory_init_zero : Config -> Prop := 
  | Step_read_before_memory_init_zero__memory_init_trap (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_data (z, y)))) \/ ((j + n) > List.length ((fun_mem (z, 0))))) -> 
    (Step_read_before_memory_init_zero (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__MEMORY_INIT x)]))
.

(** Relation definition : Step_read_before_memory_init_succ **)
Inductive Step_read_before_memory_init_succ : Config -> Prop := 
  | Step_read_before_memory_init_succ__memory_init_zero (i : nat) (j : nat) (n : reserved__N) (x : Idx) (z : State) : 
    (~  (Step_read_before_memory_init_zero (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__MEMORY_INIT x)]))) -> 
    (n = 0) -> 
    (Step_read_before_memory_init_succ (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__MEMORY_INIT x)]))
  | Step_read_before_memory_init_succ__memory_init_trap (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_data (z, y)))) \/ ((j + n) > List.length ((fun_mem (z, 0))))) -> 
    (Step_read_before_memory_init_succ (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__MEMORY_INIT x)]))
.

(** Relation definition : Step_read **)
Inductive Step_read : (Config * (list Admininstr))%type -> Prop := 
  | Step_read__call (x : Idx) (z : State) : 
    (x < List.length ((fun_funcaddr z))) -> 
    (Step_read ((z, [(Admininstr__CALL x)]), [(Admininstr__CALL_ADDR (lookup_total (fun_funcaddr z) x))]))
  | Step_read__call_indirect_call (a : Addr) (ft : Functype) (func : Func) (i : nat) (m : Moduleinst) (x : Idx) (z : State) : 
    (i < List.length ((fun_table (z, x)))) -> 
    (a < List.length ((fun_funcinst z))) -> 
    ((lookup_total (fun_table (z, x)) i) = (Ref__REF_FUNC_ADDR a)) -> 
    ((lookup_total (fun_funcinst z) a) = (m, func)) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, i)); (Admininstr__CALL_INDIRECT (x, ft))]), [(Admininstr__CALL_ADDR a)]))
  | Step_read__call_indirect_trap (ft : Functype) (i : nat) (x : Idx) (z : State) : 
    (~  (Step_read_before_call_indirect_trap (z, [(Admininstr__CONST (Numtype__I32, i)); (Admininstr__CALL_INDIRECT (x, ft))]))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, i)); (Admininstr__CALL_INDIRECT (x, ft))]), [Admininstr__TRAP]))
  | Step_read__call_addr (a : Addr) (f : Frame) (instr : (list Instr)) (k : nat) (m : Moduleinst) (n : reserved__N) (t : (list Valtype)) (t_1 : (list Valtype)) (t_2 : (list Valtype)) (val : (list Val)) (z : State) (o0 : (list Val)) : 
    (List.length (t) = List.length (o0)) -> 
    (a < List.length ((fun_funcinst z))) -> 
    (List.length (t_1) = k) -> 
    (List.length (t_2) = n) -> 
    (List.length (val) = k) -> 
    (List.Forall2 (fun t o0 => ((fun_default_ t) = (Some o0))) t o0) -> 
    ((lookup_total (fun_funcinst z) a) = (m, ((t_1, t_2), t, instr))) -> 
    (f = {| Frame__LOCAL := (val ++ o0); Frame__MODULE := m |}) -> 
    (Step_read ((z, ((List.map fun_admininstr_val val) ++ [(Admininstr__CALL_ADDR a)])), [(Admininstr__FRAME_ (n, f, [(Admininstr__LABEL_ (n, nil, (List.map fun_admininstr_instr instr)))]))]))
  | Step_read__ref_func (x : Idx) (z : State) : 
    (x < List.length ((fun_funcaddr z))) -> 
    (Step_read ((z, [(Admininstr__REF_FUNC x)]), [(Admininstr__REF_FUNC_ADDR (lookup_total (fun_funcaddr z) x))]))
  | Step_read__local_get (x : Idx) (z : State) : 
    (Step_read ((z, [(Admininstr__LOCAL_GET x)]), [(fun_admininstr_val (fun_local (z, x)))]))
  | Step_read__global_get (x : Idx) (z : State) : 
    (Step_read ((z, [(Admininstr__GLOBAL_GET x)]), [(fun_admininstr_globalinst (fun_global (z, x)))]))
  | Step_read__table_get_trap (i : nat) (x : Idx) (z : State) : 
    (i >= List.length ((fun_table (z, x)))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, i)); (Admininstr__TABLE_GET x)]), [Admininstr__TRAP]))
  | Step_read__table_get_val (i : nat) (x : Idx) (z : State) : 
    (i < List.length ((fun_table (z, x)))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, i)); (Admininstr__TABLE_GET x)]), [(fun_admininstr_ref (lookup_total (fun_table (z, x)) i))]))
  | Step_read__table_size (n : reserved__N) (x : Idx) (z : State) : 
    (List.length ((fun_table (z, x))) = n) -> 
    (Step_read ((z, [(Admininstr__TABLE_SIZE x)]), [(Admininstr__CONST (Numtype__I32, n))]))
  | Step_read__table_fill_trap (i : nat) (n : reserved__N) (val : Val) (x : Idx) (z : State) : 
    ((i + n) > List.length ((fun_table (z, x)))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_FILL x)]), [Admininstr__TRAP]))
  | Step_read__table_fill_zero (i : nat) (n : reserved__N) (val : Val) (x : Idx) (z : State) : 
    (~  (Step_read_before_table_fill_zero (z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_FILL x)]))) -> 
    (n = 0) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_FILL x)]), nil))
  | Step_read__table_fill_succ (i : nat) (n : reserved__N) (val : Val) (x : Idx) (z : State) : 
    (~  (Step_read_before_table_fill_succ (z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_FILL x)]))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_FILL x)]), [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__TABLE_SET x); (Admininstr__CONST (Numtype__I32, (i + 1))); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, (n - 1))); (Admininstr__TABLE_FILL x)]))
  | Step_read__table_copy_trap (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_table (z, y)))) \/ ((j + n) > List.length ((fun_table (z, x))))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_COPY (x, y))]), [Admininstr__TRAP]))
  | Step_read__table_copy_zero (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (~  (Step_read_before_table_copy_zero (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_COPY (x, y))]))) -> 
    (n = 0) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_COPY (x, y))]), nil))
  | Step_read__table_copy_le (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (~  (Step_read_before_table_copy_le (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_COPY (x, y))]))) -> 
    (j <= i) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_COPY (x, y))]), [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__TABLE_GET y); (Admininstr__TABLE_SET x); (Admininstr__CONST (Numtype__I32, (j + 1))); (Admininstr__CONST (Numtype__I32, (i + 1))); (Admininstr__CONST (Numtype__I32, (n - 1))); (Admininstr__TABLE_COPY (x, y))]))
  | Step_read__table_copy_gt (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (~  (Step_read_before_table_copy_gt (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_COPY (x, y))]))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_COPY (x, y))]), [(Admininstr__CONST (Numtype__I32, ((j + n) - 1))); (Admininstr__CONST (Numtype__I32, ((i + n) - 1))); (Admininstr__TABLE_GET y); (Admininstr__TABLE_SET x); (Admininstr__CONST (Numtype__I32, (j + 1))); (Admininstr__CONST (Numtype__I32, (i + 1))); (Admininstr__CONST (Numtype__I32, (n - 1))); (Admininstr__TABLE_COPY (x, y))]))
  | Step_read__table_init_trap (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_elem (z, y)))) \/ ((j + n) > List.length ((fun_table (z, x))))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_INIT (x, y))]), [Admininstr__TRAP]))
  | Step_read__table_init_zero (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (~  (Step_read_before_table_init_zero (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_INIT (x, y))]))) -> 
    (n = 0) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_INIT (x, y))]), nil))
  | Step_read__table_init_succ (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (i < List.length ((fun_elem (z, y)))) -> 
    (~  (Step_read_before_table_init_succ (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_INIT (x, y))]))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_INIT (x, y))]), [(Admininstr__CONST (Numtype__I32, j)); (fun_admininstr_ref (lookup_total (fun_elem (z, y)) i)); (Admininstr__TABLE_SET x); (Admininstr__CONST (Numtype__I32, (j + 1))); (Admininstr__CONST (Numtype__I32, (i + 1))); (Admininstr__CONST (Numtype__I32, (n - 1))); (Admininstr__TABLE_INIT (x, y))]))
  | Step_read__load_num_trap (i : nat) (n_A : reserved__N) (n_O : reserved__N) (nt : Numtype) (z : State) (o0 : nat) : 
    ((fun_size (fun_valtype_numtype nt)) = (Some o0)) -> 
    (((i + n_O) + (((Nat.div o0) 8))) >= List.length ((fun_mem (z, 0)))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, i)); (Admininstr__LOAD (nt, None, n_A, n_O))]), [Admininstr__TRAP]))
  | Step_read__load_num_val (c : C_numtype) (i : nat) (n_A : reserved__N) (n_O : reserved__N) (nt : Numtype) (z : State) (o0 : nat) (o1 : nat) : 
    ((fun_size (fun_valtype_numtype nt)) = (Some o0)) -> 
    ((fun_size (fun_valtype_numtype nt)) = (Some o1)) -> 
    ((fun_bytes_ (o0, c)) = default_val (* FIXME: $mem(z, 0)[(i + n_O) : (o1 / 8)] *)) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, i)); (Admininstr__LOAD (nt, None, n_A, n_O))]), [(Admininstr__CONST (nt, c))]))
  | Step_read__load_pack_trap (i : nat) (n : reserved__N) (n_A : reserved__N) (n_O : reserved__N) (nt : Numtype) (sx : Sx) (z : State) : 
    (((i + n_O) + (((Nat.div n) 8))) >= List.length ((fun_mem (z, 0)))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, i)); (Admininstr__LOAD (nt, (Some (n, sx)), n_A, n_O))]), [Admininstr__TRAP]))
  | Step_read__load_pack_val (c : C_numtype) (i : nat) (n : reserved__N) (n_A : reserved__N) (n_O : reserved__N) (nt : Numtype) (sx : Sx) (z : State) : 
    ((fun_bytes_ (n, c)) = default_val (* FIXME: $mem(z, 0)[(i + n_O) : (n / 8)] *)) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, i)); (Admininstr__LOAD (nt, (Some (n, sx)), n_A, n_O))]), [(Admininstr__CONST (nt, c))]))
  | Step_read__memory_fill_trap (i : nat) (n : reserved__N) (val : Val) (z : State) : 
    ((i + n) > List.length ((fun_mem (z, 0)))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_FILL]), [Admininstr__TRAP]))
  | Step_read__memory_fill_zero (i : nat) (n : reserved__N) (val : Val) (z : State) : 
    (~  (Step_read_before_memory_fill_zero (z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_FILL]))) -> 
    (n = 0) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_FILL]), nil))
  | Step_read__memory_fill_succ (i : nat) (n : reserved__N) (val : Val) (z : State) : 
    (~  (Step_read_before_memory_fill_succ (z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_FILL]))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_FILL]), [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_val val); (Admininstr__STORE (Numtype__I32, (Some 8), 0, 0)); (Admininstr__CONST (Numtype__I32, (i + 1))); (fun_admininstr_val val); (Admininstr__CONST (Numtype__I32, (n - 1))); Admininstr__MEMORY_FILL]))
  | Step_read__memory_copy_trap (i : nat) (j : nat) (n : reserved__N) (z : State) : 
    (((i + n) > List.length ((fun_table (z, 0)))) \/ ((j + n) > List.length ((fun_table (z, 0))))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_COPY]), [Admininstr__TRAP]))
  | Step_read__memory_copy_zero (i : nat) (j : nat) (n : reserved__N) (z : State) : 
    (~  (Step_read_before_memory_copy_zero (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_COPY]))) -> 
    (n = 0) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_COPY]), nil))
  | Step_read__memory_copy_le (i : nat) (j : nat) (n : reserved__N) (z : State) : 
    (~  (Step_read_before_memory_copy_le (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_COPY]))) -> 
    (j <= i) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_COPY]), [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__LOAD (Numtype__I32, (Some (8, Sx__U)), 0, 0)); (Admininstr__STORE (Numtype__I32, (Some 8), 0, 0)); (Admininstr__CONST (Numtype__I32, (j + 1))); (Admininstr__CONST (Numtype__I32, (i + 1))); (Admininstr__CONST (Numtype__I32, (n - 1))); Admininstr__MEMORY_COPY]))
  | Step_read__memory_copy_gt (i : nat) (j : nat) (n : reserved__N) (z : State) : 
    (~  (Step_read_before_memory_copy_gt (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_COPY]))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_COPY]), [(Admininstr__CONST (Numtype__I32, ((j + n) - 1))); (Admininstr__CONST (Numtype__I32, ((i + n) - 1))); (Admininstr__LOAD (Numtype__I32, (Some (8, Sx__U)), 0, 0)); (Admininstr__STORE (Numtype__I32, (Some 8), 0, 0)); (Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, (n - 1))); Admininstr__MEMORY_COPY]))
  | Step_read__memory_init_trap (i : nat) (j : nat) (n : reserved__N) (x : Idx) (y : Idx) (z : State) : 
    (((i + n) > List.length ((fun_data (z, y)))) \/ ((j + n) > List.length ((fun_mem (z, 0))))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__MEMORY_INIT x)]), [Admininstr__TRAP]))
  | Step_read__memory_init_zero (i : nat) (j : nat) (n : reserved__N) (x : Idx) (z : State) : 
    (~  (Step_read_before_memory_init_zero (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__MEMORY_INIT x)]))) -> 
    (n = 0) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__MEMORY_INIT x)]), nil))
  | Step_read__memory_init_succ (i : nat) (j : nat) (n : reserved__N) (x : Idx) (z : State) : 
    (i < List.length ((fun_data (z, x)))) -> 
    (~  (Step_read_before_memory_init_succ (z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__MEMORY_INIT x)]))) -> 
    (Step_read ((z, [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__MEMORY_INIT x)]), [(Admininstr__CONST (Numtype__I32, j)); (Admininstr__CONST (Numtype__I32, (lookup_total (fun_data (z, x)) i))); (Admininstr__STORE (Numtype__I32, (Some 8), 0, 0)); (Admininstr__CONST (Numtype__I32, (j + 1))); (Admininstr__CONST (Numtype__I32, (i + 1))); (Admininstr__CONST (Numtype__I32, (n - 1))); (Admininstr__MEMORY_INIT x)]))
.

(** Relation definition : Step **)
Inductive Step : (Config * Config)%type -> Prop := 
  | Step__pure (instr : (list Instr)) (instr' : (list Instr)) (z : State) : 
    (Step_pure ((List.map fun_admininstr_instr instr), (List.map fun_admininstr_instr instr'))) -> 
    (Step ((z, (List.map fun_admininstr_instr instr)), (z, (List.map fun_admininstr_instr instr'))))
  | Step__read (instr : (list Instr)) (instr' : (list Instr)) (z : State) : 
    (Step_read ((z, (List.map fun_admininstr_instr instr)), (List.map fun_admininstr_instr instr'))) -> 
    (Step ((z, (List.map fun_admininstr_instr instr)), (z, (List.map fun_admininstr_instr instr'))))
  | Step__local_set (val : Val) (x : Idx) (z : State) : 
    (Step ((z, [(fun_admininstr_val val); (Admininstr__LOCAL_SET x)]), ((fun_with_local (z, x, val)), nil)))
  | Step__global_set (val : Val) (x : Idx) (z : State) : 
    (Step ((z, [(fun_admininstr_val val); (Admininstr__GLOBAL_SET x)]), ((fun_with_global (z, x, val)), nil)))
  | Step__table_set_trap (i : nat) (ref : Ref) (x : Idx) (z : State) : 
    (i >= List.length ((fun_table (z, x)))) -> 
    (Step ((z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_ref ref); (Admininstr__TABLE_GET x)]), (z, [Admininstr__TRAP])))
  | Step__table_set_val (i : nat) (ref : Ref) (x : Idx) (z : State) : 
    (i < List.length ((fun_table (z, x)))) -> 
    (Step ((z, [(Admininstr__CONST (Numtype__I32, i)); (fun_admininstr_ref ref); (Admininstr__TABLE_GET x)]), ((fun_with_table (z, x, i, ref)), nil)))
  | Step__table_grow_succeed (n : reserved__N) (ref : Ref) (x : Idx) (z : State) : 
    (Step ((z, [(fun_admininstr_ref ref); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_GROW x)]), ((fun_with_tableext (z, x, [ref])), [(Admininstr__CONST (Numtype__I32, List.length ((fun_table (z, x)))))])))
  | Step__table_grow_fail (n : reserved__N) (ref : Ref) (x : Idx) (z : State) : 
    (Step ((z, [(fun_admininstr_ref ref); (Admininstr__CONST (Numtype__I32, n)); (Admininstr__TABLE_GROW x)]), (z, [(Admininstr__CONST (Numtype__I32, (0 - 1)))])))
  | Step__elem_drop (x : Idx) (z : State) : 
    (Step ((z, [(Admininstr__ELEM_DROP x)]), ((fun_with_elem (z, x, nil)), nil)))
  | Step__store_num_trap (c : C_numtype) (i : nat) (n_A : reserved__N) (n_O : reserved__N) (nt : Numtype) (z : State) (o0 : nat) : 
    ((fun_size (fun_valtype_numtype nt)) = (Some o0)) -> 
    (((i + n_O) + (((Nat.div o0) 8))) >= List.length ((fun_mem (z, 0)))) -> 
    (Step ((z, [(Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, c)); (Admininstr__STORE (nt, None, n_A, n_O))]), (z, [Admininstr__TRAP])))
  | Step__store_num_val (b : (list Byte)) (c : C_numtype) (i : nat) (n_A : reserved__N) (n_O : reserved__N) (nt : Numtype) (z : State) (o0 : nat) (o1 : nat) : 
    ((fun_size (fun_valtype_numtype nt)) = (Some o0)) -> 
    ((fun_size (fun_valtype_numtype nt)) = (Some o1)) -> 
    (b = (fun_bytes_ (o1, c))) -> 
    (Step ((z, [(Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, c)); (Admininstr__STORE (nt, None, n_A, n_O))]), ((fun_with_mem (z, 0, (i + n_O), (((Nat.div o0) 8)), b)), nil)))
  | Step__store_pack_trap (c : C_numtype) (i : nat) (n : reserved__N) (n_A : reserved__N) (n_O : reserved__N) (nt : Numtype) (z : State) : 
    (((i + n_O) + (((Nat.div n) 8))) >= List.length ((fun_mem (z, 0)))) -> 
    (Step ((z, [(Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, c)); (Admininstr__STORE (nt, (Some n), n_A, n_O))]), (z, [Admininstr__TRAP])))
  | Step__store_pack_val (b : (list Byte)) (c : C_numtype) (i : nat) (n : reserved__N) (n_A : reserved__N) (n_O : reserved__N) (nt : Numtype) (z : State) (o0 : nat) : 
    ((fun_size (fun_valtype_numtype nt)) = (Some o0)) -> 
    (b = (fun_bytes_ (n, (fun_wrap_ ((o0, n), c))))) -> 
    (Step ((z, [(Admininstr__CONST (Numtype__I32, i)); (Admininstr__CONST (Numtype__I32, c)); (Admininstr__STORE (nt, (Some n), n_A, n_O))]), ((fun_with_mem (z, 0, (i + n_O), (((Nat.div n) 8)), b)), nil)))
  | Step__memory_grow_succeed (n : reserved__N) (z : State) : 
    (Step ((z, [(Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_GROW]), ((fun_with_memext (z, 0, [0])), [(Admininstr__CONST (Numtype__I32, List.length ((fun_mem (z, 0)))))])))
  | Step__memory_grow_fail (n : reserved__N) (z : State) : 
    (Step ((z, [(Admininstr__CONST (Numtype__I32, n)); Admininstr__MEMORY_GROW]), (z, [(Admininstr__CONST (Numtype__I32, (0 - 1)))])))
  | Step__data_drop (x : Idx) (z : State) : 
    (Step ((z, [(Admininstr__DATA_DROP x)]), ((fun_with_data (z, x, nil)), nil)))
.
