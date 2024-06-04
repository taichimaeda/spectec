(* Exported Code *)
From Coq Require Import String List Unicode.Utf8.
From RecordUpdate Require Import RecordSet.
Require Import NArith.
Require Import Arith.
Declare Scope wasm_scope.

Class Inhabited (T: Type) := { default_val : T }.

Definition lookup_total {T: Type} {_: Inhabited T} (l: list T) (n: nat) : T :=
	List.nth n l default_val.

Definition the {T : Type} {_ : Inhabited T} (arg : option T) : T :=
	match arg with
		| None => default_val
		| Some v => v
	end.

Definition list_zipWith {X Y Z : Type} (f : X -> Y -> Z) (xs : list X) (ys : list Y) : list Z :=
	map (fun '(x, y) => f x y) (combine xs ys).

Definition option_zipWith {α β γ: Type} (f: α → β → γ) (x: option α) (y: option β): option γ := 
	match x, y with
		| Some x, Some y => Some (f x y)
		| _, _ => None
	end.

Fixpoint list_update {α: Type} (l: list α) (n: nat) (y: α): list α :=
	match l, n with
		| nil, _ => nil
		| x :: l', 0 => y :: l'
		| x :: l', S n => x :: list_update l' n y
	end.

Definition option_append {α: Type} (x y: option α) : option α :=
	match x with
		| Some _ => x
		| None => y
	end.

Definition option_map {α β : Type} (f : α -> β) (x : option α) : option β :=
	match x with
		| Some x => Some (f x)
		| _ => None
	end.

Fixpoint list_update_func {α: Type} (l: list α) (n: nat) (y: α -> α): list α :=
	match l, n with
		| nil, _ => nil
		| x :: l', 0 => (y x) :: l'
		| x :: l', S n => x :: list_update_func l' n y
	end.

Fixpoint list_slice {α: Type} (l: list α) (i: nat) (j: nat): list α :=
	match l, i, j with
		| nil, _, _ => nil
		| x :: l', 0, 0 => nil
		| x :: l', S n, 0 => nil
		| x :: l', 0, S m => x :: list_slice l' 0 m
		| x :: l', S n, S m => list_slice l' n m
	end.

Fixpoint list_slice_update {α: Type} (l: list α) (i: nat) (j: nat) (update_l: list α): list α :=
	match l, i, j, update_l with
		| nil, _, _, _ => nil
		| l', _, _, nil => l'
		| x :: l', 0, 0, _ => nil
		| x :: l', S n, 0, _ => nil
		| x :: l', 0, S m, y :: u_l' => y :: list_slice_update l' 0 m u_l'
		| x :: l', S n, S m, _ => x :: list_slice_update l' n m update_l
	end.

Definition list_extend {α: Type} (l: list α) (y: α): list α :=
	y :: l.

Class Append (α: Type) := _append : α -> α -> α.

Infix "++" := _append (right associativity, at level 60) : wasm_scope.

Global Instance Append_List_ {α: Type}: Append (list α) := { _append l1 l2 := List.app l1 l2 }.

Global Instance Append_Option {α: Type}: Append (option α) := { _append o1 o2 := option_append o1 o2 }.

Global Instance Append_nat : Append (nat) := { _append n1 n2 := n1 + n2}.

Global Instance Inh_unit : Inhabited unit := { default_val := tt }.

Global Instance Inh_nat : Inhabited nat := { default_val := O }.

Global Instance Inh_list {T: Type} : Inhabited (list T) := { default_val := nil }.

Global Instance Inh_option {T: Type} : Inhabited (option T) := { default_val := None }.

Global Instance Inh_Z : Inhabited Z := { default_val := Z0 }.

Global Instance Inh_prod {T1 T2: Type} {_: Inhabited T1} {_: Inhabited T2} : Inhabited (prod T1 T2) := { default_val := (default_val, default_val) }.

Definition option_to_list {T: Type} (arg : option T) : list T :=
	match arg with
		| None => nil
		| Some a => a :: nil
	end.

Coercion option_to_list: option >-> list.

Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.

(* Generated Code *)
Notation reserved__N := nat.

Definition list__reserved__N  := (list (reserved__N )).

Notation M := nat.

Definition list__M  := (list (M )).

Notation n := nat.

Definition list__n  := (list (n )).

Notation m := nat.

Definition list__m  := (list (m )).

Definition fun_Ki : nat := 1024.

Fixpoint fun_min (v_reserved__nat : nat) (v_reserved__nat : nat) : nat :=
	match (v_reserved__nat, v_reserved__nat) with
		| (0, v_j) => 0
		| (v_i, 0) => 0
		| ((S v_i), (S v_j)) => (fun_min v_i v_j)
	end.

Fixpoint fun_sum (v__ : (list nat)) : nat :=
	match (v__) with
		| ([]) => 0
		| ((v_n :: v_n')) => (v_n + (fun_sum v_n'))
	end.

Fixpoint fun_concat_ (X : Type) (v__ : (list (list X))) : (list X) :=
	match (X, v__) with
		| (_, []) => []
		| (_, (v_w :: v_w')) => (@app _ v_w (fun_concat_ X v_w'))
	end.

Inductive reserved__list (X : Type) : Type :=
	| reserved__list__ (v__ : (list X)) : reserved__list X.

Definition list__reserved__list (X : Type) := (list (reserved__list X)).

Global Instance Inhabited__reserved__list(X : Type) : Inhabited (reserved__list X) := { default_val := reserved__list__ X default_val }.

Inductive byte  : Type :=
	| byte__ (v_i : nat) : byte .

Definition list__byte  := (list (byte )).

Global Instance Inhabited__byte : Inhabited (byte) := { default_val := byte__ default_val }.

Notation uN := nat.

Definition list__uN  := (list (uN )).

Notation sN := nat.

Definition list__sN  := (list (sN )).

Notation iN := uN.

Definition list__iN  := (list (iN )).

Notation u31 := uN.

Definition list__u31  := (list (u31 )).

Notation u32 := uN.

Definition list__u32  := (list (u32 )).

Notation u64 := uN.

Definition list__u64  := (list (u64 )).

Definition fun_signif (v_reserved__N : reserved__N) : (option nat) :=
	match (v_reserved__N) with
		| (32) => (Some 23)
		| (64) => (Some 52)
		| (v_x0) => None
	end.

Definition fun_expon (v_reserved__N : reserved__N) : (option nat) :=
	match (v_reserved__N) with
		| (32) => (Some 8)
		| (64) => (Some 11)
		| (v_x0) => None
	end.

Definition fun_M (v_reserved__N : reserved__N) : nat :=
	match (v_reserved__N) with
		| (v_reserved__N) => (the (fun_signif v_reserved__N))
	end.

Definition fun_E (v_reserved__N : reserved__N) : nat :=
	match (v_reserved__N) with
		| (v_reserved__N) => (the (fun_expon v_reserved__N))
	end.

Notation fN := nat.

Definition list__fN  := (list (fN )).

Notation f32 := fN.

Definition list__f32  := (list (f32 )).

Notation f64 := fN.

Definition list__f64  := (list (f64 )).

Definition fun_fzero (v_reserved__N : reserved__N) : fN :=
	match (v_reserved__N) with
		| (v_reserved__N) => (0 : fN)
	end.

Definition fun_fone (v_reserved__N : reserved__N) : fN :=
	match (v_reserved__N) with
		| (v_reserved__N) => (1 : fN)
	end.

Definition fun_canon_ (v_reserved__N : reserved__N) : nat :=
	match (v_reserved__N) with
		| (v_reserved__N) => (2 ^ ((the (fun_signif v_reserved__N)) - 1))
	end.

Inductive char  : Type :=
	| char__ (v_i : nat) : char .

Definition list__char  := (list (char )).

Global Instance Inhabited__char : Inhabited (char) := { default_val := char__ default_val }.

Axiom fun_utf8 : forall (v__ : (list char)), (list__byte ).

Inductive name  : Type :=
	| name__ (v__ : (list char)) : name .

Definition list__name  := (list (name )).

Global Instance Inhabited__name : Inhabited (name) := { default_val := name__ default_val }.

Notation idx := u32.

Definition list__idx  := (list (idx )).

Notation typeidx := idx.

Definition list__typeidx  := (list (typeidx )).

Notation funcidx := idx.

Definition list__funcidx  := (list (funcidx )).

Notation globalidx := idx.

Definition list__globalidx  := (list (globalidx )).

Notation tableidx := idx.

Definition list__tableidx  := (list (tableidx )).

Notation memidx := idx.

Definition list__memidx  := (list (memidx )).

Notation labelidx := idx.

Definition list__labelidx  := (list (labelidx )).

Notation localidx := idx.

Definition list__localidx  := (list (localidx )).

Inductive fnn  : Type :=
	| fnn__F32  : fnn 
	| fnn__F64  : fnn .

Definition list__fnn  := (list (fnn )).

Global Instance Inhabited__fnn : Inhabited (fnn) := { default_val := fnn__F32  }.

Inductive inn  : Type :=
	| inn__I32  : inn 
	| inn__I64  : inn .

Definition list__inn  := (list (inn )).

Global Instance Inhabited__inn : Inhabited (inn) := { default_val := inn__I32  }.

Inductive valtype  : Type :=
	| valtype__INN (v_inn : inn) : valtype 
	| valtype__FNN (v_fnn : fnn) : valtype .

Definition list__valtype  := (list (valtype )).

Global Instance Inhabited__valtype : Inhabited (valtype) := { default_val := valtype__INN default_val }.

Definition resulttype  := (option valtype).

Definition list__resulttype  := (list (resulttype )).

Inductive mut  : Type :=
	| mut__MUT (v__ : (option unit)) : mut .

Definition list__mut  := (list (mut )).

Global Instance Inhabited__mut : Inhabited (mut) := { default_val := mut__MUT default_val }.

Inductive limits  : Type :=
	| limits__ (v_u32 : u32) (v__ : u32) : limits .

Definition list__limits  := (list (limits )).

Global Instance Inhabited__limits : Inhabited (limits) := { default_val := limits__ default_val default_val }.

Inductive globaltype  : Type :=
	| globaltype__ (v_mut : mut) (v_valtype : valtype) : globaltype .

Definition list__globaltype  := (list (globaltype )).

Global Instance Inhabited__globaltype : Inhabited (globaltype) := { default_val := globaltype__ default_val default_val }.

Inductive functype  : Type :=
	| functype__ (v__ : (list valtype)) (v__ : (list valtype)) : functype .

Definition list__functype  := (list (functype )).

Global Instance Inhabited__functype : Inhabited (functype) := { default_val := functype__ default_val default_val }.

Notation tabletype := limits.

Definition list__tabletype  := (list (tabletype )).

Notation memtype := limits.

Definition list__memtype  := (list (memtype )).

Inductive externtype  : Type :=
	| externtype__FUNC (v_functype : functype) : externtype 
	| externtype__GLOBAL (v_globaltype : globaltype) : externtype 
	| externtype__TABLE (v_tabletype : tabletype) : externtype 
	| externtype__MEM (v_memtype : memtype) : externtype .

Definition list__externtype  := (list (externtype )).

Global Instance Inhabited__externtype : Inhabited (externtype) := { default_val := externtype__FUNC default_val }.

Definition fun_size (v_valtype : valtype) : nat :=
	match (v_valtype) with
		| ((valtype__INN (inn__I32 ))) => 32
		| ((valtype__INN (inn__I64 ))) => 64
		| ((valtype__FNN (fnn__F32 ))) => 32
		| ((valtype__FNN (fnn__F64 ))) => 64
	end.

Inductive val_: Type :=
	| val___inn__entry : iN -> val_
	| val___fnn__entry : fN -> val_.

Global Instance Inhabited__val_ : Inhabited val_ := { default_val := val___inn__entry default_val }.

Definition list__val_  := (list (val_ )).

Coercion val___inn__entry : iN >-> val_.

Definition list__iN_val_ : list__iN -> list__val_ := map val___inn__entry.

Coercion list__iN_val_ : list__iN >-> list__val_.

Coercion val___fnn__entry : fN >-> val_.

Definition list__fN_val_ : list__fN -> list__val_ := map val___fnn__entry.

Coercion list__fN_val_ : list__fN >-> list__val_.

Inductive sx  : Type :=
	| sx__U  : sx 
	| sx__S  : sx .

Definition list__sx  := (list (sx )).

Global Instance Inhabited__sx : Inhabited (sx) := { default_val := sx__U  }.

Inductive unop___inn  : Type :=
	| unop___inn__CLZ  : unop___inn 
	| unop___inn__CTZ  : unop___inn 
	| unop___inn__POPCNT  : unop___inn .

Definition list__unop___inn  := (list (unop___inn )).

Global Instance Inhabited__unop___inn : Inhabited (unop___inn) := { default_val := unop___inn__CLZ  }.

Inductive unop___fnn  : Type :=
	| unop___fnn__ABS  : unop___fnn 
	| unop___fnn__NEG  : unop___fnn 
	| unop___fnn__SQRT  : unop___fnn 
	| unop___fnn__CEIL  : unop___fnn 
	| unop___fnn__FLOOR  : unop___fnn 
	| unop___fnn__TRUNC  : unop___fnn 
	| unop___fnn__NEAREST  : unop___fnn .

Definition list__unop___fnn  := (list (unop___fnn )).

Global Instance Inhabited__unop___fnn : Inhabited (unop___fnn) := { default_val := unop___fnn__ABS  }.

Inductive unop_  : Type :=
	| unop___inn__entry (arg : unop___inn) : unop_ 
	| unop___fnn__entry (arg : unop___fnn) : unop_ .

Definition list__unop_  := (list (unop_ )).

Global Instance Inhabited__unop_ : Inhabited (unop_) := { default_val := unop___inn__entry default_val }.

Inductive binop___inn  : Type :=
	| binop___inn__ADD  : binop___inn 
	| binop___inn__SUB  : binop___inn 
	| binop___inn__MUL  : binop___inn 
	| binop___inn__DIV (v_sx : sx) : binop___inn 
	| binop___inn__REM (v_sx : sx) : binop___inn 
	| binop___inn__AND  : binop___inn 
	| binop___inn__OR  : binop___inn 
	| binop___inn__XOR  : binop___inn 
	| binop___inn__SHL  : binop___inn 
	| binop___inn__SHR (v_sx : sx) : binop___inn 
	| binop___inn__ROTL  : binop___inn 
	| binop___inn__ROTR  : binop___inn .

Definition list__binop___inn  := (list (binop___inn )).

Global Instance Inhabited__binop___inn : Inhabited (binop___inn) := { default_val := binop___inn__ADD  }.

Inductive binop___fnn  : Type :=
	| binop___fnn__ADD  : binop___fnn 
	| binop___fnn__SUB  : binop___fnn 
	| binop___fnn__MUL  : binop___fnn 
	| binop___fnn__DIV  : binop___fnn 
	| binop___fnn__MIN  : binop___fnn 
	| binop___fnn__MAX  : binop___fnn 
	| binop___fnn__COPYSIGN  : binop___fnn .

Definition list__binop___fnn  := (list (binop___fnn )).

Global Instance Inhabited__binop___fnn : Inhabited (binop___fnn) := { default_val := binop___fnn__ADD  }.

Inductive binop_  : Type :=
	| binop___inn__entry (arg : binop___inn) : binop_ 
	| binop___fnn__entry (arg : binop___fnn) : binop_ .

Definition list__binop_  := (list (binop_ )).

Global Instance Inhabited__binop_ : Inhabited (binop_) := { default_val := binop___inn__entry default_val }.

Inductive testop___inn  : Type :=
	| testop___inn__EQZ  : testop___inn .

Definition list__testop___inn  := (list (testop___inn )).

Global Instance Inhabited__testop___inn : Inhabited (testop___inn) := { default_val := testop___inn__EQZ  }.

Inductive testop___fnn  : Type :=
	.

Definition list__testop___fnn  := (list (testop___fnn )).

Global Instance Inhabited__testop___fnn : Inhabited (testop___fnn)(* FIXME: no inhabitant found! *) .
	Admitted.

Inductive testop_  : Type :=
	| testop___inn__entry (arg : testop___inn) : testop_ 
	| testop___fnn__entry (arg : testop___fnn) : testop_ .

Definition list__testop_  := (list (testop_ )).

Global Instance Inhabited__testop_ : Inhabited (testop_) := { default_val := testop___inn__entry default_val }.

Inductive relop___inn  : Type :=
	| relop___inn__EQ  : relop___inn 
	| relop___inn__NE  : relop___inn 
	| relop___inn__LT (v_sx : sx) : relop___inn 
	| relop___inn__GT (v_sx : sx) : relop___inn 
	| relop___inn__LE (v_sx : sx) : relop___inn 
	| relop___inn__GE (v_sx : sx) : relop___inn .

Definition list__relop___inn  := (list (relop___inn )).

Global Instance Inhabited__relop___inn : Inhabited (relop___inn) := { default_val := relop___inn__EQ  }.

Inductive relop___fnn  : Type :=
	| relop___fnn__EQ  : relop___fnn 
	| relop___fnn__NE  : relop___fnn 
	| relop___fnn__LT  : relop___fnn 
	| relop___fnn__GT  : relop___fnn 
	| relop___fnn__LE  : relop___fnn 
	| relop___fnn__GE  : relop___fnn .

Definition list__relop___fnn  := (list (relop___fnn )).

Global Instance Inhabited__relop___fnn : Inhabited (relop___fnn) := { default_val := relop___fnn__EQ  }.

Inductive relop_  : Type :=
	| relop___inn__entry (arg : relop___inn) : relop_ 
	| relop___fnn__entry (arg : relop___fnn) : relop_ .

Definition list__relop_  := (list (relop_ )).

Global Instance Inhabited__relop_ : Inhabited (relop_) := { default_val := relop___inn__entry default_val }.

Inductive cvtop  : Type :=
	| cvtop__CONVERT  : cvtop 
	| cvtop__REINTERPRET  : cvtop .

Definition list__cvtop  := (list (cvtop )).

Global Instance Inhabited__cvtop : Inhabited (cvtop) := { default_val := cvtop__CONVERT  }.

Record memop := mkmemop
{	memop__ALIGN : u32
;	memop__OFFSET : u32
}.

Global Instance Inhabited_memop : Inhabited memop := 
{default_val := {|
	memop__ALIGN := default_val;
	memop__OFFSET := default_val|} }.

Definition list__memop  := (list (memop )).

Definition _append_memop (arg1 arg2 : memop) :=
{|
	memop__ALIGN := arg1.(memop__ALIGN) ++ arg2.(memop__ALIGN);
	memop__OFFSET := arg1.(memop__OFFSET) ++ arg2.(memop__OFFSET);
|}.

Global Instance Append_memop : Append memop := { _append arg1 arg2 := _append_memop arg1 arg2 }.

#[export] Instance eta__memop : Settable _ := settable! mkmemop <memop__ALIGN;memop__OFFSET>.

Definition blocktype  := (option valtype).

Definition list__blocktype  := (list (blocktype )).

Inductive packsize  : Type :=
	| packsize__ (v_i : nat) : packsize .

Definition list__packsize  := (list (packsize )).

Global Instance Inhabited__packsize : Inhabited (packsize) := { default_val := packsize__ default_val }.

Notation ww := packsize.

Definition list__ww  := (list (ww )).

Inductive instr  : Type :=
	| instr__NOP  : instr 
	| instr__UNREACHABLE  : instr 
	| instr__DROP  : instr 
	| instr__SELECT  : instr 
	| instr__BLOCK (v_blocktype : blocktype) (v__ : (list instr)) : instr 
	| instr__LOOP (v_blocktype : blocktype) (v__ : (list instr)) : instr 
	| instr__IFELSE (v_blocktype : blocktype) (v__ : (list instr)) (v__ : (list instr)) : instr 
	| instr__BR (v_labelidx : labelidx) : instr 
	| instr__BR_IF (v_labelidx : labelidx) : instr 
	| instr__BR_TABLE (v__ : (list labelidx)) (v__ : labelidx) : instr 
	| instr__CALL (v_funcidx : funcidx) : instr 
	| instr__CALL_INDIRECT (v_typeidx : typeidx) : instr 
	| instr__RETURN  : instr 
	| instr__CONST (v_valtype : valtype) (v_val_ : val_) : instr 
	| instr__UNOP (v_valtype : valtype) (v_unop_ : unop_) : instr 
	| instr__BINOP (v_valtype : valtype) (v_binop_ : binop_) : instr 
	| instr__TESTOP (v_valtype : valtype) (v_testop_ : testop_) : instr 
	| instr__RELOP (v_valtype : valtype) (v_relop_ : relop_) : instr 
	| instr__CVTOP (v_valtype_1 : valtype) (v_cvtop : cvtop) (v_valtype_2 : valtype) (v__ : (option sx)) : instr 
	| instr__LOCAL_GET (v_localidx : localidx) : instr 
	| instr__LOCAL_SET (v_localidx : localidx) : instr 
	| instr__LOCAL_TEE (v_localidx : localidx) : instr 
	| instr__GLOBAL_GET (v_globalidx : globalidx) : instr 
	| instr__GLOBAL_SET (v_globalidx : globalidx) : instr 
	| instr__LOAD_ (v_valtype : valtype) (v__ : (option (ww * sx))) (v_memop : memop) : instr 
	| instr__STORE (v_valtype : valtype) (v__ : (option ww)) (v_memop : memop) : instr 
	| instr__MEMORY_SIZE  : instr 
	| instr__MEMORY_GROW  : instr .

Definition list__instr  := (list (instr )).

Global Instance Inhabited__instr : Inhabited (instr) := { default_val := instr__NOP  }.

Definition expr  := (list instr).

Definition list__expr  := (list (expr )).

Inductive type  : Type :=
	| type__TYPE (v_functype : functype) : type .

Definition list__type  := (list (type )).

Global Instance Inhabited__type : Inhabited (type) := { default_val := type__TYPE default_val }.

Inductive local  : Type :=
	| local__LOCAL (v_valtype : valtype) : local .

Definition list__local  := (list (local )).

Global Instance Inhabited__local : Inhabited (local) := { default_val := local__LOCAL default_val }.

Inductive func  : Type :=
	| func__FUNC (v_typeidx : typeidx) (v__ : (list local)) (v_expr : expr) : func .

Definition list__func  := (list (func )).

Global Instance Inhabited__func : Inhabited (func) := { default_val := func__FUNC default_val default_val default_val }.

Inductive global  : Type :=
	| global__GLOBAL (v_globaltype : globaltype) (v_expr : expr) : global .

Definition list__global  := (list (global )).

Global Instance Inhabited__global : Inhabited (global) := { default_val := global__GLOBAL default_val default_val }.

Inductive table  : Type :=
	| table__TABLE (v_tabletype : tabletype) : table .

Definition list__table  := (list (table )).

Global Instance Inhabited__table : Inhabited (table) := { default_val := table__TABLE default_val }.

Inductive mem  : Type :=
	| mem__MEMORY (v_memtype : memtype) : mem .

Definition list__mem  := (list (mem )).

Global Instance Inhabited__mem : Inhabited (mem) := { default_val := mem__MEMORY default_val }.

Inductive elem  : Type :=
	| elem__ELEM (v_expr : expr) (v__ : (list funcidx)) : elem .

Definition list__elem  := (list (elem )).

Global Instance Inhabited__elem : Inhabited (elem) := { default_val := elem__ELEM default_val default_val }.

Inductive data  : Type :=
	| data__DATA (v_expr : expr) (v__ : (list byte)) : data .

Definition list__data  := (list (data )).

Global Instance Inhabited__data : Inhabited (data) := { default_val := data__DATA default_val default_val }.

Inductive start  : Type :=
	| start__START (v_funcidx : funcidx) : start .

Definition list__start  := (list (start )).

Global Instance Inhabited__start : Inhabited (start) := { default_val := start__START default_val }.

Inductive externidx  : Type :=
	| externidx__FUNC (v_funcidx : funcidx) : externidx 
	| externidx__GLOBAL (v_globalidx : globalidx) : externidx 
	| externidx__TABLE (v_tableidx : tableidx) : externidx 
	| externidx__MEM (v_memidx : memidx) : externidx .

Definition list__externidx  := (list (externidx )).

Global Instance Inhabited__externidx : Inhabited (externidx) := { default_val := externidx__FUNC default_val }.

Inductive export  : Type :=
	| export__EXPORT (v_name : name) (v_externidx : externidx) : export .

Definition list__export  := (list (export )).

Global Instance Inhabited__export : Inhabited (export) := { default_val := export__EXPORT default_val default_val }.

Inductive import  : Type :=
	| import__IMPORT (v_name : name) (v__ : name) (v_externtype : externtype) : import .

Definition list__import  := (list (import )).

Global Instance Inhabited__import : Inhabited (import) := { default_val := import__IMPORT default_val default_val default_val }.

Inductive module  : Type :=
	| module__MODULE (v__ : (list type)) (v__ : (list import)) (v__ : (list func)) (v__ : (list global)) (v__ : (list table)) (v__ : (list mem)) (v__ : (list elem)) (v__ : (list data)) (v__ : (list start)) (v__ : (list export)) : module .

Definition list__module  := (list (module )).

Global Instance Inhabited__module : Inhabited (module) := { default_val := module__MODULE default_val default_val default_val default_val default_val default_val default_val default_val default_val default_val }.

Fixpoint fun_funcsxt (v__ : (list externtype)) : (list functype) :=
	match (v__) with
		| ([]) => []
		| (((externtype__FUNC v_ft) :: v_xt)) => (@app _ [v_ft] (fun_funcsxt v_xt))
		| ((v_externtype :: v_xt)) => (fun_funcsxt v_xt)
	end.

Fixpoint fun_globalsxt (v__ : (list externtype)) : (list globaltype) :=
	match (v__) with
		| ([]) => []
		| (((externtype__GLOBAL v_gt) :: v_xt)) => (@app _ [v_gt] (fun_globalsxt v_xt))
		| ((v_externtype :: v_xt)) => (fun_globalsxt v_xt)
	end.

Fixpoint fun_tablesxt (v__ : (list externtype)) : (list tabletype) :=
	match (v__) with
		| ([]) => []
		| (((externtype__TABLE v_reserved__tt) :: v_xt)) => (@app _ [v_reserved__tt] (fun_tablesxt v_xt))
		| ((v_externtype :: v_xt)) => (fun_tablesxt v_xt)
	end.

Fixpoint fun_memsxt (v__ : (list externtype)) : (list memtype) :=
	match (v__) with
		| ([]) => []
		| (((externtype__MEM v_mt) :: v_xt)) => (@app _ [v_mt] (fun_memsxt v_xt))
		| ((v_externtype :: v_xt)) => (fun_memsxt v_xt)
	end.

Definition fun_memop0 : memop := {| memop__ALIGN := 0; memop__OFFSET := 0 |}.

Axiom fun_signed : forall (v_reserved__N : reserved__N) (v_reserved__nat : nat), nat.

Axiom fun_invsigned : forall (v_reserved__N : reserved__N) (v_int : nat), nat.

Axiom fun_fabs : forall (v_reserved__N : reserved__N) (v_fN : fN), fN.

Axiom fun_fceil : forall (v_reserved__N : reserved__N) (v_fN : fN), fN.

Axiom fun_ffloor : forall (v_reserved__N : reserved__N) (v_fN : fN), fN.

Axiom fun_fnearest : forall (v_reserved__N : reserved__N) (v_fN : fN), fN.

Axiom fun_fneg : forall (v_reserved__N : reserved__N) (v_fN : fN), fN.

Axiom fun_fsqrt : forall (v_reserved__N : reserved__N) (v_fN : fN), fN.

Axiom fun_ftrunc : forall (v_reserved__N : reserved__N) (v_fN : fN), fN.

Axiom fun_iclz : forall (v_reserved__N : reserved__N) (v_iN : iN), iN.

Axiom fun_ictz : forall (v_reserved__N : reserved__N) (v_iN : iN), iN.

Axiom fun_ipopcnt : forall (v_reserved__N : reserved__N) (v_iN : iN), iN.

Definition fun_unop (v_valtype : valtype) (v_unop_ : unop_) (v_val_ : val_) : list__val_ :=
	match (v_valtype, v_unop_, v_val_) with
		| ((valtype__INN v_inn), (unop___inn__entry (unop___inn__CLZ )), (val___inn__entry v_iN)) => [((fun_iclz (fun_size (valtype__INN v_inn)) v_iN) : val_)]
		| ((valtype__INN v_inn), (unop___inn__entry (unop___inn__CTZ )), (val___inn__entry v_iN)) => [((fun_ictz (fun_size (valtype__INN v_inn)) v_iN) : val_)]
		| ((valtype__INN v_inn), (unop___inn__entry (unop___inn__POPCNT )), (val___inn__entry v_iN)) => [((fun_ipopcnt (fun_size (valtype__INN v_inn)) v_iN) : val_)]
		| ((valtype__FNN v_fnn), (unop___fnn__entry (unop___fnn__ABS )), (val___fnn__entry v_fN)) => [((fun_fabs (fun_size (valtype__FNN v_fnn)) v_fN) : val_)]
		| ((valtype__FNN v_fnn), (unop___fnn__entry (unop___fnn__NEG )), (val___fnn__entry v_fN)) => [((fun_fneg (fun_size (valtype__FNN v_fnn)) v_fN) : val_)]
		| ((valtype__FNN v_fnn), (unop___fnn__entry (unop___fnn__SQRT )), (val___fnn__entry v_fN)) => [((fun_fsqrt (fun_size (valtype__FNN v_fnn)) v_fN) : val_)]
		| ((valtype__FNN v_fnn), (unop___fnn__entry (unop___fnn__CEIL )), (val___fnn__entry v_fN)) => [((fun_fceil (fun_size (valtype__FNN v_fnn)) v_fN) : val_)]
		| ((valtype__FNN v_fnn), (unop___fnn__entry (unop___fnn__FLOOR )), (val___fnn__entry v_fN)) => [((fun_ffloor (fun_size (valtype__FNN v_fnn)) v_fN) : val_)]
		| ((valtype__FNN v_fnn), (unop___fnn__entry (unop___fnn__TRUNC )), (val___fnn__entry v_fN)) => [((fun_ftrunc (fun_size (valtype__FNN v_fnn)) v_fN) : val_)]
		| ((valtype__FNN v_fnn), (unop___fnn__entry (unop___fnn__NEAREST )), (val___fnn__entry v_fN)) => [((fun_fnearest (fun_size (valtype__FNN v_fnn)) v_fN) : val_)]
		| _ => default_val
	end.

Axiom fun_fadd : forall (v_reserved__N : reserved__N) (v_fN : fN) (v_fN : fN), fN.

Axiom fun_fcopysign : forall (v_reserved__N : reserved__N) (v_fN : fN) (v_fN : fN), fN.

Axiom fun_fdiv : forall (v_reserved__N : reserved__N) (v_fN : fN) (v_fN : fN), fN.

Axiom fun_fmax : forall (v_reserved__N : reserved__N) (v_fN : fN) (v_fN : fN), fN.

Axiom fun_fmin : forall (v_reserved__N : reserved__N) (v_fN : fN) (v_fN : fN), fN.

Axiom fun_fmul : forall (v_reserved__N : reserved__N) (v_fN : fN) (v_fN : fN), fN.

Axiom fun_fsub : forall (v_reserved__N : reserved__N) (v_fN : fN) (v_fN : fN), fN.

Axiom fun_iadd : forall (v_reserved__N : reserved__N) (v_iN : iN) (v_iN : iN), iN.

Axiom fun_iand : forall (v_reserved__N : reserved__N) (v_iN : iN) (v_iN : iN), iN.

Axiom fun_idiv : forall (v_reserved__N : reserved__N) (v_sx : sx) (v_iN : iN) (v_iN : iN), iN.

Axiom fun_imul : forall (v_reserved__N : reserved__N) (v_iN : iN) (v_iN : iN), iN.

Axiom fun_ior : forall (v_reserved__N : reserved__N) (v_iN : iN) (v_iN : iN), iN.

Axiom fun_irem : forall (v_reserved__N : reserved__N) (v_sx : sx) (v_iN : iN) (v_iN : iN), iN.

Axiom fun_irotl : forall (v_reserved__N : reserved__N) (v_iN : iN) (v_iN : iN), iN.

Axiom fun_irotr : forall (v_reserved__N : reserved__N) (v_iN : iN) (v_iN : iN), iN.

Axiom fun_ishl : forall (v_reserved__N : reserved__N) (v_iN : iN) (v_u32 : u32), iN.

Axiom fun_ishr : forall (v_reserved__N : reserved__N) (v_sx : sx) (v_iN : iN) (v_u32 : u32), iN.

Axiom fun_isub : forall (v_reserved__N : reserved__N) (v_iN : iN) (v_iN : iN), iN.

Axiom fun_ixor : forall (v_reserved__N : reserved__N) (v_iN : iN) (v_iN : iN), iN.

Definition fun_binop (v_valtype : valtype) (v_binop_ : binop_) (v_val_ : val_) (v_val_ : val_) : list__val_ :=
	match (v_valtype, v_binop_, v_val_, v_val_) with
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__ADD )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => [((fun_iadd (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_)]
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__SUB )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => [((fun_isub (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_)]
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__MUL )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => [((fun_imul (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_)]
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__DIV v_sx)), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => [((fun_idiv (fun_size (valtype__INN v_inn)) v_sx v_iN_1 v_iN_2) : val_)]
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__REM v_sx)), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => [((fun_irem (fun_size (valtype__INN v_inn)) v_sx v_iN_1 v_iN_2) : val_)]
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__AND )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => [((fun_iand (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_)]
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__OR )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => [((fun_ior (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_)]
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__XOR )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => [((fun_ixor (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_)]
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__SHL )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => [((fun_ishl (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_)]
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__SHR v_sx)), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => [((fun_ishr (fun_size (valtype__INN v_inn)) v_sx v_iN_1 v_iN_2) : val_)]
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__ROTL )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => [((fun_irotl (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_)]
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__ROTR )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => [((fun_irotr (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_)]
		| ((valtype__FNN v_fnn), (binop___fnn__entry (binop___fnn__ADD )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => [((fun_fadd (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2) : val_)]
		| ((valtype__FNN v_fnn), (binop___fnn__entry (binop___fnn__SUB )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => [((fun_fsub (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2) : val_)]
		| ((valtype__FNN v_fnn), (binop___fnn__entry (binop___fnn__MUL )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => [((fun_fmul (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2) : val_)]
		| ((valtype__FNN v_fnn), (binop___fnn__entry (binop___fnn__DIV )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => [((fun_fdiv (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2) : val_)]
		| ((valtype__FNN v_fnn), (binop___fnn__entry (binop___fnn__MIN )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => [((fun_fmin (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2) : val_)]
		| ((valtype__FNN v_fnn), (binop___fnn__entry (binop___fnn__MAX )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => [((fun_fmax (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2) : val_)]
		| ((valtype__FNN v_fnn), (binop___fnn__entry (binop___fnn__COPYSIGN )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => [((fun_fcopysign (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2) : val_)]
		| _ => default_val
	end.

Axiom fun_ieqz : forall (v_reserved__N : reserved__N) (v_iN : iN), u32.

Definition fun_testop (v_valtype : valtype) (v_testop_ : testop_) (v_val_ : val_) : val_ :=
	match (v_valtype, v_testop_, v_val_) with
		| ((valtype__INN v_inn), (testop___inn__entry (testop___inn__EQZ )), (val___inn__entry v_iN)) => (fun_ieqz (fun_size (valtype__INN v_inn)) v_iN)
		| _ => default_val
	end.

Axiom fun_feq : forall (v_reserved__N : reserved__N) (v_fN : fN) (v_fN : fN), u32.

Axiom fun_fge : forall (v_reserved__N : reserved__N) (v_fN : fN) (v_fN : fN), u32.

Axiom fun_fgt : forall (v_reserved__N : reserved__N) (v_fN : fN) (v_fN : fN), u32.

Axiom fun_fle : forall (v_reserved__N : reserved__N) (v_fN : fN) (v_fN : fN), u32.

Axiom fun_flt : forall (v_reserved__N : reserved__N) (v_fN : fN) (v_fN : fN), u32.

Axiom fun_fne : forall (v_reserved__N : reserved__N) (v_fN : fN) (v_fN : fN), u32.

Axiom fun_ieq : forall (v_reserved__N : reserved__N) (v_iN : iN) (v_iN : iN), u32.

Axiom fun_ige : forall (v_reserved__N : reserved__N) (v_sx : sx) (v_iN : iN) (v_iN : iN), u32.

Axiom fun_igt : forall (v_reserved__N : reserved__N) (v_sx : sx) (v_iN : iN) (v_iN : iN), u32.

Axiom fun_ile : forall (v_reserved__N : reserved__N) (v_sx : sx) (v_iN : iN) (v_iN : iN), u32.

Axiom fun_ilt : forall (v_reserved__N : reserved__N) (v_sx : sx) (v_iN : iN) (v_iN : iN), u32.

Axiom fun_ine : forall (v_reserved__N : reserved__N) (v_iN : iN) (v_iN : iN), u32.

Definition fun_relop (v_valtype : valtype) (v_relop_ : relop_) (v_val_ : val_) (v_val_ : val_) : val_ :=
	match (v_valtype, v_relop_, v_val_, v_val_) with
		| ((valtype__INN v_inn), (relop___inn__entry (relop___inn__EQ )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (fun_ieq (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2)
		| ((valtype__INN v_inn), (relop___inn__entry (relop___inn__NE )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (fun_ine (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2)
		| ((valtype__INN v_inn), (relop___inn__entry (relop___inn__LT v_sx)), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (fun_ilt (fun_size (valtype__INN v_inn)) v_sx v_iN_1 v_iN_2)
		| ((valtype__INN v_inn), (relop___inn__entry (relop___inn__GT v_sx)), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (fun_igt (fun_size (valtype__INN v_inn)) v_sx v_iN_1 v_iN_2)
		| ((valtype__INN v_inn), (relop___inn__entry (relop___inn__LE v_sx)), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (fun_ile (fun_size (valtype__INN v_inn)) v_sx v_iN_1 v_iN_2)
		| ((valtype__INN v_inn), (relop___inn__entry (relop___inn__GE v_sx)), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (fun_ige (fun_size (valtype__INN v_inn)) v_sx v_iN_1 v_iN_2)
		| ((valtype__FNN v_fnn), (relop___fnn__entry (relop___fnn__EQ )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => (fun_feq (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2)
		| ((valtype__FNN v_fnn), (relop___fnn__entry (relop___fnn__NE )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => (fun_fne (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2)
		| ((valtype__FNN v_fnn), (relop___fnn__entry (relop___fnn__LT )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => (fun_flt (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2)
		| ((valtype__FNN v_fnn), (relop___fnn__entry (relop___fnn__GT )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => (fun_fgt (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2)
		| ((valtype__FNN v_fnn), (relop___fnn__entry (relop___fnn__LE )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => (fun_fle (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2)
		| ((valtype__FNN v_fnn), (relop___fnn__entry (relop___fnn__GE )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => (fun_fge (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2)
		| _ => default_val
	end.

Axiom fun_convert : forall (v_M : M) (v_reserved__N : reserved__N) (v_sx : sx) (v_iN : iN), fN.

Axiom fun_demote : forall (v_M : M) (v_reserved__N : reserved__N) (v_fN : fN), fN.

Axiom fun_ext : forall (v_M : M) (v_reserved__N : reserved__N) (v_sx : sx) (v_iN : iN), iN.

Axiom fun_promote : forall (v_M : M) (v_reserved__N : reserved__N) (v_fN : fN), fN.

Axiom fun_reinterpret : forall (v_valtype_1 : valtype) (v_valtype_2 : valtype) (v_val_ : val_), val_.

Axiom fun_trunc : forall (v_M : M) (v_reserved__N : reserved__N) (v_sx : sx) (v_fN : fN), iN.

Axiom fun_wrap : forall (v_M : M) (v_reserved__N : reserved__N) (v_iN : iN), iN.

Definition fun_cvtop (v_valtype_1 : valtype) (v_valtype_2 : valtype) (v_cvtop : cvtop) (v__ : (option sx)) (v_val_ : val_) : list__val_ :=
	match (v_valtype_1, v_valtype_2, v_cvtop, v__, v_val_) with
		| ((valtype__INN (inn__I32 )), (valtype__INN (inn__I64 )), (cvtop__CONVERT ), (Some v_sx), (val___inn__entry v_iN)) => [((fun_ext 32 64 v_sx v_iN) : val_)]
		| ((valtype__INN (inn__I64 )), (valtype__INN (inn__I32 )), (cvtop__CONVERT ), v_sx, (val___inn__entry v_iN)) => [((fun_wrap 64 32 v_iN) : val_)]
		| ((valtype__FNN v_fnn), (valtype__INN v_inn), (cvtop__CONVERT ), (Some v_sx), (val___fnn__entry v_fN)) => [((fun_trunc (fun_size (valtype__FNN v_fnn)) (fun_size (valtype__INN v_inn)) v_sx v_fN) : val_)]
		| ((valtype__FNN (fnn__F32 )), (valtype__FNN (fnn__F64 )), (cvtop__CONVERT ), v_sx, (val___fnn__entry v_fN)) => [((fun_promote 32 64 v_fN) : val_)]
		| ((valtype__FNN (fnn__F64 )), (valtype__FNN (fnn__F32 )), (cvtop__CONVERT ), v_sx, (val___fnn__entry v_fN)) => [((fun_demote 64 32 v_fN) : val_)]
		| ((valtype__INN v_inn), (valtype__FNN v_fnn), (cvtop__CONVERT ), (Some v_sx), (val___inn__entry v_iN)) => [((fun_convert (fun_size (valtype__INN v_inn)) (fun_size (valtype__FNN v_fnn)) v_sx v_iN) : val_)]
		| ((valtype__INN v_inn), (valtype__FNN v_fnn), (cvtop__REINTERPRET ), v_sx, (val___inn__entry v_iN)) => [((fun_reinterpret (valtype__INN v_inn) (valtype__FNN v_fnn) (v_iN : val_)) : val_)]
		| ((valtype__FNN v_fnn), (valtype__INN v_inn), (cvtop__REINTERPRET ), v_sx, (val___fnn__entry v_fN)) => [((fun_reinterpret (valtype__FNN v_fnn) (valtype__INN v_inn) (v_fN : val_)) : val_)]
		| _ => default_val
	end.

Axiom fun_ibytes : forall (v_reserved__N : reserved__N) (v_iN : iN), (list__byte ).

Axiom fun_fbytes : forall (v_reserved__N : reserved__N) (v_fN : fN), (list__byte ).

Axiom fun_bytes : forall (v_valtype : valtype) (v_val_ : val_), (list__byte ).

Axiom fun_invibytes : forall (v_reserved__N : reserved__N) (v__ : (list byte)), iN.

Axiom fun_invfbytes : forall (v_reserved__N : reserved__N) (v__ : (list byte)), fN.

Axiom fun_inot : forall (v_reserved__N : reserved__N) (v_iN : iN), iN.

Notation addr := nat.

Definition list__addr  := (list (addr )).

Notation funcaddr := addr.

Definition list__funcaddr  := (list (funcaddr )).

Notation globaladdr := addr.

Definition list__globaladdr  := (list (globaladdr )).

Notation tableaddr := addr.

Definition list__tableaddr  := (list (tableaddr )).

Notation memaddr := addr.

Definition list__memaddr  := (list (memaddr )).

Inductive val  : Type :=
	| val__CONST (v_valtype : valtype) (v_val_ : val_) : val .

Definition list__val  := (list (val )).

Global Instance Inhabited__val : Inhabited (val) := { default_val := val__CONST default_val default_val }.

Inductive result  : Type :=
	| result___VALS (v__ : (list val)) : result 
	| result__TRAP  : result .

Definition list__result  := (list (result )).

Global Instance Inhabited__result : Inhabited (result) := { default_val := result___VALS default_val }.

Inductive externval  : Type :=
	| externval__FUNC (v_funcaddr : funcaddr) : externval 
	| externval__GLOBAL (v_globaladdr : globaladdr) : externval 
	| externval__TABLE (v_tableaddr : tableaddr) : externval 
	| externval__MEM (v_memaddr : memaddr) : externval .

Definition list__externval  := (list (externval )).

Global Instance Inhabited__externval : Inhabited (externval) := { default_val := externval__FUNC default_val }.

Record exportinst := mkexportinst
{	exportinst__NAME : name
;	exportinst__VALUE : externval
}.

Global Instance Inhabited_exportinst : Inhabited exportinst := 
{default_val := {|
	exportinst__NAME := default_val;
	exportinst__VALUE := default_val|} }.

Definition list__exportinst  := (list (exportinst )).

Definition _append_exportinst (arg1 arg2 : exportinst) :=
{|
	exportinst__NAME := arg1.(exportinst__NAME); (* FIXME: This type does not have a trivial way to append *)
	exportinst__VALUE := arg1.(exportinst__VALUE); (* FIXME: This type does not have a trivial way to append *)
|}.

Global Instance Append_exportinst : Append exportinst := { _append arg1 arg2 := _append_exportinst arg1 arg2 }.

#[export] Instance eta__exportinst : Settable _ := settable! mkexportinst <exportinst__NAME;exportinst__VALUE>.

Record moduleinst := mkmoduleinst
{	moduleinst__TYPES : (list functype)
;	moduleinst__FUNCS : (list funcaddr)
;	moduleinst__GLOBALS : (list globaladdr)
;	moduleinst__TABLES : (list tableaddr)
;	moduleinst__MEMS : (list memaddr)
;	moduleinst__EXPORTS : (list exportinst)
}.

Global Instance Inhabited_moduleinst : Inhabited moduleinst := 
{default_val := {|
	moduleinst__TYPES := default_val;
	moduleinst__FUNCS := default_val;
	moduleinst__GLOBALS := default_val;
	moduleinst__TABLES := default_val;
	moduleinst__MEMS := default_val;
	moduleinst__EXPORTS := default_val|} }.

Definition list__moduleinst  := (list (moduleinst )).

Definition _append_moduleinst (arg1 arg2 : moduleinst) :=
{|
	moduleinst__TYPES := arg1.(moduleinst__TYPES) ++ arg2.(moduleinst__TYPES);
	moduleinst__FUNCS := arg1.(moduleinst__FUNCS) ++ arg2.(moduleinst__FUNCS);
	moduleinst__GLOBALS := arg1.(moduleinst__GLOBALS) ++ arg2.(moduleinst__GLOBALS);
	moduleinst__TABLES := arg1.(moduleinst__TABLES) ++ arg2.(moduleinst__TABLES);
	moduleinst__MEMS := arg1.(moduleinst__MEMS) ++ arg2.(moduleinst__MEMS);
	moduleinst__EXPORTS := arg1.(moduleinst__EXPORTS) ++ arg2.(moduleinst__EXPORTS);
|}.

Global Instance Append_moduleinst : Append moduleinst := { _append arg1 arg2 := _append_moduleinst arg1 arg2 }.

#[export] Instance eta__moduleinst : Settable _ := settable! mkmoduleinst <moduleinst__TYPES;moduleinst__FUNCS;moduleinst__GLOBALS;moduleinst__TABLES;moduleinst__MEMS;moduleinst__EXPORTS>.

Record funcinst := mkfuncinst
{	funcinst__TYPE : functype
;	funcinst__MODULE : moduleinst
;	funcinst__CODE : func
}.

Global Instance Inhabited_funcinst : Inhabited funcinst := 
{default_val := {|
	funcinst__TYPE := default_val;
	funcinst__MODULE := default_val;
	funcinst__CODE := default_val|} }.

Definition list__funcinst  := (list (funcinst )).

Definition _append_funcinst (arg1 arg2 : funcinst) :=
{|
	funcinst__TYPE := arg1.(funcinst__TYPE); (* FIXME: This type does not have a trivial way to append *)
	funcinst__MODULE := arg1.(funcinst__MODULE) ++ arg2.(funcinst__MODULE);
	funcinst__CODE := arg1.(funcinst__CODE); (* FIXME: This type does not have a trivial way to append *)
|}.

Global Instance Append_funcinst : Append funcinst := { _append arg1 arg2 := _append_funcinst arg1 arg2 }.

#[export] Instance eta__funcinst : Settable _ := settable! mkfuncinst <funcinst__TYPE;funcinst__MODULE;funcinst__CODE>.

Record globalinst := mkglobalinst
{	globalinst__TYPE : globaltype
;	globalinst__VALUE : val
}.

Global Instance Inhabited_globalinst : Inhabited globalinst := 
{default_val := {|
	globalinst__TYPE := default_val;
	globalinst__VALUE := default_val|} }.

Definition list__globalinst  := (list (globalinst )).

Definition _append_globalinst (arg1 arg2 : globalinst) :=
{|
	globalinst__TYPE := arg1.(globalinst__TYPE); (* FIXME: This type does not have a trivial way to append *)
	globalinst__VALUE := arg1.(globalinst__VALUE); (* FIXME: This type does not have a trivial way to append *)
|}.

Global Instance Append_globalinst : Append globalinst := { _append arg1 arg2 := _append_globalinst arg1 arg2 }.

#[export] Instance eta__globalinst : Settable _ := settable! mkglobalinst <globalinst__TYPE;globalinst__VALUE>.

Record tableinst := mktableinst
{	tableinst__TYPE : tabletype
;	tableinst__REFS : (list (option funcaddr))
}.

Global Instance Inhabited_tableinst : Inhabited tableinst := 
{default_val := {|
	tableinst__TYPE := default_val;
	tableinst__REFS := default_val|} }.

Definition list__tableinst  := (list (tableinst )).

Definition _append_tableinst (arg1 arg2 : tableinst) :=
{|
	tableinst__TYPE := arg1.(tableinst__TYPE); (* FIXME: This type does not have a trivial way to append *)
	tableinst__REFS := arg1.(tableinst__REFS) ++ arg2.(tableinst__REFS);
|}.

Global Instance Append_tableinst : Append tableinst := { _append arg1 arg2 := _append_tableinst arg1 arg2 }.

#[export] Instance eta__tableinst : Settable _ := settable! mktableinst <tableinst__TYPE;tableinst__REFS>.

Record meminst := mkmeminst
{	meminst__TYPE : memtype
;	meminst__BYTES : (list byte)
}.

Global Instance Inhabited_meminst : Inhabited meminst := 
{default_val := {|
	meminst__TYPE := default_val;
	meminst__BYTES := default_val|} }.

Definition list__meminst  := (list (meminst )).

Definition _append_meminst (arg1 arg2 : meminst) :=
{|
	meminst__TYPE := arg1.(meminst__TYPE); (* FIXME: This type does not have a trivial way to append *)
	meminst__BYTES := arg1.(meminst__BYTES) ++ arg2.(meminst__BYTES);
|}.

Global Instance Append_meminst : Append meminst := { _append arg1 arg2 := _append_meminst arg1 arg2 }.

#[export] Instance eta__meminst : Settable _ := settable! mkmeminst <meminst__TYPE;meminst__BYTES>.

Record store := mkstore
{	store__FUNCS : (list funcinst)
;	store__GLOBALS : (list globalinst)
;	store__TABLES : (list tableinst)
;	store__MEMS : (list meminst)
}.

Global Instance Inhabited_store : Inhabited store := 
{default_val := {|
	store__FUNCS := default_val;
	store__GLOBALS := default_val;
	store__TABLES := default_val;
	store__MEMS := default_val|} }.

Definition list__store  := (list (store )).

Definition _append_store (arg1 arg2 : store) :=
{|
	store__FUNCS := arg1.(store__FUNCS) ++ arg2.(store__FUNCS);
	store__GLOBALS := arg1.(store__GLOBALS) ++ arg2.(store__GLOBALS);
	store__TABLES := arg1.(store__TABLES) ++ arg2.(store__TABLES);
	store__MEMS := arg1.(store__MEMS) ++ arg2.(store__MEMS);
|}.

Global Instance Append_store : Append store := { _append arg1 arg2 := _append_store arg1 arg2 }.

#[export] Instance eta__store : Settable _ := settable! mkstore <store__FUNCS;store__GLOBALS;store__TABLES;store__MEMS>.

Record frame := mkframe
{	frame__LOCALS : (list val)
;	frame__MODULE : moduleinst
}.

Global Instance Inhabited_frame : Inhabited frame := 
{default_val := {|
	frame__LOCALS := default_val;
	frame__MODULE := default_val|} }.

Definition list__frame  := (list (frame )).

Definition _append_frame (arg1 arg2 : frame) :=
{|
	frame__LOCALS := arg1.(frame__LOCALS) ++ arg2.(frame__LOCALS);
	frame__MODULE := arg1.(frame__MODULE) ++ arg2.(frame__MODULE);
|}.

Global Instance Append_frame : Append frame := { _append arg1 arg2 := _append_frame arg1 arg2 }.

#[export] Instance eta__frame : Settable _ := settable! mkframe <frame__LOCALS;frame__MODULE>.

Inductive state  : Type :=
	| state__ (v_store : store) (v_frame : frame) : state .

Definition list__state  := (list (state )).

Global Instance Inhabited__state : Inhabited (state) := { default_val := state__ default_val default_val }.

Inductive admininstr  : Type :=
	| admininstr__NOP  : admininstr 
	| admininstr__UNREACHABLE  : admininstr 
	| admininstr__DROP  : admininstr 
	| admininstr__SELECT  : admininstr 
	| admininstr__BLOCK (v_blocktype : blocktype) (v__ : (list instr)) : admininstr 
	| admininstr__LOOP (v_blocktype : blocktype) (v__ : (list instr)) : admininstr 
	| admininstr__IFELSE (v_blocktype : blocktype) (v__ : (list instr)) (v__ : (list instr)) : admininstr 
	| admininstr__BR (v_labelidx : labelidx) : admininstr 
	| admininstr__BR_IF (v_labelidx : labelidx) : admininstr 
	| admininstr__BR_TABLE (v__ : (list labelidx)) (v__ : labelidx) : admininstr 
	| admininstr__CALL (v_funcidx : funcidx) : admininstr 
	| admininstr__CALL_INDIRECT (v_typeidx : typeidx) : admininstr 
	| admininstr__RETURN  : admininstr 
	| admininstr__CONST (v_valtype : valtype) (v_val_ : val_) : admininstr 
	| admininstr__UNOP (v_valtype : valtype) (v_unop_ : unop_) : admininstr 
	| admininstr__BINOP (v_valtype : valtype) (v_binop_ : binop_) : admininstr 
	| admininstr__TESTOP (v_valtype : valtype) (v_testop_ : testop_) : admininstr 
	| admininstr__RELOP (v_valtype : valtype) (v_relop_ : relop_) : admininstr 
	| admininstr__CVTOP (v_valtype_1 : valtype) (v_cvtop : cvtop) (v_valtype_2 : valtype) (v__ : (option sx)) : admininstr 
	| admininstr__LOCAL_GET (v_localidx : localidx) : admininstr 
	| admininstr__LOCAL_SET (v_localidx : localidx) : admininstr 
	| admininstr__LOCAL_TEE (v_localidx : localidx) : admininstr 
	| admininstr__GLOBAL_GET (v_globalidx : globalidx) : admininstr 
	| admininstr__GLOBAL_SET (v_globalidx : globalidx) : admininstr 
	| admininstr__LOAD_ (v_valtype : valtype) (v__ : (option (ww * sx))) (v_memop : memop) : admininstr 
	| admininstr__STORE (v_valtype : valtype) (v__ : (option ww)) (v_memop : memop) : admininstr 
	| admininstr__MEMORY_SIZE  : admininstr 
	| admininstr__MEMORY_GROW  : admininstr 
	| admininstr__CALL_ADDR (v_funcaddr : funcaddr) : admininstr 
	| admininstr__LABEL_ (v_n : n) (v__ : (list instr)) (v__ : (list admininstr)) : admininstr 
	| admininstr__FRAME_ (v_n : n) (v_frame : frame) (v__ : (list admininstr)) : admininstr 
	| admininstr__TRAP  : admininstr .

Definition list__admininstr  := (list (admininstr )).

Global Instance Inhabited__admininstr : Inhabited (admininstr) := { default_val := admininstr__NOP  }.

Inductive config  : Type :=
	| config__ (v_state : state) (v__ : (list admininstr)) : config .

Definition list__config  := (list (config )).

Global Instance Inhabited__config : Inhabited (config) := { default_val := config__ default_val default_val }.

Inductive E  : Type :=
	| E___HOLE_  : E 
	| E___SEQ (v__ : (list val)) (v_E : E) (v__ : (list instr)) : E 
	| E__LABEL_ (v_n : n) (v__ : (list instr)) (v_E : E) : E .

Definition list__E  := (list (E )).

Global Instance Inhabited__E : Inhabited (E) := { default_val := E___HOLE_  }.

Definition fun_default_ (v_valtype : valtype) : val :=
	match (v_valtype) with
		| ((valtype__INN (inn__I32 ))) => (val__CONST (valtype__INN (inn__I32 )) 0)
		| ((valtype__INN (inn__I64 ))) => (val__CONST (valtype__INN (inn__I64 )) 0)
		| ((valtype__FNN (fnn__F32 ))) => (val__CONST (valtype__FNN (fnn__F32 )) (fun_fzero 32))
		| ((valtype__FNN (fnn__F64 ))) => (val__CONST (valtype__FNN (fnn__F64 )) (fun_fzero 64))
	end.

Fixpoint fun_funcsxv (v__ : (list externval)) : (list funcaddr) :=
	match (v__) with
		| ([]) => []
		| (((externval__FUNC v_fa) :: v_xv)) => (@app _ [v_fa] (fun_funcsxv v_xv))
		| ((v_externval :: v_xv)) => (fun_funcsxv v_xv)
	end.

Fixpoint fun_globalsxv (v__ : (list externval)) : (list globaladdr) :=
	match (v__) with
		| ([]) => []
		| (((externval__GLOBAL v_ga) :: v_xv)) => (@app _ [v_ga] (fun_globalsxv v_xv))
		| ((v_externval :: v_xv)) => (fun_globalsxv v_xv)
	end.

Fixpoint fun_tablesxv (v__ : (list externval)) : (list tableaddr) :=
	match (v__) with
		| ([]) => []
		| (((externval__TABLE v_ta) :: v_xv)) => (@app _ [v_ta] (fun_tablesxv v_xv))
		| ((v_externval :: v_xv)) => (fun_tablesxv v_xv)
	end.

Fixpoint fun_memsxv (v__ : (list externval)) : (list memaddr) :=
	match (v__) with
		| ([]) => []
		| (((externval__MEM v_ma) :: v_xv)) => (@app _ [v_ma] (fun_memsxv v_xv))
		| ((v_externval :: v_xv)) => (fun_memsxv v_xv)
	end.

Definition fun_store (v_state : state) : store :=
	match (v_state) with
		| ((state__ v_s v_f)) => v_s
	end.

Definition fun_frame (v_state : state) : frame :=
	match (v_state) with
		| ((state__ v_s v_f)) => v_f
	end.

Definition fun_funcaddr (v_state : state) : (list funcaddr) :=
	match (v_state) with
		| ((state__ v_s v_f)) => (moduleinst__FUNCS (frame__MODULE v_f))
	end.

Definition fun_funcinst (v_state : state) : (list funcinst) :=
	match (v_state) with
		| ((state__ v_s v_f)) => (store__FUNCS v_s)
	end.

Definition fun_globalinst (v_state : state) : (list globalinst) :=
	match (v_state) with
		| ((state__ v_s v_f)) => (store__GLOBALS v_s)
	end.

Definition fun_tableinst (v_state : state) : (list tableinst) :=
	match (v_state) with
		| ((state__ v_s v_f)) => (store__TABLES v_s)
	end.

Definition fun_meminst (v_state : state) : (list meminst) :=
	match (v_state) with
		| ((state__ v_s v_f)) => (store__MEMS v_s)
	end.

Definition fun_moduleinst (v_state : state) : moduleinst :=
	match (v_state) with
		| ((state__ v_s v_f)) => (frame__MODULE v_f)
	end.

Definition fun_type (v_state : state) (v_typeidx : typeidx) : functype :=
	match (v_state, v_typeidx) with
		| ((state__ v_s v_f), v_x) => (lookup_total (moduleinst__TYPES (frame__MODULE v_f)) v_x)
	end.

Definition fun_func (v_state : state) (v_funcidx : funcidx) : funcinst :=
	match (v_state, v_funcidx) with
		| ((state__ v_s v_f), v_x) => (lookup_total (store__FUNCS v_s) (lookup_total (moduleinst__FUNCS (frame__MODULE v_f)) v_x))
	end.

Definition fun_global (v_state : state) (v_globalidx : globalidx) : globalinst :=
	match (v_state, v_globalidx) with
		| ((state__ v_s v_f), v_x) => (lookup_total (store__GLOBALS v_s) (lookup_total (moduleinst__GLOBALS (frame__MODULE v_f)) v_x))
	end.

Definition fun_table (v_state : state) (v_tableidx : tableidx) : tableinst :=
	match (v_state, v_tableidx) with
		| ((state__ v_s v_f), v_x) => (lookup_total (store__TABLES v_s) (lookup_total (moduleinst__TABLES (frame__MODULE v_f)) v_x))
	end.

Definition fun_mem (v_state : state) (v_memidx : memidx) : meminst :=
	match (v_state, v_memidx) with
		| ((state__ v_s v_f), v_x) => (lookup_total (store__MEMS v_s) (lookup_total (moduleinst__MEMS (frame__MODULE v_f)) v_x))
	end.

Definition fun_local (v_state : state) (v_localidx : localidx) : val :=
	match (v_state, v_localidx) with
		| ((state__ v_s v_f), v_x) => (lookup_total (frame__LOCALS v_f) v_x)
	end.

Definition fun_with_local (v_state : state) (v_localidx : localidx) (v_val : val) : state :=
	match (v_state, v_localidx, v_val) with
		| ((state__ v_s v_f), v_x, v_v) => (state__ v_s (v_f <|frame__LOCALS := (list_update (frame__LOCALS v_f) (v_x) (v_v))|>))
	end.

Definition fun_with_global (v_state : state) (v_globalidx : globalidx) (v_val : val) : state :=
	match (v_state, v_globalidx, v_val) with
		| ((state__ v_s v_f), v_x, v_v) => (state__ (v_s <|store__GLOBALS := (list_update_func (store__GLOBALS v_s) ((lookup_total (moduleinst__GLOBALS (frame__MODULE v_f)) v_x)) ((fun v_1 => v_1 <|globalinst__VALUE := v_v|>)))|>) v_f)
	end.

Definition fun_with_table (v_state : state) (v_tableidx : tableidx) (v_reserved__nat : nat) (v_funcaddr : funcaddr) : state :=
	match (v_state, v_tableidx, v_reserved__nat, v_funcaddr) with
		| ((state__ v_s v_f), v_x, v_i, v_a) => (state__ (v_s <|store__TABLES := (list_update_func (store__TABLES v_s) ((lookup_total (moduleinst__TABLES (frame__MODULE v_f)) v_x)) ((fun v_1 => v_1 <|tableinst__REFS := (list_update (tableinst__REFS v_1) (v_i) ((Some v_a)))|>)))|>) v_f)
	end.

Definition fun_with_tableinst (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) : state :=
	match (v_state, v_tableidx, v_tableinst) with
		| ((state__ v_s v_f), v_x, v_ti) => (state__ (v_s <|store__TABLES := (list_update (store__TABLES v_s) ((lookup_total (moduleinst__TABLES (frame__MODULE v_f)) v_x)) (v_ti))|>) v_f)
	end.

Definition fun_with_mem (v_state : state) (v_memidx : memidx) (v_reserved__nat : nat) (v_reserved__nat : nat) (v__ : (list byte)) : state :=
	match (v_state, v_memidx, v_reserved__nat, v_reserved__nat, v__) with
		| ((state__ v_s v_f), v_x, v_i, v_j, v_b) => (state__ (v_s <|store__MEMS := (list_update_func (store__MEMS v_s) ((lookup_total (moduleinst__MEMS (frame__MODULE v_f)) v_x)) ((fun v_1 => v_1 <|meminst__BYTES := (list_slice_update (meminst__BYTES v_1) (v_i) (v_j) (v_b))|>)))|>) v_f)
	end.

Definition fun_with_meminst (v_state : state) (v_memidx : memidx) (v_meminst : meminst) : state :=
	match (v_state, v_memidx, v_meminst) with
		| ((state__ v_s v_f), v_x, v_mi) => (state__ (v_s <|store__MEMS := (list_update (store__MEMS v_s) ((lookup_total (moduleinst__MEMS (frame__MODULE v_f)) v_x)) (v_mi))|>) v_f)
	end.

Axiom fun_growtable : forall (v_tableinst : tableinst) (v_reserved__nat : nat), tableinst.

Axiom fun_growmemory : forall (v_meminst : meminst) (v_reserved__nat : nat), meminst.

Record context := mkcontext
{	context__TYPES : (list functype)
;	context__FUNCS : (list functype)
;	context__GLOBALS : (list globaltype)
;	context__TABLES : (list tabletype)
;	context__MEMS : (list memtype)
;	context__LOCALS : (list valtype)
;	context__LABELS : (list resulttype)
;	context__RETURN : (option resulttype)
}.

Global Instance Inhabited_context : Inhabited context := 
{default_val := {|
	context__TYPES := default_val;
	context__FUNCS := default_val;
	context__GLOBALS := default_val;
	context__TABLES := default_val;
	context__MEMS := default_val;
	context__LOCALS := default_val;
	context__LABELS := default_val;
	context__RETURN := default_val|} }.

Definition list__context  := (list (context )).

Definition _append_context (arg1 arg2 : context) :=
{|
	context__TYPES := arg1.(context__TYPES) ++ arg2.(context__TYPES);
	context__FUNCS := arg1.(context__FUNCS) ++ arg2.(context__FUNCS);
	context__GLOBALS := arg1.(context__GLOBALS) ++ arg2.(context__GLOBALS);
	context__TABLES := arg1.(context__TABLES) ++ arg2.(context__TABLES);
	context__MEMS := arg1.(context__MEMS) ++ arg2.(context__MEMS);
	context__LOCALS := arg1.(context__LOCALS) ++ arg2.(context__LOCALS);
	context__LABELS := arg1.(context__LABELS) ++ arg2.(context__LABELS);
	context__RETURN := arg1.(context__RETURN) ++ arg2.(context__RETURN);
|}.

Global Instance Append_context : Append context := { _append arg1 arg2 := _append_context arg1 arg2 }.

#[export] Instance eta__context : Settable _ := settable! mkcontext <context__TYPES;context__FUNCS;context__GLOBALS;context__TABLES;context__MEMS;context__LOCALS;context__LABELS;context__RETURN>.

Inductive Limits_ok: limits -> nat -> Prop :=
	| Limits_ok__ : forall (v_n : n) (v_m : m) (v_k : nat), ((v_n <= v_m) /\ (v_m <= v_k)) -> Limits_ok (limits__ v_n v_m) v_k.

Inductive Functype_ok: functype -> Prop :=
	| Functype_ok__OK : forall (v_t_1 : (list valtype)) (v_t_2 : (option valtype)), Functype_ok (functype__ v_t_1 v_t_2).

Inductive Globaltype_ok: globaltype -> Prop :=
	| Globaltype_ok__OK : forall (v_t : valtype) (v_w0 : (option unit)), Globaltype_ok (globaltype__ (mut__MUT v_w0) v_t).

Inductive Tabletype_ok: tabletype -> Prop :=
	| Tabletype_ok__OK : forall (v_limits : limits), (Limits_ok v_limits ((2 ^ 32) - 1)) -> Tabletype_ok v_limits.

Inductive Memtype_ok: memtype -> Prop :=
	| Memtype_ok__OK : forall (v_limits : limits), (Limits_ok v_limits (2 ^ 16)) -> Memtype_ok v_limits.

Inductive Externtype_ok: externtype -> Prop :=
	| Externtype_ok__funcOK : forall (v_functype : functype), (Functype_ok v_functype) -> Externtype_ok (externtype__FUNC v_functype)
	| Externtype_ok__globalOK : forall (v_globaltype : globaltype), (Globaltype_ok v_globaltype) -> Externtype_ok (externtype__GLOBAL v_globaltype)
	| Externtype_ok__tableOK : forall (v_tabletype : tabletype), (Tabletype_ok v_tabletype) -> Externtype_ok (externtype__TABLE v_tabletype)
	| Externtype_ok__memOK : forall (v_memtype : memtype), (Memtype_ok v_memtype) -> Externtype_ok (externtype__MEM v_memtype).

Inductive Limits_sub: limits -> limits -> Prop :=
	| Limits_sub__ : forall (v_n_11 : n) (v_n_12 : n) (v_n_21 : n) (v_n_22 : n), (v_n_11 >= v_n_21) /\ (v_n_12 <= v_n_22) -> Limits_sub (limits__ v_n_11 v_n_12) (limits__ v_n_21 v_n_22).

Inductive Functype_sub: functype -> functype -> Prop :=
	| Functype_sub__ : forall (v_ft : functype), Functype_sub v_ft v_ft.

Inductive Globaltype_sub: globaltype -> globaltype -> Prop :=
	| Globaltype_sub__ : forall (v_gt : globaltype), Globaltype_sub v_gt v_gt.

Inductive Tabletype_sub: tabletype -> tabletype -> Prop :=
	| Tabletype_sub__ : forall (v_lim_1 : limits) (v_lim_2 : limits), (Limits_sub v_lim_1 v_lim_2) -> Tabletype_sub v_lim_1 v_lim_2.

Inductive Memtype_sub: memtype -> memtype -> Prop :=
	| Memtype_sub__ : forall (v_lim_1 : limits) (v_lim_2 : limits), (Limits_sub v_lim_1 v_lim_2) -> Memtype_sub v_lim_1 v_lim_2.

Inductive Externtype_sub: externtype -> externtype -> Prop :=
	| Externtype_sub__func : forall (v_ft_1 : functype) (v_ft_2 : functype), (Functype_sub v_ft_1 v_ft_2) -> Externtype_sub (externtype__FUNC v_ft_1) (externtype__FUNC v_ft_2)
	| Externtype_sub__global : forall (v_gt_1 : globaltype) (v_gt_2 : globaltype), (Globaltype_sub v_gt_1 v_gt_2) -> Externtype_sub (externtype__GLOBAL v_gt_1) (externtype__GLOBAL v_gt_2)
	| Externtype_sub__table : forall (v_tt_1 : tabletype) (v_tt_2 : tabletype), (Tabletype_sub v_tt_1 v_tt_2) -> Externtype_sub (externtype__TABLE v_tt_1) (externtype__TABLE v_tt_2)
	| Externtype_sub__mem : forall (v_mt_1 : memtype) (v_mt_2 : memtype), (Memtype_sub v_mt_1 v_mt_2) -> Externtype_sub (externtype__MEM v_mt_1) (externtype__MEM v_mt_2).

Inductive Instr_ok: context -> instr -> functype -> Prop :=
	| Instr_ok__nop : forall (v_C : context), Instr_ok v_C (instr__NOP ) (functype__ [] [])
	| Instr_ok__unreachable : forall (v_C : context) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), Instr_ok v_C (instr__UNREACHABLE ) (functype__ v_t_1 v_t_2)
	| Instr_ok__drop : forall (v_C : context) (v_t : valtype), Instr_ok v_C (instr__DROP ) (functype__ [v_t] [])
	| Instr_ok__select : forall (v_C : context) (v_t : valtype), Instr_ok v_C (instr__SELECT ) (functype__ [v_t;v_t;(valtype__INN (inn__I32 ))] [v_t])
	| Instr_ok__block : forall (v_C : context) (v_t : (option valtype)) (v_instr : (list instr)), (Instrs_ok ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := [v_t]; context__RETURN := None |} ++ v_C) v_instr (functype__ [] v_t)) -> Instr_ok v_C (instr__BLOCK v_t v_instr) (functype__ [] v_t)
	| Instr_ok__loop : forall (v_C : context) (v_t : (option valtype)) (v_instr : (list instr)), (Instrs_ok ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := [None]; context__RETURN := None |} ++ v_C) v_instr (functype__ [] v_t)) -> Instr_ok v_C (instr__LOOP v_t v_instr) (functype__ [] v_t)
	| Instr_ok__if : forall (v_C : context) (v_t : (option valtype)) (v_instr_1 : (list instr)) (v_instr_2 : (list instr)), (Instrs_ok ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := [v_t]; context__RETURN := None |} ++ v_C) v_instr_1 (functype__ [] v_t)) /\ (Instrs_ok ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := [v_t]; context__RETURN := None |} ++ v_C) v_instr_2 (functype__ [] v_t)) -> Instr_ok v_C (instr__IFELSE v_t v_instr_1 v_instr_2) (functype__ [(valtype__INN (inn__I32 ))] v_t)
	| Instr_ok__br : forall (v_C : context) (v_l : labelidx) (v_t_1 : (list valtype)) (v_t : (option valtype)) (v_t_2 : (list valtype)), (v_l < (List.length (context__LABELS v_C))) /\ ((lookup_total (context__LABELS v_C) v_l) = v_t) -> Instr_ok v_C (instr__BR v_l) (functype__ (@app _ v_t_1 v_t) v_t_2)
	| Instr_ok__br_if : forall (v_C : context) (v_l : labelidx) (v_t : (option valtype)), (v_l < (List.length (context__LABELS v_C))) /\ ((lookup_total (context__LABELS v_C) v_l) = v_t) -> Instr_ok v_C (instr__BR_IF v_l) (functype__ (@app _ v_t [(valtype__INN (inn__I32 ))]) v_t)
	| Instr_ok__br_table : forall (v_C : context) (v_l : (list labelidx)) (v_l' : labelidx) (v_t_1 : (list valtype)) (v_t : (option valtype)) (v_t_2 : (list valtype)), (v_l' < (List.length (context__LABELS v_C))) /\ List.Forall (fun v_l => (v_l < (List.length (context__LABELS v_C)))) (v_l) /\ (v_t = (lookup_total (context__LABELS v_C) v_l')) /\ List.Forall (fun v_l => (v_t = (lookup_total (context__LABELS v_C) v_l))) (v_l) -> Instr_ok v_C (instr__BR_TABLE v_l v_l') (functype__ (@app _ v_t_1 (@app _ v_t [(valtype__INN (inn__I32 ))])) v_t_2)
	| Instr_ok__call : forall (v_C : context) (v_x : idx) (v_t_1 : (list valtype)) (v_t_2 : (option valtype)), (v_x < (List.length (context__FUNCS v_C))) /\ ((lookup_total (context__FUNCS v_C) v_x) = (functype__ v_t_1 v_t_2)) -> Instr_ok v_C (instr__CALL v_x) (functype__ v_t_1 v_t_2)
	| Instr_ok__call_indirect : forall (v_C : context) (v_x : idx) (v_t_1 : (list valtype)) (v_t_2 : (option valtype)), (v_x < (List.length (context__TYPES v_C))) /\ ((lookup_total (context__TYPES v_C) v_x) = (functype__ v_t_1 v_t_2)) -> Instr_ok v_C (instr__CALL_INDIRECT v_x) (functype__ (@app _ v_t_1 [(valtype__INN (inn__I32 ))]) v_t_2)
	| Instr_ok__return : forall (v_C : context) (v_t_1 : (list valtype)) (v_t : (option valtype)) (v_t_2 : (list valtype)), ((context__RETURN v_C) = (Some v_t)) -> Instr_ok v_C (instr__RETURN ) (functype__ (@app _ v_t_1 v_t) v_t_2)
	| Instr_ok__const : forall (v_C : context) (v_t : valtype) (v_c_t : val_), Instr_ok v_C (instr__CONST v_t (v_c_t : val_)) (functype__ [] [v_t])
	| Instr_ok__unop : forall (v_C : context) (v_t : valtype) (v_unop_t : unop_), Instr_ok v_C (instr__UNOP v_t (v_unop_t : unop_)) (functype__ [v_t] [v_t])
	| Instr_ok__binop : forall (v_C : context) (v_t : valtype) (v_binop_t : binop_), Instr_ok v_C (instr__BINOP v_t (v_binop_t : binop_)) (functype__ [v_t;v_t] [v_t])
	| Instr_ok__testop : forall (v_C : context) (v_t : valtype) (v_testop_t : testop_), Instr_ok v_C (instr__TESTOP v_t (v_testop_t : testop_)) (functype__ [v_t] [(valtype__INN (inn__I32 ))])
	| Instr_ok__relop : forall (v_C : context) (v_t : valtype) (v_relop_t : relop_), Instr_ok v_C (instr__RELOP v_t (v_relop_t : relop_)) (functype__ [v_t;v_t] [(valtype__INN (inn__I32 ))])
	| Instr_ok__cvtop_reinterpret : forall (v_C : context) (v_t_1 : valtype) (v_t_2 : valtype), ((fun_size v_t_1) = (fun_size v_t_2)) -> Instr_ok v_C (instr__CVTOP v_t_1 (cvtop__REINTERPRET ) v_t_2 None) (functype__ [v_t_2] [v_t_1])
	| Instr_ok__cvtop_convert_i : forall (v_C : context) (v_inn_1 : inn) (v_inn_2 : inn) (v_sx : (option sx)), ((v_sx = None) <-> ((fun_size (valtype__INN v_inn_1)) > (fun_size (valtype__INN v_inn_2)))) -> Instr_ok v_C (instr__CVTOP (valtype__INN v_inn_1) (cvtop__CONVERT ) (valtype__INN v_inn_2) v_sx) (functype__ [(valtype__INN v_inn_2)] [(valtype__INN v_inn_1)])
	| Instr_ok__cvtop_convert_f : forall (v_C : context) (v_fnn_1 : fnn) (v_fnn_2 : fnn), Instr_ok v_C (instr__CVTOP (valtype__FNN v_fnn_1) (cvtop__CONVERT ) (valtype__FNN v_fnn_2) None) (functype__ [(valtype__FNN v_fnn_2)] [(valtype__FNN v_fnn_1)])
	| Instr_ok__local_get : forall (v_C : context) (v_x : idx) (v_t : valtype), (v_x < (List.length (context__LOCALS v_C))) /\ ((lookup_total (context__LOCALS v_C) v_x) = v_t) -> Instr_ok v_C (instr__LOCAL_GET v_x) (functype__ [] [v_t])
	| Instr_ok__local_set : forall (v_C : context) (v_x : idx) (v_t : valtype), (v_x < (List.length (context__LOCALS v_C))) /\ ((lookup_total (context__LOCALS v_C) v_x) = v_t) -> Instr_ok v_C (instr__LOCAL_SET v_x) (functype__ [v_t] [])
	| Instr_ok__local_tee : forall (v_C : context) (v_x : idx) (v_t : valtype), (v_x < (List.length (context__LOCALS v_C))) /\ ((lookup_total (context__LOCALS v_C) v_x) = v_t) -> Instr_ok v_C (instr__LOCAL_TEE v_x) (functype__ [v_t] [v_t])
	| Instr_ok__global_get : forall (v_C : context) (v_x : idx) (v_t : valtype) (v_mut : mut), (v_x < (List.length (context__GLOBALS v_C))) /\ ((lookup_total (context__GLOBALS v_C) v_x) = (globaltype__ v_mut v_t)) -> Instr_ok v_C (instr__GLOBAL_GET v_x) (functype__ [] [v_t])
	| Instr_ok__global_set : forall (v_C : context) (v_x : idx) (v_t : valtype), (v_x < (List.length (context__GLOBALS v_C))) /\ ((lookup_total (context__GLOBALS v_C) v_x) = (globaltype__ (mut__MUT (Some tt)) v_t)) -> Instr_ok v_C (instr__GLOBAL_SET v_x) (functype__ [v_t] [])
	| Instr_ok__memory_size : forall (v_C : context) (v_mt : memtype), (0 < (List.length (context__MEMS v_C))) /\ ((lookup_total (context__MEMS v_C) 0) = v_mt) -> Instr_ok v_C (instr__MEMORY_SIZE ) (functype__ [] [(valtype__INN (inn__I32 ))])
	| Instr_ok__memory_grow : forall (v_C : context) (v_mt : memtype), (0 < (List.length (context__MEMS v_C))) /\ ((lookup_total (context__MEMS v_C) 0) = v_mt) -> Instr_ok v_C (instr__MEMORY_GROW ) (functype__ [(valtype__INN (inn__I32 ))] [(valtype__INN (inn__I32 ))])
	| Instr_ok__load : forall (v_C : context) (v_nt : valtype) (v_n : (option n)) (v_sx : (option sx)) (v_memop : memop) (v_mt : memtype) (v_inn : inn), (0 < (List.length (context__MEMS v_C))) /\ ((v_n = None) <-> (v_sx = None)) /\ ((lookup_total (context__MEMS v_C) 0) = v_mt) /\ ((2 ^ (memop__ALIGN v_memop)) <= ((fun_size v_nt) / 8)) /\ List.Forall (fun v_n => (((2 ^ (memop__ALIGN v_memop)) <= (v_n / 8)) /\ ((v_n / 8) < ((fun_size v_nt) / 8)))) (option_to_list v_n) /\ ((v_n = None) \/ (v_nt = (valtype__INN v_inn))) -> Instr_ok v_C (instr__LOAD_ v_nt (option_zipWith (fun v_n v_sx => ((packsize__ v_n), v_sx)) v_n v_sx) v_memop) (functype__ [(valtype__INN (inn__I32 ))] [v_nt])
	| Instr_ok__store : forall (v_C : context) (v_nt : valtype) (v_n : (option n)) (v_memop : memop) (v_mt : memtype) (v_inn : inn), (0 < (List.length (context__MEMS v_C))) /\ ((lookup_total (context__MEMS v_C) 0) = v_mt) /\ ((2 ^ (memop__ALIGN v_memop)) <= ((fun_size v_nt) / 8)) /\ List.Forall (fun v_n => (((2 ^ (memop__ALIGN v_memop)) <= (v_n / 8)) /\ ((v_n / 8) < ((fun_size v_nt) / 8)))) (option_to_list v_n) /\ ((v_n = None) \/ (v_nt = (valtype__INN v_inn))) -> Instr_ok v_C (instr__STORE v_nt (option_map (fun v_n => (packsize__ v_n)) (v_n)) v_memop) (functype__ [(valtype__INN (inn__I32 ));v_nt] [])

with

Instrs_ok: context -> (list instr) -> functype -> Prop :=
	| Instrs_ok__empty : forall (v_C : context), Instrs_ok v_C [] (functype__ [] [])
	| Instrs_ok__seq : forall (v_C : context) (v_instr_1 : (list instr)) (v_instr_2 : instr) (v_t_1 : (list valtype)) (v_t_3 : (list valtype)) (v_t_2 : (list valtype)), (Instrs_ok v_C v_instr_1 (functype__ v_t_1 v_t_2)) /\ (Instr_ok v_C v_instr_2 (functype__ v_t_2 v_t_3)) -> Instrs_ok v_C (@app _ v_instr_1 [v_instr_2]) (functype__ v_t_1 v_t_3)
	| Instrs_ok__frame : forall (v_C : context) (v_instr : (list instr)) (v_t : (list valtype)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), (Instrs_ok v_C v_instr (functype__ v_t_1 v_t_2)) -> Instrs_ok v_C v_instr (functype__ (@app _ v_t v_t_1) (@app _ v_t v_t_2)).

Inductive Expr_ok: context -> expr -> resulttype -> Prop :=
	| Expr_ok__ : forall (v_C : context) (v_instr : (list instr)) (v_t : (option valtype)), (Instrs_ok v_C v_instr (functype__ [] v_t)) -> Expr_ok v_C v_instr v_t.

Inductive Instr_const: context -> instr -> Prop :=
	| Instr_const__constCONST : forall (v_C : context) (v_t : valtype) (v_c : val_), Instr_const v_C (instr__CONST v_t (v_c : val_))
	| Instr_const__global_getCONST : forall (v_C : context) (v_x : idx) (v_t : valtype), (v_x < (List.length (context__GLOBALS v_C))) /\ ((lookup_total (context__GLOBALS v_C) v_x) = (globaltype__ (mut__MUT None) v_t)) -> Instr_const v_C (instr__GLOBAL_GET v_x).

Inductive Expr_const: context -> expr -> Prop :=
	| Expr_const__CONST : forall (v_C : context) (v_instr : (list instr)), List.Forall (fun v_instr => (Instr_const v_C v_instr)) (v_instr) -> Expr_const v_C v_instr.

Inductive Expr_ok_const: context -> expr -> (option valtype) -> Prop :=
	| Expr_ok_const__CONST : forall (v_C : context) (v_expr : expr) (v_t : (option valtype)), (Expr_ok v_C v_expr v_t) /\ (Expr_const v_C v_expr) -> Expr_ok_const v_C v_expr v_t.

Inductive Type_ok: type -> functype -> Prop :=
	| Type_ok__ : forall (v_ft : functype), (Functype_ok v_ft) -> Type_ok (type__TYPE v_ft) v_ft.

Inductive Func_ok: context -> func -> functype -> Prop :=
	| Func_ok__ : forall (v_C : context) (v_x : idx) (v_t : (list valtype)) (v_expr : expr) (v_t_1 : (list valtype)) (v_t_2 : (option valtype)), (v_x < (List.length (context__TYPES v_C))) /\ ((lookup_total (context__TYPES v_C) v_x) = (functype__ v_t_1 v_t_2)) /\ (Expr_ok ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := []; context__RETURN := (Some v_t_2) |} ++ ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := [v_t_2]; context__RETURN := None |} ++ ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := (@app _ v_t_1 v_t); context__LABELS := []; context__RETURN := None |} ++ v_C))) v_expr v_t_2) -> Func_ok v_C (func__FUNC v_x (List.map (fun v_t => (local__LOCAL v_t)) (v_t)) v_expr) (functype__ v_t_1 v_t_2).

Inductive Global_ok: context -> global -> globaltype -> Prop :=
	| Global_ok__ : forall (v_C : context) (v_gt : globaltype) (v_expr : expr) (v_mut : mut) (v_t : valtype), (Globaltype_ok v_gt) /\ (v_gt = (globaltype__ v_mut v_t)) /\ (Expr_ok_const v_C v_expr (Some v_t)) -> Global_ok v_C (global__GLOBAL v_gt v_expr) v_gt.

Inductive Table_ok: context -> table -> tabletype -> Prop :=
	| Table_ok__ : forall (v_C : context) (v_reserved__tt : tabletype), (Tabletype_ok v_reserved__tt) -> Table_ok v_C (table__TABLE v_reserved__tt) v_reserved__tt.

Inductive Mem_ok: context -> mem -> memtype -> Prop :=
	| Mem_ok__ : forall (v_C : context) (v_mt : memtype), (Memtype_ok v_mt) -> Mem_ok v_C (mem__MEMORY v_mt) v_mt.

Inductive Elem_ok: context -> elem -> Prop :=
	| Elem_ok__OK : forall (v_C : context) (v_expr : expr) (v_x : (list idx)) (v_lim : limits) (v_ft : (list functype)), (0 < (List.length (context__TABLES v_C))) /\ ((List.length v_ft) = (List.length v_x)) /\ List.Forall2 (fun v_ft v_x => (v_x < (List.length (context__FUNCS v_C)))) (v_ft) (v_x) /\ ((lookup_total (context__TABLES v_C) 0) = v_lim) /\ (Expr_ok_const v_C v_expr (Some (valtype__INN (inn__I32 )))) /\ List.Forall2 (fun v_ft v_x => ((lookup_total (context__FUNCS v_C) v_x) = v_ft)) (v_ft) (v_x) -> Elem_ok v_C (elem__ELEM v_expr v_x).

Inductive Data_ok: context -> data -> Prop :=
	| Data_ok__OK : forall (v_C : context) (v_expr : expr) (v_b : (list byte)) (v_lim : limits), (0 < (List.length (context__MEMS v_C))) /\ ((lookup_total (context__MEMS v_C) 0) = v_lim) /\ (Expr_ok_const v_C v_expr (Some (valtype__INN (inn__I32 )))) -> Data_ok v_C (data__DATA v_expr v_b).

Inductive Start_ok: context -> start -> Prop :=
	| Start_ok__OK : forall (v_C : context) (v_x : idx), (v_x < (List.length (context__FUNCS v_C))) /\ ((lookup_total (context__FUNCS v_C) v_x) = (functype__ [] [])) -> Start_ok v_C (start__START v_x).

Inductive Import_ok: context -> import -> externtype -> Prop :=
	| Import_ok__ : forall (v_C : context) (v_name_1 : name) (v_name_2 : name) (v_xt : externtype), (Externtype_ok v_xt) -> Import_ok v_C (import__IMPORT v_name_1 v_name_2 v_xt) v_xt.

Inductive Externidx_ok: context -> externidx -> externtype -> Prop :=
	| Externidx_ok__func : forall (v_C : context) (v_x : idx) (v_ft : functype), (v_x < (List.length (context__FUNCS v_C))) /\ ((lookup_total (context__FUNCS v_C) v_x) = v_ft) -> Externidx_ok v_C (externidx__FUNC v_x) (externtype__FUNC v_ft)
	| Externidx_ok__global : forall (v_C : context) (v_x : idx) (v_gt : globaltype), (v_x < (List.length (context__GLOBALS v_C))) /\ ((lookup_total (context__GLOBALS v_C) v_x) = v_gt) -> Externidx_ok v_C (externidx__GLOBAL v_x) (externtype__GLOBAL v_gt)
	| Externidx_ok__table : forall (v_C : context) (v_x : idx) (v_reserved__tt : tabletype), (v_x < (List.length (context__TABLES v_C))) /\ ((lookup_total (context__TABLES v_C) v_x) = v_reserved__tt) -> Externidx_ok v_C (externidx__TABLE v_x) (externtype__TABLE v_reserved__tt)
	| Externidx_ok__mem : forall (v_C : context) (v_x : idx) (v_mt : memtype), (v_x < (List.length (context__MEMS v_C))) /\ ((lookup_total (context__MEMS v_C) v_x) = v_mt) -> Externidx_ok v_C (externidx__MEM v_x) (externtype__MEM v_mt).

Inductive Export_ok: context -> export -> externtype -> Prop :=
	| Export_ok__ : forall (v_C : context) (v_name : name) (v_externidx : externidx) (v_xt : externtype), (Externidx_ok v_C v_externidx v_xt) -> Export_ok v_C (export__EXPORT v_name v_externidx) v_xt.

Inductive Module_ok: module -> Prop :=
	| Module_ok__OK : forall (v_type : (list type)) (v_import : (list import)) (v_func : (list func)) (v_global : (list global)) (v_table : (list table)) (v_mem : (list mem)) (v_elem : (list elem)) (v_data : (list data)) (v_start : (option start)) (v_export : (list export)) (v_ft' : (list functype)) (v_ixt : (list externtype)) (v_C' : context) (v_gt : (list globaltype)) (v_C : context) (v_ft : (list functype)) (v_reserved__tt : (list tabletype)) (v_mt : (list memtype)) (v_xt : (list externtype)) (v_ift : (list functype)) (v_igt : (list globaltype)) (v_itt : (list tabletype)) (v_imt : (list memtype)), ((List.length v_ft') = (List.length v_type)) /\ ((List.length v_import) = (List.length v_ixt)) /\ ((List.length v_global) = (List.length v_gt)) /\ ((List.length v_ft) = (List.length v_func)) /\ ((List.length v_table) = (List.length v_reserved__tt)) /\ ((List.length v_mem) = (List.length v_mt)) /\ ((List.length v_export) = (List.length v_xt)) /\ List.Forall2 (fun v_ft' v_type => (Type_ok v_type v_ft')) (v_ft') (v_type) /\ List.Forall2 (fun v_import v_ixt => (Import_ok {| context__TYPES := v_ft'; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := []; context__RETURN := None |} v_import v_ixt)) (v_import) (v_ixt) /\ List.Forall2 (fun v_global v_gt => (Global_ok v_C' v_global v_gt)) (v_global) (v_gt) /\ List.Forall2 (fun v_ft v_func => (Func_ok v_C v_func v_ft)) (v_ft) (v_func) /\ List.Forall2 (fun v_table v_reserved__tt => (Table_ok v_C v_table v_reserved__tt)) (v_table) (v_reserved__tt) /\ List.Forall2 (fun v_mem v_mt => (Mem_ok v_C v_mem v_mt)) (v_mem) (v_mt) /\ List.Forall (fun v_elem => (Elem_ok v_C v_elem)) (v_elem) /\ List.Forall (fun v_data => (Data_ok v_C v_data)) (v_data) /\ List.Forall (fun v_start => (Start_ok v_C v_start)) (option_to_list v_start) /\ List.Forall2 (fun v_export v_xt => (Export_ok v_C v_export v_xt)) (v_export) (v_xt) /\ ((List.length v_reserved__tt) <= 1) /\ ((List.length v_mt) <= 1) /\ (v_C = {| context__TYPES := v_ft'; context__FUNCS := (@app _ v_ift v_ft); context__GLOBALS := (@app _ v_igt v_gt); context__TABLES := (@app _ v_itt v_reserved__tt); context__MEMS := (@app _ v_imt v_mt); context__LOCALS := []; context__LABELS := []; context__RETURN := None |}) /\ (v_C' = {| context__TYPES := v_ft'; context__FUNCS := (@app _ v_ift v_ft); context__GLOBALS := v_igt; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := []; context__RETURN := None |}) /\ (v_ift = (fun_funcsxt v_ixt)) /\ (v_igt = (fun_globalsxt v_ixt)) /\ (v_itt = (fun_tablesxt v_ixt)) /\ (v_imt = (fun_memsxt v_ixt)) -> Module_ok (module__MODULE v_type v_import v_func v_global v_table v_mem v_elem v_data v_start v_export).

Definition fun_coec_val__admininstr (v_val : val) : admininstr :=
	match (v_val) with
		| (val__CONST v_0 v_1) => (admininstr__CONST v_0 v_1)
	end.

Coercion fun_coec_val__admininstr : val >-> admininstr.

Definition list__val__admininstr : list__val -> list__admininstr := map fun_coec_val__admininstr.

Coercion list__val__admininstr : list__val >-> list__admininstr.

Definition fun_coec_instr__admininstr (v_instr : instr) : admininstr :=
	match (v_instr) with
		| (instr__NOP ) => (admininstr__NOP )
		| (instr__UNREACHABLE ) => (admininstr__UNREACHABLE )
		| (instr__DROP ) => (admininstr__DROP )
		| (instr__SELECT ) => (admininstr__SELECT )
		| (instr__BLOCK v_0 v_1) => (admininstr__BLOCK v_0 v_1)
		| (instr__LOOP v_0 v_1) => (admininstr__LOOP v_0 v_1)
		| (instr__IFELSE v_0 v_1 v_2) => (admininstr__IFELSE v_0 v_1 v_2)
		| (instr__BR v_0) => (admininstr__BR v_0)
		| (instr__BR_IF v_0) => (admininstr__BR_IF v_0)
		| (instr__BR_TABLE v_0 v_1) => (admininstr__BR_TABLE v_0 v_1)
		| (instr__CALL v_0) => (admininstr__CALL v_0)
		| (instr__CALL_INDIRECT v_0) => (admininstr__CALL_INDIRECT v_0)
		| (instr__RETURN ) => (admininstr__RETURN )
		| (instr__CONST v_0 v_1) => (admininstr__CONST v_0 v_1)
		| (instr__UNOP v_0 v_1) => (admininstr__UNOP v_0 v_1)
		| (instr__BINOP v_0 v_1) => (admininstr__BINOP v_0 v_1)
		| (instr__TESTOP v_0 v_1) => (admininstr__TESTOP v_0 v_1)
		| (instr__RELOP v_0 v_1) => (admininstr__RELOP v_0 v_1)
		| (instr__CVTOP v_0 v_1 v_2 v_3) => (admininstr__CVTOP v_0 v_1 v_2 v_3)
		| (instr__LOCAL_GET v_0) => (admininstr__LOCAL_GET v_0)
		| (instr__LOCAL_SET v_0) => (admininstr__LOCAL_SET v_0)
		| (instr__LOCAL_TEE v_0) => (admininstr__LOCAL_TEE v_0)
		| (instr__GLOBAL_GET v_0) => (admininstr__GLOBAL_GET v_0)
		| (instr__GLOBAL_SET v_0) => (admininstr__GLOBAL_SET v_0)
		| (instr__LOAD_ v_0 v_1 v_2) => (admininstr__LOAD_ v_0 v_1 v_2)
		| (instr__STORE v_0 v_1 v_2) => (admininstr__STORE v_0 v_1 v_2)
		| (instr__MEMORY_SIZE ) => (admininstr__MEMORY_SIZE )
		| (instr__MEMORY_GROW ) => (admininstr__MEMORY_GROW )
	end.

Coercion fun_coec_instr__admininstr : instr >-> admininstr.

Definition list__instr__admininstr : list__instr -> list__admininstr := map fun_coec_instr__admininstr.

Coercion list__instr__admininstr : list__instr >-> list__admininstr.

Inductive Step_pure: (list admininstr) -> (list admininstr) -> Prop :=
	| Step_pure__unreachable : Step_pure [(admininstr__UNREACHABLE )] [(admininstr__TRAP )]
	| Step_pure__nop : Step_pure [(admininstr__NOP )] []
	| Step_pure__drop : forall (v_val : val), Step_pure [(v_val : admininstr);(admininstr__DROP )] []
	| Step_pure__select_true : forall (v_val_1 : val) (v_val_2 : val) (v_c : iN), ((v_c : val_) <> 0) -> Step_pure [(v_val_1 : admininstr);(v_val_2 : admininstr);(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__SELECT )] [(v_val_1 : admininstr)]
	| Step_pure__select_false : forall (v_val_1 : val) (v_val_2 : val) (v_c : iN), ((v_c : val_) = 0) -> Step_pure [(v_val_1 : admininstr);(v_val_2 : admininstr);(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__SELECT )] [(v_val_2 : admininstr)]
	| Step_pure__if_true : forall (v_c : iN) (v_t : (option valtype)) (v_instr_1 : (list instr)) (v_instr_2 : (list instr)), ((v_c : val_) <> 0) -> Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__IFELSE v_t v_instr_1 v_instr_2)] [(admininstr__BLOCK v_t v_instr_1)]
	| Step_pure__if_false : forall (v_c : iN) (v_t : (option valtype)) (v_instr_1 : (list instr)) (v_instr_2 : (list instr)), ((v_c : val_) = 0) -> Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__IFELSE v_t v_instr_1 v_instr_2)] [(admininstr__BLOCK v_t v_instr_2)]
	| Step_pure__label_vals : forall (v_n : n) (v_instr : (list instr)) (v_val : (list val)), Step_pure [(admininstr__LABEL_ v_n v_instr (list__val__admininstr v_val))] (list__val__admininstr v_val)
	| Step_pure__br_zero : forall (v_n : n) (v_instr' : (list instr)) (v_val' : (list val)) (v_val : (list val)) (v_instr : (list instr)), Step_pure [(admininstr__LABEL_ v_n v_instr' (@app _ (list__val__admininstr v_val') (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__BR 0)] (list__instr__admininstr v_instr)))))] (@app _ (list__val__admininstr v_val) (list__instr__admininstr v_instr'))
	| Step_pure__br_succ : forall (v_n : n) (v_instr' : (list instr)) (v_val : (list val)) (v_l : labelidx) (v_instr : (list instr)), Step_pure [(admininstr__LABEL_ v_n v_instr' (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__BR (v_l + 1))] (list__instr__admininstr v_instr))))] (@app _ (list__val__admininstr v_val) [(admininstr__BR v_l)])
	| Step_pure__br_if_true : forall (v_c : iN) (v_l : labelidx), ((v_c : val_) <> 0) -> Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__BR_IF v_l)] [(admininstr__BR v_l)]
	| Step_pure__br_if_false : forall (v_c : iN) (v_l : labelidx), ((v_c : val_) = 0) -> Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__BR_IF v_l)] []
	| Step_pure__br_table_lt : forall (v_i : nat) (v_l : (list labelidx)) (v_l' : labelidx), (v_i < (List.length v_l)) -> Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__BR_TABLE v_l v_l')] [(admininstr__BR (lookup_total v_l v_i))]
	| Step_pure__br_table_ge : forall (v_i : nat) (v_l : (list labelidx)) (v_l' : labelidx), (v_i >= (List.length v_l)) -> Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__BR_TABLE v_l v_l')] [(admininstr__BR v_l')]
	| Step_pure__frame_vals : forall (v_n : n) (v_f : frame) (v_val : (list val)), Step_pure [(admininstr__FRAME_ v_n v_f (list__val__admininstr v_val))] (list__val__admininstr v_val)
	| Step_pure__return_frame : forall (v_n : n) (v_f : frame) (v_val' : (list val)) (v_val : (list val)) (v_instr : (list instr)), Step_pure [(admininstr__FRAME_ v_n v_f (@app _ (list__val__admininstr v_val') (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__RETURN )] (list__instr__admininstr v_instr)))))] (list__val__admininstr v_val)
	| Step_pure__return_label : forall (v_n : n) (v_instr' : (list instr)) (v_val : (list val)) (v_instr : (list instr)), Step_pure [(admininstr__LABEL_ v_n v_instr' (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__RETURN )] (list__instr__admininstr v_instr))))] (@app _ (list__val__admininstr v_val) [(admininstr__RETURN )])
	| Step_pure__trap_vals : forall (v_val : (list val)) (v_instr : (list instr)), ((v_val <> []) \/ (v_instr <> [])) -> Step_pure (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__TRAP )] (list__instr__admininstr v_instr))) [(admininstr__TRAP )]
	| Step_pure__trap_label : forall (v_n : n) (v_instr' : (list instr)), Step_pure [(admininstr__LABEL_ v_n v_instr' [(admininstr__TRAP )])] [(admininstr__TRAP )]
	| Step_pure__trap_frame : forall (v_n : n) (v_f : frame), Step_pure [(admininstr__FRAME_ v_n v_f [(admininstr__TRAP )])] [(admininstr__TRAP )]
	| Step_pure__unop_val : forall (v_t : valtype) (v_c_1 : val_) (v_unop : unop_) (v_c : val_), ((fun_unop v_t (v_unop : unop_) (v_c_1 : val_)) = [(v_c : val_)]) -> Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__UNOP v_t (v_unop : unop_))] [(admininstr__CONST v_t (v_c : val_))]
	| Step_pure__unop_trap : forall (v_t : valtype) (v_c_1 : val_) (v_unop : unop_), ((fun_unop v_t (v_unop : unop_) (v_c_1 : val_)) = []) -> Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__UNOP v_t (v_unop : unop_))] [(admininstr__TRAP )]
	| Step_pure__binop_val : forall (v_t : valtype) (v_c_1 : val_) (v_c_2 : val_) (v_binop : binop_) (v_c : val_), ((fun_binop v_t (v_binop : binop_) (v_c_1 : val_) (v_c_2 : val_)) = [(v_c : val_)]) -> Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__CONST v_t (v_c_2 : val_));(admininstr__BINOP v_t (v_binop : binop_))] [(admininstr__CONST v_t (v_c : val_))]
	| Step_pure__binop_trap : forall (v_t : valtype) (v_c_1 : val_) (v_c_2 : val_) (v_binop : binop_), ((fun_binop v_t (v_binop : binop_) (v_c_1 : val_) (v_c_2 : val_)) = []) -> Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__CONST v_t (v_c_2 : val_));(admininstr__BINOP v_t (v_binop : binop_))] [(admininstr__TRAP )]
	| Step_pure__testop : forall (v_t : valtype) (v_c_1 : val_) (v_testop : testop_) (v_c : iN), ((v_c : val_) = (fun_testop v_t (v_testop : testop_) (v_c_1 : val_))) -> Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__TESTOP v_t (v_testop : testop_))] [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_))]
	| Step_pure__relop : forall (v_t : valtype) (v_c_1 : val_) (v_c_2 : val_) (v_relop : relop_) (v_c : iN), ((v_c : val_) = (fun_relop v_t (v_relop : relop_) (v_c_1 : val_) (v_c_2 : val_))) -> Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__CONST v_t (v_c_2 : val_));(admininstr__RELOP v_t (v_relop : relop_))] [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_))]
	| Step_pure__cvtop_val : forall (v_t_1 : valtype) (v_c_1 : val_) (v_t_2 : valtype) (v_cvtop : cvtop) (v_sx : (option sx)) (v_c : val_), ((fun_cvtop v_t_1 v_t_2 v_cvtop v_sx (v_c_1 : val_)) = [(v_c : val_)]) -> Step_pure [(admininstr__CONST v_t_1 (v_c_1 : val_));(admininstr__CVTOP v_t_2 v_cvtop v_t_1 v_sx)] [(admininstr__CONST v_t_2 (v_c : val_))]
	| Step_pure__cvtop_trap : forall (v_t_1 : valtype) (v_c_1 : val_) (v_t_2 : valtype) (v_cvtop : cvtop) (v_sx : (option sx)), ((fun_cvtop v_t_1 v_t_2 v_cvtop v_sx (v_c_1 : val_)) = []) -> Step_pure [(admininstr__CONST v_t_1 (v_c_1 : val_));(admininstr__CVTOP v_t_2 v_cvtop v_t_1 v_sx)] [(admininstr__TRAP )]
	| Step_pure__local_tee : forall (v_val : val) (v_x : idx), Step_pure [(v_val : admininstr);(admininstr__LOCAL_TEE v_x)] [(v_val : admininstr);(v_val : admininstr);(admininstr__LOCAL_SET v_x)].

Inductive Step_read_before_Step_read__call_indirect_trap: config -> Prop :=
	| Step_read__call_indirect_call_neg : forall (v_z : state) (v_i : nat) (v_x : idx) (v_a : addr), (v_i < (List.length (tableinst__REFS (fun_table v_z 0)))) /\ (v_a < (List.length (fun_funcinst v_z))) /\ ((lookup_total (tableinst__REFS (fun_table v_z 0)) v_i) = (Some v_a)) /\ ((fun_type v_z v_x) = (funcinst__TYPE (lookup_total (fun_funcinst v_z) v_a))) -> Step_read_before_Step_read__call_indirect_trap (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CALL_INDIRECT v_x)]).

Inductive Step_read: config -> (list admininstr) -> Prop :=
	| Step_read__block : forall (v_z : state) (v_t : (option valtype)) (v_instr : (list instr)) (v_n : n), (((v_t = None) /\ (v_n = 0)) \/ ((v_t <> None) /\ (v_n = 1))) -> Step_read (config__ v_z [(admininstr__BLOCK v_t v_instr)]) [(admininstr__LABEL_ v_n [] (list__instr__admininstr v_instr))]
	| Step_read__loop : forall (v_z : state) (v_t : (option valtype)) (v_instr : (list instr)), Step_read (config__ v_z [(admininstr__LOOP v_t v_instr)]) [(admininstr__LABEL_ 0 [(instr__LOOP v_t v_instr)] (list__instr__admininstr v_instr))]
	| Step_read__call : forall (v_z : state) (v_x : idx), (v_x < (List.length (fun_funcaddr v_z))) -> Step_read (config__ v_z [(admininstr__CALL v_x)]) [(admininstr__CALL_ADDR (lookup_total (fun_funcaddr v_z) v_x))]
	| Step_read__call_indirect_call : forall (v_z : state) (v_i : nat) (v_x : idx) (v_a : addr), (v_i < (List.length (tableinst__REFS (fun_table v_z 0)))) /\ (v_a < (List.length (fun_funcinst v_z))) /\ ((lookup_total (tableinst__REFS (fun_table v_z 0)) v_i) = (Some v_a)) /\ ((fun_type v_z v_x) = (funcinst__TYPE (lookup_total (fun_funcinst v_z) v_a))) -> Step_read (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CALL_INDIRECT v_x)]) [(admininstr__CALL_ADDR v_a)]
	| Step_read__call_indirect_trap : forall (v_z : state) (v_i : nat) (v_x : idx), (~(Step_read_before_Step_read__call_indirect_trap (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CALL_INDIRECT v_x)]))) -> Step_read (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CALL_INDIRECT v_x)]) [(admininstr__TRAP )]
	| Step_read__call_addr : forall (v_z : state) (v_val : (list val)) (v_k : nat) (v_a : addr) (v_n : n) (v_f : frame) (v_instr : (list instr)) (v_t_1 : (list valtype)) (v_t_2 : (option valtype)) (v_mm : moduleinst) (v_func : func) (v_x : idx) (v_t : (list valtype)), (v_a < (List.length (fun_funcinst v_z))) /\ ((lookup_total (fun_funcinst v_z) v_a) = {| funcinst__TYPE := (functype__ v_t_1 v_t_2); funcinst__MODULE := v_mm; funcinst__CODE := v_func |}) /\ ((List.length v_t_1) = (List.length v_val)) /\ (v_func = (func__FUNC v_x (List.map (fun v_t => (local__LOCAL v_t)) (v_t)) v_instr)) /\ (v_f = {| frame__LOCALS := (@app _ v_val (List.map (fun v_t => (fun_default_ v_t)) (v_t))); frame__MODULE := v_mm |}) -> Step_read (config__ v_z (@app _ (list__val__admininstr v_val) [(admininstr__CALL_ADDR v_a)])) [(admininstr__FRAME_ v_n v_f [(admininstr__LABEL_ v_n [] (list__instr__admininstr v_instr))])]
	| Step_read__local_get : forall (v_z : state) (v_x : idx), Step_read (config__ v_z [(admininstr__LOCAL_GET v_x)]) [((fun_local v_z v_x) : admininstr)]
	| Step_read__global_get : forall (v_z : state) (v_x : idx), Step_read (config__ v_z [(admininstr__GLOBAL_GET v_x)]) [((globalinst__VALUE (fun_global v_z v_x)) : admininstr)]
	| Step_read__load_num_trap : forall (v_z : state) (v_i : nat) (v_t : valtype) (v_mo : memop), (((v_i + (memop__OFFSET v_mo)) + ((fun_size v_t) / 8)) > (List.length (meminst__BYTES (fun_mem v_z 0)))) -> Step_read (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__LOAD_ v_t None v_mo)]) [(admininstr__TRAP )]
	| Step_read__load_num_val : forall (v_z : state) (v_i : nat) (v_t : valtype) (v_mo : memop) (v_c : val_), ((fun_bytes v_t (v_c : val_)) = (list_slice (meminst__BYTES (fun_mem v_z 0)) (v_i + (memop__OFFSET v_mo)) ((fun_size v_t) / 8))) -> Step_read (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__LOAD_ v_t None v_mo)]) [(admininstr__CONST v_t (v_c : val_))]
	| Step_read__load_pack_trap : forall (v_z : state) (v_i : nat) (v_inn : inn) (v_n : n) (v_sx : sx) (v_mo : memop), (((v_i + (memop__OFFSET v_mo)) + (v_n / 8)) > (List.length (meminst__BYTES (fun_mem v_z 0)))) -> Step_read (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__LOAD_ (valtype__INN v_inn) (Some ((packsize__ v_n), v_sx)) v_mo)]) [(admininstr__TRAP )]
	| Step_read__load_pack_val : forall (v_z : state) (v_i : nat) (v_inn : inn) (v_n : n) (v_sx : sx) (v_mo : memop) (v_c : iN), ((fun_ibytes v_n v_c) = (list_slice (meminst__BYTES (fun_mem v_z 0)) (v_i + (memop__OFFSET v_mo)) (v_n / 8))) -> Step_read (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__LOAD_ (valtype__INN v_inn) (Some ((packsize__ v_n), v_sx)) v_mo)]) [(admininstr__CONST (valtype__INN v_inn) (fun_ext v_n (fun_size (valtype__INN v_inn)) v_sx v_c))]
	| Step_read__memory_size : forall (v_z : state) (v_n : n), (((v_n * 64) * (fun_Ki )) = (List.length (meminst__BYTES (fun_mem v_z 0)))) -> Step_read (config__ v_z [(admininstr__MEMORY_SIZE )]) [(admininstr__CONST (valtype__INN (inn__I32 )) (v_n : val_))].

Inductive Step: config -> config -> Prop :=
	| Step__pure : forall (v_z : state) (v_instr : (list instr)) (v_instr' : (list instr)), (Step_pure (list__instr__admininstr v_instr) (list__instr__admininstr v_instr')) -> Step (config__ v_z (list__instr__admininstr v_instr)) (config__ v_z (list__instr__admininstr v_instr'))
	| Step__read : forall (v_z : state) (v_instr : (list instr)) (v_instr' : (list instr)), (Step_read (config__ v_z (list__instr__admininstr v_instr)) (list__instr__admininstr v_instr')) -> Step (config__ v_z (list__instr__admininstr v_instr)) (config__ v_z (list__instr__admininstr v_instr'))
	| Step__ctxt_label : forall (v_z : state) (v_n : n) (v_instr_0 : (list instr)) (v_instr : (list instr)) (v_z' : state) (v_instr' : (list instr)), (Step (config__ v_z (list__instr__admininstr v_instr)) (config__ v_z' (list__instr__admininstr v_instr'))) -> Step (config__ v_z [(admininstr__LABEL_ v_n v_instr_0 (list__instr__admininstr v_instr))]) (config__ v_z' [(admininstr__LABEL_ v_n v_instr_0 (list__instr__admininstr v_instr'))])
	| Step__ctxt_frame : forall (v_s : store) (v_f : frame) (v_n : n) (v_f' : frame) (v_instr : (list instr)) (v_s' : store) (v_instr' : (list instr)), (Step (config__ (state__ v_s v_f') (list__instr__admininstr v_instr)) (config__ (state__ v_s' v_f') (list__instr__admininstr v_instr'))) -> Step (config__ (state__ v_s v_f) [(admininstr__FRAME_ v_n v_f' (list__instr__admininstr v_instr))]) (config__ (state__ v_s' v_f) [(admininstr__FRAME_ v_n v_f' (list__instr__admininstr v_instr'))])
	| Step__local_set : forall (v_z : state) (v_val : val) (v_x : idx), Step (config__ v_z [(v_val : admininstr);(admininstr__LOCAL_SET v_x)]) (config__ (fun_with_local v_z v_x v_val) [])
	| Step__global_set : forall (v_z : state) (v_val : val) (v_x : idx), Step (config__ v_z [(v_val : admininstr);(admininstr__GLOBAL_SET v_x)]) (config__ (fun_with_global v_z v_x v_val) [])
	| Step__store_num_trap : forall (v_z : state) (v_i : nat) (v_t : valtype) (v_c : val_) (v_mo : memop), (((v_i + (memop__OFFSET v_mo)) + ((fun_size v_t) / 8)) > (List.length (meminst__BYTES (fun_mem v_z 0)))) -> Step (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CONST v_t (v_c : val_));(admininstr__STORE v_t None v_mo)]) (config__ v_z [(admininstr__TRAP )])
	| Step__store_num_val : forall (v_z : state) (v_i : nat) (v_t : valtype) (v_c : val_) (v_mo : memop) (v_b : (list byte)), (v_b = (fun_bytes v_t (v_c : val_))) -> Step (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CONST v_t (v_c : val_));(admininstr__STORE v_t None v_mo)]) (config__ (fun_with_mem v_z 0 (v_i + (memop__OFFSET v_mo)) ((fun_size v_t) / 8) v_b) [])
	| Step__store_pack_trap : forall (v_z : state) (v_i : nat) (v_inn : inn) (v_c : iN) (v_n : n) (v_mo : memop), (((v_i + (memop__OFFSET v_mo)) + (v_n / 8)) > (List.length (meminst__BYTES (fun_mem v_z 0)))) -> Step (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CONST (valtype__INN v_inn) (v_c : val_));(admininstr__STORE (valtype__INN v_inn) (Some (packsize__ v_n)) v_mo)]) (config__ v_z [(admininstr__TRAP )])
	| Step__store_pack_val : forall (v_z : state) (v_i : nat) (v_inn : inn) (v_c : iN) (v_n : n) (v_mo : memop) (v_b : (list byte)), (v_b = (fun_ibytes v_n (fun_wrap (fun_size (valtype__INN v_inn)) v_n v_c))) -> Step (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CONST (valtype__INN v_inn) (v_c : val_));(admininstr__STORE (valtype__INN v_inn) (Some (packsize__ v_n)) v_mo)]) (config__ (fun_with_mem v_z 0 (v_i + (memop__OFFSET v_mo)) (v_n / 8) v_b) [])
	| Step__memory_grow_succeed : forall (v_z : state) (v_n : n) (v_mi : meminst), ((fun_growmemory (fun_mem v_z 0) v_n) = v_mi) -> Step (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_n : val_));(admininstr__MEMORY_GROW )]) (config__ (fun_with_meminst v_z 0 v_mi) [(admininstr__CONST (valtype__INN (inn__I32 )) ((List.length (meminst__BYTES (fun_mem v_z 0))) / (64 * (fun_Ki ))))])
	| Step__memory_grow_fail : forall (v_z : state) (v_n : n), Step (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_n : val_));(admininstr__MEMORY_GROW )]) (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (fun_invsigned 32 (0 - (1 : nat))))]).

Inductive Steps: config -> config -> Prop :=
	| Steps__refl : forall (v_z : state) (v_admininstr : (list admininstr)), Steps (config__ v_z v_admininstr) (config__ v_z v_admininstr)
	| Steps__trans : forall (v_z : state) (v_admininstr : (list admininstr)) (v_z'' : state) (v_admininstr'' : (list admininstr)) (v_z' : state) (v_admininstr' : admininstr), (Step (config__ v_z v_admininstr) (config__ v_z' [v_admininstr'])) /\ (Steps (config__ v_z' [v_admininstr']) (config__ v_z'' v_admininstr'')) -> Steps (config__ v_z v_admininstr) (config__ v_z'' v_admininstr'').

Inductive Eval_expr: state -> expr -> state -> (list val) -> Prop :=
	| Eval_expr__ : forall (v_z : state) (v_instr : (list instr)) (v_z' : state) (v_val : (list val)), (Steps (config__ v_z (list__instr__admininstr v_instr)) (config__ v_z' (list__val__admininstr v_val))) -> Eval_expr v_z v_instr v_z' v_val.

Inductive Val_ok: val -> valtype -> Prop :=
	| Val_ok__ : forall (v_t : valtype) (v_c_t : val_), Val_ok (val__CONST v_t (v_c_t : val_)) v_t.

Inductive Result_ok: result -> (list valtype) -> Prop :=
	| Result_ok__result : forall (v_v : (list val)) (v_t : (list valtype)), ((List.length v_t) = (List.length v_v)) /\ List.Forall2 (fun v_t v_v => (Val_ok v_v v_t)) (v_t) (v_v) -> Result_ok (result___VALS v_v) v_t
	| Result_ok__trap : forall (v_t : (list valtype)), Result_ok (result__TRAP ) v_t.

Inductive Externvals_ok: store -> externval -> externtype -> Prop :=
	| Externvals_ok__func : forall (v_S : store) (v_a : addr) (v_ext : functype) (v_minst : moduleinst) (v_code_func : func), (v_a < (List.length (store__FUNCS v_S))) /\ ((lookup_total (store__FUNCS v_S) v_a) = {| funcinst__TYPE := v_ext; funcinst__MODULE := v_minst; funcinst__CODE := v_code_func |}) -> Externvals_ok v_S (externval__FUNC v_a) (externtype__FUNC v_ext)
	| Externvals_ok__table : forall (v_S : store) (v_a : addr) (v_reserved__tt : tabletype) (v_tt' : tabletype) (v_fa : (list (option funcaddr))), (v_a < (List.length (store__TABLES v_S))) /\ ((lookup_total (store__TABLES v_S) v_a) = {| tableinst__TYPE := v_tt'; tableinst__REFS := v_fa |}) /\ (Tabletype_sub v_tt' v_reserved__tt) -> Externvals_ok v_S (externval__TABLE v_a) (externtype__TABLE v_reserved__tt)
	| Externvals_ok__mem : forall (v_S : store) (v_a : addr) (v_mt : memtype) (v_mt' : memtype) (v_b : (list byte)), (v_a < (List.length (store__MEMS v_S))) /\ ((lookup_total (store__MEMS v_S) v_a) = {| meminst__TYPE := v_mt'; meminst__BYTES := v_b |}) /\ (Memtype_sub v_mt' v_mt) -> Externvals_ok v_S (externval__MEM v_a) (externtype__MEM v_mt)
	| Externvals_ok__global : forall (v_S : store) (v_a : addr) (v_mut : mut) (v_valtype : valtype) (v_val_ : val_), (v_a < (List.length (store__GLOBALS v_S))) /\ ((lookup_total (store__GLOBALS v_S) v_a) = {| globalinst__TYPE := (globaltype__ v_mut v_valtype); globalinst__VALUE := (val__CONST v_valtype (v_val_ : val_)) |}) -> Externvals_ok v_S (externval__GLOBAL v_a) (externtype__GLOBAL (globaltype__ v_mut v_valtype)).

Inductive Memory_instance_ok: store -> meminst -> memtype -> Prop :=
	| Memory_instance_ok__ : forall (v_S : store) (v_mt : memtype) (v_b : (list byte)) (v_n : n) (v_m : m), (v_mt = (limits__ v_n v_m)) /\ ((List.length v_b) = v_n) /\ (Memtype_ok v_mt) -> Memory_instance_ok v_S {| meminst__TYPE := v_mt; meminst__BYTES := v_b |} v_mt.

Inductive Table_instance_ok: store -> tableinst -> tabletype -> Prop :=
	| Table_instance_ok__ : forall (v_S : store) (v_reserved__tt : tabletype) (v_fa : (list (option funcaddr))) (v_n : n) (v_m : m) (v_functype : (list (option functype))), ((List.length v_fa) = (List.length v_functype)) /\ List.Forall2 (fun v_fa v_functype => ((v_fa = None) <-> (v_functype = None))) (v_fa) (v_functype) /\ (v_reserved__tt = (limits__ v_n v_m)) /\ ((List.length v_fa) = v_n) /\ List.Forall2 (fun v_fa v_functype => List.Forall2 (fun v_fa v_functype => (Externvals_ok v_S (externval__FUNC v_fa) (externtype__FUNC v_functype))) (option_to_list v_fa) (option_to_list v_functype)) (v_fa) (v_functype) /\ (Tabletype_ok v_reserved__tt) -> Table_instance_ok v_S {| tableinst__TYPE := v_reserved__tt; tableinst__REFS := v_fa |} v_reserved__tt.

Inductive Global_instance_ok: store -> globalinst -> globaltype -> Prop :=
	| Global_instance_ok__ : forall (v_S : store) (v_gt : globaltype) (v_v : val) (v_mut : mut) (v_vt : valtype), (v_gt = (globaltype__ v_mut v_vt)) /\ (Globaltype_ok v_gt) /\ (Val_ok v_v v_vt) -> Global_instance_ok v_S {| globalinst__TYPE := v_gt; globalinst__VALUE := v_v |} v_gt.

Inductive Export_instance_ok: store -> exportinst -> Prop :=
	| Export_instance_ok__OK : forall (v_S : store) (v_name : name) (v_eval : externval) (v_ext : externtype), (Externvals_ok v_S v_eval v_ext) -> Export_instance_ok v_S {| exportinst__NAME := v_name; exportinst__VALUE := v_eval |}.

Inductive Module_instance_ok: store -> moduleinst -> context -> Prop :=
	| Module_instance_ok__ : forall (v_S : store) (v_functype : (list functype)) (v_funcaddr : (list funcaddr)) (v_globaladdr : (list globaladdr)) (v_tableaddr : (list tableaddr)) (v_memaddr : (list memaddr)) (v_exportinst : (list exportinst)) (v_functype' : (list functype)) (v_globaltype : (list globaltype)) (v_tabletype : (list tabletype)) (v_memtype : (list memtype)), ((List.length v_funcaddr) = (List.length v_functype')) /\ ((List.length v_tableaddr) = (List.length v_tabletype)) /\ ((List.length v_globaladdr) = (List.length v_globaltype)) /\ ((List.length v_memaddr) = (List.length v_memtype)) /\ List.Forall (fun v_functype => (Functype_ok v_functype)) (v_functype) /\ List.Forall2 (fun v_funcaddr v_functype' => (Externvals_ok v_S (externval__FUNC v_funcaddr) (externtype__FUNC v_functype'))) (v_funcaddr) (v_functype') /\ List.Forall2 (fun v_tableaddr v_tabletype => (Externvals_ok v_S (externval__TABLE v_tableaddr) (externtype__TABLE v_tabletype))) (v_tableaddr) (v_tabletype) /\ List.Forall2 (fun v_globaladdr v_globaltype => (Externvals_ok v_S (externval__GLOBAL v_globaladdr) (externtype__GLOBAL v_globaltype))) (v_globaladdr) (v_globaltype) /\ List.Forall2 (fun v_memaddr v_memtype => (Externvals_ok v_S (externval__MEM v_memaddr) (externtype__MEM v_memtype))) (v_memaddr) (v_memtype) /\ List.Forall (fun v_exportinst => (Export_instance_ok v_S v_exportinst)) (v_exportinst) -> Module_instance_ok v_S {| moduleinst__TYPES := v_functype; moduleinst__FUNCS := v_funcaddr; moduleinst__GLOBALS := v_globaladdr; moduleinst__TABLES := v_tableaddr; moduleinst__MEMS := v_memaddr; moduleinst__EXPORTS := v_exportinst |} {| context__TYPES := v_functype; context__FUNCS := v_functype'; context__GLOBALS := v_globaltype; context__TABLES := v_tabletype; context__MEMS := v_memtype; context__LOCALS := []; context__LABELS := []; context__RETURN := None |}.

Inductive Function_instance_ok: store -> funcinst -> functype -> Prop :=
	| Function_instance_ok__ : forall (v_S : store) (v_functype : functype) (v_moduleinst : moduleinst) (v_func : func) (v_C : context), (Functype_ok v_functype) /\ (Module_instance_ok v_S v_moduleinst v_C) /\ (Func_ok v_C v_func v_functype) -> Function_instance_ok v_S {| funcinst__TYPE := v_functype; funcinst__MODULE := v_moduleinst; funcinst__CODE := v_func |} v_functype.

Inductive Store_ok: store -> Prop :=
	| Store_ok__OK : forall (v_S : store) (v_funcinst : (list funcinst)) (v_globalinst : (list globalinst)) (v_tableinst : (list tableinst)) (v_meminst : (list meminst)) (v_functype : (list functype)) (v_globaltype : (list globaltype)) (v_tabletype : (list tabletype)) (v_memtype : (list memtype)), ((List.length v_funcinst) = (List.length v_functype)) /\ ((List.length v_globalinst) = (List.length v_globaltype)) /\ ((List.length v_tableinst) = (List.length v_tabletype)) /\ ((List.length v_meminst) = (List.length v_memtype)) /\ (v_S = {| store__FUNCS := v_funcinst; store__GLOBALS := v_globalinst; store__TABLES := v_tableinst; store__MEMS := v_meminst |}) /\ List.Forall2 (fun v_funcinst v_functype => (Function_instance_ok v_S v_funcinst v_functype)) (v_funcinst) (v_functype) /\ List.Forall2 (fun v_globalinst v_globaltype => (Global_instance_ok v_S v_globalinst v_globaltype)) (v_globalinst) (v_globaltype) /\ List.Forall2 (fun v_tableinst v_tabletype => (Table_instance_ok v_S v_tableinst v_tabletype)) (v_tableinst) (v_tabletype) /\ List.Forall2 (fun v_meminst v_memtype => (Memory_instance_ok v_S v_meminst v_memtype)) (v_meminst) (v_memtype) -> Store_ok v_S.

Inductive Frame_ok: store -> frame -> context -> Prop :=
	| Frame_ok__ : forall (v_S : store) (v_val : (list val)) (v_moduleinst : moduleinst) (v_C : context) (v_t : (list valtype)), ((List.length v_t) = (List.length v_val)) /\ (Module_instance_ok v_S v_moduleinst v_C) /\ List.Forall2 (fun v_t v_val => (Val_ok v_val v_t)) (v_t) (v_val) -> Frame_ok v_S {| frame__LOCALS := v_val; frame__MODULE := v_moduleinst |} ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := v_t; context__LABELS := []; context__RETURN := None |} ++ v_C).

Inductive Admin_instr_ok: store -> context -> admininstr -> functype -> Prop :=
	| Admin_instr_ok__instr : forall (v_S : store) (v_C : context) (v_instr : instr) (v_functype : functype), (Instr_ok v_C v_instr v_functype) -> Admin_instr_ok v_S v_C (v_instr : admininstr) v_functype
	| Admin_instr_ok__trap : forall (v_S : store) (v_C : context) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), Admin_instr_ok v_S v_C (admininstr__TRAP ) (functype__ v_t_1 v_t_2)
	| Admin_instr_ok__call_addr : forall (v_S : store) (v_C : context) (v_funcaddr : funcaddr) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), (Externvals_ok v_S (externval__FUNC v_funcaddr) (externtype__FUNC (functype__ v_t_1 v_t_2))) -> Admin_instr_ok v_S v_C (admininstr__CALL_ADDR v_funcaddr) (functype__ v_t_1 v_t_2)
	| Admin_instr_ok__label : forall (v_S : store) (v_C : context) (v_n : n) (v_instr : (list instr)) (v_admininstr : (list admininstr)) (v_t_2 : (option valtype)) (v_t_1 : (option valtype)), (Instrs_ok v_C v_instr (functype__ v_t_1 v_t_2)) /\ (Admin_instrs_ok v_S ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := [v_t_1]; context__RETURN := None |} ++ v_C) v_admininstr (functype__ [] v_t_2)) -> Admin_instr_ok v_S v_C (admininstr__LABEL_ v_n v_instr v_admininstr) (functype__ [] v_t_2)
	| Admin_instr_ok__frame : forall (v_S : store) (v_C : context) (v_n : n) (v_F : frame) (v_admininstr : (list admininstr)) (v_t : (option valtype)), (Thread_ok v_S v_t v_F v_admininstr v_t) -> Admin_instr_ok v_S v_C (admininstr__FRAME_ v_n v_F v_admininstr) (functype__ [] v_t)
	| Admin_instr_ok__weakening : forall (v_S : store) (v_C : context) (v_admininstr : admininstr) (v_t : (list valtype)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), (Admin_instr_ok v_S v_C v_admininstr (functype__ v_t_1 v_t_2)) -> Admin_instr_ok v_S v_C v_admininstr (functype__ (@app _ v_t v_t_1) (@app _ v_t v_t_2))

with

Admin_instrs_ok: store -> context -> (list admininstr) -> functype -> Prop :=
	| Admin_instrs_ok__empty : forall (v_S : store) (v_C : context), Admin_instrs_ok v_S v_C [] (functype__ [] [])
	| Admin_instrs_ok__seq : forall (v_S : store) (v_C : context) (v_admininstr_1 : (list admininstr)) (v_admininstr_2 : admininstr) (v_t_1 : (list valtype)) (v_t_3 : (list valtype)) (v_t_2 : (list valtype)), (Admin_instrs_ok v_S v_C v_admininstr_1 (functype__ v_t_1 v_t_2)) /\ (Admin_instr_ok v_S v_C v_admininstr_2 (functype__ v_t_2 v_t_3)) -> Admin_instrs_ok v_S v_C (@app _ v_admininstr_1 [v_admininstr_2]) (functype__ v_t_1 v_t_3)
	| Admin_instrs_ok__frame : forall (v_S : store) (v_C : context) (v_admininstr : (list admininstr)) (v_t : (list valtype)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), (Admin_instrs_ok v_S v_C v_admininstr (functype__ v_t_1 v_t_2)) -> Admin_instrs_ok v_S v_C v_admininstr (functype__ (@app _ v_t v_t_1) (@app _ v_t v_t_2))
	| Admin_instrs_ok__instrs : forall (v_S : store) (v_C : context) (v_instr : (list instr)) (v_functype : functype), (Instrs_ok v_C v_instr v_functype) -> Admin_instrs_ok v_S v_C (list__instr__admininstr v_instr) v_functype

with

Thread_ok: store -> resulttype -> frame -> (list admininstr) -> resulttype -> Prop :=
	| Thread_ok__ : forall (v_S : store) (v_rt : (option valtype)) (v_F : frame) (v_admininstr : (list admininstr)) (v_t : (option valtype)) (v_C : context), (Frame_ok v_S v_F v_C) /\ (Admin_instrs_ok v_S ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := []; context__RETURN := (Some v_rt) |} ++ v_C) v_admininstr (functype__ [] v_t)) -> Thread_ok v_S v_rt v_F v_admininstr v_t.

Inductive Config_ok: config -> resulttype -> Prop :=
	| Config_ok__ : forall (v_S : store) (v_F : frame) (v_admininstr : (list admininstr)) (v_t : (option valtype)), (Store_ok v_S) /\ (Thread_ok v_S None v_F v_admininstr v_t) -> Config_ok (config__ (state__ v_S v_F) v_admininstr) v_t.

Inductive Func_extension: funcinst -> funcinst -> Prop :=
	| Func_extension__ : forall (v_funcinst : funcinst), Func_extension v_funcinst v_funcinst.

Inductive Table_extension: tableinst -> tableinst -> Prop :=
	| Table_extension__ : forall (v_n1 : u32) (v_m : m) (v_fa_1 : (list (option funcaddr))) (v_n2 : u32) (v_fa_2 : (list (option funcaddr))), (v_n1 <= v_n2) -> Table_extension {| tableinst__TYPE := (limits__ v_n1 v_m); tableinst__REFS := v_fa_1 |} {| tableinst__TYPE := (limits__ v_n2 v_m); tableinst__REFS := v_fa_2 |}.

Inductive Mem_extension: meminst -> meminst -> Prop :=
	| Mem_extension__ : forall (v_n1 : u32) (v_m : m) (v_b_1 : (list byte)) (v_n2 : u32) (v_b_2 : (list byte)), (v_n1 <= v_n2) -> Mem_extension {| meminst__TYPE := (limits__ v_n1 v_m); meminst__BYTES := v_b_1 |} {| meminst__TYPE := (limits__ v_n2 v_m); meminst__BYTES := v_b_2 |}.

Inductive Global_extension: globalinst -> globalinst -> Prop :=
	| Global_extension__ : forall (v_mut : mut) (v_t2 : valtype) (v_t : valtype) (v_c1 : val_) (v_c2 : val_), ((v_mut = (mut__MUT (Some tt))) \/ ((v_c1 : val_) = (v_c2 : val_))) -> Global_extension {| globalinst__TYPE := (globaltype__ v_mut v_t2); globalinst__VALUE := (val__CONST v_t (v_c1 : val_)) |} {| globalinst__TYPE := (globaltype__ v_mut v_t2); globalinst__VALUE := (val__CONST v_t (v_c2 : val_)) |}.

Inductive Store_extension: store -> store -> Prop :=
	| Store_extension__ : forall (v_store_1 : store) (v_store_2 : store) (v_funcinst_1 : (list funcinst)) (v_tableinst_1 : (list tableinst)) (v_meminst_1 : (list meminst)) (v_globalinst_1 : (list globalinst)) (v_funcinst_1' : (list funcinst)) (v_funcinst_2 : (list funcinst)) (v_tableinst_1' : (list tableinst)) (v_tableinst_2 : (list tableinst)) (v_meminst_1' : (list meminst)) (v_meminst_2 : (list meminst)) (v_globalinst_1' : (list globalinst)) (v_globalinst_2 : (list globalinst)), ((List.length v_funcinst_1) = (List.length v_funcinst_1')) /\ ((List.length v_tableinst_1) = (List.length v_tableinst_1')) /\ ((List.length v_meminst_1) = (List.length v_meminst_1')) /\ ((List.length v_globalinst_1) = (List.length v_globalinst_1')) /\ ((store__FUNCS v_store_1) = v_funcinst_1) /\ ((store__TABLES v_store_1) = v_tableinst_1) /\ ((store__MEMS v_store_1) = v_meminst_1) /\ ((store__GLOBALS v_store_1) = v_globalinst_1) /\ ((store__FUNCS v_store_2) = (@app _ v_funcinst_1' v_funcinst_2)) /\ ((store__TABLES v_store_2) = (@app _ v_tableinst_1' v_tableinst_2)) /\ ((store__MEMS v_store_2) = (@app _ v_meminst_1' v_meminst_2)) /\ ((store__GLOBALS v_store_2) = (@app _ v_globalinst_1' v_globalinst_2)) /\ List.Forall2 (fun v_funcinst_1 v_funcinst_1' => (Func_extension v_funcinst_1 v_funcinst_1')) (v_funcinst_1) (v_funcinst_1') /\ List.Forall2 (fun v_tableinst_1 v_tableinst_1' => (Table_extension v_tableinst_1 v_tableinst_1')) (v_tableinst_1) (v_tableinst_1') /\ List.Forall2 (fun v_meminst_1 v_meminst_1' => (Mem_extension v_meminst_1 v_meminst_1')) (v_meminst_1) (v_meminst_1') /\ List.Forall2 (fun v_globalinst_1 v_globalinst_1' => (Global_extension v_globalinst_1 v_globalinst_1')) (v_globalinst_1) (v_globalinst_1') -> Store_extension v_store_1 v_store_2.
   
(* Proof Start *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq.
(* Utility lemmas *)

Ltac decomp :=
repeat lazymatch goal with
	| H: _ /\ _ |- _ => 
		destruct H
		
end.


(** Similar to [set (name := term)], but introduce an equality instead of a local definition. **)
Ltac set_eq name term :=
  set (name := term);
  have: name = term; [
      reflexivity
    | clearbody name ].

Ltac is_variable x cont1 cont2 :=
	match tt with
	| _ =>
		(* Sorry for the hack.
		Only a variable be cleared.
		Local definitions are not considered variables by this tactic. *)
		(exfalso; clear - x; assert_fails clearbody x; fail 1) || cont2
	| _ => cont1
	end.

(** The first step is to name each parameter of the predicate. **)
Ltac gen_ind_pre H :=
  let rec aux v :=
    lazymatch v with
    | ?f ?x =>
      let only_do_if_ok_direct t cont :=
        lazymatch t with
        | Type => idtac

        | _ => cont tt
        end in
      let t := type of x in
      only_do_if_ok_direct t ltac:(fun _ =>
        let t :=
          match t with
          | _ _ => t
          | ?t => eval unfold t in t
          | _ => t
          end in
        only_do_if_ok_direct t ltac:(fun _ =>
          let x' :=
            let rec get_name x :=
              match x with
              | ?f _ => get_name f
              | _ => fresh x
              | _ => fresh "x"
              end in
            get_name x in
          move: H;
          set_eq x' x;
          let E := fresh "E" x' in
          move=> E H));
      aux f
    | _ => idtac
    end in
  let Ht := type of H in
  aux Ht.

(** Then, each of the associated parameters can be generalised. **)
Ltac gen_ind_gen H :=
  let rec try_generalize t :=
    lazymatch t with
    | ?f ?x => try_generalize f; try_generalize x
    | ?x => is_variable x ltac:(generalize dependent x) ltac:(idtac)
    | _ => fail "unable to generalize" t
    end in
  let rec aux v :=
    lazymatch v with
    | ?f ?x => 
    lazymatch goal with
      | _ : x = ?y |- _ => try_generalize y
      | _ => fail "unexpected term" v
      end;
      aux f
    | _ => idtac
    end in
  let Ht := type of H in
  aux Ht.

(** After the induction, one can inverse them again (and do some cleaning). **)
Ltac gen_ind_post :=
  repeat lazymatch goal with
  | |- _ = _ -> _ => inversion 1
  | |- _ -> _ => intro
  end;
  repeat lazymatch goal with
  | H: True |- _ => clear H
  | H: ?x = ?x |- _ => clear H
  end.

(** Wrapping every part of the generalised induction together. **)
Ltac gen_ind H :=
  gen_ind_pre H;
  gen_ind_gen H;
  induction H;
  gen_ind_post.

(** Similar to [gen_ind H; subst], but cleaning just a little bit more. **)
Ltac gen_ind_subst H :=
  gen_ind H;
  subst;
  gen_ind_post.


Ltac admin_instrs_ok_dependent_ind H :=
let Ht := type of H in
lazymatch Ht with
| Admin_instrs_ok ?s ?C ?es ?tf =>
	let s2 := fresh "s2" in
	let C2 := fresh "C2" in
	let es2 := fresh "es2" in
	let tf2 := fresh "tf2" in
	remember s as s2 eqn:Hrems;
	remember C as C2 eqn:HremC;
	remember es as es2 eqn:Hremes;
	remember tf as tf2 eqn:Hremtf;
	generalize dependent Hrems;
	generalize dependent HremC;
	generalize dependent Hremtf;
	generalize dependent s; generalize dependent C;
	generalize dependent tf;
	induction H
end.

Definition typeof (v_val : val): valtype :=
	match v_val with
		| val__CONST t _ => t
	end.

Lemma list_update_func_split : forall {A : Type} (x x' : list A) (idx : nat) (f : A -> A),
	x' = list_update_func x idx f ->
	(exists y, In (f y) x') \/ x = x'.
Proof. 
	move => A x x' idx f H.
	generalize dependent idx.
	generalize dependent x'.
	induction x.
	- right. rewrite H => //.
	- move => x' idx H. destruct idx. 
		- left. exists a. rewrite H. apply in_eq.
		- destruct x'.
			- discriminate.
			- injection H as H2. apply IHx in H.
				destruct H.
				- destruct H. left. exists x0. apply List.in_cons => //.
				- right. by f_equal.
Qed.

Lemma length_app_lt: forall {A : Type} (l l' l1' l2': list A),
	length l = length l1' ->
	l' = l1' ++ l2' -> 
	(length l <= length l')%coq_nat.
Proof.
	move => A l l' l1' l2' HLength HApp.

	apply f_equal with (f := fun t => length t) in HApp.
	rewrite List.app_length in HApp.
	rewrite <- HLength in HApp.
	symmetry in HApp.
	generalize dependent l2'.
	generalize dependent l'.
	clear HLength.
	induction l; move => l' l2' HApp.
	- simpl. apply Nat.le_0_l.
	- destruct l' => //. simpl in HApp. 
		injection HApp as H.
		apply IHl in H.
		simpl. apply le_n_S. apply H.
Qed.  

Lemma length_same_split_zero: forall {A : Type} (l l2' : list A),
	length l = length l + length l2' ->
	length l2' = 0.
Proof.
	move => A l l2' H.
	generalize dependent l2'.
	induction l; move => l2' H.
	- simpl in H. symmetry in H. apply H.
	- simpl in H. injection H as ?. apply IHl. apply H.
Qed.
	

Lemma length_app_both_nil: forall {A : Type} (l l' l1' l2': list A),
	length l = length l' ->
	length l = length l1' -> 
	l' = l1' ++ l2' -> 
	l2' = [].
Proof.
	move => A l l' l1' l2' HLength HLength2 HApp.

	apply f_equal with (f := fun t => List.length t) in HApp.
	rewrite List.app_length in HApp.
	rewrite <- HLength in HApp.
	rewrite <- HLength2 in HApp.
	apply length_same_split_zero in HApp.
	rewrite <- List.length_zero_iff_nil => //=.
Qed.  

Lemma Forall2_nth {A : Type} {B : Type} (l : list A) (l' : list B) (R : A -> B -> Prop) :
      Forall2 R l l' -> length l = length l' /\ (forall i d d', (i < length l)%coq_nat -> R (List.nth i l d) (List.nth i l' d')).
Proof.
	move => H.
	split. apply (Forall2_length) in H. apply H.
	move => i d d' H'.
	generalize dependent i. induction H; move => i HLength. 
		+ apply Nat.nlt_0_r in HLength. exfalso. apply HLength.
		+ destruct i. 
			+ simpl. apply H.
			+ simpl in HLength. apply Nat.succ_lt_mono in HLength. apply IHForall2. apply HLength.
Qed.

Lemma Forall2_nth2 {A : Type} {B : Type} (l : list A) (l' : list B) (R : A -> B -> Prop) :
      Forall2 R l l' -> length l = length l' /\ (forall i d d', (i < length l')%coq_nat -> R (List.nth i l d) (List.nth i l' d')).
Proof.
	move => H.
	split. apply (Forall2_length) in H. apply H.
	move => i d d' H'.
	generalize dependent i. induction H; move => i HLength. 
		+ apply Nat.nlt_0_r in HLength. exfalso. apply HLength.
		+ destruct i. 
			+ simpl. apply H.
			+ simpl in HLength. apply Nat.succ_lt_mono in HLength. apply IHForall2. apply HLength.
Qed.

Lemma Forall2_lookup {A : Type} {X : Inhabited A} {B : Type} {Y : Inhabited B} (l : list A) (l' : list B) (R : A -> B -> Prop) :
      Forall2 R l l' -> length l = length l' /\ (forall i, (i < length l)%coq_nat -> R (lookup_total l i) (lookup_total l' i)).
Proof.
	move => H.
	split. apply (Forall2_length) in H. apply H.
	move => i H'.
	generalize dependent i. induction H; move => i HLength. 
		+ apply Nat.nlt_0_r in HLength. exfalso. apply HLength.
		+ destruct i. 
			+ simpl. apply H.
			+ simpl in HLength. apply Nat.succ_lt_mono in HLength. apply IHForall2. apply HLength.
Qed.

Lemma Forall2_lookup2 {A : Type} {X : Inhabited A} {B : Type} {Y : Inhabited B} (l : list A) (l' : list B) (R : A -> B -> Prop) :
      Forall2 R l l' -> length l = length l' /\ (forall i, (i < length l')%coq_nat -> R (lookup_total l i) (lookup_total l' i)).
Proof.
	move => H.
	split. apply (Forall2_length) in H. apply H.
	move => i H'.
	generalize dependent i. induction H; move => i HLength. 
		+ apply Nat.nlt_0_r in HLength. exfalso. apply HLength.
		+ destruct i. 
			+ simpl. apply H.
			+ simpl in HLength. apply Nat.succ_lt_mono in HLength. apply IHForall2. apply HLength.
Qed.

Lemma Forall2_Val_ok_is_same_as_map: forall v_t1 v_local_vals,
	Forall2 (fun v s => Val_ok s v) v_t1 v_local_vals <->
	List.map typeof v_local_vals = v_t1.
Proof.
	split.
	- move => H.
		generalize dependent v_local_vals.
		induction v_t1; move => v_local_vals H; destruct v_local_vals => //=; inversion H.
		subst. f_equal. 
		- inversion H3 => //=.
		- by apply IHv_t1.
	- move => H.
		generalize dependent v_local_vals.
		induction v_t1; move => v_local_vals H; destruct v_local_vals => //=.
		simpl in H. inversion H.
		apply Forall2_cons. 
		- induction v. apply Val_ok__.
		- rewrite H2. by apply IHv_t1.
Qed. 

Fixpoint In2 {A B : Type} (x : A) (y : B) (l : list A) (l' : list B) : Prop :=
    match l, l' with
      | [], [] => False
	  | [], b :: ms => False
	  | a :: ns, [] => False
      | a :: ns, b :: ms => (a = x /\ b = y) \/ In2 x y ns ms
    end.

Lemma In2_split: forall {A B : Type} (x : A) (y : B) (l : list A) (l' : list B),
	In2 x y l l' -> In x l /\ In y l'.
Proof.
	move => A B x y l l' HIn.
	generalize dependent x.
	generalize dependent y.
	generalize dependent l'.
	induction l; move => l0' y0 x0 HIn => //=.
	- destruct l0' => //=.
	- destruct l0' => //=.
		simpl in HIn.
		destruct HIn. 
		- destruct H. split; by left.
		- apply IHl in H. destruct H. split; by right.
Qed.	

Lemma Forall2_forall2 {A B : Type} (l : list A) (l' : list B) (R : A -> B -> Prop):
	Forall2 R l l' <-> length l = length l' /\ (forall x y, In2 x y l l' -> R x y).
Proof.
	split.
	- (* -> *)
		move => H.
		split. eapply Forall2_length; eauto.	
		move => x y HIn.
		generalize dependent x.
		generalize dependent y.
		induction H => //=; move => y0 x0 HIn; subst; simpl in *.
		destruct HIn. 
		- destruct H1. subst => //=.
		- by eapply IHForall2.
	- (* <- *)
		move => H.
		destruct H.
		generalize dependent l'.
		induction l => //=; move => l' H H1.
		- destruct l' => //=.
		- destruct l' => //=.
			apply Forall2_cons_iff. split.
			- apply H1. left; split => //=.
			- apply IHl. simpl in H. injection H as ?. apply H.
			- move => x y HIn. apply H1. right. apply HIn.
Qed.

Lemma Forall2_forall2weak {A B : Type} (l : list A) (l' : list B) (R : A -> B -> Prop):
	Forall2 R l l' -> (forall x , In x l -> exists y, R x y).
Proof.
	
	move => H x.
	generalize dependent x.
	induction H => //=; move => x0 HIn; subst; simpl in *.
	destruct HIn. 
	- subst. exists y. subst => //=.
	- by apply IHForall2.
Qed.

Lemma Forall2_forall2weak2 {A B : Type} (l : list A) (l' : list B) (R : A -> B -> Prop):
	Forall2 R l l' -> (forall y, In y l' -> exists x, R x y).
Proof.
	move => H y.
	generalize dependent y.
	induction H => //=; move => y0 HIn; subst; simpl in *.
	destruct HIn. 
	- subst. exists x. subst => //=.
	- by apply IHForall2.
Qed.

Lemma Forall2_forall2weak3 {A B : Type} (l : list A) (l' : list B) (R : A -> B -> Prop):
	(forall x y, In x l -> R x y) /\ length l = length l' -> Forall2 R l l'.
Proof.
	move => H.
	destruct H.
	generalize dependent l'.
	induction l; move => l0' HLength; subst; simpl in * => //=.
	- destruct l0' => //=.
	- destruct l0' => //=.
		apply Forall2_cons_iff. split.
		- apply H. left => //=.
		- apply IHl. move => x y HIn. apply H. by right.
		- simpl in HLength. injection HLength as ?. apply H0.
Qed.

Lemma Forall2_forall2weak4 {A B : Type} (l : list A) (l' : list B) (R : A -> B -> Prop):
	(forall x y, In y l' -> R x y) /\ length l = length l' -> Forall2 R l l'.
Proof.
	move => H.
	destruct H.
	generalize dependent l.
	induction l'; move => l0 HLength; subst; simpl in * => //=.
	- destruct l0 => //=.
	- destruct l0 => //=.
		apply Forall2_cons_iff. split.
		- apply H. left => //=.
		- apply IHl'. move => x y HIn. apply H. by right.
		- simpl in HLength. injection HLength as ?. apply H0.
Qed.




Lemma list_update_length: forall {A : Type} (l : list A) (i : nat) (x : A),
	length (list_update l i x) = length l.
Proof.
	move => A l i x.
	generalize dependent l.
	generalize dependent x.
	induction i; move => x l.
	- destruct l => //=.
	- destruct l => //=.
		f_equal. apply IHi.
Qed.


Lemma list_update_length_func: forall {A : Type} (l : list A) (f : A -> A) (i : nat),
	length (list_update_func l i f) = length l.
Proof.
	move => A l f i.
	generalize dependent l.
	generalize dependent f.
	induction i; move => f l.
	- destruct l => //=.
	- destruct l => //=.
		f_equal. apply IHi.
Qed.

Lemma split_append_last : forall {A : Type} (z : list A) (y : list A) (i : A) (j : A),
	@app _ z [i] = @app _ y [j] ->
	z = y /\ i = j.
Proof.
	move => A z y i j H.
	apply app_inj_tail.
	apply H.
Qed.

Lemma split_cons : forall {A : Type} (j : A) (k : A),
	[j; k] = @app _ [j] [k].
Proof.
	move => A j k.
	done.
Qed.

Lemma split_append_1 : forall {A : Type} (z : list A) (i : A) (j : A),
	@app _ z [i] = [j] ->
	z = [] /\ i = j.
Proof.
	move => A z i j H.
	apply app_eq_unit in H.
	destruct H as [[H1 H2] | [H1 H2]].
		- split. apply H1. injection H2 as H3. apply H3.
		- discriminate.
Qed.

Lemma split_append_2 : forall {A : Type} (z : list A) (i : A) (j : A) (k : A),
	@app _ z [i] = [j; k] ->
	z = [j] /\ i = k.
Proof.
	move => A z i j k H.
	apply split_append_last.
	apply H.
Qed.

Lemma split_append_left_1 : forall {A : Type} (z : list A) (i : A) (j : A),
	@app _ [i] z = [j] ->
	z = [] /\ i = j.
Proof.
	move => A z i j H.
	apply app_eq_unit in H.
	destruct H as [[H1 H2] | [H1 H2]].
		- discriminate. 
		- split. apply H2. injection H1 as H3. apply H3.
Qed.


Lemma empty_append {A : Type}: forall (i : list A) (j : list A),
	[] = @app _ i j ->
	i = [] /\ j = [].
Proof.
	move => i j H.
	simpl.
	induction i.
		- rewrite -> app_nil_l in H. split. reflexivity. symmetry in H. apply H.
		- discriminate.
Qed. 

Lemma lookup_app: forall {A : Type} {B : Inhabited A} (l l' : list A) (n : nat),
	(n < List.length l)%coq_nat ->
	lookup_total l n = lookup_total (l ++ l') n.
Proof.
	move => A B l l' n.
	move: l l'.
	induction n; move => l l' H.
	- destruct l => //=. simpl in H. apply Nat.nlt_0_r in H. exfalso. apply H.
	- destruct l => //=. 
		- simpl in H. apply Nat.nlt_0_r in H. exfalso. apply H.
		- unfold lookup_total. simpl.
		apply IHn. apply Nat.succ_lt_mono. apply H.
Qed.

Lemma instrs_empty: forall C t1 t2,
	Instrs_ok C [] (functype__ t1 t2) ->
	t1 = t2.
Proof.
	move => C t t2 H. gen_ind_subst H => //.
	- (* Seq *) symmetry in Enil. apply app_cons_not_nil in Enil. exfalso. apply Enil. 
		- (* Frame *) f_equal. by eapply IHInstrs_ok.
Qed. 


Lemma admin_empty: forall v_S C t1 t2,
	Admin_instrs_ok v_S C [] (functype__ t1 t2) ->
	t1 = t2.
Proof.
	move => v_S C t t2 H. gen_ind_subst H => //.
		- (* Seq *) symmetry in Enil. apply app_cons_not_nil in Enil. exfalso. apply Enil. 
		- (* Frame *) f_equal. by eapply IHAdmin_instrs_ok.
		- (* Instrs *) apply (instrs_empty C). apply map_eq_nil in Enil. subst. apply H.
Qed. 




Lemma val_is_same_as_admin_const: forall v_S v_C (v : val) ts,
	Admin_instr_ok v_S v_C (v : admininstr) ts ->
	exists v_valtype v_val_, Admin_instr_ok v_S v_C (admininstr__CONST v_valtype v_val_) ts.
Proof. 
	move => v_S v_C val ts HType.
	induction val.
	exists v_valtype, v_val_. done.
Qed.

Lemma admin_weakening_empty_both: forall v_S v_C v_ais ts,
    Admin_instrs_ok v_S v_C v_ais (functype__ [::] [::]) ->
    Admin_instrs_ok v_S v_C v_ais (functype__ ts ts).
Proof.
  move => v_S v_C v_ais ts HType.
  assert (Admin_instrs_ok v_S v_C v_ais (functype__ (ts ++ [::]) (ts ++ [::]))); first by apply Admin_instrs_ok__frame.
  by rewrite cats0 in H.
Qed.

Lemma instrs_weakening_empty_both: forall v_C v_ais ts,
    Instrs_ok v_C v_ais (functype__ [::] [::]) ->
    Instrs_ok v_C v_ais (functype__ ts ts).
Proof.
  move => v_C v_ais ts HType.
  assert (Instrs_ok v_C v_ais (functype__ (ts ++ [::]) (ts ++ [::]))); first by apply Instrs_ok__frame.
  by rewrite cats0 in H.
Qed.

Lemma admin_instrs_weakening_empty_1: forall v_S v_C instrs ts t2s,
    Admin_instrs_ok v_S v_C instrs (functype__ [::] t2s) ->
    Admin_instrs_ok v_S v_C instrs (functype__ ts (ts ++ t2s)).
Proof.
  move => v_S v_C instrs ts t2s HType.
  assert (Admin_instrs_ok v_S v_C instrs (functype__ (ts ++ [::]) (ts ++ t2s))); first by apply Admin_instrs_ok__frame.
  by rewrite cats0 in H.
Qed.

Lemma instrs_weakening_empty_1: forall v_C instrs ts t2s,
    Instrs_ok v_C instrs (functype__ [::] t2s) ->
    Instrs_ok v_C instrs (functype__ ts (ts ++ t2s)).
Proof.
  move => v_C instrs ts t2s HType.
  assert (Instrs_ok v_C instrs (functype__ (ts ++ [::]) (ts ++ t2s))); first by apply Instrs_ok__frame.
  by rewrite cats0 in H.
Qed.

Lemma admin_instr_weakening_empty_1: forall v_S v_C instr ts t2s,
    Admin_instr_ok v_S v_C instr (functype__ [::] t2s) ->
    Admin_instr_ok v_S v_C instr (functype__ ts (ts ++ t2s)).
Proof.
  move => v_S v_C instr ts t2s HType.
  assert (Admin_instr_ok v_S v_C instr (functype__ (ts ++ [::]) (ts ++ t2s))); first by apply Admin_instr_ok__weakening.
  by rewrite cats0 in H.
Qed.

Lemma admin_instr_weakening_empty_2: forall v_S v_C instr ts t1s,
    Admin_instr_ok v_S v_C instr (functype__ t1s []) ->
    Admin_instr_ok v_S v_C instr (functype__ (ts ++ t1s) (ts)).
Proof.
  move => v_S v_C instr ts t1s HType.
  assert (Admin_instr_ok v_S v_C instr (functype__ (ts ++ t1s) (ts ++ []))); first by apply Admin_instr_ok__weakening.
  by rewrite cats0 in H.
Qed.

Lemma composition_typing_single: forall v_C v_ais v_ai t1s t2s,
   	Instrs_ok v_C (@app _ v_ais [v_ai]) (functype__ t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = @app _ ts t1s' /\
                             t2s = @app _ ts t2s' /\
                             Instrs_ok v_C v_ais (functype__ t1s' t3s) /\
                             Instr_ok v_C v_ai (functype__ t3s t2s').
Proof.
	move => v_C v_ais v_ai t1s t2s HType. 
	gen_ind_subst HType => //.
		+ (* Empty *) apply empty_append in H1; destruct H1. discriminate.
		+ (* Seq *) apply split_append_last in H2; destruct H2; subst.
			by exists [], t1s, t2s, v_t_2.
		+ (* Frame *) edestruct IHHType; eauto.
			destruct H as [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]. subst.
			exists (@app _ v_t x), t1s', t2s', t3s'.
			by repeat split => //=; rewrite <- app_assoc; reflexivity.
Qed.

Lemma admin_composition_typing_single: forall v_S v_C v_ais v_ai t1s t2s,
    Admin_instrs_ok v_S v_C (@app _ v_ais [v_ai]) (functype__ t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = @app _ ts t1s' /\
                             t2s = @app _ ts t2s' /\
                             Admin_instrs_ok v_S v_C v_ais (functype__ t1s' t3s) /\
                             Admin_instr_ok v_S v_C v_ai (functype__ t3s t2s').
Proof.
	move => v_S v_C v_ais v_ai t1s t2s HType.
	gen_ind_subst HType.
		+ (* Empty *) apply empty_append in H2; destruct H2. discriminate.
		+ (* Seq *) apply split_append_last in H3; destruct H3; subst.
			by exists [], t1s, t2s, v_t_2.
		+ (* Frame *) edestruct IHHType; eauto.
			destruct H as [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]. subst.
			exists (@app _ v_t x), t1s', t2s', t3s'.
			by repeat split => //=; rewrite <- app_assoc; reflexivity.
		+ (* Instrs *) apply map_eq_app in H3; destruct H3 as [l1 [l2 [H4 [H5 H6]]]]. 
			apply map_eq_cons in H6; destruct H6 as [a [t1 [H7 [H8 H9]]]].
			apply map_eq_nil in H9.
			subst. apply composition_typing_single in H; destruct H as [ts [t1s' [t2s' [t3s [H1 [H2 [H3 H4]]]]]]].
			exists ts, t1s', t2s', t3s. repeat split => //.
			eapply Admin_instrs_ok__instrs; eauto.
			eapply Admin_instr_ok__instr; eauto.
Qed.

Lemma admin_composition_typing: forall v_S v_C v_ais1 v_ais2 t1s t2s,
	Admin_instrs_ok v_S v_C (v_ais1 ++ v_ais2) (functype__ t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             Admin_instrs_ok v_S v_C v_ais1 (functype__ t1s' t3s) /\
                             Admin_instrs_ok v_S v_C v_ais2 (functype__ t3s t2s').
Proof.
	move => v_S v_C v_ais1 v_ais2.
	remember (rev v_ais2) as v_ais2'.
	assert (v_ais2 = rev v_ais2'); first by (rewrite Heqv_ais2'; symmetry; apply revK).
	generalize dependent v_ais1.
	clear Heqv_ais2'. subst.
	induction v_ais2' => //=; move => v_ais1 t1s t2s HType.
	- unfold rev in HType; simpl in HType. subst.
	  rewrite cats0 in HType.
	  exists [::], t1s, t2s, t2s.
	  repeat split => //=.
	  apply admin_weakening_empty_both.
	  by apply Admin_instrs_ok__empty.
	- rewrite rev_cons in HType.
	  rewrite -cats1 in HType. subst.
	  rewrite catA in HType.
	  apply admin_composition_typing_single in HType.
	  destruct HType as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]]. subst.
	  apply IHv_ais2' in H3.
	  destruct H3 as [ts2 [t1s2 [t2s2 [t3s2 [H5 [H6 [H7 H8]]]]]]]. subst.
	  exists ts', (ts2 ++ t1s2), t2s', (ts2 ++ t3s2).
	  repeat split => //.
	  + by apply Admin_instrs_ok__frame.
	  + rewrite rev_cons. rewrite -cats1.
		eapply Admin_instrs_ok__seq; split; eauto.
		by apply Admin_instrs_ok__frame.
Qed.

Lemma app_left_single_nil: forall {A : Type} (x : A), [x] = @app _ [] [x].
Proof. done. Qed.

Lemma app_right_nil: forall {A : Type} (x : list A), x = @app _ x [].
Proof. move => A x. rewrite app_nil_r. done. Qed.

Lemma app_left_nil: forall {A : Type} (x : list A), x = @app _ [] x.
Proof. move => A x. rewrite app_nil_l. done. Qed.

Ltac apply_instrs_composition_typing_single H := 
	let ts1 := fresh "ts1_comp" in
    let ts2 := fresh "ts2_comp" in
    let ts3 := fresh "ts3_comp" in
    let ts4 := fresh "ts4_comp" in
    let H1 := fresh "H1_comp" in
    let H2 := fresh "H2_comp" in
    let H3 := fresh "H3_comp" in
    let H4 := fresh "H4_comp" in
	rewrite -> app_left_single_nil in H;
    apply composition_typing_single in H; destruct H as [ts1 [ts2 [ts3 [ts4 [H1 [H2 [H3 H4]]]]]]];
	try apply instrs_empty in H3.

Ltac apply_composition_typing_single H := 
	let ts1 := fresh "ts1_comp" in
    let ts2 := fresh "ts2_comp" in
    let ts3 := fresh "ts3_comp" in
    let ts4 := fresh "ts4_comp" in
    let H1 := fresh "H1_comp" in
    let H2 := fresh "H2_comp" in
    let H3 := fresh "H3_comp" in
    let H4 := fresh "H4_comp" in
	rewrite -> app_left_single_nil in H;
    apply admin_composition_typing_single in H; destruct H as [ts1 [ts2 [ts3 [ts4 [H1 [H2 [H3 H4]]]]]]];
	try apply admin_empty in H3.
	
Ltac apply_composition_typing_and_single H :=
	let ts1 := fresh "ts1_comp" in
    let ts2 := fresh "ts2_comp" in
    let ts3 := fresh "ts3_comp" in
    let ts4 := fresh "ts4_comp" in
    let H1 := fresh "H1_comp" in
    let H2 := fresh "H2_comp" in
    let H3 := fresh "H3_comp" in
    let H4 := fresh "H4_comp" in
	try rewrite -cat1s in H; subst;
    apply admin_composition_typing in H; destruct H as [ts1 [ts2 [ts3 [ts4 [H1 [H2 [H3 H4]]]]]]];
	apply_composition_typing_single H3.
	
Ltac apply_composition_typing H :=
	let ts1 := fresh "ts1_comp" in
	let ts2 := fresh "ts2_comp" in
	let ts3 := fresh "ts3_comp" in
	let ts4 := fresh "ts4_comp" in
	let H1 := fresh "H1_comp" in
	let H2 := fresh "H2_comp" in
	let H3 := fresh "H3_comp" in
	let H4 := fresh "H4_comp" in
	try rewrite -cat1s in H; subst;
	apply admin_composition_typing in H; destruct H as [ts1 [ts2 [ts3 [ts4 [H1 [H2 [H3 H4]]]]]]].


Lemma admin_instrs_ok_eq: forall v_S v_C v_ai tf,
	Admin_instr_ok v_S v_C v_ai tf <-> 
	Admin_instrs_ok v_S v_C [v_ai] tf.
Proof.
	split; move => H; destruct tf as [ts1 ts2].
	- (* -> *)
		assert (Admin_instrs_ok v_S v_C [] (functype__ [] [])). { apply Admin_instrs_ok__empty. }
		apply admin_weakening_empty_both with (ts := ts1) in H0.
		apply (Admin_instrs_ok__seq v_S v_C [] v_ai ts1 ts2 ts1); eauto.
	- (* <- *) 
		apply_composition_typing_single H; subst.
		apply Admin_instr_ok__weakening. apply H4_comp.
Qed.

Lemma admin_composition': forall v_S v_C v_ais1 v_ais2 t1s t2s t3s,
	Admin_instrs_ok v_S v_C v_ais1 (functype__ t1s t2s) ->
	Admin_instrs_ok v_S v_C v_ais2 (functype__ t2s t3s) ->
	Admin_instrs_ok v_S v_C (v_ais1 ++ v_ais2) (functype__ t1s t3s).
Proof.
	move => v_S v_C v_ais1 v_ais2.
	move: v_ais1.
	induction v_ais2 using List.rev_ind; move => v_ais1 t1s t2s t3s HType1 HType2.
		- apply admin_empty in HType2; by rewrite cats0; subst.
		- apply_composition_typing_single HType2.
	subst.
	rewrite catA. eapply Admin_instrs_ok__seq; split.
	eapply IHv_ais2; eauto.
	apply Admin_instrs_ok__frame with (v_t := ts1_comp) in H3_comp.
	apply H3_comp.
	apply Admin_instr_ok__weakening; eauto.
Qed.

Lemma AI_const_typing: forall v_S v_C v_t v_v t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__CONST v_t v_v) (functype__ t1s t2s) ->
    t2s = @app _ t1s [v_t].
Proof.
  	move => v_S v_C v_t v_val t1s t2s HType.
	gen_ind_subst HType.
		- (* Const *) inversion H; subst; try discriminate. injection H3 as H1. rewrite -> cat0s. f_equal. apply H1.
		- (* Weakening *) rewrite <- app_assoc. f_equal. by eapply IHHType.
Qed.

Ltac apply_const_typing_to_val H :=
	let v_valtype := fresh "v_valtype" in
    let v_val_ := fresh "v_val_" in
	apply val_is_same_as_admin_const in H; destruct H as [v_valtype [v_val_ H]];
	apply AI_const_typing in H.

Lemma Nop_typing: forall v_S v_C t1s t2s,
    Admin_instr_ok v_S v_C admininstr__NOP (functype__ t1s t2s) ->
    t1s = t2s.
Proof.
	move => v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Nop *) by inversion H; subst; try discriminate.
	- (* Weakening *) f_equal. by eapply IHHType.
Qed.

Lemma Drop_typing: forall v_S v_C t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__DROP) (functype__ t1s t2s) ->
    exists t, t1s = t2s ++ [t].
Proof.
	move => v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Drop *) by inversion H; subst; try discriminate; exists v_t.
	- (* Weakening *) edestruct IHHType as [? ?] => //=; subst.
	exists x. by repeat rewrite <- app_assoc.
Qed.

Lemma Unop_typing: forall v_S v_C v_t v_op t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__UNOP v_t v_op) (functype__ t1s t2s) ->
    t1s = t2s /\ exists ts, t1s = @app _ ts [v_t].
Proof.
	move => v_S v_C v_t v_op t1s t2s HType.
	gen_ind_subst HType.
	- (* Unop *) inversion H; subst; try discriminate.
		split. 
		- reflexivity.
		- exists []. simpl. injection H3 as H1. f_equal. apply H1.
	- (* Weakening *) edestruct IHHType as [? [??]] => //=; subst.
	repeat split => //=. exists (v_t ++ x). by rewrite <- app_assoc.
Qed.

Lemma Binop_typing: forall v_S v_C v_t v_op t1s t2s,
	Admin_instr_ok v_S v_C (admininstr__BINOP v_t v_op) (functype__ t1s t2s) ->
    t1s = t2s ++ [v_t] /\ exists ts, t2s = ts ++ [v_t].
Proof.
	move => v_S v_C v_t v_op t1s t2s HType.
	gen_ind_subst HType.
	- (* Binop *) inversion H; subst; try discriminate.
		injection H3 as H1; subst.
		split => //. exists []. eauto.
	- (* Weakening *) edestruct IHHType as [? [??]] => //=; subst.
	split. 
		- repeat rewrite <- app_assoc. reflexivity.
		- exists (v_t ++ x). by rewrite <- app_assoc.
Qed.

Lemma Testop_typing : forall v_S v_C v_t v_testop ts1 ts2,
	Admin_instr_ok v_S v_C (admininstr__TESTOP v_t (v_testop : testop_)) (functype__ ts1 ts2) ->
	exists ts, ts1 = ts ++ [v_t] /\ ts2 = ts ++ [valtype__INN inn__I32].
Proof.
	move => v_S v_C v_t v_testop ts1 ts2 HType.

	gen_ind_subst HType.
	- (* Testop *) inversion H; subst; try discriminate.
		exists []. simpl. injection H3 as H1. subst. eauto.
	- (* Weakening *) edestruct IHHType as [? [??]] => //=; subst.
	exists (v_t ++ x). by repeat split => //=; rewrite <- app_assoc.
Qed.

Lemma Select_typing: forall v_S v_C t1s t2s,
	Admin_instr_ok v_S v_C (admininstr__SELECT) (functype__ t1s t2s) ->
    exists ts t, t1s = ts ++ [t; t; valtype__INN inn__I32] /\ t2s = ts ++ [t].
Proof.
	move => v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Select *) inversion H; subst; try discriminate.
	exists [], v_t. eauto.
	- (* Weakening *) edestruct IHHType as [? [? [??]]] => //=; subst.
	exists (v_t ++ x), x0. by repeat split => //=; rewrite <- app_assoc.
Qed.

Lemma Val_Const_list_typing: forall v_S v_C v_vals t1s t2s,
    Admin_instrs_ok v_S v_C (list__val__admininstr v_vals) (functype__ t1s t2s) ->
    t2s = t1s ++ (List.map typeof v_vals).
Proof.
	move => v_S v_C v_vals.
	induction v_vals => //=; move => t1s t2s HType.
	- apply admin_empty in HType. subst. by rewrite cats0.
	- destruct a.
	  apply_composition_typing_and_single HType.
	  apply AI_const_typing in H4_comp0.
	  subst.
	  apply IHv_vals in H4_comp.
	  subst. simpl.
	  repeat rewrite <- app_assoc.  
	  by f_equal.
Qed.

Definition upd_label C labs :=
	C <| context__LABELS := labs |>.

Definition upd_local C locs :=
	C <| context__LOCALS := locs |>.

Definition upd_return C ret :=
	C <| context__RETURN := ret |>.

Definition upd_local_return C loc ret :=
	upd_return (upd_local C loc) ret. 

Definition upd_label_local_return C loc lab ret := 
	upd_label (upd_local_return C loc ret) lab.

Definition upd_local_label_return C loc lab ret := 
	upd_return (upd_label (upd_local C loc) lab) ret.

Ltac fold_upd_context :=
	lazymatch goal with
	| |- context [upd_local (upd_return ?C ?ret) ?loc] =>
		replace (upd_local (upd_return C ret) loc) with
			(upd_local_return C ret loc); try by destruct C
	| |- context [upd_return (upd_local ?C ?ret) ?loc] =>
		replace (upd_return (upd_local C ret) loc) with
			(upd_local_return C ret loc); try by destruct C
	end.
	  
Lemma upd_label_overwrite: forall C l1 l2,
	upd_label (upd_label C l1) l2 = upd_label C l2.
Proof.
  by [].
Qed.

Lemma _append_option_none: forall {A : Type} (c : option A) ,
	_append c None = c.
Proof.
	move => A c.
	unfold _append. unfold Append_Option. unfold option_append.
	induction c => //.
Qed.

Lemma _append_option_none_left: forall {A : Type} (c : option A) ,
	_append None c = c.
Proof.
	move => A c.
	unfold _append. unfold Append_Option. unfold option_append.
	destruct c => //.
Qed.

Lemma _append_some_left: forall {A : Type} (b : A) (c : option A) ,
	_append (Some b) c = (Some b).
Proof. reflexivity. Qed.

Lemma upd_label_is_same_as_append: forall v_C lab,
	upd_label v_C (_append lab (context__LABELS v_C)) = _append {| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := lab; context__RETURN := None |} v_C.
Proof.
	move => v_C lab. reflexivity.
Qed.

Lemma upd_local_is_same_as_append: forall v_C loc,
	upd_local v_C (_append loc (context__LOCALS v_C))  = _append {| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := loc; context__LABELS := []; context__RETURN := None |} v_C.
Proof.
	move => v_C loc. reflexivity.
Qed.

Lemma upd_local_return_is_same_as_append: forall v_C loc ret,
	upd_local_return v_C (_append loc (context__LOCALS v_C)) (_append ret (context__RETURN v_C)) 
	= upd_return (upd_local v_C (_append loc (context__LOCALS v_C))) (_append ret (context__RETURN ((upd_local v_C (_append loc (context__LOCALS v_C)))))).
Proof. reflexivity. Qed.


Lemma upd_return_is_same_as_append: forall v_C ret,
	upd_return v_C (_append ret (context__RETURN v_C)) = _append {| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := []; context__RETURN := ret |} v_C.
Proof.
	move => v_C ret. reflexivity.
Qed.

Lemma If_typing: forall v_S v_C t1s v_ais1 v_ais2 ts ts',
	Admin_instr_ok v_S v_C (admininstr__IFELSE t1s v_ais1 v_ais2) (functype__ ts ts') ->
	exists ts0,
   	ts = ts0 ++ [valtype__INN inn__I32] /\ ts' = ts0 ++ t1s /\
				Instrs_ok (upd_label v_C ([t1s] ++ context__LABELS v_C)) (v_ais1) (functype__ [] t1s) /\
                Instrs_ok (upd_label v_C ([t1s] ++ context__LABELS v_C)) (v_ais2) (functype__ [] t1s).
Proof.
	move => v_S v_C t1s v_ais1 v_ais2 ts ts' HType.
	gen_ind_subst HType. 
	- (* IF *) inversion H; subst; try discriminate.
		destruct H4.
		exists [].
		simpl. injection Eadmininstr__IFELSE0 as H10. subst. 
		repeat split => //. 
	- (* Weakening *) edestruct IHHType as [? [? [? ?]]]=> //=; subst.
	exists (v_t ++ x). 
	destruct H1.
	repeat split => //=; try rewrite <- app_assoc; try reflexivity.
Qed.

Lemma Br_if_typing: forall v_S v_C ts1 ts2 v_memaddr, 
	Admin_instr_ok v_S v_C (admininstr__BR_IF v_memaddr) (functype__ ts1 ts2) ->
    exists ts (ts' : resulttype), ts2 = ts ++ ts' /\ ts1 = ts2 ++ [valtype__INN inn__I32] /\ (v_memaddr < List.length (context__LABELS v_C))%coq_nat
	/\ lookup_total (context__LABELS v_C) v_memaddr = ts'.
Proof.
	move => v_S v_C ts1 ts2 v_memaddr HType.
	gen_ind_subst HType.
	- (* BR_if *) inversion H; subst; try discriminate.
		injection H3 as H1. destruct H4. exists [], v_t. simpl. 
		repeat split => //; subst. apply H0. reflexivity.
	- (* Weakening *) edestruct IHHType as [? [? [? ?]]] => //=; subst.
	exists (v_t ++ x), x0. destruct H0; subst. 
	repeat split => //=; try repeat rewrite <- app_assoc; try reflexivity.
Qed.

Lemma Br_table_typing: forall v_S v_C ts1 ts2 ids i0,
    Admin_instr_ok v_S v_C (admininstr__BR_TABLE ids i0) (functype__ ts1 ts2) ->
    exists ts1' (ts : resulttype) , ts1 = ts1' ++ ts ++ [valtype__INN (inn__I32)] /\
                        List.Forall (fun i => (i < length (context__LABELS v_C))%coq_nat) (ids) /\
						(i0 < length (context__LABELS v_C))%coq_nat /\
						(ts = (lookup_total (context__LABELS v_C) i0)) /\
						List.Forall (fun i => ts = lookup_total (context__LABELS v_C) i) (ids).
Proof.
	move => v_S v_C ts1 ts2 ids i0 HType.
	gen_ind_subst HType.
	- (* Br_table *) inversion H; subst; try discriminate.
		injection H3 as H1. destruct H4 as [H5 [H6 [H7 H8]]]. subst.
		exists v_t_1, (lookup_total (context__LABELS v_C0) i0). repeat split => //.
	- (* Weakening *) edestruct IHHType as [? [? [? [? [? [? ?]]]]]] => //=; subst.
	exists (v_t ++ x), (lookup_total (context__LABELS v_C0) i0).
	repeat split => //=; try repeat rewrite <- app_assoc; try reflexivity.
Qed.

Lemma Relop_typing: forall v_S v_C v_t v_op t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__RELOP v_t v_op) (functype__ t1s t2s) ->
    exists ts, t1s = ts ++ [v_t; v_t] /\ t2s = ts ++ [valtype__INN inn__I32].
Proof.
	move => v_S v_C v_t v_op t1s t2s HType.
	gen_ind_subst HType.
	- (* Relop *) inversion H; subst; try discriminate.
		exists []. injection H3 as H1. subst. eauto.
	- (* Weakening *) edestruct IHHType as [? [? ?]] => //=; subst.
	exists (v_t ++ x). by repeat split => //=; try rewrite <- app_assoc.
Qed.

Lemma Cvtop_typing: forall v_S v_C t1 t2 v_op v_sx t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__CVTOP t2 v_op t1 v_sx) (functype__ t1s t2s) ->
    exists ts, t1s = ts ++ [t1] /\ t2s = ts ++ [t2].
Proof.
	move => v_S v_C t1 t2 v_op v_sx t1s t2s HType.
	gen_ind_subst HType. 
	- (* Cvtop *) exists [].
		simpl. 
		inversion H; subst; try discriminate; injection H3 as H1; subst => //.
	- (* Weakening *) edestruct IHHType as [? [? ?]] => //=; subst.
	exists (v_t ++ x). by repeat split => //=; try rewrite <- app_assoc.
Qed.


Lemma Local_tee_typing: forall v_S v_C v_memaddr ts1 ts2,
    Admin_instr_ok v_S v_C (admininstr__LOCAL_TEE v_memaddr) (functype__ ts1 ts2) ->
    exists ts t, ts1 = ts2 /\ ts1 = ts ++ [t] /\ (v_memaddr < length (context__LOCALS v_C))%coq_nat /\
                lookup_total (context__LOCALS v_C) v_memaddr = t.
Proof.
	move => v_S v_C v_memaddr ts1 ts2 HType.
	gen_ind_subst HType.
	- (* Local Tee *) inversion H; subst; try discriminate.
		destruct H4.
		injection H3 as H10; subst.
		exists [], (lookup_total (context__LOCALS v_C0) v_memaddr).
		repeat split => //=.
	- (* Weakening *) edestruct IHHType as [? [? [? [? [? ?]]]]] => //=; subst.
	exists (v_t ++ x), (lookup_total (context__LOCALS v_C0) v_memaddr).
	by repeat split => //=; try rewrite <- app_assoc.
Qed.

Lemma Label_typing: forall v_S v_C n v_instrs v_admininstrs ts1 ts2,
    Admin_instr_ok v_S v_C (admininstr__LABEL_ n v_instrs v_admininstrs) (functype__ ts1 ts2) ->
    exists (ts : resulttype) (ts2' : option valtype), ts2 = ts1 ++ ts2' /\
					Instrs_ok v_C v_instrs (functype__ ts ts2') /\
                    Admin_instrs_ok v_S (upd_label v_C ([ts] ++ (context__LABELS v_C))) v_admininstrs (functype__ [] ts2').
Proof.
	move => v_S v_C n v_instrs v_admininstrs ts1 ts2 HType.
	gen_ind_subst HType => //=.
		- (* Instr *) inversion H; subst; try discriminate.
		- (* Label *) destruct H. exists v_t_1, v_t_2. repeat split => //=.
		- (* Weakening *) edestruct IHHType as [? [? [? [? ?]]]] => //=; subst. exists x, x0. by repeat split => //=; try rewrite <- app_assoc.
Qed.

Lemma Frame_typing: forall v_S v_C n v_F v_ais t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__FRAME_ n v_F v_ais) (functype__ t1s t2s) ->
    exists (ts : resulttype), t2s = t1s ++ ts /\
               Thread_ok v_S ts v_F v_ais ts.
Proof.
	move => v_S v_C n v_F v_ais t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Instr *) inversion H; subst; try discriminate.
	- (* Frame *)  exists v_t => //=.
	- (* Weakening *) edestruct IHHType as [ts2 [??]]; eauto. subst.
		exists ts2. by repeat split => //=; try rewrite <- app_assoc.
Qed.

Lemma Set_local_typing: forall v_S C i t1s t2s,
    Admin_instr_ok v_S C (admininstr__LOCAL_SET i) (functype__ t1s t2s) ->
    exists t, lookup_total (context__LOCALS C) i = t /\
    t1s = t2s ++ [t] /\
    (i < length (context__LOCALS C))%coq_nat.
Proof.
	move => v_S C i t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Set Local *) inversion H; subst; try discriminate. destruct H4.
		injection H3 as H2. exists v_t. subst; repeat split => //.
	- (* Weakening *) edestruct IHHType as [? [? [? ?]]] => //=; subst.
		exists (lookup_total (context__LOCALS C) i).
		by repeat split => //=; try rewrite <- app_assoc.
Qed.

Lemma Get_local_typing: forall v_S v_C i t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__LOCAL_GET i) (functype__ t1s t2s) ->
    exists t, lookup_total (context__LOCALS v_C) i = t /\
    t2s = t1s ++ [::t] /\
    (i < length (context__LOCALS v_C))%coq_nat.
Proof.
	move => v_S v_C i t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Get Local *) inversion H; subst; try discriminate. destruct H4.
		injection H3 as H2. exists v_t. subst; repeat split => //.
	- (* Weakening *) edestruct IHHType as [? [? [? ?]]] => //=; subst.
		exists (lookup_total (context__LOCALS v_C0) i).
		by repeat split => //=; try rewrite <- app_assoc.
Qed.

Lemma Get_global_typing: forall v_S v_C i t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__GLOBAL_GET i) (functype__ t1s t2s) ->
    exists mut t, (lookup_total (context__GLOBALS v_C) i) = globaltype__ mut t /\
    t2s = t1s ++ [::t] /\
    (i < length (context__GLOBALS v_C))%coq_nat.
Proof.
	move => ????? HType.
	gen_ind_subst HType => //=.
	 - (* Get Global *) inversion H; subst; try discriminate.
		destruct H4. injection H3 as ?. subst. exists v_mut, v_t. repeat split => //=.

	 - (* Weakening *) edestruct IHHType as [?[?[?[??]]]]; eauto => //=. exists x, x0; subst.
	 	repeat split => //; by rewrite <- app_assoc.
Qed.

Lemma Set_global_typing: forall v_S v_C i t1s t2s,
	Admin_instr_ok v_S v_C (admininstr__GLOBAL_SET i) (functype__ t1s t2s) ->
    exists t, lookup_total (context__GLOBALS v_C) i = globaltype__ (mut__MUT (Some tt)) t /\
    t1s = t2s ++ [t] /\
    (i < length (context__GLOBALS v_C))%coq_nat.
Proof.
	intros ????? HType.
	gen_ind_subst HType => //=.
	 - (* Set Global *) inversion H; subst; try discriminate.
		destruct H4 as [? ?]. injection H3 as ?; subst. exists v_t. repeat split => //=.
	- edestruct IHHType as [? [? [? ?]]]; subst => //=. exists (x).
		repeat split => //=; by rewrite <- app_assoc.
Qed.

Lemma Return_typing: forall v_S v_C t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__RETURN) (functype__ t1s t2s) ->
    exists (ts : resulttype) ts', t1s = ts' ++ ts /\
                   context__RETURN v_C = Some ts.
Proof.
	move => v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Return *) inversion H; subst; try discriminate. exists v_t, v_t_1 => //=.
	- (* Weakening *) edestruct IHHType as [? [? [?  ?]]] => //=; subst.
		exists x, (v_t ++ x0). by repeat split => //=; try rewrite <- app_assoc.
Qed.

Lemma Const_list_typing_empty: forall v_S v_C v_vals,
    Admin_instrs_ok v_S v_C (list__val__admininstr v_vals) (functype__ [::] (List.map typeof v_vals)).
Proof.
	move => v_S v_C.
	induction v_vals => //=.
	- apply Admin_instrs_ok__empty.
	- rewrite -cat1s.
		replace (typeof a :: List.map typeof v_vals) with ([::typeof a] ++ List.map typeof v_vals) => //.
		apply admin_composition' with (t2s := [::typeof a]); eauto.
		- destruct a.
			simpl.
			apply (Admin_instrs_ok__seq v_S v_C [] (admininstr__CONST v_valtype v_val_) [] [v_valtype] []).
			split.
			- apply Admin_instrs_ok__empty.
			- apply (Admin_instr_ok__instr v_S v_C (instr__CONST v_valtype v_val_) (functype__ [] [v_valtype])); subst.
				apply Instr_ok__const.
		- by apply admin_instrs_weakening_empty_1.
Qed.

(* Lemma Local_return_typing: forall v_S v_C n v_f v_val v_val' v_instr tf,
    Admin_instr_ok v_S v_C (admininstr__FRAME_ n v_f (@app _ (list__val__admininstr v_val') (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__RETURN )] (list__instr__admininstr v_instr))))) tf ->
    Admin_instrs_ok v_S v_C (list__val__admininstr v_val) tf.
Proof.
	move => v_S v_C n v_f v_val v_val' v_instr tf HType.
	destruct tf as [t1s t2s].
	apply Frame_typing in HType; destruct HType as [ts [? ?]].
	inversion H0; destruct H1; subst.
	rewrite <- upd_return_is_same_as_append in H7.
	apply admin_instrs_weakening_empty_1.
	apply_composition_typing H7.
	apply_composition_typing H4_comp.
	apply_composition_typing H4_comp0.
	apply_composition_typing_single H3_comp1.
	apply Return_typing in H4_comp0; destruct H4_comp0 as [ts0 [ts' [? ?]]]. simpl in H2.
	apply Val_Const_list_typing in H3_comp0.
	apply Val_Const_list_typing in H3_comp.
	subst.
	symmetry in H1_comp. apply app_eq_nil in H1_comp; destruct H1_comp; subst.
	simpl in *.
	destruct ts.
	unfold _append in H2. unfold Append_Option in H2. unfold option_append in H2. injection H2 as ?. subst.
	simpl in *.

	apply const_es_exists in HConst as [? ->].
	apply ety_a'; first by apply const_list_is_basic; apply v_to_e_const.
	eapply Lfilled_return_typing in Hetype; eauto; last by apply v_to_e_const.
	apply et_to_bet in Hetype; last by apply const_list_is_basic, v_to_e_const.
	apply Val_Const_list_typing in Hetype; subst; simpl in *.
	by apply Const_list_typing_empty. *)

Lemma Break_typing: forall n v_S v_C t1s t2s,
	Admin_instr_ok v_S v_C (admininstr__BR n) (functype__ t1s t2s) ->
	exists ts ts0, 
				(n < size (context__LABELS v_C))%coq_nat /\
				lookup_total (context__LABELS v_C) n = ts /\
				t1s = ts0 ++ ts.
Proof.
	move => n v_S v_C t1s t2s HType.
	gen_ind_subst HType.
	- (* BREAK *) 
		inversion H; subst; try discriminate. destruct H4.
		exists v_t, v_t_1.
		injection H3 as ?; subst; repeat split => //=.
	- (* Weakening *)
		edestruct IHHType as [ts [ts0 [? ?]]] => //=.
		destruct H0; subst.
		exists (lookup_total (context__LABELS v_C0) n), (v_t ++ ts0).
		repeat split => //=; by repeat rewrite <- app_assoc.
Qed.

Lemma CALL_ADDR_typing: forall v_S v_C a t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__CALL_ADDR a) (functype__ t1s t2s) ->
    exists v_funcinst, lookup_total (store__FUNCS v_S) a = v_funcinst.
Proof.
  move => s C a t1s t2s HType.
  gen_ind_subst HType => //.
  - (* Instr *) inversion H; subst; try discriminate.
  - (* Call Addr *) inversion H; destruct H3. exists (lookup_total (store__FUNCS s) a) => //=.
  - (* Weakening *) by eapply IHHType => //=.
Qed.

Lemma map_eq_local: forall (l l' : list valtype) ,
	List.map [eta local__LOCAL] l = List.map [eta local__LOCAL] l' -> l = l'.
Proof.
	move => l l' H.
	generalize dependent l'.
	induction l; move => l' H.
	- destruct l' => //=.
	- destruct l' => //=. repeat rewrite List.map_cons in H.
		injection H as ?.
		f_equal. 
		apply H.
		apply IHl; eauto.
Qed.

Lemma fold_append: forall v_C v_t v_func v_glob v_tab v_mem v_local v_lab v_ret,
	_append {| context__TYPES := v_t;
	context__FUNCS := v_func;
	context__GLOBALS := v_glob;
	context__TABLES := v_tab;
	context__MEMS := v_mem;
	context__LOCALS := v_local;
	context__LABELS := v_lab;
	context__RETURN := v_ret|} v_C = 
	{| context__TYPES := v_t ++ context__TYPES v_C;
	context__FUNCS := v_func ++ context__FUNCS v_C;
	context__GLOBALS := v_glob ++ context__GLOBALS v_C;
	context__TABLES := v_tab ++ context__TABLES v_C;
	context__MEMS := v_mem ++ context__MEMS v_C;
	context__LOCALS := v_local ++ context__LOCALS v_C;
	context__LABELS := v_lab ++ context__LABELS v_C;
	context__RETURN := _append v_ret (context__RETURN v_C)|}.
Proof. reflexivity. Qed.



Lemma CALL_ADDR_invoke_typing: forall v_S v_C v_a t1s t2s v_t_1 (v_t_2 : resulttype) v_mm v_func v_x v_t v_instrs,
    Admin_instr_ok v_S v_C (admininstr__CALL_ADDR v_a) (functype__ t1s t2s) ->
	((lookup_total (store__FUNCS v_S) v_a) = {| funcinst__TYPE := (functype__ v_t_1 v_t_2); funcinst__MODULE := v_mm; funcinst__CODE := v_func |}) ->
	(v_func = (func__FUNC v_x (List.map (fun v_t => (local__LOCAL v_t)) (v_t)) v_instrs)) ->
	Store_ok v_S ->
    exists ts' C', t1s = ts' ++ v_t_1 /\ t2s = ts' ++ v_t_2 /\
	Module_instance_ok v_S v_mm C' /\
	Instrs_ok (upd_local_label_return C' ((v_t_1 ++ v_t) ++ (context__LOCALS C')) (_append ([v_t_2]) (context__LABELS C')) (_append (Some v_t_2) (context__RETURN C'))) v_instrs (functype__ [::] v_t_2).
Proof.
	move => v_S v_C v_a t1s t2s v_t_1 v_t_2 v_mm v_func v_x v_t v_instrs HType Hfinst HFunc HST.


	gen_ind_subst HType => //.
	- (* Instr *) inversion H; subst; try discriminate.
	- (* Call Addr *) inversion H; destruct H4. subst. rewrite H5 in H3. injection H3 as ?. subst. inversion HST; decomp.
		apply Forall2_lookup in H8; destruct H8.
		rewrite H7 in H4. simpl in H4.
		apply H12 in H4.
		rewrite  H7 in H5.
		simpl in H5.
		rewrite H5 in H4.
		inversion H4; destruct H15 as [? [? ?]].
		inversion H20; destruct H23 as [? [? ?]].
		inversion H29.
		exists [], v_C. repeat split => //=.
		apply map_eq_local in H24; subst.
		destruct v_t_2; destruct v_t_3 => //=.
		injection H27 as ?.
		subst.
		rewrite fold_append in H30; simpl in H30.
		repeat rewrite _append_option_none_left in H30.
		apply H30.
	- (* Weakening *) edestruct IHHType as [ts0' [C' [? [? [? ?]]]]]; subst => //=.
		- apply HST.
		- apply Hfinst.
		- exists (v_t0 ++ ts0'), C'; repeat split => //=; by rewrite <- app_assoc.  
Qed.

Lemma option_zip_with_same_pack: forall (v_n0 : option nat) (v_sx0 : option sx) (v_ww_sx : option (ww * sx)),
	option_zipWith (fun (v : nat) (s : sx) => (packsize__ v, s)) v_n0 v_sx0 = v_ww_sx ->
	v_n0 = (None : option nat) <-> v_sx0 = (None : option sx) -> (exists v s, v_ww_sx = Some ((packsize__ v, s)))
	\/ (v_ww_sx = None).
Proof.
	move => v_n0 v_sx0 v_ww_sx H H2.
	assert ((None : option sx) = (None : option sx)). { reflexivity. } 
	assert ((None : option nat) = (None : option nat)). { reflexivity. } 
	destruct v_n0 => //=; destruct v_sx0 => //=; simpl in H.
	- left. exists n, s; eauto.
	- rewrite <- H2 in H0; subst. discriminate.
	- rewrite H2 in H1. discriminate.
	- right; eauto.
Qed. 

	
Lemma Load_typing: forall v_S v_C t v_memop v_ww_sx t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__LOAD_ t v_ww_sx v_memop) (functype__ t1s t2s) ->
    exists ts v_n v_sx v_inn v_mt, t1s = ts ++ [valtype__INN inn__I32] /\ t2s = ts ++ [t] /\
	(v_ww_sx = option_zipWith (fun (v : nat) (s : sx) => (packsize__ v, s)) v_n v_sx ) /\
	(0 < (List.length (context__MEMS v_C)))%coq_nat /\ ((v_n = None) <-> (v_sx = (None : option sx))) 
	/\ ((lookup_total (context__MEMS v_C) 0) = v_mt) 
	/\ ((Nat.pow 2 (memop__ALIGN v_memop))%coq_nat <= ((fun_size t) / 8)%coq_nat)%coq_nat 
	/\ List.Forall (fun v_n => ((((Nat.pow 2 (memop__ALIGN v_memop)) <= (v_n / 8))%coq_nat) 
	/\ ((v_n / 8) < ((fun_size t) / 8))%coq_nat)) (option_to_list v_n) 
	/\ ((v_n = None) \/ ([t] = [(valtype__INN v_inn)])).          
Proof.
	move => v_S v_C t v_memop v_ww_sx t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Load *) inversion H; subst; try discriminate; destruct H4 as [? [? [? [? [? ?]]]]].
		injection H3 as ?. exists [], v_n, v_sx, v_inn, v_mt. subst. repeat split => //=.
		destruct H6. 
		- left => //=. 
		- right. f_equal. apply H2.
	- (* Weakening *) edestruct IHHType as [ts [v_n [v_sx [v_inn [v_mt [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]] => //=.
	exists (v_t ++ ts), v_n, v_sx, v_inn, v_mt. subst. repeat split => //=; try repeat rewrite <- app_assoc; eauto.
Qed.

Lemma Store_typing: forall v_S v_C t v_ww v_memop t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__STORE t v_ww v_memop) (functype__ t1s t2s) ->
	exists v_n v_mt v_inn,
    t1s = t2s ++ [::valtype__INN inn__I32; t] /\
	(0 < (List.length (context__MEMS v_C)))%coq_nat 
	/\ ((lookup_total (context__MEMS v_C) 0) = v_mt) 
	/\ ((Nat.pow 2 (memop__ALIGN v_memop)) <= ((fun_size t) / 8))%coq_nat 
	/\ List.Forall (fun v_n => (((Nat.pow 2 (memop__ALIGN v_memop)) <= (v_n / 8))%coq_nat 
	/\ ((v_n / 8) < ((fun_size t) / 8))%coq_nat)) (option_to_list v_n) 
	/\ ((v_n = None) \/ (t = (valtype__INN v_inn))).
Proof.
	move => v_S v_C t v_ww v_memop t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Store *) inversion H; subst; try discriminate. destruct H4 as [? [? [? [? ?]]]].
		injection H3 as ?. exists v_n, v_mt, v_inn. subst. repeat split => //=.
	- (* Weakening *) edestruct IHHType as [v_n [v_mt [v_inn [? [? [? [? [? ?]]]]]]]] => //=.
	exists v_n, v_mt, v_inn. subst. repeat split => //=; try repeat rewrite <- app_assoc; eauto.
Qed.

Lemma Memory_size_typing: forall v_S v_C t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__MEMORY_SIZE) (functype__ t1s t2s) ->
	exists v_mt, 
	(0 < (List.length (context__MEMS v_C)))%coq_nat /\ 
	((lookup_total (context__MEMS v_C) 0) = v_mt) /\
    t2s = t1s ++ [valtype__INN inn__I32].
Proof.
	intros v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Memory Size *) inversion H; subst; try discriminate. destruct H3.
  		exists v_mt. repeat split => //=.
	- (* Weakening *) edestruct IHHType as [v_mt [? ?]]; subst=> //=. exists v_mt. destruct H0. repeat split => //=.
		rewrite H1. by repeat rewrite <- app_assoc.
Qed.

Lemma Grow_memory_typing: forall v_S v_C t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__MEMORY_GROW) (functype__ t1s t2s) ->
	exists v_mt ts, 
	(0 < (List.length (context__MEMS v_C)))%coq_nat /\ 
	((lookup_total (context__MEMS v_C) 0) = v_mt) /\
    t2s = t1s /\ t1s = ts ++ [valtype__INN inn__I32].
Proof.
	intros v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Memory Grow *) inversion H; subst; try discriminate. destruct H3.
		exists v_mt, []. repeat split => //=.
	- (* Weakening *) edestruct IHHType as [v_mt [v_ts [? [? [? ?]]]]] => //=.
		exists v_mt, (v_t ++ v_ts). subst. repeat split => //=; by repeat rewrite <- app_assoc.
Qed.
		
Lemma Block_typing: forall v_S v_C t2s v_instrs tn tm,
    Admin_instr_ok v_S v_C (admininstr__BLOCK t2s v_instrs) (functype__ tn tm) ->
    exists ts, tn = ts /\ tm = ts ++ t2s /\
		Instrs_ok (upd_label v_C ([t2s] ++ (context__LABELS v_C))) v_instrs (functype__ [] t2s).
Proof.
	move => v_S v_C t2s v_instrs tn tm HType.
	gen_ind_subst HType => //=.
	- (* Block *) 
		inversion H; subst; try discriminate. exists []. 
		injection H3 as ?; subst. repeat split => //=.
	- (* Frame *)
		edestruct IHHType as [ts [? [? ?]]] => //=; subst.
		exists (v_t ++ ts). repeat split => //=; by rewrite <- app_assoc.
Qed.

Lemma Loop_typing: forall v_S v_C t2s v_instrs tn tm,
    Admin_instr_ok v_S v_C (admininstr__LOOP t2s v_instrs) (functype__ tn tm) ->
    exists ts, tn = ts /\ tm = ts ++ t2s /\
		Instrs_ok (upd_label v_C ([None] ++ (context__LABELS v_C))) v_instrs (functype__ [] t2s).
Proof.
	move => v_S v_C t2s v_instrs tn tm HType.
	gen_ind_subst HType => //=.
	- (* Loop *) 
		inversion H; subst; try discriminate. exists []. 
		injection H3 as ?; subst. repeat split => //=.
	- (* Frame *)
		edestruct IHHType as [ts [? [? ?]]] => //=; subst.
		exists (v_t ++ ts). repeat split => //=; by rewrite <- app_assoc.
Qed.

Lemma Call_typing: forall j v_S v_C t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__CALL j) (functype__ t1s t2s) ->
    exists ts t1s' t2s', (j < length (context__FUNCS v_C))%coq_nat /\
    lookup_total (context__FUNCS v_C) j = functype__ t1s' t2s' /\
                         t1s = ts ++ t1s' /\
                         t2s = ts ++ t2s'.
Proof.
	move => j v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Call *) 
		inversion H; subst; try discriminate. destruct H4. exists [], t1s, v_t_2. 
		injection H3 as ?; subst. repeat split => //=.
	- (* Frame *)
		edestruct IHHType as [ts [t1s'' [t2s'' [? [? [? ?]]]]]] => //=; subst.
		exists (v_t ++ ts), t1s'', t2s''. repeat split => //=; by rewrite <- app_assoc.
Qed.

Lemma Call_indirect_typing: forall v_S i v_C t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__CALL_INDIRECT i) (functype__ t1s t2s) ->
    exists tn tm ts,
    (i < length (context__TYPES v_C))%coq_nat /\
    lookup_total (context__TYPES v_C) i = functype__ tn tm /\
    t1s = ts ++ tn ++ [valtype__INN inn__I32] /\ t2s = ts ++ tm.
Proof.
	move => j v_S v_C t1s t2s HType.
	gen_ind_subst HType => //=.
	- (* Call Indirect *) 
		inversion H; subst; try discriminate. destruct H4. exists v_t_1, v_t_2, []. 
		injection H3 as ?; subst. repeat split => //=.
	- (* Frame *)
		edestruct IHHType as [ts [t1s'' [t2s'' [? [? [? ?]]]]]] => //=; subst.
		exists ts, t1s'', (v_t ++ t2s''). repeat split => //=; by rewrite <- app_assoc.
Qed.

Lemma inst_t_context_local_empty: forall s i C,
	Module_instance_ok s i C ->
    context__LOCALS C = [].
Proof.
	move => s i C HMInst. inversion HMInst => //=.
Qed.

Lemma inst_t_context_labels_empty: forall s i C,
	Module_instance_ok s i C ->
    context__LABELS C = [].
Proof.
	move => s i C HMInst. inversion HMInst => //=.
Qed.
		
Lemma upd_label_unchanged: forall C lab,
    context__LABELS C = lab ->
    upd_label C lab = C.
Proof.
  move => C lab HLab.
  rewrite -HLab. unfold upd_label. by destruct C.
Qed.

Lemma upd_label_unchanged_typing: forall v_S v_C v_admininstrs v_func_type,
    Admin_instrs_ok v_S v_C v_admininstrs v_func_type <->
    Admin_instrs_ok v_S (upd_label v_C (context__LABELS v_C)) v_admininstrs v_func_type.
Proof.
  move => s C es tf.
  split.
	- move => HType.
		by rewrite upd_label_unchanged.
	- move => HType.
		simpl in HType.
		remember (context__LABELS C) as lab.
		symmetry in Heqlab.
		apply upd_label_unchanged in Heqlab.
		rewrite <- Heqlab => //=. 
Qed.

(* Generated Lemmas *)

Lemma Step_pure__unreachable_preserves : forall v_S v_C  v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__UNREACHABLE )] v_func_type ->
	Step_pure [(admininstr__UNREACHABLE )] [(admininstr__TRAP )] ->
	Admin_instrs_ok v_S v_C [(admininstr__TRAP )] v_func_type.
Proof.
	move => v_S v_C v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply (Admin_instrs_ok__seq v_S v_C [] (admininstr__TRAP) tf1 tf2 tf1).
	split.
	- apply admin_weakening_empty_both. apply Admin_instrs_ok__empty.
	- apply Admin_instr_ok__trap.
Qed.

Lemma Step_pure__nop_preserves : forall v_S v_C  v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__NOP )] v_func_type ->
	Step_pure [(admininstr__NOP )] [] ->
	Admin_instrs_ok v_S v_C [] v_func_type.
Proof.
	move => v_S v_C v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_single HType; subst.
	apply Admin_instrs_ok__frame.
	apply Nop_typing in H4_comp; subst.
	apply admin_weakening_empty_both.
	apply Admin_instrs_ok__empty.
Qed.

Lemma Step_pure__drop_preserves : forall v_S v_C (v_val : val) v_func_type,
	Admin_instrs_ok v_S v_C [(v_val : admininstr);(admininstr__DROP )] v_func_type ->
	Step_pure [(v_val : admininstr);(admininstr__DROP )] [] ->
	Admin_instrs_ok v_S v_C [] v_func_type.
Proof.
	move => v_S v_C v_val v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.

	apply Drop_typing in H4_comp1; destruct H4_comp1 as [t H1]; subst.
	apply_const_typing_to_val H4_comp0.
	subst.
	repeat rewrite -> app_assoc in H1_comp1; apply split_append_last in H1_comp1; destruct H1_comp1; subst.
	rewrite H.
	apply admin_weakening_empty_both.
	apply Admin_instrs_ok__empty.
Qed.

Lemma Step_pure__select_true_preserves : forall v_S v_C (v_val_1 : val) (v_val_2 : val) (v_c : iN) v_func_type,
	Admin_instrs_ok v_S v_C [(v_val_1 : admininstr);(v_val_2 : admininstr);(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__SELECT )] v_func_type ->
	Step_pure [(v_val_1 : admininstr);(v_val_2 : admininstr);(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__SELECT )] [(v_val_1 : admininstr)] ->
	Admin_instrs_ok v_S v_C [(v_val_1 : admininstr)] v_func_type.
Proof.
	move => v_S v_C v_val_1 v_val_2 v_c v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_and_single H4_comp.
	apply_composition_typing_and_single H4_comp1.
	apply_composition_typing_single H4_comp2.
	induction v_val_1.
	apply AI_const_typing in H4_comp0.
	apply_const_typing_to_val H4_comp.
	apply AI_const_typing in H4_comp1.
	apply Select_typing in H4_comp3; destruct H4_comp3 as [v_ts [v_t [H4_comp3 H4_comp3']]].
	subst.
	remember [:: v_t; v_t; valtype__INN inn__I32] as v_select.
	rewrite -cat1s in Heqv_select.
	remember [:: v_t; valtype__INN inn__I32] as v_select2.
	rewrite -cat1s in Heqv_select2; subst.
	repeat rewrite -> app_assoc in H1_comp2.
	apply split_append_last in H1_comp2; destruct H1_comp2.
	rewrite H in H1_comp0.
	repeat rewrite -> app_assoc in H1_comp0.
	apply split_append_last in H1_comp0; destruct H1_comp0.
	rewrite H1 in H1_comp1.
	repeat rewrite -> app_assoc in H1_comp1.
	apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H3.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (Admin_instrs_ok__seq v_S v_C [] (val__CONST v_valtype v_val_) [] [v_t] []). 
	split. apply Admin_instrs_ok__empty.
	unfold fun_coec_val__admininstr.
	apply (Admin_instr_ok__instr v_S v_C (instr__CONST v_valtype v_val_) (functype__ [] [v_t])); subst.
	apply Instr_ok__const.
Qed.

Lemma Step_pure__select_false_preserves : forall v_S v_C (v_val_1 : val) (v_val_2 : val) (v_c : iN) v_func_type,
	Admin_instrs_ok v_S v_C [(v_val_1 : admininstr);(v_val_2 : admininstr);(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__SELECT )] v_func_type ->
	Step_pure [(v_val_1 : admininstr);(v_val_2 : admininstr);(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__SELECT )] [(v_val_2 : admininstr)] ->
	Admin_instrs_ok v_S v_C [(v_val_2 : admininstr)] v_func_type.
Proof.
	move => v_S v_C v_val_1 v_val_2 v_c v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_and_single H4_comp.
	apply_composition_typing_and_single H4_comp1.
	apply_composition_typing_single H4_comp2.
	apply_const_typing_to_val H4_comp0.
	induction v_val_2.
	apply AI_const_typing in H4_comp.
	apply AI_const_typing in H4_comp1.
	apply Select_typing in H4_comp3; destruct H4_comp3 as [v_ts [v_t [H4_comp3 H4_comp3']]].
	subst.
	remember [:: v_t; v_t; valtype__INN inn__I32] as v_select.
	rewrite -cat1s in Heqv_select.
	remember [:: v_t; valtype__INN inn__I32] as v_select2.
	rewrite -cat1s in Heqv_select2; subst.
	repeat rewrite -> app_assoc in H1_comp2.
	apply split_append_last in H1_comp2; destruct H1_comp2.
	rewrite H in H1_comp0.
	repeat rewrite -> app_assoc in H1_comp0.
	apply split_append_last in H1_comp0; destruct H1_comp0.
	rewrite H1 in H1_comp1.
	repeat rewrite -> app_assoc in H1_comp1.
	apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H3.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (Admin_instrs_ok__seq v_S v_C [] (val__CONST v_valtype0 v_val_0) [] [v_t] []). 
	split. apply Admin_instrs_ok__empty.
	unfold fun_coec_val__admininstr.
	apply (Admin_instr_ok__instr v_S v_C (instr__CONST v_valtype0 v_val_0) (functype__ [] [v_t])); subst.
	apply Instr_ok__const.
Qed.

Lemma Step_pure__if_true_preserves : forall v_S v_C (v_c : iN) (v_t : (option valtype)) (v_instr_1 : (list instr)) (v_instr_2 : (list instr)) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__IFELSE v_t v_instr_1 v_instr_2)] v_func_type ->
	Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__IFELSE v_t v_instr_1 v_instr_2)] [(admininstr__BLOCK v_t v_instr_1)] ->
	Admin_instrs_ok v_S v_C [(admininstr__BLOCK v_t v_instr_1)] v_func_type.
Proof.
	move => v_S v_C v_c v_t v_instr_1 v_instr_2 v_func_type HType HReduce.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	apply AI_const_typing in H4_comp0.
	apply If_typing in H4_comp1; destruct H4_comp1 as [ts0 [H1 [H2 [H3 H4]]]].
	subst.
	repeat rewrite -> app_assoc in H1_comp1.
	apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (Admin_instrs_ok__seq v_S v_C [] (admininstr__BLOCK v_t v_instr_1) [] v_t []). 
	split. apply Admin_instrs_ok__empty.
	apply (Admin_instr_ok__instr v_S v_C (instr__BLOCK v_t v_instr_1) (functype__ [::] v_t)).
	apply (Instr_ok__block).
	rewrite <- upd_label_is_same_as_append.
	apply H3.
Qed.

Lemma Step_pure__if_false_preserves : forall v_S v_C (v_c : iN) (v_t : (option valtype)) (v_instr_1 : (list instr)) (v_instr_2 : (list instr)) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__IFELSE v_t v_instr_1 v_instr_2)] v_func_type ->
	Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__IFELSE v_t v_instr_1 v_instr_2)] [(admininstr__BLOCK v_t v_instr_2)] ->
	Admin_instrs_ok v_S v_C [(admininstr__BLOCK v_t v_instr_2)] v_func_type.
Proof.
	move => v_S v_C v_c v_t v_instr_1 v_instr_2 v_func_type HType HReduce.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	apply AI_const_typing in H4_comp0.
	apply If_typing in H4_comp1; destruct H4_comp1 as [H1 [H2 [H3 H4]]].
	subst.
	repeat rewrite -> app_assoc in H1_comp1.
	apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (Admin_instrs_ok__seq v_S v_C [] (admininstr__BLOCK v_t v_instr_2) [] v_t []). 
	split. apply Admin_instrs_ok__empty.
	apply (Admin_instr_ok__instr v_S v_C (instr__BLOCK v_t v_instr_2) (functype__ [::] v_t)).
	apply Instr_ok__block.
	rewrite <- upd_label_is_same_as_append.
	apply H4.
Qed.

Lemma Step_pure__label_vals_preserves : forall v_S v_C (v_n : n) (v_instr : (list instr)) (v_val : (list val)) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__LABEL_ v_n v_instr (list__val__admininstr v_val))] v_func_type ->
	Step_pure [(admininstr__LABEL_ v_n v_instr (list__val__admininstr v_val))] (list__val__admininstr v_val) ->
	Admin_instrs_ok v_S v_C (list__val__admininstr v_val) v_func_type.
Proof.
	move => v_S v_C v_n v_instr v_val v_func_type HType HReduce.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_single HType.
	apply Label_typing in H4_comp; destruct H4_comp as [ts [ts2' [H1 [H2 H3]]]].
	subst.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply Val_Const_list_typing in H3; subst.
	rewrite H3.
	simpl.
	apply Const_list_typing_empty.
Qed.

Lemma Step_pure__br_zero_preserves : forall v_S v_minst v_C (v_n : n) (v_instr' : (list instr)) (v_val' : (list val)) (v_val : (list val)) (v_instr : (list instr)) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__LABEL_ v_n v_instr' (@app _ (list__val__admininstr v_val') (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__BR 0)] (list__instr__admininstr v_instr)))))] v_func_type ->
	Module_instance_ok v_S v_minst v_C ->
	Step_pure [(admininstr__LABEL_ v_n v_instr' (@app _ (list__val__admininstr v_val') (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__BR 0)] (list__instr__admininstr v_instr)))))] (@app _ (list__val__admininstr v_val) (list__instr__admininstr v_instr')) ->
	Admin_instrs_ok v_S v_C (@app _ (list__val__admininstr v_val) (list__instr__admininstr v_instr')) v_func_type.
Proof.
	move => v_S v_minst v_C v_n v_instr' v_val' v_val v_instr v_func_type HType HMinst HReduce.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq in HType.
	apply Label_typing in HType; destruct HType as [ts [ts2' [? [? ?]]]].
	apply_composition_typing H1.
	apply_composition_typing H4_comp.
	apply_composition_typing H4_comp0.
	repeat rewrite <- app_right_nil in *.
	rewrite <- admin_instrs_ok_eq in H3_comp1.
	apply Break_typing in H3_comp1; destruct H3_comp1 as [ts0' [ts1' [? [? ?]]]].
	apply Val_Const_list_typing in H3_comp.
	apply Val_Const_list_typing in H3_comp0.
	subst.
	apply inst_t_context_labels_empty in HMinst as ?.
	rewrite H1 in H1_comp1. rewrite <- app_right_nil in H1_comp1. 
	unfold upd_label in H1_comp1. unfold set in H1_comp1. 
	simpl in H1_comp1.
	unfold lookup_total in H1_comp1.
	simpl in H1_comp1.
	apply empty_append in H1_comp; destruct H1_comp; subst.
	simpl in *.
	apply admin_composition' with (t2s := (ts1 ++ ts)).

Admitted.

Lemma Step_pure__br_succ_preserves : forall v_S v_C (v_n : n) (v_instr' : (list instr)) (v_val : (list val)) (v_l : labelidx) (v_instr : (list instr)) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__LABEL_ v_n v_instr' (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__BR (v_l + 1))] (list__instr__admininstr v_instr))))] v_func_type ->
	Step_pure [(admininstr__LABEL_ v_n v_instr' (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__BR (v_l + 1))] (list__instr__admininstr v_instr))))] (@app _ (list__val__admininstr v_val) [(admininstr__BR v_l)]) ->
	Admin_instrs_ok v_S v_C (@app _ (list__val__admininstr v_val) [(admininstr__BR v_l)]) v_func_type.
Proof.
Admitted.

Lemma Step_pure__br_if_true_preserves : forall v_S v_C (v_c : iN) (v_l : labelidx) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__BR_IF v_l)] v_func_type ->
	Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__BR_IF v_l)] [(admininstr__BR v_l)] ->
	Admin_instrs_ok v_S v_C [(admininstr__BR v_l)] v_func_type.
Proof.
	move => v_S v_C v_c v_l v_func_type HType HReduce.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	apply Br_if_typing in H4_comp1; destruct H4_comp1 as [ts [ts' [H1 [H2 [H3 H4]]]]].
	apply AI_const_typing in H4_comp0.
	subst.
	repeat rewrite -> app_assoc in H1_comp1; apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H.
	repeat rewrite -> app_assoc.
	apply Admin_instrs_ok__frame.
	remember (lookup_total (context__LABELS v_C) v_l) as ts'.
	apply (Admin_instrs_ok__seq v_S v_C [] (admininstr__BR v_l) ts' ts' ts').
	split. apply admin_weakening_empty_both. apply Admin_instrs_ok__empty.
	apply (Admin_instr_ok__instr _ _ (instr__BR v_l) (functype__ ts' ts')).
	apply (Instr_ok__br v_C v_l [] ts' ts'). split.
	apply H3. subst. reflexivity.
Qed.

Lemma Step_pure__br_if_false_preserves : forall v_S v_C (v_c : iN) (v_l : labelidx) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__BR_IF v_l)] v_func_type ->
	Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__BR_IF v_l)] [] ->
	Admin_instrs_ok v_S v_C [] v_func_type.
Proof.
	move => v_S v_C v_c v_l v_func_type HType HReduce.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	apply Br_if_typing in H4_comp1; destruct H4_comp1 as [ts [ts' [H1 [H2 [H3 H4]]]]].
	apply AI_const_typing in H4_comp0.
	subst.
	repeat rewrite -> app_assoc in H1_comp1; apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H.
	repeat rewrite -> app_assoc.
	apply admin_weakening_empty_both. apply Admin_instrs_ok__empty.
Qed.

Lemma Step_pure__br_table_lt_preserves : forall v_S v_C (v_i : nat) (v_l : (list labelidx)) (v_l' : labelidx) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__BR_TABLE v_l v_l')] v_func_type ->
	Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__BR_TABLE v_l v_l')] [(admininstr__BR (lookup_total v_l v_i))] ->
	(v_i < Datatypes.length v_l)%coq_nat -> 
	Admin_instrs_ok v_S v_C [(admininstr__BR (lookup_total v_l v_i))] v_func_type.
Proof.
	move => v_S v_C v_i v_l v_l' v_func_type HType HReduce H.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	apply Br_table_typing in H4_comp1; destruct H4_comp1 as [ts1' [ts [H1 [H2 [H3 [H4 H5]]]]]].
	apply AI_const_typing in H4_comp0.
	subst.
	repeat rewrite -> app_assoc in H1_comp1.
	apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H0.
	repeat rewrite <- app_assoc.
	apply Admin_instrs_ok__frame.
	apply Admin_instrs_ok__frame.
	remember (ts1' ++ lookup_total (context__LABELS v_C) v_l')%list as ts. (* Just for convencience *)
	apply (Admin_instrs_ok__seq v_S v_C [] (admininstr__BR (lookup_total v_l v_i)) ts ts3_comp1 ts).
	split. 
	+ (* Empty *) apply admin_weakening_empty_both. apply Admin_instrs_ok__empty.
	+ (* BR *) apply (Admin_instr_ok__instr _ _ (instr__BR (lookup_total v_l v_i)) (functype__ ts ts3_comp1)).
		subst. apply (Instr_ok__br v_C (lookup_total v_l v_i) ts1' (lookup_total (context__LABELS v_C) v_l') ts3_comp1).
		rewrite Forall_nth in H5.
		rewrite Forall_nth in H2.
		apply (H5 _ default_val) in H as H6.
		apply (H2 _ default_val) in H as H7.
		split => //.
Qed.

Lemma Step_pure__br_table_ge_preserves : forall v_S v_C (v_i : nat) (v_l : (list labelidx)) (v_l' : labelidx) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__BR_TABLE v_l v_l')] v_func_type ->
	Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__BR_TABLE v_l v_l')] [(admininstr__BR v_l')] ->
	(v_i >= (List.length v_l))%coq_nat ->
	Admin_instrs_ok v_S v_C [(admininstr__BR v_l')] v_func_type.
Proof.
	move => v_S v_C v_i v_l v_l' v_func_type HType HReduce H.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	apply Br_table_typing in H4_comp1; destruct H4_comp1 as [ts1' [ts [H1 [H2 [H3 [H4 H5]]]]]].
	apply AI_const_typing in H4_comp0.
	subst.
	repeat rewrite -> app_assoc in H1_comp1.
	apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H0.
	repeat rewrite <- app_assoc.
	apply Admin_instrs_ok__frame.
	apply Admin_instrs_ok__frame.
	remember (ts1' ++ lookup_total (context__LABELS v_C) v_l')%list as ts. (* Just for convencience *)
	apply (Admin_instrs_ok__seq v_S v_C [] (admininstr__BR v_l') ts ts3_comp1 ts).
	split. 
	+ (* Empty *) apply admin_weakening_empty_both. apply Admin_instrs_ok__empty.
	+ (* BR *) apply (Admin_instr_ok__instr _ _ (instr__BR v_l') (functype__ ts ts3_comp1)).
		subst. apply (Instr_ok__br v_C v_l' ts1' (lookup_total (context__LABELS v_C) v_l') ts3_comp1).
		split => //.
Qed.

Lemma Step_pure__frame_vals_preserves : forall v_S v_C (v_n : n) (v_f : frame) (v_val : (list val)) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__FRAME_ v_n v_f (list__val__admininstr v_val))] v_func_type ->
	Step_pure [(admininstr__FRAME_ v_n v_f (list__val__admininstr v_val))] (list__val__admininstr v_val) ->
	Admin_instrs_ok v_S v_C (list__val__admininstr v_val) v_func_type.
Proof.
	move => v_S v_C v_n v_f v_val v_func_type HType HReduce.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq in HType.
	apply Frame_typing in HType; destruct HType as [ts [? ?]].
	inversion H0; destruct H1.
	apply Val_Const_list_typing in H7; simpl in *; subst.
	apply admin_instrs_weakening_empty_1.
	rewrite H7.
	apply Const_list_typing_empty.
Qed.

Lemma Step_pure__return_frame_preserves : forall v_S v_C (v_n : n) (v_f : frame) (v_val' : (list val)) (v_val : (list val)) (v_instr : (list instr)) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__FRAME_ v_n v_f (@app _ (list__val__admininstr v_val') (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__RETURN )] (list__instr__admininstr v_instr)))))] v_func_type ->
	Step_pure [(admininstr__FRAME_ v_n v_f (@app _ (list__val__admininstr v_val') (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__RETURN )] (list__instr__admininstr v_instr)))))] (list__val__admininstr v_val) ->
	Admin_instrs_ok v_S v_C (list__val__admininstr v_val) v_func_type.
Proof.
Admitted.

Lemma Step_pure__return_label_preserves : forall v_S v_C (v_n : n) (v_instr' : (list instr)) (v_val : (list val)) (v_instr : (list instr)) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__LABEL_ v_n v_instr' (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__RETURN )] (list__instr__admininstr v_instr))))] v_func_type ->
	Step_pure [(admininstr__LABEL_ v_n v_instr' (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__RETURN )] (list__instr__admininstr v_instr))))] (@app _ (list__val__admininstr v_val) [(admininstr__RETURN )]) ->
	Admin_instrs_ok v_S v_C (@app _ (list__val__admininstr v_val) [(admininstr__RETURN )]) v_func_type.
Proof.
	move => v_S v_C v_n v_instr' v_val v_instr v_func_type HType HReduce.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq in HType.
	apply Label_typing in HType; destruct HType as [ts [ts2' [? [? ?]]]].
	apply_composition_typing H1.
	apply_composition_typing H4_comp.
	repeat rewrite <- app_right_nil in *.
	rewrite <- admin_instrs_ok_eq in H3_comp0.
	apply Return_typing in H3_comp0; destruct H3_comp0 as [ts0 [ts' [? ?]]].
	unfold upd_label, set in H1. simpl in H1.
	apply Val_Const_list_typing in H3_comp.
	apply empty_append in H1_comp; destruct H1_comp.
	subst. simpl in *.
	


Admitted.

Lemma Step_pure__trap_vals_preserves : forall v_S v_C (v_val : (list val)) (v_instr : (list instr)) v_func_type,
	Admin_instrs_ok v_S v_C (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__TRAP )] (list__instr__admininstr v_instr))) v_func_type ->
	((v_val <> []) \/ (v_instr <> [])) ->
	Admin_instrs_ok v_S v_C [(admininstr__TRAP )] v_func_type.
Proof.
	move => v_S v_C v_val v_instr v_func_type HType H.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq.
	apply Admin_instr_ok__trap.
Qed.

Lemma Step_pure__trap_label_preserves : forall v_S v_C (v_n : n) (v_instr' : (list instr)) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__LABEL_ v_n v_instr' [(admininstr__TRAP )])] v_func_type ->
	Admin_instrs_ok v_S v_C [(admininstr__TRAP )] v_func_type.
Proof.
	move => v_S v_C n v_instr' v_func_type HType.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq.
	apply Admin_instr_ok__trap.
Qed.

Lemma Step_pure__trap_frame_preserves : forall v_S v_C (v_n : n) (v_f : frame) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__FRAME_ v_n v_f [(admininstr__TRAP )])] v_func_type ->
	Admin_instrs_ok v_S v_C [(admininstr__TRAP )] v_func_type.
Proof.
	intros.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq.
	apply Admin_instr_ok__trap.
Qed.

Lemma Step_pure__unop_val_preserves : forall v_S v_C (v_t : valtype) (v_c_1 : val_) (v_unop : unop_) (v_c : val_) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__UNOP v_t (v_unop : unop_))] v_func_type ->
	Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__UNOP v_t (v_unop : unop_))] [(admininstr__CONST v_t (v_c : val_))] ->
	Admin_instrs_ok v_S v_C [(admininstr__CONST v_t (v_c : val_))] v_func_type.
Proof.
	move => v_S v_C t v unop_op v_c tf HType HReduce.
	destruct tf as [tf1 tf2].
	rewrite -cat1s in HType; subst.
	apply admin_composition_typing_single in HType; destruct HType as [ts1 [ts2 [ts3 [ts4 [H1 [H3 [H4 H5]]]]]]].
	rewrite -> app_left_single_nil in H4; subst.
	apply admin_composition_typing_single in H4; destruct H4 as [ts5 [ts6 [ts7 [ts8 [H6 [H7 [H8 H9]]]]]]].
	apply AI_const_typing in H9.
	apply Unop_typing in H5; destruct H5 as [H10 [ts H11]]. 
	apply admin_empty in H8; subst.
	repeat rewrite app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (Admin_instrs_ok__seq v_S v_C [] (admininstr__CONST t v_c) [] [t] []). split.
	apply Admin_instrs_ok__empty.
	apply (Admin_instr_ok__instr v_S v_C (instr__CONST t v_c) (functype__ [] [t])).
	by apply Instr_ok__const.
Qed.

Lemma Step_pure__unop_trap_preserves : forall v_S v_C (v_t : valtype) (v_c_1 : val_) (v_unop : unop_) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__UNOP v_t (v_unop : unop_))] v_func_type ->
	Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__UNOP v_t (v_unop : unop_))] [(admininstr__TRAP )] ->
	Admin_instrs_ok v_S v_C [(admininstr__TRAP )] v_func_type.
Proof.
	move => v_S v_C v_t v_c_1 v_unop v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply (Admin_instrs_ok__seq v_S v_C [] (admininstr__TRAP) tf1 tf2 tf1).
	split.
	- (* Empty *) apply admin_weakening_empty_both. apply Admin_instrs_ok__empty.
	- (* TRAP *) apply Admin_instr_ok__trap.
Qed.


Lemma Step_pure__binop_val_preserves : forall v_S v_C (v_t : valtype) (v_c_1 : val_) (v_c_2 : val_) (v_binop : binop_) (v_c : val_) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__CONST v_t (v_c_2 : val_));(admininstr__BINOP v_t (v_binop : binop_))] v_func_type ->
	Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__CONST v_t (v_c_2 : val_));(admininstr__BINOP v_t (v_binop : binop_))] [(admininstr__CONST v_t (v_c : val_))] ->
	Admin_instrs_ok v_S v_C [(admininstr__CONST v_t (v_c : val_))] v_func_type.
Proof.
	move => v_S v_C v_t v_c_1 v_c_2 v_binop v_c v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_and_single H4_comp.
	apply_composition_typing_single H4_comp1.
	apply AI_const_typing in H4_comp0.
	apply AI_const_typing in H4_comp.
	apply Binop_typing in H4_comp2; destruct H4_comp2 as [H [ts H0]].
	subst.
	repeat rewrite -> app_assoc in H1_comp0.
	apply split_append_last in H1_comp0; destruct H1_comp0.
	rewrite H in H1_comp1.
	repeat rewrite -> app_assoc in H1_comp1.
	apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H1.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (Admin_instrs_ok__seq v_S v_C [] (admininstr__CONST v_t v_c) [] [v_t] []). split.
	apply Admin_instrs_ok__empty.
	apply (Admin_instr_ok__instr v_S v_C (instr__CONST v_t v_c) (functype__ [] [v_t])).
	by apply Instr_ok__const.
Qed.

Lemma Step_pure__binop_trap_preserves : forall v_S v_C (v_t : valtype) (v_c_1 : val_) (v_c_2 : val_) (v_binop : binop_) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__CONST v_t (v_c_2 : val_));(admininstr__BINOP v_t (v_binop : binop_))] v_func_type ->
	Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__CONST v_t (v_c_2 : val_));(admininstr__BINOP v_t (v_binop : binop_))] [(admininstr__TRAP )] ->
	Admin_instrs_ok v_S v_C [(admininstr__TRAP )] v_func_type.
Proof.
	move => v_S v_C v_t v_c_1 v_c_2 v_binop v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply (Admin_instrs_ok__seq v_S v_C [] (admininstr__TRAP) tf1 tf2 tf1).
	split.
	- (* Empty *) apply admin_weakening_empty_both. apply Admin_instrs_ok__empty.
	- (* TRAP *) apply Admin_instr_ok__trap.
Qed.



Lemma Step_pure__testop_preserves : forall v_S v_C (v_t : valtype) (v_c_1 : val_) (v_testop : testop_) (v_c : iN) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__TESTOP v_t (v_testop : testop_))] v_func_type ->
	Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__TESTOP v_t (v_testop : testop_))] [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_))] ->
	Admin_instrs_ok v_S v_C [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_))] v_func_type.
Proof.
	move => v_S v_C v_t v_c_1 v_testop v_c v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	apply AI_const_typing in H4_comp0.
	apply Testop_typing in H4_comp1; destruct H4_comp1 as [ts [H1 H2]]; subst.
	repeat rewrite -> app_assoc in H1_comp1. apply split_append_last in H1_comp1; destruct H1_comp1; subst.
	rewrite H.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (Admin_instrs_ok__seq v_S v_C [] (admininstr__CONST (valtype__INN inn__I32) v_c) [] [valtype__INN inn__I32] []). 
	split.
	- (* Empty *) apply Admin_instrs_ok__empty.
	- (* Const *) apply (Admin_instr_ok__instr v_S v_C (instr__CONST (valtype__INN inn__I32) v_c) (functype__ [] [valtype__INN inn__I32])).
		by apply Instr_ok__const.
Qed.

Lemma Step_pure__relop_preserves : forall v_S v_C (v_t : valtype) (v_c_1 : val_) (v_c_2 : val_) (v_relop : relop_) (v_c : iN) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__CONST v_t (v_c_2 : val_));(admininstr__RELOP v_t (v_relop : relop_))] v_func_type ->
	Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__CONST v_t (v_c_2 : val_));(admininstr__RELOP v_t (v_relop : relop_))] [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_))] ->
	Admin_instrs_ok v_S v_C [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_))] v_func_type.
Proof.
	move => v_S v_C v_t v_c_1 v_c_2 v_relop v_c v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_and_single H4_comp.
	apply_composition_typing_single H4_comp1.
	apply AI_const_typing in H4_comp0.
	apply AI_const_typing in H4_comp.
	apply Relop_typing in H4_comp2; destruct H4_comp2 as [ts [H1 H2]].
	subst.
	rewrite split_cons in H1_comp0.
	repeat rewrite -> app_assoc in H1_comp0; apply split_append_last in H1_comp0; destruct H1_comp0.
	rewrite H in H1_comp1.
	repeat rewrite -> app_assoc in H1_comp1; apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H1.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (Admin_instrs_ok__seq v_S v_C [] (admininstr__CONST (valtype__INN inn__I32) v_c) [] [valtype__INN inn__I32] []).
	split.
	- (* Empty *) apply Admin_instrs_ok__empty.
	- (* Const *) apply (Admin_instr_ok__instr v_S v_C (instr__CONST (valtype__INN inn__I32) v_c) (functype__ [] [valtype__INN inn__I32])).
	by apply Instr_ok__const.
Qed.

Lemma Step_pure__cvtop_val_preserves : forall v_S v_C (v_t_1 : valtype) (v_c_1 : val_) (v_t_2 : valtype) (v_cvtop : cvtop) (v_sx : (option sx)) (v_c : val_) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__CONST v_t_1 (v_c_1 : val_));(admininstr__CVTOP v_t_2 v_cvtop v_t_1 v_sx)] v_func_type ->
	Step_pure [(admininstr__CONST v_t_1 (v_c_1 : val_));(admininstr__CVTOP v_t_2 v_cvtop v_t_1 v_sx)] [(admininstr__CONST v_t_2 (v_c : val_))] ->
	Admin_instrs_ok v_S v_C [(admininstr__CONST v_t_2 (v_c : val_))] v_func_type.
Proof.
	move => v_S v_C v_t_1 v_c_1 v_t_2 v_cvtop v_sx v_c v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	apply AI_const_typing in H4_comp0.
	apply Cvtop_typing in H4_comp1; destruct H4_comp1 as [ts [H1 H2]].
	subst.
	repeat rewrite -> app_assoc in H1_comp1; apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	apply (Admin_instrs_ok__seq v_S v_C [] (admininstr__CONST v_t_2 v_c) [] [v_t_2] []).
	split.
	- (* Empty *) apply Admin_instrs_ok__empty.
	- (* Const *) apply (Admin_instr_ok__instr v_S v_C (instr__CONST v_t_2 v_c) (functype__ [] [v_t_2])).
	by apply Instr_ok__const.
Qed.

Lemma Step_pure__cvtop_trap_preserves : forall v_S v_C (v_t_1 : valtype) (v_c_1 : val_) (v_t_2 : valtype) (v_cvtop : cvtop) (v_sx : (option sx)) v_func_type,
	Admin_instrs_ok v_S v_C [(admininstr__CONST v_t_1 (v_c_1 : val_));(admininstr__CVTOP v_t_2 v_cvtop v_t_1 v_sx)] v_func_type ->
	Step_pure [(admininstr__CONST v_t_1 (v_c_1 : val_));(admininstr__CVTOP v_t_2 v_cvtop v_t_1 v_sx)] [(admininstr__TRAP )] ->
	Admin_instrs_ok v_S v_C [(admininstr__TRAP )] v_func_type.
Proof.
	move => v_S v_C v_t_1 v_c_1 v_t_2 v_cvtop v_sx v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply (Admin_instrs_ok__seq v_S v_C [] (admininstr__TRAP) tf1 tf2 tf1).
	split.
	- (* Empty *) apply admin_weakening_empty_both. apply Admin_instrs_ok__empty.
	- (* TRAP *) apply Admin_instr_ok__trap.
Qed.

Lemma Step_pure__local_tee_preserves : forall v_S v_C (v_val : val) (v_x : idx) v_func_type,
	Admin_instrs_ok v_S v_C [(v_val : admininstr);(admininstr__LOCAL_TEE v_x)] v_func_type ->
	Step_pure [(v_val : admininstr);(admininstr__LOCAL_TEE v_x)] [(v_val : admininstr);(v_val : admininstr);(admininstr__LOCAL_SET v_x)] ->
	Admin_instrs_ok v_S v_C [(v_val : admininstr);(v_val : admininstr);(admininstr__LOCAL_SET v_x)] v_func_type.
Proof.
	move => v_S v_C v_val v_x v_func_type HType HReduce.
	destruct v_func_type as [tf1 tf2].
	apply_composition_typing_and_single HType.
	apply_composition_typing_single H4_comp.
	induction v_val.
	apply AI_const_typing in H4_comp0.
	apply Local_tee_typing in H4_comp1; destruct H4_comp1 as [ts [t [H1 [H2 [H3 H4]]]]].
	subst.
	repeat rewrite -> app_assoc in H1_comp1; apply split_append_last in H1_comp1; destruct H1_comp1.
	rewrite H.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	unfold fun_coec_val__admininstr.
	rewrite <- H0.
	apply (Admin_instrs_ok__seq v_S v_C [admininstr__CONST v_valtype v_val_; admininstr__CONST v_valtype v_val_] 
		(admininstr__LOCAL_SET v_x) [] [v_valtype] ([v_valtype] ++ [v_valtype])).
	split.  
	apply (Admin_instrs_ok__seq v_S v_C [admininstr__CONST v_valtype v_val_] 
		(admininstr__CONST v_valtype v_val_) [] ([v_valtype] ++ [v_valtype]) [v_valtype]).
	split. 
	apply (Admin_instrs_ok__seq v_S v_C [] 
	(admininstr__CONST v_valtype v_val_) [] [v_valtype] []).
	split.
	- (* Empty *) apply Admin_instrs_ok__empty.
	- (* Const 1 *) apply (Admin_instr_ok__instr v_S v_C (instr__CONST v_valtype v_val_) (functype__ [] [v_valtype])).
		apply Instr_ok__const.
	- (* Const 2 *) apply admin_instr_weakening_empty_1. 
		apply (Admin_instr_ok__instr v_S v_C (instr__CONST v_valtype v_val_) (functype__ [] [v_valtype])).
		apply Instr_ok__const.
	- (* Set *) apply admin_instr_weakening_empty_2. 
		apply (Admin_instr_ok__instr v_S v_C (instr__LOCAL_SET v_x) (functype__ [v_valtype] [])).
		apply Instr_ok__local_set; split => //=.
Qed.

Lemma Step_read__block_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_t : (option valtype)) (v_instr : (list instr)) (v_n : n) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab)[(admininstr__BLOCK v_t v_instr)] v_func_type ->
	Module_instance_ok v_S (frame__MODULE r_v_f) v_C  ->
	v_z = state__ v_S r_v_f ->
	(((v_t = None) /\ (v_n = 0)) \/ ((v_t <> None) /\ (v_n = 1))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (frame__LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) [(admininstr__LABEL_ v_n [] (list__instr__admininstr v_instr))] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_t v_instr v_n v_func_type v_t1 lab ret HType HMinst HState H1 HValOK.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq in HType.
	apply Block_typing in HType; destruct HType as [ts [? [? ?]]]; subst. simpl in H2.
	rewrite <- admin_instrs_ok_eq.
	apply admin_instr_weakening_empty_1.
	apply Admin_instr_ok__label with (v_t_1 := v_t).
	split.
	apply instrs_weakening_empty_both. apply Instrs_ok__empty.
	apply Admin_instrs_ok__instrs with (v_S := v_S) in H2.
	apply H2.
Qed.

Lemma Step_read__loop_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_t : (option valtype)) (v_instr : (list instr)) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab)[(admininstr__LOOP v_t v_instr)] v_func_type ->
	Module_instance_ok v_S (frame__MODULE r_v_f) v_C  ->
	v_z = state__ v_S r_v_f ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (frame__LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) [(admininstr__LABEL_ 0 [(instr__LOOP v_t v_instr)] (list__instr__admininstr v_instr))] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_t v_instr v_func_type v_t1 lab ret HType HMinst H HValOK.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq in HType.
	apply Loop_typing in HType; destruct HType as [ts [? [? ?]]]; subst. simpl in H2.
	rewrite <- admin_instrs_ok_eq.
	apply admin_instr_weakening_empty_1.
	apply Admin_instr_ok__label with (v_t_1 := None).
	split.
	- simpl.
		rewrite app_left_single_nil.
		apply (Instrs_ok__seq _ [] (instr__LOOP v_t v_instr) [] v_t []); split.
		- apply Instrs_ok__empty.
		- apply Instr_ok__loop. apply H2. 
	- apply Admin_instrs_ok__instrs with (v_S := v_S) in H2.
		apply H2.
Qed.


Lemma Step_read__call_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_x : idx) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab)[(admininstr__CALL v_x)] v_func_type ->
	Module_instance_ok v_S (frame__MODULE r_v_f) v_C  ->
	v_z = state__ v_S r_v_f ->
	(v_x < (List.length (fun_funcaddr v_z)))%coq_nat ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (frame__LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) [(admininstr__CALL_ADDR (lookup_total (fun_funcaddr v_z) v_x))] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_x v_func_type v_t1 lab ret HType HMinst H H1 HValOK.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq in HType.
	apply Call_typing in HType; destruct HType as [ts [t1s' [t2s' [? [? [? ?]]]]]]; subst.
	simpl in *.
	apply Admin_instrs_ok__frame.
	rewrite <- admin_instrs_ok_eq.
	apply Admin_instr_ok__call_addr.
	inversion HMinst. decomp.
	simpl in *.
	rewrite <- H in H1. simpl in H1.
	apply Forall2_lookup in H10; destruct H10.
	apply H15 in H1.
	rewrite <- H5 in H2; simpl in H2.
	by rewrite H2 in H1.
Qed.

Lemma tc_func_reference2: forall v_S v_C v_minst idx tf v_type,
  lookup_total (moduleinst__TYPES v_minst) idx = funcinst__TYPE v_type ->
  Module_instance_ok v_S v_minst v_C ->
  lookup_total (context__TYPES v_C) idx = tf ->
  tf = funcinst__TYPE v_type.
Proof.
	move => v_S v_C v_minst idx tf v_type H HMinst H1.
	inversion HMinst. decomp.
	rewrite <- H3 in H.
	rewrite <- H4 in H1.
	simpl in *; subst; eauto.
Qed.


Lemma store_typed_exterval_types: forall v_S v_f v_a,
	(v_a < List.length (store__FUNCS v_S))%coq_nat ->
	lookup_total (store__FUNCS v_S) v_a = v_f ->
    Store_ok v_S ->
    Externvals_ok v_S (externval__FUNC v_a) (externtype__FUNC (funcinst__TYPE v_f)).
Proof.
	move => v_S v_f v_a HLength H HST.
	inversion HST; decomp.
	rewrite H5 in H.
	
	apply Forall2_lookup in H6; destruct H6.
	rewrite H5 in HLength.
	simpl in *.
	apply H10 in HLength as HFunc.
	inversion HFunc; decomp.
	simpl in *.
	apply Externvals_ok__func with (v_minst := v_moduleinst) (v_code_func := v_func); rewrite H5; split => //=; subst.
	rewrite <- H11. simpl => //=.
Qed.

Lemma Step_read__call_indirect_call_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : nat) (v_x : idx) (v_a : addr) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab)[(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CALL_INDIRECT v_x)] v_func_type ->
	Module_instance_ok v_S (frame__MODULE r_v_f) v_C  ->
	Store_ok v_S ->
	v_z = state__ v_S r_v_f ->
	(v_i < (List.length (tableinst__REFS (fun_table v_z 0))))%coq_nat ->
	(v_a < (List.length (fun_funcinst v_z)))%coq_nat ->
	((lookup_total (tableinst__REFS (fun_table v_z 0)) v_i) = (Some v_a)) ->
	((fun_type v_z v_x) = (funcinst__TYPE (lookup_total (fun_funcinst v_z) v_a))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (frame__LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) [(admininstr__CALL_ADDR v_a)] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_i v_x v_a v_func_type v_t1 lab ret HType HMinst HST H1 H2 H3 H4 H5 HValOK.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply AI_const_typing in H4_comp0.
	rewrite <- admin_instrs_ok_eq in H4_comp.
	apply Call_indirect_typing in H4_comp; destruct H4_comp as [tn [tm [ts [? [? [? ?]]]]]]; subst.
	repeat rewrite -> app_assoc in H1. apply split_append_last in H1; destruct H1.
	rewrite H1.
	repeat rewrite -> app_assoc.
	apply Admin_instrs_ok__frame.
	rewrite <- admin_instrs_ok_eq.
	apply Admin_instr_ok__call_addr.
	destruct v_C.
	destruct v_S.
	destruct r_v_f.
	destruct frame__MODULE0.
	unfold fun_table in H4.
	unfold fun_type in H5.
	unfold fun_table in H2.
	simpl in *.
	assert ((functype__ tn tm) = funcinst__TYPE (lookup_total store__FUNCS0 v_a)) as HFType; first by eapply tc_func_reference2; eauto.
	rewrite -> HFType.
	eapply store_typed_exterval_types; eauto.
Qed.

Lemma Step_read__call_indirect_trap_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : nat) (v_x : idx) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab)[(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CALL_INDIRECT v_x)] v_func_type ->
	Module_instance_ok v_S (frame__MODULE r_v_f) v_C  ->
	v_z = state__ v_S r_v_f ->
	(~(Step_read_before_Step_read__call_indirect_trap (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CALL_INDIRECT v_x)]))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (frame__LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) [(admininstr__TRAP )] v_func_type.
Proof.
	intros.
	destruct v_func_type.
	rewrite <- admin_instrs_ok_eq.
	apply Admin_instr_ok__trap.
Qed.

Lemma concat_cancel_last_n: forall (l1 l2 l3 l4: seq valtype),
    l1 ++ l2 = l3 ++ l4 ->
    length l2 = length l4 ->
    (l1 = l3) /\  (l2 = l4).
Proof.
  move => l1 l2 l3 l4 HCat HSize.
 
  assert (length (l1 ++ l2) = length (l3 ++ l4)); first by rewrite HCat.
  repeat rewrite app_length in H.
  rewrite HSize in H. 
Admitted.

Lemma typeof_default_inverse: forall (v_t : list valtype),
	List.map typeof (List.map [eta fun_default_] v_t) = v_t.
Proof.
	move => v_t.
	induction v_t => //=.
	f_equal.
	destruct a.
	- destruct v_inn => //=.
	- destruct v_fnn => //=.
	apply IHv_t.
Qed.

Lemma Step_read__call_addr_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_val : (list val)) (v_k : nat) (v_a : addr) (v_n : n) (v_f : frame) (v_instr : (list instr)) (v_t_1 : (list valtype)) (v_t_2 : resulttype) (v_mm : moduleinst) (v_func : func) (v_x : idx) (v_t : (list valtype)) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab)(@app _ (list__val__admininstr v_val) [(admininstr__CALL_ADDR v_a)]) v_func_type ->
	Module_instance_ok v_S (frame__MODULE r_v_f) v_C  ->
	Store_ok v_S -> 
	Datatypes.length v_val = Datatypes.length v_t_1 -> 
	v_z = state__ v_S r_v_f ->
	(v_a < (List.length (fun_funcinst v_z)))%coq_nat ->
	((lookup_total (fun_funcinst v_z) v_a) = {| funcinst__TYPE := (functype__ v_t_1 v_t_2); funcinst__MODULE := v_mm; funcinst__CODE := v_func |}) ->
	(v_func = (func__FUNC v_x (List.map (fun v_t => (local__LOCAL v_t)) (v_t)) v_instr)) ->
	(v_f = {| frame__LOCALS := (@app _ v_val (List.map (fun v_t => (fun_default_ v_t)) (v_t))); frame__MODULE := v_mm |}) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (frame__LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) [(admininstr__FRAME_ v_n v_f [(admininstr__LABEL_ v_n [] (list__instr__admininstr v_instr))])] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_val v_k v_a v_n v_f v_instr v_t_1 v_t_2 v_mm v_func v_x v_t v_func_type v_t1 lab ret HType HMinst H1 H2 H3 H4 H5 H6 H7 H8.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_single HType.
	apply Val_Const_list_typing in H3_comp.
	rewrite -> H3 in H4. simpl in H4.
	rewrite -> H3 in H5. simpl in H5.
	eapply CALL_ADDR_invoke_typing with (v_t_1 := v_t_1) (v_t_2 := v_t_2) (v_mm := v_mm) in H4_comp; eauto;
	try apply H5. 
	destruct H4_comp as [ts' [C' [? [? [??]]]]].
	subst.
	apply concat_cancel_last_n in H; last by (repeat rewrite length_is_size in H2; rewrite List.map_length).
	destruct H; subst.
	repeat rewrite -> app_assoc.
	apply admin_instrs_weakening_empty_1.
	rewrite <- admin_instrs_ok_eq.
	apply Admin_instr_ok__frame.
	eapply Thread_ok__. split. 
	apply Frame_ok__ with (v_t := ((List.map typeof v_val) ++ v_t)). repeat split => //=.
	repeat rewrite -> List.app_length.
	repeat rewrite -> List.map_length => //=.
	apply H9.
	apply Forall2_Val_ok_is_same_as_map.
	rewrite List.map_app.
	rewrite List.app_inv_head_iff.
	apply typeof_default_inverse.
	rewrite <- admin_instrs_ok_eq.
	apply Admin_instr_ok__label with (v_t_1 := v_t_2); split.
	- apply instrs_weakening_empty_both. apply Instrs_ok__empty.
	- rewrite fold_append. simpl.
		repeat rewrite _append_option_none_left.
		apply Admin_instrs_ok__instrs.
		apply H10.
Qed.


Lemma Step_read__local_get_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_x : idx) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab)[(admininstr__LOCAL_GET v_x)] v_func_type ->
	Module_instance_ok v_S (frame__MODULE r_v_f) v_C  ->
	v_z = state__ v_S r_v_f ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (frame__LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) [((fun_local v_z v_x) : admininstr)] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_x v_func_type v_t1 lab ret HType HMinst H1 HValOK.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq.
	rewrite <- admin_instrs_ok_eq in HType.
	apply Get_local_typing in HType; destruct HType as [t [? [? ?]]]. 
	simpl in *.
	subst.
	apply admin_instr_weakening_empty_1.
	unfold fun_local.
	apply inst_t_context_local_empty in HMinst.
	rewrite HMinst in H2.
	rewrite HMinst.
	apply Forall2_lookup in HValOK; destruct HValOK.
	rewrite <- app_right_nil in H2.
	rewrite <- app_right_nil.
	apply H0 in H2. 
	inversion H2.
	apply (Admin_instr_ok__instr v_S (upd_label (upd_local_return v_C v_t1 ret) lab) (instr__CONST (lookup_total v_t1 v_x) v_c_t) (functype__ [] [(lookup_total v_t1 v_x)])).
	apply Instr_ok__const.
Qed.

Lemma global_type_reference: forall v_S v_i v_x v_C mut v t,
    Module_instance_ok v_S v_i v_C ->
	(v_x < Datatypes.length (context__GLOBALS v_C))%coq_nat -> 
    (globalinst__VALUE (lookup_total (store__GLOBALS v_S) (lookup_total (moduleinst__GLOBALS v_i) v_x))) = v ->
    lookup_total (context__GLOBALS v_C) v_x = globaltype__ mut t ->
    exists v_val_, typeof v = t /\ v = val__CONST t v_val_.
Proof.
	move => v_S i v_x v_C mut v t HMinst HLength HVal HTypeLookup.
	inversion HMinst; decomp; subst.
	simpl in *.
	apply Forall2_lookup2 in H9; destruct H9.
	apply H1 in HLength.
	inversion HLength; destruct H13.
	rewrite H14.
	simpl.
	rewrite HTypeLookup in H12. injection H12 as ?; eauto.
	exists v_val_.
	split => //=.
	f_equal => //=.
Qed.

Lemma Step_read__global_get_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_x : idx) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab)[(admininstr__GLOBAL_GET v_x)] v_func_type ->
	Module_instance_ok v_S (frame__MODULE r_v_f) v_C  ->
	v_z = state__ v_S r_v_f ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (frame__LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) [((globalinst__VALUE (fun_global v_z v_x)) : admininstr)] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_x v_func_type v_t1 lab ret HType HMinst H HValOK.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq in HType.
	rewrite <- admin_instrs_ok_eq.
	apply Get_global_typing in HType; destruct HType as [mut [t [? [? ?]]]].
	simpl in *.
	subst.
	unfold fun_global.

	remember ((globalinst__VALUE
	(lookup_total (store__GLOBALS v_S)
	   (lookup_total (moduleinst__GLOBALS (frame__MODULE r_v_f)) v_x)))) as v.
	eapply global_type_reference in HMinst; eauto; destruct HMinst as [v_val_ [? ?]].
	rewrite H1 in Heqv.
	apply admin_instr_weakening_empty_1.
	rewrite Heqv.
	eapply (Admin_instr_ok__instr v_S _ (instr__CONST t v_val_) (functype__ [] [t])).
	apply Instr_ok__const.
Qed.

Lemma Step_read__load_num_trap_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : nat) (v_t : valtype) (v_mo : memop) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab)[(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__LOAD_ v_t None v_mo)] v_func_type ->
	Module_instance_ok v_S (frame__MODULE r_v_f) v_C  ->
	v_z = state__ v_S r_v_f ->
	(((v_i + (memop__OFFSET v_mo)) + ((fun_size v_t) / 8)) > (List.length (meminst__BYTES (fun_mem v_z 0))))%coq_nat ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (frame__LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) [(admininstr__TRAP )] v_func_type.
Proof.
	intros.
	destruct v_func_type.
	rewrite <- admin_instrs_ok_eq.
	apply Admin_instr_ok__trap.
Qed.

Lemma Step_read__load_num_val_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : nat) (v_t : valtype) (v_mo : memop) (v_c : val_) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab)[(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__LOAD_ v_t None v_mo)] v_func_type ->
	Module_instance_ok v_S (frame__MODULE r_v_f) v_C  ->
	v_z = state__ v_S r_v_f ->
	((fun_bytes v_t (v_c : val_)) = (list_slice (meminst__BYTES (fun_mem v_z 0)) (v_i + (memop__OFFSET v_mo)) ((fun_size v_t) / 8))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (frame__LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) [(admininstr__CONST v_t (v_c : val_))] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_i v_t v_mo v_c v_func_type v_t1 lab ret HType HMinst HState H HValOK.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply AI_const_typing in H4_comp0.
	rewrite <- admin_instrs_ok_eq.
	rewrite <- admin_instrs_ok_eq in H4_comp.
	apply Load_typing in H4_comp; destruct H4_comp as [ts [v_n [v_sx [v_inn [v_mt [? [? [? [? [? [? [? [??]]]]]]]]]]]]].
	subst.
	repeat rewrite -> app_assoc in H0; apply split_append_last in H0; destruct H0.
	subst.
	repeat rewrite -> app_assoc.
	apply admin_instr_weakening_empty_1.
	eapply (Admin_instr_ok__instr v_S _ (instr__CONST v_t v_c) (functype__ [] [v_t])).
	apply Instr_ok__const.
Qed.

Lemma Step_read__load_pack_trap_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : nat) (v_inn : inn) (v_n : n) (v_sx : sx) (v_mo : memop) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab)[(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__LOAD_ (valtype__INN v_inn) (Some ((packsize__ v_n), v_sx)) v_mo)] v_func_type ->
	Module_instance_ok v_S (frame__MODULE r_v_f) v_C  ->
	v_z = state__ v_S r_v_f ->
	(((v_i + (memop__OFFSET v_mo)) + (v_n / 8)) > (List.length (meminst__BYTES (fun_mem v_z 0))))%coq_nat ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (frame__LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) [(admininstr__TRAP )] v_func_type.
Proof.
	intros.
	destruct v_func_type.
	rewrite <- admin_instrs_ok_eq.
	apply Admin_instr_ok__trap.
Qed.

Lemma Step_read__load_pack_val_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_i : nat) (v_inn : inn) (v_n : n) (v_sx : sx) (v_mo : memop) (v_c : iN) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab)[(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__LOAD_ (valtype__INN v_inn) (Some ((packsize__ v_n), v_sx)) v_mo)] v_func_type ->
	Module_instance_ok v_S (frame__MODULE r_v_f) v_C  ->
	v_z = state__ v_S r_v_f ->
	((fun_ibytes v_n v_c) = (list_slice (meminst__BYTES (fun_mem v_z 0)) (v_i + (memop__OFFSET v_mo)) (v_n / 8))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (frame__LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) [(admininstr__CONST (valtype__INN v_inn) (fun_ext v_n (fun_size (valtype__INN v_inn)) v_sx v_c))] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_i v_inn v_n v_sx v_mo v_c v_func_type v_t1 lab ret HType HMinst HState H HValOK.
	destruct v_func_type as [ts1 ts2].
	apply_composition_typing_and_single HType.
	apply AI_const_typing in H4_comp0.
	rewrite <- admin_instrs_ok_eq.
	rewrite <- admin_instrs_ok_eq in H4_comp.
	apply Load_typing in H4_comp; destruct H4_comp as [ts [v_n' [v_sx' [v_inn' [v_mt [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]].
	subst.
	repeat rewrite -> app_assoc in H0; apply split_append_last in H0; destruct H0.
	subst.
	repeat rewrite -> app_assoc.
	apply admin_instr_weakening_empty_1.
	eapply (Admin_instr_ok__instr v_S _ (instr__CONST (valtype__INN v_inn) ((fun_ext v_n (fun_size (valtype__INN v_inn)) v_sx v_c))) (functype__ [] [(valtype__INN v_inn)])).
	apply Instr_ok__const.
Qed.

Lemma Step_read__memory_size_preserves : forall v_S (r_v_f : frame) v_C (v_z : state) (v_n : n) v_func_type v_t1 lab ret ,
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab)[(admininstr__MEMORY_SIZE )] v_func_type ->
	Module_instance_ok v_S (frame__MODULE r_v_f) v_C  ->
	v_z = state__ v_S r_v_f ->
	(((v_n * 64) * (fun_Ki )) = (List.length (meminst__BYTES (fun_mem v_z 0)))) ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (frame__LOCALS r_v_f) ->
	Admin_instrs_ok v_S (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) [(admininstr__CONST (valtype__INN (inn__I32 )) (v_n : val_))] v_func_type.
Proof.
	move => v_S r_v_f v_C v_z v_n v_func_type v_t1 lab ret HType HMinst HState HLength HValOK.
	destruct v_func_type as [ts1 ts2].
	rewrite <- admin_instrs_ok_eq.
	rewrite <- admin_instrs_ok_eq in HType.
	apply Memory_size_typing in HType; destruct HType as [v_mt [? [? ?]]].
	subst.
	apply admin_instr_weakening_empty_1.
	eapply (Admin_instr_ok__instr v_S _ (instr__CONST (valtype__INN inn__I32) v_n) (functype__ [] [(valtype__INN inn__I32)])).
	apply Instr_ok__const.
Qed.

Lemma func_extension_same: forall f,
	Forall2 (fun v s => Func_extension v s) f f.
Proof.
	move => f.
	induction f => //.
	apply Forall2_cons_iff. split.
	- apply Func_extension__.
	- apply IHf.
Qed.

Lemma table_extension_same: forall t,
	Forall2 (fun v s => Table_extension v s) t t.
Proof.
	move => t.
	induction t => //.
	apply Forall2_cons_iff. split.
	- induction a. induction tableinst__TYPE0. apply Table_extension__ => //.
	- apply IHt.
Qed.

Lemma mem_extension_same: forall m,
	Forall2 (fun v s => Mem_extension v s) m m.
Proof.
	move => m.
	induction m => //.
	apply Forall2_cons_iff. split.
	- induction a. induction meminst__TYPE0. apply Mem_extension__ => //.
	- apply IHm.
Qed.

Lemma global_extension_same: forall g,
	Forall2 (fun v s => Global_extension v s) g g.
Proof.
	move => g.
	induction g => //.
	apply Forall2_cons_iff. split.
	- destruct a. destruct globalinst__TYPE0. destruct globalinst__VALUE0. apply Global_extension__. right => //.
	- apply IHg.
Qed.

Lemma store_extension_same: forall s,
    Store_extension s s.
Proof.
  move => s. 
  apply (Store_extension__ s s (store__FUNCS s) (store__TABLES s) (store__MEMS s) (store__GLOBALS s) (store__FUNCS s) [] (store__TABLES s) [] (store__MEMS s) [] (store__GLOBALS s) []).
  repeat (split => //; try rewrite -> app_nil_r).
  + by apply func_extension_same.
  + by apply table_extension_same.
  + by apply mem_extension_same.
  + by apply global_extension_same.
Qed.

Lemma config_same: forall s f ais s' f' ais',
	(config__ (state__ s f) ais) = (config__ (state__ s' f') ais') ->
	s = s' /\ f = f' /\ ais = ais'.
Proof.
	move => s f ais s' f' ais' H.
	injection H as H1 => //=.
Qed.

Lemma config_same2: forall s f ais s' f' ais',
	s = s' /\ f = f' /\ ais = ais' ->
 	(config__ (state__ s f) ais) = (config__ (state__ s' f') ais').
Proof.
	move => s f ais s' f' ais' [? [? ?]].
	f_equal => //=. f_equal => //=.
Qed.

Lemma Forall2_global: forall v_S v_idx v_val_0 v_valtype v_val_,
	(v_idx < length (store__GLOBALS v_S))%coq_nat ->
	lookup_total (store__GLOBALS v_S) v_idx = 
	{| globalinst__TYPE := globaltype__ (mut__MUT (Some tt)) v_valtype; globalinst__VALUE := val__CONST v_valtype v_val_0|} ->
	Forall2 (fun v s => Global_extension v s) (store__GLOBALS v_S) (list_update_func (store__GLOBALS v_S) v_idx 
		(fun g => g <| globalinst__VALUE := (val__CONST v_valtype v_val_) |> )).
Proof.
	move => v_S v_idx v_val0 v_valtype v_val_.
	destruct v_S; simpl.
	move: v_idx.
	induction store__GLOBALS0; move => v_idx H H2 => //=.
	destruct v_idx => //=.
	apply Forall2_cons_iff. unfold lookup_total in H2; simpl in H2; subst. split.
	- unfold set. simpl. apply Global_extension__. left => //. by eapply global_extension_same.
	- apply Forall2_cons. 
		- destruct a. destruct globalinst__TYPE0. destruct globalinst__VALUE0. apply Global_extension__. right => //.
		- unfold lookup_total in H2. simpl in H2. eapply IHstore__GLOBALS0 => //=. simpl in H. apply Nat.succ_lt_mono in H. apply H.
Qed.

Ltac removeinst2 H :=
	let H1 := fresh "HLength" in
	eapply length_app_both_nil in H as H1; eauto;
	rewrite H1 in H; rewrite <- app_right_nil in H.

Lemma update_global_unchagned: forall v_S v_S' v_f v_x v_valtype v_val_,
	v_S' =
	v_S <| store__GLOBALS :=
	list_update_func (store__GLOBALS v_S)
	(lookup_total (moduleinst__GLOBALS (frame__MODULE v_f)) v_x)
	[eta set globalinst__VALUE (fun=> val__CONST v_valtype v_val_)] |> ->
	store__FUNCS v_S = store__FUNCS v_S' /\
	store__TABLES v_S = store__TABLES v_S' /\
	length (store__GLOBALS v_S) = length (store__GLOBALS v_S') /\
	store__MEMS v_S = store__MEMS v_S'.
Proof. 
	move => v_S v_S' v_f v_x v_valtype v_val' H.
	destruct v_S'. unfold set in H. simpl in *.
	injection H as ?; subst; repeat split => //=.
	by erewrite <- list_update_length_func.
Qed.

Lemma func_agree_extension: forall v_S v_S' v_funcaddr v_funcinst_1' v_funcinst_2 v_functype,
	Externvals_ok v_S (externval__FUNC v_funcaddr) (externtype__FUNC v_functype) ->
	length (store__FUNCS v_S) = length v_funcinst_1' ->
	store__FUNCS v_S' = (v_funcinst_1' ++ v_funcinst_2)%list -> 
    Forall2 (fun v s => Func_extension v s) (store__FUNCS v_S) v_funcinst_1' ->
    Externvals_ok v_S' (externval__FUNC v_funcaddr) (externtype__FUNC v_functype).
Proof.
	move => v_S v_S' v_funcaddr v_funcinst_1' v_funcinst_2 v_functype HOk HLength HApp Hext.
	inversion HOk; destruct H2; subst.
	apply Forall2_nth in Hext; destruct Hext.
	apply (H0 _ default_val default_val) in H2 as H2'.
	unfold lookup_total in H3.
	apply (Externvals_ok__func _ _ _ v_minst v_code_func).
	apply (length_app_lt) with (l':=(store__FUNCS v_S')) (l2':= v_funcinst_2) in HLength => //=.
	split. 
	- apply (Nat.lt_le_trans _ _ _ H2 HLength).
	- unfold lookup_total.
		rewrite H in H2.
		apply app_nth1 with (l' := v_funcinst_2) (d := default_val) in H2.
		rewrite <- HApp in H2.
		destruct default_val.
		inversion H2'.
		rewrite H2. 
		rewrite <- H5.
		apply H3.
Qed.

Lemma table_agree_extension: forall v_S v_S' v_tableaddr v_tableinst_1' v_tableinst_2 v_tabletype,
    Externvals_ok v_S (externval__TABLE v_tableaddr) (externtype__TABLE v_tabletype) ->
	length (store__TABLES v_S) = length v_tableinst_1' ->
	store__TABLES v_S' = (v_tableinst_1' ++ v_tableinst_2) -> 
	Forall2 (fun v s => Table_extension v s) (store__TABLES v_S) v_tableinst_1' ->
    Externvals_ok v_S' (externval__TABLE v_tableaddr) (externtype__TABLE v_tabletype).
Proof.
	move => v_S v_S' v_tableaddr v_tableinst_1' v_tableinst_2 v_tabletype HOk HLength HApp Hext.
	inversion HOk; destruct H2; subst; destruct H3.
	apply Forall2_lookup in Hext; destruct Hext.
	apply H3 in H2 as H2'.
	inversion H2'. 
	eapply Externvals_ok__table.
	apply (length_app_lt) with (l':=(store__TABLES v_S')) (l2':= v_tableinst_2) in HLength => //=.
	split.
	- apply (Nat.lt_le_trans _ _ _ H2 HLength).
	-  
		rewrite H1 in H2.
		apply lookup_app with (l' := v_tableinst_2) in H2.
		rewrite <- HApp in H2.
		rewrite <- H2.
		rewrite <- H5. split => //=.
		rewrite <- H4 in H.
		injection H as ?.
		inversion H0. inversion H8. destruct H11.
		subst.
		injection H12 as ?.
		apply Tabletype_sub__.
		apply Limits_sub__.
		subst.
		unfold ge in H11. split.
		unfold ge.
		eapply Nat.le_trans; eauto.
		apply H14.
Qed.

Lemma global_agree_extension: forall v_S v_S' v_globaladdr v_globalinst_1' v_globalinst_2 v_globaltype,
    Externvals_ok v_S (externval__GLOBAL v_globaladdr) (externtype__GLOBAL v_globaltype) ->
	length (store__GLOBALS v_S) = length v_globalinst_1' ->
	store__GLOBALS v_S' = (v_globalinst_1' ++ v_globalinst_2) -> 
	Forall2 (fun v s => Global_extension v s) (store__GLOBALS v_S) v_globalinst_1' ->
    Externvals_ok v_S' (externval__GLOBAL v_globaladdr) (externtype__GLOBAL v_globaltype).
Proof.
	move => v_S v_S' v_globaladdr v_globalinst_1' v_globalinst_2 v_globaltype HOk HLength HApp Hext.
	inversion HOk; destruct H2; subst.
	apply Forall2_lookup in Hext; destruct Hext.
	apply H0 in H2 as H2'.
	inversion H2'.
	eapply Externvals_ok__global with (v_val_ := v_c2).
	apply (length_app_lt) with (l':=(store__GLOBALS v_S')) (l2':= v_globalinst_2) in HLength => //=.
	split.
	- apply (Nat.lt_le_trans _ _ _ H2 HLength).
	- 
		rewrite H in H2.
		apply lookup_app with (l' := v_globalinst_2) in H2.
		rewrite <- HApp in H2.
		rewrite <- H2.
		rewrite <- H1 in H3.
		injection H3 as ?.
		subst => //=.
Qed.

Lemma mem_agree_extension: forall v_S v_S' v_memaddr v_meminst_1' v_meminst_2 v_memtype,
    Externvals_ok v_S (externval__MEM v_memaddr) (externtype__MEM v_memtype) ->
	length (store__MEMS v_S) = length v_meminst_1' ->
	store__MEMS v_S' = (v_meminst_1' ++ v_meminst_2) -> 
	Forall2 (fun v s => Mem_extension v s) (store__MEMS v_S) v_meminst_1' ->
    Externvals_ok v_S' (externval__MEM v_memaddr) (externtype__MEM v_memtype).
Proof.
	move => v_S v_S' v_memaddr v_meminst_1' v_meminst_2 v_memtype HOk HLength HApp Hext.
	inversion HOk; destruct H2; subst; destruct H3 as [? ?].
	apply Forall2_lookup in Hext; destruct Hext.
	apply H3 in H2 as H2'.
	inversion H2'. 
	eapply Externvals_ok__mem.
	apply (length_app_lt) with (l':=(store__MEMS v_S')) (l2':= v_meminst_2) in HLength => //=.
	split.
	- apply (Nat.lt_le_trans _ _ _ H2 HLength).
	-  
		rewrite H1 in H2.
		apply lookup_app with (l' := v_meminst_2) in H2.
		rewrite <- HApp in H2.
		rewrite <- H2.
		rewrite <- H5. repeat split => //=. 
		rewrite <- H4 in H.
		injection H as ?.
		inversion H0. inversion H8. destruct H11.
		subst.
		injection H12 as ?.
		apply Limits_sub__.
		subst.
		unfold ge in H11. split.
		unfold ge.
		eapply Nat.le_trans; eauto.
		apply H14.
Qed.


Lemma func_extension_C: forall v_S v_S' v_funcaddrs v_funcinst_1' v_funcinst_2 tcf,
    Forall2 (fun v s => Externvals_ok v_S (externval__FUNC v) (externtype__FUNC s)) v_funcaddrs tcf ->
	length (store__FUNCS v_S) = length v_funcinst_1' ->
	store__FUNCS v_S' = (v_funcinst_1' ++ v_funcinst_2)%list -> 
	Forall2 (fun v s => Func_extension v s) (store__FUNCS v_S) v_funcinst_1' ->
    Forall2 (fun v s => Externvals_ok v_S' (externval__FUNC v) (externtype__FUNC s)) v_funcaddrs tcf.
Proof.
	move => v_S v_S' v_funcaddrs v_funcinst_1' v_funcinst_2.
	move: v_S v_S'.
	induction v_funcaddrs;
	move => v_S v_S' tcf HOk Hlength HApp Hext => //=; destruct tcf => //=; simpl in HOk; try (apply Forall2_length in HOk; discriminate).
	subst.
	apply Forall2_cons_iff. split.
	- inversion HOk; subst. apply (func_agree_extension v_S) with (v_funcinst_1' := v_funcinst_1') (v_funcinst_2 := v_funcinst_2) => //.
	- eapply IHv_funcaddrs. inversion HOk. apply H4. apply Hlength. apply HApp. apply Hext.
Qed. 	

Lemma table_extension_C: forall v_S v_S' v_tableaddrs v_tableinst_1' v_tableinst_2 tcf,
    Forall2 (fun v s => Externvals_ok v_S (externval__TABLE v) (externtype__TABLE s)) v_tableaddrs tcf ->
	length (store__TABLES v_S) = length v_tableinst_1' ->
	store__TABLES v_S' = (v_tableinst_1' ++ v_tableinst_2)%list -> 
	Forall2 (fun v s => Table_extension v s) (store__TABLES v_S) v_tableinst_1' ->
    Forall2 (fun v s => Externvals_ok v_S' (externval__TABLE v) (externtype__TABLE s)) v_tableaddrs tcf.
Proof.
	move => v_S v_S' v_tableaddrs v_tableinst_1' v_tableinst_2.
	move: v_S v_S'.
	induction v_tableaddrs;
	move => v_S v_S' tcf HOk Hlength HApp Hext => //=; destruct tcf => //=; simpl in HOk; try (apply Forall2_length in HOk; discriminate).
	subst.
	apply Forall2_cons_iff. split.
	- inversion HOk; subst. apply (table_agree_extension v_S) with (v_tableinst_1' := v_tableinst_1') (v_tableinst_2 := v_tableinst_2) => //.
	- eapply IHv_tableaddrs. inversion HOk. apply H4. apply Hlength. apply HApp. apply Hext.
Qed. 	

Lemma global_extension_C: forall v_S v_S' v_globaladdrs v_globalinst_1' v_globalinst_2 tcf,
    Forall2 (fun v s => Externvals_ok v_S (externval__GLOBAL v) (externtype__GLOBAL s)) v_globaladdrs tcf ->
	length (store__GLOBALS v_S) = length v_globalinst_1' ->
	store__GLOBALS v_S' = (v_globalinst_1' ++ v_globalinst_2)%list -> 
	Forall2 (fun v s => Global_extension v s) (store__GLOBALS v_S) v_globalinst_1' ->
    Forall2 (fun v s => Externvals_ok v_S' (externval__GLOBAL v) (externtype__GLOBAL s)) v_globaladdrs tcf.
Proof.
	move => v_S v_S' v_globaladdrs v_globalinst_1' v_globalinst_2.
	move: v_S v_S'.
	induction v_globaladdrs;
	move => v_S v_S' tcf HOk Hlength HApp Hext => //=; destruct tcf => //=; simpl in HOk; try (apply Forall2_length in HOk; discriminate).
	subst.
	apply Forall2_cons_iff. split.
	- inversion HOk; subst. apply (global_agree_extension v_S) with (v_globalinst_1' := v_globalinst_1') (v_globalinst_2 := v_globalinst_2) => //.
	- eapply IHv_globaladdrs. inversion HOk. apply H4. apply Hlength. apply HApp. apply Hext.
Qed.


Lemma mem_extension_C: forall v_S v_S' v_memaddrs v_meminst_1' v_meminst_2 tcf,
	Forall2 (fun v s => Externvals_ok v_S (externval__MEM v) (externtype__MEM s)) v_memaddrs tcf ->
	length (store__MEMS v_S) = length v_meminst_1' ->
	store__MEMS v_S' = (v_meminst_1' ++ v_meminst_2)%list -> 
	Forall2 (fun v s => Mem_extension v s) (store__MEMS v_S) v_meminst_1' ->
    Forall2 (fun v s => Externvals_ok v_S' (externval__MEM v) (externtype__MEM s)) v_memaddrs tcf.
Proof.
	move => v_S v_S' v_memaddrs v_meminst_1' v_meminst_2.
	move: v_S v_S'.
	induction v_memaddrs;
	move => v_S v_S' tcf HOk Hlength HApp Hext => //=; destruct tcf => //=; simpl in HOk; try (apply Forall2_length in HOk; discriminate).
	subst.
	apply Forall2_cons_iff. split.
	- inversion HOk; subst. apply (mem_agree_extension v_S) with (v_meminst_1' := v_meminst_1') (v_meminst_2 := v_meminst_2) => //.
	- eapply IHv_memaddrs. inversion HOk. apply H4. apply Hlength. apply HApp. apply Hext.
Qed.

Lemma ext_extension_C: forall v_S v_S' v_exportinst,
	Store_extension v_S v_S' ->
	Forall (Export_instance_ok v_S) v_exportinst -> 
	Forall (Export_instance_ok v_S') v_exportinst.
Proof.
	move => v_S v_S' v_exportinst.
	move: v_S v_S'.
	induction v_exportinst;
	move => v_S v_S' Hext HOk => //=.
	subst. inversion HOk. 
	apply Forall_cons_iff. split.
	-	inversion H1.
		subst.
		eapply Export_instance_ok__OK with (v_ext := v_ext).
		inversion Hext; decomp. 
		inversion H3; subst; destruct H20.
		- eapply func_agree_extension; eauto.
		- eapply table_agree_extension; eauto.
		- eapply mem_agree_extension; eauto.
		- eapply global_agree_extension; eauto.
	- eapply IHv_exportinst; eauto.
Qed.

Lemma module_inst_typing_extension: forall v_S v_S' v_i v_C,
    Store_extension v_S v_S' ->
    Module_instance_ok v_S v_i v_C ->
    Module_instance_ok v_S' v_i v_C.
Proof.
	move => v_S v_S' v_i v_C HStoreExtension HMIT.
	inversion HStoreExtension. 
	inversion HMIT; decomp.
	subst.
	apply Module_instance_ok__; repeat split => //=.
	- eapply func_extension_C; eauto.
	- eapply table_extension_C; eauto.
	- eapply global_extension_C ; eauto.
	- eapply mem_extension_C; eauto.
	- eapply ext_extension_C; eauto.
Qed.

Lemma store_global_extension_store_typed: forall s s' v_f v_C v_valtype v_val_ v_x,
    Store_ok s ->
    Store_extension s s' ->
	Module_instance_ok s (frame__MODULE v_f) v_C ->
	Module_instance_ok s' (frame__MODULE v_f) v_C ->
	(store__GLOBALS s') = list_update_func (store__GLOBALS s)
	(lookup_total (moduleinst__GLOBALS (frame__MODULE v_f)) v_x)
	[eta set globalinst__VALUE (fun=> val__CONST v_valtype v_val_)] ->
	Datatypes.length (store__GLOBALS s) = Datatypes.length (store__GLOBALS s') ->
    (store__FUNCS s = store__FUNCS s') ->
    (store__TABLES s = store__TABLES s') ->
    (store__MEMS s = store__MEMS s') ->
    Store_ok s'.
Proof.
	move => s s' f C v_valtype v_val_ v_x HSOK Hext HIT HITS' HUpdate HLGlobal HFeq HTeq HMeq.
	inversion HSOK; decomp.
	inversion Hext; decomp; subst.
	destruct s'.
	apply f_equal with (f := fun t => List.length t) in HMeq as ?.
	apply f_equal with (f := fun t => List.length t) in HTeq as ?.
	apply f_equal with (f := fun t => List.length t) in HFeq as ?.
	removeinst2 H22. 
	removeinst2 H20.
	removeinst2 H19.
	removeinst2 H21. subst.
	simpl in *.
	eapply Store_ok__OK with (v_funcinst := v_funcinst) (v_functype := v_functype)
		(v_tableinst := v_tableinst) (v_tabletype := v_tabletype)
		(v_meminst := v_meminst) (v_memtype := v_memtype)
		(v_globalinst := store__GLOBALS0) (v_globaltype := v_globaltype); subst; repeat split => //=.
	- rewrite HLGlobal in H1 => //=. 
	- f_equal => //=.
	- apply Forall2_forall2; split => //=. move => x y HIn.
		apply Forall2_forall2 in H5; destruct H5. apply H11 in HIn. inversion HIn; destruct H15 as [? [? ?]].
		eapply Function_instance_ok__ with (v_C := v_C); repeat split => //=.
		eapply module_inst_typing_extension; eauto.
	- apply Forall2_forall2; split => //.
		- by rewrite <- H1.
		- move => x y HIn. apply In2_split in HIn. destruct HIn.
		eapply Forall2_forall2weak2 with (y := y) in H6 => //=; destruct H6 as [x' ?].
		inversion H6; decomp; subst.
		

	
	
Admitted.

Lemma list_update_same_unchanged: forall {X : Type} {Y : Inhabited X} (l: list X) e i,
    (lookup_total l i) = e ->
	(i < length l)%coq_nat ->
    list_update l i e = l.
Proof.
	move => X Y l e i.
	generalize dependent l. generalize dependent e.
	induction i; move => e l HLookup HLT.
	- destruct l => //=. by f_equal.
	- destruct l => //=.
		f_equal. apply IHi. unfold lookup_total. unfold lookup_total in HLookup. simpl in HLookup. apply HLookup.
		by apply Nat.succ_lt_mono.
Qed.

Lemma list_update_map: forall {X Y:Type} (l:list X) i val {f: X -> Y},
    (i < length l)%coq_nat ->
    List.map f (list_update l i val) = list_update (List.map f l) i (f val).
Proof.
	move => X Y l i val.
	generalize dependent l. generalize dependent val.
	induction i; move => val l f HSize => //=.
  	- by destruct l => //=.
  	- destruct l => //=.
    	f_equal.
    	apply IHi.
		simpl in HSize. by apply Nat.succ_lt_mono.
Qed.
	
Lemma t_preservation_vs_type: forall s f ais s' f' ais' C C' v_t1 lab ret t1s t2s,
    Step (config__ (state__ s f) ais) (config__ (state__ s' f') ais') ->
    Store_ok s -> 
	Store_ok s' ->
    Module_instance_ok s (frame__MODULE f) C ->
    Module_instance_ok s' (frame__MODULE f') C' ->
	v_t1 = (context__LOCALS (upd_label (upd_local_return C (v_t1 ++ (context__LOCALS C)) ret) lab)) -> 
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (frame__LOCALS f) ->
    Admin_instrs_ok s (upd_label (upd_local_return C (v_t1 ++ (context__LOCALS C)) ret) lab) ais (functype__ t1s t2s) ->
    Forall2 (fun v_t v_val0 => Val_ok v_val0 v_t) v_t1 (frame__LOCALS f') 
	/\ length v_t1 = length (frame__LOCALS f').
Proof.
	move => s f ais s' f' ais' C C' v_t1 
		lab ret t1s t2s HReduce HStore HStore' HMInst HMInst' HValTypeEq HValOK HType.
	remember (config__ (state__ s f) ais) as c1.
	remember (config__ (state__ s' f') ais') as c2.
	generalize dependent t2s. generalize dependent t1s.
	generalize dependent lab. generalize dependent ais'. generalize dependent ais.
	induction HReduce; try intros; try (induction v_z; subst); 
	try (apply config_same in Heqc1; apply config_same in Heqc2; 
		destruct Heqc1 as [Hbefore1 [Hbefore2 Hbefore3]]; 
		destruct Heqc2 as [Hafter1 [Hafter2 Hafter3]]; split; subst => //; try apply Forall2_length in HValOK as ? => //).
	- (* Label Context *)
		injection Heqc1 as ?.
		injection Heqc2 as ?; subst.
		apply_composition_typing_single HType.
		apply Label_typing in H4_comp; destruct H4_comp as [ts [ts2' [? [??]]]]; subst.
		rewrite upd_label_overwrite in H1; simpl in H1.
		simpl in HValTypeEq.
		eapply IHHReduce; eauto.
	- (* Local Set *)
		rewrite -> Forall2_Val_ok_is_same_as_map in HValOK; rewrite -> Forall2_Val_ok_is_same_as_map.
		induction v_val.
		apply_composition_typing_and_single HType.
		apply AI_const_typing in  H4_comp0.
		apply_composition_typing_single H4_comp.
		apply Set_local_typing in H4_comp1; destruct H4_comp1 as [t [HLookup [H0' H1']]].
		subst.
		repeat rewrite -> app_assoc in H1_comp1; apply split_append_last in H1_comp1; destruct H1_comp1.
		replace (context__LOCALS C) with ([::]: list valtype) in *; last by symmetry; eapply inst_t_context_local_empty; eauto.
		rewrite -> cats0 in *.
		simpl in H1'; simpl in H0. rewrite -> List.map_length in H1'. 
		apply list_update_map with (f := typeof) (val := (val__CONST v_valtype v_val_)) in H1' as HUpdate.
		rewrite HUpdate.
		rewrite list_update_same_unchanged => //=; try rewrite List.map_length => //=.
		simpl. by rewrite list_update_length.
Qed.

Lemma store_extension_reduce: forall s f ais s' f' ais' C tf loc lab ret,
    Step (config__ (state__ s f) ais) (config__ (state__ s' f') ais') ->
    Module_instance_ok s (frame__MODULE f) C ->
    Admin_instrs_ok s (upd_label (upd_local_return C loc ret) lab) ais tf ->
    Store_ok s ->
    Store_extension s s' /\ Store_ok s'.
Proof.
	move => s f ais s' f' ais' C tf loc lab ret HReduce HIT HType HStore.
	remember (config__ (state__ s f) ais) as c1.
	remember (config__ (state__ s' f') ais') as c2.
	generalize dependent C. generalize dependent tf.
  	generalize dependent loc. generalize dependent lab. generalize dependent ret.
	generalize dependent ais. generalize dependent ais'. 
	generalize dependent f. generalize dependent f'.
	induction HReduce; try move => f' f ais' Heqc2 ais Heqc1 ret lab loc tf C HIT HType HST; try intros; destruct tf;
	try (induction v_z; 
	apply config_same in Heqc1; apply config_same in Heqc2; 
	destruct Heqc1; destruct Heqc2;
	subst; try (split => //; apply store_extension_same)).
	- (* Label Context *) 
		injection Heqc1 as H1.
		injection Heqc2 as H2.
		rewrite <- H in HType.
		apply_composition_typing_single HType.
		apply Label_typing in H4_comp; destruct H4_comp as [ts [ts2' [? [? ?]]]]; subst.
		rewrite upd_label_overwrite in H5; simpl in H5.
		eapply IHHReduce; eauto.
	- (* Label Frame *)
		injection Heqc1 as H1.
		injection Heqc2 as H2.
		rewrite <- H0 in HType.
		apply_composition_typing_single HType.
		apply Frame_typing in H4_comp. destruct H4_comp as [ts [? ?]].
		inversion H6; destruct H7.
		inversion H7; destruct H14 as [? [? ?]]; subst.
		simpl in H13.
		rewrite <- upd_return_is_same_as_append in H13; simpl in H13.
		rewrite <- upd_local_is_same_as_append in H13; simpl in H13.
		rewrite -> _append_option_none_left in H13.
		apply upd_label_unchanged_typing in H13.
		eapply IHHReduce; eauto.
	- (* Global Set *) 
		destruct H2; destruct H0; subst.
		apply_composition_typing_and_single HType.
		destruct v_val.
		apply AI_const_typing in H4_comp0.
		rewrite <- admin_instrs_ok_eq in H4_comp.
		apply Set_global_typing in H4_comp; destruct H4_comp as [t [? [?  ?]]].
		remember  (s <| store__GLOBALS :=
			list_update_func (store__GLOBALS s)
		  	(lookup_total (moduleinst__GLOBALS (frame__MODULE f)) v_x)
		  	[eta set globalinst__VALUE (fun=> val__CONST v_valtype v_val_)] |>) as s'.
		assert (Store_extension s s'). 
		{
			eapply Store_extension__ with (v_globalinst_1 := (store__GLOBALS s)) (v_globalinst_1' := (store__GLOBALS s')) (v_globalinst_2 := []); 
			repeat split => //=; subst; simpl => //=; try rewrite <- app_right_nil => //=.
			- by rewrite list_update_length_func.
			- by eapply func_extension_same.
			- by eapply table_extension_same.
			- by eapply mem_extension_same.
			- inversion HIT; decomp; subst; simpl in *. 
				remember ((lookup_total v_globaladdr v_x)) as v.
				apply Forall2_lookup2 in H12; destruct H12.
				apply H5 in H1. inversion H1; destruct H17.
				repeat rewrite -> app_assoc in H0; apply split_append_last in H0; destruct H0.
				subst.
				rewrite H in H16. injection H16 as ?; subst.
				eapply Forall2_global => //=. apply H18.
		}
		split => //=.
		eapply module_inst_typing_extension with (v_S' := s') in HIT; eauto.
		apply update_global_unchagned in Heqs' as ?. destruct H3 as [? [? [??]]].

		



	- (* Store Num Val *)
	- (* Store Pack Val *)
	- (* Memory Grow Succeed *)
Admitted.
	
Lemma reduce_inst_unchanged: forall s f ais s' f' ais',
    Step (config__ (state__ s f) ais) (config__ (state__ s' f') ais') ->
    frame__MODULE f = frame__MODULE f'.
Proof.
	move => s f ais s' f' ais' HReduce.
	remember (config__ (state__ s f) ais) as c1.
	remember (config__ (state__ s' f') ais') as c2.
	generalize dependent ais. generalize dependent ais'.
	induction HReduce; try intros; try (induction v_z); try induction v_z'; try (apply config_same in Heqc1;
	apply config_same in Heqc2; destruct Heqc1 as [? [? ?]];
	destruct Heqc2 as [? [? ?]]; subst => //).
	eapply IHHReduce; eauto.
Qed.

Theorem t_pure_preservation: forall v_s v_minst v_ais v_ais' v_C loc lab ret tf,
    Module_instance_ok v_s v_minst v_C ->
    Admin_instrs_ok v_s (upd_label (upd_local_return v_C loc ret) lab) v_ais tf ->
    Step_pure v_ais v_ais' ->
    Admin_instrs_ok v_s (upd_label (upd_local_return v_C loc ret) lab) v_ais' tf.
Proof.
	move => v_s v_minst v_ais v_ais' v_C loc lab ret tf HInstType HType HReduce.
	inversion HReduce; subst.
	- eapply Step_pure__unreachable_preserves; eauto.
	- eapply Step_pure__nop_preserves; eauto.
	- eapply Step_pure__drop_preserves; eauto.
	- eapply Step_pure__select_true_preserves; eauto.
	- eapply Step_pure__select_false_preserves; eauto.
	- eapply Step_pure__if_true_preserves; eauto.
	- eapply Step_pure__if_false_preserves; eauto.
	- eapply Step_pure__label_vals_preserves; eauto.
	- eapply Step_pure__br_zero_preserves; eauto.
	- eapply Step_pure__br_succ_preserves; eauto.
	- eapply Step_pure__br_if_true_preserves; eauto.
	- eapply Step_pure__br_if_false_preserves; eauto.
	- eapply Step_pure__br_table_lt_preserves; eauto.
	- eapply Step_pure__br_table_ge_preserves; eauto.
	- eapply Step_pure__frame_vals_preserves; eauto.
	- eapply Step_pure__return_frame_preserves; eauto.
	- eapply Step_pure__return_label_preserves; eauto.
	- eapply Step_pure__trap_vals_preserves; eauto.
	- eapply Step_pure__trap_label_preserves; eauto.
	- eapply Step_pure__trap_frame_preserves; eauto.
	- eapply Step_pure__unop_val_preserves; eauto.
	- eapply Step_pure__unop_trap_preserves; eauto.
	- eapply Step_pure__binop_val_preserves; eauto.
	- eapply Step_pure__binop_trap_preserves; eauto.
	- eapply Step_pure__testop_preserves; eauto.
	- eapply Step_pure__relop_preserves; eauto.
	- eapply Step_pure__cvtop_val_preserves; eauto.
	- eapply Step_pure__cvtop_trap_preserves; eauto.
	- eapply Step_pure__local_tee_preserves; eauto.
Qed.

Lemma t_read_preservation: forall v_s v_f v_ais v_ais' v_C v_t1 t1s t2s lab ret,
    Step_read (config__ (state__ v_s v_f) v_ais) v_ais' ->
    Store_ok v_s ->
    Module_instance_ok v_s (frame__MODULE v_f) v_C ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (frame__LOCALS v_f) ->
    Admin_instrs_ok v_s (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) v_ais (functype__ t1s t2s) ->
    Admin_instrs_ok v_s (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) v_ais' (functype__ t1s t2s).
Proof.
	move => v_s v_f v_ais v_ais' v_C v_t1 t1s t2s lab ret HReduce HST.
	move: v_C ret lab t1s t2s.
	remember (config__ (state__ v_s v_f) v_ais) as c1.
	induction HReduce; move => C ret lab tx ty HIT1 HValOK HType; decomp; destruct v_z; try eauto;
	try (apply config_same in Heqc1; destruct Heqc1 as [Hbefore1 [Hbefore2 Hbefore3]]; subst => //).
	- eapply Step_read__block_preserves; eauto.
	- eapply Step_read__loop_preserves; eauto.
	- eapply Step_read__call_preserves; eauto.
	- eapply Step_read__call_indirect_call_preserves; eauto.
	- eapply Step_read__call_indirect_trap_preserves; eauto.
	- eapply Step_read__call_addr_preserves; eauto.
	- eapply Step_read__local_get_preserves; eauto.
	- eapply Step_read__global_get_preserves; eauto.
	- eapply Step_read__load_num_trap_preserves; eauto.
	- eapply Step_read__load_num_val_preserves; eauto.
	- eapply Step_read__load_pack_trap_preserves; eauto.
	- eapply Step_read__load_pack_val_preserves; eauto.
	- eapply Step_read__memory_size_preserves; eauto.
Qed.

Lemma t_preservation_type: forall v_s v_f v_ais v_s' v_f' v_ais' v_C v_t1 t1s t2s lab ret,
    Step (config__ (state__ v_s v_f) v_ais) (config__ (state__ v_s' v_f') v_ais') ->
    Store_ok v_s ->
    Store_ok v_s' ->
	Store_extension v_s v_s' -> 
    Module_instance_ok v_s (frame__MODULE v_f) v_C ->
    Module_instance_ok v_s' (frame__MODULE v_f) v_C ->
	Forall2 (fun v_t v_val => Val_ok v_val v_t) v_t1 (frame__LOCALS v_f) ->
    Admin_instrs_ok v_s (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) v_ais (functype__ t1s t2s) ->
    Admin_instrs_ok v_s' (upd_label (upd_local_return v_C (v_t1 ++ context__LOCALS v_C) ret) lab) v_ais' (functype__ t1s t2s).
Proof.
	move => v_s v_f v_ais v_s' v_f' v_ais' v_C v_t1 t1s t2s lab ret HReduce HST1 HST2 HSExt.
	move: v_C ret lab t1s t2s.
	remember (config__ (state__ v_s v_f) v_ais) as c1.
	remember (config__ (state__ v_s' v_f') v_ais') as c2.
	generalize dependent v_ais.
	generalize dependent v_ais'.
	generalize dependent v_t1.
	generalize dependent v_f.
	generalize dependent v_f'.
	induction HReduce; move => r_v_f' r_v_f v_t1 v_ais' Heqc2 v_ais Heqc1 v_C ret lab tx ty HIT1 HIT2 HValOK HType; try (destruct v_z; subst);  try (destruct v_z'; subst); try eauto;
	try (apply config_same in Heqc1; apply config_same in Heqc2; 
		destruct Heqc1 as [Hbefore1 [Hbefore2 Hbefore3]]; 
		destruct Heqc2 as [Hafter1 [Hafter2 Hafter3]]; subst => //).
	- (* Step_pure *) eapply t_pure_preservation; eauto.
	- (* Step_read *) eapply t_read_preservation; eauto.
	- (* Context Label *) 
		rewrite <- admin_instrs_ok_eq in HType.
		apply Label_typing in HType as H. destruct H as [ts [ts2' [? [? ?]]]].
		subst.
		apply admin_instrs_weakening_empty_1.
		rewrite <- admin_instrs_ok_eq.
		apply Admin_instr_ok__label with (v_t_1 := ts).
		split => //=.
		eapply IHHReduce => //=.
	- (* Context Frame *)
		rewrite <- admin_instrs_ok_eq in HType.
		apply Frame_typing in HType as H. destruct H as [ts [? ?]].
		subst.
		apply admin_instrs_weakening_empty_1.
		rewrite <- admin_instrs_ok_eq.
		apply Admin_instr_ok__frame.
		inversion H0. subst. destruct H.
		apply Thread_ok__ with (v_C := v_C0).
		inversion H; destruct H2 as [? [? ?]]. 
		split.
		- apply Frame_ok__.
			repeat split => //=.
			eapply module_inst_typing_extension; eauto.
		-
			apply inst_t_context_local_empty in H6 as H'.
			rewrite upd_label_unchanged_typing.
			remember v_t as val.
			rewrite -> app_right_nil in Heqval.
			rewrite <- H' in Heqval. subst.
			eapply IHHReduce => //=.
			eapply module_inst_typing_extension; eauto.
	- (* Local set *)
		apply_composition_typing_and_single HType.
		destruct v_val.
		apply AI_const_typing in H4_comp0.
		rewrite <- admin_instrs_ok_eq in H4_comp.
		apply Set_local_typing in H4_comp; destruct H4_comp as [t [? [? ?]]].
		subst.
		repeat rewrite -> app_assoc in H0; apply split_append_last in H0; destruct H0.
		subst.
		apply admin_weakening_empty_both.
		apply Admin_instrs_ok__empty.
	- (* Global set *)
		apply_composition_typing_and_single HType.
		destruct v_val.
		apply AI_const_typing in H4_comp0.
		rewrite <- admin_instrs_ok_eq in H4_comp.
		apply Set_global_typing in H4_comp. destruct H4_comp as [t [? [? ?]]].
		subst.
		repeat rewrite -> app_assoc in H0; apply split_append_last in H0; destruct H0.
		subst.
		apply admin_weakening_empty_both.
		apply Admin_instrs_ok__empty.
	- (* Store Num Trap *)
		rewrite <- admin_instrs_ok_eq.
		apply Admin_instr_ok__trap.
	- (* Store Num Val *)
		apply_composition_typing HType.
		apply_composition_typing_and_single H4_comp.
		rewrite <- admin_instrs_ok_eq in H3_comp.
		apply AI_const_typing in H3_comp.
		apply AI_const_typing in H4_comp.
		rewrite <- admin_instrs_ok_eq in H4_comp0.
		apply Store_typing in H4_comp0; destruct H4_comp0 as [v_n [v_mt [v_inn [? [? [? [? [? ?]]]]]]]].
		subst.
		remember [:: valtype__INN inn__I32; v_t] as v_t'.
		rewrite -cat1s in Heqv_t'.
		subst.
		repeat rewrite -> app_assoc in H; apply split_append_last in H; destruct H; subst.
		rewrite H in H1_comp0.
		repeat rewrite -> app_assoc in H1_comp0; apply split_append_last in H1_comp0; destruct H1_comp0; subst.
		subst.
		apply admin_weakening_empty_both.
		apply Admin_instrs_ok__empty.
	- (* Store Pack Trap *)
		rewrite <- admin_instrs_ok_eq.
		apply Admin_instr_ok__trap.
	- (* Store Pack Val *)
		apply_composition_typing HType.
		apply_composition_typing_and_single H4_comp.
		rewrite <- admin_instrs_ok_eq in H3_comp.
		apply AI_const_typing in H3_comp.
		apply AI_const_typing in H4_comp.
		rewrite <- admin_instrs_ok_eq in H4_comp0.
		apply Store_typing in H4_comp0; destruct H4_comp0 as [v_n' [v_mt' [v_inn' [? [? [? [? [? ?]]]]]]]].
		subst.
		remember [:: valtype__INN inn__I32; valtype__INN v_inn] as v_t'.
		rewrite -cat1s in Heqv_t'.
		subst.
		repeat rewrite -> app_assoc in H; apply split_append_last in H; destruct H; subst.
		rewrite H in H1_comp0.
		repeat rewrite -> app_assoc in H1_comp0; apply split_append_last in H1_comp0; destruct H1_comp0; subst.
		subst.
		apply admin_weakening_empty_both.
		apply Admin_instrs_ok__empty.
	- (* Memory Grow Succeed *)
		apply_composition_typing_and_single HType.
		apply AI_const_typing in H4_comp0.
		rewrite <- admin_instrs_ok_eq in H4_comp.
		apply Grow_memory_typing in H4_comp; destruct H4_comp as [v_mt [ts [? [? [? ?]]]]].
		subst.
		repeat rewrite -> app_assoc in H2; apply split_append_last in H2; destruct H2; subst.
		repeat rewrite -> app_assoc.
		apply admin_instrs_weakening_empty_1.
		rewrite <- admin_instrs_ok_eq.
		remember (Datatypes.length (meminst__BYTES (fun_mem (state__ v_s r_v_f) 0)) / (64 * fun_Ki)%coq_nat) as v_n'.
		eapply (Admin_instr_ok__instr _ _ (instr__CONST (valtype__INN inn__I32) v_n') (functype__ [] [(valtype__INN inn__I32)])).
		apply Instr_ok__const.
	- (* Memory Grow Fail *)
		apply_composition_typing_and_single HType.
		apply AI_const_typing in H4_comp0.
		rewrite <- admin_instrs_ok_eq in H4_comp.
		apply Grow_memory_typing in H4_comp; destruct H4_comp as [v_mt [ts [? [? [? ?]]]]].
		subst.
		repeat rewrite -> app_assoc in H2; apply split_append_last in H2; destruct H2; subst.
		repeat rewrite -> app_assoc.
		apply admin_instrs_weakening_empty_1.
		rewrite <- admin_instrs_ok_eq.
		remember (fun_invsigned 32 (0 - 1)%coq_nat) as v_n'.
		eapply (Admin_instr_ok__instr _ _ (instr__CONST (valtype__INN inn__I32) v_n') (functype__ [] [(valtype__INN inn__I32)])).
		apply Instr_ok__const.
Qed.

(* Ultimate goal of project *)				
Theorem t_preservation: forall c1 ts c2,
	Step c1 c2 ->
	Config_ok c1 ts ->
	Config_ok c2 ts.
Proof.
	move => c1 ts c2 HReduce HType.
	induction c1; induction v_state.
	induction c2. induction v_state.
	inversion HType; destruct H3.
	inversion H4; destruct H5.
	rewrite <- upd_return_is_same_as_append in H11.
	inversion H5. destruct H12 as [H0' [H1' H2']].
	rewrite <- upd_local_is_same_as_append in H15.
	subst.
	rewrite <- upd_local_return_is_same_as_append in H11.
	apply upd_label_unchanged_typing in H11.
	assert (Store_extension v_store v_store0 /\ Store_ok v_store0).
	{
		apply (store_extension_reduce 
			v_store  
			{|frame__LOCALS := v_val;frame__MODULE := v_moduleinst|} 
			v__ v_store0 v_frame0 v__0 v_C0 (functype__ [::] ts) 
			(_append v_t1 (context__LOCALS v_C0)) 
			(context__LABELS (upd_local_return v_C0 (_append v_t1 (context__LOCALS v_C0)) (_append (option_map [eta Some] None) (context__RETURN v_C0))))
			(_append (Some None) (context__RETURN v_C0))) => //.
	}
	destruct H.
	apply reduce_inst_unchanged in HReduce as HModuleInst.
	induction v_frame0.
	simpl in HModuleInst.
	remember {|frame__LOCALS := v_val;frame__MODULE := v_moduleinst|} as f.
	assert (Module_instance_ok v_store0 v_moduleinst v_C0). { apply (module_inst_typing_extension v_store); eauto. }
	apply Config_ok__; split => //=.
	eapply Thread_ok__; split => //=.
	rewrite <- HModuleInst.
	eapply (Frame_ok__ v_store0 frame__LOCALS0 v_moduleinst v_C0 v_t1); eauto.
	apply (t_preservation_vs_type) with (v_t1 := v_t1) (C := v_C0) (C' := v_C0) 
		(lab:= (context__LABELS (upd_local_return v_C0 (_append v_t1 (context__LOCALS v_C0)) (_append (option_map [eta Some] None) (context__RETURN v_C0))))) 
		(ret:= (_append (Some None) (context__RETURN v_C0))) (t1s := []) (t2s := ts) in HReduce as H10; try destruct H10; try apply Forall2_length in H10; repeat split => //.
	- apply H3.
	- apply H0.
	- by rewrite Heqf.
	- by rewrite <- HModuleInst.
	- simpl. apply inst_t_context_local_empty in H1. rewrite H1. by rewrite -> app_nil_r.
	- by rewrite Heqf.
	- apply H11.
	(* Actual Typing proof *)
	rewrite <- upd_return_is_same_as_append; simpl.
	rewrite <- upd_local_is_same_as_append; simpl.
	fold_upd_context.
	rewrite -> _append_option_none_left.
	rewrite upd_label_unchanged_typing.
	eapply t_preservation_type; eauto; try rewrite -> Heqf; eauto.
Qed.