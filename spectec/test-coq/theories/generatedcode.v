(* Exported Code *)
From Coq Require Import String List Unicode.Utf8 Reals.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.
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
		| x :: l', S n, m => list_slice l' n m
	end.

Fixpoint list_slice_update {α: Type} (l: list α) (i: nat) (j: nat) (update_l: list α): list α :=
	match l, i, j, update_l with
		| nil, _, _, _ => nil
		| l', _, _, nil => l'
		| x :: l', 0, 0, _ => nil
		| x :: l', S n, 0, _ => nil
		| x :: l', 0, S m, y :: u_l' => y :: list_slice_update l' 0 m u_l'
		| x :: l', S n, m, _ => x :: list_slice_update l' n m update_l
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

Definition option_eq_dec (A : Type) (eq_dec : forall (x y : A), {x = y} + {x <> y}):
  forall (x y : option A), {x = y} + {x <> y}.
Proof.
  move=> x y.
  case: x; case: y; try by [left | right].
  move => x' y'.
  case: (eq_dec x' y') => H.
  - left. by congr Some.
  - right. move => [Hcontra]. by apply: H.
Qed.

Ltac decidable_equality_step :=
  first [
      by apply: eq_comparable
    | apply: List.list_eq_dec
    | apply: option_eq_dec
    | apply: PeanoNat.Nat.eq_dec
    | by eauto
    | intros; apply: decP; by (exact _ || eauto)
    | decide equality ].

Ltac decidable_equality :=
  repeat decidable_equality_step.

Lemma eq_dec_Equality_axiom : forall t (eq_dec : forall x y : t, {x = y} + {x <> y}),
  let eqb v1 v2 := is_left (eq_dec v1 v2) in
  Equality.axiom eqb.
Proof.
  move=> t eq_dec eqb x y. rewrite /eqb. case: (eq_dec x y).
  - move=> E /=. by apply/ReflectT.
  - move=> E /=. by apply/ReflectF.
Qed.

Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.

(* Generated Code *)
(* Notation Definition at: spec/wasm-1.0-test/0-aux.watsup:11.1-11.15 *)
Notation reserved__N := nat.

Definition list__reserved__N  := (list (reserved__N )).

Definition option__reserved__N  := (option (reserved__N )).

(* Notation Definition at: spec/wasm-1.0-test/0-aux.watsup:12.1-12.15 *)
Notation M := nat.

Definition list__M  := (list (M )).

Definition option__M  := (option (M )).

(* Notation Definition at: spec/wasm-1.0-test/0-aux.watsup:13.1-13.15 *)
Notation n := nat.

Definition list__n  := (list (n )).

Definition option__n  := (option (n )).

(* Notation Definition at: spec/wasm-1.0-test/0-aux.watsup:14.1-14.15 *)
Notation m := nat.

Definition list__m  := (list (m )).

Definition option__m  := (option (m )).

(* Auxiliary Definition at: spec/wasm-1.0-test/0-aux.watsup:21.1-21.14 *)
Definition fun_Ki : nat := 1024.

(* Mutual Recursion at: spec/wasm-1.0-test/0-aux.watsup:27.1-27.25 *)
(* Auxiliary Definition at: spec/wasm-1.0-test/0-aux.watsup:27.1-27.25 *)
Fixpoint fun_min (v_reserved__nat_0 : nat) (v_reserved__nat_1 : nat) : nat :=
	match (v_reserved__nat_0, v_reserved__nat_1) with
		| (0, v_j) => 0
		| (v_i, 0) => 0
		| ((S v_i), (S v_j)) => (fun_min v_i v_j)
	end.

(* Mutual Recursion at: spec/wasm-1.0-test/0-aux.watsup:32.1-32.21 *)
(* Auxiliary Definition at: spec/wasm-1.0-test/0-aux.watsup:32.1-32.21 *)
Fixpoint fun_sum (v___0 : (list nat)) : nat :=
	match (v___0) with
		| ([]) => 0
		| ((v_n :: v_n')) => (v_n + (fun_sum v_n'))
	end.

(* Mutual Recursion at: spec/wasm-1.0-test/0-aux.watsup:39.1-39.59 *)
(* Auxiliary Definition at: spec/wasm-1.0-test/0-aux.watsup:39.1-39.59 *)
Fixpoint fun_concat_ (X : Type) (v___1 : (list (list X))) : (list X) :=
	match (X, v___1) with
		| (_, []) => []
		| (_, (v_w :: v_w')) => (@app _ v_w (fun_concat_ X v_w'))
	end.

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:6.1-6.49 *)
Inductive reserved__list (X : Type) : Type :=
	| reserved__list__ (v__ : (list X)) : reserved__list X.

Definition list__reserved__list (X : Type) := (list (reserved__list X)).

Definition option__reserved__list (X : Type) := (option (reserved__list X)).

Global Instance Inhabited__reserved__list (X : Type) : Inhabited (reserved__list X) := { default_val := reserved__list__ X default_val }.

Definition reserved__list_eq_dec : forall (X : Type) (v1 v2 : reserved__list X),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition reserved__list_eqb (X : Type) (v1 v2 : reserved__list X) : bool :=
reserved__list_eq_dec X v1 v2.
Definition eqreserved__listP (X : Type) : Equality.axiom (reserved__list_eqb X) :=
eq_dec_Equality_axiom (reserved__list X) (reserved__list_eq_dec X).

Canonical Structure reserved__list_eqMixin (X : Type) := EqMixin (eqreserved__listP X).
Canonical Structure reserved__list_eqType (X : Type) :=
Eval hnf in EqType (reserved__list X) (reserved__list_eqMixin X).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:15.1-15.50 *)
Inductive byte  : Type :=
	| byte__ (v_i : nat) : byte .

Definition list__byte  := (list (byte )).

Definition option__byte  := (option (byte )).

Global Instance Inhabited__byte  : Inhabited (byte ) := { default_val := byte__  default_val }.

Definition byte_eq_dec : forall  (v1 v2 : byte ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition byte_eqb  (v1 v2 : byte ) : bool :=
byte_eq_dec  v1 v2.
Definition eqbyteP  : Equality.axiom (byte_eqb ) :=
eq_dec_Equality_axiom (byte ) (byte_eq_dec ).

Canonical Structure byte_eqMixin  := EqMixin (eqbyteP ).
Canonical Structure byte_eqType  :=
Eval hnf in EqType (byte ) (byte_eqMixin ).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:17.1-17.61 *)
Notation uN := nat.

Definition list__uN  := (list (uN )).

Definition option__uN  := (option (uN )).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:18.1-18.59 *)
Notation sN := nat.

Definition list__sN  := (list (sN )).

Definition option__sN  := (option (sN )).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:19.1-19.51 *)
Notation iN := uN.

Definition list__iN  := (list (iN )).

Definition option__iN  := (option (iN )).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:20.1-20.16 *)
Notation u31 := uN.

Definition list__u31  := (list (u31 )).

Definition option__u31  := (option (u31 )).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:21.1-21.16 *)
Notation u32 := uN.

Definition list__u32  := (list (u32 )).

Definition option__u32  := (option (u32 )).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:22.1-22.16 *)
Notation u64 := uN.

Definition list__u64  := (list (u64 )).

Definition option__u64  := (option (u64 )).

(* Auxiliary Definition at: spec/wasm-1.0-test/1-syntax.watsup:29.1-29.35 *)
Definition fun_signif (v_reserved__N_0 : reserved__N) : (option nat) :=
	match (v_reserved__N_0) with
		| (32) => (Some 23)
		| (64) => (Some 52)
		| (v_x0) => None
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/1-syntax.watsup:33.1-33.34 *)
Definition fun_expon (v_reserved__N_0 : reserved__N) : (option nat) :=
	match (v_reserved__N_0) with
		| (32) => (Some 8)
		| (64) => (Some 11)
		| (v_x0) => None
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/1-syntax.watsup:37.1-37.30 *)
Definition fun_M (v_reserved__N_0 : reserved__N) : nat :=
	match (v_reserved__N_0) with
		| (v_reserved__N) => (the (fun_signif v_reserved__N))
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/1-syntax.watsup:40.1-40.30 *)
Definition fun_E (v_reserved__N_0 : reserved__N) : nat :=
	match (v_reserved__N_0) with
		| (v_reserved__N) => (the (fun_expon v_reserved__N))
	end.

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:43.1-43.67 *)
Notation fN := nat.

Definition list__fN  := (list (fN )).

Definition option__fN  := (option (fN )).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:45.1-45.16 *)
Notation f32 := fN.

Definition list__f32  := (list (f32 )).

Definition option__f32  := (option (f32 )).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:46.1-46.16 *)
Notation f64 := fN.

Definition list__f64  := (list (f64 )).

Definition option__f64  := (option (f64 )).

(* Auxiliary Definition at: spec/wasm-1.0-test/1-syntax.watsup:48.1-48.36 *)
Definition fun_fzero (v_reserved__N_0 : reserved__N) : fN :=
	match (v_reserved__N_0) with
		| (v_reserved__N) => (0 : fN)
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/1-syntax.watsup:51.1-51.36 *)
Definition fun_fone (v_reserved__N_0 : reserved__N) : fN :=
	match (v_reserved__N_0) with
		| (v_reserved__N) => (1 : fN)
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/1-syntax.watsup:54.1-54.21 *)
Definition fun_canon_ (v_reserved__N_0 : reserved__N) : nat :=
	match (v_reserved__N_0) with
		| (v_reserved__N) => (2 ^ ((the (fun_signif v_reserved__N)) - 1))
	end.

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:62.1-62.85 *)
Inductive char  : Type :=
	| char__ (v_i : nat) : char .

Definition list__char  := (list (char )).

Definition option__char  := (option (char )).

Global Instance Inhabited__char  : Inhabited (char ) := { default_val := char__  default_val }.

Definition char_eq_dec : forall  (v1 v2 : char ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition char_eqb  (v1 v2 : char ) : bool :=
char_eq_dec  v1 v2.
Definition eqcharP  : Equality.axiom (char_eqb ) :=
eq_dec_Equality_axiom (char ) (char_eq_dec ).

Canonical Structure char_eqMixin  := EqMixin (eqcharP ).
Canonical Structure char_eqType  :=
Eval hnf in EqType (char ) (char_eqMixin ).

(* Axiom Definition at: spec/wasm-1.0-test/1-syntax.watsup:64.1-64.25 *)
Axiom fun_utf8 : forall (v___0 : (list char)), (list__byte ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:66.1-66.70 *)
Inductive name  : Type :=
	| name__ (v__ : (list char)) : name .

Definition list__name  := (list (name )).

Definition option__name  := (option (name )).

Global Instance Inhabited__name  : Inhabited (name ) := { default_val := name__  default_val }.

Definition name_eq_dec : forall  (v1 v2 : name ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition name_eqb  (v1 v2 : name ) : bool :=
name_eq_dec  v1 v2.
Definition eqnameP  : Equality.axiom (name_eqb ) :=
eq_dec_Equality_axiom (name ) (name_eq_dec ).

Canonical Structure name_eqMixin  := EqMixin (eqnameP ).
Canonical Structure name_eqType  :=
Eval hnf in EqType (name ) (name_eqMixin ).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:75.1-75.36 *)
Notation idx := u32.

Definition list__idx  := (list (idx )).

Definition option__idx  := (option (idx )).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:77.1-77.45 *)
Notation typeidx := idx.

Definition list__typeidx  := (list (typeidx )).

Definition option__typeidx  := (option (typeidx )).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:78.1-78.49 *)
Notation funcidx := idx.

Definition list__funcidx  := (list (funcidx )).

Definition option__funcidx  := (option (funcidx )).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:79.1-79.49 *)
Notation globalidx := idx.

Definition list__globalidx  := (list (globalidx )).

Definition option__globalidx  := (option (globalidx )).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:80.1-80.47 *)
Notation tableidx := idx.

Definition list__tableidx  := (list (tableidx )).

Definition option__tableidx  := (option (tableidx )).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:81.1-81.46 *)
Notation memidx := idx.

Definition list__memidx  := (list (memidx )).

Definition option__memidx  := (option (memidx )).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:82.1-82.47 *)
Notation labelidx := idx.

Definition list__labelidx  := (list (labelidx )).

Definition option__labelidx  := (option (labelidx )).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:83.1-83.47 *)
Notation localidx := idx.

Definition list__localidx  := (list (localidx )).

Definition option__localidx  := (option (localidx )).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:97.1-97.38 *)
Inductive fnn  : Type :=
	| fnn__F32  : fnn 
	| fnn__F64  : fnn .

Definition list__fnn  := (list (fnn )).

Definition option__fnn  := (option (fnn )).

Global Instance Inhabited__fnn  : Inhabited (fnn ) := { default_val := fnn__F32   }.

Definition fnn_eq_dec : forall  (v1 v2 : fnn ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition fnn_eqb  (v1 v2 : fnn ) : bool :=
fnn_eq_dec  v1 v2.
Definition eqfnnP  : Equality.axiom (fnn_eqb ) :=
eq_dec_Equality_axiom (fnn ) (fnn_eq_dec ).

Canonical Structure fnn_eqMixin  := EqMixin (eqfnnP ).
Canonical Structure fnn_eqType  :=
Eval hnf in EqType (fnn ) (fnn_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:96.1-96.38 *)
Inductive inn  : Type :=
	| inn__I32  : inn 
	| inn__I64  : inn .

Definition list__inn  := (list (inn )).

Definition option__inn  := (option (inn )).

Global Instance Inhabited__inn  : Inhabited (inn ) := { default_val := inn__I32   }.

Definition inn_eq_dec : forall  (v1 v2 : inn ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition inn_eqb  (v1 v2 : inn ) : bool :=
inn_eq_dec  v1 v2.
Definition eqinnP  : Equality.axiom (inn_eqb ) :=
eq_dec_Equality_axiom (inn ) (inn_eq_dec ).

Canonical Structure inn_eqMixin  := EqMixin (eqinnP ).
Canonical Structure inn_eqType  :=
Eval hnf in EqType (inn ) (inn_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:92.1-94.12 *)
Inductive valtype  : Type :=
	| valtype__INN (v_inn : inn) : valtype 
	| valtype__FNN (v_fnn : fnn) : valtype .

Definition list__valtype  := (list (valtype )).

Definition option__valtype  := (option (valtype )).

Global Instance Inhabited__valtype  : Inhabited (valtype ) := { default_val := valtype__INN  default_val }.

Definition valtype_eq_dec : forall  (v1 v2 : valtype ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition valtype_eqb  (v1 v2 : valtype ) : bool :=
valtype_eq_dec  v1 v2.
Definition eqvaltypeP  : Equality.axiom (valtype_eqb ) :=
eq_dec_Equality_axiom (valtype ) (valtype_eq_dec ).

Canonical Structure valtype_eqMixin  := EqMixin (eqvaltypeP ).
Canonical Structure valtype_eqType  :=
Eval hnf in EqType (valtype ) (valtype_eqMixin ).

(* Auxiliary Definition at: spec/wasm-1.0-test/1-syntax.watsup:99.1-99.32 *)
Definition fun_optionSize (v___0 : (option valtype)) : nat :=
	match (v___0) with
		| ((Some v_valtype)) => 1
		| (None) => 0
	end.

(* Type Alias Definition at: spec/wasm-1.0-test/1-syntax.watsup:105.1-106.11 *)
Definition resulttype  := (option valtype).

Definition list__resulttype  := (list (resulttype )).

Definition option__resulttype  := (option (resulttype )).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:108.1-108.18 *)
Inductive mut  : Type :=
	| mut__MUT (v__ : (option unit)) : mut .

Definition list__mut  := (list (mut )).

Definition option__mut  := (option (mut )).

Global Instance Inhabited__mut  : Inhabited (mut ) := { default_val := mut__MUT  default_val }.

Definition mut_eq_dec : forall  (v1 v2 : mut ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition mut_eqb  (v1 v2 : mut ) : bool :=
mut_eq_dec  v1 v2.
Definition eqmutP  : Equality.axiom (mut_eqb ) :=
eq_dec_Equality_axiom (mut ) (mut_eq_dec ).

Canonical Structure mut_eqMixin  := EqMixin (eqmutP ).
Canonical Structure mut_eqType  :=
Eval hnf in EqType (mut ) (mut_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:110.1-111.16 *)
Inductive limits  : Type :=
	| limits__ (v_u32 : u32) (v__ : u32) : limits .

Definition list__limits  := (list (limits )).

Definition option__limits  := (option (limits )).

Global Instance Inhabited__limits  : Inhabited (limits ) := { default_val := limits__  default_val default_val }.

Definition limits_eq_dec : forall  (v1 v2 : limits ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition limits_eqb  (v1 v2 : limits ) : bool :=
limits_eq_dec  v1 v2.
Definition eqlimitsP  : Equality.axiom (limits_eqb ) :=
eq_dec_Equality_axiom (limits ) (limits_eq_dec ).

Canonical Structure limits_eqMixin  := EqMixin (eqlimitsP ).
Canonical Structure limits_eqType  :=
Eval hnf in EqType (limits ) (limits_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:112.1-113.14 *)
Inductive globaltype  : Type :=
	| globaltype__ (v_mut : mut) (v_valtype : valtype) : globaltype .

Definition list__globaltype  := (list (globaltype )).

Definition option__globaltype  := (option (globaltype )).

Global Instance Inhabited__globaltype  : Inhabited (globaltype ) := { default_val := globaltype__  default_val default_val }.

Definition globaltype_eq_dec : forall  (v1 v2 : globaltype ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition globaltype_eqb  (v1 v2 : globaltype ) : bool :=
globaltype_eq_dec  v1 v2.
Definition eqglobaltypeP  : Equality.axiom (globaltype_eqb ) :=
eq_dec_Equality_axiom (globaltype ) (globaltype_eq_dec ).

Canonical Structure globaltype_eqMixin  := EqMixin (eqglobaltypeP ).
Canonical Structure globaltype_eqType  :=
Eval hnf in EqType (globaltype ) (globaltype_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:114.1-115.23 *)
Inductive functype  : Type :=
	| functype__ (v__ : (list valtype)) (v__ : (list valtype)) : functype .

Definition list__functype  := (list (functype )).

Definition option__functype  := (option (functype )).

Global Instance Inhabited__functype  : Inhabited (functype ) := { default_val := functype__  default_val default_val }.

Definition functype_eq_dec : forall  (v1 v2 : functype ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition functype_eqb  (v1 v2 : functype ) : bool :=
functype_eq_dec  v1 v2.
Definition eqfunctypeP  : Equality.axiom (functype_eqb ) :=
eq_dec_Equality_axiom (functype ) (functype_eq_dec ).

Canonical Structure functype_eqMixin  := EqMixin (eqfunctypeP ).
Canonical Structure functype_eqType  :=
Eval hnf in EqType (functype ) (functype_eqMixin ).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:116.1-117.9 *)
Notation tabletype := limits.

Definition list__tabletype  := (list (tabletype )).

Definition option__tabletype  := (option (tabletype )).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:118.1-119.9 *)
Notation memtype := limits.

Definition list__memtype  := (list (memtype )).

Definition option__memtype  := (option (memtype )).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:120.1-121.70 *)
Inductive externtype  : Type :=
	| externtype__FUNC (v_functype : functype) : externtype 
	| externtype__GLOBAL (v_globaltype : globaltype) : externtype 
	| externtype__TABLE (v_tabletype : tabletype) : externtype 
	| externtype__MEM (v_memtype : memtype) : externtype .

Definition list__externtype  := (list (externtype )).

Definition option__externtype  := (option (externtype )).

Global Instance Inhabited__externtype  : Inhabited (externtype ) := { default_val := externtype__FUNC  default_val }.

Definition externtype_eq_dec : forall  (v1 v2 : externtype ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition externtype_eqb  (v1 v2 : externtype ) : bool :=
externtype_eq_dec  v1 v2.
Definition eqexterntypeP  : Equality.axiom (externtype_eqb ) :=
eq_dec_Equality_axiom (externtype ) (externtype_eq_dec ).

Canonical Structure externtype_eqMixin  := EqMixin (eqexterntypeP ).
Canonical Structure externtype_eqType  :=
Eval hnf in EqType (externtype ) (externtype_eqMixin ).

(* Auxiliary Definition at: spec/wasm-1.0-test/1-syntax.watsup:133.1-133.40 *)
Definition fun_size (v_valtype_0 : valtype) : nat :=
	match (v_valtype_0) with
		| ((valtype__INN (inn__I32 ))) => 32
		| ((valtype__INN (inn__I64 ))) => 64
		| ((valtype__FNN (fnn__F32 ))) => 32
		| ((valtype__FNN (fnn__F64 ))) => 64
	end.

(* Family Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:135.1-135.21 *)
Inductive val_: Type :=
	| val___inn__entry : iN -> val_
	| val___fnn__entry : fN -> val_.

Global Instance Inhabited__val_ : Inhabited val_ := { default_val := val___inn__entry default_val }.

Definition list__val_  := (list (val_ )).

Definition option__val_  := (option (val_ )).

Coercion val___inn__entry : iN >-> val_.

Definition list__iN__val_ : list__iN  -> list__val_ := map val___inn__entry.

Coercion list__iN__val_ : list__iN >-> list__val_.

Definition option__iN__val_ : option__iN -> option__val_ := option_map val___inn__entry.

Coercion option__iN__val_ : option__iN >-> option__val_.

Coercion val___fnn__entry : fN >-> val_.

Definition list__fN__val_ : list__fN  -> list__val_ := map val___fnn__entry.

Coercion list__fN__val_ : list__fN >-> list__val_.

Definition option__fN__val_ : option__fN -> option__val_ := option_map val___fnn__entry.

Coercion option__fN__val_ : option__fN >-> option__val_.

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:142.1-142.42 *)
Inductive sx  : Type :=
	| sx__U  : sx 
	| sx__S  : sx .

Definition list__sx  := (list (sx )).

Definition option__sx  := (option (sx )).

Global Instance Inhabited__sx  : Inhabited (sx ) := { default_val := sx__U   }.

Definition sx_eq_dec : forall  (v1 v2 : sx ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition sx_eqb  (v1 v2 : sx ) : bool :=
sx_eq_dec  v1 v2.
Definition eqsxP  : Equality.axiom (sx_eqb ) :=
eq_dec_Equality_axiom (sx ) (sx_eq_dec ).

Canonical Structure sx_eqMixin  := EqMixin (eqsxP ).
Canonical Structure sx_eqType  :=
Eval hnf in EqType (sx ) (sx_eqMixin ).

(* Family Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:144.1-144.22 *)
Inductive unop___inn  : Type :=
	| unop___inn__CLZ  : unop___inn 
	| unop___inn__CTZ  : unop___inn 
	| unop___inn__POPCNT  : unop___inn .

Definition list__unop___inn  := (list (unop___inn )).

Definition option__unop___inn  := (option (unop___inn )).

Global Instance Inhabited__unop___inn  : Inhabited (unop___inn ) := { default_val := unop___inn__CLZ   }.

Definition unop___inn_eq_dec : forall  (v1 v2 : unop___inn ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition unop___inn_eqb  (v1 v2 : unop___inn ) : bool :=
unop___inn_eq_dec  v1 v2.
Definition equnop___innP  : Equality.axiom (unop___inn_eqb ) :=
eq_dec_Equality_axiom (unop___inn ) (unop___inn_eq_dec ).

Canonical Structure unop___inn_eqMixin  := EqMixin (equnop___innP ).
Canonical Structure unop___inn_eqType  :=
Eval hnf in EqType (unop___inn ) (unop___inn_eqMixin ).

Inductive unop___fnn  : Type :=
	| unop___fnn__ABS  : unop___fnn 
	| unop___fnn__NEG  : unop___fnn 
	| unop___fnn__SQRT  : unop___fnn 
	| unop___fnn__CEIL  : unop___fnn 
	| unop___fnn__FLOOR  : unop___fnn 
	| unop___fnn__TRUNC  : unop___fnn 
	| unop___fnn__NEAREST  : unop___fnn .

Definition list__unop___fnn  := (list (unop___fnn )).

Definition option__unop___fnn  := (option (unop___fnn )).

Global Instance Inhabited__unop___fnn  : Inhabited (unop___fnn ) := { default_val := unop___fnn__ABS   }.

Definition unop___fnn_eq_dec : forall  (v1 v2 : unop___fnn ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition unop___fnn_eqb  (v1 v2 : unop___fnn ) : bool :=
unop___fnn_eq_dec  v1 v2.
Definition equnop___fnnP  : Equality.axiom (unop___fnn_eqb ) :=
eq_dec_Equality_axiom (unop___fnn ) (unop___fnn_eq_dec ).

Canonical Structure unop___fnn_eqMixin  := EqMixin (equnop___fnnP ).
Canonical Structure unop___fnn_eqType  :=
Eval hnf in EqType (unop___fnn ) (unop___fnn_eqMixin ).

Inductive unop_  : Type :=
	| unop___inn__entry (arg : unop___inn) : unop_ 
	| unop___fnn__entry (arg : unop___fnn) : unop_ .

Definition list__unop_  := (list (unop_ )).

Definition option__unop_  := (option (unop_ )).

Global Instance Inhabited__unop_  : Inhabited (unop_ ) := { default_val := unop___inn__entry  default_val }.

Definition unop__eq_dec : forall  (v1 v2 : unop_ ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition unop__eqb  (v1 v2 : unop_ ) : bool :=
unop__eq_dec  v1 v2.
Definition equnop_P  : Equality.axiom (unop__eqb ) :=
eq_dec_Equality_axiom (unop_ ) (unop__eq_dec ).

Canonical Structure unop__eqMixin  := EqMixin (equnop_P ).
Canonical Structure unop__eqType  :=
Eval hnf in EqType (unop_ ) (unop__eqMixin ).

(* Family Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:148.1-148.23 *)
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

Definition option__binop___inn  := (option (binop___inn )).

Global Instance Inhabited__binop___inn  : Inhabited (binop___inn ) := { default_val := binop___inn__ADD   }.

Definition binop___inn_eq_dec : forall  (v1 v2 : binop___inn ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition binop___inn_eqb  (v1 v2 : binop___inn ) : bool :=
binop___inn_eq_dec  v1 v2.
Definition eqbinop___innP  : Equality.axiom (binop___inn_eqb ) :=
eq_dec_Equality_axiom (binop___inn ) (binop___inn_eq_dec ).

Canonical Structure binop___inn_eqMixin  := EqMixin (eqbinop___innP ).
Canonical Structure binop___inn_eqType  :=
Eval hnf in EqType (binop___inn ) (binop___inn_eqMixin ).

Inductive binop___fnn  : Type :=
	| binop___fnn__ADD  : binop___fnn 
	| binop___fnn__SUB  : binop___fnn 
	| binop___fnn__MUL  : binop___fnn 
	| binop___fnn__DIV  : binop___fnn 
	| binop___fnn__MIN  : binop___fnn 
	| binop___fnn__MAX  : binop___fnn 
	| binop___fnn__COPYSIGN  : binop___fnn .

Definition list__binop___fnn  := (list (binop___fnn )).

Definition option__binop___fnn  := (option (binop___fnn )).

Global Instance Inhabited__binop___fnn  : Inhabited (binop___fnn ) := { default_val := binop___fnn__ADD   }.

Definition binop___fnn_eq_dec : forall  (v1 v2 : binop___fnn ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition binop___fnn_eqb  (v1 v2 : binop___fnn ) : bool :=
binop___fnn_eq_dec  v1 v2.
Definition eqbinop___fnnP  : Equality.axiom (binop___fnn_eqb ) :=
eq_dec_Equality_axiom (binop___fnn ) (binop___fnn_eq_dec ).

Canonical Structure binop___fnn_eqMixin  := EqMixin (eqbinop___fnnP ).
Canonical Structure binop___fnn_eqType  :=
Eval hnf in EqType (binop___fnn ) (binop___fnn_eqMixin ).

Inductive binop_  : Type :=
	| binop___inn__entry (arg : binop___inn) : binop_ 
	| binop___fnn__entry (arg : binop___fnn) : binop_ .

Definition list__binop_  := (list (binop_ )).

Definition option__binop_  := (option (binop_ )).

Global Instance Inhabited__binop_  : Inhabited (binop_ ) := { default_val := binop___inn__entry  default_val }.

Definition binop__eq_dec : forall  (v1 v2 : binop_ ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition binop__eqb  (v1 v2 : binop_ ) : bool :=
binop__eq_dec  v1 v2.
Definition eqbinop_P  : Equality.axiom (binop__eqb ) :=
eq_dec_Equality_axiom (binop_ ) (binop__eq_dec ).

Canonical Structure binop__eqMixin  := EqMixin (eqbinop_P ).
Canonical Structure binop__eqType  :=
Eval hnf in EqType (binop_ ) (binop__eqMixin ).

(* Family Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:155.1-155.24 *)
Inductive testop___inn  : Type :=
	| testop___inn__EQZ  : testop___inn .

Definition list__testop___inn  := (list (testop___inn )).

Definition option__testop___inn  := (option (testop___inn )).

Global Instance Inhabited__testop___inn  : Inhabited (testop___inn ) := { default_val := testop___inn__EQZ   }.

Definition testop___inn_eq_dec : forall  (v1 v2 : testop___inn ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition testop___inn_eqb  (v1 v2 : testop___inn ) : bool :=
testop___inn_eq_dec  v1 v2.
Definition eqtestop___innP  : Equality.axiom (testop___inn_eqb ) :=
eq_dec_Equality_axiom (testop___inn ) (testop___inn_eq_dec ).

Canonical Structure testop___inn_eqMixin  := EqMixin (eqtestop___innP ).
Canonical Structure testop___inn_eqType  :=
Eval hnf in EqType (testop___inn ) (testop___inn_eqMixin ).

Inductive testop___fnn  : Type :=
	.

Definition list__testop___fnn  := (list (testop___fnn )).

Definition option__testop___fnn  := (option (testop___fnn )).

Global Instance Inhabited__testop___fnn  : Inhabited (testop___fnn )(* FIXME: no inhabitant found! *) .
	Admitted.

Inductive testop_  : Type :=
	| testop___inn__entry (arg : testop___inn) : testop_ 
	| testop___fnn__entry (arg : testop___fnn) : testop_ .

Definition list__testop_  := (list (testop_ )).

Definition option__testop_  := (option (testop_ )).

Global Instance Inhabited__testop_  : Inhabited (testop_ ) := { default_val := testop___inn__entry  default_val }.

Definition testop__eq_dec : forall  (v1 v2 : testop_ ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition testop__eqb  (v1 v2 : testop_ ) : bool :=
testop__eq_dec  v1 v2.
Definition eqtestop_P  : Equality.axiom (testop__eqb ) :=
eq_dec_Equality_axiom (testop_ ) (testop__eq_dec ).

Canonical Structure testop__eqMixin  := EqMixin (eqtestop_P ).
Canonical Structure testop__eqType  :=
Eval hnf in EqType (testop_ ) (testop__eqMixin ).

(* Family Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:159.1-159.23 *)
Inductive relop___inn  : Type :=
	| relop___inn__EQ  : relop___inn 
	| relop___inn__NE  : relop___inn 
	| relop___inn__LT (v_sx : sx) : relop___inn 
	| relop___inn__GT (v_sx : sx) : relop___inn 
	| relop___inn__LE (v_sx : sx) : relop___inn 
	| relop___inn__GE (v_sx : sx) : relop___inn .

Definition list__relop___inn  := (list (relop___inn )).

Definition option__relop___inn  := (option (relop___inn )).

Global Instance Inhabited__relop___inn  : Inhabited (relop___inn ) := { default_val := relop___inn__EQ   }.

Definition relop___inn_eq_dec : forall  (v1 v2 : relop___inn ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition relop___inn_eqb  (v1 v2 : relop___inn ) : bool :=
relop___inn_eq_dec  v1 v2.
Definition eqrelop___innP  : Equality.axiom (relop___inn_eqb ) :=
eq_dec_Equality_axiom (relop___inn ) (relop___inn_eq_dec ).

Canonical Structure relop___inn_eqMixin  := EqMixin (eqrelop___innP ).
Canonical Structure relop___inn_eqType  :=
Eval hnf in EqType (relop___inn ) (relop___inn_eqMixin ).

Inductive relop___fnn  : Type :=
	| relop___fnn__EQ  : relop___fnn 
	| relop___fnn__NE  : relop___fnn 
	| relop___fnn__LT  : relop___fnn 
	| relop___fnn__GT  : relop___fnn 
	| relop___fnn__LE  : relop___fnn 
	| relop___fnn__GE  : relop___fnn .

Definition list__relop___fnn  := (list (relop___fnn )).

Definition option__relop___fnn  := (option (relop___fnn )).

Global Instance Inhabited__relop___fnn  : Inhabited (relop___fnn ) := { default_val := relop___fnn__EQ   }.

Definition relop___fnn_eq_dec : forall  (v1 v2 : relop___fnn ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition relop___fnn_eqb  (v1 v2 : relop___fnn ) : bool :=
relop___fnn_eq_dec  v1 v2.
Definition eqrelop___fnnP  : Equality.axiom (relop___fnn_eqb ) :=
eq_dec_Equality_axiom (relop___fnn ) (relop___fnn_eq_dec ).

Canonical Structure relop___fnn_eqMixin  := EqMixin (eqrelop___fnnP ).
Canonical Structure relop___fnn_eqType  :=
Eval hnf in EqType (relop___fnn ) (relop___fnn_eqMixin ).

Inductive relop_  : Type :=
	| relop___inn__entry (arg : relop___inn) : relop_ 
	| relop___fnn__entry (arg : relop___fnn) : relop_ .

Definition list__relop_  := (list (relop_ )).

Definition option__relop_  := (option (relop_ )).

Global Instance Inhabited__relop_  : Inhabited (relop_ ) := { default_val := relop___inn__entry  default_val }.

Definition relop__eq_dec : forall  (v1 v2 : relop_ ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition relop__eqb  (v1 v2 : relop_ ) : bool :=
relop__eq_dec  v1 v2.
Definition eqrelop_P  : Equality.axiom (relop__eqb ) :=
eq_dec_Equality_axiom (relop_ ) (relop__eq_dec ).

Canonical Structure relop__eqMixin  := EqMixin (eqrelop_P ).
Canonical Structure relop__eqType  :=
Eval hnf in EqType (relop_ ) (relop__eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:167.1-167.37 *)
Inductive cvtop  : Type :=
	| cvtop__CONVERT  : cvtop 
	| cvtop__REINTERPRET  : cvtop .

Definition list__cvtop  := (list (cvtop )).

Definition option__cvtop  := (option (cvtop )).

Global Instance Inhabited__cvtop  : Inhabited (cvtop ) := { default_val := cvtop__CONVERT   }.

Definition cvtop_eq_dec : forall  (v1 v2 : cvtop ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition cvtop_eqb  (v1 v2 : cvtop ) : bool :=
cvtop_eq_dec  v1 v2.
Definition eqcvtopP  : Equality.axiom (cvtop_eqb ) :=
eq_dec_Equality_axiom (cvtop ) (cvtop_eq_dec ).

Canonical Structure cvtop_eqMixin  := EqMixin (eqcvtopP ).
Canonical Structure cvtop_eqType  :=
Eval hnf in EqType (cvtop ) (cvtop_eqMixin ).

(* Record Creation Definition at: spec/wasm-1.0-test/1-syntax.watsup:170.1-170.68 *)
Record memop := mkmemop
{	memop__ALIGN : u32
;	memop__OFFSET : u32
}.

Global Instance Inhabited_memop : Inhabited memop := 
{default_val := {|
	memop__ALIGN := default_val;
	memop__OFFSET := default_val|} }.

Definition list__memop  := (list (memop )).

Definition option__memop  := (option (memop )).

Definition _append_memop (arg1 arg2 : memop) :=
{|
	memop__ALIGN := arg1.(memop__ALIGN) ++ arg2.(memop__ALIGN);
	memop__OFFSET := arg1.(memop__OFFSET) ++ arg2.(memop__OFFSET);
|}.

Global Instance Append_memop : Append memop := { _append arg1 arg2 := _append_memop arg1 arg2 }.

#[export] Instance eta__memop : Settable _ := settable! mkmemop <memop__ALIGN;memop__OFFSET>.

(* Type Alias Definition at: spec/wasm-1.0-test/1-syntax.watsup:177.1-177.52 *)
Definition blocktype  := (option valtype).

Definition list__blocktype  := (list (blocktype )).

Definition option__blocktype  := (option (blocktype )).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:227.1-227.53 *)
Inductive packsize  : Type :=
	| packsize__ (v_i : nat) : packsize .

Definition list__packsize  := (list (packsize )).

Definition option__packsize  := (option (packsize )).

Global Instance Inhabited__packsize  : Inhabited (packsize ) := { default_val := packsize__  default_val }.

Definition packsize_eq_dec : forall  (v1 v2 : packsize ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition packsize_eqb  (v1 v2 : packsize ) : bool :=
packsize_eq_dec  v1 v2.
Definition eqpacksizeP  : Equality.axiom (packsize_eqb ) :=
eq_dec_Equality_axiom (packsize ) (packsize_eq_dec ).

Canonical Structure packsize_eqMixin  := EqMixin (eqpacksizeP ).
Canonical Structure packsize_eqType  :=
Eval hnf in EqType (packsize ) (packsize_eqMixin ).

(* Notation Definition at: spec/wasm-1.0-test/1-syntax.watsup:228.1-228.34 *)
Notation ww := packsize.

Definition list__ww  := (list (ww )).

Definition option__ww  := (option (ww )).

(* Mutual Recursion at: spec/wasm-1.0-test/1-syntax.watsup:230.1-236.16 *)
(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:230.1-236.16 *)
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

Definition option__instr  := (option (instr )).

Global Instance Inhabited__instr  : Inhabited (instr ) := { default_val := instr__NOP   }.

Definition instr_eq_dec : forall  (v1 v2 : instr ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition instr_eqb  (v1 v2 : instr ) : bool :=
instr_eq_dec  v1 v2.
Definition eqinstrP  : Equality.axiom (instr_eqb ) :=
eq_dec_Equality_axiom (instr ) (instr_eq_dec ).

Canonical Structure instr_eqMixin  := EqMixin (eqinstrP ).
Canonical Structure instr_eqType  :=
Eval hnf in EqType (instr ) (instr_eqMixin ).

(* Type Alias Definition at: spec/wasm-1.0-test/1-syntax.watsup:238.1-239.9 *)
Definition expr  := (list instr).

Definition list__expr  := (list (expr )).

Definition option__expr  := (option (expr )).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:249.1-250.16 *)
Inductive type  : Type :=
	| type__TYPE (v_functype : functype) : type .

Definition list__type  := (list (type )).

Definition option__type  := (option (type )).

Global Instance Inhabited__type  : Inhabited (type ) := { default_val := type__TYPE  default_val }.

Definition type_eq_dec : forall  (v1 v2 : type ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition type_eqb  (v1 v2 : type ) : bool :=
type_eq_dec  v1 v2.
Definition eqtypeP  : Equality.axiom (type_eqb ) :=
eq_dec_Equality_axiom (type ) (type_eq_dec ).

Canonical Structure type_eqMixin  := EqMixin (eqtypeP ).
Canonical Structure type_eqType  :=
Eval hnf in EqType (type ) (type_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:251.1-252.16 *)
Inductive local  : Type :=
	| local__LOCAL (v_valtype : valtype) : local .

Definition list__local  := (list (local )).

Definition option__local  := (option (local )).

Global Instance Inhabited__local  : Inhabited (local ) := { default_val := local__LOCAL  default_val }.

Definition local_eq_dec : forall  (v1 v2 : local ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition local_eqb  (v1 v2 : local ) : bool :=
local_eq_dec  v1 v2.
Definition eqlocalP  : Equality.axiom (local_eqb ) :=
eq_dec_Equality_axiom (local ) (local_eq_dec ).

Canonical Structure local_eqMixin  := EqMixin (eqlocalP ).
Canonical Structure local_eqType  :=
Eval hnf in EqType (local ) (local_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:253.1-254.27 *)
Inductive func  : Type :=
	| func__FUNC (v_typeidx : typeidx) (v__ : (list local)) (v_expr : expr) : func .

Definition list__func  := (list (func )).

Definition option__func  := (option (func )).

Global Instance Inhabited__func  : Inhabited (func ) := { default_val := func__FUNC  default_val default_val default_val }.

Definition func_eq_dec : forall  (v1 v2 : func ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition func_eqb  (v1 v2 : func ) : bool :=
func_eq_dec  v1 v2.
Definition eqfuncP  : Equality.axiom (func_eqb ) :=
eq_dec_Equality_axiom (func ) (func_eq_dec ).

Canonical Structure func_eqMixin  := EqMixin (eqfuncP ).
Canonical Structure func_eqType  :=
Eval hnf in EqType (func ) (func_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:255.1-256.25 *)
Inductive global  : Type :=
	| global__GLOBAL (v_globaltype : globaltype) (v_expr : expr) : global .

Definition list__global  := (list (global )).

Definition option__global  := (option (global )).

Global Instance Inhabited__global  : Inhabited (global ) := { default_val := global__GLOBAL  default_val default_val }.

Definition global_eq_dec : forall  (v1 v2 : global ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition global_eqb  (v1 v2 : global ) : bool :=
global_eq_dec  v1 v2.
Definition eqglobalP  : Equality.axiom (global_eqb ) :=
eq_dec_Equality_axiom (global ) (global_eq_dec ).

Canonical Structure global_eqMixin  := EqMixin (eqglobalP ).
Canonical Structure global_eqType  :=
Eval hnf in EqType (global ) (global_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:257.1-258.18 *)
Inductive table  : Type :=
	| table__TABLE (v_tabletype : tabletype) : table .

Definition list__table  := (list (table )).

Definition option__table  := (option (table )).

Global Instance Inhabited__table  : Inhabited (table ) := { default_val := table__TABLE  default_val }.

Definition table_eq_dec : forall  (v1 v2 : table ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition table_eqb  (v1 v2 : table ) : bool :=
table_eq_dec  v1 v2.
Definition eqtableP  : Equality.axiom (table_eqb ) :=
eq_dec_Equality_axiom (table ) (table_eq_dec ).

Canonical Structure table_eqMixin  := EqMixin (eqtableP ).
Canonical Structure table_eqType  :=
Eval hnf in EqType (table ) (table_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:259.1-260.17 *)
Inductive mem  : Type :=
	| mem__MEMORY (v_memtype : memtype) : mem .

Definition list__mem  := (list (mem )).

Definition option__mem  := (option (mem )).

Global Instance Inhabited__mem  : Inhabited (mem ) := { default_val := mem__MEMORY  default_val }.

Definition mem_eq_dec : forall  (v1 v2 : mem ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition mem_eqb  (v1 v2 : mem ) : bool :=
mem_eq_dec  v1 v2.
Definition eqmemP  : Equality.axiom (mem_eqb ) :=
eq_dec_Equality_axiom (mem ) (mem_eq_dec ).

Canonical Structure mem_eqMixin  := EqMixin (eqmemP ).
Canonical Structure mem_eqType  :=
Eval hnf in EqType (mem ) (mem_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:261.1-262.21 *)
Inductive elem  : Type :=
	| elem__ELEM (v_expr : expr) (v__ : (list funcidx)) : elem .

Definition list__elem  := (list (elem )).

Definition option__elem  := (option (elem )).

Global Instance Inhabited__elem  : Inhabited (elem ) := { default_val := elem__ELEM  default_val default_val }.

Definition elem_eq_dec : forall  (v1 v2 : elem ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition elem_eqb  (v1 v2 : elem ) : bool :=
elem_eq_dec  v1 v2.
Definition eqelemP  : Equality.axiom (elem_eqb ) :=
eq_dec_Equality_axiom (elem ) (elem_eq_dec ).

Canonical Structure elem_eqMixin  := EqMixin (eqelemP ).
Canonical Structure elem_eqType  :=
Eval hnf in EqType (elem ) (elem_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:263.1-264.18 *)
Inductive data  : Type :=
	| data__DATA (v_expr : expr) (v__ : (list byte)) : data .

Definition list__data  := (list (data )).

Definition option__data  := (option (data )).

Global Instance Inhabited__data  : Inhabited (data ) := { default_val := data__DATA  default_val default_val }.

Definition data_eq_dec : forall  (v1 v2 : data ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition data_eqb  (v1 v2 : data ) : bool :=
data_eq_dec  v1 v2.
Definition eqdataP  : Equality.axiom (data_eqb ) :=
eq_dec_Equality_axiom (data ) (data_eq_dec ).

Canonical Structure data_eqMixin  := EqMixin (eqdataP ).
Canonical Structure data_eqType  :=
Eval hnf in EqType (data ) (data_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:265.1-266.16 *)
Inductive start  : Type :=
	| start__START (v_funcidx : funcidx) : start .

Definition list__start  := (list (start )).

Definition option__start  := (option (start )).

Global Instance Inhabited__start  : Inhabited (start ) := { default_val := start__START  default_val }.

Definition start_eq_dec : forall  (v1 v2 : start ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition start_eqb  (v1 v2 : start ) : bool :=
start_eq_dec  v1 v2.
Definition eqstartP  : Equality.axiom (start_eqb ) :=
eq_dec_Equality_axiom (start ) (start_eq_dec ).

Canonical Structure start_eqMixin  := EqMixin (eqstartP ).
Canonical Structure start_eqType  :=
Eval hnf in EqType (start ) (start_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:268.1-269.66 *)
Inductive externidx  : Type :=
	| externidx__FUNC (v_funcidx : funcidx) : externidx 
	| externidx__GLOBAL (v_globalidx : globalidx) : externidx 
	| externidx__TABLE (v_tableidx : tableidx) : externidx 
	| externidx__MEM (v_memidx : memidx) : externidx .

Definition list__externidx  := (list (externidx )).

Definition option__externidx  := (option (externidx )).

Global Instance Inhabited__externidx  : Inhabited (externidx ) := { default_val := externidx__FUNC  default_val }.

Definition externidx_eq_dec : forall  (v1 v2 : externidx ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition externidx_eqb  (v1 v2 : externidx ) : bool :=
externidx_eq_dec  v1 v2.
Definition eqexternidxP  : Equality.axiom (externidx_eqb ) :=
eq_dec_Equality_axiom (externidx ) (externidx_eq_dec ).

Canonical Structure externidx_eqMixin  := EqMixin (eqexternidxP ).
Canonical Structure externidx_eqType  :=
Eval hnf in EqType (externidx ) (externidx_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:270.1-271.24 *)
Inductive export  : Type :=
	| export__EXPORT (v_name : name) (v_externidx : externidx) : export .

Definition list__export  := (list (export )).

Definition option__export  := (option (export )).

Global Instance Inhabited__export  : Inhabited (export ) := { default_val := export__EXPORT  default_val default_val }.

Definition export_eq_dec : forall  (v1 v2 : export ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition export_eqb  (v1 v2 : export ) : bool :=
export_eq_dec  v1 v2.
Definition eqexportP  : Equality.axiom (export_eqb ) :=
eq_dec_Equality_axiom (export ) (export_eq_dec ).

Canonical Structure export_eqMixin  := EqMixin (eqexportP ).
Canonical Structure export_eqType  :=
Eval hnf in EqType (export ) (export_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:272.1-273.30 *)
Inductive import  : Type :=
	| import__IMPORT (v_name : name) (v__ : name) (v_externtype : externtype) : import .

Definition list__import  := (list (import )).

Definition option__import  := (option (import )).

Global Instance Inhabited__import  : Inhabited (import ) := { default_val := import__IMPORT  default_val default_val default_val }.

Definition import_eq_dec : forall  (v1 v2 : import ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition import_eqb  (v1 v2 : import ) : bool :=
import_eq_dec  v1 v2.
Definition eqimportP  : Equality.axiom (import_eqb ) :=
eq_dec_Equality_axiom (import ) (import_eq_dec ).

Canonical Structure import_eqMixin  := EqMixin (eqimportP ).
Canonical Structure import_eqType  :=
Eval hnf in EqType (import ) (import_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/1-syntax.watsup:275.1-276.76 *)
Inductive module  : Type :=
	| module__MODULE (v__ : (list type)) (v__ : (list import)) (v__ : (list func)) (v__ : (list global)) (v__ : (list table)) (v__ : (list mem)) (v__ : (list elem)) (v__ : (list data)) (v__ : (list start)) (v__ : (list export)) : module .

Definition list__module  := (list (module )).

Definition option__module  := (option (module )).

Global Instance Inhabited__module  : Inhabited (module ) := { default_val := module__MODULE  default_val default_val default_val default_val default_val default_val default_val default_val default_val default_val }.

Definition module_eq_dec : forall  (v1 v2 : module ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition module_eqb  (v1 v2 : module ) : bool :=
module_eq_dec  v1 v2.
Definition eqmoduleP  : Equality.axiom (module_eqb ) :=
eq_dec_Equality_axiom (module ) (module_eq_dec ).

Canonical Structure module_eqMixin  := EqMixin (eqmoduleP ).
Canonical Structure module_eqType  :=
Eval hnf in EqType (module ) (module_eqMixin ).

(* Mutual Recursion at: spec/wasm-1.0-test/2-syntax-aux.watsup:20.1-20.64 *)
(* Auxiliary Definition at: spec/wasm-1.0-test/2-syntax-aux.watsup:20.1-20.64 *)
Fixpoint fun_funcsxt (v___0 : (list externtype)) : (list functype) :=
	match (v___0) with
		| ([]) => []
		| (((externtype__FUNC v_ft) :: v_xt)) => (@app _ [v_ft] (fun_funcsxt v_xt))
		| ((v_externtype :: v_xt)) => (fun_funcsxt v_xt)
	end.

(* Mutual Recursion at: spec/wasm-1.0-test/2-syntax-aux.watsup:21.1-21.66 *)
(* Auxiliary Definition at: spec/wasm-1.0-test/2-syntax-aux.watsup:21.1-21.66 *)
Fixpoint fun_globalsxt (v___0 : (list externtype)) : (list globaltype) :=
	match (v___0) with
		| ([]) => []
		| (((externtype__GLOBAL v_gt) :: v_xt)) => (@app _ [v_gt] (fun_globalsxt v_xt))
		| ((v_externtype :: v_xt)) => (fun_globalsxt v_xt)
	end.

(* Mutual Recursion at: spec/wasm-1.0-test/2-syntax-aux.watsup:22.1-22.65 *)
(* Auxiliary Definition at: spec/wasm-1.0-test/2-syntax-aux.watsup:22.1-22.65 *)
Fixpoint fun_tablesxt (v___0 : (list externtype)) : (list tabletype) :=
	match (v___0) with
		| ([]) => []
		| (((externtype__TABLE v_reserved__tt) :: v_xt)) => (@app _ [v_reserved__tt] (fun_tablesxt v_xt))
		| ((v_externtype :: v_xt)) => (fun_tablesxt v_xt)
	end.

(* Mutual Recursion at: spec/wasm-1.0-test/2-syntax-aux.watsup:23.1-23.63 *)
(* Auxiliary Definition at: spec/wasm-1.0-test/2-syntax-aux.watsup:23.1-23.63 *)
Fixpoint fun_memsxt (v___0 : (list externtype)) : (list memtype) :=
	match (v___0) with
		| ([]) => []
		| (((externtype__MEM v_mt) :: v_xt)) => (@app _ [v_mt] (fun_memsxt v_xt))
		| ((v_externtype :: v_xt)) => (fun_memsxt v_xt)
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/2-syntax-aux.watsup:49.1-49.33 *)
Definition fun_memop0 : memop := {| memop__ALIGN := 0; memop__OFFSET := 0 |}.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:7.1-7.57 *)
Axiom fun_signed : forall (v_reserved__N_0 : reserved__N) (v_reserved__nat_1 : nat), nat.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:10.1-10.66 *)
Axiom fun_invsigned : forall (v_reserved__N_0 : reserved__N) (v_int_1 : nat), nat.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:74.1-74.57 *)
Axiom fun_fabs : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:77.1-77.58 *)
Axiom fun_fceil : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:78.1-78.58 *)
Axiom fun_ffloor : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:80.1-80.61 *)
Axiom fun_fnearest : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:75.1-75.57 *)
Axiom fun_fneg : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:76.1-76.58 *)
Axiom fun_fsqrt : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:79.1-79.58 *)
Axiom fun_ftrunc : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:56.1-56.57 *)
Axiom fun_iclz : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN), iN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:57.1-57.57 *)
Axiom fun_ictz : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN), iN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:58.1-58.60 *)
Axiom fun_ipopcnt : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN), iN.

(* Auxiliary Definition at: spec/wasm-1.0-test/3-numerics.watsup:16.1-17.32 *)
Definition fun_unop (v_valtype_0 : valtype) (v_unop__1 : unop_) (v_val__2 : val_) : option__val_ :=
	match (v_valtype_0, v_unop__1, v_val__2) with
		| ((valtype__INN v_inn), (unop___inn__entry (unop___inn__CLZ )), (val___inn__entry v_iN)) => (Some ((fun_iclz (fun_size (valtype__INN v_inn)) v_iN) : val_))
		| ((valtype__INN v_inn), (unop___inn__entry (unop___inn__CTZ )), (val___inn__entry v_iN)) => (Some ((fun_ictz (fun_size (valtype__INN v_inn)) v_iN) : val_))
		| ((valtype__INN v_inn), (unop___inn__entry (unop___inn__POPCNT )), (val___inn__entry v_iN)) => (Some ((fun_ipopcnt (fun_size (valtype__INN v_inn)) v_iN) : val_))
		| ((valtype__FNN v_fnn), (unop___fnn__entry (unop___fnn__ABS )), (val___fnn__entry v_fN)) => (Some ((fun_fabs (fun_size (valtype__FNN v_fnn)) v_fN) : val_))
		| ((valtype__FNN v_fnn), (unop___fnn__entry (unop___fnn__NEG )), (val___fnn__entry v_fN)) => (Some ((fun_fneg (fun_size (valtype__FNN v_fnn)) v_fN) : val_))
		| ((valtype__FNN v_fnn), (unop___fnn__entry (unop___fnn__SQRT )), (val___fnn__entry v_fN)) => (Some ((fun_fsqrt (fun_size (valtype__FNN v_fnn)) v_fN) : val_))
		| ((valtype__FNN v_fnn), (unop___fnn__entry (unop___fnn__CEIL )), (val___fnn__entry v_fN)) => (Some ((fun_fceil (fun_size (valtype__FNN v_fnn)) v_fN) : val_))
		| ((valtype__FNN v_fnn), (unop___fnn__entry (unop___fnn__FLOOR )), (val___fnn__entry v_fN)) => (Some ((fun_ffloor (fun_size (valtype__FNN v_fnn)) v_fN) : val_))
		| ((valtype__FNN v_fnn), (unop___fnn__entry (unop___fnn__TRUNC )), (val___fnn__entry v_fN)) => (Some ((fun_ftrunc (fun_size (valtype__FNN v_fnn)) v_fN) : val_))
		| ((valtype__FNN v_fnn), (unop___fnn__entry (unop___fnn__NEAREST )), (val___fnn__entry v_fN)) => (Some ((fun_fnearest (fun_size (valtype__FNN v_fnn)) v_fN) : val_))
		| _ => default_val
	end.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:67.1-67.56 *)
Axiom fun_fadd : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN) (v_fN_2 : fN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:73.1-73.61 *)
Axiom fun_fcopysign : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN) (v_fN_2 : fN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:70.1-70.56 *)
Axiom fun_fdiv : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN) (v_fN_2 : fN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:72.1-72.56 *)
Axiom fun_fmax : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN) (v_fN_2 : fN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:71.1-71.56 *)
Axiom fun_fmin : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN) (v_fN_2 : fN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:69.1-69.56 *)
Axiom fun_fmul : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN) (v_fN_2 : fN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:68.1-68.56 *)
Axiom fun_fsub : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN) (v_fN_2 : fN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:43.1-43.55 *)
Axiom fun_iadd : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN) (v_iN_2 : iN), iN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:49.1-49.56 *)
Axiom fun_iand : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN) (v_iN_2 : iN), iN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:46.1-46.64 *)
Axiom fun_idiv : forall (v_reserved__N_0 : reserved__N) (v_sx_1 : sx) (v_iN_2 : iN) (v_iN_3 : iN), iN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:45.1-45.56 *)
Axiom fun_imul : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN) (v_iN_2 : iN), iN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:50.1-50.55 *)
Axiom fun_ior : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN) (v_iN_2 : iN), iN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:47.1-47.64 *)
Axiom fun_irem : forall (v_reserved__N_0 : reserved__N) (v_sx_1 : sx) (v_iN_2 : iN) (v_iN_3 : iN), iN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:54.1-54.57 *)
Axiom fun_irotl : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN) (v_iN_2 : iN), iN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:55.1-55.57 *)
Axiom fun_irotr : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN) (v_iN_2 : iN), iN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:52.1-52.59 *)
Axiom fun_ishl : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN) (v_u32_2 : u32), iN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:53.1-53.67 *)
Axiom fun_ishr : forall (v_reserved__N_0 : reserved__N) (v_sx_1 : sx) (v_iN_2 : iN) (v_u32_3 : u32), iN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:44.1-44.56 *)
Axiom fun_isub : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN) (v_iN_2 : iN), iN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:51.1-51.56 *)
Axiom fun_ixor : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN) (v_iN_2 : iN), iN.

(* Auxiliary Definition at: spec/wasm-1.0-test/3-numerics.watsup:18.1-19.34 *)
Definition fun_binop (v_valtype_0 : valtype) (v_binop__1 : binop_) (v_val__2 : val_) (v_val__3 : val_) : option__val_ :=
	match (v_valtype_0, v_binop__1, v_val__2, v_val__3) with
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__ADD )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (Some ((fun_iadd (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_))
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__SUB )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (Some ((fun_isub (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_))
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__MUL )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (Some ((fun_imul (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_))
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__DIV v_sx)), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (Some ((fun_idiv (fun_size (valtype__INN v_inn)) v_sx v_iN_1 v_iN_2) : val_))
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__REM v_sx)), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (Some ((fun_irem (fun_size (valtype__INN v_inn)) v_sx v_iN_1 v_iN_2) : val_))
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__AND )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (Some ((fun_iand (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_))
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__OR )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (Some ((fun_ior (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_))
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__XOR )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (Some ((fun_ixor (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_))
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__SHL )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (Some ((fun_ishl (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_))
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__SHR v_sx)), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (Some ((fun_ishr (fun_size (valtype__INN v_inn)) v_sx v_iN_1 v_iN_2) : val_))
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__ROTL )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (Some ((fun_irotl (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_))
		| ((valtype__INN v_inn), (binop___inn__entry (binop___inn__ROTR )), (val___inn__entry v_iN_1), (val___inn__entry v_iN_2)) => (Some ((fun_irotr (fun_size (valtype__INN v_inn)) v_iN_1 v_iN_2) : val_))
		| ((valtype__FNN v_fnn), (binop___fnn__entry (binop___fnn__ADD )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => (Some ((fun_fadd (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2) : val_))
		| ((valtype__FNN v_fnn), (binop___fnn__entry (binop___fnn__SUB )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => (Some ((fun_fsub (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2) : val_))
		| ((valtype__FNN v_fnn), (binop___fnn__entry (binop___fnn__MUL )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => (Some ((fun_fmul (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2) : val_))
		| ((valtype__FNN v_fnn), (binop___fnn__entry (binop___fnn__DIV )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => (Some ((fun_fdiv (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2) : val_))
		| ((valtype__FNN v_fnn), (binop___fnn__entry (binop___fnn__MIN )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => (Some ((fun_fmin (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2) : val_))
		| ((valtype__FNN v_fnn), (binop___fnn__entry (binop___fnn__MAX )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => (Some ((fun_fmax (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2) : val_))
		| ((valtype__FNN v_fnn), (binop___fnn__entry (binop___fnn__COPYSIGN )), (val___fnn__entry v_fN_1), (val___fnn__entry v_fN_2)) => (Some ((fun_fcopysign (fun_size (valtype__FNN v_fnn)) v_fN_1 v_fN_2) : val_))
		| _ => default_val
	end.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:59.1-59.60 *)
Axiom fun_ieqz : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN), u32.

(* Auxiliary Definition at: spec/wasm-1.0-test/3-numerics.watsup:20.1-21.32 *)
Definition fun_testop (v_valtype_0 : valtype) (v_testop__1 : testop_) (v_val__2 : val_) : val_ :=
	match (v_valtype_0, v_testop__1, v_val__2) with
		| ((valtype__INN v_inn), (testop___inn__entry (testop___inn__EQZ )), (val___inn__entry v_iN)) => (fun_ieqz (fun_size (valtype__INN v_inn)) v_iN)
		| _ => default_val
	end.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:81.1-81.58 *)
Axiom fun_feq : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN) (v_fN_2 : fN), u32.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:86.1-86.58 *)
Axiom fun_fge : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN) (v_fN_2 : fN), u32.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:84.1-84.58 *)
Axiom fun_fgt : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN) (v_fN_2 : fN), u32.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:85.1-85.58 *)
Axiom fun_fle : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN) (v_fN_2 : fN), u32.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:83.1-83.58 *)
Axiom fun_flt : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN) (v_fN_2 : fN), u32.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:82.1-82.58 *)
Axiom fun_fne : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN) (v_fN_2 : fN), u32.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:60.1-60.58 *)
Axiom fun_ieq : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN) (v_iN_2 : iN), u32.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:65.1-65.66 *)
Axiom fun_ige : forall (v_reserved__N_0 : reserved__N) (v_sx_1 : sx) (v_iN_2 : iN) (v_iN_3 : iN), u32.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:63.1-63.66 *)
Axiom fun_igt : forall (v_reserved__N_0 : reserved__N) (v_sx_1 : sx) (v_iN_2 : iN) (v_iN_3 : iN), u32.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:64.1-64.66 *)
Axiom fun_ile : forall (v_reserved__N_0 : reserved__N) (v_sx_1 : sx) (v_iN_2 : iN) (v_iN_3 : iN), u32.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:62.1-62.66 *)
Axiom fun_ilt : forall (v_reserved__N_0 : reserved__N) (v_sx_1 : sx) (v_iN_2 : iN) (v_iN_3 : iN), u32.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:61.1-61.58 *)
Axiom fun_ine : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN) (v_iN_2 : iN), u32.

(* Auxiliary Definition at: spec/wasm-1.0-test/3-numerics.watsup:22.1-23.34 *)
Definition fun_relop (v_valtype_0 : valtype) (v_relop__1 : relop_) (v_val__2 : val_) (v_val__3 : val_) : val_ :=
	match (v_valtype_0, v_relop__1, v_val__2, v_val__3) with
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

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:32.1-32.84 *)
Axiom fun_convert : forall (v_M_0 : M) (v_reserved__N_1 : reserved__N) (v_sx_2 : sx) (v_iN_3 : iN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:30.1-30.79 *)
Axiom fun_demote : forall (v_M_0 : M) (v_reserved__N_1 : reserved__N) (v_fN_2 : fN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:28.1-28.80 *)
Axiom fun_ext : forall (v_M_0 : M) (v_reserved__N_1 : reserved__N) (v_sx_2 : sx) (v_iN_3 : iN), iN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:31.1-31.80 *)
Axiom fun_promote : forall (v_M_0 : M) (v_reserved__N_1 : reserved__N) (v_fN_2 : fN), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:33.1-34.35 *)
Axiom fun_reinterpret : forall (v_valtype_1_0 : valtype) (v_valtype_2_1 : valtype) (v_val__2 : val_), val_.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:29.1-29.82 *)
Axiom fun_trunc : forall (v_M_0 : M) (v_reserved__N_1 : reserved__N) (v_sx_2 : sx) (v_fN_3 : fN), iN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:27.1-27.77 *)
Axiom fun_wrap : forall (v_M_0 : M) (v_reserved__N_1 : reserved__N) (v_iN_2 : iN), iN.

(* Auxiliary Definition at: spec/wasm-1.0-test/3-numerics.watsup:24.1-25.42 *)
Definition fun_cvtop (v_valtype_1_0 : valtype) (v_valtype_2_1 : valtype) (v_cvtop_2 : cvtop) (v___3 : (option sx)) (v_val__4 : val_) : option__val_ :=
	match (v_valtype_1_0, v_valtype_2_1, v_cvtop_2, v___3, v_val__4) with
		| ((valtype__INN (inn__I32 )), (valtype__INN (inn__I64 )), (cvtop__CONVERT ), (Some v_sx), (val___inn__entry v_iN)) => (Some ((fun_ext 32 64 v_sx v_iN) : val_))
		| ((valtype__INN (inn__I64 )), (valtype__INN (inn__I32 )), (cvtop__CONVERT ), v_sx, (val___inn__entry v_iN)) => (Some ((fun_wrap 64 32 v_iN) : val_))
		| ((valtype__FNN v_fnn), (valtype__INN v_inn), (cvtop__CONVERT ), (Some v_sx), (val___fnn__entry v_fN)) => (Some ((fun_trunc (fun_size (valtype__FNN v_fnn)) (fun_size (valtype__INN v_inn)) v_sx v_fN) : val_))
		| ((valtype__FNN (fnn__F32 )), (valtype__FNN (fnn__F64 )), (cvtop__CONVERT ), v_sx, (val___fnn__entry v_fN)) => (Some ((fun_promote 32 64 v_fN) : val_))
		| ((valtype__FNN (fnn__F64 )), (valtype__FNN (fnn__F32 )), (cvtop__CONVERT ), v_sx, (val___fnn__entry v_fN)) => (Some ((fun_demote 64 32 v_fN) : val_))
		| ((valtype__INN v_inn), (valtype__FNN v_fnn), (cvtop__CONVERT ), (Some v_sx), (val___inn__entry v_iN)) => (Some ((fun_convert (fun_size (valtype__INN v_inn)) (fun_size (valtype__FNN v_fnn)) v_sx v_iN) : val_))
		| ((valtype__INN v_inn), (valtype__FNN v_fnn), (cvtop__REINTERPRET ), v_sx, (val___inn__entry v_iN)) => (Some ((fun_reinterpret (valtype__INN v_inn) (valtype__FNN v_fnn) (v_iN : val_)) : val_))
		| ((valtype__FNN v_fnn), (valtype__INN v_inn), (cvtop__REINTERPRET ), v_sx, (val___fnn__entry v_fN)) => (Some ((fun_reinterpret (valtype__FNN v_fnn) (valtype__INN v_inn) (v_fN : val_)) : val_))
		| _ => default_val
	end.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:36.1-36.75 *)
Axiom fun_ibytes : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN), (list__byte ).

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:37.1-37.75 *)
Axiom fun_fbytes : forall (v_reserved__N_0 : reserved__N) (v_fN_1 : fN), (list__byte ).

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:38.1-38.76 *)
Axiom fun_bytes : forall (v_valtype_0 : valtype) (v_val__1 : val_), (list__byte ).

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:40.1-40.30 *)
Axiom fun_invibytes : forall (v_reserved__N_0 : reserved__N) (v___1 : (list byte)), iN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:41.1-41.30 *)
Axiom fun_invfbytes : forall (v_reserved__N_0 : reserved__N) (v___1 : (list byte)), fN.

(* Axiom Definition at: spec/wasm-1.0-test/3-numerics.watsup:48.1-48.57 *)
Axiom fun_inot : forall (v_reserved__N_0 : reserved__N) (v_iN_1 : iN), iN.

(* Notation Definition at: spec/wasm-1.0-test/4-runtime.watsup:5.1-5.39 *)
Notation addr := nat.

Definition list__addr  := (list (addr )).

Definition option__addr  := (option (addr )).

(* Notation Definition at: spec/wasm-1.0-test/4-runtime.watsup:6.1-6.53 *)
Notation funcaddr := addr.

Definition list__funcaddr  := (list (funcaddr )).

Definition option__funcaddr  := (option (funcaddr )).

(* Notation Definition at: spec/wasm-1.0-test/4-runtime.watsup:7.1-7.53 *)
Notation globaladdr := addr.

Definition list__globaladdr  := (list (globaladdr )).

Definition option__globaladdr  := (option (globaladdr )).

(* Notation Definition at: spec/wasm-1.0-test/4-runtime.watsup:8.1-8.51 *)
Notation tableaddr := addr.

Definition list__tableaddr  := (list (tableaddr )).

Definition option__tableaddr  := (option (tableaddr )).

(* Notation Definition at: spec/wasm-1.0-test/4-runtime.watsup:9.1-9.50 *)
Notation memaddr := addr.

Definition list__memaddr  := (list (memaddr )).

Definition option__memaddr  := (option (memaddr )).

(* Inductive Type Definition at: spec/wasm-1.0-test/4-runtime.watsup:24.1-25.55 *)
Inductive val  : Type :=
	| val__CONST (v_valtype : valtype) (v_val_ : val_) : val .

Definition list__val  := (list (val )).

Definition option__val  := (option (val )).

Global Instance Inhabited__val  : Inhabited (val ) := { default_val := val__CONST  default_val default_val }.

Definition val_eq_dec : forall  (v1 v2 : val ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition val_eqb  (v1 v2 : val ) : bool :=
val_eq_dec  v1 v2.
Definition eqvalP  : Equality.axiom (val_eqb ) :=
eq_dec_Equality_axiom (val ) (val_eq_dec ).

Canonical Structure val_eqMixin  := EqMixin (eqvalP ).
Canonical Structure val_eqType  :=
Eval hnf in EqType (val ) (val_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/4-runtime.watsup:27.1-28.22 *)
Inductive result  : Type :=
	| result___VALS (v__ : (list val)) : result 
	| result__TRAP  : result .

Definition list__result  := (list (result )).

Definition option__result  := (option (result )).

Global Instance Inhabited__result  : Inhabited (result ) := { default_val := result___VALS  default_val }.

Definition result_eq_dec : forall  (v1 v2 : result ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition result_eqb  (v1 v2 : result ) : bool :=
result_eq_dec  v1 v2.
Definition eqresultP  : Equality.axiom (result_eqb ) :=
eq_dec_Equality_axiom (result ) (result_eq_dec ).

Canonical Structure result_eqMixin  := EqMixin (eqresultP ).
Canonical Structure result_eqType  :=
Eval hnf in EqType (result ) (result_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/4-runtime.watsup:36.1-37.70 *)
Inductive externval  : Type :=
	| externval__FUNC (v_funcaddr : funcaddr) : externval 
	| externval__GLOBAL (v_globaladdr : globaladdr) : externval 
	| externval__TABLE (v_tableaddr : tableaddr) : externval 
	| externval__MEM (v_memaddr : memaddr) : externval .

Definition list__externval  := (list (externval )).

Definition option__externval  := (option (externval )).

Global Instance Inhabited__externval  : Inhabited (externval ) := { default_val := externval__FUNC  default_val }.

Definition externval_eq_dec : forall  (v1 v2 : externval ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition externval_eqb  (v1 v2 : externval ) : bool :=
externval_eq_dec  v1 v2.
Definition eqexternvalP  : Equality.axiom (externval_eqb ) :=
eq_dec_Equality_axiom (externval ) (externval_eq_dec ).

Canonical Structure externval_eqMixin  := EqMixin (eqexternvalP ).
Canonical Structure externval_eqType  :=
Eval hnf in EqType (externval ) (externval_eqMixin ).

(* Record Creation Definition at: spec/wasm-1.0-test/4-runtime.watsup:61.1-63.22 *)
Record exportinst := mkexportinst
{	exportinst__NAME : name
;	exportinst__VALUE : externval
}.

Global Instance Inhabited_exportinst : Inhabited exportinst := 
{default_val := {|
	exportinst__NAME := default_val;
	exportinst__VALUE := default_val|} }.

Definition list__exportinst  := (list (exportinst )).

Definition option__exportinst  := (option (exportinst )).

Definition _append_exportinst (arg1 arg2 : exportinst) :=
{|
	exportinst__NAME := arg1.(exportinst__NAME); (* FIXME: This type does not have a trivial way to append *)
	exportinst__VALUE := arg1.(exportinst__VALUE); (* FIXME: This type does not have a trivial way to append *)
|}.

Global Instance Append_exportinst : Append exportinst := { _append arg1 arg2 := _append_exportinst arg1 arg2 }.

#[export] Instance eta__exportinst : Settable _ := settable! mkexportinst <exportinst__NAME;exportinst__VALUE>.

(* Record Creation Definition at: spec/wasm-1.0-test/4-runtime.watsup:65.1-71.26 *)
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

Definition option__moduleinst  := (option (moduleinst )).

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

(* Record Creation Definition at: spec/wasm-1.0-test/4-runtime.watsup:48.1-51.16 *)
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

Definition option__funcinst  := (option (funcinst )).

Definition _append_funcinst (arg1 arg2 : funcinst) :=
{|
	funcinst__TYPE := arg1.(funcinst__TYPE); (* FIXME: This type does not have a trivial way to append *)
	funcinst__MODULE := arg1.(funcinst__MODULE) ++ arg2.(funcinst__MODULE);
	funcinst__CODE := arg1.(funcinst__CODE); (* FIXME: This type does not have a trivial way to append *)
|}.

Global Instance Append_funcinst : Append funcinst := { _append arg1 arg2 := _append_funcinst arg1 arg2 }.

#[export] Instance eta__funcinst : Settable _ := settable! mkfuncinst <funcinst__TYPE;funcinst__MODULE;funcinst__CODE>.

(* Record Creation Definition at: spec/wasm-1.0-test/4-runtime.watsup:52.1-54.16 *)
Record globalinst := mkglobalinst
{	globalinst__TYPE : globaltype
;	globalinst__VALUE : val
}.

Global Instance Inhabited_globalinst : Inhabited globalinst := 
{default_val := {|
	globalinst__TYPE := default_val;
	globalinst__VALUE := default_val|} }.

Definition list__globalinst  := (list (globalinst )).

Definition option__globalinst  := (option (globalinst )).

Definition _append_globalinst (arg1 arg2 : globalinst) :=
{|
	globalinst__TYPE := arg1.(globalinst__TYPE); (* FIXME: This type does not have a trivial way to append *)
	globalinst__VALUE := arg1.(globalinst__VALUE); (* FIXME: This type does not have a trivial way to append *)
|}.

Global Instance Append_globalinst : Append globalinst := { _append arg1 arg2 := _append_globalinst arg1 arg2 }.

#[export] Instance eta__globalinst : Settable _ := settable! mkglobalinst <globalinst__TYPE;globalinst__VALUE>.

(* Record Creation Definition at: spec/wasm-1.0-test/4-runtime.watsup:55.1-57.24 *)
Record tableinst := mktableinst
{	tableinst__TYPE : tabletype
;	tableinst__REFS : (list (option funcaddr))
}.

Global Instance Inhabited_tableinst : Inhabited tableinst := 
{default_val := {|
	tableinst__TYPE := default_val;
	tableinst__REFS := default_val|} }.

Definition list__tableinst  := (list (tableinst )).

Definition option__tableinst  := (option (tableinst )).

Definition _append_tableinst (arg1 arg2 : tableinst) :=
{|
	tableinst__TYPE := arg1.(tableinst__TYPE); (* FIXME: This type does not have a trivial way to append *)
	tableinst__REFS := arg1.(tableinst__REFS) ++ arg2.(tableinst__REFS);
|}.

Global Instance Append_tableinst : Append tableinst := { _append arg1 arg2 := _append_tableinst arg1 arg2 }.

#[export] Instance eta__tableinst : Settable _ := settable! mktableinst <tableinst__TYPE;tableinst__REFS>.

(* Record Creation Definition at: spec/wasm-1.0-test/4-runtime.watsup:58.1-60.18 *)
Record meminst := mkmeminst
{	meminst__TYPE : memtype
;	meminst__BYTES : (list byte)
}.

Global Instance Inhabited_meminst : Inhabited meminst := 
{default_val := {|
	meminst__TYPE := default_val;
	meminst__BYTES := default_val|} }.

Definition list__meminst  := (list (meminst )).

Definition option__meminst  := (option (meminst )).

Definition _append_meminst (arg1 arg2 : meminst) :=
{|
	meminst__TYPE := arg1.(meminst__TYPE); (* FIXME: This type does not have a trivial way to append *)
	meminst__BYTES := arg1.(meminst__BYTES) ++ arg2.(meminst__BYTES);
|}.

Global Instance Append_meminst : Append meminst := { _append arg1 arg2 := _append_meminst arg1 arg2 }.

#[export] Instance eta__meminst : Settable _ := settable! mkmeminst <meminst__TYPE;meminst__BYTES>.

(* Record Creation Definition at: spec/wasm-1.0-test/4-runtime.watsup:83.1-87.20 *)
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

Definition option__store  := (option (store )).

Definition _append_store (arg1 arg2 : store) :=
{|
	store__FUNCS := arg1.(store__FUNCS) ++ arg2.(store__FUNCS);
	store__GLOBALS := arg1.(store__GLOBALS) ++ arg2.(store__GLOBALS);
	store__TABLES := arg1.(store__TABLES) ++ arg2.(store__TABLES);
	store__MEMS := arg1.(store__MEMS) ++ arg2.(store__MEMS);
|}.

Global Instance Append_store : Append store := { _append arg1 arg2 := _append_store arg1 arg2 }.

#[export] Instance eta__store : Settable _ := settable! mkstore <store__FUNCS;store__GLOBALS;store__TABLES;store__MEMS>.

(* Record Creation Definition at: spec/wasm-1.0-test/4-runtime.watsup:89.1-91.24 *)
Record frame := mkframe
{	frame__LOCALS : (list val)
;	frame__MODULE : moduleinst
}.

Global Instance Inhabited_frame : Inhabited frame := 
{default_val := {|
	frame__LOCALS := default_val;
	frame__MODULE := default_val|} }.

Definition list__frame  := (list (frame )).

Definition option__frame  := (option (frame )).

Definition _append_frame (arg1 arg2 : frame) :=
{|
	frame__LOCALS := arg1.(frame__LOCALS) ++ arg2.(frame__LOCALS);
	frame__MODULE := arg1.(frame__MODULE) ++ arg2.(frame__MODULE);
|}.

Global Instance Append_frame : Append frame := { _append arg1 arg2 := _append_frame arg1 arg2 }.

#[export] Instance eta__frame : Settable _ := settable! mkframe <frame__LOCALS;frame__MODULE>.

(* Inductive Type Definition at: spec/wasm-1.0-test/4-runtime.watsup:93.1-93.47 *)
Inductive state  : Type :=
	| state__ (v_store : store) (v_frame : frame) : state .

Definition list__state  := (list (state )).

Definition option__state  := (option (state )).

Global Instance Inhabited__state  : Inhabited (state ) := { default_val := state__  default_val default_val }.

Definition state_eq_dec : forall  (v1 v2 : state ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition state_eqb  (v1 v2 : state ) : bool :=
state_eq_dec  v1 v2.
Definition eqstateP  : Equality.axiom (state_eqb ) :=
eq_dec_Equality_axiom (state ) (state_eq_dec ).

Canonical Structure state_eqMixin  := EqMixin (eqstateP ).
Canonical Structure state_eqType  :=
Eval hnf in EqType (state ) (state_eqMixin ).

(* Mutual Recursion at: spec/wasm-1.0-test/4-runtime.watsup:105.1-110.9 *)
(* Inductive Type Definition at: spec/wasm-1.0-test/4-runtime.watsup:105.1-110.9 *)
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

Definition option__admininstr  := (option (admininstr )).

Global Instance Inhabited__admininstr  : Inhabited (admininstr ) := { default_val := admininstr__NOP   }.

Definition admininstr_eq_dec : forall  (v1 v2 : admininstr ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition admininstr_eqb  (v1 v2 : admininstr ) : bool :=
admininstr_eq_dec  v1 v2.
Definition eqadmininstrP  : Equality.axiom (admininstr_eqb ) :=
eq_dec_Equality_axiom (admininstr ) (admininstr_eq_dec ).

Canonical Structure admininstr_eqMixin  := EqMixin (eqadmininstrP ).
Canonical Structure admininstr_eqType  :=
Eval hnf in EqType (admininstr ) (admininstr_eqMixin ).

(* Inductive Type Definition at: spec/wasm-1.0-test/4-runtime.watsup:94.1-94.62 *)
Inductive config  : Type :=
	| config__ (v_state : state) (v__ : (list admininstr)) : config .

Definition list__config  := (list (config )).

Definition option__config  := (option (config )).

Global Instance Inhabited__config  : Inhabited (config ) := { default_val := config__  default_val default_val }.

Definition config_eq_dec : forall  (v1 v2 : config ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition config_eqb  (v1 v2 : config ) : bool :=
config_eq_dec  v1 v2.
Definition eqconfigP  : Equality.axiom (config_eqb ) :=
eq_dec_Equality_axiom (config ) (config_eq_dec ).

Canonical Structure config_eqMixin  := EqMixin (eqconfigP ).
Canonical Structure config_eqType  :=
Eval hnf in EqType (config ) (config_eqMixin ).

(* Mutual Recursion at: spec/wasm-1.0-test/4-runtime.watsup:112.1-115.25 *)
(* Inductive Type Definition at: spec/wasm-1.0-test/4-runtime.watsup:112.1-115.25 *)
Inductive E  : Type :=
	| E___HOLE_  : E 
	| E___SEQ (v__ : (list val)) (v_E : E) (v__ : (list instr)) : E 
	| E__LABEL_ (v_n : n) (v__ : (list instr)) (v_E : E) : E .

Definition list__E  := (list (E )).

Definition option__E  := (option (E )).

Global Instance Inhabited__E  : Inhabited (E ) := { default_val := E___HOLE_   }.

Definition E_eq_dec : forall  (v1 v2 : E ),
{v1 = v2} + {v1 <> v2}.
Proof. Admitted.

Definition E_eqb  (v1 v2 : E ) : bool :=
E_eq_dec  v1 v2.
Definition eqEP  : Equality.axiom (E_eqb ) :=
eq_dec_Equality_axiom (E ) (E_eq_dec ).

Canonical Structure E_eqMixin  := EqMixin (eqEP ).
Canonical Structure E_eqType  :=
Eval hnf in EqType (E ) (E_eqMixin ).

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:7.1-7.29 *)
Definition fun_default_ (v_valtype_0 : valtype) : val :=
	match (v_valtype_0) with
		| ((valtype__INN (inn__I32 ))) => (val__CONST (valtype__INN (inn__I32 )) 0)
		| ((valtype__INN (inn__I64 ))) => (val__CONST (valtype__INN (inn__I64 )) 0)
		| ((valtype__FNN (fnn__F32 ))) => (val__CONST (valtype__FNN (fnn__F32 )) (fun_fzero 32))
		| ((valtype__FNN (fnn__F64 ))) => (val__CONST (valtype__FNN (fnn__F64 )) (fun_fzero 64))
	end.

(* Mutual Recursion at: spec/wasm-1.0-test/5-runtime-aux.watsup:17.1-17.62 *)
(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:17.1-17.62 *)
Fixpoint fun_funcsxv (v___0 : (list externval)) : (list funcaddr) :=
	match (v___0) with
		| ([]) => []
		| (((externval__FUNC v_fa) :: v_xv)) => (@app _ [v_fa] (fun_funcsxv v_xv))
		| ((v_externval :: v_xv)) => (fun_funcsxv v_xv)
	end.

(* Mutual Recursion at: spec/wasm-1.0-test/5-runtime-aux.watsup:18.1-18.64 *)
(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:18.1-18.64 *)
Fixpoint fun_globalsxv (v___0 : (list externval)) : (list globaladdr) :=
	match (v___0) with
		| ([]) => []
		| (((externval__GLOBAL v_ga) :: v_xv)) => (@app _ [v_ga] (fun_globalsxv v_xv))
		| ((v_externval :: v_xv)) => (fun_globalsxv v_xv)
	end.

(* Mutual Recursion at: spec/wasm-1.0-test/5-runtime-aux.watsup:19.1-19.63 *)
(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:19.1-19.63 *)
Fixpoint fun_tablesxv (v___0 : (list externval)) : (list tableaddr) :=
	match (v___0) with
		| ([]) => []
		| (((externval__TABLE v_ta) :: v_xv)) => (@app _ [v_ta] (fun_tablesxv v_xv))
		| ((v_externval :: v_xv)) => (fun_tablesxv v_xv)
	end.

(* Mutual Recursion at: spec/wasm-1.0-test/5-runtime-aux.watsup:20.1-20.61 *)
(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:20.1-20.61 *)
Fixpoint fun_memsxv (v___0 : (list externval)) : (list memaddr) :=
	match (v___0) with
		| ([]) => []
		| (((externval__MEM v_ma) :: v_xv)) => (@app _ [v_ma] (fun_memsxv v_xv))
		| ((v_externval :: v_xv)) => (fun_memsxv v_xv)
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:46.1-46.57 *)
Definition fun_store (v_state_0 : state) : store :=
	match (v_state_0) with
		| ((state__ v_s v_f)) => v_s
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:47.1-47.57 *)
Definition fun_frame (v_state_0 : state) : frame :=
	match (v_state_0) with
		| ((state__ v_s v_f)) => v_f
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:53.1-53.64 *)
Definition fun_funcaddr (v_state_0 : state) : (list funcaddr) :=
	match (v_state_0) with
		| ((state__ v_s v_f)) => (moduleinst__FUNCS (frame__MODULE v_f))
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:56.1-56.57 *)
Definition fun_funcinst (v_state_0 : state) : (list funcinst) :=
	match (v_state_0) with
		| ((state__ v_s v_f)) => (store__FUNCS v_s)
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:57.1-57.59 *)
Definition fun_globalinst (v_state_0 : state) : (list globalinst) :=
	match (v_state_0) with
		| ((state__ v_s v_f)) => (store__GLOBALS v_s)
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:58.1-58.58 *)
Definition fun_tableinst (v_state_0 : state) : (list tableinst) :=
	match (v_state_0) with
		| ((state__ v_s v_f)) => (store__TABLES v_s)
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:59.1-59.56 *)
Definition fun_meminst (v_state_0 : state) : (list meminst) :=
	match (v_state_0) with
		| ((state__ v_s v_f)) => (store__MEMS v_s)
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:60.1-60.58 *)
Definition fun_moduleinst (v_state_0 : state) : moduleinst :=
	match (v_state_0) with
		| ((state__ v_s v_f)) => (frame__MODULE v_f)
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:68.1-68.66 *)
Definition fun_type (v_state_0 : state) (v_typeidx_1 : typeidx) : functype :=
	match (v_state_0, v_typeidx_1) with
		| ((state__ v_s v_f), v_x) => (lookup_total (moduleinst__TYPES (frame__MODULE v_f)) v_x)
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:69.1-69.66 *)
Definition fun_func (v_state_0 : state) (v_funcidx_1 : funcidx) : funcinst :=
	match (v_state_0, v_funcidx_1) with
		| ((state__ v_s v_f), v_x) => (lookup_total (store__FUNCS v_s) (lookup_total (moduleinst__FUNCS (frame__MODULE v_f)) v_x))
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:70.1-70.68 *)
Definition fun_global (v_state_0 : state) (v_globalidx_1 : globalidx) : globalinst :=
	match (v_state_0, v_globalidx_1) with
		| ((state__ v_s v_f), v_x) => (lookup_total (store__GLOBALS v_s) (lookup_total (moduleinst__GLOBALS (frame__MODULE v_f)) v_x))
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:71.1-71.67 *)
Definition fun_table (v_state_0 : state) (v_tableidx_1 : tableidx) : tableinst :=
	match (v_state_0, v_tableidx_1) with
		| ((state__ v_s v_f), v_x) => (lookup_total (store__TABLES v_s) (lookup_total (moduleinst__TABLES (frame__MODULE v_f)) v_x))
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:72.1-72.65 *)
Definition fun_mem (v_state_0 : state) (v_memidx_1 : memidx) : meminst :=
	match (v_state_0, v_memidx_1) with
		| ((state__ v_s v_f), v_x) => (lookup_total (store__MEMS v_s) (lookup_total (moduleinst__MEMS (frame__MODULE v_f)) v_x))
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:73.1-73.67 *)
Definition fun_local (v_state_0 : state) (v_localidx_1 : localidx) : val :=
	match (v_state_0, v_localidx_1) with
		| ((state__ v_s v_f), v_x) => (lookup_total (frame__LOCALS v_f) v_x)
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:85.1-85.89 *)
Definition fun_with_local (v_state_0 : state) (v_localidx_1 : localidx) (v_val_2 : val) : state :=
	match (v_state_0, v_localidx_1, v_val_2) with
		| ((state__ v_s v_f), v_x, v_v) => (state__ v_s (v_f <|frame__LOCALS := (list_update (frame__LOCALS v_f) (v_x) (v_v))|>))
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:86.1-86.96 *)
Definition fun_with_global (v_state_0 : state) (v_globalidx_1 : globalidx) (v_val_2 : val) : state :=
	match (v_state_0, v_globalidx_1, v_val_2) with
		| ((state__ v_s v_f), v_x, v_v) => (state__ (v_s <|store__GLOBALS := (list_update_func (store__GLOBALS v_s) ((lookup_total (moduleinst__GLOBALS (frame__MODULE v_f)) v_x)) ((fun v_1 => v_1 <|globalinst__VALUE := v_v|>)))|>) v_f)
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:87.1-87.97 *)
Definition fun_with_table (v_state_0 : state) (v_tableidx_1 : tableidx) (v_reserved__nat_2 : nat) (v_funcaddr_3 : funcaddr) : state :=
	match (v_state_0, v_tableidx_1, v_reserved__nat_2, v_funcaddr_3) with
		| ((state__ v_s v_f), v_x, v_i, v_a) => (state__ (v_s <|store__TABLES := (list_update_func (store__TABLES v_s) ((lookup_total (moduleinst__TABLES (frame__MODULE v_f)) v_x)) ((fun v_1 => v_1 <|tableinst__REFS := (list_update (tableinst__REFS v_1) (v_i) ((Some v_a)))|>)))|>) v_f)
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:88.1-88.89 *)
Definition fun_with_tableinst (v_state_0 : state) (v_tableidx_1 : tableidx) (v_tableinst_2 : tableinst) : state :=
	match (v_state_0, v_tableidx_1, v_tableinst_2) with
		| ((state__ v_s v_f), v_x, v_ti) => (state__ (v_s <|store__TABLES := (list_update (store__TABLES v_s) ((lookup_total (moduleinst__TABLES (frame__MODULE v_f)) v_x)) (v_ti))|>) v_f)
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:89.1-89.100 *)
Definition fun_with_mem (v_state_0 : state) (v_memidx_1 : memidx) (v_reserved__nat_2 : nat) (v_reserved__nat_3 : nat) (v___4 : (list byte)) : state :=
	match (v_state_0, v_memidx_1, v_reserved__nat_2, v_reserved__nat_3, v___4) with
		| ((state__ v_s v_f), v_x, v_i, v_j, v_b) => (state__ (v_s <|store__MEMS := (list_update_func (store__MEMS v_s) ((lookup_total (moduleinst__MEMS (frame__MODULE v_f)) v_x)) ((fun v_1 => v_1 <|meminst__BYTES := (list_slice_update (meminst__BYTES v_1) (v_i) (v_j) (v_b))|>)))|>) v_f)
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:90.1-90.87 *)
Definition fun_with_meminst (v_state_0 : state) (v_memidx_1 : memidx) (v_meminst_2 : meminst) : state :=
	match (v_state_0, v_memidx_1, v_meminst_2) with
		| ((state__ v_s v_f), v_x, v_mi) => (state__ (v_s <|store__MEMS := (list_update (store__MEMS v_s) ((lookup_total (moduleinst__MEMS (frame__MODULE v_f)) v_x)) (v_mi))|>) v_f)
	end.

(* Axiom Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:102.1-102.43 *)
Axiom fun_growtable : forall (v_tableinst_0 : tableinst) (v_reserved__nat_1 : nat), tableinst.

(* Inductive Relations Definition at: spec/wasm-1.0-test/5-runtime-aux.watsup:104.1-104.47 *)
Inductive growmemory: meminst -> nat -> meminst -> Prop :=
	| growmemory__ : forall (v_meminst_1 : meminst) (v_n : n) (v_meminst_2 : meminst) (v_i : nat) (v_j : nat) (v_b : (list byte)) (v_i' : nat), (v_meminst_1 = {| meminst__TYPE := (limits__ v_i v_j); meminst__BYTES := v_b |}) -> (v_i' = (v_i + v_n)) -> (v_meminst_2 = {| meminst__TYPE := (limits__ v_i' v_j); meminst__BYTES := (@app _ v_b [(byte__ 0)]) |}) -> (v_i' <= v_j) -> growmemory v_meminst_1 v_n v_meminst_2.

(* Record Creation Definition at: spec/wasm-1.0-test/6-typing.watsup:5.1-8.62 *)
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

Definition option__context  := (option (context )).

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

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:18.1-18.66 *)
Inductive Limits_ok: limits -> nat -> Prop :=
	| Limits_ok__ : forall (v_n : n) (v_m : m) (v_k : nat), ((v_n <= v_m) /\ (v_m <= v_k)) -> Limits_ok (limits__ v_n v_m) v_k.

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:19.1-19.64 *)
Inductive Functype_ok: functype -> Prop :=
	| Functype_ok__OK : forall (v_t_1 : (list valtype)) (v_t_2 : (option valtype)), Functype_ok (functype__ v_t_1 v_t_2).

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:20.1-20.66 *)
Inductive Globaltype_ok: globaltype -> Prop :=
	| Globaltype_ok__OK : forall (v_t : valtype) (v_w0 : (option unit)), Globaltype_ok (globaltype__ (mut__MUT v_w0) v_t).

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:21.1-21.65 *)
Inductive Tabletype_ok: tabletype -> Prop :=
	| Tabletype_ok__OK : forall (v_limits : limits), (Limits_ok v_limits ((2 ^ 32) - 1)) -> Tabletype_ok v_limits.

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:22.1-22.63 *)
Inductive Memtype_ok: memtype -> Prop :=
	| Memtype_ok__OK : forall (v_limits : limits), (Limits_ok v_limits (2 ^ 16)) -> Memtype_ok v_limits.

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:23.1-23.66 *)
Inductive Externtype_ok: externtype -> Prop :=
	| Externtype_ok__funcOK : forall (v_functype : functype), (Functype_ok v_functype) -> Externtype_ok (externtype__FUNC v_functype)
	| Externtype_ok__globalOK : forall (v_globaltype : globaltype), (Globaltype_ok v_globaltype) -> Externtype_ok (externtype__GLOBAL v_globaltype)
	| Externtype_ok__tableOK : forall (v_tabletype : tabletype), (Tabletype_ok v_tabletype) -> Externtype_ok (externtype__TABLE v_tabletype)
	| Externtype_ok__memOK : forall (v_memtype : memtype), (Memtype_ok v_memtype) -> Externtype_ok (externtype__MEM v_memtype).

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:69.1-69.75 *)
Inductive Limits_sub: limits -> limits -> Prop :=
	| Limits_sub__ : forall (v_n_11 : n) (v_n_12 : n) (v_n_21 : n) (v_n_22 : n), (v_n_11 >= v_n_21) -> (v_n_12 <= v_n_22) -> Limits_sub (limits__ v_n_11 v_n_12) (limits__ v_n_21 v_n_22).

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:70.1-70.73 *)
Inductive Functype_sub: functype -> functype -> Prop :=
	| Functype_sub__ : forall (v_ft : functype), Functype_sub v_ft v_ft.

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:71.1-71.75 *)
Inductive Globaltype_sub: globaltype -> globaltype -> Prop :=
	| Globaltype_sub__ : forall (v_gt : globaltype), Globaltype_sub v_gt v_gt.

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:72.1-72.74 *)
Inductive Tabletype_sub: tabletype -> tabletype -> Prop :=
	| Tabletype_sub__ : forall (v_lim_1 : limits) (v_lim_2 : limits), (Limits_sub v_lim_1 v_lim_2) -> Tabletype_sub v_lim_1 v_lim_2.

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:73.1-73.72 *)
Inductive Memtype_sub: memtype -> memtype -> Prop :=
	| Memtype_sub__ : forall (v_lim_1 : limits) (v_lim_2 : limits), (Limits_sub v_lim_1 v_lim_2) -> Memtype_sub v_lim_1 v_lim_2.

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:74.1-74.75 *)
Inductive Externtype_sub: externtype -> externtype -> Prop :=
	| Externtype_sub__func : forall (v_ft_1 : functype) (v_ft_2 : functype), (Functype_sub v_ft_1 v_ft_2) -> Externtype_sub (externtype__FUNC v_ft_1) (externtype__FUNC v_ft_2)
	| Externtype_sub__global : forall (v_gt_1 : globaltype) (v_gt_2 : globaltype), (Globaltype_sub v_gt_1 v_gt_2) -> Externtype_sub (externtype__GLOBAL v_gt_1) (externtype__GLOBAL v_gt_2)
	| Externtype_sub__table : forall (v_tt_1 : tabletype) (v_tt_2 : tabletype), (Tabletype_sub v_tt_1 v_tt_2) -> Externtype_sub (externtype__TABLE v_tt_1) (externtype__TABLE v_tt_2)
	| Externtype_sub__mem : forall (v_mt_1 : memtype) (v_mt_2 : memtype), (Memtype_sub v_mt_1 v_mt_2) -> Externtype_sub (externtype__MEM v_mt_1) (externtype__MEM v_mt_2).

(* Mutual Recursion at: spec/wasm-1.0-test/6-typing.watsup:119.1-120.65 *)
(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:119.1-119.64 *)
Inductive Instr_ok: context -> instr -> functype -> Prop :=
	| Instr_ok__nop : forall (v_C : context), Instr_ok v_C (instr__NOP ) (functype__ [] [])
	| Instr_ok__unreachable : forall (v_C : context) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), Instr_ok v_C (instr__UNREACHABLE ) (functype__ v_t_1 v_t_2)
	| Instr_ok__drop : forall (v_C : context) (v_t : valtype), Instr_ok v_C (instr__DROP ) (functype__ [v_t] [])
	| Instr_ok__select : forall (v_C : context) (v_t : valtype), Instr_ok v_C (instr__SELECT ) (functype__ [v_t;v_t;(valtype__INN (inn__I32 ))] [v_t])
	| Instr_ok__block : forall (v_C : context) (v_t : (option valtype)) (v_instr : (list instr)), (Instrs_ok ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := [v_t]; context__RETURN := None |} ++ v_C) v_instr (functype__ [] v_t)) -> Instr_ok v_C (instr__BLOCK v_t v_instr) (functype__ [] v_t)
	| Instr_ok__loop : forall (v_C : context) (v_t : (option valtype)) (v_instr : (list instr)), (Instrs_ok ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := [None]; context__RETURN := None |} ++ v_C) v_instr (functype__ [] v_t)) -> Instr_ok v_C (instr__LOOP v_t v_instr) (functype__ [] v_t)
	| Instr_ok__if : forall (v_C : context) (v_t : (option valtype)) (v_instr_1 : (list instr)) (v_instr_2 : (list instr)), (Instrs_ok ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := [v_t]; context__RETURN := None |} ++ v_C) v_instr_1 (functype__ [] v_t)) -> (Instrs_ok ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := [v_t]; context__RETURN := None |} ++ v_C) v_instr_2 (functype__ [] v_t)) -> Instr_ok v_C (instr__IFELSE v_t v_instr_1 v_instr_2) (functype__ [(valtype__INN (inn__I32 ))] v_t)
	| Instr_ok__br : forall (v_C : context) (v_l : labelidx) (v_t_1 : (list valtype)) (v_t : (option valtype)) (v_t_2 : (list valtype)), (v_l < (List.length (context__LABELS v_C))) -> ((lookup_total (context__LABELS v_C) v_l) = v_t) -> Instr_ok v_C (instr__BR v_l) (functype__ (@app _ v_t_1 v_t) v_t_2)
	| Instr_ok__br_if : forall (v_C : context) (v_l : labelidx) (v_t : (option valtype)), (v_l < (List.length (context__LABELS v_C))) -> ((lookup_total (context__LABELS v_C) v_l) = v_t) -> Instr_ok v_C (instr__BR_IF v_l) (functype__ (@app _ v_t [(valtype__INN (inn__I32 ))]) v_t)
	| Instr_ok__br_table : forall (v_C : context) (v_l : (list labelidx)) (v_l' : labelidx) (v_t_1 : (list valtype)) (v_t : (option valtype)) (v_t_2 : (list valtype)), (v_l' < (List.length (context__LABELS v_C))) -> List.Forall (fun v_l => (v_l < (List.length (context__LABELS v_C)))) (v_l) -> (v_t = (lookup_total (context__LABELS v_C) v_l')) -> List.Forall (fun v_l => (v_t = (lookup_total (context__LABELS v_C) v_l))) (v_l) -> Instr_ok v_C (instr__BR_TABLE v_l v_l') (functype__ (@app _ v_t_1 (@app _ v_t [(valtype__INN (inn__I32 ))])) v_t_2)
	| Instr_ok__call : forall (v_C : context) (v_x : idx) (v_t_1 : (list valtype)) (v_t_2 : (option valtype)), (v_x < (List.length (context__FUNCS v_C))) -> ((lookup_total (context__FUNCS v_C) v_x) = (functype__ v_t_1 v_t_2)) -> Instr_ok v_C (instr__CALL v_x) (functype__ v_t_1 v_t_2)
	| Instr_ok__call_indirect : forall (v_C : context) (v_x : idx) (v_t_1 : (list valtype)) (v_t_2 : (option valtype)), (v_x < (List.length (context__TYPES v_C))) -> ((lookup_total (context__TYPES v_C) v_x) = (functype__ v_t_1 v_t_2)) -> Instr_ok v_C (instr__CALL_INDIRECT v_x) (functype__ (@app _ v_t_1 [(valtype__INN (inn__I32 ))]) v_t_2)
	| Instr_ok__return : forall (v_C : context) (v_t_1 : (list valtype)) (v_t : (option valtype)) (v_t_2 : (list valtype)), ((context__RETURN v_C) = (Some v_t)) -> Instr_ok v_C (instr__RETURN ) (functype__ (@app _ v_t_1 v_t) v_t_2)
	| Instr_ok__const : forall (v_C : context) (v_t : valtype) (v_c_t : val_), Instr_ok v_C (instr__CONST v_t (v_c_t : val_)) (functype__ [] [v_t])
	| Instr_ok__unop : forall (v_C : context) (v_t : valtype) (v_unop_t : unop_), Instr_ok v_C (instr__UNOP v_t (v_unop_t : unop_)) (functype__ [v_t] [v_t])
	| Instr_ok__binop : forall (v_C : context) (v_t : valtype) (v_binop_t : binop_), Instr_ok v_C (instr__BINOP v_t (v_binop_t : binop_)) (functype__ [v_t;v_t] [v_t])
	| Instr_ok__testop : forall (v_C : context) (v_t : valtype) (v_testop_t : testop_), Instr_ok v_C (instr__TESTOP v_t (v_testop_t : testop_)) (functype__ [v_t] [(valtype__INN (inn__I32 ))])
	| Instr_ok__relop : forall (v_C : context) (v_t : valtype) (v_relop_t : relop_), Instr_ok v_C (instr__RELOP v_t (v_relop_t : relop_)) (functype__ [v_t;v_t] [(valtype__INN (inn__I32 ))])
	| Instr_ok__cvtop_reinterpret : forall (v_C : context) (v_t_1 : valtype) (v_t_2 : valtype), ((fun_size v_t_1) = (fun_size v_t_2)) -> Instr_ok v_C (instr__CVTOP v_t_1 (cvtop__REINTERPRET ) v_t_2 None) (functype__ [v_t_2] [v_t_1])
	| Instr_ok__cvtop_convert_i : forall (v_C : context) (v_inn_1 : inn) (v_inn_2 : inn) (v_sx : (option sx)), ((v_sx = None) <-> ((fun_size (valtype__INN v_inn_1)) > (fun_size (valtype__INN v_inn_2)))) -> Instr_ok v_C (instr__CVTOP (valtype__INN v_inn_1) (cvtop__CONVERT ) (valtype__INN v_inn_2) v_sx) (functype__ [(valtype__INN v_inn_2)] [(valtype__INN v_inn_1)])
	| Instr_ok__cvtop_convert_f : forall (v_C : context) (v_fnn_1 : fnn) (v_fnn_2 : fnn), Instr_ok v_C (instr__CVTOP (valtype__FNN v_fnn_1) (cvtop__CONVERT ) (valtype__FNN v_fnn_2) None) (functype__ [(valtype__FNN v_fnn_2)] [(valtype__FNN v_fnn_1)])
	| Instr_ok__local_get : forall (v_C : context) (v_x : idx) (v_t : valtype), (v_x < (List.length (context__LOCALS v_C))) -> ((lookup_total (context__LOCALS v_C) v_x) = v_t) -> Instr_ok v_C (instr__LOCAL_GET v_x) (functype__ [] [v_t])
	| Instr_ok__local_set : forall (v_C : context) (v_x : idx) (v_t : valtype), (v_x < (List.length (context__LOCALS v_C))) -> ((lookup_total (context__LOCALS v_C) v_x) = v_t) -> Instr_ok v_C (instr__LOCAL_SET v_x) (functype__ [v_t] [])
	| Instr_ok__local_tee : forall (v_C : context) (v_x : idx) (v_t : valtype), (v_x < (List.length (context__LOCALS v_C))) -> ((lookup_total (context__LOCALS v_C) v_x) = v_t) -> Instr_ok v_C (instr__LOCAL_TEE v_x) (functype__ [v_t] [v_t])
	| Instr_ok__global_get : forall (v_C : context) (v_x : idx) (v_t : valtype) (v_mut : mut), (v_x < (List.length (context__GLOBALS v_C))) -> ((lookup_total (context__GLOBALS v_C) v_x) = (globaltype__ v_mut v_t)) -> Instr_ok v_C (instr__GLOBAL_GET v_x) (functype__ [] [v_t])
	| Instr_ok__global_set : forall (v_C : context) (v_x : idx) (v_t : valtype), (v_x < (List.length (context__GLOBALS v_C))) -> ((lookup_total (context__GLOBALS v_C) v_x) = (globaltype__ (mut__MUT (Some tt)) v_t)) -> Instr_ok v_C (instr__GLOBAL_SET v_x) (functype__ [v_t] [])
	| Instr_ok__memory_size : forall (v_C : context) (v_mt : memtype), (0 < (List.length (context__MEMS v_C))) -> ((lookup_total (context__MEMS v_C) 0) = v_mt) -> Instr_ok v_C (instr__MEMORY_SIZE ) (functype__ [] [(valtype__INN (inn__I32 ))])
	| Instr_ok__memory_grow : forall (v_C : context) (v_mt : memtype), (0 < (List.length (context__MEMS v_C))) -> ((lookup_total (context__MEMS v_C) 0) = v_mt) -> Instr_ok v_C (instr__MEMORY_GROW ) (functype__ [(valtype__INN (inn__I32 ))] [(valtype__INN (inn__I32 ))])
	| Instr_ok__load : forall (v_C : context) (v_nt : valtype) (v_n : (option n)) (v_sx : (option sx)) (v_memop : memop) (v_mt : memtype) (v_inn : inn), (0 < (List.length (context__MEMS v_C))) -> ((v_n = None) <-> (v_sx = None)) -> ((lookup_total (context__MEMS v_C) 0) = v_mt) -> ((2 ^ (memop__ALIGN v_memop)) <= ((fun_size v_nt) / 8)) -> List.Forall (fun v_n => (((2 ^ (memop__ALIGN v_memop)) <= (v_n / 8)) /\ ((v_n / 8) < ((fun_size v_nt) / 8)))) (option_to_list v_n) -> ((v_n = None) \/ (v_nt = (valtype__INN v_inn))) -> Instr_ok v_C (instr__LOAD_ v_nt (option_zipWith (fun v_n v_sx => ((packsize__ v_n), v_sx)) v_n v_sx) v_memop) (functype__ [(valtype__INN (inn__I32 ))] [v_nt])
	| Instr_ok__store : forall (v_C : context) (v_nt : valtype) (v_n : (option n)) (v_memop : memop) (v_mt : memtype) (v_inn : inn), (0 < (List.length (context__MEMS v_C))) -> ((lookup_total (context__MEMS v_C) 0) = v_mt) -> ((2 ^ (memop__ALIGN v_memop)) <= ((fun_size v_nt) / 8)) -> List.Forall (fun v_n => (((2 ^ (memop__ALIGN v_memop)) <= (v_n / 8)) /\ ((v_n / 8) < ((fun_size v_nt) / 8)))) (option_to_list v_n) -> ((v_n = None) \/ (v_nt = (valtype__INN v_inn))) -> Instr_ok v_C (instr__STORE v_nt (option_map (fun v_n => (packsize__ v_n)) (v_n)) v_memop) (functype__ [(valtype__INN (inn__I32 ));v_nt] [])

with

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:120.1-120.65 *)
Instrs_ok: context -> (list instr) -> functype -> Prop :=
	| Instrs_ok__empty : forall (v_C : context), Instrs_ok v_C [] (functype__ [] [])
	| Instrs_ok__seq : forall (v_C : context) (v_instr_1 : (list instr)) (v_instr_2 : instr) (v_t_1 : (list valtype)) (v_t_3 : (list valtype)) (v_t_2 : (list valtype)), (Instrs_ok v_C v_instr_1 (functype__ v_t_1 v_t_2)) -> (Instr_ok v_C v_instr_2 (functype__ v_t_2 v_t_3)) -> Instrs_ok v_C (@app _ v_instr_1 [v_instr_2]) (functype__ v_t_1 v_t_3)
	| Instrs_ok__frame : forall (v_C : context) (v_instr : (list instr)) (v_t : (list valtype)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), (Instrs_ok v_C v_instr (functype__ v_t_1 v_t_2)) -> Instrs_ok v_C v_instr (functype__ (@app _ v_t v_t_1) (@app _ v_t v_t_2)).

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:121.1-121.69 *)
Inductive Expr_ok: context -> expr -> resulttype -> Prop :=
	| Expr_ok__ : forall (v_C : context) (v_instr : (list instr)) (v_t : (option valtype)), (Instrs_ok v_C v_instr (functype__ [] v_t)) -> Expr_ok v_C v_instr v_t.

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:293.1-293.79 *)
Inductive Instr_const: context -> instr -> Prop :=
	| Instr_const__constCONST : forall (v_C : context) (v_t : valtype) (v_c : val_), Instr_const v_C (instr__CONST v_t (v_c : val_))
	| Instr_const__global_getCONST : forall (v_C : context) (v_x : idx) (v_t : valtype), (v_x < (List.length (context__GLOBALS v_C))) -> ((lookup_total (context__GLOBALS v_C) v_x) = (globaltype__ (mut__MUT None) v_t)) -> Instr_const v_C (instr__GLOBAL_GET v_x).

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:294.1-294.78 *)
Inductive Expr_const: context -> expr -> Prop :=
	| Expr_const__CONST : forall (v_C : context) (v_instr : (list instr)), List.Forall (fun v_instr => (Instr_const v_C v_instr)) (v_instr) -> Expr_const v_C v_instr.

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:295.1-295.79 *)
Inductive Expr_ok_const: context -> expr -> (option valtype) -> Prop :=
	| Expr_ok_const__CONST : forall (v_C : context) (v_expr : expr) (v_t : (option valtype)), (Expr_ok v_C v_expr v_t) -> (Expr_const v_C v_expr) -> Expr_ok_const v_C v_expr v_t.

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:319.1-319.73 *)
Inductive Type_ok: type -> functype -> Prop :=
	| Type_ok__ : forall (v_ft : functype), (Functype_ok v_ft) -> Type_ok (type__TYPE v_ft) v_ft.

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:320.1-320.73 *)
Inductive Func_ok: context -> func -> functype -> Prop :=
	| Func_ok__ : forall (v_C : context) (v_x : idx) (v_t : (list valtype)) (v_expr : expr) (v_t_1 : (list valtype)) (v_t_2 : (option valtype)), (v_x < (List.length (context__TYPES v_C))) -> ((lookup_total (context__TYPES v_C) v_x) = (functype__ v_t_1 v_t_2)) -> (Expr_ok ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := []; context__RETURN := (Some v_t_2) |} ++ ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := [v_t_2]; context__RETURN := None |} ++ ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := (@app _ v_t_1 v_t); context__LABELS := []; context__RETURN := None |} ++ v_C))) v_expr v_t_2) -> Func_ok v_C (func__FUNC v_x (List.map (fun v_t => (local__LOCAL v_t)) (v_t)) v_expr) (functype__ v_t_1 v_t_2).

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:321.1-321.75 *)
Inductive Global_ok: context -> global -> globaltype -> Prop :=
	| Global_ok__ : forall (v_C : context) (v_gt : globaltype) (v_expr : expr) (v_mut : mut) (v_t : valtype), (Globaltype_ok v_gt) -> (v_gt = (globaltype__ v_mut v_t)) -> (Expr_ok_const v_C v_expr (Some v_t)) -> Global_ok v_C (global__GLOBAL v_gt v_expr) v_gt.

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:322.1-322.74 *)
Inductive Table_ok: context -> table -> tabletype -> Prop :=
	| Table_ok__ : forall (v_C : context) (v_reserved__tt : tabletype), (Tabletype_ok v_reserved__tt) -> Table_ok v_C (table__TABLE v_reserved__tt) v_reserved__tt.

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:323.1-323.72 *)
Inductive Mem_ok: context -> mem -> memtype -> Prop :=
	| Mem_ok__ : forall (v_C : context) (v_mt : memtype), (Memtype_ok v_mt) -> Mem_ok v_C (mem__MEMORY v_mt) v_mt.

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:324.1-324.73 *)
Inductive Elem_ok: context -> elem -> Prop :=
	| Elem_ok__OK : forall (v_C : context) (v_expr : expr) (v_x : (list idx)) (v_lim : limits) (v_ft : (list functype)), (0 < (List.length (context__TABLES v_C))) -> ((List.length v_ft) = (List.length v_x)) -> List.Forall2 (fun v_ft v_x => (v_x < (List.length (context__FUNCS v_C)))) (v_ft) (v_x) -> ((lookup_total (context__TABLES v_C) 0) = v_lim) -> (Expr_ok_const v_C v_expr (Some (valtype__INN (inn__I32 )))) -> List.Forall2 (fun v_ft v_x => ((lookup_total (context__FUNCS v_C) v_x) = v_ft)) (v_ft) (v_x) -> Elem_ok v_C (elem__ELEM v_expr v_x).

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:325.1-325.73 *)
Inductive Data_ok: context -> data -> Prop :=
	| Data_ok__OK : forall (v_C : context) (v_expr : expr) (v_b : (list byte)) (v_lim : limits), (0 < (List.length (context__MEMS v_C))) -> ((lookup_total (context__MEMS v_C) 0) = v_lim) -> (Expr_ok_const v_C v_expr (Some (valtype__INN (inn__I32 )))) -> Data_ok v_C (data__DATA v_expr v_b).

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:326.1-326.74 *)
Inductive Start_ok: context -> start -> Prop :=
	| Start_ok__OK : forall (v_C : context) (v_x : idx), (v_x < (List.length (context__FUNCS v_C))) -> ((lookup_total (context__FUNCS v_C) v_x) = (functype__ [] [])) -> Start_ok v_C (start__START v_x).

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:374.1-374.80 *)
Inductive Import_ok: context -> import -> externtype -> Prop :=
	| Import_ok__ : forall (v_C : context) (v_name_1 : name) (v_name_2 : name) (v_xt : externtype), (Externtype_ok v_xt) -> Import_ok v_C (import__IMPORT v_name_1 v_name_2 v_xt) v_xt.

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:376.1-376.83 *)
Inductive Externidx_ok: context -> externidx -> externtype -> Prop :=
	| Externidx_ok__func : forall (v_C : context) (v_x : idx) (v_ft : functype), (v_x < (List.length (context__FUNCS v_C))) -> ((lookup_total (context__FUNCS v_C) v_x) = v_ft) -> Externidx_ok v_C (externidx__FUNC v_x) (externtype__FUNC v_ft)
	| Externidx_ok__global : forall (v_C : context) (v_x : idx) (v_gt : globaltype), (v_x < (List.length (context__GLOBALS v_C))) -> ((lookup_total (context__GLOBALS v_C) v_x) = v_gt) -> Externidx_ok v_C (externidx__GLOBAL v_x) (externtype__GLOBAL v_gt)
	| Externidx_ok__table : forall (v_C : context) (v_x : idx) (v_reserved__tt : tabletype), (v_x < (List.length (context__TABLES v_C))) -> ((lookup_total (context__TABLES v_C) v_x) = v_reserved__tt) -> Externidx_ok v_C (externidx__TABLE v_x) (externtype__TABLE v_reserved__tt)
	| Externidx_ok__mem : forall (v_C : context) (v_x : idx) (v_mt : memtype), (v_x < (List.length (context__MEMS v_C))) -> ((lookup_total (context__MEMS v_C) v_x) = v_mt) -> Externidx_ok v_C (externidx__MEM v_x) (externtype__MEM v_mt).

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:375.1-375.80 *)
Inductive Export_ok: context -> export -> externtype -> Prop :=
	| Export_ok__ : forall (v_C : context) (v_name : name) (v_externidx : externidx) (v_xt : externtype), (Externidx_ok v_C v_externidx v_xt) -> Export_ok v_C (export__EXPORT v_name v_externidx) v_xt.

(* Inductive Relations Definition at: spec/wasm-1.0-test/6-typing.watsup:406.1-406.62 *)
Inductive Module_ok: module -> Prop :=
	| Module_ok__OK : forall (v_type : (list type)) (v_import : (list import)) (v_func : (list func)) (v_global : (list global)) (v_table : (list table)) (v_mem : (list mem)) (v_elem : (list elem)) (v_data : (list data)) (v_start : (option start)) (v_export : (list export)) (v_ft' : (list functype)) (v_ixt : (list externtype)) (v_C' : context) (v_gt : (list globaltype)) (v_C : context) (v_ft : (list functype)) (v_reserved__tt : (list tabletype)) (v_mt : (list memtype)) (v_xt : (list externtype)) (v_ift : (list functype)) (v_igt : (list globaltype)) (v_itt : (list tabletype)) (v_imt : (list memtype)), ((List.length v_ft') = (List.length v_type)) -> ((List.length v_import) = (List.length v_ixt)) -> ((List.length v_global) = (List.length v_gt)) -> ((List.length v_ft) = (List.length v_func)) -> ((List.length v_table) = (List.length v_reserved__tt)) -> ((List.length v_mem) = (List.length v_mt)) -> ((List.length v_export) = (List.length v_xt)) -> List.Forall2 (fun v_ft' v_type => (Type_ok v_type v_ft')) (v_ft') (v_type) -> List.Forall2 (fun v_import v_ixt => (Import_ok {| context__TYPES := v_ft'; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := []; context__RETURN := None |} v_import v_ixt)) (v_import) (v_ixt) -> List.Forall2 (fun v_global v_gt => (Global_ok v_C' v_global v_gt)) (v_global) (v_gt) -> List.Forall2 (fun v_ft v_func => (Func_ok v_C v_func v_ft)) (v_ft) (v_func) -> List.Forall2 (fun v_table v_reserved__tt => (Table_ok v_C v_table v_reserved__tt)) (v_table) (v_reserved__tt) -> List.Forall2 (fun v_mem v_mt => (Mem_ok v_C v_mem v_mt)) (v_mem) (v_mt) -> List.Forall (fun v_elem => (Elem_ok v_C v_elem)) (v_elem) -> List.Forall (fun v_data => (Data_ok v_C v_data)) (v_data) -> List.Forall (fun v_start => (Start_ok v_C v_start)) (option_to_list v_start) -> List.Forall2 (fun v_export v_xt => (Export_ok v_C v_export v_xt)) (v_export) (v_xt) -> ((List.length v_reserved__tt) <= 1) -> ((List.length v_mt) <= 1) -> (v_C = {| context__TYPES := v_ft'; context__FUNCS := (@app _ v_ift v_ft); context__GLOBALS := (@app _ v_igt v_gt); context__TABLES := (@app _ v_itt v_reserved__tt); context__MEMS := (@app _ v_imt v_mt); context__LOCALS := []; context__LABELS := []; context__RETURN := None |}) -> (v_C' = {| context__TYPES := v_ft'; context__FUNCS := (@app _ v_ift v_ft); context__GLOBALS := v_igt; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := []; context__RETURN := None |}) -> (v_ift = (fun_funcsxt v_ixt)) -> (v_igt = (fun_globalsxt v_ixt)) -> (v_itt = (fun_tablesxt v_ixt)) -> (v_imt = (fun_memsxt v_ixt)) -> Module_ok (module__MODULE v_type v_import v_func v_global v_table v_mem v_elem v_data v_start v_export).

(* Auxiliary Definition at: spec/wasm-1.0-test/8-reduction.watsup:6.1-6.63 *)
Definition fun_coec_val__admininstr (v_val : val) : admininstr :=
	match (v_val) with
		| (val__CONST v_0 v_1) => (admininstr__CONST v_0 v_1)
	end.

(* Type Coercion Definition at: spec/wasm-1.0-test/8-reduction.watsup:6.1-6.63 *)
Coercion fun_coec_val__admininstr : val >-> admininstr.

Definition list__val__admininstr : list__val -> list__admininstr := map fun_coec_val__admininstr.

Coercion list__val__admininstr : list__val >-> list__admininstr.

Definition option__val__admininstr : option__val -> option__admininstr := option_map fun_coec_val__admininstr.

Coercion option__val__admininstr : option__val >-> option__admininstr.

(* Auxiliary Definition at: spec/wasm-1.0-test/8-reduction.watsup:6.1-6.63 *)
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

(* Type Coercion Definition at: spec/wasm-1.0-test/8-reduction.watsup:6.1-6.63 *)
Coercion fun_coec_instr__admininstr : instr >-> admininstr.

Definition list__instr__admininstr : list__instr -> list__admininstr := map fun_coec_instr__admininstr.

Coercion list__instr__admininstr : list__instr >-> list__admininstr.

Definition option__instr__admininstr : option__instr -> option__admininstr := option_map fun_coec_instr__admininstr.

Coercion option__instr__admininstr : option__instr >-> option__admininstr.

(* Inductive Relations Definition at: spec/wasm-1.0-test/8-reduction.watsup:6.1-6.63 *)
Inductive Step_pure: (list admininstr) -> (list admininstr) -> Prop :=
	| Step_pure__unreachable : Step_pure [(admininstr__UNREACHABLE )] [(admininstr__TRAP )]
	| Step_pure__nop : Step_pure [(admininstr__NOP )] []
	| Step_pure__drop : forall (v_val : val), Step_pure [(v_val : admininstr);(admininstr__DROP )] []
	| Step_pure__select_true : forall (v_val_1 : val) (v_val_2 : val) (v_c : iN), ((v_c : val_) <> 0) -> Step_pure [(v_val_1 : admininstr);(v_val_2 : admininstr);(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__SELECT )] [(v_val_1 : admininstr)]
	| Step_pure__select_false : forall (v_val_1 : val) (v_val_2 : val) (v_c : iN), ((v_c : val_) = 0) -> Step_pure [(v_val_1 : admininstr);(v_val_2 : admininstr);(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__SELECT )] [(v_val_2 : admininstr)]
	| Step_pure__if_true : forall (v_c : iN) (v_t : (option valtype)) (v_instr_1 : (list instr)) (v_instr_2 : (list instr)), ((v_c : val_) <> 0) -> Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__IFELSE v_t v_instr_1 v_instr_2)] [(admininstr__BLOCK v_t v_instr_1)]
	| Step_pure__if_false : forall (v_c : iN) (v_t : (option valtype)) (v_instr_1 : (list instr)) (v_instr_2 : (list instr)), ((v_c : val_) = 0) -> Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__IFELSE v_t v_instr_1 v_instr_2)] [(admininstr__BLOCK v_t v_instr_2)]
	| Step_pure__label_vals : forall (v_n : n) (v_instr : (list instr)) (v_val : (list val)), Step_pure [(admininstr__LABEL_ v_n v_instr (list__val__admininstr v_val))] (list__val__admininstr v_val)
	| Step_pure__br_zero : forall (v_n : n) (v_instr : (list instr)) (v_val' : (list val)) (v_val : (list val)) (v_admininstr : (list admininstr)), ((List.length v_val) = v_n) -> Step_pure [(admininstr__LABEL_ v_n v_instr (@app _ (list__val__admininstr v_val') (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__BR 0)] v_admininstr))))] (@app _ (list__val__admininstr v_val) (list__instr__admininstr v_instr))
	| Step_pure__br_succ : forall (v_n : n) (v_instr : (list instr)) (v_val : (list val)) (v_l : labelidx) (v_admininstr : (list admininstr)), Step_pure [(admininstr__LABEL_ v_n v_instr (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__BR (v_l + 1))] v_admininstr)))] (@app _ (list__val__admininstr v_val) [(admininstr__BR v_l)])
	| Step_pure__br_if_true : forall (v_c : iN) (v_l : labelidx), ((v_c : val_) <> 0) -> Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__BR_IF v_l)] [(admininstr__BR v_l)]
	| Step_pure__br_if_false : forall (v_c : iN) (v_l : labelidx), ((v_c : val_) = 0) -> Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_));(admininstr__BR_IF v_l)] []
	| Step_pure__br_table_lt : forall (v_i : nat) (v_l : (list labelidx)) (v_l' : labelidx), (v_i < (List.length v_l)) -> Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__BR_TABLE v_l v_l')] [(admininstr__BR (lookup_total v_l v_i))]
	| Step_pure__br_table_ge : forall (v_i : nat) (v_l : (list labelidx)) (v_l' : labelidx), (v_i >= (List.length v_l)) -> Step_pure [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__BR_TABLE v_l v_l')] [(admininstr__BR v_l')]
	| Step_pure__frame_vals : forall (v_n : n) (v_f : frame) (v_val : (list val)), Step_pure [(admininstr__FRAME_ v_n v_f (list__val__admininstr v_val))] (list__val__admininstr v_val)
	| Step_pure__return_frame : forall (v_n : n) (v_f : frame) (v_val' : (list val)) (v_val : (list val)) (v_admininstr : (list admininstr)), ((List.length v_val) = v_n) -> Step_pure [(admininstr__FRAME_ v_n v_f (@app _ (list__val__admininstr v_val') (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__RETURN )] v_admininstr))))] (list__val__admininstr v_val)
	| Step_pure__return_label : forall (v_n : n) (v_instr : (list instr)) (v_val : (list val)) (v_admininstr : (list admininstr)), Step_pure [(admininstr__LABEL_ v_n v_instr (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__RETURN )] v_admininstr)))] (@app _ (list__val__admininstr v_val) [(admininstr__RETURN )])
	| Step_pure__trap_vals : forall (v_val : (list val)) (v_admininstr : (list admininstr)), ((v_val <> []) \/ (v_admininstr <> [])) -> Step_pure (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__TRAP )] v_admininstr)) [(admininstr__TRAP )]
	| Step_pure__trap_label : forall (v_n : n) (v_instr : (list instr)), Step_pure [(admininstr__LABEL_ v_n v_instr [(admininstr__TRAP )])] [(admininstr__TRAP )]
	| Step_pure__trap_frame : forall (v_n : n) (v_f : frame), Step_pure [(admininstr__FRAME_ v_n v_f [(admininstr__TRAP )])] [(admininstr__TRAP )]
	| Step_pure__unop_val : forall (v_t : valtype) (v_c_1 : val_) (v_unop : unop_) (v_c : val_), ((fun_unop v_t (v_unop : unop_) (v_c_1 : val_)) = (Some (v_c : val_))) -> Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__UNOP v_t (v_unop : unop_))] [(admininstr__CONST v_t (v_c : val_))]
	| Step_pure__unop_trap : forall (v_t : valtype) (v_c_1 : val_) (v_unop : unop_), ((fun_unop v_t (v_unop : unop_) (v_c_1 : val_)) = None) -> Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__UNOP v_t (v_unop : unop_))] [(admininstr__TRAP )]
	| Step_pure__binop_val : forall (v_t : valtype) (v_c_1 : val_) (v_c_2 : val_) (v_binop : binop_) (v_c : val_), ((fun_binop v_t (v_binop : binop_) (v_c_1 : val_) (v_c_2 : val_)) = (Some (v_c : val_))) -> Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__CONST v_t (v_c_2 : val_));(admininstr__BINOP v_t (v_binop : binop_))] [(admininstr__CONST v_t (v_c : val_))]
	| Step_pure__binop_trap : forall (v_t : valtype) (v_c_1 : val_) (v_c_2 : val_) (v_binop : binop_), ((fun_binop v_t (v_binop : binop_) (v_c_1 : val_) (v_c_2 : val_)) = None) -> Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__CONST v_t (v_c_2 : val_));(admininstr__BINOP v_t (v_binop : binop_))] [(admininstr__TRAP )]
	| Step_pure__testop : forall (v_t : valtype) (v_c_1 : val_) (v_testop : testop_) (v_c : iN), ((v_c : val_) = (fun_testop v_t (v_testop : testop_) (v_c_1 : val_))) -> Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__TESTOP v_t (v_testop : testop_))] [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_))]
	| Step_pure__relop : forall (v_t : valtype) (v_c_1 : val_) (v_c_2 : val_) (v_relop : relop_) (v_c : iN), ((v_c : val_) = (fun_relop v_t (v_relop : relop_) (v_c_1 : val_) (v_c_2 : val_))) -> Step_pure [(admininstr__CONST v_t (v_c_1 : val_));(admininstr__CONST v_t (v_c_2 : val_));(admininstr__RELOP v_t (v_relop : relop_))] [(admininstr__CONST (valtype__INN (inn__I32 )) (v_c : val_))]
	| Step_pure__cvtop_val : forall (v_t_1 : valtype) (v_c_1 : val_) (v_t_2 : valtype) (v_cvtop : cvtop) (v_sx : (option sx)) (v_c : val_), ((fun_cvtop v_t_1 v_t_2 v_cvtop v_sx (v_c_1 : val_)) = (Some (v_c : val_))) -> Step_pure [(admininstr__CONST v_t_1 (v_c_1 : val_));(admininstr__CVTOP v_t_2 v_cvtop v_t_1 v_sx)] [(admininstr__CONST v_t_2 (v_c : val_))]
	| Step_pure__cvtop_trap : forall (v_t_1 : valtype) (v_c_1 : val_) (v_t_2 : valtype) (v_cvtop : cvtop) (v_sx : (option sx)), ((fun_cvtop v_t_1 v_t_2 v_cvtop v_sx (v_c_1 : val_)) = None) -> Step_pure [(admininstr__CONST v_t_1 (v_c_1 : val_));(admininstr__CVTOP v_t_2 v_cvtop v_t_1 v_sx)] [(admininstr__TRAP )]
	| Step_pure__local_tee : forall (v_val : val) (v_x : idx), Step_pure [(v_val : admininstr);(admininstr__LOCAL_TEE v_x)] [(v_val : admininstr);(v_val : admininstr);(admininstr__LOCAL_SET v_x)].

(* Inductive Relations Definition at: spec/wasm-1.0-test/8-reduction.watsup:7.1-7.63 *)
Inductive Step_read_before_Step_read__call_indirect_trap: config -> Prop :=
	| Step_read__call_indirect_call_neg : forall (v_z : state) (v_i : nat) (v_x : idx) (v_a : addr), (v_i < (List.length (tableinst__REFS (fun_table v_z 0)))) -> (v_a < (List.length (fun_funcinst v_z))) -> ((lookup_total (tableinst__REFS (fun_table v_z 0)) v_i) = (Some v_a)) -> ((fun_type v_z v_x) = (funcinst__TYPE (lookup_total (fun_funcinst v_z) v_a))) -> Step_read_before_Step_read__call_indirect_trap (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CALL_INDIRECT v_x)]).

(* Inductive Relations Definition at: spec/wasm-1.0-test/8-reduction.watsup:7.1-7.63 *)
Inductive Step_read: config -> (list admininstr) -> Prop :=
	| Step_read__block : forall (v_z : state) (v_t : (option valtype)) (v_instr : (list instr)) (v_n : n), (((v_t = None) /\ (v_n = 0)) \/ ((v_t <> None) /\ (v_n = 1))) -> Step_read (config__ v_z [(admininstr__BLOCK v_t v_instr)]) [(admininstr__LABEL_ v_n [] (list__instr__admininstr v_instr))]
	| Step_read__loop : forall (v_z : state) (v_t : (option valtype)) (v_instr : (list instr)) (v_n : n), (((v_t = None) /\ (v_n = 0)) \/ ((v_t <> None) /\ (v_n = 1))) -> Step_read (config__ v_z [(admininstr__LOOP v_t v_instr)]) [(admininstr__LABEL_ v_n [(instr__LOOP v_t v_instr)] (list__instr__admininstr v_instr))]
	| Step_read__call : forall (v_z : state) (v_x : idx), (v_x < (List.length (fun_funcaddr v_z))) -> Step_read (config__ v_z [(admininstr__CALL v_x)]) [(admininstr__CALL_ADDR (lookup_total (fun_funcaddr v_z) v_x))]
	| Step_read__call_indirect_call : forall (v_z : state) (v_i : nat) (v_x : idx) (v_a : addr), (v_i < (List.length (tableinst__REFS (fun_table v_z 0)))) -> (v_a < (List.length (fun_funcinst v_z))) -> ((lookup_total (tableinst__REFS (fun_table v_z 0)) v_i) = (Some v_a)) -> ((fun_type v_z v_x) = (funcinst__TYPE (lookup_total (fun_funcinst v_z) v_a))) -> Step_read (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CALL_INDIRECT v_x)]) [(admininstr__CALL_ADDR v_a)]
	| Step_read__call_indirect_trap : forall (v_z : state) (v_i : nat) (v_x : idx), (~(Step_read_before_Step_read__call_indirect_trap (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CALL_INDIRECT v_x)]))) -> Step_read (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CALL_INDIRECT v_x)]) [(admininstr__TRAP )]
	| Step_read__call_addr : forall (v_z : state) (v_val : (list val)) (v_k : nat) (v_a : addr) (v_n : n) (v_f : frame) (v_instr : (list instr)) (v_t_1 : (list valtype)) (v_t_2 : (option valtype)) (v_mm : moduleinst) (v_func : func) (v_x : idx) (v_t : (list valtype)), (v_a < (List.length (fun_funcinst v_z))) -> ((lookup_total (fun_funcinst v_z) v_a) = {| funcinst__TYPE := (functype__ v_t_1 v_t_2); funcinst__MODULE := v_mm; funcinst__CODE := v_func |}) -> ((List.length v_t_1) = (List.length v_val)) -> (v_n = (fun_optionSize v_t_2)) -> (v_func = (func__FUNC v_x (List.map (fun v_t => (local__LOCAL v_t)) (v_t)) v_instr)) -> (v_f = {| frame__LOCALS := (@app _ v_val (List.map (fun v_t => (fun_default_ v_t)) (v_t))); frame__MODULE := v_mm |}) -> Step_read (config__ v_z (@app _ (list__val__admininstr v_val) [(admininstr__CALL_ADDR v_a)])) [(admininstr__FRAME_ v_n v_f [(admininstr__LABEL_ v_n [] (list__instr__admininstr v_instr))])]
	| Step_read__local_get : forall (v_z : state) (v_x : idx), Step_read (config__ v_z [(admininstr__LOCAL_GET v_x)]) [((fun_local v_z v_x) : admininstr)]
	| Step_read__global_get : forall (v_z : state) (v_x : idx), Step_read (config__ v_z [(admininstr__GLOBAL_GET v_x)]) [((globalinst__VALUE (fun_global v_z v_x)) : admininstr)]
	| Step_read__load_num_trap : forall (v_z : state) (v_i : nat) (v_t : valtype) (v_mo : memop), (((v_i + (memop__OFFSET v_mo)) + ((fun_size v_t) / 8)) > (List.length (meminst__BYTES (fun_mem v_z 0)))) -> Step_read (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__LOAD_ v_t None v_mo)]) [(admininstr__TRAP )]
	| Step_read__load_num_val : forall (v_z : state) (v_i : nat) (v_t : valtype) (v_mo : memop) (v_c : val_), ((fun_bytes v_t (v_c : val_)) = (list_slice (meminst__BYTES (fun_mem v_z 0)) (v_i + (memop__OFFSET v_mo)) ((fun_size v_t) / 8))) -> Step_read (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__LOAD_ v_t None v_mo)]) [(admininstr__CONST v_t (v_c : val_))]
	| Step_read__load_pack_trap : forall (v_z : state) (v_i : nat) (v_inn : inn) (v_n : n) (v_sx : sx) (v_mo : memop), (((v_i + (memop__OFFSET v_mo)) + (v_n / 8)) > (List.length (meminst__BYTES (fun_mem v_z 0)))) -> Step_read (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__LOAD_ (valtype__INN v_inn) (Some ((packsize__ v_n), v_sx)) v_mo)]) [(admininstr__TRAP )]
	| Step_read__load_pack_val : forall (v_z : state) (v_i : nat) (v_inn : inn) (v_n : n) (v_sx : sx) (v_mo : memop) (v_c : iN), ((fun_ibytes v_n v_c) = (list_slice (meminst__BYTES (fun_mem v_z 0)) (v_i + (memop__OFFSET v_mo)) (v_n / 8))) -> Step_read (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__LOAD_ (valtype__INN v_inn) (Some ((packsize__ v_n), v_sx)) v_mo)]) [(admininstr__CONST (valtype__INN v_inn) (fun_ext v_n (fun_size (valtype__INN v_inn)) v_sx v_c))]
	| Step_read__memory_size : forall (v_z : state) (v_n : n), (((v_n * 64) * (fun_Ki )) = (List.length (meminst__BYTES (fun_mem v_z 0)))) -> Step_read (config__ v_z [(admininstr__MEMORY_SIZE )]) [(admininstr__CONST (valtype__INN (inn__I32 )) (v_n : val_))].

(* Mutual Recursion at: spec/wasm-1.0-test/8-reduction.watsup:5.1-5.63 *)
(* Inductive Relations Definition at: spec/wasm-1.0-test/8-reduction.watsup:5.1-5.63 *)
Inductive Step: config -> config -> Prop :=
	| Step__pure : forall (v_z : state) (v_admininstr : (list admininstr)) (v_admininstr' : (list admininstr)), (Step_pure v_admininstr v_admininstr') -> Step (config__ v_z v_admininstr) (config__ v_z v_admininstr')
	| Step__read : forall (v_z : state) (v_admininstr : (list admininstr)) (v_admininstr' : (list admininstr)), (Step_read (config__ v_z v_admininstr) v_admininstr') -> Step (config__ v_z v_admininstr) (config__ v_z v_admininstr')
	| Step__ctxt_seq : forall (v_z : state) (v_val : (list val)) (v_admininstr : (list admininstr)) (v_admininstr'' : (list admininstr)) (v_z' : state) (v_admininstr' : (list admininstr)), (Step (config__ v_z v_admininstr) (config__ v_z' v_admininstr')) -> Step (config__ v_z (@app _ (list__val__admininstr v_val) (@app _ v_admininstr v_admininstr''))) (config__ v_z' (@app _ (list__val__admininstr v_val) (@app _ v_admininstr' v_admininstr'')))
	| Step__ctxt_label : forall (v_z : state) (v_n : n) (v_instr : (list instr)) (v_admininstr : (list admininstr)) (v_z' : state) (v_admininstr' : (list admininstr)), (Step (config__ v_z v_admininstr) (config__ v_z' v_admininstr')) -> Step (config__ v_z [(admininstr__LABEL_ v_n v_instr v_admininstr)]) (config__ v_z' [(admininstr__LABEL_ v_n v_instr v_admininstr')])
	| Step__ctxt_frame : forall (v_s : store) (v_f : frame) (v_n : n) (v_f' : frame) (v_admininstr : (list admininstr)) (v_s' : store) (v_f'' : frame) (v_admininstr' : (list admininstr)), (Step (config__ (state__ v_s v_f') v_admininstr) (config__ (state__ v_s' v_f'') v_admininstr')) -> Step (config__ (state__ v_s v_f) [(admininstr__FRAME_ v_n v_f' v_admininstr)]) (config__ (state__ v_s' v_f) [(admininstr__FRAME_ v_n v_f'' v_admininstr')])
	| Step__local_set : forall (v_z : state) (v_val : val) (v_x : idx), Step (config__ v_z [(v_val : admininstr);(admininstr__LOCAL_SET v_x)]) (config__ (fun_with_local v_z v_x v_val) [])
	| Step__global_set : forall (v_z : state) (v_val : val) (v_x : idx), Step (config__ v_z [(v_val : admininstr);(admininstr__GLOBAL_SET v_x)]) (config__ (fun_with_global v_z v_x v_val) [])
	| Step__store_num_trap : forall (v_z : state) (v_i : nat) (v_t : valtype) (v_c : val_) (v_mo : memop), (((v_i + (memop__OFFSET v_mo)) + ((fun_size v_t) / 8)) > (List.length (meminst__BYTES (fun_mem v_z 0)))) -> Step (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CONST v_t (v_c : val_));(admininstr__STORE v_t None v_mo)]) (config__ v_z [(admininstr__TRAP )])
	| Step__store_num_val : forall (v_z : state) (v_i : nat) (v_t : valtype) (v_c : val_) (v_mo : memop) (v_b : (list byte)), (v_b = (fun_bytes v_t (v_c : val_))) -> Step (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CONST v_t (v_c : val_));(admininstr__STORE v_t None v_mo)]) (config__ (fun_with_mem v_z 0 (v_i + (memop__OFFSET v_mo)) ((fun_size v_t) / 8) v_b) [])
	| Step__store_pack_trap : forall (v_z : state) (v_i : nat) (v_inn : inn) (v_c : iN) (v_n : n) (v_mo : memop), (((v_i + (memop__OFFSET v_mo)) + (v_n / 8)) > (List.length (meminst__BYTES (fun_mem v_z 0)))) -> Step (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CONST (valtype__INN v_inn) (v_c : val_));(admininstr__STORE (valtype__INN v_inn) (Some (packsize__ v_n)) v_mo)]) (config__ v_z [(admininstr__TRAP )])
	| Step__store_pack_val : forall (v_z : state) (v_i : nat) (v_inn : inn) (v_c : iN) (v_n : n) (v_mo : memop) (v_b : (list byte)), (v_b = (fun_ibytes v_n (fun_wrap (fun_size (valtype__INN v_inn)) v_n v_c))) -> Step (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_i : val_));(admininstr__CONST (valtype__INN v_inn) (v_c : val_));(admininstr__STORE (valtype__INN v_inn) (Some (packsize__ v_n)) v_mo)]) (config__ (fun_with_mem v_z 0 (v_i + (memop__OFFSET v_mo)) (v_n / 8) v_b) [])
	| Step__memory_grow_succeed : forall (v_z : state) (v_n : n) (v_mi : meminst), (growmemory (fun_mem v_z 0) v_n v_mi) -> Step (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_n : val_));(admininstr__MEMORY_GROW )]) (config__ (fun_with_meminst v_z 0 v_mi) [(admininstr__CONST (valtype__INN (inn__I32 )) ((List.length (meminst__BYTES (fun_mem v_z 0))) / (64 * (fun_Ki ))))])
	| Step__memory_grow_fail : forall (v_z : state) (v_n : n), Step (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (v_n : val_));(admininstr__MEMORY_GROW )]) (config__ v_z [(admininstr__CONST (valtype__INN (inn__I32 )) (fun_invsigned 32 (0 - (1 : nat))))]).

(* Mutual Recursion at: spec/wasm-1.0-test/8-reduction.watsup:8.1-8.63 *)
(* Inductive Relations Definition at: spec/wasm-1.0-test/8-reduction.watsup:8.1-8.63 *)
Inductive Steps: config -> config -> Prop :=
	| Steps__refl : forall (v_z : state) (v_admininstr : (list admininstr)), Steps (config__ v_z v_admininstr) (config__ v_z v_admininstr)
	| Steps__trans : forall (v_z : state) (v_admininstr : (list admininstr)) (v_z'' : state) (v_admininstr'' : (list admininstr)) (v_z' : state) (v_admininstr' : admininstr), (Step (config__ v_z v_admininstr) (config__ v_z' [v_admininstr'])) -> (Steps (config__ v_z' [v_admininstr']) (config__ v_z'' v_admininstr'')) -> Steps (config__ v_z v_admininstr) (config__ v_z'' v_admininstr'').

(* Inductive Relations Definition at: spec/wasm-1.0-test/8-reduction.watsup:29.1-29.69 *)
Inductive Eval_expr: state -> expr -> state -> (list val) -> Prop :=
	| Eval_expr__ : forall (v_z : state) (v_instr : (list instr)) (v_z' : state) (v_val : (list val)), (Steps (config__ v_z (list__instr__admininstr v_instr)) (config__ v_z' (list__val__admininstr v_val))) -> Eval_expr v_z v_instr v_z' v_val.

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:8.1-8.34 *)
Inductive Val_ok: val -> valtype -> Prop :=
	| Val_ok__ : forall (v_t : valtype) (v_c_t : val_), Val_ok (val__CONST v_t (v_c_t : val_)) v_t.

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:16.1-16.41 *)
Inductive Result_ok: result -> (list valtype) -> Prop :=
	| Result_ok__result : forall (v_v : (list val)) (v_t : (list valtype)), ((List.length v_t) = (List.length v_v)) -> List.Forall2 (fun v_t v_v => (Val_ok v_v v_t)) (v_t) (v_v) -> Result_ok (result___VALS v_v) v_t
	| Result_ok__trap : forall (v_t : (list valtype)), Result_ok (result__TRAP ) v_t.

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:27.1-27.56 *)
Inductive Externvals_ok: store -> externval -> externtype -> Prop :=
	| Externvals_ok__func : forall (v_S : store) (v_a : addr) (v_ext : functype) (v_minst : moduleinst) (v_code_func : func), (v_a < (List.length (store__FUNCS v_S))) -> ((lookup_total (store__FUNCS v_S) v_a) = {| funcinst__TYPE := v_ext; funcinst__MODULE := v_minst; funcinst__CODE := v_code_func |}) -> Externvals_ok v_S (externval__FUNC v_a) (externtype__FUNC v_ext)
	| Externvals_ok__table : forall (v_S : store) (v_a : addr) (v_reserved__tt : tabletype) (v_tt' : tabletype) (v_fa : (list (option funcaddr))), (v_a < (List.length (store__TABLES v_S))) -> ((lookup_total (store__TABLES v_S) v_a) = {| tableinst__TYPE := v_tt'; tableinst__REFS := v_fa |}) -> (Tabletype_sub v_tt' v_reserved__tt) -> Externvals_ok v_S (externval__TABLE v_a) (externtype__TABLE v_reserved__tt)
	| Externvals_ok__mem : forall (v_S : store) (v_a : addr) (v_mt : memtype) (v_mt' : memtype) (v_b : (list byte)), (v_a < (List.length (store__MEMS v_S))) -> ((lookup_total (store__MEMS v_S) v_a) = {| meminst__TYPE := v_mt'; meminst__BYTES := v_b |}) -> (Memtype_sub v_mt' v_mt) -> Externvals_ok v_S (externval__MEM v_a) (externtype__MEM v_mt)
	| Externvals_ok__global : forall (v_S : store) (v_a : addr) (v_mut : mut) (v_valtype : valtype) (v_val_ : val_), (v_a < (List.length (store__GLOBALS v_S))) -> ((lookup_total (store__GLOBALS v_S) v_a) = {| globalinst__TYPE := (globaltype__ v_mut v_valtype); globalinst__VALUE := (val__CONST v_valtype (v_val_ : val_)) |}) -> Externvals_ok v_S (externval__GLOBAL v_a) (externtype__GLOBAL (globaltype__ v_mut v_valtype)).

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:49.1-49.56 *)
Inductive Memory_instance_ok: store -> meminst -> memtype -> Prop :=
	| Memory_instance_ok__ : forall (v_S : store) (v_mt : memtype) (v_b : (list byte)) (v_n : n) (v_m : m), (v_mt = (limits__ v_n v_m)) -> ((List.length v_b) = ((v_n * 64) * (fun_Ki ))) -> (Memtype_ok v_mt) -> Memory_instance_ok v_S {| meminst__TYPE := v_mt; meminst__BYTES := v_b |} v_mt.

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:59.1-59.59 *)
Inductive Table_instance_ok: store -> tableinst -> tabletype -> Prop :=
	| Table_instance_ok__ : forall (v_S : store) (v_reserved__tt : tabletype) (v_fa : (list (option funcaddr))) (v_n : n) (v_m : m) (v_functype : (list (option functype))), ((List.length v_fa) = (List.length v_functype)) -> List.Forall2 (fun v_fa v_functype => ((v_fa = None) <-> (v_functype = None))) (v_fa) (v_functype) -> (v_reserved__tt = (limits__ v_n v_m)) -> List.Forall2 (fun v_fa v_functype => List.Forall2 (fun v_fa v_functype => (Externvals_ok v_S (externval__FUNC v_fa) (externtype__FUNC v_functype))) (option_to_list v_fa) (option_to_list v_functype)) (v_fa) (v_functype) -> (Tabletype_ok v_reserved__tt) -> Table_instance_ok v_S {| tableinst__TYPE := v_reserved__tt; tableinst__REFS := v_fa |} v_reserved__tt.

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:69.1-69.62 *)
Inductive Global_instance_ok: store -> globalinst -> globaltype -> Prop :=
	| Global_instance_ok__ : forall (v_S : store) (v_gt : globaltype) (v_v : val) (v_mut : mut) (v_vt : valtype), (v_gt = (globaltype__ v_mut v_vt)) -> (Globaltype_ok v_gt) -> (Val_ok v_v v_vt) -> Global_instance_ok v_S {| globalinst__TYPE := v_gt; globalinst__VALUE := v_v |} v_gt.

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:79.1-79.54 *)
Inductive Export_instance_ok: store -> exportinst -> Prop :=
	| Export_instance_ok__OK : forall (v_S : store) (v_name : name) (v_eval : externval) (v_ext : externtype), (Externvals_ok v_S v_eval v_ext) -> Export_instance_ok v_S {| exportinst__NAME := v_name; exportinst__VALUE := v_eval |}.

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:87.1-87.59 *)
Inductive Module_instance_ok: store -> moduleinst -> context -> Prop :=
	| Module_instance_ok__ : forall (v_S : store) (v_functype : (list functype)) (v_funcaddr : (list funcaddr)) (v_globaladdr : (list globaladdr)) (v_tableaddr : (list tableaddr)) (v_memaddr : (list memaddr)) (v_exportinst : (list exportinst)) (v_functype' : (list functype)) (v_globaltype : (list globaltype)) (v_tabletype : (list tabletype)) (v_memtype : (list memtype)), ((List.length v_funcaddr) = (List.length v_functype')) -> ((List.length v_tableaddr) = (List.length v_tabletype)) -> ((List.length v_globaladdr) = (List.length v_globaltype)) -> ((List.length v_memaddr) = (List.length v_memtype)) -> List.Forall (fun v_functype => (Functype_ok v_functype)) (v_functype) -> List.Forall2 (fun v_funcaddr v_functype' => (Externvals_ok v_S (externval__FUNC v_funcaddr) (externtype__FUNC v_functype'))) (v_funcaddr) (v_functype') -> List.Forall2 (fun v_tableaddr v_tabletype => (Externvals_ok v_S (externval__TABLE v_tableaddr) (externtype__TABLE v_tabletype))) (v_tableaddr) (v_tabletype) -> List.Forall2 (fun v_globaladdr v_globaltype => (Externvals_ok v_S (externval__GLOBAL v_globaladdr) (externtype__GLOBAL v_globaltype))) (v_globaladdr) (v_globaltype) -> List.Forall2 (fun v_memaddr v_memtype => (Externvals_ok v_S (externval__MEM v_memaddr) (externtype__MEM v_memtype))) (v_memaddr) (v_memtype) -> List.Forall (fun v_exportinst => (Export_instance_ok v_S v_exportinst)) (v_exportinst) -> Module_instance_ok v_S {| moduleinst__TYPES := v_functype; moduleinst__FUNCS := v_funcaddr; moduleinst__GLOBALS := v_globaladdr; moduleinst__TABLES := v_tableaddr; moduleinst__MEMS := v_memaddr; moduleinst__EXPORTS := v_exportinst |} {| context__TYPES := v_functype; context__FUNCS := v_functype'; context__GLOBALS := v_globaltype; context__TABLES := v_tabletype; context__MEMS := v_memtype; context__LOCALS := []; context__LABELS := []; context__RETURN := None |}.

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:101.1-101.60 *)
Inductive Function_instance_ok: store -> funcinst -> functype -> Prop :=
	| Function_instance_ok__ : forall (v_S : store) (v_functype : functype) (v_moduleinst : moduleinst) (v_func : func) (v_C : context), (Functype_ok v_functype) -> (Module_instance_ok v_S v_moduleinst v_C) -> (Func_ok v_C v_func v_functype) -> Function_instance_ok v_S {| funcinst__TYPE := v_functype; funcinst__MODULE := v_moduleinst; funcinst__CODE := v_func |} v_functype.

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:111.1-111.33 *)
Inductive Store_ok: store -> Prop :=
	| Store_ok__OK : forall (v_S : store) (v_funcinst : (list funcinst)) (v_globalinst : (list globalinst)) (v_tableinst : (list tableinst)) (v_meminst : (list meminst)) (v_functype : (list functype)) (v_globaltype : (list globaltype)) (v_tabletype : (list tabletype)) (v_memtype : (list memtype)), ((List.length v_funcinst) = (List.length v_functype)) -> ((List.length v_globalinst) = (List.length v_globaltype)) -> ((List.length v_tableinst) = (List.length v_tabletype)) -> ((List.length v_meminst) = (List.length v_memtype)) -> (v_S = {| store__FUNCS := v_funcinst; store__GLOBALS := v_globalinst; store__TABLES := v_tableinst; store__MEMS := v_meminst |}) -> List.Forall2 (fun v_funcinst v_functype => (Function_instance_ok v_S v_funcinst v_functype)) (v_funcinst) (v_functype) -> List.Forall2 (fun v_globalinst v_globaltype => (Global_instance_ok v_S v_globalinst v_globaltype)) (v_globalinst) (v_globaltype) -> List.Forall2 (fun v_tableinst v_tabletype => (Table_instance_ok v_S v_tableinst v_tabletype)) (v_tableinst) (v_tabletype) -> List.Forall2 (fun v_meminst v_memtype => (Memory_instance_ok v_S v_meminst v_memtype)) (v_meminst) (v_memtype) -> Store_ok v_S.

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:176.1-176.44 *)
Inductive Frame_ok: store -> frame -> context -> Prop :=
	| Frame_ok__ : forall (v_S : store) (v_val : (list val)) (v_moduleinst : moduleinst) (v_C : context) (v_t : (list valtype)), ((List.length v_t) = (List.length v_val)) -> (Module_instance_ok v_S v_moduleinst v_C) -> List.Forall2 (fun v_t v_val => (Val_ok v_val v_t)) (v_t) (v_val) -> Frame_ok v_S {| frame__LOCALS := v_val; frame__MODULE := v_moduleinst |} ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := v_t; context__LABELS := []; context__RETURN := None |} ++ v_C).

(* Mutual Recursion at: spec/wasm-1.0-test/A-soundness.watsup:123.1-125.75 *)
(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:123.1-123.65 *)
Inductive Admin_instr_ok: store -> context -> admininstr -> functype -> Prop :=
	| Admin_instr_ok__instr : forall (v_S : store) (v_C : context) (v_instr : instr) (v_functype : functype), (Instr_ok v_C v_instr v_functype) -> Admin_instr_ok v_S v_C (v_instr : admininstr) v_functype
	| Admin_instr_ok__trap : forall (v_S : store) (v_C : context) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), Admin_instr_ok v_S v_C (admininstr__TRAP ) (functype__ v_t_1 v_t_2)
	| Admin_instr_ok__call_addr : forall (v_S : store) (v_C : context) (v_funcaddr : funcaddr) (v_t_1 : (list valtype)) (v_t_2 : (option valtype)), (Externvals_ok v_S (externval__FUNC v_funcaddr) (externtype__FUNC (functype__ v_t_1 v_t_2))) -> Admin_instr_ok v_S v_C (admininstr__CALL_ADDR v_funcaddr) (functype__ v_t_1 v_t_2)
	| Admin_instr_ok__label : forall (v_S : store) (v_C : context) (v_n : n) (v_instr : (list instr)) (v_admininstr : (list admininstr)) (v_t_2 : (option valtype)) (v_t_1 : (option valtype)), (Instrs_ok v_C v_instr (functype__ v_t_1 v_t_2)) -> (Admin_instrs_ok v_S ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := [v_t_1]; context__RETURN := None |} ++ v_C) v_admininstr (functype__ [] v_t_2)) -> (v_n = (fun_optionSize v_t_1)) -> Admin_instr_ok v_S v_C (admininstr__LABEL_ v_n v_instr v_admininstr) (functype__ [] v_t_2)
	| Admin_instr_ok__frame : forall (v_S : store) (v_C : context) (v_n : n) (v_F : frame) (v_admininstr : (list admininstr)) (v_t : (option valtype)), (Thread_ok v_S (Some v_t) v_F v_admininstr v_t) -> (v_n = (fun_optionSize v_t)) -> Admin_instr_ok v_S v_C (admininstr__FRAME_ v_n v_F v_admininstr) (functype__ [] v_t)
	| Admin_instr_ok__weakening : forall (v_S : store) (v_C : context) (v_admininstr : admininstr) (v_t : (list valtype)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), (Admin_instr_ok v_S v_C v_admininstr (functype__ v_t_1 v_t_2)) -> Admin_instr_ok v_S v_C v_admininstr (functype__ (@app _ v_t v_t_1) (@app _ v_t v_t_2))

with

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:124.1-124.67 *)
Admin_instrs_ok: store -> context -> (list admininstr) -> functype -> Prop :=
	| Admin_instrs_ok__empty : forall (v_S : store) (v_C : context), Admin_instrs_ok v_S v_C [] (functype__ [] [])
	| Admin_instrs_ok__seq : forall (v_S : store) (v_C : context) (v_admininstr_1 : (list admininstr)) (v_admininstr_2 : admininstr) (v_t_1 : (list valtype)) (v_t_3 : (list valtype)) (v_t_2 : (list valtype)), (Admin_instrs_ok v_S v_C v_admininstr_1 (functype__ v_t_1 v_t_2)) -> (Admin_instr_ok v_S v_C v_admininstr_2 (functype__ v_t_2 v_t_3)) -> Admin_instrs_ok v_S v_C (@app _ v_admininstr_1 [v_admininstr_2]) (functype__ v_t_1 v_t_3)
	| Admin_instrs_ok__frame : forall (v_S : store) (v_C : context) (v_admininstr : (list admininstr)) (v_t : (list valtype)) (v_t_1 : (list valtype)) (v_t_2 : (list valtype)), (Admin_instrs_ok v_S v_C v_admininstr (functype__ v_t_1 v_t_2)) -> Admin_instrs_ok v_S v_C v_admininstr (functype__ (@app _ v_t v_t_1) (@app _ v_t v_t_2))
	| Admin_instrs_ok__instrs : forall (v_S : store) (v_C : context) (v_instr : (list instr)) (v_functype : functype), (Instrs_ok v_C v_instr v_functype) -> Admin_instrs_ok v_S v_C (list__instr__admininstr v_instr) v_functype

with

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:125.1-125.75 *)
Thread_ok: store -> (option resulttype) -> frame -> (list admininstr) -> resulttype -> Prop :=
	| Thread_ok__ : forall (v_S : store) (v_rt : (option resulttype)) (v_F : frame) (v_admininstr : (list admininstr)) (v_t : (option valtype)) (v_C : context), (Frame_ok v_S v_F v_C) -> (Admin_instrs_ok v_S ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := []; context__RETURN := v_rt |} ++ v_C) v_admininstr (functype__ [] v_t)) -> Thread_ok v_S v_rt v_F v_admininstr v_t.

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:188.1-188.43 *)
Inductive Config_ok: config -> resulttype -> Prop :=
	| Config_ok__ : forall (v_S : store) (v_F : frame) (v_admininstr : (list admininstr)) (v_t : (option valtype)), (Store_ok v_S) -> (Thread_ok v_S None v_F v_admininstr v_t) -> Config_ok (config__ (state__ v_S v_F) v_admininstr) v_t.

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:199.1-199.48 *)
Inductive Func_extension: funcinst -> funcinst -> Prop :=
	| Func_extension__ : forall (v_funcinst : funcinst), Func_extension v_funcinst v_funcinst.

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:200.1-200.51 *)
Inductive Table_extension: tableinst -> tableinst -> Prop :=
	| Table_extension__ : forall (v_n1 : u32) (v_m : m) (v_fa_1 : (list (option funcaddr))) (v_n2 : u32) (v_fa_2 : (list (option funcaddr))), (v_n1 <= v_n2) -> Table_extension {| tableinst__TYPE := (limits__ v_n1 v_m); tableinst__REFS := v_fa_1 |} {| tableinst__TYPE := (limits__ v_n2 v_m); tableinst__REFS := v_fa_2 |}.

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:201.1-201.45 *)
Inductive Mem_extension: meminst -> meminst -> Prop :=
	| Mem_extension__ : forall (v_n1 : u32) (v_m : m) (v_b_1 : (list byte)) (v_n2 : u32) (v_b_2 : (list byte)), (v_n1 <= v_n2) -> Mem_extension {| meminst__TYPE := (limits__ v_n1 v_m); meminst__BYTES := v_b_1 |} {| meminst__TYPE := (limits__ v_n2 v_m); meminst__BYTES := v_b_2 |}.

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:202.1-202.54 *)
Inductive Global_extension: globalinst -> globalinst -> Prop :=
	| Global_extension__ : forall (v_mut : mut) (v_t2 : valtype) (v_c1 : val_) (v_c2 : val_), ((v_mut = (mut__MUT (Some tt))) \/ ((v_c1 : val_) = (v_c2 : val_))) -> Global_extension {| globalinst__TYPE := (globaltype__ v_mut v_t2); globalinst__VALUE := (val__CONST v_t2 (v_c1 : val_)) |} {| globalinst__TYPE := (globaltype__ v_mut v_t2); globalinst__VALUE := (val__CONST v_t2 (v_c2 : val_)) |}.

(* Inductive Relations Definition at: spec/wasm-1.0-test/A-soundness.watsup:203.1-203.43 *)
Inductive Store_extension: store -> store -> Prop :=
	| Store_extension__ : forall (v_store_1 : store) (v_store_2 : store) (v_funcinst_1 : (list funcinst)) (v_tableinst_1 : (list tableinst)) (v_meminst_1 : (list meminst)) (v_globalinst_1 : (list globalinst)) (v_funcinst_1' : (list funcinst)) (v_funcinst_2 : (list funcinst)) (v_tableinst_1' : (list tableinst)) (v_tableinst_2 : (list tableinst)) (v_meminst_1' : (list meminst)) (v_meminst_2 : (list meminst)) (v_globalinst_1' : (list globalinst)) (v_globalinst_2 : (list globalinst)), ((List.length v_funcinst_1) = (List.length v_funcinst_1')) -> ((List.length v_tableinst_1) = (List.length v_tableinst_1')) -> ((List.length v_meminst_1) = (List.length v_meminst_1')) -> ((List.length v_globalinst_1) = (List.length v_globalinst_1')) -> ((store__FUNCS v_store_1) = v_funcinst_1) -> ((store__TABLES v_store_1) = v_tableinst_1) -> ((store__MEMS v_store_1) = v_meminst_1) -> ((store__GLOBALS v_store_1) = v_globalinst_1) -> ((store__FUNCS v_store_2) = (@app _ v_funcinst_1' v_funcinst_2)) -> ((store__TABLES v_store_2) = (@app _ v_tableinst_1' v_tableinst_2)) -> ((store__MEMS v_store_2) = (@app _ v_meminst_1' v_meminst_2)) -> ((store__GLOBALS v_store_2) = (@app _ v_globalinst_1' v_globalinst_2)) -> List.Forall2 (fun v_funcinst_1 v_funcinst_1' => (Func_extension v_funcinst_1 v_funcinst_1')) (v_funcinst_1) (v_funcinst_1') -> List.Forall2 (fun v_tableinst_1 v_tableinst_1' => (Table_extension v_tableinst_1 v_tableinst_1')) (v_tableinst_1) (v_tableinst_1') -> List.Forall2 (fun v_meminst_1 v_meminst_1' => (Mem_extension v_meminst_1 v_meminst_1')) (v_meminst_1) (v_meminst_1') -> List.Forall2 (fun v_globalinst_1 v_globalinst_1' => (Global_extension v_globalinst_1 v_globalinst_1')) (v_globalinst_1) (v_globalinst_1') -> Store_extension v_store_1 v_store_2.

(* Mutual Recursion at: spec/wasm-1.0-test/A-soundness.watsup:235.1-235.31 *)
(* Auxiliary Definition at: spec/wasm-1.0-test/A-soundness.watsup:235.1-235.31 *)
Fixpoint fun_types_of (v___0 : (list val)) : (list valtype) :=
	match (v___0) with
		| ([]) => []
		| (((val__CONST v_valtype v_val_) :: v_val')) => (@app _ [v_valtype] (fun_types_of v_val'))
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/A-soundness.watsup:239.1-239.33 *)
Definition fun_is_const (v_admininstr_0 : admininstr) : bool :=
	match (v_admininstr_0) with
		| ((admininstr__CONST v_valtype v_val_)) => true
		| (v_admininstr) => false
	end.

(* Mutual Recursion at: spec/wasm-1.0-test/A-soundness.watsup:243.1-243.36 *)
(* Auxiliary Definition at: spec/wasm-1.0-test/A-soundness.watsup:243.1-243.36 *)
Fixpoint fun_const_list (v___0 : (list admininstr)) : bool :=
	match (v___0) with
		| ([]) => true
		| ((v_admininstr :: v_admininstr')) => ((fun_is_const v_admininstr) && (fun_const_list v_admininstr'))
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/A-soundness.watsup:247.1-247.35 *)
Definition fun_not_lf_br (v___0 : (list admininstr)) : Prop :=
	match (v___0) with
		| (v_admininstr) => forall (v_val : (list val)) (v_l : labelidx) (v_admininstr' : (list admininstr)), (v_admininstr <> (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__BR v_l)] v_admininstr')))
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/A-soundness.watsup:252.1-252.39 *)
Definition fun_not_lf_return (v___0 : (list admininstr)) : Prop :=
	match (v___0) with
		| (v_admininstr) => forall (v_val : (list val)) (v_l : labelidx) (v_admininstr' : (list admininstr)), (v_admininstr <> (@app _ (list__val__admininstr v_val) (@app _ [(admininstr__RETURN )] v_admininstr')))
	end.

(* Auxiliary Definition at: spec/wasm-1.0-test/A-soundness.watsup:257.1-257.39 *)
Definition fun_terminal_form (v___0 : (list admininstr)) : bool :=
	match (v___0) with
		| (v_admininstr) => ((fun_const_list v_admininstr) || (v_admininstr == [(admininstr__TRAP )]))
	end.

(* Theorem Definition at: spec/wasm-1.0-test/A-soundness.watsup:261.1-265.57 *)
Theorem t_progress : forall (v_s : store) (v_f : frame) (v_admininstr : admininstr) (v_t : valtype), forall (v_s : store) (v_f : frame) (v_admininstr : (list admininstr)) (v_t : (option valtype)), ((Config_ok (config__ (state__ v_s v_f) v_admininstr) v_t) -> ((fun_terminal_form v_admininstr) \/ forall (v_s' : store) (v_f' : frame) (v_admininstr' : (list admininstr)) (v_s : store) (v_f : frame) (v_admininstr : (list admininstr)), (Step (config__ (state__ v_s v_f) v_admininstr) (config__ (state__ v_s' v_f') v_admininstr')))).
Proof. Admitted.

(* Lemma Definition at: spec/wasm-1.0-test/A-soundness.watsup:272.1-283.62 *)
Lemma t_progress_e : forall (v_s : store) (v_C : context) (v_C' : context) (v_f : frame) (v_val : val) (v_admininstr : admininstr) (v_ft : functype) (v_valtype_1 : valtype) (v_valtype_2 : valtype) (v_lab : valtype) (v_ret : valtype), forall (v_s : store) (v_C : context) (v_C' : context) (v_f : frame) (v_val : (list val)) (v_admininstr : (list admininstr)) (v_ft : functype) (v_valtype_1 : (list valtype)) (v_valtype_2 : (list valtype)) (v_lab : valtype) (v_ret : valtype), ((Admin_instrs_ok v_s v_C v_admininstr v_ft) -> ((v_ft = (functype__ v_valtype_1 v_valtype_2)) -> ((v_C = ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := []; context__RETURN := (Some (Some v_ret)) |} ++ ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := [(Some v_lab)]; context__RETURN := None |} ++ ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := (fun_types_of (frame__LOCALS v_f)); context__LABELS := []; context__RETURN := None |} ++ v_C')))) -> ((Module_instance_ok v_s (frame__MODULE v_f) v_C) -> (((fun_types_of v_val) = v_valtype_1) -> ((Store_ok v_s) -> ((fun_not_lf_br v_admininstr) -> ((fun_not_lf_return v_admininstr) -> ((fun_terminal_form (@app _ (list__val__admininstr v_val) v_admininstr)) \/ forall (v_s' : store) (v_f' : frame) (v_admininstr' : (list admininstr)) (v_s : store) (v_f : frame) (v_val : (list val)) (v_admininstr : (list admininstr)), (Step (config__ (state__ v_s v_f) (@app _ (list__val__admininstr v_val) v_admininstr)) (config__ (state__ v_s' v_f') v_admininstr'))))))))))).
Proof. Admitted.

(* Lemma Definition at: spec/wasm-1.0-test/A-soundness.watsup:285.1-296.56 *)
Lemma t_progress_be : forall (v_s : store) (v_C : context) (v_C' : context) (v_f : frame) (v_val : val) (v_instr : instr) (v_ft : functype) (v_valtype_1 : valtype) (v_valtype_2 : valtype) (v_lab : valtype) (v_ret : valtype), forall (v_s : store) (v_C : context) (v_C' : context) (v_f : frame) (v_val : (list val)) (v_instr : (list instr)) (v_ft : functype) (v_valtype_1 : (list valtype)) (v_valtype_2 : (list valtype)) (v_lab : valtype) (v_ret : valtype), ((Instrs_ok v_C v_instr v_ft) -> ((v_ft = (functype__ v_valtype_1 v_valtype_2)) -> ((v_C = ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := []; context__RETURN := (Some (Some v_ret)) |} ++ ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := [(Some v_lab)]; context__RETURN := None |} ++ ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := (fun_types_of (frame__LOCALS v_f)); context__LABELS := []; context__RETURN := None |} ++ v_C')))) -> ((Module_instance_ok v_s (frame__MODULE v_f) v_C) -> (((fun_types_of v_val) = v_valtype_1) -> ((Store_ok v_s) -> ((fun_not_lf_br (list__instr__admininstr v_instr)) -> ((fun_not_lf_return (list__instr__admininstr v_instr)) -> ((fun_const_list (list__instr__admininstr v_instr)) \/ forall (v_s' : store) (v_f' : frame) (v_admininstr : (list admininstr)) (v_s : store) (v_f : frame) (v_val : (list val)) (v_instr : (list instr)), (Step (config__ (state__ v_s v_f) (@app _ (list__val__admininstr v_val) (list__instr__admininstr v_instr))) (config__ (state__ v_s' v_f') v_admininstr))))))))))).
Proof. Admitted.

(* Theorem Definition at: spec/wasm-1.0-test/A-soundness.watsup:298.1-298.46 *)
Theorem t_progress' : forall (v_s : store) (v_f : frame) (v_admininstr : (list admininstr)) (v_t : (option valtype)), ((Config_ok (config__ (state__ v_s v_f) v_admininstr) v_t) -> ((fun_terminal_form v_admininstr) \/ forall (v_s' : store) (v_f' : frame) (v_admininstr' : (list admininstr)) (v_s : store) (v_f : frame) (v_admininstr : (list admininstr)), (Step (config__ (state__ v_s v_f) v_admininstr) (config__ (state__ v_s' v_f') v_admininstr')))).
Proof. Admitted.

(* Lemma Definition at: spec/wasm-1.0-test/A-soundness.watsup:305.1-305.46 *)
Lemma t_progress_e' : forall (v_s : store) (v_C : context) (v_C' : context) (v_f : frame) (v_val : (list val)) (v_admininstr : (list admininstr)) (v_ft : functype) (v_valtype_1 : (list valtype)) (v_valtype_2 : (list valtype)) (v_lab : valtype) (v_ret : valtype), ((Admin_instrs_ok v_s v_C v_admininstr v_ft) -> ((v_ft = (functype__ v_valtype_1 v_valtype_2)) -> ((v_C = ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := []; context__RETURN := (Some (Some v_ret)) |} ++ ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := [(Some v_lab)]; context__RETURN := None |} ++ ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := (fun_types_of (frame__LOCALS v_f)); context__LABELS := []; context__RETURN := None |} ++ v_C')))) -> ((Module_instance_ok v_s (frame__MODULE v_f) v_C) -> (((fun_types_of v_val) = v_valtype_1) -> ((Store_ok v_s) -> ((fun_not_lf_br v_admininstr) -> ((fun_not_lf_return v_admininstr) -> ((fun_terminal_form (@app _ (list__val__admininstr v_val) v_admininstr)) \/ forall (v_s' : store) (v_f' : frame) (v_admininstr' : (list admininstr)) (v_s : store) (v_f : frame) (v_val : (list val)) (v_admininstr : (list admininstr)), (Step (config__ (state__ v_s v_f) (@app _ (list__val__admininstr v_val) v_admininstr)) (config__ (state__ v_s' v_f') v_admininstr'))))))))))).
Proof. Admitted.

(* Lemma Definition at: spec/wasm-1.0-test/A-soundness.watsup:319.1-319.47 *)
Lemma t_progress_be' : forall (v_s : store) (v_C : context) (v_C' : context) (v_f : frame) (v_val : (list val)) (v_instr : (list instr)) (v_ft : functype) (v_valtype_1 : (list valtype)) (v_valtype_2 : (list valtype)) (v_lab : valtype) (v_ret : valtype), ((Instrs_ok v_C v_instr v_ft) -> ((v_ft = (functype__ v_valtype_1 v_valtype_2)) -> ((v_C = ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := []; context__RETURN := (Some (Some v_ret)) |} ++ ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := []; context__LABELS := [(Some v_lab)]; context__RETURN := None |} ++ ({| context__TYPES := []; context__FUNCS := []; context__GLOBALS := []; context__TABLES := []; context__MEMS := []; context__LOCALS := (fun_types_of (frame__LOCALS v_f)); context__LABELS := []; context__RETURN := None |} ++ v_C')))) -> ((Module_instance_ok v_s (frame__MODULE v_f) v_C) -> (((fun_types_of v_val) = v_valtype_1) -> ((Store_ok v_s) -> ((fun_not_lf_br (list__instr__admininstr v_instr)) -> ((fun_not_lf_return (list__instr__admininstr v_instr)) -> ((fun_const_list (list__instr__admininstr v_instr)) \/ forall (v_s' : store) (v_f' : frame) (v_admininstr : (list admininstr)) (v_s : store) (v_f : frame) (v_val : (list val)) (v_instr : (list instr)), (Step (config__ (state__ v_s v_f) (@app _ (list__val__admininstr v_val) (list__instr__admininstr v_instr))) (config__ (state__ v_s' v_f') v_admininstr))))))))))).
Proof. Admitted.

