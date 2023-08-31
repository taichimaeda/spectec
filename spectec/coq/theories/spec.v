(* Coq code below *)

Require Import List String.

Import ListNotations.

Open Scope type_scope.

Definition n := nat.

Definition name := string.

Definition byte := nat.

Definition u32 := nat.

Definition idx := nat.

Definition funcidx := idx.

Definition globalidx := idx.

Definition tableidx := idx.

Definition memidx := idx.

Definition elemidx := idx.

Definition dataidx := idx.

Definition labelidx := idx.

Definition localidx := idx.

Inductive numtype : Type :=
| numtype__i32 : numtype
| numtype__i64 : numtype
| numtype__f32 : numtype
| numtype__f64 : numtype
.

Inductive vectype : Type :=
| vectype__v128 : vectype
.

Inductive reftype : Type :=
| reftype__funcref : reftype
| reftype__externref : reftype
.

Inductive valtype : Type :=
| valtype__i32 : valtype
| valtype__i64 : valtype
| valtype__f32 : valtype
| valtype__f64 : valtype
| valtype__v128 : valtype
| valtype__funcref : valtype
| valtype__externref : valtype
| valtype__bot : valtype
.

(* Funcdef *)
Definition valtype_numtype (arg : numtype) : valtype := 
  match arg with
  | (*case_pat*)numtype__i32 => (*case_exp*)valtype__i32
  | (*case_pat*)numtype__i64 => (*case_exp*)valtype__i64
  | (*case_pat*)numtype__f32 => (*case_exp*)valtype__f32
  | (*case_pat*)numtype__f64 => (*case_exp*)valtype__f64
end.

(* Funcdef *)
Definition valtype_reftype (arg : reftype) : valtype := 
  match arg with
  | (*case_pat*)reftype__funcref => (*case_exp*)valtype__funcref
  | (*case_pat*)reftype__externref => (*case_exp*)valtype__externref
end.

(* Funcdef *)
Definition valtype_vectype (arg : vectype) : valtype := 
  match arg with
  | (*case_pat*)vectype__v128 => (*case_exp*)valtype__v128
end.

Inductive In : Type :=
| In__i32 : In
| In__i64 : In
.

(* Funcdef *)
Definition numtype_in (arg : In) : numtype := 
  match arg with
  | (*case_pat*)In__i32 => (*case_exp*)numtype__i32
  | (*case_pat*)In__i64 => (*case_exp*)numtype__i64
end.

(* Funcdef *)
Definition valtype_in (arg : In) : valtype := 
  match arg with
  | (*case_pat*)In__i32 => (*case_exp*)valtype__i32
  | (*case_pat*)In__i64 => (*case_exp*)valtype__i64
end.

Inductive fn : Type :=
| fn__f32 : fn
| fn__f64 : fn
.

(* Funcdef *)
Definition numtype_fn (arg : fn) : numtype := 
  match arg with
  | (*case_pat*)fn__f32 => (*case_exp*)numtype__f32
  | (*case_pat*)fn__f64 => (*case_exp*)numtype__f64
end.

(* Funcdef *)
Definition valtype_fn (arg : fn) : valtype := 
  match arg with
  | (*case_pat*)fn__f32 => (*case_exp*)valtype__f32
  | (*case_pat*)fn__f64 => (*case_exp*)valtype__f64
end.

Definition resulttype := (list valtype).

Definition limits := (u32 * u32).

Definition globaltype := ((option unit) * valtype).

Definition functype := (resulttype * resulttype).

Definition tabletype := (limits * reftype).

Definition memtype := limits.

Definition elemtype := reftype.

Definition datatype := unit.

Inductive externtype : Type :=
| externtype__global : globaltype -> externtype
| externtype__func : functype -> externtype
| externtype__table : tabletype -> externtype
| externtype__mem : memtype -> externtype
.

Inductive sx : Type :=
| sx__u : sx
| sx__s : sx
.

Inductive unop_ixx : Type :=
| unop_ixx__clz : unop_ixx
| unop_ixx__ctz : unop_ixx
| unop_ixx__popcnt : unop_ixx
.

Inductive unop_fxx : Type :=
| unop_fxx__abs : unop_fxx
| unop_fxx__neg : unop_fxx
| unop_fxx__sqrt : unop_fxx
| unop_fxx__ceil : unop_fxx
| unop_fxx__floor : unop_fxx
| unop_fxx__trunc : unop_fxx
| unop_fxx__nearest : unop_fxx
.

Inductive binop_ixx : Type :=
| binop_ixx__add : binop_ixx
| binop_ixx__sub : binop_ixx
| binop_ixx__mul : binop_ixx
| binop_ixx__div : sx -> binop_ixx
| binop_ixx__rem : sx -> binop_ixx
| binop_ixx__and : binop_ixx
| binop_ixx__or : binop_ixx
| binop_ixx__xor : binop_ixx
| binop_ixx__shl : binop_ixx
| binop_ixx__shr : sx -> binop_ixx
| binop_ixx__rotl : binop_ixx
| binop_ixx__rotr : binop_ixx
.

Inductive binop_fxx : Type :=
| binop_fxx__add : binop_fxx
| binop_fxx__sub : binop_fxx
| binop_fxx__mul : binop_fxx
| binop_fxx__div : binop_fxx
| binop_fxx__min : binop_fxx
| binop_fxx__max : binop_fxx
| binop_fxx__copysign : binop_fxx
.

Inductive testop_ixx : Type :=
| testop_ixx__eqz : testop_ixx
.

Inductive testop_fxx : Type :=
.

Inductive relop_ixx : Type :=
| relop_ixx__eq : relop_ixx
| relop_ixx__ne : relop_ixx
| relop_ixx__lt : sx -> relop_ixx
| relop_ixx__gt : sx -> relop_ixx
| relop_ixx__le : sx -> relop_ixx
| relop_ixx__ge : sx -> relop_ixx
.

Inductive relop_fxx : Type :=
| relop_fxx__eq : relop_fxx
| relop_fxx__ne : relop_fxx
| relop_fxx__lt : relop_fxx
| relop_fxx__gt : relop_fxx
| relop_fxx__le : relop_fxx
| relop_fxx__ge : relop_fxx
.

Inductive unop_numtype : Type :=
| unop_numtype___i : unop_ixx -> unop_numtype
| unop_numtype___f : unop_fxx -> unop_numtype
.

Inductive binop_numtype : Type :=
| binop_numtype___i : binop_ixx -> binop_numtype
| binop_numtype___f : binop_fxx -> binop_numtype
.

Inductive testop_numtype : Type :=
| testop_numtype___i : testop_ixx -> testop_numtype
| testop_numtype___f : testop_fxx -> testop_numtype
.

Inductive relop_numtype : Type :=
| relop_numtype___i : relop_ixx -> relop_numtype
| relop_numtype___f : relop_fxx -> relop_numtype
.

Inductive cvtop : Type :=
| cvtop__convert : cvtop
| cvtop__reinterpret : cvtop
.

Definition c_numtype := nat.

Definition c_vectype := nat.

Definition blocktype := functype.

Inductive instr : Type :=
| instr__unreachable : instr
| instr__nop : instr
| instr__drop : instr
| instr__select : (option valtype) -> instr
| instr__block : blocktype -> (list instr) -> instr
| instr__loop : blocktype -> (list instr) -> instr
| instr__if : blocktype -> (list instr) -> (list instr) -> instr
| instr__br : labelidx -> instr
| instr__br_if : labelidx -> instr
| instr__br_table : (list labelidx) -> labelidx -> instr
| instr__call : funcidx -> instr
| instr__call_indirect : tableidx -> functype -> instr
| instr__return : instr
| instr__const : numtype -> c_numtype -> instr
| instr__unop : numtype -> unop_numtype -> instr
| instr__binop : numtype -> binop_numtype -> instr
| instr__testop : numtype -> testop_numtype -> instr
| instr__relop : numtype -> relop_numtype -> instr
| instr__extend : numtype -> n -> instr
| instr__cvtop : numtype -> cvtop -> numtype -> (option sx) -> instr
| instr__ref_null : reftype -> instr
| instr__ref_func : funcidx -> instr
| instr__ref_is_null : instr
| instr__local_get : localidx -> instr
| instr__local_set : localidx -> instr
| instr__local_tee : localidx -> instr
| instr__global_get : globalidx -> instr
| instr__global_set : globalidx -> instr
| instr__table_get : tableidx -> instr
| instr__table_set : tableidx -> instr
| instr__table_size : tableidx -> instr
| instr__table_grow : tableidx -> instr
| instr__table_fill : tableidx -> instr
| instr__table_copy : tableidx -> tableidx -> instr
| instr__table_init : tableidx -> elemidx -> instr
| instr__elem_drop : elemidx -> instr
| instr__memory_size : instr
| instr__memory_grow : instr
| instr__memory_fill : instr
| instr__memory_copy : instr
| instr__memory_init : dataidx -> instr
| instr__data_drop : dataidx -> instr
| instr__load : numtype -> (option (n * sx)) -> u32 -> u32 -> instr
| instr__store : numtype -> (option n) -> u32 -> u32 -> instr
.

Definition expr := (list instr).

Inductive elemmode : Type :=
| elemmode__table : tableidx -> expr -> elemmode
| elemmode__declare : elemmode
.

Inductive datamode : Type :=
| datamode__memory : memidx -> expr -> datamode
.

Definition func := (functype * (list valtype) * expr).

Definition global := (globaltype * expr).

Definition table := tabletype.

Definition mem := memtype.

Definition elem := (reftype * (list expr) * (option elemmode)).

Definition data := ((list byte) * (option datamode)).

Definition start := funcidx.

Inductive externuse : Type :=
| externuse__func : funcidx -> externuse
| externuse__global : globalidx -> externuse
| externuse__table : tableidx -> externuse
| externuse__mem : memidx -> externuse
.

Definition export := (name * externuse).

Definition import := (name * name * externtype).

Definition module := ((list import) * (list func) * (list global) * (list table) * (list mem) * (list elem) * (list data) * (option start) * (list export)).

(* Funcdef *)
Definition ki (arg : unit) : nat := 
  match arg with
  | (* Empty Tuple *) tt => 1024
end.

(* Funcdef *)
Definition size (arg : valtype) : (option nat) := 
  match arg with
  | (*case_pat*)valtype__i32 => (Some 32)
  | (*case_pat*)valtype__i64 => (Some 64)
  | (*case_pat*)valtype__f32 => (Some 32)
  | (*case_pat*)valtype__f64 => (Some 64)
  | (*case_pat*)valtype__v128 => (Some 128)
  | (*var_pat*)x => None
end.

(* Funcdef *)
Definition test_sub_atom_22 (arg : n) : nat := 
  match arg with
  | (*var_pat*)n_3_atom_y => 0
end.

(* Funcdef *)
Definition curried_ (arg : (n * n)) : nat := 
  match arg with
  | ((*var_pat*)n_1, (*var_pat*)n_2) => n_1 + n_2
end.

Record context : Type :=
{
  context__func : (list functype);
  context__global : (list globaltype);
  context__table : (list tabletype);
  context__mem : (list memtype);
  context__elem : (list elemtype);
  context__data : (list datatype);
  context__local : (list valtype);
  context__label : (list resulttype);
  context__return : (option resulttype)
}.

Inductive limits_ok : (limits * nat) -> Prop :=
| limits_ok__noname (k : nat) (n_1 : n) (n_2 : n): 
  n_1 <= n_2 /\ n_2 <= k ->
  limits_ok ((n_1, n_2), k)
.

Inductive functype_ok : functype -> Prop :=
| functype_ok__noname (ft : functype): 
  functype_ok ft
.

Inductive globaltype_ok : globaltype -> Prop :=
| globaltype_ok__noname (gt : globaltype): 
  globaltype_ok gt
.

Inductive tabletype_ok : tabletype -> Prop :=
| tabletype_ok__noname (lim : limits) (rt : reftype): 
  (limits_ok (lim, Nat.pow 2 32 - 1)) ->
  tabletype_ok (lim, rt)
.

Inductive memtype_ok : memtype -> Prop :=
| memtype_ok__noname (lim : limits): 
  (limits_ok (lim, Nat.pow 2 16)) ->
  memtype_ok lim
.

Inductive externtype_ok : externtype -> Prop :=
| externtype_ok__func (functype : functype): 
  (functype_ok functype) ->
  externtype_ok ((*case_exp*)externtype__func functype)
| externtype_ok__global (globaltype : globaltype): 
  (globaltype_ok globaltype) ->
  externtype_ok ((*case_exp*)externtype__global globaltype)
| externtype_ok__table (tabletype : tabletype): 
  (tabletype_ok tabletype) ->
  externtype_ok ((*case_exp*)externtype__table tabletype)
| externtype_ok__mem (memtype : memtype): 
  (memtype_ok memtype) ->
  externtype_ok ((*case_exp*)externtype__mem memtype)
.

Inductive valtype_sub : (valtype * valtype) -> Prop :=
| valtype_sub__refl (t : valtype): 
  valtype_sub (t, t)
| valtype_sub__bot (t : valtype): 
  valtype_sub ((*case_exp*)valtype__bot, t)
.

Inductive resulttype_sub : ((list valtype) * (list valtype)) -> Prop :=
| resulttype_sub__noname (t_1 : (list valtype)) (t_2 : (list valtype)): 
  (List.length t_1) = (List.length t_2) ->
  (List.Forall2 (fun t_1 t_2 => (valtype_sub (t_1, t_2))) t_1 t_2) ->
  resulttype_sub (t_1, t_2)
.

Inductive limits_sub : (limits * limits) -> Prop :=
| limits_sub__noname (n_11 : n) (n_12 : n) (n_21 : n) (n_22 : n): 
  n_11 >= n_21 ->
  n_12 <= n_22 ->
  limits_sub ((n_11, n_12), (n_21, n_22))
.

Inductive functype_sub : (functype * functype) -> Prop :=
| functype_sub__noname (ft : functype): 
  functype_sub (ft, ft)
.

Inductive globaltype_sub : (globaltype * globaltype) -> Prop :=
| globaltype_sub__noname (gt : globaltype): 
  globaltype_sub (gt, gt)
.

Inductive tabletype_sub : (tabletype * tabletype) -> Prop :=
| tabletype_sub__noname (lim_1 : limits) (lim_2 : limits) (rt : reftype): 
  (limits_sub (lim_1, lim_2)) ->
  tabletype_sub ((lim_1, rt), (lim_2, rt))
.

Inductive memtype_sub : (memtype * memtype) -> Prop :=
| memtype_sub__noname (lim_1 : limits) (lim_2 : limits): 
  (limits_sub (lim_1, lim_2)) ->
  memtype_sub (lim_1, lim_2)
.

Inductive externtype_sub : (externtype * externtype) -> Prop :=
| externtype_sub__func (ft_1 : functype) (ft_2 : functype): 
  (functype_sub (ft_1, ft_2)) ->
  externtype_sub (((*case_exp*)externtype__func ft_1), ((*case_exp*)externtype__func ft_2))
| externtype_sub__global (gt_1 : globaltype) (gt_2 : globaltype): 
  (globaltype_sub (gt_1, gt_2)) ->
  externtype_sub (((*case_exp*)externtype__global gt_1), ((*case_exp*)externtype__global gt_2))
| externtype_sub__table (tt_1 : tabletype) (tt_2 : tabletype): 
  (tabletype_sub (tt_1, tt_2)) ->
  externtype_sub (((*case_exp*)externtype__table tt_1), ((*case_exp*)externtype__table tt_2))
| externtype_sub__mem (mt_1 : memtype) (mt_2 : memtype): 
  (memtype_sub (mt_1, mt_2)) ->
  externtype_sub (((*case_exp*)externtype__mem mt_1), ((*case_exp*)externtype__mem mt_2))
.

Inductive blocktype_ok : (context * blocktype * functype) -> Prop :=
| blocktype_ok__noname (c : context) (ft : functype): 
  (functype_ok ft) ->
  blocktype_ok (c, ft, ft)
.

Inductive instr_ok : (context * instr * functype) -> Prop :=
| instr_ok__unreachable (c : context) (t_1 : (list valtype)) (t_2 : (list valtype)): 
  instr_ok (c, (*case_exp*)instr__unreachable, (t_1, t_2))
| instr_ok__nop (c : context): 
  instr_ok (c, (*case_exp*)instr__nop, ([], []))
| instr_ok__drop (c : context) (t : valtype): 
  instr_ok (c, (*case_exp*)instr__drop, ([t], []))
| instr_ok__select_expl (c : context) (t : valtype): 
  instr_ok (c, ((*case_exp*)instr__select (Some t)), ([t; t; (*case_exp*)valtype__i32], [t]))
| instr_ok__select_impl (c : context) (numtype : numtype) (t : valtype) (t' : valtype) (vectype : vectype): 
  (valtype_sub (t, t')) ->
  t' = (valtype_numtype numtype) \/ t' = (valtype_vectype vectype) ->
  instr_ok (c, ((*case_exp*)instr__select None), ([t; t; (*case_exp*)valtype__i32], [t]))
| instr_ok__block (c : context) (bt : blocktype) (instr : (list instr)) (t_1 : (list valtype)) (t_2 : (list valtype)): 
  (blocktype_ok (c, bt, (t_1, t_2))) ->
  (instrseq_ok ((List.comp (
{|
  func := [];
  global := [];
  table := [];
  mem := [];
  elem := [];
  data := [];
  local := [];
  label := [t_2];
  return := None;
|})
 c), instr, (t_1, t_2))) ->
  instr_ok (c, ((*case_exp*)instr__block (bt, instr)), (t_1, t_2))
| instr_ok__loop (c : context) (bt : blocktype) (instr : (list instr)) (t_1 : (list valtype)) (t_2 : (list valtype)): 
  (blocktype_ok (c, bt, (t_1, t_2))) ->
  (instrseq_ok ((List.comp (
{|
  func := [];
  global := [];
  table := [];
  mem := [];
  elem := [];
  data := [];
  local := [];
  label := [t_1];
  return := None;
|})
 c), instr, (t_1, t_2))) ->
  instr_ok (c, ((*case_exp*)instr__loop (bt, instr)), (t_1, t_2))
| instr_ok__if (c : context) (bt : blocktype) (instr_1 : (list instr)) (instr_2 : (list instr)) (t_1 : (list valtype)) (t_2 : (list valtype)): 
  (blocktype_ok (c, bt, (t_1, t_2))) ->
  (instrseq_ok ((List.comp (
{|
  func := [];
  global := [];
  table := [];
  mem := [];
  elem := [];
  data := [];
  local := [];
  label := [t_2];
  return := None;
|})
 c), instr_1, (t_1, t_2))) ->
  (instrseq_ok ((List.comp (
{|
  func := [];
  global := [];
  table := [];
  mem := [];
  elem := [];
  data := [];
  local := [];
  label := [t_2];
  return := None;
|})
 c), instr_2, (t_1, t_2))) ->
  instr_ok (c, ((*case_exp*)instr__if (bt, instr_1, instr_2)), ((List.app t_1 [(*case_exp*)valtype__i32]), t_2))
| instr_ok__br (c : context) (l : labelidx) (t : (list valtype)) (t_1 : (list valtype)) (t_2 : (list valtype)): 
  l < (List.length c.(label)) ->
  (list_get c.(label) l) = t ->
  instr_ok (c, ((*case_exp*)instr__br l), ((List.app t_1 t), t_2))
| instr_ok__br_if (c : context) (l : labelidx) (t : (list valtype)): 
  l < (List.length c.(label)) ->
  (list_get c.(label) l) = t ->
  instr_ok (c, ((*case_exp*)instr__br_if l), ((List.app t [(*case_exp*)valtype__i32]), t))
| instr_ok__br_table (c : context) (l : (list labelidx)) (l' : labelidx) (t : (list valtype)) (t_1 : (list valtype)) (t_2 : (list valtype)): 
  (List.Forall (fun l => l < (List.length c.(label))) l) ->
  l' < (List.length c.(label)) ->
  (List.Forall (fun l => (resulttype_sub (t, (list_get c.(label) l)))) l) ->
  (resulttype_sub (t, (list_get c.(label) l'))) ->
  instr_ok (c, ((*case_exp*)instr__br_table (l, l')), ((List.app t_1 t), t_2))
| instr_ok__return (c : context) (t : (list valtype)) (t_1 : (list valtype)) (t_2 : (list valtype)): 
  c.(return) = (Some t) ->
  instr_ok (c, (*case_exp*)instr__return, ((List.app t_1 t), t_2))
| instr_ok__call (c : context) (t_1 : (list valtype)) (t_2 : (list valtype)) (x : idx): 
  x < (List.length c.(func)) ->
  (list_get c.(func) x) = (t_1, t_2) ->
  instr_ok (c, ((*case_exp*)instr__call x), (t_1, t_2))
| instr_ok__call_indirect (c : context) (ft : functype) (lim : limits) (t_1 : (list valtype)) (t_2 : (list valtype)) (x : idx): 
  x < (List.length c.(table)) ->
  (list_get c.(table) x) = (lim, (*case_exp*)reftype__funcref) ->
  ft = (t_1, t_2) ->
  instr_ok (c, ((*case_exp*)instr__call_indirect (x, ft)), ((List.app t_1 [(*case_exp*)valtype__i32]), t_2))
| instr_ok__const (c : context) (c_nt : c_numtype) (nt : numtype): 
  instr_ok (c, ((*case_exp*)instr__const (nt, c_nt)), ([], [(valtype_numtype nt)]))
| instr_ok__unop (c : context) (nt : numtype) (unop : unop_numtype): 
  instr_ok (c, ((*case_exp*)instr__unop (nt, unop)), ([(valtype_numtype nt)], [(valtype_numtype nt)]))
| instr_ok__binop (c : context) (binop : binop_numtype) (nt : numtype): 
  instr_ok (c, ((*case_exp*)instr__binop (nt, binop)), ([(valtype_numtype nt); (valtype_numtype nt)], [(valtype_numtype nt)]))
| instr_ok__testop (c : context) (nt : numtype) (testop : testop_numtype): 
  instr_ok (c, ((*case_exp*)instr__testop (nt, testop)), ([(valtype_numtype nt)], [(*case_exp*)valtype__i32]))
| instr_ok__relop (c : context) (nt : numtype) (relop : relop_numtype): 
  instr_ok (c, ((*case_exp*)instr__relop (nt, relop)), ([(valtype_numtype nt); (valtype_numtype nt)], [(*case_exp*)valtype__i32]))
| instr_ok__extend (c : context) (n : n) (nt : numtype) (o0 : nat): 
  (size (valtype_numtype nt)) = (Some o0) ->
  n <= o0 ->
  instr_ok (c, ((*case_exp*)instr__extend (nt, n)), ([(valtype_numtype nt)], [(valtype_numtype nt)]))
| instr_ok__reinterpret (c : context) (nt_1 : numtype) (nt_2 : numtype) (o0 : nat) (o1 : nat): 
  (size (valtype_numtype nt_1)) = (Some o0) ->
  (size (valtype_numtype nt_2)) = (Some o1) ->
  nt_1 <> nt_2 ->
  o0 = o1 ->
  instr_ok (c, ((*case_exp*)instr__cvtop (nt_1, (*case_exp*)cvtop__reinterpret, nt_2, None)), ([(valtype_numtype nt_2)], [(valtype_numtype nt_1)]))
| instr_ok__convert_i (c : context) (in_1 : In) (in_2 : In) (sx : (option sx)) (o0 : nat) (o1 : nat): 
  (size (valtype_in in_1)) = (Some o0) ->
  (size (valtype_in in_2)) = (Some o1) ->
  in_1 <> in_2 ->
  sx = None = o0 > o1 ->
  instr_ok (c, ((*case_exp*)instr__cvtop ((numtype_in in_1), (*case_exp*)cvtop__convert, (numtype_in in_2), sx)), ([(valtype_in in_2)], [(valtype_in in_1)]))
| instr_ok__convert_f (c : context) (fn_1 : fn) (fn_2 : fn): 
  fn_1 <> fn_2 ->
  instr_ok (c, ((*case_exp*)instr__cvtop ((numtype_fn fn_1), (*case_exp*)cvtop__convert, (numtype_fn fn_2), None)), ([(valtype_fn fn_2)], [(valtype_fn fn_1)]))
| instr_ok__ref_null (c : context) (rt : reftype): 
  instr_ok (c, ((*case_exp*)instr__ref_null rt), ([], [(valtype_reftype rt)]))
| instr_ok__ref_func (c : context) (ft : functype) (x : idx): 
  x < (List.length c.(func)) ->
  (list_get c.(func) x) = ft ->
  instr_ok (c, ((*case_exp*)instr__ref_func x), ([], [(*case_exp*)valtype__funcref]))
| instr_ok__ref_is_null (c : context) (rt : reftype): 
  instr_ok (c, (*case_exp*)instr__ref_is_null, ([(valtype_reftype rt)], [(*case_exp*)valtype__i32]))
| instr_ok__local_get (c : context) (t : valtype) (x : idx): 
  x < (List.length c.(local)) ->
  (list_get c.(local) x) = t ->
  instr_ok (c, ((*case_exp*)instr__local_get x), ([], [t]))
| instr_ok__local_set (c : context) (t : valtype) (x : idx): 
  x < (List.length c.(local)) ->
  (list_get c.(local) x) = t ->
  instr_ok (c, ((*case_exp*)instr__local_set x), ([t], []))
| instr_ok__local_tee (c : context) (t : valtype) (x : idx): 
  x < (List.length c.(local)) ->
  (list_get c.(local) x) = t ->
  instr_ok (c, ((*case_exp*)instr__local_tee x), ([t], [t]))
| instr_ok__global_get (c : context) (t : valtype) (x : idx) (w0 : (option unit)): 
  x < (List.length c.(global)) ->
  (list_get c.(global) x) = (w0, t) ->
  instr_ok (c, ((*case_exp*)instr__global_get x), ([], [t]))
| instr_ok__global_set (c : context) (t : valtype) (x : idx): 
  x < (List.length c.(global)) ->
  (list_get c.(global) x) = ((Some (* Empty Tuple *) tt), t) ->
  instr_ok (c, ((*case_exp*)instr__global_set x), ([t], []))
| instr_ok__table_get (c : context) (lim : limits) (rt : reftype) (x : idx): 
  x < (List.length c.(table)) ->
  (list_get c.(table) x) = (lim, rt) ->
  instr_ok (c, ((*case_exp*)instr__table_get x), ([(*case_exp*)valtype__i32], [(valtype_reftype rt)]))
| instr_ok__table_set (c : context) (lim : limits) (rt : reftype) (x : idx): 
  x < (List.length c.(table)) ->
  (list_get c.(table) x) = (lim, rt) ->
  instr_ok (c, ((*case_exp*)instr__table_set x), ([(*case_exp*)valtype__i32; (valtype_reftype rt)], []))
| instr_ok__table_size (c : context) (tt : tabletype) (x : idx): 
  x < (List.length c.(table)) ->
  (list_get c.(table) x) = tt ->
  instr_ok (c, ((*case_exp*)instr__table_size x), ([], [(*case_exp*)valtype__i32]))
| instr_ok__table_grow (c : context) (lim : limits) (rt : reftype) (x : idx): 
  x < (List.length c.(table)) ->
  (list_get c.(table) x) = (lim, rt) ->
  instr_ok (c, ((*case_exp*)instr__table_grow x), ([(valtype_reftype rt); (*case_exp*)valtype__i32], [(*case_exp*)valtype__i32]))
| instr_ok__table_fill (c : context) (lim : limits) (rt : reftype) (x : idx): 
  x < (List.length c.(table)) ->
  (list_get c.(table) x) = (lim, rt) ->
  instr_ok (c, ((*case_exp*)instr__table_fill x), ([(*case_exp*)valtype__i32; (valtype_reftype rt); (*case_exp*)valtype__i32], []))
| instr_ok__table_copy (c : context) (lim_1 : limits) (lim_2 : limits) (rt : reftype) (x_1 : idx) (x_2 : idx): 
  x_1 < (List.length c.(table)) ->
  x_2 < (List.length c.(table)) ->
  (list_get c.(table) x_1) = (lim_1, rt) ->
  (list_get c.(table) x_2) = (lim_2, rt) ->
  instr_ok (c, ((*case_exp*)instr__table_copy (x_1, x_2)), ([(*case_exp*)valtype__i32; (*case_exp*)valtype__i32; (*case_exp*)valtype__i32], []))
| instr_ok__table_init (c : context) (lim : limits) (rt : reftype) (x_1 : idx) (x_2 : idx): 
  x_1 < (List.length c.(table)) ->
  x_2 < (List.length c.(elem)) ->
  (list_get c.(table) x_1) = (lim, rt) ->
  (list_get c.(elem) x_2) = rt ->
  instr_ok (c, ((*case_exp*)instr__table_init (x_1, x_2)), ([(*case_exp*)valtype__i32; (*case_exp*)valtype__i32; (*case_exp*)valtype__i32], []))
| instr_ok__elem_drop (c : context) (rt : reftype) (x : idx): 
  x < (List.length c.(elem)) ->
  (list_get c.(elem) x) = rt ->
  instr_ok (c, ((*case_exp*)instr__elem_drop x), ([], []))
| instr_ok__memory_size (c : context) (mt : memtype): 
  0 < (List.length c.(mem)) ->
  (list_get c.(mem) 0) = mt ->
  instr_ok (c, (*case_exp*)instr__memory_size, ([], [(*case_exp*)valtype__i32]))
| instr_ok__memory_grow (c : context) (mt : memtype): 
  0 < (List.length c.(mem)) ->
  (list_get c.(mem) 0) = mt ->
  instr_ok (c, (*case_exp*)instr__memory_grow, ([(*case_exp*)valtype__i32], [(*case_exp*)valtype__i32]))
| instr_ok__memory_fill (c : context) (mt : memtype): 
  0 < (List.length c.(mem)) ->
  (list_get c.(mem) 0) = mt ->
  instr_ok (c, (*case_exp*)instr__memory_fill, ([(*case_exp*)valtype__i32; (*case_exp*)valtype__i32; (*case_exp*)valtype__i32], []))
| instr_ok__memory_copy (c : context) (mt : memtype): 
  0 < (List.length c.(mem)) ->
  (list_get c.(mem) 0) = mt ->
  instr_ok (c, (*case_exp*)instr__memory_copy, ([(*case_exp*)valtype__i32; (*case_exp*)valtype__i32; (*case_exp*)valtype__i32], []))
| instr_ok__memory_init (c : context) (mt : memtype) (x : idx): 
  0 < (List.length c.(mem)) ->
  x < (List.length c.(data)) ->
  (list_get c.(mem) 0) = mt ->
  (list_get c.(data) x) = (* Empty Tuple *) tt ->
  instr_ok (c, ((*case_exp*)instr__memory_init x), ([(*case_exp*)valtype__i32; (*case_exp*)valtype__i32; (*case_exp*)valtype__i32], []))
| instr_ok__data_drop (c : context) (x : idx): 
  x < (List.length c.(data)) ->
  (list_get c.(data) x) = (* Empty Tuple *) tt ->
  instr_ok (c, ((*case_exp*)instr__data_drop x), ([], []))
| instr_ok__load (c : context) (In : In) (mt : memtype) (n : (option n)) (n_a : n) (n_o : n) (nt : numtype) (sx : (option sx)) (o0 : nat) (o1 : (option nat)): 
  0 < (List.length c.(mem)) ->
  n = None = o1 = None ->
  n = None = sx = None ->
  (size (valtype_numtype nt)) = (Some o0) ->
  (option.map (fun o1 => (size (valtype_numtype nt)) = (Some o1)) o1) ->
  (list_get c.(mem) 0) = mt ->
  Nat.pow 2 n_a <= o0 / 8 ->
  (option_zip (fun n o1 => Nat.pow 2 n_a <= n / 8 /\ n / 8 < o1 / 8) n o1) ->
  n = None \/ nt = (numtype_in In) ->
  instr_ok (c, ((*case_exp*)instr__load (nt, (option_zip (fun n sx => (n, sx)) n sx), n_a, n_o)), ([(*case_exp*)valtype__i32], [(valtype_numtype nt)]))
| instr_ok__store (c : context) (In : In) (mt : memtype) (n : (option n)) (n_a : n) (n_o : n) (nt : numtype) (o0 : nat) (o1 : (option nat)): 
  0 < (List.length c.(mem)) ->
  n = None = o1 = None ->
  (size (valtype_numtype nt)) = (Some o0) ->
  (option.map (fun o1 => (size (valtype_numtype nt)) = (Some o1)) o1) ->
  (list_get c.(mem) 0) = mt ->
  Nat.pow 2 n_a <= o0 / 8 ->
  (option_zip (fun n o1 => Nat.pow 2 n_a <= n / 8 /\ n / 8 < o1 / 8) n o1) ->
  n = None \/ nt = (numtype_in In) ->
  instr_ok (c, ((*case_exp*)instr__store (nt, n, n_a, n_o)), ([(*case_exp*)valtype__i32; (valtype_numtype nt)], []))

with
Inductive instrseq_ok : (context * (list instr) * functype) -> Prop :=
| instrseq_ok__empty (c : context): 
  instrseq_ok (c, [], ([], []))
| instrseq_ok__seq (c : context) (instr_1 : instr) (instr_2 : instr) (t_1 : (list valtype)) (t_2 : (list valtype)) (t_3 : (list valtype)): 
  (instr_ok (c, instr_1, (t_1, t_2))) ->
  (instrseq_ok (c, [instr_2], (t_2, t_3))) ->
  instrseq_ok (c, (List.app [instr_1] [instr_2]), (t_1, t_3))
| instrseq_ok__weak (c : context) (instr : (list instr)) (t'_1 : (list valtype)) (t'_2 : (list valtype)) (t_1 : (list valtype)) (t_2 : (list valtype)): 
  (instrseq_ok (c, instr, (t_1, t_2))) ->
  (resulttype_sub (t'_1, t_1)) ->
  (resulttype_sub (t_2, t'_2)) ->
  instrseq_ok (c, instr, (t'_1, t'_2))
| instrseq_ok__frame (c : context) (instr : (list instr)) (t : (list valtype)) (t_1 : (list valtype)) (t_2 : (list valtype)): 
  (instrseq_ok (c, instr, (t_1, t_2))) ->
  instrseq_ok (c, instr, ((List.app t t_1), (List.app t t_2)))
.

Inductive expr_ok : (context * expr * resulttype) -> Prop :=
| expr_ok__noname (c : context) (instr : (list instr)) (t : (list valtype)): 
  (instrseq_ok (c, instr, ([], t))) ->
  expr_ok (c, instr, t)
.

Inductive instr_const : (context * instr) -> Prop :=
| instr_const__const (c : context) (c : c_numtype) (nt : numtype): 
  instr_const (c, ((*case_exp*)instr__const (nt, c)))
| instr_const__ref_null (c : context) (rt : reftype): 
  instr_const (c, ((*case_exp*)instr__ref_null rt))
| instr_const__ref_func (c : context) (x : idx): 
  instr_const (c, ((*case_exp*)instr__ref_func x))
| instr_const__global_get (c : context) (t : valtype) (x : idx): 
  x < (List.length c.(global)) ->
  (list_get c.(global) x) = (None, t) ->
  instr_const (c, ((*case_exp*)instr__global_get x))
.

Inductive expr_const : (context * expr) -> Prop :=
| expr_const__noname (c : context) (instr : (list instr)): 
  (List.Forall (fun instr => (instr_const (c, instr))) instr) ->
  expr_const (c, instr)
.

Inductive expr_ok_const : (context * expr * valtype) -> Prop :=
| expr_ok_const__noname (c : context) (expr : expr) (t : valtype): 
  (expr_ok (c, expr, [t])) ->
  (expr_const (c, expr)) ->
  expr_ok_const (c, expr, t)
.

Inductive func_ok : (context * func * functype) -> Prop :=
| func_ok__noname (c : context) (expr : expr) (ft : functype) (t : (list valtype)) (t_1 : (list valtype)) (t_2 : (list valtype)): 
  ft = (t_1, t_2) ->
  (functype_ok ft) ->
  (expr_ok ((List.comp (
{|
  func := [];
  global := [];
  table := [];
  mem := [];
  elem := [];
  data := [];
  local := [];
  label := [];
  return := (Some t_2);
|})
 (List.comp (
{|
  func := [];
  global := [];
  table := [];
  mem := [];
  elem := [];
  data := [];
  local := [];
  label := [t_2];
  return := None;
|})
 (List.comp (
{|
  func := [];
  global := [];
  table := [];
  mem := [];
  elem := [];
  data := [];
  local := (List.app t_1 t);
  label := [];
  return := None;
|})
 c))), expr, t_2)) ->
  func_ok (c, (ft, t, expr), ft)
.

Inductive global_ok : (context * global * globaltype) -> Prop :=
| global_ok__noname (c : context) (expr : expr) (gt : globaltype) (t : valtype) (w0 : (option unit)): 
  (globaltype_ok gt) ->
  gt = (w0, t) ->
  (expr_ok_const (c, expr, t)) ->
  global_ok (c, (gt, expr), gt)
.

Inductive table_ok : (context * table * tabletype) -> Prop :=
| table_ok__noname (c : context) (tt : tabletype): 
  (tabletype_ok tt) ->
  table_ok (c, tt, tt)
.

Inductive mem_ok : (context * mem * memtype) -> Prop :=
| mem_ok__noname (c : context) (mt : memtype): 
  (memtype_ok mt) ->
  mem_ok (c, mt, mt)
.

Inductive elemmode_ok : (context * elemmode * reftype) -> Prop :=
| elemmode_ok__active (c : context) (expr : expr) (lim : limits) (rt : reftype) (x : idx): 
  x < (List.length c.(table)) ->
  (list_get c.(table) x) = (lim, rt) ->
  (* FIXME: unsuppurted exp:  *) ->
  elemmode_ok (c, ((*case_exp*)elemmode__table (x, expr)), rt)
| elemmode_ok__declare (c : context) (rt : reftype): 
  elemmode_ok (c, (*case_exp*)elemmode__declare, rt)
.

Inductive elem_ok : (context * elem * reftype) -> Prop :=
| elem_ok__noname (c : context) (elemmode : (option elemmode)) (expr : (list expr)) (rt : reftype): 
  (List.Forall (fun expr => (expr_ok (c, expr, [(valtype_reftype rt)]))) expr) ->
  (option.map (fun elemmode => (elemmode_ok (c, elemmode, rt))) elemmode) ->
  elem_ok (c, (rt, expr, elemmode), rt)
.

Inductive datamode_ok : (context * datamode) -> Prop :=
| datamode_ok__noname (c : context) (expr : expr) (mt : memtype): 
  0 < (List.length c.(mem)) ->
  (list_get c.(mem) 0) = mt ->
  (* FIXME: unsuppurted exp:  *) ->
  datamode_ok (c, ((*case_exp*)datamode__memory (0, expr)))
.

Inductive data_ok : (context * data) -> Prop :=
| data_ok__noname (c : context) (b : (list byte)) (datamode : (option datamode)): 
  (option.map (fun datamode => (datamode_ok (c, datamode))) datamode) ->
  data_ok (c, (b, datamode))
.

Inductive start_ok : (context * start) -> Prop :=
| start_ok__noname (c : context) (x : idx): 
  x < (List.length c.(func)) ->
  (list_get c.(func) x) = ([], []) ->
  start_ok (c, x)
.

Inductive import_ok : (context * import * externtype) -> Prop :=
| import_ok__noname (c : context) (name_1 : name) (name_2 : name) (xt : externtype): 
  (externtype_ok xt) ->
  import_ok (c, (name_1, name_2, xt), xt)
.

Inductive externuse_ok : (context * externuse * externtype) -> Prop :=
| externuse_ok__func (c : context) (ft : functype) (x : idx): 
  x < (List.length c.(func)) ->
  (list_get c.(func) x) = ft ->
  externuse_ok (c, ((*case_exp*)externuse__func x), ((*case_exp*)externtype__func ft))
| externuse_ok__global (c : context) (gt : globaltype) (x : idx): 
  x < (List.length c.(global)) ->
  (list_get c.(global) x) = gt ->
  externuse_ok (c, ((*case_exp*)externuse__global x), ((*case_exp*)externtype__global gt))
| externuse_ok__table (c : context) (tt : tabletype) (x : idx): 
  x < (List.length c.(table)) ->
  (list_get c.(table) x) = tt ->
  externuse_ok (c, ((*case_exp*)externuse__table x), ((*case_exp*)externtype__table tt))
| externuse_ok__mem (c : context) (mt : memtype) (x : idx): 
  x < (List.length c.(mem)) ->
  (list_get c.(mem) x) = mt ->
  externuse_ok (c, ((*case_exp*)externuse__mem x), ((*case_exp*)externtype__mem mt))
.

Inductive export_ok : (context * export * externtype) -> Prop :=
| export_ok__noname (c : context) (externuse : externuse) (name : name) (xt : externtype): 
  (externuse_ok (c, externuse, xt)) ->
  export_ok (c, (name, externuse), xt)
.

Inductive module_ok : module -> Prop :=
| module_ok__noname (c : context) (data : (list data)) (elem : (list elem)) (export : (list export)) (ft : (list functype)) (func : (list func)) (global : (list global)) (gt : (list globaltype)) (import : (list import)) (mem : (list mem)) (mt : (list memtype)) (n : n) (rt : (list reftype)) (start : (option start)) (table : (list table)) (tt : (list tabletype)): 
  (List.length ft) = (List.length func) ->
  (List.length global) = (List.length gt) ->
  (List.length table) = (List.length tt) ->
  (List.length mem) = (List.length mt) ->
  (List.length elem) = (List.length rt) ->
  c = (
{|
  func := ft;
  global := gt;
  table := tt;
  mem := mt;
  elem := rt;
  data := [(* Empty Tuple *) tt];
  local := [];
  label := [];
  return := None;
|})
 ->
  (List.Forall2 (fun ft func => (func_ok (c, func, ft))) ft func) ->
  (List.Forall2 (fun global gt => (global_ok (c, global, gt))) global gt) ->
  (List.Forall2 (fun table tt => (table_ok (c, table, tt))) table tt) ->
  (List.Forall2 (fun mem mt => (mem_ok (c, mem, mt))) mem mt) ->
  (List.Forall2 (fun elem rt => (elem_ok (c, elem, rt))) elem rt) ->
  (List.Forall (fun data => (data_ok (c, data))) data) ->
  (option.map (fun start => (start_ok (c, start))) start) ->
  (List.length mem) <= 1 ->
  module_ok (import, func, global, table, mem, elem, data, start, export)
.

Definition addr := nat.

Definition funcaddr := addr.

Definition globaladdr := addr.

Definition tableaddr := addr.

Definition memaddr := addr.

Definition elemaddr := addr.

Definition dataaddr := addr.

Definition labeladdr := addr.

Definition hostaddr := addr.

Inductive num : Type :=
| num__const : numtype -> c_numtype -> num
.

Inductive ref : Type :=
| ref__ref_null : reftype -> ref
| ref__ref_func_addr : funcaddr -> ref
| ref__ref_host_addr : hostaddr -> ref
.

Inductive val : Type :=
| val__const : numtype -> c_numtype -> val
| val__ref_null : reftype -> val
| val__ref_func_addr : funcaddr -> val
| val__ref_host_addr : hostaddr -> val
.

Inductive result : Type :=
| result___vals : (list val) -> result
| result__trap : result
.

Inductive externval : Type :=
| externval__func : funcaddr -> externval
| externval__global : globaladdr -> externval
| externval__table : tableaddr -> externval
| externval__mem : memaddr -> externval
.

(* Funcdef *)
Definition default_ (arg : valtype) : (option val) := 
  match arg with
  | (*case_pat*)valtype__i32 => (Some ((*case_exp*)val__const ((*case_exp*)numtype__i32, 0)))
  | (*case_pat*)valtype__i64 => (Some ((*case_exp*)val__const ((*case_exp*)numtype__i64, 0)))
  | (*case_pat*)valtype__f32 => (Some ((*case_exp*)val__const ((*case_exp*)numtype__f32, 0)))
  | (*case_pat*)valtype__f64 => (Some ((*case_exp*)val__const ((*case_exp*)numtype__f64, 0)))
  | (*case_pat*)valtype__funcref => (Some ((*case_exp*)val__ref_null (*case_exp*)reftype__funcref))
  | (*case_pat*)valtype__externref => (Some ((*case_exp*)val__ref_null (*case_exp*)reftype__externref))
  | (*var_pat*)x => None
end.

Record exportinst : Type :=
{
  exportinst__name : name;
  exportinst__value : externval
}.

Record moduleinst : Type :=
{
  moduleinst__func : (list funcaddr);
  moduleinst__global : (list globaladdr);
  moduleinst__table : (list tableaddr);
  moduleinst__mem : (list memaddr);
  moduleinst__elem : (list elemaddr);
  moduleinst__data : (list dataaddr);
  moduleinst__export : (list exportinst)
}.

Record funcinst : Type :=
{
  funcinst__module : moduleinst;
  funcinst__code : func
}.

Record globalinst : Type :=
{
  globalinst__type : globaltype;
  globalinst__value : val
}.

Record tableinst : Type :=
{
  tableinst__type : tabletype;
  tableinst__elem : (list ref)
}.

Record meminst : Type :=
{
  meminst__type : memtype;
  meminst__data : (list byte)
}.

Record eleminst : Type :=
{
  eleminst__type : elemtype;
  eleminst__elem : (list ref)
}.

Record datainst : Type :=
{
  datainst__data : (list byte)
}.

Record store : Type :=
{
  store__func : (list funcinst);
  store__global : (list globalinst);
  store__table : (list tableinst);
  store__mem : (list meminst);
  store__elem : (list eleminst);
  store__data : (list datainst)
}.

Record frame : Type :=
{
  frame__local : (list val);
  frame__module : moduleinst
}.

Definition state := (store * frame).

Inductive admininstr : Type :=
| admininstr__unreachable : admininstr
| admininstr__nop : admininstr
| admininstr__drop : admininstr
| admininstr__select : (option valtype) -> admininstr
| admininstr__block : blocktype -> (list instr) -> admininstr
| admininstr__loop : blocktype -> (list instr) -> admininstr
| admininstr__if : blocktype -> (list instr) -> (list instr) -> admininstr
| admininstr__br : labelidx -> admininstr
| admininstr__br_if : labelidx -> admininstr
| admininstr__br_table : (list labelidx) -> labelidx -> admininstr
| admininstr__call : funcidx -> admininstr
| admininstr__call_indirect : tableidx -> functype -> admininstr
| admininstr__return : admininstr
| admininstr__const : numtype -> c_numtype -> admininstr
| admininstr__unop : numtype -> unop_numtype -> admininstr
| admininstr__binop : numtype -> binop_numtype -> admininstr
| admininstr__testop : numtype -> testop_numtype -> admininstr
| admininstr__relop : numtype -> relop_numtype -> admininstr
| admininstr__extend : numtype -> n -> admininstr
| admininstr__cvtop : numtype -> cvtop -> numtype -> (option sx) -> admininstr
| admininstr__ref_null : reftype -> admininstr
| admininstr__ref_func : funcidx -> admininstr
| admininstr__ref_is_null : admininstr
| admininstr__local_get : localidx -> admininstr
| admininstr__local_set : localidx -> admininstr
| admininstr__local_tee : localidx -> admininstr
| admininstr__global_get : globalidx -> admininstr
| admininstr__global_set : globalidx -> admininstr
| admininstr__table_get : tableidx -> admininstr
| admininstr__table_set : tableidx -> admininstr
| admininstr__table_size : tableidx -> admininstr
| admininstr__table_grow : tableidx -> admininstr
| admininstr__table_fill : tableidx -> admininstr
| admininstr__table_copy : tableidx -> tableidx -> admininstr
| admininstr__table_init : tableidx -> elemidx -> admininstr
| admininstr__elem_drop : elemidx -> admininstr
| admininstr__memory_size : admininstr
| admininstr__memory_grow : admininstr
| admininstr__memory_fill : admininstr
| admininstr__memory_copy : admininstr
| admininstr__memory_init : dataidx -> admininstr
| admininstr__data_drop : dataidx -> admininstr
| admininstr__load : numtype -> (option (n * sx)) -> u32 -> u32 -> admininstr
| admininstr__store : numtype -> (option n) -> u32 -> u32 -> admininstr
| admininstr__ref_func_addr : funcaddr -> admininstr
| admininstr__ref_host_addr : hostaddr -> admininstr
| admininstr__call_addr : funcaddr -> admininstr
| admininstr__label_ : n -> (list instr) -> (list admininstr) -> admininstr
| admininstr__frame_ : n -> frame -> (list admininstr) -> admininstr
| admininstr__trap : admininstr
.

(* Funcdef *)
Definition admininstr_instr (arg : instr) : admininstr := 
  match arg with
  | (*case_pat*)instr__unreachable => (*case_exp*)admininstr__unreachable
  | (*case_pat*)instr__nop => (*case_exp*)admininstr__nop
  | (*case_pat*)instr__drop => (*case_exp*)admininstr__drop
  | (*case_pat*)instr__select (*var_pat*)x => ((*case_exp*)admininstr__select x)
  | (*case_pat*)instr__block ((*var_pat*)x0, (*var_pat*)x1) => ((*case_exp*)admininstr__block (x0, x1))
  | (*case_pat*)instr__loop ((*var_pat*)x0, (*var_pat*)x1) => ((*case_exp*)admininstr__loop (x0, x1))
  | (*case_pat*)instr__if ((*var_pat*)x0, (*var_pat*)x1, (*var_pat*)x2) => ((*case_exp*)admininstr__if (x0, x1, x2))
  | (*case_pat*)instr__br (*var_pat*)x => ((*case_exp*)admininstr__br x)
  | (*case_pat*)instr__br_if (*var_pat*)x => ((*case_exp*)admininstr__br_if x)
  | (*case_pat*)instr__br_table ((*var_pat*)x0, (*var_pat*)x1) => ((*case_exp*)admininstr__br_table (x0, x1))
  | (*case_pat*)instr__call (*var_pat*)x => ((*case_exp*)admininstr__call x)
  | (*case_pat*)instr__call_indirect ((*var_pat*)x0, (*var_pat*)x1) => ((*case_exp*)admininstr__call_indirect (x0, x1))
  | (*case_pat*)instr__return => (*case_exp*)admininstr__return
  | (*case_pat*)instr__const ((*var_pat*)x0, (*var_pat*)x1) => ((*case_exp*)admininstr__const (x0, x1))
  | (*case_pat*)instr__unop ((*var_pat*)x0, (*var_pat*)x1) => ((*case_exp*)admininstr__unop (x0, x1))
  | (*case_pat*)instr__binop ((*var_pat*)x0, (*var_pat*)x1) => ((*case_exp*)admininstr__binop (x0, x1))
  | (*case_pat*)instr__testop ((*var_pat*)x0, (*var_pat*)x1) => ((*case_exp*)admininstr__testop (x0, x1))
  | (*case_pat*)instr__relop ((*var_pat*)x0, (*var_pat*)x1) => ((*case_exp*)admininstr__relop (x0, x1))
  | (*case_pat*)instr__extend ((*var_pat*)x0, (*var_pat*)x1) => ((*case_exp*)admininstr__extend (x0, x1))
  | (*case_pat*)instr__cvtop ((*var_pat*)x0, (*var_pat*)x1, (*var_pat*)x2, (*var_pat*)x3) => ((*case_exp*)admininstr__cvtop (x0, x1, x2, x3))
  | (*case_pat*)instr__ref_null (*var_pat*)x => ((*case_exp*)admininstr__ref_null x)
  | (*case_pat*)instr__ref_func (*var_pat*)x => ((*case_exp*)admininstr__ref_func x)
  | (*case_pat*)instr__ref_is_null => (*case_exp*)admininstr__ref_is_null
  | (*case_pat*)instr__local_get (*var_pat*)x => ((*case_exp*)admininstr__local_get x)
  | (*case_pat*)instr__local_set (*var_pat*)x => ((*case_exp*)admininstr__local_set x)
  | (*case_pat*)instr__local_tee (*var_pat*)x => ((*case_exp*)admininstr__local_tee x)
  | (*case_pat*)instr__global_get (*var_pat*)x => ((*case_exp*)admininstr__global_get x)
  | (*case_pat*)instr__global_set (*var_pat*)x => ((*case_exp*)admininstr__global_set x)
  | (*case_pat*)instr__table_get (*var_pat*)x => ((*case_exp*)admininstr__table_get x)
  | (*case_pat*)instr__table_set (*var_pat*)x => ((*case_exp*)admininstr__table_set x)
  | (*case_pat*)instr__table_size (*var_pat*)x => ((*case_exp*)admininstr__table_size x)
  | (*case_pat*)instr__table_grow (*var_pat*)x => ((*case_exp*)admininstr__table_grow x)
  | (*case_pat*)instr__table_fill (*var_pat*)x => ((*case_exp*)admininstr__table_fill x)
  | (*case_pat*)instr__table_copy ((*var_pat*)x0, (*var_pat*)x1) => ((*case_exp*)admininstr__table_copy (x0, x1))
  | (*case_pat*)instr__table_init ((*var_pat*)x0, (*var_pat*)x1) => ((*case_exp*)admininstr__table_init (x0, x1))
  | (*case_pat*)instr__elem_drop (*var_pat*)x => ((*case_exp*)admininstr__elem_drop x)
  | (*case_pat*)instr__memory_size => (*case_exp*)admininstr__memory_size
  | (*case_pat*)instr__memory_grow => (*case_exp*)admininstr__memory_grow
  | (*case_pat*)instr__memory_fill => (*case_exp*)admininstr__memory_fill
  | (*case_pat*)instr__memory_copy => (*case_exp*)admininstr__memory_copy
  | (*case_pat*)instr__memory_init (*var_pat*)x => ((*case_exp*)admininstr__memory_init x)
  | (*case_pat*)instr__data_drop (*var_pat*)x => ((*case_exp*)admininstr__data_drop x)
  | (*case_pat*)instr__load ((*var_pat*)x0, (*var_pat*)x1, (*var_pat*)x2, (*var_pat*)x3) => ((*case_exp*)admininstr__load (x0, x1, x2, x3))
  | (*case_pat*)instr__store ((*var_pat*)x0, (*var_pat*)x1, (*var_pat*)x2, (*var_pat*)x3) => ((*case_exp*)admininstr__store (x0, x1, x2, x3))
end.

(* Funcdef *)
Definition admininstr_ref (arg : ref) : admininstr := 
  match arg with
  | (*case_pat*)ref__ref_null (*var_pat*)x => ((*case_exp*)admininstr__ref_null x)
  | (*case_pat*)ref__ref_func_addr (*var_pat*)x => ((*case_exp*)admininstr__ref_func_addr x)
  | (*case_pat*)ref__ref_host_addr (*var_pat*)x => ((*case_exp*)admininstr__ref_host_addr x)
end.

(* Funcdef *)
Definition admininstr_val (arg : val) : admininstr := 
  match arg with
  | (*case_pat*)val__const ((*var_pat*)x0, (*var_pat*)x1) => ((*case_exp*)admininstr__const (x0, x1))
  | (*case_pat*)val__ref_null (*var_pat*)x => ((*case_exp*)admininstr__ref_null x)
  | (*case_pat*)val__ref_func_addr (*var_pat*)x => ((*case_exp*)admininstr__ref_func_addr x)
  | (*case_pat*)val__ref_host_addr (*var_pat*)x => ((*case_exp*)admininstr__ref_host_addr x)
end.

Definition config := (state * (list admininstr)).

(* Funcdef *)
Definition funcaddr (arg : state) : (list funcaddr) := 
  match arg with
  | ((*var_pat*)s, (*var_pat*)f) => f.(module).(func)
end.

(* Funcdef *)
Definition funcinst (arg : state) : (list funcinst) := 
  match arg with
  | ((*var_pat*)s, (*var_pat*)f) => s.(func)
end.

(* Funcdef *)
Definition globalinst (arg : state) : (list globalinst) := 
  match arg with
  | ((*var_pat*)s, (*var_pat*)f) => s.(global)
end.

(* Funcdef *)
Definition tableinst (arg : state) : (list tableinst) := 
  match arg with
  | ((*var_pat*)s, (*var_pat*)f) => s.(table)
end.

(* Funcdef *)
Definition meminst (arg : state) : (list meminst) := 
  match arg with
  | ((*var_pat*)s, (*var_pat*)f) => s.(mem)
end.

(* Funcdef *)
Definition eleminst (arg : state) : (list eleminst) := 
  match arg with
  | ((*var_pat*)s, (*var_pat*)f) => s.(elem)
end.

(* Funcdef *)
Definition datainst (arg : state) : (list datainst) := 
  match arg with
  | ((*var_pat*)s, (*var_pat*)f) => s.(data)
end.

(* Funcdef *)
Definition func (arg : (state * funcidx)) : funcinst := 
  match arg with
  | (((*var_pat*)s, (*var_pat*)f), (*var_pat*)x) => (list_get s.(func) (list_get f.(module).(func) x))
end.

(* Funcdef *)
Definition global (arg : (state * globalidx)) : globalinst := 
  match arg with
  | (((*var_pat*)s, (*var_pat*)f), (*var_pat*)x) => (list_get s.(global) (list_get f.(module).(global) x))
end.

(* Funcdef *)
Definition table (arg : (state * tableidx)) : tableinst := 
  match arg with
  | (((*var_pat*)s, (*var_pat*)f), (*var_pat*)x) => (list_get s.(table) (list_get f.(module).(table) x))
end.

(* Funcdef *)
Definition mem (arg : (state * memidx)) : meminst := 
  match arg with
  | (((*var_pat*)s, (*var_pat*)f), (*var_pat*)x) => (list_get s.(mem) (list_get f.(module).(mem) x))
end.

(* Funcdef *)
Definition elem (arg : (state * tableidx)) : eleminst := 
  match arg with
  | (((*var_pat*)s, (*var_pat*)f), (*var_pat*)x) => (list_get s.(elem) (list_get f.(module).(elem) x))
end.

(* Funcdef *)
Definition data (arg : (state * dataidx)) : datainst := 
  match arg with
  | (((*var_pat*)s, (*var_pat*)f), (*var_pat*)x) => (list_get s.(data) (list_get f.(module).(data) x))
end.

(* Funcdef *)
Definition local (arg : (state * localidx)) : val := 
  match arg with
  | (((*var_pat*)s, (*var_pat*)f), (*var_pat*)x) => (list_get f.(local) x)
end.

(* Funcdef *)
Definition with_local (arg : (state * localidx * val)) : state := 
  match arg with
  | (((*var_pat*)s, (*var_pat*)f), (*var_pat*)x, (*var_pat*)v) => (s, f(* TODO: record update: with local := (list_set f.(local) x v)*))
end.

(* Funcdef *)
Definition with_global (arg : (state * globalidx * val)) : state := 
  match arg with
  | (((*var_pat*)s, (*var_pat*)f), (*var_pat*)x, (*var_pat*)v) => (s(* TODO: record update: with global := (list_set s.(global) (list_get f.(module).(global) x) (list_get s.(global) (list_get f.(module).(global) x))(* TODO: record update: with value := v*))*), f)
end.

(* Funcdef *)
Definition with_table (arg : (state * tableidx * nat * ref)) : state := 
  match arg with
  | (((*var_pat*)s, (*var_pat*)f), (*var_pat*)x, (*var_pat*)i, (*var_pat*)r) => (s(* TODO: record update: with table := (list_set s.(table) (list_get f.(module).(table) x) (list_get s.(table) (list_get f.(module).(table) x))(* TODO: record update: with elem := (list_set (list_get s.(table) (list_get f.(module).(table) x)).(elem) i r)*))*), f)
end.

(* Funcdef *)
Definition with_tableinst (arg : (state * tableidx * tableinst)) : state := 
  match arg with
  | (((*var_pat*)s, (*var_pat*)f), (*var_pat*)x, (*var_pat*)ti) => (s(* TODO: record update: with table := (list_set s.(table) (list_get f.(module).(table) x) ti)*), f)
end.

(* Funcdef *)
Definition with_mem (arg : (state * memidx * nat * nat * (list byte))) : state := 
  match arg with
  | (((*var_pat*)s, (*var_pat*)f), (*var_pat*)x, (*var_pat*)i, (*var_pat*)j, (* test_iter_pat *)b) => ((* FIXME: unsuppurted exp: SliceP *), f)
end.

(* Funcdef *)
Definition with_meminst (arg : (state * memidx * meminst)) : state := 
  match arg with
  | (((*var_pat*)s, (*var_pat*)f), (*var_pat*)x, (*var_pat*)mi) => (s(* TODO: record update: with mem := (list_set s.(mem) (list_get f.(module).(mem) x) mi)*), f)
end.

(* Funcdef *)
Definition with_elem (arg : (state * elemidx * (list ref))) : state := 
  match arg with
  | (((*var_pat*)s, (*var_pat*)f), (*var_pat*)x, (* test_iter_pat *)r) => (s(* TODO: record update: with elem := (list_set s.(elem) (list_get f.(module).(elem) x) (list_get s.(elem) (list_get f.(module).(elem) x))(* TODO: record update: with elem := r*))*), f)
end.

(* Funcdef *)
Definition with_data (arg : (state * dataidx * (list byte))) : state := 
  match arg with
  | (((*var_pat*)s, (*var_pat*)f), (*var_pat*)x, (* test_iter_pat *)b) => (s(* TODO: record update: with data := (list_set s.(data) (list_get f.(module).(data) x) (list_get s.(data) (list_get f.(module).(data) x))(* TODO: record update: with data := b*))*), f)
end.

(* Funcdef *)
Definition grow_table (arg : (tableinst * nat * ref)) : (option tableinst) := 
  match arg with
  | ((*var_pat*)ti, (*var_pat*)n, (*var_pat*)r) => (Some ti')
  | (*var_pat*)x => None
end.

(* Funcdef *)
Definition grow_memory (arg : (meminst * nat)) : (option meminst) := 
  match arg with
  | ((*var_pat*)mi, (*var_pat*)n) => (Some mi')
  | (*var_pat*)x => None
end.

Inductive e : Type :=
| e___hole : e
| e___seq : (list val) -> e -> (list instr) -> e
| e__label_ : n -> (list instr) -> e -> e
.

(* Funcdef *)
Definition unop (arg : (unop_numtype * numtype * c_numtype)) : (list c_numtype) := 
  match arg with
  | 
end.

(* Funcdef *)
Definition binop (arg : (binop_numtype * numtype * c_numtype * c_numtype)) : (list c_numtype) := 
  match arg with
  | 
end.

(* Funcdef *)
Definition testop (arg : (testop_numtype * numtype * c_numtype)) : c_numtype := 
  match arg with
  | 
end.

(* Funcdef *)
Definition relop (arg : (relop_numtype * numtype * c_numtype * c_numtype)) : c_numtype := 
  match arg with
  | 
end.

(* Funcdef *)
Definition ext (arg : (nat * nat * sx * c_numtype)) : c_numtype := 
  match arg with
  | 
end.

(* Funcdef *)
Definition cvtop (arg : (numtype * cvtop * numtype * (option sx) * c_numtype)) : (list c_numtype) := 
  match arg with
  | 
end.

(* Funcdef *)
Definition wrap_ (arg : ((nat * nat) * c_numtype)) : nat := 
  match arg with
  | 
end.

(* Funcdef *)
Definition bytes_ (arg : (nat * c_numtype)) : (list byte) := 
  match arg with
  | 
end.

Inductive step_pure_before_ref_is_null_false : (list admininstr) -> Prop :=
| step_pure_before_ref_is_null_false__ref_is_null_true (rt : reftype) (val : val): 
  val = ((*case_exp*)val__ref_null rt) ->
  step_pure_before_ref_is_null_false [(admininstr_val val); (*case_exp*)admininstr__ref_is_null]
.

Inductive step_pure : ((list admininstr) * (list admininstr)) -> Prop :=
| step_pure__unreachable : 
  step_pure ([(*case_exp*)admininstr__unreachable], [(*case_exp*)admininstr__trap])
| step_pure__nop : 
  step_pure ([(*case_exp*)admininstr__nop], [])
| step_pure__drop (val : val): 
  step_pure ([(admininstr_val val); (*case_exp*)admininstr__drop], [])
| step_pure__select_true (c : c_numtype) (t : (option valtype)) (val_1 : val) (val_2 : val): 
  c <> 0 ->
  step_pure ([(admininstr_val val_1); (admininstr_val val_2); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, c)); ((*case_exp*)admininstr__select t)], [(admininstr_val val_1)])
| step_pure__select_false (c : c_numtype) (t : (option valtype)) (val_1 : val) (val_2 : val): 
  c = 0 ->
  step_pure ([(admininstr_val val_1); (admininstr_val val_2); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, c)); ((*case_exp*)admininstr__select t)], [(admininstr_val val_2)])
| step_pure__block (bt : blocktype) (instr : (list instr)) (k : nat) (n : n) (t_1 : (list valtype)) (t_2 : (list valtype)) (val : (list val)): 
  bt = (t_1, t_2) ->
  step_pure ((List.app (List.map admininstr_val val) [((*case_exp*)admininstr__block (bt, instr))]), [((*case_exp*)admininstr__label_ (n, [], (List.app (List.map admininstr_val val) (List.map admininstr_instr instr))))])
| step_pure__loop (bt : blocktype) (instr : (list instr)) (k : nat) (n : n) (t_1 : (list valtype)) (t_2 : (list valtype)) (val : (list val)): 
  bt = (t_1, t_2) ->
  step_pure ((List.app (List.map admininstr_val val) [((*case_exp*)admininstr__loop (bt, instr))]), [((*case_exp*)admininstr__label_ (k, [((*case_exp*)instr__loop (bt, instr))], (List.app (List.map admininstr_val val) (List.map admininstr_instr instr))))])
| step_pure__if_true (bt : blocktype) (c : c_numtype) (instr_1 : (list instr)) (instr_2 : (list instr)): 
  c <> 0 ->
  step_pure ([((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, c)); ((*case_exp*)admininstr__if (bt, instr_1, instr_2))], [((*case_exp*)admininstr__block (bt, instr_1))])
| step_pure__if_false (bt : blocktype) (c : c_numtype) (instr_1 : (list instr)) (instr_2 : (list instr)): 
  c = 0 ->
  step_pure ([((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, c)); ((*case_exp*)admininstr__if (bt, instr_1, instr_2))], [((*case_exp*)admininstr__block (bt, instr_2))])
| step_pure__label_vals (instr : (list instr)) (n : n) (val : (list val)): 
  step_pure ([((*case_exp*)admininstr__label_ (n, instr, (List.map admininstr_val val)))], (List.map admininstr_val val))
| step_pure__br_zero (instr : (list instr)) (instr' : (list instr)) (n : n) (val : (list val)) (val' : (list val)): 
  step_pure ([((*case_exp*)admininstr__label_ (n, instr', (List.app (List.map admininstr_val val') (List.app (List.map admininstr_val val) (List.app [((*case_exp*)admininstr__br 0)] (List.map admininstr_instr instr))))))], (List.app (List.map admininstr_val val) (List.map admininstr_instr instr')))
| step_pure__br_succ (instr : (list instr)) (instr' : (list instr)) (l : labelidx) (n : n) (val : (list val)): 
  step_pure ([((*case_exp*)admininstr__label_ (n, instr', (List.app (List.map admininstr_val val) (List.app [((*case_exp*)admininstr__br l + 1)] (List.map admininstr_instr instr)))))], (List.app (List.map admininstr_val val) [((*case_exp*)admininstr__br l)]))
| step_pure__br_if_true (c : c_numtype) (l : labelidx): 
  c <> 0 ->
  step_pure ([((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, c)); ((*case_exp*)admininstr__br_if l)], [((*case_exp*)admininstr__br l)])
| step_pure__br_if_false (c : c_numtype) (l : labelidx): 
  c = 0 ->
  step_pure ([((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, c)); ((*case_exp*)admininstr__br_if l)], [])
| step_pure__br_table_lt (i : nat) (l : (list labelidx)) (l' : labelidx): 
  i < (List.length l) ->
  step_pure ([((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__br_table (l, l'))], [((*case_exp*)admininstr__br (list_get l i))])
| step_pure__br_table_ge (i : nat) (l : (list labelidx)) (l' : labelidx): 
  i >= (List.length l) ->
  step_pure ([((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__br_table (l, l'))], [((*case_exp*)admininstr__br l')])
| step_pure__frame_vals (f : frame) (n : n) (val : (list val)): 
  step_pure ([((*case_exp*)admininstr__frame_ (n, f, (List.map admininstr_val val)))], (List.map admininstr_val val))
| step_pure__return_frame (f : frame) (instr : (list instr)) (n : n) (val : (list val)) (val' : (list val)): 
  step_pure ([((*case_exp*)admininstr__frame_ (n, f, (List.app (List.map admininstr_val val') (List.app (List.map admininstr_val val) (List.app [(*case_exp*)admininstr__return] (List.map admininstr_instr instr))))))], (List.map admininstr_val val))
| step_pure__return_label (instr : (list instr)) (instr' : (list instr)) (k : nat) (val : (list val)): 
  step_pure ([((*case_exp*)admininstr__label_ (k, instr', (List.app (List.map admininstr_val val) (List.app [(*case_exp*)admininstr__return] (List.map admininstr_instr instr)))))], (List.app (List.map admininstr_val val) [(*case_exp*)admininstr__return]))
| step_pure__unop_val (c : c_numtype) (c_1 : c_numtype) (nt : numtype) (unop : unop_numtype): 
  (unop (unop, nt, c_1)) = [c] ->
  step_pure ([((*case_exp*)admininstr__const (nt, c_1)); ((*case_exp*)admininstr__unop (nt, unop))], [((*case_exp*)admininstr__const (nt, c))])
| step_pure__unop_trap (c_1 : c_numtype) (nt : numtype) (unop : unop_numtype): 
  (unop (unop, nt, c_1)) = [] ->
  step_pure ([((*case_exp*)admininstr__const (nt, c_1)); ((*case_exp*)admininstr__unop (nt, unop))], [(*case_exp*)admininstr__trap])
| step_pure__binop_val (binop : binop_numtype) (c : c_numtype) (c_1 : c_numtype) (c_2 : c_numtype) (nt : numtype): 
  (binop (binop, nt, c_1, c_2)) = [c] ->
  step_pure ([((*case_exp*)admininstr__const (nt, c_1)); ((*case_exp*)admininstr__const (nt, c_2)); ((*case_exp*)admininstr__binop (nt, binop))], [((*case_exp*)admininstr__const (nt, c))])
| step_pure__binop_trap (binop : binop_numtype) (c_1 : c_numtype) (c_2 : c_numtype) (nt : numtype): 
  (binop (binop, nt, c_1, c_2)) = [] ->
  step_pure ([((*case_exp*)admininstr__const (nt, c_1)); ((*case_exp*)admininstr__const (nt, c_2)); ((*case_exp*)admininstr__binop (nt, binop))], [(*case_exp*)admininstr__trap])
| step_pure__testop (c : c_numtype) (c_1 : c_numtype) (nt : numtype) (testop : testop_numtype): 
  c = (testop (testop, nt, c_1)) ->
  step_pure ([((*case_exp*)admininstr__const (nt, c_1)); ((*case_exp*)admininstr__testop (nt, testop))], [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, c))])
| step_pure__relop (c : c_numtype) (c_1 : c_numtype) (c_2 : c_numtype) (nt : numtype) (relop : relop_numtype): 
  c = (relop (relop, nt, c_1, c_2)) ->
  step_pure ([((*case_exp*)admininstr__const (nt, c_1)); ((*case_exp*)admininstr__const (nt, c_2)); ((*case_exp*)admininstr__relop (nt, relop))], [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, c))])
| step_pure__extend (c : c_numtype) (n : n) (nt : numtype) (o0 : nat): 
  (size (valtype_numtype nt)) = (Some o0) ->
  step_pure ([((*case_exp*)admininstr__const (nt, c)); ((*case_exp*)admininstr__extend (nt, n))], [((*case_exp*)admininstr__const (nt, (ext (n, o0, (*case_exp*)sx__s, c))))])
| step_pure__cvtop_val (c : c_numtype) (c_1 : c_numtype) (cvtop : cvtop) (nt_1 : numtype) (nt_2 : numtype) (sx : (option sx)): 
  (cvtop (nt_1, cvtop, nt_2, sx, c_1)) = [c] ->
  step_pure ([((*case_exp*)admininstr__const (nt_1, c_1)); ((*case_exp*)admininstr__cvtop (nt_2, cvtop, nt_1, sx))], [((*case_exp*)admininstr__const (nt_2, c))])
| step_pure__cvtop_trap (c_1 : c_numtype) (cvtop : cvtop) (nt_1 : numtype) (nt_2 : numtype) (sx : (option sx)): 
  (cvtop (nt_1, cvtop, nt_2, sx, c_1)) = [] ->
  step_pure ([((*case_exp*)admininstr__const (nt_1, c_1)); ((*case_exp*)admininstr__cvtop (nt_2, cvtop, nt_1, sx))], [(*case_exp*)admininstr__trap])
| step_pure__ref_is_null_true (rt : reftype) (val : val): 
  val = ((*case_exp*)val__ref_null rt) ->
  step_pure ([(admininstr_val val); (*case_exp*)admininstr__ref_is_null], [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, 1))])
| step_pure__ref_is_null_false (val : val): 
  ~ (step_pure_before_ref_is_null_false [(admininstr_val val); (*case_exp*)admininstr__ref_is_null]) ->
  step_pure ([(admininstr_val val); (*case_exp*)admininstr__ref_is_null], [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, 0))])
| step_pure__local_tee (val : val) (x : idx): 
  step_pure ([(admininstr_val val); ((*case_exp*)admininstr__local_tee x)], [(admininstr_val val); (admininstr_val val); ((*case_exp*)admininstr__local_set x)])
.

Inductive step_read_before_call_indirect_trap : config -> Prop :=
| step_read_before_call_indirect_trap__call_indirect_call (a : addr) (ft : functype) (ft' : functype) (i : nat) (instr : (list instr)) (t : (list valtype)) (x : idx) (z : state): 
  i < (List.length (table (z, x)).(elem)) ->
  a < (List.length (funcinst z)) ->
  (list_get (table (z, x)).(elem) i) = ((*case_exp*)ref__ref_func_addr a) ->
  (list_get (funcinst z) a).(code) = (ft', t, instr) ->
  ft = ft' ->
  step_read_before_call_indirect_trap (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__call_indirect (x, ft))])
.

Inductive step_read_before_table_fill_zero : config -> Prop :=
| step_read_before_table_fill_zero__table_fill_trap (i : nat) (n : n) (val : val) (x : idx) (z : state): 
  i + n > (List.length (table (z, x)).(elem)) ->
  step_read_before_table_fill_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_fill x)])
.

Inductive step_read_before_table_fill_succ : config -> Prop :=
| step_read_before_table_fill_succ__table_fill_zero (i : nat) (n : n) (val : val) (x : idx) (z : state): 
  ~ (step_read_before_table_fill_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_fill x)])) ->
  n = 0 ->
  step_read_before_table_fill_succ (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_fill x)])
| step_read_before_table_fill_succ__table_fill_trap (i : nat) (n : n) (val : val) (x : idx) (z : state): 
  i + n > (List.length (table (z, x)).(elem)) ->
  step_read_before_table_fill_succ (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_fill x)])
.

Inductive step_read_before_table_copy_zero : config -> Prop :=
| step_read_before_table_copy_zero__table_copy_trap (i : nat) (j : nat) (n : n) (x : idx) (y : idx) (z : state): 
  i + n > (List.length (table (z, y)).(elem)) \/ j + n > (List.length (table (z, x)).(elem)) ->
  step_read_before_table_copy_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_copy (x, y))])
.

Inductive step_read_before_table_copy_le : config -> Prop :=
| step_read_before_table_copy_le__table_copy_zero (i : nat) (j : nat) (n : n) (x : idx) (y : idx) (z : state): 
  ~ (step_read_before_table_copy_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_copy (x, y))])) ->
  n = 0 ->
  step_read_before_table_copy_le (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_copy (x, y))])
| step_read_before_table_copy_le__table_copy_trap (i : nat) (j : nat) (n : n) (x : idx) (y : idx) (z : state): 
  i + n > (List.length (table (z, y)).(elem)) \/ j + n > (List.length (table (z, x)).(elem)) ->
  step_read_before_table_copy_le (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_copy (x, y))])
.

Inductive step_read_before_table_copy_gt : config -> Prop :=
| step_read_before_table_copy_gt__table_copy_le (i : nat) (j : nat) (n : n) (x : idx) (y : idx) (z : state): 
  ~ (step_read_before_table_copy_le (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_copy (x, y))])) ->
  j <= i ->
  step_read_before_table_copy_gt (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_copy (x, y))])
| step_read_before_table_copy_gt__table_copy_zero (i : nat) (j : nat) (n : n) (x : idx) (y : idx) (z : state): 
  ~ (step_read_before_table_copy_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_copy (x, y))])) ->
  n = 0 ->
  step_read_before_table_copy_gt (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_copy (x, y))])
| step_read_before_table_copy_gt__table_copy_trap (i : nat) (j : nat) (n : n) (x : idx) (y : idx) (z : state): 
  i + n > (List.length (table (z, y)).(elem)) \/ j + n > (List.length (table (z, x)).(elem)) ->
  step_read_before_table_copy_gt (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_copy (x, y))])
.

Inductive step_read_before_table_init_zero : config -> Prop :=
| step_read_before_table_init_zero__table_init_trap (i : nat) (j : nat) (n : n) (x : idx) (y : idx) (z : state): 
  i + n > (List.length (elem (z, y)).(elem)) \/ j + n > (List.length (table (z, x)).(elem)) ->
  step_read_before_table_init_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_init (x, y))])
.

Inductive step_read_before_table_init_succ : config -> Prop :=
| step_read_before_table_init_succ__table_init_zero (i : nat) (j : nat) (n : n) (x : idx) (y : idx) (z : state): 
  ~ (step_read_before_table_init_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_init (x, y))])) ->
  n = 0 ->
  step_read_before_table_init_succ (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_init (x, y))])
| step_read_before_table_init_succ__table_init_trap (i : nat) (j : nat) (n : n) (x : idx) (y : idx) (z : state): 
  i + n > (List.length (elem (z, y)).(elem)) \/ j + n > (List.length (table (z, x)).(elem)) ->
  step_read_before_table_init_succ (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_init (x, y))])
.

Inductive step_read_before_memory_fill_zero : config -> Prop :=
| step_read_before_memory_fill_zero__memory_fill_trap (i : nat) (n : n) (val : val) (z : state): 
  i + n > (List.length (mem (z, 0)).(data)) ->
  step_read_before_memory_fill_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_fill])
.

Inductive step_read_before_memory_fill_succ : config -> Prop :=
| step_read_before_memory_fill_succ__memory_fill_zero (i : nat) (n : n) (val : val) (z : state): 
  ~ (step_read_before_memory_fill_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_fill])) ->
  n = 0 ->
  step_read_before_memory_fill_succ (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_fill])
| step_read_before_memory_fill_succ__memory_fill_trap (i : nat) (n : n) (val : val) (z : state): 
  i + n > (List.length (mem (z, 0)).(data)) ->
  step_read_before_memory_fill_succ (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_fill])
.

Inductive step_read_before_memory_copy_zero : config -> Prop :=
| step_read_before_memory_copy_zero__memory_copy_trap (i : nat) (j : nat) (n : n) (z : state): 
  i + n > (List.length (mem (z, 0)).(data)) \/ j + n > (List.length (mem (z, 0)).(data)) ->
  step_read_before_memory_copy_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_copy])
.

Inductive step_read_before_memory_copy_le : config -> Prop :=
| step_read_before_memory_copy_le__memory_copy_zero (i : nat) (j : nat) (n : n) (z : state): 
  ~ (step_read_before_memory_copy_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_copy])) ->
  n = 0 ->
  step_read_before_memory_copy_le (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_copy])
| step_read_before_memory_copy_le__memory_copy_trap (i : nat) (j : nat) (n : n) (z : state): 
  i + n > (List.length (mem (z, 0)).(data)) \/ j + n > (List.length (mem (z, 0)).(data)) ->
  step_read_before_memory_copy_le (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_copy])
.

Inductive step_read_before_memory_copy_gt : config -> Prop :=
| step_read_before_memory_copy_gt__memory_copy_le (i : nat) (j : nat) (n : n) (z : state): 
  ~ (step_read_before_memory_copy_le (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_copy])) ->
  j <= i ->
  step_read_before_memory_copy_gt (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_copy])
| step_read_before_memory_copy_gt__memory_copy_zero (i : nat) (j : nat) (n : n) (z : state): 
  ~ (step_read_before_memory_copy_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_copy])) ->
  n = 0 ->
  step_read_before_memory_copy_gt (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_copy])
| step_read_before_memory_copy_gt__memory_copy_trap (i : nat) (j : nat) (n : n) (z : state): 
  i + n > (List.length (mem (z, 0)).(data)) \/ j + n > (List.length (mem (z, 0)).(data)) ->
  step_read_before_memory_copy_gt (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_copy])
.

Inductive step_read_before_memory_init_zero : config -> Prop :=
| step_read_before_memory_init_zero__memory_init_trap (i : nat) (j : nat) (n : n) (x : idx) (z : state): 
  i + n > (List.length (data (z, x)).(data)) \/ j + n > (List.length (mem (z, 0)).(data)) ->
  step_read_before_memory_init_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__memory_init x)])
.

Inductive step_read_before_memory_init_succ : config -> Prop :=
| step_read_before_memory_init_succ__memory_init_zero (i : nat) (j : nat) (n : n) (x : idx) (z : state): 
  ~ (step_read_before_memory_init_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__memory_init x)])) ->
  n = 0 ->
  step_read_before_memory_init_succ (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__memory_init x)])
| step_read_before_memory_init_succ__memory_init_trap (i : nat) (j : nat) (n : n) (x : idx) (z : state): 
  i + n > (List.length (data (z, x)).(data)) \/ j + n > (List.length (mem (z, 0)).(data)) ->
  step_read_before_memory_init_succ (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__memory_init x)])
.

Inductive step_read : (config * (list admininstr)) -> Prop :=
| step_read__call (x : idx) (z : state): 
  x < (List.length (funcaddr z)) ->
  step_read ((z, [((*case_exp*)admininstr__call x)]), [((*case_exp*)admininstr__call_addr (list_get (funcaddr z) x))])
| step_read__call_indirect_call (a : addr) (ft : functype) (ft' : functype) (i : nat) (instr : (list instr)) (t : (list valtype)) (x : idx) (z : state): 
  i < (List.length (table (z, x)).(elem)) ->
  a < (List.length (funcinst z)) ->
  (list_get (table (z, x)).(elem) i) = ((*case_exp*)ref__ref_func_addr a) ->
  (list_get (funcinst z) a).(code) = (ft', t, instr) ->
  ft = ft' ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__call_indirect (x, ft))]), [((*case_exp*)admininstr__call_addr a)])
| step_read__call_indirect_trap (ft : functype) (i : nat) (x : idx) (z : state): 
  ~ (step_read_before_call_indirect_trap (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__call_indirect (x, ft))])) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__call_indirect (x, ft))]), [(*case_exp*)admininstr__trap])
| step_read__call_addr (a : addr) (f : frame) (func : func) (instr : (list instr)) (k : nat) (m : moduleinst) (n : n) (t : (list valtype)) (t_1 : (list valtype)) (t_2 : (list valtype)) (val : (list val)) (z : state) (o0 : (list val)): 
  (List.length t) = (List.length o0) ->
  a < (List.length (funcinst z)) ->
  (List.Forall2 (fun t o0 => (default_ t) = (Some o0)) t o0) ->
  (list_get (funcinst z) a) = (
{|
  module := m;
  code := func;
|})
 ->
  func = ((t_1, t_2), t, instr) ->
  f = (
{|
  local := (List.app val o0);
  module := m;
|})
 ->
  step_read ((z, (List.app (List.map admininstr_val val) [((*case_exp*)admininstr__call_addr a)])), [((*case_exp*)admininstr__frame_ (n, f, [((*case_exp*)admininstr__label_ (n, [], (List.map admininstr_instr instr)))]))])
| step_read__ref_func (x : idx) (z : state): 
  x < (List.length (funcaddr z)) ->
  step_read ((z, [((*case_exp*)admininstr__ref_func x)]), [((*case_exp*)admininstr__ref_func_addr (list_get (funcaddr z) x))])
| step_read__local_get (x : idx) (z : state): 
  step_read ((z, [((*case_exp*)admininstr__local_get x)]), [(admininstr_val (local (z, x)))])
| step_read__global_get (x : idx) (z : state): 
  step_read ((z, [((*case_exp*)admininstr__global_get x)]), [(admininstr_val (global (z, x)).(value))])
| step_read__table_get_trap (i : nat) (x : idx) (z : state): 
  i >= (List.length (table (z, x)).(elem)) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__table_get x)]), [(*case_exp*)admininstr__trap])
| step_read__table_get_val (i : nat) (x : idx) (z : state): 
  i < (List.length (table (z, x)).(elem)) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__table_get x)]), [(admininstr_ref (list_get (table (z, x)).(elem) i))])
| step_read__table_size (n : n) (x : idx) (z : state): 
  (List.length (table (z, x)).(elem)) = n ->
  step_read ((z, [((*case_exp*)admininstr__table_size x)]), [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n))])
| step_read__table_fill_trap (i : nat) (n : n) (val : val) (x : idx) (z : state): 
  i + n > (List.length (table (z, x)).(elem)) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_fill x)]), [(*case_exp*)admininstr__trap])
| step_read__table_fill_zero (i : nat) (n : n) (val : val) (x : idx) (z : state): 
  ~ (step_read_before_table_fill_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_fill x)])) ->
  n = 0 ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_fill x)]), [])
| step_read__table_fill_succ (i : nat) (n : n) (val : val) (x : idx) (z : state): 
  ~ (step_read_before_table_fill_succ (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_fill x)])) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_fill x)]), [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__table_set x); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i + 1)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n - 1)); ((*case_exp*)admininstr__table_fill x)])
| step_read__table_copy_trap (i : nat) (j : nat) (n : n) (x : idx) (y : idx) (z : state): 
  i + n > (List.length (table (z, y)).(elem)) \/ j + n > (List.length (table (z, x)).(elem)) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_copy (x, y))]), [(*case_exp*)admininstr__trap])
| step_read__table_copy_zero (i : nat) (j : nat) (n : n) (x : idx) (y : idx) (z : state): 
  ~ (step_read_before_table_copy_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_copy (x, y))])) ->
  n = 0 ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_copy (x, y))]), [])
| step_read__table_copy_le (i : nat) (j : nat) (n : n) (x : idx) (y : idx) (z : state): 
  ~ (step_read_before_table_copy_le (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_copy (x, y))])) ->
  j <= i ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_copy (x, y))]), [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__table_get y); ((*case_exp*)admininstr__table_set x); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j + 1)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i + 1)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n - 1)); ((*case_exp*)admininstr__table_copy (x, y))])
| step_read__table_copy_gt (i : nat) (j : nat) (n : n) (x : idx) (y : idx) (z : state): 
  ~ (step_read_before_table_copy_gt (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_copy (x, y))])) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_copy (x, y))]), [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j + n - 1)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i + n - 1)); ((*case_exp*)admininstr__table_get y); ((*case_exp*)admininstr__table_set x); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n - 1)); ((*case_exp*)admininstr__table_copy (x, y))])
| step_read__table_init_trap (i : nat) (j : nat) (n : n) (x : idx) (y : idx) (z : state): 
  i + n > (List.length (elem (z, y)).(elem)) \/ j + n > (List.length (table (z, x)).(elem)) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_init (x, y))]), [(*case_exp*)admininstr__trap])
| step_read__table_init_zero (i : nat) (j : nat) (n : n) (x : idx) (y : idx) (z : state): 
  ~ (step_read_before_table_init_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_init (x, y))])) ->
  n = 0 ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_init (x, y))]), [])
| step_read__table_init_succ (i : nat) (j : nat) (n : n) (x : idx) (y : idx) (z : state): 
  i < (List.length (elem (z, y)).(elem)) ->
  ~ (step_read_before_table_init_succ (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_init (x, y))])) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_init (x, y))]), [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); (admininstr_ref (list_get (elem (z, y)).(elem) i)); ((*case_exp*)admininstr__table_set x); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j + 1)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i + 1)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n - 1)); ((*case_exp*)admininstr__table_init (x, y))])
| step_read__load_num_trap (i : nat) (n_a : n) (n_o : n) (nt : numtype) (z : state) (o0 : nat): 
  (size (valtype_numtype nt)) = (Some o0) ->
  i + n_o + o0 / 8 > (List.length (mem (z, 0)).(data)) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__load (nt, None, n_a, n_o))]), [(*case_exp*)admininstr__trap])
| step_read__load_num_val (c : c_numtype) (i : nat) (n_a : n) (n_o : n) (nt : numtype) (z : state) (o0 : nat) (o1 : nat): 
  (size (valtype_numtype nt)) = (Some o0) ->
  (size (valtype_numtype nt)) = (Some o1) ->
  (bytes_ (o0, c)) = (* FIXME: unsuppurted exp: Unknown exp: $mem(z, 0).DATA_meminst[(i + n_O) : (o1 / 8)] *) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__load (nt, None, n_a, n_o))]), [((*case_exp*)admininstr__const (nt, c))])
| step_read__load_pack_trap (i : nat) (n : n) (n_a : n) (n_o : n) (nt : numtype) (sx : sx) (z : state): 
  i + n_o + n / 8 > (List.length (mem (z, 0)).(data)) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__load (nt, (Some (n, sx)), n_a, n_o))]), [(*case_exp*)admininstr__trap])
| step_read__load_pack_val (c : c_numtype) (i : nat) (n : n) (n_a : n) (n_o : n) (nt : numtype) (sx : sx) (z : state) (o0 : nat): 
  (size (valtype_numtype nt)) = (Some o0) ->
  (bytes_ (n, c)) = (* FIXME: unsuppurted exp: Unknown exp: $mem(z, 0).DATA_meminst[(i + n_O) : (n / 8)] *) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__load (nt, (Some (n, sx)), n_a, n_o))]), [((*case_exp*)admininstr__const (nt, (ext (n, o0, sx, c))))])
| step_read__memory_size (n : n) (z : state): 
  (* FIXME: unsuppurted exp: Unknown exp: ((n * 64) * $Ki) *) = (List.length (mem (z, 0)).(data)) ->
  step_read ((z, [(*case_exp*)admininstr__memory_size]), [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n))])
| step_read__memory_fill_trap (i : nat) (n : n) (val : val) (z : state): 
  i + n > (List.length (mem (z, 0)).(data)) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_fill]), [(*case_exp*)admininstr__trap])
| step_read__memory_fill_zero (i : nat) (n : n) (val : val) (z : state): 
  ~ (step_read_before_memory_fill_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_fill])) ->
  n = 0 ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_fill]), [])
| step_read__memory_fill_succ (i : nat) (n : n) (val : val) (z : state): 
  ~ (step_read_before_memory_fill_succ (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_fill])) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_fill]), [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_val val); ((*case_exp*)admininstr__store ((*case_exp*)numtype__i32, (Some 8), 0, 0)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i + 1)); (admininstr_val val); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n - 1)); (*case_exp*)admininstr__memory_fill])
| step_read__memory_copy_trap (i : nat) (j : nat) (n : n) (z : state): 
  i + n > (List.length (mem (z, 0)).(data)) \/ j + n > (List.length (mem (z, 0)).(data)) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_copy]), [(*case_exp*)admininstr__trap])
| step_read__memory_copy_zero (i : nat) (j : nat) (n : n) (z : state): 
  ~ (step_read_before_memory_copy_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_copy])) ->
  n = 0 ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_copy]), [])
| step_read__memory_copy_le (i : nat) (j : nat) (n : n) (z : state): 
  ~ (step_read_before_memory_copy_le (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_copy])) ->
  j <= i ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_copy]), [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__load ((*case_exp*)numtype__i32, (Some (8, (*case_exp*)sx__u)), 0, 0)); ((*case_exp*)admininstr__store ((*case_exp*)numtype__i32, (Some 8), 0, 0)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j + 1)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i + 1)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n - 1)); (*case_exp*)admininstr__memory_copy])
| step_read__memory_copy_gt (i : nat) (j : nat) (n : n) (z : state): 
  ~ (step_read_before_memory_copy_gt (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_copy])) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_copy]), [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j + n - 1)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i + n - 1)); ((*case_exp*)admininstr__load ((*case_exp*)numtype__i32, (Some (8, (*case_exp*)sx__u)), 0, 0)); ((*case_exp*)admininstr__store ((*case_exp*)numtype__i32, (Some 8), 0, 0)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n - 1)); (*case_exp*)admininstr__memory_copy])
| step_read__memory_init_trap (i : nat) (j : nat) (n : n) (x : idx) (z : state): 
  i + n > (List.length (data (z, x)).(data)) \/ j + n > (List.length (mem (z, 0)).(data)) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__memory_init x)]), [(*case_exp*)admininstr__trap])
| step_read__memory_init_zero (i : nat) (j : nat) (n : n) (x : idx) (z : state): 
  ~ (step_read_before_memory_init_zero (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__memory_init x)])) ->
  n = 0 ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__memory_init x)]), [])
| step_read__memory_init_succ (i : nat) (j : nat) (n : n) (x : idx) (z : state): 
  i < (List.length (data (z, x)).(data)) ->
  ~ (step_read_before_memory_init_succ (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__memory_init x)])) ->
  step_read ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__memory_init x)]), [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, (list_get (data (z, x)).(data) i))); ((*case_exp*)admininstr__store ((*case_exp*)numtype__i32, (Some 8), 0, 0)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, j + 1)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i + 1)); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n - 1)); ((*case_exp*)admininstr__memory_init x)])
.

Inductive step : (config * config) -> Prop :=
| step__pure (instr : (list instr)) (instr' : (list instr)) (z : state): 
  (step_pure ((List.map admininstr_instr instr), (List.map admininstr_instr instr'))) ->
  step ((z, (List.map admininstr_instr instr)), (z, (List.map admininstr_instr instr')))
| step__read (instr : (list instr)) (instr' : (list instr)) (z : state): 
  (step_read ((z, (List.map admininstr_instr instr)), (List.map admininstr_instr instr'))) ->
  step ((z, (List.map admininstr_instr instr)), (z, (List.map admininstr_instr instr')))
| step__local_set (val : val) (x : idx) (z : state): 
  step ((z, [(admininstr_val val); ((*case_exp*)admininstr__local_set x)]), ((with_local (z, x, val)), []))
| step__global_set (val : val) (x : idx) (z : state): 
  step ((z, [(admininstr_val val); ((*case_exp*)admininstr__global_set x)]), ((with_global (z, x, val)), []))
| step__table_set_trap (i : nat) (ref : ref) (x : idx) (z : state): 
  i >= (List.length (table (z, x)).(elem)) ->
  step ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_ref ref); ((*case_exp*)admininstr__table_set x)]), (z, [(*case_exp*)admininstr__trap]))
| step__table_set_val (i : nat) (ref : ref) (x : idx) (z : state): 
  i < (List.length (table (z, x)).(elem)) ->
  step ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); (admininstr_ref ref); ((*case_exp*)admininstr__table_set x)]), ((with_table (z, x, i, ref)), []))
| step__table_grow_succeed (n : n) (ref : ref) (ti : tableinst) (x : idx) (z : state) (o0 : tableinst): 
  (grow_table ((table (z, x)), n, ref)) = (Some o0) ->
  o0 = ti ->
  step ((z, [(admininstr_ref ref); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_grow x)]), ((with_tableinst (z, x, ti)), [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, (List.length (table (z, x)).(elem))))]))
| step__table_grow_fail (n : n) (ref : ref) (x : idx) (z : state): 
  step ((z, [(admininstr_ref ref); ((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)admininstr__table_grow x)]), (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, 0 - 1))]))
| step__elem_drop (x : idx) (z : state): 
  step ((z, [((*case_exp*)admininstr__elem_drop x)]), ((with_elem (z, x, [])), []))
| step__store_num_trap (c : c_numtype) (i : nat) (n_a : n) (n_o : n) (nt : numtype) (z : state) (o0 : nat): 
  (size (valtype_numtype nt)) = (Some o0) ->
  i + n_o + o0 / 8 > (List.length (mem (z, 0)).(data)) ->
  step ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const (nt, c)); ((*case_exp*)admininstr__store (nt, None, n_a, n_o))]), (z, [(*case_exp*)admininstr__trap]))
| step__store_num_val (b : (list byte)) (c : c_numtype) (i : nat) (n_a : n) (n_o : n) (nt : numtype) (z : state) (o0 : nat) (o1 : nat): 
  (size (valtype_numtype nt)) = (Some o0) ->
  (size (valtype_numtype nt)) = (Some o1) ->
  b = (bytes_ (o1, c)) ->
  step ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const (nt, c)); ((*case_exp*)admininstr__store (nt, None, n_a, n_o))]), ((with_mem (z, 0, i + n_o, o0 / 8, b)), []))
| step__store_pack_trap (c : c_numtype) (i : nat) (n : n) (n_a : n) (n_o : n) (nt : numtype) (z : state): 
  i + n_o + n / 8 > (List.length (mem (z, 0)).(data)) ->
  step ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const (nt, c)); ((*case_exp*)admininstr__store (nt, (Some n), n_a, n_o))]), (z, [(*case_exp*)admininstr__trap]))
| step__store_pack_val (b : (list byte)) (c : c_numtype) (i : nat) (n : n) (n_a : n) (n_o : n) (nt : numtype) (z : state) (o0 : nat): 
  (size (valtype_numtype nt)) = (Some o0) ->
  b = (bytes_ (n, (wrap_ ((o0, n), c)))) ->
  step ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, i)); ((*case_exp*)admininstr__const (nt, c)); ((*case_exp*)admininstr__store (nt, (Some n), n_a, n_o))]), ((with_mem (z, 0, i + n_o, n / 8, b)), []))
| step__memory_grow_succeed (mi : meminst) (n : n) (z : state) (o0 : meminst): 
  (grow_memory ((mem (z, 0)), n)) = (Some o0) ->
  o0 = mi ->
  step ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_grow]), ((with_meminst (z, 0, mi)), [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, (List.length (mem (z, 0)).(data)) / (* FIXME: unsuppurted exp: Unknown exp: (64 * $Ki) *)))]))
| step__memory_grow_fail (n : n) (z : state): 
  step ((z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, n)); (*case_exp*)admininstr__memory_grow]), (z, [((*case_exp*)admininstr__const ((*case_exp*)numtype__i32, 0 - 1))]))
| step__data_drop (x : idx) (z : state): 
  step ((z, [((*case_exp*)admininstr__data_drop x)]), ((with_data (z, x, [])), []))
.

(* Funcdef *)
Fixpoint funcs (arg : (list externval)) : (list funcaddr) := 
  match arg with
  | [] => []
  | (* FIXME: unsuppurted pat:Unsupported match pattern [FUNC_externval(fa)] :: externval'*{externval'}*) => (List.app [fa] (funcs externval'))
  | (* FIXME: unsuppurted pat:Unsupported match pattern [externval] :: externval'*{externval'}*) => (funcs externval')
end.

(* Funcdef *)
Fixpoint globals (arg : (list externval)) : (list globaladdr) := 
  match arg with
  | [] => []
  | (* FIXME: unsuppurted pat:Unsupported match pattern [GLOBAL_externval(ga)] :: externval'*{externval'}*) => (List.app [ga] (globals externval'))
  | (* FIXME: unsuppurted pat:Unsupported match pattern [externval] :: externval'*{externval'}*) => (globals externval')
end.

(* Funcdef *)
Fixpoint tables (arg : (list externval)) : (list tableaddr) := 
  match arg with
  | [] => []
  | (* FIXME: unsuppurted pat:Unsupported match pattern [TABLE_externval(ta)] :: externval'*{externval'}*) => (List.app [ta] (tables externval'))
  | (* FIXME: unsuppurted pat:Unsupported match pattern [externval] :: externval'*{externval'}*) => (tables externval')
end.

(* Funcdef *)
Fixpoint mems (arg : (list externval)) : (list memaddr) := 
  match arg with
  | [] => []
  | (* FIXME: unsuppurted pat:Unsupported match pattern [MEM_externval(ma)] :: externval'*{externval'}*) => (List.app [ma] (mems externval'))
  | (* FIXME: unsuppurted pat:Unsupported match pattern [externval] :: externval'*{externval'}*) => (mems externval')
end.

(* Funcdef *)
Definition instexport (arg : ((list funcaddr) * (list globaladdr) * (list tableaddr) * (list memaddr) * export)) : exportinst := 
  match arg with
  | ((* test_iter_pat *)fa, (* test_iter_pat *)ga, (* test_iter_pat *)ta, (* test_iter_pat *)ma, ((*var_pat*)name, (*case_pat*)externuse__func (*var_pat*)x)) => (
{|
  name := name;
  value := ((*case_exp*)externval__func (list_get fa x));
|})

  | ((* test_iter_pat *)fa, (* test_iter_pat *)ga, (* test_iter_pat *)ta, (* test_iter_pat *)ma, ((*var_pat*)name, (*case_pat*)externuse__global (*var_pat*)x)) => (
{|
  name := name;
  value := ((*case_exp*)externval__global (list_get ga x));
|})

  | ((* test_iter_pat *)fa, (* test_iter_pat *)ga, (* test_iter_pat *)ta, (* test_iter_pat *)ma, ((*var_pat*)name, (*case_pat*)externuse__table (*var_pat*)x)) => (
{|
  name := name;
  value := ((*case_exp*)externval__table (list_get ta x));
|})

  | ((* test_iter_pat *)fa, (* test_iter_pat *)ga, (* test_iter_pat *)ta, (* test_iter_pat *)ma, ((*var_pat*)name, (*case_pat*)externuse__mem (*var_pat*)x)) => (
{|
  name := name;
  value := ((*case_exp*)externval__mem (list_get ma x));
|})

end.

(* Funcdef *)
Definition allocfunc (arg : (store * moduleinst * func)) : (store * funcaddr) := 
  match arg with
  | ((*var_pat*)s, (*var_pat*)m, (*var_pat*)func) => (s(* TODO: record update: with func := (List.app s.(func) [fi])*), (List.length s.(func)))
end.

(* Funcdef *)
Definition allocfuncs (arg : (store * moduleinst * (list func))) : (store * (list funcaddr)) := 
  match arg with
  | ((*var_pat*)s, (*var_pat*)m, []) => (s, [])
  | ((*var_pat*)s, (*var_pat*)m, (* FIXME: unsuppurted pat:Unsupported match pattern [func] :: func'*{func'}*)) => (s_2, (List.app [fa] fa'))
end.

(* Funcdef *)
Definition allocglobal (arg : (store * globaltype * val)) : (store * globaladdr) := 
  match arg with
  | ((*var_pat*)s, (*var_pat*)globaltype, (*var_pat*)val) => (s(* TODO: record update: with global := (List.app s.(global) [gi])*), (List.length s.(global)))
end.

(* Funcdef *)
Definition allocglobals (arg : (store * (list globaltype) * (list val))) : (store * (list globaladdr)) := 
  match arg with
  | ((*var_pat*)s, [], []) => (s, [])
  | ((*var_pat*)s, (* FIXME: unsuppurted pat:Unsupported match pattern [globaltype] :: globaltype'*{globaltype'}*), (* FIXME: unsuppurted pat:Unsupported match pattern [val] :: val'*{val'}*)) => (s_2, (List.app [ga] ga'))
end.

(* Funcdef *)
Definition alloctable (arg : (store * tabletype)) : (store * tableaddr) := 
  match arg with
  | ((*var_pat*)s, (((*var_pat*)i, (*var_pat*)j), (*var_pat*)rt)) => (s(* TODO: record update: with table := (List.app s.(table) [ti])*), (List.length s.(table)))
end.

(* Funcdef *)
Definition alloctables (arg : (store * (list tabletype))) : (store * (list tableaddr)) := 
  match arg with
  | ((*var_pat*)s, []) => (s, [])
  | ((*var_pat*)s, (* FIXME: unsuppurted pat:Unsupported match pattern [tabletype] :: tabletype'*{tabletype'}*)) => (s_2, (List.app [ta] ta'))
end.

(* Funcdef *)
Definition allocmem (arg : (store * memtype)) : (store * memaddr) := 
  match arg with
  | ((*var_pat*)s, ((*var_pat*)i, (*var_pat*)j)) => (s(* TODO: record update: with mem := (List.app s.(mem) [mi])*), (List.length s.(mem)))
end.

(* Funcdef *)
Definition allocmems (arg : (store * (list memtype))) : (store * (list memaddr)) := 
  match arg with
  | ((*var_pat*)s, []) => (s, [])
  | ((*var_pat*)s, (* FIXME: unsuppurted pat:Unsupported match pattern [memtype] :: memtype'*{memtype'}*)) => (s_2, (List.app [ma] ma'))
end.

(* Funcdef *)
Definition allocelem (arg : (store * reftype * (list ref))) : (store * elemaddr) := 
  match arg with
  | ((*var_pat*)s, (*var_pat*)rt, (* test_iter_pat *)ref) => (s(* TODO: record update: with elem := (List.app s.(elem) [ei])*), (List.length s.(elem)))
end.

(* Funcdef *)
Definition allocelems (arg : (store * (list reftype) * (list (list ref)))) : (store * (list elemaddr)) := 
  match arg with
  | ((*var_pat*)s, [], []) => (s, [])
  | ((*var_pat*)s, (* FIXME: unsuppurted pat:Unsupported match pattern [rt] :: rt'*{rt'}*), (* FIXME: unsuppurted pat:Unsupported match pattern [ref]*{ref} :: ref'*{ref'}*{ref'}*)) => (s_2, (List.app [ea] ea'))
end.

(* Funcdef *)
Definition allocdata (arg : (store * (list byte))) : (store * dataaddr) := 
  match arg with
  | ((*var_pat*)s, (* test_iter_pat *)byte) => (s(* TODO: record update: with data := (List.app s.(data) [di])*), (List.length s.(data)))
end.

(* Funcdef *)
Definition allocdatas (arg : (store * (list (list byte)))) : (store * (list dataaddr)) := 
  match arg with
  | ((*var_pat*)s, []) => (s, [])
  | ((*var_pat*)s, (* FIXME: unsuppurted pat:Unsupported match pattern [byte]*{byte} :: byte'*{byte'}*{byte'}*)) => (s_2, (List.app [da] da'))
end.

(* Funcdef *)
Definition allocmodule (arg : (store * module * (list externval) * (list val) * (list (list ref)))) : (store * moduleinst) := 
  match arg with
  | ((*var_pat*)s, (*var_pat*)module, (* test_iter_pat *)externval, (* test_iter_pat *)val, (* FIXME: unsuppurted pat:Unsupported match pattern ref*{ref}*{ref}*)) => (s_6, m)
end.

(* Funcdef *)
Definition runelem (arg : (elem * idx)) : (list instr) := 
  match arg with
  | (((*var_pat*)reftype, (* test_iter_pat *)expr, None), (*var_pat*)i) => []
  | (((*var_pat*)reftype, (* test_iter_pat *)expr, (Some (*case_pat*)elemmode__declare)), (*var_pat*)i) => [((*case_exp*)instr__elem_drop i)]
  | (((*var_pat*)reftype, (* test_iter_pat *)expr, (Some (*case_pat*)elemmode__table ((*var_pat*)x, (* test_iter_pat *)instr))), (*var_pat*)i) => (List.app instr [((*case_exp*)instr__const ((*case_exp*)numtype__i32, 0)); ((*case_exp*)instr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)instr__table_init (x, i)); ((*case_exp*)instr__elem_drop i)])
end.

(* Funcdef *)
Definition rundata (arg : (data * idx)) : (list instr) := 
  match arg with
  | (((* test_iter_pat *)byte, None), (*var_pat*)i) => []
  | (((* test_iter_pat *)byte, (Some (*case_pat*)datamode__memory (0, (* test_iter_pat *)instr))), (*var_pat*)i) => (List.app instr [((*case_exp*)instr__const ((*case_exp*)numtype__i32, 0)); ((*case_exp*)instr__const ((*case_exp*)numtype__i32, n)); ((*case_exp*)instr__memory_init i); ((*case_exp*)instr__data_drop i)])
end.

(* Funcdef *)
Fixpoint concat_instr (arg : (list (list instr))) : (list instr) := 
  match arg with
  | [] => []
  | (* FIXME: unsuppurted pat:Unsupported match pattern [instr]*{instr} :: instr'*{instr'}*{instr'}*) => (List.app instr (concat_instr (List.map (fun instr' => instr') instr')))
end.

(* Funcdef *)
Definition instantiation (arg : (store * module * (list externval))) : config := 
  match arg with
  | ((*var_pat*)s, (*var_pat*)module, (* test_iter_pat *)externval) => ((s', f), (List.app (List.map admininstr_instr instr_elem) (List.app (List.map admininstr_instr instr_data) (option.map (fun x => ((*case_exp*)admininstr__call x)) x))))
end.

(* Funcdef *)
Definition invocation (arg : (store * funcaddr * (list val))) : config := 
  match arg with
  | ((*var_pat*)s, (*var_pat*)fa, (* test_iter_pat *)val) => ((s, f), (List.app (List.map admininstr_val val) [((*case_exp*)admininstr__call_addr fa)]))
end.

