From Coq Require Import String List Unicode.Utf8.
From RecordUpdate Require Import RecordSet.
Require Import NArith.
Require Import Arith.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.
(* TODO: Is Notation global? *)
(* TODO: Is Coercion global? *)
From WasmSpectec Require Import generatedcode.
From WasmSpectec Require Import helper_lemmas helper_tactics typing_lemmas.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.

(* NOTE: Naming conventions:
         1. type for types
         2. type__constructor for types with multiple constructors
         3. type__ for types with a single constructor *)

(* NOTE: Comment out below to display coercions in proof state *)
(* Set Printing Coercions. *)
(* NOTE: Comment out below to display parentheses in proof state *)
(* Set Printing Parentheses. *)

(* TODO: Use SSReflect seq operations in generated coercions *)
Lemma map_map {A B : Type} (f : A -> B) (s : seq A) : List.map f s = map f s.
Proof. by []. Qed.

Lemma length_size {A : Type} (s : seq A) : Datatypes.length s = size s.
Proof. by []. Qed.

Lemma cat_app {A : Type} (s1 s2 : seq A) : List.app s1 s2 = cat s1 s2.
Proof. by []. Qed.

Lemma cat_nil : forall T (s1 s2 : seq T),
  (s1 ++ s2) = [::] <-> s1 = [::] /\ s2 = [::].
Proof.
  move => T s1 s2. split.
  - by case: s1; case s2.
  - by move => [-> ->].
Qed.

Definition is_const (e : admininstr) : bool :=
  if e is admininstr__CONST _ _ then true else false.

Definition const_list (es : list admininstr) : bool :=
  List.forallb is_const es.

Lemma v_to_e_const: forall vs,
    const_list (list__val__admininstr vs).
Proof.
  move => vs. elim: vs => //=.
  move => v vs Hconst.
  by case v => //=.
Qed.

(* NOTE: const_list es is coerced into proposition by is_true *)
Definition terminal_form (es : list admininstr) :=
  const_list es \/ es = [:: admininstr__TRAP].

Lemma const_list_cat: forall vs1 vs2,
    const_list (vs1 ++ vs2) = const_list vs1 && const_list vs2.
Proof.
  move => vs1 vs2.
  repeat rewrite cat_app.
  rewrite /const_list.
  by rewrite List.forallb_app.
Qed.

Lemma const_list_concat: forall vs1 vs2,
    const_list vs1 ->
    const_list vs2 ->
    const_list (vs1 ++ vs2).
Proof.
  move => vs1 vs2 Hconst1 Hconst2.
  rewrite const_list_cat.
  apply/andP => //=.
Qed.

Lemma const_list_split: forall vs1 vs2,
    const_list (vs1 ++ vs2) ->
    const_list vs1 /\
    const_list vs2.
Proof.
  move => vs1 vs2 Hconst.
  rewrite const_list_cat in Hconst.
  by move/andP in Hconst.
Qed.    

Lemma const_es_exists: forall es,
    const_list es ->
    {vs | es = list__val__admininstr vs}.
Proof.
  induction es => //=.
  - by exists [::].
  - move => HConst.
    move/andP in HConst. destruct HConst as [? HConst].
    destruct a => //=.
    apply IHes in HConst as [vs ->].
    (* TODO: Name v_valtype and v_val_ appropriately *)
    by exists (val__CONST v_valtype v_val_ :: vs).
Qed.

(* TODO: Rename this lemma more appropriately *)
(* TODO: There may be an equivalent lemma in ssreflect *)
Lemma map_eq_nil {A B : Type} (f : A -> B) (l : seq A) :
  map f l = [::] -> l = [::].
Proof.
  case: l => //=.
Qed.

(* TODO: Rename this lemma more appropriately *)
(* TODO: There may be an equivalent lemma in ssreflect *)
Lemma map_neq_nil {A B : Type} (f: A -> B) (l: seq A) :
  map f l <> [] → l <> [].
Proof.
  case: l => //=.
Qed.

(* MEMO: reduce_simple -> Step_pure *)
(* MEMO: rs_trap -> Step_pure__trap_vals *)
Lemma reduce_trap_left: forall vs,
    const_list vs ->
    vs <> [::] ->
    Step_pure (vs ++ [:: admininstr__TRAP]) [:: admininstr__TRAP].
Proof.
  move => vs HConst H.
  apply const_es_exists in HConst as [vcs ->].
  eapply Step_pure__trap_vals with (v_val := vcs) (v_admininstr := [::]) => //=.
  rewrite /list__val__admininstr in H.
  left. by apply/map_neq_nil: H.
Qed.

(* TODO: Rename this lemma more appropriately *)
Lemma v_e_trap: forall vs es,
    const_list vs ->
    vs ++ es = [:: admininstr__TRAP] ->
    vs = [::] /\ es = [:: admininstr__TRAP].
Proof.
  move => vs es HConst H.
  destruct vs => //=.
  destruct vs => //=. destruct es => //=.
  simpl in H. inversion H. by subst.
Qed.

(* TODO: Rename this lemma more appropriately *)
Lemma concat_cancel_last: forall {X:Type} (l1 l2: seq X) (e1 e2:X),
    l1 ++ [::e1] = l2 ++ [::e2] ->
    l1 = l2 /\ e1 = e2.
Proof.
  move => X l1 l2 e1 e2 H.
  assert (rev (l1 ++ [::e1]) = rev (l2 ++ [::e2])); first by rewrite H.
  repeat rewrite rev_cat in H0. inversion H0.
  rewrite - (revK l1). rewrite H3. split => //. by apply revK.
Qed.

(* TODO: Rename this lemma more appropriately *)
Lemma extract_list1 : forall {X:Type} (es: seq X) (e1 e2:X),
    es ++ [::e1] = [::e2] ->
    es = [::] /\ e1 = e2.
Proof.
  move => X es e1 e2 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma v_to_e_cat: forall vs1 vs2,
    list__val__admininstr vs1 ++ list__val__admininstr vs2 =
    list__val__admininstr (vs1 ++ vs2).
Proof.
  move => vs1. elim: vs1 => //=.
  - move => a l IH vs2. by rewrite IH.
Qed.

Lemma be_to_e_cat: forall bes1 bes2,
    list__instr__admininstr bes1 ++ list__instr__admininstr bes2 =
    list__instr__admininstr (bes1 ++ bes2).
Proof.
  move => bes1. elim: bes1 => //=.
  - move => a l IH bes2. by rewrite IH.
Qed.

Lemma to_e_list_cat: forall bes1 bes2,
    list__instr__admininstr (bes1 ++ bes2) = 
    list__instr__admininstr bes1 ++ list__instr__admininstr bes2.
Proof.
  induction bes1 => //.
  move => bes2. simpl. by f_equal.
Qed.

(* TODO: Move this to the top of this file *)
Lemma cat_split: forall {X: Type} (l l1 l2: seq X),
    l = l1 ++ l2 ->
    l1 = take (size l1) l /\
    l2 = drop (size l1) l.
Proof.
  move => X l l1.
  generalize dependent l.
  induction l1 => //=; move => l l2 HCat; subst => //=.
  - split. by rewrite take0. by rewrite drop0.
  - edestruct IHl1.
    instantiate (1 := l2). eauto.
    split => //.
    by f_equal.
Qed.

(* MEMO: reduce -> Step *)
Lemma reduce_composition: forall cs st es es0 st' es',
    const_list cs ->
    Step (config__ st es) (config__ st' es') ->
    Step (config__ st (cs ++ es ++ es0)) (config__ st' (cs ++ es' ++ es0)).
Proof.
  move => cs st es es0 st' es' HConst HReduce.
  move/const_es_exists: HConst => [vcs Heq].
  rewrite Heq.
  by apply: Step__ctxt_seq.
Qed.

Lemma reduce_composition_right: forall st es es0 st' es',
    Step (config__ st es) (config__ st' es') ->
    Step (config__ st (es ++ es0)) (config__ st' (es' ++ es0)).
Proof.
  move => st es es0 st' es' HReduce.
  eapply reduce_composition in HReduce.
  instantiate (1 := es0) in HReduce.
  instantiate (1 := [::]) in HReduce.
  - by simpl in HReduce.
  - by [].
Qed.

Lemma reduce_composition_left: forall st cs es st' es',
    const_list cs ->
    Step (config__ st es) (config__ st' es') ->
    Step (config__ st (cs ++ es)) (config__ st' (cs ++ es')).
Proof.
  move => st cs es st' es' HConst HReduce.
  eapply reduce_composition in HReduce; eauto.
  instantiate (1 := [::]) in HReduce.
  by repeat rewrite cats0 in HReduce.
Qed.

Lemma terminal_form_v_e: forall vs es,
    const_list vs ->
    terminal_form (vs ++ es) ->
    terminal_form es.
Proof.
  move => vs es HConst HTerm.
  unfold terminal_form in HTerm.
  destruct HTerm.
  - unfold terminal_form. left.
    apply const_list_split in H. by destruct H.
  - destruct vs => //=.
    + simpl in H. subst. unfold terminal_form. by right.
    + destruct vs => //=. destruct es => //=.
      simpl in H. inversion H. by subst.
Qed.

Lemma typeof_append: forall ts t vs,
    map typeof vs = ts ++ [:: t] ->
    exists v,
      vs = take (size ts) vs ++ [:: v] /\
      map typeof (take (size ts) vs) = ts /\
      typeof v = t.
Proof.
  move => ts t vs HMapType.
  apply cat_split in HMapType.
  destruct HMapType.
  rewrite -map_take in H.
  rewrite -map_drop in H0.
  destruct (drop (size ts) vs) eqn:HDrop => //=.
  destruct l => //=.
  inversion H0. subst.
  exists v.
  split => //.
  rewrite -HDrop. by rewrite cat_take_drop.
Qed.

(* NOTE: Given Hts : [seq typeof i  | i <- vcs] = [:: t],
         generates equalities on elements of vcs like [:: v1] = [:: t] and typeof v1 = t *)
Ltac invert_typeof_vcs :=
  lazymatch goal with
  | H: map typeof ?vcs = [:: _; _; _] |- _ =>
    let v1 := fresh "v1" in
    let v2 := fresh "v2" in 
    let v3 := fresh "v3" in 
    let v4 := fresh "v4" in 
    let vcs1 := fresh "vcs1" in
    let vcs2 := fresh "vcs2" in
    let vcs3 := fresh "vcs3" in
    let vcs4 := fresh "vcs4" in 
    let Ht1 := fresh "Ht1" in
    let Ht2 := fresh "Ht2" in
    let Ht3 := fresh "Ht3" in
    case: vcs H => [| v1 vcs1] H //=;
    case: vcs1 H => [| v2 vcs2] H //=;
    case: vcs2 H => [| v3 vcs3] H //=;
    case: vcs3 H => [| v4 vcs4] H //=;
    case: H => Ht1 Ht2 Ht3
  | H: map typeof ?vcs = [:: _; _] |- _ =>
    let v1 := fresh "v1" in
    let v2 := fresh "v2" in 
    let v3 := fresh "v3" in 
    let vcs1 := fresh "vcs1" in
    let vcs2 := fresh "vcs2" in
    let vcs3 := fresh "vcs3" in
    let Ht1 := fresh "Ht1" in
    let Ht2 := fresh "Ht2" in
    case: vcs H => [| v1 vcs1] H //=;
    case: vcs1 H => [| v2 vcs2] H //=;
    case: vcs2 H => [| v3 vcs3] H //=;
    case: H => Ht1 Ht2
  | H: map typeof ?vcs = [:: _] |- _ =>
    let v1 := fresh "v1" in
    let v2 := fresh "v2" in 
    let vcs1 := fresh "vcs1" in
    let vcs2 := fresh "vcs2" in
    let Ht1 := fresh "Ht1" in
    case: vcs H => [| v1 vcs1] H //=;
    case: vcs1 H => [| v2 vcs2] H //=;
    case: H => Ht1
  | H: map typeof ?vcs = [::] |- _ =>
    let v1 := fresh "v1" in 
    let vcs1 := fresh "vcs1" in
    (* NOTE: This performs injection on Hts : [seq typeof i  | i <- vcs] = [:: t1] *)
    case: vcs H => [| v1 vcs1] H //=
  end.

Ltac decidable_equality_step :=
  first [
      by apply: eq_comparable
    | apply: List.list_eq_dec
    (* | apply: Coqlib.option_eq *)
    | apply: PeanoNat.Nat.eq_dec
    | by eauto
    | intros; apply: decP; by (exact _ || eauto)
    | decide equality ].

(** Solve a goal of the form [forall a1 a2, {a1 = a2} + {a1 <> a2}]. **)
Ltac decidable_equality :=
  repeat decidable_equality_step.

Lemma eq_dec_Equality_axiom : forall t (eq_dec : forall x y : t, {x = y} + {x <> y}),
  let eqb v1 v2 := is_left (eq_dec v1 v2) in
  Equality.axiom eqb.
Proof.
  move=> t eq_dec eqb x y. rewrite /eqb. case: (eq_dec x y).
  - move=> E. by apply/ReflectT.
  - move=> E. by apply/ReflectF.
Qed.

(* TODO: Auto-generate these instances for each type *)
Definition functype_eq_dec : forall tf1 tf2 : functype,
  {tf1 = tf2} + {tf1 <> tf2}.
Proof. decidable_equality. Defined.

Definition functype_eqb v1 v2 : bool := functype_eq_dec v1 v2.
Definition eqfunctypeP : Equality.axiom functype_eqb :=
  eq_dec_Equality_axiom functype functype_eq_dec.

Canonical Structure functype_eqMixin := EqMixin eqfunctypeP.
Canonical Structure functype_eqType :=
  Eval hnf in EqType functype functype_eqMixin.

Definition admininstr_eq_dec : forall e1 e2 : admininstr,
  {e1 = e2} + {e1 <> e2}.
Admitted.
(* TODO: This does not terminate for some reason *)
(* Proof. decidable_equality. Defined. *)

Definition admininstr_eqb v1 v2 : bool := admininstr_eq_dec v1 v2.
Definition eqadmininstrP : Equality.axiom admininstr_eqb :=
  eq_dec_Equality_axiom admininstr admininstr_eq_dec.

Canonical Structure admininstr_eqMixin := EqMixin eqadmininstrP.
Canonical Structure admininstr_eqType :=
  Eval hnf in EqType admininstr admininstr_eqMixin.

(* NOTE: This is a temporary solution to ensure valtype matches corresponding val_
         There is no check that ensures valtype and val_ matches 
         and thus we cannot tell e.g. v3 is inn from typeof (val__CONST t3 v3) = valtype__INN inn__I32 *)
Definition val_wf (c : generatedcode.val): Prop :=
  match c with
      | val__CONST (valtype__INN inn) (val___inn__entry n) => True
      | val__CONST (valtype__FNN fnn) (val___fnn__entry n) => True
      | _ => False
  end.

Axiom val_wf_temp: forall (v : generatedcode.val), val_wf v.

Ltac invert_val_wf v :=
  let H := fresh "H" in
  let t := fresh "t" in
  let n := fresh "n" in
  let f := fresh "f" in
  let inn := fresh "inn" in
  let fnn := fresh "fnn" in
  have H := val_wf_temp v; rewrite /val_wf in H;
  (* TODO: Rewrite using case tactic somehow *)
  destruct v as [t v];
  destruct v as [v | v];
  destruct t as [inn | fnn] => //= {H}.

Lemma fun_testop_returns_inn_entry : forall t testop v c,
  fun_testop t testop v = c ->
  exists c', c = val___inn__entry c'.
Proof.
  move => t testop v c H.
  (* TODO: This is a bit tedious *)
  case: t H => [nn | nn] H;
  case: nn H => H;
  case: testop H => [arg | arg] H;
  case: arg H => H;
  case: v H => v' H;
  try rewrite /fun_testop /= in H;
  try rewrite /default_val /= in H;
  by eauto.
Qed.

Lemma fun_relop_returns_inn_entry : forall t relop v1 v2 c,
  fun_relop t relop v1 v2 = c ->
  exists c', c = val___inn__entry c'.
Proof.
  move => t relop v1 v2 c H.
  (* TODO: This is a bit tedious *)
  case: t H => [nn | nn] H;
  case: nn H => H;
  case: relop H => [arg | arg] H;
  do [ case: arg H => [ | | sx | sx | sx | sx ] H 
     | case: arg H => H ];
  case: v1 H => v1' H;
  case: v2 H => v2' H;
  try rewrite /fun_relop /= in H;
  try rewrite /default_val /= in H;
  by eauto.
Qed.

Lemma list_slice_size : forall {T : Type} (bs : seq T) i j,
  i + j <= size bs ->
  size (list_slice bs i j) = j.
Proof.
  move => T bs.
  elim: bs => [| b bs' IH].
  - move => /= i j H.
    have H' := leq_addl i j.
    move: (leq_trans H' H) => {}H.
    rewrite (leqn0 j) in H.
    by move/eqP in H.
  - move => /= i j H.
    case: i H => [| i'] H; case: j H => [| j'] H //=.
    + congr S. by apply: IH.
    + apply: IH.
      rewrite -[i'.+1]addn1 -[(size bs').+1]addn1 in H.
      rewrite -addnA -[1 + j'.+1]addnC addnA in H.
      by rewrite (leq_add2r 1) in H.
Qed.

Axiom fun_bytes_inverse : forall t bs,
  size bs = fun_size t / 8 ->
  exists c, fun_bytes t c = bs.

Axiom fun_ibytes_inverse : forall n bs,
  size bs = n / 8 ->
  exists c, fun_ibytes n c = bs.

(* NOTE: Mutual induction principle used in t_progress_be *)
Scheme Instr_ok_ind' := Induction for Instr_ok Sort Prop
  with Instrs_ok_ind' := Induction for Instrs_ok Sort Prop.

Definition br_reduce es := 
  exists vcs l es',
  es = list__val__admininstr vcs ++ [:: admininstr__BR l] ++ es'.

Definition return_reduce es :=
  exists vcs es',
  es = list__val__admininstr vcs ++ [:: admininstr__RETURN] ++ es'.

(* NOTE: We could define this as ~ (br_reduce es) *)
Definition not_lf_br es :=
  forall vcs l es',
  es <> list__val__admininstr vcs ++ [:: admininstr__BR l] ++ es'.

(* NOTE: We could define this as ~ (br_reduce es) *)
Definition not_lf_return es :=
  forall vcs es',
  es <> list__val__admininstr vcs ++ [:: admininstr__RETURN] ++ es'.

(* TODO: Define this in generatedcode.v *)
Fixpoint split_vals (es : seq admininstr) : seq (generatedcode.val) * seq admininstr :=
  match es with
  | (admininstr__CONST t v) :: es' =>
    let: (vs', es'') := split_vals es' in
    ((val__CONST t v) :: vs', es'')
  | _ => ([::], es)
  end.

Lemma split_vals_inverse : forall vs es es',
  split_vals es = (vs, es') ->
  es = list__val__admininstr vs ++ es'.
Proof.
  move => vs es es' H.
  move: vs es' H.
  elim: es => [ | e es' IH].
  - move => vs es' H.
    case: H => Hvs Hes'.
    by rewrite -Hvs -Hes'.
  - (* TODO: Using case tactic involves introducing constructor parameters of e
             which is tedious *)
    destruct e;
    try (move => vs es'' H;
         case: H => Hvs Hes'';
         by rewrite -Hvs -Hes'').
    move => vs es'' H.
    case Ees': (split_vals es') => [svs ses].
    rewrite /= Ees' in H.
    case: H => Hvs Hes''.
    move/IH: Ees' => {}IH.
    by rewrite -Hvs -Hes'' IH /=.
Qed.

Lemma split_vals_prefix : forall vs e es,
  (forall t v, e <> admininstr__CONST t v) ->
  split_vals (list__val__admininstr vs ++ [:: e] ++ es) = (vs, [:: e] ++ es).
Proof.
  move => vs e es H.
  elim: vs => [| v vs'].
  - case: e H => //=.
    move => t' v' Hcontra.
    by move/(_ t' v'): Hcontra.
  - case: v => /=.
    move => t' v' IH.
    by rewrite IH.
Qed.

Lemma br_reduce_decidable : forall es,
  decidable (br_reduce es).
Proof.
  rewrite /decidable /br_reduce.
  move => es.
  case Ees: (split_vals es) => [vs es'].
  case Ees': es' => [| e es''].
  - right. move => [vcs [l [es''' Hcontra]]].
    rewrite Hcontra in Ees.
    rewrite (split_vals_prefix vcs (admininstr__BR l) es''') in Ees; last by [].
    case: Ees => Hvs Hes'.
    by rewrite Ees' in Hes'.
  - (* TODO: Using case tactic involves introducing constructor parameters of e
             which is tedious *)
    destruct e;
    try (right;
         move => [vcs [l [es''' Hcontra]]];
         rewrite Hcontra in Ees;
         rewrite (split_vals_prefix vcs (admininstr__BR l) es''') in Ees; last by [];
         case: Ees => Hvs Hes';
         by rewrite Ees' in Hes').
    left. exists vs, v_labelidx, es''.
    rewrite /= -Ees'.
    by rewrite (split_vals_inverse _ _ _ Ees).
Qed.

Lemma not_br_reduce_not_lf_br : forall es,
  ~ (br_reduce es) -> not_lf_br es.
Proof.
  rewrite /br_reduce /not_lf_br.
  move => es H1 vcs l es' H2.
  apply: H1. by exists vcs, l, es'. 
Qed.

Lemma not_return_reduce_not_lf_return : forall es,
  ~ (return_reduce es) -> not_lf_return es.
Proof.
  rewrite /return_reduce /not_lf_return.
  move => es H1 vcs es' H2.
  apply: H1. by exists vcs, es'.
Qed.

Lemma not_lf_br_singleton : forall e l,
  not_lf_br [:: e] -> e <> admininstr__BR l.
Proof.
  move => e l H Hcontra.
  rewrite Hcontra /not_lf_br in H.
  by move/(_ [::] l [::]): H => H.
Qed.

Lemma not_lf_return_singleton : forall e,
  not_lf_return [:: e] -> e <> admininstr__RETURN.
Proof.
  move => e H Hcontra.
  rewrite Hcontra /not_lf_return in H.
  by move/(_ [::] [::]): H => H.
Qed.

(* TODO: Duplicate of composition_typing_single? *)
Lemma Instrs_ok_rcons : forall C bes be ts1 ts2, 
  Instrs_ok C (bes ++ [:: be]) (functype__ ts1 ts2) ->
  exists ts ts1' ts2' ts3,
    ts1 = ts ++ ts1' /\
    ts2 = ts ++ ts2' /\
    Instrs_ok C bes (functype__ ts1' ts3) /\
    Instr_ok C be (functype__ ts3 ts2').
Proof.
  move => C bes be ts1 ts2 Hinstrs.
  move Ebes': (bes ++ [:: be]) => bes'.
  move Etf: (functype__ ts1 ts2) => tf.
  rewrite Ebes' Etf in Hinstrs.
  move: bes be ts1 ts2 Ebes' Etf.
  (* NOTE: This is a type families syntax for elim tactic *)
  elim: C bes' tf / Hinstrs => [
    C | 
    C bes' be' ts1' ts2' ts3' Hinstrs IH Hinstrs' |
    C bes' ts ts1' ts2' Hinstrs IH ].
  - move => bes be ts1 ts2 Ebes' Etf.
    by case: bes Ebes'.
  - move => bes be ts1 ts2 Ebes' Etf.
    case: Etf => -> ->.
    move/(split_append_last _ _ _ _ ): Ebes' => [-> ->].
    by exists [::], ts1', ts2', ts3'.
  - move => bes be ts1 ts2 Ebes' Etf.
    move/(_ bes be ts1' ts2'): IH => IH.
    case: IH => //= [ts' [ts1'' [ts2'' [ts3'' [E1 [E2 [IH1 IH2]]]]]]].
    case: Etf => Etf1 Etf2. rewrite E1 E2 in Etf1 Etf2.
    exists (ts ++ ts'), ts1'', ts2'', ts3''.
    by rewrite -2!catA.
Qed.

(* TODO: Duplicate of admin_composition_typing_single? *)
Lemma Admin_instrs_ok_rcons : forall s C es e ts1 ts2,
  Admin_instrs_ok s C (es ++ [:: e]) (functype__ ts1 ts2) ->
  exists ts ts1' ts2' ts3,
    ts1 = ts ++ ts1' /\
    ts2 = ts ++ ts2' /\
    Admin_instrs_ok s C es (functype__ ts1' ts3) /\
    Admin_instr_ok s C e (functype__ ts3 ts2').
Proof.
  move => s C es e ts1 ts2 Hadmin.
  move Ees': (es ++ [:: e]) => es'.
  move Etf: (functype__ ts1 ts2) => tf.
  rewrite Ees' Etf in Hadmin.
  move: es e ts1 ts2 Ees' Etf.
  (* NOTE: This is a type families syntax for elim tactic *)
  elim: s C es' tf / Hadmin => [
    s C |
    s C es' e' ts1' ts2' ts3' Hadmin IH Hadmin' |
    s C es' ts ts1' ts2' Hadmin IH |
    s C es' tf Hinstrs ].
  - move => es e ts1 ts2 Ees' Etf.
    by move/cat_nil: Ees' => [Hes He].
  - move => es e ts1 ts2 Ees' Etf.
    case: Etf => -> ->.
    move/(split_append_last _ _ _ _ ): Ees' => [-> ->].
    by exists [::], ts1', ts2', ts3'.
  - move => es e ts1 ts2 Ees' Etf.
    move/(_ es e ts1' ts2'): IH => IH.
    case: IH => //= [ts' [ts1'' [ts2'' [ts3'' [E1 [E2 [IH1 IH2]]]]]]].
    case: Etf => Etf1 Etf2. rewrite E1 E2 in Etf1 Etf2.
    exists (ts ++ ts'), ts1'', ts2'', ts3''.
    by rewrite -2!catA.
  - move => es e ts1 ts2 Ees' Etf.
    rewrite /list__instr__admininstr in Ees'. symmetry in Ees'.
    (* TODO: View for move tactic doesn't work for some reason here *)
    (* TODO: Avoid using map_eq_app etc *)
    move: (map_eq_app _ _ _ _ Ees') => {Ees'} [bes [bes' [Ees' [Ebes Ebes']]]].
    move: (map_eq_cons _ _ Ebes') => {Ebes'} [be [bes'' [Ebes' [Ebe Ebes'']]]].
    move: (map_eq_nil _ _ Ebes'') => {}Ebes''.
    rewrite {}Ebes' {}Ebes'' in Ees'.
    rewrite -Ebes -Ebe.
    rewrite -/list__instr__admininstr in Ebes *.
    rewrite Ees' -Etf in Hinstrs.
    move: (Instrs_ok_rcons C bes be ts1 ts2 Hinstrs) => [ts' [ts1'' [ts2'' [ts3' [Ets1 [Ets2 [Hinstrs1 Hinstrs2]]]]]]].
    exists ts', ts1'', ts2'', ts3'.
    do ! split => //=.
    + by apply: Admin_instrs_ok__instrs.
    + by apply: Admin_instr_ok__instr.
Qed.
    
(* TODO: Duplicate ofadmin_composition_typing?  *)
Lemma Admin_instrs_ok_cat : forall s C es1 es2 ts1 ts2,
  Admin_instrs_ok s C (es1 ++ es2) (functype__ ts1 ts2) -> 
  exists ts ts1' ts2' ts3,
    ts1 = ts ++ ts1' /\
    ts2 = ts ++ ts2' /\
    Admin_instrs_ok s C es1 (functype__ ts1' ts3) /\
    Admin_instrs_ok s C es2 (functype__ ts3 ts2').
Proof.
  move => s C es1 es2 ts1 ts2 Hadmin.
  move: s C es1 ts1 ts2 Hadmin.
  (* NOTE: Induction on list es2 in reverse direction 
           which works better with Admin_instrs_ok__seq and Admin_instrs_ok_rcons *)
  elim/last_ind: es2 => [| es2' e2 IH].
  - move => s C es1 ts1 ts2 Hadmin.
    exists [::], ts1, ts2, ts2.
    do ! split => //=.
    + by rewrite cats0 in Hadmin.
    + rewrite -[ts2]cats0.
      apply: Admin_instrs_ok__frame.
      by apply: Admin_instrs_ok__empty.
  - move => s C es1 ts1 ts2 Hadmin.
    rewrite -cats1 catA in Hadmin *.
    move/Admin_instrs_ok_rcons: Hadmin => [ts [ts1' [ts2' [ts3 [Ets1 [Ets2 [Hadmin1 Hadmin2]]]]]]].
    move/(_ s C es1 ts1' ts3 Hadmin1): IH => [ts' [ts1'' [ts2'' [ts3' [Ets1' [Ets2' [Hadmin1' Hadmin2']]]]]]].
    move/(Admin_instrs_ok__frame _ _ _ ts'): Hadmin1' => Hadmin1'. rewrite 2!cat_app -Ets1' in Hadmin1'.
    move/(Admin_instrs_ok__frame _ _ _ ts'): Hadmin2' => Hadmin2'. rewrite 2!cat_app -Ets2' in Hadmin2'.
    move: (Admin_instrs_ok__seq _ _ _ e2 _ ts2' _ Hadmin2' Hadmin2) => {}Hadmin2'.
    exists ts, ts1', ts2', (ts' ++ ts3').
    by do ! split => //=.
Qed.

Lemma Admin_instrs_ok_all : forall s C es ts1 ts2,
  Admin_instrs_ok s C es (functype__ ts1 ts2) -> 
  forall e, e \in es -> exists ts1' ts2', Admin_instr_ok s C e (functype__ ts1' ts2').
Proof.
  (* TODO: Make use of `+` elsewhere *)
  move => + + es.
  elim/last_ind: es => [| es' e'].
  - move => s C ts1 ts2 Hadmin e Hin.
    by rewrite in_nil in Hin.
  - move => IH s C ts1 ts2 Hadmin e Hin.
    rewrite mem_rcons in_cons in Hin.
    rewrite -cats1 in Hadmin.
    move/Admin_instrs_ok_rcons: Hadmin => [ts [ts1' [ts2' [ts3 [Ets1 [Ets2 [Hadmin1 Hadmin2]]]]]]].
    move/orP: Hin => [Hin1 | Hin2].
    + move/eqP: Hin1 => Hin1.
      rewrite Hin1.
      by exists ts3, ts2'.
    + move/IH: Hadmin1 => {}IH. 
      by move/(_ e Hin2): IH => IH.
Qed.

Lemma s_typing_lf_br : forall s f es ts l,
  Thread_ok s None f es ts ->
  Forall (fun e => e <> admininstr__BR l) es.
Proof.
  move => s f es ts l Hthread.
  (* TODO: Get rid of subst *)
  inversion Hthread as [? ? ? ? ? ? Hframe Hadmin Hs Hrs Hf Hes Hts] => {Hthread} //=. subst.
  move/Admin_instrs_ok_all: Hadmin => Hadmin.
  elim: es Hadmin => [| e' es' IH] Hadmin;
  first by apply: Forall_nil.
  apply: Forall_cons.
  - move => Hcontra.
    have Hin : e' \in e' :: es'.
    { rewrite in_cons. apply/orP. by left. }
    move/(_ e' Hin): Hadmin => [ts1' [ts2' Hadmin]].
    rewrite Hcontra in Hadmin.
    (* TODO: Avoid using destruct/dependent induction *)
    Require Import Coq.Program.Equality.
    destruct e'; dependent induction Hadmin => //=.    
    (* TODO: Both goals generated by above has v_admininstr = admininstr__BR l
             H2 : Instr_ok in first goal and 
             H3 : Admin_instr_ok in second goal 
             to derive contradiction because context__LABELS has to be non empty for branch *)
    + have Hbr : v_instr = instr__BR l.
      { destruct v_instr; by inversion x. }
      rewrite Hbr in H.
      inversion H => //=.
      (* TODO: Contradiction in H4 : l < Datatypes.length
               Need to derive context__LABELS v_C = [::] when performing inversion Hthread,
               which holds because Frame_ok s f v_C and Module_instance_ok v_S v_moduleinst v_C *)
      simpl in H4.
      inversion Hframe.
      by admit.
    + apply: IHHadmin => //=.
      - by apply: Hframe.
      - by apply: IH.
  - apply: IH.
    move => e Hin.
    have Hin' : e \in e' :: es'.
    { rewrite in_cons. apply/orP. by right. }
    by move/(_ e Hin'): Hadmin => Hadmin.
Admitted.

Lemma s_typing_lf_return : forall s f es ts,
  Thread_ok s None f es ts ->
  Forall (fun e => forall l, e <> admininstr__BR l) es.
Proof.
Admitted.

(* Lemma br_reduce_extract_vs *)
(* TODO: Two major facts to be proven:
         1. v_n in admininstr__LABEL is equal to the length of types in
            context__LABELS of context used to validate admininstr__BR inside the label
         2. if vcs ++ admininstr__BR is well-typed then length of vcs must be
            greater than or equal to the length of types in context__LABELS of context
            used to validate vcs ++ admininstr__BR *)

(* Lemma return_reduce_extract_vs *)

(* MEMO: be_typing -> Instrs_ok *)
(* MEMO: f.(f_inst) -> f.(frame__MODULE) *)
(* TODO: Reorder premises in consistent order *)
Lemma t_progress_be: forall s C C' f vcs bes tf ts1 ts2 lab ret,
  Instrs_ok C bes tf ->
  tf = functype__ ts1 ts2 ->
  C = (upd_local_label_return C' (map typeof f.(frame__LOCALS)) lab ret) ->
  Module_instance_ok s f.(frame__MODULE) C' ->
  map typeof vcs = ts1 ->
  Store_ok s ->
  not_lf_br (list__instr__admininstr bes) ->
  not_lf_return (list__instr__admininstr bes) ->
  const_list (list__instr__admininstr bes) \/
  exists s' f' es', Step (config__ (state__ s f) (list__val__admininstr vcs ++ list__instr__admininstr bes)) (config__ (state__ s' f') es').
Proof.
  move => s C C' f vcs bes tf ts1 ts2 lab ret Hinstrs.
  move: s f C' vcs ts1 ts2 lab ret.
  apply Instrs_ok_ind' with 
    (P := fun C be tf (Hinstr : Instr_ok C be tf) => 
      forall s f C' vcs ts1 ts2 lab ret,
      tf = functype__ ts1 ts2 ->
      C = (upd_local_label_return C' (map typeof f.(frame__LOCALS)) lab ret) ->
      Module_instance_ok s f.(frame__MODULE) C' ->
      map typeof vcs = ts1 ->
      Store_ok s ->
      not_lf_br (list__instr__admininstr [:: be]) ->
      not_lf_return (list__instr__admininstr [:: be]) ->
      const_list (list__instr__admininstr [:: be]) \/
      exists s' f' es', Step (config__ (state__ s f) (list__val__admininstr vcs ++ list__instr__admininstr [:: be])) (config__ (state__ s' f') es'))
    (P0 := fun C bes tf (Hinstrs : Instrs_ok C bes tf) =>
      forall s f C' vcs ts1 ts2 lab ret,
      tf = functype__ ts1 ts2 ->
      C = (upd_local_label_return C' (map typeof f.(frame__LOCALS)) lab ret) ->
      Module_instance_ok s f.(frame__MODULE) C' ->
      map typeof vcs = ts1 ->
      Store_ok s ->
      not_lf_br (list__instr__admininstr bes) ->
      not_lf_return (list__instr__admininstr bes) ->
      const_list (list__instr__admininstr bes) \/
      exists s' f' es', Step (config__ (state__ s f) (list__val__admininstr vcs ++ list__instr__admininstr bes)) (config__ (state__ s' f') es'))
      => // {C bes tf Hinstrs}.
  - (* Instr_ok__nop *)
    move => C.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    (* TODO: Can we get rid of ++ [::] in exists? *)
    right. exists s, f, (list__val__admininstr vcs ++ [::] ++ [::]).
    apply Step__ctxt_seq with
      (v_admininstr := [:: admininstr__NOP]).
    by apply: Step__pure Step_pure__nop.
  - (* Instr_ok__unreachable *)
    move => C ts1 ts2.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    (* TODO: Can we get rid of ++ [::] in exists? *)
    right. exists s, f, (list__val__admininstr vcs ++ [:: admininstr__TRAP] ++ [::]).
    apply Step__ctxt_seq with
      (v_admininstr := [:: admininstr__UNREACHABLE]).
    by apply: Step__pure Step_pure__unreachable.
  - (* Instr_ok__drop *)
    move => C t.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    (* TODO: Replace injection in other places with case
              e.g. injection Htf => _ Htf1. rewrite -{}Htf1 in Hts. *)
    (* TODO: Use invert_typeof_vcs in t_progress_e too. *)
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    exists s, f, [::].
    apply: Step__pure.
    by apply: Step_pure__drop.
  - (* Instr_ok__select *)
    move => C t.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    invert_val_wf v3. rewrite /= in Ht3. rewrite Ht3.
    case: v3 => [| v3'].
    - exists s, f, (list__val__admininstr [:: v2]).
      apply: Step__pure.
      by apply: Step_pure__select_false.
    - exists s, f, (list__val__admininstr [:: v1]).
      apply: Step__pure.
      by apply: Step_pure__select_true.
  - (* Instr_ok__block *)
    move => C bt bes _ _.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right. exists s, f, [:: admininstr__LABEL_ (fun_optionSize bt) [::] (list__instr__admininstr bes)].
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    apply: Step__read. apply: Step_read__block.
    case: bt Hnotbr Hnotret => [bt |] Hnotbr Hnotret //=; by [right | left].
  - (* Instr_ok__loop *)
    move => C bt bes _ _.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right. exists s, f, [:: admininstr__LABEL_ (fun_optionSize bt) [:: instr__LOOP bt bes] (list__instr__admininstr bes)].
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    apply: Step__read. apply: Step_read__loop.
    case: bt Hnotbr Hnotret => [bt |] Hnotbr Hnotret //=; by [right | left].
  - (* Instr_ok__if *)
    move => C bt bes1 bes2 _ _ _ _.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    invert_val_wf v1. rewrite /= in Ht1. rewrite Ht1.
    case: v1 => [| v1'].
    - exists s, f, [:: admininstr__BLOCK bt bes2].
      apply: Step__pure.
      by apply: Step_pure__if_false.
    - exists s, f, [:: admininstr__BLOCK bt bes1].
      apply: Step__pure.
      by apply: Step_pure__if_true.
  - (* Instr_ok__br *)
    move => C l ts1 ts ts2 Hlablen Hlablookup.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    rewrite /not_lf_br /= in Hnotbr.
    inversion Hnotbr as [|? ? Hcontra].
    by move/(_ l): Hcontra.
  - (* Instr_ok__br_if *)
    move => C l ts Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -{}Htf1 in Hts.
    move/typeof_append: Hts => [v1 [Hvcs [Hts Ht1]]]. rewrite {}Hvcs.
    set vcs' := take (size (option_to_list ts)) vcs.
    invert_val_wf v1. rewrite /= in Ht1. rewrite Ht1.
    case: v1 => [| v1'].
    + exists s, f, (list__val__admininstr vcs').
      (* TODO: Can we get rid of these rewrites? *)
      have -> : forall vcs1 vcs2, list__val__admininstr (vcs1 ++ vcs2) = list__val__admininstr vcs1 ++ list__val__admininstr vcs2.
      { move => vcs1 vcs2. rewrite /list__val__admininstr. rewrite !map_map. by rewrite map_cat. }
      have -> : (list__val__admininstr vcs' ++ list__val__admininstr [:: val__CONST (valtype__INN inn__I32) (val___inn__entry 0)]) ++ [:: admininstr__BR_IF l] = list__val__admininstr vcs' ++ (list__val__admininstr [:: val__CONST (valtype__INN inn__I32) (val___inn__entry 0)] ++ [:: admininstr__BR_IF l]) ++ [::]. { by rewrite -2!catA cats0. }
      have {2}-> : list__val__admininstr vcs' = list__val__admininstr vcs' ++ [::] ++ [::]. { by rewrite 2!cats0. }
      (* TODO: This fails while vanilla tactic succeeds *)
      (* apply: Step__ctxt_seq. *)
      apply Step__ctxt_seq.
      apply: Step__pure.
      by apply: Step_pure__br_if_false.
    + exists s, f, (list__val__admininstr vcs' ++ [:: admininstr__BR l]).
      (* TODO: Can we get rid of these rewrites? *)
      have -> : forall vcs1 vcs2, list__val__admininstr (vcs1 ++ vcs2) = list__val__admininstr vcs1 ++ list__val__admininstr vcs2.
      { move => vcs1 vcs2. rewrite /list__val__admininstr. rewrite !map_map. by rewrite map_cat. }
      have -> : (list__val__admininstr vcs' ++ list__val__admininstr [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1'.+1)]) ++ [:: admininstr__BR_IF l] = list__val__admininstr vcs' ++ (list__val__admininstr [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1'.+1)] ++ [:: admininstr__BR_IF l]) ++ [::]. { by rewrite -2!catA cats0. }
      have -> : list__val__admininstr vcs' ++ [:: admininstr__BR l] = list__val__admininstr vcs' ++ [:: admininstr__BR l] ++ [::]. { by rewrite !cats0. }
      (* TODO: This fails while vanilla tactic succeeds *)
      (* apply: Step__ctxt_seq. *)
      apply Step__ctxt_seq.
      apply: Step__pure.
      by apply: Step_pure__br_if_true.
  - (* Instr_ok__br_table *)
    move => C ls lN ts1 ts ts2 HlenlN Hlenls HlookuplN Hlookupls.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -{}Htf1 in Hts.
    rewrite cat_app catA in Hts.
    move/typeof_append: Hts => [v1 [Hvcs [Hts Ht1]]]. rewrite {}Hvcs.
    set vcs' := take (size (ts1 ++ option_to_list ts)) vcs.
    invert_val_wf v1. rewrite /= in Ht1. rewrite Ht1.
    case Hv1: (v1 < size ls);
    move/ltP: Hv1 => Hv1.
    + exists s, f, (list__val__admininstr vcs' ++ [:: admininstr__BR (lookup_total ls v1)]).
      (* TODO: Can we get rid of these rewrites? *)
      have -> : forall vcs1 vcs2, list__val__admininstr (vcs1 ++ vcs2) = list__val__admininstr vcs1 ++ list__val__admininstr vcs2.
      { move => vcs1 vcs2. rewrite /list__val__admininstr. rewrite !map_map. by rewrite map_cat. }
      rewrite -catA.
      have -> : forall es1 es2 es3, es1 ++ es2 ++ es3 = es1 ++ (es2 ++ es3) ++ [::]. { move => T es1 es2 es3. by rewrite -catA cats0. }
      have -> : list__val__admininstr vcs' ++ [:: admininstr__BR (lookup_total ls v1)] = list__val__admininstr vcs' ++ [:: admininstr__BR (lookup_total ls v1)] ++ [::]. { by rewrite !cats0. }
      (* TODO: This fails while vanilla tactic succeeds *)
      (* apply: Step__ctxt_seq. *)
      apply Step__ctxt_seq.
      apply: Step__pure.
      apply: Step_pure__br_table_lt.
      by rewrite length_size.
    + exists s, f, (list__val__admininstr vcs' ++ [:: admininstr__BR lN]).
      (* TODO: Can we get rid of these rewrites? *)
      have -> : forall vcs1 vcs2, list__val__admininstr (vcs1 ++ vcs2) = list__val__admininstr vcs1 ++ list__val__admininstr vcs2.
      { move => vcs1 vcs2. rewrite /list__val__admininstr. rewrite !map_map. by rewrite map_cat. }
      rewrite -catA.
      have -> : forall es1 es2 es3, es1 ++ es2 ++ es3 = es1 ++ (es2 ++ es3) ++ [::]. { move => T es1 es2 es3. by rewrite -catA cats0. }
      have -> : list__val__admininstr vcs' ++ [:: admininstr__BR lN] = list__val__admininstr vcs' ++ [:: admininstr__BR lN] ++ [::]. { by rewrite !cats0. }
      (* TODO: This fails while vanilla tactic succeeds *)
      (* apply: Step__ctxt_seq. *)
      apply Step__ctxt_seq.
      apply: Step__pure.
      apply: Step_pure__br_table_ge.
      rewrite length_size.
      move/ltP: Hv1 => Hv1. apply/leP.
      by rewrite /ge leqNgt.
  - (* Instr_ok__call *)
    move => C x ts1 ts2 Haddr Hlookup.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    (* TODO: Can we get rid of ++ [::] in exists? *)
    right. exists s, f, (list__val__admininstr vcs ++ [:: admininstr__CALL_ADDR (lookup_total (fun_funcaddr (state__ s f)) x)] ++ [::]).
    (* TODO: Can we get rid of these rewrites? *)
    rewrite -[list__val__admininstr vcs ++ _]cats0 -catA.
    apply Step__ctxt_seq with
      (v_admininstr := [:: admininstr__CALL x]).
    apply: Step__read. apply: Step_read__call.
    rewrite !length_size in Haddr *.
    (* TODO: Extract this into a separate lemma *)
    have H1 : context__FUNCS C = context__FUNCS C'.
    { move => {Haddr Hlookup}.
      case: C Hcontext => ? ? ? ? ? ? ? ? Hcontext.
      case: C' Hcontext Hmod => ? ? ? ? ? ? ? ? Hcontext Hmod.
      inversion Hmod => /=. inversion Hcontext => /=. by []. }
    rewrite {}H1 in Haddr.
    (* TODO: Extract this into a separate lemma *)
    have H2 : size (context__FUNCS C') = size (fun_funcaddr (state__ s f)).
    { move => {Hcontext Haddr}.
      case: C' Hmod => ? ? ? ? ? ? ? ? Hmod.
      inversion Hmod as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hs Hf] => //=.
      by rewrite -Hf => //=. }
    by rewrite -{}H2.
  - (* Instr_ok__call_indirect *)
    move => C x ts1 ts2 Haddr Hlookup.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    (* TODO: Make use of typeof_append in t_progress_e too *)
    case: Htf => Htf1 _. rewrite -{}Htf1 in Hts.
    move/typeof_append: Hts => [v1 [Hvcs [Hts Ht1]]]. rewrite {}Hvcs.
    invert_val_wf v1. rewrite /= in Ht1. rewrite Ht1.
    case E1: (lookup_total (tableinst__REFS (fun_table (state__ s f) 0)) v1) => [a |].
    case E2: (fun_type (state__ s f) x == funcinst__TYPE (lookup_total (fun_funcinst (state__ s f)) a)).
    case E3: (v1 < Datatypes.length (tableinst__REFS (fun_table (state__ s f) 0))).
    case E4: (a < Datatypes.length (store__FUNCS s)).
    all: try move/eqP: E2 => E2;
          try move/ltP: E3 => E3;
          try move/ltP: E4 => E4.
    + exists s, f, (list__val__admininstr (take (size ts1) vcs) ++ [:: admininstr__CALL_ADDR a]).
      (* TODO: Can we get rid of these rewrites? *)
      have -> : (list__val__admininstr (take (size ts1) vcs ++ [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1)]) ++ [:: admininstr__CALL_INDIRECT x]) = (list__val__admininstr (take (size ts1) vcs) ++ (list__val__admininstr [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1)] ++ [:: admininstr__CALL_INDIRECT x]) ++ [::]).
      { rewrite cats0 catA. rewrite /list__val__admininstr. rewrite !map_map. rewrite map_cat. by []. }
      rewrite -[[:: admininstr__CALL_ADDR a]]cats0.
      apply Step__ctxt_seq with
        (v_admininstr := list__val__admininstr [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1)] ++ [:: admininstr__CALL_INDIRECT x]%list).
      apply: Step__read.
      apply: Step_read__call_indirect_call => //=.
    + exists s, f, (list__val__admininstr (take (size ts1) vcs) ++ [:: admininstr__TRAP]).
      (* TODO: Can we get rid of these rewrites? *)
      have -> : (list__val__admininstr (take (size ts1) vcs ++ [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1)]) ++ [:: admininstr__CALL_INDIRECT x]) = (list__val__admininstr (take (size ts1) vcs) ++ (list__val__admininstr [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1)] ++ [:: admininstr__CALL_INDIRECT x]) ++ [::]).
      { rewrite cats0 catA. rewrite /list__val__admininstr. rewrite !map_map. rewrite map_cat. by []. }
      rewrite -[[:: admininstr__TRAP]]cats0.
      apply Step__ctxt_seq with
        (v_admininstr := list__val__admininstr [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1)] ++ [:: admininstr__CALL_INDIRECT x]).
      apply: Step__read.
      apply: Step_read__call_indirect_trap.
      move => Hcontra.
      inversion Hcontra as [[s' f'] i' x' a' E3' E4' E1' E2' [Hs' Hf' Hi' Hx']].
      rewrite E1 in E1'. inversion E1' as [E1''].
      rewrite -E1'' in E4'.
      by move/E4: E4' => E4''.
    + exists s, f, (list__val__admininstr (take (size ts1) vcs) ++ [:: admininstr__TRAP]).
      (* TODO: Can we get rid of these rewrites? *)
      have -> : (list__val__admininstr (take (size ts1) vcs ++ [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1)]) ++ [:: admininstr__CALL_INDIRECT x]) = (list__val__admininstr (take (size ts1) vcs) ++ (list__val__admininstr [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1)] ++ [:: admininstr__CALL_INDIRECT x]) ++ [::]).
      { rewrite cats0 catA. rewrite /list__val__admininstr. rewrite !map_map. rewrite map_cat. by []. }
      rewrite -[[:: admininstr__TRAP]]cats0.
      apply Step__ctxt_seq with
        (v_admininstr := list__val__admininstr [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1)] ++ [:: admininstr__CALL_INDIRECT x]).
      apply: Step__read.
      apply: Step_read__call_indirect_trap.
      move => Hcontra.
      inversion Hcontra as [[s' f'] i' x' a' E3' E4' E1' E2' [Hs' Hf' Hi' Hx']].
      by move/E3: E3' => E3''.
    + exists s, f, (list__val__admininstr (take (size ts1) vcs) ++ [:: admininstr__TRAP]).
      (* TODO: Can we get rid of these rewrites? *)
      have -> : (list__val__admininstr (take (size ts1) vcs ++ [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1)]) ++ [:: admininstr__CALL_INDIRECT x]) = (list__val__admininstr (take (size ts1) vcs) ++ (list__val__admininstr [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1)] ++ [:: admininstr__CALL_INDIRECT x]) ++ [::]).
      { rewrite cats0 catA. rewrite /list__val__admininstr. rewrite !map_map. rewrite map_cat. by []. }
      rewrite -[[:: admininstr__TRAP]]cats0.
      apply Step__ctxt_seq with
        (v_admininstr := list__val__admininstr [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1)] ++ [:: admininstr__CALL_INDIRECT x]).
      apply: Step__read.
      apply: Step_read__call_indirect_trap.
      move => Hcontra.
      inversion Hcontra as [[s' f'] i' x' a' E3' E4' E1' E2' [Hs' Hf' Hi' Hx']].
      rewrite E1 in E1'. inversion E1' as [E1''].
      rewrite -E1'' in E2'.
      by move/E2: E2' => E2''.
    + exists s, f, (list__val__admininstr (take (size ts1) vcs) ++ [:: admininstr__TRAP]).
      (* TODO: Can we get rid of these rewrites? *)
      have -> : (list__val__admininstr (take (size ts1) vcs ++ [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1)]) ++ [:: admininstr__CALL_INDIRECT x]) = (list__val__admininstr (take (size ts1) vcs) ++ (list__val__admininstr [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1)] ++ [:: admininstr__CALL_INDIRECT x]) ++ [::]).
      { rewrite cats0 catA. rewrite /list__val__admininstr. rewrite !map_map. rewrite map_cat. by []. }
      rewrite -[[:: admininstr__TRAP]]cats0.
      apply Step__ctxt_seq with
        (v_admininstr := list__val__admininstr [:: val__CONST (valtype__INN inn__I32) (val___inn__entry v1)] ++ [:: admininstr__CALL_INDIRECT x]).
      apply: Step__read.
      apply: Step_read__call_indirect_trap.
      move => Hcontra.
      inversion Hcontra as [[s' f'] i' x' a' E3' E4' E1' E2' [Hs' Hf' Hi' Hx']].
      by rewrite E1 in E1'.
  - (* Instr_ok__return *)
    move => C ts1 ts ts2 Hretts.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    rewrite /not_lf_return /= in Hnotret.
    by inversion Hnotret.
  - (* Instr_ok__const *)
    move => C t vc.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    by left. 
  - (* Instr_ok__unop *)
    move => C t unop.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    case: v1 Ht1 => [t1 v1] /= Ht1. rewrite Ht1.
    case Eunop: (fun_unop t unop v1) => [c | ].
    + exists s, f, [:: admininstr__CONST t c].
      apply: Step__pure.
      by apply: Step_pure__unop_val.
    + exists s, f, [:: admininstr__TRAP].
      apply: Step__pure.
      by apply: Step_pure__unop_trap.
  - (* Instr_ok__binop *)
    move => C t binop.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    case: v1 Ht1 => [t1 v1] /= Ht1. rewrite Ht1.
    case: v2 Ht2 => [t2 v2] /= Ht2. rewrite Ht2.
    case Ebinop: (fun_binop t binop v1 v2) => [c | ].
    + exists s, f, [:: admininstr__CONST t c].
      apply: Step__pure.
      by apply: Step_pure__binop_val.
    + exists s, f, [:: admininstr__TRAP].
      apply: Step__pure.
      by apply: Step_pure__binop_trap.
  - (* Instr_ok__testop *)
    move => C t testop.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    case: v1 Ht1 => [t1 v1] /= Ht1. rewrite Ht1.
    move Etestop: (fun_testop t testop v1) => c.
    exists s, f, [:: admininstr__CONST (valtype__INN inn__I32) c].
    move/fun_testop_returns_inn_entry: (Etestop) => [c' Hc'].
    rewrite Hc'. rewrite Hc' in Etestop.
    apply: Step__pure.
    by apply: Step_pure__testop.
  - (* Instr_ok__relop *)
    move => C t relop.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right. 
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    case: v1 Ht1 => [t1 v1] /= Ht1. rewrite Ht1.
    case: v2 Ht2 => [t2 v2] /= Ht2. rewrite Ht2.
    move Erelop: (fun_relop t relop v1 v2) => c.
    exists s, f, [:: admininstr__CONST (valtype__INN inn__I32) c].
    move/fun_relop_returns_inn_entry: (Erelop) => [c' Hc'].
    rewrite Hc'. rewrite Hc' in Erelop.
    apply: Step__pure.
    by apply: Step_pure__relop.
  - (* Instr_ok__cvtop_reinterpret *)
    move => C t2' t1' Hsize.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    case: v1 Ht1 => [t1 v1] /= Ht1. rewrite Ht1.
    case Ecvtop: (fun_cvtop t1' t2' cvtop__REINTERPRET None v1) => [c | ].
    + exists s, f, [:: admininstr__CONST t2' c].
      apply: Step__pure.
      by apply: Step_pure__cvtop_val.
    + exists s, f, [:: admininstr__TRAP].
      apply: Step__pure.
      by apply: Step_pure__cvtop_trap.
  - (* Instr_ok__cvtop_convert_i *)
    move => C inn2 inn1 sx Hinn.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    case: v1 Ht1 => [t1 v1] /= Ht1. rewrite Ht1.
    case Ecvtop: (fun_cvtop (valtype__INN inn1) (valtype__INN inn2) cvtop__CONVERT sx v1) => [c | ].
    + exists s, f, [:: admininstr__CONST (valtype__INN inn2) c].
      apply: Step__pure.
      by apply: Step_pure__cvtop_val.
    + exists s, f, [:: admininstr__TRAP].
      apply: Step__pure.
      by apply: Step_pure__cvtop_trap.
  - (* Instr_ok__cvtop_convert_f *)
    move => C fnn2 fnn1.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    case: v1 Ht1 => [t1 v1] /= Ht1. rewrite Ht1.
    case Ecvtop: (fun_cvtop (valtype__FNN fnn1) (valtype__FNN fnn2) cvtop__CONVERT None v1) => [c | ].
    + exists s, f, [:: admininstr__CONST (valtype__FNN fnn2) c].
      apply: Step__pure.
      by apply: Step_pure__cvtop_val.
    + exists s, f, [:: admininstr__TRAP].
      apply: Step__pure.
      by apply: Step_pure__cvtop_trap.
  - (* Instr_ok__local_get *)
    move => C x t Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    exists s, f, (list__val__admininstr [:: fun_local (state__ s f) x]).
    apply: Step__read.
    by apply: Step_read__local_get.
  - (* Instr_ok__local_set *)
    move => C x t Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    (* TODO: Does set/pose tactic support destructuring? *)
    case Estate: (fun_with_local (state__ s f) x v1) => [s' f'].
    exists s', f', [::].
    rewrite -Estate.
    by apply: Step__local_set.
  - (* Instr_ok__local_tee *)
    move => C x t Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    exists s, f, [:: fun_coec_val__admininstr v1; fun_coec_val__admininstr v1; admininstr__LOCAL_SET x].
    apply: Step__pure.
    by apply: Step_pure__local_tee.
  - (* Instr_ok__global_get *)
    move => C x t mut Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    exists s, f, (list__val__admininstr [:: globalinst__VALUE (fun_global (state__ s f) x)]).
    apply: Step__read.
    by apply: Step_read__global_get.
  - (* Instr_ok__global_set *)
    move => C x t Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    (* TODO: Does set/pose tactic support destructuring? *)
    case Estate: (fun_with_global (state__ s f) x v1) => [s' f'].
    exists s', f', [::].
    rewrite -Estate.
    by apply: Step__global_set.
  - (* Instr_ok__memory_size *)
    move => C mt Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    (* TODO: This pose tactic cannot infer Inh_nat for some reason *)
    (* pose addr := (lookup_total (moduleinst__MEMS (frame__MODULE f)) 0). *)
    pose addr := (@lookup_total nat Inh_nat (moduleinst__MEMS (frame__MODULE f)) 0).
    inversion Hstore as [? ? ? ? meminsts ? ? ? memts ? ? ? ? Hs ? ? ? Hmem Hs'] => {Hs'}.
    have {}Hcontext : context__MEMS C = context__MEMS C'.
    { rewrite Hcontext. by case: C' Hcontext Hmod => *. }
    have {}Haddr : addr < size meminsts.
    { inversion Hmod as [? ? ? ? ? memaddrs ? ? ? ? ? ? ? ? Hmemaddrs ? ? ? ? Hext Hexp Hs' Hf HC'] => {Hexp Hs'}.
      rewrite /addr -Hf /=.
      (* TODO: Use all2 instead *)
      move/Forall2_lookup: Hext => [_ Hext].
      move/(_ 0): Hext => Hext.
      rewrite Hmemaddrs in Hext.
      rewrite Hcontext -HC' /= in Hlen.
      move/Hext: Hlen => {}Hext.
      inversion Hext as [| | ? ? ? ? ? Hlen' |].
      rewrite Hs length_size /= in Hlen'.
      by move/ltP: Hlen' => Hlen'. }
    have {}Hmem : Memory_instance_ok s (lookup_total meminsts addr) (lookup_total memts addr).
    { (* TODO: Use all2 instead *)
      move/Forall2_lookup: Hmem => [_ Hmem].
      move/(_ addr): Hmem => Hmem.
      move/ltP: Haddr => Haddr.
      rewrite length_size in Hmem.
      by move/(_ Haddr): Hmem => {}Hmem. }
    inversion Hmem as [? ? ? n ? ? Hlen' ? Hs' Hlookup' Hmt'] => {Hs' Hmt'}.
    exists s, f, [:: admininstr__CONST (valtype__INN inn__I32) (val___inn__entry n)].
    apply: Step__read.
    apply: Step_read__memory_size.
    rewrite length_size in Hlen'.
    rewrite /addr in Hlookup'.
    by rewrite length_size /fun_mem Hs -Hlookup' Hlen'.
  - (* Instr_ok__memory_grow *)
    move => C mt Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    invert_val_wf v1. rewrite /= in Ht1. rewrite Ht1.
    set meminst1 := (fun_mem (state__ s f) 0).
    (* TODO: Does set/pose tactic support destructuring? *)
    case Ememinst1: meminst1 => [[limn1 limm1] bs1].
    pose meminst2 := mkmeminst (limits__ (limn1 + v1) limm1) (bs1 ++ [:: byte__ 0]).
    (* TODO: Does set/pose tactic support destructuring? *)
    case Estate: (fun_with_meminst (state__ s f) 0 meminst2) => [s' f'].
    (* NOTE: We could just use Step__memory_grow_fail but
              we assume we can alway grow memory when it does not exceed predefined maximum size *)
    case Elimm1: (limn1 + v1 <= limm1).
    + exists s', f', [:: admininstr__CONST (valtype__INN inn__I32) (val___inn__entry (size (meminst__BYTES (fun_mem (state__ s f) 0)) / (64 * fun_Ki)%coq_nat))].
      rewrite -length_size -Estate.
      apply: Step__memory_grow_succeed.
      apply: (growmemory__ meminst1 v1 meminst2 limn1 limm1 bs1 (limn1 + v1)) => //=.
      by apply/leP.
    + exists s, f, [:: admininstr__CONST (valtype__INN inn__I32) (val___inn__entry (fun_invsigned 32 (0 - 1)%coq_nat))].
      by apply: Step__memory_grow_fail.
  - (* Instr_ok__load *)
    (* TODO: memop should be name as memarg *)
    move => C t n sx memop mt inn Hlen Hsize Hlookup Halign1 Halign2 Hinn.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    invert_val_wf v1. rewrite /= in Ht1. rewrite Ht1.
    case En: n => [n' |]; case Esx: sx => [sx' |].
    + (* NOTE: t of t.load is expected to be inn *)
      case: Hinn => [Hcontra | ->] //=; first by rewrite En in Hcontra.
      case Hcond: (((v1 + memop__OFFSET memop)%coq_nat + n' / 8)%coq_nat > size (meminst__BYTES (fun_mem (state__ s f) 0))).
      * move/ltP: Hcond => Hcond.
        exists s, f, [:: admininstr__TRAP].
        apply: Step__read.
        by apply: Step_read__load_pack_trap.
      * move/negbT: Hcond => Hcond.
        rewrite -leqNgt in Hcond.
        move/list_slice_size: Hcond => Hcond.
        move/fun_ibytes_inverse: Hcond => [c Hcond].
        exists s, f, [:: admininstr__CONST (valtype__INN inn) (fun_ext n' (fun_size (valtype__INN inn)) sx' c)].
        apply: Step__read.
        by apply: Step_read__load_pack_val.
    + move/Hsize: Esx => Hcontra.
      by rewrite En in Hcontra.
    + move/Hsize: En => Hcontra.
      by rewrite Esx in Hcontra.
    + case Hcond: (((v1 + memop__OFFSET memop)%coq_nat + fun_size t / 8)%coq_nat > size (meminst__BYTES (fun_mem (state__ s f) 0))).
      * move/ltP: Hcond => Hcond.
        exists s, f, [:: admininstr__TRAP].
        apply: Step__read.
        by apply: Step_read__load_num_trap.
      * move/negbT: Hcond => Hcond.
        rewrite -leqNgt in Hcond.
        move/list_slice_size: Hcond => Hcond.
        move/fun_bytes_inverse: Hcond => [c Hcond].
        exists s, f, [:: admininstr__CONST t c].
        apply: Step__read.
        by apply: Step_read__load_num_val.
  - (* Instr_ok__store *)
    (* TODO: memop should be name as memarg *)
    move => C t n memop mt inn Hlen Hlookup Halign1 Halign2 Hinn.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    invert_val_wf v1. rewrite /= in Ht1. rewrite Ht1.
    invert_val_wf v2. rewrite /= in Ht2. rewrite Ht2.
    + case En: n => [n' |].
      * (* NOTE: t of t.store is expected to be inn *)
        case: Hinn => [Hcontra | ->] //=; first by rewrite En in Hcontra.
        case Hcond: (((v1 + memop__OFFSET memop)%coq_nat + n' / 8)%coq_nat > size (meminst__BYTES (fun_mem (state__ s f) 0))).
        { move/ltP: Hcond => Hcond.
          exists s, f, [:: admininstr__TRAP].
          by apply: Step__store_pack_trap. }
        { set bs := fun_ibytes n' (fun_wrap (fun_size (valtype__INN inn)) n' v2).
          case Estate: (fun_with_mem (state__ s f) 0 (v1 + memop__OFFSET memop)%coq_nat (n' / 8) bs) => [s' f'].
          exists s', f', [::].
          rewrite -Estate.
          by apply: Step__store_pack_val. }
      * case Hcond: (((v1 + memop__OFFSET memop)%coq_nat + fun_size t / 8)%coq_nat > size (meminst__BYTES (fun_mem (state__ s f) 0))).
        { move/ltP: Hcond => Hcond.
          exists s, f, [:: admininstr__TRAP].
          by apply: Step__store_num_trap. }
        { set bs := fun_bytes t v2.
          case Estate: (fun_with_mem (state__ s f) 0 (v1 + memop__OFFSET memop)%coq_nat (fun_size t / 8) bs) => [s' f'].
          exists s', f', [::].
          rewrite -Estate.
          by apply: Step__store_num_val. }
    + case En: n => [n' |].
      * (* NOTE: t of t.store is expected to be inn *)
        case: Hinn => [Hcontra | Hinn] //=; first by rewrite En in Hcontra.
        by rewrite Hinn /= in Ht2.
      * case Hcond: (((v1 + memop__OFFSET memop)%coq_nat + fun_size t / 8)%coq_nat > size (meminst__BYTES (fun_mem (state__ s f) 0))).
        { move/ltP: Hcond => Hcond.
          exists s, f, [:: admininstr__TRAP].
          rewrite -Ht2 /= in Hcond *.
          by apply: Step__store_num_trap. }
        { set bs := fun_bytes t v2.
          case Estate: (fun_with_mem (state__ s f) 0 (v1 + memop__OFFSET memop)%coq_nat (fun_size t / 8) bs) => [s' f'].
          exists s', f', [::].
          rewrite -Estate /=.
          rewrite /bs -Ht2 /= in Hcond *.
          by apply: Step__store_num_val. }
  - (* Instrs_ok__empty *)
    move => C s.
    move => f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    by left.
  - (* Instrs_ok__seq *)
    move => C bes1 be2 ts1 ts2 ts3 Hinstrs1 IH1 Hinstr2 IH2.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    (* MEMO: This is failing because of Hnotbr and Hnotret in IH *)
    have Heqtf1 : functype__ ts1 ts3 = functype__ ts1 ts3 by [].
    have Heqts1 : ts1' = ts1 by inversion Htf.
    rewrite Heqts1 in Hts.
    rewrite cat_app -be_to_e_cat in Hnotbr Hnotret.
    move/not_lf_br_cat: Hnotbr => [Hnotbr1 Hnotbr2].
    move/not_lf_return_cat: Hnotret => [Hnotret1 Hnotret2].
    move: (IH1 s f C' vcs ts1 ts3 lab ret Heqtf1 Hcontext Hmod Hts Hstore Hnotbr1 Hnotret1) => {}IH1.
    case: IH1 => [Hconst1 | Hprog1].
    + move/const_es_exists: Hconst1 => [vs1 Hvs1].
      (* NOTE: Maybe we should make a separate lemma rather than reusing Val_Const_list_typing in Heqts2 *)
      have Hadmin1 : Admin_instrs_ok s C (list__instr__admininstr bes1) (functype__ ts1 ts3).
      { by apply: Admin_instrs_ok__instrs. }
      rewrite Hvs1 in Hadmin1 *.
      have Heqtf2 : functype__ ts3 ts2 = functype__ ts3 ts2 by [].
      have Heqts2 : map typeof (vcs ++ vs1) = ts3.
      { move/Val_Const_list_typing: Hadmin1 => Hadmin1.
        by rewrite Hadmin1 -Hts map_map map_cat. }
      move: (IH2 s f C' (vcs ++ vs1) ts3 ts2 lab ret Heqtf2 Hcontext Hmod Heqts2 Hstore Hnotbr2 Hnotret2) => {}IH2.
      case: IH2 => [Hconst2 | Hprog2].
      * left. rewrite -be_to_e_cat Hvs1.
        apply: const_list_concat => //=.
        by apply: v_to_e_const.
      * right.
        rewrite -v_to_e_cat -Hvs1 in Hprog2.
        by rewrite -catA be_to_e_cat in Hprog2.
    + right. move: Hprog1 => [s' [f' [es1' Hprog1]]].
      exists s', f', (es1' ++ list__instr__admininstr [:: be2]).
      rewrite -be_to_e_cat catA.
      by apply Step__ctxt_seq with (v_val := [::]).
  - (* Instrs_ok__frame *)
    move => C bes ts ts1 ts2 Hinstrs IH.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    (* NOTE: This should be named as Instrs_ok__weakening *)
    (* TODO: Get rid of duplicate proof *)
    have Heqtf : functype__ ts1 ts2 = functype__ ts1 ts2 by [].
    have Heqts : map typeof (drop (length ts) vcs) = ts1.
    { rewrite map_drop.
      injection Htf => Htf2 Htf1.
      rewrite -Hts in Htf1. by rewrite -Htf1 drop_cat length_size ltnn subnn drop0. }
    move: (IH s f C' (drop (length ts) vcs) ts1 ts2 lab ret Heqtf Hcontext Hmod Heqts Hstore Hnotbr Hnotret) => {}IH.
    have -> : vcs = (take (size ts) vcs ++ drop (size ts) vcs) by rewrite cat_take_drop.
    rewrite {}length_size in IH.
    set vcs1 := take (size ts) vcs in IH *.
    set vcs2 := drop (size ts) vcs in IH *.
    case: IH => [Hconst | Hprog].
    + by left.
    + right. move: Hprog => [s' [f' [es' IH]]].
      exists s', f', (list__val__admininstr vcs1 ++ es').
      rewrite -v_to_e_cat -catA.
      (* TODO: Can we get rid of these rewrites? *)
      rewrite -[list__val__admininstr vcs2 ++ _]cats0.
      rewrite -[list__val__admininstr vcs1 ++ es']cats0.
      rewrite -[(list__val__admininstr vcs1 ++ es') ++ [::]]catA.
      by apply Step__ctxt_seq with
        (v_admininstr := list__val__admininstr vcs2 ++ list__instr__admininstr bes)
        (v_admininstr' := es')
        (v_admininstr'' := [::]).
  (* TODO: These goals are shelved by Instr_ok__call_indirect for some reason *)
  Unshelve.
  - apply: Build_Inhabited.
    by apply: None.
  - apply: Build_Inhabited.
    pose functype := functype__ [::] [::].
    pose modinst := mkmoduleinst [::] [::] [::] [::] [::] [::].
    pose func := func__FUNC 0 [::] [::].
    by apply: (mkfuncinst functype modinst func).
Qed.

(* TODO: Similar to admin_instrs_ok_eq *)
Lemma Instr_ok_Instrs_ok: forall C be tf,
  Instr_ok C be tf -> Instrs_ok C [:: be] tf.
Proof.
  move => C be tf Hinstr.
  rewrite -[[:: be]]cat0s.
  case: tf Hinstr => [ts1 ts2] Hinstr.
  apply Instrs_ok__seq with (v_t_2 := ts1) => //=.
  apply: instrs_weakening_empty_both.
  by apply: Instrs_ok__empty.
Qed.

(* NOTE: Mutual induction principle used in t_progress_e *)
Scheme Admin_instr_ok_ind' := Induction for Admin_instr_ok Sort Prop
  with Admin_instrs_ok_ind' := Induction for Admin_instrs_ok Sort Prop
  with Thread_ok_ind' := Induction for Thread_ok Sort Prop.

(* MEMO: AI_local -> Admininstr__FRAME_ *)
(* MEMO: e_typing -> Admin_instrs_ok *)
(* MEMO: store_typing -> Store_ok *)
(* MEMO: reduce -> Step *)
(* MEMO: reduce -> Step_read *)
(* NOTE: lholed is no longer used in specifying opsem
         Use evaluation context E directly *)
(* TODO: Reorder premises in consistent order *)
Lemma t_progress_e: forall s C C' f vcs es tf ts1 ts2 lab ret,
  Admin_instrs_ok s C es tf ->
  tf = functype__ ts1 ts2 ->
  C = (upd_local_label_return C' (map typeof f.(frame__LOCALS)) lab ret) ->
  Module_instance_ok s f.(frame__MODULE) C' ->
  map typeof vcs = ts1 ->
  Store_ok s ->
  (* not_lf_br_outside es -> *)
  (* not_lf_return es -> *)
  terminal_form (list__val__admininstr vcs ++ es) \/
  exists s' f' es', Step (config__ (state__ s f) (list__val__admininstr vcs ++ es)) (config__ (state__ s' f') es').
Proof.
  move => s C C' f vcs es tf ts1 ts2 lab ret Hadmin.
  move: f C' vcs ts1 ts2 lab ret.
  apply Admin_instrs_ok_ind' with 
    (P := fun s C e tf (Hadmin : Admin_instr_ok s C e tf) => 
      forall f C' vcs ts1 ts2 lab ret,
      tf = functype__ ts1 ts2 ->
      C = (upd_local_label_return C' (map typeof f.(frame__LOCALS)) lab ret) ->
      Module_instance_ok s f.(frame__MODULE) C' ->
      map typeof vcs = ts1 ->
      Store_ok s ->
      (* not_lf_br_outside [:: e] -> *)
      (* not_lf_return [:: e] -> *)
      terminal_form (list__val__admininstr vcs ++ [:: e]) \/
      exists s' f' es', Step (config__ (state__ s f) (list__val__admininstr vcs ++ [:: e])) (config__ (state__ s' f') es'))
    (P0 := fun s C es tf (Hadmin : Admin_instrs_ok s C es tf) => 
      forall f C' vcs ts1 ts2 lab ret,
      tf = functype__ ts1 ts2 ->
      C = (upd_local_label_return C' (map typeof f.(frame__LOCALS)) lab ret) ->
      Module_instance_ok s f.(frame__MODULE) C' ->
      map typeof vcs = ts1 ->
      Store_ok s ->
      (* not_lf_br_outside es -> *)
      (* not_lf_return es -> *)
      terminal_form (list__val__admininstr vcs ++ es) \/
      exists s' f' es', Step (config__ (state__ s f) (list__val__admininstr vcs ++ es)) (config__ (state__ s' f') es'))
    (P1 := fun s rs f es ts (Hthread : Thread_ok s rs f es ts) =>
      Store_ok s ->
      (* not_lf_br_outside es -> *)
      (* not_lf_return es -> *)
      (const_list es /\ length es = length ts) \/
      es = [::admininstr__TRAP] \/
      exists s' f' es', Step (config__ (state__ s f) es) (config__ (state__ s' f') es')) 
    => // {s C es tf Hadmin}.
  - (* Admin_instr_ok__instr *)
    move => s C be tf Hinstr.
    move => f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore.
    have Hinstrs: Instrs_ok C [:: be] tf by apply Instr_ok_Instrs_ok.
    pose Hprog := t_progress_be s C C' f vcs [:: be] tf ts1 ts2 lab ret Hinstrs Htf Hcontext Hmod Hts Hstore.
    case: Hprog => [Hconst | Hprog].
    + left. rewrite /terminal_form.
      left. apply: const_list_concat => //=.
      by apply: v_to_e_const.
    + by right. 
  - (* Admin_instr_ok__trap *)
    move => s C ts1 ts2.
    move => f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore.
    case: vcs Hts => [| vc vcs] Hts //=.
    + left. rewrite /terminal_form. by right.
    + right. exists s, f, [:: admininstr__TRAP].
      apply: Step__pure.
      apply Step_pure__trap_vals with (v_val := vc :: vcs).
      by left. 
  - (* Admin_instr_ok__call_addr *)
    (* NOTE: admininstr__CALL_ADDR corresponds to invoke instruction *)
    move => s C addr ts1 ts2 Hext.
    move => f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore.
    right.
    injection Htf => _ Htf1. rewrite -{}Htf1 in Hts.
    inversion Hext as [? ? ? inst func Haddr Hlookup Hs Ha Htf' | | | ] => //=.
    case Hfunc: func Hlookup => [x ls es] Hlookup.
    pose ts := map (fun '(local__LOCAL t) => t) ls.
    pose f' := (mkframe (vcs ++ (map fun_default_ ts)) inst).
    exists s, f, [:: admininstr__FRAME_ (size ts2) f' [:: admininstr__LABEL_ (size ts2) [::] (list__instr__admininstr es)]].
    apply: Step__read.
    eapply Step_read__call_addr with 
      (v_t_1 := ts1) (v_t_2 := ts2)
      (v_mm := inst) (v_func := func) => //=.
    - by rewrite Hfunc.
    - by rewrite -Hts 2!length_size size_map. 
    - by case: ts2 Hext Htf Htf' Hlookup.
    - rewrite Hfunc. congr func__FUNC.
      rewrite /ts {ts f'} map_map.
      (* TODO: Extract this into a separate lemma *)
      elim: ls {Hfunc Hlookup} => [| l ls IH] => //=.
      rewrite -IH. congr cons.
      by case: l.
  - (* Admin_instr_ok__label *)
    move => s C n bes es t1 t2 Hinstrs Hadmin IH Hsize.
    move => f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore.
    (* TODO: Can we simplify this? *)
    have Heqc : _append {|
      context__TYPES := [::];
      context__FUNCS := [::];
      context__GLOBALS := [::];
      context__TABLES := [::];
      context__MEMS := [::];
      context__LOCALS := [::];
      context__LABELS := [:: t2];
      context__RETURN := None
      |} C = upd_local_label_return C' [seq typeof i  | i <- frame__LOCALS f] (t2 :: lab) ret.
      by rewrite Hcontext.
    have Heqtf : functype__ [::] (option_to_list t1) = functype__ [::] (option_to_list t1) by [].
    have Heqts : map typeof [::] = [::] by [].
    move: (IH f C' [::] [::] (option_to_list t1) (t2 :: lab) ret Heqtf Heqc Hmod Heqts Hstore) 
      => {Heqtf Heqc Hmod Heqts Hstore} {}IH.
    case: IH => [Hterm | Hprog].
    + right. exists s, f, (list__val__admininstr vcs ++ es).
      (* TODO: Can we get rid of these rewrites? *)
      rewrite -[list__val__admininstr vcs ++ _]cats0.
      rewrite -[list__val__admininstr vcs ++ es]cats0.
      rewrite -2!catA.
      apply Step__ctxt_seq with
        (v_admininstr := [:: admininstr__LABEL_ n bes es])
        (v_admininstr' := es).
      case: Hterm => /= [Hconst | Htrap].
      * move: (const_es_exists _ Hconst) => [vs Hvs]. rewrite Hvs.
        apply: Step__pure.
        by apply: Step_pure__label_vals.
      * rewrite Htrap.
        apply: Step__pure.
        by apply: Step_pure__trap_label.
    + right. move: Hprog => [s' [f' [es' IH]]].
      exists s', f', (list__val__admininstr vcs ++ [:: admininstr__LABEL_ n bes es']).
      apply Step__ctxt_seq with 
        (v_admininstr := [:: admininstr__LABEL_ n bes es])
        (v_admininstr' := [:: admininstr__LABEL_ n bes es']).
      by apply: Step__ctxt_label.
  - (* Admin_instr_ok__frame *)
    move => s C n f es t Hthread IH Hsize.
    move => f' C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore.
    move: (IH Hstore) => {Hstore} {}IH.
    case: IH => [[Hconst Hlen] | [Htrap | Hprog]].
    + right. exists s, f', (list__val__admininstr vcs ++ es).
      (* TODO: Can we get rid of these rewrites? *)
      rewrite -[list__val__admininstr vcs ++ _]cats0.
      rewrite -[list__val__admininstr vcs ++ es]cats0.
      rewrite -2!catA.
      apply Step__ctxt_seq with 
        (v_admininstr := [:: admininstr__FRAME_ n f es])
        (v_admininstr' := es).
      move: (const_es_exists _ Hconst) => [vs Hvs]. rewrite Hvs.
      apply: Step__pure.
      by apply: Step_pure__frame_vals.
    + right. rewrite Htrap.
      exists s, f', (list__val__admininstr vcs ++ [:: admininstr__TRAP]).
      apply Step__ctxt_seq with
        (v_admininstr := [:: admininstr__FRAME_ n f [:: admininstr__TRAP]])
        (v_admininstr' := [:: admininstr__TRAP]).
      apply: Step__pure.
      by apply: Step_pure__trap_frame.
    + right. move: Hprog => [s' [f'' [es' Hprog]]].
      exists s', f', (list__val__admininstr vcs ++ [:: admininstr__FRAME_ n f'' es']).
      apply Step__ctxt_seq with
        (v_admininstr := [:: admininstr__FRAME_ n f es])
        (v_admininstr' := [:: admininstr__FRAME_ n f'' es']).
      by apply: Step__ctxt_frame.
  - (* Admin_instr_ok__weakening *)
    move => s C e ts ts1 ts2 Hadmin IH.
    move => f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore.
    have Heqtf : functype__ ts1 ts2 = functype__ ts1 ts2 by [].
    have Heqts : map typeof (drop (length ts) vcs) = ts1.
    { rewrite map_drop.
      injection Htf => Htf2 Htf1.
      rewrite -Hts in Htf1. by rewrite -Htf1 drop_cat length_size ltnn subnn drop0. }
    move: (IH f C' (drop (length ts) vcs) ts1 ts2 lab ret Heqtf Hcontext Hmod Heqts Hstore) => {}IH.
    have -> : vcs = (take (size ts) vcs ++ drop (size ts) vcs) by rewrite cat_take_drop.
    rewrite length_size in IH.
    set vcs1 := take (size ts) vcs in IH *.
    set vcs2 := drop (size ts) vcs in IH *.
    case: IH => [Hterm | Hprog].
    + case: Hterm => [Hconst | Htrap].
      * left. left.
        (* TODO: v_to_e_cat should be used elsewhere when applying Step__ctxt_seq *)
        rewrite -v_to_e_cat -catA.
        apply: const_list_concat => //=.
        by apply: v_to_e_const.
      * rewrite -v_to_e_cat -catA Htrap.
        case: vcs1 => [| vc1 vcs1] //=.
        -- left. by right.
        -- right. exists s, f, [:: admininstr__TRAP].
           apply: Step__pure.
           apply Step_pure__trap_vals with (v_val := (vc1 :: vcs1)).
           by left.
    + right. move: Hprog => [s' [f' [es' IH]]].
      exists s', f', (list__val__admininstr vcs1 ++ es').
      rewrite -v_to_e_cat -catA.
      (* TODO: Can we get rid of these rewrites? *)
      rewrite -[list__val__admininstr vcs2 ++ _]cats0.
      rewrite -[list__val__admininstr vcs1 ++ es']cats0.
      rewrite -[(list__val__admininstr vcs1 ++ es') ++ [::]]catA.
      by apply Step__ctxt_seq with
        (v_admininstr := list__val__admininstr vcs2 ++ [:: e])
        (v_admininstr' := es')
        (v_admininstr'' := [::]).
  - (* Admin_instrs_ok__empty *)
    move => s C.
    move => f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore.
    left. rewrite cats0 /terminal_form.
    left. by apply: v_to_e_const.
  - (* Admin_instrs_ok__seq *)
    move => s C es1 e2 ts1 ts2 ts3 Hadmin1 IH1 Hadmin2 IH2.
    move => f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore.
    have Heqtf1 : functype__ ts1 ts3 = functype__ ts1 ts3 by [].
    have Heqts1 : ts1' = ts1 by inversion Htf.
    rewrite Heqts1 in Hts.
    move: (IH1 f C' vcs ts1 ts3 lab ret Heqtf1 Hcontext Hmod Hts Hstore) => {}IH1.
    case: IH1 => [Hterm1 | Hprog1].
    + case: Hterm1 => [Hconst1 | Htrap1].
      * move/const_list_split: Hconst1 => [Hconst1 Hconst2].
        move/const_es_exists: Hconst2 => [vs1 Hvs1].
        rewrite Hvs1 in Hadmin1 *.
        have Heqtf2 : functype__ ts3 ts2 = functype__ ts3 ts2 by [].
        have Heqts2 : map typeof (vcs ++ vs1) = ts3.
        { move/Val_Const_list_typing: Hadmin1 => Hadmin1.
          by rewrite Hadmin1 -Hts map_map map_cat. }
        move: (IH2 f C' (vcs ++ vs1) ts3 ts2 lab ret Heqtf2 Hcontext Hmod Heqts2 Hstore) => {}IH2.
        case: IH2 => [Hterm2 | Hprog2].
        { case: Hterm2 => [Hconst2 | Htrap2].
          - left. left.
            by rewrite -v_to_e_cat -catA in Hconst2.
          - left. right.
            move: (extract_list1 _ _ _ Htrap2) => [Hvcs He].
            rewrite catA v_to_e_cat Hvcs He /=. 
            by rewrite /terminal_form. }
        { right. by rewrite catA v_to_e_cat. }
      * right. move: (v_e_trap _ _ (v_to_e_const vcs) Htrap1) => [-> ->] //=.
        exists s, f, [:: admininstr__TRAP].
        apply: Step__pure.
        apply Step_pure__trap_vals with (v_val := [::]).
        by right.
    + right. move: Hprog1 => [s' [f' [es1' Hprog1]]].
      exists s', f', (es1' ++ [:: e2]).
      rewrite catA.
      by apply Step__ctxt_seq with (v_val := [::]).
  - (* Admin_instrs_ok__frame *)
    move => s C es ts ts1 ts2 Hadmin IH.
    move => f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore.
    (* NOTE: This is equivalent to Admin_instr_ok__weakening but for Admin_instrs_ok *)
    (* TODO: Get rid of duplicate proof *)
    have Heqtf : functype__ ts1 ts2 = functype__ ts1 ts2 by [].
    have Heqts : map typeof (drop (length ts) vcs) = ts1.
    { rewrite map_drop.
      injection Htf => Htf2 Htf1.
      rewrite -Hts in Htf1. by rewrite -Htf1 drop_cat length_size ltnn subnn drop0. }
    move: (IH f C' (drop (length ts) vcs) ts1 ts2 lab ret Heqtf Hcontext Hmod Heqts Hstore) => {}IH.
    have -> : vcs = (take (size ts) vcs ++ drop (size ts) vcs) by rewrite cat_take_drop.
    rewrite {}length_size in IH.
    set vcs1 := take (size ts) vcs in IH *.
    set vcs2 := drop (size ts) vcs in IH *.
    case: IH => [Hterm | Hprog].
    + case: Hterm => [Hconst | Htrap].
      * left. left.
        rewrite -v_to_e_cat -catA.
        apply const_list_concat => //=.
        by apply v_to_e_const.
      * rewrite -v_to_e_cat -catA Htrap.
        case: vcs1 => /= [| vc1 vcs1].
        { left. by right. }
        { right. exists s, f, [:: admininstr__TRAP].
          apply: Step__pure.
          apply Step_pure__trap_vals with (v_val := (vc1 :: vcs1)).
          by left. }
    + right. move: Hprog => [s' [f' [es' IH]]].
      exists s', f', (list__val__admininstr vcs1 ++ es').
      rewrite -v_to_e_cat -catA.
      (* TODO: Can we get rid of these rewrites? *)
      rewrite -[list__val__admininstr vcs2 ++ _]cats0.
      rewrite -[list__val__admininstr vcs1 ++ es']cats0.
      rewrite -[(list__val__admininstr vcs1 ++ es') ++ [::]]catA.
      by apply Step__ctxt_seq with
        (v_admininstr := list__val__admininstr vcs2 ++ es)
        (v_admininstr' := es')
        (v_admininstr'' := [::]).
  - (* Admin_instrs_ok__instrs *)
    (* NOTE: This is equivalent to Admin_instr_ok__instr but for Admin_instrs_ok *)
    (* TODO: Get rid of duplicate proof *)
    move => s C bes tf Hinstrs.
    move => f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore.
    pose Hprog := t_progress_be s C C' f vcs bes tf ts1 ts2 lab ret Hinstrs Htf Hcontext Hmod Hts Hstore.
    case: Hprog => [Hconst | Hprog].
    + left. rewrite /terminal_form.
      left. apply: const_list_concat => //=.
      by apply: v_to_e_const.
    + by right. 
  - (* Thread_ok__ *)
    move => s rs f es ts C.
    move => Hframe Hadmin IH Hstore.
    have Heqtf : functype__ [::] ts = functype__ [::] ts by [].
    have Heqts : map typeof [::] = [::] by [].
    (* TODO: Remove duplicate proof *)
    have Heq1 : context__LOCALS C = map typeof (frame__LOCALS f).
    { inversion Hframe as [? ? ? ? ? ? Hmod Hval].
      inversion Hmod => //=. rewrite cat_app cats0.
      (* TODO: Use all2 instead *)
      by apply Forall2_Val_ok_is_same_as_map in Hval. }
    have Heq2 : context__LABELS C = [::].
    { inversion Hframe as [? ? ? ? ? ? Hmod]. by inversion Hmod. }
    have Heq3 : context__RETURN C = None.
    { inversion Hframe as [? ? ? ? ? ? Hmod]. by inversion Hmod. }
    (* TODO: Can we simplify this? *)
    have Heqc : _append {|
        context__TYPES := [::];
        context__FUNCS := [::];
        context__GLOBALS := [::];
        context__TABLES := [::];
        context__MEMS := [::];
        context__LOCALS := [::];
        context__LABELS := [::];
        context__RETURN := Some rs
      |} C = upd_local_label_return (upd_local C [::]) [seq typeof i  | i <- frame__LOCALS f] [::] (Some rs).
    { move => {IH Hframe Hadmin}.
      case: C Heq1 Heq2 Heq3 => //= ? ? ? ? ? ? ? ? Heq1 Heq2 Heq3.
      by rewrite -Heq1 Heq2 Heq3. }
    have Hmod : Module_instance_ok s (frame__MODULE f) (upd_local C [::]).
    { inversion Hframe as [? ? ? ? ? ? Hmod] => {Hframe} //=.
      by inversion Hmod. }
    move: (IH f (upd_local C [::]) [::] [::] ts [::] (Some rs) Heqtf Heqc Hmod Heqts Hstore) => {}IH {Heqtf Heqc}.
    case: IH => /= [Hterm | Hprog].
    + case: Hterm => [Hconst | Htrap].
      * left. split => //=.
        move/const_es_exists: Hconst => [vs Hvs].
        rewrite Hvs in Hadmin *.
        move/Val_Const_list_typing: Hadmin => /= ->.
        by rewrite 2!length_size map_map 2!size_map.
      * right. left. by rewrite Htrap.
    + right. by right.
Qed.

Theorem t_progress: forall s f es ts,
  Config_ok (config__ (state__ s f) es) ts ->
  terminal_form es \/
  exists s' f' es', Step (config__ (state__ s f) es) (config__ (state__ s' f') es').
Proof.
  move => s f es ts Hconfig.
  inversion Hconfig as [? ? ? ? Hstore Hthread]; subst.
  inversion Hthread as [? ? ? ? ? C Hframe Hadmin]; subst.
  eapply t_progress_e with
    (lab := [::]) (ret := Some None)
    (vcs := [::]) (ts1 := [::]) (ts2 := ts)
    (C' := upd_local_label_return C [::] [::] None) => //=.
  - (* TODO: Name these lemmas explicitly *)
    have Heq1 : context__LOCALS C = map typeof (frame__LOCALS f).
    { inversion Hframe as [? ? ? ? ? ? Hmod Hval].
      inversion Hmod => //=. rewrite cat_app cats0.
      (* TODO: Use all2 instead *)
      by apply Forall2_Val_ok_is_same_as_map in Hval. }
    have Heq2 : context__LABELS C = [::].
    { inversion Hframe as [? ? ? ? ? ? Hmod]. by inversion Hmod. }
    have Heq3 : context__RETURN C = None.
    { inversion Hframe as [? ? ? ? ? ? Hmod]. by inversion Hmod. }
    by rewrite -Heq1 -Heq2 -Heq3 {Heq1 Heq2 Heq3}.
  - inversion Hframe as [? ? ? ? ? ? Hmod] => {Hframe}.
    by inversion Hmod.
Qed.