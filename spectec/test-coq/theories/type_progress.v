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
(* From WasmSpectec Require Import type_preservation. *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq.

(* NOTE: Naming conventions:
         1. type for types
         2. type__constructor for types with multiple constructors
         3. type__ for types with a single constructor *)

(* NOTE: Comment out below to display coercions in proof state *)
(* Set Printing Coercions. *)
(* NOTE: Comment out below to display parentheses in proof state *)
(* Set Printing Parentheses. *)

(* TODO: Get rid of coercion functions *)
Fixpoint lfill (lh : E) (es : list admininstr) : list admininstr :=
  match lh with
  | E___HOLE_ => es
  | E___SEQ vs lh' es' => (list__val__admininstr vs) ++ (lfill lh' es) ++ (list__instr__admininstr es')
  | E__LABEL_ n es' lh' => [admininstr__LABEL_ n es' (lfill lh' es)]
  end.

Definition lh_push_back_es (es0 : list instr) (lh: E): E :=
  match lh with
  | E___HOLE_ => E___HOLE_
  | E___SEQ vs lh' es => E___SEQ vs lh' (es ++ es0)
  | E__LABEL_ n es lh' => E__LABEL_ n es lh'
  end.

Lemma lfill_push_back_es : forall (lh: E) (es : list admininstr) (es0 : list instr),
    lfill (lh_push_back_es es0 lh) es = lfill lh es ++ list__instr__admininstr es0.
Proof.
  (* move => lh es es0.
  destruct lh; simpl in * => //; by repeat rewrite -catA => //. *)
Admitted.

Definition is_const (e : admininstr) : bool :=
  if e is admininstr__CONST _ _ then true else false.

Definition const_list (es : list admininstr) : bool :=
  List.forallb is_const es.

(* NOTE: const_list es is coerced into proposition by is_true *)
Definition terminal_form (es : list admininstr) :=
  const_list es \/ es = [:: admininstr__TRAP].

Lemma const_list_cat: forall vs1 vs2,
    const_list (vs1 ++ vs2) = const_list vs1 && const_list vs2.
Proof.
  move => vs1 vs2.
  repeat rewrite cat_app.
  unfold const_list.
  by rewrite List.forallb_app.
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

(* TODO: There may be an equivalent lemma in ssreflect *)
Lemma map_nonempty {A B : Type} (f: A -> B) (l: seq A) :
  seq.map f l <> [] → l <> [].
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
  eapply Step_pure__trap_vals with (v_val := vcs) (v_instr := [::]) => //=.
  rewrite /list__val__admininstr in H.
  left. by apply/map_nonempty: H.
Qed.

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
  apply const_es_exists in HConst as [vcs Heq].
  Check Step__ctxt_label.
  (* TODO: What corresponds to r_label in this case?  *)
  (* eapply r_label with (lh := LH_base vcs es0) => //=; eauto; by rewrite - Heq => //. *)
Admitted.

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

Lemma terminal_trap: terminal_form [:: admininstr__TRAP].
Proof.
  unfold terminal_form. by right.
Qed.

(* NOTE: This lemma will not be useful since admininstr does not contain instr *)
(* Lemma e_b_inverse: forall es,
    es_is_basic es ->
    to_e_list (to_b_list es) = es.
Proof.
  move => es HAI_basic.
  by erewrite e_b_elim; eauto.
Qed. *)

Lemma typeof_append: forall ts t vs,
    map typeof vs = ts ++ [::t] ->
    exists v,
      vs = take (size ts) vs ++ [::v] /\
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
  rewrite -HDrop.
  (* TODO: For some reason this rewrite fails *)
  (* by rewrite cat_take_drop. *)
  symmetry. apply cat_take_drop.
Qed.

(* TODO: This hint for auto might not work as expected *)
Hint Constructors Step_pure : core.
(* Hint Constructors reduce_simple : core. *)
(* Hint Constructors opsem.reduce_simple : core. *)

Ltac invert_typeof_vcs :=
  lazymatch goal with
  | H: map typeof ?vcs = [::_; _; _] |- _ =>
    destruct vcs => //=; destruct vcs => //=; destruct vcs => //=; destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  | H: map typeof ?vcs = [::_; _] |- _ =>
    destruct vcs => //=; destruct vcs => //=; destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  | H: map typeof ?vcs = [::_] |- _ =>
    destruct vcs => //=; destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  | H: map typeof ?vcs = [::] |- _ =>
    destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  end.

Lemma nth_error_map: forall {X Y:Type} (l: seq X) n f {fx: Y},
    List.nth_error (map f l) n = Some fx ->
    exists x, List.nth_error l n = Some x /\
    f x = fx.
Proof.
  move => X Y l n.
  generalize dependent l.
  induction n => //; move => l f fx HN.
  - destruct l => //=.
    simpl in HN. inversion HN. subst. by eauto.
  - destruct l => //=.
    simpl in HN. by apply IHn.
Qed.

Definition not_lf_br (es : list admininstr) :=
  forall k (lh: E), lfill lh [:: admininstr__BR k] <> es.

Definition not_lf_br_outside (es : list admininstr) :=
  (* TODO: How should we express this with E? *)
  (* (forall n (lh: lholed n) k, lfill lh [:: admininstr__BR k] = es -> k < n) -> *)
  forall (lh : E) k, lfill lh [:: admininstr__BR k] = es -> k < 999.

Definition not_lf_return (es: list admininstr) :=
  forall (lh : E), lfill lh [:: admininstr__RETURN] <> es.

(* 
Lemma nlfbr_right: forall es es',
    not_lf_br (es ++ list__instr__admininstr es') ->
    not_lf_br es.
Proof.
  unfold not_lf_br.
  move => es es' HNLF k lh HContra.
  subst es.
  Set Printing Coercions.
  (* TODO: Why does this rewrite fail? *)
  (* rewrite -(lfill_push_back_es lh [:: admininstr__BR k] es') in HNLF. *)
  rewrite -lfill_push_back_es in HNLF.
  by eapply HNLF.
Qed.

Lemma nlfret_right: forall es n es',
    not_lf_return (es ++ es') n ->
    not_lf_return es n.
Proof.
  unfold not_lf_return.
  move => es n es' HNLF lh HContra.
  subst es.
  rewrite -lfill_push_back_es in HNLF.
  by eapply HNLF.
Qed.

Lemma nlfbr_left: forall es n cs vcs,
    cs = v_to_e_list vcs ->
    not_lf_br (cs ++ es) n ->
    not_lf_br es n.
Proof.
  unfold not_lf_br.
  move => es n vcs cs -> IH k lh ?.
  subst es.
  erewrite <- lfill_push_front_vs in IH; eauto.
  by eapply IH.
Qed.

Lemma nlfret_left: forall es n cs vcs,
    cs = v_to_e_list vcs ->
    not_lf_return (cs ++ es) n ->
    not_lf_return es n.
Proof.
  unfold not_lf_return.
  move => es n vcs cs -> IH lh ?.
  subst es.
  erewrite <- lfill_push_front_vs in IH; eauto.
  by eapply IH.
Qed.

Ltac auto_basic :=
  repeat lazymatch goal with
  | |- es_is_basic [::AI_basic _; AI_basic _; AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- es_is_basic [::AI_basic _; AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- es_is_basic [::AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- es_is_basic [::AI_basic _] =>
    simpl; repeat split
  | |- e_is_basic (AI_basic ?e) =>
    by unfold e_is_basic; exists e
  end.

(** A common scheme in the progress proof, with a continuation. **)
Ltac solve_progress_cont cont :=
  repeat eexists;
  solve [
      apply r_simple; solve [ eauto | constructor; eauto | cont; eauto ]
    | cont ].

(** The same, but without continuation. **)
Ltac solve_progress :=
  solve_progress_cont ltac:(fail). *)

(* MEMO: be_typing -> Instrs_ok *)
(* MEMO: f.(f_inst) -> f.(frame__MODULE) *)
Lemma t_progress_be: forall C bes ts1 ts2 vcs lab ret s f,
    Store_ok s ->
    Module_instance_ok s f.(frame__MODULE) C ->
    Instrs_ok (upd_label (upd_local_return C (map typeof f.(frame__LOCALS)) ret) lab) bes (functype__ ts1 ts2) ->
    map typeof vcs = ts1 ->
    not_lf_br (list__instr__admininstr bes) ->
    not_lf_return (list__instr__admininstr bes) ->
    const_list (list__instr__admininstr bes) \/
    exists s' f' es', Step (config__ (state__ s f) (list__val__admininstr vcs ++ list__instr__admininstr bes)) (config__ (state__ s' f') es').
Proof.

(* MEMO: s_typing -> Thread_ok *)
Lemma s_typing_lf_br: forall s rs f es ts,
  Thread_ok s rs f es ts ->
  not_lf_br_outside es.
Proof.
Admitted.

(* MEMO: s_typing -> Thread_ok *)
Lemma s_typing_lf_return: forall s f es ts,
  Thread_ok s None f es ts ->
  not_lf_return es.
Proof.
Admitted.

(* NOTE: Mutual induction principle used in t_progress_e *)
Scheme Admin_instrs_ok_ind' := Induction for Admin_instrs_ok Sort Prop
  with Thread_ok_ind' := Induction for Thread_ok Sort Prop.

(* MEMO: AI_local -> Admininstr__FRAME_ *)
(* MEMO: e_typing -> Admin_instrs_ok *)
(* MEMO: store_typing -> Store_ok *)
(* MEMO: reduce -> Step *)
(* MEMO: reduce -> Step_read *)
(* NOTE: lholed is no longer used in specifying opsem
         Use evaluation context E directly *)
Lemma t_progress_e: forall s C C' f vcs es tf ts1 ts2 lab ret,
  Admin_instrs_ok s C es tf ->
  tf = functype__ ts1 ts2 ->
  C = (upd_label (upd_local_return C' (map typeof f.(frame__LOCALS)) ret) lab) ->
  Module_instance_ok s f.(frame__MODULE) C' ->
  map typeof vcs = ts1 ->
  Store_ok s ->
  not_lf_br_outside es ->
  not_lf_return es ->
  terminal_form (list__val__admininstr vcs ++ es) \/
  exists s' f' es', Step (config__ (state__ s f) (list__val__admininstr vcs ++ es)) (config__ (state__ s' f') es').
Proof.
Admitted.

Theorem t_progress: forall s f es ts,
  Config_ok (config__ (state__ s f) es) ts ->
  terminal_form es \/
  exists s' f' es', Step (config__ (state__ s f) es) (config__ (state__ s' f') es').
Proof.
Admitted.
