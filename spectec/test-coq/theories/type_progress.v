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
  eapply Step_pure__trap_vals with (v_val := vcs) (v_admininstr := [::]) => //=.
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
    Instrs_ok (upd_local_label_return C (map typeof f.(frame__LOCALS)) lab ret) bes (functype__ ts1 ts2) ->
    map typeof vcs = ts1 ->
    (* not_lf_br (list__instr__admininstr bes) -> *)
    (* not_lf_return (list__instr__admininstr bes) -> *)
    const_list (list__instr__admininstr bes) \/
    exists s' f' es', Step (config__ (state__ s f) (list__val__admininstr vcs ++ list__instr__admininstr bes)) (config__ (state__ s' f') es').
Proof.
Admitted.

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

Lemma instr_ok_instrs_ok: forall C be tf,
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
    => //= {s C es tf Hadmin}.
  - (* Admin_instr_ok__instr *)
    move => s C be tf Hinstr.
    move => f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hconst Hstore.
    have Hinstrs: Instrs_ok C [:: be] tf by apply instr_ok_instrs_ok.
    rewrite Htf Hcontext in Hinstrs.
    pose Hprog := t_progress_be C' [:: be] ts1 ts2 vcs lab ret s f Hstore Hmod Hinstrs Hconst.
    case: Hprog => Hprog.
    + left. rewrite /terminal_form.
      left. case be in *; inversion Hprog.
      apply const_list_concat => //=.
      by apply v_to_e_const.
    + by right. 
  - (* Admin_instr_ok__trap *)
    move => s C es tf Hadmin.
    by admit.
  - (* Admin_instr_ok__call_addr *)
    by admit.
  - (* Admin_instr_ok__label *)
    by admit.
  - (* Admin_instr_ok__frame *)
    by admit.
  - (* Admin_instr_ok__weakening *)
    by admit.
  - (* Admin_instrs_ok__empty *)
    by admit.
  - (* Admin_instrs_ok__seq *)
    by admit.
  - (* Admin_instrs_ok__frame *)
    by admit.
  - (* Thread_ok__ *)
    by admit.
Admitted.

Theorem t_progress: forall s f es ts,
  Config_ok (config__ (state__ s f) es) ts ->
  terminal_form es \/
  exists s' f' es', Step (config__ (state__ s f) es) (config__ (state__ s' f') es').
Proof.
  move => s f es ts Hconfig.
  inversion Hconfig as [? ? ? ? Hstore Hthread]. subst.
  
  Print Thread_ok.
  inversion Hthread as [? ? ? ? ? C Hframe Hadmin]. subst.
  pose C' := upd_local_label_return C [::] [::] None.
  eapply t_progress_e with
    (vcs := [::]) (lab := [::]) (ret := Some None)
    (ts2 := ts) (C' := C') => //=.
  - rewrite -upd_return_is_same_as_append in Hadmin.
    rewrite /_append /Append_Option /option_append in Hadmin.
    suff Heqc:
      (upd_return C (Some None)) =
      (upd_local_label_return C' (map typeof (frame__LOCALS f)) [::] (Some None)).
    + by rewrite -Heqc.
    + have Heq1 : context__LOCALS C = map typeof (frame__LOCALS f).
      { inversion Hframe as [? ? ? ? ? ? Hmod Hval] => {Hframe} //=.
        inversion Hmod => //=. rewrite List.app_nil_r.
        by apply Forall2_Val_ok_is_same_as_map in Hval. }
      have Heq2 : context__LABELS C = [::].
      { inversion Hframe as [? ? ? ? ? ? Hmod] => {Hframe} //=.
        by inversion Hmod => //=. }
      have Heq3 : context__RETURN C = None.
      { inversion Hframe as [? ? ? ? ? ? Hmod] => {Hframe} //=.
        by inversion Hmod => //=. }
      case HeqC': C'. inversion HeqC'. subst.
      rewrite -Heq1 -Heq2 -Heq3 {Heq1 Heq2 Heq3}.
      by rewrite /upd_local_return /upd_local /upd_return.
  - clear Hstore Hthread Hadmin.
    inversion Hframe as [? ? ? ? ? ? Hmod] => {Hframe} //=. subst.
    case v_C in *. inversion Hmod => //=.
Qed.