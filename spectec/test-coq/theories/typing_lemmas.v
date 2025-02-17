From Coq Require Import String List Unicode.Utf8.
From RecordUpdate Require Import RecordSet.
Require Import NArith.
Require Import Arith.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.
From WasmSpectec Require Import generatedcode helper_lemmas helper_tactics.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq.

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

Definition typeof (v_val : val): valtype :=
	match v_val with
		| val__CONST t _ => t
	end.
	
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
		simpl. injection H3 as H10. subst. 
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
					fun_optionSize ts = n /\
                    Admin_instrs_ok v_S (upd_label v_C ([ts] ++ (context__LABELS v_C))) v_admininstrs (functype__ [] ts2').
Proof.
	move => v_S v_C n v_instrs v_admininstrs ts1 ts2 HType.
	gen_ind_subst HType => //=.
		- (* Instr *) inversion H; subst; try discriminate.
		- (* Label *) destruct H as [? [? ?]]. exists v_t_1, v_t_2. repeat split => //=.
		- (* Weakening *) edestruct IHHType as [? [? [? [? ?]]]] => //=; subst. exists x, x0. by repeat split => //=; try rewrite <- app_assoc.
Qed.

Lemma Frame_typing: forall v_S v_C n v_F v_ais t1s t2s,
    Admin_instr_ok v_S v_C (admininstr__FRAME_ n v_F v_ais) (functype__ t1s t2s) ->
    exists (ts : resulttype), t2s = t1s ++ ts /\
               Thread_ok v_S ts v_F v_ais ts /\ 
			   (n = (fun_optionSize ts)). 
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

Lemma Break_typing: forall n v_S v_C t1s t2s,
	Admin_instr_ok v_S v_C (admininstr__BR n) (functype__ t1s t2s) ->
	exists ts ts0, 
				(n < length (context__LABELS v_C))%coq_nat /\
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
	- (* Call Addr *) inversion H; destruct H4. subst. rewrite -H5 in H3. injection H3 as ?. subst. inversion HST; decomp.
		apply Forall2_lookup in H8; destruct H8.
		rewrite H7 in H4. simpl in H4.
		apply H12 in H4.
		rewrite  H7 in H5.
		simpl in H5.
		rewrite -H5 in H4.
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
	- (* Load *) inversion H; subst; try discriminate; destruct H4 as [? [? [? [? [? ?]]]]]; 
		injection H3 as ?; exists [], v_n, v_sx, v_inn, v_mt; subst; repeat split => //=.
		- (* Load 0 *) by left.
		- (* Load 1 *) by right.
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
	- (* Store *) inversion H; subst; try discriminate; destruct H4 as [? [? [? [? ?]]]];
		injection H3 as ?; exists v_n, v_mt, v_inn; subst; repeat split => //=.
		- by left.
		- by right.
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

