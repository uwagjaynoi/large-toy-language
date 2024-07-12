Definition nf : tm -> Prop := normal_form step.

Theorem nf_if_value (t : tm) : value t -> nf t.
Proof.
  intros vt. induction vt; intros [t' st]; iac st; unfold not in *; eauto.
Qed.

(* Working Line *)

Ltac find_value_step :=
  match goal with
  Hv : value ?t,
  Hs : ?t --> ?t'
  |- _ => exfalso; apply (nf_if_value t Hv (ex_intro _ t' Hs)) end.

Ltac find_value_step_aggr :=
  match goal with
  Hs : ?t --> ?t'
  |- _ => exfalso; assert (Hv : value t); [eauto | apply (nf_if_value t Hv (ex_intro _ t' Hs))] end.


Theorem determinism (t t1 t2 : tm) : t --> t1 -> t --> t2 -> t1 = t2.
Proof.
  (* generalize dependent t2. generalize dependent t1.
  induction t; intros t1' t2' S1 S2; iac S1; iac S2; f_equal; try(reflexivity); try(solve_by_invert); eauto; try(find_value_step); try(find_value_step_aggr). *)

  intros Ht1. generalize dependent t2.
  induction Ht1; let tname:= fresh"t2" in intros tname Ht2;
  iac Ht2; try(reflexivity); try(solve_by_invert); try(find_value_step); f_equal; eauto; try(find_value_step_aggr).
Qed.

Lemma nf_multi_refl (t1 t2 : tm) : nf t1 -> t1 -->* t2 -> t1 = t2.
Proof.
  intros. unfold nf in *; iac H0; [eauto| exfalso; eauto].
Qed.

Theorem multi_det (t t1 t2 : tm) : t -->* t1 -> t -->* t2 -> nf t1 -> nf t2 -> t1 = t2.
Proof.
  intros H1 H2 H3 H4. generalize dependent t2.
  induction H1.
  - intros. eapply nf_multi_refl; eauto.
  - specialize (IHmulti H3). intros. iac H2.
  + exfalso; eauto.
  + assert (Heq := determinism _ _ _ H H0). subst. eauto.
Qed.

Theorem multi_pre : forall t1 t2 T, t1 -->* t2 -> empty |-- t1 \in T -> empty |-- t2 \in T.
Proof.
  intros t1 t2 T H. induction H; eauto.
  intros. apply IHmulti. eapply preservation; eauto.
Qed.

Ltac get_prog t :=
  match goal with
  H : empty |-- t \in ?T
  |- _ =>
    let Hv := fresh"Hv" in
    let t'n := fresh"t'" in
    let Hp := fresh"H" in
    destruct (progress t T H) as [Hv | [t'n Hp]]; (discuss_value || clear H) end.
Ltac locate_has_type :=
  repeat match goal with
  H : empty |-- ?t \in ?T
  |- _ => get_prog t; eauto end.

Theorem value_if_nf_ty : forall t T, empty |-- t \in T -> nf t -> value t.
Proof with eauto.
  induction t; intros T HT Hnf.
  13: {
    remember empty as Gamma.
    remember <{t1 :: t2}> as t.
    generalize dependent t1. generalize dependent t2.
    generalize dependent HeqGamma. induction HT;
    intros; subst; try(discriminate).
    injection Heqt as Heq1 Heq2. subst.
    econstructor.
    - eapply IHt1...
      intros [t' Hs]...
    - get_prog t3...
    + eapply IHt2...
      intros [t' Hs]...
    + exfalso...
  }
  all:
  iac HT;
  try(discriminate);
  try(econstructor; unfold nf in *; eauto; fail);
  try(exfalso; locate_has_type; fail).
  - exfalso. locate_has_type; destruct n...
  - locate_has_type; exfalso...
  - locate_has_type; exfalso...
  - locate_has_type; econstructor; eauto; exfalso; eauto...
Qed.

Inductive limit_tm : tm -> Prop :=
  | nf_var : forall (x : string), limit_tm <{x}>
  | nf_app : forall t1 t2, limit_tm t1 -> limit_tm t2 -> limit_tm <{t1 t2}>
  | nf_abs : forall x T t, limit_tm t -> limit_tm <{\x:T, t}>
  (* | nf_const : forall (n : nat), limit_tm <{n}>
  | nf_succ : forall t, limit_tm t -> limit_tm <{succ t}>
  | nf_pred : forall t, limit_tm t -> limit_tm <{pred t}>
  | nf_mult : forall t1 t2, limit_tm t1 -> limit_tm t2 -> limit_tm <{t1 * t2}>
  | nf_if0 : forall t1 t2 t3, limit_tm t1 -> limit_tm t2 -> limit_tm t3 -> limit_tm <{if0 t1 then t2 else t3}>
  | nf_inl : forall t T2, limit_tm t -> limit_tm <{inl T2 t}>
  | nf_inr : forall t T1, limit_tm t -> limit_tm <{inr T1 t}>
  | nf_case : forall t0 x1 t1 x2 t2, limit_tm t0 -> limit_tm t1 -> limit_tm t2 -> limit_tm <{case t0 of | inl x1 => t1 | inr x2 => t2}>
  | nf_nil : forall T, limit_tm <{nil T}>
  | nf_cons : forall t1 t2, limit_tm t1 -> limit_tm t2 -> limit_tm <{t1 :: t2}>
  | nf_lcase : forall t1 t2 x1 x2 t3, limit_tm t1 -> limit_tm t2 -> limit_tm t3 -> limit_tm <{case t1 of | nil => t2 | x1 :: x2 => t3}> *)
  | nf_unit : limit_tm <{unit}>
  (* | nf_pair : forall t1 t2, limit_tm t1 -> limit_tm t2 -> limit_tm <{(t1, t2)}>
  | nf_fst : forall t, limit_tm t -> limit_tm <{t.fst}>
  | nf_snd : forall t, limit_tm t -> limit_tm <{t.snd}>
  | nf_let : forall x t1 t2, limit_tm t1 -> limit_tm t2 -> limit_tm <{let x=t1 in t2}>. *)
  .

Inductive limit_ty : ty -> Prop :=
  | lty_arrow T1 T2 : limit_ty T1 -> limit_ty T2 -> limit_ty (Ty_Arrow T1 T2)
  | lty_unit : limit_ty Ty_Unit.

Theorem type_unique t : forall Gamma T1 T2, Gamma |-- t \in T1 -> Gamma |-- t \in T2 -> T1 = T2.
Proof.
  induction t; intros Gamma T1 T2 HT1 HT2;
  iac HT1; iac HT2; f_equal; eauto.
  - rewrite H1 in H2. injection H2. eauto.
  - specialize (IHt1 _ _ _ H2 H3).
    injection IHt1; eauto.
  - admit.
  - admit.
  - admit.
  - specialize (IHt1 _ _ _ H4 H6). subst. eauto.
  - specialize (IHt _ _ _ H1 H2). injection IHt. eauto.
Admitted.

Definition normalizing (t : tm) := exists t', t -->* t' /\ nf t'.

Definition context_value := list (string * tm * ty).

Fixpoint cond_cv (l : context_value) : Prop :=
  match l with
  | nil => True
  | cons (x, t, T) l' => (empty |-- t \in T /\ value t) /\ cond_cv l'
  end.

Fixpoint content_cv (l : list (string * tm * ty)): context :=
  match l with
  | nil => empty
  | cons (x, _, T) l' => (x |-> T; content_cv l')
  end.

Fixpoint substm (l : list (string * tm * ty)) (t : tm) : tm :=
  match l with
  | nil => t
  | cons (y, yt, _) yt' => substm yt' <{[y:=yt]t}>
  end.

(* Fixpoint emptyProp1 (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Arrow T1 T2 => forall v, value v -> emptyProp1 T1 v -> emptyProp1 T2 <{t v}>
  | _ => normalizing t
  end.

Fixpoint nocond (Gamma : context_value) (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Arrow T1 T2 => forall v, value v -> nocond Gamma T1 v -> nocond Gamma T2 <{t v}>
  | _ => normalizing (substm Gamma t)
  end. *)

Fixpoint use_norm t T : Prop :=
  match T with
  | Ty_Arrow T1 T2 => normalizing t /\ forall v, empty |-- v \in T1 -> use_norm v T1 -> use_norm <{t v}> T2
  | Ty_Unit => t -->* <{unit}>
  | _ => True
  end.

Lemma one_multi_dia t t1 t2 : t --> t1 -> t -->* t2 -> nf t2 -> t1 -->* t2.
Proof.
  intros.
  iac H0.
  - exfalso. apply H1. eauto.
  - assert (H4:=determinism _ _ _ H H2).
    subst.
    eauto.
Qed.

Theorem use_back : forall T t t', t --> t' -> use_norm t' T -> use_norm t T.
Proof.
  induction T.
  1:{
    intros. simpl in *. intuition.
    - destruct H1. exists x0; intuition. eauto.
    - eauto.
  }
  4:{
    intros; simpl in *.
    eauto.
  }
Admitted.

Theorem use_for : forall T t t', t --> t' -> use_norm t T -> use_norm t' T.
Proof.
  induction T.
  1:{
    intros. simpl in *. intuition.
    - destruct H1. exists x0; intuition. eauto using one_multi_dia.
    - eauto.
  }
  4:{
    intros; simpl in *.
    assert (H1 : nf <{unit}>).
    {
      intros []. iac H1.
    }
    eauto using one_multi_dia.
  }
Admitted.


Theorem use_back2 : forall T t t', t -->* t' -> use_norm t' T -> use_norm t T.
Proof.
  intros. induction H; eauto using use_back.
Qed.

Theorem use_for2 : forall T t t', t -->* t' -> use_norm t T -> use_norm t' T.
Proof.
  intros. induction H; eauto using use_for.
Qed.

Inductive good : context_value -> Prop :=
  | goodn : good nil
  | goodc s t T Gamma : good Gamma -> empty |-- t \in T -> use_norm t T -> good (cons (s,t,T) Gamma).

Definition d : context_value -> context := content_cv.

Ltac search_eq :=
  subst;
  try match goal with
  H : (?s |-> _ ; _) ?s = Some _ |- _
  => rewrite update_eq in H; injection H as H; subst
  end;
  try match goal with
  H : (?s |-> _ ; _) ?t = _, H2 : ?s <> ?t |- _
  => rewrite update_neq in H; eauto
  end.

Lemma wt_subst_eq : forall t Gamma T x t', Gamma |-- t \in T -> Gamma x = None -> <{[x:=t']t}> = t.
Proof.
  induction t; intros; simpl; try(iac H; f_equal; eauto; fail).
  - iac H. destruct (eqb_spec x0 s).
    + subst. congruence.
    + reflexivity.
  - destruct (eqb_spec x0 s); try(reflexivity).
    f_equal. iac H. eapply IHt.
    + eapply H6.
    + rewrite update_neq; eauto.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma wt_substi_eq : forall Gamma' t Gamma T, Gamma |-- t \in T -> (forall p q r, Lists.List.In (p,q,r) Gamma' -> Gamma p = None) -> substm Gamma' t = t.
Proof.
  induction Gamma'; intros.
  - reflexivity.
  - destruct a as [[p q] r]. simpl.
    erewrite wt_subst_eq.
    + eapply IHGamma'.
      * apply H.
      * intros. eapply H0. right. eapply H1.
    + eapply H.
    + eapply H0. left. reflexivity.
Qed.

Lemma substi_app_commute : forall Gamma t1 t2, substm Gamma <{t1 t2}> = tm_app (substm Gamma t1) (substm Gamma t2).
Proof.
  induction Gamma; try(reflexivity).
  destruct a as [[p q] r].
  simpl.
  intros. eauto.
Qed.


Lemma app1_cong : forall t1 t1' t2, t1 -->* t1' -> <{t1 t2}> -->* <{t1' t2}>.
Proof.
  intros.
  induction H; eauto.
Qed.

Lemma app2_cong : forall t1 t2 t2', value t1 -> t2 -->* t2' -> <{t1 t2}> -->* <{t1 t2'}>.
Proof.
  intros.
  induction H0; eauto.
Qed.

Definition filt (x : string) (l : context_value) : context_value :=
  Lists.List.filter (fun a =>
  match a with (p,q,r) => negb (p =? x)%string end) l.

Lemma abs_substi Gamma : forall s T t, substm Gamma <{\s:T,t}> = tm_abs s T (substm (filt s Gamma) t).
Proof.
  induction Gamma.
  - intros; simpl. reflexivity.
  - intros; simpl. destruct a as [[p q] r].
    destruct (eqb_spec p s).
    + rewrite IHGamma. reflexivity.
    + rewrite IHGamma. reflexivity.
Qed.

Fixpoint d' (Gamma : context_value) (Base : context) : context :=
  match Gamma with
  | nil => Base
  | cons (p,q,r) Gamma' => p|->r; d' Gamma' (Base)
  end.

Lemma good_filt : forall s Gamma, good Gamma -> good (filt s Gamma).
Proof.
  induction Gamma; simpl; eauto.
  destruct a as [[p q] r].
  intros.
  iac H.
  destruct (negb (p =? s)%string); try(eauto).
  - econstructor; eauto.
Qed.

Lemma filt_swap Gamma : forall Base s t, good Gamma -> (s |-> t; d' Gamma Base) = d' (filt s Gamma) (s |-> t; Base).
Proof.
  induction Gamma; intros; simpl.
  - reflexivity.
  - destruct a as [[p q] r].
    destruct (eqb_spec p s); subst; simpl.
    + rewrite update_shadow. apply IHGamma. iac H; eauto.
    + rewrite update_permute; eauto. f_equal.
      eapply IHGamma. iac H; eauto.
Qed.

Lemma substi_unit : forall Gamma, substm Gamma <{unit}> = <{unit}>.
Proof.
  induction Gamma; simpl; eauto.
  rewrite IHGamma.
  destruct a as [[]].
  reflexivity.
Qed.

Lemma rm_substi : forall (t : tm) (Base : context) (Gamma: context_value) (T : ty), good Gamma -> (d' Gamma Base) |-- t \in T <-> has_type Base (substm Gamma t) T.
Proof.
  induction t.
  1:{ (* var*)
    intros. split.
    {
      induction Gamma; simpl in *; eauto.
      destruct a as [[p q] r].
      destruct (eqb_spec p s); subst.
      + iac H. intros. iac H. search_eq.
        assert (substm Gamma q = q).
        {
          eapply wt_substi_eq.
          - eapply H5.
          - reflexivity.
        }
        rewrite H. eapply weakening_empty. eauto.
      + intros. iac H0. search_eq. apply IHGamma; eauto.
        iac H. eauto.
    }
    {
      induction Gamma; simpl in *; intros; eauto.
      destruct a as [[p q] r].
      iac H. destruct (eqb_spec p s); search_eq.
      - econstructor. rewrite update_eq.
        erewrite wt_substi_eq in H0.
        + f_equal. eapply type_unique; [idtac | eapply H0].
          eauto using weakening_empty.
        + exact H6.
        + reflexivity.
      - econstructor. rewrite update_neq; eauto.
        specialize (IHGamma H4 H0).
        iac IHGamma. eauto.
    }
  }
  1:{ (*app*)
    split.
    {
      specialize (IHt1 Base Gamma).
      specialize (IHt2 Base Gamma).
      rewrite substi_app_commute.
      intros. iac H0. econstructor.
      + eapply IHt1; eauto.
      + eapply IHt2; eauto.
    }
    {
      intros. rewrite substi_app_commute in H0. iac H0. econstructor; [eapply IHt1 | eapply IHt2]; eauto.
    }
  }
  1:{ (* abs *)
    split.
    {
      intros. iac H0.
      rewrite abs_substi. econstructor.
      eapply IHt.
      - eauto using good_filt.
      - rewrite <- filt_swap; eauto.
    }
    {
      intros. rewrite abs_substi in H0.
      iac H0. econstructor.
      apply IHt in H6; eauto using good_filt.
      rewrite filt_swap; eauto.
    }
  }
  12:{ (*unit*)
    intros.
    rewrite substi_unit.
    split; intros HT; iac HT; econstructor.
  }
Admitted.

Lemma d_to_d' : forall Gamma, d Gamma = d' Gamma empty.
Proof.
  induction Gamma as [|[[]]]; simpl; eauto.
  rewrite IHGamma; eauto.
Qed.

Lemma neqb_neq : forall x y, x <> y -> (x =? y)%string = false.
Proof.
  intros.
  destruct (eqb_spec x0 y0).
  - contradiction.
  - reflexivity.
Qed.

Lemma subst_eqabs s1 t1 T t: <{[s1:=t1](\s1:T,t)}> = <{\s1:T,t}>.
Proof.
  unfold subst; rewrite eqb_refl; reflexivity.
Qed.
Lemma subst_neqabs s1 s2 t1 T t: s1 <> s2 -> <{[s1:=t1](\s2:T,t)}> = <{\s2:T,[s1:=t1]t}>.
Proof.
  intro. apply neqb_neq in H.
  unfold subst; rewrite H. reflexivity.
Qed.

Lemma subst_eqvar s1 t: <{[s1:=t]s1}> = t.
Proof.
  unfold subst; rewrite eqb_refl; reflexivity.
Qed.
Lemma subst_neqvar s1 (s2 : string) t : s1 <> s2 -> <{[s1:=t]s2}> = s2.
Proof.
  intro. apply neqb_neq in H.
  unfold subst; rewrite H. reflexivity.
Qed.

Ltac tackle_eq :=
  subst; repeat
  (rewrite subst_eqabs in * ||
  rewrite subst_eqvar in * ||
  (erewrite subst_neqabs; [idtac | (eauto; fail)]) ||
  (erewrite subst_neqvar; [idtac | (eauto; fail)])).

Lemma subst_shadow : forall s t1 t2, <{[s:=t1]t2}> = t2 -> forall t, <{[s:=t1]([s:=t2]t)}> = <{[s:=t2]t}>.
Proof.
  induction t; simpl; try(f_equal; eauto).
  - destruct (eqb_spec s s0); eauto. unfold subst.
    destruct (eqb_spec s s0); eauto.
    contradiction.
  - destruct (eqb_spec s s0); eauto; subst; tackle_eq.
    + reflexivity.
    + rewrite IHt; reflexivity.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma subst_permute : forall s1 s2 t1 t2, s1 <> s2 -> <{[s1:=t1]t2}> = t2 -> <{[s2:=t2]t1}> = t1 -> forall t, <{[s1:=t1]([s2:=t2]t)}> = <{[s2:=t2]([s1:=t1]t)}>.
Proof.
  induction t; simpl; try(f_equal; eauto; fail).
  - destruct (eqb_spec s2 s); destruct (eqb_spec s1 s); subst.
    + congruence.
    + tackle_eq. eauto.
    + tackle_eq. eauto.
    + tackle_eq. eauto.
  - destruct (eqb_spec s2 s); destruct (eqb_spec s1 s); subst.
    + congruence.
    + tackle_eq. eauto.
    + tackle_eq. eauto.
    + tackle_eq. rewrite IHt. reflexivity.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma permute : forall Gamma p q t T, good Gamma -> empty |-- q \in T -> subst p q (substm (filt p Gamma) t) = substm Gamma (subst p q t).
Proof.
  induction Gamma; intros; simpl.
  - reflexivity.
  - destruct a as [[p1 q1] r1].
    destruct (eqb_spec p1 p); subst; simpl.
    + iac H. erewrite IHGamma; eauto. symmetry. f_equal. eapply subst_shadow. eapply wt_subst_eq.
      * eapply H0.
      * reflexivity.
    + iac H. erewrite IHGamma; eauto. f_equal. eapply subst_permute; eauto.
      * eapply wt_subst_eq.
        -- eapply H6.
        -- reflexivity.
      * eapply wt_subst_eq.
        -- eapply H0.
        -- reflexivity.
Qed.

Theorem use_norm_to_norm v T : use_norm v T -> normalizing v.
Proof.
  destruct T.
  - simpl. intuition.
  - admit.
  - admit.
  - admit.
  - intros. simpl in H.
    exists <{unit}>. intuition. intros [t' H1].
    iac H1.
  - admit.
Admitted.

Theorem main t : forall Gamma T, d Gamma |-- t \in T -> good Gamma -> use_norm (substm Gamma t) T.
Proof.
  induction t.
  - intros. iac H. induction Gamma; simpl in *.
    + discriminate.
    + destruct a as [[s1 t1] T1].
      destruct (eqb_spec s1 s).
      * search_eq. iac H0.
        erewrite wt_substi_eq; [eauto | apply H5 | reflexivity].
      * search_eq. iac H0.
        eauto.
  - intros. iac H.
    specialize (IHt1 _ _ H4 H0).
    specialize (IHt2 _ _ H6 H0).
    simpl in IHt1.
    rewrite substi_app_commute.
    destruct IHt1. apply H1.
    + repeat rewrite d_to_d' in *. eapply rm_substi; eauto.
    + eauto.
  - rename t into T. intros. iac H. simpl. intros.
    split.
    + rewrite abs_substi.
      eexists. split; [eapply multi_refl | idtac].
      intros []. iac H.
    + intros.
      rewrite abs_substi.
      assert (H2 := use_norm_to_norm _ _ H1).
      destruct H2 as [v' [H3 H4]].
      assert (empty |-- v' \in T).
      {
        eauto using multi_pre.
      }
      assert (use_norm v' T).
      {
        eauto using use_for2.
      }
      assert (H7 := goodc s v' T _ H0 H2 H5).
      specialize (IHt (cons (s,v',T) Gamma) T1 H6 H7). simpl in IHt.
      erewrite <- permute in IHt; eauto.
      eapply use_back2; [idtac | eapply IHt].
      eapply multi_trans.
      * eapply app2_cong.
        -- econstructor.
        -- eapply H3.
      * eapply multi_R. econstructor.
        eapply value_if_nf_ty; eauto.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - intros. rewrite substi_unit.
    iac H. eapply multi_refl.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Theorem norm : forall t T, empty |-- t \in T -> normalizing t.
Proof.
  intros.
  eapply use_norm_to_norm.
  eapply (main t nil).
  - exact H.
  - econstructor.
Qed.


(* Fixpoint strong_norm Gamma t T : Prop :=
  (content_cv Gamma) |-- t \in T /\
  match T with
  | Ty_Arrow T1 T2 => forall v, strong_norm Gamma v T1 -> strong_norm Gamma <{t v}> T2
  | Ty_Unit => substm Gamma t -->* <{unit}>
  | _ => True
  end.

Definition strong_norm' Gamma t T : Prop :=
  (content_cv Gamma) |-- t \in T /\
  match T with
  | Ty_Arrow T1 T2 => forall v, strong_norm Gamma v T1 -> strong_norm Gamma <{t v}> T2
  | Ty_Unit => substm Gamma t -->* <{unit}>
  | _ => True
  end.

Lemma eq_norm Gamma t T : strong_norm Gamma t T <-> strong_norm' Gamma t T.
Proof.
  destruct T; unfold strong_norm', strong_norm; split; eauto.
Qed. *)

(* Definition Prop1 (Gamma : context_value) (T : ty) (t : tm) : Prop := (Lists.List.Forall (fun x => match x with (p,q,r) => emptyProp1 r q /\ empty |-- q \in r end) Gamma) -> nocond Gamma T t. *)

(* Lemma allnil : forall A (P : A -> Prop), (Lists.List.Forall P nil) <-> True.
Proof.
  intros. simpl. split; eauto.
Qed. *)

(* Lemma empty_same1 : forall T t, emptyProp1 T t <-> nocond nil T t.
Proof with eauto.
  unfold Prop1.
  induction T; intuition.
  - simpl. intuition.
    apply IHT2.
    apply H... apply IHT1...
  - intro. intros. apply IHT2. apply H... apply IHT1...
Qed. *)

(* Lemma empty_same2 : forall T t, Prop1 nil T t <-> nocond nil T t.
Proof.
  unfold Prop1.
  intros. rewrite allnil. intuition.
Qed. *)

(* Lemma Prop1_iff : forall Gamma T t, Prop1 Gamma T t <-> ((forall p q r, Lists.List.In (p,q,r) Gamma -> emptyProp1 r q) -> normalizing (substm Gamma t)).
Proof.
  intros.
  split.
  - destruct T; eauto using empty_same.
    unfold Prop1. simpl. *)

(* Definition ind_prop (t : tm) := forall Gamma T, (content_cv Gamma) |-- t \in T -> Prop1 Gamma T t. *)

(* Definition ind_prop (t : tm) : Prop :=
  limit_tm t -> forall Gamma T, content_cv Gamma |-- t \in T -> cond_cv Gamma -> normalizing (substm Gamma t) /\ forall x T t', t -->* <{\x:T, t'}> -> normalizing (substm Gamma t').

Definition str_ind_prop (t : tm) : Prop :=
  ind_prop t . *)


(* Lemma str_str_ind_to_ind : forall t, str_str_ind_prop t -> str_ind_prop t.
Proof.
  unfold str_str_ind_prop; eauto.
Qed. *)
(* Lemma str_ind_to_ind : forall t, str_ind_prop t -> ind_prop t.
Proof.
  destruct t; unfold str_ind_prop; intuition.
Qed. *)

Lemma rm_substi : forall (t : tm) (Gamma: context_value) (T : ty), cond_cv Gamma -> content_cv Gamma |-- t \in T <-> has_type empty (substm Gamma t) T.
Proof.
  induction t.
  1:{
    split; intros.
    - induction Gamma; simpl in *; eauto.
      destruct a as [[p q] r].
      destruct (eqb_spec p s); subst.
      + destruct H as [[H1 H2] H3].
        iac H0. search_eq.
        rewrite (wt_substi_eq Gamma _ _ _ H1 (fun _ _ _ _ => eq_refl)). auto.
      + iac H0. search_eq. apply IHGamma; eauto.
        intuition.
    - induction Gamma; simpl in *; eauto.
      destruct a as [[p q] r].
      destruct (eqb_spec p s); subst; econstructor.
      + rewrite update_eq. f_equal.
        destruct H as [[H1 H2] H3].
        rewrite (wt_substi_eq Gamma _ _ _ H1 (fun _ _ _ _ => eq_refl)) in H0.
        admit.
      + rewrite update_neq; eauto.
        specialize (IHGamma (proj2 H) H0).
        iac IHGamma. eauto.
  }
  1:{
    intros.
    specialize (IHt1 Gamma).
    specialize (IHt2 Gamma).
    rewrite substi_app_commute.
    split.
    - intros. iac H0. econstructor.
      + eapply IHt1; eauto.
      + eapply IHt2; eauto.
    - intros. iac H0. econstructor.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  }
  1:{
    split.
    - intros. rewrite abs_substi.
      iac H0.
      econstructor.
      destruct (nonempty t).
      destruct H0.
      assert (cond_cv ((s,x0,t)::Gamma)%list).
      {
        repeat split; eauto.
      }
      assert (H3 := proj1 (IHt (cons (s,x0,t) Gamma) T1 H2) H6).
      simpl in H3.
      rewrite <- permute in H3.
      admit.
    - intros. rewrite abs_substi in H0.
      iac H0. econstructor.
      destruct (nonempty t).
      destruct H0.
      eapply (IHt (cons (s,x0,t) Gamma)).
      + split; eauto.
      + admit.
  }
  12:{
    admit.
  }
Admitted.
  (* induction Gamma; split; eauto.
  + intros. destruct a as [[p q] r]. simpl in *.
    eapply IHGamma.
    - destruct H. eauto.
    - destruct H as [[H1 H2] H3].
      eapply (rm_context_by_subst _ _ _ _ _ _ H0 H1).
  + intros. induction t.
    - rewrite . *)
(* Qed. *)

Theorem tm_var_case : forall (s : string) T Gamma, content_cv Gamma |-- s \in T -> cond_cv Gamma -> normalizing (substm Gamma s).
Proof with eauto.
  induction Gamma; simpl in *; intros HT HC.
  + iac HT. discriminate.
  + destruct a as [[s0 t] T'].
    destruct (eqb_spec s0 s).
    * subst. iac HT. rewrite update_eq in H1.
      injection H1 as H1; subst.
      destruct HC as [[H1 H2] H3].
      erewrite wt_substi_eq.
      -- exists t.
          split; eauto. apply nf_if_value; eauto.
      -- apply H1.
      -- reflexivity.
    * iac HT. rewrite update_neq in H1; eauto.
      destruct HC as [[H4 H2] H3].
      eapply IHGamma; eauto.
Qed.

Lemma nocond_cong_substi : forall Gamma T t1 t2, substm Gamma t1 = substm Gamma t2 -> nocond Gamma T t1 -> nocond Gamma T t2.
Proof.
  induction T.
  1:{(*App*)
    simpl. intros. apply IHT2 with (t1 := <{t1 v}>).
    - rewrite substi_app_commute.
      rewrite substi_app_commute.
      f_equal; eauto.
    - eauto.
  }
  4:{(*Unit*)
    intros. simpl in *.
    rewrite H in H0; eauto.
  }
Admitted.

Theorem tm_var_case2 : forall T (s : string) t Gamma,
  emptyProp1 T t -> empty |-- t \in T -> nocond ((s,t,T)::Gamma)%list T s.
Proof.
  induction T.
  1:{
    simpl. intros.
    eapply (nocond_cong_substi ((s, t, <{{ T1 -> T2 }}>) :: Gamma) _ <{t v}>).
    - repeat rewrite substi_app_commute.
      f_equal; eauto.
      simpl. rewrite eqb_refl. f_equal.
      eapply wt_subst_eq; [eapply H0 | reflexivity].
    -

  }
Admitted.

Lemma ind_prop_norm Gamma (t : tm) T : (content_cv Gamma) |-- t \in T -> Prop1 Gamma T t -> normalizing (substm Gamma t).
Admitted.

Theorem nofix_normalizing_context : forall t Gamma T,
  (content_cv Gamma) |-- t \in T ->
  cond_cv Gamma ->
  Lists.List.Forall (fun a => match a with (p,q,r) => strong_norm' nil q r end) Gamma ->
  strong_norm' Gamma t T.
Proof.
  induction t; intros.
  - iac H.
    assert (exists t, Lists.List.In (s,t,T) Gamma).
    {
      admit.
    }
    destruct H.
    assert (strong_norm' nil x0 T). {admit. }
    destruct H2. split.
    + econstructor. eauto.
    + destruct T.
      * intros. rewrite eq_norm in *.
        destruct H5. split.
        specialize (H3 _ H5).

    induction Gamma.
    + discriminate.
    + destruct a as [[p q] r]. simpl in H4.
      destruct (eqb_spec p s); subst.
      * iac H1. destruct r.
        -- simpl in *. destruct H3.
           search_eq.
          split.
        ++ econstructor. simpl. rewrite update_eq. reflexivity.
        ++ intros.
          specialize (H1 v).

Theorem nofix_normalizing_context : forall t, ind_prop t.
Proof.
  induction t; unfold ind_prop.
  - intros. iac H. intros H.
    (* generalize dependent T. *)
    induction Gamma.
    + discriminate.
    + simpl in H2. destruct a as [[p q] r].
      destruct (eqb_spec p s).
      * subst. iac H. rewrite update_eq in H2.
        injection H2 as H2. subst.
        clear H4 IHGamma.
        destruct H3.
        eapply tm_var_case2; eauto.
      * rewrite update_neq in H2; eauto.
        assert (nocond Gamma T s).
        {
          iac H.
          apply IHGamma; eauto.
        }
        clear IHGamma.
        admit.
  - intros. iac H.
    unfold Prop1. intros.
    assert (H2 := IHt2 _ _ H5).
    destruct (ind_prop_norm _ _ _ H5 H2).
    destruct H0.
    assert (value x0). {admit. }
    assert (nocond Gamma T2 x0). {Check (H2 H). admit. }

    assert (H8:=(IHt1 _ _ H3 H x0 H4 H6) : nocond Gamma T <{t1 x0}>).
    admit.
  - intros. iac H. intro H1. simpl. intros.
    admit.

Theorem nofix_normalizing_context :
  forall t, str_ind_prop t.
Proof.
  induction t; unfold str_ind_prop, ind_prop;
  intros nf; iac nf; intros Gamma T HT HC; split.
  - eauto using tm_var_case.
  - intros. iac H. iac H0.
  - apply str_ind_to_ind in IHt2.
    assert (H3 := str_ind_to_ind _ IHt1).
    rewrite substi_app_commute.
    iac HT.
    destruct (H3 H1 _ _ H5 HC).
    destruct H. destruct H.
    assert (H10 := rm_substi _ _ _ HC H5).
    assert (H11 := multi_pre _ _ _ H H10).
    assert (H8 := value_if_nf_ty _ _ H11 H4).
    assert (H12 : exists x T1 t1, x0 = tm_abs x T1 t1).
    {
      destruct H8; iac H11.
      exists x0, T2, t0. reflexivity.
    }
    destruct H12 as [x [T1 [t3 eq]]].
    subst.
    destruct (IHt2 H2 _ _ H7 HC) as [[x0 []]].
    assert (normalizing <{(\x:T1, t3) x0}> -> normalizing (tm_app (substm Gamma t1) (substm Gamma t2))).
    {
      intros. destruct H13 as [x1 [H14 H13]].
      exists x1.
      split; eauto.
      eapply multi_trans; try(eapply H14).
      eapply multi_trans; try(eapply (app2_cong _ _ _ H8 H6)).
      eapply app1_cong.
      eauto.
    }
    eapply H13; clear H13.
    assert (ind_prop t3). {admit. }
    assert (normalizing <{[x:=x0]t3}>).
    {

    }
    Check (H3 t1).
    Check (H13 _ _ _ )
    clear H0 H8.








  -
  induction t; intros context T nf ty1 wt.
  - iac ty1. induction context.
    + discriminate.
    + simpl in H1. destruct a. destruct p. simpl. destruct (eqb_spec s0 s).
      * subst. rewrite update_eq in H1. injection H1 as H1. subst.
        simpl.
        assert (empty |-- t0 \in T /\ value t0). {eapply wt. left. eauto. }
        admit.
      * rewrite update_neq in H1; eauto. eapply IHcontext; eauto.
        intros. eapply wt. right. eauto.
  -


        eapply IHcontext.
        rewrite (eq_eqb).
        assert (empty |-- s \in T). {eapply wt. left. eauto. }
        eapply IHcontext; eauto.
        -- intros. eapply wt. right. eauto.
        --
Admitted.

(* Fixpoint remove_let (t : tm) : tm :=
  match t with
  | <{let x=t1 in t2}> => remove_let t2
  | _ => t
  end. *)

Ltac get_norm :=
  repeat match goal with
  H1 : forall T, limit_tm ?t -> empty |-- ?t \in T -> normalizing ?t,
  H2 : limit_tm ?t,
  H3 : empty |-- ?t \in ?T
  |- _ =>
    specialize (H1 T H2 H3); let t'n := fresh"t'" in let Hn1 := fresh"H" in let Hn2 := fresh"H" in destruct H1 as [t'n [Hn1 Hn2]] end.

Ltac get_value :=
  repeat match goal with
  H1 : nf ?t',
  H2 : empty |-- ?t \in ?T,
  H3 : ?t -->* ?t'
  |- _ =>
  let HT' := fresh"HT" in assert (HT' := multi_pre _ _ _ H3 H2); clear H2;
  let Hv := fresh"Hv" in assert (Hv := value_if_nf_ty _ _ HT' H1); clear H1 end.

Theorem nofix_normalizing : forall t T, limit_tm t -> empty |-- t \in T -> normalizing t.
Proof.
  induction t; intros T nft HT; iac nft; iac HT.
  - discriminate.
  - get_norm. get_value. discuss_value.
    exists <{[x0:=t']t0}>. eauto.
  (* Check (value_if_nf_ty t1 ). *)
  (* match goal with
  H1 : nf ?t',
  H2 : empty |-- ?t \in ?T,
  H3 : ?t -->* ?t'
  |- _ =>
  let Hv := fresh"Hv" in assert (Hv := value_if_nf_ty t' T (multi_pre _ _ _ H3 H2) H1); clear H1 end.
  get_value.
  match goal with
  H1 : nf ?t,
  H2 : empty |-- ?t \in ?T
  |- _ =>
  let Hv := fresh"Hv" in assert (Hv := value_if_nf_ty t T H2 H1); clear H1 end. *)

  get_value. Print nf.
Abort. *)

(* one way: 加入语境 把语境中所有项代为value时norm *)
(* another way: 找到递减量 *)
