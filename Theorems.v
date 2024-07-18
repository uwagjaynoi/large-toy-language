From Lambda Require Import Map.
From Lambda Require Import Syntax.
From Lambda Require Import Lemma.
From Lambda Require Import LibTactics.
Set Default Goal Selector "!".

Theorem progress : forall t T,
  empty |-- t \in T ->
  value t \/ exists t', t --> t'.
Proof.
  Ltac instantiate_IH :=
    repeat match goal with
    | IH : empty = empty -> _ |- _ =>
      specialize (IH eq_refl);
      destruct IH as [? | [? ?]]; eauto
    end.
  Ltac invert_value :=
    try match goal with
    | Hv : value ?t,
      HT : has_type ?t _ empty |- _ =>
      solve [inverts Hv; inverts HT; eauto]
    end.
  intros t T HT. remember empty as Gamma.
  induction HT; try subst Gamma; eauto;
  instantiate_IH; invert_value.
  discriminate.
Defined.

Theorem subst_type x U v :
  empty |-- v \in U -> forall t Gamma T,
  (x |-> U ; Gamma) |-- t \in T ->
  Gamma |-- <{[x:=v]t}> \in T.
Proof.
  Ltac remember_context Gamma :=
    match goal with
    | H : has_type ?t ?T Gamma |- ?g =>
      let H2 := fresh "H" in
      let p := fresh "p" in
        assert (H2 : forall (p : context), p ~ Gamma -> has_type t T p -> g); [clear H; intros p Hequ H | eauto]
    end.
  Ltac subst_context G :=
    repeat match goal with
    | Hequ : G ~ _,
      Heq : G _ = _ |- _ =>
      rewrite Hequ in Heq
    end.
  Ltac eq_case :=
    repeat match goal with
    | |- has_type (if ?x =? ?y then _ else _) _ _ =>
      destruct (eqb_spec x y); subst ; eauto using weaken_empty
    | H : (?s |-> _ ; _) ?s = Some _ |- _ =>
      rewrite update_eq in H; inverts H; eauto using weaken_empty
    | H : (?s |-> _ ; _) ?t = _,
      H2 : ?s <> ?t |- _ =>
      rewrite update_neq in H; eauto using weaken_empty
    | H : (?s |-> _ ; _) ?t = _,
      H2 : ?t <> ?s |- _ =>
      rewrite update_neq in H; eauto using weaken_empty
    end.
  Ltac enough_cong :=
    match goal with
    | H : has_type ?t ?T _ |- has_type ?t ?T _ =>
      gen H; eapply has_type_extensionality
    | H : forall G, _ -> has_type ?t ?T G |- has_type ?t ?T _ =>
      apply H
    end.
  Ltac subst_cong :=
    match goal with
    | Hequ : ?G ~ _ |- ?G ~ _ =>
      apply (mapeq_trans _ _ _ Hequ)
    | Hequ : ?G ~ _ |- (update _ _ ?G) ~ _ =>
      apply (mapeq_trans _ _ _ (mapeq_cong _ _ _ _ Hequ))
    | Hequ : ?G ~ _ |- (update _ _ (update _ _ ?G)) ~ _ =>
      apply (mapeq_trans _ _ _ (mapeq_cong _ _ _ _ (mapeq_cong _ _ _ _ Hequ)))
    end.
  introv HTv HT.
  remember_context (x |-> U ; Gamma); gen Gamma.
  induction HT;
  intros Gamma' Heq; subst_context Gamma;
  simpl; eauto;
  try econstructor; eauto; eq_case; enough_cong; try subst_cong;
  eauto using update_shadow, update_permute, mapeq_cong.
  - (* list ABA=AB *)
    unfold update. intros z.
    destruct (x =? z), (y =? z); reflexivity.
  - (* list ABC=CAB *)
    eapply mapeq_trans.
    + eapply mapeq_cong.
      eapply update_permute; auto.
    + eapply update_permute; auto.
Defined.

Theorem preservation t t' T :
  empty |-- t \in T -> t --> t' -> empty |-- t' \in T.
Proof.
  intros HT. remember empty as Gamma. gen t'.
  induction HT; subst Gamma; try discriminate;
  introv HS; inverts HS; eauto;
  try match goal with
  | H : has_type _ (?c ?T1) _ |- _ =>
    inverts H
  | H : has_type _ (?c ?T1 ?T2) _ |- _ =>
    inverts H
  end;
  eauto using subst_type.
Defined.