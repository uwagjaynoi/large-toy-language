From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.


Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.


Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y.
  - apply H.
  - apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y.
      + assumption.
      + apply IHG. assumption.
Qed.


Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | simpl]);
  apply multi_refl.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Lemma nf_is_value : forall t,
  normal_form step t -> value t.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y.
  - apply H.
  - apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    -  assumption.
    -
      apply multi_step with y.
      + assumption.
      + apply IHG. assumption.
Qed.

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t -->* t' /\ step_normal_form t').

Theorem normal_forms_unique:
  deterministic normal_form_of.
Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | simpl]);
  apply multi_refl.

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck : core.

Definition nf : tm -> Prop := normal_form step.

Theorem nf_if_value (t : tm) : value t -> nf t.

Ltac find_value_step :=
  match goal with
  Hv : value ?t,
  Hs : ?t --> ?t'
  |- _ => exfalso; apply (nf_if_value t Hv (ex_intro _ t' Hs)) end.

Ltac find_value_step_aggr :=
  match goal with
  Hs : ?t --> ?t'
  |- _ => exfalso; assert (Hv : value t); [eauto | apply (nf_if_value t Hv (ex_intro _ t' Hs))] end.

Theorem type_unique t : forall Gamma T1 T2, Gamma |-- t \in T1 -> Gamma |-- t \in T2 -> T1 = T2.

Definition normalizing (t : tm) := exists t', t -->* t' /\ nf t'.

Definition context_value := list (string * tm * ty).

Lemma good_filt : forall s Gamma, good Gamma -> good (filt s Gamma).

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