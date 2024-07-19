From Coq Require Import Init.Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Lemma nf_is_value : forall t,
  normal_form step t -> value t.

Theorem type_unique t : forall Gamma T1 T2, Gamma |-- t \in T1 -> Gamma |-- t \in T2 -> T1 = T2.

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
