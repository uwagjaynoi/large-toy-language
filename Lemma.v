From Lambda Require Import Map.
From Lambda Require Import Syntax.
From Lambda Require Import LibTactics.
From Coq Require Import Classes.CEquivalence.
From Coq Require Classes.CMorphisms.
Set Default Goal Selector "!".

Lemma weaken t T :
  forall (G1 : context), G1 |-- t \in T ->
  forall (G2 : context), includedin G1 G2 ->
  G2 |-- t \in T.
Proof.
  introv HT; induction HT; intros; eauto 7 using includedin_update.
Defined.

Corollary weaken_empty t T :
  empty |-- t \in T -> forall G, G |-- t \in T.
Proof.
  intros. eapply weaken; eauto. discriminate.
Defined.

Corollary has_type_extensionality :
  forall G1 G2 t T,
  G1 ~ G2 -> G1 |-- t \in T -> G2 |-- t \in T.
Proof.
  introv Hext HT. eapply weaken; eauto. congruence.
Defined.

Global Instance equiv_rel {A} :
  Equivalence (@mapeq A) :=
{|
  Equivalence_Reflexive := mapeq_refl;
  Equivalence_Symmetric := mapeq_sym;
  Equivalence_Transitive := mapeq_trans
|}.

Global Instance update_morphism {A} x v :
  CMorphisms.Proper (CMorphisms.respectful (@mapeq A) (@mapeq A)) (update x v) := fun _ _ => mapeq_cong _ _ _ _.

Global Instance has_type_morphism t T :
  CMorphisms.Proper (CMorphisms.respectful mapeq iffT) (has_type t T) :=
  (fun m1 m2 Hequ =>
   (has_type_extensionality m1 m2 t T Hequ,
   has_type_extensionality m2 m1 t T (mapeq_sym m1 m2 Hequ))).
