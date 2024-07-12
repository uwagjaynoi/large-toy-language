

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From PLF Require Import AMaps.
From PLF Require Import BImp.
Set Default Goal Selector "!".

Definition FILL_IN_HERE := <{True}>.








Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm.



Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.



Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n ==> n
  | E_Plus : forall t1 t2 n1 n2,
      t1 ==> n1 ->
      t2 ==> n2 ->
      P t1 t2 ==> (n1 + n2)

where " t '==>' n " := (eval t n).

Definition relation (X : Type) := X -> X -> Prop.









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


Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).









Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          P (C n1) (C n2)
      --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').





Theorem step_deterministic :
  deterministic step.
Proof.
  intros x y1 y2 H1. generalize y2. induction H1; intros.
  - inversion H; subst; try(solve_by_invert); reflexivity.
  - inversion H; subst; try(solve_by_invert); f_equal.
    + apply IHstep; assumption.
    + inversion H3; subst; solve_by_invert.
    + inversion H3; subst; solve_by_invert.
  - inversion H; subst. inversion H0; subst; try(solve_by_invert).
    f_equal. apply IHstep; assumption.
Qed.











Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  induction t.
  -  left. apply v_const.
  -  right. destruct IHt1 as [IHt1 | [t1' Ht1] ].
    +  destruct IHt2 as [IHt2 | [t2' Ht2] ].
      *  inversion IHt1. inversion IHt2.
        exists (C (n + n0)).
        apply ST_PlusConstConst.
      *
        exists (P t1 t2').
        apply ST_Plus2; auto.
    +
      exists (P t1' t2).
      apply ST_Plus1. apply Ht1.
Qed.





Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.





Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form. intros v H. destruct H.
  intros contra. destruct contra. inversion H.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof.
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t --> t').
  { apply strong_progress. }
  destruct G as [G | G].
  -  apply G.
  -  contradiction.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split.
  - apply nf_is_value.
  - apply value_is_nf.
Qed.



Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.







Notation " t '-->*' t' " := (multi step t t') (at level 40).





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
Proof.

  unfold deterministic. unfold normal_form_of.
  intros x y1 y2 P1.
  destruct P1 as [P11 P12]. generalize P12. induction P11.
  - intros _ [H1 _]. destruct H1; try(reflexivity).
    exfalso. apply P12. exists y; assumption.
  - intros _ [H1 H2]. destruct H1.
  + exfalso. apply H2. exists y; assumption.
  + destruct (step_deterministic _ _ _ H H0).
    destruct (IHP11 P12 P12 (conj H1 H2)). reflexivity.
Qed.




Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.



Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 -->* t1' ->
     P t1 t2 -->* P t1' t2.
Proof.
  intros t1 t1' t2 H. induction H.
  -  apply multi_refl.
  -  apply multi_step with (P y t2).
    + apply ST_Plus1. apply H.
    + apply IHmulti.
Qed.


Lemma multistep_congr_2 : forall v1 t2 t2',
     value v1 ->
     t2 -->* t2' ->
     P v1 t2 -->* P v1 t2'.
Proof.
  intros v1 t2 t2' vv1 H2. induction H2.
  - apply multi_refl.
  - apply multi_step with (P v1 y); try(assumption).
    constructor; assumption.
Qed.



Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  induction t.
  -
    exists (C n).
    split.
    +  apply multi_refl.
    +

      apply nf_same_as_value. apply v_const.
  -
    destruct IHt1 as [t1' [Hsteps1 Hnormal1] ].
    destruct IHt2 as [t2' [Hsteps2 Hnormal2] ].
    apply nf_same_as_value in Hnormal1.
    apply nf_same_as_value in Hnormal2.
    destruct Hnormal1 as [n1].
    destruct Hnormal2 as [n2].
    exists (C (n1 + n2)).
    split.
    +
      apply multi_trans with (P (C n1) t2).
      * apply multistep_congr_1. apply Hsteps1.
      * apply multi_trans with (P (C n1) (C n2)).
        { apply multistep_congr_2.
          - apply v_const.
          - apply Hsteps2. }
        apply multi_R. apply ST_PlusConstConst.
    +
      apply nf_same_as_value. apply v_const.
Qed.









Theorem eval__multistep : forall t n,
  t ==> n -> t -->* C n.





Proof.
  intros t n H. induction H.
  - apply multi_refl.
  - apply multi_trans with (P (C n1) t2).
  + apply multistep_congr_1; assumption.
  + apply multi_trans with (P (C n1) (C n2)).
  * apply multistep_congr_2; try(constructor); assumption.
  * apply multi_R. constructor.
Qed.





Definition manual_grade_for_eval__multistep_inf : option (nat*string) := None.





Lemma step__eval : forall t t' n,
     t --> t' ->
     t' ==> n ->
     t  ==> n.
Proof.
  intros t t' n Hs. generalize dependent n. induction Hs.
  - intros. inversion H; subst. repeat constructor.
  - intros. inversion H; subst. apply IHHs in H2. constructor; assumption.
  - intros. inversion H0; subst. constructor; try(assumption). apply IHHs; assumption.
Qed.







Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t ==> n.
Proof.
  intros t t' [H1 H2].
  rewrite nf_same_as_value in H2. destruct H2. exists n.
  split; try(reflexivity). remember (C n) as Cn.
  induction H1.
  - subst. constructor.
  - subst. eapply step__eval.
  + apply H.
  + apply IHmulti. reflexivity.
Qed.

Theorem evalF_eval : forall t n,
  evalF t = n <-> t ==> n.
Proof.
  split.
  - intros. subst. induction t; try(constructor); assumption.
  - intros. induction H; try(reflexivity).
    simpl. lia.
Qed.




Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).



Reserved Notation " a '/' st '-->a' a' "
                  (at level 40, st at level 39).
Inductive astep (st : state) : aexp -> aexp -> Prop :=
  | AS_Id : forall (i : string),
      i / st -->a (st i)
  | AS_Plus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 + a2 }> / st -->a <{ a1' + a2 }>
  | AS_Plus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 + a2 }>  / st -->a <{ v1 + a2' }>
  | AS_Plus : forall (v1 v2 : nat),
      <{ v1 + v2 }> / st -->a (v1 + v2)
  | AS_Minus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 - a2 }> / st -->a <{ a1' - a2 }>
  | AS_Minus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 - a2 }>  / st -->a <{ v1 - a2' }>
  | AS_Minus : forall (v1 v2 : nat),
      <{ v1 - v2 }> / st -->a (v1 - v2)
  | AS_Mult1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 * a2 }> / st -->a <{ a1' * a2 }>
  | AS_Mult2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 * a2 }>  / st -->a <{ v1 * a2' }>
  | AS_Mult : forall (v1 v2 : nat),
      <{ v1 * v2 }> / st -->a (v1 * v2)

    where " a '/' st '-->a' a' " := (astep st a a').

Reserved Notation " b '/' st '-->b' b' "
                  (at level 40, st at level 39).
Inductive bstep (st : state) : bexp -> bexp -> Prop :=
| BS_Eq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 = a2 }> / st -->b <{ a1' = a2 }>
| BS_Eq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 = a2 }> / st -->b <{ v1 = a2' }>
| BS_Eq : forall (v1 v2 : nat),
    <{ v1 = v2 }> / st -->b
    (if (v1 =? v2) then <{ true }> else <{ false }>)
| BS_LtEq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 <= a2 }> / st -->b <{ a1' <= a2 }>
| BS_LtEq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 <= a2 }> / st -->b <{ v1 <= a2' }>
| BS_LtEq : forall (v1 v2 : nat),
    <{ v1 <= v2 }> / st -->b
    (if (v1 <=? v2) then <{ true }> else <{ false }>)
| BS_NotStep : forall b1 b1',
    b1 / st -->b b1' ->
    <{ ~ b1 }> / st -->b <{ ~ b1' }>
| BS_NotTrue  : <{ ~ true }> / st  -->b <{ false }>
| BS_NotFalse : <{ ~ false }> / st -->b <{ true }>
| BS_AndStep : forall b1 b1' b2,
    b1 / st -->b b1' ->
    <{ b1 && b2 }> / st -->b <{ b1' && b2 }>
| BS_AndTrueStep : forall b2 b2',
    b2 / st -->b b2' ->
    <{ true && b2 }> / st -->b <{ true && b2' }>
| BS_AndFalse : forall b2,
    <{ false && b2 }> / st -->b <{ false }>
| BS_AndTrueTrue  : <{ true && true  }> / st -->b <{ true }>
| BS_AndTrueFalse : <{ true && false }> / st -->b <{ false }>

where " b '/' st '-->b' b' " := (bstep st b b').





Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).




Tactic Notation "print_goal" := idtac.


Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | simpl]);
  apply multi_refl.
