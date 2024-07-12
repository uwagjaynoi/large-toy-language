From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
(* Require Export Coq.INDEXs.INDEX. *)
(* From Coq Require Import Logic.FunctionalExtensionality. *)
(* From Coq Require Import Lists.List. *)
(* Import ListNotations. *)
Set Default Goal Selector "!".

Section map.
Variable INDEX : Type.
Variable eqb : INDEX -> INDEX -> bool.
Infix "=?" := eqb (at level 70).
Variable eqb_spec : forall x y, reflect (x=y) (x=?y).


(* #[global] *)

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Lemma eq_to_ext {A} (f g : total_map A) : f = g -> f ~ g.
Proof. congruence. Defined.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof. intros. unfold t_update. rewrite eqb_refl. reflexivity. Qed.
Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof. intros. unfold t_update. rewrite <- eqb_neq in H. rewrite H. reflexivity. Defined.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) ~ (x !-> v2 ; m).
Proof.
  intros. unfold t_update. destruct (x =? x0); reflexivity.
Defined.
Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x1 <> x2 ->
  (x1 !-> v1 ; x2 !-> v2 ; m) ~ (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros. unfold t_update.
  destruct (eqb_spec x1 x), (eqb_spec x2 x); try reflexivity.
  congruence.
Defined.



(* #[global] Hint Resolve update_eq : core. *)




End map.