Require Import Bool.Bool.
From Lambda Require Import LibTactics.
Set Default Goal Selector "!".

Axiom INDEX : Type.
Axiom eqb : INDEX -> INDEX -> bool.
Infix "=?" := eqb (at level 70).
Axiom eqb_spec : forall x y, reflect (x=y) (x=?y).

Property eqb_refl x : (x =? x) = true.
Proof. destruct (eqb_spec x x); auto. Defined.
Property eqb_eq x y : (x =? y) = true <-> x = y.
Proof. destruct (eqb_spec x y); split; auto. congruence. Defined.
Property eqb_neq x y : (x =? y) = false <-> x <> y.
Proof. destruct (eqb_spec x y); split; auto; congruence. Defined.
#[export]
Hint Resolve eqb_eq eqb_neq : core.

Definition map (A : Type) : Type := INDEX -> option A.
Definition empty {A : Type} : map A := fun _ => None.
Definition update {A : Type} x v : map A -> map A :=
  fun m x' => if x =? x' then Some v else m x'.
Notation "x '|->' v ';' m" := (update x v m) (at level 100, v at next level, right associativity).
Notation "x '|->' v" := (update x v empty) (at level 100).

Property update_eq A (m : map A) x v : (x |-> v ; m) x = Some v.
Proof. repeat unfolds; rewrite eqb_refl; reflexivity. Defined.
Property update_neq A (m : map A) x1 x2 v :
  x2 <> x1 -> (x2 |-> v ; m) x1 = m x1.
Proof. intros Hneq. repeat unfolds. rewrite <- eqb_neq in Hneq. rewrite Hneq. reflexivity. Defined.

Definition mapeq {A} (m1 m2 : map A) : Type := forall x, m1 x = m2 x.
Notation "f ~ g" := (mapeq f g) (at level 70).
Fact eq_to_mapeq {A} (f g : map A) : f = g -> f ~ g.
Proof. congruence. Defined.
Fact mapeq_refl {A} (f : map A) : f ~ f.
Proof. congruence. Defined.
Fact mapeq_sym {A} (f g : map A) : f ~ g -> g ~ f.
Proof. congruence. Defined.
Fact mapeq_trans {A} (f g h : map A) : f ~ g -> g ~ h -> f ~ h.
Proof. congruence. Defined.
Fact mapeq_cong {A} {f g : map A} {x} {v} :
  f ~ g -> (x |-> v; f) ~ (x |-> v; g).
Proof. intros H x0. repeat unfolds. destruct (x =? x0); auto. Defined.
#[export]
Hint Resolve eq_to_mapeq mapeq_refl mapeq_sym : core.

Property update_shadow A (m : map A) x v1 v2 :
  (x |-> v2 ; x |-> v1 ; m) ~ (x |-> v2 ; m).
Proof. intros x0; repeat unfolds; destruct (x =? x0); reflexivity. Defined.
Property update_permute A (m : map A) x1 x2 v1 v2 :
  x1 <> x2 -> (x1 |-> v1 ; x2 |-> v2 ; m) ~ (x2 |-> v2 ; x1 |-> v1 ; m).
Proof. intros Hneq x; repeat unfolds; destruct (eqb_spec x1 x), (eqb_spec x2 x); auto; congruence. Defined.

Definition includedin {A} (m m' : map A) :=
  forall x v, m x = Some v -> m' x = Some v.
Property includedin_update A (m m' : map A) (x : INDEX) (vx : A) :
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold includedin.
  intros H y vy.
  destruct (eqb_spec x y) as [Hxy | Hxy].
  - subst y. repeat rewrite update_eq. auto.
  - repeat rewrite update_neq; auto.
Defined.