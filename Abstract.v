Require Import Bool.Bool.

Axiom INDEX : Type.
Axiom eqb : INDEX -> INDEX -> bool.
Infix "=?" := eqb (at level 70).
Axiom eqb_spec : forall x y, reflect (x=y) (x=?y).

Property eqb_refl x : (x =? x) = true. Admitted.
Property eqb_eq x y : (x =? y) = true <-> x = y. Admitted.
Property eqb_neq x y : (x =? y) = false <-> x <> y. Admitted.

Definition map (A : Type) : Type := INDEX -> option A.
Definition empty {A : Type} : map A := fun _ => None.
Definition update {A : Type} x v : map A -> map A :=
  fun m x' => if x =? x' then Some v else m x'.
Notation "x '|->' v ';' m" := (update x v m) (at level 100, v at next level, right associativity).
Notation "x '|->' v" := (update x v empty) (at level 100).

Property update_eq A (m : map A) x v : (x |-> v ; m) x = Some v. Admitted.
Property update_neq A (m : map A) x1 x2 v :
  x2 <> x1 -> (x2 |-> v ; m) x1 = m x1.
Admitted.

Definition mapeq {A} (m1 m2 : map A) : Type := forall x, m1 x = m2 x.
Notation "f ~ g" := (mapeq f g) (at level 70).
Fact eq_to_mapeq {A} (f g : map A) : f = g -> f ~ g. Admitted.
Fact mapeq_refl {A} (f : map A) : f ~ f. Admitted.
Fact mapeq_sym {A} (f g : map A) : f ~ g -> g ~ f. Admitted.
Fact mapeq_trans {A} (f g h : map A) : f ~ g -> g ~ h -> f ~ h. Admitted.
Fact mapeq_cong {A} {f g : map A} {x} {v} :
	f ~ g -> (x |-> v; f) ~ (x |-> v; g).
Admitted.

Property update_shadow A (m : map A) x v1 v2 :
  (x |-> v2 ; x |-> v1 ; m) ~ (x |-> v2 ; m).
Admitted.
Property update_permute A (m : map A) x1 x2 v1 v2 :
  x1 <> x2 -> (x1 |-> v1 ; x2 |-> v2 ; m) ~ (x2 |-> v2 ; x1 |-> v1 ; m).
Admitted.

Definition includedin {A} (m m' : map A) :=
  forall x v, m x = Some v -> m' x = Some v.
Property includedin_update A (m m' : map A) (x : INDEX) (vx : A) :
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
Admitted.