Inductive tree (A : Set) : Set :=
	| node : A -> list (tree A) -> tree A
.

From Coq Require Import List.
Import ListNotations.

Definition ind :=
	forall (A : Set) (P : tree A -> Prop),
	(forall (a : A)(l : list (tree A)), (forall x, In x l -> P x) -> P (node A a l))
	-> forall (t : tree A), P t.

Inductive is_sub {A : Set} : tree A -> tree A -> Set :=
	| sub_refl t : is_sub t t
	| sub_cons t1 t2 a l :
		is_sub t1 t2 ->
		In t2 l ->
		is_sub t1 (node _ a l)
.

Theorem tree_ind' : ind.
Admitted.

Fixpoint sz {A : Set} (t : tree A) : nat :=
	match t with
	| node _ _ l => S (fold_right (fun x acc => acc + sz x) 0 l)
	end.

Print sz.

Lemma endPt {A : Type} {x y : A} {P : A -> Type} : x = y -> P x -> P y.
Proof.
	intros. subst. auto.
Qed.

Axiom FF : forall {X : Type}, X.

(* Axioms (A : Set) (P : tree A -> Prop)
	(rec : forall (a : A)(l : list (tree A)), (forall x, In x l -> P x) -> P (node A a l)).
Check @list_rec (tree A) (fun l => forall x, In x l -> P x) (fun _ contra => match contra with end)
(fun a l IH x p => match p with or_introl eq => endPt eq _ | or_intror HIn => IH _ HIn end). *)

Fixpoint tree_ind'' (A : Set) (P : tree A -> Prop)
	(rec : forall (a : A)(l : list (tree A)), (forall x, In x l -> P x) -> P (node A a l)) (t : tree A) : P t :=
	match t with
	| node _ a l =>
		rec a l (@list_rec (tree A) (fun l => forall x, In x l -> P x) (fun _ contra => match contra with end)
(fun a l IH x p => match p with or_introl eq => endPt eq (tree_ind' A P rec a) | or_intror HIn => IH _ HIn end) l)
	end.

Fixpoint tree_ind' (A : Set) (P : tree A -> Prop)
	(rec : forall (a : A)(l : list (tree A)), (forall x, In x l -> P x) -> P (node A a l)) (t : tree A) {struct t} : P t.
Proof.
	destruct t.
	apply rec.
	intros.
	destruct l.
	- destruct H.
	- destruct H; subst.
		+ apply tree_ind'. eauto.
		+ apply tree_ind'. eauto.
Defined.