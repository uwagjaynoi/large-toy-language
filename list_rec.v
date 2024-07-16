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