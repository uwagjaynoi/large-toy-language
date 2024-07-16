Axiom A : Type.
Axiom le : A -> A -> Prop.
Notation "x <= y" := (le x y).
Axiom le_refl : forall x, x <= x.
Axiom le_trans : forall x y z, x <= y -> y <= z -> x <= z.

Require Import Bool.Bool.

Axiom INDEX : Type.
Axiom eqb : INDEX -> INDEX -> bool.
Infix "=?" := eqb (at level 70).
Axiom eqb_spec : forall x y, reflect (x=y) (x=?y).

Definition record := list (INDEX * A).

Require Import List.
Import ListNotations.

Fixpoint lookup (r : record) (i : INDEX) : list A :=
	match r with
	| nil => []
	| (i', a) :: r' => if i =? i' then a :: lookup r' i else lookup r' i
	end.

Fixpoint list_le (l1 l2 : list A) : Prop :=
	match l1, l2 with
	| _, [] => True
	| a1 :: l1', a2 :: l2' => a1 <= a2 /\ list_le l1' l2'
	| [], _ :: _ => False
	end.
Definition includedin (r r' : record) :=
	forall i, list_le (lookup r i) (lookup r' i).

Inductive subtype : record -> record -> Prop :=
	| S_refl r : subtype r r
	| S_trans r1 r2 r3 : subtype r1 r2 -> subtype r2 r3 -> subtype r1 r3
	| S_nil r : subtype r []
	| S_dep a1 a2 r1 r2 i :
		le a1 a2 ->
		subtype r1 r2 ->
		subtype ((i, a1) :: r1) ((i, a2) :: r2)
	| S_perm r1 i1 i2 a1 a2 :
		i1 <> i2 ->
		subtype ((i1, a1) :: (i2, a2) :: r1) ((i2, a2) :: (i1, a1) :: r1)
.

From Lambda Require Import LibTactics.

#[local]
Hint Unfold includedin : core.
#[local]
Hint Constructors subtype : core.
#[local]
Hint Resolve le_refl : core.
#[local]
Hint Resolve le_trans : core.

Lemma Lle_refl l : list_le l l.
Proof.
	induction l; simpl; eauto.
Qed.

Lemma Lle_trans l1 l2 l3 : list_le l1 l2 -> list_le l2 l3 -> list_le l1 l3.
Proof.
	gen l1 l2. induction l3; intros [] []; simpl; intros; eauto; try solve [false].
	destruct H, H0; split; eauto.
Qed.

Lemma Lle_cong a l1 l2 : list_le l1 l2 -> list_le (a :: l1) (a :: l2).
Proof.
	intros. simpl; eauto.
Qed.

#[local]
Hint Resolve Lle_refl Lle_trans Lle_cong : core.

Theorem sound : forall r r', subtype r r' -> includedin r r'.
Proof.
	intros. induction H; unfold includedin in *.
	- eauto.
	- eauto.
	- simpl. intros. destruct (lookup r i); simpl; trivial.
	- intros. specialize (IHsubtype i0). simpl in *.
		destruct (eqb_spec i0 i); simpl; eauto.
	- intros. simpl in *.
		destruct (eqb_spec i i1), (eqb_spec i i2);
		try subst i1; try subst i2; try congruence; eauto.
Qed.

(* Fixpoint remove (i : INDEX) (r : record) : record :=
	match r with
	| nil => nil
	| (i', a) :: r' => if i =? i' then r' else (i', a) :: remove i r'
	end. *)

Lemma lookup_concat r1 r2 i : lookup (r1 ++ r2) i = lookup r1 i ++ lookup r2 i.
Proof.
	induction r1; simpl; eauto.
	destruct a as [i' a], (i =? i'); eauto.
	rewrite IHr1. reflexivity.
Qed.

Lemma lookup_hd r1 i a l :
	lookup r1 i = a :: l ->
	exists r2 r3, r1 = r2 ++ (i, a) :: r3 /\ lookup r2 i = [].
Proof.
	gen a l. induction r1; intros; simpl in *; eauto.
	- discriminate.
	- destruct a as [i' a].
		destruct (eqb_spec i i'); subst.
		+ inverts H.
			exists (nil : record), r1; eauto.
		+ apply IHr1 in H. destruct H as (r2 & r3 & ? & ?).
			subst r1.
			exists ((i', a) :: r2), r3; split; eauto.
			simpl. destruct (eqb_spec i i'); eauto. congruence.
Qed.

Lemma sub_commute1 r1 r2 i a :
	lookup r1 i = [] ->
	subtype (r1 ++ (i,a) :: r2) ((i,a) :: r1 ++ r2).
Proof.
	gen r2. induction r1; intros.
	- simpl. auto.
	- simpl in *.
		destruct a0 as [i' a1]; destruct (eqb_spec i i'); try discriminate.
		eapply S_trans with ((i',a1)::(i,a)::r1++r2).
		+ constructor; auto.
		+ constructor. auto.
Qed.

Fact eqb_refl x : (x =? x) = true.
Proof.
	destruct (eqb_spec x x); eauto; congruence.
Qed.

Fact eqb_neq x y : x <> y -> (x =? y) = false.
Proof.
	destruct (eqb_spec x y); congruence.
Qed.

Theorem complete : forall r r', includedin r r' -> subtype r r'.
Proof.
	intros r r'. gen r. induction r'.
	- intros. eauto.
	- intros. destruct a as (i, a).
		assert (Hi := H i). simpl in Hi. rewrite eqb_refl in Hi.
		destruct (lookup r i) as [|a' l] eqn:Hi'; simpl in Hi; tryfalse.
		destruct Hi.
		apply lookup_hd in Hi'. destruct Hi' as (r1 & r2 & ? & ?).
		subst r.
		eapply S_trans with ((i,a')::(r1++r2)).
		+ apply sub_commute1. auto.
		+ constructor; auto. apply IHr'.
			intros i0. specialize (H i0). simpl in H.
			destruct (eqb_spec i0 i); subst.
			* rewrite lookup_concat in H |- *. rewrite H3 in *.
				simpl in *. rewrite eqb_refl in H. destruct H.
				auto.
			* rewrite lookup_concat in H |- *.
				simpl in H. rewrite (eqb_neq _ _ n) in H. auto.
Qed.

Fixpoint lookup1 (r : record) (i : INDEX) : option A :=
	match r with
	| nil => None
	| (i', a) :: r' => if i =? i' then Some a else lookup1 r' i
	end.

Search (list _ -> option _).

Lemma consist r i : lookup1 r i = hd_error (lookup r i).
Proof.
	induction r; simpl; eauto.
	destruct a as [j a]; destruct (i =? j); simpl.
	- reflexivity.
	- assumption.
Qed.

Inductive subtype2 : record -> record -> Prop :=
	| S2_nil r : subtype2 r []
	| S2_cons r1 r2 i a :
		lookup1 r1 i = Some a ->
		subtype2 r1 r2 ->
		subtype2 r1 ((i, a) :: r2)
.

Definition includedin2 : record -> record -> Prop :=
	fun r r' => forall i a, In a (lookup r' i) ->
	exists a', lookup1 r i = Some a' /\ le a' a.

Definition includedin0 : record -> record -> Prop :=
	fun r r' => forall i a, lookup1 r' i = Some a ->
	exists a', lookup1 r i = Some a' /\ le a' a.

Fact includedin_1 r1 r2: includedin r1 r2 -> includedin0 r1 r2.
Proof.
	induction r2; unfold includedin, includedin0 in *; simpl; intros; eauto.
	- discriminate.
	- destruct a as [i' a]. specialize (H i).
		destruct (i =? i').
		+ inverts H0.
			assert (Heq := consist r1 i).
			destruct (lookup r1 i); simpl in *; tryfalse.
			destruct H. eauto.
		+ assert (Heq2 := consist r2 i).
			rewrite H0 in Heq2.
			destruct (lookup r2 i); try discriminate.
			inverts Heq2.
			assert (Heq1 := consist r1 i).
			destruct (lookup r1 i); tryfalse.
			destruct H. simpl in Heq1.
			eauto.
Qed.

Fact includedin_2 r1 r2: includedin2 r1 r2 -> includedin0 r1 r2.
Proof.
	induction r2; unfold includedin2, includedin0 in *; simpl; intros; eauto.
	- discriminate.
	- destruct a as [i' a]. specialize (H i).
		destruct (i =? i').
		+ inverts H0. destruct (H a0); eauto.
			left. reflexivity.
		+ destruct (H a0).
			* assert (Heq1 := consist r2 i).
				destruct (lookup r2 i); simpl in *; try congruence.
				left. congruence.
			* destruct H1. eauto.
Qed.
