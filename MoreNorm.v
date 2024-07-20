Require Import Bool.Bool.
Require Import Classes.CEquivalence.
Require Classes.CMorphisms.
From Lambda Require Import LibTactics.
Set Default Goal Selector "!".

Section STLC.

(* Map *)
Variable INDEX : Type.
Variable eqb : INDEX -> INDEX -> bool.
Infix "=?" := eqb (at level 70).
Variable eqb_spec : forall x y, reflect (x=y) (x=?y).

Property eqb_refl x : (x =? x) = true.
Proof. destruct (eqb_spec x x); auto. Defined.
Property eqb_eq x y : (x =? y) = true <-> x = y.
Proof. destruct (eqb_spec x y); split; auto. congruence. Defined.
Property eqb_neq x y : (x =? y) = false <-> x <> y.
Proof. destruct (eqb_spec x y); split; auto; congruence. Defined.
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
Fact mapeq_cong {A} (f g : map A) x v :
  f ~ g -> (x |-> v; f) ~ (x |-> v; g).
Proof. intros H x0. repeat unfolds. destruct (x =? x0); auto. Defined.
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

(* Syntax *)
Disable Notation "/\".
Disable Notation "\/".
Disable Notation "'exists'" (all).
Disable Notation "( x , y , .. , z )".
Notation "A /\ B" := (A * B)%type.
Notation "A \/ B" := (A + B)%type.
Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..)).
Notation "( x , .. , y , z )" := (pair x .. (pair y z) ..). (* (x,y,z) == (x,(y,z)) *)

Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Empty : ty
  | Ty_Unit  : ty
  | Ty_Sum   : ty -> ty -> ty
  | Ty_Prod  : ty -> ty -> ty
  | Ty_List  : ty -> ty
.

Inductive tm : Type :=
  | tm_var   : INDEX -> tm
  | tm_abs   : INDEX -> ty -> tm -> tm
  | tm_app   : tm -> tm -> tm
  | tm_elim  : tm -> ty -> tm
  | tm_unit  : tm
  | tm_inl   : ty -> tm -> tm
  | tm_inr   : ty -> tm -> tm
  | tm_Scase : tm -> INDEX -> tm -> INDEX -> tm -> tm
  | tm_pair  : tm -> tm -> tm
  | tm_fst   : tm -> tm
  | tm_snd   : tm -> tm
  | tm_nil   : ty -> tm
  | tm_cons  : tm -> tm -> tm
  | tm_Lcase : tm -> tm -> INDEX -> INDEX -> tm -> tm
  | tm_Lfix  : tm -> tm -> tm -> tm
  | tm_let   : INDEX -> tm -> tm -> tm
.

Declare Custom Entry stlc.
Declare Custom Entry stlc_ty.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "( x )" := x (in custom stlc_ty, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
Notation "{ x }" := x (in custom stlc at level 1, x constr).

Notation "S -> T"           := (Ty_Arrow S T)
  (in custom stlc_ty at level 50, right associativity).
Notation "'Empty'"          := (Ty_Empty)
  (in custom stlc_ty at level 0).
Notation "'Unit'"           := (Ty_Unit)
  (in custom stlc_ty at level 0).
Notation "S + T"            := (Ty_Sum S T)
  (in custom stlc_ty at level 50, right associativity).
Notation "S * T"            := (Ty_Prod S T)
  (in custom stlc_ty at level 40, right associativity).
Notation "'List' T"         := (Ty_List T)
  (in custom stlc_ty at level 0).

Reserved Notation "'[' x ':=' s ']' t"
  (in custom stlc at level 20, x constr).
Fixpoint subst (x : INDEX) (e : tm) (t : tm) : tm :=
  match t with
  | tm_var y => if y =? x then e else tm_var y
  | tm_app t1 t2 => tm_app <{[x:=e]t1}> <{[x:=e]t2}>
  | tm_abs y T t1 => tm_abs y T (if y =? x then t1 else <{[x:=e]t1}>)
  | tm_elim t1 T => tm_elim <{[x:=e]t1}> T
  | tm_unit => tm_unit
  | tm_inl T t1 => tm_inl T <{[x:=e]t1}>
  | tm_inr T t1 => tm_inr T <{[x:=e]t1}>
  | tm_Scase t1 y t2 z t3 =>
    tm_Scase <{[x:=e]t1}> y (if y =? x then t2 else <{[x:=e]t2}>) z (if z =? x then t3 else <{[x:=e]t3}>)
  | tm_pair t1 t2 => tm_pair <{[x:=e]t1}> <{[x:=e]t2}>
  | tm_fst t1 => tm_fst <{[x:=e]t1}>
  | tm_snd t1 => tm_snd <{[x:=e]t1}>
  | tm_nil T => tm_nil T
  | tm_cons t1 t2 => tm_cons <{[x:=e]t1}> <{[x:=e]t2}>
  | tm_Lcase t1 t2 y z t3 =>
    tm_Lcase <{[x:=e]t1}> <{[x:=e]t2}> y z (if y =? x then t3 else if z =? x then t3 else <{[x:=e]t3}>)
  | tm_Lfix t1 t2 t3 => tm_Lfix <{[x:=e]t1}> <{[x:=e]t2}> <{[x:=e]t3}>
  | tm_let y t1 t2 => tm_let y <{[x:=e]t1}> (if y =? x then t2 else <{[x:=e]t2}>)
  end
where "'[' x ':=' e ']' t" := (subst x e t) (in custom stlc).

Inductive value : tm -> Type :=
  | v_abs x T t     : value (tm_abs x T t)
  | v_unit          : value tm_unit
  | v_inl T t       : value t -> value (tm_inl T t)
  | v_inr T t       : value t -> value (tm_inr T t)
  | v_pair t1 t2    : value t1 -> value t2 -> value (tm_pair t1 t2)
  | v_nil T         : value (tm_nil T)
  | v_cons t1 t2    : value t1 -> value t2 -> value (tm_cons t1 t2)
.
Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).
Inductive step : tm -> tm -> Type :=
  | ST_app1 t1 t1' t2 :
    t1 --> t1' ->
    tm_app t1 t2 --> tm_app t1' t2
  | ST_app2 v1 t2 t2' :
    value v1 ->
    t2 --> t2' ->
    tm_app v1 t2 --> tm_app v1 t2'
  | ST_appAbs x T t v :
    value v ->
    tm_app (tm_abs x T t) v --> <{[x:=v]t}>
  | ST_elim1 t1 t1' T :
    t1 --> t1' ->
    tm_elim t1 T --> tm_elim t1' T
  | ST_inl1 T t1 t1' :
    t1 --> t1' ->
    tm_inl T t1 --> tm_inl T t1'
  | ST_inr1 T t1 t1' :
    t1 --> t1' ->
    tm_inr T t1 --> tm_inr T t1'
  | ST_Scase1 t1 t1' x t2 y t3 :
    t1 --> t1' ->
    tm_Scase t1 x t2 y t3 --> tm_Scase t1' x t2 y t3
  | ST_ScaseInl T v1 x t2 y t3 :
    value v1 ->
    tm_Scase (tm_inl T v1) x t2 y t3 --> <{[x:=v1]t2}>
  | ST_ScaseInr T t1 x t2 y t3 :
    value t1 ->
    tm_Scase (tm_inr T t1) x t2 y t3 --> <{[y:=t1]t3}>
  | ST_pair1 t1 t1' t2 :
    t1 --> t1' ->
    tm_pair t1 t2 --> tm_pair t1' t2
  | ST_pair2 v1 t2 t2' :
    value v1 ->
    t2 --> t2' ->
    tm_pair v1 t2 --> tm_pair v1 t2'
  | ST_fst1 t1 t1' :
    t1 --> t1' ->
    tm_fst t1 --> tm_fst t1'
  | ST_fstPair v1 v2 :
    value v1 ->
    value v2 ->
    tm_fst (tm_pair v1 v2) --> v1
  | ST_snd1 t1 t1' :
    t1 --> t1' ->
    tm_snd t1 --> tm_snd t1'
  | ST_sndPair v1 v2 :
    value v1 ->
    value v2 ->
    tm_snd (tm_pair v1 v2) --> v2
  | ST_cons1 t1 t1' t2 :
    t1 --> t1' ->
    tm_cons t1 t2 --> tm_cons t1' t2
  | ST_cons2 v1 t2 t2' :
    value v1 ->
    t2 --> t2' ->
    tm_cons v1 t2 --> tm_cons v1 t2'
  | ST_Lcase1 t1 t1' t2 x y t3 :
    t1 --> t1' ->
    tm_Lcase t1 t2 x y t3 --> tm_Lcase t1' t2 x y t3
  | ST_LcaseNil T t2 x y t3 :
    tm_Lcase (tm_nil T) t2 x y t3 --> t2
  | ST_LcaseCons v1 v2 t2 x y t3 :
    value v1 ->
    value v2 ->
    tm_Lcase (tm_cons v1 v2) t2 x y t3 --> <{[y:=v2][x:=v1]t3}>
  | ST_Lfix1 t1 t1' t2 t3 :
    t1 --> t1' ->
    tm_Lfix t1 t2 t3 --> tm_Lfix t1' t2 t3
  | ST_LfixNil T t2 t3 :
    tm_Lfix (tm_nil T) t2 t3 --> t2
  | ST_LfixCons v1 v2 t2 t3 :
    value v1 ->
    value v2 ->
    tm_Lfix (tm_cons v1 v2) t2 t3 --> tm_app (tm_app (tm_app t3 v1) v2) (tm_Lfix v2 t2 t3)
  | ST_let1 x t1 t1' t2 :
    t1 --> t1' ->
    tm_let x t1 t2 --> tm_let x t1' t2
  | ST_letValue x v1 t2 :
    value v1 ->
    tm_let x v1 t2 --> <{[x:=v1]t2}>
where "t '-->' t'" := (step t t').
Hint Constructors step : core.

Definition context : Type := map ty.
Reserved Notation "Gamma '|--' t '\in' T" (at level 40, T custom stlc_ty at level 0).
Inductive has_type : tm -> ty -> context -> Type :=
  | T_Var (Gamma : context) x T : Gamma x = Some T ->
    Gamma |-- tm_var x \in T
  | T_Abs (Gamma : context) x T1 T2 t :
    (x |-> T1; Gamma) |-- t \in T2 ->
    Gamma |-- tm_abs x T1 t \in (T1 -> T2)
  | T_App (Gamma : context) T1 T2 t1 t2 :
    Gamma |-- t1 \in (T1 -> T2) ->
    Gamma |-- t2 \in T1 ->
    Gamma |-- tm_app t1 t2 \in T2
  | T_Elim (Gamma : context) T t :
    Gamma |-- t \in Empty ->
    Gamma |-- tm_elim t T \in T
  | T_Unit Gamma :
    Gamma |-- tm_unit \in Unit
  | T_Inl Gamma T1 T2 t :
    Gamma |-- t \in T1 ->
    Gamma |-- tm_inl T2 t \in (T1 + T2)
  | T_Inr Gamma T1 T2 t :
    Gamma |-- t \in T2 ->
    Gamma |-- tm_inr T1 t \in (T1 + T2)
  | T_Scase Gamma t1 x t2 y t3 T T1 T2 :
    Gamma |-- t1 \in (T1 + T2) ->
    (x |-> T1; Gamma) |-- t2 \in T ->
    (y |-> T2; Gamma) |-- t3 \in T ->
    Gamma |-- tm_Scase t1 x t2 y t3 \in T
  | T_Pair Gamma t1 t2 T1 T2 :
    Gamma |-- t1 \in T1 ->
    Gamma |-- t2 \in T2 ->
    Gamma |-- tm_pair t1 t2 \in (T1 * T2)
  | T_Fst Gamma t T1 T2 :
    Gamma |-- t \in (T1 * T2) ->
    Gamma |-- tm_fst t \in T1
  | T_Snd Gamma t T1 T2 :
    Gamma |-- t \in (T1 * T2) ->
    Gamma |-- tm_snd t \in T2
  | T_Nil Gamma T :
    Gamma |-- tm_nil T \in List T
  | T_Cons Gamma t1 t2 T :
    Gamma |-- t1 \in T ->
    Gamma |-- t2 \in List T ->
    Gamma |-- tm_cons t1 t2 \in List T
  | T_Lcase Gamma t1 t2 x y t3 T U :
    Gamma |-- t1 \in List T ->
    Gamma |-- t2 \in U ->
    (x |-> T; y |-> <{{List T}}>; Gamma) |-- t3 \in U ->
    Gamma |-- tm_Lcase t1 t2 x y t3 \in U
  | T_Lfix Gamma t1 t2 t3 T U :
    Gamma |-- t1 \in List T ->
    Gamma |-- t2 \in U ->
    Gamma |-- t3 \in (T -> List T -> U -> U) ->
    Gamma |-- tm_Lfix t1 t2 t3 \in U
  | T_Let Gamma x t1 t2 T1 T2 :
    Gamma |-- t1 \in T1 ->
    (x |-> T1; Gamma) |-- t2 \in T2 ->
    Gamma |-- tm_let x t1 t2 \in T2
where "Gamma '|--' t '\in' T" := (has_type t T Gamma).
Hint Constructors has_type : core.


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

(* Instance equiv_rel {A} :
  Equivalence (@mapeq A) :=
{|
  Equivalence_Reflexive := mapeq_refl;
  Equivalence_Symmetric := mapeq_sym;
  Equivalence_Transitive := mapeq_trans
|}.

Instance update_morphism {A} x v :
  CMorphisms.Proper (CMorphisms.respectful (@mapeq A) (@mapeq A)) (update x v) := fun _ _ => mapeq_cong _ _ _ _.

Instance has_type_morphism t T :
  CMorphisms.Proper (CMorphisms.respectful mapeq iffT) (has_type t T) :=
  (fun m1 m2 Hequ =>
   (has_type_extensionality m1 m2 t T Hequ,
   has_type_extensionality m2 m1 t T (mapeq_sym m1 m2 Hequ))). *)

Theorem progress : forall t T,
  empty |-- t \in T ->
  value t \/ exists t', t --> t'.
Proof.
  Ltac instantiate_IH :=
    repeat match goal with
    | IH : empty = empty -> _ |- _ =>
      specialize (IH eq_refl);
      destruct IH as [? | [? ?]]; eauto
    end.
  Ltac invert_value :=
    try match goal with
    | Hv : value ?t,
      HT : empty |-- ?t \in _ |- _ =>
      solve [inverts Hv; inverts HT; eauto]
    end.
  intros t T HT. remember empty as Gamma.
  induction HT; try subst Gamma; eauto;
  instantiate_IH; invert_value.
  discriminate.
Defined.

Ltac eq_case :=
  match goal with
  | |- _ |-- (if ?x =? ?y then _ else _) \in _ =>
    destruct (eqb_spec x y); subst
  | H : (?s |-> _ ; _) ?s = Some _ |- _ =>
    rewrite update_eq in H; inverts H
  | H : (?s |-> _ ; _) ?t = _,
    H2 : ?s <> ?t |- _ =>
    rewrite update_neq in H
  | H : (?s |-> _ ; _) ?t = _,
    H2 : ?t <> ?s |- _ =>
    rewrite update_neq in H
  end.

Theorem subst_type x U v :
  empty |-- v \in U -> forall t Gamma T,
  (x |-> U ; Gamma) |-- t \in T ->
  Gamma |-- <{[x:=v]t}> \in T.
Proof.
  Ltac remember_context Gamma :=
    match goal with
    | H : has_type ?t ?T Gamma |- ?g =>
      let H2 := fresh "H" in
      let p := fresh "p" in
        assert (H2 : forall (p : context), p ~ Gamma -> has_type t T p -> g); [clear H; intros p Hequ H | eauto]
    end.
  Ltac subst_context G :=
    repeat match goal with
    | Hequ : G ~ _,
      Heq : G _ = _ |- _ =>
      rewrite Hequ in Heq
    end.
  Ltac enough_cong :=
    match goal with
    | H : _ |-- ?t \in ?T |- _ |-- ?t \in ?T =>
      gen H; eapply has_type_extensionality
    | H : forall G, _ -> G |-- ?t \in ?T |- _ |-- ?t \in ?T =>
      apply H
    end.
  Ltac subst_cong :=
    match goal with
    | Hequ : ?G ~ _ |- ?G ~ _ =>
      apply (mapeq_trans _ _ _ Hequ)
    | Hequ : ?G ~ _ |- (_ |-> _; ?G) ~ _ =>
      apply (mapeq_trans _ _ _ (mapeq_cong _ _ _ _ Hequ))
    | Hequ : ?G ~ _ |- (_ |-> _; _ |-> _; ?G) ~ _ =>
      apply (mapeq_trans _ _ _ (mapeq_cong _ _ _ _ (mapeq_cong _ _ _ _ Hequ)))
    end.
  introv HTv HT.
  remember_context (x |-> U ; Gamma); gen Gamma.
  induction HT;
  intros Gamma' Heq; subst_context Gamma;
  simpl; eauto;
  try econstructor; eauto; repeat (eq_case; eauto using weaken_empty); enough_cong; try subst_cong;
  eauto using update_shadow, update_permute, mapeq_cong.
  - (* list ABA=AB *)
    unfold update. intros z.
    destruct (x =? z), (y =? z); reflexivity.
  - (* list ABC=CAB *)
    eapply mapeq_trans.
    + eapply mapeq_cong.
      eapply update_permute; auto.
    + eapply update_permute; auto.
Defined.

Theorem preservation t t' T :
  empty |-- t \in T -> t --> t' -> empty |-- t' \in T.
Proof.
  intros HT. remember empty as Gamma. gen t'.
  induction HT; subst Gamma; try discriminate;
  introv HS; inverts HS; eauto;
  try match goal with
  | H : has_type _ (?c ?T1) _ |- _ =>
    inverts H
  | H : has_type _ (?c ?T1 ?T2) _ |- _ =>
    inverts H
  end;
  eauto using subst_type.
Defined.

Inductive multi {X : Type} (R : crelation X) : crelation X :=
  | multi_refl x : multi R x x
  | multi_step x y z : R x y -> multi R y z -> multi R x z.
Hint Constructors multi : core.

Fact multi_R (X : Type) (R : crelation X) x y : R x y -> multi R x y.
Proof. eauto. Defined.

Theorem multi_trans (X : Type) (R : crelation X) x y z :
  multi R x y -> multi R y z -> multi R x z.
Proof.
  intros G; induction G; eauto.
Defined.

Notation " t '-->*' t' " := (multi step t t') (at level 40).
Definition normal t := forall t', t --> t' -> False.
Hint Unfold normal : core.
(* Hint Immediate term : idents …. *)

Property value__normal : forall t, value t -> normal t.
Proof.
  induction t; unfold normal in *;
  intros Hv t' HS; inverts Hv; inverts HS; eauto.
Defined.

Lemma determinism t t1 t2 :
  t --> t1 ->
  t --> t2 ->
  t1 = t2.
Proof.
  intros HS1; gen t2.
  induction HS1; intros ? HS2; inverts HS2; eauto;
  try solve[f_equal; eauto];
  try match goal with
    | Hv : value ?t, HS : ?t --> _ |- _ =>
    false; apply (value__normal _ Hv _ HS)
    | HS : ?t --> _ |- _ =>
    solve [false; assert (Hv : value t); [eauto | apply (value__normal _ Hv _ HS)]]
  end.
Defined.

Fact normal_multi__refl t1 t2 : normal t1 -> t1 -->* t2 -> t1 = t2.
Proof.
  intros Hnf HM; inverts HM; [eauto| exfalso; eauto].
Defined.

Property multi_preservation t1 t2 T :
  t1 -->* t2 ->
  empty |-- t1 \in T ->
  empty |-- t2 \in T.
Proof.
  intros HM; induction HM; eauto using preservation.
Defined.

Property step_multi_diamond t t1 t2 :
  t --> t1 -> t -->* t2 -> normal t2 ->
  t1 -->* t2.
Proof.
  intros HS HM Hnf. inverts HM; try solve[false; eauto].
  eapply determinism in HS; eauto. rewrite <- HS. auto.
Defined.

Definition halt t := exists t', t -->* t' /\ normal t'.
Hint Transparent halt : core.
Hint Unfold halt : core.

Property halt_back t t' :
  t --> t' ->
  halt t' ->
  halt t.
Proof.
  intros ? (? & ? & ?); eauto.
Defined.

Property halt_forward t t' :
  t --> t' ->
  halt t ->
  halt t'.
Proof.
  intros ? (? & ? & ?). eauto using step_multi_diamond.
Defined.

Fixpoint strong_norm (t : tm) (T : ty) : Type :=
  match T with
  | Ty_Arrow T1 T2 => halt t  /\
    forall t1,
    empty |-- t1 \in T1 ->
    strong_norm t1 T1 ->
    strong_norm (tm_app t t1) T2
  | Ty_Empty => False
  | Ty_Unit => halt t
  | Ty_Sum T1 T2 => halt t /\
    (forall t1, t -->* tm_inl T2 t1 ->
    normal t1 ->
    strong_norm t1 T1) /\
    (forall t2, t -->* tm_inr T1 t2 ->
    normal t2 ->
    strong_norm t2 T2)
  | Ty_Prod T1 T2 =>
    halt t /\
    (forall t1 t2, t -->* tm_pair t1 t2 ->
    normal t1 -> normal t2 ->
    strong_norm t1 T1 /\ strong_norm t2 T2)
  | Ty_List T => halt t
  end.

Lemma strong_norm_back T :
  forall t t', t --> t' ->
  strong_norm t' T ->
  strong_norm t T.
Proof.
  induction T; intros t t' HS; simpl.
  - (* arrow *)
    intros [Hh Hs]; split;
    eauto using halt_back.
  - (* empty *) auto.
  - (* unit *) eauto using halt_back.
  - (* sum *)
    intros [Hh [Hs1 Hs2]]; repeat split; eauto using halt_back.
    + intros t1 HM Hnf. apply Hs1; auto.
      eapply step_multi_diamond; eauto.
      intros t3 HS3. inverts HS3.
      eauto.
    + intros t2 HM Hnf. apply Hs2; auto.
      eapply step_multi_diamond; eauto.
      intros t3 HS3. inverts HS3.
      eauto.
  - (* prod *)
    intros [Hh Hs]. split; eauto using halt_back.
    introv HM Hnf1 Hnf2; apply Hs; eauto.
    assert (Hnf : normal (tm_pair t1 t2)).
    {
      intros t3 HS3. inverts HS3; eauto.
    }
    eauto using step_multi_diamond.
  - (* list *) (* WRONG!!! *)
    eauto using halt_back.
Defined.

Lemma strong_norm_forward T :
  forall t t', t --> t' ->
  strong_norm t T ->
  strong_norm t' T.
Proof.
  induction T; intros t t' HS; simpl.
  - (* arrow *)
    intros [Hh Hs]; split;
    eauto using halt_forward.
  - (* empty *) auto.
  - (* unit *) eauto using halt_forward.
  - (* sum *)
    intros [Hh [Hs1 Hs2]]; repeat split; eauto using halt_forward.
  - (* prod *)
    intros [Hh Hs]; split; eauto using halt_forward.
  - (* list *) (* WRONG!!! *)
    eauto using halt_forward.
Defined.

Corollary strong_norm_multi_back T :
  forall t t', t -->* t' ->
  strong_norm t' T ->
  strong_norm t T.
Proof.
  introv HM; induction HM; eauto using strong_norm_back.
Defined.

Corollary strong_norm_multi_forward T :
  forall t t', t -->* t' ->
  strong_norm t T ->
  strong_norm t' T.
Proof.
  introv HM; induction HM; eauto using strong_norm_forward.
Defined.

Proposition strong_norm__halt T :
  forall t, strong_norm t T -> halt t.
Proof.
  induction T; simpl; intros t Hs; intuition.
Defined.

Definition contextv := list (INDEX * (tm * ty)).
Fixpoint to_context (l : contextv) : context :=
  match l with
  | nil => empty
  | cons (x,t,T) l' => x|->T; to_context l'
  end
.
Inductive close : contextv -> Type :=
  | closen : close nil
  | closec x t T G : close G -> empty |-- t \in T -> strong_norm t T -> close (cons (x,t,T) G)
.
Fixpoint substm (l : contextv) (t : tm) : tm :=
  match l with
  | nil => t
  | cons (x,t',_) l' => substm l' <{[x:=t']t}>
  end
.
Notation "[/ l ] t" := (substm l t) (in custom stlc at level 20, l constr).

Fact wt_subst_eq t :
  forall Gamma T x t',
  Gamma |-- t \in T ->
  Gamma x = None ->
  <{[x:=t']t}> = t.
Proof.
  Ltac remove_eq :=
    match goal with
    | |- (if ?x =? ?y then _ else _) = _ =>
      destruct (eqb_spec x y); [subst |
        assert (forall (Gamma : context) t, Gamma y = None -> (x |-> t; Gamma) y = None);
        [intros; rewrite update_neq; eauto | eauto]
      ]
    end.
  induction t; introv HT Heq; simpl; inverts HT; eauto;
  f_equal ; repeat remove_eq; eauto.
  congruence.
Defined.

Corollary wt_substm_eq (Gamma' : contextv) :
  forall t Gamma T, Gamma |-- t \in T ->
  (forall x t1 T1, Lists.List.In (x,t1,T1) Gamma' -> Gamma x = None) ->
  substm Gamma' t = t.
Proof.
  induction Gamma' as [|[x [t1 T1]] ?]; intros; simpl in *; eauto.
  erewrite wt_subst_eq; eauto.
Defined.

Lemma var_case Gammav x T :
  (to_context Gammav) x = Some T ->
  close Gammav ->
  strong_norm (substm Gammav (tm_var x)) T.
Proof.
  induction Gammav; simpl; try discriminate.
  destruct a as (x1 & t & T1).
  intros Heq Hc. inverts Hc.
  destruct (eqb_spec x x1); subst; eq_case; eauto.
  erewrite wt_substm_eq; eauto.
Defined.

Fixpoint filter_out (x : INDEX) (l : contextv) : contextv :=
  match l with
  | nil => nil
  | cons (x',t,T) l' => if x =? x' then filter_out x l' else cons (x',t,T) (filter_out x l')
  end
.

Proposition substm_abs : forall x T1 Gammav t,
  substm Gammav (tm_abs x T1 t) = tm_abs x T1 (substm (filter_out x Gammav) t).
Proof.
  induction Gammav as [|[x' [t' T']] ?]; simpl; intros; eauto.
  rewrite IHGammav. f_equal. destruct (eqb_spec x x'); subst; eauto.
Defined.

Fact value__halt t : value t -> halt t.
Proof.
  intros Hv. exists t; eauto using value__normal.
Defined.

Fact app_cong2 : forall v1 t2 t2',
  value v1 ->
  t2 -->* t2' ->
  tm_app v1 t2 -->* tm_app v1 t2'.
Proof.
  introv Hv HM. induction HM; eauto.
Defined.

Property normal_wt__value t T :
  normal t -> empty |-- t \in T -> value t.
Proof.
  intros Hnf HT. destruct (progress _ _ HT); eauto.
  destruct s; false; eauto.
Defined.

Lemma subst_shadow : forall x t1 t2, <{[x:=t1]t2}> = t2 -> forall t, <{[x:=t1]([x:=t2]t)}> = <{[x:=t2]t}>.
  induction t; simpl; f_equal; eauto;
  repeat match goal with |- context [?x =? ?y] => destruct (eqb_spec x y); subst; simpl; eauto; try congruence end.
Defined.

Lemma subst_permute : forall x1 x2 t1 t2, x1 <> x2 -> <{[x1:=t1]t2}> = t2 -> <{[x2:=t2]t1}> = t1 -> forall t, <{[x1:=t1]([x2:=t2]t)}> = <{[x2:=t2]([x1:=t1]t)}>.
  introv Hneq Heq1 Heq2.
  induction t; simpl; eauto;
  repeat match goal with
  | |- context [?x =? ?y] => destruct (eqb_spec x y); subst; simpl; eauto
  | |- _ => congruence
  end.
Defined.

Theorem substm_subst : forall Gammav x t1 T t,
  close Gammav ->
  empty |-- t1 \in T ->
  <{[x:=t1]([/filter_out x Gammav]t)}> = <{[/Gammav]([x:=t1]t)}>.
Proof.
  induction Gammav as [|[x' [t' T']]?]; intros; simpl; eauto.
  inverts X.
  destruct (eqb_spec x x'); subst.
  - erewrite IHGammav; eauto.
    f_equal. symmetry. eapply subst_shadow.
    eapply wt_subst_eq; eauto.
  - simpl. erewrite IHGammav; eauto.
    f_equal. eapply subst_permute; eauto using wt_subst_eq.
Defined.

Lemma substm_wt t Gammav T :
  (to_context Gammav) |-- t \in T ->
  close Gammav ->
  empty |-- <{[/Gammav]t}> \in T.
Proof.
  gen t T.
  induction Gammav as [|[x [t1 T1]] ?]; simpl; eauto.
  intros t T HT Hc. inverts Hc.
  eauto using subst_type.
Defined.

Proposition substm_app Gammav :
  forall t1 t2,
  substm Gammav (tm_app t1 t2) = tm_app (substm Gammav t1) (substm Gammav t2).
Proof.
  induction Gammav as [|[x [t T]] ?]; simpl; eauto.
Defined.

Proposition substm_inl Gammav :
  forall T t,
  substm Gammav (tm_inl T t) = tm_inl T (substm Gammav t).
Proof.
  induction Gammav as [|[x [t T]] ?]; simpl; eauto.
Defined.

Proposition substm_inr Gammav :
  forall T t,
  substm Gammav (tm_inr T t) = tm_inr T (substm Gammav t).
Proof.
  induction Gammav as [|[x [t T]] ?]; simpl; eauto.
Defined.

Proposition substm_pair Gammav :
  forall t1 t2,
  substm Gammav (tm_pair t1 t2) = tm_pair (substm Gammav t1) (substm Gammav t2).
Proof.
  induction Gammav as [|[x [t T]] ?]; simpl; eauto.
Defined.

Proposition substm_fst Gammav :
  forall t,
  substm Gammav (tm_fst t) = tm_fst (substm Gammav t).
Proof.
  induction Gammav as [|[x [t T]] ?]; simpl; eauto.
Defined.

Proposition substm_snd Gammav :
  forall t,
  substm Gammav (tm_snd t) = tm_snd (substm Gammav t).
Proof.
  induction Gammav as [|[x [t T]] ?]; simpl; eauto.
Defined.

Proposition halt__inl_halt t T :
  halt t -> halt (tm_inl T t).
Proof.
  intros [t' [HM Hnf]]. induction HM.
  - exists (tm_inl T x); split; eauto. intros t' HS. inverts HS. eauto.
  - apply IHHM in Hnf. gen Hnf. apply halt_back. auto.
Defined.

Proposition halt__inr_halt t T :
  halt t -> halt (tm_inr T t).
Proof.
  intros [t' [HM Hnf]]. induction HM.
  - exists (tm_inr T x); split; eauto. intros t' HS. inverts HS. eauto.
  - apply IHHM in Hnf. gen Hnf. apply halt_back. auto.
Defined.

Proposition inl_multistep_elim t t' T :
  tm_inl T t -->* t' ->
  exists t'', t' = tm_inl T t'' /\ t -->* t''.
Proof.
  remember (tm_inl T t) as lt.
  intros HM.
  gen t. induction HM; intros; subst; eauto.
  inverts r. edestruct IHHM as (t'' & Heq & HM2); eauto.
Defined.

Proposition inr_multistep_elim t t' T :
  tm_inr T t -->* t' ->
  exists t'', t' = tm_inr T t'' /\ t -->* t''.
Proof.
  remember (tm_inr T t) as lt.
  intros HM.
  gen t. induction HM; intros; subst; eauto.
  inverts r. edestruct IHHM as (t'' & Heq & HM2); eauto.
Defined.

Proposition pair_multistep_elim t1 t2 t1' t2' :
  tm_pair t1 t2 -->* tm_pair t1' t2' ->
  t1 -->* t1' /\ t2 -->* t2'.
Proof.
  remember (tm_pair t1 t2) as t.
  remember (tm_pair t1' t2') as t'.
  intros HM.
  gen t1 t2 t1' t2'. induction HM; intros; subst; eauto.
  - inverts Heqt'; eauto.
  - inverts r; destruct (IHHM _ _ eq_refl _ _ eq_refl); eauto.
Defined.


Proposition substm_Scase Gammav :
  forall t1 x t2 y t3,
  substm Gammav (tm_Scase t1 x t2 y t3) = tm_Scase (substm Gammav t1) x (substm (filter_out x Gammav) t2) y (substm (filter_out y Gammav) t3).
Proof.
  induction Gammav as [|[x' [t' T']] ?]; intros; simpl; eauto.
  rewrite IHGammav; f_equal.
  - destruct (x =? x'); reflexivity.
  - destruct (y =? x'); reflexivity.
Defined.

Proposition Scase_cong1 t1 t1' x t2 y t3 :
  t1 -->* t1' ->
  tm_Scase t1 x t2 y t3 -->* tm_Scase t1' x t2 y t3.
Proof.
  intros HM. induction HM; eauto.
Defined.

Proposition pair_cong t1 t1' t2 t2' :
  t1 -->* t1' ->
  value t1' ->
  t2 -->* t2' ->
  tm_pair t1 t2 -->* tm_pair t1' t2'.
Proof.
  intros.
  eapply multi_trans with (tm_pair t1' t2).
  - clear X0 X1. induction X; eauto.
  - induction X1; eauto.
Defined.

Proposition fst_cong t t' :
  t -->* t' ->
  tm_fst t -->* tm_fst t'.
Proof.
  intros HM; induction HM; eauto.
Defined.

Proposition snd_cong t t' :
  t -->* t' ->
  tm_snd t -->* tm_snd t'.
Proof.
  intros HM; induction HM; eauto.
Defined.

Theorem has_type__strong_norm t Gamma T :
  (to_context Gamma) |-- t \in T ->
  close Gamma ->
  strong_norm <{[/Gamma]t}> T.
Proof.
  introv HT. remember (to_context Gamma) as G. gen Gamma.
  induction HT; intros Gv Heq Hc; subst; simpl.
  - (* var *) eauto using var_case.
  - (* abs *) split.
    + rewrite substm_abs. eauto using value__halt.
    + intros t1 HT1 Hs.
      destruct (strong_norm__halt _ _ Hs) as (t1' & HM & Hnf).
      specializes IHHT (cons (x,t1',T1) Gv) ___.
      * constructor; eauto using multi_preservation, strong_norm_multi_forward.
      * simpl in IHHT. gen IHHT.
        eapply (strong_norm_multi_back); eauto.
        rewrite substm_abs.
        eapply multi_trans.
        -- eapply app_cong2; eauto.
        -- eapply multi_R.
           erewrite <- substm_subst; eauto using normal_wt__value, multi_preservation.
  - (* app *)
    specializes IHHT1 Hc ___. simpl in IHHT1.
    destruct IHHT1 as [(t1' & HM & Hnf) IH12].
    specializes IHHT2 Hc ___. specializes IH12 IHHT2.
    + eauto using substm_wt.
    + rewrite substm_app. eauto.
  - (* elim *) false. simpl in IHHT. eauto.
  - (* unit *) apply value__halt.
    induction Gv as [|[? [? ?]] ?]; simpl in *; eauto.
    inverts Hc; eauto.
  - (* inl *) rewrite substm_inl. repeat split.
    + apply halt__inl_halt.
      eapply strong_norm__halt. eauto.
    + intros. apply inl_multistep_elim in X.
      destruct X as (t'' & Heq & HM).
      inverts Heq.
      specializes IHHT; eauto. gen IHHT.
      eapply strong_norm_multi_forward; eauto.
    + intros. apply inl_multistep_elim in X.
      destruct X as (t'' & Heq & HM).
      discriminate.
  - (* inr *) rewrite substm_inr. repeat split.
    + apply halt__inr_halt.
      eapply strong_norm__halt. eauto.
    + intros. apply inr_multistep_elim in X.
      destruct X as (t'' & Heq & HM).
      discriminate.
    + intros. apply inr_multistep_elim in X.
      destruct X as (t'' & Heq & HM).
      inverts Heq.
      specializes IHHT; eauto. gen IHHT.
      eapply strong_norm_multi_forward; eauto.
  - (* Scase *) rewrite substm_Scase.
    specializes IHHT1; eauto.
    lets (t' & HM & Hnf) : strong_norm__halt IHHT1.
    assert (HT : empty |-- t' \in (T1 + T2)).
    {
      eapply multi_preservation; eauto.
      eapply substm_wt; eauto.
    }
    assert (Hv : value t').
    {
      eauto using normal_wt__value.
    }
    inverts HT; inverts Hv.
    + specializes IHHT2 (cons (x,t,T1) Gv) ___.
      * constructor; eauto.
        destruct IHHT1 as [_ [IH _]].
        specializes IH HM.
        eauto using value__normal.
      * simpl in IHHT2. erewrite <-substm_subst in IHHT2; eauto. gen IHHT2.
        eapply strong_norm_multi_back; eauto.
        eapply multi_trans with (tm_Scase (tm_inl T2 t) x <{ [/filter_out x Gv] t2 }> y <{ [/filter_out y Gv] t3 }>).
        -- apply Scase_cong1. auto.
        -- apply multi_R. constructor. auto.
    + specializes IHHT3 (cons (y,t,T2) Gv) ___.
      * constructor; eauto.
        destruct IHHT1 as [_ [_ IH]].
        specializes IH HM.
        eauto using value__normal.
      * simpl in IHHT3. erewrite <-substm_subst in IHHT3; eauto. gen IHHT3.
        eapply strong_norm_multi_back; eauto.
        eapply multi_trans with (tm_Scase (tm_inr T1 t) x <{ [/filter_out x Gv] t2 }> y <{ [/filter_out y Gv] t3 }>).
        -- apply Scase_cong1. auto.
        -- apply multi_R. constructor. auto.
  - (* pair *) rewrite substm_pair.
    specializes IHHT1; eauto.
    specializes IHHT2; eauto.
    lets (t1' & HM1 & Hnf1) : strong_norm__halt IHHT1.
    lets (t2' & HM2 & Hnf2) : strong_norm__halt IHHT2.
    split.
    + exists (tm_pair t1' t2'); split; eauto.
      * assert (Hv : value t1').
        {
          eapply normal_wt__value; eauto.
          eapply multi_preservation; eauto.
          eapply substm_wt; eauto.
        }
        eapply pair_cong; eauto.
      * intros t3 HS3. inverts HS3; eauto.
    + intros. apply pair_multistep_elim in X.
      destruct X. eauto using strong_norm_multi_forward.
  - (* fst *) rewrite substm_fst.
    specializes IHHT; eauto. simpl in IHHT.
    destruct IHHT as [[t' [HM Hnf]] IH].
    assert (HT' : empty |-- t' \in (T1 * T2)).
    {
      eapply multi_preservation; eauto.
      eapply substm_wt; eauto.
    }
    assert (Hv : value t').
    {
      eauto using normal_wt__value.
    }
    inverts HT'; inverts Hv.
    specializes IH ___; eauto using value__normal.
    destruct IH as [IH _]. gen IH.
    apply strong_norm_multi_back; eauto.
    eapply multi_trans with (tm_fst (tm_pair t1 t2)).
    + eapply fst_cong; eauto.
    + apply multi_R. constructor; auto.
  - (* snd *) rewrite substm_snd.
    specializes IHHT; eauto. simpl in IHHT.
    destruct IHHT as [[t' [HM Hnf]] IH].
    assert (HT' : empty |-- t' \in (T1 * T2)).
    {
      eapply multi_preservation; eauto.
      eapply substm_wt; eauto.
    }
    assert (Hv : value t').
    {
      eauto using normal_wt__value.
    }
    inverts HT'; inverts Hv.
    specializes IH ___; eauto using value__normal.
    destruct IH as [_ IH]. gen IH.
    apply strong_norm_multi_back; eauto.
    eapply multi_trans with (tm_snd (tm_pair t1 t2)).
    + eapply snd_cong; eauto.
    + apply multi_R. constructor; auto.
  - (* nil *) admit.
  - (* cons *) admit.
  - (* Lcase *) admit.
  - (* Lfix *) admit.
  - (* let *) admit.
Admitted.

Corollary has_type__halt t T :
  empty |-- t \in T -> halt t.
Proof.
  intros HT. eapply strong_norm__halt;
  eapply has_type__strong_norm with (Gamma := nil); eauto. constructor.
Defined.

(* Computing *)
Definition pp_progress t T (H : empty |-- t \in T) :
  option tm :=
  match progress _ _ H with
  | inl _ => None
  | inr (existT _ t' _) => Some t'
  end.

Require Import List.
Import ListNotations.
Fixpoint simp_list t1 t2 (H : t1 -->* t2) : list tm :=
  match H with
  | multi_refl _ _ => [t2]
  | multi_step _ _ _ t1' t2' H' => t1 :: simp_list _ _ H'
  end.

Fixpoint simp_cor (l : list tm) : Type :=
  match l with
  | [] => True
  | (t1 :: l') =>
    match l' with
    | [] => True
    | (t2 :: l'') => t1 --> t2 /\ simp_cor l'
    end
  end.

Property simp_COR t1 t2 (H : t1 -->* t2) : simp_cor (simp_list _ _ H).
Proof.
  enough (H1 : simp_cor (simp_list _ _ H) /\ match simp_list _ _ H with | [] => False | (x :: _) => x = t1 end). {destruct H1. eauto. }
  induction H; simpl; try split; eauto.
  destruct IHmulti, (simp_list y z H); subst; try split; eauto.
Defined.

Definition compute_list t T :
  empty |-- t \in T -> list tm :=
  fun HT => match has_type__halt _ _ HT with
  | existT _ t' (pair HM Hnf) => simp_list _ _ HM
  end.

End STLC.

Check progress.

Import Nat.
Theorem my_eqb_spec (x y : nat) : reflect (x = y) (x =? y).
Proof.
  gen y. induction x.
  - intros []; simpl; constructor; congruence.
  - intros []; simpl.
    + constructor. congruence.
    + destruct (IHx n); constructor; congruence.
Defined.

Arguments tm_app {INDEX}.
Arguments tm_abs {INDEX}.
Arguments tm_var {INDEX}.
Arguments tm_unit {INDEX}.
Definition eg : has_type nat eqb
  (tm_app
    (tm_app
      (tm_app (tm_abs 0 (Ty_Arrow Ty_Unit Ty_Unit) (tm_abs 1 (Ty_Arrow Ty_Unit Ty_Unit) (tm_abs 2 Ty_Unit (tm_app (tm_var 0) (tm_app (tm_var 1) (tm_var 2)))))) (tm_abs 3 Ty_Unit (tm_var 3)))
      (tm_abs 3 Ty_Unit tm_unit))
    tm_unit)
  Ty_Unit  (empty _).
Proof.
  repeat (try reflexivity; econstructor).
Defined.

Compute (compute_list _ _ my_eqb_spec _ _ eg).