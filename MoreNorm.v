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
  Ltac eq_case :=
    repeat match goal with
    | |- _ |-- (if ?x =? ?y then _ else _) \in _ =>
      destruct (eqb_spec x y); subst ; eauto using weaken_empty
    | H : (?s |-> _ ; _) ?s = Some _ |- _ =>
      rewrite update_eq in H; inverts H; eauto using weaken_empty
    | H : (?s |-> _ ; _) ?t = _,
      H2 : ?s <> ?t |- _ =>
      rewrite update_neq in H; eauto using weaken_empty
    | H : (?s |-> _ ; _) ?t = _,
      H2 : ?t <> ?s |- _ =>
      rewrite update_neq in H; eauto using weaken_empty
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
  try econstructor; eauto; eq_case; enough_cong; try subst_cong;
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
    forall t1, empty |-- t1 \in T1 -> strong_norm t1 T1 ->
    strong_norm (tm_app t t1) T2
  | Ty_Empty => False
  | Ty_Unit => halt t
  | Ty_Sum T1 T2 => halt t /\
    (forall t1, t -->* tm_inl T2 t1
    -> normal t1
    -> strong_norm t1 T1) /\
    (forall t2, t -->* tm_inr T1 t2
    -> normal t2
    -> strong_norm t2 T2)
  | Ty_Prod T1 T2 =>
    strong_norm (tm_fst t) T1 /\
    strong_norm (tm_snd t) T2
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
    intros [Hs1 Hs2]; split; eauto.
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
    intros [Hs1 Hs2]; split; eauto.
  - (* list *) (* WRONG!!! *)
    eauto using halt_forward.


Corollary has_type__halt t T :
  empty |-- t \in T -> halt t.
Admitted.

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

Check prod.
Locate "*".
Locate "( x , y )".

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