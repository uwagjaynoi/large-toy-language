Require Import Bool.Bool.
Require Import Classes.CRelationClasses Classes.CEquivalence Classes.CMorphisms.
Require Setoids.Setoid.
Require Import Setoid Morphisms CMorphisms.
From PLF Require Import LibTactics.
Set Default Goal Selector "!".

Section STLC.

(* Assumptions *)
Variable INDEX : Set.
Variable eqb : INDEX -> INDEX -> bool.
Infix "=?" := eqb (at level 70).
Variable eqb_spec : forall x y, reflect (x=y) (x=?y).

(* Map *)
Lemma eqb_refl x : (x=?x) = true.
Proof. destruct (eqb_spec x x); auto. Defined.
Lemma eqb_eq x y : (x =? y) = true <-> x = y.
Proof. destruct (eqb_spec x y); split; auto. congruence. Defined.
Lemma eqb_neq x y : (x =? y) = false <-> x <> y.
Proof. destruct (eqb_spec x y); split; auto; congruence. Defined.
Hint Resolve eqb_eq eqb_neq : core.

Definition total_map (A : Set) := INDEX -> A.
Definition t_empty {A : Set} (v : A) : total_map A := (fun _ => v).
Definition t_update {A : Set} x v : total_map A -> total_map A :=
  fun m x' => if x =? x' then v else m x'.
Definition partial_map (A : Set) := total_map (option A).
Definition empty {A : Set} : partial_map A := t_empty None.
Definition update {A : Set} x v : partial_map A -> partial_map A := t_update x (Some v).
Notation "x '|->' v ';' m" := (update x v m) (at level 100, v at next level, right associativity).
Notation "x '|->' v" := (update x v empty) (at level 100).

Lemma update_eq A (m : partial_map A) x v : (x |-> v ; m) x = Some v.
Proof. repeat unfolds; rewrite eqb_refl; reflexivity. Defined.
Theorem update_neq A (m : partial_map A) x1 x2 v :
  x2 <> x1 -> (x2 |-> v ; m) x1 = m x1.
Proof. intros Hneq. repeat unfolds. rewrite <- eqb_neq in Hneq. rewrite Hneq. reflexivity. Defined.

Definition mapeq {A} (m1 m2 : partial_map A) : Set := forall x, m1 x = m2 x.
Notation "f ~ g" := (mapeq f g) (at level 70).
Lemma eq_to_mapeq {A} (f g : partial_map A) : f = g -> f ~ g.
Proof. congruence. Defined.
Lemma mapeq_refl {A} (f : partial_map A) : f ~ f.
Proof. congruence. Defined.
Lemma mapeq_sym {A} (f g : partial_map A) : f ~ g -> g ~ f.
Proof. congruence. Defined.
Lemma mapeq_trans {A} (f g h : partial_map A) : f ~ g -> g ~ h -> f ~ h.
Proof. congruence. Defined.
Lemma mapeq_cong {A} {f g : partial_map A} {x} {v} : f ~ g -> (x |-> v; f) ~ (x |-> v; g).
Proof. intros H x0. repeat unfolds. destruct (x =? x0); auto. Defined.
Local Hint Resolve eq_to_mapeq mapeq_refl mapeq_sym : core.

Lemma update_shadow A (m : partial_map A) x v1 v2 :
  (x |-> v2 ; x |-> v1 ; m) ~ (x |-> v2 ; m).
Proof. intros x0; repeat unfolds; destruct (x =? x0); reflexivity. Defined.
Theorem update_permute A (m : partial_map A) x1 x2 v1 v2 :
  x1 <> x2 -> (x1 |-> v1 ; x2 |-> v2 ; m) ~ (x2 |-> v2 ; x1 |-> v1 ; m).
Proof. intros Hneq x; repeat unfolds; destruct (eqb_spec x1 x), (eqb_spec x2 x); auto; congruence. Defined.

Definition includedin {A} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.
Lemma includedin_update A (m m' : partial_map A) (x : INDEX) (vx : A) :
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold includedin.
  intros H y vy.
  destruct (eqb_spec x y) as [Hxy | Hxy].
  - subst y. repeat rewrite update_eq. auto.
  - repeat rewrite update_neq; auto.
Defined.

(* Logic *)
Disable Notation "/\".
Disable Notation "\/".
Disable Notation "'exists'" (all).
Disable Notation "( x , y , .. , z )".
Notation "A /\ B" := (A * B)%type.
Notation "A \/ B" := (A + B)%type.
Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..)).
Notation "( x , .. , y , z )" := (pair x .. (pair y z) ..).

(* Syntax *)
Inductive ty : Type :=
  | Ty_Bot   : ty
  | Ty_Top   : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Empty : ty
  | Ty_Unit  : ty
  (* | Ty_Bool  : ty *)
  (* | Ty_Nat   : ty *)
  (* | Ty_Sum   : ty -> ty -> ty *)
  (* | Ty_List  : ty -> ty *)
  (* | Ty_Prod  : ty -> ty -> ty *)
  (* | Ty_RNil  : ty *)
  (* | Ty_RCons : T -> ty -> ty -> ty *)
  (* | Ty_VNil  : ty *)
  (* | Ty_VCons : T -> ty -> ty -> ty *)
.

Inductive tm : Type :=
  | tm_var   : INDEX -> tm
  | tm_abs   : INDEX -> ty -> tm -> tm
  | tm_app   : tm -> tm -> tm
  | tm_elim  : tm -> ty -> tm
  | tm_unit  : tm
.

(* Notation *)
Declare Custom Entry stlc.
Declare Custom Entry stlc_ty.

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "( x )" := x (in custom stlc_ty, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).

Notation "'Bot'"   := (Ty_Bot)       (in custom stlc_ty at level 0).
Notation "'Top'"   := (Ty_Top)       (in custom stlc_ty at level 0).
Notation "S -> T"  := (Ty_Arrow S T) (in custom stlc_ty at level 50, right associativity).
Notation "'Empty'" := (Ty_Empty)     (in custom stlc_ty at level 0).
Notation "'Unit'"  := (Ty_Unit)      (in custom stlc_ty at level 0).

Coercion tm_var : INDEX >-> tm.
Notation "\ x : T , t" :=
  (tm_abs x T t) (in custom stlc at level 90,
                  x at level 99,
                  T custom stlc_ty at level 99,
                  t custom stlc at level 99,
                  left associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "t '.elim' T" := (tm_elim t T) (in custom stlc at level 1).
Notation "'unit'" := tm_unit (in custom stlc at level 0).
Notation "{ x }" := x (in custom stlc at level 1, x constr).

(* Operations *)
Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : INDEX) (e : tm) (t : tm) : tm :=
  match t with
  | tm_var s => if s =? x then e else tm_var s
  | <{t1 t2}> => <{([x:=e]t1) ([x:=e]t2)}>
  | <{\s:T, t1}> => let t1' := (if s =? x then t1 else <{[x:=e]t1}>) in <{\s:T, t1'}>
  | <{t.elim T1}> => <{([x:=e]t).elim T1}>
  | <{unit}> => <{unit}>
  end
where "'[' x ':=' e ']' t" := (subst x e t) (in custom stlc).

Inductive value : tm -> Type :=
  | v_abs x T t : value <{\x:T,t}>
  | v_unit      : value <{unit}>
.
Local Hint Constructors value : core.

Definition valuec (t : tm) : bool :=
  match t with
  | tm_abs _ _ _ | tm_unit => true
  | tm_var _ | tm_app _ _ | tm_elim _ _ => false
  end.

Inductive reflectT (P : Set) : bool -> Set :=
  | ReflectTT : P -> reflectT P true
  | ReflectTF : (P -> False) -> reflectT P false
.

Theorem value_reflect : forall t, reflectT (value t) (valuec t).
Proof.
  induction t; simpl; constructor; auto; intros Hv; inverts Hv.
Defined.

Reserved Notation "t '--->' t'" (at level 40).
Inductive step : tm -> tm -> Type :=
  | ST_App1 t1 t1' t2 : t1 ---> t1' ->
    <{t1 t2}> ---> <{t1' t2}>
  | ST_App2 v1 t2 t2' : value v1 -> t2 ---> t2' ->
    <{v1 t2}> ---> <{v1 t2'}>
  | ST_AppAbs x T t v : value v ->
    <{(\x:T,t) v}> ---> <{[x:=v]t}>
  | ST_Elim1 t1 t1' T : t1 ---> t1' ->
    <{t1.elim T}> ---> <{t1'.elim T}>
where "t '--->' t'" := (step t t').
Local Hint Constructors step : core.

Notation " 'some' x <- e1 'then' e2 'else' e3 " := (match e1 with
                              | Some x => e2
                              | None => e3
                              end)
         (x name, right associativity, at level 60).

Definition get_abs : tm -> (INDEX -> tm -> option tm) -> option tm :=
  fun t f => match t with
  | <{\x:_,t1}> => f x t1
  | _ => None
  end.
Notation " 'abs' x 'of' t <<- e1 ;; e2" := (get_abs e1 (fun x t => e2))
         (right associativity, at level 60).
Notation " 'assertv' t ;; e" :=
  (if valuec t then e else None)
  (right associativity, at level 60).

Fixpoint stepc (t : tm) : option tm :=
  match t with
  | tm_var _ | tm_abs _ _ _ | tm_unit => None
  | <{t1 t2}> =>
    some t1' <- stepc t1 then Some <{t1' t2}> else
    some t2' <- stepc t2 then (assertv t1 ;; Some <{t1 t2'}>) else
    assertv t2;; abs x of t <<- t1 ;; Some <{[x:=t2]t}>
  | <{t1.elim T}> =>
    some t1' <- stepc t1 then Some <{t1'.elim T}> else
    None
  end.

Theorem value__normal_form : forall t t', value t -> t ---> t' -> False.
Proof.
  introv Hv. destruct Hv; intros Hs; inverts Hs.
Defined.

Theorem value__no_stepc : forall t, value t -> stepc t = None.
Proof.
  introv Hv; inverts Hv; reflexivity.
Defined.

Lemma value__valuec : forall t, value t -> valuec t = true.
Proof.
  introv Hv. destruct (value_reflect t); auto.
Defined.

Ltac unwrap1 :=
  repeat match goal with
    | H : Some _ = Some _ |- _ => injection H as H; subst
    | H : some t <- ?e then _ else _ = _ |- _ => destruct e as [t|]
    | H : assertv ?t ;; _ = _ |- _ => destruct (value_reflect t)
    | H : (abs x of t <<- ?t1 ;; _) = _ |- _ =>
    destruct t1; simpl in H; try discriminate
    (* | H : forall t', iffT (Some ?t' = Some t') (?t ---> t') |- _ => *)
  end.

Ltac simp_monad :=
  repeat match goal with
    | H : value ?t |- _ => rewrite (value__no_stepc _ H)
    | H : value ?t |- _ => rewrite (value__valuec _ H)
    | IH : forall t', ?t ---> t' -> stepc ?t = Some t' ,
      H : ?t ---> ?t' |- _ =>
      apply IH in H; rewrite H
  end; try reflexivity.

Theorem step_sound : forall t t', (stepc t = Some t') -> (t ---> t').
  induction t; simpl; intros t';
  try discriminate;
  intros Hc; unwrap1; try discriminate; eauto.
Defined.

Theorem step_complete : forall t t', (t ---> t') -> (stepc t = Some t').
Proof.
  induction t; simpl; intros t';
  try solve[intros HS; inverts HS; simp_monad].
Defined.

(* Typing *)
Reserved Notation "T '<:' U" (at level 40).
Inductive subtype : ty -> ty -> Set :=
  | S_Refl            T : T <: T
  | S_Bot             T : <{{Bot}}> <: T
  | S_Top             T : T <: <{{Top}}>
  | S_Arrow T1 T2 U1 U2 : T2 <: T1 -> U1 <: U2 -> <{{T1 -> U1}}> <: <{{T2 -> U2}}>
where "T '<:' U" := (subtype T U).
Local Hint Constructors subtype : core.

(* Subtype Lemmas *)
Lemma sub_inversion_arrow U V1 V2 :
  U <: <{{V1 -> V2}}> -> U = <{{Bot}}> \/
  exists U1 U2, U = <{{U1 -> U2}}> /\
  V1 <: U1 /\ U2 <: V2.
Proof. intros HSU; inverts HSU; eauto 6. Defined.

Lemma sup_inversion_arrow U1 U2 V :
  <{{U1 -> U2}}> <: V -> V = <{{Top}}> \/
  exists V1 V2, V = <{{V1 -> V2}}> /\
  V1 <: U1 /\ U2 <: V2.
Proof. intros HSU; inverts HSU; eauto 6. Defined.

Lemma sub_inversion_bot U :
  U <: <{{Bot}}> -> U = <{{Bot}}>.
Proof. intros HSU; inverts HSU; eauto. Defined.

Lemma sub_inversion_empty U :
  U <: <{{Empty}}> -> U = <{{Bot}}> \/ U = <{{Empty}}>.
Proof. intros HSU; inverts HSU; eauto. Defined.

Theorem subtype_trans T1 T2 T3 : T1 <: T2 -> T2 <: T3 -> T1 <: T3.
Proof.
  gen T2 T3.
  cut ((forall T2 T3, T1 <: T2 -> T2 <: T3 -> T1 <: T3) /\ (forall T2 T3, T2 <: T1 -> T3 <: T2 -> T3 <: T1)). {intros []. auto. }
  induction T1;
  split; intros T2 T3 HSU1 HSU2; auto;
  inverts HSU1; auto;
  inverts HSU2; auto;
  destruct IHT1_1, IHT1_2; eauto.
Defined.

Hint Extern 1 (subtype ?S ?U) =>
  match goal with
  | H: subtype S ?T |- _ => apply (@subtype_trans S T U)
  | H: subtype ?T U |- _ => apply (@subtype_trans S T U)
  end : core.

Lemma sub_arrow_arrow U1 U2 V1 V2 :
  <{{U1 -> U2}}> <: <{{V1 -> V2}}> ->
  V1 <: U1 /\ U2 <: V2.
Proof.
  intros HSU. apply sub_inversion_arrow in HSU.
  destruct HSU as [Hcontra|(U3 & U4 & Heq & HSU1 & HSU2)].
  - discriminate.
  - inverts Heq. auto.
Defined.

Ltac sub_inverts H :=
  match type of H with
  | <{{_ -> _}}> <: <{{_ -> _}}> => destruct (sub_arrow_arrow _ _ _ _ H); clear H
  | _ <: <{{_ -> _}}> => destruct (sub_inversion_arrow _ _ _ H) as [?|(?&?&?&?&?)]; subst
  | <{{_ -> _}}> <: _ => destruct (sup_inversion_arrow _ _ _ H) as [?|(?&?&?&?&?)]; subst
  | _ <: <{{Bot}}> => apply sub_inversion_bot in H; subst
  | _ <: <{{Empty}}> => destruct (sub_inversion_empty _ H) as [?|?]; subst
  end.

Fixpoint subtypecp (S1 S2 : ty) : bool * bool :=
  match S1, S2 with
  | <{{Bot}}>, <{{Bot}}> => (true, true)
  | <{{Bot}}>, _ => (true, false)
  | <{{Top}}>, <{{Top}}> => (true, true)
  | <{{Top}}>, _ => (false, true)
  | <{{S11 -> S12}}>, <{{Bot}}> => (false, true)
  | <{{S11 -> S12}}>, <{{Top}}> => (true, false)
  | <{{S11 -> S12}}>, <{{S21 -> S22}}> => (snd (subtypecp S11 S21) && fst (subtypecp S12 S22), fst (subtypecp S11 S21) && snd (subtypecp S12 S22))
  | <{{_ -> _}}>, _ => (false, false)
  | <{{Empty}}>, <{{Bot}}> => (false, true)
  | <{{Empty}}>, <{{Top}}> => (true, false)
  | <{{Empty}}>, <{{Empty}}> => (true, true)
  | <{{Empty}}>, _ => (false, false)
  | <{{Unit}}>, <{{Bot}}> => (false, true)
  | <{{Unit}}>, <{{Top}}> => (true, false)
  | <{{Unit}}>, <{{Unit}}> => (true, true)
  | <{{Unit}}>, _ => (false, false)
  end.

Theorem subtype_reflectp : forall S1 S2, reflectT (S1 <: S2) (fst (subtypecp S1 S2)) /\ reflectT (S2 <: S1) (snd (subtypecp S1 S2)).
  induction S1 as [| |S11 IH1 S12 IH2| |]; intros [| |S21 S22| |]; simpl;
  try solve[split; constructor; eauto; intros HSU; inverts HSU].
  destruct (IH1 S21) as [H1 H2], (IH2 S22) as [H3 H4];
  destruct (fst (subtypecp S11 S21));
  destruct (snd (subtypecp S11 S21));
  destruct (fst (subtypecp S12 S22));
  destruct (snd (subtypecp S12 S22));
  inverts H1; inverts H2; inverts H3; inverts H4; simpl;
  split; constructor; eauto;
  intros Hcontra; sub_inverts Hcontra; eauto.
Defined.

Definition subtypec (S1 S2 : ty) : bool := fst (subtypecp S1 S2).
Theorem subtype_reflect : forall S1 S2, reflectT (S1 <: S2) (subtypec S1 S2).
Proof. intros; destruct (subtype_reflectp S1 S2); eauto. Defined.

Lemma subtypec_refl T : subtypec T T = true.
Proof. destruct (subtype_reflect T T); eauto. Defined.

Definition context : Set := partial_map ty.
Reserved Notation "Gamma '|--' t '\in' T" (at level 40, t custom stlc, T custom stlc_ty at level 0).
Inductive has_type : tm -> ty -> context -> Set :=
  | T_Var (Gamma : context) (x : INDEX) T : Gamma x = Some T ->
    Gamma |-- x \in T
  | T_Abs (Gamma : context) (x : INDEX) T1 T2 t :
    (x |-> T2; Gamma) |-- t \in T1 ->
    Gamma |-- \x:T2,t \in (T2 -> T1)
  | T_App (Gamma : context) T1 T2 t1 t2 :
    Gamma |-- t1 \in (T1 -> T2) ->
    Gamma |-- t2 \in T1 ->
    Gamma |-- <{t1 t2}> \in T2
  | T_Elim (Gamma : context) T t :
    Gamma |-- t \in Empty ->
    Gamma |-- t.elim T \in T
  | T_Unit Gamma :
    Gamma |-- <{unit}> \in Unit
  | T_Sub Gamma T1 T2 t : T1 <: T2 ->
    Gamma |-- t \in T1 ->
    Gamma |-- t \in T2
where "Gamma '|--' t '\in' T" := (has_type t T Gamma).
Local Hint Constructors has_type : core.


(* value *)

Lemma value_bot t :
  empty |-- t \in Bot ->
  value t ->
  False.
Proof.
  intros HT. remember empty as emp. remember Ty_Bot as bot.
  induction HT; subst; try discriminate; try solve[intros Hv; inverts Hv].
  - (* sub *) eauto using sub_inversion_bot.
Defined.

Lemma value_empty t :
  empty |-- t \in Empty ->
  value t ->
  False.
Proof.
  intros HT. remember empty as emp. remember Ty_Empty as Emp.
  induction HT; subst; try discriminate; try solve[intros Hv; inverts Hv].
  - (* sub *) apply sub_inversion_empty in s. destruct s; eauto. subst. eauto using value_bot.
Defined.

Lemma value_arrow t T1 T2 :
  empty |-- t \in (T1 -> T2) ->
  value t ->
  exists T1', T1 <: T1' /\
  exists x u, t = <{\x:T1', u}> /\ ((x |-> T1') |-- u \in T2).
Proof.
  intros HT.
  remember empty as emp; gen Heqemp.
  remember <{{T1 -> T2}}> as TArr; gen T1 T2.
  induction HT; intros T1' T2' Hemp Heq Hv; subst; try discriminate;
  try solve[inverts Hv].
  - (* abs *)
    injection Hemp as ? ?; subst; eauto 6.
  - (* sub *)
    sub_inverts s.
    + false. eauto using value_bot.
    + specialize (IHHT _ _ eq_refl eq_refl Hv).
      destruct IHHT as (T1 & HSU3 & x1 & u & Heq & HT2). subst.
      exists T1.
      eauto 7.
Defined.

Lemma value__nf (t : tm) : value t -> forall t', t ---> t' -> False.
  intros HV t' HS; inverts HV; inverts HS.
Defined.

Lemma type_inversion_var Gamma (x : INDEX) T :
  Gamma |-- x \in T ->
  exists T', Gamma x = Some T' /\ T' <: T.
Proof.
  remember (tm_var x) as t.
  intros HT. induction HT; inverts Heqt; eauto.
  destruct IHHT as (? & ? & ?); eauto using subtype_trans.
Defined.

Inductive hastype_index : Set :=
  | i_var | i_abs | i_app | i_elim | i_unit | i_sub
.

Lemma debug_has_type_induction :
	      forall
         P : forall (t : tm) (t0 : ty) (c : context), c |-- t \in t0 -> Set,
       (forall (Gamma : context) (x : INDEX) (T : ty) (e : Gamma x = Some T),
        (exists iii, iii=i_var) ->
        P x T Gamma (T_Var Gamma x T e)) ->
       (forall (Gamma : context) (x : INDEX) (T1 T2 : ty)
          (t : tm) (h : (x |-> T2; Gamma) |-- t \in T1),
        P t T1 (x |-> T2; Gamma) h ->
        (exists iii, iii=i_abs) ->
        P <{ \ x : T2, t }> <{{ T2 -> T1 }}> Gamma (T_Abs Gamma x T1 T2 t h)) ->
       (forall (Gamma : context) (T1 T2 : ty) (t1 t2 : tm)
          (h : Gamma |-- t1 \in (T1 -> T2)),
        P t1 <{{ T1 -> T2 }}> Gamma h ->
        forall h0 : Gamma |-- t2 \in T1,
        P t2 T1 Gamma h0 ->
        (exists iii, iii=i_app) ->
        P <{ t1 t2 }> T2 Gamma (T_App Gamma T1 T2 t1 t2 h h0)) ->
       (forall (Gamma : context) (T : ty) (t : tm)
          (h : Gamma |-- t \in Empty),
        P t <{{ Empty }}> Gamma h ->
        (exists iii, iii=i_elim) ->
        P <{ t .elim T }> T Gamma (T_Elim Gamma T t h)) ->
       (forall Gamma : context,
        (exists iii, iii=i_unit) ->
        P <{ unit }> <{{ Unit }}> Gamma (T_Unit Gamma)) ->
       (forall (Gamma : context) (T1 T2 : ty) (t : tm)
          (s : T1 <: T2) (h : Gamma |-- t \in T1),
        (exists iii, iii=i_sub) ->
        P t T1 Gamma h -> P t T2 Gamma (T_Sub Gamma T1 T2 t s h)) ->
       forall (t : tm) (t0 : ty) (c : context) (h : c |-- t \in t0),
       P t t0 c h.
Proof.
  intros P H1 H2 H3 H4 H5 H6.
  induction h; eauto.
Defined.

Lemma abs_not_in_bot Gamma x T t : Gamma |-- \x:T,t \in Bot -> False.
Proof.
  remember <{\x:T,t}> as t0. remember <{{Bot}}> as T0.
  intros HT; induction HT; intros; inverts Heqt0; inverts HeqT0.
  sub_inverts s. auto.
Defined.

Definition sub_context (Gamma Gamma' : context) :=
  forall x T', Gamma' x = Some T' ->
  exists T, Gamma x = Some T /\ T <: T'.
Lemma sub_context_upd Gamma Gamma' x T1 T2 :
  sub_context Gamma Gamma' ->
  T1 <: T2 ->
  sub_context (x|->T1; Gamma) (x|->T2; Gamma').
Proof.
  intros H HSU x0 T' Heq.
  destruct (eqb_spec x x0); subst.
  - rewrite update_eq in *. inverts Heq. eauto.
  - rewrite update_neq in *; eauto.
Defined.

Lemma sub_context_refl Gamma:
  sub_context Gamma Gamma.
Proof. unfold sub_context; eauto. Defined.
Lemma sub_context_upd_refl1 Gamma Gamma' x T :
  sub_context Gamma Gamma' ->
  sub_context (x|->T; Gamma) (x|->T; Gamma').
Proof. eauto using sub_context_upd. Defined.
Lemma sub_context_upd_refl2 Gamma x T1 T2 :
  T1 <: T2 ->
  sub_context (x|->T1; Gamma) (x|->T2; Gamma).
Proof. eauto using sub_context_upd, sub_context_refl. Defined.

Theorem sub_context_type Gamma Gamma' t T :
  sub_context Gamma Gamma' ->
  Gamma' |-- t \in T ->
  Gamma |-- t \in T.
Proof.
  intros Hsub HT. gen Gamma. induction HT; intros; eauto.
  - (* var *) destruct (Hsub _ _ e) as [T' [Heq HSU]]. eauto.
  - (* abs *) eauto using sub_context_upd_refl1.
Defined.

Lemma type_inversion_abs Gamma x T0 T1 T2 t :
  Gamma |-- \x:T0,t \in <{{T1 -> T2}}> ->
  T1 <: T0 /\ (x|->T1; Gamma) |-- t \in T2.
Proof.
  remember (tm_abs x T0 t) as t0. remember <{{T1 -> T2}}> as T3.
  introv HT. gen T1 T2.
  (* gen x T1 t. *)
  (* eapply debug_has_type_induction. *)
  induction HT; intros; inverts Heqt0.
  - inverts HeqT3; eauto.
  - subst. sub_inverts s.
    + false. eauto using abs_not_in_bot.
    + edestruct IHHT as [IH1 IH2]; split; eauto.
      eapply T_Sub with (T1 := x1); eauto.
      eapply sub_context_type; eauto.
      eapply sub_context_upd_refl2; eauto.
Defined.

Lemma type_inversion_app Gamma T2 t1 t2 :
  Gamma |-- t1 t2 \in T2 ->
  exists T1, Gamma |-- t1 \in <{{T1 -> T2}}> /\ Gamma |-- t2 \in T1.
Proof.
  remember <{t1 t2}> as t0. introv HT.
  induction HT; intros; inverts Heqt0; eauto.
  destruct IHHT as (T3 & HT1 & HT2); eauto.
Defined.

Lemma type_inversion_elim Gamma T1 T2 t :
  Gamma |-- t.elim T1 \in T2 ->
  Gamma |-- t \in Empty /\ T1 <: T2.
Proof.
  remember <{t.elim T1}> as t0. introv HT.
  induction HT; intros; inverts Heqt0; eauto.
  destruct IHHT as (IH1 & IH2); eauto.
Defined.

Fixpoint eqb_ty (T1 T2 : ty) : bool :=
  match T1,T2 with
  | <{{Bot}}>, <{{Bot}}> => true
  | <{{Top}}>, <{{Top}}> => true
  | <{{T11 -> T12}}>, <{{T21 -> T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{Empty}}>, <{{Empty}}> => true
  | <{{Unit}}>, <{{Unit}}> => true
  | _,_ =>
      false
  end
.

Theorem eqb_ty_reflect (T1 T2 : ty) : reflectT (T1 = T2) (eqb_ty T1 T2).
Proof.
  gen T2.
  induction T1 as [| |T11 IH1 T12 IH2| |]; intros [| |T21 T22 | |]; simpl;
  try solve[constructor; congruence].
  specialize (IH1 T21); specialize (IH2 T22);
  destruct (eqb_ty T11 T21), (eqb_ty T12 T22); inverts IH1; inverts IH2; constructor; congruence.
Defined.

Lemma eqb_ty_refl T : eqb_ty T T = true.
Proof.
  destruct (eqb_ty_reflect T T); eauto.
Defined.

Definition get_to : ty -> (ty -> ty -> option ty) -> option ty :=
  fun T f => match T with
  | <{{T1 -> T2}}> => f T1 T2
  | _ => None
  end.
Notation " T1 'to' T2 <<- e1 ;; e2" := (get_to e1 (fun T1 T2 => e2))
         (right associativity, at level 60).
Notation " T1 == T2 ;; e" := (if eqb_ty T1 T2 then e else None) (right associativity, at level 60).
Notation " T1 'sub' T2 ;; e" := (if subtypec T1 T2 then e else None) (right associativity, at level 60).

Definition empty_short : ty -> option ty -> option ty :=
  fun T f => match T with
  | <{{Bot}}> => Some <{{Bot}}>
  | _ => f
  end.
Definition isEmpty : ty -> option ty -> option ty :=
  fun T f => match T with
  | <{{Empty}}> | <{{Bot}}> => f
  | _ => None
  end.
Notation " 'emptyshort' T ;; e" := (empty_short T e) (right associativity, at level 60).
Notation " 'IsEmpty' T ;; e" := (isEmpty T e) (right associativity, at level 60).
Notation " x <- e1 ;; e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end)
         (right associativity, at level 60).

Fixpoint has_typec (t : tm) (Gamma : context) : option ty :=
  match t with
  | tm_var x => Gamma x
  | <{\x:T1, t1}> =>
    T2 <- has_typec t1 (x|->T1; Gamma);;
    Some <{{T1 -> T2}}>
  | <{t1 t2}> =>
    T1 <- has_typec t1 Gamma ;;
    T2 <- has_typec t2 Gamma ;;
    emptyshort T1 ;;
    T11 to T12 <<- T1 ;;
    T2 sub T11 ;;
    Some T12
  | <{t.elim T}> =>
    T1 <- has_typec t Gamma;;
    IsEmpty T1;;
    Some T
  | <{unit}> => Some <{{Unit}}>
  end
.

Ltac unwrap' T1 T2 E :=
  match goal with
  | H : Some _ = Some _ |- _ => inverts H
  | H : _ <- ?e ;; _ = Some _ |- _ =>
    destruct e as [T1|] eqn:E; simpl in H; try discriminate
  | H : (_ to _ <<- ?e ;; _) = Some _ |- _ =>
    destruct e; simpl in H; try discriminate
  | H : (?T1 == ?T2 ;; _) = Some _ |- _ => destruct (eqb_ty_reflect T1 T2); [subst | discriminate]
  | H : (emptyshort ?T ;; _) = _ |- _ => destruct T; simpl in H; try discriminate
  | H : (?T1 sub ?T2 ;; _) = Some _ |- _ => destruct (subtype_reflect T1 T2);
  [idtac | discriminate]
  | H : (IsEmpty ?T ;; _) = Some _ |- _ => destruct T; simpl in H; try discriminate
  end
.
Ltac unwrap := repeat
  let T1 := fresh "T" in
  let T2 := fresh "T" in
  let E1 := fresh "Heq" in
  unwrap' T1 T2 E1.

Theorem type_checking_sound (t : tm) : forall Gamma T,
  has_typec t Gamma = Some T ->
  has_type t T Gamma.
Proof.
  induction t; intros Gamma T Heq; simpl in Heq; unwrap; eauto.
Defined.

Theorem type_checking_complete (t : tm) : forall Gamma T,
  has_type t T Gamma ->
  exists T', has_typec t Gamma = Some T' /\ T' <: T.
Proof.
  intros Gamma T HT; induction HT; simpl; eauto.
  - (* abs *)
    destruct IHHT as (T' & IH & HSU). rewrite IH. eauto.
  - (* app *)
    destruct IHHT1 as (T1' & IH1 & HSU1). rewrite IH1.
    destruct IHHT2 as (T2' & IH2 & HSU2). rewrite IH2.
    sub_inverts HSU1; simpl; eauto.
    destruct (subtype_reflect T2' x); eauto; try solve [false; eauto].
  - (* empty *)
    destruct IHHT as (T' & IH & HSU). rewrite IH.
    sub_inverts HSU; simpl; eauto.
  - (* sub *) destruct IHHT as (T' & IH & HSU); eauto.
Defined.

(* Lemma has_type_abs_inversion Gamma x T1 t T :
  Gamma |-- \x:T1,t \in T -> (T = <{{Top}}>) +
  {U1 & {U2 & T = <{{U1 -> U2}}> *
  U1 <: T1 *
  (x|->T1; Gamma) |-- t \in U2}}. *)

Theorem progress (t : tm) (T : ty) :
  empty |-- t \in T ->
  value t \/ exists t', t ---> t'.
Proof.
  intros HT; remember empty as emp; gen Heqemp.
  induction HT; intros Heq; subst; auto.
  - (* var *) discriminate.
  - (* app *)
    right.
    destruct IHHT1 as [IH1|[t1' IH1]]; eauto.
    destruct IHHT2 as [IH2|[t2' IH2]]; eauto.
    lets (T1' & HSU & x & u & Heq & HT) : value_arrow HT1 IH1. subst t1. eauto.
  - (* elim *)
    destruct IHHT as [IH|[t' IH]]; eauto. false. eauto using value_empty.
Defined.

Theorem weakening (Gamma1 Gamma2 : context) : includedin Gamma1 Gamma2 ->
  forall t T, Gamma1 |-- t \in T -> Gamma2 |-- t \in T.
Proof.
  introv Hi HT; gen Gamma2; induction HT; eauto using includedin_update.
Defined.

Lemma weakening_empty : forall Gamma t T,
     empty |-- t \in T  ->
     Gamma |-- t \in T.
Proof. introv; eapply weakening; discriminate. Defined.

Lemma has_type_ext : forall Gamma1 Gamma2 t T, (forall x, Gamma1 x = Gamma2 x) -> Gamma1 |-- t \in T -> Gamma2 |-- t \in T.
Proof.
  introv Hext. apply weakening. congruence.
Defined.

Instance equiv_rel : @CRelationClasses.Equivalence context mapeq.
Proof. split; eauto using mapeq_trans. Defined.

Instance update_mor x v : CMorphisms.Proper ((@mapeq ty) ==> (@mapeq ty)) (update x v).
Proof.
  unfolds. intros m1 m2. apply mapeq_cong.
Defined.

Instance has_type_mor t T : CMorphisms.Proper ((@mapeq ty) ==> iffT) (has_type t T).
Proof.
  unfolds. intros m1 m2. split; eauto using has_type_ext; auto.
Defined.

Ltac eq_case_ty :=
  repeat match goal with
  | |- has_type (if ?x =? ?y then _ else _) ?T ?Gamma
  => destruct (eqb_spec x y); subst
  | H : (?x |-> _; _) ?x = _ |- _ => rewrite update_eq in H
  | H : (?x |-> _; _) ?y = _, Hneq : ?y <> ?x |- _ => rewrite update_neq in H; auto
  | H : Some _ = Some _ |- _ => injection H as H; subst
  | H : has_type _ _ (?x |-> _; ?x |-> _; _) |- _ => rewrite update_shadow in H
  | H : has_type _ _ (?x |-> _; ?y |-> _; _), Hneq : ?x <> ?y |- _ => rewrite update_permute in H; auto
  end;
  eauto.
   (* repeat rewrite ABA_eq_AB in *; eauto; try (solve_permute; fail). *)

Ltac remember_context Gamma :=
  match goal with
  | H : has_type ?t ?T Gamma |- ?g =>
    let H2 := fresh"H" in
    let p := fresh"p" in
      assert (H2 : forall p, p ~ Gamma -> has_type t T p -> g); [clear H; intros p Hequ H | eauto]
  end.

Ltac subst_context G :=
  match goal with
  | Hequ : G ~ _, Heq : G _ = _ |- _ => rewrite Hequ in Heq
  end.

Theorem substitution_preserves_typing (x : INDEX) (U : ty) (v : tm) : empty |-- v \in U -> forall t Gamma T,
  (x |-> U ; Gamma) |-- t \in T -> Gamma |-- [x:=v]t \in T.
Proof.
  intros HTv t Gamma T HT.
  remember_context (x |-> U ; Gamma). gen Gamma.
  induction HT;
  intros Gamma' Heq; try subst_context Gamma; subst; simpl; eauto.
  - (* var *) eq_case_ty. eauto using weakening_empty.
  - (* abs *) econstructor. eq_case_ty.
    + rewrite Heq in HT. rewrite update_shadow in HT. eauto.
    + specializes IHHT (x0 |-> T2; Gamma') ___.
      rewrite Heq. apply update_permute; auto.
Defined.

Theorem preservation (t t' : tm) (T : ty) : empty |-- t \in T -> t ---> t' -> empty |-- t' \in T.
Proof.
  intros HT HS. remember empty as emp. gen t'.
  induction HT; subst Gamma; try discriminate;
  introv HS; inverts HS; eauto.
  - (* app *)
    apply value_arrow in HT1; auto.
    destruct HT1 as (T1' & HSU & x0 & u & Heq & HT). injection Heq as ? ? ?; subst.
    eauto using substitution_preserves_typing.
Defined.

Inductive multi : tm -> tm -> Type :=
  | multi_refl x : multi x x
  | multi_step x y z : step x y -> multi y z -> multi x z
.
Hint Constructors multi : core.

Notation " t '-->*' t' " := (multi t t') (at level 40).
Theorem multi_R x y : x ---> y -> x -->* y.
Proof. eauto. Defined.
Theorem multi_trans x y z :
  x -->* y -> y -->* z -> x -->* z.
Proof.
  intros G H. induction G; eauto.
Defined.
Definition nf t := forall t', t ---> t' -> False.
Hint Unfold nf : core.

Ltac find_value_step :=
  match goal with
  Hv : value ?t,
  HS : ?t ---> ?t'
  |- _ => false; apply (value__nf _ Hv _ HS) end.

Ltac find_value_step_aggr :=
  match goal with
  HS : ?t ---> ?t'
  |- _ => exfalso; assert (Hv : value t); [eauto | apply (value__nf _ Hv _ HS)] end.

Theorem determinism t t1 t2 : t ---> t1 -> t ---> t2 -> t1 = t2.
Proof.
  intros HS1. gen t2.
  induction HS1; introv HS2; inverts HS2; eauto;
  f_equal; eauto; try find_value_step; find_value_step_aggr.
Defined.

Lemma nf_multi_refl (t1 t2 : tm) : nf t1 -> t1 -->* t2 -> t1 = t2.
Proof.
  intros Hnf HM. unfold nf in *; inverts HM; [eauto| exfalso; eauto].
Defined.

Theorem multi_preservation t1 t2 T :
  t1 -->* t2 ->
  empty |-- t1 \in T ->
  empty |-- t2 \in T.
Proof.
  intros HM; induction HM; eauto using preservation.
Defined.

Definition normalizing t := exists t', t -->* t' /\ nf t'.
Hint Unfold normalizing : core.

Fixpoint strong_norm t T : Type :=
  match T with
  | Ty_Bot | Ty_Empty => False
  | Ty_Top => normalizing t
  | Ty_Arrow T1 T2 =>
    normalizing t /\ forall t1,
    empty |-- t1 \in T1 -> strong_norm t1 T1 -> strong_norm <{t t1}> T2
  | Ty_Unit => t -->* <{unit}>
  end.

Theorem norm_back t t' : t ---> t' -> normalizing t' -> normalizing t.
Proof.
  intros HS (t'' & HM & Hnf); eauto.
Defined.
Hint Resolve norm_back : core.

Lemma step_multi_diamond t t1 t2 :
  t ---> t1 ->
  t -->* t2 ->
  nf t2 ->
  t1 -->* t2.
Proof.
  intros HS HM Hnf. inverts HM; try solve[false; eauto].
  rewrite (determinism _ _ _ HS H). auto.
Defined.

Theorem multi_determinism (t t1 t2 : tm) : t -->* t1 -> t -->* t2 -> nf t1 -> nf t2 -> t1 = t2.
Proof.
  intros HM1 HM2 Hnf1 Hnf2. generalize dependent t2.
  induction HM1.
  - intros. eauto using nf_multi_refl.
  - intros. eauto using step_multi_diamond.
Defined.

Theorem norm_forward t t' : t ---> t' -> normalizing t -> normalizing t'.
Proof.
  intros HS (t'' & HM & Hnf). eauto using step_multi_diamond.
Defined.
Hint Resolve norm_forward : core.

Theorem strong_norm_back T : forall t t',
  t ---> t' ->
  strong_norm t' T ->
  strong_norm t T.
Proof.
  induction T; simpl; eauto; intros t t' HS.
  - (* arr *)
    intros [Hn Hs]; split; eauto.
Defined.

Lemma nf_unit : nf <{unit}>.
Proof. intros t HS. inverts HS. Defined.
Hint Resolve nf_unit : core.

Theorem strong_norm_forward T : forall t t',
  t ---> t' ->
  strong_norm t T ->
  strong_norm t' T.
Proof.
  induction T; simpl; eauto; intros t t' HS.
  - (* arr *)
    intros [Hn Hs]; split; eauto.
  - (* unit *) intros HM. eapply step_multi_diamond; eauto.
Defined.

Theorem strong_norm_multi_back T : forall t t',
  t -->* t' ->
  strong_norm t' T ->
  strong_norm t T.
Proof.
  introv HM; induction HM; eauto using strong_norm_back.
Defined.

Theorem strong_norm_multi_forward T : forall t t',
  t -->* t' ->
  strong_norm t T ->
  strong_norm t' T.
Proof.
  introv HM; induction HM; eauto using strong_norm_forward.
Defined.

Definition contextv := list (INDEX * (tm * ty)).
Fixpoint addto_context (l : contextv) (G : context) : context :=
  match l with
  | nil => G
  | cons (x,t,T) l' => x|->T; addto_context l' G
  end
.
Notation "l ||-> G" := (addto_context l G) (at level 100).

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

Lemma wt_subst_eq t : forall Gamma T x t', Gamma |-- t \in T -> Gamma x = None -> <{[x:=t']t}> = t.
Proof.
  induction t; introv HT Heq; simpl; eauto.
   (* try solve[inverts HT; f_equal; eauto]. *)
  - (* var *)
    apply type_inversion_var in HT.
    destruct HT as (T' & Heqi & HSU).
    (*--------------------------------------------------*)
    destruct (eqb_spec i x); [congruence | reflexivity].
  - apply type_inversion_abs in HT.
  - admit.
  -
    destruct (eqb_spec x0 s); try(reflexivity).
    f_equal. iac H. eapply IHt.
    + eapply H6.
    + rewrite update_neq; eauto.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma wt_substi_eq : forall Gamma' t Gamma T, Gamma |-- t \in T -> (forall p q r, Lists.List.In (p,q,r) Gamma' -> Gamma p = None) -> substm Gamma' t = t.
Proof.
  induction Gamma'; intros.
  - reflexivity.
  - destruct a as [[p q] r]. simpl.
    erewrite wt_subst_eq.
    + eapply IHGamma'.
      * apply H.
      * intros. eapply H0. right. eapply H1.
    + eapply H.
    + eapply H0. left. reflexivity.
Qed.

Lemma var_case Gammav x T :
  (Gammav ||-> empty) x = Some T ->
  close Gammav ->
  strong_norm <{[/Gammav]x}> T.
Proof.
  induction Gammav; simpl; try discriminate.
  destruct a as (x1 & t & T1).
  intros Heq Hc. inverts Hc.
  destruct (eqb_spec x x1); subst; eq_case_ty.

  Check update_neq.
  2:{}

Theorem has_type__strong_norm t : forall Gamma T,
  (Gamma ||-> empty) |-- t \in T ->
  close Gamma ->
  strong_norm <{[/Gamma]t}> T.
Proof.
  introv HT. remember (Gamma ||-> empty) as G.
  gen Gamma. induction HT; intros Gammav Heq; subst.
  -
Admitted.


(* Computing *)
Definition pretty_print_progress t T (H : empty |-- t \in T) : option tm :=
  match progress _ _ H with
  | inl _ => None
  | inr (existT _ t' _) => Some t'
  end.
Import SigTNotations.
Fixpoint infinite_compute (n : nat) t T (HT : empty |-- t \in T) : option (sigT (fun t' => empty |-- t' \in T)) :=
  match n with
  | 0 => Some (t ; HT)
  | S n' =>
    match infinite_compute n' t T HT with
    | None => None
    | Some (t' ; HT') =>
      match (progress _ _ HT') with
      | inl _ => None
      | inr (t'' ; HS) => Some (t'' ; preservation _ _ _ HT' HS)
      end
    end
  end.

Print All Dependencies preservation.

Definition pretty_print_multiprogress n t T (H : empty |-- t \in T) : option tm :=
  match infinite_compute n _ _ H with
  | Some (t;_) => Some t
  | None => None
  end.

End STLC.

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
(* Arguments tm_app {INDEX}.
Arguments tm_app {INDEX}.
Arguments tm_app {INDEX}. *)
Definition eg : has_type nat eqb
  (tm_app
    (tm_app
      (tm_app (tm_abs 0 (Ty_Arrow Ty_Unit Ty_Unit) (tm_abs 1 (Ty_Arrow Ty_Unit Ty_Unit) (tm_abs 2 Ty_Unit (tm_app (tm_var 0) (tm_app (tm_var 1) (tm_var 2)))))) (tm_abs 3 Ty_Unit (tm_var 3)))
      (tm_abs 3 Ty_Unit tm_unit))
    tm_unit)
  Ty_Unit  (empty _).
  repeat (try reflexivity; econstructor).
Defined.

Compute (pretty_print_progress _ _ _ _ eg).
Locate eqb_spec.

Compute (pretty_print_multiprogress _ _ my_eqb_spec 3 _ _ eg).
Print Assumptions pretty_print_multiprogress.