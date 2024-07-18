From Lambda Require Import Map.
Set Default Goal Selector "!".

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

Coercion tm_var : INDEX >-> tm.
Notation "\ x : T , t" := (tm_abs x T t)
  (in custom stlc at level 90,
  x at level 99,
  T custom stlc_ty at level 99,
  t custom stlc at level 99,
  left associativity).
Notation "x y" := (tm_app x y)
  (in custom stlc at level 1, left associativity).
Notation "t '.elim' T" := (tm_elim t T)
  (in custom stlc at level 1).
Notation "'unit'" := (tm_unit)
  (in custom stlc at level 0).
(* omitted *)

Notation "{ x }" := x (in custom stlc at level 1, x constr).

(* Operations *)
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
Global Hint Constructors value : core.

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
Global Hint Constructors step : core.

Definition context : Type := map ty.
Definition empty : context := empty.
Reserved Notation "Gamma '|--' t '\in' T" (at level 40, T custom stlc_ty at level 0).
Inductive has_type : tm -> ty -> context -> Type :=
  | T_Var (Gamma : context) (x : INDEX) T : Gamma x = Some T ->
    Gamma |-- x \in T
  | T_Abs (Gamma : context) (x : INDEX) T1 T2 t :
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
Global Hint Constructors has_type : core.