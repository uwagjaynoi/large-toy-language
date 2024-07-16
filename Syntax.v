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
  | Ty_Bot   : ty
  | Ty_Top   : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Empty : ty
  | Ty_Unit  : ty
  | Ty_Bool  : ty
  | Ty_Nat   : ty
  | Ty_Sum   : ty -> ty -> ty
  | Ty_Prod  : ty -> ty -> ty
  | Ty_List  : ty -> ty
  | Ty_RNil  : ty
  | Ty_RCons : INDEX -> ty -> ty -> ty
  | Ty_VNil  : ty
  | Ty_VCons : INDEX -> ty -> ty -> ty
.

Inductive tm : Type :=
  | tm_var   : INDEX -> tm
  | tm_abs   : INDEX -> ty -> tm -> tm
  | tm_app   : tm -> tm -> tm
  | tm_elim  : tm -> ty -> tm
  | tm_unit  : tm
  | tm_true  : tm
  | tm_false : tm
  | tm_ite   : tm -> tm -> tm -> tm
  | tm_O     : tm
  | tm_S     : tm -> tm
  | tm_Ncase : tm -> tm -> INDEX -> tm -> tm
  | tm_Nfix  : tm -> tm -> tm -> tm
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
  | tm_rnil  : tm
  | tm_rcons : INDEX -> tm -> tm -> tm
  | tm_rproj : tm -> INDEX -> tm
  | tm_vsing : INDEX -> tm -> ty -> ty -> tm
  | tm_vhd   : tm -> tm -> tm
  | tm_vcons : INDEX -> INDEX -> tm -> tm -> tm
  | tm_vtl  : tm
  | tm_let   : INDEX -> tm -> tm -> tm
  | tm_fix   : tm -> tm
  | tm_error : tm
.

Declare Custom Entry stlc.
Declare Custom Entry stlc_ty.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "( x )" := x (in custom stlc_ty, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).

Notation "'Bot'"            := (Ty_Bot)
  (in custom stlc_ty at level 0).
Notation "'Top'"            := (Ty_Top)
  (in custom stlc_ty at level 0).
Notation "S -> T"           := (Ty_Arrow S T)
  (in custom stlc_ty at level 50, right associativity).
Notation "'Empty'"          := (Ty_Empty)
  (in custom stlc_ty at level 0).
Notation "'Unit'"           := (Ty_Unit)
  (in custom stlc_ty at level 0).
Notation "'Bool'"           := (Ty_Bool)
  (in custom stlc_ty at level 0).
Notation "'Nat'"            := (Ty_Nat)
  (in custom stlc_ty at level 0).
Notation "S + T"            := (Ty_Sum S T)
  (in custom stlc_ty at level 50, right associativity).
Notation "S * T"            := (Ty_Prod S T)
  (in custom stlc_ty at level 40, right associativity).
Notation "'List' T"         := (Ty_List T)
  (in custom stlc_ty at level 0).
Notation "'RNil'"           := (Ty_RNil)
  (in custom stlc_ty at level 0).
Notation "x ':' T1 '::' T2" := (Ty_RCons x T1 T2)
  (in custom stlc_ty at level 60, right associativity).
Notation "'VNil'"           := (Ty_VNil)
  (in custom stlc_ty at level 0).
Notation "x ':' T1 '||' T2" := (Ty_VCons x T1 T2)
  (in custom stlc_ty at level 60, right associativity).

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
Notation "'true'" := (tm_true)
  (in custom stlc at level 0).
Notation "'false'" := (tm_false)
  (in custom stlc at level 0).
Notation "'if' c 'then' t1 'else' t2" := (tm_ite c t1 t2)
  (in custom stlc at level 1, c at level 0, t1 at level 0, t2 at level 0).

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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_ite t1 t2 t3 => tm_ite <{[x:=e]t1}> <{[x:=e]t2}> <{[x:=e]t3}>
  | tm_O => tm_O
  | tm_S t1 => tm_S <{[x:=e]t1}>
  | tm_Ncase t1 t2 y t3 => tm_Ncase <{[x:=e]t1}> <{[x:=e]t2}> y (if y =? x then t3 else <{[x:=e]t3}>)
  | tm_Nfix t1 t2 t3 => tm_Nfix <{[x:=e]t1}> <{[x:=e]t2}> <{[x:=e]t3}>
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
    tm_Lcase <{[x:=e]t1}> <{[x:=e]t2}> y z (if orb (y =? x) (z =? x) then t3 else <{[x:=e]t3}>)
  | tm_Lfix t1 t2 t3 => tm_Lfix <{[x:=e]t1}> <{[x:=e]t2}> <{[x:=e]t3}>
  | tm_rnil => tm_rnil
  | tm_rcons y t1 t2 => tm_rcons y <{[x:=e]t1}> <{[x:=e]t2}>
  | tm_rproj t1 y => tm_rproj <{[x:=e]t1}> y
  | tm_vsing y t1 T1 T2 => tm_vsing y <{[x:=e]t1}> T1 T2
  | tm_vhd t1 t2 => tm_vhd <{[x:=e]t1}> <{[x:=e]t2}>
  | tm_vcons y z t1 t2 => tm_vcons y z (if z =? x then t1 else <{[x:=e]t1}>) <{[x:=e]t2}>
  | tm_vtl => tm_vtl
  | tm_let y t1 t2 => tm_let y <{[x:=e]t1}> (if y =? x then t2 else <{[x:=e]t2}>)
  | tm_fix t1 => tm_fix <{[x:=e]t1}>
  | tm_error => tm_error
  end
where "'[' x ':=' e ']' t" := (subst x e t) (in custom stlc).

Inductive value : tm -> Type :=
  | v_abs x T t     : value (tm_abs x T t)
  | v_unit          : value tm_unit
  | v_true          : value tm_true
  | v_false         : value tm_false
  | v_O             : value tm_O
  | v_S t           : value t -> value (tm_S t)
  | v_inl T t       : value t -> value (tm_inl T t)
  | v_inr T t       : value t -> value (tm_inr T t)
  | v_pair t1 t2    : value t1 -> value t2 -> value (tm_pair t1 t2)
  | v_nil T         : value (tm_nil T)
  | v_cons t1 t2    : value t1 -> value t2 -> value (tm_cons t1 t2)
  | v_rnil          : value tm_rnil
  | v_rcons x t1 t2 : value t1 -> value t2 -> value (tm_rcons x t1 t2)
  | v_vsing x t1 T1 T2 : value t1 -> value (tm_vsing x t1 T1 T2)
.
Local Hint Constructors value : core.

Notation "'error'" := tm_error.

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
  | ST_ite1 t1 t1' t2 t3 :
    t1 --> t1' ->
    tm_ite t1 t2 t3 --> tm_ite t1' t2 t3
  | ST_iteTrue t2 t3 :
    tm_ite tm_true t2 t3 --> t2
  | ST_iteFalse t2 t3 :
    tm_ite tm_false t2 t3 --> t3
  | ST_succ1 t1 t1' :
    t1 --> t1' ->
    tm_S t1 --> tm_S t1'
  | ST_Ncase1 t1 t1' t2 x t3 :
    t1 --> t1' ->
    tm_Ncase t1 t2 x t3 --> tm_Ncase t1' t2 x t3
  | ST_NcaseO t2 x t3 :
    tm_Ncase tm_O t2 x t3 --> t2
  | ST_NcaseS t1 t2 x t3 :
    value t1 ->
    tm_Ncase (tm_S t1) t2 x t3 --> <{[x:=t1]t3}>
  | ST_Nfix1 t1 t1' t2 t3 :
    t1 --> t1' ->
    tm_Nfix t1 t2 t3 --> tm_Nfix t1' t2 t3
  | ST_NfixO t2 t3 :
    tm_Nfix tm_O t2 t3 --> t2
  | ST_NfixS v1 t2 t3 :
    value v1 ->
    tm_Nfix (tm_S v1) t2 t3 --> tm_app (tm_app t3 v1) (tm_Nfix v1 t2 t3)
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
  | ST_rcons1 x t1 t1' t2 :
    t1 --> t1' ->
    tm_rcons x t1 t2 --> tm_rcons x t1' t2
  | ST_rcons2 x v1 t2 t2' :
    value v1 ->
    t2 --> t2' ->
    tm_rcons x v1 t2 --> tm_rcons x v1 t2'
  | ST_rproj1 t1 t1' x :
    t1 --> t1' ->
    tm_rproj t1 x --> tm_rproj t1' x
  | ST_rprojO x v1 v2 :
    value v1 ->
    value v2 ->
    tm_rproj (tm_rcons x v1 v2) x --> v1
  | ST_rprojS x y v1 v2 :
    value v1 ->
    value v2 ->
    y <> x ->
    tm_rproj (tm_rcons y v1 v2) x --> tm_rproj v2 x
  | ST_vsing1 x t1 t1' T1 T2 :
    t1 --> t1' ->
    tm_vsing x t1 T1 T2 --> tm_vsing x t1' T1 T2
  | ST_vhd1 t1 t1' t2 :
    t1 --> t1' ->
    tm_vhd t1 t2 --> tm_vhd t1' t2
  | ST_vhd2 v1 t2 t2' :
    value v1 ->
    t2 --> t2' ->
    tm_vhd v1 t2 --> tm_vhd v1 t2'
  | ST_vO x y v1 v2 t1 T1 T2:
    value v1 ->
    value v2 ->
    tm_vhd (tm_vsing x v1 T1 T2) (tm_vcons x y t1 v2) --> <{[y:=v1]t1}>
  | ST_vS x y z v1 v2 t1 T1 T2:
    value v1 ->
    value v2 ->
    x <> y ->
    tm_vhd (tm_vsing x v1 T1 T2) (tm_vcons y z t1 v2) --> tm_vhd (tm_vsing x v1 T1 T2) v2
  | ST_vcons1 x y t1 t2 t2' :
    t2 --> t2' ->
    tm_vcons x y t1 t2 --> tm_vcons x y t1 t2'
  | ST_let1 x t1 t1' t2 :
    t1 --> t1' ->
    tm_let x t1 t2 --> tm_let x t1' t2
  | ST_letValue x v1 t2 :
    value v1 ->
    tm_let x v1 t2 --> <{[x:=v1]t2}>
  | ST_fix1 t1 t1' :
    t1 --> t1' ->
    tm_fix t1 --> tm_fix t1'
  | ST_fixAbs x T t :
    tm_fix (tm_abs x T t) --> <{[x:={tm_fix (tm_abs x T t)}]t}>
  | STE_app1 t2 :
    tm_app error t2 --> error
  | STE_app2 v1 :
    value v1 ->
    tm_app v1 error --> error
  | STE_elim1 T :
    tm_elim error T --> error
  | STE_ite t2 t3 :
    tm_ite error t2 t3 --> error
  | STE_succ :
    tm_S error --> tm_S error
  | STE_Ncase t2 x t3 :
    tm_Ncase error t2 x t3 --> error
  | STE_Nfix t2 t3 :
    tm_Nfix error t2 t3 --> error
  | STE_inl T :
    tm_inl T error --> error
  | STE_inr T :
    tm_inr T error --> error
  | ST_EScase x t2 y t3 :
    tm_Scase error x t2 y t3 --> error
  | ST_Epair1 t2 :
    tm_pair error t2 --> error
  | ST_Epair2 v1 :
    value v1 ->
    tm_pair v1 error --> error
  | STE_fst :
    tm_fst error --> error
  | STE_snd :
    tm_snd error --> error
  | STE_cons1 t2 :
    tm_cons error t2 --> error
  | STE_cons2 v1 :
    tm_cons v1 error --> error
  | STE_Lcase1 t2 x y t3 :
    tm_Lcase error t2 x y t3 --> error
  | STE_Lfix1 t2 t3 :
    tm_Lfix error t2 t3 --> error
  | STE_rcons1 x t2 :
    tm_rcons x error t2 --> error
  | STE_rcons2 x v1 :
    value v1 ->
    tm_rcons x v1 error --> error
  | STE_rproj x :
    tm_rproj error x --> error
  | STE_vsing x T1 T2 :
    tm_vsing x error T1 T2 --> error
  | STE_vhd1 t2 :
    tm_vhd error t2 --> error
  | STE_vhd2 v1 :
    value v1 ->
    tm_vhd v1 error --> error
  | STE_vcons1 x y t1 :
    tm_vcons x y t1 error --> error
  | STE_let1 x t2 :
    tm_let x error t2 --> error
  | STE_fix1 :
    tm_fix error --> error
where "t '-->' t'" := (step t t').
Local Hint Constructors step : core.

Inductive IsRecord : ty -> Type :=
  | IsR_Nil : IsRecord <{{RNil}}>
  | IsR_Cons x T1 T2 : IsRecord T2 -> IsRecord <{{x:T1::T2}}>
.

Inductive IsVariant : ty -> Type :=
  | IsV_Nil : IsVariant <{{VNil}}>
  | IsV_Cons x T1 T2 : IsVariant T2 -> IsVariant <{{x:T1||T2}}>
.

Inductive WellFormed : ty -> Type :=
  | WF_Bot : WellFormed <{{Bot}}>
  | WF_Top : WellFormed <{{Top}}>
  | WF_Arrow T1 T2 : WellFormed T1 -> WellFormed T2 -> WellFormed <{{T1 -> T2}}>
  | WF_Empty : WellFormed <{{Empty}}>
  | WF_Unit : WellFormed <{{Unit}}>
  | WF_Bool : WellFormed <{{Bool}}>
  | WF_Nat : WellFormed <{{Nat}}>
  | WF_Sum T1 T2 : WellFormed T1 -> WellFormed T2 -> WellFormed <{{T1 + T2}}>
  | WF_Prod T1 T2 : WellFormed T1 -> WellFormed T2 -> WellFormed <{{T1 * T2}}>
  | WF_List T : WellFormed T -> WellFormed <{{List T}}>
  | WF_RNil : WellFormed <{{RNil}}>
  | WF_RCons x T1 T2 : WellFormed T1 -> WellFormed T2 -> IsRecord T2 -> WellFormed <{{x:T1::T2}}>
  | WF_VNil : WellFormed <{{VNil}}>
  | WF_VCons x T1 T2 : WellFormed T1 -> WellFormed T2 -> IsVariant T2 -> WellFormed <{{x:T1||T2}}>
.

Fixpoint lookup (T : ty) (x : INDEX) : option ty :=
  match T with
  | Ty_RCons y T1 T2 =>
    if x =? y then Some T1 else lookup T2 x
  | Ty_VCons y T1 T2 =>
    if x =? y then Some T1 else lookup T2 x
  | _ => None
  end.

Reserved Notation "T '<:' U" (at level 40).
Inductive subtype : ty -> ty -> Type :=
  | S_Refl            T : WellFormed T -> T <: T
  | S_Bot             T : WellFormed T -> <{{Bot}}> <: T
  | S_Top             T : WellFormed T -> T <: <{{Top}}>
  | S_Arrow T1 T2 U1 U2 : T2 <: T1 -> U1 <: U2 -> <{{T1 -> U1}}> <: <{{T2 -> U2}}>
  | S_Sum   T1 T2 U1 U2 : T1 <: T2 -> U1 <: U2 -> <{{T1 + U1}}> <: <{{T2 + U2}}>
  | S_Prod  T1 T2 U1 U2 : T1 <: T2 -> U1 <: U2 -> <{{T1 * U1}}> <: <{{T2 * U2}}>
  | S_List        T1 T2 : T1 <: T2 -> <{{List T1}}> <: <{{List T2}}>
  | S_Rnil            T :
    IsRecord T ->
    WellFormed T ->
    T <: <{{RNil}}>
  | S_Rcons x T T' T1 T2 :
    IsRecord T1 -> WellFormed T1 ->
    IsRecord T2 -> WellFormed T2 ->
    lookup T1 x = Some T' ->
    T' <: T ->
    T1 <: <{{x:T::T2}}>
  | S_Vnil            T :
    IsVariant T ->
    WellFormed T ->
    <{{VNil}}> <: T
  | S_Vcons x T T' T1 T2 :
    IsVariant T1 -> WellFormed T1 ->
    IsVariant T2 -> WellFormed T2 ->
    lookup T2 x = Some T' ->
    T <: T' ->
    <{{x:T||T1}}> <: T2
where "T '<:' U" := (subtype T U).
Local Hint Constructors subtype : core.

Definition context : Type := map ty.
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
  (* write type deduction for every term *)
  | T_True Gamma :
    Gamma |-- tm_true \in Bool
  | T_False Gamma :
    Gamma |-- tm_false \in Bool
  | T_Ite Gamma t1 t2 t3 T :
    Gamma |-- t1 \in Bool ->
    Gamma |-- t2 \in T ->
    Gamma |-- t3 \in T ->
    Gamma |-- tm_ite t1 t2 t3 \in T
  | T_O Gamma :
    Gamma |-- tm_O \in Nat
  | T_S Gamma t :
    Gamma |-- t \in Nat ->
    Gamma |-- tm_S t \in Nat
  | T_Ncase Gamma t1 t2 x t3 T :
    Gamma |-- t1 \in Nat ->
    Gamma |-- t2 \in T ->
    (x |-> <{{Nat}}>; Gamma) |-- t3 \in T ->
    Gamma |-- tm_Ncase t1 t2 x t3 \in T
  | T_Nfix Gamma t1 t2 t3 T :
    Gamma |-- t1 \in Nat ->
    Gamma |-- t2 \in T ->
    Gamma |-- t3 \in (Nat -> T -> T) ->
    Gamma |-- tm_Nfix t1 t2 t3 \in T
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
  | T_Lcase Gamma t1 t2 x y t3 T :
    Gamma |-- t1 \in List T ->
    Gamma |-- t2 \in T ->
    (x |-> T; y |-> <{{List T}}>; Gamma) |-- t3 \in T ->
    Gamma |-- tm_Lcase t1 t2 x y t3 \in T
  | T_Lfix Gamma t1 t2 t3 T U :
    Gamma |-- t1 \in List T ->
    Gamma |-- t2 \in U ->
    Gamma |-- t3 \in (T -> List T -> U -> U) ->
    Gamma |-- tm_Lfix t1 t2 t3 \in U
  | T_Rnil Gamma :
    Gamma |-- tm_rnil \in RNil
  | T_Rcons Gamma x t1 t2 T1 T2 :
    IsRecord T2 ->
    Gamma |-- t1 \in T1 ->
    Gamma |-- t2 \in T2 ->
    Gamma |-- tm_rcons x t1 t2 \in (x:T1::T2)
  | T_Rproj Gamma t x T T1 :
    IsRecord T ->
    Gamma |-- t \in T ->
    lookup T x = Some T1 ->
    Gamma |-- tm_rproj t x \in T1
  | T_Vsing Gamma x t T1 T :
    IsVariant T ->
    Gamma |-- t \in T1 ->
    lookup T x = Some T1 ->
    Gamma |-- tm_vsing x t T1 T \in T
  (* vhd vcons vtl ??? *)
  | T_Let Gamma x t1 t2 T1 T2 :
    Gamma |-- t1 \in T1 ->
    (x |-> T1; Gamma) |-- t2 \in T2 ->
    Gamma |-- tm_let x t1 t2 \in T2
  | T_Fix Gamma t T :
    Gamma |-- t \in (T -> T) ->
    Gamma |-- tm_fix t \in T
  | T_Error Gamma :
    Gamma |-- tm_error \in Bot
  | T_Sub Gamma T1 T2 t : T1 <: T2 ->
    Gamma |-- t \in T1 ->
    Gamma |-- t \in T2
where "Gamma '|--' t '\in' T" := (has_type t T Gamma).
Local Hint Constructors has_type : core.