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
  | ST_vhdVcons x y v1 v2 t1 T1 T2:
    tm_vhd (tm_vsing x v1 T1 T2) (tm_vcons x y t1 v2) --> <{[y:=v1]t1}>
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
where "t '-->' t'" := (step t t').
Local Hint Constructors step : core.
