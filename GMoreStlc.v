(** * MoreStlc: More on the Simply Typed Lambda-Calculus *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import AMaps.
From PLF Require Import DTypes.
From PLF Require Import CSmallstep.
From PLF Require Import EStlc.
Set Default Goal Selector "!".


(* ################################################################# *)
(** * Exercise: Formalizing the Extensions *)

Module STLCExtended.

(** In this series of exercises, you will formalize some of the
    extensions described in this chapter.  We've provided the
    necessary additions to the syntax of terms and types, and we've
    included a few examples that you can test your definitions with to
    make sure they are working as expected.  You'll fill in the rest
    of the definitions and extend all the proofs accordingly.

    To get you started, we've provided implementations for:
     - numbers
     - sums
     - lists
     - unit

    You need to complete the implementations for:
     - pairs
     - let (which involves binding)
     - [fix]

    A good strategy is to work on the extensions one at a time, in
    separate passes, rather than trying to work through the file from
    start to finish in a single pass.  For each definition or proof,
    begin by reading carefully through the parts that are provided for
    you, referring to the text in the [Stlc] chapter for
    high-level intuitions and the embedded comments for detailed
    mechanics. *)

(* ----------------------------------------------------------------- *)
(** *** Syntax *)

Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat  : ty
  | Ty_Sum  : ty -> ty -> ty
  | Ty_List : ty -> ty
  | Ty_Unit : ty
  | Ty_Prod : ty -> ty -> ty.

Inductive tm : Type :=
  (* pure STLC *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* numbers *)
  | tm_const: nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0  : tm -> tm -> tm -> tm
  (* sums *)
  | tm_inl : ty -> tm -> tm
  | tm_inr : ty -> tm -> tm
  | tm_case : tm -> string -> tm -> string -> tm -> tm
          (* i.e., [case t0 of inl x1 => t1 | inr x2 => t2] *)
  (* lists *)
  | tm_nil : ty -> tm
  | tm_cons : tm -> tm -> tm
  | tm_lcase : tm -> tm -> string -> string -> tm -> tm
           (* i.e., [case t1 of | nil => t2 | x::y => t3] *)
  (* unit *)
  | tm_unit : tm

  (* You are going to be working on the following extensions: *)

  (* pairs *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
  (* let *)
  | tm_let : string -> tm -> tm -> tm
         (* i.e., [let x = t1 in t2] *)
  (* fix *)
  | tm_fix  : tm -> tm.

(** Note that, for brevity, we've omitted booleans and instead
    provided a single [if0] form combining a zero test and a
    conditional.  That is, instead of writing

       if x = 0 then ... else ...

    we'll write this:

       if0 x then ... else ...
*)

Definition w : string := "w".
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Declare Custom Entry stlc_ty.

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "<{{ e }}>" := e (e custom stlc_ty at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "( x )" := x (in custom stlc_ty, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc_ty at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "{ x }" := x (in custom stlc at level 1, x constr).

Notation "'Nat'" := Ty_Nat (in custom stlc_ty at level 0).
Notation "'succ' x" := (tm_succ x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "'pred' x" := (tm_pred x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "x * y" := (tm_mult x y) (in custom stlc at level 1,
                                      left associativity).
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Coercion tm_const : nat >-> tm.

Notation "S + T" :=
  (Ty_Sum S T) (in custom stlc_ty at level 3, left associativity).
Notation "'inl' T t" := (tm_inl T t) (in custom stlc at level 0,
                                         T custom stlc_ty at level 0,
                                         t custom stlc at level 0).
Notation "'inr' T t" := (tm_inr T t) (in custom stlc at level 0,
                                         T custom stlc_ty at level 0,
                                         t custom stlc at level 0).
Notation "'case' t0 'of' '|' 'inl' x1 '=>' t1 '|' 'inr' x2 '=>' t2" :=
  (tm_case t0 x1 t1 x2 t2) (in custom stlc at level 89,
                               t0 custom stlc at level 99,
                               x1 custom stlc at level 99,
                               t1 custom stlc at level 99,
                               x2 custom stlc at level 99,
                               t2 custom stlc at level 99,
                               left associativity).

Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc_ty at level 2, X custom stlc_ty, Y custom stlc_ty at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 1).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 1).

Notation "'List' T" :=
  (Ty_List T) (in custom stlc_ty at level 4).
Notation "'nil' T" := (tm_nil T) (in custom stlc at level 0, T custom stlc_ty at level 0).
Notation "h '::' t" := (tm_cons h t) (in custom stlc at level 2, right associativity).
Notation "'case' t1 'of' '|' 'nil' '=>' t2 '|' x '::' y '=>' t3" :=
  (tm_lcase t1 t2 x y t3) (in custom stlc at level 89,
                              t1 custom stlc at level 99,
                              t2 custom stlc at level 99,
                              x constr at level 1,
                              y constr at level 1,
                              t3 custom stlc at level 99,
                              left associativity).

Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc_ty at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).

Notation "'let' x '=' t1 'in' t2" :=
  (tm_let x t1 t2) (in custom stlc at level 0).

Notation "'fix' t" := (tm_fix t) (in custom stlc at level 0).

(* ----------------------------------------------------------------- *)
(** *** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

(** **** Exercise: 3 stars, standard (STLCExtended.subst) *)
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  (* numbers *)
  | tm_const _ =>
      t
  | <{succ t1}> =>
      <{succ [x := s] t1}>
  | <{pred t1}> =>
      <{pred [x := s] t1}>
  | <{t1 * t2}> =>
      <{ ([x := s] t1) * ([x := s] t2)}>
  | <{if0 t1 then t2 else t3}> =>
      <{if0 [x := s] t1 then [x := s] t2 else [x := s] t3}>
  (* sums *)
  | <{inl T2 t1}> =>
      <{inl T2 ( [x:=s] t1) }>
  | <{inr T1 t2}> =>
      <{inr T1 ( [x:=s] t2) }>
  | <{case t0 of | inl y1 => t1 | inr y2 => t2}> =>
      <{case ([x:=s] t0) of
         | inl y1 => { if String.eqb x y1 then t1 else <{ [x:=s] t1 }> }
         | inr y2 => {if String.eqb x y2 then t2 else <{ [x:=s] t2 }> } }>
  (* lists *)
  | <{nil _}> =>
      t
  | <{t1 :: t2}> =>
      <{ ([x:=s] t1) :: [x:=s] t2 }>
  | <{case t1 of | nil => t2 | y1 :: y2 => t3}> =>
      <{case ( [x:=s] t1 ) of
        | nil => [x:=s] t2
        | y1 :: y2 =>
        {if String.eqb x y1 then
           t3
         else if String.eqb x y2 then t3
              else <{ [x:=s] t3 }> } }>
  (* unit *)
  | <{unit}> => <{unit}>
  (* pairs *)
  | <{(t1,t2)}> => <{([x:=s]t1,[x:=s]t2)}>
  | <{t.fst}> => <{([x:=s]t).fst}>
  | <{t.snd}> => <{([x:=s]t).snd}>
  (* let *)
  | <{let y=t1 in t2}> => tm_let y <{[x:=s]t1}> (if String.eqb x y then t2 else <{[x:=s]t2}>)
  (* fix *)
  | <{fix t}> => <{fix ([x:=s]t)}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).


Reserved Notation "'[' x '::=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst' (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      tm_abs y T (if String.eqb x y then t1 else <{[x::=s] t1}>)
  | <{t1 t2}> =>
      <{([x::=s] t1) ([x::=s] t2)}>
  (* numbers *)
  | tm_const _ =>
      t
  | <{succ t1}> =>
      <{succ [x::=s] t1}>
  | <{pred t1}> =>
      <{pred [x::=s] t1}>
  | <{t1 * t2}> =>
      <{ ([x::=s] t1) * ([x::=s] t2)}>
  | <{if0 t1 then t2 else t3}> =>
      <{if0 [x::=s] t1 then [x::=s] t2 else [x::=s] t3}>
  (* sums *)
  | <{inl T2 t1}> =>
      <{inl T2 ( [x::=s] t1) }>
  | <{inr T1 t2}> =>
      <{inr T1 ( [x::=s] t2) }>
  | <{case t0 of | inl y1 => t1 | inr y2 => t2}> =>
      <{case ([x::=s] t0) of
         | inl y1 => { if String.eqb x y1 then t1 else <{ [x::=s] t1 }> }
         | inr y2 => {if String.eqb x y2 then t2 else <{ [x::=s] t2 }> } }>
  (* lists *)
  | <{nil _}> =>
      t
  | <{t1 :: t2}> =>
      <{ ([x::=s] t1) :: [x::=s] t2 }>
  | <{case t1 of | nil => t2 | y1 :: y2 => t3}> =>
      <{case ( [x::=s] t1 ) of
        | nil => [x::=s] t2
        | y1 :: y2 =>
        {if String.eqb x y1 then
           t3
         else if String.eqb x y2 then t3
              else <{ [x::=s] t3 }> } }>
  (* unit *)
  | <{unit}> => <{unit}>
  (* pairs *)
  | <{(t1,t2)}> => <{([x::=s]t1,[x::=s]t2)}>
  | <{t.fst}> => <{([x::=s]t).fst}>
  | <{t.snd}> => <{([x::=s]t).snd}>
  (* let *)
  | <{let y=t1 in t2}> => tm_let y <{[x::=s]t1}> (if String.eqb x y then t2 else <{[x::=s]t2}>)
  (* fix *)
  | <{fix t}> => <{fix ([x::=s]t)}>
  end
where "'[' x '::=' s ']' t" := (subst' x s t) (in custom stlc).

Ltac eq_case_eq :=
  repeat match goal with
  |- (if (?x =? ?y)%string then _ else _) = (if (?x =? ?y)%string then _ else _)
  => destruct (x =? y)%string; eauto end.
Theorem subst_eq : forall t x s, <{[x:=s]t}> = <{[x::=s]t}>.
Proof with eauto.
  induction t; simpl; intros; f_equal; eauto; eq_case_eq.
  destruct (x0 =? s)%string; f_equal...
Qed.

(* Make sure the following tests are valid by reflexzivity: *)
Example substeg1 :
  <{ [z:=0] (let w = z in z) }> = <{ let w = 0 in 0 }>.
Proof. reflexivity. Qed.

Example substeg2 :
  <{ [z:=0] (let w = z in w) }> = <{ let w = 0 in w }>.
Proof. reflexivity. Qed.

Example substeg3 :
  <{ [z:=0] (let y = succ 0 in z) }> = <{ let y = succ 0 in 0 }>.
Proof. reflexivity. Qed.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Reduction *)

(** Next we define the values of our language. *)

Inductive value : tm -> Prop :=
  (* In pure STLC, function abstractions are values: *)
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  (* Numbers are values: *)
  | v_nat : forall n : nat,
      value <{n}>
  (* A tagged value is a value:  *)
  | v_inl : forall v T1,
      value v ->
      value <{inl T1 v}>
  | v_inr : forall v T1,
      value v ->
      value <{inr T1 v}>
  (* A list is a value iff its head and tail are values: *)
  | v_lnil : forall T1, value <{nil T1}>
  | v_lcons : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{v1 :: v2}>
  (* A unit is always a value *)
  | v_unit : value <{unit}>
  (* A pair is a value if both components are: *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{(v1, v2)}>.

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

(** **** Exercise: 3 stars, standard (STLCExtended.step) *)
Inductive step : tm -> tm -> Prop :=
  (* pure STLC *)
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  (* numbers *)
  | ST_Succ : forall t1 t1',
         t1 --> t1' ->
         <{succ t1}> --> <{succ t1'}>
  | ST_SuccNat : forall n : nat,
         <{succ n}> --> <{ {S n} }>
  | ST_Pred : forall t1 t1',
         t1 --> t1' ->
         <{pred t1}> --> <{pred t1'}>
  | ST_PredNat : forall n:nat,
         <{pred n}> --> <{ {n - 1} }>
  | ST_Mulconsts : forall n1 n2 : nat,
         <{n1 * n2}> --> <{ {n1 * n2} }>
  | ST_Mult1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 * t2}> --> <{t1' * t2}>
  | ST_Mult2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 * t2}> --> <{v1 * t2'}>
  | ST_If0 : forall t1 t1' t2 t3,
         t1 --> t1' ->
         <{if0 t1 then t2 else t3}> --> <{if0 t1' then t2 else t3}>
  | ST_If0_Zero : forall t2 t3,
         <{if0 0 then t2 else t3}> --> t2
  | ST_If0_Nonzero : forall n t2 t3,
         <{if0 {S n} then t2 else t3}> --> t3
  (* sums *)
  | ST_Inl : forall t1 t1' T2,
        t1 --> t1' ->
        <{inl T2 t1}> --> <{inl T2 t1'}>
  | ST_Inr : forall t2 t2' T1,
        t2 --> t2' ->
        <{inr T1 t2}> --> <{inr T1 t2'}>
  | ST_Case : forall t0 t0' x1 t1 x2 t2,
        t0 --> t0' ->
        <{case t0 of | inl x1 => t1 | inr x2 => t2}> -->
        <{case t0' of | inl x1 => t1 | inr x2 => t2}>
  | ST_CaseInl : forall v0 x1 t1 x2 t2 T2,
        value v0 ->
        <{case inl T2 v0 of | inl x1 => t1 | inr x2 => t2}> --> <{ [x1:=v0]t1 }>
  | ST_CaseInr : forall v0 x1 t1 x2 t2 T1,
        value v0 ->
        <{case inr T1 v0 of | inl x1 => t1 | inr x2 => t2}> --> <{ [x2:=v0]t2 }>
  (* lists *)
  | ST_Cons1 : forall t1 t1' t2,
       t1 --> t1' ->
       <{t1 :: t2}> --> <{t1' :: t2}>
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       <{v1 :: t2}> --> <{v1 :: t2'}>
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
       t1 --> t1' ->
       <{case t1 of | nil => t2 | x1 :: x2 => t3}> -->
       <{case t1' of | nil => t2 | x1 :: x2 => t3}>
  | ST_LcaseNil : forall T1 t2 x1 x2 t3,
       <{case nil T1 of | nil => t2 | x1 :: x2 => t3}> --> t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
       value v1 ->
       value vl ->
       <{case v1 :: vl of | nil => t2 | x1 :: x2 => t3}>
         -->  <{ [x2 := vl] ([x1 := v1] t3) }>

  (* Add rules for the following extensions. *)

  (* pairs *)
  | ST_Pair1 : forall t1 t2 t1',
       t1 --> t1' ->
       <{(t1,t2)}> --> <{(t1',t2)}>
  | ST_Pair2 : forall t1 t2 t2',
       value t1 ->
       t2 --> t2' ->
       <{(t1,t2)}> --> <{(t1,t2')}>
  | ST_Fst1 : forall t1 t1',
       t1 --> t1' ->
       <{t1.fst}> --> <{t1'.fst}>
  | ST_FstPair : forall t1 t2,
       value t1 ->
       value t2 ->
       <{(t1,t2).fst}> --> t1
  | ST_Snd1 : forall t1 t1',
       t1 --> t1' ->
       <{t1.snd}> --> <{t1'.snd}>
  | ST_SndPair : forall t1 t2,
       value t1 ->
       value t2 ->
       <{(t1,t2).snd}> --> t2
  (* FILL IN HERE *)
  (* let *)
  | ST_Let1 : forall x t1 t1' t2,
       t1 --> t1' ->
       <{let x=t1 in t2}> --> <{let x=t1' in t2}>
  | ST_LetSubst : forall x t1 t2,
       value t1 ->
       <{let x=t1 in t2}> --> <{[x:=t1]t2}>
  (* fix *)
  | ST_Fix1 : forall t1 t1',
       t1 --> t1' ->
       <{fix t1}> --> <{fix t1'}>
  | ST_FixRec : forall x T t,
       <{fix (\x:T,t)}> --> <{[x:=fix (\x:T,t)]t}>
  where "t '-->' t'" := (step t t').

(** [] *)

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

(* ----------------------------------------------------------------- *)
(** *** Typing *)

Definition context := partial_map ty.

(** Next we define the typing rules.  These are nearly direct
    transcriptions of the inference rules shown above. *)

Reserved Notation "Gamma '|--' t '\in' T" (at level 40, t custom stlc, T custom stlc_ty at level 0).

(** **** Exercise: 3 stars, standard (STLCExtended.has_type) *)
Inductive has_type : context -> tm -> ty -> Prop :=
  (* pure STLC *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
    (x |-> T2 ; Gamma) |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  (* numbers *)
  | T_Nat : forall Gamma (n : nat),
      Gamma |-- n \in Nat
  | T_Succ : forall Gamma t,
      Gamma |-- t \in Nat ->
      Gamma |-- succ t \in Nat
  | T_Pred : forall Gamma t,
      Gamma |-- t \in Nat ->
      Gamma |-- pred t \in Nat
  | T_Mult : forall Gamma t1 t2,
      Gamma |-- t1 \in Nat ->
      Gamma |-- t2 \in Nat ->
      Gamma |-- t1 * t2 \in Nat
  | T_If0 : forall Gamma t1 t2 t3 T0,
      Gamma |-- t1 \in Nat ->
      Gamma |-- t2 \in T0 ->
      Gamma |-- t3 \in T0 ->
      Gamma |-- if0 t1 then t2 else t3 \in T0
  (* sums *)
  | T_Inl : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- (inl T2 t1) \in (T1 + T2)
  | T_Inr : forall Gamma t2 T1 T2,
      Gamma |-- t2 \in T2 ->
      Gamma |-- (inr T1 t2) \in (T1 + T2)
  | T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T3,
      Gamma |-- t0 \in (T1 + T2) ->
      (x1 |-> T1 ; Gamma) |-- t1 \in T3 ->
      (x2 |-> T2 ; Gamma) |-- t2 \in T3 ->
      Gamma |-- (case t0 of | inl x1 => t1 | inr x2 => t2) \in T3
  (* lists *)
  | T_Nil : forall Gamma T1,
      Gamma |-- (nil T1) \in (List T1)
  | T_Cons : forall Gamma t1 t2 T1,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in (List T1) ->
      Gamma |-- (t1 :: t2) \in (List T1)
  | T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
      Gamma |-- t1 \in (List T1) ->
      Gamma |-- t2 \in T2 ->
      (x1 |-> T1 ; x2 |-> <{{List T1}}> ; Gamma) |-- t3 \in T2 ->
      Gamma |-- (case t1 of | nil => t2 | x1 :: x2 => t3) \in T2
  (* unit *)
  | T_Unit : forall Gamma,
      Gamma |-- unit \in Unit

  (* Add rules for the following extensions. *)

  (* pairs *)
  | T_Pair : forall Gamma t1 T1 t2 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1,t2) \in (T1 * T2)
  | T_Fst : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- <{t.fst}> \in T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- <{t.snd}> \in T2
  (* let *)
  | T_Let : forall Gamma x t1 T1 t2 T2,
      Gamma |-- t1 \in T1 ->
      (x |-> T1; Gamma) |-- t2 \in T2 ->
      Gamma |-- (let x=t1 in t2) \in T2
  (* fix *)
  | T_Fix : forall Gamma t T,
      Gamma |-- t \in (T -> T) ->
      Gamma |-- fix t \in T
where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

(** [] *)

Hint Constructors has_type : core.

(* ================================================================= *)
(** ** Examples *)

(** **** Exercise: 5 stars, standard, optional (STLCExtended_examples)

    This section presents formalized versions of the examples from
    above (plus several more).

    For each example, uncomment proofs and replace [Admitted] by
    [Qed] once you've implemented enough of the definitions for
    the tests to pass.

    The examples at the beginning focus on specific features; you can
    use these to make sure your definition of a given feature is
    reasonable before moving on to extending the proofs later in the
    file with the cases relating to this feature.
    The later examples require all the features together, so you'll
    need to come back to these when you've got all the definitions
    filled in. *)

Module Examples.

(* ----------------------------------------------------------------- *)
(** *** Preliminaries *)

(** First, let's define a few variable names: *)

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".
Notation processSum := "processSum".
Notation n := "n".
Notation eq := "eq".
Notation m := "m".
Notation evenodd := "evenodd".
Notation even := "even".
Notation odd := "odd".
Notation eo := "eo".

(** Next, a bit of Coq hackery to automate searching for typing
    derivations.  You don't need to understand this bit in detail --
    just have a look over it so that you'll know what to look for if
    you ever find yourself needing to make custom extensions to
    [auto].

    The following [Hint] declarations say that, whenever [auto]
    arrives at a goal of the form [(Gamma |-- (tm_app e1 e1) \in T)], it
    should consider [eapply T_App], leaving an existential variable
    for the middle type T1, and similar for [lcase]. That variable
    will then be filled in during the search for type derivations for
    [e1] and [e2].  We also include a hint to "try harder" when
    solving equality goals; this is useful to automate uses of
    [T_Var] (which includes an equality as a precondition). *)

Hint Extern 2 (has_type _ (tm_app _ _) _) =>
  eapply T_App; auto : core.
Hint Extern 2 (has_type _ (tm_lcase _ _ _ _ _) _) =>
  eapply T_Lcase; auto : core.
Hint Extern 2 (_ = _) => compute; reflexivity : core.

(* ----------------------------------------------------------------- *)
(** *** Numbers *)

Module Numtest.

Definition tm_test :=
  <{if0
    (pred
      (succ
        (pred
          (2 * 0))))
    then 5
    else 6}>.

Example typechecks :
  empty |-- tm_test \in Nat.
Proof.
  unfold tm_test.
  (* This typing derivation is quite deep, so we need
     to increase the max search depth of [auto] from the
     default 5 to 10. *)
  auto 10.
Qed.

Example reduces :
  tm_test -->* 5.
Proof.
  unfold tm_test. normalize.
Qed.

End Numtest.

(* ----------------------------------------------------------------- *)
(** *** Products *)

Module ProdTest.

Definition tm_test :=
  <{((5,6),7).fst.snd}>.

Example typechecks :
  empty |-- tm_test \in Nat.
Proof. unfold tm_test. eauto. Qed.

Example reduces :
  tm_test -->* 6.
Proof.
  unfold tm_test. normalize.
Qed.

End ProdTest.

(* ----------------------------------------------------------------- *)
(** *** [let] *)

Module LetTest.

Definition tm_test :=
  <{let x = (pred 6) in
    (succ x)}>.

Example typechecks :
  empty |-- tm_test \in Nat.
Proof. unfold tm_test. eauto. Qed.

Example reduces :
  tm_test -->* 6.
Proof.
  unfold tm_test. normalize.
Qed.

End LetTest.

Module LetTest1.

Definition tm_test :=
  <{let z = pred 6 in
    (succ z)}>.

Example typechecks :
  empty |-- tm_test \in Nat.
Proof. unfold tm_test. eauto. Qed.

Example reduces :
  tm_test -->* 6.
Proof.
  unfold tm_test. normalize.
Qed.

End LetTest1.

(* ----------------------------------------------------------------- *)
(** *** Sums *)

Module Sumtest1.

Definition tm_test :=
  <{case (inl Nat 5) of
    | inl x => x
    | inr y => y}>.

Example typechecks :
  empty |-- tm_test \in Nat.
Proof. unfold tm_test. eauto. Qed.

Example reduces :
  tm_test -->* 5.
Proof.
  unfold tm_test. normalize.
Qed.

End Sumtest1.

Module Sumtest2.

(* let processSum =
     \x:Nat+Nat.
        case x of
          inl n => n
          inr n => tm_test0 n then 1 else 0 in
   (processSum (inl Nat 5), processSum (inr Nat 5))    *)

Definition tm_test :=
  <{let processSum =
    (\x:Nat + Nat,
      case x of
       | inl n => n
       | inr n => (if0 n then 1 else 0)) in
    (processSum (inl Nat 5), processSum (inr Nat 5))}>.

Example typechecks :
  empty |-- tm_test \in (Nat * Nat).
Proof. unfold tm_test. eauto 10. Qed.

Example reduces :
  tm_test -->* <{(5, 0)}>.
Proof.
  unfold tm_test. normalize.
Qed.

End Sumtest2.

(* ----------------------------------------------------------------- *)
(** *** Lists *)

Module ListTest.

(* let l = cons 5 (cons 6 (nil Nat)) in
   case l of
     nil => 0
   | x::y => x*x *)

Definition tm_test :=
  <{let l = (5 :: 6 :: (nil Nat)) in
    case l of
    | nil => 0
    | x :: y => (x * x)}>.

Example typechecks :
  empty |-- tm_test \in Nat.
Proof. unfold tm_test. eauto. Qed.

Example reduces :
  tm_test -->* 25.
Proof.
  unfold tm_test. normalize.
Qed.

End ListTest.

(* ----------------------------------------------------------------- *)
(** *** [fix] *)

Module FixTest1.

Definition fact :=
  <{fix
      (\f:Nat->Nat,
        \a:Nat,
         if0 a then 1 else (a * (f (pred a))))}>.

(** (Warning: you may be able to typecheck [fact] but still have some
    rules wrong!) *)

Example typechecks :
  empty |-- fact \in (Nat -> Nat).
Proof. unfold fact. auto 10. Qed.

Example reduces :
  <{fact 4}> -->* 24.
Proof.
  unfold fact. normalize.
Qed.

End FixTest1.

Module FixTest2.

Definition map :=
  <{ \g:Nat->Nat,
       fix
         (\f:(List Nat)->(List Nat),
            \l:List Nat,
               case l of
               | nil => nil Nat
               | x::l => ((g x)::(f l)))}>.

Example typechecks :
  empty |-- map \in
    ((Nat -> Nat) -> ((List Nat) -> (List Nat))).
Proof. unfold map. auto 10. Qed.

Example reduces :
  <{map (\a:Nat, succ a) (1 :: 2 :: (nil Nat))}>
  -->* <{2 :: 3 :: (nil Nat)}>.
Proof.
  unfold map. normalize.
Qed.

End FixTest2.

Module FixTest3.

Definition equal :=
  <{fix
        (\eq:Nat->Nat->Nat,
           \m:Nat, \n:Nat,
             if0 m then (if0 n then 1 else 0)
             else (if0 n
                   then 0
                   else (eq (pred m) (pred n))))}>.

Example typechecks :
  empty |-- equal \in (Nat -> Nat -> Nat).
Proof. unfold equal. auto 10. Qed.

Example reduces :
  <{equal 4 4}> -->* 1.
Proof.
  unfold equal. normalize.
Qed.
(* GRADE_THEOREM 0.25: reduces *)

Example reduces2 :
  <{equal 4 5}> -->* 0.
Proof.
  unfold equal. normalize.
Qed.
(* GRADE_THEOREM 0.25: reduces2 *)

End FixTest3.

Module FixTest4.

Definition eotest :=
<{let evenodd =
         fix
           (\eo: ((Nat -> Nat) * (Nat -> Nat)),
              (\n:Nat, if0 n then 1 else (eo.snd (pred n)),
               \n:Nat, if0 n then 0 else (eo.fst (pred n)))) in
    let even = evenodd.fst in
    let odd  = evenodd.snd in
    (even 3, even 4)}>.

Example typechecks :
  empty |-- eotest \in (Nat * Nat).
Proof. unfold eotest. eauto 30. Qed.

Example reduces :
  eotest -->* <{(0, 1)}>.
Proof.
  unfold eotest. eauto 10. normalize.
Qed.

End FixTest4.
End Examples.
(** [] *)

(* ================================================================= *)
(** ** Properties of Typing *)

(** The proofs of progress and preservation for this enriched system
    are essentially the same (though of course longer) as for the pure
    STLC. *)

(* ----------------------------------------------------------------- *)
(** *** Progress *)

(** **** Exercise: 3 stars, standard (STLCExtended.progress)

    Complete the proof of [progress].

    Theorem: Suppose empty |-- t \in T.  Then either
      1. t is a value, or
      2. t --> t' for some t'.

    Proof: By induction on the given typing derivation. *)
Ltac des_prog' H := destruct H as [ |[ ]].
Ltac des_prog t:=
  match goal with
  | Hprog : value t \/ (exists t', t --> t')
  |- _ => des_prog' Hprog; eauto end.
Ltac discuss_value :=
  try match goal with
  Hv : value ?t,
  HT : empty |-- ?t \in (?T1 -> ?T2)
  |- _ => induction Hv; try(solve_by_invert); iac HT end;
  repeat match goal with
  Hv : value ?t,
  HT : empty |-- ?t \in Nat
  |- _ => destruct Hv; try(solve_by_invert); clear HT end;
  try match goal with
  Hv : value ?t,
  HT : empty |-- ?t \in (?T1 + ?T2)
  |- _ => destruct Hv; try(solve_by_invert); iac HT end;
  try match goal with
  Hv : value ?t,
  HT : empty |-- ?t \in (List ?T)
  |- _ => induction Hv; try(solve_by_invert) end;
  try match goal with
  Hv : value ?t,
  HT : empty |-- ?t \in (?T1 * ?T2)
  |- _ => destruct Hv; try(solve_by_invert) end;
  idtac.
Ltac work :=
  repeat match goal with
  Hprog : value ?t \/ (exists t', ?t --> t')
  |- _ => des_prog' Hprog end;
  discuss_value; eauto.
Ltac rm_eq_refl :=
  repeat match goal with
  H : ?x = ?x -> ?H' |- _ => specialize (H eq_refl) end.
Ltac inst_ty :=
  repeat match goal with
  H : empty |-- ?t \in ?T,
  IH : forall T, empty |-- ?t \in T -> _ |- _ => specialize (IH T H) end.

Theorem progress : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  (* intros t T Ht.
  remember empty as Gamma.
  generalize dependent HeqGamma.
  induction Ht; intros HeqGamma; subst; rm_eq_refl; work;
  try(discriminate); destruct n... *)

  induction t; intros T Ht; iac Ht; inst_ty; work;
  try(discriminate); destruct n...
Qed.
(** [] *)

(* ================================================================= *)
(** ** Weakening *)

(** The weakening claim and (automated) proof are exactly the
    same as for the original STLC. (We only need to increase the
    search depth of eauto to 7.) *)

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma  |-- t \in T  ->
     Gamma' |-- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto 7 using includedin_update.
Qed.

Lemma weakening_empty : forall Gamma t T,
     empty |-- t \in T  ->
     Gamma |-- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Substitution *)

(** **** Exercise: 2 stars, standard (STLCExtended.substitution_preserves_typing)

    Complete the proof of [substitution_preserves_typing]. *)
Lemma ABA_eq_AB (Gamma : context) (x1 x2 : string) (T1 T2 T3 : ty) :
  (x1 |-> T1; x2 |-> T2; x1 |-> T3; Gamma) = (x1 |-> T1; x2 |-> T2; Gamma).
Proof with eauto.
  destruct (eqb_spec x1 x2).
  - subst. repeat rewrite update_shadow...
  - rewrite (update_permute _ _ _ _ T2 T3)... rewrite update_shadow...
Qed.

Ltac solve_permute :=
  try match goal with
  IH : forall Gamma, _ = _ -> empty |-- ?v \in ?U ->
       Gamma |-- [?x ::= ?v] ?t \in ?T
  |- ?Gamma |-- [?x ::= ?v] ?t \in ?T =>
    apply IH; eauto; rewrite update_permute; eauto end;
  try match goal with
  IH : forall T Gamma, (?x |-> ?U; Gamma) |-- ?t \in T ->
       Gamma |-- [?x ::= ?v] ?t \in T
  |- (?Gamma) |-- [?x ::= ?v] ?t \in ?T =>
    apply IH; rewrite update_permute; eauto end.
Ltac eq_case_ty :=
  repeat match goal with
  |- has_type ?Gamma (if (?x =? ?y)%string then _ else _) ?T
  => destruct (eqb_spec x y); subst end;
  repeat rewrite update_shadow in *; repeat rewrite ABA_eq_AB in *; eauto; try (solve_permute; fail).

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  (x |-> U ; Gamma) |-- t \in T ->
  empty |-- v \in U   ->
  Gamma |-- [x:=v]t \in T.
Proof with eauto.
  (* intros Gamma x U t v T Ht Hv. rewrite subst_eq.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H; iac H; simpl; eauto;
  try(econstructor; eauto; eq_case_ty; eauto; fail).
  - destruct (eqb_spec x s); subst.
    + rewrite update_eq in H2.
      injection H2 as H2; subst.
      eauto using weakening_empty.
    + rewrite update_neq in H2...
  - econstructor... eq_case_ty.
    rewrite (update_permute _ _ x s0)... *)

  intros Gamma x U t v T Ht. rewrite subst_eq.
  remember (x|->U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' Heq HTv; subst Gamma; simpl;
  try(econstructor; eauto; eq_case_ty; eauto; fail).
  - destruct (eqb_spec x x0); subst.
    + rewrite update_eq in H. injection H as H; subst.
      eauto using weakening_empty.
    + rewrite update_neq in H...
  - econstructor... eq_case_ty. apply IHHt3...
    rewrite (update_permute _ _ x x1)...
    rewrite (update_permute _ _ x x2)...
Qed.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Preservation *)

(** **** Exercise: 3 stars, standard (STLCExtended.preservation)

    Complete the proof of [preservation]. *)

Ltac try_find_hastype_with_info :=
  try match goal with
  H : has_type ?Gamma ?t (?c ?T1)
  |- _ => iac H end;
  try match goal with
  H : has_type ?Gamma ?t (?c ?T1 ?T2)
  |- _ => iac H end;
  try match goal with
  H : has_type ?Gamma ?t (?c ?T1 ?T2 ?T3)
  |- _ => iac H end;
  try match goal with
  H : has_type ?Gamma ?t (?c ?T1 ?T2 ?T3 ?T4)
  |- _ => iac H end;
  try match goal with
  H : has_type ?Gamma ?t (?c ?T1 ?T2 ?T3 ?T4 ?T5)
  |- _ => iac H end;
  idtac.

Theorem preservation : forall t t' T,
     empty |-- t \in T  ->
     t --> t'  ->
     empty |-- t' \in T.
Proof with eauto.
  Hint Resolve substitution_preserves_typing : core.
  (* intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
  intros t' HE; iac HE; try(iac HT1); try(iac HT)... *)

  (* intros. generalize dependent T. induction H0; intros T' HT;
  iac HT; eauto; try(econstructor; eauto; fail);
  try_find_hastype_with_info... *)

  induction t; intros t' T Ht Hs; iac Hs; iac Ht; eauto;
  try_find_hastype_with_info...
Qed.
(** [] *)

End STLCExtended.

(* 2024-01-03 15:04 *)
