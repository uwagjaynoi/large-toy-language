(*
  This file compiles, and where there is a fail, is has error message
  Recursive call to _ has principal argument equal to _ instad of _
  OR
  cannot unify "match t with
                           | 0 | _ => F1
                           end" and "F1" (in eq1)
*)

Check nat_rec.
Check list_rec.
Axiom F1 : nat -> bool.
Axiom F2 : nat -> bool.

Fail Definition test1 : nat -> bool :=
  fix f (n : nat) : bool :=
    match n with
    | O => true
    | S n' =>
      (fix f (m : nat) : bool :=
        match m with
        | O => true
        | S m' => andb (negb (f m'))  (negb (f n'))
        end) n'
    end.

Definition test2 : nat -> bool :=
  fix f (n : nat) : bool :=
    match n with
    | O => true
    | S n' => ((fun (m : nat) => f) 100 n')
    end.

Definition test3 : nat -> bool :=
  fix f (n : nat) : bool :=
    match n with
    | O => true
    | S n' =>
      (fun (m : nat) => match m with
                        | O => f
                        | S _ => f end) n' n'
    end.
Fail Definition eq1 (t : nat):
  (fun (m : nat) => match m with
                    | O => F1
                    | S _ => F1 end) t = F1
:= eq_refl.

Fail Definition test4 : nat -> bool :=
  fix f (n : nat) : bool :=
    match n with
    | O => true
    | S n' =>
      (fun (m : nat) => match m with
                        | O => f
                        | S _ => F1 end) (S n') (S n')
    end.
Definition eq2 (t : nat) :
  (fun (m : nat) => match m with
                    | O => F2
                    | S _ => F1 end) (S t) = F1
:= eq_refl.

Fail Definition test5 : nat -> bool :=
  fix f (n : nat) : bool :=
    match n with
    | O => true
    | S n' =>
      (fun (m : nat) => match m with
                        | O => f
                        | S _ => F1 end) 1 (S n')
    end.
Definition eq3 : (fun (m : nat) =>
    match m with | O => F2 | S _ => F1 end) 1 = F1 := eq_refl.

Fail Definition test9 : nat -> bool :=
  fix f (n : nat) : bool :=
    match n with
    | O => true
    | S n' => if true then f (S n') else f n'
    end.

Definition test10 : nat -> bool :=
  fix f (n : nat) : bool :=
    match n with
    | O => true
    | S n' => if true then f n' else f n'
    end.

Fail Definition test11 : nat -> bool :=
  fix f (n : nat) : bool :=
    match n with
    | O => true
    | S n' => f 0
    end.


Inductive tree := (* binary tree *)
| tn : tree
| tc : nat -> tree -> tree -> tree
.

Axiom F3 : tree -> bool.

Definition test6 : tree -> nat :=
  fix f (t : tree) : nat :=
  match t with
  | tn => 0
  | tc n ls rs => S (f (if F3 (tc n ls rs) then ls else rs))
  end.
Definition test7 : tree -> nat :=
  fix f (t : tree) : nat :=
  match t with
  | tn => 0
  | tc n ls rs => S (f (if true then ls else (tc n ls rs)))
  end.
Fail Definition test8 : tree -> nat :=
  fix f (t : tree) : nat :=
  match t with
  | tn => 0
  | tc n ls rs => S (f (if false then ls else (tc n ls rs)))
  end.