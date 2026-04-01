(******************************************************************************
    Author:         Alex Ramirez
    Description:    Problems and solutions for the Basics chapter of Logical
                    Foundations book.
******************************************************************************)
From Stdlib Require Export String.

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_working_day (d:day) : day :=
    match d with
        | monday => tuesday
        | tuesday => wednesday
        | wednesday => thursday
        | thursday => friday
        | friday => monday
        | saturday => monday
        | sunday => monday
    end.

Compute (next_working_day friday).
Compute (next_working_day (next_working_day saturday)).

Example test_nwd1: next_working_day monday = tuesday.

Example test_next_working_day:
    (next_working_day (next_working_day saturday)) = tuesday.
 Proof. simpl. reflexivity. Qed.

(* EXTRA: 
    these are some of my own definitions and proofs to play around with the days
*)
Definition is_weekday (d:day) : bool :=
    match d with 
        | sunday => false
        | saturday => false
        | _ => true
    end.

Definition is_weekend (d:day) : bool :=
    match d with
        | sunday => true
        | saturday => true
        | _ => false
    end.

Theorem next_working_day_never_weekend: forall d:day,
    is_weekday (next_working_day d) = true.
Proof.
    intros d.
    destruct d.
        - simpl. reflexivity. 
        - simpl. reflexivity.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - simpl. reflexivity.
        - simpl. reflexivity.
Qed.
