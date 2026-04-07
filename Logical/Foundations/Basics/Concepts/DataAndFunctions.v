(** * https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html

    Software Foundations / Logical Foundations / Basics / Data and Functions
*)
From Stdlib Require Export String.

(* Days of the Week *)
Section DaysOfTheWeek.
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

    Example test_next_working_day:
        (next_working_day (next_working_day saturday)) = tuesday.
    Proof. simpl. reflexivity. Qed.
End DaysOfTheWeek.

(* Booleans *)
Section Booleans.
    Inductive bool : Type :=
        | true
        | false.

    Definition negb (b:bool) : bool :=
        match b with
            | true => false
            | false => true
        end.
    Definition andb (b1:bool) (b2:bool) : bool :=
        match b1 with
            | true => b2
            | false => false
        end.
    Definition orb (b1:bool) (b2:bool) : bool :=
        match b1 with
            | true => true
            | false => b2
        end.

    Example test_orb1: (orb true false) = true.
    Proof. simpl. reflexivity. Qed.
    Example test_orb2: (orb false false) = false.
    Proof. simpl. reflexivity. Qed.
    Example test_orb3: (orb false true) = true.
    Proof. simpl. reflexivity. Qed.
    Example test_orb4: (orb true true) = true.
    Proof. simpl. reflexivity. Qed.

    Notation "x && y" := (andb x y).
    Notation "x || y" := (orb x y).
    Example test_orb5: false || false || true = true.
    Proof. simpl. reflexivity. Qed.

    Definition negb' (b:bool) : bool :=
        if b then false
        else true.
    Definition andb' (b1:bool) (b2:bool) : bool :=
        if b1 then b2
        else false.
    Definition orb' (b1:bool) (b2:bool) : bool :=
        if b1 then true
        else b2.

    Inductive bw : Type :=
        | bw_black
        | bw_white.
    Definition invert (x: bw) : bw :=
        if x then bw_white
        else bw_black.
    Compute (invert bw_black).
    (* ==> bw_white : bw *)
    Compute (invert bw_white).
    (* ==> bw_black : bw *)
End Booleans.

Module Types.
    Check true.
    (* ===> true : bool *)

    Check true
    : bool.
    Check (negb true)
    : bool.

    Check negb
    : bool -> bool.
End Types.

Module NewTypesFromOld.
    Inductive rgb : Type :=
        | red
        | green
        | blue.
    Inductive color : Type :=
        | black
        | white
        | primary (p : rgb).
End NewTypesFromOld.

Module Numbers.
    Fixpoint even (n:nat) : bool :=
        match n with
            | O => true
            | S O => false
            | S (S n') => even n'
        end.

    Definition odd (n:nat) : bool :=
        negb (even n).
        
    Example test_odd1: odd 1 = true.
    Proof. simpl. reflexivity. Qed.
    Example test_odd2: odd 4 = false.
    Proof. simpl. reflexivity. Qed.
End Numbers.