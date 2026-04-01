(** * Intro to Tax module
    This module provies some logic and structures to do a simple tax bracket
    selection and income tax calculation based on collected demographics.
*)
From LF.Alex Require Export Assert.

Inductive filing : Type :=
    | Single
    | Married.

Inductive bracket : Type :=
    | Bracket (min:nat) (max:nat) (tax:nat).
