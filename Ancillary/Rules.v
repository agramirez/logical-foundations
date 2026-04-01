From Stdlib Require Import String.
Open Scope string_scope.

Inductive property : Type :=
    | Property (name:string) (value:nat).

Inductive list (X:Type) : Type :=
    | nil
    | cons (x:X) (l:list X).

Inductive vehicle : Type :=
    | Vehicle (properties:list property).

Inductive rule : Type :=
    | Rule (name:string) (apply:)