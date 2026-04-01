(** * Introduction
    This is a module for testing linking and import/export functionality within the project.
*)
From Stdlib Require Export String.

(** An [assert] type is the same as true/false. *)
Inductive assert : Type :=
    | Yes
    | No.

(** [nega] negates the provided assertion (e.g. Yes becomes No, etc.) *)
Definition nega (a:assert) : assert :=
    if a then No else Yes.

(** [nega_inv] is a simple theory to prove that nega is an involutive function. *)
Theorem nega_inv: forall a:assert,
    nega (nega a) = a.
Proof.
    intros a.
    destruct a.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

(** Junke definition for test purposes. *)
Definition ok := Yes.