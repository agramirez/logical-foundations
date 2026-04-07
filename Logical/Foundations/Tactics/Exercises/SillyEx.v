(** *Introduction
    https://softwarefoundations.cis.upenn.edu/lf-current/Tactics.html#lab153

    Complete the following proof using only intros and apply.
*)
Require Export LF.Basics.Concepts.DataAndFunctions.
Import Numbers.

Theorem silly_ex : forall p,
    (forall n, even n = true -> even (S n) = false) ->
    (forall n, even n = false -> odd n = true) ->
    even p = true ->
    odd (S p) = true.
Proof.
    intros p H1 H2 H3.
    apply H2. apply H1. apply H3.
Qed.