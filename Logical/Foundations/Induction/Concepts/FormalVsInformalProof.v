(** * Formal vs. Informal Proof

    https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html#lab69
*)
Require Export LF.Induction.Concepts.ProofsWithinProofs.

Theorem add_assoc' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
simpl. rewrite IHn'. reflexivity. Qed.

Theorem add_assoc'' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
    intros n m p. induction n as [| n' IHn'].
    - (* n = 0 *)
    reflexivity.
    - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity. 
Qed.