(** * Proofs Within Proofs

    https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html#lab69
*)
Require Export LF.Induction.Concepts.ProofByInduction.
Require Export LF.Induction.Exercises.BasicInduction.

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  replace (n + 0 + 0) with n.
  - reflexivity.
  - rewrite add_comm. simpl. rewrite add_comm. reflexivity.
Qed.

(* alex proof of concept tests *)
Theorem mult_0_plus'': forall n m:nat,
    (n + 0 + 0) * m = n * m.
Proof.
    intros n m.
    replace (n + 0) with n.
    - replace (n + 0) with n.
        + reflexivity.
        + rewrite add_0_r. reflexivity.
    - rewrite add_0_r. reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
    intros n m p q.
    (* We just need to swap (n + m) for (m + n)... seems
    like add_comm should do the trick! *)
    rewrite add_comm.
    (* Doesn't work... Rocq rewrites the wrong plus! :-( *)
Abort.

Theorem plus_rearrange : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
    intros n m p q.
    replace (n + m) with (m + n).
    - reflexivity.
    - rewrite add_comm. reflexivity.
Qed.