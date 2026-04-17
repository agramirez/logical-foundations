(** *Proof by Induction Chapter

    https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html
*)
Require Export LF.Basics.Everything.

Theorem add_0_r_firsttry : forall n:nat,
    n + 0 = n.
Proof.
    intros n.
    simpl. (* Does nothing! *)
Abort.

Theorem add_0_r_secondtry : forall n:nat,
    n + 0 = n.
Proof.
    intros n. destruct n as [| n'] eqn:E.
    - (* n = 0 *)
    reflexivity. (* so far so good... *)
    - (* n = S n' *)
    simpl. (* ...but here we are stuck again *)
Abort.

Theorem add_0_r : forall n:nat, 
    n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. 
Qed.

Theorem minus_n_n : forall n,
    minus n n = 0.
Proof.
    (* WORKED IN CLASS *)
    intros n. induction n as [| n' IHn'].
    - (* n = 0 *)
    simpl. reflexivity.
    - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. 
Qed.

Fixpoint double (n:nat) :=
    match n with
        | O => O
        | S n' => S (S (double n'))
    end.

Check double.