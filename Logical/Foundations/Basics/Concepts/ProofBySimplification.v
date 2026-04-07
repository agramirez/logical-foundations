(** * Proof by Simplification

    https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html#lab37
*)
Require Export DataAndFunctions.

Example plus_1_1 : 1 + 1 = 2.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
    intros n. simpl. reflexivity. 
Qed.

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
    intros n. reflexivity. 
Qed.

Theorem plus_O_n'' : forall n : nat, 0 + n = n.
Proof.
    intros m. reflexivity. 
Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
    intros n. reflexivity. 
Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
    intros n. reflexivity. 
Qed.