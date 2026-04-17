(** * Pairs of Numbers

    https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html#lab82
*)
Require Export LF.Induction.Everything.

Module NatList.

    Inductive natprod : Type :=
        | pair (n1 n2 : nat).

    Check (pair 3 5).

    Definition fst (p:natprod) : nat :=
        match p with
            | pair n _ => n
        end.

    Definition snd (p:natprod) : nat :=
        match p with
            | pair _ n => n
        end.

    Compute fst (pair 3 5).

    Notation "( x , y )" := (pair x y).

    Compute fst (3,5).

    Definition fst' (p:natprod) : nat :=
        match p with
            | (x,_) => x
        end.

    Definition snd' (p:natprod) : nat :=
        match p with
            | (_,y) => y
        end.

    Definition swap_pair (p:natprod) : natprod :=
        match p with
            | (x,y) => (y,x)
        end.

    Theorem surjective_pairing' : forall (n m : nat),
        (n,m) = (fst (n,m), snd (n,m)).
    Proof. reflexivity. Qed.

    Theorem surjective_pairing'' : forall (n m:nat),
        (n,m) = (fst (n,m), snd (n,m)).
    Proof. intros n m. simpl. reflexivity. Qed. 

    Theorem surjective_pairing_stuck : forall (p : natprod),
        p = (fst p, snd p).
    Proof. intros p. simpl. Abort.

    Theorem surjective_pairing : forall (p : natprod),
        p = (fst p, snd p).
    Proof. intros p. destruct p as [n m]. simpl. reflexivity. Qed.

End NatList.