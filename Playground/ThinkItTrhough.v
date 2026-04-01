(* What are we proving?
    We are proving logical properties of functions based on
    specific tactics.
*)
Fixpoint summation (a b:nat) : nat :=
    match a with
        | O => b
        | S a' => S (summation a' b)
    end.

Example test_summation1: (summation 10 5) = 15.
Proof. simpl. reflexivity. Qed.
Example test_summation2: (summation 0 10) = 10.
Proof. simpl. reflexivity. Qed.

(* to test identity we need to distinguish between the left 
and right sides*)
Theorem sum_id_r: forall a:nat,
    a = summation 0 a.
Proof.
    intros a. simpl. reflexivity.
Qed.

(* in this case we needed to use the hypothesis, while in 
the example above it was not necessary...why?*)
Theorem sum_id_r': forall a:nat,
    a = summation a 0.
Proof. 
    intros a.
    induction a as [|a' Ha'].
    - simpl. reflexivity.
    - simpl. rewrite <- Ha'. reflexivity.
Qed.


(* we can prove identity on the left side as well with the
same two tactics...although the placement of the 0 makes a
difference just as it does on the right sie. *)
Theorem sum_id_l: forall a:nat,
    summation 0 a = a.
Proof.
    intros a. simpl. reflexivity.
Qed. 

Theorem sim_id_l': forall a:nat,
    summation a 0 = a.
Proof. 
    intros a.
    induction a as [|a' Ha'].
    - simpl. reflexivity.
    - simpl. rewrite -> Ha'. reflexivity.
Qed.

(* here we define a subtraction function *)
Fixpoint subtraction (a b:nat) : nat :=
    match a,b with
        | _,O => a
        | O,_ => O
        | S a', S b' => subtraction a' b'
    end.

Theorem sub_0_l: forall a:nat, 0 = subtraction 0 a.
Proof. 
    intros a.
    destruct a.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.
Theorem sub_0_r: forall a:nat, a = subtraction a 0.
Proof.
    intros a.
    destruct a.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Theorem add_comm: forall a b c:nat,
    (summation (summation a b) c) = (summation a (summation b c)).
Proof.
    intros a b c.
    induction a.
    - induction b.
        + induction c.
            { simpl. reflexivity. }
            { simpl. reflexivity. }
        + induction c.
            { simpl. reflexivity. }
            { simpl. reflexivity. }
    - induction b.
        + induction c.
            { simpl. rewrite -> IHa. simpl. reflexivity. }
            { simpl. rewrite -> IHa. simpl. reflexivity. }
        + simpl. rewrite -> IHa. simpl. reflexivity.
Qed.

Inductive letter : Type :=
    | A | B | C | D | F.

Inductive comparison : Type :=
    | Eq | Lt | Gt.

Definition lower_letter (l:letter) : letter :=
    match l with 
        | A => B
        | B => C
        | C => D
        | D => F
        | F => F
    end.

Definition compare_letter (l1 l2:letter) : comparison :=
    match l1,l2 with
        | A,A => Eq
        | A,_ => Gt
        | B,A => Lt
        | B,B => Eq
        | B,_ => Gt
        | C,(A|B) => Lt
        | C,C => Eq
        | C,_ => Gt
        | D,D => Eq
        | D,F => Gt
        | D,_ => Lt
        | F,F => Eq
        | F,_ => Lt
    end.

Lemma lower_letter_F_is_F: lower_letter F = F.
Proof. simpl. reflexivity. Qed.

Theorem lower_letter_lowers: forall l:letter,
    compare_letter F l = Lt -> 
    compare_letter (lower_letter l) l = Lt.
Proof.
    intros l Hf.
    destruct l.
    - simpl. reflexivity. 
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - rewrite lower_letter_F_is_F. rewrite Hf. reflexivity.
Qed.