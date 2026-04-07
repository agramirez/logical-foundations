(** *Introduction

    https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html#lab97
*)
Require Export LF.Lists.Concepts.ListsOfNumbers.

Theorem nil_app : forall l : natlist,
    [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
    intros l. destruct l as [| n l'].
    - (* l = nil *)
    reflexivity.
    - (* l = cons n l' *)
    reflexivity. Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
    intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
    - (* l1 = nil *)
    reflexivity.
    - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. 
Qed.

Theorem repeat_double_firsttry : forall c n: nat,
    repeat n c ++ repeat n c = repeat n (c + c).
Proof.
intros c. induction c as [| c' IHc'].
- (* c = 0 *)
intros n. simpl. reflexivity.
- (* c = S c' *)
intros n. simpl.
(*  Now we seem to be stuck.  The IH cannot be used to
    rewrite repeat n (c' + S c'): it only works
    for repeat n (c' + c'). If the IH were more liberal here
    (e.g., if it worked for an arbitrary second summand),
    the proof would go through. *)
Abort.

Theorem repeat_plus: forall c1 c2 n: nat,
    repeat n c1 ++ repeat n c2 = repeat n (c1 + c2).
Proof.
    intros c1 c2 n.
    induction c1 as [| c1' IHc1'].
    - simpl. reflexivity.
    - simpl.
    rewrite <- IHc1'.
    reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => rev t ++ [h]
    end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist,
    length (rev l) = length l.
Proof.
    intros l. induction l as [| n l' IHl'].
    - (* l = nil *)
    reflexivity.
    - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
        by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
        involving ++, but we don't have any useful equations
        in either the immediate context or in the global
        environment!  We can make a little progress by using
        the IH to rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

Theorem app_rev_length_S_firsttry: forall l n,
    length (rev l ++ [n]) = S (length (rev l)).
Proof.
    intros l. induction l as [| m l' IHl'].
    - (* l =  *)
    intros n. simpl. reflexivity.
    - (* l = m:: l' *)
    intros n. simpl.
    (* IHl' not applicable. *)
Abort.

Theorem app_length_S: forall l n,
    length (l ++ [n]) = S (length l).
Proof.
    intros l n. induction l as [| m l' IHl'].
    - (* l =  *)
    simpl. reflexivity.
    - (* l = m:: l' *)
    simpl.
    rewrite IHl'.
    reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
    length (rev l) = length l.
Proof.
    intros l. induction l as [| n l' IHl'].
    - (* l = nil *)
    reflexivity.
    - (* l = cons *)
    simpl.
    rewrite -> app_length_S.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem app_length : forall l1 l2 : natlist,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
    (* WORKED IN CLASS *)
    intros l1 l2. induction l1 as [| n l1' IHl1'].
    - (* l1 = nil *)
    reflexivity.
    - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity. 
Qed.