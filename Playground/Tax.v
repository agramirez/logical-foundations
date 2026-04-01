Module Simple.

Inductive list (X:Type) : Type :=
    | nil
    | cons (x:X) (l:list X).

Arguments nil {X}.
Arguments cons {X}.

Notation "x :: l" := (cons x l).
Notation "[]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

Check [1;2;3;4].
Check [true;false;true].

Inductive bracket : Type :=
    | Bracket (min:nat) (max:nat) (tax:nat).
Notation "( min , max , tax )" := (Bracket min max tax).

Check [(0,100,10);(101,200,20)].

Fixpoint ltb (m n:nat) : bool :=
    match m,n with
        | O,S n' => true
        | S m', S n' => ltb m' n'
        | _,_ => false
    end.
Notation "x <? y" := (ltb x y) (at level 40).
Fixpoint gtb (m n:nat) : bool :=
    match m,n with
        | S m',O => true
        | S m',S n' => gtb m' n'
        | _,_ => false
    end. 
Notation "x >? y" := (gtb x y) (at level 60).
Fixpoint eqb (m n:nat) : bool :=
    match m,n with
        | O,O => true
        | S m',S n' => eqb m' n'
        | _,_ => false
    end.
Notation "x =? y" := (eqb x y) (at level 60).
Definition apply_bracket (income:nat) (b:bracket) : nat :=
    match b with
        | (mn,mx,tx) => 
            if (income <? mn) then 0
            else if income >? mx then tx * (mx-mx)
            else tx * (income-mx)
    end.

Example test_eq_not_gt_lt1: 0 >? 0 = 0 <? 0.
Proof. simpl. reflexivity. Qed.
Example test_eq_not_gt_lt2: 1 >? 1 = 1 <? 1.
Proof. simpl. reflexivity. Qed.

Theorem gt_same: forall m:nat,
    m >? m = false.
Proof. 
    intros m. 
    induction m as [|m' Hm'].
    - simpl. reflexivity.
    - simpl. rewrite -> Hm'. reflexivity.
Qed.

Theorem lt_same: forall m:nat,
    m <? m = false.
Proof.
    intros m.
    induction m as [|m' Hm'].
    - simpl. reflexivity.
    - simpl. rewrite -> Hm'. reflexivity.
Qed.

Theorem eq_same: forall m:nat,
    m =? m = true.
Proof.
    intros m.
    induction m as [|m' Hm'].
    - simpl. reflexivity.
    - simpl. rewrite Hm'. reflexivity.
Qed.  

Theorem eq_gt_lt: forall  m:nat,
    m =? m = true -> m >? m = m <? m.
Proof.
    intros m Heq.
    induction m as [|m' Hm'].
    - simpl. reflexivity.
    - simpl. rewrite gt_same. rewrite lt_same. reflexivity.
Qed.

Theorem eq_not_gt: forall m:nat,
    m =? m <> m >? m.
Proof. 
    intros m.
    induction m as [|m' Hm'].
    - simpl. discriminate.
    - simpl. rewrite eq_same. rewrite gt_same. discriminate.
Qed.

Theorem eq_is_eqb': forall n m:nat,
    n = m -> n =? m = true.
Proof. 
    intros n m Heq.
    destruct n.
    - destruct m.
        + simpl. reflexivity.
        + rewrite <- Heq. simpl. reflexivity.
    - induction m as [|m' Hm'].
        + rewrite -> Heq. simpl. reflexivity.
        + rewrite -> Hm'.   

End Simple.