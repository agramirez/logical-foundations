Inductive list (X:Type) : Type :=
  | nil
  | cons (x:X) (l:list X).

Fixpoint repeat (X:Type) (x:X) (count:nat) : list X :=
    match count with
        | O => nil X
        | S count' => cons X x (repeat X x count')
    end.

Example test_repeat1: repeat nat 4 2 = (cons nat 4 (cons nat 4 (nil nat))).
Proof. simpl. reflexivity. Qed.
Example test_repeat2: repeat bool false 1 = (cons bool false (nil bool)).
Proof. simpl. reflexivity. Qed.

Module MumbleGrumble.
    Inductive mumble : Type :=
        | a
        | b (x : mumble) (y : nat)
        | c.
    Inductive grumble (X:Type) : Type :=
        | d (m : mumble)
        | e (x : X).
    
    (* Which of the following are well-typed elements of grumble X for some type 
    X? (Add YES or NO to each line.*)
    (*
        d (b a 5) (* fails, d is generic and requires a type specifier*)
        d mumble (b a 5) (* works as expected, because the type mumble is specified *)
        d bool (b a 5) (* works as expected because a type is specified, even though not used*)
        e bool true (* works as expected because the correct type is specified and used *)
        e mumble (b c 0) (* works as expected because correct type is specified and used *)
        e bool (b c 0) (* does not work as expected, because wrong type is specified *)
        c (* works as expected*)
    *)
End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
    match count with 
        | O => nil X
        | S count' => cons X x (repeat' X x count')
    end.

Check repeat'.
Check repeat.

Fixpoint repeat'' X x count : list X :=
    match count with
        | O => nil _
        | S count' => cons _ x (repeat'' _ x count')
    end.

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Definition list123''' := cons 1 (cons 2 (cons 3 nil)).

Inductive list' {X:Type} : Type :=
    | nil'
    | cons' (x:X) (l:list').


Fixpoint app {X:Type} (l1 l2:list X) : list X :=
    match l1 with
        | nil => l2
        | cons h t => cons h (app t l2)
    end.

Example test_app1: 
    app (cons 1 (cons 2 nil)) (cons 3 (cons 4 nil)) = 
    (cons 1 (cons 2 (cons 3 (cons 4 nil)))).
Proof. simpl. reflexivity. Qed.

Example test_app2:
    app (cons 1 nil) nil = cons 1 nil.
Proof. simpl. reflexivity. Qed.

Fixpoint rev {X:Type} (l:list X) : list X :=
    match l with
        | nil => nil
        | cons h t => app (rev t) (cons h nil)
    end.

Example test_rev1: rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. simpl. reflexivity. Qed.

Example test_rev2: rev (cons true nil) = cons true nil.
Proof. simpl. reflexivity. Qed.

Fixpoint length {X:Type} (l:list X) : nat :=
    match l with
        | nil => O
        | cons h t => S (length t)
    end.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. simpl. reflexivity. Qed.

Fail Definition mynil := nil.

Check @nil.
Check @nil nat.

(* list notation *)
Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

(* Exercises for Lists *)
Theorem app_nil_r: forall (X:Type), forall l:list X,
    l ++ [] = l.
Proof. 
    intros X l.
    induction l as [|type l' Hl'].
    - simpl. reflexivity.
    - simpl. rewrite -> Hl'. reflexivity.
Qed.

Theorem app_assoc: forall A (l m n:list A),
    l ++ m ++ n = (l ++ m) ++ n.
Proof.
    intros A l m n.
    induction l as [|t' l' Hl'].
    - induction m as [|t'' m' Hm'].
        + induction n as [|t''' n' Hn'].
            { simpl. reflexivity. }
            { simpl. reflexivity. }
        + induction n as [|t''' n' Hn'].
            { simpl. reflexivity. }
            { simpl. reflexivity. }
    - simpl. rewrite <- Hl'. reflexivity.
Qed.

Theorem app_length: forall (X:Type) (l1 l2:list X),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
    intros X l1 l2.
    induction l1 as [|tl1 l' Hl'].
        - simpl. reflexivity.
        - simpl. rewrite <- Hl'. reflexivity.
Qed.

Example test_rev_app_distr: 
    rev ([1;2;3] ++ [4;5;6]) = rev [4;5;6] ++ rev [1;2;3].
Proof. simpl. reflexivity. Qed.

Theorem app_is_cons: forall X:Type, forall e:X, forall l:list X,
    app [e] l = e :: l.
Proof.
    intros X e l.
    simpl.
    reflexivity.
Qed. 

Theorem rev_app_distr: forall X (l1 l2:list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
    intros X l1 l2.
    induction l1 as [|t1' l1' Hl1'].
        - induction l2 as [|t2' l2' Hl2'].
            + simpl. reflexivity.
            + simpl. rewrite <- app_assoc. simpl. reflexivity.
        - induction l2 as [|t2' l2' Hl2'].
            + simpl. rewrite -> Hl1'. simpl. reflexivity.
            + simpl in Hl1'. simpl in Hl2'. simpl. rewrite -> Hl1'. rewrite <- app_assoc. reflexivity.
Qed.

Theorem rev_involutive: forall X:Type, forall l:list X,
    rev (rev l) = l.
Proof.
    intros X l.
    induction l as [|t' l' Hl'].
        - simpl. reflexivity.
        - simpl. rewrite -> rev_app_distr. rewrite -> Hl'. simpl. reflexivity.
Qed. 
