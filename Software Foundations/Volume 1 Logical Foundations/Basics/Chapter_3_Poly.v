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
            + simpl in Hl1'. 
                simpl in Hl2'. 
                simpl. 
                rewrite -> Hl1'. 
                rewrite <- app_assoc. 
                reflexivity.
Qed.

Theorem rev_involutive: forall X:Type, forall l:list X,
    rev (rev l) = l.
Proof.
    intros X l.
    induction l as [|t' l' Hl'].
        - simpl. reflexivity.
        - simpl. rewrite -> rev_app_distr. rewrite -> Hl'. simpl. reflexivity.
Qed. 

(* polymorphic pairs *)
Inductive prod (X Y:Type) : Type :=
    | pair (x:X) (y:Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y:Type} (p: X * Y) : X :=
    match p with (x,_) => x end.

Definition snd {X Y:Type} (p: X * Y) : Y :=
    match p with (_,y) => y end.

Fixpoint combine {X Y:Type} (lx:list X) (ly:list Y) : list (X*Y) :=
    match lx,ly with
        | [],_ => []
        | _,[] => []
        | x :: tx, y :: ty => (x,y) :: (combine tx ty)
    end.


(*Question: What is the type of combine?
Answer: It is list of products of X and Y.
*)
Check @combine.

(*Question: What does Compute (combine [1;2] [false;false;true;true])  print?
Answer: It should print [(1,false);(2,false)]
*)
Compute (combine [1;2] [false;false;true;true]).

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
    match l with
        | [] => ([],[])
        | (x,y) :: t => (x :: (fst (split t)), y :: (snd (split t)))
    end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. simpl. reflexivity. Qed.

(* Polymorphic Options *)
Module OptionPlayground.

Inductive option (X:Type) (x:X) : Type :=
    | Some (x:X)
    | None.

Arguments Some {X}.
Arguments None {X}.

End OptionPlayground.

Fixpoint nth_error {X:Type} (l:list X) (nth:nat) : option X :=
    match l with
        | nil => None
        | a :: l' => match nth with
                        | O => Some a
                        | S n' => nth_error l' n'
                    end
    end.
    
Example test_nth_error1: nth_error [4;5;6;7] 0 = Some 4.
Proof. simpl. reflexivity. Qed.
Example test_nth_error2: nth_error [[1];[2]] 1 = Some [2].
Proof. simpl. reflexivity. Qed.
Example test_nth_error3: nth_error [true] 2 = None.
Proof. simpl. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
    match l with
        | [] => None
        | h :: t => Some h
    end.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. simpl. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. simpl. reflexivity. Qed.

(* Functions as Data *)
Definition doit3times {X:Type} (f:X -> X) (n:X) : X :=
    f (f (f n)).

Check @doit3times.

Definition minustwo (n:nat) : nat :=
    match n with
        | (S (S n')) => n'
        | _ => O
    end. 

Definition negb (b:bool) : bool :=
    if b then false else true.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. simpl. reflexivity. Qed.
Example test_doit3times': doit3times negb false = true.
Proof. simpl. reflexivity. Qed.

Fixpoint filter {X:Type} (check:X -> bool) (l:list X) : list X :=
    match l with
        | [] => []
        | h :: t =>
            if check h then h :: (filter check t)
            else filter check t
    end.

Fixpoint even (n:nat) : bool :=
    match n with
        | O => true
        | S O => false
        | S (S n') => even n'
    end.

Compute even 0.
Compute even 1.
Compute even 2.
Compute even 10.
Compute even 11.

Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. simpl. reflexivity. Qed.

Fixpoint eqb (m n:nat) : bool :=
    match m,n with
        | O,O => true
        | S m', S n' => eqb m' n'
        | _,_ => false
    end.
Notation "x =? y" := (eqb x y) (at level 70, right associativity).

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2: filter length_is_1 [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
                        = [ [3]; [4]; [8] ].
Proof. simpl. reflexivity. Qed.

Definition odd (n:nat) : bool :=
    negb (even n).

Definition countoddmembers' (l : list nat) : nat :=
  length (filter odd l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

(* Anonymous functions *)
Example test_anon_fun':
    doit3times (fun n => n * n) 2 = 256.
Proof. simpl. reflexivity. Qed.

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. simpl. reflexivity. Qed.

Fixpoint gtb (m n:nat) : bool :=
    match m,n with
        | S m', O => true
        | S m', S n' => gtb m' n'
        | _,_ => false
    end.

Example test_gtb1: gtb 3 2 = true.
Proof. simpl. reflexivity. Qed.

Example test_gtb2: gtb 2 3 = false.
Proof. simpl. reflexivity. Qed.

Example test_gtb3: gtb 3 3 = false.
Proof. simpl. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
    filter (fun n => (andb (even n) (gtb n 7))) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. simpl. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. simpl. reflexivity. Qed.

(* Exercise: 3 stars, standard (partition) *)
Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
    ((filter test l),(filter (fun e => negb (test e)) l)).
    
Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. simpl. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. simpl. reflexivity. Qed.

(* MAP *)
Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

