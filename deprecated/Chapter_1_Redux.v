Module GPS.

(* Here we create our own version of "boolean" values.  We call it "affirm"*)
Inductive affirm : Type :=
    | Yes
    | No.

Definition nega (a:affirm) : affirm :=
    match a with Yes => No | No => Yes end.

Definition anda (a b:affirm) : affirm :=
    match a with Yes => b | No => No end.
    
Definition ora (a b:affirm) : affirm :=
    match a with Yes => Yes | No => b end.

(* simple tests to make sure that our definition of or (ora) works *)
Example test_ora1: ora Yes No = Yes.
Proof. simpl. reflexivity. Qed.
Example test_ora2: ora No No = No.
Proof. simpl. reflexivity. Qed.
Example test_ora3: ora No Yes = Yes.
Proof. simpl. reflexivity. Qed.
Example test_ora4: ora Yes Yes = Yes.
Proof. simpl. reflexivity. Qed.

(* Now we create a notation for our definitions *)
Notation "x || y" := (ora x y).
Notation "x && y" := (anda x y).

(* And now we test a chain of oras *)
Example test_ora5: No || No || Yes = Yes.
Proof. simpl. reflexivity. Qed.

(* alternate notation of conditional *)
Definition nega' (a:affirm) : affirm := if a then No else Yes.
Definition anda' (a b:affirm) : affirm := if a then b else No.
Definition ora' (a b:affirm) : affirm := if b then Yes else b. 

(* EXERCISE 1: nanda *)
Definition nanda (a b:affirm) : affirm :=
    match a,b with
        | Yes,Yes => No
        | _,_ => Yes
    end.

Example test_nanda1: (nanda Yes No) = Yes.
Proof. simpl. reflexivity. Qed.
Example test_nanda2: (nanda No Yes) = Yes.
Proof. simpl. reflexivity. Qed.
Example test_nanda3: (nanda No No) = Yes.
Proof. simpl. reflexivity. Qed.
Example test_nanda4: (nanda Yes Yes) = No.
Proof. simpl. reflexivity. Qed.

(* EXERCISE 2: anda3 *)
Definition anda3 (a b c:affirm) : affirm :=
    match a,b,c with
        | Yes,Yes,Yes => Yes
        | _,_,_ => No
    end.

Example test_anda31: (anda3 Yes Yes Yes) = Yes.
Proof. simpl. reflexivity. Qed.
Example test_anda32: (anda3 No Yes Yes) = No.
Proof. simpl. reflexivity. Qed.
Example test_anda33: (anda3 Yes No Yes) = No.
Proof. simpl. reflexivity. Qed.
Example test_anda34: (anda3 Yes Yes No) = No.
Proof. simpl. reflexivity. Qed.

(* learning about checks *)
Check Yes.
Check (nega Yes).
Check nega.

End GPS.

Module Tax.

Inductive filer : Type :=
    | Single (income:nat)
    | Married (husband wife:nat).

End Tax.

Module Forefathers.
Import GPS.

Inductive counting : Type :=
    | One
    | More (n:counting).

Definition previous (n:counting) : counting :=
    match n with
        | One => One
        | More lessone => lessone
    end.

Check (More (More (More (More One)))).

Definition minustwo (c:counting) : counting :=
    match c with
        | One => One
        | More One => One
        | More (More other) => other
    end.

Compute (minustwo (More (More (More One)))).

(* Here we define a function for finding out if a counting number is 
odd or even *)
Fixpoint even (c:counting) : affirm :=
    match c with
        | One => No
        | More One => Yes
        | More c' => even c'
    end.

Example test_even1: even One = No.
Proof. simpl. reflexivity. Qed.
Example test_even2: even (More One) = Yes.
Proof. simpl. reflexivity. Qed.

Definition odd (c:counting) : affirm :=
    nega (even c).

Fixpoint plus (n m:counting) : counting :=
    match n with
        | One => More m
        | More n' => More (plus n' m)
    end. 

Definition one := One.
Definition two := (More One).
Definition three := (More (More One)).
Definition five := (More (More (More (More One)))).

Compute (plus two three).

Compute odd five.

Example test_odd1: odd five = No.
Proof. simpl. reflexivity. Qed.

Fixpoint  multiply (m n:counting) : counting :=
    match m with
        | One => n
        | More m' => plus n (multiply m' n)
    end.

Example test_multiply1: multiply One three = three.
Proof. simpl. reflexivity. Qed.
Example test_multiply2: multiply One One = One.
Proof. simpl. reflexivity. Qed.
Example test_multiply3: multiply two three = More (More (More (More (More One)))).
Proof. simpl. reflexivity. Qed.

Fixpoint minus (m n:counting) : counting :=
    match m,n with
        | One,_ => One
        | More m',More n' => minus m' n'
        | _,One => m
    end.

Fixpoint exponent (exp pow:counting) : counting :=
    match pow with
        | One => One
        | More pow' => multiply exp (exponent exp pow')
    end.

Example test_exponent1: exponent One One = One.
Proof. simpl. reflexivity. Qed.
Example test_exponent2: exponent One (More (More One)) = One.
Proof. simpl. reflexivity. Qed.
Example test_exponent3: exponent (More One) (More One) = (More (More (More One))).
Proof. simpl. reflexivity. Qed.

End Forefathers.