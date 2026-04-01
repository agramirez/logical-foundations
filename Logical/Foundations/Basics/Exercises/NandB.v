(** *Instructions 
The Admitted command can be used as a placeholder for an incomplete proof. We 
use it in exercises to indicate the parts that we're leaving for you -- i.e., 
your job is to replace Admitteds with real proofs.

Remove "Admitted." below and complete the definition of the following function; 
then make sure that the Example assertions below can each be verified by Rocq. 
(I.e., fill in each proof, following the model of the orb tests above, and make 
sure Rocq accepts it.) The function should return true if either or both of its 
inputs are false.

Hint: if simpl will not simplify the goal in your proof, it's probably because 
you defined nandb without using a match expression. Try a different definition 
of nandb, or just skip over simpl and go directly to reflexivity. We'll explain 
what's happening later in the chapter. 
*)
From LF.Basics.Concepts Require Export DataAndFunctions.

Definition nandb (b1:bool) (b2:bool) : bool :=
    match b1,b2 with
        | true,true => false
        | _,_ => true
    end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.