(** * Introduction to LateDays
    The LateDays module is my solution to the __Course Late Policies, Formalized__
    section of the Logical Foundations: Basics chapter.
*)

(** [letter] defines the major grading letters given to students. *)
Inductive letter : Type := A | B | C | D | F.
(** [modifer] defines the modifiers to the letter grades (e.g. A-, C+, etc.).
    The Natural modified is used when no "real" modifier is provided for a letter
    (e.g. A, B, etc.)
*)
Inductive modifier : Type := Plus | Natural | Minus.
(** [grade] is the combination of Letter grade and it's modifier (e.g. A+, A, A-, etc.) *)
Inductive grade : Type := Grade (l:letter) (m:modifier).
(** [comparison] is a type used to compare grades.  This will serve to prove certain 
properties about our grading functions. *)
Inductive comparison : Type := Gt | Eq | Lt.

(* some sanity checks*)
Check Grade A Plus.
Check Grade D Minus.

(** [letter_comparison], as the name implies, compares two letter's to determine their place
in the sequence of grades.  That is, an A is a better grade than B and C is a lesser grade than B. 
Since we're lowering grades based on the number of late days of an assignment, then it stands to
reason that we will find this property useful to know which grades are higher and which are lower.
*)
Definition letter_comparison (f s:letter) : comparison :=
    match f,s with
        | A,A => Eq
        | A,_ => Gt
        | B,A => Lt
        | B,B => Eq
        | B,_ => Gt
        | C,C => Eq
        | C,(A|B) => Lt
        | C,_ => Gt
        | D,D => Eq
        | D,(A|B|C) => Lt
        | D,_ => Gt
        | F,F => Eq
        | F,_ => Lt
    end.

(* sanity check examples for grades *)
Example a_gt_c: (letter_comparison A C) = Gt.
Proof. simpl. reflexivity. Qed.
Example b_lt_a: letter_comparison B A = Lt.
Proof. simpl. reflexivity. Qed.
Example d_eq_d: letter_comparison D D = Eq.
Proof. simpl. reflexivity. Qed.
Example b_gt_f: letter_comparison B F = Gt.
Proof. simpl. reflexivity. Qed.

(** [letter_comparison_eq] is a proof that comparing any letter to itself will always yield equality. *)
Theorem letter_comparison_eq: forall l:letter, letter_comparison l l = Eq.
Proof. intros [].
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

(** [modifier_comparison] compares the letter modifier in the same way that we compare letters.
    Again, since we're make a distinction of lowering or highering grades, then we must have a 
    way to compare modifiers. *)
Definition modifier_comparison (f s:modifier) : comparison :=
    match f,s with
        | Plus,Plus => Eq
        | Plus,_ => Gt
        | Natural,Plus => Lt
        | Natural,Natural => Eq
        | Natural,_ => Gt
        | Minus,Minus => Eq
        | Minus,_ => Lt
    end.

(** [modifier_comparison_eq] proof that comparing a modifier to itself will always yield equal. *)
Theorem modifier_comparison_eq: forall m:modifier, modifier_comparison m m = Eq.
Proof. intros [].
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

(** [grade_comparison] compares the first grade and determines if it is greater, lesser, or equal to the second. *)
Definition grade_comparison (g1 g2 : grade) : comparison :=
    match g1,g2 with
        | Grade L1 M1, Grade L2 M2 => 
            match letter_comparison L1 L2 with
                | Eq => modifier_comparison M1 M2 
                | Lt => Lt
                | Gt => Gt
            end
    end.

(* sanity checks *)
Example test_gc_Am_Bp_Gt: grade_comparison (Grade A Minus) (Grade B Plus) = Gt.
Proof. simpl. reflexivity. Qed.
Example test_gc_Am_Ap_Lt: grade_comparison (Grade A Minus) (Grade A Plus) = Lt.
Proof. simpl. reflexivity. Qed.
Example test_gc_Fp_Fp_Eq: grade_comparison (Grade F Plus) (Grade F Plus) = Eq.
Proof. simpl. reflexivity. Qed.
Example test_gc_Bm_Cp_Gt: grade_comparison (Grade B Minus) (Grade C Plus) = Gt.
Proof. simpl. reflexivity. Qed.

(** [lower_letter] moves a letter down the "goodness" sequence.  Note, once we 
    get to F there is no "lower letter" therefore we yield F back. *)
Definition lower_letter (l:letter) : letter :=
    match l with
        | A => B
        | B => C
        | C => D
        | D => F
        | F => F
    end.

(** [lower_letter_F_is_F] a lemma that states the obvious, but is useful in future proofs. *)
Lemma lower_letter_F_is_F:
    lower_letter F = F.
Proof.
  simpl. reflexivity.
Qed.

(** [lower_letter_lowers] proves that when we call lower_letter on a letter, we get a "lower" 
    letter back.  Note that because F lowers to F we must use our lower_letter_F_is_F lemma 
    to complete our proof. *)
Theorem lower_letter_lowers: forall l:letter, 
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.
Proof. intros l H. destruct l eqn:Hl. 
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - rewrite -> lower_letter_F_is_F. rewrite -> H. reflexivity.
Qed.

(** [lower_grade] lowers a grade by lower to the lower modifier or switching 
    and switching to a lower letter when appropriate. 
    
    TODO: We're treating the grade F-, F+ and F as if they were different values...
    I think this should be modified such that F is F no matter the modifier.
    So, for example, there is no difference between F- and F+, and so 
    compare_grade (Grade F Natural) (Grade F Plus) would yield Eq...I think this is 
    part of the assignment...but I'll modify it once I'm done refactoring.
*)
Definition lower_grade (g:grade) : grade :=
    match g with
        | Grade l Minus => match l with 
            | F => g 
            | _ => Grade (lower_letter l) Plus
        end
        | Grade l Plus => Grade l Natural
        | Grade l Natural => Grade l Minus 
    end. 

(* sanity checks *)
Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof. simpl. reflexivity. Qed.
Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof. simpl. reflexivity. Qed.
Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof. simpl. reflexivity. Qed.
Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof. simpl. reflexivity. Qed.
Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof. simpl. reflexivity. Qed.
Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof. simpl. reflexivity. Qed.
Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof. simpl. reflexivity. Qed.

(** [lower_grade_F_Minus] yields itself since we can't get "lower" than F Minus. 

    TODO: This should be changed such that (Grade F Plus) yields (Grade F Normal)
    and (Grade F Minus) yields (Grade F Normal)...but I'll do that after I'm done 
    refactoring. 
*)
Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof. simpl. reflexivity. Qed.

(** [lower_grade_lowers] proves that lowering a grade yields a lower grade, except 
    in the special case of (Grade F Minus). *)
Theorem lower_grade_lowers : forall (g : grade),
    (* this hypothesis must be provided in order to complete the proof 
        because (Grade F Minus) compared to itself will yield Eq, but 
        here we are saying that ANY grade g (including (Grade F Minus)) 
        will yield Lt*)
    grade_comparison (Grade F Minus) g = Lt -> 
    grade_comparison (lower_grade g) g = Lt.
Proof.
    intros g Hf. destruct g eqn:Hg. destruct m.
    - simpl. simpl in Hf. rewrite <- Hf. rewrite -> letter_comparison_eq. reflexivity.
    - simpl. simpl in Hf. rewrite <- Hf. rewrite -> letter_comparison_eq. reflexivity.
    - destruct l eqn:Hl.
        + simpl. reflexivity.
        + simpl. reflexivity.
        + simpl. reflexivity.
        + simpl. reflexivity.
        + rewrite <- Hf. simpl. reflexivity.
Qed.

(** [lt] compares two natural numbers and returns true if they are equal, false otherwise

    TODO: I redefined this theory instead of importing it from Basics.v because I didn't
    know how to get the dang compilation and imports to work.  I fitured it out and I should
    remove this theorem once I'm done with the refactoring.
*)
Fixpoint lt (f s:nat) : bool :=
    match f,s with
        | O,O => false
        | O,S _ => true
        | S f',O => false
        | S f',S s' => lt f' s'
    end.
Notation "x <? y" := (lt x y) (at level 40).


(** [apply_late_policy] lowers the grade based on the number of days after the 
    assignment is due. *)
Definition apply_late_policy (late_days:nat) (g:grade) : grade :=
    if late_days <? 9 then g
    else if late_days <? 17 then lower_grade g
    else if late_days <? 21 then lower_grade (lower_grade g)
    else lower_grade (lower_grade (lower_grade g)).

(** [apply_late_policy_unfold] helps us with our final proof. *)
Lemma apply_late_policy_unfold :
  forall (late_days : nat) (g : grade),
    (apply_late_policy late_days g)
    =
    (if late_days <? 9 then g else
       if late_days <? 17 then lower_grade g
       else if late_days <? 21 then lower_grade (lower_grade g)
            else lower_grade (lower_grade (lower_grade g))).
Proof.
  intros. reflexivity.
Qed.

(** [no_penalty_for_mostly_on_time] proves that we don't penalize the student
    when the assigment is handed 8 or less days after the due date. *)
Theorem no_penalty_for_mostly_on_time: forall (late_days:nat), forall (g:grade),
    (late_days <? 9 = true) ->
    (apply_late_policy late_days g) = g.
Proof.
    intros late_days g.
    intros H.
    rewrite -> apply_late_policy_unfold.
    rewrite -> H.
    reflexivity.
Qed.
    

(** [grade_lowered_once] proves that for between 9 and 16 days late
    we lower the grade by the modifier only once. *)
Theorem grade_lowered_once : forall (late_days : nat) (g : grade),
    (late_days <? 9 = false) -> 
    (late_days <? 17 = true) ->
    (apply_late_policy late_days g) = (lower_grade g).
Proof. 
    intros late_days g. 
    intros NoLessThan8. 
    intros NoMoreThan17.
    rewrite -> apply_late_policy_unfold. 
    rewrite -> NoLessThan8.
    rewrite -> NoMoreThan17.
    reflexivity.
Qed.
