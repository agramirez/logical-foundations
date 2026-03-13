Module First.

(*
  Author:       Alex Ramirez
  Description:  Solved problems from More Exercises section of Basics Functional Programming in Rocq (Chapter 2) of Logical Foundations
*)

Inductive letter : Type := A | B | C | D | F.
Inductive modifier : Type := Plus | Natural | Minus.
Inductive grade : Type := Grade (l:letter) (m:modifier).
Inductive comparison : Type := Gt | Eq | Lt.

Check Grade A Plus.
Check Grade D Minus.

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

Example a_gt_c: (letter_comparison A C) = Gt.
Proof. simpl. reflexivity. Qed.
Example b_lt_a: letter_comparison B A = Lt.
Proof. simpl. reflexivity. Qed.
Example d_eq_d: letter_comparison D D = Eq.
Proof. simpl. reflexivity. Qed.
Example b_gt_f: letter_comparison B F = Gt.
Proof. simpl. reflexivity. Qed.

Theorem letter_comparison_eq: forall l:letter, letter_comparison l l = Eq.
Proof. intros [].
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

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

Theorem modifier_comparison_eq: forall m:modifier, modifier_comparison m m = Eq.
Proof. intros [].
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Definition grade_comparison (g1 g2 : grade) : comparison :=
    match g1,g2 with
        | Grade L1 M1, Grade L2 M2 => 
            match letter_comparison L1 L2 with
                | Eq => modifier_comparison M1 M2 
                | Lt => Lt
                | Gt => Gt
            end
    end.

Example test_gc_Am_Bp_Gt: grade_comparison (Grade A Minus) (Grade B Plus) = Gt.
Proof. simpl. reflexivity. Qed.
Example test_gc_Am_Ap_Lt: grade_comparison (Grade A Minus) (Grade A Plus) = Lt.
Proof. simpl. reflexivity. Qed.
Example test_gc_Fp_Fp_Eq: grade_comparison (Grade F Plus) (Grade F Plus) = Eq.
Proof. simpl. reflexivity. Qed.
Example test_gc_Bm_Cp_Gt: grade_comparison (Grade B Minus) (Grade C Plus) = Gt.
Proof. simpl. reflexivity. Qed.

Definition lower_letter (l:letter) : letter :=
    match l with
        | A => B
        | B => C
        | C => D
        | D => F
        | F => F
    end.

Theorem lower_letter_F_is_F:
    lower_letter F = F.
Proof.
  simpl. reflexivity.
Qed.

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

Definition lower_grade (g:grade) : grade :=
    match g with
        | Grade l Minus => match l with 
            | F => g 
            | _ => Grade (lower_letter l) Plus
        end
        | Grade l Plus => Grade l Natural
        | Grade l Natural => Grade l Minus 
    end. 

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

Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof. simpl. reflexivity. Qed.

Theorem lower_grade_lowers : forall (g : grade),
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

Fixpoint lt (f s:nat) : bool :=
    match f,s with
        | O,O => false
        | O,S _ => true
        | S f',O => false
        | S f',S s' => lt f' s'
    end.
Notation "x <? y" := (lt x y) (at level 40).


Definition apply_late_policy (late_days:nat) (g:grade) : grade :=
    if late_days <? 9 then g
    else if late_days <? 17 then lower_grade g
    else if late_days <? 21 then lower_grade (lower_grade g)
    else lower_grade (lower_grade (lower_grade g)).

Theorem apply_late_policy_unfold :
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

Theorem no_penalty_for_mostly_on_time: forall (late_days:nat), forall (g:grade),
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

Theorem grade_lowered_once : forall (late_days : nat) (g : grade),
    (late_days <? 9 = true) ->
    (apply_late_policy late_days g) = g.
Proof.
    intros late_days g.
    intros H.
    rewrite -> apply_late_policy_unfold.
    rewrite -> H.
    reflexivity.
Qed.

End First.
