(** * Everything

    This file serves as a collector for all sections and exercises in the chapter.  
    It can be used to import all of the work completed.
*)
Require Export LF.Basics.Concepts.DataAndFunctions.
Require Export LF.Basics.Concepts.ProofBySimplification.
Require Export LF.Basics.Concepts.ProofByRewriting.
Require Export LF.Basics.Concepts.ProofByCaseAnalysis.

Require Export LF.Basics.Exercises.AndB3.
Require Export LF.Basics.Exercises.AndBTrueElim2.
Require Export LF.Basics.Exercises.Factorial.
Require Export LF.Basics.Exercises.LtB.
Require Export LF.Basics.Exercises.MoreExercises.
Require Export LF.Basics.Exercises.MultN1.
Require Export LF.Basics.Exercises.NandB.
Require Export LF.Basics.Exercises.PlusIdExercise.
Require Export LF.Basics.Exercises.ZeroNbeQPlus1.

(* LateDays required a special definition of <? so we 
won't export it here since it conflicts with the standard
definition. in Basics.Excercises.ZeroNbeQPlus1.

Note that the reason for the dual definition was the notation
and more specifically, the level (70 in LateDays).  This level
was necessary to get the proof to work.
*)
(* Require Export Exercises.LateDays. *)