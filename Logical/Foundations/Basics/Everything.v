(** * Everything

    This file serves as a collector for all sections and exercises in the chapter.  
    It can be used to import all of the work completed.
*)
Require Export Concepts.DataAndFunctions.
Require Export Concepts.ProofBySimplification.
Require Export Concepts.ProofByRewriting.
Require Export Concepts.ProofByCaseAnalysis.

Require Export Exercises.AndB3.
Require Export Exercises.AndBTrueElim2.
Require Export Exercises.Factorial.
Require Export Exercises.LtB.
Require Export Exercises.MoreExercises.
Require Export Exercises.MultN1.
Require Export Exercises.NandB.
Require Export Exercises.PlusIdExercise.
Require Export Exercises.ZeroNbeQPlus1.

(* LateDays required a special definition of <? so we 
won't export it here since it conflicts with the standard
definition. in Basics.Excercises.ZeroNbeQPlus1.

Note that the reason for the dual definition was the notation
and more specifically, the level (70 in LateDays).  This level
was necessary to get the proof to work.
*)
(* Require Export Exercises.LateDays. *)