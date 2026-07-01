(** Common standard library imports. *)

From Stdlib Require List.
Export List.ListNotations.
Open Scope list_scope.
From Stdlib Require Export
  Relations Program Wellfounded
  Lia RelationClasses SetoidList Permutation SetoidPermutation
  FunInd Recdef PeanoNat Nat Program.Wf Classical.
From Equations Require Export Equations.
Require Export Equations.Prop.Logic.

Create HintDb ct.
Create Rewrite HintDb ct.

From CegarTableaux Require Export Utils ListExt.
