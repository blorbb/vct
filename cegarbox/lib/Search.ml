open Assumptions
open Derivation
open DiaClause
open Tree

module JumpSolution =
 struct
  type t =
  | Sat of Tree.t list
  | Unsat of DiaClause.t * Assumptions.t * Derivation.t

  (** val t_rect :
      (Tree.t list -> 'a1) -> (DiaClause.t -> Assumptions.t -> Derivation.t
      -> 'a1) -> t -> 'a1 **)

  let t_rect f f0 = function
  | Sat t1s -> f t1s
  | Unsat (failed_dia, core, deriv) -> f0 failed_dia core deriv

  (** val t_rec :
      (Tree.t list -> 'a1) -> (DiaClause.t -> Assumptions.t -> Derivation.t
      -> 'a1) -> t -> 'a1 **)

  let t_rec f f0 = function
  | Sat t1s -> f t1s
  | Unsat (failed_dia, core, deriv) -> f0 failed_dia core deriv
 end

module Solution =
 struct
  type t =
  | Sat of Tree.t
  | Unsat of Assumptions.t * Derivation.t

  (** val t_rect :
      (Tree.t -> 'a1) -> (Assumptions.t -> Derivation.t -> 'a1) -> t -> 'a1 **)

  let t_rect f f0 = function
  | Sat t1 -> f t1
  | Unsat (core, deriv) -> f0 core deriv

  (** val t_rec :
      (Tree.t -> 'a1) -> (Assumptions.t -> Derivation.t -> 'a1) -> t -> 'a1 **)

  let t_rec f f0 = function
  | Sat t1 -> f t1
  | Unsat (core, deriv) -> f0 core deriv
 end
