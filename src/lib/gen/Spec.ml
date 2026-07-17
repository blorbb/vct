open Assumptions
open CplSolution
open CplSolver
open Datatypes
open Derivation
open DiaClause
open Fml
open ImportStd
open Lclauses
open List
open ListDef
open Logic
open Mcnf0
open McnfExt
open Nnf
open Tree
open Valuation

let __ = let rec f _ = Obj.repr f in Obj.repr f

module JumpSolution =
 struct
  type t =
  | Sat of Tree.t list
  | Unsat of DiaClause.t * Assumptions.t * Derivation.t

  (** val t_rect :
      (Tree.t list -> 'a1) -> (DiaClause.t -> Assumptions.t -> Derivation.t
      -> 'a1) -> t -> 'a1 **)

  let t_rect sat unsat = function
  | Sat t1s -> sat t1s
  | Unsat (failed_dia, core, deriv) -> unsat failed_dia core deriv

  (** val t_rec :
      (Tree.t list -> 'a1) -> (DiaClause.t -> Assumptions.t -> Derivation.t
      -> 'a1) -> t -> 'a1 **)

  let t_rec sat unsat = function
  | Sat t1s -> sat t1s
  | Unsat (failed_dia, core, deriv) -> unsat failed_dia core deriv
 end

module Solution =
 struct
  type t =
  | Sat of Tree.t
  | Unsat of Assumptions.t * Derivation.t

  (** val t_rect :
      (Tree.t -> 'a1) -> (Assumptions.t -> Derivation.t -> 'a1) -> t -> 'a1 **)

  let t_rect sat unsat = function
  | Sat t1 -> sat t1
  | Unsat (core, deriv) -> unsat core deriv

  (** val t_rec :
      (Tree.t -> 'a1) -> (Assumptions.t -> Derivation.t -> 'a1) -> t -> 'a1 **)

  let t_rec sat unsat = function
  | Sat t1 -> sat t1
  | Unsat (core, deriv) -> unsat core deriv

  (** val is_sat : t -> bool **)

  let is_sat = function
  | Sat _ -> true
  | Unsat (_, _) -> false
 end

(** val tableau_jumps :
    t -> Lclauses.t -> Mcnf0.t -> (Assumptions.t -> Solution.t) ->
    JumpSolution.t **)

let tableau_jumps a a0 a1 b =
  let rec fix_F x =
    let v = let pr1,_ = x in pr1 in
    let next_tableau =
      let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
    in
    let { cpls = cpls0; boxes = boxes0; dias = dias0 } =
      let pr1,_ = let _,pr2 = x in pr2 in pr1
    in
    (match dias0 with
     | [] -> JumpSolution.Sat []
     | t0 :: l ->
       let (n, t1) = t0 in
       if forces_atm v n
       then (match let fired_boxes =
                     apply
                       (apply boxes0
                         (filter (fun pat ->
                           let (a2, _) = pat in forces_atm v a2)))
                       (map snd)
                   in
                   next_tableau (t1 :: fired_boxes) with
             | Solution.Sat t2 ->
               (match let y = v,({ cpls = cpls0; boxes = boxes0; dias =
                        l },((let pr1,_ =
                                let _,pr2 = let _,pr2 = x in pr2 in pr2
                              in
                              pr1),next_tableau))
                      in
                      fix_F y with
                | JumpSolution.Sat t1s ->
                  JumpSolution.Sat (app t1s (t2 :: []))
                | JumpSolution.Unsat (failed_dia, core, deriv) ->
                  JumpSolution.Unsat (failed_dia, core, deriv))
             | Solution.Unsat (core, deriv) ->
               JumpSolution.Unsat ((n, t1), core, deriv))
       else let y = v,({ cpls = cpls0; boxes = boxes0; dias =
              l },((let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr1),next_tableau))
            in
            fix_F y)
  in fix_F (a,(a0,(a1,b)))

(** val tableau : Mcnf0.t -> CplSolver.t -> Assumptions.t -> Solution.t **)

let tableau a a0 b =
  let rec fix_F x =
    let s0 = let pr1,_ = let _,pr2 = x in pr2 in pr1 in
    let a1 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in
    let tableau0 = fun a2 a3 b0 -> let y = a2,(a3,b0) in (fun _ -> fix_F y) in
    (match inspect (solve_with_assumptions s0 a1) with
     | Sat v ->
       (match let pr1,_ = x in pr1 with
        | [] -> Solution.Sat (Coq_make (v, []))
        | t0 :: l ->
          (match inspect
                   (tableau_jumps v t0 l (fun a' ->
                     tableau0 l (cplsolver_mcnf l) a' __)) with
           | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
           | JumpSolution.Unsat (failed_dia, core, deriv) ->
             let (n, t1) = failed_dia in
             let conflict_set = conflict_set_of (t0 :: l) v n core in
             let s0' = CplSolver.add_conflict_set s0 conflict_set in
             let mc0' = add_conflict_set (t0 :: l) conflict_set in
             (match tableau0 mc0' s0' a1 __ with
              | Solution.Sat t2 -> Solution.Sat t2
              | Solution.Unsat (rs_core, rs_deriv) ->
                Solution.Unsat (rs_core, (JumpRestart (v, (n, t1), deriv,
                  rs_deriv))))))
     | Unsat core -> Solution.Unsat (core, (Id core)))
  in fix_F (a,(a0,b))

(** val solve_mcnf : Mcnf0.t -> Solution.t **)

let solve_mcnf mc0 =
  tableau mc0 (cplsolver_mcnf mc0) []

(** val solve_fml : Fml.t -> Solution.t **)

let solve_fml phi =
  apply (apply (apply phi from_fml) from_nnf) solve_mcnf
