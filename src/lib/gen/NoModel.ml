open Assumptions
open CplSolution
open CplSolver
open Datatypes
open Fml
open ImportStd
open Lclauses
open List
open ListDef
open Logic
open Mcnf0
open McnfExt
open Nnf
open Valuation

let __ = let rec f _ = Obj.repr f in Obj.repr f

module JumpSolution =
 struct
  type t =
  | Sat
  | Unsat of int * Assumptions.t
 end

module Solution =
 struct
  type t =
  | Sat
  | Unsat of Assumptions.t

  (** val is_sat : t -> bool **)

  let is_sat = function
  | Sat -> true
  | Unsat _ -> false
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
     | [] -> JumpSolution.Sat
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
             | Solution.Sat ->
               let y = v,({ cpls = cpls0; boxes = boxes0; dias =
                 l },((let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in
                       pr1),next_tableau))
               in
               fix_F y
             | Solution.Unsat core -> JumpSolution.Unsat (n, core))
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
        | [] -> Solution.Sat
        | t0 :: l ->
          (match inspect
                   (tableau_jumps v t0 l (fun a' ->
                     tableau0 l (cplsolver_mcnf l) a' __)) with
           | JumpSolution.Sat -> Solution.Sat
           | JumpSolution.Unsat (c, core) ->
             let conflict_set = conflict_set_of (t0 :: l) v c core in
             let s0' = CplSolver.add_conflict_set s0 conflict_set in
             let mc0' = add_conflict_set (t0 :: l) conflict_set in
             tableau0 mc0' s0' a1 __))
     | Unsat core -> Solution.Unsat core)
  in fix_F (a,(a0,b))

(** val solve_mcnf : Mcnf0.t -> Solution.t **)

let solve_mcnf mc0 =
  tableau mc0 (cplsolver_mcnf mc0) []

(** val solve_fml : Fml.t -> Solution.t **)

let solve_fml phi =
  apply (apply (apply phi from_fml) from_nnf) solve_mcnf
