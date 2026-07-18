open Assumptions
open CplSolution
open CplSolver
open Datatypes
open Derivation
open DiaClause
open Fml
open Lclauses
open List
open ListDef
open Logic
open Mcnf0
open McnfExt
open Nnf
open Spec
open Tree
open Valuation

let __ = let rec f _ = Obj.repr f in Obj.repr f

module Solution = Solution

module JumpSolution = JumpSolution

(** val tableau_jumps :
    t -> Lclauses.t -> Mcnf0.t -> Tree.t list -> (Assumptions.t ->
    Solution.t) -> JumpSolution.t **)

let tableau_jumps a a0 a1 a2 b =
  let rec fix_F x =
    let v = let pr1,_ = x in pr1 in
    let next_tableau =
      let _,pr2 = let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
      in
      pr2
    in
    let { cpls = cpls0; boxes = boxes0; dias = dias0 } =
      let pr1,_ = let _,pr2 = x in pr2 in pr1
    in
    (match dias0 with
     | [] ->
       JumpSolution.Sat
         (let pr1,_ =
            let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
          in
          pr1)
     | t0 :: l ->
       let (t1, t2) = t0 in
       if forces_atm v t1
       then let fired_boxes =
              map snd
                (filter (fun pat -> let (a3, _) = pat in forces_atm v a3)
                  boxes0)
            in
            (match next_tableau (t2 :: fired_boxes) with
             | Solution.Sat t3 ->
               let y = v,({ cpls = cpls0; boxes = boxes0; dias =
                 l },((let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in
                       pr1),((t3 :: (let pr1,_ =
                                       let _,pr2 =
                                         let _,pr2 = let _,pr2 = x in pr2 in
                                         pr2
                                       in
                                       pr2
                                     in
                                     pr1)),next_tableau)))
               in
               fix_F y
             | Solution.Unsat (core, deriv) ->
               JumpSolution.Unsat ((t1, t2), core, deriv))
       else let y = v,({ cpls = cpls0; boxes = boxes0; dias =
              l },((let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr1),(
              (let pr1,_ =
                 let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
               in
               pr1),next_tableau)))
            in
            fix_F y)
  in fix_F (a,(a0,(a1,(a2,b))))

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
                   (tableau_jumps v t0 l [] (fun a' ->
                     tableau0 l (cplsolver_mcnf l) a' __)) with
           | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
           | JumpSolution.Unsat (failed_dia, core, deriv) ->
             let (t1, t2) = failed_dia in
             let conflict_set = conflict_set_of (t0 :: l) v t1 core in
             let s0' = CplSolver.add_conflict_set s0 conflict_set in
             let mc0' = add_conflict_set (t0 :: l) conflict_set in
             (match tableau0 mc0' s0' a1 __ with
              | Solution.Sat t3 -> Solution.Sat t3
              | Solution.Unsat (rs_core, rs_deriv) ->
                Solution.Unsat (rs_core, (JumpRestart (v, (t1, t2), deriv,
                  rs_deriv))))))
     | Unsat core -> Solution.Unsat (core, (Id core)))
  in fix_F (a,(a0,b))

(** val solve_mcnf : Mcnf0.t -> Solution.t **)

let solve_mcnf mc0 =
  tableau mc0 (cplsolver_mcnf mc0) []

(** val solve_fml : Fml.t -> Solution.t **)

let solve_fml phi =
  solve_mcnf (from_nnf (from_fml phi))
