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
       let (n, t1) = t0 in
       if forces_atm v n
       then let fired_boxes =
              apply
                (apply boxes0
                  (filter (fun pat -> let (a3, _) = pat in forces_atm v a3)))
                (map snd)
            in
            (match next_tableau (t1 :: fired_boxes) with
             | Solution.Sat t2 ->
               let y = v,({ cpls = cpls0; boxes = boxes0; dias =
                 l },((let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in
                       pr1),((t2 :: (let pr1,_ =
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
               JumpSolution.Unsat ((n, t1), core, deriv))
       else let y = v,({ cpls = cpls0; boxes = boxes0; dias =
              l },((let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr1),(
              (let pr1,_ =
                 let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
               in
               pr1),next_tableau)))
            in
            fix_F y)
  in fix_F (a,(a0,(a1,(a2,b))))

(** val tableau : Assumptions.t -> CplSolver.t -> Mcnf0.t -> Solution.t **)

let tableau a a0 b =
  let rec fix_F x =
    let a1 = let pr1,_ = x in pr1 in
    let s0 = let pr1,_ = let _,pr2 = x in pr2 in pr1 in
    let tableau0 = fun a2 a3 b0 -> let y = a2,(a3,b0) in (fun _ -> fix_F y) in
    (match inspect (solve_with_assumptions s0 a1) with
     | Sat v ->
       (match let _,pr2 = let _,pr2 = x in pr2 in pr2 with
        | [] -> Solution.Sat (Coq_make (v, []))
        | t0 :: l ->
          (match inspect
                   (tableau_jumps v t0 l [] (fun a' ->
                     tableau0 a' (make_with_clauses (first_cpls l)) l __)) with
           | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
           | JumpSolution.Unsat (failed_dia, core, deriv) ->
             let (n, t1) = failed_dia in
             let conflict_set = conflict_set_of (t0 :: l) v n core in
             let s0' = CplSolver.add_conflict_set s0 conflict_set in
             let mc0' = add_conflict_set (t0 :: l) conflict_set in
             (match tableau0 a1 s0' mc0' __ with
              | Solution.Sat t2 -> Solution.Sat t2
              | Solution.Unsat (rs_core, rs_deriv) ->
                Solution.Unsat (rs_core, (JumpRestart (v, (n, t1), deriv,
                  rs_deriv))))))
     | Unsat core -> Solution.Unsat (core, (Id core)))
  in fix_F (a,(a0,b))

(** val solve_mcnf : Mcnf0.t -> Solution.t **)

let solve_mcnf mc0 =
  let cpls0 = first_cpls mc0 in
  let s0 = make_with_clauses cpls0 in tableau [] s0 mc0

(** val solve_fml : Fml.t -> Solution.t **)

let solve_fml phi =
  apply (apply (apply phi from_fml) from_nnf) solve_mcnf
