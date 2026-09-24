open Assumptions
open Cct
open CplSolution
open CplSolver
open Datatypes
open DiaClause
open Fml
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
  | Unsat of DiaClause.t * Assumptions.t * Cct.t

  (** val t_rect :
      (Tree.t list -> 'a1) -> (DiaClause.t -> Assumptions.t -> Cct.t -> 'a1)
      -> t -> 'a1 **)

  let t_rect sat unsat = function
  | Sat t1s -> sat t1s
  | Unsat (failed_dia, core, cct) -> unsat failed_dia core cct

  (** val t_rec :
      (Tree.t list -> 'a1) -> (DiaClause.t -> Assumptions.t -> Cct.t -> 'a1)
      -> t -> 'a1 **)

  let t_rec sat unsat = function
  | Sat t1s -> sat t1s
  | Unsat (failed_dia, core, cct) -> unsat failed_dia core cct
 end

module Solution =
 struct
  type t =
  | Sat of Tree.t
  | Unsat of Assumptions.t * Cct.t

  (** val t_rect :
      (Tree.t -> 'a1) -> (Assumptions.t -> Cct.t -> 'a1) -> t -> 'a1 **)

  let t_rect sat unsat = function
  | Sat t1 -> sat t1
  | Unsat (core, cct) -> unsat core cct

  (** val t_rec :
      (Tree.t -> 'a1) -> (Assumptions.t -> Cct.t -> 'a1) -> t -> 'a1 **)

  let t_rec sat unsat = function
  | Sat t1 -> sat t1
  | Unsat (core, cct) -> unsat core cct

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
       let (t1, t2) = t0 in
       if forces_atm v t1
       then (match let fired_boxes =
                     map snd
                       (filter (fun pat ->
                         let (a2, _) = pat in forces_atm v a2) boxes0)
                   in
                   next_tableau (t2 :: fired_boxes) with
             | Solution.Sat t3 ->
               (match let y = v,({ cpls = cpls0; boxes = boxes0; dias =
                        l },((let pr1,_ =
                                let _,pr2 = let _,pr2 = x in pr2 in pr2
                              in
                              pr1),next_tableau))
                      in
                      fix_F y with
                | JumpSolution.Sat t1s ->
                  JumpSolution.Sat (app t1s (t3 :: []))
                | JumpSolution.Unsat (failed_dia, core, cct) ->
                  JumpSolution.Unsat (failed_dia, core, cct))
             | Solution.Unsat (core, cct) ->
               JumpSolution.Unsat ((t1, t2), core, cct))
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
           | JumpSolution.Unsat (failed_dia, core, cct) ->
             let (t1, t2) = failed_dia in
             let conflict_set = t1 :: (box_culprits (t0 :: l) v core) in
             let s0' = add_conflict_set s0 conflict_set in
             let mc0' = add_cs (t0 :: l) conflict_set in
             (match tableau0 mc0' s0' a1 __ with
              | Solution.Sat t3 -> Solution.Sat t3
              | Solution.Unsat (rs_core, rs_cct) ->
                Solution.Unsat (rs_core, (JumpRestart (v, (t1, t2), cct,
                  rs_cct))))))
     | Unsat core -> Solution.Unsat (core, (Local core)))
  in fix_F (a,(a0,b))

(** val solve_mcnf : Mcnf0.t -> Solution.t **)

let solve_mcnf mc0 =
  tableau mc0 (cplsolver_mcnf mc0) []

(** val solve_fml : Fml.t -> Solution.t **)

let solve_fml phi =
  solve_mcnf (from_nnf (from_fml phi))
