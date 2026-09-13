open Assumptions
open Cached
open CplSolution
open CplSolver
open Datatypes
open Fml
open Lclauses
open List
open ListDef
open Lit
open Logic
open Mcnf0
open McnfExt
open Nnf
open NoWit
open Valuation

let __ = let rec f _ = Obj.repr f in Obj.repr f

module Cache = Cache

module Caches = Caches

module JumpSolution = Cached.JumpSolution

module Solution = Cached.Solution

(** val get_fired_boxes : t -> Lclauses.t -> Lit.t list **)

let get_fired_boxes v l0 =
  map snd (filter (fun pat -> let (a, _) = pat in forces_atm v a) l0.boxes)

(** val tableau_jumps :
    t -> Lclauses.t -> Mcnf0.t -> (Assumptions.t -> Caches.t -> Solution.t)
    -> Lit.t list -> Caches.t -> JumpSolution.t **)

let tableau_jumps a a0 a1 a2 a3 b =
  let rec fix_F x =
    let v = let pr1,_ = x in pr1 in
    let next_tableau =
      let pr1,_ = let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
      in
      pr1
    in
    let fired_boxes =
      let pr1,_ =
        let _,pr2 = let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
        in
        pr2
      in
      pr1
    in
    let { cpls = cpls0; boxes = boxes0; dias = dias0 } =
      let pr1,_ = let _,pr2 = x in pr2 in pr1
    in
    (match dias0 with
     | [] ->
       JumpSolution.Sat
         (let _,pr2 =
            let _,pr2 =
              let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
            in
            pr2
          in
          pr2)
     | t0 :: l ->
       let (t1, t2) = t0 in
       if forces_atm v t1
       then (match next_tableau (t2 :: fired_boxes)
                     (let _,pr2 =
                        let _,pr2 =
                          let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2
                          in
                          pr2
                        in
                        pr2
                      in
                      pr2) with
             | Solution.Sat caches ->
               let y = v,({ cpls = cpls0; boxes = boxes0; dias =
                 l },((let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in
                       pr1),(next_tableau,(fired_boxes,caches))))
               in
               fix_F y
             | Solution.Unsat (core, caches) ->
               JumpSolution.Unsat (t1, core, caches))
       else let y = v,({ cpls = cpls0; boxes = boxes0; dias =
              l },((let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr1),(next_tableau,(fired_boxes,
              (let _,pr2 =
                 let _,pr2 =
                   let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
                 in
                 pr2
               in
               pr2)))))
            in
            fix_F y)
  in fix_F (a,(a0,(a1,(a2,(a3,b)))))

(** val tableau :
    Mcnf0.t -> CplSolver.t -> Assumptions.t -> Caches.t -> Solution.t **)

let tableau a a0 a1 b =
  let rec fix_F x =
    let s0 = let pr1,_ = let _,pr2 = x in pr2 in pr1 in
    let a2 = let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr1 in
    let caches = let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2 in
    let tableau0 = fun a3 a4 a5 b0 ->
      let y = a3,(a4,(a5,b0)) in (fun _ -> fix_F y)
    in
    if Caches.contains caches a2
    then Solution.Sat caches
    else (match inspect (solve_with_assumptions s0 a2) with
          | Sat v ->
            (match let pr1,_ = x in pr1 with
             | [] -> Solution.Sat (Caches.add caches a2)
             | t0 :: l ->
               let (t1, t2) = Caches.destruct caches in
               (match let s1 = cplsolver_mcnf l in
                      let fired_boxes = get_fired_boxes v t0 in
                      inspect
                        (tableau_jumps v t0 l (fun a' caches1' ->
                          tableau0 l s1 a' caches1' __) fired_boxes t2) with
                | JumpSolution.Sat caches0 ->
                  Solution.Sat ((Cache.add t1 a2) :: caches0)
                | JumpSolution.Unsat (c, core, caches0) ->
                  let conflict_set = c :: (box_culprits (t0 :: l) v core) in
                  let s0' = add_conflict_set s0 conflict_set in
                  let mc0' = add_cs (t0 :: l) conflict_set in
                  tableau0 mc0' s0' a2 (t1 :: caches0) __))
          | Unsat core -> Solution.Unsat (core, caches))
  in fix_F (a,(a0,(a1,b)))

(** val solve_mcnf : Mcnf0.t -> Solution.t **)

let solve_mcnf mc0 =
  tableau mc0 (cplsolver_mcnf mc0) [] []

(** val solve_fml : Fml.t -> Solution.t **)

let solve_fml phi =
  solve_mcnf (from_nnf (from_fml phi))
