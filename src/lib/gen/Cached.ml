open Assumptions
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
open Trie
open Valuation

let __ = let rec f _ = Obj.repr f in Obj.repr f

module Cache = Make(Ordered)

module Caches =
 struct
  type t = Cache.t list

  (** val contains : t -> Assumptions.t -> bool **)

  let contains caches a =
    match caches with
    | [] -> false
    | c :: _ -> Cache.contains c a

  (** val destruct : t -> Cache.t * t **)

  let destruct = function
  | [] -> (Cache.empty, [])
  | c :: rest -> (c, rest)

  (** val add : t -> Assumptions.t -> t **)

  let add caches a =
    match caches with
    | [] -> (Cache.singleton a) :: []
    | c :: rest -> (Cache.add c a) :: rest
 end

module JumpSolution =
 struct
  type t =
  | Sat of Caches.t
  | Unsat of int * Assumptions.t * Caches.t
 end

module Solution =
 struct
  type t =
  | Sat of Caches.t
  | Unsat of Assumptions.t * Caches.t

  (** val is_sat : t -> bool **)

  let is_sat = function
  | Sat _ -> true
  | Unsat (_, _) -> false
 end

(** val tableau_jumps :
    t -> Lclauses.t -> Mcnf0.t -> (Assumptions.t -> Caches.t -> Solution.t)
    -> Caches.t -> JumpSolution.t **)

let tableau_jumps a a0 a1 a2 b =
  let rec fix_F x =
    let v = let pr1,_ = x in pr1 in
    let next_tableau =
      let pr1,_ = let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
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
            let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
          in
          pr2)
     | t0 :: l ->
       let (t1, t2) = t0 in
       if forces_atm v t1
       then (match let fired_boxes =
                     map snd
                       (filter (fun pat ->
                         let (a3, _) = pat in forces_atm v a3) boxes0)
                   in
                   next_tableau (t2 :: fired_boxes)
                     (let _,pr2 =
                        let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in
                        pr2
                      in
                      pr2) with
             | Solution.Sat caches ->
               let y = v,({ cpls = cpls0; boxes = boxes0; dias =
                 l },((let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in
                       pr1),(next_tableau,caches)))
               in
               fix_F y
             | Solution.Unsat (core, caches) ->
               JumpSolution.Unsat (t1, core, caches))
       else let y = v,({ cpls = cpls0; boxes = boxes0; dias =
              l },((let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr1),(next_tableau,
              (let _,pr2 =
                 let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
               in
               pr2))))
            in
            fix_F y)
  in fix_F (a,(a0,(a1,(a2,b))))

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
                      inspect
                        (tableau_jumps v t0 l (fun a' caches1' ->
                          tableau0 l s1 a' caches1' __) t2) with
                | JumpSolution.Sat caches0 ->
                  Solution.Sat ((Cache.add t1 a2) :: caches0)
                | JumpSolution.Unsat (c, core, caches0) ->
                  let conflict_set = conflict_set_of (t0 :: l) v c core in
                  let s0' = CplSolver.add_conflict_set s0 conflict_set in
                  let mc0' = add_conflict_set (t0 :: l) conflict_set in
                  tableau0 mc0' s0' a2 (t1 :: caches0) __))
          | Unsat core -> Solution.Unsat (core, caches))
  in fix_F (a,(a0,(a1,b)))

(** val solve_mcnf : Mcnf0.t -> Solution.t **)

let solve_mcnf mc0 =
  tableau mc0 (cplsolver_mcnf mc0) [] []

(** val solve_fml : Fml.t -> Solution.t **)

let solve_fml phi =
  solve_mcnf (from_nnf (from_fml phi))
