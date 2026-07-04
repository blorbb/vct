open Assumptions
open BoxClause
open Classes
open CplClause
open CplSolution
open CplSolver
open Datatypes
open Derivation
open DiaClause
open Fml
open Lclauses
open List
open ListDef
open Lit
open Logic
open Mchain
open MchainExt
open Mcnf0
open Nnf
open Tree
open Utils
open Valuation

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Spec =
 struct
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

  (** val tableau_jumps_clause_2_clause_2_clause_2 :
      t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Tree.t
      -> (t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) -> __
      -> JumpSolution.t) -> JumpSolution.t -> JumpSolution.t **)

  let tableau_jumps_clause_2_clause_2_clause_2 _ _ _ _ _ _ _ _ t1 _ = function
  | JumpSolution.Sat t1s -> JumpSolution.Sat (app t1s (t1 :: []))
  | JumpSolution.Unsat (failed_dia, core, deriv) ->
    JumpSolution.Unsat (failed_dia, core, deriv)

  (** val tableau_jumps_clause_2_clause_2 :
      t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      Solution.t -> (t -> Lclauses.t -> Mchain.t -> (Assumptions.t ->
      Solution.t) -> __ -> JumpSolution.t) -> JumpSolution.t **)

  let tableau_jumps_clause_2_clause_2 v cpls0 boxes0 c d dias' mc1 next_tableau0 refine tableau_jumps0 =
    match refine with
    | Solution.Sat t0 ->
      (match tableau_jumps0 v { cpls = cpls0; boxes = boxes0; dias = dias' }
               mc1 next_tableau0 __ with
       | JumpSolution.Sat t1s -> JumpSolution.Sat (app t1s (t0 :: []))
       | JumpSolution.Unsat (failed_dia, core, deriv) ->
         JumpSolution.Unsat (failed_dia, core, deriv))
    | Solution.Unsat (core, deriv) -> JumpSolution.Unsat ((c, d), core, deriv)

  (** val tableau_jumps_clause_2 :
      t -> CplClause.t list -> BoxClause.t list -> int -> bool -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) -> (t ->
      Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) -> __ ->
      JumpSolution.t) -> JumpSolution.t **)

  let tableau_jumps_clause_2 v cpls0 boxes0 c refine d dias' mc1 next_tableau0 tableau_jumps0 =
    if refine
    then (match let fired_boxes =
                  apply
                    (apply boxes0
                      (filter (fun pat -> let (a, _) = pat in forces_atm v a)))
                    (map snd)
                in
                next_tableau0 (d :: fired_boxes) with
          | Solution.Sat t0 ->
            (match tableau_jumps0 v { cpls = cpls0; boxes = boxes0; dias =
                     dias' } mc1 next_tableau0 __ with
             | JumpSolution.Sat t1s -> JumpSolution.Sat (app t1s (t0 :: []))
             | JumpSolution.Unsat (failed_dia, core, deriv) ->
               JumpSolution.Unsat (failed_dia, core, deriv))
          | Solution.Unsat (core, deriv) ->
            JumpSolution.Unsat ((c, d), core, deriv))
    else tableau_jumps0 v { cpls = cpls0; boxes = boxes0; dias = dias' } mc1
           next_tableau0 __

  (** val tableau_jumps_functional :
      t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) -> (t ->
      Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) -> __ ->
      JumpSolution.t) -> JumpSolution.t **)

  let tableau_jumps_functional v l0 mc1 next_tableau0 tableau_jumps0 =
    let { cpls = cpls0; boxes = boxes0; dias = dias0 } = l0 in
    (match dias0 with
     | [] -> JumpSolution.Sat []
     | t0 :: l ->
       let (n, t1) = t0 in
       if forces_atm v n
       then (match let fired_boxes =
                     apply
                       (apply boxes0
                         (filter (fun pat ->
                           let (a, _) = pat in forces_atm v a)))
                       (map snd)
                   in
                   next_tableau0 (t1 :: fired_boxes) with
             | Solution.Sat t2 ->
               (match tableau_jumps0 v { cpls = cpls0; boxes = boxes0; dias =
                        l } mc1 next_tableau0 __ with
                | JumpSolution.Sat t1s ->
                  JumpSolution.Sat (app t1s (t2 :: []))
                | JumpSolution.Unsat (failed_dia, core, deriv) ->
                  JumpSolution.Unsat (failed_dia, core, deriv))
             | Solution.Unsat (core, deriv) ->
               JumpSolution.Unsat ((n, t1), core, deriv))
       else tableau_jumps0 v { cpls = cpls0; boxes = boxes0; dias = l } mc1
              next_tableau0 __)

  (** val tableau_jumps :
      t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      JumpSolution.t **)

  let tableau_jumps a a0 a1 b =
    let rec fix_F x =
      let v = let pr1,_ = x in pr1 in
      let next_tableau0 =
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
                     next_tableau0 (t1 :: fired_boxes) with
               | Solution.Sat t2 ->
                 (match let y = v,({ cpls = cpls0; boxes = boxes0; dias =
                          l },((let pr1,_ =
                                  let _,pr2 = let _,pr2 = x in pr2 in pr2
                                in
                                pr1),next_tableau0))
                        in
                        fix_F y with
                  | JumpSolution.Sat t1s ->
                    JumpSolution.Sat (app t1s (t2 :: []))
                  | JumpSolution.Unsat (failed_dia, core, deriv) ->
                    JumpSolution.Unsat (failed_dia, core, deriv))
               | Solution.Unsat (core, deriv) ->
                 JumpSolution.Unsat ((n, t1), core, deriv))
         else let y = v,({ cpls = cpls0; boxes = boxes0; dias =
                l },((let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in
                      pr1),next_tableau0))
              in
              fix_F y)
    in fix_F (a,(a0,(a1,b)))

  (** val tableau_jumps_unfold_clause_2_clause_2_clause_2 :
      t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Tree.t
      -> JumpSolution.t -> JumpSolution.t **)

  let tableau_jumps_unfold_clause_2_clause_2_clause_2 _ _ _ _ _ _ _ _ t1 = function
  | JumpSolution.Sat t1s -> JumpSolution.Sat (app t1s (t1 :: []))
  | JumpSolution.Unsat (failed_dia, core, deriv) ->
    JumpSolution.Unsat (failed_dia, core, deriv)

  (** val tableau_jumps_unfold_clause_2_clause_2 :
      t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      Solution.t -> JumpSolution.t **)

  let tableau_jumps_unfold_clause_2_clause_2 v cpls0 boxes0 c d dias' mc1 next_tableau0 = function
  | Solution.Sat t0 ->
    (match tableau_jumps v { cpls = cpls0; boxes = boxes0; dias = dias' } mc1
             next_tableau0 with
     | JumpSolution.Sat t1s -> JumpSolution.Sat (app t1s (t0 :: []))
     | JumpSolution.Unsat (failed_dia, core, deriv) ->
       JumpSolution.Unsat (failed_dia, core, deriv))
  | Solution.Unsat (core, deriv) -> JumpSolution.Unsat ((c, d), core, deriv)

  (** val tableau_jumps_unfold_clause_2 :
      t -> CplClause.t list -> BoxClause.t list -> int -> bool -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      JumpSolution.t **)

  let tableau_jumps_unfold_clause_2 v cpls0 boxes0 c refine d dias' mc1 next_tableau0 =
    if refine
    then (match let fired_boxes =
                  apply
                    (apply boxes0
                      (filter (fun pat -> let (a, _) = pat in forces_atm v a)))
                    (map snd)
                in
                next_tableau0 (d :: fired_boxes) with
          | Solution.Sat t0 ->
            (match tableau_jumps v { cpls = cpls0; boxes = boxes0; dias =
                     dias' } mc1 next_tableau0 with
             | JumpSolution.Sat t1s -> JumpSolution.Sat (app t1s (t0 :: []))
             | JumpSolution.Unsat (failed_dia, core, deriv) ->
               JumpSolution.Unsat (failed_dia, core, deriv))
          | Solution.Unsat (core, deriv) ->
            JumpSolution.Unsat ((c, d), core, deriv))
    else tableau_jumps v { cpls = cpls0; boxes = boxes0; dias = dias' } mc1
           next_tableau0

  (** val tableau_jumps_unfold :
      t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      JumpSolution.t **)

  let tableau_jumps_unfold v l0 mc1 next_tableau0 =
    let { cpls = cpls0; boxes = boxes0; dias = dias0 } = l0 in
    (match dias0 with
     | [] -> JumpSolution.Sat []
     | t0 :: l ->
       let (n, t1) = t0 in
       if forces_atm v n
       then (match let fired_boxes =
                     apply
                       (apply boxes0
                         (filter (fun pat ->
                           let (a, _) = pat in forces_atm v a)))
                       (map snd)
                   in
                   next_tableau0 (t1 :: fired_boxes) with
             | Solution.Sat t2 ->
               (match tableau_jumps v { cpls = cpls0; boxes = boxes0; dias =
                        l } mc1 next_tableau0 with
                | JumpSolution.Sat t1s ->
                  JumpSolution.Sat (app t1s (t2 :: []))
                | JumpSolution.Unsat (failed_dia, core, deriv) ->
                  JumpSolution.Unsat (failed_dia, core, deriv))
             | Solution.Unsat (core, deriv) ->
               JumpSolution.Unsat ((n, t1), core, deriv))
       else tableau_jumps v { cpls = cpls0; boxes = boxes0; dias = l } mc1
              next_tableau0)

  type tableau_jumps_graph =
  | Coq_tableau_jumps_graph_equation_1 of t * CplClause.t list
     * BoxClause.t list * Mchain.t * (Assumptions.t -> Solution.t)
  | Coq_tableau_jumps_graph_refinement_2 of t * CplClause.t list
     * BoxClause.t list * int * Lit.t * DiaClause.t list * Mchain.t
     * (Assumptions.t -> Solution.t) * tableau_jumps_clause_2_graph
  and tableau_jumps_clause_2_graph =
  | Coq_tableau_jumps_clause_2_graph_refinement_1 of t * CplClause.t list
     * BoxClause.t list * int * Lit.t * DiaClause.t list * Mchain.t
     * (Assumptions.t -> Solution.t) * tableau_jumps_clause_2_clause_2_graph
  | Coq_tableau_jumps_clause_2_graph_equation_2 of t * CplClause.t list
     * BoxClause.t list * int * Lit.t * DiaClause.t list * Mchain.t
     * (Assumptions.t -> Solution.t) * tableau_jumps_graph
  and tableau_jumps_clause_2_clause_2_graph =
  | Coq_tableau_jumps_clause_2_clause_2_graph_refinement_1 of t
     * CplClause.t list * BoxClause.t list * int * Lit.t * DiaClause.t list
     * Mchain.t * (Assumptions.t -> Solution.t) * Tree.t
     * tableau_jumps_graph * tableau_jumps_clause_2_clause_2_clause_2_graph
  | Coq_tableau_jumps_clause_2_clause_2_graph_equation_2 of t
     * CplClause.t list * BoxClause.t list * int * Lit.t * DiaClause.t list
     * Mchain.t * (Assumptions.t -> Solution.t) * Assumptions.t * Derivation.t
  and tableau_jumps_clause_2_clause_2_clause_2_graph =
  | Coq_tableau_jumps_clause_2_clause_2_clause_2_graph_equation_1 of 
     t * CplClause.t list * BoxClause.t list * int * Lit.t * DiaClause.t list
     * Mchain.t * (Assumptions.t -> Solution.t) * Tree.t * Tree.t list
  | Coq_tableau_jumps_clause_2_clause_2_clause_2_graph_equation_2 of 
     t * CplClause.t list * BoxClause.t list * int * Lit.t * DiaClause.t list
     * Mchain.t * (Assumptions.t -> Solution.t) * Tree.t * DiaClause.t
     * Assumptions.t * Derivation.t

  (** val tableau_jumps_graph_mut :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> tableau_jumps_clause_2_graph -> 'a2 ->
      'a1) -> (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_clause_2_clause_2_graph -> 'a3 -> 'a2) -> (t ->
      CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
      list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_graph -> 'a1 -> 'a2) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> Tree.t -> tableau_jumps_graph -> 'a1
      -> tableau_jumps_clause_2_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (t
      -> CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
      list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Assumptions.t ->
      Derivation.t -> 'a3) -> (t -> CplClause.t list -> BoxClause.t list ->
      int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
      Solution.t) -> Tree.t -> Tree.t list -> 'a4) -> (t -> CplClause.t list
      -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> Tree.t -> DiaClause.t -> Assumptions.t
      -> Derivation.t -> 'a4) -> t -> Lclauses.t -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> JumpSolution.t -> tableau_jumps_graph
      -> 'a1 **)

  let tableau_jumps_graph_mut tableau_jumps_graph_equation_1 tableau_jumps_graph_refinement_2 tableau_jumps_clause_2_graph_refinement_1 tableau_jumps_clause_2_graph_equation_2 tableau_jumps_clause_2_clause_2_graph_refinement_1 tableau_jumps_clause_2_clause_2_graph_equation_2 tableau_jumps_clause_2_clause_2_clause_2_graph_equation_1 tableau_jumps_clause_2_clause_2_clause_2_graph_equation_2 =
    let rec f _ _ _ _ _ = function
    | Coq_tableau_jumps_graph_equation_1 (v0, cpls0, boxes0, mc2,
                                          next_tableau0) ->
      tableau_jumps_graph_equation_1 v0 cpls0 boxes0 mc2 next_tableau0
    | Coq_tableau_jumps_graph_refinement_2 (v0, cpls0, boxes0, c, d, dias',
                                            mc2, next_tableau0, hind) ->
      tableau_jumps_graph_refinement_2 v0 cpls0 boxes0 c d dias' mc2
        next_tableau0 hind
        (f0 v0 cpls0 boxes0 c (forces_atm v0 c) d dias' mc2 next_tableau0
          (if forces_atm v0 c
           then (match let fired_boxes =
                         apply
                           (apply boxes0
                             (filter (fun pat ->
                               let (a, _) = pat in forces_atm v0 a)))
                           (map snd)
                       in
                       next_tableau0 (d :: fired_boxes) with
                 | Solution.Sat t1 ->
                   (match tableau_jumps v0 { cpls = cpls0; boxes = boxes0;
                            dias = dias' } mc2 next_tableau0 with
                    | JumpSolution.Sat t1s ->
                      JumpSolution.Sat (app t1s (t1 :: []))
                    | JumpSolution.Unsat (failed_dia, core, deriv) ->
                      JumpSolution.Unsat (failed_dia, core, deriv))
                 | Solution.Unsat (core, deriv) ->
                   JumpSolution.Unsat ((c, d), core, deriv))
           else tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                  dias' } mc2 next_tableau0)
          hind)
    and f0 _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_graph_refinement_1 (v0, cpls0, boxes0, c0,
                                                     d0, dias'0, mc2,
                                                     next_tableau0, hind) ->
      tableau_jumps_clause_2_graph_refinement_1 v0 cpls0 boxes0 c0 d0 dias'0
        mc2 next_tableau0 hind
        (f1 v0 cpls0 boxes0 c0 d0 dias'0 mc2 next_tableau0
          (let fired_boxes =
             apply
               (apply boxes0
                 (filter (fun pat -> let (a, _) = pat in forces_atm v0 a)))
               (map snd)
           in
           next_tableau0 (d0 :: fired_boxes))
          (match let fired_boxes =
                   apply
                     (apply boxes0
                       (filter (fun pat ->
                         let (a, _) = pat in forces_atm v0 a)))
                     (map snd)
                 in
                 next_tableau0 (d0 :: fired_boxes) with
           | Solution.Sat t1 ->
             (match tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                      dias'0 } mc2 next_tableau0 with
              | JumpSolution.Sat t1s -> JumpSolution.Sat (app t1s (t1 :: []))
              | JumpSolution.Unsat (failed_dia, core, deriv) ->
                JumpSolution.Unsat (failed_dia, core, deriv))
           | Solution.Unsat (core, deriv) ->
             JumpSolution.Unsat ((c0, d0), core, deriv))
          hind)
    | Coq_tableau_jumps_clause_2_graph_equation_2 (v0, cpls0, boxes0, c0, d0,
                                                   dias'0, mc2,
                                                   next_tableau0, hind) ->
      tableau_jumps_clause_2_graph_equation_2 v0 cpls0 boxes0 c0 d0 dias'0
        mc2 next_tableau0 hind
        (f v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 } mc2
          next_tableau0
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 next_tableau0)
          hind)
    and f1 _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_clause_2_graph_refinement_1 (v0, cpls0,
                                                              boxes0, c0, d0,
                                                              dias'0, mc2,
                                                              next_tableau0,
                                                              t1, hind, hind0) ->
      tableau_jumps_clause_2_clause_2_graph_refinement_1 v0 cpls0 boxes0 c0
        d0 dias'0 mc2 next_tableau0 t1 hind
        (f v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 } mc2
          next_tableau0
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 next_tableau0)
          hind)
        hind0
        (f2 v0 cpls0 boxes0 c0 d0 dias'0 mc2 next_tableau0 t1
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 next_tableau0)
          (match tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                   dias'0 } mc2 next_tableau0 with
           | JumpSolution.Sat t1s -> JumpSolution.Sat (app t1s (t1 :: []))
           | JumpSolution.Unsat (failed_dia, core, deriv) ->
             JumpSolution.Unsat (failed_dia, core, deriv))
          hind0)
    | Coq_tableau_jumps_clause_2_clause_2_graph_equation_2 (v0, cpls0,
                                                            boxes0, c0, d0,
                                                            dias'0, mc2,
                                                            next_tableau0,
                                                            core, deriv) ->
      tableau_jumps_clause_2_clause_2_graph_equation_2 v0 cpls0 boxes0 c0 d0
        dias'0 mc2 next_tableau0 core deriv
    and f2 _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_clause_2_clause_2_graph_equation_1 (
        v0, cpls0, boxes0, c0, d0, dias'0, mc2, next_tableau0, t2, t1s) ->
      tableau_jumps_clause_2_clause_2_clause_2_graph_equation_1 v0 cpls0
        boxes0 c0 d0 dias'0 mc2 next_tableau0 t2 t1s
    | Coq_tableau_jumps_clause_2_clause_2_clause_2_graph_equation_2 (
        v0, cpls0, boxes0, c0, d0, dias'0, mc2, next_tableau0, t2,
        failed_dia, core, deriv) ->
      tableau_jumps_clause_2_clause_2_clause_2_graph_equation_2 v0 cpls0
        boxes0 c0 d0 dias'0 mc2 next_tableau0 t2 failed_dia core deriv
    in f

  (** val tableau_jumps_clause_2_graph_mut :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> tableau_jumps_clause_2_graph -> 'a2 ->
      'a1) -> (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_clause_2_clause_2_graph -> 'a3 -> 'a2) -> (t ->
      CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
      list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_graph -> 'a1 -> 'a2) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> Tree.t -> tableau_jumps_graph -> 'a1
      -> tableau_jumps_clause_2_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (t
      -> CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
      list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Assumptions.t ->
      Derivation.t -> 'a3) -> (t -> CplClause.t list -> BoxClause.t list ->
      int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
      Solution.t) -> Tree.t -> Tree.t list -> 'a4) -> (t -> CplClause.t list
      -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> Tree.t -> DiaClause.t -> Assumptions.t
      -> Derivation.t -> 'a4) -> t -> CplClause.t list -> BoxClause.t list ->
      int -> bool -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t
      -> Solution.t) -> JumpSolution.t -> tableau_jumps_clause_2_graph -> 'a2 **)

  let tableau_jumps_clause_2_graph_mut tableau_jumps_graph_equation_1 tableau_jumps_graph_refinement_2 tableau_jumps_clause_2_graph_refinement_1 tableau_jumps_clause_2_graph_equation_2 tableau_jumps_clause_2_clause_2_graph_refinement_1 tableau_jumps_clause_2_clause_2_graph_equation_2 tableau_jumps_clause_2_clause_2_clause_2_graph_equation_1 tableau_jumps_clause_2_clause_2_clause_2_graph_equation_2 =
    let rec f _ _ _ _ _ = function
    | Coq_tableau_jumps_graph_equation_1 (v0, cpls0, boxes0, mc2,
                                          next_tableau0) ->
      tableau_jumps_graph_equation_1 v0 cpls0 boxes0 mc2 next_tableau0
    | Coq_tableau_jumps_graph_refinement_2 (v0, cpls0, boxes0, c, d, dias',
                                            mc2, next_tableau0, hind) ->
      tableau_jumps_graph_refinement_2 v0 cpls0 boxes0 c d dias' mc2
        next_tableau0 hind
        (f0 v0 cpls0 boxes0 c (forces_atm v0 c) d dias' mc2 next_tableau0
          (if forces_atm v0 c
           then (match let fired_boxes =
                         apply
                           (apply boxes0
                             (filter (fun pat ->
                               let (a, _) = pat in forces_atm v0 a)))
                           (map snd)
                       in
                       next_tableau0 (d :: fired_boxes) with
                 | Solution.Sat t1 ->
                   (match tableau_jumps v0 { cpls = cpls0; boxes = boxes0;
                            dias = dias' } mc2 next_tableau0 with
                    | JumpSolution.Sat t1s ->
                      JumpSolution.Sat (app t1s (t1 :: []))
                    | JumpSolution.Unsat (failed_dia, core, deriv) ->
                      JumpSolution.Unsat (failed_dia, core, deriv))
                 | Solution.Unsat (core, deriv) ->
                   JumpSolution.Unsat ((c, d), core, deriv))
           else tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                  dias' } mc2 next_tableau0)
          hind)
    and f0 _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_graph_refinement_1 (v0, cpls0, boxes0, c0,
                                                     d0, dias'0, mc2,
                                                     next_tableau0, hind) ->
      tableau_jumps_clause_2_graph_refinement_1 v0 cpls0 boxes0 c0 d0 dias'0
        mc2 next_tableau0 hind
        (f1 v0 cpls0 boxes0 c0 d0 dias'0 mc2 next_tableau0
          (let fired_boxes =
             apply
               (apply boxes0
                 (filter (fun pat -> let (a, _) = pat in forces_atm v0 a)))
               (map snd)
           in
           next_tableau0 (d0 :: fired_boxes))
          (match let fired_boxes =
                   apply
                     (apply boxes0
                       (filter (fun pat ->
                         let (a, _) = pat in forces_atm v0 a)))
                     (map snd)
                 in
                 next_tableau0 (d0 :: fired_boxes) with
           | Solution.Sat t1 ->
             (match tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                      dias'0 } mc2 next_tableau0 with
              | JumpSolution.Sat t1s -> JumpSolution.Sat (app t1s (t1 :: []))
              | JumpSolution.Unsat (failed_dia, core, deriv) ->
                JumpSolution.Unsat (failed_dia, core, deriv))
           | Solution.Unsat (core, deriv) ->
             JumpSolution.Unsat ((c0, d0), core, deriv))
          hind)
    | Coq_tableau_jumps_clause_2_graph_equation_2 (v0, cpls0, boxes0, c0, d0,
                                                   dias'0, mc2,
                                                   next_tableau0, hind) ->
      tableau_jumps_clause_2_graph_equation_2 v0 cpls0 boxes0 c0 d0 dias'0
        mc2 next_tableau0 hind
        (f v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 } mc2
          next_tableau0
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 next_tableau0)
          hind)
    and f1 _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_clause_2_graph_refinement_1 (v0, cpls0,
                                                              boxes0, c0, d0,
                                                              dias'0, mc2,
                                                              next_tableau0,
                                                              t1, hind, hind0) ->
      tableau_jumps_clause_2_clause_2_graph_refinement_1 v0 cpls0 boxes0 c0
        d0 dias'0 mc2 next_tableau0 t1 hind
        (f v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 } mc2
          next_tableau0
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 next_tableau0)
          hind)
        hind0
        (f2 v0 cpls0 boxes0 c0 d0 dias'0 mc2 next_tableau0 t1
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 next_tableau0)
          (match tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                   dias'0 } mc2 next_tableau0 with
           | JumpSolution.Sat t1s -> JumpSolution.Sat (app t1s (t1 :: []))
           | JumpSolution.Unsat (failed_dia, core, deriv) ->
             JumpSolution.Unsat (failed_dia, core, deriv))
          hind0)
    | Coq_tableau_jumps_clause_2_clause_2_graph_equation_2 (v0, cpls0,
                                                            boxes0, c0, d0,
                                                            dias'0, mc2,
                                                            next_tableau0,
                                                            core, deriv) ->
      tableau_jumps_clause_2_clause_2_graph_equation_2 v0 cpls0 boxes0 c0 d0
        dias'0 mc2 next_tableau0 core deriv
    and f2 _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_clause_2_clause_2_graph_equation_1 (
        v0, cpls0, boxes0, c0, d0, dias'0, mc2, next_tableau0, t2, t1s) ->
      tableau_jumps_clause_2_clause_2_clause_2_graph_equation_1 v0 cpls0
        boxes0 c0 d0 dias'0 mc2 next_tableau0 t2 t1s
    | Coq_tableau_jumps_clause_2_clause_2_clause_2_graph_equation_2 (
        v0, cpls0, boxes0, c0, d0, dias'0, mc2, next_tableau0, t2,
        failed_dia, core, deriv) ->
      tableau_jumps_clause_2_clause_2_clause_2_graph_equation_2 v0 cpls0
        boxes0 c0 d0 dias'0 mc2 next_tableau0 t2 failed_dia core deriv
    in f0

  (** val tableau_jumps_clause_2_clause_2_graph_mut :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> tableau_jumps_clause_2_graph -> 'a2 ->
      'a1) -> (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_clause_2_clause_2_graph -> 'a3 -> 'a2) -> (t ->
      CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
      list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_graph -> 'a1 -> 'a2) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> Tree.t -> tableau_jumps_graph -> 'a1
      -> tableau_jumps_clause_2_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (t
      -> CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
      list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Assumptions.t ->
      Derivation.t -> 'a3) -> (t -> CplClause.t list -> BoxClause.t list ->
      int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
      Solution.t) -> Tree.t -> Tree.t list -> 'a4) -> (t -> CplClause.t list
      -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> Tree.t -> DiaClause.t -> Assumptions.t
      -> Derivation.t -> 'a4) -> t -> CplClause.t list -> BoxClause.t list ->
      int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
      Solution.t) -> Solution.t -> JumpSolution.t ->
      tableau_jumps_clause_2_clause_2_graph -> 'a3 **)

  let tableau_jumps_clause_2_clause_2_graph_mut tableau_jumps_graph_equation_1 tableau_jumps_graph_refinement_2 tableau_jumps_clause_2_graph_refinement_1 tableau_jumps_clause_2_graph_equation_2 tableau_jumps_clause_2_clause_2_graph_refinement_1 tableau_jumps_clause_2_clause_2_graph_equation_2 tableau_jumps_clause_2_clause_2_clause_2_graph_equation_1 tableau_jumps_clause_2_clause_2_clause_2_graph_equation_2 =
    let rec f _ _ _ _ _ = function
    | Coq_tableau_jumps_graph_equation_1 (v0, cpls0, boxes0, mc2,
                                          next_tableau0) ->
      tableau_jumps_graph_equation_1 v0 cpls0 boxes0 mc2 next_tableau0
    | Coq_tableau_jumps_graph_refinement_2 (v0, cpls0, boxes0, c, d, dias',
                                            mc2, next_tableau0, hind) ->
      tableau_jumps_graph_refinement_2 v0 cpls0 boxes0 c d dias' mc2
        next_tableau0 hind
        (f0 v0 cpls0 boxes0 c (forces_atm v0 c) d dias' mc2 next_tableau0
          (if forces_atm v0 c
           then (match let fired_boxes =
                         apply
                           (apply boxes0
                             (filter (fun pat ->
                               let (a, _) = pat in forces_atm v0 a)))
                           (map snd)
                       in
                       next_tableau0 (d :: fired_boxes) with
                 | Solution.Sat t1 ->
                   (match tableau_jumps v0 { cpls = cpls0; boxes = boxes0;
                            dias = dias' } mc2 next_tableau0 with
                    | JumpSolution.Sat t1s ->
                      JumpSolution.Sat (app t1s (t1 :: []))
                    | JumpSolution.Unsat (failed_dia, core, deriv) ->
                      JumpSolution.Unsat (failed_dia, core, deriv))
                 | Solution.Unsat (core, deriv) ->
                   JumpSolution.Unsat ((c, d), core, deriv))
           else tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                  dias' } mc2 next_tableau0)
          hind)
    and f0 _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_graph_refinement_1 (v0, cpls0, boxes0, c0,
                                                     d0, dias'0, mc2,
                                                     next_tableau0, hind) ->
      tableau_jumps_clause_2_graph_refinement_1 v0 cpls0 boxes0 c0 d0 dias'0
        mc2 next_tableau0 hind
        (f1 v0 cpls0 boxes0 c0 d0 dias'0 mc2 next_tableau0
          (let fired_boxes =
             apply
               (apply boxes0
                 (filter (fun pat -> let (a, _) = pat in forces_atm v0 a)))
               (map snd)
           in
           next_tableau0 (d0 :: fired_boxes))
          (match let fired_boxes =
                   apply
                     (apply boxes0
                       (filter (fun pat ->
                         let (a, _) = pat in forces_atm v0 a)))
                     (map snd)
                 in
                 next_tableau0 (d0 :: fired_boxes) with
           | Solution.Sat t1 ->
             (match tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                      dias'0 } mc2 next_tableau0 with
              | JumpSolution.Sat t1s -> JumpSolution.Sat (app t1s (t1 :: []))
              | JumpSolution.Unsat (failed_dia, core, deriv) ->
                JumpSolution.Unsat (failed_dia, core, deriv))
           | Solution.Unsat (core, deriv) ->
             JumpSolution.Unsat ((c0, d0), core, deriv))
          hind)
    | Coq_tableau_jumps_clause_2_graph_equation_2 (v0, cpls0, boxes0, c0, d0,
                                                   dias'0, mc2,
                                                   next_tableau0, hind) ->
      tableau_jumps_clause_2_graph_equation_2 v0 cpls0 boxes0 c0 d0 dias'0
        mc2 next_tableau0 hind
        (f v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 } mc2
          next_tableau0
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 next_tableau0)
          hind)
    and f1 _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_clause_2_graph_refinement_1 (v0, cpls0,
                                                              boxes0, c0, d0,
                                                              dias'0, mc2,
                                                              next_tableau0,
                                                              t1, hind, hind0) ->
      tableau_jumps_clause_2_clause_2_graph_refinement_1 v0 cpls0 boxes0 c0
        d0 dias'0 mc2 next_tableau0 t1 hind
        (f v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 } mc2
          next_tableau0
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 next_tableau0)
          hind)
        hind0
        (f2 v0 cpls0 boxes0 c0 d0 dias'0 mc2 next_tableau0 t1
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 next_tableau0)
          (match tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                   dias'0 } mc2 next_tableau0 with
           | JumpSolution.Sat t1s -> JumpSolution.Sat (app t1s (t1 :: []))
           | JumpSolution.Unsat (failed_dia, core, deriv) ->
             JumpSolution.Unsat (failed_dia, core, deriv))
          hind0)
    | Coq_tableau_jumps_clause_2_clause_2_graph_equation_2 (v0, cpls0,
                                                            boxes0, c0, d0,
                                                            dias'0, mc2,
                                                            next_tableau0,
                                                            core, deriv) ->
      tableau_jumps_clause_2_clause_2_graph_equation_2 v0 cpls0 boxes0 c0 d0
        dias'0 mc2 next_tableau0 core deriv
    and f2 _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_clause_2_clause_2_graph_equation_1 (
        v0, cpls0, boxes0, c0, d0, dias'0, mc2, next_tableau0, t2, t1s) ->
      tableau_jumps_clause_2_clause_2_clause_2_graph_equation_1 v0 cpls0
        boxes0 c0 d0 dias'0 mc2 next_tableau0 t2 t1s
    | Coq_tableau_jumps_clause_2_clause_2_clause_2_graph_equation_2 (
        v0, cpls0, boxes0, c0, d0, dias'0, mc2, next_tableau0, t2,
        failed_dia, core, deriv) ->
      tableau_jumps_clause_2_clause_2_clause_2_graph_equation_2 v0 cpls0
        boxes0 c0 d0 dias'0 mc2 next_tableau0 t2 failed_dia core deriv
    in f1

  (** val tableau_jumps_clause_2_clause_2_clause_2_graph_mut :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> tableau_jumps_clause_2_graph -> 'a2 ->
      'a1) -> (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_clause_2_clause_2_graph -> 'a3 -> 'a2) -> (t ->
      CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
      list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_graph -> 'a1 -> 'a2) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> Tree.t -> tableau_jumps_graph -> 'a1
      -> tableau_jumps_clause_2_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (t
      -> CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
      list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Assumptions.t ->
      Derivation.t -> 'a3) -> (t -> CplClause.t list -> BoxClause.t list ->
      int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
      Solution.t) -> Tree.t -> Tree.t list -> 'a4) -> (t -> CplClause.t list
      -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> Tree.t -> DiaClause.t -> Assumptions.t
      -> Derivation.t -> 'a4) -> t -> CplClause.t list -> BoxClause.t list ->
      int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
      Solution.t) -> Tree.t -> JumpSolution.t -> JumpSolution.t ->
      tableau_jumps_clause_2_clause_2_clause_2_graph -> 'a4 **)

  let tableau_jumps_clause_2_clause_2_clause_2_graph_mut _ _ _ _ _ _ tableau_jumps_clause_2_clause_2_clause_2_graph_equation_1 tableau_jumps_clause_2_clause_2_clause_2_graph_equation_2 _ _ _ _ _ _ _ _ _ _ _ = function
  | Coq_tableau_jumps_clause_2_clause_2_clause_2_graph_equation_1 (v0, cpls0,
                                                                   boxes0,
                                                                   c0, d0,
                                                                   dias'0,
                                                                   mc2,
                                                                   next_tableau0,
                                                                   t2, t1s) ->
    tableau_jumps_clause_2_clause_2_clause_2_graph_equation_1 v0 cpls0 boxes0
      c0 d0 dias'0 mc2 next_tableau0 t2 t1s
  | Coq_tableau_jumps_clause_2_clause_2_clause_2_graph_equation_2 (v0, cpls0,
                                                                   boxes0,
                                                                   c0, d0,
                                                                   dias'0,
                                                                   mc2,
                                                                   next_tableau0,
                                                                   t2,
                                                                   failed_dia,
                                                                   core, deriv) ->
    tableau_jumps_clause_2_clause_2_clause_2_graph_equation_2 v0 cpls0 boxes0
      c0 d0 dias'0 mc2 next_tableau0 t2 failed_dia core deriv

  (** val tableau_jumps_graph_rect :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> tableau_jumps_clause_2_graph -> 'a2 ->
      'a1) -> (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_clause_2_clause_2_graph -> 'a3 -> 'a2) -> (t ->
      CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
      list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_graph -> 'a1 -> 'a2) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> Tree.t -> tableau_jumps_graph -> 'a1
      -> tableau_jumps_clause_2_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (t
      -> CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
      list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Assumptions.t ->
      Derivation.t -> 'a3) -> (t -> CplClause.t list -> BoxClause.t list ->
      int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
      Solution.t) -> Tree.t -> Tree.t list -> 'a4) -> (t -> CplClause.t list
      -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> Tree.t -> DiaClause.t -> Assumptions.t
      -> Derivation.t -> 'a4) -> t -> Lclauses.t -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> JumpSolution.t -> tableau_jumps_graph
      -> 'a1 **)

  let tableau_jumps_graph_rect =
    tableau_jumps_graph_mut

  (** val tableau_jumps_graph_correct :
      t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_graph **)

  let tableau_jumps_graph_correct v l0 mc1 next_tableau0 =
    let rec fix_F x =
      let x1 = let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr1 in
      let x2 = let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2 in
      let x0 = fun a a0 a1 b -> let y = a,(a0,(a1,b)) in (fun _ -> fix_F y) in
      let { cpls = cpls0; boxes = boxes0; dias = dias0 } =
        let pr1,_ = let _,pr2 = x in pr2 in pr1
      in
      (match dias0 with
       | [] ->
         Coq_tableau_jumps_graph_equation_1 ((let pr1,_ = x in pr1), cpls0,
           boxes0, x1, x2)
       | t0 :: l ->
         let (n, t1) = t0 in
         Coq_tableau_jumps_graph_refinement_2 ((let pr1,_ = x in pr1), cpls0,
         boxes0, n, t1, l, x1, x2,
         (let refine = forces_atm (let pr1,_ = x in pr1) n in
          if refine
          then Coq_tableau_jumps_clause_2_graph_refinement_1
                 ((let pr1,_ = x in pr1), cpls0, boxes0, n, t1, l, x1, x2,
                 (let refine0 =
                    let fired_boxes =
                      apply
                        (apply boxes0
                          (filter (fun pat ->
                            let (a, _) = pat in
                            forces_atm (let pr1,_ = x in pr1) a)))
                        (map snd)
                    in
                    x2 (t1 :: fired_boxes)
                  in
                  match refine0 with
                  | Solution.Sat t2 ->
                    Coq_tableau_jumps_clause_2_clause_2_graph_refinement_1
                      ((let pr1,_ = x in pr1), cpls0, boxes0, n, t1, l, x1,
                      x2, t2,
                      (x0 (let pr1,_ = x in pr1) { cpls = cpls0; boxes =
                        boxes0; dias = l } x1 x2 __),
                      (let refine1 =
                         tableau_jumps (let pr1,_ = x in pr1) { cpls = cpls0;
                           boxes = boxes0; dias = l } x1 x2
                       in
                       match refine1 with
                       | JumpSolution.Sat t1s ->
                         Coq_tableau_jumps_clause_2_clause_2_clause_2_graph_equation_1
                           ((let pr1,_ = x in pr1), cpls0, boxes0, n, t1, l,
                           x1, x2, t2, t1s)
                       | JumpSolution.Unsat (failed_dia, core, deriv) ->
                         Coq_tableau_jumps_clause_2_clause_2_clause_2_graph_equation_2
                           ((let pr1,_ = x in pr1), cpls0, boxes0, n, t1, l,
                           x1, x2, t2, failed_dia, core, deriv)))
                  | Solution.Unsat (core, deriv) ->
                    Coq_tableau_jumps_clause_2_clause_2_graph_equation_2
                      ((let pr1,_ = x in pr1), cpls0, boxes0, n, t1, l, x1,
                      x2, core, deriv)))
          else Coq_tableau_jumps_clause_2_graph_equation_2
                 ((let pr1,_ = x in pr1), cpls0, boxes0, n, t1, l, x1, x2,
                 (x0 (let pr1,_ = x in pr1) { cpls = cpls0; boxes = boxes0;
                   dias = l } x1 x2 __)))))
    in fix_F (v,(l0,(mc1,next_tableau0)))

  (** val tableau_jumps_elim :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> 'a1 -> __ -> 'a1) -> (t -> CplClause.t
      list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list ->
      Mchain.t -> (Assumptions.t -> Solution.t) -> Assumptions.t ->
      Derivation.t -> __ -> __ -> 'a1) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> Tree.t -> Tree.t list -> __ -> 'a1 ->
      __ -> __ -> 'a1) -> (t -> CplClause.t list -> BoxClause.t list -> int
      -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
      Solution.t) -> Tree.t -> DiaClause.t -> Assumptions.t -> Derivation.t
      -> __ -> 'a1 -> __ -> __ -> 'a1) -> t -> Lclauses.t -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> 'a1 **)

  let tableau_jumps_elim tableau_jumps_graph_equation_1 tableau_jumps_clause_2_graph_equation_2 tableau_jumps_clause_2_clause_2_graph_equation_2 tableau_jumps_clause_2_clause_2_clause_2_graph_equation_1 tableau_jumps_clause_2_clause_2_clause_2_graph_equation_2 v l0 mc1 next_tableau0 =
    tableau_jumps_graph_mut tableau_jumps_graph_equation_1
      (fun _ _ _ _ _ _ _ _ _ x -> x __) (fun _ _ _ _ _ _ _ _ _ x -> x __)
      (fun v0 cpls0 boxes0 c d dias' mc0 next_tableau1 _ ->
      tableau_jumps_clause_2_graph_equation_2 v0 cpls0 boxes0 c d dias' mc0
        next_tableau1)
      (fun _ _ _ _ _ _ _ _ _ _ x _ x0 -> x0 __ x)
      tableau_jumps_clause_2_clause_2_graph_equation_2
      tableau_jumps_clause_2_clause_2_clause_2_graph_equation_1
      tableau_jumps_clause_2_clause_2_clause_2_graph_equation_2 v l0 mc1
      next_tableau0 (tableau_jumps v l0 mc1 next_tableau0)
      (tableau_jumps_graph_correct v l0 mc1 next_tableau0)

  (** val coq_FunctionalElimination_tableau_jumps :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> __) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> __ -> __ -> __) -> (t -> CplClause.t
      list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list ->
      Mchain.t -> (Assumptions.t -> Solution.t) -> Assumptions.t ->
      Derivation.t -> __ -> __ -> __) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> Tree.t -> Tree.t list -> __ -> __ ->
      __ -> __ -> __) -> (t -> CplClause.t list -> BoxClause.t list -> int ->
      Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t)
      -> Tree.t -> DiaClause.t -> Assumptions.t -> Derivation.t -> __ -> __
      -> __ -> __ -> __) -> t -> Lclauses.t -> Mchain.t -> (Assumptions.t ->
      Solution.t) -> __ **)

  let coq_FunctionalElimination_tableau_jumps =
    tableau_jumps_elim

  (** val coq_FunctionalInduction_tableau_jumps :
      (t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      JumpSolution.t) coq_FunctionalInduction **)

  let coq_FunctionalInduction_tableau_jumps =
    Obj.magic tableau_jumps_graph_correct

  (** val tableau_clause_1_clause_2_clause_2 :
      Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> CplSolver.t -> Mchain.t -> __ ->
      Solution.t) -> JumpSolution.t -> Solution.t **)

  let tableau_clause_1_clause_2_clause_2 a s0 v _ l0 mc1 tableau0 = function
  | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
  | JumpSolution.Unsat (failed_dia, core, deriv) ->
    let (n, t0) = failed_dia in
    let conflict_set = conflict_set_of (l0 :: mc1) v n core in
    let s0' = CplSolver.add_conflict_set s0 conflict_set in
    let mc0' = add_conflict_set (l0 :: mc1) conflict_set in
    (match tableau0 a s0' mc0' __ with
     | Solution.Sat t1 -> Solution.Sat t1
     | Solution.Unsat (rs_core, rs_deriv) ->
       Solution.Unsat (rs_core, (JumpRestart (v, (n, t0), deriv, rs_deriv))))

  (** val tableau_clause_1_clause_2 :
      Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t list ->
      (Assumptions.t -> CplSolver.t -> Mchain.t -> __ -> Solution.t) ->
      Solution.t **)

  let tableau_clause_1_clause_2 a s0 v _ refine tableau0 =
    match refine with
    | [] -> Solution.Sat (Coq_make (v, []))
    | t0 :: l ->
      (match inspect
               (tableau_jumps v t0 l (fun a' ->
                 tableau0 a' (make_with_clauses (first_cpls l)) l __)) with
       | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
       | JumpSolution.Unsat (failed_dia, core, deriv) ->
         let (n, t1) = failed_dia in
         let conflict_set = conflict_set_of (t0 :: l) v n core in
         let s0' = CplSolver.add_conflict_set s0 conflict_set in
         let mc0' = add_conflict_set (t0 :: l) conflict_set in
         (match tableau0 a s0' mc0' __ with
          | Solution.Sat t2 -> Solution.Sat t2
          | Solution.Unsat (rs_core, rs_deriv) ->
            Solution.Unsat (rs_core, (JumpRestart (v, (n, t1), deriv,
              rs_deriv)))))

  (** val tableau_clause_1 :
      Assumptions.t -> CplSolver.t -> CplSolution.t -> Mchain.t ->
      (Assumptions.t -> CplSolver.t -> Mchain.t -> __ -> Solution.t) ->
      Solution.t **)

  let tableau_clause_1 a s0 refine mc0 tableau0 =
    match refine with
    | Sat v ->
      (match mc0 with
       | [] -> Solution.Sat (Coq_make (v, []))
       | t0 :: l ->
         (match inspect
                  (tableau_jumps v t0 l (fun a' ->
                    tableau0 a' (make_with_clauses (first_cpls l)) l __)) with
          | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
          | JumpSolution.Unsat (failed_dia, core, deriv) ->
            let (n, t1) = failed_dia in
            let conflict_set = conflict_set_of (t0 :: l) v n core in
            let s0' = CplSolver.add_conflict_set s0 conflict_set in
            let mc0' = add_conflict_set (t0 :: l) conflict_set in
            (match tableau0 a s0' mc0' __ with
             | Solution.Sat t2 -> Solution.Sat t2
             | Solution.Unsat (rs_core, rs_deriv) ->
               Solution.Unsat (rs_core, (JumpRestart (v, (n, t1), deriv,
                 rs_deriv))))))
    | Unsat core -> Solution.Unsat (core, (Id core))

  (** val tableau_functional :
      Assumptions.t -> CplSolver.t -> Mchain.t -> (Assumptions.t ->
      CplSolver.t -> Mchain.t -> __ -> Solution.t) -> Solution.t **)

  let tableau_functional a s0 mc0 tableau0 =
    match inspect (solve_with_assumptions s0 a) with
    | Sat v ->
      (match mc0 with
       | [] -> Solution.Sat (Coq_make (v, []))
       | t0 :: l ->
         (match inspect
                  (tableau_jumps v t0 l (fun a' ->
                    tableau0 a' (make_with_clauses (first_cpls l)) l __)) with
          | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
          | JumpSolution.Unsat (failed_dia, core, deriv) ->
            let (n, t1) = failed_dia in
            let conflict_set = conflict_set_of (t0 :: l) v n core in
            let s0' = CplSolver.add_conflict_set s0 conflict_set in
            let mc0' = add_conflict_set (t0 :: l) conflict_set in
            (match tableau0 a s0' mc0' __ with
             | Solution.Sat t2 -> Solution.Sat t2
             | Solution.Unsat (rs_core, rs_deriv) ->
               Solution.Unsat (rs_core, (JumpRestart (v, (n, t1), deriv,
                 rs_deriv))))))
    | Unsat core -> Solution.Unsat (core, (Id core))

  (** val tableau : Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t **)

  let tableau a a0 b =
    let rec fix_F x =
      let a1 = let pr1,_ = x in pr1 in
      let s0 = let pr1,_ = let _,pr2 = x in pr2 in pr1 in
      let tableau0 = fun a2 a3 b0 -> let y = a2,(a3,b0) in (fun _ -> fix_F y)
      in
      (match inspect (solve_with_assumptions s0 a1) with
       | Sat v ->
         (match let _,pr2 = let _,pr2 = x in pr2 in pr2 with
          | [] -> Solution.Sat (Coq_make (v, []))
          | t0 :: l ->
            (match inspect
                     (tableau_jumps v t0 l (fun a' ->
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

  (** val tableau_unfold_clause_1_clause_2_clause_2 :
      Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> JumpSolution.t -> Solution.t **)

  let tableau_unfold_clause_1_clause_2_clause_2 a s0 v _ l0 mc1 = function
  | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
  | JumpSolution.Unsat (failed_dia, core, deriv) ->
    let (n, t0) = failed_dia in
    let conflict_set = conflict_set_of (l0 :: mc1) v n core in
    let s0' = CplSolver.add_conflict_set s0 conflict_set in
    let mc0' = add_conflict_set (l0 :: mc1) conflict_set in
    (match tableau a s0' mc0' with
     | Solution.Sat t1 -> Solution.Sat t1
     | Solution.Unsat (rs_core, rs_deriv) ->
       Solution.Unsat (rs_core, (JumpRestart (v, (n, t0), deriv, rs_deriv))))

  (** val tableau_unfold_clause_1_clause_2 :
      Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t list ->
      Solution.t **)

  let tableau_unfold_clause_1_clause_2 a s0 v _ = function
  | [] -> Solution.Sat (Coq_make (v, []))
  | t0 :: l ->
    (match inspect
             (tableau_jumps v t0 l (fun a' ->
               tableau a' (make_with_clauses (first_cpls l)) l)) with
     | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
     | JumpSolution.Unsat (failed_dia, core, deriv) ->
       let (n, t1) = failed_dia in
       let conflict_set = conflict_set_of (t0 :: l) v n core in
       let s0' = CplSolver.add_conflict_set s0 conflict_set in
       let mc0' = add_conflict_set (t0 :: l) conflict_set in
       (match tableau a s0' mc0' with
        | Solution.Sat t2 -> Solution.Sat t2
        | Solution.Unsat (rs_core, rs_deriv) ->
          Solution.Unsat (rs_core, (JumpRestart (v, (n, t1), deriv,
            rs_deriv)))))

  (** val tableau_unfold_clause_1 :
      Assumptions.t -> CplSolver.t -> CplSolution.t -> Mchain.t -> Solution.t **)

  let tableau_unfold_clause_1 a s0 refine mc0 =
    match refine with
    | Sat v ->
      (match mc0 with
       | [] -> Solution.Sat (Coq_make (v, []))
       | t0 :: l ->
         (match inspect
                  (tableau_jumps v t0 l (fun a' ->
                    tableau a' (make_with_clauses (first_cpls l)) l)) with
          | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
          | JumpSolution.Unsat (failed_dia, core, deriv) ->
            let (n, t1) = failed_dia in
            let conflict_set = conflict_set_of (t0 :: l) v n core in
            let s0' = CplSolver.add_conflict_set s0 conflict_set in
            let mc0' = add_conflict_set (t0 :: l) conflict_set in
            (match tableau a s0' mc0' with
             | Solution.Sat t2 -> Solution.Sat t2
             | Solution.Unsat (rs_core, rs_deriv) ->
               Solution.Unsat (rs_core, (JumpRestart (v, (n, t1), deriv,
                 rs_deriv))))))
    | Unsat core -> Solution.Unsat (core, (Id core))

  (** val tableau_unfold :
      Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t **)

  let tableau_unfold a s0 mc0 =
    match inspect (solve_with_assumptions s0 a) with
    | Sat v ->
      (match mc0 with
       | [] -> Solution.Sat (Coq_make (v, []))
       | t0 :: l ->
         (match inspect
                  (tableau_jumps v t0 l (fun a' ->
                    tableau a' (make_with_clauses (first_cpls l)) l)) with
          | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
          | JumpSolution.Unsat (failed_dia, core, deriv) ->
            let (n, t1) = failed_dia in
            let conflict_set = conflict_set_of (t0 :: l) v n core in
            let s0' = CplSolver.add_conflict_set s0 conflict_set in
            let mc0' = add_conflict_set (t0 :: l) conflict_set in
            (match tableau a s0' mc0' with
             | Solution.Sat t2 -> Solution.Sat t2
             | Solution.Unsat (rs_core, rs_deriv) ->
               Solution.Unsat (rs_core, (JumpRestart (v, (n, t1), deriv,
                 rs_deriv))))))
    | Unsat core -> Solution.Unsat (core, (Id core))

  type tableau_graph =
  | Coq_tableau_graph_refinement_1 of Assumptions.t * CplSolver.t * Mchain.t
     * tableau_clause_1_graph
  and tableau_clause_1_graph =
  | Coq_tableau_clause_1_graph_refinement_1 of Assumptions.t * CplSolver.t
     * t * Mchain.t * tableau_clause_1_clause_2_graph
  | Coq_tableau_clause_1_graph_equation_2 of Assumptions.t * CplSolver.t
     * Assumptions.t * Mchain.t
  and tableau_clause_1_clause_2_graph =
  | Coq_tableau_clause_1_clause_2_graph_equation_1 of Assumptions.t
     * CplSolver.t * t * Mchain.t
  | Coq_tableau_clause_1_clause_2_graph_refinement_2 of Assumptions.t
     * CplSolver.t * t * Mchain.t * Lclauses.t * Lclauses.t list
     * (Assumptions.t -> tableau_graph)
     * tableau_clause_1_clause_2_clause_2_graph
  and tableau_clause_1_clause_2_clause_2_graph =
  | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1 of Assumptions.t
     * CplSolver.t * t * Mchain.t * Lclauses.t * Lclauses.t list * Tree.t list
  | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2 of Assumptions.t
     * CplSolver.t * t * Mchain.t * Lclauses.t * Lclauses.t list * int
     * Lit.t * Assumptions.t * Derivation.t * tableau_graph

  (** val tableau_graph_mut :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
      'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
      CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> tableau_graph) -> (Assumptions.t
      -> 'a1) -> tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> Tree.t list -> __ -> 'a4) -> (Assumptions.t ->
      CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
      int -> Lit.t -> Assumptions.t -> Derivation.t -> __ -> tableau_graph ->
      'a1 -> 'a4) -> Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t
      -> tableau_graph -> 'a1 **)

  let tableau_graph_mut tableau_graph_refinement_1 tableau_clause_1_graph_refinement_1 tableau_clause_1_graph_equation_2 tableau_clause_1_clause_2_graph_equation_1 tableau_clause_1_clause_2_graph_refinement_2 tableau_clause_1_clause_2_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_2 =
    let rec f _ _ _ _ = function
    | Coq_tableau_graph_refinement_1 (a0, s1, mc1, hind) ->
      tableau_graph_refinement_1 a0 s1 mc1 hind
        (f0 a0 s1 (inspect (solve_with_assumptions s1 a0)) mc1
          (match inspect (solve_with_assumptions s1 a0) with
           | Sat v ->
             (match mc1 with
              | [] -> Solution.Sat (Coq_make (v, []))
              | t1 :: l ->
                (match inspect
                         (tableau_jumps v t1 l (fun a' ->
                           tableau a' (make_with_clauses (first_cpls l)) l)) with
                 | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
                 | JumpSolution.Unsat (failed_dia, core, deriv) ->
                   let (n, t2) = failed_dia in
                   let conflict_set = conflict_set_of (t1 :: l) v n core in
                   let s0' = CplSolver.add_conflict_set s1 conflict_set in
                   let mc0' = add_conflict_set (t1 :: l) conflict_set in
                   (match tableau a0 s0' mc0' with
                    | Solution.Sat t3 -> Solution.Sat t3
                    | Solution.Unsat (rs_core, rs_deriv) ->
                      Solution.Unsat (rs_core, (JumpRestart (v, (n, t2),
                        deriv, rs_deriv))))))
           | Unsat core -> Solution.Unsat (core, (Id core)))
          hind)
    and f0 _ _ _ _ _ = function
    | Coq_tableau_clause_1_graph_refinement_1 (a0, s1, v, mc1, hind) ->
      tableau_clause_1_graph_refinement_1 a0 s1 v __ mc1 hind
        (f1 a0 s1 v __ mc1 mc1
          (match mc1 with
           | [] -> Solution.Sat (Coq_make (v, []))
           | t1 :: l ->
             (match inspect
                      (tableau_jumps v t1 l (fun a' ->
                        tableau a' (make_with_clauses (first_cpls l)) l)) with
              | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
              | JumpSolution.Unsat (failed_dia, core, deriv) ->
                let (n, t2) = failed_dia in
                let conflict_set = conflict_set_of (t1 :: l) v n core in
                let s0' = CplSolver.add_conflict_set s1 conflict_set in
                let mc0' = add_conflict_set (t1 :: l) conflict_set in
                (match tableau a0 s0' mc0' with
                 | Solution.Sat t3 -> Solution.Sat t3
                 | Solution.Unsat (rs_core, rs_deriv) ->
                   Solution.Unsat (rs_core, (JumpRestart (v, (n, t2), deriv,
                     rs_deriv))))))
          hind)
    | Coq_tableau_clause_1_graph_equation_2 (a0, s1, a', mc1) ->
      tableau_clause_1_graph_equation_2 a0 s1 a' __ mc1
    and f1 _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_graph_equation_1 (a0, s1, v0, mc1) ->
      tableau_clause_1_clause_2_graph_equation_1 a0 s1 v0 __ mc1
    | Coq_tableau_clause_1_clause_2_graph_refinement_2 (a0, s1, v0, mc1, l0,
                                                        mc2, hind, hind0) ->
      tableau_clause_1_clause_2_graph_refinement_2 a0 s1 v0 __ mc1 l0 mc2
        hind (fun a' ->
        f a' (make_with_clauses (first_cpls mc2)) mc2
          (tableau a' (make_with_clauses (first_cpls mc2)) mc2) (hind a'))
        hind0
        (f2 a0 s1 v0 __ mc1 l0 mc2
          (inspect
            (tableau_jumps v0 l0 mc2 (fun a' ->
              tableau a' (make_with_clauses (first_cpls mc2)) mc2)))
          (match inspect
                   (tableau_jumps v0 l0 mc2 (fun a' ->
                     tableau a' (make_with_clauses (first_cpls mc2)) mc2)) with
           | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v0, t1s))
           | JumpSolution.Unsat (failed_dia, core, deriv) ->
             let (n, t1) = failed_dia in
             let conflict_set = conflict_set_of (l0 :: mc2) v0 n core in
             let s0' = CplSolver.add_conflict_set s1 conflict_set in
             let mc0' = add_conflict_set (l0 :: mc2) conflict_set in
             (match tableau a0 s0' mc0' with
              | Solution.Sat t2 -> Solution.Sat t2
              | Solution.Unsat (rs_core, rs_deriv) ->
                Solution.Unsat (rs_core, (JumpRestart (v0, (n, t1), deriv,
                  rs_deriv)))))
          hind0)
    and f2 _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               t1s) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_1 a0 s1 v0 __ mc2 l1
        mc3 t1s __
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               c, d,
                                                               jump_core,
                                                               jump_deriv,
                                                               hind) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_2 a0 s1 v0 __ mc2 l1
        mc3 c d jump_core jump_deriv __ hind
        (let conflict_set = conflict_set_of (l1 :: mc3) v0 c jump_core in
         let s0' = CplSolver.add_conflict_set s1 conflict_set in
         let mc0' = add_conflict_set (l1 :: mc3) conflict_set in
         f a0 s0' mc0' (tableau a0 s0' mc0') hind)
    in f

  (** val tableau_clause_1_graph_mut :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
      'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
      CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> tableau_graph) -> (Assumptions.t
      -> 'a1) -> tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> Tree.t list -> __ -> 'a4) -> (Assumptions.t ->
      CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
      int -> Lit.t -> Assumptions.t -> Derivation.t -> __ -> tableau_graph ->
      'a1 -> 'a4) -> Assumptions.t -> CplSolver.t -> CplSolution.t ->
      Mchain.t -> Solution.t -> tableau_clause_1_graph -> 'a2 **)

  let tableau_clause_1_graph_mut tableau_graph_refinement_1 tableau_clause_1_graph_refinement_1 tableau_clause_1_graph_equation_2 tableau_clause_1_clause_2_graph_equation_1 tableau_clause_1_clause_2_graph_refinement_2 tableau_clause_1_clause_2_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_2 =
    let rec f _ _ _ _ = function
    | Coq_tableau_graph_refinement_1 (a0, s1, mc1, hind) ->
      tableau_graph_refinement_1 a0 s1 mc1 hind
        (f0 a0 s1 (inspect (solve_with_assumptions s1 a0)) mc1
          (match inspect (solve_with_assumptions s1 a0) with
           | Sat v ->
             (match mc1 with
              | [] -> Solution.Sat (Coq_make (v, []))
              | t1 :: l ->
                (match inspect
                         (tableau_jumps v t1 l (fun a' ->
                           tableau a' (make_with_clauses (first_cpls l)) l)) with
                 | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
                 | JumpSolution.Unsat (failed_dia, core, deriv) ->
                   let (n, t2) = failed_dia in
                   let conflict_set = conflict_set_of (t1 :: l) v n core in
                   let s0' = CplSolver.add_conflict_set s1 conflict_set in
                   let mc0' = add_conflict_set (t1 :: l) conflict_set in
                   (match tableau a0 s0' mc0' with
                    | Solution.Sat t3 -> Solution.Sat t3
                    | Solution.Unsat (rs_core, rs_deriv) ->
                      Solution.Unsat (rs_core, (JumpRestart (v, (n, t2),
                        deriv, rs_deriv))))))
           | Unsat core -> Solution.Unsat (core, (Id core)))
          hind)
    and f0 _ _ _ _ _ = function
    | Coq_tableau_clause_1_graph_refinement_1 (a0, s1, v, mc1, hind) ->
      tableau_clause_1_graph_refinement_1 a0 s1 v __ mc1 hind
        (f1 a0 s1 v __ mc1 mc1
          (match mc1 with
           | [] -> Solution.Sat (Coq_make (v, []))
           | t1 :: l ->
             (match inspect
                      (tableau_jumps v t1 l (fun a' ->
                        tableau a' (make_with_clauses (first_cpls l)) l)) with
              | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
              | JumpSolution.Unsat (failed_dia, core, deriv) ->
                let (n, t2) = failed_dia in
                let conflict_set = conflict_set_of (t1 :: l) v n core in
                let s0' = CplSolver.add_conflict_set s1 conflict_set in
                let mc0' = add_conflict_set (t1 :: l) conflict_set in
                (match tableau a0 s0' mc0' with
                 | Solution.Sat t3 -> Solution.Sat t3
                 | Solution.Unsat (rs_core, rs_deriv) ->
                   Solution.Unsat (rs_core, (JumpRestart (v, (n, t2), deriv,
                     rs_deriv))))))
          hind)
    | Coq_tableau_clause_1_graph_equation_2 (a0, s1, a', mc1) ->
      tableau_clause_1_graph_equation_2 a0 s1 a' __ mc1
    and f1 _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_graph_equation_1 (a0, s1, v0, mc1) ->
      tableau_clause_1_clause_2_graph_equation_1 a0 s1 v0 __ mc1
    | Coq_tableau_clause_1_clause_2_graph_refinement_2 (a0, s1, v0, mc1, l0,
                                                        mc2, hind, hind0) ->
      tableau_clause_1_clause_2_graph_refinement_2 a0 s1 v0 __ mc1 l0 mc2
        hind (fun a' ->
        f a' (make_with_clauses (first_cpls mc2)) mc2
          (tableau a' (make_with_clauses (first_cpls mc2)) mc2) (hind a'))
        hind0
        (f2 a0 s1 v0 __ mc1 l0 mc2
          (inspect
            (tableau_jumps v0 l0 mc2 (fun a' ->
              tableau a' (make_with_clauses (first_cpls mc2)) mc2)))
          (match inspect
                   (tableau_jumps v0 l0 mc2 (fun a' ->
                     tableau a' (make_with_clauses (first_cpls mc2)) mc2)) with
           | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v0, t1s))
           | JumpSolution.Unsat (failed_dia, core, deriv) ->
             let (n, t1) = failed_dia in
             let conflict_set = conflict_set_of (l0 :: mc2) v0 n core in
             let s0' = CplSolver.add_conflict_set s1 conflict_set in
             let mc0' = add_conflict_set (l0 :: mc2) conflict_set in
             (match tableau a0 s0' mc0' with
              | Solution.Sat t2 -> Solution.Sat t2
              | Solution.Unsat (rs_core, rs_deriv) ->
                Solution.Unsat (rs_core, (JumpRestart (v0, (n, t1), deriv,
                  rs_deriv)))))
          hind0)
    and f2 _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               t1s) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_1 a0 s1 v0 __ mc2 l1
        mc3 t1s __
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               c, d,
                                                               jump_core,
                                                               jump_deriv,
                                                               hind) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_2 a0 s1 v0 __ mc2 l1
        mc3 c d jump_core jump_deriv __ hind
        (let conflict_set = conflict_set_of (l1 :: mc3) v0 c jump_core in
         let s0' = CplSolver.add_conflict_set s1 conflict_set in
         let mc0' = add_conflict_set (l1 :: mc3) conflict_set in
         f a0 s0' mc0' (tableau a0 s0' mc0') hind)
    in f0

  (** val tableau_clause_1_clause_2_graph_mut :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
      'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
      CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> tableau_graph) -> (Assumptions.t
      -> 'a1) -> tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> Tree.t list -> __ -> 'a4) -> (Assumptions.t ->
      CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
      int -> Lit.t -> Assumptions.t -> Derivation.t -> __ -> tableau_graph ->
      'a1 -> 'a4) -> Assumptions.t -> CplSolver.t -> t -> Mchain.t ->
      Mchain.t -> Solution.t -> tableau_clause_1_clause_2_graph -> 'a3 **)

  let tableau_clause_1_clause_2_graph_mut tableau_graph_refinement_1 tableau_clause_1_graph_refinement_1 tableau_clause_1_graph_equation_2 tableau_clause_1_clause_2_graph_equation_1 tableau_clause_1_clause_2_graph_refinement_2 tableau_clause_1_clause_2_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_2 a s0 v mc0 refine t0 t1 =
    let rec f _ _ _ _ = function
    | Coq_tableau_graph_refinement_1 (a0, s1, mc1, hind) ->
      tableau_graph_refinement_1 a0 s1 mc1 hind
        (f0 a0 s1 (inspect (solve_with_assumptions s1 a0)) mc1
          (match inspect (solve_with_assumptions s1 a0) with
           | Sat v0 ->
             (match mc1 with
              | [] -> Solution.Sat (Coq_make (v0, []))
              | t3 :: l ->
                (match inspect
                         (tableau_jumps v0 t3 l (fun a' ->
                           tableau a' (make_with_clauses (first_cpls l)) l)) with
                 | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v0, t1s))
                 | JumpSolution.Unsat (failed_dia, core, deriv) ->
                   let (n, t4) = failed_dia in
                   let conflict_set = conflict_set_of (t3 :: l) v0 n core in
                   let s0' = CplSolver.add_conflict_set s1 conflict_set in
                   let mc0' = add_conflict_set (t3 :: l) conflict_set in
                   (match tableau a0 s0' mc0' with
                    | Solution.Sat t5 -> Solution.Sat t5
                    | Solution.Unsat (rs_core, rs_deriv) ->
                      Solution.Unsat (rs_core, (JumpRestart (v0, (n, t4),
                        deriv, rs_deriv))))))
           | Unsat core -> Solution.Unsat (core, (Id core)))
          hind)
    and f0 _ _ _ _ _ = function
    | Coq_tableau_clause_1_graph_refinement_1 (a0, s1, v0, mc1, hind) ->
      tableau_clause_1_graph_refinement_1 a0 s1 v0 __ mc1 hind
        (f1 a0 s1 v0 mc1 mc1
          (match mc1 with
           | [] -> Solution.Sat (Coq_make (v0, []))
           | t3 :: l ->
             (match inspect
                      (tableau_jumps v0 t3 l (fun a' ->
                        tableau a' (make_with_clauses (first_cpls l)) l)) with
              | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v0, t1s))
              | JumpSolution.Unsat (failed_dia, core, deriv) ->
                let (n, t4) = failed_dia in
                let conflict_set = conflict_set_of (t3 :: l) v0 n core in
                let s0' = CplSolver.add_conflict_set s1 conflict_set in
                let mc0' = add_conflict_set (t3 :: l) conflict_set in
                (match tableau a0 s0' mc0' with
                 | Solution.Sat t5 -> Solution.Sat t5
                 | Solution.Unsat (rs_core, rs_deriv) ->
                   Solution.Unsat (rs_core, (JumpRestart (v0, (n, t4), deriv,
                     rs_deriv))))))
          hind)
    | Coq_tableau_clause_1_graph_equation_2 (a0, s1, a', mc1) ->
      tableau_clause_1_graph_equation_2 a0 s1 a' __ mc1
    and f1 _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_graph_equation_1 (a0, s1, v0, mc1) ->
      tableau_clause_1_clause_2_graph_equation_1 a0 s1 v0 __ mc1
    | Coq_tableau_clause_1_clause_2_graph_refinement_2 (a0, s1, v0, mc1, l0,
                                                        mc2, hind, hind0) ->
      tableau_clause_1_clause_2_graph_refinement_2 a0 s1 v0 __ mc1 l0 mc2
        hind (fun a' ->
        f a' (make_with_clauses (first_cpls mc2)) mc2
          (tableau a' (make_with_clauses (first_cpls mc2)) mc2) (hind a'))
        hind0
        (f2 a0 s1 v0 __ mc1 l0 mc2
          (inspect
            (tableau_jumps v0 l0 mc2 (fun a' ->
              tableau a' (make_with_clauses (first_cpls mc2)) mc2)))
          (match inspect
                   (tableau_jumps v0 l0 mc2 (fun a' ->
                     tableau a' (make_with_clauses (first_cpls mc2)) mc2)) with
           | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v0, t1s))
           | JumpSolution.Unsat (failed_dia, core, deriv) ->
             let (n, t3) = failed_dia in
             let conflict_set = conflict_set_of (l0 :: mc2) v0 n core in
             let s0' = CplSolver.add_conflict_set s1 conflict_set in
             let mc0' = add_conflict_set (l0 :: mc2) conflict_set in
             (match tableau a0 s0' mc0' with
              | Solution.Sat t4 -> Solution.Sat t4
              | Solution.Unsat (rs_core, rs_deriv) ->
                Solution.Unsat (rs_core, (JumpRestart (v0, (n, t3), deriv,
                  rs_deriv)))))
          hind0)
    and f2 _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               t1s) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_1 a0 s1 v0 __ mc2 l1
        mc3 t1s __
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               c, d,
                                                               jump_core,
                                                               jump_deriv,
                                                               hind) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_2 a0 s1 v0 __ mc2 l1
        mc3 c d jump_core jump_deriv __ hind
        (let conflict_set = conflict_set_of (l1 :: mc3) v0 c jump_core in
         let s0' = CplSolver.add_conflict_set s1 conflict_set in
         let mc0' = add_conflict_set (l1 :: mc3) conflict_set in
         f a0 s0' mc0' (tableau a0 s0' mc0') hind)
    in f1 a s0 v mc0 refine t0 t1

  (** val tableau_clause_1_clause_2_clause_2_graph_mut :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
      'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
      CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> tableau_graph) -> (Assumptions.t
      -> 'a1) -> tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> Tree.t list -> __ -> 'a4) -> (Assumptions.t ->
      CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
      int -> Lit.t -> Assumptions.t -> Derivation.t -> __ -> tableau_graph ->
      'a1 -> 'a4) -> Assumptions.t -> CplSolver.t -> t -> Mchain.t ->
      Lclauses.t -> Lclauses.t list -> JumpSolution.t -> Solution.t ->
      tableau_clause_1_clause_2_clause_2_graph -> 'a4 **)

  let tableau_clause_1_clause_2_clause_2_graph_mut tableau_graph_refinement_1 tableau_clause_1_graph_refinement_1 tableau_clause_1_graph_equation_2 tableau_clause_1_clause_2_graph_equation_1 tableau_clause_1_clause_2_graph_refinement_2 tableau_clause_1_clause_2_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_2 a s0 v mc0 l0 mc1 refine t0 t1 =
    let rec f _ _ _ _ = function
    | Coq_tableau_graph_refinement_1 (a0, s1, mc2, hind) ->
      tableau_graph_refinement_1 a0 s1 mc2 hind
        (f0 a0 s1 (inspect (solve_with_assumptions s1 a0)) mc2
          (match inspect (solve_with_assumptions s1 a0) with
           | Sat v0 ->
             (match mc2 with
              | [] -> Solution.Sat (Coq_make (v0, []))
              | t3 :: l ->
                (match inspect
                         (tableau_jumps v0 t3 l (fun a' ->
                           tableau a' (make_with_clauses (first_cpls l)) l)) with
                 | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v0, t1s))
                 | JumpSolution.Unsat (failed_dia, core, deriv) ->
                   let (n, t4) = failed_dia in
                   let conflict_set = conflict_set_of (t3 :: l) v0 n core in
                   let s0' = CplSolver.add_conflict_set s1 conflict_set in
                   let mc0' = add_conflict_set (t3 :: l) conflict_set in
                   (match tableau a0 s0' mc0' with
                    | Solution.Sat t5 -> Solution.Sat t5
                    | Solution.Unsat (rs_core, rs_deriv) ->
                      Solution.Unsat (rs_core, (JumpRestart (v0, (n, t4),
                        deriv, rs_deriv))))))
           | Unsat core -> Solution.Unsat (core, (Id core)))
          hind)
    and f0 _ _ _ _ _ = function
    | Coq_tableau_clause_1_graph_refinement_1 (a0, s1, v0, mc2, hind) ->
      tableau_clause_1_graph_refinement_1 a0 s1 v0 __ mc2 hind
        (f1 a0 s1 v0 __ mc2 mc2
          (match mc2 with
           | [] -> Solution.Sat (Coq_make (v0, []))
           | t3 :: l ->
             (match inspect
                      (tableau_jumps v0 t3 l (fun a' ->
                        tableau a' (make_with_clauses (first_cpls l)) l)) with
              | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v0, t1s))
              | JumpSolution.Unsat (failed_dia, core, deriv) ->
                let (n, t4) = failed_dia in
                let conflict_set = conflict_set_of (t3 :: l) v0 n core in
                let s0' = CplSolver.add_conflict_set s1 conflict_set in
                let mc0' = add_conflict_set (t3 :: l) conflict_set in
                (match tableau a0 s0' mc0' with
                 | Solution.Sat t5 -> Solution.Sat t5
                 | Solution.Unsat (rs_core, rs_deriv) ->
                   Solution.Unsat (rs_core, (JumpRestart (v0, (n, t4), deriv,
                     rs_deriv))))))
          hind)
    | Coq_tableau_clause_1_graph_equation_2 (a0, s1, a', mc2) ->
      tableau_clause_1_graph_equation_2 a0 s1 a' __ mc2
    and f1 _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_graph_equation_1 (a0, s1, v0, mc2) ->
      tableau_clause_1_clause_2_graph_equation_1 a0 s1 v0 __ mc2
    | Coq_tableau_clause_1_clause_2_graph_refinement_2 (a0, s1, v0, mc2, l1,
                                                        mc3, hind, hind0) ->
      tableau_clause_1_clause_2_graph_refinement_2 a0 s1 v0 __ mc2 l1 mc3
        hind (fun a' ->
        f a' (make_with_clauses (first_cpls mc3)) mc3
          (tableau a' (make_with_clauses (first_cpls mc3)) mc3) (hind a'))
        hind0
        (f2 a0 s1 v0 mc2 l1 mc3
          (inspect
            (tableau_jumps v0 l1 mc3 (fun a' ->
              tableau a' (make_with_clauses (first_cpls mc3)) mc3)))
          (match inspect
                   (tableau_jumps v0 l1 mc3 (fun a' ->
                     tableau a' (make_with_clauses (first_cpls mc3)) mc3)) with
           | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v0, t1s))
           | JumpSolution.Unsat (failed_dia, core, deriv) ->
             let (n, t3) = failed_dia in
             let conflict_set = conflict_set_of (l1 :: mc3) v0 n core in
             let s0' = CplSolver.add_conflict_set s1 conflict_set in
             let mc0' = add_conflict_set (l1 :: mc3) conflict_set in
             (match tableau a0 s0' mc0' with
              | Solution.Sat t4 -> Solution.Sat t4
              | Solution.Unsat (rs_core, rs_deriv) ->
                Solution.Unsat (rs_core, (JumpRestart (v0, (n, t3), deriv,
                  rs_deriv)))))
          hind0)
    and f2 _ _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               t1s) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_1 a0 s1 v0 __ mc2 l1
        mc3 t1s __
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               c, d,
                                                               jump_core,
                                                               jump_deriv,
                                                               hind) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_2 a0 s1 v0 __ mc2 l1
        mc3 c d jump_core jump_deriv __ hind
        (let conflict_set = conflict_set_of (l1 :: mc3) v0 c jump_core in
         let s0' = CplSolver.add_conflict_set s1 conflict_set in
         let mc0' = add_conflict_set (l1 :: mc3) conflict_set in
         f a0 s0' mc0' (tableau a0 s0' mc0') hind)
    in f2 a s0 v mc0 l0 mc1 refine t0 t1

  (** val tableau_graph_rect :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
      'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
      CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> tableau_graph) -> (Assumptions.t
      -> 'a1) -> tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> Tree.t list -> __ -> 'a4) -> (Assumptions.t ->
      CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
      int -> Lit.t -> Assumptions.t -> Derivation.t -> __ -> tableau_graph ->
      'a1 -> 'a4) -> Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t
      -> tableau_graph -> 'a1 **)

  let tableau_graph_rect =
    tableau_graph_mut

  (** val tableau_graph_correct :
      Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_graph **)

  let tableau_graph_correct a s0 mc0 =
    let rec fix_F x =
      Coq_tableau_graph_refinement_1 ((let pr1,_ = x in pr1),
        (let pr1,_ = let _,pr2 = x in pr2 in pr1),
        (let _,pr2 = let _,pr2 = x in pr2 in pr2),
        (let refine =
           inspect
             (solve_with_assumptions
               (let pr1,_ = let _,pr2 = x in pr2 in pr1)
               (let pr1,_ = x in pr1))
         in
         match refine with
         | Sat v ->
           Coq_tableau_clause_1_graph_refinement_1 ((let pr1,_ = x in pr1),
             (let pr1,_ = let _,pr2 = x in pr2 in pr1), v,
             (let _,pr2 = let _,pr2 = x in pr2 in pr2),
             (let refine0 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in
              let x0 = fun a0 a1 b -> let y = a0,(a1,b) in (fun _ -> fix_F y)
              in
              (match refine0 with
               | [] ->
                 Coq_tableau_clause_1_clause_2_graph_equation_1
                   ((let pr1,_ = x in pr1),
                   (let pr1,_ = let _,pr2 = x in pr2 in pr1), v,
                   (let _,pr2 = let _,pr2 = x in pr2 in pr2))
               | t0 :: l ->
                 Coq_tableau_clause_1_clause_2_graph_refinement_2
                   ((let pr1,_ = x in pr1),
                   (let pr1,_ = let _,pr2 = x in pr2 in pr1), v,
                   (let _,pr2 = let _,pr2 = x in pr2 in pr2), t0, l,
                   (fun a' -> x0 a' (make_with_clauses (first_cpls l)) l __),
                   (let refine1 =
                      inspect
                        (tableau_jumps v t0 l (fun a' ->
                          tableau a' (make_with_clauses (first_cpls l)) l))
                    in
                    match refine1 with
                    | JumpSolution.Sat t1s ->
                      Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1
                        ((let pr1,_ = x in pr1),
                        (let pr1,_ = let _,pr2 = x in pr2 in pr1), v,
                        (let _,pr2 = let _,pr2 = x in pr2 in pr2), t0, l, t1s)
                    | JumpSolution.Unsat (failed_dia, core, deriv) ->
                      let (n, t1) = failed_dia in
                      Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2
                      ((let pr1,_ = x in pr1),
                      (let pr1,_ = let _,pr2 = x in pr2 in pr1), v,
                      (let _,pr2 = let _,pr2 = x in pr2 in pr2), t0, l, n,
                      t1, core, deriv,
                      (let conflict_set = conflict_set_of (t0 :: l) v n core
                       in
                       let s0' =
                         CplSolver.add_conflict_set
                           (let pr1,_ = let _,pr2 = x in pr2 in pr1)
                           conflict_set
                       in
                       let mc0' = add_conflict_set (t0 :: l) conflict_set in
                       x0 (let pr1,_ = x in pr1) s0' mc0' __)))))))
         | Unsat core ->
           Coq_tableau_clause_1_graph_equation_2 ((let pr1,_ = x in pr1),
             (let pr1,_ = let _,pr2 = x in pr2 in pr1), core,
             (let _,pr2 = let _,pr2 = x in pr2 in pr2))))
    in fix_F (a,(s0,mc0))

  (** val tableau_elim :
      (Assumptions.t -> CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> __
      -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> __
      -> __ -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t
      -> Lclauses.t -> Lclauses.t list -> Tree.t list -> __ -> __ ->
      (Assumptions.t -> 'a1) -> __ -> __ -> 'a1) -> (Assumptions.t ->
      CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
      int -> Lit.t -> Assumptions.t -> Derivation.t -> __ -> 'a1 -> __ ->
      (Assumptions.t -> 'a1) -> __ -> __ -> 'a1) -> Assumptions.t ->
      CplSolver.t -> Mchain.t -> 'a1 **)

  let tableau_elim tableau_clause_1_graph_equation_2 tableau_clause_1_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_2 a s0 mc0 =
    tableau_graph_mut (fun _ _ _ _ x -> x __) (fun _ _ _ _ _ _ x -> x __)
      tableau_clause_1_graph_equation_2
      tableau_clause_1_clause_2_graph_equation_1
      (fun _ _ _ _ _ _ _ _ x _ x0 -> x0 __ x)
      tableau_clause_1_clause_2_clause_2_graph_equation_1
      (fun a0 s1 v _ mc1 l0 mc2 c d jump_core jump_deriv _ _ ->
      tableau_clause_1_clause_2_clause_2_graph_equation_2 a0 s1 v __ mc1 l0
        mc2 c d jump_core jump_deriv __)
      a s0 mc0 (tableau a s0 mc0) (tableau_graph_correct a s0 mc0)

  (** val coq_FunctionalElimination_tableau :
      (Assumptions.t -> CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> __
      -> __) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> __ ->
      __ -> __) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      Lclauses.t -> Lclauses.t list -> Tree.t list -> __ -> __ ->
      (Assumptions.t -> __) -> __ -> __ -> __) -> (Assumptions.t ->
      CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
      int -> Lit.t -> Assumptions.t -> Derivation.t -> __ -> __ -> __ ->
      (Assumptions.t -> __) -> __ -> __ -> __) -> Assumptions.t ->
      CplSolver.t -> Mchain.t -> __ **)

  let coq_FunctionalElimination_tableau =
    tableau_elim

  (** val coq_FunctionalInduction_tableau :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t)
      coq_FunctionalInduction **)

  let coq_FunctionalInduction_tableau =
    Obj.magic tableau_graph_correct

  (** val next_tableau : Mchain.t -> Assumptions.t -> Solution.t **)

  let next_tableau mc1 a' =
    tableau a' (make_with_clauses (first_cpls mc1)) mc1

  (** val solve_mchain : Mchain.t -> Solution.t **)

  let solve_mchain mc0 =
    let cpls0 = first_cpls mc0 in
    let s0 = make_with_clauses cpls0 in tableau [] s0 mc0

  (** val solve_fml : Fml.t -> Solution.t **)

  let solve_fml phi =
    apply (apply (apply (apply phi from_fml) from_nnf) from_mcnf) solve_mchain
 end

module TailRec =
 struct
  module Solution = Spec.Solution

  module JumpSolution = Spec.JumpSolution

  (** val tableau_jumps_clause_2 :
      t -> CplClause.t list -> BoxClause.t list -> int -> bool -> Lit.t ->
      DiaClause.t list -> Mchain.t -> Tree.t list -> (Assumptions.t ->
      Solution.t) -> (t -> Lclauses.t -> Mchain.t -> Tree.t list ->
      (Assumptions.t -> Solution.t) -> __ -> JumpSolution.t) -> JumpSolution.t **)

  let tableau_jumps_clause_2 v cpls0 boxes0 c refine d dias' mc1 t1s next_tableau0 tableau_jumps0 =
    if refine
    then let fired_boxes =
           apply
             (apply boxes0
               (filter (fun pat -> let (a, _) = pat in forces_atm v a)))
             (map snd)
         in
         (match next_tableau0 (d :: fired_boxes) with
          | Solution.Sat t1 ->
            tableau_jumps0 v { cpls = cpls0; boxes = boxes0; dias = dias' }
              mc1 (t1 :: t1s) next_tableau0 __
          | Solution.Unsat (core, deriv) ->
            JumpSolution.Unsat ((c, d), core, deriv))
    else tableau_jumps0 v { cpls = cpls0; boxes = boxes0; dias = dias' } mc1
           t1s next_tableau0 __

  (** val tableau_jumps_functional :
      t -> Lclauses.t -> Mchain.t -> Tree.t list -> (Assumptions.t ->
      Solution.t) -> (t -> Lclauses.t -> Mchain.t -> Tree.t list ->
      (Assumptions.t -> Solution.t) -> __ -> JumpSolution.t) -> JumpSolution.t **)

  let tableau_jumps_functional v l0 mc1 t1s next_tableau0 tableau_jumps0 =
    let { cpls = cpls0; boxes = boxes0; dias = dias0 } = l0 in
    (match dias0 with
     | [] -> JumpSolution.Sat t1s
     | t0 :: l ->
       let (n, t1) = t0 in
       if forces_atm v n
       then let fired_boxes =
              apply
                (apply boxes0
                  (filter (fun pat -> let (a, _) = pat in forces_atm v a)))
                (map snd)
            in
            (match next_tableau0 (t1 :: fired_boxes) with
             | Solution.Sat t2 ->
               tableau_jumps0 v { cpls = cpls0; boxes = boxes0; dias = l }
                 mc1 (t2 :: t1s) next_tableau0 __
             | Solution.Unsat (core, deriv) ->
               JumpSolution.Unsat ((n, t1), core, deriv))
       else tableau_jumps0 v { cpls = cpls0; boxes = boxes0; dias = l } mc1
              t1s next_tableau0 __)

  (** val tableau_jumps :
      t -> Lclauses.t -> Mchain.t -> Tree.t list -> (Assumptions.t ->
      Solution.t) -> JumpSolution.t **)

  let tableau_jumps a a0 a1 a2 b =
    let rec fix_F x =
      let v = let pr1,_ = x in pr1 in
      let next_tableau0 =
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
              (match next_tableau0 (t1 :: fired_boxes) with
               | Solution.Sat t2 ->
                 let y = v,({ cpls = cpls0; boxes = boxes0; dias =
                   l },((let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2
                         in
                         pr1),((t2 :: (let pr1,_ =
                                         let _,pr2 =
                                           let _,pr2 = let _,pr2 = x in pr2 in
                                           pr2
                                         in
                                         pr2
                                       in
                                       pr1)),next_tableau0)))
                 in
                 fix_F y
               | Solution.Unsat (core, deriv) ->
                 JumpSolution.Unsat ((n, t1), core, deriv))
         else let y = v,({ cpls = cpls0; boxes = boxes0; dias =
                l },((let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in
                      pr1),((let pr1,_ =
                               let _,pr2 =
                                 let _,pr2 = let _,pr2 = x in pr2 in pr2
                               in
                               pr2
                             in
                             pr1),next_tableau0)))
              in
              fix_F y)
    in fix_F (a,(a0,(a1,(a2,b))))

  (** val tableau_jumps_unfold_clause_2 :
      t -> CplClause.t list -> BoxClause.t list -> int -> bool -> Lit.t ->
      DiaClause.t list -> Mchain.t -> Tree.t list -> (Assumptions.t ->
      Solution.t) -> JumpSolution.t **)

  let tableau_jumps_unfold_clause_2 v cpls0 boxes0 c refine d dias' mc1 t1s next_tableau0 =
    if refine
    then let fired_boxes =
           apply
             (apply boxes0
               (filter (fun pat -> let (a, _) = pat in forces_atm v a)))
             (map snd)
         in
         (match next_tableau0 (d :: fired_boxes) with
          | Solution.Sat t1 ->
            tableau_jumps v { cpls = cpls0; boxes = boxes0; dias = dias' }
              mc1 (t1 :: t1s) next_tableau0
          | Solution.Unsat (core, deriv) ->
            JumpSolution.Unsat ((c, d), core, deriv))
    else tableau_jumps v { cpls = cpls0; boxes = boxes0; dias = dias' } mc1
           t1s next_tableau0

  (** val tableau_jumps_unfold :
      t -> Lclauses.t -> Mchain.t -> Tree.t list -> (Assumptions.t ->
      Solution.t) -> JumpSolution.t **)

  let tableau_jumps_unfold v l0 mc1 t1s next_tableau0 =
    let { cpls = cpls0; boxes = boxes0; dias = dias0 } = l0 in
    (match dias0 with
     | [] -> JumpSolution.Sat t1s
     | t0 :: l ->
       let (n, t1) = t0 in
       if forces_atm v n
       then let fired_boxes =
              apply
                (apply boxes0
                  (filter (fun pat -> let (a, _) = pat in forces_atm v a)))
                (map snd)
            in
            (match next_tableau0 (t1 :: fired_boxes) with
             | Solution.Sat t2 ->
               tableau_jumps v { cpls = cpls0; boxes = boxes0; dias = l } mc1
                 (t2 :: t1s) next_tableau0
             | Solution.Unsat (core, deriv) ->
               JumpSolution.Unsat ((n, t1), core, deriv))
       else tableau_jumps v { cpls = cpls0; boxes = boxes0; dias = l } mc1
              t1s next_tableau0)

  type tableau_jumps_graph =
  | Coq_tableau_jumps_graph_equation_1 of t * CplClause.t list
     * BoxClause.t list * Mchain.t * Tree.t list
     * (Assumptions.t -> Solution.t)
  | Coq_tableau_jumps_graph_refinement_2 of t * CplClause.t list
     * BoxClause.t list * int * Lit.t * DiaClause.t list * Mchain.t
     * Tree.t list * (Assumptions.t -> Solution.t)
     * tableau_jumps_clause_2_graph
  and tableau_jumps_clause_2_graph =
  | Coq_tableau_jumps_clause_2_graph_equation_1 of t * CplClause.t list
     * BoxClause.t list * int * Lit.t * DiaClause.t list * Mchain.t
     * Tree.t list * (Assumptions.t -> Solution.t)
     * (Tree.t -> tableau_jumps_graph)
  | Coq_tableau_jumps_clause_2_graph_equation_2 of t * CplClause.t list
     * BoxClause.t list * int * Lit.t * DiaClause.t list * Mchain.t
     * Tree.t list * (Assumptions.t -> Solution.t) * tableau_jumps_graph

  (** val tableau_jumps_graph_mut :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> Tree.t list
      -> (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      Tree.t list -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_clause_2_graph -> 'a2 -> 'a1) -> (t -> CplClause.t list
      -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      Tree.t list -> (Assumptions.t -> Solution.t) -> (Tree.t ->
      tableau_jumps_graph) -> (Tree.t -> 'a1) -> 'a2) -> (t -> CplClause.t
      list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list ->
      Mchain.t -> Tree.t list -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_graph -> 'a1 -> 'a2) -> t -> Lclauses.t -> Mchain.t ->
      Tree.t list -> (Assumptions.t -> Solution.t) -> JumpSolution.t ->
      tableau_jumps_graph -> 'a1 **)

  let tableau_jumps_graph_mut tableau_jumps_graph_equation_1 tableau_jumps_graph_refinement_2 tableau_jumps_clause_2_graph_equation_1 tableau_jumps_clause_2_graph_equation_2 =
    let rec f _ _ _ _ _ _ = function
    | Coq_tableau_jumps_graph_equation_1 (v0, cpls0, boxes0, mc2, t1s0,
                                          next_tableau0) ->
      tableau_jumps_graph_equation_1 v0 cpls0 boxes0 mc2 t1s0 next_tableau0
    | Coq_tableau_jumps_graph_refinement_2 (v0, cpls0, boxes0, c, d, dias',
                                            mc2, t1s0, next_tableau0, hind) ->
      tableau_jumps_graph_refinement_2 v0 cpls0 boxes0 c d dias' mc2 t1s0
        next_tableau0 hind
        (f0 v0 cpls0 boxes0 c (forces_atm v0 c) d dias' mc2 t1s0
          next_tableau0
          (if forces_atm v0 c
           then let fired_boxes =
                  apply
                    (apply boxes0
                      (filter (fun pat ->
                        let (a, _) = pat in forces_atm v0 a)))
                    (map snd)
                in
                (match next_tableau0 (d :: fired_boxes) with
                 | Solution.Sat t1 ->
                   tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                     dias' } mc2 (t1 :: t1s0) next_tableau0
                 | Solution.Unsat (core, deriv) ->
                   JumpSolution.Unsat ((c, d), core, deriv))
           else tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                  dias' } mc2 t1s0 next_tableau0)
          hind)
    and f0 _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_graph_equation_1 (v0, cpls0, boxes0, c0, d0,
                                                   dias'0, mc2, t1s0,
                                                   next_tableau0, hind) ->
      tableau_jumps_clause_2_graph_equation_1 v0 cpls0 boxes0 c0 d0 dias'0
        mc2 t1s0 next_tableau0 hind (fun t1 ->
        f v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 } mc2 (t1 :: t1s0)
          next_tableau0
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 (t1 :: t1s0) next_tableau0)
          (hind t1))
    | Coq_tableau_jumps_clause_2_graph_equation_2 (v0, cpls0, boxes0, c0, d0,
                                                   dias'0, mc2, t1s0,
                                                   next_tableau0, hind) ->
      tableau_jumps_clause_2_graph_equation_2 v0 cpls0 boxes0 c0 d0 dias'0
        mc2 t1s0 next_tableau0 hind
        (f v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 } mc2 t1s0
          next_tableau0
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 t1s0 next_tableau0)
          hind)
    in f

  (** val tableau_jumps_clause_2_graph_mut :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> Tree.t list
      -> (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      Tree.t list -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_clause_2_graph -> 'a2 -> 'a1) -> (t -> CplClause.t list
      -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      Tree.t list -> (Assumptions.t -> Solution.t) -> (Tree.t ->
      tableau_jumps_graph) -> (Tree.t -> 'a1) -> 'a2) -> (t -> CplClause.t
      list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list ->
      Mchain.t -> Tree.t list -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_graph -> 'a1 -> 'a2) -> t -> CplClause.t list ->
      BoxClause.t list -> int -> bool -> Lit.t -> DiaClause.t list ->
      Mchain.t -> Tree.t list -> (Assumptions.t -> Solution.t) ->
      JumpSolution.t -> tableau_jumps_clause_2_graph -> 'a2 **)

  let tableau_jumps_clause_2_graph_mut tableau_jumps_graph_equation_1 tableau_jumps_graph_refinement_2 tableau_jumps_clause_2_graph_equation_1 tableau_jumps_clause_2_graph_equation_2 =
    let rec f _ _ _ _ _ _ = function
    | Coq_tableau_jumps_graph_equation_1 (v0, cpls0, boxes0, mc2, t1s0,
                                          next_tableau0) ->
      tableau_jumps_graph_equation_1 v0 cpls0 boxes0 mc2 t1s0 next_tableau0
    | Coq_tableau_jumps_graph_refinement_2 (v0, cpls0, boxes0, c, d, dias',
                                            mc2, t1s0, next_tableau0, hind) ->
      tableau_jumps_graph_refinement_2 v0 cpls0 boxes0 c d dias' mc2 t1s0
        next_tableau0 hind
        (f0 v0 cpls0 boxes0 c (forces_atm v0 c) d dias' mc2 t1s0
          next_tableau0
          (if forces_atm v0 c
           then let fired_boxes =
                  apply
                    (apply boxes0
                      (filter (fun pat ->
                        let (a, _) = pat in forces_atm v0 a)))
                    (map snd)
                in
                (match next_tableau0 (d :: fired_boxes) with
                 | Solution.Sat t1 ->
                   tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                     dias' } mc2 (t1 :: t1s0) next_tableau0
                 | Solution.Unsat (core, deriv) ->
                   JumpSolution.Unsat ((c, d), core, deriv))
           else tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                  dias' } mc2 t1s0 next_tableau0)
          hind)
    and f0 _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_graph_equation_1 (v0, cpls0, boxes0, c0, d0,
                                                   dias'0, mc2, t1s0,
                                                   next_tableau0, hind) ->
      tableau_jumps_clause_2_graph_equation_1 v0 cpls0 boxes0 c0 d0 dias'0
        mc2 t1s0 next_tableau0 hind (fun t1 ->
        f v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 } mc2 (t1 :: t1s0)
          next_tableau0
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 (t1 :: t1s0) next_tableau0)
          (hind t1))
    | Coq_tableau_jumps_clause_2_graph_equation_2 (v0, cpls0, boxes0, c0, d0,
                                                   dias'0, mc2, t1s0,
                                                   next_tableau0, hind) ->
      tableau_jumps_clause_2_graph_equation_2 v0 cpls0 boxes0 c0 d0 dias'0
        mc2 t1s0 next_tableau0 hind
        (f v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 } mc2 t1s0
          next_tableau0
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 t1s0 next_tableau0)
          hind)
    in f0

  (** val tableau_jumps_graph_rect :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> Tree.t list
      -> (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      Tree.t list -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_clause_2_graph -> 'a2 -> 'a1) -> (t -> CplClause.t list
      -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      Tree.t list -> (Assumptions.t -> Solution.t) -> (Tree.t ->
      tableau_jumps_graph) -> (Tree.t -> 'a1) -> 'a2) -> (t -> CplClause.t
      list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list ->
      Mchain.t -> Tree.t list -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_graph -> 'a1 -> 'a2) -> t -> Lclauses.t -> Mchain.t ->
      Tree.t list -> (Assumptions.t -> Solution.t) -> JumpSolution.t ->
      tableau_jumps_graph -> 'a1 **)

  let tableau_jumps_graph_rect =
    tableau_jumps_graph_mut

  (** val tableau_jumps_graph_correct :
      t -> Lclauses.t -> Mchain.t -> Tree.t list -> (Assumptions.t ->
      Solution.t) -> tableau_jumps_graph **)

  let tableau_jumps_graph_correct v l0 mc1 t1s next_tableau0 =
    let rec fix_F x =
      let x1 = let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr1 in
      let x2 =
        let pr1,_ = let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
        in
        pr1
      in
      let x3 =
        let _,pr2 = let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
        in
        pr2
      in
      let x0 = fun a a0 a1 a2 b ->
        let y = a,(a0,(a1,(a2,b))) in (fun _ -> fix_F y)
      in
      let { cpls = cpls0; boxes = boxes0; dias = dias0 } =
        let pr1,_ = let _,pr2 = x in pr2 in pr1
      in
      (match dias0 with
       | [] ->
         Coq_tableau_jumps_graph_equation_1 ((let pr1,_ = x in pr1), cpls0,
           boxes0, x1, x2, x3)
       | t0 :: l ->
         let (n, t1) = t0 in
         Coq_tableau_jumps_graph_refinement_2 ((let pr1,_ = x in pr1), cpls0,
         boxes0, n, t1, l, x1, x2, x3,
         (let refine = forces_atm (let pr1,_ = x in pr1) n in
          if refine
          then Coq_tableau_jumps_clause_2_graph_equation_1
                 ((let pr1,_ = x in pr1), cpls0, boxes0, n, t1, l, x1, x2,
                 x3, (fun t2 ->
                 x0 (let pr1,_ = x in pr1) { cpls = cpls0; boxes = boxes0;
                   dias = l } x1 (t2 :: x2) x3 __))
          else Coq_tableau_jumps_clause_2_graph_equation_2
                 ((let pr1,_ = x in pr1), cpls0, boxes0, n, t1, l, x1, x2,
                 x3,
                 (x0 (let pr1,_ = x in pr1) { cpls = cpls0; boxes = boxes0;
                   dias = l } x1 x2 x3 __)))))
    in fix_F (v,(l0,(mc1,(t1s,next_tableau0))))

  (** val tableau_jumps_elim :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> Tree.t list
      -> (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      Tree.t list -> (Assumptions.t -> Solution.t) -> (Tree.t -> 'a1) -> __
      -> 'a1) -> (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t
      -> DiaClause.t list -> Mchain.t -> Tree.t list -> (Assumptions.t ->
      Solution.t) -> 'a1 -> __ -> 'a1) -> t -> Lclauses.t -> Mchain.t ->
      Tree.t list -> (Assumptions.t -> Solution.t) -> 'a1 **)

  let tableau_jumps_elim tableau_jumps_graph_equation_1 tableau_jumps_clause_2_graph_equation_1 tableau_jumps_clause_2_graph_equation_2 v l0 mc1 t1s next_tableau0 =
    tableau_jumps_graph_mut tableau_jumps_graph_equation_1
      (fun _ _ _ _ _ _ _ _ _ _ x -> x __)
      (fun v0 cpls0 boxes0 c d dias' mc0 t1s0 next_tableau1 _ ->
      tableau_jumps_clause_2_graph_equation_1 v0 cpls0 boxes0 c d dias' mc0
        t1s0 next_tableau1)
      (fun v0 cpls0 boxes0 c d dias' mc0 t1s0 next_tableau1 _ ->
      tableau_jumps_clause_2_graph_equation_2 v0 cpls0 boxes0 c d dias' mc0
        t1s0 next_tableau1)
      v l0 mc1 t1s next_tableau0 (tableau_jumps v l0 mc1 t1s next_tableau0)
      (tableau_jumps_graph_correct v l0 mc1 t1s next_tableau0)

  (** val coq_FunctionalElimination_tableau_jumps :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> Tree.t list
      -> (Assumptions.t -> Solution.t) -> __) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      Tree.t list -> (Assumptions.t -> Solution.t) -> (Tree.t -> __) -> __ ->
      __) -> (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> Tree.t list -> (Assumptions.t ->
      Solution.t) -> __ -> __ -> __) -> t -> Lclauses.t -> Mchain.t -> Tree.t
      list -> (Assumptions.t -> Solution.t) -> __ **)

  let coq_FunctionalElimination_tableau_jumps =
    tableau_jumps_elim

  (** val coq_FunctionalInduction_tableau_jumps :
      (t -> Lclauses.t -> Mchain.t -> Tree.t list -> (Assumptions.t ->
      Solution.t) -> JumpSolution.t) coq_FunctionalInduction **)

  let coq_FunctionalInduction_tableau_jumps =
    Obj.magic tableau_jumps_graph_correct

  (** val tableau_clause_1_clause_2_clause_2 :
      Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> CplSolver.t -> Mchain.t -> __ ->
      Solution.t) -> JumpSolution.t -> Solution.t **)

  let tableau_clause_1_clause_2_clause_2 a s0 v _ l0 mc1 tableau0 = function
  | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
  | JumpSolution.Unsat (failed_dia, core, deriv) ->
    let (n, t0) = failed_dia in
    let conflict_set = conflict_set_of (l0 :: mc1) v n core in
    let s0' = CplSolver.add_conflict_set s0 conflict_set in
    let mc0' = add_conflict_set (l0 :: mc1) conflict_set in
    (match tableau0 a s0' mc0' __ with
     | Solution.Sat t1 -> Solution.Sat t1
     | Solution.Unsat (rs_core, rs_deriv) ->
       Solution.Unsat (rs_core, (JumpRestart (v, (n, t0), deriv, rs_deriv))))

  (** val tableau_clause_1_clause_2 :
      Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t list ->
      (Assumptions.t -> CplSolver.t -> Mchain.t -> __ -> Solution.t) ->
      Solution.t **)

  let tableau_clause_1_clause_2 a s0 v _ refine tableau0 =
    match refine with
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
         (match tableau0 a s0' mc0' __ with
          | Solution.Sat t2 -> Solution.Sat t2
          | Solution.Unsat (rs_core, rs_deriv) ->
            Solution.Unsat (rs_core, (JumpRestart (v, (n, t1), deriv,
              rs_deriv)))))

  (** val tableau_clause_1 :
      Assumptions.t -> CplSolver.t -> CplSolution.t -> Mchain.t ->
      (Assumptions.t -> CplSolver.t -> Mchain.t -> __ -> Solution.t) ->
      Solution.t **)

  let tableau_clause_1 a s0 refine mc0 tableau0 =
    match refine with
    | Sat v ->
      (match mc0 with
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
            (match tableau0 a s0' mc0' __ with
             | Solution.Sat t2 -> Solution.Sat t2
             | Solution.Unsat (rs_core, rs_deriv) ->
               Solution.Unsat (rs_core, (JumpRestart (v, (n, t1), deriv,
                 rs_deriv))))))
    | Unsat core -> Solution.Unsat (core, (Id core))

  (** val tableau_functional :
      Assumptions.t -> CplSolver.t -> Mchain.t -> (Assumptions.t ->
      CplSolver.t -> Mchain.t -> __ -> Solution.t) -> Solution.t **)

  let tableau_functional a s0 mc0 tableau0 =
    match inspect (solve_with_assumptions s0 a) with
    | Sat v ->
      (match mc0 with
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
            (match tableau0 a s0' mc0' __ with
             | Solution.Sat t2 -> Solution.Sat t2
             | Solution.Unsat (rs_core, rs_deriv) ->
               Solution.Unsat (rs_core, (JumpRestart (v, (n, t1), deriv,
                 rs_deriv))))))
    | Unsat core -> Solution.Unsat (core, (Id core))

  (** val tableau : Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t **)

  let tableau a a0 b =
    let rec fix_F x =
      let a1 = let pr1,_ = x in pr1 in
      let s0 = let pr1,_ = let _,pr2 = x in pr2 in pr1 in
      let tableau0 = fun a2 a3 b0 -> let y = a2,(a3,b0) in (fun _ -> fix_F y)
      in
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

  (** val tableau_unfold_clause_1_clause_2_clause_2 :
      Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> JumpSolution.t -> Solution.t **)

  let tableau_unfold_clause_1_clause_2_clause_2 a s0 v _ l0 mc1 = function
  | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
  | JumpSolution.Unsat (failed_dia, core, deriv) ->
    let (n, t0) = failed_dia in
    let conflict_set = conflict_set_of (l0 :: mc1) v n core in
    let s0' = CplSolver.add_conflict_set s0 conflict_set in
    let mc0' = add_conflict_set (l0 :: mc1) conflict_set in
    (match tableau a s0' mc0' with
     | Solution.Sat t1 -> Solution.Sat t1
     | Solution.Unsat (rs_core, rs_deriv) ->
       Solution.Unsat (rs_core, (JumpRestart (v, (n, t0), deriv, rs_deriv))))

  (** val tableau_unfold_clause_1_clause_2 :
      Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t list ->
      Solution.t **)

  let tableau_unfold_clause_1_clause_2 a s0 v _ = function
  | [] -> Solution.Sat (Coq_make (v, []))
  | t0 :: l ->
    (match inspect
             (tableau_jumps v t0 l [] (fun a' ->
               tableau a' (make_with_clauses (first_cpls l)) l)) with
     | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
     | JumpSolution.Unsat (failed_dia, core, deriv) ->
       let (n, t1) = failed_dia in
       let conflict_set = conflict_set_of (t0 :: l) v n core in
       let s0' = CplSolver.add_conflict_set s0 conflict_set in
       let mc0' = add_conflict_set (t0 :: l) conflict_set in
       (match tableau a s0' mc0' with
        | Solution.Sat t2 -> Solution.Sat t2
        | Solution.Unsat (rs_core, rs_deriv) ->
          Solution.Unsat (rs_core, (JumpRestart (v, (n, t1), deriv,
            rs_deriv)))))

  (** val tableau_unfold_clause_1 :
      Assumptions.t -> CplSolver.t -> CplSolution.t -> Mchain.t -> Solution.t **)

  let tableau_unfold_clause_1 a s0 refine mc0 =
    match refine with
    | Sat v ->
      (match mc0 with
       | [] -> Solution.Sat (Coq_make (v, []))
       | t0 :: l ->
         (match inspect
                  (tableau_jumps v t0 l [] (fun a' ->
                    tableau a' (make_with_clauses (first_cpls l)) l)) with
          | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
          | JumpSolution.Unsat (failed_dia, core, deriv) ->
            let (n, t1) = failed_dia in
            let conflict_set = conflict_set_of (t0 :: l) v n core in
            let s0' = CplSolver.add_conflict_set s0 conflict_set in
            let mc0' = add_conflict_set (t0 :: l) conflict_set in
            (match tableau a s0' mc0' with
             | Solution.Sat t2 -> Solution.Sat t2
             | Solution.Unsat (rs_core, rs_deriv) ->
               Solution.Unsat (rs_core, (JumpRestart (v, (n, t1), deriv,
                 rs_deriv))))))
    | Unsat core -> Solution.Unsat (core, (Id core))

  (** val tableau_unfold :
      Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t **)

  let tableau_unfold a s0 mc0 =
    match inspect (solve_with_assumptions s0 a) with
    | Sat v ->
      (match mc0 with
       | [] -> Solution.Sat (Coq_make (v, []))
       | t0 :: l ->
         (match inspect
                  (tableau_jumps v t0 l [] (fun a' ->
                    tableau a' (make_with_clauses (first_cpls l)) l)) with
          | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
          | JumpSolution.Unsat (failed_dia, core, deriv) ->
            let (n, t1) = failed_dia in
            let conflict_set = conflict_set_of (t0 :: l) v n core in
            let s0' = CplSolver.add_conflict_set s0 conflict_set in
            let mc0' = add_conflict_set (t0 :: l) conflict_set in
            (match tableau a s0' mc0' with
             | Solution.Sat t2 -> Solution.Sat t2
             | Solution.Unsat (rs_core, rs_deriv) ->
               Solution.Unsat (rs_core, (JumpRestart (v, (n, t1), deriv,
                 rs_deriv))))))
    | Unsat core -> Solution.Unsat (core, (Id core))

  type tableau_graph =
  | Coq_tableau_graph_refinement_1 of Assumptions.t * CplSolver.t * Mchain.t
     * tableau_clause_1_graph
  and tableau_clause_1_graph =
  | Coq_tableau_clause_1_graph_refinement_1 of Assumptions.t * CplSolver.t
     * t * Mchain.t * tableau_clause_1_clause_2_graph
  | Coq_tableau_clause_1_graph_equation_2 of Assumptions.t * CplSolver.t
     * Assumptions.t * Mchain.t
  and tableau_clause_1_clause_2_graph =
  | Coq_tableau_clause_1_clause_2_graph_equation_1 of Assumptions.t
     * CplSolver.t * t * Mchain.t
  | Coq_tableau_clause_1_clause_2_graph_refinement_2 of Assumptions.t
     * CplSolver.t * t * Mchain.t * Lclauses.t * Lclauses.t list
     * (Assumptions.t -> tableau_graph)
     * tableau_clause_1_clause_2_clause_2_graph
  and tableau_clause_1_clause_2_clause_2_graph =
  | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1 of Assumptions.t
     * CplSolver.t * t * Mchain.t * Lclauses.t * Lclauses.t list * Tree.t list
  | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2 of Assumptions.t
     * CplSolver.t * t * Mchain.t * Lclauses.t * Lclauses.t list * int
     * Lit.t * Assumptions.t * Derivation.t * tableau_graph

  (** val tableau_graph_mut :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
      'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
      CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> tableau_graph) -> (Assumptions.t
      -> 'a1) -> tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> Tree.t list -> __ -> 'a4) -> (Assumptions.t ->
      CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
      int -> Lit.t -> Assumptions.t -> Derivation.t -> __ -> tableau_graph ->
      'a1 -> 'a4) -> Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t
      -> tableau_graph -> 'a1 **)

  let tableau_graph_mut tableau_graph_refinement_1 tableau_clause_1_graph_refinement_1 tableau_clause_1_graph_equation_2 tableau_clause_1_clause_2_graph_equation_1 tableau_clause_1_clause_2_graph_refinement_2 tableau_clause_1_clause_2_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_2 =
    let rec f _ _ _ _ = function
    | Coq_tableau_graph_refinement_1 (a0, s1, mc1, hind) ->
      tableau_graph_refinement_1 a0 s1 mc1 hind
        (f0 a0 s1 (inspect (solve_with_assumptions s1 a0)) mc1
          (match inspect (solve_with_assumptions s1 a0) with
           | Sat v ->
             (match mc1 with
              | [] -> Solution.Sat (Coq_make (v, []))
              | t1 :: l ->
                (match inspect
                         (tableau_jumps v t1 l [] (fun a' ->
                           tableau a' (make_with_clauses (first_cpls l)) l)) with
                 | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
                 | JumpSolution.Unsat (failed_dia, core, deriv) ->
                   let (n, t2) = failed_dia in
                   let conflict_set = conflict_set_of (t1 :: l) v n core in
                   let s0' = CplSolver.add_conflict_set s1 conflict_set in
                   let mc0' = add_conflict_set (t1 :: l) conflict_set in
                   (match tableau a0 s0' mc0' with
                    | Solution.Sat t3 -> Solution.Sat t3
                    | Solution.Unsat (rs_core, rs_deriv) ->
                      Solution.Unsat (rs_core, (JumpRestart (v, (n, t2),
                        deriv, rs_deriv))))))
           | Unsat core -> Solution.Unsat (core, (Id core)))
          hind)
    and f0 _ _ _ _ _ = function
    | Coq_tableau_clause_1_graph_refinement_1 (a0, s1, v, mc1, hind) ->
      tableau_clause_1_graph_refinement_1 a0 s1 v __ mc1 hind
        (f1 a0 s1 v __ mc1 mc1
          (match mc1 with
           | [] -> Solution.Sat (Coq_make (v, []))
           | t1 :: l ->
             (match inspect
                      (tableau_jumps v t1 l [] (fun a' ->
                        tableau a' (make_with_clauses (first_cpls l)) l)) with
              | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
              | JumpSolution.Unsat (failed_dia, core, deriv) ->
                let (n, t2) = failed_dia in
                let conflict_set = conflict_set_of (t1 :: l) v n core in
                let s0' = CplSolver.add_conflict_set s1 conflict_set in
                let mc0' = add_conflict_set (t1 :: l) conflict_set in
                (match tableau a0 s0' mc0' with
                 | Solution.Sat t3 -> Solution.Sat t3
                 | Solution.Unsat (rs_core, rs_deriv) ->
                   Solution.Unsat (rs_core, (JumpRestart (v, (n, t2), deriv,
                     rs_deriv))))))
          hind)
    | Coq_tableau_clause_1_graph_equation_2 (a0, s1, a', mc1) ->
      tableau_clause_1_graph_equation_2 a0 s1 a' __ mc1
    and f1 _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_graph_equation_1 (a0, s1, v0, mc1) ->
      tableau_clause_1_clause_2_graph_equation_1 a0 s1 v0 __ mc1
    | Coq_tableau_clause_1_clause_2_graph_refinement_2 (a0, s1, v0, mc1, l0,
                                                        mc2, hind, hind0) ->
      tableau_clause_1_clause_2_graph_refinement_2 a0 s1 v0 __ mc1 l0 mc2
        hind (fun a' ->
        f a' (make_with_clauses (first_cpls mc2)) mc2
          (tableau a' (make_with_clauses (first_cpls mc2)) mc2) (hind a'))
        hind0
        (f2 a0 s1 v0 __ mc1 l0 mc2
          (inspect
            (tableau_jumps v0 l0 mc2 [] (fun a' ->
              tableau a' (make_with_clauses (first_cpls mc2)) mc2)))
          (match inspect
                   (tableau_jumps v0 l0 mc2 [] (fun a' ->
                     tableau a' (make_with_clauses (first_cpls mc2)) mc2)) with
           | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v0, t1s))
           | JumpSolution.Unsat (failed_dia, core, deriv) ->
             let (n, t1) = failed_dia in
             let conflict_set = conflict_set_of (l0 :: mc2) v0 n core in
             let s0' = CplSolver.add_conflict_set s1 conflict_set in
             let mc0' = add_conflict_set (l0 :: mc2) conflict_set in
             (match tableau a0 s0' mc0' with
              | Solution.Sat t2 -> Solution.Sat t2
              | Solution.Unsat (rs_core, rs_deriv) ->
                Solution.Unsat (rs_core, (JumpRestart (v0, (n, t1), deriv,
                  rs_deriv)))))
          hind0)
    and f2 _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               t1s) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_1 a0 s1 v0 __ mc2 l1
        mc3 t1s __
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               c, d,
                                                               jump_core,
                                                               jump_deriv,
                                                               hind) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_2 a0 s1 v0 __ mc2 l1
        mc3 c d jump_core jump_deriv __ hind
        (let conflict_set = conflict_set_of (l1 :: mc3) v0 c jump_core in
         let s0' = CplSolver.add_conflict_set s1 conflict_set in
         let mc0' = add_conflict_set (l1 :: mc3) conflict_set in
         f a0 s0' mc0' (tableau a0 s0' mc0') hind)
    in f

  (** val tableau_clause_1_graph_mut :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
      'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
      CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> tableau_graph) -> (Assumptions.t
      -> 'a1) -> tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> Tree.t list -> __ -> 'a4) -> (Assumptions.t ->
      CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
      int -> Lit.t -> Assumptions.t -> Derivation.t -> __ -> tableau_graph ->
      'a1 -> 'a4) -> Assumptions.t -> CplSolver.t -> CplSolution.t ->
      Mchain.t -> Solution.t -> tableau_clause_1_graph -> 'a2 **)

  let tableau_clause_1_graph_mut tableau_graph_refinement_1 tableau_clause_1_graph_refinement_1 tableau_clause_1_graph_equation_2 tableau_clause_1_clause_2_graph_equation_1 tableau_clause_1_clause_2_graph_refinement_2 tableau_clause_1_clause_2_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_2 =
    let rec f _ _ _ _ = function
    | Coq_tableau_graph_refinement_1 (a0, s1, mc1, hind) ->
      tableau_graph_refinement_1 a0 s1 mc1 hind
        (f0 a0 s1 (inspect (solve_with_assumptions s1 a0)) mc1
          (match inspect (solve_with_assumptions s1 a0) with
           | Sat v ->
             (match mc1 with
              | [] -> Solution.Sat (Coq_make (v, []))
              | t1 :: l ->
                (match inspect
                         (tableau_jumps v t1 l [] (fun a' ->
                           tableau a' (make_with_clauses (first_cpls l)) l)) with
                 | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
                 | JumpSolution.Unsat (failed_dia, core, deriv) ->
                   let (n, t2) = failed_dia in
                   let conflict_set = conflict_set_of (t1 :: l) v n core in
                   let s0' = CplSolver.add_conflict_set s1 conflict_set in
                   let mc0' = add_conflict_set (t1 :: l) conflict_set in
                   (match tableau a0 s0' mc0' with
                    | Solution.Sat t3 -> Solution.Sat t3
                    | Solution.Unsat (rs_core, rs_deriv) ->
                      Solution.Unsat (rs_core, (JumpRestart (v, (n, t2),
                        deriv, rs_deriv))))))
           | Unsat core -> Solution.Unsat (core, (Id core)))
          hind)
    and f0 _ _ _ _ _ = function
    | Coq_tableau_clause_1_graph_refinement_1 (a0, s1, v, mc1, hind) ->
      tableau_clause_1_graph_refinement_1 a0 s1 v __ mc1 hind
        (f1 a0 s1 v __ mc1 mc1
          (match mc1 with
           | [] -> Solution.Sat (Coq_make (v, []))
           | t1 :: l ->
             (match inspect
                      (tableau_jumps v t1 l [] (fun a' ->
                        tableau a' (make_with_clauses (first_cpls l)) l)) with
              | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v, t1s))
              | JumpSolution.Unsat (failed_dia, core, deriv) ->
                let (n, t2) = failed_dia in
                let conflict_set = conflict_set_of (t1 :: l) v n core in
                let s0' = CplSolver.add_conflict_set s1 conflict_set in
                let mc0' = add_conflict_set (t1 :: l) conflict_set in
                (match tableau a0 s0' mc0' with
                 | Solution.Sat t3 -> Solution.Sat t3
                 | Solution.Unsat (rs_core, rs_deriv) ->
                   Solution.Unsat (rs_core, (JumpRestart (v, (n, t2), deriv,
                     rs_deriv))))))
          hind)
    | Coq_tableau_clause_1_graph_equation_2 (a0, s1, a', mc1) ->
      tableau_clause_1_graph_equation_2 a0 s1 a' __ mc1
    and f1 _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_graph_equation_1 (a0, s1, v0, mc1) ->
      tableau_clause_1_clause_2_graph_equation_1 a0 s1 v0 __ mc1
    | Coq_tableau_clause_1_clause_2_graph_refinement_2 (a0, s1, v0, mc1, l0,
                                                        mc2, hind, hind0) ->
      tableau_clause_1_clause_2_graph_refinement_2 a0 s1 v0 __ mc1 l0 mc2
        hind (fun a' ->
        f a' (make_with_clauses (first_cpls mc2)) mc2
          (tableau a' (make_with_clauses (first_cpls mc2)) mc2) (hind a'))
        hind0
        (f2 a0 s1 v0 __ mc1 l0 mc2
          (inspect
            (tableau_jumps v0 l0 mc2 [] (fun a' ->
              tableau a' (make_with_clauses (first_cpls mc2)) mc2)))
          (match inspect
                   (tableau_jumps v0 l0 mc2 [] (fun a' ->
                     tableau a' (make_with_clauses (first_cpls mc2)) mc2)) with
           | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v0, t1s))
           | JumpSolution.Unsat (failed_dia, core, deriv) ->
             let (n, t1) = failed_dia in
             let conflict_set = conflict_set_of (l0 :: mc2) v0 n core in
             let s0' = CplSolver.add_conflict_set s1 conflict_set in
             let mc0' = add_conflict_set (l0 :: mc2) conflict_set in
             (match tableau a0 s0' mc0' with
              | Solution.Sat t2 -> Solution.Sat t2
              | Solution.Unsat (rs_core, rs_deriv) ->
                Solution.Unsat (rs_core, (JumpRestart (v0, (n, t1), deriv,
                  rs_deriv)))))
          hind0)
    and f2 _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               t1s) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_1 a0 s1 v0 __ mc2 l1
        mc3 t1s __
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               c, d,
                                                               jump_core,
                                                               jump_deriv,
                                                               hind) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_2 a0 s1 v0 __ mc2 l1
        mc3 c d jump_core jump_deriv __ hind
        (let conflict_set = conflict_set_of (l1 :: mc3) v0 c jump_core in
         let s0' = CplSolver.add_conflict_set s1 conflict_set in
         let mc0' = add_conflict_set (l1 :: mc3) conflict_set in
         f a0 s0' mc0' (tableau a0 s0' mc0') hind)
    in f0

  (** val tableau_clause_1_clause_2_graph_mut :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
      'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
      CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> tableau_graph) -> (Assumptions.t
      -> 'a1) -> tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> Tree.t list -> __ -> 'a4) -> (Assumptions.t ->
      CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
      int -> Lit.t -> Assumptions.t -> Derivation.t -> __ -> tableau_graph ->
      'a1 -> 'a4) -> Assumptions.t -> CplSolver.t -> t -> Mchain.t ->
      Mchain.t -> Solution.t -> tableau_clause_1_clause_2_graph -> 'a3 **)

  let tableau_clause_1_clause_2_graph_mut tableau_graph_refinement_1 tableau_clause_1_graph_refinement_1 tableau_clause_1_graph_equation_2 tableau_clause_1_clause_2_graph_equation_1 tableau_clause_1_clause_2_graph_refinement_2 tableau_clause_1_clause_2_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_2 a s0 v mc0 refine t0 t1 =
    let rec f _ _ _ _ = function
    | Coq_tableau_graph_refinement_1 (a0, s1, mc1, hind) ->
      tableau_graph_refinement_1 a0 s1 mc1 hind
        (f0 a0 s1 (inspect (solve_with_assumptions s1 a0)) mc1
          (match inspect (solve_with_assumptions s1 a0) with
           | Sat v0 ->
             (match mc1 with
              | [] -> Solution.Sat (Coq_make (v0, []))
              | t3 :: l ->
                (match inspect
                         (tableau_jumps v0 t3 l [] (fun a' ->
                           tableau a' (make_with_clauses (first_cpls l)) l)) with
                 | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v0, t1s))
                 | JumpSolution.Unsat (failed_dia, core, deriv) ->
                   let (n, t4) = failed_dia in
                   let conflict_set = conflict_set_of (t3 :: l) v0 n core in
                   let s0' = CplSolver.add_conflict_set s1 conflict_set in
                   let mc0' = add_conflict_set (t3 :: l) conflict_set in
                   (match tableau a0 s0' mc0' with
                    | Solution.Sat t5 -> Solution.Sat t5
                    | Solution.Unsat (rs_core, rs_deriv) ->
                      Solution.Unsat (rs_core, (JumpRestart (v0, (n, t4),
                        deriv, rs_deriv))))))
           | Unsat core -> Solution.Unsat (core, (Id core)))
          hind)
    and f0 _ _ _ _ _ = function
    | Coq_tableau_clause_1_graph_refinement_1 (a0, s1, v0, mc1, hind) ->
      tableau_clause_1_graph_refinement_1 a0 s1 v0 __ mc1 hind
        (f1 a0 s1 v0 mc1 mc1
          (match mc1 with
           | [] -> Solution.Sat (Coq_make (v0, []))
           | t3 :: l ->
             (match inspect
                      (tableau_jumps v0 t3 l [] (fun a' ->
                        tableau a' (make_with_clauses (first_cpls l)) l)) with
              | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v0, t1s))
              | JumpSolution.Unsat (failed_dia, core, deriv) ->
                let (n, t4) = failed_dia in
                let conflict_set = conflict_set_of (t3 :: l) v0 n core in
                let s0' = CplSolver.add_conflict_set s1 conflict_set in
                let mc0' = add_conflict_set (t3 :: l) conflict_set in
                (match tableau a0 s0' mc0' with
                 | Solution.Sat t5 -> Solution.Sat t5
                 | Solution.Unsat (rs_core, rs_deriv) ->
                   Solution.Unsat (rs_core, (JumpRestart (v0, (n, t4), deriv,
                     rs_deriv))))))
          hind)
    | Coq_tableau_clause_1_graph_equation_2 (a0, s1, a', mc1) ->
      tableau_clause_1_graph_equation_2 a0 s1 a' __ mc1
    and f1 _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_graph_equation_1 (a0, s1, v0, mc1) ->
      tableau_clause_1_clause_2_graph_equation_1 a0 s1 v0 __ mc1
    | Coq_tableau_clause_1_clause_2_graph_refinement_2 (a0, s1, v0, mc1, l0,
                                                        mc2, hind, hind0) ->
      tableau_clause_1_clause_2_graph_refinement_2 a0 s1 v0 __ mc1 l0 mc2
        hind (fun a' ->
        f a' (make_with_clauses (first_cpls mc2)) mc2
          (tableau a' (make_with_clauses (first_cpls mc2)) mc2) (hind a'))
        hind0
        (f2 a0 s1 v0 __ mc1 l0 mc2
          (inspect
            (tableau_jumps v0 l0 mc2 [] (fun a' ->
              tableau a' (make_with_clauses (first_cpls mc2)) mc2)))
          (match inspect
                   (tableau_jumps v0 l0 mc2 [] (fun a' ->
                     tableau a' (make_with_clauses (first_cpls mc2)) mc2)) with
           | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v0, t1s))
           | JumpSolution.Unsat (failed_dia, core, deriv) ->
             let (n, t3) = failed_dia in
             let conflict_set = conflict_set_of (l0 :: mc2) v0 n core in
             let s0' = CplSolver.add_conflict_set s1 conflict_set in
             let mc0' = add_conflict_set (l0 :: mc2) conflict_set in
             (match tableau a0 s0' mc0' with
              | Solution.Sat t4 -> Solution.Sat t4
              | Solution.Unsat (rs_core, rs_deriv) ->
                Solution.Unsat (rs_core, (JumpRestart (v0, (n, t3), deriv,
                  rs_deriv)))))
          hind0)
    and f2 _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               t1s) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_1 a0 s1 v0 __ mc2 l1
        mc3 t1s __
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               c, d,
                                                               jump_core,
                                                               jump_deriv,
                                                               hind) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_2 a0 s1 v0 __ mc2 l1
        mc3 c d jump_core jump_deriv __ hind
        (let conflict_set = conflict_set_of (l1 :: mc3) v0 c jump_core in
         let s0' = CplSolver.add_conflict_set s1 conflict_set in
         let mc0' = add_conflict_set (l1 :: mc3) conflict_set in
         f a0 s0' mc0' (tableau a0 s0' mc0') hind)
    in f1 a s0 v mc0 refine t0 t1

  (** val tableau_clause_1_clause_2_clause_2_graph_mut :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
      'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
      CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> tableau_graph) -> (Assumptions.t
      -> 'a1) -> tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> Tree.t list -> __ -> 'a4) -> (Assumptions.t ->
      CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
      int -> Lit.t -> Assumptions.t -> Derivation.t -> __ -> tableau_graph ->
      'a1 -> 'a4) -> Assumptions.t -> CplSolver.t -> t -> Mchain.t ->
      Lclauses.t -> Lclauses.t list -> JumpSolution.t -> Solution.t ->
      tableau_clause_1_clause_2_clause_2_graph -> 'a4 **)

  let tableau_clause_1_clause_2_clause_2_graph_mut tableau_graph_refinement_1 tableau_clause_1_graph_refinement_1 tableau_clause_1_graph_equation_2 tableau_clause_1_clause_2_graph_equation_1 tableau_clause_1_clause_2_graph_refinement_2 tableau_clause_1_clause_2_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_2 a s0 v mc0 l0 mc1 refine t0 t1 =
    let rec f _ _ _ _ = function
    | Coq_tableau_graph_refinement_1 (a0, s1, mc2, hind) ->
      tableau_graph_refinement_1 a0 s1 mc2 hind
        (f0 a0 s1 (inspect (solve_with_assumptions s1 a0)) mc2
          (match inspect (solve_with_assumptions s1 a0) with
           | Sat v0 ->
             (match mc2 with
              | [] -> Solution.Sat (Coq_make (v0, []))
              | t3 :: l ->
                (match inspect
                         (tableau_jumps v0 t3 l [] (fun a' ->
                           tableau a' (make_with_clauses (first_cpls l)) l)) with
                 | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v0, t1s))
                 | JumpSolution.Unsat (failed_dia, core, deriv) ->
                   let (n, t4) = failed_dia in
                   let conflict_set = conflict_set_of (t3 :: l) v0 n core in
                   let s0' = CplSolver.add_conflict_set s1 conflict_set in
                   let mc0' = add_conflict_set (t3 :: l) conflict_set in
                   (match tableau a0 s0' mc0' with
                    | Solution.Sat t5 -> Solution.Sat t5
                    | Solution.Unsat (rs_core, rs_deriv) ->
                      Solution.Unsat (rs_core, (JumpRestart (v0, (n, t4),
                        deriv, rs_deriv))))))
           | Unsat core -> Solution.Unsat (core, (Id core)))
          hind)
    and f0 _ _ _ _ _ = function
    | Coq_tableau_clause_1_graph_refinement_1 (a0, s1, v0, mc2, hind) ->
      tableau_clause_1_graph_refinement_1 a0 s1 v0 __ mc2 hind
        (f1 a0 s1 v0 __ mc2 mc2
          (match mc2 with
           | [] -> Solution.Sat (Coq_make (v0, []))
           | t3 :: l ->
             (match inspect
                      (tableau_jumps v0 t3 l [] (fun a' ->
                        tableau a' (make_with_clauses (first_cpls l)) l)) with
              | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v0, t1s))
              | JumpSolution.Unsat (failed_dia, core, deriv) ->
                let (n, t4) = failed_dia in
                let conflict_set = conflict_set_of (t3 :: l) v0 n core in
                let s0' = CplSolver.add_conflict_set s1 conflict_set in
                let mc0' = add_conflict_set (t3 :: l) conflict_set in
                (match tableau a0 s0' mc0' with
                 | Solution.Sat t5 -> Solution.Sat t5
                 | Solution.Unsat (rs_core, rs_deriv) ->
                   Solution.Unsat (rs_core, (JumpRestart (v0, (n, t4), deriv,
                     rs_deriv))))))
          hind)
    | Coq_tableau_clause_1_graph_equation_2 (a0, s1, a', mc2) ->
      tableau_clause_1_graph_equation_2 a0 s1 a' __ mc2
    and f1 _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_graph_equation_1 (a0, s1, v0, mc2) ->
      tableau_clause_1_clause_2_graph_equation_1 a0 s1 v0 __ mc2
    | Coq_tableau_clause_1_clause_2_graph_refinement_2 (a0, s1, v0, mc2, l1,
                                                        mc3, hind, hind0) ->
      tableau_clause_1_clause_2_graph_refinement_2 a0 s1 v0 __ mc2 l1 mc3
        hind (fun a' ->
        f a' (make_with_clauses (first_cpls mc3)) mc3
          (tableau a' (make_with_clauses (first_cpls mc3)) mc3) (hind a'))
        hind0
        (f2 a0 s1 v0 mc2 l1 mc3
          (inspect
            (tableau_jumps v0 l1 mc3 [] (fun a' ->
              tableau a' (make_with_clauses (first_cpls mc3)) mc3)))
          (match inspect
                   (tableau_jumps v0 l1 mc3 [] (fun a' ->
                     tableau a' (make_with_clauses (first_cpls mc3)) mc3)) with
           | JumpSolution.Sat t1s -> Solution.Sat (Coq_make (v0, t1s))
           | JumpSolution.Unsat (failed_dia, core, deriv) ->
             let (n, t3) = failed_dia in
             let conflict_set = conflict_set_of (l1 :: mc3) v0 n core in
             let s0' = CplSolver.add_conflict_set s1 conflict_set in
             let mc0' = add_conflict_set (l1 :: mc3) conflict_set in
             (match tableau a0 s0' mc0' with
              | Solution.Sat t4 -> Solution.Sat t4
              | Solution.Unsat (rs_core, rs_deriv) ->
                Solution.Unsat (rs_core, (JumpRestart (v0, (n, t3), deriv,
                  rs_deriv)))))
          hind0)
    and f2 _ _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               t1s) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_1 a0 s1 v0 __ mc2 l1
        mc3 t1s __
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               c, d,
                                                               jump_core,
                                                               jump_deriv,
                                                               hind) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_2 a0 s1 v0 __ mc2 l1
        mc3 c d jump_core jump_deriv __ hind
        (let conflict_set = conflict_set_of (l1 :: mc3) v0 c jump_core in
         let s0' = CplSolver.add_conflict_set s1 conflict_set in
         let mc0' = add_conflict_set (l1 :: mc3) conflict_set in
         f a0 s0' mc0' (tableau a0 s0' mc0') hind)
    in f2 a s0 v mc0 l0 mc1 refine t0 t1

  (** val tableau_graph_rect :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
      'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
      CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> tableau_graph) -> (Assumptions.t
      -> 'a1) -> tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> Tree.t list -> __ -> 'a4) -> (Assumptions.t ->
      CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
      int -> Lit.t -> Assumptions.t -> Derivation.t -> __ -> tableau_graph ->
      'a1 -> 'a4) -> Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t
      -> tableau_graph -> 'a1 **)

  let tableau_graph_rect =
    tableau_graph_mut

  (** val tableau_graph_correct :
      Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_graph **)

  let tableau_graph_correct a s0 mc0 =
    let rec fix_F x =
      Coq_tableau_graph_refinement_1 ((let pr1,_ = x in pr1),
        (let pr1,_ = let _,pr2 = x in pr2 in pr1),
        (let _,pr2 = let _,pr2 = x in pr2 in pr2),
        (let refine =
           inspect
             (solve_with_assumptions
               (let pr1,_ = let _,pr2 = x in pr2 in pr1)
               (let pr1,_ = x in pr1))
         in
         match refine with
         | Sat v ->
           Coq_tableau_clause_1_graph_refinement_1 ((let pr1,_ = x in pr1),
             (let pr1,_ = let _,pr2 = x in pr2 in pr1), v,
             (let _,pr2 = let _,pr2 = x in pr2 in pr2),
             (let refine0 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in
              let x0 = fun a0 a1 b -> let y = a0,(a1,b) in (fun _ -> fix_F y)
              in
              (match refine0 with
               | [] ->
                 Coq_tableau_clause_1_clause_2_graph_equation_1
                   ((let pr1,_ = x in pr1),
                   (let pr1,_ = let _,pr2 = x in pr2 in pr1), v,
                   (let _,pr2 = let _,pr2 = x in pr2 in pr2))
               | t0 :: l ->
                 Coq_tableau_clause_1_clause_2_graph_refinement_2
                   ((let pr1,_ = x in pr1),
                   (let pr1,_ = let _,pr2 = x in pr2 in pr1), v,
                   (let _,pr2 = let _,pr2 = x in pr2 in pr2), t0, l,
                   (fun a' -> x0 a' (make_with_clauses (first_cpls l)) l __),
                   (let refine1 =
                      inspect
                        (tableau_jumps v t0 l [] (fun a' ->
                          tableau a' (make_with_clauses (first_cpls l)) l))
                    in
                    match refine1 with
                    | JumpSolution.Sat t1s ->
                      Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1
                        ((let pr1,_ = x in pr1),
                        (let pr1,_ = let _,pr2 = x in pr2 in pr1), v,
                        (let _,pr2 = let _,pr2 = x in pr2 in pr2), t0, l, t1s)
                    | JumpSolution.Unsat (failed_dia, core, deriv) ->
                      let (n, t1) = failed_dia in
                      Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2
                      ((let pr1,_ = x in pr1),
                      (let pr1,_ = let _,pr2 = x in pr2 in pr1), v,
                      (let _,pr2 = let _,pr2 = x in pr2 in pr2), t0, l, n,
                      t1, core, deriv,
                      (let conflict_set = conflict_set_of (t0 :: l) v n core
                       in
                       let s0' =
                         CplSolver.add_conflict_set
                           (let pr1,_ = let _,pr2 = x in pr2 in pr1)
                           conflict_set
                       in
                       let mc0' = add_conflict_set (t0 :: l) conflict_set in
                       x0 (let pr1,_ = x in pr1) s0' mc0' __)))))))
         | Unsat core ->
           Coq_tableau_clause_1_graph_equation_2 ((let pr1,_ = x in pr1),
             (let pr1,_ = let _,pr2 = x in pr2 in pr1), core,
             (let _,pr2 = let _,pr2 = x in pr2 in pr2))))
    in fix_F (a,(s0,mc0))

  (** val tableau_elim :
      (Assumptions.t -> CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> __
      -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> __
      -> __ -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t
      -> Lclauses.t -> Lclauses.t list -> Tree.t list -> __ -> __ ->
      (Assumptions.t -> 'a1) -> __ -> __ -> 'a1) -> (Assumptions.t ->
      CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
      int -> Lit.t -> Assumptions.t -> Derivation.t -> __ -> 'a1 -> __ ->
      (Assumptions.t -> 'a1) -> __ -> __ -> 'a1) -> Assumptions.t ->
      CplSolver.t -> Mchain.t -> 'a1 **)

  let tableau_elim tableau_clause_1_graph_equation_2 tableau_clause_1_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_2 a s0 mc0 =
    tableau_graph_mut (fun _ _ _ _ x -> x __) (fun _ _ _ _ _ _ x -> x __)
      tableau_clause_1_graph_equation_2
      tableau_clause_1_clause_2_graph_equation_1
      (fun _ _ _ _ _ _ _ _ x _ x0 -> x0 __ x)
      tableau_clause_1_clause_2_clause_2_graph_equation_1
      (fun a0 s1 v _ mc1 l0 mc2 c d jump_core jump_deriv _ _ ->
      tableau_clause_1_clause_2_clause_2_graph_equation_2 a0 s1 v __ mc1 l0
        mc2 c d jump_core jump_deriv __)
      a s0 mc0 (tableau a s0 mc0) (tableau_graph_correct a s0 mc0)

  (** val coq_FunctionalElimination_tableau :
      (Assumptions.t -> CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> __
      -> __) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> __ ->
      __ -> __) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      Lclauses.t -> Lclauses.t list -> Tree.t list -> __ -> __ ->
      (Assumptions.t -> __) -> __ -> __ -> __) -> (Assumptions.t ->
      CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
      int -> Lit.t -> Assumptions.t -> Derivation.t -> __ -> __ -> __ ->
      (Assumptions.t -> __) -> __ -> __ -> __) -> Assumptions.t ->
      CplSolver.t -> Mchain.t -> __ **)

  let coq_FunctionalElimination_tableau =
    tableau_elim

  (** val coq_FunctionalInduction_tableau :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t)
      coq_FunctionalInduction **)

  let coq_FunctionalInduction_tableau =
    Obj.magic tableau_graph_correct

  (** val solve_mchain : Mchain.t -> Solution.t **)

  let solve_mchain mc0 =
    let cpls0 = first_cpls mc0 in
    let s0 = make_with_clauses cpls0 in tableau [] s0 mc0

  (** val solve_fml : Fml.t -> Solution.t **)

  let solve_fml phi =
    apply (apply (apply (apply phi from_fml) from_nnf) from_mcnf) solve_mchain
 end

module NoModel =
 struct
  module JumpSolution =
   struct
    type t =
    | Sat
    | Unsat of int * Assumptions.t

    (** val t_rect : 'a1 -> (int -> Assumptions.t -> 'a1) -> t -> 'a1 **)

    let t_rect sat unsat = function
    | Sat -> sat
    | Unsat (c, core) -> unsat c core

    (** val t_rec : 'a1 -> (int -> Assumptions.t -> 'a1) -> t -> 'a1 **)

    let t_rec sat unsat = function
    | Sat -> sat
    | Unsat (c, core) -> unsat c core
   end

  module Solution =
   struct
    type t =
    | Sat
    | Unsat of Assumptions.t

    (** val t_rect : 'a1 -> (Assumptions.t -> 'a1) -> t -> 'a1 **)

    let t_rect sat unsat = function
    | Sat -> sat
    | Unsat core -> unsat core

    (** val t_rec : 'a1 -> (Assumptions.t -> 'a1) -> t -> 'a1 **)

    let t_rec sat unsat = function
    | Sat -> sat
    | Unsat core -> unsat core

    (** val is_sat : t -> bool **)

    let is_sat = function
    | Sat -> true
    | Unsat _ -> false
   end

  (** val tableau_jumps_clause_2_clause_2 :
      t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      Solution.t -> (t -> Lclauses.t -> Mchain.t -> (Assumptions.t ->
      Solution.t) -> __ -> JumpSolution.t) -> JumpSolution.t **)

  let tableau_jumps_clause_2_clause_2 v cpls0 boxes0 c _ dias' mc1 next_tableau0 refine tableau_jumps0 =
    match refine with
    | Solution.Sat ->
      tableau_jumps0 v { cpls = cpls0; boxes = boxes0; dias = dias' } mc1
        next_tableau0 __
    | Solution.Unsat core -> JumpSolution.Unsat (c, core)

  (** val tableau_jumps_clause_2 :
      t -> CplClause.t list -> BoxClause.t list -> int -> bool -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) -> (t ->
      Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) -> __ ->
      JumpSolution.t) -> JumpSolution.t **)

  let tableau_jumps_clause_2 v cpls0 boxes0 c refine d dias' mc1 next_tableau0 tableau_jumps0 =
    if refine
    then (match let fired_boxes =
                  apply
                    (apply boxes0
                      (filter (fun pat -> let (a, _) = pat in forces_atm v a)))
                    (map snd)
                in
                next_tableau0 (d :: fired_boxes) with
          | Solution.Sat ->
            tableau_jumps0 v { cpls = cpls0; boxes = boxes0; dias = dias' }
              mc1 next_tableau0 __
          | Solution.Unsat core -> JumpSolution.Unsat (c, core))
    else tableau_jumps0 v { cpls = cpls0; boxes = boxes0; dias = dias' } mc1
           next_tableau0 __

  (** val tableau_jumps_functional :
      t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) -> (t ->
      Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) -> __ ->
      JumpSolution.t) -> JumpSolution.t **)

  let tableau_jumps_functional v l0 mc1 next_tableau0 tableau_jumps0 =
    let { cpls = cpls0; boxes = boxes0; dias = dias0 } = l0 in
    (match dias0 with
     | [] -> JumpSolution.Sat
     | t0 :: l ->
       let (n, t1) = t0 in
       if forces_atm v n
       then (match let fired_boxes =
                     apply
                       (apply boxes0
                         (filter (fun pat ->
                           let (a, _) = pat in forces_atm v a)))
                       (map snd)
                   in
                   next_tableau0 (t1 :: fired_boxes) with
             | Solution.Sat ->
               tableau_jumps0 v { cpls = cpls0; boxes = boxes0; dias = l }
                 mc1 next_tableau0 __
             | Solution.Unsat core -> JumpSolution.Unsat (n, core))
       else tableau_jumps0 v { cpls = cpls0; boxes = boxes0; dias = l } mc1
              next_tableau0 __)

  (** val tableau_jumps :
      t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      JumpSolution.t **)

  let tableau_jumps a a0 a1 b =
    let rec fix_F x =
      let v = let pr1,_ = x in pr1 in
      let next_tableau0 =
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
                     next_tableau0 (t1 :: fired_boxes) with
               | Solution.Sat ->
                 let y = v,({ cpls = cpls0; boxes = boxes0; dias =
                   l },((let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2
                         in
                         pr1),next_tableau0))
                 in
                 fix_F y
               | Solution.Unsat core -> JumpSolution.Unsat (n, core))
         else let y = v,({ cpls = cpls0; boxes = boxes0; dias =
                l },((let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in
                      pr1),next_tableau0))
              in
              fix_F y)
    in fix_F (a,(a0,(a1,b)))

  (** val tableau_jumps_unfold_clause_2_clause_2 :
      t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      Solution.t -> JumpSolution.t **)

  let tableau_jumps_unfold_clause_2_clause_2 v cpls0 boxes0 c _ dias' mc1 next_tableau0 = function
  | Solution.Sat ->
    tableau_jumps v { cpls = cpls0; boxes = boxes0; dias = dias' } mc1
      next_tableau0
  | Solution.Unsat core -> JumpSolution.Unsat (c, core)

  (** val tableau_jumps_unfold_clause_2 :
      t -> CplClause.t list -> BoxClause.t list -> int -> bool -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      JumpSolution.t **)

  let tableau_jumps_unfold_clause_2 v cpls0 boxes0 c refine d dias' mc1 next_tableau0 =
    if refine
    then (match let fired_boxes =
                  apply
                    (apply boxes0
                      (filter (fun pat -> let (a, _) = pat in forces_atm v a)))
                    (map snd)
                in
                next_tableau0 (d :: fired_boxes) with
          | Solution.Sat ->
            tableau_jumps v { cpls = cpls0; boxes = boxes0; dias = dias' }
              mc1 next_tableau0
          | Solution.Unsat core -> JumpSolution.Unsat (c, core))
    else tableau_jumps v { cpls = cpls0; boxes = boxes0; dias = dias' } mc1
           next_tableau0

  (** val tableau_jumps_unfold :
      t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      JumpSolution.t **)

  let tableau_jumps_unfold v l0 mc1 next_tableau0 =
    let { cpls = cpls0; boxes = boxes0; dias = dias0 } = l0 in
    (match dias0 with
     | [] -> JumpSolution.Sat
     | t0 :: l ->
       let (n, t1) = t0 in
       if forces_atm v n
       then (match let fired_boxes =
                     apply
                       (apply boxes0
                         (filter (fun pat ->
                           let (a, _) = pat in forces_atm v a)))
                       (map snd)
                   in
                   next_tableau0 (t1 :: fired_boxes) with
             | Solution.Sat ->
               tableau_jumps v { cpls = cpls0; boxes = boxes0; dias = l } mc1
                 next_tableau0
             | Solution.Unsat core -> JumpSolution.Unsat (n, core))
       else tableau_jumps v { cpls = cpls0; boxes = boxes0; dias = l } mc1
              next_tableau0)

  type tableau_jumps_graph =
  | Coq_tableau_jumps_graph_equation_1 of t * CplClause.t list
     * BoxClause.t list * Mchain.t * (Assumptions.t -> Solution.t)
  | Coq_tableau_jumps_graph_refinement_2 of t * CplClause.t list
     * BoxClause.t list * int * Lit.t * DiaClause.t list * Mchain.t
     * (Assumptions.t -> Solution.t) * tableau_jumps_clause_2_graph
  and tableau_jumps_clause_2_graph =
  | Coq_tableau_jumps_clause_2_graph_refinement_1 of t * CplClause.t list
     * BoxClause.t list * int * Lit.t * DiaClause.t list * Mchain.t
     * (Assumptions.t -> Solution.t) * tableau_jumps_clause_2_clause_2_graph
  | Coq_tableau_jumps_clause_2_graph_equation_2 of t * CplClause.t list
     * BoxClause.t list * int * Lit.t * DiaClause.t list * Mchain.t
     * (Assumptions.t -> Solution.t) * tableau_jumps_graph
  and tableau_jumps_clause_2_clause_2_graph =
  | Coq_tableau_jumps_clause_2_clause_2_graph_equation_1 of t
     * CplClause.t list * BoxClause.t list * int * Lit.t * DiaClause.t list
     * Mchain.t * (Assumptions.t -> Solution.t) * tableau_jumps_graph
  | Coq_tableau_jumps_clause_2_clause_2_graph_equation_2 of t
     * CplClause.t list * BoxClause.t list * int * Lit.t * DiaClause.t list
     * Mchain.t * (Assumptions.t -> Solution.t) * Assumptions.t

  (** val tableau_jumps_graph_mut :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> tableau_jumps_clause_2_graph -> 'a2 ->
      'a1) -> (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_clause_2_clause_2_graph -> 'a3 -> 'a2) -> (t ->
      CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
      list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_graph -> 'a1 -> 'a2) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> tableau_jumps_graph -> 'a1 -> 'a3) ->
      (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      Assumptions.t -> 'a3) -> t -> Lclauses.t -> Mchain.t -> (Assumptions.t
      -> Solution.t) -> JumpSolution.t -> tableau_jumps_graph -> 'a1 **)

  let tableau_jumps_graph_mut tableau_jumps_graph_equation_1 tableau_jumps_graph_refinement_2 tableau_jumps_clause_2_graph_refinement_1 tableau_jumps_clause_2_graph_equation_2 tableau_jumps_clause_2_clause_2_graph_equation_1 tableau_jumps_clause_2_clause_2_graph_equation_2 =
    let rec f _ _ _ _ _ = function
    | Coq_tableau_jumps_graph_equation_1 (v0, cpls0, boxes0, mc2,
                                          next_tableau0) ->
      tableau_jumps_graph_equation_1 v0 cpls0 boxes0 mc2 next_tableau0
    | Coq_tableau_jumps_graph_refinement_2 (v0, cpls0, boxes0, c, d, dias',
                                            mc2, next_tableau0, hind) ->
      tableau_jumps_graph_refinement_2 v0 cpls0 boxes0 c d dias' mc2
        next_tableau0 hind
        (f0 v0 cpls0 boxes0 c (forces_atm v0 c) d dias' mc2 next_tableau0
          (if forces_atm v0 c
           then (match let fired_boxes =
                         apply
                           (apply boxes0
                             (filter (fun pat ->
                               let (a, _) = pat in forces_atm v0 a)))
                           (map snd)
                       in
                       next_tableau0 (d :: fired_boxes) with
                 | Solution.Sat ->
                   tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                     dias' } mc2 next_tableau0
                 | Solution.Unsat core -> JumpSolution.Unsat (c, core))
           else tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                  dias' } mc2 next_tableau0)
          hind)
    and f0 _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_graph_refinement_1 (v0, cpls0, boxes0, c0,
                                                     d0, dias'0, mc2,
                                                     next_tableau0, hind) ->
      tableau_jumps_clause_2_graph_refinement_1 v0 cpls0 boxes0 c0 d0 dias'0
        mc2 next_tableau0 hind
        (f1 v0 cpls0 boxes0 c0 d0 dias'0 mc2 next_tableau0
          (let fired_boxes =
             apply
               (apply boxes0
                 (filter (fun pat -> let (a, _) = pat in forces_atm v0 a)))
               (map snd)
           in
           next_tableau0 (d0 :: fired_boxes))
          (match let fired_boxes =
                   apply
                     (apply boxes0
                       (filter (fun pat ->
                         let (a, _) = pat in forces_atm v0 a)))
                     (map snd)
                 in
                 next_tableau0 (d0 :: fired_boxes) with
           | Solution.Sat ->
             tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
               mc2 next_tableau0
           | Solution.Unsat core -> JumpSolution.Unsat (c0, core))
          hind)
    | Coq_tableau_jumps_clause_2_graph_equation_2 (v0, cpls0, boxes0, c0, d0,
                                                   dias'0, mc2,
                                                   next_tableau0, hind) ->
      tableau_jumps_clause_2_graph_equation_2 v0 cpls0 boxes0 c0 d0 dias'0
        mc2 next_tableau0 hind
        (f v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 } mc2
          next_tableau0
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 next_tableau0)
          hind)
    and f1 _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_clause_2_graph_equation_1 (v0, cpls0,
                                                            boxes0, c0, d0,
                                                            dias'0, mc2,
                                                            next_tableau0,
                                                            hind) ->
      tableau_jumps_clause_2_clause_2_graph_equation_1 v0 cpls0 boxes0 c0 d0
        dias'0 mc2 next_tableau0 hind
        (f v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 } mc2
          next_tableau0
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 next_tableau0)
          hind)
    | Coq_tableau_jumps_clause_2_clause_2_graph_equation_2 (v0, cpls0,
                                                            boxes0, c0, d0,
                                                            dias'0, mc2,
                                                            next_tableau0,
                                                            core) ->
      tableau_jumps_clause_2_clause_2_graph_equation_2 v0 cpls0 boxes0 c0 d0
        dias'0 mc2 next_tableau0 core
    in f

  (** val tableau_jumps_clause_2_graph_mut :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> tableau_jumps_clause_2_graph -> 'a2 ->
      'a1) -> (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_clause_2_clause_2_graph -> 'a3 -> 'a2) -> (t ->
      CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
      list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_graph -> 'a1 -> 'a2) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> tableau_jumps_graph -> 'a1 -> 'a3) ->
      (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      Assumptions.t -> 'a3) -> t -> CplClause.t list -> BoxClause.t list ->
      int -> bool -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t
      -> Solution.t) -> JumpSolution.t -> tableau_jumps_clause_2_graph -> 'a2 **)

  let tableau_jumps_clause_2_graph_mut tableau_jumps_graph_equation_1 tableau_jumps_graph_refinement_2 tableau_jumps_clause_2_graph_refinement_1 tableau_jumps_clause_2_graph_equation_2 tableau_jumps_clause_2_clause_2_graph_equation_1 tableau_jumps_clause_2_clause_2_graph_equation_2 =
    let rec f _ _ _ _ _ = function
    | Coq_tableau_jumps_graph_equation_1 (v0, cpls0, boxes0, mc2,
                                          next_tableau0) ->
      tableau_jumps_graph_equation_1 v0 cpls0 boxes0 mc2 next_tableau0
    | Coq_tableau_jumps_graph_refinement_2 (v0, cpls0, boxes0, c, d, dias',
                                            mc2, next_tableau0, hind) ->
      tableau_jumps_graph_refinement_2 v0 cpls0 boxes0 c d dias' mc2
        next_tableau0 hind
        (f0 v0 cpls0 boxes0 c (forces_atm v0 c) d dias' mc2 next_tableau0
          (if forces_atm v0 c
           then (match let fired_boxes =
                         apply
                           (apply boxes0
                             (filter (fun pat ->
                               let (a, _) = pat in forces_atm v0 a)))
                           (map snd)
                       in
                       next_tableau0 (d :: fired_boxes) with
                 | Solution.Sat ->
                   tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                     dias' } mc2 next_tableau0
                 | Solution.Unsat core -> JumpSolution.Unsat (c, core))
           else tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                  dias' } mc2 next_tableau0)
          hind)
    and f0 _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_graph_refinement_1 (v0, cpls0, boxes0, c0,
                                                     d0, dias'0, mc2,
                                                     next_tableau0, hind) ->
      tableau_jumps_clause_2_graph_refinement_1 v0 cpls0 boxes0 c0 d0 dias'0
        mc2 next_tableau0 hind
        (f1 v0 cpls0 boxes0 c0 d0 dias'0 mc2 next_tableau0
          (let fired_boxes =
             apply
               (apply boxes0
                 (filter (fun pat -> let (a, _) = pat in forces_atm v0 a)))
               (map snd)
           in
           next_tableau0 (d0 :: fired_boxes))
          (match let fired_boxes =
                   apply
                     (apply boxes0
                       (filter (fun pat ->
                         let (a, _) = pat in forces_atm v0 a)))
                     (map snd)
                 in
                 next_tableau0 (d0 :: fired_boxes) with
           | Solution.Sat ->
             tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
               mc2 next_tableau0
           | Solution.Unsat core -> JumpSolution.Unsat (c0, core))
          hind)
    | Coq_tableau_jumps_clause_2_graph_equation_2 (v0, cpls0, boxes0, c0, d0,
                                                   dias'0, mc2,
                                                   next_tableau0, hind) ->
      tableau_jumps_clause_2_graph_equation_2 v0 cpls0 boxes0 c0 d0 dias'0
        mc2 next_tableau0 hind
        (f v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 } mc2
          next_tableau0
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 next_tableau0)
          hind)
    and f1 _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_clause_2_graph_equation_1 (v0, cpls0,
                                                            boxes0, c0, d0,
                                                            dias'0, mc2,
                                                            next_tableau0,
                                                            hind) ->
      tableau_jumps_clause_2_clause_2_graph_equation_1 v0 cpls0 boxes0 c0 d0
        dias'0 mc2 next_tableau0 hind
        (f v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 } mc2
          next_tableau0
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 next_tableau0)
          hind)
    | Coq_tableau_jumps_clause_2_clause_2_graph_equation_2 (v0, cpls0,
                                                            boxes0, c0, d0,
                                                            dias'0, mc2,
                                                            next_tableau0,
                                                            core) ->
      tableau_jumps_clause_2_clause_2_graph_equation_2 v0 cpls0 boxes0 c0 d0
        dias'0 mc2 next_tableau0 core
    in f0

  (** val tableau_jumps_clause_2_clause_2_graph_mut :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> tableau_jumps_clause_2_graph -> 'a2 ->
      'a1) -> (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_clause_2_clause_2_graph -> 'a3 -> 'a2) -> (t ->
      CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
      list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_graph -> 'a1 -> 'a2) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> tableau_jumps_graph -> 'a1 -> 'a3) ->
      (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      Assumptions.t -> 'a3) -> t -> CplClause.t list -> BoxClause.t list ->
      int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
      Solution.t) -> Solution.t -> JumpSolution.t ->
      tableau_jumps_clause_2_clause_2_graph -> 'a3 **)

  let tableau_jumps_clause_2_clause_2_graph_mut tableau_jumps_graph_equation_1 tableau_jumps_graph_refinement_2 tableau_jumps_clause_2_graph_refinement_1 tableau_jumps_clause_2_graph_equation_2 tableau_jumps_clause_2_clause_2_graph_equation_1 tableau_jumps_clause_2_clause_2_graph_equation_2 =
    let rec f _ _ _ _ _ = function
    | Coq_tableau_jumps_graph_equation_1 (v0, cpls0, boxes0, mc2,
                                          next_tableau0) ->
      tableau_jumps_graph_equation_1 v0 cpls0 boxes0 mc2 next_tableau0
    | Coq_tableau_jumps_graph_refinement_2 (v0, cpls0, boxes0, c, d, dias',
                                            mc2, next_tableau0, hind) ->
      tableau_jumps_graph_refinement_2 v0 cpls0 boxes0 c d dias' mc2
        next_tableau0 hind
        (f0 v0 cpls0 boxes0 c (forces_atm v0 c) d dias' mc2 next_tableau0
          (if forces_atm v0 c
           then (match let fired_boxes =
                         apply
                           (apply boxes0
                             (filter (fun pat ->
                               let (a, _) = pat in forces_atm v0 a)))
                           (map snd)
                       in
                       next_tableau0 (d :: fired_boxes) with
                 | Solution.Sat ->
                   tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                     dias' } mc2 next_tableau0
                 | Solution.Unsat core -> JumpSolution.Unsat (c, core))
           else tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias =
                  dias' } mc2 next_tableau0)
          hind)
    and f0 _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_graph_refinement_1 (v0, cpls0, boxes0, c0,
                                                     d0, dias'0, mc2,
                                                     next_tableau0, hind) ->
      tableau_jumps_clause_2_graph_refinement_1 v0 cpls0 boxes0 c0 d0 dias'0
        mc2 next_tableau0 hind
        (f1 v0 cpls0 boxes0 c0 d0 dias'0 mc2 next_tableau0
          (let fired_boxes =
             apply
               (apply boxes0
                 (filter (fun pat -> let (a, _) = pat in forces_atm v0 a)))
               (map snd)
           in
           next_tableau0 (d0 :: fired_boxes))
          (match let fired_boxes =
                   apply
                     (apply boxes0
                       (filter (fun pat ->
                         let (a, _) = pat in forces_atm v0 a)))
                     (map snd)
                 in
                 next_tableau0 (d0 :: fired_boxes) with
           | Solution.Sat ->
             tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
               mc2 next_tableau0
           | Solution.Unsat core -> JumpSolution.Unsat (c0, core))
          hind)
    | Coq_tableau_jumps_clause_2_graph_equation_2 (v0, cpls0, boxes0, c0, d0,
                                                   dias'0, mc2,
                                                   next_tableau0, hind) ->
      tableau_jumps_clause_2_graph_equation_2 v0 cpls0 boxes0 c0 d0 dias'0
        mc2 next_tableau0 hind
        (f v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 } mc2
          next_tableau0
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 next_tableau0)
          hind)
    and f1 _ _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_jumps_clause_2_clause_2_graph_equation_1 (v0, cpls0,
                                                            boxes0, c0, d0,
                                                            dias'0, mc2,
                                                            next_tableau0,
                                                            hind) ->
      tableau_jumps_clause_2_clause_2_graph_equation_1 v0 cpls0 boxes0 c0 d0
        dias'0 mc2 next_tableau0 hind
        (f v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 } mc2
          next_tableau0
          (tableau_jumps v0 { cpls = cpls0; boxes = boxes0; dias = dias'0 }
            mc2 next_tableau0)
          hind)
    | Coq_tableau_jumps_clause_2_clause_2_graph_equation_2 (v0, cpls0,
                                                            boxes0, c0, d0,
                                                            dias'0, mc2,
                                                            next_tableau0,
                                                            core) ->
      tableau_jumps_clause_2_clause_2_graph_equation_2 v0 cpls0 boxes0 c0 d0
        dias'0 mc2 next_tableau0 core
    in f1

  (** val tableau_jumps_graph_rect :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> tableau_jumps_clause_2_graph -> 'a2 ->
      'a1) -> (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_clause_2_clause_2_graph -> 'a3 -> 'a2) -> (t ->
      CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
      list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_graph -> 'a1 -> 'a2) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> tableau_jumps_graph -> 'a1 -> 'a3) ->
      (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      Assumptions.t -> 'a3) -> t -> Lclauses.t -> Mchain.t -> (Assumptions.t
      -> Solution.t) -> JumpSolution.t -> tableau_jumps_graph -> 'a1 **)

  let tableau_jumps_graph_rect =
    tableau_jumps_graph_mut

  (** val tableau_jumps_graph_correct :
      t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      tableau_jumps_graph **)

  let tableau_jumps_graph_correct v l0 mc1 next_tableau0 =
    let rec fix_F x =
      let x1 = let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr1 in
      let x2 = let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2 in
      let x0 = fun a a0 a1 b -> let y = a,(a0,(a1,b)) in (fun _ -> fix_F y) in
      let { cpls = cpls0; boxes = boxes0; dias = dias0 } =
        let pr1,_ = let _,pr2 = x in pr2 in pr1
      in
      (match dias0 with
       | [] ->
         Coq_tableau_jumps_graph_equation_1 ((let pr1,_ = x in pr1), cpls0,
           boxes0, x1, x2)
       | t0 :: l ->
         let (n, t1) = t0 in
         Coq_tableau_jumps_graph_refinement_2 ((let pr1,_ = x in pr1), cpls0,
         boxes0, n, t1, l, x1, x2,
         (let refine = forces_atm (let pr1,_ = x in pr1) n in
          if refine
          then Coq_tableau_jumps_clause_2_graph_refinement_1
                 ((let pr1,_ = x in pr1), cpls0, boxes0, n, t1, l, x1, x2,
                 (let refine0 =
                    let fired_boxes =
                      apply
                        (apply boxes0
                          (filter (fun pat ->
                            let (a, _) = pat in
                            forces_atm (let pr1,_ = x in pr1) a)))
                        (map snd)
                    in
                    x2 (t1 :: fired_boxes)
                  in
                  match refine0 with
                  | Solution.Sat ->
                    Coq_tableau_jumps_clause_2_clause_2_graph_equation_1
                      ((let pr1,_ = x in pr1), cpls0, boxes0, n, t1, l, x1,
                      x2,
                      (x0 (let pr1,_ = x in pr1) { cpls = cpls0; boxes =
                        boxes0; dias = l } x1 x2 __))
                  | Solution.Unsat core ->
                    Coq_tableau_jumps_clause_2_clause_2_graph_equation_2
                      ((let pr1,_ = x in pr1), cpls0, boxes0, n, t1, l, x1,
                      x2, core)))
          else Coq_tableau_jumps_clause_2_graph_equation_2
                 ((let pr1,_ = x in pr1), cpls0, boxes0, n, t1, l, x1, x2,
                 (x0 (let pr1,_ = x in pr1) { cpls = cpls0; boxes = boxes0;
                   dias = l } x1 x2 __)))))
    in fix_F (v,(l0,(mc1,next_tableau0)))

  (** val tableau_jumps_elim :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> 'a1 -> __ -> 'a1) -> (t -> CplClause.t
      list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list ->
      Mchain.t -> (Assumptions.t -> Solution.t) -> 'a1 -> __ -> __ -> 'a1) ->
      (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      Assumptions.t -> __ -> __ -> 'a1) -> t -> Lclauses.t -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> 'a1 **)

  let tableau_jumps_elim tableau_jumps_graph_equation_1 tableau_jumps_clause_2_graph_equation_2 tableau_jumps_clause_2_clause_2_graph_equation_1 tableau_jumps_clause_2_clause_2_graph_equation_2 v l0 mc1 next_tableau0 =
    tableau_jumps_graph_mut tableau_jumps_graph_equation_1
      (fun _ _ _ _ _ _ _ _ _ x -> x __) (fun _ _ _ _ _ _ _ _ _ x -> x __)
      (fun v0 cpls0 boxes0 c d dias' mc0 next_tableau1 _ ->
      tableau_jumps_clause_2_graph_equation_2 v0 cpls0 boxes0 c d dias' mc0
        next_tableau1)
      (fun v0 cpls0 boxes0 c d dias' mc0 next_tableau1 _ ->
      tableau_jumps_clause_2_clause_2_graph_equation_1 v0 cpls0 boxes0 c d
        dias' mc0 next_tableau1)
      tableau_jumps_clause_2_clause_2_graph_equation_2 v l0 mc1 next_tableau0
      (tableau_jumps v l0 mc1 next_tableau0)
      (tableau_jumps_graph_correct v l0 mc1 next_tableau0)

  (** val coq_FunctionalElimination_tableau_jumps :
      (t -> CplClause.t list -> BoxClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> __) -> (t -> CplClause.t list ->
      BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> __ -> __ -> __) -> (t -> CplClause.t
      list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list ->
      Mchain.t -> (Assumptions.t -> Solution.t) -> __ -> __ -> __ -> __) ->
      (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
      DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      Assumptions.t -> __ -> __ -> __) -> t -> Lclauses.t -> Mchain.t ->
      (Assumptions.t -> Solution.t) -> __ **)

  let coq_FunctionalElimination_tableau_jumps =
    tableau_jumps_elim

  (** val coq_FunctionalInduction_tableau_jumps :
      (t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) ->
      JumpSolution.t) coq_FunctionalInduction **)

  let coq_FunctionalInduction_tableau_jumps =
    Obj.magic tableau_jumps_graph_correct

  (** val tableau_clause_1_clause_2_clause_2 :
      Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> CplSolver.t -> Mchain.t -> __ ->
      Solution.t) -> JumpSolution.t -> Solution.t **)

  let tableau_clause_1_clause_2_clause_2 a s0 v _ l0 mc1 tableau0 = function
  | JumpSolution.Sat -> Solution.Sat
  | JumpSolution.Unsat (c, core) ->
    let conflict_set = conflict_set_of (l0 :: mc1) v c core in
    let s0' = CplSolver.add_conflict_set s0 conflict_set in
    let mc0' = add_conflict_set (l0 :: mc1) conflict_set in
    tableau0 a s0' mc0' __

  (** val tableau_clause_1_clause_2 :
      Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t list ->
      (Assumptions.t -> CplSolver.t -> Mchain.t -> __ -> Solution.t) ->
      Solution.t **)

  let tableau_clause_1_clause_2 a s0 v _ refine tableau0 =
    match refine with
    | [] -> Solution.Sat
    | t0 :: l ->
      (match inspect
               (tableau_jumps v t0 l (fun a' ->
                 tableau0 a' (make_with_clauses (first_cpls l)) l __)) with
       | JumpSolution.Sat -> Solution.Sat
       | JumpSolution.Unsat (c, core) ->
         let conflict_set = conflict_set_of (t0 :: l) v c core in
         let s0' = CplSolver.add_conflict_set s0 conflict_set in
         let mc0' = add_conflict_set (t0 :: l) conflict_set in
         tableau0 a s0' mc0' __)

  (** val tableau_clause_1 :
      Assumptions.t -> CplSolver.t -> CplSolution.t -> Mchain.t ->
      (Assumptions.t -> CplSolver.t -> Mchain.t -> __ -> Solution.t) ->
      Solution.t **)

  let tableau_clause_1 a s0 refine mc0 tableau0 =
    match refine with
    | Sat v ->
      (match mc0 with
       | [] -> Solution.Sat
       | t0 :: l ->
         (match inspect
                  (tableau_jumps v t0 l (fun a' ->
                    tableau0 a' (make_with_clauses (first_cpls l)) l __)) with
          | JumpSolution.Sat -> Solution.Sat
          | JumpSolution.Unsat (c, core) ->
            let conflict_set = conflict_set_of (t0 :: l) v c core in
            let s0' = CplSolver.add_conflict_set s0 conflict_set in
            let mc0' = add_conflict_set (t0 :: l) conflict_set in
            tableau0 a s0' mc0' __))
    | Unsat core -> Solution.Unsat core

  (** val tableau_functional :
      Assumptions.t -> CplSolver.t -> Mchain.t -> (Assumptions.t ->
      CplSolver.t -> Mchain.t -> __ -> Solution.t) -> Solution.t **)

  let tableau_functional a s0 mc0 tableau0 =
    match inspect (solve_with_assumptions s0 a) with
    | Sat v ->
      (match mc0 with
       | [] -> Solution.Sat
       | t0 :: l ->
         (match inspect
                  (tableau_jumps v t0 l (fun a' ->
                    tableau0 a' (make_with_clauses (first_cpls l)) l __)) with
          | JumpSolution.Sat -> Solution.Sat
          | JumpSolution.Unsat (c, core) ->
            let conflict_set = conflict_set_of (t0 :: l) v c core in
            let s0' = CplSolver.add_conflict_set s0 conflict_set in
            let mc0' = add_conflict_set (t0 :: l) conflict_set in
            tableau0 a s0' mc0' __))
    | Unsat core -> Solution.Unsat core

  (** val tableau : Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t **)

  let tableau a a0 b =
    let rec fix_F x =
      let a1 = let pr1,_ = x in pr1 in
      let s0 = let pr1,_ = let _,pr2 = x in pr2 in pr1 in
      let tableau0 = fun a2 a3 b0 -> let y = a2,(a3,b0) in (fun _ -> fix_F y)
      in
      (match inspect (solve_with_assumptions s0 a1) with
       | Sat v ->
         (match let _,pr2 = let _,pr2 = x in pr2 in pr2 with
          | [] -> Solution.Sat
          | t0 :: l ->
            (match inspect
                     (tableau_jumps v t0 l (fun a' ->
                       tableau0 a' (make_with_clauses (first_cpls l)) l __)) with
             | JumpSolution.Sat -> Solution.Sat
             | JumpSolution.Unsat (c, core) ->
               let conflict_set = conflict_set_of (t0 :: l) v c core in
               let s0' = CplSolver.add_conflict_set s0 conflict_set in
               let mc0' = add_conflict_set (t0 :: l) conflict_set in
               tableau0 a1 s0' mc0' __))
       | Unsat core -> Solution.Unsat core)
    in fix_F (a,(a0,b))

  (** val tableau_unfold_clause_1_clause_2_clause_2 :
      Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> JumpSolution.t -> Solution.t **)

  let tableau_unfold_clause_1_clause_2_clause_2 a s0 v _ l0 mc1 = function
  | JumpSolution.Sat -> Solution.Sat
  | JumpSolution.Unsat (c, core) ->
    let conflict_set = conflict_set_of (l0 :: mc1) v c core in
    let s0' = CplSolver.add_conflict_set s0 conflict_set in
    let mc0' = add_conflict_set (l0 :: mc1) conflict_set in tableau a s0' mc0'

  (** val tableau_unfold_clause_1_clause_2 :
      Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t list ->
      Solution.t **)

  let tableau_unfold_clause_1_clause_2 a s0 v _ = function
  | [] -> Solution.Sat
  | t0 :: l ->
    (match inspect
             (tableau_jumps v t0 l (fun a' ->
               tableau a' (make_with_clauses (first_cpls l)) l)) with
     | JumpSolution.Sat -> Solution.Sat
     | JumpSolution.Unsat (c, core) ->
       let conflict_set = conflict_set_of (t0 :: l) v c core in
       let s0' = CplSolver.add_conflict_set s0 conflict_set in
       let mc0' = add_conflict_set (t0 :: l) conflict_set in
       tableau a s0' mc0')

  (** val tableau_unfold_clause_1 :
      Assumptions.t -> CplSolver.t -> CplSolution.t -> Mchain.t -> Solution.t **)

  let tableau_unfold_clause_1 a s0 refine mc0 =
    match refine with
    | Sat v ->
      (match mc0 with
       | [] -> Solution.Sat
       | t0 :: l ->
         (match inspect
                  (tableau_jumps v t0 l (fun a' ->
                    tableau a' (make_with_clauses (first_cpls l)) l)) with
          | JumpSolution.Sat -> Solution.Sat
          | JumpSolution.Unsat (c, core) ->
            let conflict_set = conflict_set_of (t0 :: l) v c core in
            let s0' = CplSolver.add_conflict_set s0 conflict_set in
            let mc0' = add_conflict_set (t0 :: l) conflict_set in
            tableau a s0' mc0'))
    | Unsat core -> Solution.Unsat core

  (** val tableau_unfold :
      Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t **)

  let tableau_unfold a s0 mc0 =
    match inspect (solve_with_assumptions s0 a) with
    | Sat v ->
      (match mc0 with
       | [] -> Solution.Sat
       | t0 :: l ->
         (match inspect
                  (tableau_jumps v t0 l (fun a' ->
                    tableau a' (make_with_clauses (first_cpls l)) l)) with
          | JumpSolution.Sat -> Solution.Sat
          | JumpSolution.Unsat (c, core) ->
            let conflict_set = conflict_set_of (t0 :: l) v c core in
            let s0' = CplSolver.add_conflict_set s0 conflict_set in
            let mc0' = add_conflict_set (t0 :: l) conflict_set in
            tableau a s0' mc0'))
    | Unsat core -> Solution.Unsat core

  type tableau_graph =
  | Coq_tableau_graph_refinement_1 of Assumptions.t * CplSolver.t * Mchain.t
     * tableau_clause_1_graph
  and tableau_clause_1_graph =
  | Coq_tableau_clause_1_graph_refinement_1 of Assumptions.t * CplSolver.t
     * t * Mchain.t * tableau_clause_1_clause_2_graph
  | Coq_tableau_clause_1_graph_equation_2 of Assumptions.t * CplSolver.t
     * Assumptions.t * Mchain.t
  and tableau_clause_1_clause_2_graph =
  | Coq_tableau_clause_1_clause_2_graph_equation_1 of Assumptions.t
     * CplSolver.t * t * Mchain.t
  | Coq_tableau_clause_1_clause_2_graph_refinement_2 of Assumptions.t
     * CplSolver.t * t * Mchain.t * Lclauses.t * Lclauses.t list
     * (Assumptions.t -> tableau_graph)
     * tableau_clause_1_clause_2_clause_2_graph
  and tableau_clause_1_clause_2_clause_2_graph =
  | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1 of Assumptions.t
     * CplSolver.t * t * Mchain.t * Lclauses.t * Lclauses.t list
  | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2 of Assumptions.t
     * CplSolver.t * t * Mchain.t * Lclauses.t * Lclauses.t list * int
     * Assumptions.t * tableau_graph

  (** val tableau_graph_mut :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
      'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
      CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> tableau_graph) -> (Assumptions.t
      -> 'a1) -> tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> __ -> 'a4) -> (Assumptions.t -> CplSolver.t -> t ->
      __ -> Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Assumptions.t
      -> __ -> tableau_graph -> 'a1 -> 'a4) -> Assumptions.t -> CplSolver.t
      -> Mchain.t -> Solution.t -> tableau_graph -> 'a1 **)

  let tableau_graph_mut tableau_graph_refinement_1 tableau_clause_1_graph_refinement_1 tableau_clause_1_graph_equation_2 tableau_clause_1_clause_2_graph_equation_1 tableau_clause_1_clause_2_graph_refinement_2 tableau_clause_1_clause_2_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_2 =
    let rec f _ _ _ _ = function
    | Coq_tableau_graph_refinement_1 (a0, s1, mc1, hind) ->
      tableau_graph_refinement_1 a0 s1 mc1 hind
        (f0 a0 s1 (inspect (solve_with_assumptions s1 a0)) mc1
          (match inspect (solve_with_assumptions s1 a0) with
           | Sat v ->
             (match mc1 with
              | [] -> Solution.Sat
              | t1 :: l ->
                (match inspect
                         (tableau_jumps v t1 l (fun a' ->
                           tableau a' (make_with_clauses (first_cpls l)) l)) with
                 | JumpSolution.Sat -> Solution.Sat
                 | JumpSolution.Unsat (c, core) ->
                   let conflict_set = conflict_set_of (t1 :: l) v c core in
                   let s0' = CplSolver.add_conflict_set s1 conflict_set in
                   let mc0' = add_conflict_set (t1 :: l) conflict_set in
                   tableau a0 s0' mc0'))
           | Unsat core -> Solution.Unsat core)
          hind)
    and f0 _ _ _ _ _ = function
    | Coq_tableau_clause_1_graph_refinement_1 (a0, s1, v, mc1, hind) ->
      tableau_clause_1_graph_refinement_1 a0 s1 v __ mc1 hind
        (f1 a0 s1 v __ mc1 mc1
          (match mc1 with
           | [] -> Solution.Sat
           | t1 :: l ->
             (match inspect
                      (tableau_jumps v t1 l (fun a' ->
                        tableau a' (make_with_clauses (first_cpls l)) l)) with
              | JumpSolution.Sat -> Solution.Sat
              | JumpSolution.Unsat (c, core) ->
                let conflict_set = conflict_set_of (t1 :: l) v c core in
                let s0' = CplSolver.add_conflict_set s1 conflict_set in
                let mc0' = add_conflict_set (t1 :: l) conflict_set in
                tableau a0 s0' mc0'))
          hind)
    | Coq_tableau_clause_1_graph_equation_2 (a0, s1, a', mc1) ->
      tableau_clause_1_graph_equation_2 a0 s1 a' __ mc1
    and f1 _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_graph_equation_1 (a0, s1, v0, mc1) ->
      tableau_clause_1_clause_2_graph_equation_1 a0 s1 v0 __ mc1
    | Coq_tableau_clause_1_clause_2_graph_refinement_2 (a0, s1, v0, mc1, l0,
                                                        mc2, hind, hind0) ->
      tableau_clause_1_clause_2_graph_refinement_2 a0 s1 v0 __ mc1 l0 mc2
        hind (fun a' ->
        f a' (make_with_clauses (first_cpls mc2)) mc2
          (tableau a' (make_with_clauses (first_cpls mc2)) mc2) (hind a'))
        hind0
        (f2 a0 s1 v0 __ mc1 l0 mc2
          (inspect
            (tableau_jumps v0 l0 mc2 (fun a' ->
              tableau a' (make_with_clauses (first_cpls mc2)) mc2)))
          (match inspect
                   (tableau_jumps v0 l0 mc2 (fun a' ->
                     tableau a' (make_with_clauses (first_cpls mc2)) mc2)) with
           | JumpSolution.Sat -> Solution.Sat
           | JumpSolution.Unsat (c, core) ->
             let conflict_set = conflict_set_of (l0 :: mc2) v0 c core in
             let s0' = CplSolver.add_conflict_set s1 conflict_set in
             let mc0' = add_conflict_set (l0 :: mc2) conflict_set in
             tableau a0 s0' mc0')
          hind0)
    and f2 _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1 (a0, s1, v0,
                                                               mc2, l1, mc3) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_1 a0 s1 v0 __ mc2 l1
        mc3 __
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               c, jump_core,
                                                               hind) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_2 a0 s1 v0 __ mc2 l1
        mc3 c jump_core __ hind
        (let conflict_set = conflict_set_of (l1 :: mc3) v0 c jump_core in
         let s0' = CplSolver.add_conflict_set s1 conflict_set in
         let mc0' = add_conflict_set (l1 :: mc3) conflict_set in
         f a0 s0' mc0' (tableau a0 s0' mc0') hind)
    in f

  (** val tableau_clause_1_graph_mut :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
      'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
      CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> tableau_graph) -> (Assumptions.t
      -> 'a1) -> tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> __ -> 'a4) -> (Assumptions.t -> CplSolver.t -> t ->
      __ -> Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Assumptions.t
      -> __ -> tableau_graph -> 'a1 -> 'a4) -> Assumptions.t -> CplSolver.t
      -> CplSolution.t -> Mchain.t -> Solution.t -> tableau_clause_1_graph ->
      'a2 **)

  let tableau_clause_1_graph_mut tableau_graph_refinement_1 tableau_clause_1_graph_refinement_1 tableau_clause_1_graph_equation_2 tableau_clause_1_clause_2_graph_equation_1 tableau_clause_1_clause_2_graph_refinement_2 tableau_clause_1_clause_2_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_2 =
    let rec f _ _ _ _ = function
    | Coq_tableau_graph_refinement_1 (a0, s1, mc1, hind) ->
      tableau_graph_refinement_1 a0 s1 mc1 hind
        (f0 a0 s1 (inspect (solve_with_assumptions s1 a0)) mc1
          (match inspect (solve_with_assumptions s1 a0) with
           | Sat v ->
             (match mc1 with
              | [] -> Solution.Sat
              | t1 :: l ->
                (match inspect
                         (tableau_jumps v t1 l (fun a' ->
                           tableau a' (make_with_clauses (first_cpls l)) l)) with
                 | JumpSolution.Sat -> Solution.Sat
                 | JumpSolution.Unsat (c, core) ->
                   let conflict_set = conflict_set_of (t1 :: l) v c core in
                   let s0' = CplSolver.add_conflict_set s1 conflict_set in
                   let mc0' = add_conflict_set (t1 :: l) conflict_set in
                   tableau a0 s0' mc0'))
           | Unsat core -> Solution.Unsat core)
          hind)
    and f0 _ _ _ _ _ = function
    | Coq_tableau_clause_1_graph_refinement_1 (a0, s1, v, mc1, hind) ->
      tableau_clause_1_graph_refinement_1 a0 s1 v __ mc1 hind
        (f1 a0 s1 v __ mc1 mc1
          (match mc1 with
           | [] -> Solution.Sat
           | t1 :: l ->
             (match inspect
                      (tableau_jumps v t1 l (fun a' ->
                        tableau a' (make_with_clauses (first_cpls l)) l)) with
              | JumpSolution.Sat -> Solution.Sat
              | JumpSolution.Unsat (c, core) ->
                let conflict_set = conflict_set_of (t1 :: l) v c core in
                let s0' = CplSolver.add_conflict_set s1 conflict_set in
                let mc0' = add_conflict_set (t1 :: l) conflict_set in
                tableau a0 s0' mc0'))
          hind)
    | Coq_tableau_clause_1_graph_equation_2 (a0, s1, a', mc1) ->
      tableau_clause_1_graph_equation_2 a0 s1 a' __ mc1
    and f1 _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_graph_equation_1 (a0, s1, v0, mc1) ->
      tableau_clause_1_clause_2_graph_equation_1 a0 s1 v0 __ mc1
    | Coq_tableau_clause_1_clause_2_graph_refinement_2 (a0, s1, v0, mc1, l0,
                                                        mc2, hind, hind0) ->
      tableau_clause_1_clause_2_graph_refinement_2 a0 s1 v0 __ mc1 l0 mc2
        hind (fun a' ->
        f a' (make_with_clauses (first_cpls mc2)) mc2
          (tableau a' (make_with_clauses (first_cpls mc2)) mc2) (hind a'))
        hind0
        (f2 a0 s1 v0 __ mc1 l0 mc2
          (inspect
            (tableau_jumps v0 l0 mc2 (fun a' ->
              tableau a' (make_with_clauses (first_cpls mc2)) mc2)))
          (match inspect
                   (tableau_jumps v0 l0 mc2 (fun a' ->
                     tableau a' (make_with_clauses (first_cpls mc2)) mc2)) with
           | JumpSolution.Sat -> Solution.Sat
           | JumpSolution.Unsat (c, core) ->
             let conflict_set = conflict_set_of (l0 :: mc2) v0 c core in
             let s0' = CplSolver.add_conflict_set s1 conflict_set in
             let mc0' = add_conflict_set (l0 :: mc2) conflict_set in
             tableau a0 s0' mc0')
          hind0)
    and f2 _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1 (a0, s1, v0,
                                                               mc2, l1, mc3) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_1 a0 s1 v0 __ mc2 l1
        mc3 __
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               c, jump_core,
                                                               hind) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_2 a0 s1 v0 __ mc2 l1
        mc3 c jump_core __ hind
        (let conflict_set = conflict_set_of (l1 :: mc3) v0 c jump_core in
         let s0' = CplSolver.add_conflict_set s1 conflict_set in
         let mc0' = add_conflict_set (l1 :: mc3) conflict_set in
         f a0 s0' mc0' (tableau a0 s0' mc0') hind)
    in f0

  (** val tableau_clause_1_clause_2_graph_mut :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
      'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
      CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> tableau_graph) -> (Assumptions.t
      -> 'a1) -> tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> __ -> 'a4) -> (Assumptions.t -> CplSolver.t -> t ->
      __ -> Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Assumptions.t
      -> __ -> tableau_graph -> 'a1 -> 'a4) -> Assumptions.t -> CplSolver.t
      -> t -> Mchain.t -> Mchain.t -> Solution.t ->
      tableau_clause_1_clause_2_graph -> 'a3 **)

  let tableau_clause_1_clause_2_graph_mut tableau_graph_refinement_1 tableau_clause_1_graph_refinement_1 tableau_clause_1_graph_equation_2 tableau_clause_1_clause_2_graph_equation_1 tableau_clause_1_clause_2_graph_refinement_2 tableau_clause_1_clause_2_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_2 a s0 v mc0 refine t0 t1 =
    let rec f _ _ _ _ = function
    | Coq_tableau_graph_refinement_1 (a0, s1, mc1, hind) ->
      tableau_graph_refinement_1 a0 s1 mc1 hind
        (f0 a0 s1 (inspect (solve_with_assumptions s1 a0)) mc1
          (match inspect (solve_with_assumptions s1 a0) with
           | Sat v0 ->
             (match mc1 with
              | [] -> Solution.Sat
              | t3 :: l ->
                (match inspect
                         (tableau_jumps v0 t3 l (fun a' ->
                           tableau a' (make_with_clauses (first_cpls l)) l)) with
                 | JumpSolution.Sat -> Solution.Sat
                 | JumpSolution.Unsat (c, core) ->
                   let conflict_set = conflict_set_of (t3 :: l) v0 c core in
                   let s0' = CplSolver.add_conflict_set s1 conflict_set in
                   let mc0' = add_conflict_set (t3 :: l) conflict_set in
                   tableau a0 s0' mc0'))
           | Unsat core -> Solution.Unsat core)
          hind)
    and f0 _ _ _ _ _ = function
    | Coq_tableau_clause_1_graph_refinement_1 (a0, s1, v0, mc1, hind) ->
      tableau_clause_1_graph_refinement_1 a0 s1 v0 __ mc1 hind
        (f1 a0 s1 v0 mc1 mc1
          (match mc1 with
           | [] -> Solution.Sat
           | t3 :: l ->
             (match inspect
                      (tableau_jumps v0 t3 l (fun a' ->
                        tableau a' (make_with_clauses (first_cpls l)) l)) with
              | JumpSolution.Sat -> Solution.Sat
              | JumpSolution.Unsat (c, core) ->
                let conflict_set = conflict_set_of (t3 :: l) v0 c core in
                let s0' = CplSolver.add_conflict_set s1 conflict_set in
                let mc0' = add_conflict_set (t3 :: l) conflict_set in
                tableau a0 s0' mc0'))
          hind)
    | Coq_tableau_clause_1_graph_equation_2 (a0, s1, a', mc1) ->
      tableau_clause_1_graph_equation_2 a0 s1 a' __ mc1
    and f1 _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_graph_equation_1 (a0, s1, v0, mc1) ->
      tableau_clause_1_clause_2_graph_equation_1 a0 s1 v0 __ mc1
    | Coq_tableau_clause_1_clause_2_graph_refinement_2 (a0, s1, v0, mc1, l0,
                                                        mc2, hind, hind0) ->
      tableau_clause_1_clause_2_graph_refinement_2 a0 s1 v0 __ mc1 l0 mc2
        hind (fun a' ->
        f a' (make_with_clauses (first_cpls mc2)) mc2
          (tableau a' (make_with_clauses (first_cpls mc2)) mc2) (hind a'))
        hind0
        (f2 a0 s1 v0 __ mc1 l0 mc2
          (inspect
            (tableau_jumps v0 l0 mc2 (fun a' ->
              tableau a' (make_with_clauses (first_cpls mc2)) mc2)))
          (match inspect
                   (tableau_jumps v0 l0 mc2 (fun a' ->
                     tableau a' (make_with_clauses (first_cpls mc2)) mc2)) with
           | JumpSolution.Sat -> Solution.Sat
           | JumpSolution.Unsat (c, core) ->
             let conflict_set = conflict_set_of (l0 :: mc2) v0 c core in
             let s0' = CplSolver.add_conflict_set s1 conflict_set in
             let mc0' = add_conflict_set (l0 :: mc2) conflict_set in
             tableau a0 s0' mc0')
          hind0)
    and f2 _ _ _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1 (a0, s1, v0,
                                                               mc2, l1, mc3) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_1 a0 s1 v0 __ mc2 l1
        mc3 __
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               c, jump_core,
                                                               hind) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_2 a0 s1 v0 __ mc2 l1
        mc3 c jump_core __ hind
        (let conflict_set = conflict_set_of (l1 :: mc3) v0 c jump_core in
         let s0' = CplSolver.add_conflict_set s1 conflict_set in
         let mc0' = add_conflict_set (l1 :: mc3) conflict_set in
         f a0 s0' mc0' (tableau a0 s0' mc0') hind)
    in f1 a s0 v mc0 refine t0 t1

  (** val tableau_clause_1_clause_2_clause_2_graph_mut :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
      'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
      CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> tableau_graph) -> (Assumptions.t
      -> 'a1) -> tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> __ -> 'a4) -> (Assumptions.t -> CplSolver.t -> t ->
      __ -> Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Assumptions.t
      -> __ -> tableau_graph -> 'a1 -> 'a4) -> Assumptions.t -> CplSolver.t
      -> t -> Mchain.t -> Lclauses.t -> Lclauses.t list -> JumpSolution.t ->
      Solution.t -> tableau_clause_1_clause_2_clause_2_graph -> 'a4 **)

  let tableau_clause_1_clause_2_clause_2_graph_mut tableau_graph_refinement_1 tableau_clause_1_graph_refinement_1 tableau_clause_1_graph_equation_2 tableau_clause_1_clause_2_graph_equation_1 tableau_clause_1_clause_2_graph_refinement_2 tableau_clause_1_clause_2_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_2 a s0 v mc0 l0 mc1 refine t0 t1 =
    let rec f _ _ _ _ = function
    | Coq_tableau_graph_refinement_1 (a0, s1, mc2, hind) ->
      tableau_graph_refinement_1 a0 s1 mc2 hind
        (f0 a0 s1 (inspect (solve_with_assumptions s1 a0)) mc2
          (match inspect (solve_with_assumptions s1 a0) with
           | Sat v0 ->
             (match mc2 with
              | [] -> Solution.Sat
              | t3 :: l ->
                (match inspect
                         (tableau_jumps v0 t3 l (fun a' ->
                           tableau a' (make_with_clauses (first_cpls l)) l)) with
                 | JumpSolution.Sat -> Solution.Sat
                 | JumpSolution.Unsat (c, core) ->
                   let conflict_set = conflict_set_of (t3 :: l) v0 c core in
                   let s0' = CplSolver.add_conflict_set s1 conflict_set in
                   let mc0' = add_conflict_set (t3 :: l) conflict_set in
                   tableau a0 s0' mc0'))
           | Unsat core -> Solution.Unsat core)
          hind)
    and f0 _ _ _ _ _ = function
    | Coq_tableau_clause_1_graph_refinement_1 (a0, s1, v0, mc2, hind) ->
      tableau_clause_1_graph_refinement_1 a0 s1 v0 __ mc2 hind
        (f1 a0 s1 v0 __ mc2 mc2
          (match mc2 with
           | [] -> Solution.Sat
           | t3 :: l ->
             (match inspect
                      (tableau_jumps v0 t3 l (fun a' ->
                        tableau a' (make_with_clauses (first_cpls l)) l)) with
              | JumpSolution.Sat -> Solution.Sat
              | JumpSolution.Unsat (c, core) ->
                let conflict_set = conflict_set_of (t3 :: l) v0 c core in
                let s0' = CplSolver.add_conflict_set s1 conflict_set in
                let mc0' = add_conflict_set (t3 :: l) conflict_set in
                tableau a0 s0' mc0'))
          hind)
    | Coq_tableau_clause_1_graph_equation_2 (a0, s1, a', mc2) ->
      tableau_clause_1_graph_equation_2 a0 s1 a' __ mc2
    and f1 _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_graph_equation_1 (a0, s1, v0, mc2) ->
      tableau_clause_1_clause_2_graph_equation_1 a0 s1 v0 __ mc2
    | Coq_tableau_clause_1_clause_2_graph_refinement_2 (a0, s1, v0, mc2, l1,
                                                        mc3, hind, hind0) ->
      tableau_clause_1_clause_2_graph_refinement_2 a0 s1 v0 __ mc2 l1 mc3
        hind (fun a' ->
        f a' (make_with_clauses (first_cpls mc3)) mc3
          (tableau a' (make_with_clauses (first_cpls mc3)) mc3) (hind a'))
        hind0
        (f2 a0 s1 v0 mc2 l1 mc3
          (inspect
            (tableau_jumps v0 l1 mc3 (fun a' ->
              tableau a' (make_with_clauses (first_cpls mc3)) mc3)))
          (match inspect
                   (tableau_jumps v0 l1 mc3 (fun a' ->
                     tableau a' (make_with_clauses (first_cpls mc3)) mc3)) with
           | JumpSolution.Sat -> Solution.Sat
           | JumpSolution.Unsat (c, core) ->
             let conflict_set = conflict_set_of (l1 :: mc3) v0 c core in
             let s0' = CplSolver.add_conflict_set s1 conflict_set in
             let mc0' = add_conflict_set (l1 :: mc3) conflict_set in
             tableau a0 s0' mc0')
          hind0)
    and f2 _ _ _ _ _ _ _ _ = function
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1 (a0, s1, v0,
                                                               mc2, l1, mc3) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_1 a0 s1 v0 __ mc2 l1
        mc3 __
    | Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2 (a0, s1, v0,
                                                               mc2, l1, mc3,
                                                               c, jump_core,
                                                               hind) ->
      tableau_clause_1_clause_2_clause_2_graph_equation_2 a0 s1 v0 __ mc2 l1
        mc3 c jump_core __ hind
        (let conflict_set = conflict_set_of (l1 :: mc3) v0 c jump_core in
         let s0' = CplSolver.add_conflict_set s1 conflict_set in
         let mc0' = add_conflict_set (l1 :: mc3) conflict_set in
         f a0 s0' mc0' (tableau a0 s0' mc0') hind)
    in f2 a s0 v mc0 l0 mc1 refine t0 t1

  (** val tableau_graph_rect :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
      'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
      CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> (Assumptions.t -> tableau_graph) -> (Assumptions.t
      -> 'a1) -> tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) ->
      (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t ->
      Lclauses.t list -> __ -> 'a4) -> (Assumptions.t -> CplSolver.t -> t ->
      __ -> Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Assumptions.t
      -> __ -> tableau_graph -> 'a1 -> 'a4) -> Assumptions.t -> CplSolver.t
      -> Mchain.t -> Solution.t -> tableau_graph -> 'a1 **)

  let tableau_graph_rect =
    tableau_graph_mut

  (** val tableau_graph_correct :
      Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_graph **)

  let tableau_graph_correct a s0 mc0 =
    let rec fix_F x =
      Coq_tableau_graph_refinement_1 ((let pr1,_ = x in pr1),
        (let pr1,_ = let _,pr2 = x in pr2 in pr1),
        (let _,pr2 = let _,pr2 = x in pr2 in pr2),
        (let refine =
           inspect
             (solve_with_assumptions
               (let pr1,_ = let _,pr2 = x in pr2 in pr1)
               (let pr1,_ = x in pr1))
         in
         match refine with
         | Sat v ->
           Coq_tableau_clause_1_graph_refinement_1 ((let pr1,_ = x in pr1),
             (let pr1,_ = let _,pr2 = x in pr2 in pr1), v,
             (let _,pr2 = let _,pr2 = x in pr2 in pr2),
             (let refine0 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in
              let x0 = fun a0 a1 b -> let y = a0,(a1,b) in (fun _ -> fix_F y)
              in
              (match refine0 with
               | [] ->
                 Coq_tableau_clause_1_clause_2_graph_equation_1
                   ((let pr1,_ = x in pr1),
                   (let pr1,_ = let _,pr2 = x in pr2 in pr1), v,
                   (let _,pr2 = let _,pr2 = x in pr2 in pr2))
               | t0 :: l ->
                 Coq_tableau_clause_1_clause_2_graph_refinement_2
                   ((let pr1,_ = x in pr1),
                   (let pr1,_ = let _,pr2 = x in pr2 in pr1), v,
                   (let _,pr2 = let _,pr2 = x in pr2 in pr2), t0, l,
                   (fun a' -> x0 a' (make_with_clauses (first_cpls l)) l __),
                   (let refine1 =
                      inspect
                        (tableau_jumps v t0 l (fun a' ->
                          tableau a' (make_with_clauses (first_cpls l)) l))
                    in
                    match refine1 with
                    | JumpSolution.Sat ->
                      Coq_tableau_clause_1_clause_2_clause_2_graph_equation_1
                        ((let pr1,_ = x in pr1),
                        (let pr1,_ = let _,pr2 = x in pr2 in pr1), v,
                        (let _,pr2 = let _,pr2 = x in pr2 in pr2), t0, l)
                    | JumpSolution.Unsat (c, core) ->
                      Coq_tableau_clause_1_clause_2_clause_2_graph_equation_2
                        ((let pr1,_ = x in pr1),
                        (let pr1,_ = let _,pr2 = x in pr2 in pr1), v,
                        (let _,pr2 = let _,pr2 = x in pr2 in pr2), t0, l, c,
                        core,
                        (let conflict_set = conflict_set_of (t0 :: l) v c core
                         in
                         let s0' =
                           CplSolver.add_conflict_set
                             (let pr1,_ = let _,pr2 = x in pr2 in pr1)
                             conflict_set
                         in
                         let mc0' = add_conflict_set (t0 :: l) conflict_set in
                         x0 (let pr1,_ = x in pr1) s0' mc0' __)))))))
         | Unsat core ->
           Coq_tableau_clause_1_graph_equation_2 ((let pr1,_ = x in pr1),
             (let pr1,_ = let _,pr2 = x in pr2 in pr1), core,
             (let _,pr2 = let _,pr2 = x in pr2 in pr2))))
    in fix_F (a,(s0,mc0))

  (** val tableau_elim :
      (Assumptions.t -> CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> __
      -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> __
      -> __ -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t
      -> Lclauses.t -> Lclauses.t list -> __ -> __ -> (Assumptions.t -> 'a1)
      -> __ -> __ -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ ->
      Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Assumptions.t -> __
      -> 'a1 -> __ -> (Assumptions.t -> 'a1) -> __ -> __ -> 'a1) ->
      Assumptions.t -> CplSolver.t -> Mchain.t -> 'a1 **)

  let tableau_elim tableau_clause_1_graph_equation_2 tableau_clause_1_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_1 tableau_clause_1_clause_2_clause_2_graph_equation_2 a s0 mc0 =
    tableau_graph_mut (fun _ _ _ _ x -> x __) (fun _ _ _ _ _ _ x -> x __)
      tableau_clause_1_graph_equation_2
      tableau_clause_1_clause_2_graph_equation_1
      (fun _ _ _ _ _ _ _ _ x _ x0 -> x0 __ x)
      tableau_clause_1_clause_2_clause_2_graph_equation_1
      (fun a0 s1 v _ mc1 l0 mc2 c jump_core _ _ ->
      tableau_clause_1_clause_2_clause_2_graph_equation_2 a0 s1 v __ mc1 l0
        mc2 c jump_core __)
      a s0 mc0 (tableau a s0 mc0) (tableau_graph_correct a s0 mc0)

  (** val coq_FunctionalElimination_tableau :
      (Assumptions.t -> CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> __
      -> __) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> __ ->
      __ -> __) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
      Lclauses.t -> Lclauses.t list -> __ -> __ -> (Assumptions.t -> __) ->
      __ -> __ -> __) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t
      -> Lclauses.t -> Lclauses.t list -> int -> Assumptions.t -> __ -> __ ->
      __ -> (Assumptions.t -> __) -> __ -> __ -> __) -> Assumptions.t ->
      CplSolver.t -> Mchain.t -> __ **)

  let coq_FunctionalElimination_tableau =
    tableau_elim

  (** val coq_FunctionalInduction_tableau :
      (Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t)
      coq_FunctionalInduction **)

  let coq_FunctionalInduction_tableau =
    Obj.magic tableau_graph_correct

  (** val solve_mchain : Mchain.t -> Solution.t **)

  let solve_mchain mc0 =
    let cpls0 = first_cpls mc0 in
    let s0 = make_with_clauses cpls0 in tableau [] s0 mc0

  (** val solve_fml : Fml.t -> Solution.t **)

  let solve_fml phi =
    apply
      (apply (apply (apply (apply phi from_fml) from_nnf) from_mcnf) simplify)
      solve_mchain

  (** val next_tableau : Mchain.t -> Assumptions.t -> Solution.t **)

  let next_tableau mc1 a' =
    tableau a' (make_with_clauses (first_cpls mc1)) mc1
 end
