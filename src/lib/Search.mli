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

module Spec :
 sig
  module JumpSolution :
   sig
    type t =
    | Sat of Tree.t list
    | Unsat of DiaClause.t * Assumptions.t * Derivation.t

    val t_rect :
      (Tree.t list -> 'a1) -> (DiaClause.t -> Assumptions.t -> Derivation.t
      -> 'a1) -> t -> 'a1

    val t_rec :
      (Tree.t list -> 'a1) -> (DiaClause.t -> Assumptions.t -> Derivation.t
      -> 'a1) -> t -> 'a1
   end

  module Solution :
   sig
    type t =
    | Sat of Tree.t
    | Unsat of Assumptions.t * Derivation.t

    val t_rect :
      (Tree.t -> 'a1) -> (Assumptions.t -> Derivation.t -> 'a1) -> t -> 'a1

    val t_rec :
      (Tree.t -> 'a1) -> (Assumptions.t -> Derivation.t -> 'a1) -> t -> 'a1

    val is_sat : t -> bool
   end

  val tableau_jumps_clause_2_clause_2_clause_2 :
    t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
    list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Tree.t -> (t ->
    Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) -> __ ->
    JumpSolution.t) -> JumpSolution.t -> JumpSolution.t

  val tableau_jumps_clause_2_clause_2 :
    t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
    list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Solution.t -> (t ->
    Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) -> __ ->
    JumpSolution.t) -> JumpSolution.t

  val tableau_jumps_clause_2 :
    t -> CplClause.t list -> BoxClause.t list -> int -> bool -> Lit.t ->
    DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) -> (t ->
    Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) -> __ ->
    JumpSolution.t) -> JumpSolution.t

  val tableau_jumps_functional :
    t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) -> (t ->
    Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) -> __ ->
    JumpSolution.t) -> JumpSolution.t

  val tableau_jumps :
    t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) ->
    JumpSolution.t

  val tableau_jumps_unfold_clause_2_clause_2_clause_2 :
    t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
    list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Tree.t ->
    JumpSolution.t -> JumpSolution.t

  val tableau_jumps_unfold_clause_2_clause_2 :
    t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
    list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Solution.t ->
    JumpSolution.t

  val tableau_jumps_unfold_clause_2 :
    t -> CplClause.t list -> BoxClause.t list -> int -> bool -> Lit.t ->
    DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
    JumpSolution.t

  val tableau_jumps_unfold :
    t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) ->
    JumpSolution.t

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

  val tableau_jumps_graph_mut :
    (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> (Assumptions.t
    -> Solution.t) -> 'a1) -> (t -> CplClause.t list -> BoxClause.t list ->
    int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
    Solution.t) -> tableau_jumps_clause_2_graph -> 'a2 -> 'a1) -> (t ->
    CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list
    -> Mchain.t -> (Assumptions.t -> Solution.t) ->
    tableau_jumps_clause_2_clause_2_graph -> 'a3 -> 'a2) -> (t -> CplClause.t
    list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t
    -> (Assumptions.t -> Solution.t) -> tableau_jumps_graph -> 'a1 -> 'a2) ->
    (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
    list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Tree.t ->
    tableau_jumps_graph -> 'a1 ->
    tableau_jumps_clause_2_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (t ->
    CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list
    -> Mchain.t -> (Assumptions.t -> Solution.t) -> Assumptions.t ->
    Derivation.t -> 'a3) -> (t -> CplClause.t list -> BoxClause.t list -> int
    -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t)
    -> Tree.t -> Tree.t list -> 'a4) -> (t -> CplClause.t list -> BoxClause.t
    list -> int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
    Solution.t) -> Tree.t -> DiaClause.t -> Assumptions.t -> Derivation.t ->
    'a4) -> t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) ->
    JumpSolution.t -> tableau_jumps_graph -> 'a1

  val tableau_jumps_clause_2_graph_mut :
    (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> (Assumptions.t
    -> Solution.t) -> 'a1) -> (t -> CplClause.t list -> BoxClause.t list ->
    int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
    Solution.t) -> tableau_jumps_clause_2_graph -> 'a2 -> 'a1) -> (t ->
    CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list
    -> Mchain.t -> (Assumptions.t -> Solution.t) ->
    tableau_jumps_clause_2_clause_2_graph -> 'a3 -> 'a2) -> (t -> CplClause.t
    list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t
    -> (Assumptions.t -> Solution.t) -> tableau_jumps_graph -> 'a1 -> 'a2) ->
    (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
    list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Tree.t ->
    tableau_jumps_graph -> 'a1 ->
    tableau_jumps_clause_2_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (t ->
    CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list
    -> Mchain.t -> (Assumptions.t -> Solution.t) -> Assumptions.t ->
    Derivation.t -> 'a3) -> (t -> CplClause.t list -> BoxClause.t list -> int
    -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t)
    -> Tree.t -> Tree.t list -> 'a4) -> (t -> CplClause.t list -> BoxClause.t
    list -> int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
    Solution.t) -> Tree.t -> DiaClause.t -> Assumptions.t -> Derivation.t ->
    'a4) -> t -> CplClause.t list -> BoxClause.t list -> int -> bool -> Lit.t
    -> DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
    JumpSolution.t -> tableau_jumps_clause_2_graph -> 'a2

  val tableau_jumps_clause_2_clause_2_graph_mut :
    (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> (Assumptions.t
    -> Solution.t) -> 'a1) -> (t -> CplClause.t list -> BoxClause.t list ->
    int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
    Solution.t) -> tableau_jumps_clause_2_graph -> 'a2 -> 'a1) -> (t ->
    CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list
    -> Mchain.t -> (Assumptions.t -> Solution.t) ->
    tableau_jumps_clause_2_clause_2_graph -> 'a3 -> 'a2) -> (t -> CplClause.t
    list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t
    -> (Assumptions.t -> Solution.t) -> tableau_jumps_graph -> 'a1 -> 'a2) ->
    (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
    list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Tree.t ->
    tableau_jumps_graph -> 'a1 ->
    tableau_jumps_clause_2_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (t ->
    CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list
    -> Mchain.t -> (Assumptions.t -> Solution.t) -> Assumptions.t ->
    Derivation.t -> 'a3) -> (t -> CplClause.t list -> BoxClause.t list -> int
    -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t)
    -> Tree.t -> Tree.t list -> 'a4) -> (t -> CplClause.t list -> BoxClause.t
    list -> int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
    Solution.t) -> Tree.t -> DiaClause.t -> Assumptions.t -> Derivation.t ->
    'a4) -> t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
    DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) ->
    Solution.t -> JumpSolution.t -> tableau_jumps_clause_2_clause_2_graph ->
    'a3

  val tableau_jumps_clause_2_clause_2_clause_2_graph_mut :
    (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> (Assumptions.t
    -> Solution.t) -> 'a1) -> (t -> CplClause.t list -> BoxClause.t list ->
    int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
    Solution.t) -> tableau_jumps_clause_2_graph -> 'a2 -> 'a1) -> (t ->
    CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list
    -> Mchain.t -> (Assumptions.t -> Solution.t) ->
    tableau_jumps_clause_2_clause_2_graph -> 'a3 -> 'a2) -> (t -> CplClause.t
    list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t
    -> (Assumptions.t -> Solution.t) -> tableau_jumps_graph -> 'a1 -> 'a2) ->
    (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
    list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Tree.t ->
    tableau_jumps_graph -> 'a1 ->
    tableau_jumps_clause_2_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (t ->
    CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list
    -> Mchain.t -> (Assumptions.t -> Solution.t) -> Assumptions.t ->
    Derivation.t -> 'a3) -> (t -> CplClause.t list -> BoxClause.t list -> int
    -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t)
    -> Tree.t -> Tree.t list -> 'a4) -> (t -> CplClause.t list -> BoxClause.t
    list -> int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
    Solution.t) -> Tree.t -> DiaClause.t -> Assumptions.t -> Derivation.t ->
    'a4) -> t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
    DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Tree.t
    -> JumpSolution.t -> JumpSolution.t ->
    tableau_jumps_clause_2_clause_2_clause_2_graph -> 'a4

  val tableau_jumps_graph_rect :
    (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> (Assumptions.t
    -> Solution.t) -> 'a1) -> (t -> CplClause.t list -> BoxClause.t list ->
    int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
    Solution.t) -> tableau_jumps_clause_2_graph -> 'a2 -> 'a1) -> (t ->
    CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list
    -> Mchain.t -> (Assumptions.t -> Solution.t) ->
    tableau_jumps_clause_2_clause_2_graph -> 'a3 -> 'a2) -> (t -> CplClause.t
    list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t
    -> (Assumptions.t -> Solution.t) -> tableau_jumps_graph -> 'a1 -> 'a2) ->
    (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t
    list -> Mchain.t -> (Assumptions.t -> Solution.t) -> Tree.t ->
    tableau_jumps_graph -> 'a1 ->
    tableau_jumps_clause_2_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (t ->
    CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list
    -> Mchain.t -> (Assumptions.t -> Solution.t) -> Assumptions.t ->
    Derivation.t -> 'a3) -> (t -> CplClause.t list -> BoxClause.t list -> int
    -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t -> Solution.t)
    -> Tree.t -> Tree.t list -> 'a4) -> (t -> CplClause.t list -> BoxClause.t
    list -> int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
    Solution.t) -> Tree.t -> DiaClause.t -> Assumptions.t -> Derivation.t ->
    'a4) -> t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) ->
    JumpSolution.t -> tableau_jumps_graph -> 'a1

  val tableau_jumps_graph_correct :
    t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) ->
    tableau_jumps_graph

  val tableau_jumps_elim :
    (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> (Assumptions.t
    -> Solution.t) -> 'a1) -> (t -> CplClause.t list -> BoxClause.t list ->
    int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
    Solution.t) -> 'a1 -> __ -> 'a1) -> (t -> CplClause.t list -> BoxClause.t
    list -> int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
    Solution.t) -> Assumptions.t -> Derivation.t -> __ -> __ -> 'a1) -> (t ->
    CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list
    -> Mchain.t -> (Assumptions.t -> Solution.t) -> Tree.t -> Tree.t list ->
    __ -> 'a1 -> __ -> __ -> 'a1) -> (t -> CplClause.t list -> BoxClause.t
    list -> int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
    Solution.t) -> Tree.t -> DiaClause.t -> Assumptions.t -> Derivation.t ->
    __ -> 'a1 -> __ -> __ -> 'a1) -> t -> Lclauses.t -> Mchain.t ->
    (Assumptions.t -> Solution.t) -> 'a1

  val coq_FunctionalElimination_tableau_jumps :
    (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> (Assumptions.t
    -> Solution.t) -> __) -> (t -> CplClause.t list -> BoxClause.t list ->
    int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
    Solution.t) -> __ -> __ -> __) -> (t -> CplClause.t list -> BoxClause.t
    list -> int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
    Solution.t) -> Assumptions.t -> Derivation.t -> __ -> __ -> __) -> (t ->
    CplClause.t list -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list
    -> Mchain.t -> (Assumptions.t -> Solution.t) -> Tree.t -> Tree.t list ->
    __ -> __ -> __ -> __ -> __) -> (t -> CplClause.t list -> BoxClause.t list
    -> int -> Lit.t -> DiaClause.t list -> Mchain.t -> (Assumptions.t ->
    Solution.t) -> Tree.t -> DiaClause.t -> Assumptions.t -> Derivation.t ->
    __ -> __ -> __ -> __ -> __) -> t -> Lclauses.t -> Mchain.t ->
    (Assumptions.t -> Solution.t) -> __

  val coq_FunctionalInduction_tableau_jumps :
    (t -> Lclauses.t -> Mchain.t -> (Assumptions.t -> Solution.t) ->
    JumpSolution.t) coq_FunctionalInduction

  val tableau_clause_1_clause_2_clause_2 :
    Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t -> Lclauses.t
    list -> (Assumptions.t -> CplSolver.t -> Mchain.t -> __ -> Solution.t) ->
    JumpSolution.t -> Solution.t

  val tableau_clause_1_clause_2 :
    Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t list ->
    (Assumptions.t -> CplSolver.t -> Mchain.t -> __ -> Solution.t) ->
    Solution.t

  val tableau_clause_1 :
    Assumptions.t -> CplSolver.t -> CplSolution.t -> Mchain.t ->
    (Assumptions.t -> CplSolver.t -> Mchain.t -> __ -> Solution.t) ->
    Solution.t

  val tableau_functional :
    Assumptions.t -> CplSolver.t -> Mchain.t -> (Assumptions.t -> CplSolver.t
    -> Mchain.t -> __ -> Solution.t) -> Solution.t

  val tableau : Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t

  val tableau_unfold_clause_1_clause_2_clause_2 :
    Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t -> Lclauses.t
    list -> JumpSolution.t -> Solution.t

  val tableau_unfold_clause_1_clause_2 :
    Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t list ->
    Solution.t

  val tableau_unfold_clause_1 :
    Assumptions.t -> CplSolver.t -> CplSolution.t -> Mchain.t -> Solution.t

  val tableau_unfold : Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t

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

  val tableau_graph_mut :
    (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
    'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
    tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
    CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) -> (Assumptions.t ->
    CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    (Assumptions.t -> tableau_graph) -> (Assumptions.t -> 'a1) ->
    tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    Tree.t list -> __ -> 'a4) -> (Assumptions.t -> CplSolver.t -> t -> __ ->
    Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Lit.t ->
    Assumptions.t -> Derivation.t -> __ -> tableau_graph -> 'a1 -> 'a4) ->
    Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t -> tableau_graph
    -> 'a1

  val tableau_clause_1_graph_mut :
    (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
    'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
    tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
    CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) -> (Assumptions.t ->
    CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    (Assumptions.t -> tableau_graph) -> (Assumptions.t -> 'a1) ->
    tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    Tree.t list -> __ -> 'a4) -> (Assumptions.t -> CplSolver.t -> t -> __ ->
    Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Lit.t ->
    Assumptions.t -> Derivation.t -> __ -> tableau_graph -> 'a1 -> 'a4) ->
    Assumptions.t -> CplSolver.t -> CplSolution.t -> Mchain.t -> Solution.t
    -> tableau_clause_1_graph -> 'a2

  val tableau_clause_1_clause_2_graph_mut :
    (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
    'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
    tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
    CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) -> (Assumptions.t ->
    CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    (Assumptions.t -> tableau_graph) -> (Assumptions.t -> 'a1) ->
    tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    Tree.t list -> __ -> 'a4) -> (Assumptions.t -> CplSolver.t -> t -> __ ->
    Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Lit.t ->
    Assumptions.t -> Derivation.t -> __ -> tableau_graph -> 'a1 -> 'a4) ->
    Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Mchain.t -> Solution.t
    -> tableau_clause_1_clause_2_graph -> 'a3

  val tableau_clause_1_clause_2_clause_2_graph_mut :
    (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
    'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
    tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
    CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) -> (Assumptions.t ->
    CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    (Assumptions.t -> tableau_graph) -> (Assumptions.t -> 'a1) ->
    tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    Tree.t list -> __ -> 'a4) -> (Assumptions.t -> CplSolver.t -> t -> __ ->
    Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Lit.t ->
    Assumptions.t -> Derivation.t -> __ -> tableau_graph -> 'a1 -> 'a4) ->
    Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t -> Lclauses.t
    list -> JumpSolution.t -> Solution.t ->
    tableau_clause_1_clause_2_clause_2_graph -> 'a4

  val tableau_graph_rect :
    (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
    'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
    tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
    CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) -> (Assumptions.t ->
    CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    (Assumptions.t -> tableau_graph) -> (Assumptions.t -> 'a1) ->
    tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    Tree.t list -> __ -> 'a4) -> (Assumptions.t -> CplSolver.t -> t -> __ ->
    Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Lit.t ->
    Assumptions.t -> Derivation.t -> __ -> tableau_graph -> 'a1 -> 'a4) ->
    Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t -> tableau_graph
    -> 'a1

  val tableau_graph_correct :
    Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_graph

  val tableau_elim :
    (Assumptions.t -> CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> __ ->
    'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> __ -> __
    -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
    Lclauses.t -> Lclauses.t list -> Tree.t list -> __ -> __ ->
    (Assumptions.t -> 'a1) -> __ -> __ -> 'a1) -> (Assumptions.t ->
    CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    int -> Lit.t -> Assumptions.t -> Derivation.t -> __ -> 'a1 -> __ ->
    (Assumptions.t -> 'a1) -> __ -> __ -> 'a1) -> Assumptions.t ->
    CplSolver.t -> Mchain.t -> 'a1

  val coq_FunctionalElimination_tableau :
    (Assumptions.t -> CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> __ ->
    __) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> __ -> __
    -> __) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
    Lclauses.t -> Lclauses.t list -> Tree.t list -> __ -> __ ->
    (Assumptions.t -> __) -> __ -> __ -> __) -> (Assumptions.t -> CplSolver.t
    -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Lit.t
    -> Assumptions.t -> Derivation.t -> __ -> __ -> __ -> (Assumptions.t ->
    __) -> __ -> __ -> __) -> Assumptions.t -> CplSolver.t -> Mchain.t -> __

  val coq_FunctionalInduction_tableau :
    (Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t)
    coq_FunctionalInduction

  val next_tableau : Mchain.t -> Assumptions.t -> Solution.t

  val solve_mchain : Mchain.t -> Solution.t

  val solve_fml : Fml.t -> Solution.t
 end

module TailRec :
 sig
  module Solution :
   sig
    type t = Spec.Solution.t =
    | Sat of Tree.t
    | Unsat of Assumptions.t * Derivation.t

    val t_rect :
      (Tree.t -> 'a1) -> (Assumptions.t -> Derivation.t -> 'a1) -> t -> 'a1

    val t_rec :
      (Tree.t -> 'a1) -> (Assumptions.t -> Derivation.t -> 'a1) -> t -> 'a1

    val is_sat : t -> bool
   end

  module JumpSolution :
   sig
    type t = Spec.JumpSolution.t =
    | Sat of Tree.t list
    | Unsat of DiaClause.t * Assumptions.t * Derivation.t

    val t_rect :
      (Tree.t list -> 'a1) -> (DiaClause.t -> Assumptions.t -> Derivation.t
      -> 'a1) -> t -> 'a1

    val t_rec :
      (Tree.t list -> 'a1) -> (DiaClause.t -> Assumptions.t -> Derivation.t
      -> 'a1) -> t -> 'a1
   end

  val tableau_jumps_clause_2 :
    t -> CplClause.t list -> BoxClause.t list -> int -> bool -> Lit.t ->
    DiaClause.t list -> Mchain.t -> Tree.t list -> (Assumptions.t ->
    Solution.t) -> (t -> Lclauses.t -> Mchain.t -> Tree.t list ->
    (Assumptions.t -> Solution.t) -> __ -> JumpSolution.t) -> JumpSolution.t

  val tableau_jumps_functional :
    t -> Lclauses.t -> Mchain.t -> Tree.t list -> (Assumptions.t ->
    Solution.t) -> (t -> Lclauses.t -> Mchain.t -> Tree.t list ->
    (Assumptions.t -> Solution.t) -> __ -> JumpSolution.t) -> JumpSolution.t

  val tableau_jumps :
    t -> Lclauses.t -> Mchain.t -> Tree.t list -> (Assumptions.t ->
    Solution.t) -> JumpSolution.t

  val tableau_jumps_unfold_clause_2 :
    t -> CplClause.t list -> BoxClause.t list -> int -> bool -> Lit.t ->
    DiaClause.t list -> Mchain.t -> Tree.t list -> (Assumptions.t ->
    Solution.t) -> JumpSolution.t

  val tableau_jumps_unfold :
    t -> Lclauses.t -> Mchain.t -> Tree.t list -> (Assumptions.t ->
    Solution.t) -> JumpSolution.t

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

  val tableau_jumps_graph_mut :
    (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> Tree.t list ->
    (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
    BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
    Tree.t list -> (Assumptions.t -> Solution.t) ->
    tableau_jumps_clause_2_graph -> 'a2 -> 'a1) -> (t -> CplClause.t list ->
    BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
    Tree.t list -> (Assumptions.t -> Solution.t) -> (Tree.t ->
    tableau_jumps_graph) -> (Tree.t -> 'a1) -> 'a2) -> (t -> CplClause.t list
    -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
    Tree.t list -> (Assumptions.t -> Solution.t) -> tableau_jumps_graph ->
    'a1 -> 'a2) -> t -> Lclauses.t -> Mchain.t -> Tree.t list ->
    (Assumptions.t -> Solution.t) -> JumpSolution.t -> tableau_jumps_graph ->
    'a1

  val tableau_jumps_clause_2_graph_mut :
    (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> Tree.t list ->
    (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
    BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
    Tree.t list -> (Assumptions.t -> Solution.t) ->
    tableau_jumps_clause_2_graph -> 'a2 -> 'a1) -> (t -> CplClause.t list ->
    BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
    Tree.t list -> (Assumptions.t -> Solution.t) -> (Tree.t ->
    tableau_jumps_graph) -> (Tree.t -> 'a1) -> 'a2) -> (t -> CplClause.t list
    -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
    Tree.t list -> (Assumptions.t -> Solution.t) -> tableau_jumps_graph ->
    'a1 -> 'a2) -> t -> CplClause.t list -> BoxClause.t list -> int -> bool
    -> Lit.t -> DiaClause.t list -> Mchain.t -> Tree.t list -> (Assumptions.t
    -> Solution.t) -> JumpSolution.t -> tableau_jumps_clause_2_graph -> 'a2

  val tableau_jumps_graph_rect :
    (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> Tree.t list ->
    (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
    BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
    Tree.t list -> (Assumptions.t -> Solution.t) ->
    tableau_jumps_clause_2_graph -> 'a2 -> 'a1) -> (t -> CplClause.t list ->
    BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
    Tree.t list -> (Assumptions.t -> Solution.t) -> (Tree.t ->
    tableau_jumps_graph) -> (Tree.t -> 'a1) -> 'a2) -> (t -> CplClause.t list
    -> BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
    Tree.t list -> (Assumptions.t -> Solution.t) -> tableau_jumps_graph ->
    'a1 -> 'a2) -> t -> Lclauses.t -> Mchain.t -> Tree.t list ->
    (Assumptions.t -> Solution.t) -> JumpSolution.t -> tableau_jumps_graph ->
    'a1

  val tableau_jumps_graph_correct :
    t -> Lclauses.t -> Mchain.t -> Tree.t list -> (Assumptions.t ->
    Solution.t) -> tableau_jumps_graph

  val tableau_jumps_elim :
    (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> Tree.t list ->
    (Assumptions.t -> Solution.t) -> 'a1) -> (t -> CplClause.t list ->
    BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
    Tree.t list -> (Assumptions.t -> Solution.t) -> (Tree.t -> 'a1) -> __ ->
    'a1) -> (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
    DiaClause.t list -> Mchain.t -> Tree.t list -> (Assumptions.t ->
    Solution.t) -> 'a1 -> __ -> 'a1) -> t -> Lclauses.t -> Mchain.t -> Tree.t
    list -> (Assumptions.t -> Solution.t) -> 'a1

  val coq_FunctionalElimination_tableau_jumps :
    (t -> CplClause.t list -> BoxClause.t list -> Mchain.t -> Tree.t list ->
    (Assumptions.t -> Solution.t) -> __) -> (t -> CplClause.t list ->
    BoxClause.t list -> int -> Lit.t -> DiaClause.t list -> Mchain.t ->
    Tree.t list -> (Assumptions.t -> Solution.t) -> (Tree.t -> __) -> __ ->
    __) -> (t -> CplClause.t list -> BoxClause.t list -> int -> Lit.t ->
    DiaClause.t list -> Mchain.t -> Tree.t list -> (Assumptions.t ->
    Solution.t) -> __ -> __ -> __) -> t -> Lclauses.t -> Mchain.t -> Tree.t
    list -> (Assumptions.t -> Solution.t) -> __

  val coq_FunctionalInduction_tableau_jumps :
    (t -> Lclauses.t -> Mchain.t -> Tree.t list -> (Assumptions.t ->
    Solution.t) -> JumpSolution.t) coq_FunctionalInduction

  val tableau_clause_1_clause_2_clause_2 :
    Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t -> Lclauses.t
    list -> (Assumptions.t -> CplSolver.t -> Mchain.t -> __ -> Solution.t) ->
    JumpSolution.t -> Solution.t

  val tableau_clause_1_clause_2 :
    Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t list ->
    (Assumptions.t -> CplSolver.t -> Mchain.t -> __ -> Solution.t) ->
    Solution.t

  val tableau_clause_1 :
    Assumptions.t -> CplSolver.t -> CplSolution.t -> Mchain.t ->
    (Assumptions.t -> CplSolver.t -> Mchain.t -> __ -> Solution.t) ->
    Solution.t

  val tableau_functional :
    Assumptions.t -> CplSolver.t -> Mchain.t -> (Assumptions.t -> CplSolver.t
    -> Mchain.t -> __ -> Solution.t) -> Solution.t

  val tableau : Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t

  val tableau_unfold_clause_1_clause_2_clause_2 :
    Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t -> Lclauses.t
    list -> JumpSolution.t -> Solution.t

  val tableau_unfold_clause_1_clause_2 :
    Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t list ->
    Solution.t

  val tableau_unfold_clause_1 :
    Assumptions.t -> CplSolver.t -> CplSolution.t -> Mchain.t -> Solution.t

  val tableau_unfold : Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t

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

  val tableau_graph_mut :
    (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
    'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
    tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
    CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) -> (Assumptions.t ->
    CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    (Assumptions.t -> tableau_graph) -> (Assumptions.t -> 'a1) ->
    tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    Tree.t list -> __ -> 'a4) -> (Assumptions.t -> CplSolver.t -> t -> __ ->
    Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Lit.t ->
    Assumptions.t -> Derivation.t -> __ -> tableau_graph -> 'a1 -> 'a4) ->
    Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t -> tableau_graph
    -> 'a1

  val tableau_clause_1_graph_mut :
    (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
    'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
    tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
    CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) -> (Assumptions.t ->
    CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    (Assumptions.t -> tableau_graph) -> (Assumptions.t -> 'a1) ->
    tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    Tree.t list -> __ -> 'a4) -> (Assumptions.t -> CplSolver.t -> t -> __ ->
    Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Lit.t ->
    Assumptions.t -> Derivation.t -> __ -> tableau_graph -> 'a1 -> 'a4) ->
    Assumptions.t -> CplSolver.t -> CplSolution.t -> Mchain.t -> Solution.t
    -> tableau_clause_1_graph -> 'a2

  val tableau_clause_1_clause_2_graph_mut :
    (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
    'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
    tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
    CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) -> (Assumptions.t ->
    CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    (Assumptions.t -> tableau_graph) -> (Assumptions.t -> 'a1) ->
    tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    Tree.t list -> __ -> 'a4) -> (Assumptions.t -> CplSolver.t -> t -> __ ->
    Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Lit.t ->
    Assumptions.t -> Derivation.t -> __ -> tableau_graph -> 'a1 -> 'a4) ->
    Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Mchain.t -> Solution.t
    -> tableau_clause_1_clause_2_graph -> 'a3

  val tableau_clause_1_clause_2_clause_2_graph_mut :
    (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
    'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
    tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
    CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) -> (Assumptions.t ->
    CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    (Assumptions.t -> tableau_graph) -> (Assumptions.t -> 'a1) ->
    tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    Tree.t list -> __ -> 'a4) -> (Assumptions.t -> CplSolver.t -> t -> __ ->
    Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Lit.t ->
    Assumptions.t -> Derivation.t -> __ -> tableau_graph -> 'a1 -> 'a4) ->
    Assumptions.t -> CplSolver.t -> t -> Mchain.t -> Lclauses.t -> Lclauses.t
    list -> JumpSolution.t -> Solution.t ->
    tableau_clause_1_clause_2_clause_2_graph -> 'a4

  val tableau_graph_rect :
    (Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_clause_1_graph ->
    'a2 -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
    tableau_clause_1_clause_2_graph -> 'a3 -> 'a2) -> (Assumptions.t ->
    CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> 'a2) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> 'a3) -> (Assumptions.t ->
    CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    (Assumptions.t -> tableau_graph) -> (Assumptions.t -> 'a1) ->
    tableau_clause_1_clause_2_clause_2_graph -> 'a4 -> 'a3) -> (Assumptions.t
    -> CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    Tree.t list -> __ -> 'a4) -> (Assumptions.t -> CplSolver.t -> t -> __ ->
    Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Lit.t ->
    Assumptions.t -> Derivation.t -> __ -> tableau_graph -> 'a1 -> 'a4) ->
    Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t -> tableau_graph
    -> 'a1

  val tableau_graph_correct :
    Assumptions.t -> CplSolver.t -> Mchain.t -> tableau_graph

  val tableau_elim :
    (Assumptions.t -> CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> __ ->
    'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> __ -> __
    -> 'a1) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
    Lclauses.t -> Lclauses.t list -> Tree.t list -> __ -> __ ->
    (Assumptions.t -> 'a1) -> __ -> __ -> 'a1) -> (Assumptions.t ->
    CplSolver.t -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list ->
    int -> Lit.t -> Assumptions.t -> Derivation.t -> __ -> 'a1 -> __ ->
    (Assumptions.t -> 'a1) -> __ -> __ -> 'a1) -> Assumptions.t ->
    CplSolver.t -> Mchain.t -> 'a1

  val coq_FunctionalElimination_tableau :
    (Assumptions.t -> CplSolver.t -> Assumptions.t -> __ -> Mchain.t -> __ ->
    __) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t -> __ -> __
    -> __) -> (Assumptions.t -> CplSolver.t -> t -> __ -> Mchain.t ->
    Lclauses.t -> Lclauses.t list -> Tree.t list -> __ -> __ ->
    (Assumptions.t -> __) -> __ -> __ -> __) -> (Assumptions.t -> CplSolver.t
    -> t -> __ -> Mchain.t -> Lclauses.t -> Lclauses.t list -> int -> Lit.t
    -> Assumptions.t -> Derivation.t -> __ -> __ -> __ -> (Assumptions.t ->
    __) -> __ -> __ -> __) -> Assumptions.t -> CplSolver.t -> Mchain.t -> __

  val coq_FunctionalInduction_tableau :
    (Assumptions.t -> CplSolver.t -> Mchain.t -> Solution.t)
    coq_FunctionalInduction

  val solve_mchain : Mchain.t -> Solution.t

  val solve_fml : Fml.t -> Solution.t
 end
