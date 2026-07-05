module RTree = struct
  type t =
    { v : int list
    ; c : t list
    }
  [@@deriving show { with_path = false }]

  let rec of_vct_tree (t : Vct.Tree.t) =
    let (Vct.Tree.Coq_make (v, c)) = t in
    { v; c = List.map of_vct_tree c }
  ;;
end

module Lit = struct
  type t = Vct.Lit.t =
    | Pos of int
    | Neg of int

  let pp fmt t =
    match t with
    | Pos p -> Format.fprintf fmt "+%i" p
    | Neg p -> Format.fprintf fmt "-%i" p
  ;;

  (* let show t = Format.asprintf "%a" pp t *)
end

module Deriv = struct
  type t =
    | Id of { a : Lit.t list }
    | Jr of
        { v : int list
        ; dia : int * Lit.t
        ; jump : t
        ; restart : t
        }
  [@@deriving show { with_path = false }]

  let rec of_vct_deriv (t : Vct.Derivation.t) =
    match t with
    | Id a -> Id { a }
    | JumpRestart (v, dia, jump, restart) ->
      Jr { v; dia; jump = of_vct_deriv jump; restart = of_vct_deriv restart }
  ;;
end

module Lclauses = struct
  type t = Vct.Lclauses.t =
    { cpls : Lit.t list list
    ; boxes : (int * Lit.t) list
    ; dias : (int * Lit.t) list
    }
  [@@deriving show { with_path = false }]
end

module Mcnf = struct
  type t = Lclauses.t list [@@deriving show { with_path = false }]
end

let parse_str str =
  let intohylo =
    str
    |> Str.global_replace (Str.regexp_string "[]") "[r1]"
    |> Str.global_replace (Str.regexp_string "<>") "<r1>"
  in
  let intohylo = "begin " ^ intohylo ^ " end" in
  let lexbuf = Lexing.from_string intohylo in
  Vct.Parser.file Vct.Lexer.next_token lexbuf
;;

let convert fml = fml |> Vct.Nnf.from_fml |> Vct.Mcnf0.from_nnf
(* |> Vct.Mcnf.simplify *)

let print_solution str =
  Printf.printf "FORMULA: %s\n\n" str;
  let fml = parse_str str in
  let mc0 = convert fml in
  Printf.printf "MCNF:\n%s\n\n" (Mcnf.show mc0);
  (match Vct.Solver.TailRec.solve_mcnf mc0 with
   | Sat t -> Printf.printf "SAT:\n%s\n\n" (t |> RTree.of_vct_tree |> RTree.show)
   | Unsat (_a, d) ->
     Printf.printf "UNSAT:\n%s\n\n" (d |> Deriv.of_vct_deriv |> Deriv.show));
  print_newline ()
;;

let () =
  print_solution "~([](p1 -> p2) -> ([]p1 -> []p2))";
  print_solution "~([](p1 -> p2) -> ([]p1 -> []p3))";
  print_solution "[]false";
  print_solution "[]p1 & <>~p1";
  print_solution "<>p1 & <>~p1";
  print_solution "~(<>(p1 | p2) <-> (<>p1 | <>p2))"
;;
