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

let print_solution str =
  Printf.printf "%s : " str;
  (match parse_str str |> Vct.Solver.TailRec.solve_fml with
   | Sat t ->
     print_endline "SAT";
     print_endline (t |> RTree.of_vct_tree |> RTree.show)
   | Unsat (_a, d) ->
     print_endline "UNSAT";
     print_endline (d |> Deriv.of_vct_deriv |> Deriv.show));
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
