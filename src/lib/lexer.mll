{
	open Lexing
	open Parser

	exception SyntaxError of string

	let newline lexbuf =
		let pos = lexbuf.lex_curr_p in
		lexbuf.lex_curr_p <-
			{pos with pos_lnum = pos.pos_lnum + 1;
			          pos_bol = pos.pos_cnum}
}

let digit = ['0'-'9']
let ident = digit+

rule next_token = parse
| ' ' | '\t' { next_token lexbuf }
| '\n' | '\r' { newline lexbuf; next_token lexbuf }
| "%" { comment lexbuf }
| '<' 'r' (ident as id) '>' {
    if id = "1" then Diamond 1
    else raise (SyntaxError ("Unsupported relation r" ^ id ^ ". Only r1 is allowed."))
  }
| '[' 'r' (ident as id) ']' {
    if id = "1" then Boxe 1
    else raise (SyntaxError ("Unsupported relation r" ^ id ^ ". Only r1 is allowed."))
  }
| "(" { LPAR }
| ")" { RPAR }
| "~" { Not }
| "&" { Conj }
| "|" { Dij }
| "<->" { Equiv }
| "->" { Impl }
| "true" { TRUE }
| "false" { FALSE }
| "begin" { BEGIN }
| "end" { END }
| eof { EOF }
(* We require atoms to be strictly positive, but some benchmarks use p0. *)
| "p" (ident as p) { Prop (int_of_string p + 1) }
| _ as s { raise (SyntaxError ("illegal character: " ^ (String.make 1 s))) }

and comment = parse
| '\n' { newline lexbuf; next_token lexbuf }
| eof { EOF }
| _ { comment lexbuf }
