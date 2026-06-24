
%token LPAR RPAR
%token <int> Diamond Boxe
%token TRUE FALSE
%token EOF
%token Conj
%token Dij
%token Impl
%token Equiv
%token Not
%token BEGIN END
%token <int> Prop

// Precedence lowest to highest binding
%right Equiv
%right Impl
%right Dij
%right Conj
%nonassoc Boxe Diamond Not

%start file
%type <Fml.t> file

%%

file :
| BEGIN; f = formula; END; EOF { f }

formula:
| TRUE { Fml.Or (Fml.Var 0, Fml.Neg (Fml.Var 0)) }
| FALSE { Fml.And (Fml.Var 0, Fml.Neg (Fml.Var 0)) }
| p = Prop { Fml.Var p }
| LPAR; f = formula; RPAR { f }
| Not; f = formula { Fml.Neg f }
| f1 = formula; Conj; f2 = formula { Fml.And (f1, f2) }
| f1 = formula; Dij; f2 = formula { Fml.Or (f1, f2) }
| f1 = formula; Impl; f2 = formula { Fml.Impl (f1, f2) }
| f1 = formula; Equiv; f2 = formula { Fml.And (Fml.Impl (f1, f2), Fml.Impl (f2, f1)) }
| _b = Boxe; f = formula { Fml.Box f }
| _d = Diamond; f = formula { Fml.Dia f }
