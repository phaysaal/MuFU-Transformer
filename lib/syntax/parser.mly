
%{
open MuFU_util
open Raw_hflz
%}

%token <int> INT
%token <string> LIDENT
%token <string> UIDENT

%token START_HES START_ENV EOF
%token LPAREN  "(" RPAREN  ")"
%token LSQUARE "[" RSQUARE "]"
%token LANGRE  "<" RANGRE  ">"
%token TRUE FALSE
%token LAMBDA DOT "." COLON ":"
%token DEF_G "=v"
%token DEF_L "=m"
%token FORALL 

%token PLUS  "+" MINUS "-" STAR  "*" SLASH "/" PERCENT "%" NEG
%token EQ "=" NEQ "<>" LE "<=" GE ">=" /* LT "<" GT ">" */
%token AND "&&" OR "||"

%token TBOOL TINT TARROW "->" SEMICOLON ";"

%right OR
%right AND
%left PLUS MINUS
%left STAR
%nonassoc NEG

%type <Raw_hflz.hes> hes
%type <(string * Type.abstraction_ty) list> env
%type <Type.abstraction_ty> abstraction_ty
%type <Type.abstraction_argty> abstraction_argty
%type <Raw_hflz.hes * (string * Type.abstraction_ty) list option> main
%start main

%%

main:
| hes EOF     { $1, None    }
| hes env EOF { $1, Some $2 }

(******************************************************************************)
(* HES                                                                        *)
(******************************************************************************)

hes:
| START_HES hflz_rule+ { $2 }

hflz_rule:
| uvar lvar* def_fixpoint hflz DOT
    { { var  = $1
      ; args = $2
      ; fix  = $3
      ; body = $4
      }
    }

hflz:
| abs_expr { $1 }

abs_expr:
| lambdas and_or_expr { mk_abss $1 $2 }

and_or_expr:
| and_or_expr "&&" and_or_expr  { mk_ands [$1;$3] }
| and_or_expr "||" and_or_expr  { mk_ors  [$1;$3] }
| FORALL lvar "." and_or_expr   { mk_forall $2 $4 }
| pred_expr                     { $1 }

pred_expr:
| arith_expr                 { $1               }
| arith_expr pred arith_expr { mk_pred $2 $1 $3 }

arith_expr:
| app_expr                 { $1                }
| arith_expr op arith_expr { mk_op $2  [$1;$3] }
| "-" arith_expr %prec NEG { mk_op Arith.Sub [mk_int 0;$2] }

app_expr:
| atom atom* { mk_apps $1 $2 }

atom:
| INT  { mk_int   $1 }
| bool { mk_bool  $1 }
| lvar { mk_var   $1 }
| uvar { mk_var   $1 }
| "(" hflz ")" { $2 }

(******************************************************************************)
(* Predicate                                                                  *)
(******************************************************************************)

env:
| START_ENV assignment* { $2 }

assignment:
| uvar ":" abstraction_ty DOT { $1, $3 }

abstraction_ty:
| TBOOL                    { Type.TyBool[]   }
| TBOOL "[" separated_list(";", predicate) "]" { Type.TyBool($3) }
| lvar ":" abstraction_argty "->" abstraction_ty
    { let x = Id.{ name=$1; id=(-1); ty=$3 } in
      Type.TyArrow(x, $5)
    }
| abstraction_argty "->" abstraction_ty
    { let x = Id.{ name="_"; id=(-1); ty=$1 } in
      Type.TyArrow(x, $3)
    }

abstraction_argty:
| TINT                   { Type.TyInt      }
| "(" abstraction_ty ")" { Type.TySigma $2 }

predicate:
| and_or_predicate { $1 }

and_or_predicate:
| and_or_predicate "&&" and_or_predicate { Formula.mk_ands [$1;$3] }
| and_or_predicate "||" and_or_predicate { Formula.mk_ors  [$1;$3] }
| a_predicate                            { $1                      }

a_predicate:
| atom_predicate { $1 }
| arith pred arith { Formula.mk_pred $2 [$1;$3] }

arith:
| atom_arith          { $1                                  }
| arith op arith      { Arith.mk_op $2  [$1;$3]             }
| "-" arith %prec NEG { Arith.mk_op Sub Arith.[mk_int 0;$2] }

atom_arith:
| "(" arith ")" { $2                                          }
| INT           { Arith.mk_int $1                             }
| lvar          { let x = Id.{ name=$1; ty=`Int; id=(-1) } in
                  Arith.mk_var x
                }

atom_predicate:
| TRUE  { Formula.Bool true  }
| FALSE { Formula.Bool false }
| "(" predicate ")"     { $2 }


(******************************************************************************)
(* Util                                                                       *)
(******************************************************************************)

%inline op:
| "+" { Arith.Add  }
| "-" { Arith.Sub  }
| "*" { Arith.Mult }
| "/" { Arith.Div }
| "%" { Arith.Mod }

pred:
| "="  { Formula.Eq  }
| "<>" { Formula.Neq }
| "<=" { Formula.Le  }
| ">=" { Formula.Ge  }
| "<"  { Formula.Lt  }
| ">"  { Formula.Gt  }

def_fixpoint:
| "=v" { Fixpoint.Greatest }
| "=m" { Fixpoint.Least    }


lambdas:
| lambda* { List.concat $1 }
lambda:
| LAMBDA lvar* "." { $2 }

lvar:
(* Adhoc way. Because hoice complains the use of _ as an identity *)
| LIDENT { if $1 = "_" then "replaced!" else $1 }

uvar:
| UIDENT { $1 }

bool:
| TRUE  { true  }
| FALSE { false }
