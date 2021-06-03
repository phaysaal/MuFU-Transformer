open Hflmc2_syntax
module H = Raw_hflz
module A = Arith
module F = Formula
module FP = Fixpoint

let rec pp_list f ?(sep=",") = function
    [] -> ""
  | [x] -> f x
  | x::xs -> f x ^ sep ^ pp_list ~sep:sep f xs
;;

let id x = x
;;

let pp_op = function
    A.Add -> "+"
  | A.Sub -> "-"
  | A.Mult -> "*"
  | A.Div -> "/"
  | A.Mod -> "%"
;;

let pp_pred = function
    F.Eq -> "="
  | F.Neq -> "<>"
  | F.Le -> "<="
  | F.Ge -> ">="
  | F.Lt -> "<"
  | F.Gt -> ">"
;;

let rec pp_formula = function
    H.Bool true -> "(0 = 0)"
  | H.Bool false -> "(0 <> 0)"
  | H.Var s -> s
  | H.Or (f1, f2) -> "(" ^ pp_formula f1 ^ " \\/ " ^ pp_formula f2 ^ ")"
  | H.And (f1, f2) -> "(" ^ pp_formula f1 ^ " /\\ " ^ pp_formula f2 ^ ")"
  | H.Abs (s, f) -> "\\" ^ s ^ "." ^ pp_formula f 
  | H.App (f1, f2) -> pp_formula f1 ^ " " ^ pp_formula f2
  | H.Int i -> if i < 0 then "(" ^ string_of_int i ^ ")" else string_of_int i
  | H.Op (o, fs) -> "(" ^ (List.map pp_formula fs |> pp_list id ~sep:(pp_op o)) ^ ")"
  | H.Pred (p, fs) -> List.map pp_formula fs |> pp_list id ~sep:(pp_pred p)
  | H.Forall (s, f) -> "∀ " ^ s ^ "." ^ pp_formula f
  | H.Exists (s, f) -> "∃" ^ s ^ "." ^ pp_formula f
;;

let pp_munu = function
    FP.Least -> "=μ"
  | FP.Greatest -> "=v"
              

let pp_rule rule =
  rule.H.var ^ " " ^ (pp_list id ~sep:" " rule.H.args) ^ " " ^ pp_munu rule.H.fix ^ " " ^ pp_formula rule.H.body
;;

let pp_hes hes =
  pp_list pp_rule ~sep:"\n" hes
;;

let dbg tag str =
  tag ^ ": " ^ str
  |> print_endline
;;

let dbgn tag str =
  tag ^ ": " |> print_endline;
  str        |> print_endline
