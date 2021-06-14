open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.FuncDecl
open Z3.Goal
open Z3.Tactic
open Z3.Tactic.ApplyResult
open Z3.Probe
open Z3.Solver
open Z3.Arithmetic
open Z3.Arithmetic.Integer
open Z3.Arithmetic.Real
open Z3.BitVector

open Hflmc2_syntax
   
module H = Raw_hflz
module P = Printer

exception TestFailedException of string

exception UnsupportedFormula of string

let rec arith_to_z3 ctx bounds = function
    H.Var s ->
     begin
       try
         let (_, bv) = List.find (fun (s',_) -> s=s') bounds in
         bv
       with
         _ ->
         Expr.mk_const ctx (Symbol.mk_string ctx s) (Integer.mk_sort ctx)
     end
  | H.Int i ->
     Integer.mk_numeral_i ctx i
  | H.Op (o, fs) ->
     let fs' = List.map (arith_to_z3 ctx bounds) fs in
     begin
       match o with
         Arith.Add ->
         Arithmetic.mk_add ctx fs'
       | Arith.Sub ->
          Arithmetic.mk_sub ctx fs'
       | Arith.Mult ->
          Arithmetic.mk_mul ctx fs'
       | Arith.Div ->
          let a = List.hd fs' in
          let b = List.tl fs' |> List.hd in
          Arithmetic.mk_div ctx a b
       | Arith.Mod ->
           raise (UnsupportedFormula "Mod")
     end
  | _ ->
     raise (UnsupportedFormula "Arith _")
;;

let rec app_to_z3 ctx args bounds = function
    H.App (f1, f2) ->
    app_to_z3 ctx (f2::args) bounds f1
  | H.Var s ->

     let fname = (mk_string ctx s) in
     let args' = List.map (arith_to_z3 ctx bounds) args in
     
    
     let bs = (Integer.mk_sort ctx) in

     let domain = List.map (fun _ -> bs) args' in

     let f = mk_func_decl ctx fname domain (Boolean.mk_sort ctx) in
  
     let fapp = (mk_app ctx f args') in
     fapp
  | _ ->
     raise (UnsupportedFormula "App _")
;;

let op_map = [(Formula.Eq, mk_eq);(Formula.Lt, mk_lt);(Formula.Gt, mk_gt);(Formula.Le, mk_le);(Formula.Ge, mk_ge)]

let rec pred_to_z3 ctx bounds = function
    H.Bool true ->
     Boolean.mk_true ctx
  | H.Bool false ->
     Boolean.mk_false ctx
  | H.App _ as f ->
     app_to_z3 ctx [] bounds f
  | H.Pred (op, f1::f2::_) ->
     begin
       let f1' = arith_to_z3 ctx bounds f1 in
       let f2' = arith_to_z3 ctx bounds f2 in
       match op with
       | Formula.Neq ->
          let ff' = mk_eq ctx f1' f2' in
          (try
            Boolean.mk_not ctx ff'
          with
            e ->
            print_endline (Sort.to_string (Expr.get_sort f1'));
            print_endline (Sort.to_string (Expr.get_sort f2'));
            print_endline (Sort.to_string (Expr.get_sort ff'));
            raise e
          )
       | _ ->
          let _, mk = List.find (fun (op',_) -> op=op') op_map in
          mk ctx f1' f2'
     end
  | H.Exists (s, f) ->
     let s' = Symbol.mk_string ctx s in
     let s'' = Expr.mk_const ctx (Symbol.mk_string ctx s) (Integer.mk_sort ctx) in
     let bv = Quantifier.mk_bound ctx 0 (Integer.mk_sort ctx) in
     let f' = pred_to_z3 ctx ((s,bv)::bounds) f in
     let is = Integer.mk_sort ctx in
     let types = [is] in
     let names = [s'] in
  
     let x = (Quantifier.mk_exists ctx types names f' None [] [] None None) in
     Quantifier.expr_of_quantifier x 
     
  | H.Or (f1, f2) ->
     let f1' = pred_to_z3 ctx bounds f1 in
     
     (try
        let f2' = pred_to_z3 ctx bounds f2 in
        Boolean.mk_or ctx [f1'; f2']
      with
        e ->
        print_endline (P.pp_formula f2);
        raise e
     )
  | H.And (f1, f2) ->
     Boolean.mk_and ctx [pred_to_z3 ctx bounds f1; pred_to_z3 ctx bounds f2]
  | f ->
     P.pp_formula f |> P.dbg "Unsupported Formula for z3 conversion";
     raise (UnsupportedFormula "Pred _")
;;

let rec disj_to_z3 ctx = function
    H.Or (f1, f2) ->
    disj_to_z3 ctx f1 @ disj_to_z3 ctx f2
  | f ->
     [pred_to_z3 ctx [] f]
;;
  

let rec conj_to_z3 ctx = function
    H.And (f1, f2) ->
     let f1' = conj_to_z3 ctx f1  in
     let f2' = conj_to_z3 ctx f2 in
     f1' @ f2'
  | f ->
     let ds : Expr.expr list = disj_to_z3 ctx f in
     let h : Expr.expr = if List.length ds = 1 then
                List.hd ds
              else
                Boolean.mk_or ctx ds
     in
     [h]
;;

let hflz_to_z3 ctx f =
  let cs = conj_to_z3 ctx f in
  let f' = if List.length cs = 1 then
                List.hd cs
              else
                Boolean.mk_and ctx cs
  in
  f'
;;
       
let is_tautology f =
  let cfg = [("proof", "true")] in
  let ctx = mk_context cfg in
  let g = (mk_goal ctx true false false) in
  let f' = hflz_to_z3 ctx f in
  let expr' = Boolean.mk_not ctx f' in
  Goal.add g [ expr' ];
   (
    let solver = (mk_solver ctx None) in
    (List.iter (fun a -> (Solver.add solver [ a ])) (get_formulas g)) ;
    
    let r = check solver [] in
    if r == SATISFIABLE then
      false
    else if r == UNSATISFIABLE then
      true
    else
      false
  );
;;


let is_unsat f =
  let cfg = [("proof", "true")] in
  let ctx = mk_context cfg in
  let g = (mk_goal ctx true false false) in
  let expr' = hflz_to_z3 ctx f in
  Goal.add g [ expr' ];
   (
    let solver = (mk_solver ctx None) in
    (List.iter (fun a -> (Solver.add solver [ a ])) (get_formulas g)) ;
    
    let r = check solver [] in
    if r == SATISFIABLE then
      false
    else if r == UNSATISFIABLE then
      true
    else
      false
  );

