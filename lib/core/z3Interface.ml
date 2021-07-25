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
  | e ->
     P.pp_formula e |> P.dbg "Unsupported";
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
   )
;;

exception TestFailException of string
                             
let solve_model f =
  let cfg = [("model", "true"); ("proof", "false")] in
  let ctx = (mk_context cfg) in

  let f' = hflz_to_z3 ctx f in
  let g = mk_goal ctx true false false in
  Goal.add g [f'];

  let ar = Tactic.apply (and_then ctx (mk_tactic ctx ("simplify")) (mk_tactic ctx "solve-eqs") []) g None in

  let solver = mk_solver ctx None in
  let f e = Solver.add solver [ e ] in
  ignore (List.map f (get_formulas (get_subgoal ar 0)));
  let q = check solver [] in
  
  if q != SATISFIABLE then
    raise (TestFailException "UNSAT")
  else
    let m = get_model solver in
    match m with
      None -> raise (TestFailException "NO_MODEL")
      | Some m ->
         let ds = Model.get_const_decls m in
         let model = List.fold_left (fun model d ->
                         let e = FuncDecl.apply d [] in
                         match Z3.Model.eval m e true with
                           None -> model
                         | Some v ->
                            if Expr.is_numeral v then
                              (FuncDecl.get_name d |> Symbol.get_string, Expr.to_string v |> int_of_string)::model
                            else
                              model
                       ) [] ds
         in
         model
;;

(*         
         List.iter (fun d ->
             
             
             let Some v = Z3.Model.eval m exp true in
             Printf.printf "%s %d %s\n" (Symbol.get_string (FuncDecl.get_name d)) (List.length ps) (Expr.to_string v)) ds;
         Printf.printf "Solver says: %s\n" (string_of_status q) ;
	       Printf.printf "Model: \n%s\n" (Model.to_string m)
 *)       



   (*     
let get_model () =
  let cfg = [("model", "true"); ("proof", "false")] in
  let ctx = (mk_context cfg) in
  Printf.printf "Model Checked Test\n";

  let xs = [H.Pred (Formula.Eq, [H.Var "xx"; H.Var "x"]);
            H.Pred (Formula.Eq, [(H.Op (Arith.Add, [H.Var "yy"; H.Var "zz"])); (H.Op (Arith.Sub, [H.Op (Arith.Add, [H.Var "y"; H.Var "z"]); H.Var "a"]))]);
            H.Pred (Formula.Eq, [H.Var "yy"; (H.Op (Arith.Sub, [H.Var "y"; H.Var "b"]))]);
            H.Pred (Formula.Eq, [H.Var "zz"; (H.Op (Arith.Sub, [H.Var "z"; H.Var "b"]))]);
            H.Pred (Formula.Gt, [H.Op (Arith.Add, [H.Var "a"; H.Var "b"]); H.Int 0]);
           ] in
            
  let xs' = List.fold_left (fun a b -> H.And (a, b)) (List.hd xs) (List.tl xs) in
  let zs  = hflz_to_z3 ctx xs' in
  
  (* let xr = Expr.mk_const ctx (Symbol.mk_string ctx "x") (Integer.mk_sort ctx) in
  let yr = Expr.mk_const ctx (Symbol.mk_string ctx "y") (Integer.mk_sort ctx) in
  let zr = Expr.mk_const ctx (Symbol.mk_string ctx "z") (Integer.mk_sort ctx) in
  let xxr = Expr.mk_const ctx (Symbol.mk_string ctx "x'") (Integer.mk_sort ctx) in
  let yyr = Expr.mk_const ctx (Symbol.mk_string ctx "y'") (Integer.mk_sort ctx) in
  let zzr = Expr.mk_const ctx (Symbol.mk_string ctx "z'") (Integer.mk_sort ctx) in
  let ar = Expr.mk_const ctx (Symbol.mk_string ctx "a") (Integer.mk_sort ctx) in
  let br = Expr.mk_const ctx (Symbol.mk_string ctx "b") (Integer.mk_sort ctx) in
   *)
  let g4 = mk_goal ctx true false false in
(*
  (* x'=x & y'+z'=y+z-a & y'=y-b & z'=z-b *)
  Goal.add g4 [mk_gt ctx ar (Integer.mk_numeral_i ctx 0)];
  Goal.add g4 [mk_gt ctx br (Integer.mk_numeral_i ctx 0)];
  Goal.add g4 [mk_eq ctx xxr xr];
  Goal.add g4 [mk_eq ctx (Arithmetic.mk_add ctx [yyr;zzr]) (Arithmetic.mk_sub ctx [(Arithmetic.mk_add ctx [yr;zr]); ar])];
  Goal.add g4 [mk_eq ctx yyr (Arithmetic.mk_sub ctx [yr;br])];
  Goal.add g4 [mk_eq ctx zzr (Arithmetic.mk_sub ctx [zr;br])]; *)
  Goal.add g4 [zs];
  (*
  Goal.add g4 [mk_eq ctx yr (Arithmetic.mk_add ctx [xr; (Integer.mk_numeral_i ctx 2)])];
  Goal.add g4 [mk_gt ctx yr (Integer.mk_numeral_i ctx 12)]; *)
  (* 
     Printf.printf "Goal: %s\n" (Goal.to_string g4);
  (
    let ar = Tactic.apply (mk_tactic ctx "simplify") g4 None in
    Printf.printf "Tactic: %s\n" (ApplyResult.to_string ar);
    if ((get_num_subgoals ar) == 1 && ((is_decided_sat (get_subgoal ar 0)) || (is_decided_unsat (get_subgoal ar 0)))) then
      raise (TestFailException "")
    else
      Printf.printf "Test Passed\n"
  ); *)
  (
    let ar = Tactic.apply (and_then ctx (mk_tactic ctx ("simplify")) (mk_tactic ctx "solve-eqs") []) g4 None in
    (* if ((get_num_subgoals ar) == 1 && ((is_decided_sat (get_subgoal ar 0)) || (is_decided_unsat (get_subgoal ar 0)))) then
      raise (TestFailException "")
    else
      Printf.printf "Test Passed\n";
     *)
    let solver = mk_solver ctx None in
    let f e = Solver.add solver [ e ] in
    ignore (List.map f (get_formulas (get_subgoal ar 0)));
    let q = check solver [] in
    if q != SATISFIABLE then
      raise (TestFailException "")
    else
      let m = get_model solver in
      match m with
        None -> raise (TestFailException "")
      | Some m ->
         let ds = Model.get_const_decls m in
         List.iter (fun d ->
             let ps = FuncDecl.get_parameters d in
             let exp = FuncDecl.apply d [] in
             let Some v = Z3.Model.eval m exp true in
             Printf.printf "%s %d %s\n" (Symbol.get_string (FuncDecl.get_name d)) (List.length ps) (Expr.to_string v)) ds;
         Printf.printf "Solver says: %s\n" (string_of_status q) ;
	       Printf.printf "Model: \n%s\n" (Model.to_string m) 
  )
    *)
