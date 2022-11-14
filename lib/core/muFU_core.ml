open Hflmc2_syntax
open Transformer

module T = Transformer
module H = Raw_hflz
module P = Printer
module M = Mult_transformer
         

let print_cnf_goal_formula cnf_goal =
  P.pp_formula cnf_goal |> P.dbgn "CNF of Goal:"
;;

let print_goal goal =
  P.pp_rule goal |> P.dbgn "Goal:";
;;

let print_seperation aux goal =
  print_goal goal;
  P.pp_hes aux |> P.dbgn "AUX:";
;;



let transform (hes : H.hes) env : string =
  
  let aux, goals = Seperator.seperate_goal_and_defs hes in
  let goal = List.hd goals in
  print_seperation aux goal;

  M.start_analysis 5 goal aux env

  (*
  let alldefs : H.hes_rule list = T.transform_hes aux goal env in
  print_endline "~*~*~*~*~*~*~*~*~*~*~*";

  let head = List.hd alldefs |> make_head in
  let result = head::List.tl alldefs in
  let outtxt1 = P.pp_list ~sep:"\n" P.pp_rule result in

  let outtxt = "%HES\n" ^ outtxt1 in 
  outtxt |> P.dbgn "Result";

  outtxt
  *)
  
  (* Z3Interface.get_model ();
  "Done" *);;
