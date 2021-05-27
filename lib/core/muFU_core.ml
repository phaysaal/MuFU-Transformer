open Hflmc2_syntax
open Transformer
   
module H = Raw_hflz
module P = Printer
         

let print_cnf_goal_formula cnf_goal =
  P.pp_formula cnf_goal |> P.dbgn "CNF of Goal:";
;;

let print_goal goal =
  P.pp_rule goal |> P.dbgn "Goal:";
;;

let print_seperation aux goal =
  print_goal goal;
  P.pp_hes aux |> P.dbgn "AUX:";
;;

         
let transform (hes : H.hes) : H.hes =
  let aux, goals = Seperator.seperate_goal_and_defs hes in
  let goal = List.hd goals in
  print_seperation aux goal;

  let alldefs : H.hes_rule list = transform_hes aux goal in
  print_endline "~*~*~*~*~*~*~*~*~*~*~*";
  P.pp_list ~sep:"\n" P.pp_rule alldefs |> P.dbgn "Result";
  alldefs

