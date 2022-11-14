open Hflmc2_syntax
   
module H = Raw_hflz
module T = Transformer
module P = Printer
module S = Set.Make(Int)
module U = MatchMaker
         
module D = Map.Make(String)
module AP = ArithmeticProcessor

exception NotImplemented of string
                          
let get_size_change_graph defs =
  raise (NotImplemented "Size Change Graph")
  
let get_reg_ex size_change_graph =
  raise (NotImplemented "Reg Ex")
  
let get_summary_info reg_ex =
  raise (NotImplemented "Summary Info")

let get_constraints summary_info formula =
  raise (NotImplemented "Constraint")

let get_model constraints =
  raise (NotImplemented "Model")

let get_unfolded_formula formula model =
  raise (NotImplemented "Unfolded")

let get_transformed_formula formula rule_head rule_body =
  raise (NotImplemented "Unfolded")
         
let transform defs rule =
  let rule_name = rule.H.var in
  let rule_body = rule.H.body in
  let size_change_graph = get_size_change_graph defs in
  let reg_ex = get_reg_ex size_change_graph in
  let summary_info = get_summary_info reg_ex in
  let constraints = get_constraints summary_info rule_body in
  let model = get_model constraints in
  let unfolded_formula = get_unfolded_formula rule_body model in
  let transformed_rule = get_transformed_formula unfolded_formula rule_name rule_body in
  transformed_rule
