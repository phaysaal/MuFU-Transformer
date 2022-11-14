open Hflmc2_syntax

module L = Tools
module H = Raw_hflz
module T = Transformer
module P = Printer
module S = Set.Make(Int)
module U = MatchMaker
         
type ('a, 'b) t = Fail of 'a | Succeed of 'b
(** 
    0. Take an singleton queue with the goal formula
    1. Take the popped formula
    2. Unfold all predicates one by one in the formula
    3. push them in the queue.
    4. Repeat max
 *)
                                        

  
let unfold f defs =
  T.exec_unfold defs f 
;;

let unfold_nth_pred formula defs n =
  let comb res f1 f2 f aux =
    match res with
      Succeed f1' ->
      Succeed (f f1' f2)
    | Fail i' ->
       let res2 = aux i' f2 in
       match res2 with
         Succeed f2' ->
          Succeed (f f1 f2')
       | _ -> res2
  in
  let comb_list i aux =
    List.fold_left
      (fun (acc, res1) f ->
        match res1 with
          Succeed fs -> ([], Succeed (fs@[f]))
        | Fail i ->
           let res2 = aux i f in
           match res2 with
             Succeed f' -> [], Succeed (acc@[f'])
           | Fail i' -> (acc@[f], Fail i')  
      ) ([], Fail i)
  in
  let rec aux i = function
    | H.Bool _ -> Fail i
  | H.Var _ -> Fail i
  | H.Or (f1, f2) ->
     let res = aux i f1 in
     comb res f1 f2 (fun a b -> H.Or (a,b)) aux
  | H.And (f1, f2) ->
     let res = aux i f1 in
     comb res f1 f2 (fun a b -> H.And (a,b)) aux
  | H.Abs (s, f1) ->
     comb (Fail i) f1 f1 (fun _ b -> H.Abs (s,b)) aux
  | H.App _ as f ->
     if i=n then
       Succeed (unfold f defs)
     else
       Fail (i+1)
  | H.Int _ -> Fail i
  | H.Op (a, fs) ->
     begin
       let _, res = comb_list i aux fs in
       match res with
         Succeed fs' -> Succeed (H.Op (a, fs'))
       | Fail i' -> Fail i'
     end
  | H.Pred (s, fs) ->
     begin
       let _, res = comb_list i aux fs in
       match res with
         Succeed fs' -> Succeed (H.Pred (s, fs'))
       | Fail i' -> Fail i'
     end
  | H.Exists (s, f1) ->
     comb (Fail i) f1 f1 (fun _ b -> H.Exists (s,b)) aux
  | H.Forall (s, f1) ->
     comb (Fail i) f1 f1 (fun _ b -> H.Forall (s,b)) aux
  in
  aux 1 formula
;;

let unfold_all_pred formula defs =
  let rec aux acc i =
    let nth_unfolded_formula = unfold_nth_pred formula defs i in
    match nth_unfolded_formula with
      Fail _ -> acc
    | Succeed new_formula -> 
      aux (new_formula::acc) (i+1)
  in
  aux [] 1

  
let try_match goal unfolded =
  P.pp_formula goal |> P.dbg "goal: ";
  P.pp_formula unfolded |> P.dbg "-> ";
  let connective = L.get_connective goal in
  let uniq_con = L.is_uniconnected unfolded in
  P.dbg "uniconnected: " (if uniq_con then "true" else "false");
  let broken_formula = L.break unfolded in
  let broken_goal    = L.break goal in
  let n = List.length @@ broken_goal in
  let perms = L.permute broken_formula in
  let rec match_formulas () =
    let perm = Stream.next perms in
    let perm_n, _ = L.take n perm in
    let perm_n' = L.join connective perm_n in
    let res = U.unify goal perm_n' in
    match res with
      None ->
       P.pp_formula perm_n' |> P.dbg "Matching failed";
      match_formulas ()
    | Some _ ->
       
       let formula = L.join connective perm in
       P.pp_formula perm_n' |> P.dbg "@@@ Matching found @@@";
       Some formula
  in
  let res = try match_formulas () with Stream.Failure -> None in
  res
;;

let formula_to_rule predname goal connective formula =
  let fix = (if connective=L._or then Fixpoint.Greatest else Fixpoint.Least) in
  let fv_f' = U.fv formula in
  let params = List.filter (fun v -> List.mem v fv_f') goal.H.args in
  let newrule = T.mk_rule predname params fix formula in
  newrule, params

let are_all_single defs =
  List.for_all (fun d -> L.is_single d.H.body) defs

let make_head rule =
  let args = rule.H.args in
  let var = rule.H.var in
  let body = List.fold_left (fun body arg -> H.mk_forall arg body) rule.H.body args in
  let newrule = {H.var=var; args=[]; fix=Fixpoint.Greatest; body=body} in
  newrule
;;

let rec try_match_quicker max defs_map goal unfolded =
  let goal_body = goal.H.body in
  if L.is_uniconnected goal_body then
    let connective = L.get_connective goal_body in
    let rec aux unfolded =
      if L.is_connected_with connective unfolded then
        let predname = T.new_predicate_name () in
        let (is_match, f') = U.find_matching goal.H.fix predname goal.H.args goal_body unfolded in
        if is_match then
          begin
            let newpred, params = formula_to_rule predname goal connective f' in
            let vparams = List.map H.mk_var params in
            
            let f = U.implode_pred predname vparams in
            Some (newpred, f, f')
          end
        else
          None
      else
        begin
        let normal_unfolded = (if connective = L._or then T.cnf_of_formula else T.dnf_of_formula) unfolded in
        P.pp_formula normal_unfolded |> P.dbg "Normal_unfolded";
        let splitted_formulas = (if connective = L._or then U.get_conjuncts else U.get_disjuncts) normal_unfolded in
        let res = List.fold_left
                    (fun acc formula ->
                      match acc with
                        None ->
                         begin
                           match aux formula with
                             None -> None
                           | Some (newpred, f, f') -> Some ([newpred], [f], [f'], [formula])
                         end
                      | Some (newpreds, fs, fs', formulas) ->
                         match aux formula with
                           None -> None
                         | Some (newpred, f, f') -> Some (newpreds@[newpred], fs@[f], fs'@[f'], formulas@[formula])
                    ) None splitted_formulas in
          match res with
        | Some (newpred::_, fs, fs', formulas) ->
           let rest = List.filter (fun sf -> not (List.exists (fun f -> sf=f) formulas)) splitted_formulas in
           let otherdefs, rest' = List.fold_left (fun (odefs, acc) formula ->
                                      if L.has_more_than_one_app formula then
                                        begin
                                          let np = T.new_predicate_name () in
                                          let goal', _ = formula_to_rule np goal connective formula in
                                          P.pp_rule goal' |> P.dbgn " New Rule to be pattern matched";
                                          let queue = Queue.create () in
                                          Queue.push goal.H.body queue;
                                          let res = unfold_until_max_or_matched max queue goal' defs_map 0 in
                                          match res with
                                            Some (r, x, _) ->
                                             (r::odefs, x::acc)
                                          | None -> (odefs, formula::acc)
                                        end
                                      else
                                        (odefs, formula::acc)
                                    ) ([], []) rest in
           let full_formula = L.join connective (fs'@rest) in
           let fs'' = L.join connective (fs) in
           let newpred' = T.mk_rule newpred.H.var newpred.H.args newpred.H.fix full_formula in 
           Some (newpred', fs'', full_formula)
        | _ -> None
        end
    in
    aux unfolded
  else
    failwith "Mix of connectives in the goal not supported"

and try_match_switch max defs_map goal unfolded =
  let res = try_match_quicker max defs_map goal unfolded in
  (* try_match goal.H.body unfolded *)
  (* match res with
    None -> None
  | Some f'' ->
     let fv_f'' = U.fv f'' in
     let params = List.filter (fun v -> List.mem v fv_f'') goal.H.args in
     let newpred = T.mk_rule goal.var params goal.fix f'' in
     P.pp_rule newpred |> P.dbg "RULE()";
     Some ([newpred],params)
   *)
  res
  
and unfold_until_max_or_matched max queue goal defs_map i =
  if Queue.is_empty queue then
    None
  else
    begin let formula = Queue.pop queue in
          P.pp_formula formula |> P.dbg ("To be unfolded " ^ (string_of_int i) ^ " ");
          let unfoldeds = unfold_all_pred formula defs_map in
          P.pp_list P.pp_formula unfoldeds |> P.dbgn "Unfolded formulas";
          let res =
            List.fold_left (fun res unfolded ->
                match res with
                  None -> 
                   begin match try_match_switch max defs_map goal unfolded with
                     None ->
                      Queue.push unfolded queue; None
                   | res' -> res'
                   end
                | _ -> res
              ) None unfoldeds in
          match res with
            None -> if i < max
                    then unfold_until_max_or_matched max queue goal defs_map (i+1)
                    else None
          | _ -> res
    end
  
let start_analysis max goal defs env =
  
  let defs_map = T.make_def_map defs in
  let alldefs =
    if are_all_single defs then
      begin
        P.dbg "Single-mode" "";
        let alldefs : H.hes_rule list = T.transform_hes defs goal env in
        alldefs
    end
  else
    begin
      P.dbg "Multi-mode" "";
      let queue = Queue.create () in
      (* let unfoldeds = unfold_all_pred goal.H.body defs_map in
      List.iter (fun uf -> Queue.push uf queue) unfoldeds; *)
      Queue.push goal.H.body queue;
      (* let max = 2 in *)
      let res = unfold_until_max_or_matched max queue goal defs_map 0 in
      match res with
        Some (r, x, _) ->
         P.pp_formula x |> P.dbg "@@Matched";
         P.pp_rule r |> P.dbg "@@New rule";
         let goal_pred = {H.var=goal.H.var; args=goal.args; fix=goal.fix; body=x} in
         goal_pred::r::defs
         
      | None -> P.dbg "!!! Matched None" ""; failwith "Not folded"
    end
  in
  print_endline "~*~*~*~*~*~*~*~*~*~*~*";    
  let head = List.hd alldefs |> make_head in
  let result = head::List.tl alldefs in
  let outtxt1 = P.pp_list ~sep:"\n" P.pp_rule result in

  let outtxt = "%HES\n" ^ outtxt1 in 
  outtxt |> P.dbgn "Result";

  outtxt 

