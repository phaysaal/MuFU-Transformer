open Hflmc2_syntax
module H = Raw_hflz 

let get_preds =
  let rec aux res = function
    | H.App (H.Var s, _) ->
       s::res
    | H.Pred (_, hflzs) ->
       List.fold_left aux res hflzs
    | H.And (hflz1, hflz2) 
      | H.Or (hflz1, hflz2)
      | H.App (hflz1, hflz2) ->
       let res1 = aux res hflz1 in
       aux res1 hflz2
    | H.Abs (_, hflz) -> aux res hflz
    | H.Op (_, hflzs) ->
       List.fold_left aux res hflzs
    | H.Exists (_, hflz) ->
       aux res hflz
    | H.Forall (_, hflz) ->
       aux res hflz
    | _ -> res
  in
  aux []
;;

let seperate_goal_and_defs (hes : H.hes) =
  let uniq = List.sort_uniq String.compare in
  let get_called_preds rule =
    (get_preds rule.H.body)
  in
  let called = uniq (List.concat (List.map get_called_preds hes)) in
  let seperate_goal rule =
    let hd = rule.H.var in
    List.mem hd called
  in
  let aux, goal = List.partition seperate_goal hes in
  (aux, goal)
