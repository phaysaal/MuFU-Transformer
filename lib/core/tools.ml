module H = Hflmc2_syntax.Raw_hflz
module F = Hflmc2_syntax.Formula
module FX = Hflmc2_syntax.Fixpoint
module S = Set.Make(Int)

exception Strange of string
                   
let _or = 0
let _and = 1
let _exists = 2

let pause msg =
    
      if msg = "" then print_endline "Paused. Press ENTER to continue." else print_endline msg;
      let _ = read_line () in
      ()
;;

let get_connective = function
    H.Or _ -> _or
  | H.And _ -> _and
  | H.Exists _ -> _exists
  | _ -> -1

let rev_connective = function
    0 -> _and
  | 1 -> _or
  | _ -> failwith "No reverse"
       
let rec take n = function
    [] when n>0 -> failwith "take"
  | [] -> ([],[])
  | (x::xs) as xs' ->
     if n=0
     then ([], xs')
     else let (xs'', zs) = take (n-1) xs in
          (x::xs'',zs)
;;

let make_head rule =
  let args = rule.H.args in
  let var = rule.H.var in
  let body = List.fold_left (fun body arg -> H.mk_forall arg body) rule.H.body args in
  let newrule = {H.var=var; args=[]; fix=FX.Greatest; body=body} in
  newrule
;;


let rec join c xs =
  let xs' = List.filter (function
                  H.Pred (F.Eq, [H.Int 0; H.Int 0]) when c = _and -> false
                | H.Bool true when c = _and -> false
                | H.Pred (F.Neq, [H.Int 0; H.Int 0]) when c = _or -> false
                | H.Bool false when c = _or -> false
                | _ -> true
              ) xs in
  if List.length xs' = 1 then List.hd xs'
  else if c = _and then H.mk_ands xs'
  else if c = _or then H.mk_ors xs'
  else failwith "Invalid connective"
;;

let permute lst =
  let rec range i n =
    if i=n then [] else i::range (i+1) n in
  let nth i s =
    let ls = S.elements s in
    let ls' = List.sort (fun a b -> a-b) ls in
    List.nth ls' i in
  let lstar = Array.of_list lst in
  let len   = Array.length lstar in
  let ks    = range 1 (len + 1) in
  let indices = S.of_list (range 0 len) in
  let choose k (v, indices, res) =
    let idx = v mod k in
    let ix = try (nth idx indices) with _ -> print_endline ("Not actually found " ^ (string_of_int idx)); raise Not_found in
    (v / k, S.remove ix indices, lstar.(ix) :: res)
  in
  let perm i =
    let (v, _, res) =
      List.fold_right choose ks (i, indices, [])
    in
    if v > 0 then None else Some res
  in
  Stream.from perm
;;

let rec is_connected_with i = function
  | H.Or (f1, f2) ->
     i=_or && is_connected_with i f1 && is_connected_with i f2
  | H.And (f1, f2) ->
     i=_and && is_connected_with i f1 && is_connected_with i f2
  | _ -> true
;;

let is_uniconnected formula =  
  match formula with
  | H.Or (f1, f2) ->
     is_connected_with _or f1 && is_connected_with _or f2
  | H.And (f1, f2) ->
     is_connected_with _and f1 && is_connected_with _and f2
  | _ -> true
;;

let rec break_at conn f =
  match f with
  | H.Or (f1, f2) ->
     if conn=0 then break_at conn f1 @ break_at conn f2 else [f]
  | H.And (f1, f2) ->
     if conn=1 then break_at conn f1 @ break_at conn f2 else [f]
  | _ -> [f]
  
let break formula = 
  match formula with
  | H.Or (f1, f2) ->
     break_at _or f1 @ break_at _or f2
  | H.And (f1, f2) ->
     break_at _and f1 @ break_at _and f2
  | _ -> [formula] 
;;

let rec rec_break formula = 
  match formula with
  | H.Or (f1, f2) ->
     rec_break f1 @ rec_break f2
  | H.And (f1, f2) ->
     rec_break f1 @ rec_break f2
  | _ -> [formula] 
;;

let rec has_app f =
  match f with
    H.And (f1, f2)  
  | H.Or (f1, f2) -> has_app f1 || has_app f2
  | H.App _ -> true
  | H.Exists (_,f) -> has_app f
  | _ -> false
;;
let rec has_one_app = function
  | H.Or (f1, f2)
  | H.And (f1, f2) ->
     if has_one_app f1 then
       not (has_app f2)
     else
       has_one_app f2
  | H.Exists (_, f) ->
     has_one_app f
  | H.App _ -> true
  | _ -> false
;;
let has_no_app f = not (has_app f)
;;
let has_more_than_one_app f = has_app f && not (has_one_app f)
;;
let is_single f =
  let r = has_one_app f in
  r
;;

let rec get_predicates = function
    H.App _ as f -> [f]
  | H.And (f1, f2) ->
     get_predicates f1 @ get_predicates f2
  | H.Or (f1, f2) ->
     get_predicates f1 @ get_predicates f2
  | _ -> []
;;

let rec get_predicates_ex = function
    H.App _ as f -> [f]
  | H.And (f1, f2) ->
     get_predicates_ex f1 @ get_predicates_ex f2
  | H.Or (f1, f2) ->
     get_predicates_ex f1 @ get_predicates_ex f2
  | H.Exists _ as f -> [f]
  | _ -> []
;;

let is_const = function
      H.Int _ ->
       true
    | _ ->
       false
;;

let get_int = function H.Int i -> i | _ -> raise (Strange "Not an Int");;

let get_str = function H.Var v -> v | x -> raise (Strange ("Not a Var " ^ Printer.pp_formula x));;

let get_permutation_stream inp =
  let stream = permute (List.rev inp) in
  stream
;;
  
let get_permutations inp =
  let stream = get_permutation_stream inp in
  let rec fact n =
    if n=0 then 1 else fact (n-1) * n in
  let list = Stream.npeek (fact (List.length inp)) stream in
  list
;;

