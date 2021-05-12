open Hflmc2_syntax
   
module H = Raw_hflz
module F = Formula
module A = Arith

module P = Printer

let equiv f1 f2 =
  f1 = f2;;

(*
let is_atomic = function
    H.App _ -> true
  | H.Pred _ -> true
  | _ -> false
 *)

let rec mk_ors = function
    [] -> H.Pred (Formula.Eq, [H.Int 0; Int 1])
  | [f] -> f
  | f::fs ->
     H.Or (f, mk_ors fs)
;;
  
let rec mk_ands = function
    [] -> H.Pred (Formula.Eq, [H.Int 0; Int 0])
  | [f] -> f
  | f::fs ->
     H.And (f, mk_ands fs)
;;

let compare_raw_hflz f1 f2 =
  match f1, f2 with
  | H.Pred _, H.App _ ->
     -1
  | H.App _, H.Pred _ ->
     1
  | _ ->
     H.compare_raw_hflz f1 f2
;;

let rec hflz_to_or_list = function
    H.Or (f1, f2) ->
     let f1' = hflz_to_or_list f1 in
     let f2' = hflz_to_or_list f2 in
     f1' @ f2'
  | f ->
     [cnf_ext f]

and hflz_to_and_list = function
    H.And (f1, f2) ->
      let f1' = hflz_to_and_list f1 in
      let f2' = hflz_to_and_list f2 in
      f1' @ f2'
  | f ->
     [cnf_ext f]
  
and cnf_ext formula =
  match formula with
  (** Equivalence *)
  | H.Or (f1, f2) when equiv f1 f2 ->
     cnf_ext f1
  | H.And (f1, f2) when equiv f1 f2 ->
     cnf_ext f1
  (** Distributivity of | over & *)
  (** (f1 & f2) | f => (f1 | f) & (f2 | f) *)
  | H.Or (H.And (f1, f2), f) ->
     let f' = cnf_ext f in
     H.And (H.Or (cnf_ext f1,f') |> cnf_ext,
            H.Or (cnf_ext f2,f') |> cnf_ext)
  (** x | (y & z) => (y | x) & (z | x) *)
  | H.Or (f, H.And (f1, f2)) ->
     let f' = cnf_ext f in
     H.And (H.Or (f', cnf_ext f1) |> cnf_ext,
            H.Or (f', cnf_ext f2) |> cnf_ext)
  (** Associativity and commutativity *)
  | H.Or _ as f ->
     let fs = hflz_to_or_list f in
     let fs' = List.sort_uniq compare_raw_hflz fs in
     mk_ors fs'
  | H.And _ as f ->
     let fs = hflz_to_and_list f in
    let fs' = List.sort_uniq compare_raw_hflz fs in
    mk_ands fs'
  (** Relational and Arithmetic *)
  | H.Pred (F.Eq, fs) ->
     let fs' = List.sort_uniq compare_raw_hflz fs in
     H.Pred (F.Eq, List.map cnf_ext fs')
  | H.Op (A.Add, fs) ->
     let fs' = List.sort_uniq compare_raw_hflz fs in
     H.Op (A.Add, List.map cnf_ext fs')
  | H.Op (A.Mult, fs) ->
     let fs' = List.sort_uniq compare_raw_hflz fs in
     H.Op (A.Mult, List.map cnf_ext fs')
  | _ -> formula
;;

(*
  (x & y) & (z & w) 
= (x & (y & (z & w)))

  (x1 & x3) & (x4 & x2)
= 
*)
         
let unfold hes = hes;;

let fold hes = hes;;

let rec transform_hes aux (goal : H.hes_rule) = function
    0 -> goal
  | n ->
     let goal' = unfold goal in
     let goal'' = fold goal' in
     transform_hes aux goal'' (n-1)
       
  
  

    
