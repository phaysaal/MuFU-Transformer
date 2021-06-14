open Hflmc2_syntax

module P = Printer
module H = Raw_hflz

exception UnexpectedExpression


        
let pp_pair (o, f) = (P.pp_op o) ^ "(" ^ P.pp_formula f ^ ")";;

let pp_pairs (o, fs) = (P.pp_op o) ^ "[" ^ P.pp_list ~sep:"" pp_pair fs ^ "]";;

let pp_pairss fs = P.pp_list ~sep:"" pp_pairs fs;;

let eval exp =  
  let rec eval_atomic = function
    | H.Op (Arith.Add, H.Int x::H.Int y::_) -> H.Int (x+y), true
    | H.Op (Arith.Sub, H.Int x::H.Int y::_) -> H.Int (x-y), true
    | H.Op (Arith.Mult, H.Int x::H.Int y::_) -> H.Int (x*y), true
    | H.Op (Arith.Add, x::H.Int 0::_) -> eval_atomic x |> fst, true
    | H.Op (Arith.Add, H.Int 0::x::_) -> eval_atomic x |> fst, true
    | H.Op (Arith.Sub, x::H.Int 0::_) -> eval_atomic x |> fst, true
    | H.Op (Arith.Sub, x1::x2::_) when fst (eval_atomic x1)=fst(eval_atomic x2) -> H.Int 0, true
    | H.Op (Arith.Mult, _::H.Int 0::_) -> H.Int 0, true
    | H.Op (Arith.Mult, H.Int 0::_::_) -> H.Int 0, true
    | H.Op (Arith.Mult, x::H.Int 1::_) -> eval_atomic x |> fst, true
    | H.Op (Arith.Mult, H.Int 1::x::_) -> eval_atomic x |> fst, true
    | H.Op (Arith.Div, x::H.Op(Arith.Div, y::z::[])::[]) -> (** a/(b/c) = (a*c)/b *)
       H.Op (Arith.Div, [H.Op (Arith.Mult, [x;z]);y]), true
    | H.Op (Arith.Div, x::H.Int 1::_) -> x, true
    | H.Op (Arith.Div, _::H.Int 0::_) as f ->
       P.pp_formula f |> P.dbg " Exception";
       raise UnexpectedExpression
    | H.Op (Arith.Div, H.Int x::H.Int y::_) as f ->
       let r = x/y in
       if r*y = x then
         H.Int (x/y), true
       else
         f, false
    | H.Op (Arith.Div, H.Int 0::_::_) -> H.Int 0, true
    | H.Op (Arith.Div, x1::x2::_) when fst(eval_atomic x1)=fst(eval_atomic x2) -> H.Int 1, true
    | H.Op (Arith.Mod, H.Int 0::_::_) -> H.Int 0, true
    | H.Op (Arith.Mod, H.Int c1::H.Int c2::_) when c1<c2 -> H.Int c1, true
    | x -> x, false
  in
  
  let rec eval_comp = function
    | H.Op (Arith.Sub, x::H.Op(Arith.Sub, H.Int 0::y::_)::_) -> H.Op (Arith.Add, [x;y]), true
    | H.Op (op, e1::(H.Op (Arith.Mult, e2::(H.Int (-1))::_))::_)
    | H.Op (op, e1::(H.Op (Arith.Mult, (H.Int (-1))::e2::_))::_) when op = Arith.Add || op = Arith.Sub->
       begin
         let op' =
         match op with
           Arith.Add -> Arith.Sub 
         | Arith.Sub -> Arith.Add
         | Arith.Div ->
            print_endline "DIV";
            raise UnexpectedExpression
         | _ ->
            raise UnexpectedExpression
         in
         H.Op (op', e1::e2::[]) |> eval_comp |> fst, true
       end
    | H.Op (o, (H.Op (Arith.Add, x::y::_))::z::_) when o = Arith.Add || o = Arith.Sub ->
       H.Op (Arith.Add, x::(H.Op(o, y::z::[]))::[]) |> eval_comp |> fst, true
      
    | H.Op (Arith.Sub, H.Op (Arith.Sub, x::y::_)::z::_) ->
       H.Op (Arith.Sub, x::H.Op (Arith.Add, y::z::[])::[]) |> eval_comp |> fst, true
      
    | H.Op (Arith.Add, H.Op (Arith.Sub, x::y::_)::z::_) ->
       H.Op (Arith.Sub, x::H.Op(Arith.Sub, y::z::[])::[]) |> eval_comp |> fst, true
       
    | H.Op (o, x::y::_) ->
       begin
         let x', bx = eval_comp x in
         let y', by = eval_comp y in
         
         if bx && by then
           H.Op (o, x::y::[]) |> eval_comp |> fst, true
         else
           begin
             let f' = H.Op (o, [x';y']) in
             (* P.pp_formula f' |> P.dbg "f'"; *)
             let expr', b = f' |> eval_atomic in
             (* P.pp_formula expr' |> P.dbg "expr'"; *)
             if b then
               expr' |> eval_comp
             else
               expr', false
           end
       end
    | x -> x, false
  in
  let res = eval_comp exp |> fst in
  res
;;

(*
  (a+b)*(c+d) -> a*(c+d) + b*(c+d) --> a*c + a*d + b*c + b*d
  (a+b)/(c+d) -> a/(c+d) + b/(c+d) --> a/(c+d) + b/(c+d)
*)
let sum_of_mult f =
  let mk_op o f1 f2 = H.Op (o, [f1;f2]) in
  let is_sum o = o = Arith.Add || o = Arith.Sub in
  let is_mult o = o = Arith.Mult || o = Arith.Div in
  
  let rec mk_left o' x y =
    match y with
    | H.Op (o, _::_::_) when is_sum o && o'=Arith.Div ->
       y
    | H.Op (o, a::b::_) when is_sum o -> mk_op o (mk_left o' x a) (mk_left o' x b) (* x*(a+b) -> x*a+x*b *)
    | _ -> mk_op o' x y
  in
  let rec mk_right o' x y =
    match x with
    | H.Op (o, a::b::_) when is_sum o -> mk_op o (mk_right o' a y) (mk_right o' b y) (* (a+b)*y -> a*y + b*y *)
    | _ -> mk_left o' x y
  in
  let rec mk f =
    match f with
    | H.Op (o, f1::f2::_) when is_sum o -> mk_op o (mk f1) (mk f2)
    | H.Op (o, f1::f2::_) when is_mult o -> mk_right o (mk f1) (mk f2) (* f1*f2 *)
    | _ -> f 
  in
  mk f
;;

let neg_list xs =
  List.map (function (Arith.Add, [(op, H.Int n)]) when n < 0 ->
                      (Arith.Add, [(op, H.Int (0-n))])
                   | (Arith.Add, x) -> (Arith.Sub, x)
                   | (Arith.Sub, x) -> (Arith.Add, x)
                   | x -> x) xs
;;

let inv_list xs =
  List.map (function (Arith.Mult, x) -> (Arith.Div, x)
                                   | (Arith.Div, x) -> (Arith.Mult, x)
                                   | x -> x) xs
;;

let inv_sum_list xs =
  List.map (fun (op, ys) -> (op, inv_list ys)) xs
;;


let sum_list f =
  let rec mult_list = function
      H.Op (Arith.Mult, a::b::_) ->
       mult_list a @ mult_list b
    | H.Op (Arith.Div, a::b::_) ->
       let res = mult_list b in
       let res' = inv_list res in
       mult_list a @ res'
    | x -> [(Arith.Mult, x)]
  in
  let rec sum_list = function
      H.Op (Arith.Add, a::H.Int i::_) when i<0 ->
       sum_list a @ [Arith.Sub, [(Arith.Mult, H.Int (0-i))]]
    | H.Op (Arith.Add, a::b::_) ->
       sum_list a @ sum_list b
    | H.Op (Arith.Sub, a::b::_) ->
       let res = sum_list b in
       let res' = neg_list res in
       sum_list a @ res'
    | x -> [(Arith.Add, mult_list x)]
  in
  let rec reduce_mult = function
      [] -> []
    | ((Arith.Mult, y) as x)::xs ->
       begin
         match List.partition (function (Arith.Div, y') when y=y' -> true | _ -> false) xs with
           [], _ ->  x::reduce_mult xs
         | _::zs, ws -> reduce_mult (zs@ws)
       end
    | ((Arith.Div, y) as x)::xs ->
       begin
         match List.partition (function (Arith.Mult, y') when y=y' -> true | _ -> false) xs with
         [], _ ->  x::reduce_mult xs
         | _::zs, ws -> reduce_mult (zs@ws)
       end
    | x::xs -> x::reduce_mult xs
  in
  
  let rec reduce_sum = function
      [] -> []
    | ((Arith.Add, y) as x)::xs ->
       begin
         match List.partition (function (Arith.Sub, y') when y=y' -> true | _ -> false) xs with
           [], _ ->  (Arith.Add, reduce_mult y)::reduce_sum xs
         | _::zs, ws -> reduce_sum (zs@ws)
       end
    | ((Arith.Sub, y) as x)::xs ->
       begin
         match List.partition (function (Arith.Add, y') when y=y' -> true | _ -> false) xs with
         [], _ ->  (Arith.Sub, reduce_mult y)::reduce_sum xs
         | _::zs, ws -> reduce_sum (zs@ws)
       end
    | x::xs -> x::reduce_sum xs
  in

  let reduce_int f =
    let rec reduce_int acc = function
        [] -> acc, []
      | (Arith.Add, [(Arith.Mult, H.Int i)])::xs ->
         reduce_int (acc+i) xs
      | (Arith.Sub, [(Arith.Mult, H.Int i)])::xs ->
         reduce_int (acc-i) xs
      | (Arith.Add, [(Arith.Div, H.Int i)])::xs ->
         reduce_int (acc+(1/i)) xs
      | (Arith.Sub, [(Arith.Div, H.Int i)])::xs ->
         reduce_int (acc-(1/i)) xs
      | x::xs ->
         let (r, xs') = reduce_int acc xs in
         (r, x::xs')
    in
    let r, xs' = reduce_int 0 f in
    if r = 0 then
      xs'
    else
      xs' @ [(Arith.Add, [(Arith.Mult, H.Int r)])]
  in
  (* P.pp_formula f |> P.dbg "-----\nf";
  pp_pairss (f |> sum_list) |> P.dbg "sum_list";
  pp_pairss (f |> sum_list |> reduce_sum) |> P.dbg "reduce_sum";
  pp_pairss (f |> sum_list |> reduce_sum |> reduce_int) |> P.dbg "reduce_int"; *)
  f |> sum_list |> reduce_sum |> reduce_int
;;

let var_to_str = function
    H.Var s -> s
  | _ -> ""
;;
     
let cx_d v f =
(*  print_endline "**********";
  f |> P.pp_formula |> P.dbg "f";
  v |> P.id |> P.dbg "v";
 *)
  let is_in v = function
      H.Var w -> w = v
    | _ -> false
  in
  let mult_compare v f1 f2 =
    
    if var_to_str f2 = v then
      begin
        
        1
      end
    else if var_to_str f1 = v then
      begin
        
        -1
      end
    else
      let r = String.compare (H.show_raw_hflz f1) (H.show_raw_hflz f2) in
      if r > 0 then 1 else -1
  in
  let sum_compare v f1 f2 =
    
    let pairs_f1 = List.map snd f1 in
    let pairs_f2 = List.map snd f2 in
    if is_in v (List.hd pairs_f1) && is_in v (List.hd pairs_f2) then
      String.compare (P.pp_list P.pp_formula (List.tl pairs_f1)) (P.pp_list P.pp_formula (List.tl pairs_f2))  
    else if is_in v (List.hd pairs_f1) then
      -1
    else if is_in v (List.hd pairs_f2) then
      1
    else
      let r = String.compare (P.pp_list P.pp_formula pairs_f1) (P.pp_list P.pp_formula pairs_f2) in
      if r > 0 then 1 else -1
  in
  
  
  let rec get_first op = function
      [] -> [],[]
    | ((o,_) as x)::xs ->
       if o = op then
         [x], xs
       else
         let (x', xs') = get_first op xs in
         (x', x::xs')
  in
  let pull op xs =
    let (x, xs') = get_first op xs in
    x @ xs'
  in
  let sort_mult xs =
    List.sort_uniq (fun (_,f1) (_,f2) ->
        mult_compare v f1 f2
      ) xs |> pull Arith.Mult
  in
  let sort_sum xs =
    let xs' = List.map (fun (o, ys) -> (o, sort_mult ys)) xs in
    List.sort_uniq (fun (_, f1) (_, f2) -> sum_compare v f1 f2) xs' |> pull Arith.Add
  in
  let partition_sum fs =
    List.partition (fun (_, gs) -> is_in v (snd (List.hd gs)) ) fs
  in
  let coeff (cx, d) =
    let c = List.map (fun (o, cs) ->
                let cs' = List.tl cs in
                if List.length cs' = 0 then
                  (o, [(Arith.Mult, H.Int 1)])
                else
                  (o, cs')
              ) cx in
    (c, d)
  in
  (* f |> sum_list |> sort_sum |> partition_sum |> fst |> P.pp_list pp_pairs |> P.dbg "after sumlist"; *)
  f |> sum_list |> sort_sum |> partition_sum |> coeff (* |> reconstruct *)
;;

let rec inv = function
    H.Op (Arith.Mult, x::y::_) ->
     H.Op (Arith.Div, inv x::inv y::[])
  | H.Op (Arith.Div, x::y::_) ->
     H.Op (Arith.Mult, inv x::inv y::[])
  | x -> x;;

let rec neg = function
    H.Op (Arith.Add, x::y::_) ->
     H.Op (Arith.Sub, inv x::neg y::[])
  | H.Op (Arith.Sub, x::y::_) ->
     H.Op (Arith.Add, inv x::neg y::[])
  | x -> x
;;

let rec list_to_mult = function
    [] -> H.Int 0
  | [(Arith.Mult, x)] -> x
  | [(Arith.Div, x)] -> H.Op (Arith.Div, [H.Int 1;x])                  
  | (Arith.Mult, x)::((Arith.Div, _)::_ as xs) ->
     let inv_xs = inv_list xs in
     let xs_exp = list_to_mult inv_xs in
     (* let y_xs = H.Op (Arith.Div, [y;inv xs_exp]) in *)
     H.Op (Arith.Div, [x;xs_exp])
  | (Arith.Mult, x)::ys ->
     H.Op (Arith.Mult, [x;list_to_mult ys])
  | f ->
     P.pp_list pp_pair f |> P.dbg " Exception in list_to_mult";
     raise UnexpectedExpression;;

let rec simplify_mult = function
    [] -> []
  | (Arith.Mult, x)::xs ->
     let duals, others = List.partition (function (Arith.Div, y) when x=y -> true | _ -> false) xs in
     if List.length duals > 0 then
       simplify_mult (List.tl duals @ others)
     else
       (Arith.Mult, x)::simplify_mult xs
  | (Arith.Div, x)::xs ->
     let duals, others = List.partition (function (Arith.Mult, y) when x=y -> true | _ -> false) xs in
     if List.length duals > 0 then
       simplify_mult (List.tl duals @ others)
     else
       (Arith.Div, x)::simplify_mult xs
  | _ ->
     raise UnexpectedExpression;;

let simplify_mult' (op, xs) =
  (op, simplify_mult xs)
    
let rec simplify_sum = function
    [] -> []
  | (Arith.Add, x)::xs ->
     let duals, others = List.partition (function (Arith.Sub, y) when x=y -> true | _ -> false) xs in
     if List.length duals > 0 then
       simplify_sum (List.tl duals @ others)
     else
       (Arith.Add, simplify_mult x)::simplify_sum xs
  | (Arith.Sub, x)::xs ->
     let duals, others = List.partition (function (Arith.Add, y) when x=y -> true | _ -> false) xs in
     if List.length duals > 0 then
       simplify_sum (List.tl duals @ others)
     else
       (Arith.Sub, simplify_mult x)::simplify_sum xs
  | _ ->
     raise UnexpectedExpression;;

let rec list_to_sum = function
    [] -> H.Int 0
  | [(Arith.Add, x)] -> list_to_mult x
  | [(Arith.Sub, x)] -> H.Op (Arith.Sub, [H.Int 0; list_to_mult x])                  
  | (Arith.Add, x)::((Arith.Sub, _)::_ as xs) ->
     (* P.pp_list pp_pairs xs |> P.dbg " xs"; *)
     (** +x -y [+z; +w; +v] *)
     (** +x -y [-z; -w; -v] *)

     (** +x - [+y; -z; -w; -v] *)
     (** +x - [+y; +z; +w; +v] *)
     
     let neg_xs = neg_list xs in
     (* P.pp_list pp_pairs neg_xs |> P.dbg " neg xs"; *)
     
     let xs_exp = list_to_sum neg_xs in
     (* P.pp_formula xs_exp |> P.dbg " xs_exp"; *)
     (** +x -y +(z+w) *)
     (** +x -(y-(z+w)) *)
     (*     let y_xs = H.Op (Arith.Sub, [list_to_mult y;xs_exp]) in *)
     (** x + y + z) *)
     H.Op (Arith.Sub, [list_to_mult x;xs_exp])
  | (Arith.Add, x)::ys ->
     H.Op (Arith.Add, [list_to_mult x;list_to_sum ys])
  | (Arith.Sub, _)::_ as xs ->
     H.Op (Arith.Sub, [H.Int 0;list_to_sum (neg_list xs)])
  | f ->
     P.pp_list pp_pairs f |> P.dbg " Exception in list_to_sum";
     raise UnexpectedExpression;;

let list_to_exp xs =
  let f' = list_to_sum (simplify_sum xs) in
  (* P.dbg "list_to_sum" (P.pp_formula f'); *)
  f' |> eval
  
;;

(*
  a/(a+b) --> (a/a)+(a/b) 
  1/(1+2)=1/3     1/1 + 1/2=3/2
  (a+b)/(c+d) --> a/(a+b) + b/(c+d)
 *)

let list_div xs ys =

  let ys', xs' =
    match ys with
      (Arith.Sub, _)::_ ->
      neg_list ys, neg_list xs
    | _ -> ys, xs
  in
  
  let op, ys'' =
    match ys' with
      (_, (Arith.Div, _)::_)::_ ->
      Arith.Mult, inv_sum_list ys'
    | _ ->
       Arith.Div, ys'
  in
  
  (* P.dbg "xs'.." (P.pp_list pp_pairs xs');
  P.dbg "ys'.." (P.pp_list pp_pairs ys');
  P.dbg "ys''.." (P.pp_list pp_pairs ys''); *)
  let x = list_to_exp xs' in
  let y = list_to_exp ys'' in
  (* P.dbg "x.." (P.pp_formula x);
  P.dbg "y.." (P.pp_formula y); *)
  
  H.Op (op, [x;y]) |> sum_of_mult |> eval
;;

let reconstruct v (c, d) =
  let c' = list_to_sum c |> eval in
  let d' = list_to_sum d |> eval in
  H.Op (Arith.Add, [H.Op (Arith.Mult, [H.Var v;c']);d'])
;;


let normalize_v v f =
  f |> eval |> sum_of_mult |> cx_d v |> reconstruct v |> eval
;;

let normalize f =
  (* P.dbg "f" (P.pp_formula (f));
  P.dbg "eval" (P.pp_formula (f |> eval));
  P.dbg "eval + sum_of_mult" (P.pp_formula (f |> eval |> sum_of_mult));
  P.dbg "eval + sum_of_mult + sum_list" (pp_pairss (f |> eval |> sum_of_mult |> sum_list));
  P.dbg "eval + sum_of_mult + sum_list + list_to_exp" (P.pp_formula (f |> eval |> sum_of_mult |> sum_list |> list_to_exp)); *)
  f |> eval |> sum_of_mult |> sum_list |> list_to_exp
;;
