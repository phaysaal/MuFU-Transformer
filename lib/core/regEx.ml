module P = Printer   
module H = Hflmc2_syntax.Raw_hflz
module A = Hflmc2_syntax.Arith
module F = Hflmc2_syntax.Formula
module AP = ArithmeticProcessor
         
type param    = string
                  [@@ deriving show,ord,iter,map,fold]
type sc       = (param * int * param)
                  [@@ deriving ord,show,iter,map,fold]
type pred     = string
                  [@@ deriving ord,show,iter,map,fold]
module D      = Map.Make(String)
type edge     = pred * sc list * pred * int
                              [@@ deriving ord,show,iter,map,fold]
type m = H.raw_hflz [@@ deriving ord,show,iter,map,fold]
type regex = EmpSet
              | EmpStr
              | Char of edge
              | Concat of regex * regex
              | Alter of regex list
              | Star of regex
                          [@@ deriving ord,show,iter,map,fold]

type c_re = CEmpSet
          | CEmpStr
          | CChar of edge
          | CConcat of c_re * c_re
          | CIter of c_re * m
                              [@@ deriving ord,show,iter,map,fold]

type xxx = XEmp
         | XCh of edge
         | XCat of (xxx list * m) * (xxx list * m)
         | XIter of (xxx list * m * m)
                      [@@ deriving ord,show,iter,map,fold]
                   
type nfa_edge  = pred * edge list
                          [@@ deriving ord,show,iter,map,fold]
type gedge     = ScRE of regex
               | AbsRE of pred * regex
               | AlterRE of gedge list
                              [@@ deriving ord,show,iter,map,fold]

let show_sc (a, i, b) =
  "(" ^ a ^ "," ^ (string_of_int i) ^ "," ^ b ^ ")"
  (* (* a ^ "." ^ *) string_of_int i (* ^ "." ^ b *) *)
  
let show_edge (a, d, b, tag) =
  (* "{" ^ P.pp_list show_sc ~sep:"," d ^ "}" *)
  a ^ "{" ^ (P.pp_list show_sc d) ^ "}" ^ b ^ ":" ^ (string_of_int tag)
  (* "e_{" ^ a ^ b ^ (string_of_int tag) ^ "}" *)
                          
let rec show_regex = function
    EmpSet -> ""
  | EmpStr -> "EMP"
  | Char ss -> show_edge ss
  | Concat (a, b) -> show_regex a ^ "." ^ show_regex b
  | Alter bs -> "(" ^ (P.pp_list show_regex ~sep:" | " bs) ^ ")"
  | Star a -> match a with
                EmpSet -> ""
              | EmpStr -> "e"
              | Char _ -> "{" ^ show_regex a ^ "}^*"
              | _ -> "(" ^ show_regex a ^ ")^*"
;;

let rec show_raw_hflz = function
    H.Var s -> s
  | H.Int i -> string_of_int i
  | H.Or (a,b) -> "!(" ^ show_raw_hflz a ^ ") \\to " ^ show_raw_hflz b
  | H.Pred (F.Gt, a::b::_) -> show_raw_hflz a ^ ">" ^ show_raw_hflz b
  | H.Pred (F.Ge, a::b::_) -> show_raw_hflz a ^ ">=" ^ show_raw_hflz b
  | H.Pred (F.Lt, a::b::_) -> show_raw_hflz a ^ "<" ^ show_raw_hflz b
  | H.Pred (F.Le, a::b::_) -> show_raw_hflz a ^ "<=" ^ show_raw_hflz b
  | H.Op (A.Sub, a::b::_) ->  show_raw_hflz a ^ "-" ^ show_raw_hflz b
  | h -> H.show_raw_hflz h

let rec iterS f c = function
    [] -> ""
  | [x] -> f x
  | x::xs -> f x ^ iterS f c xs
       
let rec show_xxx = function
    XEmp -> ""
  | XCh a -> Format.sprintf "(%s)" (show_edge a)
  | XCat ((a,ma),(b,mb)) -> Format.sprintf "(%s^{%s} %s^{%s})" (iterS show_xxx "" a) (show_raw_hflz ma) (iterS show_xxx "" b) (show_raw_hflz mb)
  | XIter (a,m,n) -> Format.sprintf "[%s^{%s}->%s]" (iterS show_xxx "" a) (show_raw_hflz m) (show_raw_hflz n)  
       
let rec show_c_re = function
    CEmpSet -> ""
  | CEmpStr -> "E"
  | CChar s -> show_edge s
  | CConcat (a, b) -> show_c_re a ^ "." ^ show_c_re b
  | CIter (a,b) -> "(" ^ show_c_re a ^ ")^{" ^ (show_raw_hflz b) ^ "}"
;;

let rec show_gedge = function
    ScRE scre ->
    "(" ^ show_regex scre ^ ")"
  | AbsRE (pred, gedge) ->
     pred ^ "(" ^ show_regex gedge ^ ")"
  | AlterRE gedges ->
     "(" ^ (P.pp_list show_gedge ~sep:" \\mid " gedges) ^ ")"
;;

let nv = ref 0;;

let newvar () =
  nv := !nv+1;
  H.Var ("m" ^ (string_of_int !nv))
;;


let rec mk_alter (xs : regex list) =
  match xs with
    [] -> failwith "Empty list in alter"
  | x::[] ->
     let r = x in
     r
  | _ ->
     let r = Alter xs in
     r;;

let mk_alterRE gedges =
  let gedges' = List.fold_left (fun acc g ->
                    match g with
                      ScRE _ -> g::acc
                    | AbsRE _ -> g::acc
                    | AlterRE (x::[]) -> x::acc
                    | AlterRE gs ->
                       gs @ acc
                  ) [] gedges in
  AlterRE (List.rev gedges')
  
let rec to_common = function
    ScRE _ as g -> g
  | AbsRE _ as g -> g
  | AlterRE gedges ->
     let rec aux = function
         [] -> []
       | (ScRE _ as g)::gs ->
          let gs' = aux gs in
          g::gs'
       | (AbsRE (pred, re))::gs ->
          let matched, unmatched = List.partition (function AbsRE (p,_) when p=pred -> true | _ -> false) gs in
          let snds = List.map (function AbsRE (_,re) -> re | _ -> failwith "Totally unexpected") matched in
          let g' = AbsRE (pred, mk_alter (re::snds)) in
          let gs' = aux unmatched in
          g'::gs'
       | (AlterRE _ as g)::gs ->
          let g' = to_common g in
          let gs' = aux gs in
          g'::gs'
     in
     let r = aux gedges in
     if List.length r = 0 then
       ScRE EmpStr
     else if List.length r = 1 then
       List.hd r
     else
       mk_alterRE r

let rec is_final x = function
    ScRE _ -> true
  | AbsRE (p,_) -> p=x
  | AlterRE gedges -> List.for_all (is_final x) gedges
;;                                                

let build_gnfa (graph : ((pred * (param * int * param) list * int) list) D.t) : gedge D.t =
  let build_gnfa_edge from_pred edges =
    let aux (to_pred, sc_infos, i) =
      let scre = Char (to_pred, sc_infos, from_pred, i) in
      AbsRE (to_pred, scre) in
    let xs = List.map aux edges in
    mk_alterRE xs |> to_common in
  D.mapi build_gnfa_edge graph

let concat_alter xs =
  List.fold_left (fun acc -> function AlterRE xs -> acc @ xs | x -> acc @ [x]) [] xs
  
let get_re_from_absre = function
    AbsRE (_, re) -> re
  | _ -> failwith "Impossoble 3"
    
let rec reduce gnfa dest head = function 
    ScRE _ as scre -> scre  (* T_(B -> A) a  -->  a *)
  | AbsRE (pred, re) when head = pred ->
     ScRE (Star re) (* T_(B -> A) B a --> B a *)
  | AbsRE (pred, _) as g when pred = dest ->
     g
  | AbsRE (pred, re) ->
     let re' = replace gnfa pred re in (* T_(B -> A) C a --> (body of C)a *)
     re'
  | AlterRE gedges -> (* T_(B -> A) (a | b) -->   *)
     let gedges' = mk_common gedges in
     let mt, unmt = List.partition (function AbsRE (pr, _) -> pr=head | _ -> false) gedges' in
     if List.length mt = 0 then
       begin
         let unmt' = List.map (reduce gnfa dest head) unmt in
         mk_alterRE unmt' end
     else if List.length mt = 1 then
       begin let mst = Star (get_re_from_absre @@ List.hd mt) in 
             let unmt'' = List.map (fun x -> concat x (ScRE mst)) unmt in
             if List.length unmt'' = 0 then
               ScRE mst
             else if List.length unmt'' = 1 then
               List.hd unmt''
             else
               mk_alterRE unmt end
     else
       failwith "Impossible 2"

and mk_common = function
    [] -> []
  | (AbsRE (pr, _) as x)::_ as xs ->
     begin let mt, unmt = List.partition (function AbsRE (p,_) -> p=pr | _ -> false) xs in 
           let mt_res : regex list = List.map (function AbsRE (_,d) -> d | _ -> failwith "Impossible") mt in  
           match mt_res with
             [] -> failwith "Impossible"
           | _::[] -> x::mk_common unmt
           | _ -> AbsRE (pr, Alter (mt_res))::mk_common unmt   
     end
  | x::xs -> x::mk_common xs
           
and replace gnfa pred re = (* pred re --> (body of pred) re *)
  let body = D.find pred gnfa in
  let rec aux = function
      ScRE x -> ScRE (Concat (x, re))  (* (x) r --> (x r) *)
    | AbsRE (pred, x) -> let r = AbsRE (pred, Concat (x, re)) in (* (A x) r --> A (x r)  *)
                         r
    | AlterRE gedges ->
       let gedges' = List.map aux gedges in
       AlterRE gedges' (* (x | y) r --> (x r | y r) *)
  in
  aux body
  
and concat a b =
  match a, b with
    ScRE a', ScRE b' -> ScRE (Concat (a',b'))
  | AbsRE (pred, a'), ScRE b' -> AbsRE (pred, Concat (a', b'))
  | AlterRE gedges, ScRE _ -> AlterRE (List.map (fun a' -> concat a' b) gedges) 
  | _, _ -> failwith "Unexpected so far"

let rec is_rec dest = function
    ScRE _ -> false
  | AbsRE (pred, _) -> pred = dest
  | AlterRE edges -> List.exists (is_rec dest) edges
                                
let eval gnfa body x =
  reduce gnfa x x body |> reduce gnfa x x

let (--) a b = H.Op (A.Sub, [a;b]);;
let (>>) a b = H.Pred (F.Gt, [a;b]);;
let (<<=) a b = H.Pred (F.Le, [a;b]);;
let (||) a b = H.Or (a,b);;
let zero = H.Int 0;;
let one = H.Int 1;;

let rec simplify_alter = function
  | Concat (x,y) ->
     Concat (simplify_alter x, simplify_alter y)
  | Star x ->
     Star (simplify_alter x)
  | Alter ([]) -> EmpStr
  | Alter ([x]) -> x
  | Alter (x::xs) ->
     List.fold_left (fun x y ->
         Alter ([simplify_alter x; simplify_alter y])
       ) x xs
  | g -> g
;;

let simplify_alter = function
    ScRE x -> simplify_alter x
  | _ -> failwith "Strange Input as gedge"
    
let rec re_to_cs m = function
    EmpSet -> CEmpSet, []
  | EmpStr -> CEmpStr, []
  | Char a -> CIter (CChar a, m), []
  | Alter (x::y::[]) ->
     let m1 = newvar () in
     let x',c1 = re_to_cs m1 x in
     let y',c2 = re_to_cs (m--m1) y in
     CConcat (x',y'), c1@c2@[m1<<=m] 
  | Concat (Alter (x::y::_), z) ->
     let m1 = newvar () in
     let x',c1 = re_to_cs m1 (Concat (x,z)) in
     let y',c2 = re_to_cs (m--m1) (Concat (y,z)) in
     CConcat (x',y'), c1@c2@[m1<<=m]
  | Concat (z, Alter (x::y::_)) ->
     let m1 = newvar () in
     let x',c1 = re_to_cs m1 (Concat (z,x)) in
     let y',c2 = re_to_cs (m--m1) (Concat (z,y)) in
     CConcat (x',y'), c1@c2@[m1<<=m]
     
  | Concat (x,y) ->
     let x',c1 = re_to_cs one x in
     let y',c2 = re_to_cs one y in
     CIter (CConcat (x',y'), m), c1@c2
  | Star x ->
     let m1 = newvar () in
     let x',cs = re_to_cs m1 x in
     x', cs@[(m1 <<= zero) || (m >> zero)]
  | _ -> failwith "Unsupported and Unnatural"

let eq a b = H.mk_pred F.Eq a b
let neq a b = H.mk_pred F.Neq a b

let gt a b = H.mk_pred F.Gt a b
let leq a b = H.mk_pred F.Le a b

let add a b = H.mk_op A.Add [a;b]
let sub a b = H.mk_op A.Sub [a;b]
let mul a b = H.mk_op A.Mult [a;b]

let _true = H.mk_bool true
          
let mk_and a b = if a = _true then b
                 else if b = _true then a
                 else H.mk_and a b

let rel a b = (* H.mk_or (leq a zero)  (gt b zero) *) H.mk_or (neq b zero)  (eq a zero) 

let get model (x:string) =
  try
    H.Int (D.find x model)
  with
    Not_found ->
    P.dbg "Not found" x;
    raise Not_found

let rec has_star r : bool =
  match r with 
    CIter _ -> true
  | CConcat (a,b) ->
     let a1 : bool = has_star a in
     let b1 : bool = has_star b in
     if a1 then true else if b1 then true else false
  | _ -> false

let cconcat a b =
  if a = CEmpStr then b
  else if b = CEmpStr then a
  else CConcat (a,b)
  
let rec star_free = function
    CIter _ -> CEmpStr
  | CConcat (a, b) ->
     cconcat (star_free a) (star_free b)
  | r -> r
       
let rec straight m ms r =
  let ms' = ms @ [m] in
  (* Printf.printf "%s , %s -> %s\n" (show_regex r) (iterS P.pp_formula "." ms) (P.pp_formula m); *)
  match r with
    EmpSet -> CEmpSet, H.mk_bool true, []
  | EmpStr -> CEmpStr, H.mk_bool true, []
  | Char a -> CIter ((CChar a), m), H.mk_bool true, [(r,ms,[])]
  | Alter (a::b::_) ->
     let m1 = newvar () in
     let m2 = newvar () in
     let (a', f1, s1) = straight m1 ms' a in
     let (b', f2, s2) = straight m2 ms' b in
     CConcat (a', b'), mk_and (eq (add m1 m2) m) @@ mk_and f1 f2, s1@s2@[r,ms,[m1;m2]]
  | Concat (a, b) ->
     let (a', f1, s1) = straight m ms' a in
     let (b', f2, s2) = straight m ms' b in
     CConcat (a', b'), mk_and f1 f2, s1@s2@[r,ms,[]]
  | Star a ->
     let m1 = newvar () in
     let (a', f, s) = straight m1 ms' a in
     a', H.mk_ands [f; rel m1 m], s@[r,ms,[m1]]
  | _ -> failwith "Invalid Alter"

let expand_star a n =
  let b = has_star a in
  if b then
    let a' = star_free a in
    if a' = CEmpStr then
      a
    else
      let a'' = CIter (a', AP.normalize @@ sub n one) in 
      CConcat (a, a'')
  else
    CIter (a, n)

module Z = Z3Interface
module T = UFCommon


let list_to_D d =
  List.fold_left (fun mp (x,y) -> D.add x y mp) D.empty d
;;
         
let solve cs model_old =
  P.pp_list P.pp_formula cs |> P.dbg "Local Constraints";
  let rec mk_simple_model f =    
    let v = T.fv f |> List.hd in
    match f with
      H.Pred (F.Eq, _::y::_) as f ->
       let y' = AP.normalize y in
       (v, Tools.get_int y')
    | _ -> failwith "Invalid Case: Not an Eq"
  in
  let is_simple =
    let fvs = List.map T.fv cs |> List.concat |> List.sort_uniq String.compare in
    List.for_all (fun v -> let v' = H.Var v in List.exists (function H.Pred (F.Eq, x::_::_) -> AP.normalize x = v'| _ -> false) cs) fvs
  (* List.exists (fun s -> List.length (T.fv s) > 1) cs *) in
  if not is_simple then
    begin P.dbg "Complex Model:" "Yes";
          let cs' = List.fold_left H.mk_and (H.Bool true) cs in
          let model = Z.solve_model cs' @ model_old in
          P.pp_list (fun (s,i) -> Printf.sprintf "%s: %d, " s i) model |> P.dbg "model";
          list_to_D model
    end
  else
    begin P.dbg "Complex Model:" "No";
      let model = List.map mk_simple_model cs @ model_old in
      P.pp_list (fun (s,i) -> Printf.sprintf "%s: %d, " s i) model |> P.dbg "model";
      list_to_D model
    end
  
let compile model (a': (c_re * H.raw_hflz list) list) =
  let a'' = List.map (fun (x,m) ->
                let n = newvar () in
                (x, (m,n))) a' in
  let cvs = List.map snd a' |> List.concat |> List.sort (fun a b -> String.compare (P.var_to_str a) (P.var_to_str b)) in
  let cs = List.fold_left (fun acc v ->
               try let vs = List.filter (fun (_, (ms,_)) -> List.mem v ms) a'' |> List.map (fun (_,(_,n)) -> n)  in
                   let vs' = List.fold_left (fun a b -> add a b) zero vs in
                   let v' = get model (P.var_to_str v)  in
                   acc@[(eq vs' v')]
               with _ -> acc
             ) [] cvs in
  let cs' = solve cs (D.fold (fun x v acc -> acc@[(x,v)]) model []) in
  let rs = List.fold_left (fun acc (a, (_, n)) ->
               try
                 let i = get cs' (P.var_to_str n) in
                 acc@[expand_star a i]
               with
                 Not_found -> acc@[a]
             ) [] a'' in
  let r1' = List.fold_left (fun a b -> CConcat (a,b)) CEmpStr rs in
  r1'
;;

let rec m_eval model = function
    H.Int x -> x
  | H.Var m ->
     D.find m model
  | H.Op (A.Sub, a::b::_) ->
     let a' = m_eval model a in
     let b' = m_eval model b in
     a'-b'
  | _ -> failwith "Out of scope"

let rec crecon model cr =
  
  match cr with
    CEmpSet -> CEmpSet
  | CEmpStr -> CEmpStr
  | CChar a -> CChar a
  | CConcat (a, b) ->
     let a' = crecon model a in
     let b' = crecon model b in
     CConcat (a',b')
  | CIter (a, m) ->
     let a' = crecon model a in
     let v = m_eval model m |> H.mk_int in
     
     CIter (a', v)

let rec recon model s m ms r =
  let ms' = ms @ [m] in
  let (_, _, nm) = List.find (fun (r',ms',_) -> r=r' && ms=ms') s in   
  match r with
    EmpSet -> [(CEmpSet,[m])]
  | EmpStr -> [(CEmpStr,[m])]
  | Char a -> [(CChar a,[m])]
  | Alter (a::b::_) ->
     begin match nm with
       m1::m2::_ ->
       let a' = recon model s m1 ms' a in
       let b' = recon model s m2 ms' b in
       a' @ b'
     | _ -> failwith "Invalid Alter" end
  | Concat (a, b) ->
     let a' = recon model s m ms' a in
     let b' = recon model s m ms' b in
     List.map (fun (x,m1) -> List.map (fun (y,m2) -> CConcat (x,y),m1@m2) b') a' |> List.concat
  | Star a ->
     let n = List.hd nm in
     let a' = recon model s n ms' a in
     let r1 = compile model a' in
     [r1,[m]]
  | _ -> failwith "Invalid Alter"

let recon model s m r =
  let a' = recon model s m [] r in
  let r1 = compile model a' in
  r1
;;


(* ((a|b)(c|d))^n -> 
   a -> m1
   b -> m2
   c -> m3
   d -> m4
   (ac)^n1,(bc)^n2,(ad)^n3,(bd)^n4
   [m1,m3]->n1  [m2,m3]->n2  [m1,m4]->n3  [m2,m4]->n4
   n1+n3=m1
   n1+n2=m3
   n2+n4=m2
   n3+n4=m4
   n=n1+n2+n3+n4

   (abc)^n ->
   abc, [n,n,n]->n1
   n=n1    
   
   (a(b)^m2 c)^n ->
   abc, [m1,m2,m1]->n1
   n1=n
   m1=n1
   
 *)
  
let rec f m = function
    EmpSet -> ([], zero)
  | EmpStr -> ([], zero)
  | Char a -> ([CChar a], m)
  | Alter (a::b::_) ->
     let m1 = newvar () in
     let m2 = newvar () in
     let (a', _) = f m1 a in
     let (b', _) = f m2 b in
     a' @ b', m
  | Concat (a, b) ->
     let (a', _) = f m a in
     let (b', _) = f m b in
     List.concat @@ List.map (fun a'' -> List.map (fun b'' -> CConcat (a'',b'')) b') a', m
  | Star a ->
     let m1 = newvar () in
     let (a', n) = f m1 a in
     List.map (fun a'' -> CIter(CIter (a'',n), m)) a', m
  | _ -> failwith "Invalid Alter"


let rec abs_summary_info = function
    CEmpStr -> []
  | CEmpSet -> []
  | CConcat (a,b) ->
     let da = abs_summary_info a in
     let db = abs_summary_info b in
     (* List.mapi (fun i (x,i1,_) ->
         let (_,i2,z) = (* try
             List.find (fun (y',_,_) -> y=y') db
           with
             Not_found ->
             P.dbg "a:" (show_c_re a);
             P.dbg "b:" (show_c_re b);
             raise Not_found *)
           List.nth db i 
         in
         (x,add i1 i2,z)
       ) da
     *)
     List.map (fun (x,i1,y) ->
         let (_,i2,z) = try
             List.find (fun (y',_,_) -> y=y') db
           with
             Not_found ->
             P.dbg "a:" (show_c_re a);
             P.dbg "b:" (show_c_re b);
             raise Not_found 
         in
         (x,add i1 i2,z)
       ) da
  | CIter (a, n) ->
     let da = abs_summary_info a in
     List.map (fun (x,i,y) -> (x,mul i n,y)) da
  | CChar (_, deltas, _, _) ->
     List.map (fun (x,i,y) -> (x, H.mk_int i, y)) deltas
     

let rec concat_n x n =
  if n = 0 then []
  else
    x @ (concat_n x (n-1))
;;

let rec flatten = function
    CEmpStr -> []
  | CEmpSet -> []
  | CConcat (a,b) ->
     let da = flatten a in
     let db = flatten b in
     da @ db
  | CIter (a, n) ->
     let da = flatten a in
     let i = Tools.get_int n in
     concat_n da i
  | CChar (_, _, dest, tag) ->
     [(dest,tag)]


let rec src_dest = function
    CChar (_, b, _, _) ->
    let src_dest = List.map (fun (x,_,y) -> (x,y)) b in
    src_dest
  | CConcat (a, b) ->
     let sda = src_dest a in
     let sdb = src_dest b in
     let r = List.fold_left (fun acc (x,y) ->
                 let ys = List.filter (fun (z,_) -> z=y) sdb in
                 let ws = List.map (fun (_, w) -> (x,w)) ys in
                 acc @ ws
               ) [] sda in

     r
  | CIter (a, _) ->
     src_dest a
  | _ -> []
;;

let min_iter x =
  let sdx = src_dest x in
  let rec aux e c sd =
    if List.for_all (fun (x,y) -> x=y) sd then
      (e, c)
    else
      let d'' = List.fold_left (fun acc (x, y) ->
                    let ys = List.filter (fun (z,_) -> z=y) sdx in
                    let ws = List.map (fun (_, w) -> (x,w)) ys in
                    acc @ ws
                  ) [] sd in
      if d'' = sd then
        begin
          P.pp "x: %s\n" (show_c_re x);
          failwith "Ta da da"
        end
      else
        aux (cconcat e x) (cconcat x x) d''
  in
  aux CEmpStr x sdx
;;

    
let citer m x =
  if has_star x then
    let x'' = star_free x in
    let mx', mx'' = min_iter x'' in
    let x' = if x'' = CEmpStr then CEmpStr else CIter (mx'', sub m one) in
    cconcat (cconcat x mx') x'
  else
    let _, mx' = min_iter x in
    CIter (mx', m)
;;
    
let rec summary_info m = function
  | EmpSet -> [], H.mk_bool true
  | EmpStr -> [CEmpStr], H.mk_bool true
  | Char a -> [CChar a], H.mk_bool true
  | Alter (a::b::_) ->
     let m1 = newvar () in
     let m2 = newvar () in
     let a', (c1 : H.raw_hflz) = summary_info m1 a in
     let a'' = List.map (fun x -> citer m1 x) a' in
     let b', c2 = summary_info m2 b in
     let b'' = List.map (fun x -> citer m2 x) b' in
     a'' @ b'', mk_and (eq (add m1 m2) m) @@ mk_and c1 c2
  | Concat (a, b) ->
     let a', c1 = summary_info m a in
     let b', c2 = summary_info m b in
     let r = List.map (fun x ->
                 List.map (fun y ->
                     cconcat x y) b') a'
             |> List.concat in
     let c = mk_and c1 c2 in
     r, c
  | Star a ->
     let m1 = newvar () in
     let a', (c':H.raw_hflz) = summary_info m1 a in
     let b = List.exists has_star a' in
     let a'' = List.map (citer m1) a' in
     let a''' = List.fold_left (fun a b -> cconcat a b) CEmpStr a'' in
     let r: H.raw_hflz = rel m1 m in 
     let c = mk_and r c' in
     if b then
       [a'''; CEmpStr], c
     else
       [a'''], c
  | _ -> failwith "Unsupported Alter"
;;

let get_summary_info x =
  let m = newvar () in
  let x' = simplify_alter x in (** alter list to alter tuple *)
  let cx, constraints = summary_info m x' in
  let constraints' = mk_and (eq m one) constraints in
  cx, constraints'
  
