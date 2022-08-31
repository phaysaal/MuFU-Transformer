
open Hflmc2_util
open Id
open Type

type t =
  | Bool of bool
  | Var  of abstracted_ty Id.t
  (* If `Original, t list must have just 2 elements
   * TODO It may be better to devide constructors *)
  | Or   of t list * [ `Original | `Inserted ]
  | And  of t list * [ `Original | `Inserted ]
  | Abs  of abstracted_ty Id.t * t
  | App  of t * t
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type hes_rule =
  { var  : abstracted_ty Id.t
  ; body : t
  ; fix  : Fixpoint.t
  }
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type hes = hes_rule list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

(* Construction *)

let mk_var x = Var x

let mk_ands ?(kind=`Original) = function
  | [] -> Bool true
  | [x] -> x
  | xs -> And(xs, kind)

let mk_ors ?(kind=`Original) = function
  | [] -> Bool false
  | [x] -> x
  | xs -> Or(xs, kind)

let mk_app t1 t2 = App(t1,t2)
let mk_apps t ts = List.fold_left ts ~init:t ~f:mk_app

let mk_abs x t = Abs(x, t)
let mk_abss xs t = List.fold_right xs ~init:t ~f:mk_abs

let mk_const : 'ty -> t -> t =
  fun ty t ->
    let x = Id.gen ty in
    Abs(x, t)

let mk_identity : abstracted_ty -> t =
  fun ty ->
    let x = Id.gen ty in
    Abs(x, Var x)

(* Deconstruct *)

let decompose_abs =
  let rec go acc phi = match phi with
    | Abs(x,phi) -> go (x::acc) phi
    | _ -> (List.rev acc, phi)
  in
  go []

let decompose_app =
  let rec go phi acc = match phi with
    | App(phi,x) -> go phi (x::acc)
    | _ -> (phi, acc)
  in
  fun phi -> go phi []

(* free variables *)
let rec fvs = function
  | Var x          -> IdSet.singleton x
  | Bool _         -> IdSet.empty
  | Or (phis,_)    -> IdSet.union_list (List.map phis ~f:fvs)
  | And(phis,_)    -> IdSet.union_list (List.map phis ~f:fvs)
  | App(phi1,phi2) -> IdSet.union (fvs phi1) (fvs phi2)
  | Abs(x,phi)     -> IdSet.remove (fvs phi) x

(* type *)
let rec type_of = function
  | Var x -> x.ty
  | App (phi, _) ->
      begin match type_of phi with
      | ATyArrow(_, ret_ty) -> ret_ty
      | _ -> assert false
      end
  | Abs (x, phi) -> ATyArrow(x.ty, type_of phi)
  | _ -> ATyBool

