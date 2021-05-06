open Hflmc2_util

(* General Type *)

type 'ty arg
  = TyInt
  | TySigma of 'ty
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type 'annot ty
  = TyBool of 'annot
  | TyArrow of 'annot ty arg Id.t * 'annot ty
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type 'annot arg_ty = 'annot ty arg
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let unsafe_unlift : 'annot arg_ty -> 'annot ty = function
  | TyInt -> invalid_arg "unsafe_unlift"
  | TySigma ty -> ty

let lift_arg x = Id.{ x with ty = TySigma x.ty }

(* Simple Type *)

type simple_ty = unit ty
  [@@deriving eq,ord,show,iter,map,fold,sexp]
type simple_argty = simple_ty arg
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let to_simple : 'a ty -> simple_ty = 
  fun x -> map_ty (fun _ -> ()) x

let mk_arrows : 'annot ty arg Id.t list -> 'annot ty -> 'annot ty =
  fun args ret_ty ->
    List.fold_right args ~init:ret_ty ~f:begin fun arg ret_ty ->
      TyArrow(arg, ret_ty)
    end

let decompose_arrow : 'annot ty -> 'annot ty arg Id.t list * 'annot =
  let rec go acc = function
    | TyBool ann -> List.rev acc, ann
    | TyArrow (x, ty) -> go (x::acc) ty
  in fun x -> go [] x

let rec merge
          : ('annot -> 'annot -> 'annot)
         -> 'annot ty
         -> 'annot ty
         -> 'annot ty =
  fun append ty1 ty2 -> match ty1, ty2 with
    | TyBool a1, TyBool a2 -> TyBool (append a1 a2)
    | TyArrow ({ty=TyInt;_} as x1, rty1)
    , TyArrow ({ty=TyInt;_} as x2, rty2) when Id.eq x1 x2 ->
        TyArrow ( x1, merge append rty1 rty2 )
    | TyArrow ({ty=TySigma aty1;_} as x1, rty1)
    , TyArrow ({ty=TySigma aty2;_} as x2, rty2) when Id.eq x1 x2 ->
        TyArrow
          ( {x1 with ty = TySigma (merge append aty1 aty2)}
          , merge append rty1 rty2 )
    | _ -> invalid_arg "Type.merge"

let merges : ('annot -> 'annot -> 'annot) -> 'annot ty list -> 'annot ty =
  fun append tys -> match tys with
    | [] -> invalid_arg "Type.merges"
    | ty::tys -> List.fold_right ~init:ty tys ~f:(merge append)

(* Abstraction Type *)

type abstraction_ty = Formula.t list ty
  [@@deriving eq,ord,show,iter,map,fold,sexp]
type abstraction_argty = abstraction_ty arg
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type abstracted_ty =
  | ATyBool
  | ATyArrow of abstracted_argty * abstracted_ty
and abstracted_argty = abstracted_ty
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let rec abstract : abstraction_ty -> abstracted_ty = function
  | TyBool preds ->
      (* bool -> ... -> bool -> o *)
      Fn.apply_n_times ~n:(List.length preds)
        (fun ret -> ATyArrow(ATyBool, ret)) ATyBool
  | TyArrow({ Id.ty = TyInt; _ }, ret) ->
      abstract ret
  | TyArrow({ Id.ty = TySigma arg; _}, ret) ->
      ATyArrow(abstract arg, abstract ret)

let rec arity_of_abstracted_ty : abstracted_ty -> int = function
  | ATyBool -> 0
  | ATyArrow(_, aty) -> 1 + arity_of_abstracted_ty aty

