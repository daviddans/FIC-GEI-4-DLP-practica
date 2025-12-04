
type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  | TyString           (*type string*)
  | TyTuple of ty list (*type tuple*)
;;

type context =
  (string * ty) list
;;

type term =
    TmTrue
  | TmFalse
  | TmIf of term * term * term
  | TmZero
  | TmSucc of term
  | TmPred of term
  | TmIsZero of term
  | TmVar of string
  | TmAbs of string * ty * term
  | TmApp of term * term
  | TmLetIn of string * term * term
  | TmString of string        (*term string*)
  | TmConcat of term * term   (*concat operator *)
  | TmTuple of term list      (*term for tuples*)
  | TmProj of term * int      (*term for projections*)
;;

val emptyctx : context;;
val addbinding : context -> string -> ty -> context;;
val getbinding : context -> string -> ty;;

val string_of_ty : ty -> string;;
exception Type_error of string;;
val typeof : context -> term -> ty;;

val string_of_term : term -> string;;
exception NoRuleApplies;;
val eval : term -> term;;

