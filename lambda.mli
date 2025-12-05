type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  | TyAlias of string (*type for type aliases *)
  | TyString           (*type string*)
  | TyTuple of ty list (*type tuple*)
  | TyRecord of (string * ty) list  (*type record*)
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
  | TmFix of term
  | TmString of string        (*term string*)
  | TmConcat of term * term   (*concat operator *)
  | TmTuple of term list      (*term for tuples*)
  | TmProj of term * int      (*term for projections*)
  | TmRecord of (string * term) list  (* pair list (tag, value) *)
  | TmProjVar of term * string       (* projection for tags (string) *)
;;

type sentence =
  | Eval of term
  | Bind of string * term
  | Alias of string * ty

val emptyctx : context;;
val addbinding : context -> string -> ty -> context;;
val getbinding : context -> string -> ty;;

val string_of_ty : ty -> string;;
exception Type_error of string;;
val typeof : context -> term -> ty;;

val string_of_term : term -> string;;
exception NoRuleApplies;;
val eval : term -> term;;

(*Types and functions for global declarations*)
type global_entry =
  | GlobalValue of term
  | GlobalType of ty

type global_context = (string * global_entry) list

val emptygctx : global_context
val addglobal : global_context -> string -> global_entry -> global_context
val getglobal : global_context -> string -> global_entry
val expand_globals : global_context -> term -> term
val expand_aliases : global_context -> term -> term

