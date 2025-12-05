type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  | TyList of ty
  | TyAlias of string               (* Type for type aliases (user-defined names) *)
  | TyString                        (* Type for text strings *)
  | TyTuple of ty list              (* Type for tuples (sequences of typed elements) *)
  | TyRecord of (string * ty) list  (* Type for records (list of labeled fields) *)
  | TyVariant of (string * ty) list    (* type variant *)
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
  | TmFix of term                   (* Fixed-point combinator for recursion *)
  | TmString of string              (* String literal value *)
  | TmConcat of term * term         (* String concatenation operator *)
  | TmTuple of term list            (* Tuple constructor (list of terms) *)
  | TmProj of term * int            (* Tuple projection (access element by index) *)
  | TmRecord of (string * term) list (* Record constructor (list of label-value pairs) *)
  | TmProjVar of term * string      (* Record projection (access field by label) *)
  | TmNil of ty                     (* Empty list (Nil), carries the type of its elements *)
  | TmCons of term * term           (* Cons constructor: adds a head element to a tail list *)
  | TmIsNil of term                 (* Check if the list is empty (returns boolean) *)
  | TmHead of term                  (* Retrieve the head (first element) of the list *)
  | TmTail of term                  (* Retrieve the tail (rest of the list) *)
  | TmVariant of string * term (*term for variant values*)
  | TmAs of term * ty (*term for type ascription*)
  | TmCase of term * (string * string * term) list (*term for pattern matching construcction*)
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

