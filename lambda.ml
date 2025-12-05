
(* TYPE DEFINITIONS *)

type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  | TyList of ty
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
  | TmString of string        (*type string*)
  | TmConcat of term * term   (*concat operator*)
  | TmTuple of term list      (*term for tuples*)
  | TmProj of term * int      (*term for projections*)
  | TmRecord of (string * term) list  (* pair list (tag, value) *)
  | TmProjVar of term * string       (* projection for tags (string) *)
  | TmNil of ty                     (* Lista vacía, lleva el tipo explícito *)
  | TmCons of term * term           (* Cons: cabeza y cola *)
  | TmIsNil of term                 (* Chequeo si es vacía *)
  | TmHead of term                  (* Obtener cabeza *)
  | TmTail of term                  (* Obtener cola *)
;;

type sentence =
  | Eval of term
  | Bind of string * term
  | Alias of string * ty

(* Local context managent for type declarations *)

let emptyctx =
  []
;;

let addbinding ctx x bind =
  (x, bind) :: ctx
;;

let getbinding ctx x =
  List.assoc x ctx
;;

(*Global context magement*)

type global_entry =
  | GlobalValue of term
  | GlobalType of ty

type global_context = (string * global_entry) list

let emptygctx : global_context = []

let addglobal gctx name entry =
  (name, entry) :: gctx
  
let rec getglobal gctx name =
  match gctx with
  | [] -> raise Not_found
  | (n, e) :: rest ->
      if n = name then e else getglobal rest name


(* TYPE MANAGEMENT (TYPING) *)

let rec string_of_ty ty = match ty with
    TyBool ->
      "Bool"
  | TyNat ->
      "Nat"
  | TyString ->        (* type string match *)
      "String"
  | TyArr (ty1, ty2) ->
      "(" ^ string_of_ty ty1 ^ ")" ^ " -> " ^ "(" ^ string_of_ty ty2 ^ ")"
;;

let string_of_ty ty =
  let rec aux nest t = (*Aux func to give proper nesting parenthesis*)
    match t with
    | TyBool -> "Bool"
    | TyNat -> "Nat"
    | TyString -> "String" 
    | TyArr (t1, t2) ->
        let left = aux 1 t1 in
        let right = aux 0 t2 in
        let s = left ^ " -> " ^ right in
        if nest > 0 then "(" ^ s ^ ")" else s
    (* case for Tuple Types *)
    | TyTuple l ->
        let s = String.concat ", " (List.map (aux 0) l) in
        "{" ^ s ^ "}"
    (* Case for Record Types*)
    | TyRecord fields ->
        let f (l, t) = l ^ ":" ^ aux 0 t in
        "{" ^ String.concat ", " (List.map f fields) ^ "}"
    | TyAlias s -> s

    | TyList t1 -> 
        "List " ^ aux 0 t1
  in
  aux 0 ty
;;

exception Type_error of string
;;

let rec typeof ctx tm = match tm with
    (* T-True *)
    TmTrue ->
      TyBool
    (* T-False *)
  | TmFalse ->
      TyBool
    (*type string*)
  | TmString _ ->      
      TyString
    (*type of the concat operator term*)
  | TmConcat (t1, t2) -> 
      if typeof ctx t1 = TyString then
        if typeof ctx t2 = TyString then TyString
        else raise (Type_error "second argument of concat is not a string")
      else raise (Type_error "first argument of concat is not a string")
    (* T-If *)
  | TmIf (t1, t2, t3) ->
      if typeof ctx t1 = TyBool then
        let tyT2 = typeof ctx t2 in
        if typeof ctx t3 = tyT2 then tyT2
        else raise (Type_error "arms of conditional have different types")
      else
        raise (Type_error "guard of conditional not a boolean")
    (* T-Zero *)
  | TmZero ->
      TyNat
    (* T-Succ *)
  | TmSucc t1 ->
      if typeof ctx t1 = TyNat then TyNat
      else raise (Type_error "argument of succ is not a number")
    (* T-Pred *)
  | TmPred t1 ->
      if typeof ctx t1 = TyNat then TyNat
      else raise (Type_error "argument of pred is not a number")
    (* T-Iszero *)
  | TmIsZero t1 ->
      if typeof ctx t1 = TyNat then TyBool
      else raise (Type_error "argument of iszero is not a number")
    (* T-Var *)
  | TmVar x ->
      (try getbinding ctx x with
       _ -> raise (Type_error ("no binding type for variable " ^ x)))
    (* T-Abs *)
  | TmAbs (x, tyT1, t2) ->
      let ctx' = addbinding ctx x tyT1 in
      let tyT2 = typeof ctx' t2 in
      TyArr (tyT1, tyT2)
    (* T-App *)
  | TmApp (t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match tyT1 with
           TyArr (tyT11, tyT12) ->
             if tyT2 = tyT11 then tyT12
             else raise (Type_error "parameter type mismatch")
         | _ -> raise (Type_error "arrow type expected"))
    (* T-Let *)
  | TmLetIn (x, t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let ctx' = addbinding ctx x tyT1 in
      typeof ctx' t2

  (* T-Nil: nil[T] tiene tipo List T *)
  | TmNil ty ->
      TyList ty

  (* T-Cons: cons t1 t2 
     Verifica que t2 sea una lista del mismo tipo que t1.
     Devuelve List T. *)
  | TmCons (t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match tyT2 with
       | TyList tyListElem ->
           if tyT1 = tyListElem then TyList tyT1
           else raise (Type_error "elements of list have different types")
       | _ -> raise (Type_error "second argument of cons is not a list"))

  (* T-IsNil: isnil t 
     Verifica que t sea una lista. Devuelve Bool. *)
  | TmIsNil t ->
      (match typeof ctx t with
       | TyList _ -> TyBool
       | _ -> raise (Type_error "argument of isnil is not a list"))

  (* T-Head: head t 
     Verifica que t sea una lista de tipo T. Devuelve T. *)
  | TmHead t ->
      (match typeof ctx t with
       | TyList tyT -> tyT
       | _ -> raise (Type_error "argument of head is not a list"))

  (* T-Tail: tail t 
     Verifica que t sea una lista de tipo T. Devuelve List T. *)
  | TmTail t ->
      (match typeof ctx t with
       | TyList tyT -> TyList tyT
       | _ -> raise (Type_error "argument of tail is not a list"))

    (* T-Tuple: Check type of each element *)
  | TmTuple l ->
        TyTuple (List.map (typeof ctx) l)

    (* T-Proj: Check that subterm is a tuple and index is within bounds *)
  | TmProj (t, i) ->
        (match typeof ctx t with
         | TyTuple fieldTys ->
             (* Verificamos que el índice sea válido (1-based index) *)
             if i < 1 || i > List.length fieldTys then
               raise (Type_error ("projection index " ^ string_of_int i ^ " out of bounds"))
             else
               (* List.nth usa índice 0, por eso restamos 1 *)
               List.nth fieldTys (i - 1)
         | _ -> 
             raise (Type_error "argument of projection is not a tuple"))
   (* T-Record: *)
  | TmRecord fields ->
        let field_tys = List.map (fun (li, ti) -> (li, typeof ctx ti)) fields in
        TyRecord field_tys

    (* T-ProjVar:  *)
  | TmProjVar (t, l) ->
        (match typeof ctx t with
         | TyRecord field_tys ->
             (try List.assoc l field_tys
              with Not_found -> raise (Type_error ("label " ^ l ^ " not found")))
         | _ -> 
             raise (Type_error "Expected record type"))  

  | TmFix t1 ->
      let tyT1 = typeof ctx t1 in
      (match tyT1 with
           TyArr (tyT11, tyT12) ->
             if tyT11 = tyT12 then tyT12
             else raise (Type_error "result of body not compatible with domain")
         | _ -> raise (Type_error "arrow type expected"))
    
;;

(* TERMS MANAGEMENT (EVALUATION) *)

let string_of_term tm =
  let rec aux nest t = (*Give terms proper nesting parenthesis*)
    let s =
      match t with

      | TmTrue -> "true"
      | TmFalse -> "false"
      | TmZero -> "0"
      | TmString s -> "\"" ^ s ^ "\""
      | TmVar x -> x

      | TmSucc t ->
          let rec f n t' = match t' with
          TmZero -> string_of_int n
        | TmSucc s -> f (n+1) s
        | _ -> "succ " ^  aux 1 t 
      in f 1 t

      | TmPred t1 ->
          "pred " ^ aux 1 t1

      | TmIsZero t1 ->
          "iszero " ^ aux 1 t1

      | TmAbs (x, ty, t1) ->
          "lambda " ^ x ^ ":" ^ string_of_ty ty ^ ". " ^ aux 0 t1

      | TmApp (t1, t2) ->
          aux 1 t1 ^ " " ^ aux 1 t2

      | TmIf (t1, t2, t3) ->
          "if " ^ aux 0 t1 ^
          " then " ^ aux 0 t2 ^
          " else " ^ aux 0 t3

      | TmLetIn (x, t1, t2) ->
          "let " ^ x ^ " = " ^ aux 0 t1 ^ " in " ^ aux 0 t2
          
      | TmFix t ->
          "fix " ^ aux 0 t

      | TmConcat (t1, t2) ->
          aux 1 t1 ^ " ^ " ^ aux 1 t2

      (*cases for Tuple Terms and Projections *)
      | TmTuple l ->
          let s = String.concat ", " (List.map (aux 0) l) in
          "{" ^ s ^ "}"
      | TmProj (t, i) ->
          aux 2 t ^ "." ^ string_of_int i
        
      (*cases for Record Terms and Projections *)    
      | TmRecord fields ->
          let f (l, t) = l ^ "=" ^ aux 0 t in
          "{" ^ String.concat ", " (List.map f fields) ^ "}"
      | TmProjVar (t, l) ->
          aux 2 t ^ "." ^ l

      | TmNil ty -> 
          "nil[" ^ string_of_ty ty ^ "]"
      | TmCons (t1, t2) -> 
          "cons " ^ aux 2 t1 ^ " " ^ aux 2 t2
      | TmIsNil t1 ->
          "isnil " ^ aux 1 t1
      | TmHead t1 ->
          "head " ^ aux 1 t1
      | TmTail t1 ->
          "tail " ^ aux 1 t1
    in
    (* add parentheses only when nested *)
    if nest > 0 then "(" ^ s ^ ")" else s
  in
  aux 0 tm

let rec ldif l1 l2 = match l1 with
    [] -> []
  | h::t -> if List.mem h l2 then ldif t l2 else h::(ldif t l2)
;;

let rec lunion l1 l2 = match l1 with
    [] -> l2
  | h::t -> if List.mem h l2 then lunion t l2 else h::(lunion t l2)
;;

let rec free_vars tm = match tm with
    TmTrue ->
      []
  | TmFalse ->
      []
  | TmIf (t1, t2, t3) ->
      lunion (lunion (free_vars t1) (free_vars t2)) (free_vars t3)
  | TmZero ->
      []
  | TmSucc t ->
      free_vars t
  | TmPred t ->
      free_vars t
  | TmIsZero t ->
      free_vars t
  | TmVar s ->
      [s]
  | TmAbs (s, _, t) ->
      ldif (free_vars t) [s]
  | TmApp (t1, t2) ->
      lunion (free_vars t1) (free_vars t2)
  | TmLetIn (s, t1, t2) ->
      lunion (ldif (free_vars t2) [s]) (free_vars t1)
  | TmFix t ->
      free_vars t
  | TmString _ ->
      []
  | TmConcat (t1, t2) ->
      lunion (free_vars t1) (free_vars t2)

  (*Cases for Tuples free vars *)
  | TmTuple l ->
      List.fold_left (fun acc t -> lunion acc (free_vars t)) [] l
  | TmProj (t, _) ->
      free_vars t

  (*cases for Record Terms and Projections *)        
  | TmRecord fields ->
      List.fold_left (fun acc (_, t) -> lunion acc (free_vars t)) [] fields
  | TmProjVar (t, _) ->
      free_vars t
  | TmNil _ ->
      []
  | TmCons (t1, t2) ->
      lunion (free_vars t1) (free_vars t2)
  | TmIsNil t ->
      free_vars t
  | TmHead t ->
      free_vars t
  | TmTail t ->
      free_vars t
;;

let rec fresh_name x l =
  if not (List.mem x l) then x else fresh_name (x ^ "'") l
;;

let rec subst x s tm = match tm with
    TmTrue ->
      TmTrue
  | TmFalse ->
      TmFalse
  | TmIf (t1, t2, t3) ->
      TmIf (subst x s t1, subst x s t2, subst x s t3)
  | TmZero ->
      TmZero
  | TmSucc t ->
      TmSucc (subst x s t)
  | TmPred t ->
      TmPred (subst x s t)
  | TmIsZero t ->
      TmIsZero (subst x s t)
  | TmVar y ->
      if y = x then s else tm
  | TmAbs (y, tyY, t) ->
      if y = x then tm
      else let fvs = free_vars s in
           if not (List.mem y fvs)
           then TmAbs (y, tyY, subst x s t)
           else let z = fresh_name y (free_vars t @ fvs) in
                TmAbs (z, tyY, subst x s (subst y (TmVar z) t))
  | TmApp (t1, t2) ->
      TmApp (subst x s t1, subst x s t2)
  | TmLetIn (y, t1, t2) ->
      if y = x then TmLetIn (y, subst x s t1, t2)
      else let fvs = free_vars s in
           if not (List.mem y fvs)
           then TmLetIn (y, subst x s t1, subst x s t2)
           else let z = fresh_name y (free_vars t2 @ fvs) in
                TmLetIn (z, subst x s t1, subst x s (subst y (TmVar z) t2))
  | TmFix t ->
      TmFix (subst x s t)
  | TmString s ->
      TmString s
  | TmConcat (t1, t2) ->
      TmConcat (subst x s t1, subst x s t2)

  (* Cases for Substitution in Tuples *)
  | TmTuple l ->
      TmTuple (List.map (subst x s) l)
  | TmProj (t, i) ->
      TmProj (subst x s t, i)
  
  (* Cases for Substitution in Records*)
  | TmRecord fields ->
      TmRecord (List.map (fun (l, t) -> (l, subst x s t)) fields)
  | TmProjVar (t, l) ->
      TmProjVar (subst x s t, l)

  | TmNil ty ->
      TmNil ty
  | TmCons (t1, t2) ->
      TmCons (subst x s t1, subst x s t2)
  | TmIsNil t ->
      TmIsNil (subst x s t)
  | TmHead t ->
      TmHead (subst x s t)
  | TmTail t ->
      TmTail (subst x s t)
;;

let rec isnumericval tm = match tm with
    TmZero -> true
  | TmSucc t -> isnumericval t
  | _ -> false
;;

let rec isval tm = match tm with
    TmTrue  -> true
  | TmFalse -> true
  | TmAbs _ -> true
  | TmString _ -> true
  | t when isnumericval t -> true
  (* Case: A tuple is a value if all its elements are values *)
  | TmTuple l -> List.for_all isval l

  | TmRecord fields -> List.for_all (fun (_, t) -> isval t) fields

  | TmNil _ -> true
  | TmCons (h, t) -> isval h && isval t

  | _ -> false
;;

exception NoRuleApplies
;;

let rec eval1 tm = match tm with
    (* E-IfTrue *)
    TmIf (TmTrue, t2, _) ->
      t2

    (* E-IfFalse *)
  | TmIf (TmFalse, _, t3) ->
      t3

    (* E-If *)
  | TmIf (t1, t2, t3) ->
      let t1' = eval1 t1 in
      TmIf (t1', t2, t3)

    (* E-Succ *)
  | TmSucc t1 ->
      let t1' = eval1 t1 in
      TmSucc t1'

    (* E-PredZero *)
  | TmPred TmZero ->
      TmZero

    (* E-PredSucc *)
  | TmPred (TmSucc nv1) when isnumericval nv1 ->
      nv1

    (* E-Pred *)
  | TmPred t1 ->
      let t1' = eval1 t1 in
      TmPred t1'

    (* E-IszeroZero *)
  | TmIsZero TmZero ->
      TmTrue

    (* E-IszeroSucc *)
  | TmIsZero (TmSucc nv1) when isnumericval nv1 ->
      TmFalse

    (* E-Iszero *)
  | TmIsZero t1 ->
      let t1' = eval1 t1 in
      TmIsZero t1'

    (* E-AppAbs *)
  | TmApp (TmAbs(x, _, t12), v2) when isval v2 ->
      subst x v2 t12

    (* E-App2: evaluate argument before applying function *)
  | TmApp (v1, t2) when isval v1 ->
      let t2' = eval1 t2 in
      TmApp (v1, t2')

    (* E-App1: evaluate function before argument *)
  | TmApp (t1, t2) ->
      let t1' = eval1 t1 in
      TmApp (t1', t2)

    (* E-LetV *)
  | TmLetIn (x, v1, t2) when isval v1 ->
      subst x v1 t2

    (* E-Let *)
  | TmLetIn(x, t1, t2) ->
      let t1' = eval1 t1 in
      TmLetIn (x, t1', t2)

  | TmFix (TmAbs(x, _, t12)) ->
      subst x tm t12

    (* E-Fix: Evaluar el argumento de fix si aún no es un valor *)
  | TmFix t1 ->
      let t1' = eval1 t1 in
      TmFix t1'

    (* E-ConcatString: Real op*)
  | TmConcat (TmString s1, TmString s2) ->
      TmString (s1 ^ s2)

    (* E-Concat2: second argument eval*)
  | TmConcat (v1, t2) when isval v1 ->
      let t2' = eval1 t2 in
      TmConcat (v1, t2')

    (* E-Concat1: first argument eval *)
  | TmConcat (t1, t2) ->
      let t1' = eval1 t1 in
      TmConcat (t1', t2)

  (* E-ProjTuple: Extract component from a fully evaluated tuple *)
  | TmProj (TmTuple fields, i) when isval (TmTuple fields) ->
        (* OCaml usa índices desde 0, el usuario usa desde 1 *)
        (try List.nth fields (i - 1)
         with Failure _ | Invalid_argument _ -> raise NoRuleApplies)

    (* E-Proj: Congruence rule for projection *)
  | TmProj (t1, i) ->
        let t1' = eval1 t1 in
        TmProj (t1', i)

    (* E-Tuple: Evaluate components from left to right *)
  | TmTuple l ->
        let rec eval_fields = function
          | [] -> raise NoRuleApplies (* All are values *)
          | t :: rest -> 
              if isval t then 
                t :: eval_fields rest (* Keep evaluated value and continue *)
              else 
                let t' = eval1 t in (* Reduce the first non-value *)
                t' :: rest
        in
        TmTuple (eval_fields l)
    (* E-ProjRecord: Extraer el valor de un campo si el registro ya es un valor *)
  | TmProjVar (TmRecord fields, label) when isval (TmRecord fields) ->
        (try List.assoc label fields
         with Not_found -> raise NoRuleApplies)

    (* E-ProjVar: Regla de congruencia (evaluar el término proyectado) *)
  | TmProjVar (t1, label) ->
        let t1' = eval1 t1 in
        TmProjVar (t1', label)

    (* E-Record: Evaluar los campos de izquierda a derecha *)
  | TmRecord fields ->
        let rec eval_fields = function
          | [] -> raise NoRuleApplies (* Todos son valores *)
          | (l, t) :: rest ->
              if isval t then
                (l, t) :: eval_fields rest (* Ya es valor, seguir con el siguiente *)
              else
                let t' = eval1 t in        (* Evaluar este campo *)
                (l, t') :: rest
        in
        TmRecord (eval_fields fields)

  (* E-Cons1: Evaluar la cabeza primero *)
  | TmCons (t1, t2) when not (isval t1) ->
      let t1' = eval1 t1 in
      TmCons (t1', t2)
      
  (* E-Cons2: Evaluar la cola cuando la cabeza ya es un valor *)
  | TmCons (v1, t2) when isval v1 && not (isval t2) ->
      let t2' = eval1 t2 in
      TmCons (v1, t2')

  (* E-IsNilNil: isnil nil -> true *)
  | TmIsNil (TmNil _) ->
      TmTrue

  (* E-IsNilCons: isnil (cons v1 v2) -> false *)
  | TmIsNil (TmCons (v1, v2)) when isval v1 && isval v2 ->
      TmFalse

  (* E-IsNil: Regla de congruencia *)
  | TmIsNil t1 ->
      let t1' = eval1 t1 in
      TmIsNil t1'

  (* E-HeadCons: head (cons v1 v2) -> v1 *)
  | TmHead (TmCons (v1, v2)) when isval v1 && isval v2 ->
      v1

  (* E-Head: Regla de congruencia *)
  | TmHead t1 ->
      let t1' = eval1 t1 in
      TmHead t1'

  (* E-TailCons: tail (cons v1 v2) -> v2 *)
  | TmTail (TmCons (v1, v2)) when isval v1 && isval v2 ->
      v2

  (* E-Tail: Regla de congruencia *)
  | TmTail t1 ->
      let t1' = eval1 t1 in
      TmTail t1'

  | _ ->
      raise NoRuleApplies
;;

let rec eval tm =
  try
    let tm' = eval1 tm in
    eval tm'
  with
    NoRuleApplies -> tm
;;

(*Expands global variables with the term it is storing*)
let expand_globals gctx tm =
  let rec aux bound t =
    match t with
    | TmVar x ->
        if List.mem x bound then t
        else (
          match getglobal gctx x with
          | GlobalValue v -> v
          | _ | exception Not_found -> t
        )

    | TmAbs(x, ty, body) ->
        TmAbs(x, ty, aux (x :: bound) body)

    | TmApp(t1, t2) ->
        TmApp(aux bound t1, aux bound t2)

    | TmLetIn(x, t1, t2) ->
        TmLetIn(x, aux bound t1, aux (x :: bound) t2)

    | TmFix t -> 
        TmFix(aux bound t)

    | TmIf(t1, t2, t3) ->
        TmIf(aux bound t1, aux bound t2, aux bound t3)

    | TmConcat(t1, t2) ->
        TmConcat(aux bound t1, aux bound t2)

    | TmSucc t1    -> TmSucc(aux bound t1)
    | TmPred t1    -> TmPred(aux bound t1)
    | TmIsZero t1  -> TmIsZero(aux bound t1)

    | TmTuple xs ->
        TmTuple(List.map (aux bound) xs)

    | TmProj(t1, i) ->
        TmProj(aux bound t1, i)

    | TmRecord fields ->
        TmRecord(List.map (fun (l, t) -> (l, aux bound t)) fields)

    | TmProjVar(t1, l) ->
        TmProjVar(aux bound t1, l)

    | TmNil ty ->
        TmNil ty
    | TmCons (t1, t2) ->
        TmCons (aux bound t1, aux bound t2)
    | TmIsNil t1 ->
        TmIsNil (aux bound t1)
    | TmHead t1 ->
        TmHead (aux bound t1)
    | TmTail t1 ->
        TmTail (aux bound t1)

    (* Base cases, leave untouched *)
    | TmTrue | TmFalse | TmZero | TmString _ -> t
  in
  aux [] tm

(* Fully expands type aliases inside a term *)
let expand_aliases gctx tm =
  (* helper for types *)
  let rec expand_ty t =
    match t with
    | TyAlias name ->
        (match getglobal gctx name with
         | GlobalType real -> expand_ty real
         | _ -> t)
    | TyArr (t1, t2) ->
        TyArr (expand_ty t1, expand_ty t2)
    | TyTuple ts ->
        TyTuple (List.map expand_ty ts)
    | TyRecord fields ->
        TyRecord (List.map (fun (l, ty) -> (l, expand_ty ty)) fields)

    | _ -> t
  in

  (* walk term *)
  let rec aux t =
    match t with
    | TmAbs(x, ty, body) ->
        TmAbs(x, expand_ty ty, aux body)

    | TmLetIn(x, t1, t2) ->
        TmLetIn(x, aux t1, aux t2)

    | TmFix t -> 
        TmFix(aux t)

    | TmApp(t1, t2) ->
        TmApp(aux t1, aux t2)

    | TmIf(t1, t2, t3) ->
        TmIf(aux t1, aux t2, aux t3)

    | TmSucc t1 -> TmSucc(aux t1)
    | TmPred t1 -> TmPred(aux t1)
    | TmIsZero t1 -> TmIsZero(aux t1)
    | TmConcat(t1, t2) -> TmConcat(aux t1, aux t2)

    | TmTuple xs ->
        TmTuple (List.map aux xs)

    | TmProj(t1, i) ->
        TmProj(aux t1, i)

    | TmRecord fields ->
        TmRecord (List.map (fun (l,t) -> (l, aux t)) fields)

    | TmProjVar(t1, l) ->
        TmProjVar(aux t1, l)
        | TmNil ty ->
        TmNil (expand_ty ty)  
    | TmCons (t1, t2) ->
        TmCons (aux t1, aux t2)
    | TmIsNil t1 ->
        TmIsNil (aux t1)
    | TmHead t1 ->
        TmHead (aux t1)
    | TmTail t1 ->
        TmTail (aux t1)

    (* base terms remain unchanged *)
    | (TmVar _ | TmTrue | TmFalse | TmZero | TmString _) ->
        t
  in

  aux tm
