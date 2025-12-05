
(* TYPE DEFINITIONS *)

type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  | TyAlias of string (*type for type aliases *)
  | TyString           (*type string*)
  | TyTuple of ty list (*type tuple*)
  | TyRecord of (string * ty) list  (*type record*)
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
  | TmString of string        (*term string*)
  | TmConcat of term * term   (*concat operator *)
  | TmTuple of term list      (*term for tuples*)
  | TmProj of term * int      (*term for projections*)
  | TmRecord of (string * term) list  (* pair list (tag, value) *)
  | TmProjVar of term * string       (* projection for tags (string) *)
  | TmVariant of string * term (*term for variant values*)
  | TmAs of term * ty (*term for type ascription*)
  | TmCase of term * (string * string * term) list (*term for pattern matching construcction*)
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
    | TyVariant fields ->
        let f (l, t) = l ^ " : " ^ aux 0 t in
        "<" ^ String.concat ", " (List.map f fields) ^ ">"
  
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
             
  (* Bare variant: we force the user to always write `<tag=v> as SomeVariantType` *)
  | TmVariant (_, _) ->
      raise (Type_error "bare variant must be annotated with `as`")

  (* Ascription *)
  | TmAs (v, asTy) ->
      begin match v, asTy with
      (* Special case: variant value ascribed with a variant type *)
      | TmVariant (lbl, t1), TyVariant field_tys ->
          (* 1) the label must exist in the variant type *)
          let field_ty =
            try List.assoc lbl field_tys
            with Not_found ->
              raise (Type_error ("unknown variant tag " ^ lbl))
          in
          (* 2) the payload must have the right type *)
          let ty_payload = typeof ctx t1 in
          if ty_payload = field_ty then asTy
          else
            raise (Type_error "variant payload type does not match its tag type")

      (* General ascription: expression type must match ascribed type *)
      | _, _ ->
          let tyV = typeof ctx v in
          if tyV = asTy then asTy
          else raise (Type_error "ascribed type mismatch")
      end

  (* T-Case: pattern matching on variants *)
  | TmCase (scrut, branches) ->
      (* compute scrutinee type *)
      let ty_scrut = typeof ctx scrut in

      (* ensure scrutinee is a variant *)
      let field_tys =
        match ty_scrut with
        | TyVariant fts -> fts
        | _ -> raise (Type_error "case expression applied to non-variant value")
      in
      (* check each branch produces same type *)
      let branch_types =
        List.map
          (fun (lbl, binder, body) ->
            (* 1) label must exist in variant type *)
            let ty_arg =
              try List.assoc lbl field_tys
              with Not_found ->
                raise (Type_error ("unknown case label " ^ lbl))
            in
            (* 2) type check body under binder typing *)
            let ctx' = addbinding ctx binder ty_arg in
            typeof ctx' body
          )
          branches
      in
      (* 3) ensure all branch types identical *)
      (match branch_types with
       | [] -> raise (Type_error "empty case expression")
       | ty1 :: rest ->
           List.iter
             (fun ty -> if ty <> ty1 then
                 raise (Type_error "case branches produce different types"))
               rest;
           ty1)
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
      | TmVariant (tag, v) ->
          "<" ^ tag ^ " = " ^ aux 0 v ^ ">"

      | TmAs (t1, ty) ->
          aux 0 t1 ^ " as " ^ string_of_ty ty

      | TmCase (scrut, branches) ->
          let branch_to_str (lbl, x, body) =
            "<" ^ lbl ^ "=" ^ x ^ "> => " ^ aux 0 body
          in
          "case " ^ aux 0 scrut ^ " of "
          ^ String.concat " | " (List.map branch_to_str branches)

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
  (*Substitution in variants*)
  | TmVariant (lbl, v1) ->
      TmVariant(lbl, subst x s v1)
  (*Substitution in ascriptions*)
  | TmAs (v, ty) ->
      TmAs(subst x s v, ty)
  (*Substitution in case statements*)
  | TmCase (scrut, branches) ->
      let scrut' = subst x s scrut in
      let branches' =
        List.map
          (fun (lbl, binder, body) ->
            if binder = x then
              (lbl, binder, body)   (* binder shadows variable *)
            else
              (lbl, binder, subst x s body))
          branches
      in
      TmCase(scrut', branches')

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
  | TmVariant (_, v) -> isval v       (* variant is value if its payload is value *)
  | TmAs (v, _) -> isval v            (* ascription is value when underlying term is value *)

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

  (* E-Variant: evaluate inside variant *)
  | TmVariant (lbl, v) when not (isval v) ->
      let v' = eval1 v in
      TmVariant(lbl, v')

  (* E-As: evaluate term under ascription *)
  | TmAs (v, ty) when not (isval v) ->
      let v' = eval1 v in
      TmAs(v', ty)

  (* E-Case: evaluate scrutinee *)
  | TmCase (scrut, branches) when not (isval scrut) ->
      let scrut' = eval1 scrut in
      TmCase(scrut', branches)

  (* E-CaseMatch *)
  | TmCase (TmAs (TmVariant(lbl, v), ty), branches)
    when isval v ->
      (* find matching branch *)
      let (_, binder, body) =
        try List.find (fun (l, _, _) -> l = lbl) branches
        with Not_found -> raise NoRuleApplies
      in
      subst binder v body


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

    | TmIf(t1, t2, t3) ->
        TmIf(aux bound t1, aux bound t2, aux bound t3)

    | TmConcat(t1, t2) ->
        TmConcat(aux bound t1, aux bound t2)

    | TmSucc t1 -> TmSucc(aux bound t1)
    | TmPred t1 -> TmPred(aux bound t1)
    | TmIsZero t1 -> TmIsZero(aux bound t1)

    | TmTuple xs ->
        TmTuple(List.map (aux bound) xs)

    | TmProj(t1, i) ->
        TmProj(aux bound t1, i)

    | TmRecord fields ->
        TmRecord(List.map (fun (l, t) -> (l, aux bound t)) fields)

    | TmProjVar(t1, l) ->
        TmProjVar(aux bound t1, l)

    | TmVariant(lbl, v) ->
        TmVariant(lbl, aux bound v)

    | TmAs(v, ty) ->
        TmAs(aux bound v, ty)

    | TmCase(scrut, branches) ->
        TmCase(aux bound scrut,
               List.map
                 (fun (lbl, binder, body) -> (lbl, binder, aux bound body))
                 branches)

    (* Base terms *)
    | TmTrue | TmFalse | TmZero | TmString _ ->
        t
  in
  aux [] tm

  (* Fully expands type aliases inside a term *)
let expand_aliases gctx tm =
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
    | TyVariant fields ->
        TyVariant (List.map (fun (l, ty) -> (l, expand_ty ty)) fields)
    | _ -> t
  in
  let rec aux t =
    match t with
    | TmAbs(x, ty, body) ->
        TmAbs(x, expand_ty ty, aux body)

    | TmLetIn(x, t1, t2) ->
        TmLetIn(x, aux t1, aux t2)

    | TmApp(t1, t2) ->
        TmApp(aux t1, aux t2)

    | TmIf(t1, t2, t3) ->
        TmIf(aux t1, aux t2, aux t3)

    | TmSucc t1 -> TmSucc(aux t1)
    | TmPred t1 -> TmPred(aux t1)
    | TmIsZero t1 -> TmIsZero(aux t1)
    | TmConcat(t1, t2) -> TmConcat(aux t1, aux t2)

    | TmTuple xs ->
        TmTuple(List.map aux xs)

    | TmProj(t1, i) ->
        TmProj(aux t1, i)

    | TmRecord fields ->
        TmRecord(List.map (fun (l,t) -> (l, aux t)) fields)

    | TmProjVar(t1, l) ->
        TmProjVar(aux t1, l)

    | TmVariant(lbl, t1) ->
        TmVariant(lbl, aux t1)

    | TmAs(v, ty) ->
        TmAs(aux v, expand_ty ty)

    | TmCase(scrut, branches) ->
        TmCase(aux scrut,
               List.map (fun (lbl,binder,body) ->
                            (lbl,binder, aux body)) branches)

    | TmVar _ | TmTrue | TmFalse | TmZero | TmString _ ->
        t
  in
  aux tm