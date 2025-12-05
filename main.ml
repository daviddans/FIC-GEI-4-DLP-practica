open Parsing
open Lexing

open Lambda
open Parser
open Lexer

(* Read until user writes ;; *)
let read_until_terminator () =
  let buf = Buffer.create 128 in
  let rec aux () =
    let line = read_line () in
    match String.index_opt line ';' with
    | Some i when i + 1 < String.length line && line.[i+1] = ';' ->
        Buffer.add_string buf (String.sub line 0 i);
        Buffer.add_char buf '\n';
        Buffer.contents buf
    | _ ->
        Buffer.add_string buf line;
        Buffer.add_char buf '\n';
        aux ()
  in
  aux ()
;;

let rec top_level_loop () =
  print_endline "Evaluator of lambda expressions...";

  let rec loop ctx gctx =
    try
      print_string ">> "; flush stdout;

      let input = read_until_terminator () in
      let cmd = s token (from_string input) in

      match cmd with

      (* ----------------- Evaluate expression ----------------- *)
| Eval tm ->
    (* expand aliases inside term *)
    let tm1 = expand_aliases gctx tm in
    (* expand global bindings *)
    let tm2 = expand_globals gctx tm1 in
    let tyTm = typeof ctx tm2 in
    let v = eval tm2 in
    print_endline (string_of_term v ^ " : " ^ string_of_ty tyTm);
    loop ctx gctx

      (* ----------------- Bind global term --------------------- *)
| Bind (x, tm) ->
    let tm1 = expand_aliases gctx tm in
    let tm2 = expand_globals gctx tm1 in
    let ty = typeof ctx tm2 in
    let v = eval tm2 in
    let gctx' = addglobal gctx x (GlobalValue v) in
    print_endline ("defined " ^ x ^ " : " ^ string_of_ty ty);
    loop ctx gctx'


      (* ----------------- Store type alias --------------------- *)
| Alias (x, ty) ->
    (* expand aliases inside stored type *)
    let finalTy =
      let rec expand_ty t =
        match t with
        | TyAlias name ->
            (match getglobal gctx name with
             | GlobalType real -> expand_ty real
             | _ -> t)
        | TyArr (a,b) -> TyArr(expand_ty a, expand_ty b)
        | TyTuple ts -> TyTuple(List.map expand_ty ts)
        | TyRecord fs -> TyRecord(List.map (fun (l,ty)->(l,expand_ty ty)) fs)
        | _ -> t
      in expand_ty ty
    in
    let gctx' = addglobal gctx x (GlobalType finalTy) in
    print_endline ("type " ^ x ^ " = " ^ string_of_ty finalTy);
    loop ctx gctx'

    (* ----------------- Errors --------------------- *)
    with
    | Lexical_error ->
        print_endline "lexical error"; loop ctx gctx
    | Parse_error ->
        print_endline "syntax error"; loop ctx gctx
    | Type_error e ->
        print_endline ("type error: " ^ e); loop ctx gctx
    | End_of_file ->
        print_endline "...bye!!!"
  in

  loop emptyctx emptygctx
;;

let () = top_level_loop ()
