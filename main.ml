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
  
  (* extend loop with global context *)
  let rec loop ctx gctx =
    try
      print_string ">> "; flush stdout;

      let input = read_until_terminator () in
      let cmd = s token (from_string input) in

      match cmd with

      (* --------- EVALUATION OF A PURE EXPRESSION --------- *)
      | Eval tm ->
          (* expand global references first *)
          let tm' = expand_globals gctx tm in
          (* typecheck expanded term *)
          let tyTm = typeof ctx tm' in
          (* evaluate expanded term *)
          let v = eval tm' in
          print_endline (string_of_term v ^ " : " ^ string_of_ty tyTm);
          loop ctx gctx

      (* --------- GLOBAL TERM BINDING --------- *)
      | Bind (x, tm) ->
          (* expand globals inside assigned term *)
          let tm' = expand_globals gctx tm in
          (* first typecheck original term *)
          let ty = typeof ctx tm' in
          (* then evaluate original term once *)
          let v  = eval tm' in
          (* extend global context *)
          let gctx' = addglobal gctx x (GlobalValue v) in
          print_endline ("defined " ^ x ^ " : " ^ string_of_ty ty);
          loop ctx gctx'

      (* --------- GLOBAL TYPE ALIASING --------- *)
      | Alias (x, ty) ->
          let gctx' = addglobal gctx x (GlobalType ty) in
          print_endline ("type " ^ x ^ " = " ^ string_of_ty ty);
          loop ctx gctx'

    (* --------- ERRORS --------- *)
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
