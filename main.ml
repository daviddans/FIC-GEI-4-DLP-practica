open Parsing;;
open Lexing;;

open Lambda;;
open Parser;;
open Lexer;;

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
  
let rec top_level_loop () =
  print_endline "Evaluator of lambda expressions...";
  let rec loop ctx =
    try
      print_string ">> "; flush stdout;
      let input = read_until_terminator () in
      let tm = s token (from_string input) in
      let tyTm = typeof ctx tm in
      print_endline (string_of_term (eval tm) ^ " : " ^ string_of_ty tyTm);
      loop ctx
    with
    | Lexical_error ->
        print_endline "lexical error"; loop ctx
    | Parse_error ->
        print_endline "syntax error"; loop ctx
    | Type_error e ->
        print_endline ("type error: " ^ e); loop ctx
    | End_of_file ->
        print_endline "...bye!!!"
  in
  loop emptyctx
;;

let () = top_level_loop ()
