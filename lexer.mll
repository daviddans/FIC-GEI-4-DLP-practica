
{
  open Parser;;
  exception Lexical_error;;
}

rule token = parse
    [' ' '\t' '\n']  { token lexbuf }
  | "lambda"    { LAMBDA }
  | "L"         { LAMBDA }
  | "true"      { TRUE }
  | "false"     { FALSE }
  | "if"        { IF }
  | "then"      { THEN }
  | "else"      { ELSE }
  | "succ"      { SUCC }
  | "pred"      { PRED }
  | "iszero"    { ISZERO }
  | "let"       { LET }
  | "letrec"    { LETREC }  
  | "in"        { IN }
  | "Bool"      { BOOL }
  | "Nat"       { NAT }
  | '('         { LPAREN }
  | ')'         { RPAREN }

  | "List"      { LIST }     
  | "nil"       { NIL }      
  | "cons"      { CONS }      
  | "isnil"     { ISNIL }     
  | "head"      { HEAD }      
  | "tail"      { TAIL }      
  | '['         { LSQUARE }   
  | ']'         { RSQUARE }   

  | '{'         { LBRACE }   
  | '}'         { RBRACE }   
  | ','         { COMMA }    

  | '.'         { DOT }
  | '='         { EQ }
  | ':'         { COLON }
  | "->"        { ARROW }
  | "String"    { STRING }    
  | "^"    { CONCAT }    
  | ['0'-'9']+  { INTV (int_of_string (Lexing.lexeme lexbuf)) }
  | ['a'-'z']['a'-'z' '_' '0'-'9']*
                { IDV (Lexing.lexeme lexbuf) }
  | ['A'-'Z']['a'-'z' '_' '0'-'9']*
                { ALS (Lexing.lexeme lexbuf) }
  | "\"" [^ '"']* "\""
      { let s = Lexing.lexeme lexbuf in
        STRINGV (String.sub s 1 (String.length s - 2)) }
  | eof         { EOF }
  | _           { raise Lexical_error }
