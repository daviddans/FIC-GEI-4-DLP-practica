
%{
  open Lambda;;
%}

%token LAMBDA
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token SUCC
%token PRED
%token ISZERO
%token LET
%token LETREC
%token IN
%token BOOL
%token NAT
%token STRING            
%token CONCAT

%token LBRACE
%token RBRACE
%token COMMA

%token LIST
%token NIL
%token CONS
%token ISNIL
%token HEAD
%token TAIL
%token LSQUARE
%token RSQUARE

%token LPAREN
%token RPAREN
%token DOT
%token EQ
%token COLON
%token ARROW
%token EOF

%token <int> INTV
%token <string> IDV
%token <string> ALS 
%token <string> STRINGV 

%start s
%type <Lambda.sentence> s

%%

s :
    term EOF
      {Eval $1 }
    | IDV EQ term EOF
        {Bind ($1, $3) }
    | LET IDV EQ term EOF          
        {Bind ($2, $4) }
    | LETREC IDV COLON ty EQ term EOF   
        { Bind ($2, TmFix (TmAbs ($2, $4, $6))) }
    | ALS EQ ty EOF 
        {Alias ($1, $3)}
    

term :
    appTerm
      { $1 }
  | IF term THEN term ELSE term
      { TmIf ($2, $4, $6) }
  | LAMBDA IDV COLON ty DOT term
      { TmAbs ($2, $4, $6) }
  | LET IDV EQ term IN term
      { TmLetIn ($2, $4, $6) }
  | LETREC IDV COLON ty EQ term IN term
      { TmLetIn ($2, TmFix (TmAbs ($2, $4, $6)), $8) }

appTerm :
    atomicTerm
      { $1 }
  | SUCC atomicTerm
      { TmSucc $2 }
  | PRED atomicTerm
      { TmPred $2 }
  | ISZERO atomicTerm
      { TmIsZero $2 }
  | appTerm atomicTerm
      { TmApp ($1, $2) }
  | atomicTerm CONCAT atomicTerm   
      { TmConcat ($1, $3) }
  | appTerm DOT INTV
      { TmProj ($1, $3) }
  | appTerm DOT IDV
      { TmProjVar ($1, $3) }
  | CONS atomicTerm atomicTerm
      { TmCons ($2, $3) }
  | ISNIL atomicTerm
      { TmIsNil $2 }
  | HEAD atomicTerm
      { TmHead $2 }
  | TAIL atomicTerm
      { TmTail $2 }
    

atomicTerm :
    LPAREN term RPAREN
      { $2 }
  | TRUE
      { TmTrue }
  | FALSE
      { TmFalse }
  | IDV
      { TmVar $1 }
  | INTV
      { let rec f = function
            0 -> TmZero
          | n -> TmSucc (f (n-1))
        in f $1 }
  | STRINGV           
      { TmString $1 }
  | LBRACE fields RBRACE
      { TmRecord $2 }
  | LBRACE tupleTerm RBRACE
      { TmTuple $2 }
  | NIL LSQUARE ty RSQUARE
      { TmNil $3 }

ty :
    atomicTy
      { $1 }
  | atomicTy ARROW ty
      { TyArr ($1, $3) }

atomicTy :
    LPAREN ty RPAREN
      { $2 }
  | BOOL
      { TyBool }
  | NAT
      { TyNat }
  | STRING          
      { TyString }
  | ALS
        { TyAlias $1 }  
  | LBRACE tupleType RBRACE
      { TyTuple $2 }
  | LBRACE field_types RBRACE
      { TyRecord $2 }
  | LIST atomicTy
      { TyList $2 }


tupleType :
    ty
      { [$1] }
  | ty COMMA tupleType
      { $1 :: $3 }

tupleTerm :
    term
      { [$1] }
  | term COMMA tupleTerm
      { $1 :: $3 }

field_types :
  | { [] }
  | ne_field_types { $1 }

ne_field_types :
  | IDV COLON ty 
      { [($1, $3)] }
  | IDV COLON ty COMMA ne_field_types 
      { ($1, $3) :: $5 }

fields :
  | { [] }
  | ne_fields { $1 }

ne_fields :
  | IDV EQ term 
      { [($1, $3)] }
  | IDV EQ term COMMA ne_fields 
      { ($1, $3) :: $5 }
