%{
open ErrorReport
open Syntree

let fillList itm len =
   let rec loop itm len lst =
      if len = 0 then
         lst
      else
         loop itm (len - 1) (itm :: lst)
   in
      loop itm len []
;;

let parse_error str =
   errorAndDie "Syntax error"
;;

(* Takes a typedecl and returns the default value for it 

*)
let rec resolveDefault = function
   Ptrtype( _ ) -> Nilconst
 | Arraytype( len, typestm ) -> 
     if len = -1 then
        Nilconst
     else
        Arrayconst (fillList (Conststm( resolveDefault typestm )) len)
 | Functype( _ ) -> Nilconst
 | Customtype( _ ) -> Nilconst
 | Intsize( _ ) -> Intconst( 0 )
 | Uintsize( _ ) -> Intconst( 0 )
 | Floatsize( _ ) -> Floatconst( 0. )
 | Int -> Intconst( 0 )
 | Long -> Intconst( 0 )
 | Float -> Floatconst( 0. )
 | Double -> Floatconst( 0. )
 | Uint -> Intconst( 0 )
 | Ulong -> Intconst( 0 )
 | Char -> Charconst( '\000' )
 | Str -> Stringconst( "" )
 | Bool -> Boolconst( false )
 | Voidtype -> Nilconst
 | Compoundtype( a, b ) -> Nilconst
 | Structtype( _ ) -> Nilconst
 | Nulltype -> Nilconst
;;

let isConstStm = function
   Conststm( _ ) -> true
 | _ -> false
;;



%}

%token ADD SUB MUL DIV MOD
%token LPAREN RPAREN COLON POINTER ARRAY ASSIGN AT ASM DOT DEF NIL VOID 
%token FUNC LBRACE RBRACE EOF
%token DO IF WHILE 
%token LET CONST GLOBAL STRUCT TYPE
%token GT LT GTE LTE EQ NEQ
%token AND OR NOT XOR BAND BOR BNOT BXOR SHL SHR
%token <int> INT
%token <float> FLOAT
%token <char> CHAR
%token <string> STRING SYMBOL
%token <bool> BOOLEAN

/* For an array#foo expr, the array bit is evaluated first 
   ^array#foo is ^(array#foo), I believe.
   Well, lower = higher precedence.  We can figure out the exact mechanics of
   it later.
*/ 
%left DOT
%left ARRAY

%type <Syntree.decl list> main
%start main

%%

main:  
	  /* EMPTY */ 
	  	{[]}
	| decllst
	  	{$1}
	;

decllst:
	  decl
	  	{[$1]}
	| decl decllst
	  	{$1 :: $2}
	;

decl:
	  LPAREN fundecl RPAREN
	  	{$2}
	| LPAREN constdecl RPAREN
	  	{$2}
	| LPAREN globaldecl RPAREN
	  	{$2}
	| LPAREN structdecl RPAREN
		{$2}
	| LPAREN newtypedecl RPAREN
		{$2}
	;

structdecl:
	  STRUCT SYMBOL structitmlst
	  	{Structdecl( $2, $3 )}
	  ;

structitmlst:
	  structitm
	  	{[$1]}
	| structitm structitmlst
		{$1 :: $2}
	;

structitm:
	  LPAREN SYMBOL typedecl RPAREN
		{Structitem( $2, $3, Conststm( Nilconst ) )}
	| LPAREN SYMBOL typedecl value RPAREN
		{if isConstStm $4 then Structitem( $2, $3, $4 )
		    else errorAndDie "Tried to use a non-constant default!"}
	;

newtypedecl:
	  TYPE SYMBOL typedecl
	  	{Typedecl( $2, $3 )}
	  ;

fundecl:
	  DEF SYMBOL typedecl LPAREN arglist RPAREN funbody
	  	{Fundecl( $2, $3, $5, $7 )}
	| DEF SYMBOL typedecl LPAREN RPAREN funbody
		{Fundecl( $2, $3, [], $6 )}
	;

funbody:
	  funstm
	  	{[$1]}
	| funstm funbody
		{$1 :: $2}
	;

funstm:
	  expr
	  	{$1}
	| vardecl
		{$1}
	| LPAREN fundecl RPAREN
		{fundecl2funstm $2}
	;

arglist:
	  arg arglist
	  	{$1 :: $2}
	| arg
	  	{[$1]}
	;

/* Yay, we have easy machinery for default values for function args */
arg:
	  SYMBOL typedecl
		{Vardecl( $1, $2, Conststm( resolveDefault $2 ) )}
	;

typestm:
	  SYMBOL
	  	{parseType $1}
	| POINTER typedecl
	  	{Ptrtype( $2 )}
	| ARRAY typedecl
	  	{Arraytype( -1, $2 )}
	| ARRAY INT typedecl
	  	{if $2 > 0 
		    then Arraytype( $2, $3 ) 
		    else errorAndDie "Array length must be greater than 0!"}
	| VOID
		{Voidtype}
	;

typedecl:
	  COLON typestm
	  	{$2}
          /* This causes two conflicts, but also just so happens to do what I
	     want. */
	| COLON typestm typedecl
	  	{Compoundtype( $2, $3)}
	| LBRACE typedecl RBRACE
		{match $2 with
		   Compoundtype( a, b ) -> Functype( a, b )
		 | _ -> Functype( $2, Voidtype )}
	;


constdecl:
	  CONST SYMBOL typedecl value
	  	{Constdecl( Vardecl( $2, $3, $4 ) )}
	;

globaldecl:
	  GLOBAL SYMBOL typedecl
	  	{Globaldecl( Vardecl( $2, $3, Conststm( resolveDefault $3 ) ) )}
	| GLOBAL SYMBOL typedecl expr
	  	{Globaldecl( Vardecl( $2, $3, $4 ) )}
	;

valuelst:
	  value
	  	{[$1]}
	| value valuelst
		{$1 :: $2}
	;

value:
	  SYMBOL
	  	{Varstm( $1 )}
	| INT
	  	{Conststm( Intconst( $1 ) )}
	| CHAR
	  	{Conststm( Charconst( $1 ) )}
	| FLOAT
	  	{Conststm( Floatconst( $1 ) )}
	| STRING
	  	{Conststm( Stringconst( $1 ) )}
	| NIL
	  	{Conststm( Nilconst )}
	| BOOLEAN
		{Conststm( Boolconst( $1 ) )}
	| aref
		{$1}
	| sref
		{$1}
	| arraylit
		{Conststm( $1 )}
	;

aref:
	  expr ARRAY expr
	  	{Aref( $1, $3 )}
	;

sref:
	  expr DOT SYMBOL
	  	{Sref( $1, $3 )}
	;

arraylit:
	  LBRACE valuelst RBRACE
	  	{Arrayconst( $2 )}
	;

expr:
	  value
	  	{$1}
	| LPAREN funcall RPAREN
	  	{$2}
	| LPAREN ifexpr RPAREN
	  	{$2}
	| LPAREN doexpr RPAREN
	  	{$2}
	| LPAREN whileexpr RPAREN
	  	{$2}
	| LPAREN mathexpr RPAREN
	  	{$2}
	| LPAREN relexpr RPAREN
	  	{$2}
	| LPAREN logicexpr RPAREN
	  	{$2}
	| LPAREN bitexpr RPAREN
	  	{$2}
	| LPAREN assignexpr RPAREN
		{$2}
	| LPAREN asmexpr RPAREN
		{$2}
	;

assignexpr:
	  ASSIGN rvalue expr
	  	{Assignstm( $2, $3 )}
	;

rvalue:
	  aref
	  	{$1}
	| sref
		{$1}
	| SYMBOL
		{Varstm( $1 )}
	;

exprlst:
	  expr exprlst
	  	{$1 :: $2}
	| expr
	  	{[$1]}
	;


vardecl:
	  LPAREN LET varlst RPAREN
	  	{Letstm( $3 )}
	;

varlst:
	  varstm
	  	{[$1]}
	| varstm varlst
	  	{$1 :: $2}
	;

varstm:
	  LPAREN SYMBOL COLON typestm RPAREN
	  	{Vardecl( $2, $4, Conststm( resolveDefault $4 ) ) }
	| LPAREN SYMBOL COLON typestm expr RPAREN
	  	{Vardecl( $2, $4, $5 )}
	;

funcall:
	  expr
	  	{Funcall( $1, [] )}
	| expr exprlst
		{Funcall( $1, $2 )}
	;

ifexpr:
	  IF expr expr
	  	{Ifstm( $2, $3, Nullstm )}
	| IF expr expr expr
	  	{Ifstm( $2, $3, $4 )}
	;

doexpr:
	  DO exprlst
	  	{Dostm( $2 )}
	;

whileexpr:
	  WHILE expr exprlst
	  	{Whilestm( $2, $3 )}
	;

asmexpr:
	  ASM STRING
	  	{Asmstm( $2 )}
	;

mathexpr:
	  ADD exprlst
	  	{Opexpr( Add, $2 )}
	| SUB exprlst
	  	{Opexpr( Sub, $2 )}
	| MUL exprlst
	  	{Opexpr( Mul, $2 )}
	| DIV exprlst
	  	{Opexpr( Div, $2 )}
	| MOD exprlst
	  	{Opexpr( Mod, $2 )}
	;

relexpr:
	  EQ exprlst
	  	{Opexpr( Eq, $2 )}
	| NEQ exprlst
	  	{Opexpr( Neq, $2 )}
	| GT exprlst
	  	{Opexpr( Gt, $2 )}
	| GTE exprlst
	  	{Opexpr( Gte, $2 )}
	| LT exprlst
	  	{Opexpr( Lt, $2 )}
	| LTE exprlst
	  	{Opexpr( Lte, $2 )}
	;

logicexpr:
	  AND exprlst
	  	{Opexpr( And, $2 )}
	| OR exprlst
	  	{Opexpr( Or, $2 )}
	| XOR exprlst
	  	{Opexpr( Xor, $2 )}
	| NOT expr
	  	{Opexpr( Not, [$2] )}
	;

bitexpr:
	  BNOT expr
	  	{Opexpr( Bnot, [$2] )}
	| BAND exprlst
	  	{Opexpr( Band, $2 )}
	| BOR exprlst
	  	{Opexpr( Bor, $2 )}
	| BXOR exprlst
	  	{Opexpr( Bxor, $2 )}
	| SHL expr expr
	  	{Opexpr( Shl, [$2; $3] )}
	| SHR expr expr
	  	{Opexpr( Shr, [$2; $3] )}
	;




