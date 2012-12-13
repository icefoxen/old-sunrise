(* lex.mll
   A lexer for Sunrise.  Ocamllex.  Good stuff.


   Simon Heath
   18/4/2005
*)

{

open Parse
open ErrorReport
exception Eof
exception Lexer_error

let inComment = ref 0;;

(* Abbreviation for the func that returns the string
   being lexed.
*)
let gs = Lexing.lexeme;;

(* Advances the position of the error-checking vars. *)
let adv lb =
  let c = (gs lb) in
  (*
  if c <> " " then
     Printf.printf "Lexed: '%s'\n" (gs lb);
  *)
  chrNum := !chrNum + (String.length (Lexing.lexeme lb));;


let str2int x =
   Scanf.sscanf x "%i" (fun x -> x)
;;

let str2char x =
   Scanf.sscanf x "%C" (fun x -> x) 
;;

let str2str x =
   Scanf.sscanf x "%S" (fun x -> x) 
;;


}


let id = 
  ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_' ]*

let inum =
   '-'?(['0'-'9']+|"0x"['0'-'9''a'-'f''A'-'F']+|"0o"['0'-'7']+)
let bnum =
   '-'?"0b"['0''1']+
let fnum =
   '-'?['0'-'9']+'.'['0'-'9']*

let chr =
   ("'"_"'") | ("'\\"(inum|bnum)"'") | ("'\\"("n"|"b"|"r"|"t"|"'"|"\\")"'")

let str = '"'([^'"''\\']|'\\'_)*'"'


rule token = parse
   ";"			{ adv lexbuf; lcomment lexbuf }
 | (inum|bnum)		{ adv lexbuf; INT( str2int (gs lexbuf) ) }
 | fnum			{ adv lexbuf; FLOAT( float_of_string (gs lexbuf) ) }
 | chr                  { adv lexbuf; CHAR( str2char (gs lexbuf) ) }
 | "\n"			{ nl (); token lexbuf }
 | [' ''\t']		{ adv lexbuf; token lexbuf }
 | "+"			{ adv lexbuf; ADD }
 | "-"			{ adv lexbuf; SUB }
 | "*"			{ adv lexbuf; MUL }
 | "/"			{ adv lexbuf; DIV }
 | "%"			{ adv lexbuf; MOD }
 | "("			{ adv lexbuf; LPAREN }
 | ")"			{ adv lexbuf; RPAREN }
 | "{"			{ adv lexbuf; LBRACE }
 | "}"			{ adv lexbuf; RBRACE }
 | ":"			{ adv lexbuf; COLON }
 | "^"			{ adv lexbuf; POINTER }
 | "#"			{ adv lexbuf; ARRAY }
 | "set"		{ adv lexbuf; ASSIGN }
 | "@"			{ adv lexbuf; AT }
 | "."			{ adv lexbuf; DOT }
 | "def"		{ adv lexbuf; DEF }
 | "NIL"		{ adv lexbuf; NIL }
 | "void"		{ adv lexbuf; VOID }
 | "func"		{ adv lexbuf; FUNC }
 | "do"			{ adv lexbuf; DO }
 | "if"			{ adv lexbuf; IF }
 | "while"		{ adv lexbuf; WHILE }
 | "let"		{ adv lexbuf; LET }
 | "const"		{ adv lexbuf; CONST }
 | "global"		{ adv lexbuf; GLOBAL }
 | "struct"		{ adv lexbuf; STRUCT }
 | "type"		{ adv lexbuf; TYPE }
 | "asm"		{ adv lexbuf; ASM }
 | ">"			{ adv lexbuf; GT }
 | "<"			{ adv lexbuf; LT }
 | ">="			{ adv lexbuf; GTE }
 | "<="			{ adv lexbuf; LTE }
 | "="			{ adv lexbuf; EQ }
 | "/="			{ adv lexbuf; NEQ }
 | "<<"			{ adv lexbuf; SHL }
 | ">>"			{ adv lexbuf; SHR }
 | "and"		{ adv lexbuf; AND }
 | "or"			{ adv lexbuf; OR }
 | "not"		{ adv lexbuf; NOT }
 | "xor"		{ adv lexbuf; XOR }
 | "band"		{ adv lexbuf; BAND }
 | "bor"		{ adv lexbuf; BOR }
 | "bnot"		{ adv lexbuf; BNOT }
 | "bxor"		{ adv lexbuf; BXOR }
 | "true"		{ adv lexbuf; BOOLEAN( true ) }
 | "false"		{ adv lexbuf; BOOLEAN( false ) }
 | "force"		{ adv lexbuf; FORCE }
 | "/-"			{ adv lexbuf; inComment := !inComment + 1; 
 				bcomment lexbuf }
 | str			{ adv lexbuf; STRING( str2str (gs lexbuf) ) }
 | id			{ adv lexbuf; SYMBOL( (gs lexbuf) ) }
 | eof			{ EOF }
 | _			{ errorAndDie "Invalid token!" }

and bcomment = parse
   "/-"			{ adv lexbuf; inComment := !inComment + 1; 
                          bcomment lexbuf }
 | "-/"			{ adv lexbuf; inComment := !inComment - 1; 
                          if !inComment <= 0 then token lexbuf
			                    else bcomment lexbuf }
 | '\n'			{ nl (); bcomment lexbuf }
 | _			{ adv lexbuf; bcomment lexbuf } 


and lcomment = parse
   '\n'			{ nl (); token lexbuf }
 | _			{ adv lexbuf; lcomment lexbuf }
