(* syntree.ml
   Abstract syntax tree for Sunrise.

   ...okay, I need to think about this sanely for a while, instead of
   working like it's GCC.
   Main types: expressions, statements, declerations, variable declerations,
   variable references, types, type declerations...

   Simon Heath
   11/4/2005
*)


open Printf



type operation =
    Add
  | Sub
  | Mul
  | Div
  | Mod
  | Eq
  | Neq
  | Gt
  | Gte
  | Lt
  | Lte
  | And
  | Or
  | Not
  | Xor
  | Band
  | Bor
  | Bnot
  | Bxor
  | Shl
  | Shr


and stmt = 
    (* Operation, args *)
    Opexpr of operation * stmt list  
      (* Name, args *)
  | Funcall of stmt * stmt list
      (* Condition, if part, else part (possibly a Nullstm) *)
  | Ifstm of stmt * stmt * stmt
      (* Condition, body *)
  | Whilestm of stmt * stmt list
      (* Body *)
  | Dostm of stmt list
      (* Asm string (format undefined so far) *)
  | Asmstm of string
      (* Var decls *)
  | Letstm of vardecl list
      (* Nothing; an empty statement *)
  | Nullstm
      (* A constant *)
  | Conststm of const
      (* A function decleration...  kinda messy since we already have a 
	 decl type, but... Read down for clarification/rantage.  *)
  | Funstm of string * typestm * vardecl list * stmt list
      (* A variable name *)
  | Varstm of string
      (* An array reference *)
  | Aref of stmt * stmt
      (* A structure reference --the stmt can be another sref*)
  | Sref of stmt * string
      (* A pointer reference *)
  | Assignstm of stmt * stmt
      (* A force expression *)
  | Forcestm of typestm * stmt
      (* A pointer dereference *)
  | Ptrstm of stmt
      (* An address reference *)
  | Addrstm of stmt

and const =
    Intconst of int
  | Floatconst of float
  | Noneconst

and vardecl =
    (* Name, type, default value *)
    Vardecl of string * typestm * stmt

and decl =
    (* Name, return type, args, body *)
    Fundecl of string * typestm * vardecl list * stmt list
      (* Name, type *)
  | Typedecl of string * typestm
      (* Name, fields *)
(*
  | Structdecl of string * structitem list
*)
  | Globaldecl of vardecl
  | Constdecl of vardecl

(*
and structitem =
  (* Name type, default value *)
  Structitem of string * typestm * const
*)

and typestm =
    Int
  | Float
  | Nonetype
;;

(* Check if a symbol is a primative type 
   Sizes of int, long etc are architecture-dependant, see sizes.ml
*)
let parseType = function
    "int" -> Int
  | "float" -> Float
  | a -> ErrorReport.errorAndDie (a ^ " is not a valid type!")
;;

(* Slightly ugly hacks to handle function stuff.
   This arises from the uncomfortable situation that there are really three
   different types of ways we can have a "function": We can have a function
   declared in the top level, a fundecl.  Or we can have a function decl
   nested inside another function, a funstm.  Or we can have a function 
   declared as a variable and assigned to some value, a functype.

   This is a dilemma that results mainly from Sunrise's syntax and parser,
   I suppose...  Statements and declerations are not orthogonal, but some
   serve the same purpose (value and function decleration).  I could 
   technically make declerations and statements the same OCaml type, but
   that would complicate certain parts of the syntax tree (as opposed to 
   complicating these parts instead) and give us less benefit from OCaml's
   type-checking; it would technically allow, for instance, a global decl
   inside a function decl, which shouldn't be allowed.  The parser doesn't
   (shouldn't) allow it anyway, but BSTS.

   Potential solution/simplification: Have a Funstmt be a wrapper for
   a Fundecl, or vice-versa.
*)

let funstm2fundecl = function
    Funstm( a, b, c, d ) -> Fundecl( a, b, c, d )
  | _ -> raise (Failure "funstm2fundecl wasn't given a Funstm")
;;

let fundecl2funstm = function
    Fundecl( a, b, c, d ) -> Funstm( a, b, c, d )
  | _ -> raise (Failure "fundecl2stm wasn't given a Fundecl")
;;

let vardecl2typestm = function
    Vardecl( _, typestm, _ ) -> typestm
;;
(*
let vardecllst2typestm lst =
  let vardecl2typestm = function
      Vardecl( _, ts, _ ) -> ts
  in
  let rec loop vdlst =
    match vdlst with
	[] -> Voidtype
      | a :: b ->
	  if b = [] then
	    (vardecl2typestm a)
	  else
	    Compoundtype( (vardecl2typestm a), loop b )
  in
    loop lst
;;

let rec typestm2typestmlst = function
    Compoundtype( itm, rest ) -> itm :: (typestm2typestmlst rest)
  | other -> [other]
;;

let rec typestmlst2typestm l = 
  match l with
    [] -> Voidtype
  | a :: [] -> a
  | a :: b -> Compoundtype( a, (typestmlst2typestm b) )
;;


let fundecl2typestm = function
    Fundecl( _, b, c, _ ) -> Functype( b, (vardecllst2typestm c) )
  | _ -> raise (Failure "fundecl2typestm wasn't given a Fundecl")
;;

let funstm2typestm = function
    Funstm( _, b, c, _ ) -> Functype( b, (vardecllst2typestm c) )
  | _ -> raise (Failure "funstm2typestm wasn't given a Funstm")
;;
*)
(*
(* Not tail-recursive, but it doesn't much matter *)
let varDeclLst2typestm v =
  let rec loop vdlst =
    match vdlst with
	[] -> Voidtype
      | a :: b ->
	  if b = [] then
	    a
	  else
	    Compoundtype( a, loop b )
  in
    loop v
;; 
*)
    


(*
let compoundtype2list x =
  let rec helper cmptype lst =
    match cmptype with
	Compoundtype( a, b ) ->
      | a -> a :: lst
  in
    helper x []
;;
*)


(***********************)
(* Unparsing functions *)

let rec typestmt2str = function
(*    Ptrtype( typstm ) -> 
      ":^" ^ (typestmt2str typstm)
  | Arraytype( size, typestmt ) ->
      ":#" ^ (if size = -1 then "" else (string_of_int size)) ^ 
      (typestmt2str typestmt)
  | Functype( rettype, vartype ) ->
      ":{" ^ (typestmt2str rettype) ^ " " ^ (typestmt2str vartype) ^ "}"
  | Customtype( s ) -> ":" ^ s
  | Voidtype -> ":void"
  | Compoundtype( fsttype, sndtype ) -> 
      (typestmt2str fsttype) ^ (typestmt2str sndtype)
  | Structtype( itmlst ) -> ":someStruct"
  | Intsize( n ) -> ":int" ^ (string_of_int (n * 8))
  | Uintsize( n ) -> ":uint" ^ (string_of_int (n * 8))
  | Floatsize( n ) -> ":float" ^ (string_of_int (n * 8))
*)
  | Int -> ":int"
  | Float -> ":float"
(*
  | Long -> ":long"

  | Double -> ":double"
  | Uint -> ":uint"
  | Ulong -> ":ulong"
  | Char -> ":char"
  | Str -> ":str"
  | Bool -> ":bool"
*)
  | Nonetype -> "None"
;;

let rec op2str = function
    Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"
  | Eq -> "="
  | Neq -> "/="
  | Gt -> ">"
  | Gte -> ">="
  | Lt -> "<"
  | Lte -> "<="
  | And -> "and"
  | Or -> "or"
  | Not -> "not"
  | Xor -> "xor"
  | Band -> "band"
  | Bor -> "bor"
  | Bnot -> "bnot"
  | Bxor -> "bxor"
  | Shl -> "<<"
  | Shr -> ">>"
;;
