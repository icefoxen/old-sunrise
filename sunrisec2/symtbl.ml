(* symtbl.ml
   Symbol table.

   There are two symbol tables: one for variables/functions, one for types.

   Okay.  I have to think of how packages are going to work later, 
   and how we remember scopes.  Types are global, of course.
   Okay.  A stack of hashtable-scopes, just for fun.

   Simon Heath
   11/04/2005
*)

open ErrorReport
open Syntree
open Sizes

exception SymtblException of string;;

type alloctype =
    Global
  | Const
  | Let
;;

(* This should also check the type table to work out size of structs
   and types
*)
let rec getSize pkg arch = function
    Ptrtype( _ ) -> arch.pointersize
  | Arraytype( len, typ ) -> len * (getSize pkg arch typ)
  | Functype( _ ) -> arch.pointersize
  | Customtype( _ ) -> ErrorReport.errorAndDie "XXX: Size of custom types!"
  | Voidtype -> 0
      (* For now at least, compound types = function pointers *)
  | Compoundtype( _ ) -> arch.pointersize 
  | Structtype( _ ) -> ErrorReport.errorAndDie "XXX: Size of structs!"
  | Intsize( i ) -> i
  | Uintsize( i ) -> i
  | Floatsize( i ) -> i
  | Int -> arch.intsize
  | Long -> arch.longsize
  | Float -> arch.floatsize
  | Double -> arch.doublesize
  | Uint -> arch.intsize
  | Ulong -> arch.longsize
  | Char -> arch.charsize
  | Str -> ErrorReport.error "Hmm, work out const-length strings..."; arch.pointersize
  | Bool -> arch.boolsize
  | Nulltype -> arch.pointersize
;;

let getLocalSize pkg tp = getSize pkg Sizes.localarch tp;;




type vartype = {
  vartype : Syntree.typestm;
  varval : Syntree.stmt;
  varalloc : alloctype;
  varsize : int;
  (* is constant? *)
  varconst : bool;
}
;;

(* Makes a variable, works out it's size itself 
   Directness is whether the variable is a reference; since they're implicit,
   we have to do some work (elsewhere) to get it.
*)
let makeVar pkg vtype vval valloc vconst = {
  vartype = vtype;
  varval = vval;
  varalloc = valloc;
  varsize = getLocalSize pkg vtype;
  varconst = vconst;
};;


type typetype =
    Syntree.typestm
;;

type package = {
  mutable smsymtbl : (string, vartype) Hashtbl.t list;
  mutable smtypetbl : (string, typetype) Hashtbl.t;
};;

let makePackage () =  {
  smsymtbl = [Hashtbl.create 16];
  smtypetbl = Hashtbl.create 24;
}

(* A variable that doesn't exist, for initialization and error-checking and 
   such. *)
let nullvar = makeVar (makePackage ()) 
		Syntree.Voidtype Syntree.Nullstm Global true;;



let addVar pkg name vr =
  if Hashtbl.mem (List.hd pkg.smsymtbl) name then
    errorAndDie ("Variable " ^ name ^ " redefined!")
  else
    Hashtbl.add (List.hd pkg.smsymtbl) name vr
;;

let varExists pkg name =
  let rec loop currpkg name rest =
    if Hashtbl.mem currpkg name then
      true
    else if rest = [] then
      false
    else
      loop (List.hd rest) name (List.tl rest)
  in
    loop (List.hd pkg.smsymtbl) name (List.tl pkg.smsymtbl)
;;

let getVar pkg name =
  let lst = ref pkg.smsymtbl in
  let res = ref nullvar in
    while !lst <> [] do
      let itm = List.hd !lst in
	if Hashtbl.mem itm name then (
	  res := Hashtbl.find itm name;
	  lst := List.tl !lst;
	)
	else
	  lst := List.tl !lst;
    done;
    if !res = nullvar then
      errorAndDie ("Var \"" ^ name ^ "\" does not exist!");
    !res
;;

let pushScope pkg =
  pkg.smsymtbl <- (Hashtbl.create 16) :: pkg.smsymtbl
;;

let popScope pkg =
  if pkg.smsymtbl = [] then
    raise (SymtblException "Tried to pop the global scope!!")
  else
    pkg.smsymtbl <- List.tl pkg.smsymtbl
;;

let getType pkg name =
  if Hashtbl.mem pkg.smtypetbl name then
    Hashtbl.find pkg.smtypetbl name
  else
    errorAndDie "getType: Type %s does not exist!" name
;;

let typeExists pkg name =
  Hashtbl.mem pkg.smtypetbl name
;;




(* Takes a Customtype and resolves it down to what it fundamentally is *)
let rec resolveCustomType pkg typ =
  match typ with
      Customtype( name ) -> 
	let t = getType pkg name in
	  resolveCustomType pkg t
    | a -> a
;;

(* XXX: This is all a big mess 'cause I'm an idiot and tried to implement
   half-assed polymorphism!
*)
(* Right now, types must compare exactly.
   XXX: Later on, coercion and such will happen here.
   Pointer auto-referencing might not work correctly.
*)
let rec hasCompatibleType pkg typ1 typ2 =
  let rec isPointer = function
      Ptrtype( _ ) -> true
    | _ -> false
  and getPtrval = function
      Ptrtype( a ) -> a
    | _ -> Voidtype
  in

  (* I THINK this covers pointer auto-referencing *)
  (* First, trivial case --this is very right, 'cause Customtypes with 
     with different names can never intermix. (Dunno quite how right that is,
     actually, but...)  *)
  if typ1 = typ2 then
    true
  (* Then see if typ1 is a pointer to typ2 *)
  else if isPointer typ1 then
    (* First we check to see if typ2 is NIL, which can be assigned to any 
       pointer *)
    if typ2 = Nulltype then
      true
    else
      hasCompatibleType pkg (getPtrval typ1) typ2
  (* Then see if typ2 is a pointer to typ1 --NIL doesn't work this way 
     around *)
  else if isPointer typ2 then
    hasCompatibleType pkg typ1 (getPtrval typ2)
  (* Otherwise, it's false. *)
  else
    false
;;

(* This takes two types, and if the first can be coerced to the second (such 
   as an int8 turning into an int16, order is important), return the coerced 
   type.
   If given a non-coercable type (like a struct), the hasComaptibleType will
   fail, so...
*)
let coerceType pkg fromtype totype =
  if hasCompatibleType pkg fromtype totype then
    totype
  else
    errorAndDie ("coerceType: Failed!  " ^ (typestmt2str fromtype) ^ 
		 " cannot be coerced to " ^ (typestmt2str totype))
;;



let varHasCompatibleType pkg name typ =
  let v = getVar pkg name in
    hasCompatibleType pkg v.vartype typ
;;

let getVarType pkg name =
  let v = getVar pkg name in
    v.vartype
;;


let addType pkg name typ =
  if Hashtbl.mem pkg.smtypetbl name then
    errorAndDie ("addType: Type name " ^ name ^ " redefined!")
  else
    Hashtbl.add pkg.smtypetbl name typ
;;



let alloctype2str = function
    Global -> "Global"
  | Const -> "Const"
  | Let -> "Let"
;;


(* Takes a vardecl and returns true if it's a direct type (int, pointer, etc)
   and false if it's an indirect type (var-length array, structure).
   This is for when we're not sure; local types and @'d structure fields
   are always direct.
   Global values... hmm, the spec says only fixed-length arrays are allowed
   for global values.  This may not be the case.  Let's treat globals exactly
   like let variables; non-atomic types are references.
   Constants are always non-references.
   Fixed-length arrays are always non-references.
*)
(* Oh, I don't need this!  Bliss! 
let rec isDirect pkg vardecl =
  match vardecl with 
      Vardecl( _, typestm, _ ) ->
	match typestm with
	    Ptrtype( _ ) -> true
	  | Arraytype( len, _ ) -> if len < 0 then false else true
	  | Functype( _ ) -> false
	  | Customtype( nm ) ->  isDirect pkg 
	      (Vardecl( "", (getType pkg nm), Nullstm ))
	  | Voidtype -> 
	      errorAndDie "Semant.isDirect: Variables may not be void!"
	  | Compoundtype( a, b ) -> false
	  | Str -> false
	  | _ -> true
*)

(* XXX: Do we use this with consts?  o_O *)
let addVarDecl pkg vd =
  match vd with
      Vardecl( name, typ, defval ) ->
	let v = makeVar pkg typ defval Let false in
	  addVar pkg name v 

;;







(* Dump a package, for debugging (and probably later, actual package 
   interfaces) *)
let printPackage pkg =
  let printVar nm dat =
    Printf.printf 
      "Var %s: type %s, (nodefault), alloc type: %s, size: %d, const? %b\n" 
      nm (Syntree.typestmt2str dat.vartype) (alloctype2str dat.varalloc) 
      dat.varsize dat.varconst
  and printType nm dat =
    Printf.printf "Type: %s, %s\n" nm (Syntree.typestmt2str dat)
  in
    Hashtbl.iter printType pkg.smtypetbl;
    List.iter (Hashtbl.iter printVar) pkg.smsymtbl
;;
