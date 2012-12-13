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
  | Local
  | Let
;;

(* This should also check the type table to work out size of structs
   and types
*)
let rec getSize pkg arch = function
    Ptrtype( _ ) -> arch.pointersize
  | Arraytype( len, typ ) -> len * (getSize pkg arch typ)
  | Functype( _ ) -> arch.pointersize
  | Customtype( _ ) -> arch.pointersize (* XXX *)
  | Voidtype -> 0
      (* For now at least, compound types = function pointers *)
  | Compoundtype( _ ) -> arch.pointersize 
  | Structtype( _ ) -> ErrorReport.errorAndDie "Size of structs!"
  | Intsize( i ) -> i
  | Uintsize( i ) -> i
  | Floatsize( i ) -> i
  | Byte -> arch.bytesize
  | Int -> arch.intsize
  | Long -> arch.longsize
  | Float -> arch.floatsize
  | Double -> arch.doublesize
  | Uint -> arch.intsize
  | Ulong -> arch.longsize
  | Char -> arch.charsize
  | Str -> ErrorReport.error "Hmm, work out const-length strings..."; arch.pointersize
  | Bool -> arch.boolsize
;;

let getLocalSize pkg tp = getSize pkg Sizes.localarch tp;;




type vartype = {
  vartype : Syntree.typestm;
  varval : Syntree.stmt;
  varalloc : alloctype;
  (* This is whether or not the variable is a reference *)
  vardirect : bool;
  varsize : int;
  (* is constant? *)
  varconst : bool;
}
;;

(* Makes a variable, works out it's size itself 
   Directness is whether the variable is a reference; since they're implicit,
   we have to do some work (elsewhere) to get it.
*)
let makeVar pkg vtype vval valloc vdirect vconst = {
  vartype = vtype;
  varval = vval;
  varalloc = valloc;
  vardirect = vdirect;
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
		Syntree.Voidtype Syntree.Nullstm Global false true;;



let addVar pkg name vr =
  if Hashtbl.mem (List.hd pkg.smsymtbl) name then
    errorAndDie "Variable %s redefined!" name
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

(* Right now, types must compare exactly.
   Later on, coercion and such will happen here.
   XXX: ...hrm.  What type does NIL have anyway???
*)
let hasCompatibleType pkg typ1 typ2 =
  typ1 = typ2
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
    errorAndDie ("Type name " ^ name ^ " redefined!")
  else
    Hashtbl.add pkg.smtypetbl name typ
;;

let getType pkg name =
  if Hashtbl.mem pkg.smtypetbl name then
    Hashtbl.find pkg.smtypetbl name
  else
    errorAndDie "Type %s does not exist!" name
;;

let typeExists pkg name =
  Hashtbl.mem pkg.smtypetbl name
;;



let alloctype2str = function
    Global -> "Global"
  | Const -> "Const"
  | Local -> "Local"
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

and addVarDecl pkg vd =
  match vd with
      Vardecl( name, typ, defval ) ->
	let v = makeVar pkg typ defval Let (isDirect pkg vd) false in
	  addVar pkg name v 

;;







(* Dump a package, for debugging (and probably later, actual package 
   interfaces) *)
let printPackage pkg =
  let printVar nm dat =
    Printf.printf 
      "Var %s: type %s, (nodefault), alloc type: %s, direct? %b, size: %d, const? %b\n" 
      nm (Syntree.typestmt2str dat.vartype) (alloctype2str dat.varalloc) 
      dat.vardirect dat.varsize dat.varconst
  and printType nm dat =
    Printf.printf "Type: %s, %s\n" nm (Syntree.typestmt2str dat)
  in
    Hashtbl.iter printType pkg.smtypetbl;
    List.iter (Hashtbl.iter printVar) pkg.smsymtbl
;;
