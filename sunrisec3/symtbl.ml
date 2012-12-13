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


type vartype = {
  vartype : Syntree.typestm;
  varval : Syntree.stmt;
  varalloc : alloctype;
  varsize : int;
  (* is constant? *)
  varconst : bool;
}
;;

type typetype =
    Syntree.typestm
;;

type package = {
  mutable smsymtbl : (string, vartype) Hashtbl.t list;
  mutable smtypetbl : (string, typetype) Hashtbl.t;
};;

let getType pkg name =
  if Hashtbl.mem pkg.smtypetbl name then
    Hashtbl.find pkg.smtypetbl name
  else
    errorAndDie ("getType: Type " ^ name ^ " does not exist!")
;;


let makePackage () =  {
  smsymtbl = [Hashtbl.create 16];
  smtypetbl = Hashtbl.create 24;
};;


(* This should also check the type table to work out size of structs
   and types
*)
let rec getSize pkg arch = function
    Ptrtype( _ ) -> arch.pointersize
  | Arraytype( len, typ ) -> len * (getSize pkg arch typ)
  | Functype( _ ) -> arch.pointersize
  | Customtype( str ) -> let a = (getType pkg str) in 
      getSize pkg arch a
  | Voidtype -> 0
      (* For now at least, compound types = function pointers *)
  | Compoundtype( _ ) -> arch.pointersize 
  | Structtype( items ) -> 
      let structsize x y =
	match y with 
	    Structitem( _, typ, _ ) -> x + (getSize pkg arch typ) 
      in
	List.fold_left structsize 0 items
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
  | Str -> arch.pointersize
  | Bool -> arch.boolsize
  | Nulltype -> arch.pointersize


and getLocalSize pkg tp = getSize pkg Sizes.localarch tp


(* Makes a variable, works out it's size itself 
   Directness is whether the variable is a reference; since they're implicit,
   we have to do some work (elsewhere) to get it.
*)


and makeVar pkg vtype vval valloc vconst = {
  vartype = vtype;
  varval = vval;
  varalloc = valloc;
  varsize = getLocalSize pkg vtype;
  varconst = vconst;
}

(* Returns an item if it exists... *)
and getVar pkg name =
  let isWhatWeWant x =
    Hashtbl.mem x name
  in
    try 
      Hashtbl.find (List.find isWhatWeWant pkg.smsymtbl;) name
    with
	Not_found -> errorAndDie ("Var \"" ^ name ^ "\" does not exist!");
;;



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


let pushScope pkg =
  pkg.smsymtbl <- (Hashtbl.create 16) :: pkg.smsymtbl
;;

let popScope pkg =
  if pkg.smsymtbl = [] then
    raise (SymtblException "Tried to pop the global scope!!")
  else
    pkg.smsymtbl <- List.tl pkg.smsymtbl
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
   So now I shall rip it apart and do it right.
   *rip rip rip gnaw tear crunch wail*
*)
(* Right now, types must compare exactly.
   However, (type foo :int) (let (a :foo)) (<- a 10) will work.
   And I'm making it so small numbers coerce implicitly to big numbers.
*)

let isInt typ =
  match typ with
      Int
    | Uint
    | Intsize( _ )
    | Uintsize( _ )
    | Long
    | Ulong -> true
    | _ -> false
;;

let isFloat typ =
  match typ with
    | Float
    | Floatsize( _ )
    | Double -> true
    | _ -> false
;;

let isNumber typ =
  (isInt typ) or (isFloat typ)
;;

(* This becomes easier once we realize that there are THREE types of numbers:
   Integers, unsigned integers, and floats.
   Integers can only be implicitly coerced to any integer of greater or
   equal size and the same signed-ness, or to a float.
   A float can only be implicitly coerced to a float of greater or equal
   size.
*)
let numberIsAllowed pkg f t =
  if (isNumber f) && (isNumber t) then
    match f with
	Int -> 
	  (match t with
	     | Int
	     | Intsize( _ )
	     | Long -> (getLocalSize pkg f) <= (getLocalSize pkg t)

	     | Uint
	     | Uintsize( _ )
	     | Ulong -> false

	     | Float
	     | Floatsize( _ )
	     | Double -> true
	     | _ -> errorAndDie "numberIsAllowed: This is impossible!"
	  )
      | Uint -> 
	  (match t with
	     | Int
	     | Intsize( _ )
	     | Long -> false

	     | Uint
	     | Uintsize( _ )
	     | Ulong -> (getLocalSize pkg f) <= (getLocalSize pkg t)

	     | Float
	     | Floatsize( _ )
	     | Double -> true
	     | _ -> errorAndDie "numberIsAllowed: This is impossible!"
	  )
      | Intsize( _ ) ->
	  (match t with
	     | Int
	     | Intsize( _ )
	     | Long -> (getLocalSize pkg f) <= (getLocalSize pkg t)

	     | Uint
	     | Uintsize( _ )
	     | Ulong -> false

	     | Float
	     | Floatsize( _ )
	     | Double -> true
	     | _ -> errorAndDie "numberIsAllowed: This is impossible!"
	  )
      | Uintsize( _ ) ->
	  (match t with
	     | Int
	     | Intsize( _ )
	     | Long -> false

	     | Uint
	     | Uintsize( _ )
	     | Ulong -> (getLocalSize pkg f) <= (getLocalSize pkg t)

	     | Float
	     | Floatsize( _ )
	     | Double -> true
	     | _ -> errorAndDie "numberIsAllowed: This is impossible!"
	  )
      | Long -> 
	  (match t with
	     | Int
	     | Intsize( _ )
	     | Long -> (getLocalSize pkg f) <= (getLocalSize pkg t)

	     | Uint
	     | Uintsize( _ )
	     | Ulong -> false

	     | Float
	     | Floatsize( _ )
	     | Double -> true
	     | _ -> errorAndDie "numberIsAllowed: This is impossible!"

	  )
      | Ulong -> 
	  (match t with
	     | Int
	     | Intsize( _ )
	     | Long -> false

	     | Uint
	     | Uintsize( _ )
	     | Ulong -> (getLocalSize pkg f) <= (getLocalSize pkg t)

	     | Float
	     | Floatsize( _ )
	     | Double -> true
	     | _ -> errorAndDie "numberIsAllowed: This is impossible!"
	  )
      | Float -> 
	  (match t with
	     | Int
	     | Intsize( _ )
	     | Long -> false

	     | Uint
	     | Uintsize( _ )
	     | Ulong -> false

	     | Float
	     | Floatsize( _ )
	     | Double -> (getLocalSize pkg f) <= (getLocalSize pkg t)
	     | _ -> errorAndDie "numberIsAllowed: This is impossible!"
	  )
      | Floatsize( _ ) ->
	  (match t with
	     | Int
	     | Intsize( _ )
	     | Long -> false

	     | Uint
	     | Uintsize( _ )
	     | Ulong -> false

	     | Float
	     | Floatsize( _ )
	     | Double -> (getLocalSize pkg f) <= (getLocalSize pkg t)
	     | _ -> errorAndDie "numberIsAllowed: This is impossible!"
	  )
      | Double ->
	  (match t with
	     | Int
	     | Intsize( _ )
	     | Long -> false

	     | Uint
	     | Uintsize( _ )
	     | Ulong -> false

	     | Float
	     | Floatsize( _ )
	     | Double -> (getLocalSize pkg f) <= (getLocalSize pkg t)
	     | _ -> errorAndDie "numberIsAllowed: This is impossible!"
	  )
      | _ -> errorAndDie "numberIsAllowed: This is more impossible!"
  else
    errorAndDie ("Number " ^ (typestmt2str f) ^ 
		 " cannot be assigned to " ^ (typestmt2str t) ^
		 " without a force!")

;;

let isStruct = function
    Structtype( _ ) -> true
  | _ -> false
;;

let isPointer = function
    Ptrtype( _ ) -> true
  | Functype( _ ) -> true
  | _ -> false
;;

let getPtrval = function
    Ptrtype( a ) -> a
  | _ -> Voidtype
;;

let rec resolvePtrval = function
    Ptrtype( a ) -> resolvePtrval a
  | a -> a
;;

let isArrayType = function
    Arraytype( _ ) -> true
  | _ -> false
;;

let isCompoundType = function
    Compoundtype( _ ) -> true
  | _ -> false
;;

let rec getArrayLen f =
  match f with
      Arraytype( len, _ ) -> len
    | Ptrtype( a ) -> getArrayLen a
    | _ -> errorAndDie ("getArrayLen: Given a " ^ (typestmt2str f))
;;

let rec getArrayType f =
  match f with
      Arraytype( _, t ) -> t
    | Ptrtype( a ) -> getArrayType a
    | _ -> errorAndDie ("getArrayType: Given a " ^ (typestmt2str f))
;;

let pointsToArray t =
  let pt = resolvePtrval t in
    isArrayType pt
;;

(* Returns true if an array has a length > 0 or a pointer aims at an
   array with any length, even -1 (no fixed size in terms of
   type-checking, though they are still bounds-checked.)
*)
let isSaneArray pkg t =
  let t1 = resolveCustomType pkg t in
  let l = getArrayLen t1 in

    if isPointer t1 then
      if pointsToArray t1 then
	if l = (-1) or l > 0 then
	  true
	else begin
	  false
	end
      else
	errorAndDie ("isSaneArray: Given a " ^ (typestmt2str t) ^
		     ", which isn't array and REALLY REALLY shouldn't " ^
		     "even be getting to this function!")
    else begin
      if l > 0 then
	true
      else begin
	false
      end
    end
;;


(* This returns true if typ1 is a pointer to typ2 or vice versa. *)
let rec hasCompatiblePointer pkg typ1 typ2 =
  (* This covers pointer auto-referencing, I'm 90% certain it work *)
  if isPointer typ1 then
    (* First we check to see if typ2 is NIL, which can be assigned to any 
       pointer *)
    if typ2 = Nulltype then
      true
    else
      hasCompatiblePointer pkg (getPtrval typ1) typ2
  else if isPointer typ2 then
    if typ1 = Nulltype then
      true
    else
      hasCompatiblePointer pkg typ1 (getPtrval typ2)

  (* Otherwise, if the types are equal (for whatever standard of
     "equality" we use), it works. *)
  else if hasCompatibleType pkg typ1 typ2 then
    true
  else
    false

(* Note that the order of typ1 and typ2 IS significant, because
   numberIsAllowed only works one way (int8 -> int16, but int16 does not 
   -> int8.  However, the exact context and junk is more or less arcane.
   As in, there's some logic behind it, but I don't want to bother working
   out exactly what.

   Hmm, this is also probably going to get a bit weird with regards to
   pointers to arrays...
   Basically, the deal is that arrays must have a fixed size, but pointers
   to arrays don't necessarily.  Of course, given the recursive and 
   relatively loose nature of the structures involved, that's a bit wiggy.
   There's nothing in the parser that prevents you from writing :#:foo,
   with no length attached.
*)

(* Basically, it works like this:
   typ1 and typ2 are the same type and length
   or, typ1 or typ2 or both is a pointer to the same type and length
   or, typ1 or typ2 or both is a pointer to the same type and 
   unknown length.
*)
and hasCompatibleArray pkg typ1 typ2 =
  (* Kay, see, the thing is, if isSaneArray works then we KNOW that
     the array either has a reasonable length, is a pointer to same, or
     is a pointer to an array with variable length.  Thus we can work on
     those assumptions, and assume we're working with a pointer if we get
     an array with -1 length. *)
  if (isSaneArray pkg typ1) && (isSaneArray pkg typ2) then
    let a = resolvePtrval typ1
    and b = resolvePtrval typ2 in
    let al = getArrayLen a
    and bl = getArrayLen b in
    let at = getArrayType a
    and bt = getArrayType b in
      Printf.printf "Array check: %s and %s\n"
	(typestmt2str typ1) (typestmt2str typ2);
      (* XXX: Not quite right, should check for compatibility *)
      if a = b then 
	true
      else if at = bt then
	if (al = bl) or (al = -1) or (bl = -1) then
	  true
	else
	  false
      else
	false
  else
    errorAndDie ("Array " ^ (typestmt2str typ1) ^ " or " ^
		 (typestmt2str typ2) ^ " is not sane!  Help!")
      

(* Hideous, but somehow functional 
   Ah, edge-cases.
*)
and hasCompatibleCompoundType pkg typ1 typ2 =
  let rec loop t1 t2 =
    (match t1 with
	 Compoundtype( a1, b1 ) ->
	   (match t2 with
		Compoundtype( a2, b2 ) ->
		  let tp1 = resolveCustomType pkg a1
		  and tp2 = resolveCustomType pkg a2 in
		    if tp1 = tp2 then
		      loop b1 b2
		    else
		      false
	      | _ ->
		  let tp1 = resolveCustomType pkg t1
		  and tp2 = resolveCustomType pkg t2 in
		    tp1 = tp2)
	   
       | _ -> 
	   let tp1 = resolveCustomType pkg t1
	   and tp2 = resolveCustomType pkg t2 in
	     tp1 = tp2)
  in
    loop typ1 typ2



and hasCompatibleType pkg typ1 typ2 =
  let t1 = resolveCustomType pkg typ1
  and t2 = resolveCustomType pkg typ2 in
    if isNumber t1 && isNumber t2 then
      numberIsAllowed pkg t1 t2
    else if isPointer t1 || isPointer t2 then
      if pointsToArray t1 || pointsToArray t2 then
	hasCompatibleArray pkg t1 t2
      else
	(hasCompatiblePointer pkg t1 t2)
    else if isArrayType t1 || isArrayType t2 then
      hasCompatibleArray pkg t1 t2
    else if isCompoundType t1 || isCompoundType t2 then
      hasCompatibleCompoundType pkg t1 t2
    else
      t1 = t2
;;



(* This takes two types, and if the first can be coerced to the second (such 
   as an int16 turning into an int8, order is important), return the coerced 
   type.
   If given a non-coercable type (like a struct), the hasComaptibleType will
   fail, so...
*)
let forceType pkg totype fromtype =
  let rec isForcable typ =
    match typ with
	Customtype( x ) -> isForcable (resolveCustomType pkg typ)
      | Ptrtype( _ )
      | Intsize( _ )
      | Uintsize( _ )
      | Floatsize( _ )
      | Int | Long | Uint | Ulong | Float | Double | Char | Bool ->
	  true
      | other -> false
  in
    if (isForcable fromtype) && (isForcable totype) then
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
      "Var \"%s\": type %s, alloc type: %s, size: %d, const? %b\n" 
      nm (Syntree.typestmt2str dat.vartype) (alloctype2str dat.varalloc) 
      dat.varsize dat.varconst
  and printType nm dat =
    Printf.printf "Type: %s, %s\n" nm (Syntree.typestmt2str dat)
  in
    Hashtbl.iter printType pkg.smtypetbl;
    List.iter (Hashtbl.iter printVar) pkg.smsymtbl
;;



