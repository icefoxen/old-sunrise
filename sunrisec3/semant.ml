(* semant.ml
   Semantic checking for Sunrise.
   Basically works thus:
   Zeroth pass, setup:
   Initialize; add all the default types (if necessary; it isn't).
   Import packages, when they exist.
   First pass:
   Go through the syntax tree.  For each const/global, stick it in the
   global symbol table.  For each type, stick it in the type table.  For
   each function, stick the name and type in the global symbol table.
   Second pass:
   For each function, go through it.  Push a scope for each function and
   "do" block.  For each expression, figure out the types of it's arguments,
   and if they match correctly return the expression's type.
   The function that does the actual type matching is 
   Symtbl.hasCompatibleType.
   Signal an error if they don't match.  Signal an error if a variable or 
   type name doesn't exist.
   Pop a stack each time you leave a do block or function

   Whew, that's sorta messy.  I can see why compiler-writers like forward 
   references...

   Notes: Type matching is basically a collection of isolated but 
   sophisticated special cases.  Messy, but fairly contained.  Pointers
   and non-pointers of the same type automagically dereference, numbers
   suddenly turn from less-specific to more-specific types (I still don't
   have a sane way of handling signed and unsigned integer conversion),
   arrays compare each other's length and pointers to any-length array
   are allowed.  Now, what would be nice, is if we could alter the syntax
   tree at this point and add in little statements to explicitly note that
   these operations are taking place --basically, after we were done
   type-checking, we would have explicit references and dereferences, 
   all type conversions would be explicit, and so would most bounds-checks
   and stuff.  That would make generating IR rather simpler.  But that's
   not strictly necessary, and would complicate things because instead of
   just checking validity, we'd need to check validity AND generate code.

   The thing is... this is truely the best and simplest place to stick in
   various kinds of high-level optimization, like perhaps math constant 
   folding (since that can have effects on compile-time array bounds- 
   checking).  Though now that I think of that, no reason that COULDN'T
   happen in the IR...
   And it's really the ONLY reasonable place to stick in all the code for
   intermediate code-generation, or at least hooks for such.
   And the thing is, this is a rather big wodger of 400 lines or so
   (it seems like a lot more, trust me!) of very very tightly-integrated 
   code that does lots of weird and diverse shit to all parts of a bigass 
   and rather convoluted tree.  It REALLY doesn't need to try to be doing
   three things at once with it.  But making it simpler would require doing
   a lot of code duplication to, for instance, infer all the integer
   coercions and half the type checking all over again.  That's inefficient, 
   and probably also rather hard to maintain.
   I'm just moaning.  But it's bloody irritating.

   TODO:
   Make assigning to a constant an error.
   Check sizes and translation of custom types.
   Improve error reporting: line numbers, custom type names
   
   Simon Heath
   12/5/2005
*)

open Syntree
open ErrorReport

exception SemanticException of string


(* Perform various verification on structs.  Messy, but relatively 
   straightforward. *)
let structHasMember typ membername =
  let structNameEq = function
      Structitem( fieldname, _, _ ) -> fieldname = membername
  in
    match typ with
	Structtype( lst ) -> List.find structNameEq lst
      | _ -> errorAndDie ("structHasMember: looking for " ^ membername ^
			  " in a type that isn't a struct!")
;;

(* Raises an error if a struct has a duplicate field name 
   We get a list of names, sort it, then cdr down it testing to see if
   each name is exists in the rest of the list.
   Slow, but structs aren't going to be that long, so.
   Better way would be to sort the list, THEN go down it; sorting can be
   logn, this is always n^2ish
*)
let structMembersAreUnique fieldlst =
  let rec verifyMembers lst =
    match lst with
	[] -> ()
      | a :: b -> 
	  if List.mem a b then
	    errorAndDie ("Struct member " ^ a ^ " is duplicated!")
	  else
	    verifyMembers b
  in

  let itemnames = List.sort compare
    (List.map (function Structitem( fieldname, _, _ ) -> fieldname) fieldlst)
  in
    verifyMembers itemnames
;;


let structGetMemberType typ membername =
  let structNameEq = function
      Structitem( fieldname, _, _ ) -> fieldname = membername
  and structType = function
      Structitem( _, tp, _ ) -> tp
  in
  let rec structSearch nm lst =
    if lst = [] then
      errorAndDie ("structGetMemberType: Field " ^ nm ^ 
		   " does not exist in given struct!")
    else if structNameEq (List.hd lst) then
      structType (List.hd lst)
    else
      structSearch nm (List.tl lst)
  in
    match typ with
	Structtype( lst ) -> structSearch membername lst
      | _ -> errorAndDie ("structGetMemberType: looking for " ^ membername ^
			  " in a type that isn't a struct!")  
;;



(* Grabs the names of all the types, globals, consts, and functions, and
   puts them into the symbol table.  We do this so we don't need forward
   reference.
*)
let populate syntree pkg =
  let grabDecl = function
      Typedecl( name, typestm ) -> 
	Symtbl.addType pkg name typestm
    | Structdecl( name, structitems ) ->
	Symtbl.addType pkg name (Structtype( structitems ))
    | Fundecl( name, rettype, args, _ ) -> 
	Symtbl.addVar pkg name 
	  (Symtbl.makeVar pkg 
	     (Functype( rettype, (vardecllst2typestm args) ))
	     (Conststm( Nilconst )) Symtbl.Global true)
    | Globaldecl( Vardecl( name, typestm, defval ) ) -> 
	Symtbl.addVar pkg name (Symtbl.makeVar pkg typestm defval 
				  Symtbl.Global false)
    | Constdecl( Vardecl( name, typestm, defval ) ) ->
	Symtbl.addVar pkg name (Symtbl.makeVar pkg typestm defval 
				  Symtbl.Global true)
  in
    List.iter grabDecl syntree
;;

(* Analyzes all the types, structs, globals, consts, and functions. 
   Makes sure the types all exist, types match, variables exist, and so on.
   We declare a bunch of sub-functions, each of which handles a certain type
   of syntax tree componant (statment, expression, vardecl, etc) and returns
   the type of the componant analyzed.  In other words, it treats everything
   as an expression.

   The hooks to do the back-end and code-generation may end up being
   interlaced here, to save a traversal and a bunch of code duplication
   handling analysis of scopes.

   XXX: Default values for non-normal-sized numbers!
   Works for floats but not ints?  Well, ints are bigger than int8's.
   "NIL is a special value that can be assigned to any pointer".
   XXX: Initialize fixed-length arrays where a single value is given!
   analyzeVar may need another argument to give it more context on directness,
   constantness, and so on...  The population of the symtable should handle
   some of that already though.  Don't do work twice.
   XXX: Make sure pointers to local values aren't returned, or local 
   values aren't assigned to non-local pointers (if possible...)
   Basically... check the last certain assignment of the pointer in
   question and make sure it wasn't local.  Should this happen in IR?
   No, because IR is typeless.
   XXX: Double-check arithmatic conversions...  (set intvar (+ 10 95.2))
   vs (set intvar 95.2)
*)

let analyze syntree pkg = 
  let rec analyzeDecl = function
      Fundecl( name, rettype, args, body ) -> 
	if Symtbl.varExists pkg name then
	  analyzeFunc name rettype args body
	else
	  raise (SemanticException "This should never happen! (because symtbl should be populated)")
    | Typedecl( name, typestm ) -> 
	if Symtbl.typeExists pkg name then 
	  analyzeType typestm
	else
	  raise (SemanticException "This should never happen!")
    | Structdecl( name, fields ) -> 
	if Symtbl.typeExists pkg name then
	  analyzeStruct name fields
	else
	  raise (SemanticException "This should never happen!")
    | Globaldecl( Vardecl( name, typestm, defval ) ) -> 
	if Symtbl.varExists pkg name then (
	  ignore (analyzeType typestm);
	  analyzeVar name defval; 
	)
	else
	  raise (SemanticException "This should never happen!")
    | Constdecl( Vardecl( name, typestm, defval ) ) -> 
	if Symtbl.varExists pkg name then ( 
	  ignore (analyzeType typestm);
	  analyzeVar name defval; 
	)
	else
	  raise (SemanticException "This should never happen!")

  (* Makes sure a function returns the right type, and analyzes it's 
     contents. 
  *)
  and analyzeFunc name rettype args body =
    (* First we make sure the return type matches the last statement 
       We have no explicit "return" or "break", so this is easy; the return 
       value is always the last statement 
       An explicit return statement also makes this easy.  Both implicit and
       explicit would make it (a bit more) complicated.
    *)
    if List.length body < 1 then
      errorAndDie (Printf.sprintf "Type %s returns %s but has no body!"
		     name (typestmt2str rettype))
    else (
      (* FIRST we push a new scope, add the arguments (no analysis,
	 'cause no default values...), analyze the function body, then
	 pop the scope and return the function sig. *)
      Symtbl.pushScope pkg;
      List.iter (fun x -> Symtbl.addVarDecl pkg x) args;
      List.iter (fun x -> ignore (analyzeStmt x)) body;

      (* THEN we check the type of the last statement Trying to
	 analyze the last statement before we've analyzed things like
	 var decleration is a bad bad idea.  As I learned the hard
	 way.
	 We have no explicit "return" or "break", so this is
	 easy; the return value is always the last statement An
	 explicit return statement also makes this easy.  Both
	 implicit and explicit would make it (somewhat) complicated.
      *)
      let lasttype = analyzeStmt (List.hd (List.rev body)) in
	(* Function returns void, we don't bother checking return type *)
	if rettype = Voidtype then (
	  Symtbl.popScope pkg;
	  fundecl2typestm (Fundecl( name, rettype, args, body ))
	    (* We check for compatible return type and do exact same thing *)
	) else if Symtbl.hasCompatibleType pkg lasttype rettype then (
	  Symtbl.popScope pkg;
	  fundecl2typestm (Fundecl( name, rettype, args, body ))
	)
	  (* Error *)
	else
	  errorAndDie (Printf.sprintf 
			 "Function %s declared to return %s but returns %s!"
			 name (typestmt2str rettype) 
			 (typestmt2str lasttype));
    )
      
  (* Makes sure a type statement is valid 
     ...Basically, make sure the type you're defining you name exists.  
     That's all so far.  Nothing sophisticated.
  *)
  and analyzeType typestm =
    match typestm with
        Ptrtype( ts ) -> analyzeType ts
      | Arraytype( len, ts ) -> analyzeType ts
      | Functype( rettype, args ) -> ignore (analyzeType rettype);
	  ignore (analyzeType args);
	  typestm
      | Compoundtype( ts, ts2 ) -> ignore (analyzeType ts); 
	  analyzeType ts2;
      | Customtype( name ) ->
	  if Symtbl.typeExists pkg name then
	    analyzeType (Symtbl.getType pkg name)
	  else
	    errorAndDie ("Type :" ^ name ^ " does not exist!")
      | Voidtype -> 
	  errorAndDie "You defined a type as void!  Don't do it."
	    (* Default types *)
      | other -> other

  (* Makes sure all the types in a structure are valid, no recursive fields,
     etc.
  *)
  and analyzeStruct name fields =
    List.iter (analyzeStructItem name) fields;
    structMembersAreUnique fields;
    Structtype( fields )

  (* When this gets called, the type table should already be populated
     with struct names, so recursive pointers are possible.  We just need to
     make sure the recursive field isn't a direct field.  *)
  and analyzeStructItem structname itm =
    let rec customTypeEqualStructName typ =
      match typ with
	  Customtype( name ) -> 
	    if name = structname then
	      true
	    else
	      let t = Symtbl.getType pkg name in
		customTypeEqualStructName t
	| a -> false
    in
      match itm with
	  (* Defval is always a valid constant, since it's put there by the
	     parser.  *)
	  Structitem( name, typ, defval ) ->
	    (* Check to see if it's a recursive struct, and that's it. *)
	    match typ with
		Customtype( nm ) ->
		  if customTypeEqualStructName typ then
		    errorAndDie 
		      ("Struct " ^ structname ^ 
		       " declares a recursive field: " ^ name)
		  else
		    ()  (* Everything is fine! *)
	      | _ -> () (* It's not a struct, we're not interested. *)

  (* Makes sure a variable decleration is valid, initializing value
     exists, etc.  Takes a name and a value; the name should already
     be in the symbol table, so.  
  *)
  and analyzeVar name defval =
    let deftype = analyzeStmt defval in
      if Symtbl.varHasCompatibleType pkg name deftype then
	Symtbl.getVarType pkg name
      else
	let msg = Printf.sprintf "Variable %s's default value is of the wrong\ntype!  It should be %s\n" name "XXX: fixme" in
	  errorAndDie msg


  (* Makes sure a statement is valid.  Nullstm's are ignored.
     An assignment returns the value assigned.  A vardecl, while loop,
     left-out else statement, etc, return Voidtype. *)
  and analyzeStmt stm =
    match stm with 
	Opexpr( op, stmlst ) -> analyzeOpexpr op stmlst
      | Funcall( fnexpr, args ) -> (* args is a list of statements *)
	  let fn = analyzeStmt fnexpr in
	    (match fn with
		 Functype( rettype, funargs ) -> (* funargs is Compoundtype *)
		   (* Make sure the given args are valid statements, then
		      turn them into a Compoundtype list *)
		   let argtypes = List.map (fun x -> analyzeStmt x) args in
		   let argtypes = typestmlst2typestm argtypes in
		     if Symtbl.hasCompatibleType pkg argtypes funargs then (
		       rettype
		     )else
		       errorAndDie ("Function has type " ^
				    (typestmt2str funargs) ^ " but is given " 
				    ^ (typestmt2str argtypes))
			 
	       | a -> errorAndDie ("Variable " ^ 
				   (typestmt2str a) ^ " is not a function!"))

      | Ifstm( cond, ifpart, elsepart ) ->
	  let condtype = analyzeStmt cond in
	    if Symtbl.hasCompatibleType pkg condtype Bool then
	      let t1 = analyzeStmt ifpart
	      and t2 = analyzeStmt elsepart in
		if Symtbl.hasCompatibleType pkg t1 t2 then
		  t1
		else
		  (errorAndDie ("If statement returns " ^ (typestmt2str t1) ^
				" but the else part returns " ^ (typestmt2str t2)))
	    else
	      errorAndDie ("If statement condition doesn't return bool!")

      | Whilestm( cond, body ) -> 
	  let condtype = analyzeStmt cond in
	    if Symtbl.hasCompatibleType pkg condtype Bool then
	      List.iter (fun x -> ignore (analyzeStmt x))  body
		(*ignore (analyzeStmt (List.hd (List.rev body))) *)
	    else
	      errorAndDie ("If statement condition doesn't return bool!");
	    Voidtype

      (* Returns the value of the last statement, like scheme "begin" *)
      | Dostm( stms ) ->
	  Symtbl.pushScope pkg;
	  List.iter (fun x -> ignore (analyzeStmt x)) stms;
	  let a = analyzeStmt (List.hd (List.rev stms)) in
	    Symtbl.popScope pkg;
	    a

      | Asmstm( str ) -> Voidtype

      (* Default checking of structs, numbers are weird, *)
      | Letstm( vdecls ) -> 
	  let insertvardecl = function
	      Vardecl( name, typ, vl ) ->
		if (Symtbl.hasCompatibleType pkg (analyzeStmt vl) typ) then
		  let v = Symtbl.makeVar pkg typ vl Symtbl.Let false in
		    Symtbl.addVar pkg name v

		(* An utter kludge, but I dunno how I want to do struct 
		   consts yet...  it doesn't work very well, 'cause:
		   1) default values are "part" of a struct type, and
		   2) two different structs can have identical members.
		*)
		else if Symtbl.isStruct (Symtbl.resolveCustomType pkg typ) then
		  let v = Symtbl.makeVar pkg typ vl Symtbl.Let false in
		    Symtbl.addVar pkg name v
		else
		  errorAndDie ("Var " ^ name ^ " has type " ^ 
			       (Syntree.typestmt2str typ) ^
			       " but has a default value of type " ^
			       (Syntree.typestmt2str (analyzeStmt vl)))
	  in
	    List.iter insertvardecl vdecls;
	    Voidtype
      | Nullstm -> Voidtype
      | Conststm( const ) -> analyzeConst const
      | Funstm( nm, rettype, vars, body ) -> 
	  let vr = 
	    (Symtbl.makeVar pkg 
	       (Functype( rettype, (vardecllst2typestm vars) ))
	       (Conststm( Nilconst )) Symtbl.Let true) in
	    Symtbl.addVar pkg nm vr;	   
	    analyzeFunc nm rettype vars body
      | Varstm( str ) -> Symtbl.getVarType pkg str
	  (* Okay, 2nd stm is a number or array, 1st is an array 
	     XXX: Okay, you can do some static array-length checks here
	     if you want.  Const or const-folded rvalues, for instance.  *)
      | Aref( stm1, stm2 ) ->
	  let rec isArray f =
	    match f with
		Arraytype( len, typ ) -> true
	      | Customtype( a ) -> isArray (Symtbl.resolveCustomType pkg f)
	      | _ -> false
	  in
	  let restype = 
	    if Symtbl.hasCompatibleType pkg (analyzeStmt stm2) Int then
	      analyzeStmt stm1
	    else if Symtbl.hasCompatibleType pkg (analyzeStmt stm2) Uint then
	      analyzeStmt stm1
	    else
	      errorAndDie ("Array referenced with a non-int index!")
	  in
	    if isArray restype then
	      restype
	    else
	      errorAndDie ("Tried to reference something that isn't an " ^
			   "array, but a " ^ (typestmt2str restype))
		
      (* Okay, str is an item name, 1st is an expr that returns a
	 struct *)
      | Sref( stm, str ) -> 
	  let stype = analyzeStmt stm in
	  let mtype = structGetMemberType stype str in
	    mtype
	      
      | Assignstm( lval, stm ) -> 
	  let lvaltype = analyzeStmt lval 
	  and stmtype = analyzeStmt stm in
	    (* This is a slightly silly bit of code to make sure you don't
	       assign to a const.  It's kinda complicated, 'cause a const can 
	       be a struct or an array. 
	       
	    *)
	    (match lval with 
		 Varstm( v ) ->		   
		   let vr = Symtbl.getVar pkg v in 
		     if vr.Symtbl.varconst then 
		       errorAndDie ("Tried to assign a value to const " ^ v)
	       | Aref( v, _ )
	       | Sref( v, _ ) ->
		   (match v with
		       Varstm( v ) ->
			 let vr = Symtbl.getVar pkg v in 
			   if vr.Symtbl.varconst then 
			     errorAndDie ("Tried to assign a value to const " ^ v)
		     | _ -> ())
	       | _ -> ()
	    );
	    
	    if Symtbl.hasCompatibleType pkg stmtype lvaltype then
	      lvaltype
	    else
	      errorAndDie ("Assignment between incompatible types: (set " ^
			   (typestmt2str lvaltype) ^ " " ^ 
			   (typestmt2str stmtype) ^ ")")
      | Forcestm( totype, stm ) -> 
	  (* Returns true if typ can be the target of a force statement
	     --In other words, only atomic types, not arrays, functions or
	     structs *)
	  let rec isForcable typ =
	    match typ with
		Arraytype( _ )
	      | Structtype( _ )
	      | Functype( _ )
	      | Compoundtype( _ ) -> false
	      | Nulltype -> errorAndDie ("Tried to coerce a type to NIL!")
	      | Customtype( _ ) -> isForcable
		  (Symtbl.resolveCustomType pkg typ)
	      | Ptrtype( t ) ->
		  (* Pointers can be forced to other pointers or ints *)
		  let isPointer = function
		      Ptrtype( _ ) -> true
		    | Intsize( _ )
		    | Uintsize( _ )
		    | Int
		    | Long
		    | Uint -> 
			Printf.eprintf "You are forcing a pointer to an int.  You better know what you're doing!\n";
			flush stderr;
			true
		    | _ -> false
		  in
		  let stmtype = analyzeStmt stm in
		    if isPointer stmtype then
		      true
		    else
		      errorAndDie ("Tried to force a " ^ 
				   (typestmt2str stmtype) ^
				   " to a pointer!\n")
	      | a -> true
	  in
	    if (isForcable totype) && (isForcable (analyzeStmt stm)) then
	      totype
	    else
	      errorAndDie ("Tried to force to an invalid type: " ^
			   (typestmt2str totype))

  (* Makes sure statements are valid.  *)
  and analyzeOpexpr op args =
    let checkstuff stm1 stm2 = 
      let a = analyzeStmt stm1
      and b = analyzeStmt stm2 in
	if Symtbl.hasCompatibleType pkg a b then
	  stm1
	else
	  errorAndDie ("analyzeOpexpr: whatever")
    and isBool stm =
      let f = analyzeStmt stm in
	match f with
	    Bool -> true
	  | _ -> false
    and isInt stm =
      let f = analyzeStmt stm in
	match f with
	    Int
	  | Uint
	  | Intsize( _ )
	  | Uintsize( _ )
	  | Long
	  | Ulong -> true
	  | _ -> false
    and isFloat stm =
      let f = analyzeStmt stm in
	match f with
	  | Float
	  | Floatsize( _ )
	  | Double -> true
	  | _ -> false
    in
    let isNum stm =
      (isInt stm) or (isFloat stm)
    in
    let checkNums lst =
      List.iter 
	(fun x -> if not (isNum x) then 
	   (errorAndDie "Number expected!"))
	lst
    and checkBools lst =
      List.iter 
	(fun x -> if not (isBool x) then 
	   (errorAndDie "Boolean expected!"))
	lst
    in
      match op with
	  Add
	| Sub
	| Mul
	| Div 
	| Mod ->
	    (* Numbers must all be the same type, one way or another *)
	    checkNums args;
	    ignore (List.fold_left (checkstuff) (List.hd args) args);
	    analyzeStmt (List.hd args)
	| Eq
	| Neq
	| Gt
	| Gte
	| Lt
	| Lte ->
	    checkNums args;
	    ignore (List.fold_left (checkstuff) (List.hd args) args);
	    analyzeStmt (List.hd args)
	| And
	| Or
	| Not
	| Xor ->
	    checkBools args;
	    ignore (List.fold_left (checkstuff) (List.hd args) args);
	    analyzeStmt (List.hd args)
	| Band
	| Bor
	| Bnot
	| Bxor
	    (* Shift operations only ever have two args *)
	| Shl
	| Shr ->
	    (* This may or may not be wrong. *)
	    checkNums args;  
	    ignore (List.fold_left (checkstuff) (List.hd args) args);
	    analyzeStmt (List.hd args)

  (* Gmph, I need some generic int type... *)
  and analyzeConst const =
    match const with
	(* XXX: Fix this to return the right size!  
	   We do this by working out all the int sizes, choosing
	   the smallest one that fits, and that's what we return.
	   Unsigned int's... don't quite work right now. *)
	Intconst( a ) -> Int
      | Floatconst( _ ) -> Float
	  (* XXX: Make sure all array items are right!  We don't. *)
      | Arrayconst( a ) -> 
	  (*
	    let arrayitems = List.map analyzeStmt a in
	    let t = List.fold_left (Symtbl.hasCompatibleType pkg) 
	    (List.hd arrayitems) arrayitems in
	    Arraytype( (List.length arrayitems), t )
	  *)
	  Arraytype( (List.length a),
		     (analyzeStmt (List.hd a)) )
      | Charconst( _ ) -> Char
      | Stringconst( _ ) -> Str
      | Boolconst( _ ) -> Bool
	  (*
	    | Structconst( a ) -> Structtype( [] ) (* XXX *)
	  *)
	  (* NIL, a null pointer, can be assigned to any pointer 
	     type *)
      | Nilconst -> Nulltype
  in
    (* Now we just call analyzeDecl on all the decl's.  Neat, huh?  
       ^_^ *)
    List.iter (fun x -> ignore (analyzeDecl x)) syntree
;;


(* Okay.  Driver function. 
   First we go through and populate the symbol tables with
   type, variable and function names.
   Then we go through and analyze the functions.
   It's very very simple, actually.  Thank gods something is.
*)
let doSemanticStuff syntree =
  (* We need variables to hang on to things *)
  let stbl = Symtbl.makePackage () in
    populate syntree stbl;
    analyze syntree stbl;
    Printf.printf "Printing package:\n";
    Symtbl.printPackage stbl;
    stbl
;;


