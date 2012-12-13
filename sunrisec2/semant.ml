(* semant.ml
   Semantic checking for Sunrise.
   Basically works thus:
   Initialize; add all the default types.
   Import packages, when they exist.
   Go through the syntax tree.  For each const/global, stick it in the
   global symbol table.  For each type, stick it in the type table.
   For each function, go through it.  Push a scope for each function and
   "do" block.  For each expression, figure out the types of it's arguments,
   and if they match correctly return the expression's type.
   This is easy for now, since types MUST match up perfectly.
   Signal an error if they don't.  Signal an error if a variable or type
   name doesn't exist.
   Pop a stack each time you leave a do block or function.

   TODO:
   Allow implicit coercion of narrow types to wider types.
   Do parametric polymorphism.
   Allow explicit coercion of wider types to narrower types.
   Allow explicit coercion of non-pointers to pointers and signed/unsigned.

   Basically, do two passes: One to note all the function names and types,
   and another to actually go into the functions and structs and so on and
   do real type-checking.

   Okay.  We go through all the types, grab the names, then work 'em out.
   Then we go through all the globals and consts, work them out.
   Then we go through all the functions, grab the names, then work them out.
   Whew, that's sorta messy.  I can see why compiler-writers like forward 
   references...
   
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

   XXX: Check for lengths of fixed-length arrays!
   XXX: Initialize fixed-length arrays where a single value is given!
   analyzeVar may need another argument to give it more context on directness,
   constantness, and so on...  The population of the symtable should handle
   some of that already though.  Don't do work twice.
   XXX: Make sure pointers to local values aren't returned, or local 
   values aren't assigned to non-local pointers.
*)

let analyze syntree pkg = 
  let rec analyzeDecl = function
      Fundecl( name, rettype, args, body ) -> 
	if Symtbl.varExists pkg name then
	  analyzeFunc name rettype args body
	else
	  raise (SemanticException "This should never happen!")
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
       explicit would make it (somewhat) complicated.
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
      (* List.iter (fun x -> analyzeVar nm defval) args; *)
      List.iter (fun x -> ignore (analyzeStmt x)) body;
      (* THEN we check the type of the last statement 
	 Trying to analyze the last statement before we've analyzed things
	 like var decleration is a bad bad idea.  As I learned the hard
	 way.  *)
      let lasttype = analyzeStmt (List.hd (List.rev body)) in
	(* Void type, we don't bother checking return type *)
	if rettype = Voidtype then (
	  Symtbl.popScope pkg;
	  fundecl2typestm (Fundecl( name, rettype, args, body ))
	    (* We check for compatible return type and do exact same thing *)
	) else if Symtbl.hasCompatibleType pkg rettype lasttype then (
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
	  (* Should never happen, since we write all struct types by name *)
      | Structtype( itms ) -> 
	  (error "Semant.analyzeType: Structtype!  Weird!"); 
	  Structtype( itms )
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
     make sure the recursive field isn't a direct field.
  *)
  and analyzeStructItem structname itm =
    match itm with
	Structitem( name, typ, defval ) ->
	  (* We find out the type of defval and if it matches with typ,
	     then check to see if it's a recursive @ field, and that's it. *)
	  let deftype = analyzeStmt defval in
	    (* Make sure the default value is valid *)
	    if Symtbl.hasCompatibleType pkg (analyzeType typ) deftype then
	      (* Make sure we don't have a recursive field 
		 XXX: This could be a problem with:
		 (type foo bar)
		 (struct bar (a :foo))
		 How do I solve this?  I have to drill down through 
		 Customtypes...
	      *)
	      match typ with
		  Customtype( nm ) ->
		    if (nm = structname) then
		      errorAndDie 
			("Struct " ^ structname ^ 
			 " declares a recursive field!")
		    else
		      ()  (* Everything is fine! *)
		| _ -> () (* It's not a struct, we're not interested. *)
	    else
	      errorAndDie ("In struct " ^ structname ^ ", field " ^ name ^
			   " has an invalid default value")
		

  (* Makes sure a variable decleration is valid, initializing value exists,
     etc.
     Takes a name and a value; the name should already be in the symbol table,
     so.
  *)
  and analyzeVar name defval =
    let deftype = analyzeStmt defval in
      if Symtbl.varHasCompatibleType pkg name deftype then
	Symtbl.getVarType pkg name
      else
	errorAndDie ("Variable " ^ name ^ "'s default value is of the wrong type!")

  (* Makes sure a statement is valid.  Nullstm's are ignored.
     An assignment returns the value assigned.  A vardecl, while loop,
     left-out else statement, etc, return Voidtype. *)
  and analyzeStmt stm =
    match stm with 
	Opexpr( op, stmlst ) -> analyzeOpexpr op stmlst
      | Funcall( fnexpr, args ) -> (* args is a list of statements *)
	  (match fnexpr with
	       Varstm( x ) -> Printf.printf "Analyzing function: %s\n" x;
	     | _ -> ());
	  let fn = analyzeStmt fnexpr in
	    (match fn with
		 Functype( rettype, rgs ) -> (* rgs is a Compoundtype *)
		   let argtypes = List.map (fun x -> analyzeStmt x) args in
		   let argtypes = typestmlst2typestm argtypes in
		     if Symtbl.hasCompatibleType pkg argtypes rgs then
		       rettype
		     else
		       errorAndDie ("Function has type " ^
				    (typestmt2str rgs) ^ " but is given " ^
				    (typestmt2str argtypes))
			 
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
	      analyzeStmt (List.hd (List.rev body))
	    else
	      errorAndDie ("If statement condition doesn't return bool!")

      (* Returns the value of the last statement, like scheme "begin" *)
      | Dostm( stms ) ->
	  Symtbl.pushScope pkg;
	  let a = analyzeStmt (List.hd (List.rev stms)) in
	    Symtbl.popScope pkg;
	    a
	      

      | Asmstm( str ) -> Voidtype
      | Letstm( vdecls ) -> 
	  let insertvardecl = function
	      Vardecl( name, typ, vl ) ->
		Printf.printf "Inserting var %s\n" name;
		let v = Symtbl.makeVar pkg typ vl Symtbl.Let false in
		  Symtbl.addVar pkg name v
	  in
	    List.iter insertvardecl vdecls;
	    Voidtype
      | Nullstm -> Voidtype
      | Conststm( const ) -> analyzeConst const
      | Funstm( nm, rettype, vars, body ) -> Voidtype
      | Varstm( str ) -> Symtbl.getVarType pkg str
	  (* Okay, 2nd stm is a number or array, 1st is an array *)
      | Aref( stm1, stm2 ) -> 
	  if Symtbl.hasCompatibleType pkg (analyzeStmt stm2) Uint then
	    analyzeStmt stm1
	  else
	    errorAndDie ("Array referenced with a non-uint index!")

      (* Okay, str is an item name, 1st is an expr that returns a
	 struct *)
      | Sref( stm, str ) -> 
	  let stype = analyzeStmt stm in
	  let mtype = structGetMemberType stype str in
	    mtype
      | Assignstm( lval, stm ) -> 
	  let lvaltype = analyzeStmt lval 
	  and stmtype = analyzeStmt stm in
	    if Symtbl.hasCompatibleType pkg lvaltype stmtype then
	      lvaltype
	    else
	      errorAndDie ("Assignment between incompatible types: (<- " ^
			   (typestmt2str lvaltype) ^ " " ^ 
			   (typestmt2str stmtype) ^ ")")

  (* Makes sure statements are valid. 
     Basically, all types have to be compatable with each other.  I don't
     /think/ there are any cases where A is compatible with B and C, but
     B and C are not compatible with each other.
     ...yes there is.  Nil pointers.
     Okay.  For math, all types must be numbers, and compatible with each 
     other.
     For comparison, all types must be compatible with each other.
     For logic, all types must be bool.
     For binary operations, all types must be numbers of the same size.
  *)
  and analyzeOpexpr op args =
    match op with
	Add
      | Sub
      | Mul
      | Div
	  (* Not quite sure this works the way it should 'cause of List.hd
	     Well, it does now.  It won't when we actually coerce types.
	     (Basically, it'll say fine when given an int16 and an int8; an
	     int8 fits in an int16.  But it won't work when given an int16 
	     then an int8, or something of that nature)
	  *)
      | Mod -> List.fold_left 
	  (fun x y -> Symtbl.coerceType pkg x (analyzeStmt y)) Int args
      | Eq
      | Neq
      | Gt
      | Gte
      | Lt
	  (* Same here XXX: Return type must be bool! *)
      | Lte -> List.fold_left 
	  (fun x y -> Symtbl.coerceType pkg x (analyzeStmt y)) Int args;
      | And
      | Or
      | Not
	  (* This time it works, 'cause it's just booleans *)
      | Xor -> List.fold_left 
	  (fun x y -> Symtbl.coerceType pkg x (analyzeStmt y)) Bool args
      | Band
      | Bor
      | Bnot
      | Bxor
	  (* Shift operations only ever have two args *)
      | Shl
      | Shr -> List.fold_left 
	  (fun x y -> Symtbl.coerceType pkg x (analyzeStmt y)) Int args

  (* Gmph, I need some generic int type... *)
  and analyzeConst const =
    match const with
	Intconst( _ ) -> Int (* Imperfect, but for now functional *)
      | Floatconst( _ ) -> Float
      | Arrayconst( a ) -> Voidtype
      | Charconst( _ ) -> Char
      | Stringconst( _ ) -> Str
      | Boolconst( _ ) -> Bool
	  (* NIL, a null pointer, can be assigned to any pointer type *)
      | Nilconst -> Nulltype
  in
    (* Now we just call analyzeDecl on all the decl's.  Neat, huh?  ^_^ *)
    List.iter (fun x -> ignore (analyzeDecl x)) syntree
;;


(* Okay.  Driver function. 
   First we go through and populate the symbol tables with
   type, variable and function names.
   Then we go through and analyze the functions.
*)

let doSemanticStuff syntree =
  (* We need variables to hang on to things *)
  let stbl = Symtbl.makePackage () in
    populate syntree stbl;
    analyze syntree stbl;
    Printf.printf "Printing package:\n";
    Symtbl.printPackage stbl;
;;


