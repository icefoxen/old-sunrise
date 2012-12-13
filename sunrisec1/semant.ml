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


(* Grabs the names of all the types, globals, consts, and functions, and
   puts them into the symbol table.  We do this so we don't need forward
   reference.

   XXX: Directness analysis (whether or notot something is a reference)
   is a bit weird...
   Basically, if something is a var-length array, a structure, or a function
   pointer, it's indirect (the vartype.vardirect field is false).
   Constants are always direct.  Globals, I'm not sure about....
   Otherwise, it's direct.
   There are a couple special cases with that for structure and local 
   variables...  (@ fields in structs, and "local" vs "let" variables).
   I believe it works though.  Gotta test it to know for sure.
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
	     (Conststm( Nilconst )) Symtbl.Global true true)
    | Globaldecl( Vardecl( name, typestm, defval ) ) -> 
	Symtbl.addVar pkg name (Symtbl.makeVar pkg typestm defval 
				  Symtbl.Global true false)
    | Constdecl( Vardecl( name, typestm, defval ) ) ->
	Symtbl.addVar pkg name (Symtbl.makeVar pkg typestm defval 
				  Symtbl.Global true true)
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
   XXX: Make sure local values aren't returned.  What about let'd const-length
   arrays?
   GRRRRRR.  Let/Local is a kludge!  How do I fix it?  Can't, without
   re-writing the language relatively significantly.
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
       explicit would make it complicated.
    *)
    if rettype <> Voidtype then 
      (* Make sure there's an actual function body *)
      if List.length body < 1 then
	errorAndDie (Printf.sprintf "Type %s returns %s but has no body!"
		       name (typestmt2str rettype))
	  (* Check the type of the last statement *)
      else 
	let lasttype = analyzeStmt (List.hd (List.rev body)) in
	  if Symtbl.hasCompatibleType pkg rettype lasttype then (  
	    (* Push a new scope, add the arguments (no analysis, 'cause no
	       default values...), analyze the function body, then pop 
	       the scope and return the function sig. *)
	    Symtbl.pushScope pkg;
	    List.iter (fun x -> Symtbl.addVarDecl pkg x) args;
	    (*	    List.iter (fun x -> analyzeVar (* nm defval *)) args; *)
	    List.iter (fun x -> ignore (analyzeStmt x)) body;
	    Symtbl.popScope pkg;
	    fundecl2typestm (Fundecl( name, rettype, args, body ))
	  ) 
	  else (
	    errorAndDie (Printf.sprintf 
			   "Function %s declared to return %s but returns %s!"
			   name (typestmt2str rettype) 
			   (typestmt2str lasttype))
	  ) 
    else (* Return type equals void *)
      Voidtype 
	
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
      | Structtype( itms ) -> Structtype( itms )
      | Customtype( name ) ->
	  if Symtbl.typeExists pkg name then
	    analyzeType (Symtbl.getType pkg name)
	  else
	    errorAndDie ("Type :" ^ name ^ " does not exist!")
      | Voidtype -> 
	  errorAndDie "You defined a type as void!  Don't do it."
	    (* atomic types *)
      | other -> other

  (* Makes sure all the types in a structure are valid, no recursive @-fields,
     etc *)
  and analyzeStruct name fields =
    List.iter (analyzeStructItem name) fields;
    Structtype( fields )

  (* When this gets called, the type table should already be populated
     with struct names, so recursive structs are possible.  We just need to
     make sure the recursive field isn't an @-field.
  *)
  and analyzeStructItem structname itm =
    match itm with
	Structitem( name, typ, defval, isinline ) ->
	  (* We find out the type of defval and if it matches with typ,
	     then check to see if it's a recursive @ field, and that's it. *)
	  let deftype = analyzeStmt defval in
	    (* Make sure the default value is valid *)
	    if Symtbl.hasCompatibleType pkg (analyzeType typ) deftype then
	      (* Make sure we don't have a recursive @-type *)
	      match typ with
		  Customtype( nm ) ->
		    if isinline && (nm = structname) then
		      errorAndDie 
			("Struct " ^ structname ^ 
			 " declares a recursive @-field!")
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
     XXX: What does a left-out else statement return?  A var decl?  An 
     assignment?  A while loop?  Voidtype, I suppose.
     How do we know struct fields? *)
  and analyzeStmt stm =
    match stm with 
	Opexpr( op, stmlst ) -> analyzeOpexpr op stmlst
      | Funcall( fnexpr, args ) -> (* args is a list of statements *)
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
      | Dostm( stms ) ->
	  analyzeStmt (List.hd (List.rev stms))
      | Asmstm( str ) -> Voidtype
      | Localstm( vdcls ) -> Voidtype
      | Letstm( vdcls ) -> Voidtype
      | Nullstm -> Voidtype
      | Conststm( const ) -> analyzeConst const
      | Funstm( nm, rettype, vars, body ) -> Voidtype
      | Varstm( str ) -> Symtbl.getVarType pkg str
	  (* Okay, 2nd stm is a number or array, 1st is an array *)
      | Aref( stm, stm2 ) -> Voidtype 
	  (* Okay, str is an item name, 1st is an expr that returns a struct *)
      | Sref( stm, str ) -> Voidtype
      | Ptrref( stm ) -> 
	  let stmtype = analyzeStmt stm in
	    (match stmtype with
		Ptrtype( typestm ) -> typestm
	      | other -> errorAndDie 
		  ("Tried to refer to a pointer but expression is type " ^
		   typestmt2str stmtype))
      | Assignstm( lval, stm ) -> 
	  let lvaltype = analyzeStmt lval 
	  and stmtype = analyzeStmt stm in
	    if Symtbl.hasCompatibleType pkg lvaltype stmtype then
	      lvaltype
	    else
	      errorAndDie ("Assignment between incompatible types: (<- " ^
			  (typestmt2str lvaltype) ^ " " ^ 
			   (typestmt2str stmtype) ^ ")")

  (* Makes sure statements are valid. *)
  and analyzeOpexpr op args =
    Voidtype
  and analyzeConst const =
    Voidtype
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


