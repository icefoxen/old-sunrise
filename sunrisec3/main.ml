(* main.ml
   Main driver and UI junk.
   Not quite sure how the overall toolchain is going to be structured yet.
   As in, compiler, linker, assembler, package manager, library manager...

   Simon Heath
   Whenever
*)

let compileFile fn =
  ErrorReport.reset fn;
  try
    let lexbuf = Lexing.from_channel (open_in fn) in
    let parsetree = Parse.main Lex.token lexbuf in
      Printf.printf "# of statements parsed: %d\n" (List.length parsetree);
      (*Syntree.printParseTree parsetree; *)
      print_endline "Parsing succeeded!  Have a cookie!";
      ignore (Semant.doSemanticStuff parsetree);
      print_endline "Semantic junk succeceded!  Have another cookie!";


  with
      Sys_error a -> (Printf.eprintf "File does not exist: %s\n" a; 
		    exit 1)
    | Parsing.Parse_error -> 
	ErrorReport.error "Fatal parse error: Bad programmer, no cookie for you!"
;;

let usage () = 
  print_endline "Usage: sunrisec filename.sr"
;;


let _ =
  
  let fn = Sys.argv.(1) in
    compileFile fn
  
;;

