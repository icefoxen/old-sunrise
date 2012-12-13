(* errorReport.ml
   General error reporting.  This module keeps track of where we are in
   the file, amoung other things.

   Simon Heath
   13/1/2004
*)


let lineNum = ref 1;;
let chrNum = ref 1;;
let fileName = ref "";;


(* Increments line count *)
let nl () =
   lineNum := !lineNum + 1;
   chrNum := 0;;

(* Prints an error message *)
let error str =
   Printf.eprintf "Fatal error in %s: " !fileName;
   Printf.eprintf "%d.%d: %s\n" !lineNum !chrNum str;;

let errorAndDie msg =
   error msg;
   exit 1;;

(* Resets the error-checker *)
let reset fname =
   fileName := fname;
   lineNum := 1;
   chrNum := 0;;
