(* sizes.ml
   Type sizes for various architectures.

   Simon Heath
   12/4/2005
*)

open Syntree;;

(* The size of all unspecified-length types, in bytes 
   Bits might be better for word-addressed machines, but how many of those
   are still around?
   I don't know, actually.
*)
type archsize = {
   intsize : int;
   longsize : int;
   floatsize : int;
   doublesize : int;
   charsize : int;
   boolsize : int;
   pointersize : int;
};;

let intel_x86 = {
   intsize = 4;
   longsize = 8;
   floatsize = 4;
   doublesize = 8;
   charsize = 1;
   boolsize = 1;
   pointersize = 4;
};;

(* There might be a better way to do this, probably involving some sort of
   config file that knows all this stuff itself, but this works all right 
   for now *)
let localarch = intel_x86;;
(*
let getSize arch = function
   "int"	-> arch.intsize
 | "long"	-> arch.longsize
 | "byte"	-> arch.bytesize
 | "float"	-> arch.floatsize
 | "double"	-> arch.doublesize
 | "char"	-> arch.charsize
 | "bool"	-> arch.boolsize
 | "ptr"	-> arch.pointersize
 
;;
*)

