(* dumbcodegen.ml
   We try to do a naive translation of the symbol table and syntax tree
   into x86 assembly.

   ...arg.  We need a way to dereference pointers.  As in, specify a location
   in memory from a register.
   ...the locations are annoying.

   Simon Heath
   12/9/2005
*)

(*
type addr = ADDR of int;;
type reg = REG of int;;

type loc = 
    addr
  | reg
;;
*)

type loc = 
    ADDR of int
  | REG of int
;;

(* This... KINDA works... *)
type location =
    LOC of loc
  | PTRREF of loc * int
;;

type opcodes =

  (* Load/store *)
    LOAD
  | STORE

  (* Arithmatic *)
  | ADD
  | SUB
  | MUL
  | DIV
  | MOD
  | INC
  | DEC

  (* Logic *)
  | SHL
  | SHR
  | AND
  | OR
  | NOT
  | XOR
  | COMP
  | NEG

  (* Branch *)
  | JMP
  | JL
  | JG
  | JLE
  | JGE
  | JE
  | JNE
  | CMP
  | LABEL of string

  (* Floating point *)
  | FLOAD
  | FSTORE
  | FADD
  | FSUB
  | FMUL
  | FDIV
;;


let importedSyms = ref [];;
let exportedSyms = ref [];;

let instrQ = Queue.create ();;

let globals = ref [];;
let consts = ref [];;

let outputInstr x = Queue.add x instrQ;;

let gensymidx = ref 0;;
let gensym () =
  incr gensymidx;
  Printf.sprintf "SYM%d" !gensymidx;
;;
