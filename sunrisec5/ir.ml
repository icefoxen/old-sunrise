(* ir.ml
   Intermediate representation.
   Kinda a lower-level version of the syntax tree.

   Two-arg math ops in correct order, loops and if's reduced to simplest
   forms (goto's?), typeless, exact var sizes, explicit pointer refs,
   explicit pointer arithmatic...  generally, one step up from asm.

   Which is, of course, the very point.

   Tree form, I guess.  Optimization...  loop hoisting and unrolling,
   constant folding, tail-call optimization, maybe a bit of other stuff.
   Optimizer passes over the tree, building the new one as it goes.

   We should also insert bounds-checking code for arrays, then do our
   best to optimize it out.  Assignments from a :^:#:foo to an :#n:foo
   need size-checking also.

   ...we have an issue.  It's called the lack of persistance in the
   symbol table...
   Well, everything's verified, so I guess we can just pull the vars
   and such directly...

   Simon Heath
   14/9/2005
*)

open Syntree

type binop =
    AddOp of stm * stm 
  | SubOp of stm * stm 
  | MulOp of stm * stm 
  | DivOp of stm * stm 
  | ModOp of stm * stm 
  | EqOp of stm * stm 
  | NeqOp of stm * stm 
  | GtOp of stm * stm 
  | LtOp of stm * stm 
  | GteOp of stm * stm 
  | LteOp of stm * stm 
  | AndOp of stm * stm 
  | OrOp of stm * stm 
  | NotOp of stm * stm 
  | XorOp of stm * stm 
  | BandOp of stm * stm
  | BorOp of stm * stm 
  | BnotOp of stm * stm 
  | BxorOp of stm * stm 
  | ShlOp of stm * stm 
  | ShrOp of stm * stm 

and vl = 
    (*
      Reg of int
      RegPtr of int * int (* reg + offset *)
      Mem of int
      Const of int
    *)

    (* Ditch reg and mem for these?  number/address * size * pointer offset
    *)
    ArgLoc of int * int * int
  | LocalLoc of int * int * int
  | TempLoc of int * int * int
  | GlobalLoc of int * int * int
  | ConstLoc of int * int * int

and stm =
    BinopStm of binop
  | AsmStm of string
  | AllocStm of int
      (* From, to *)
  | CastStm of typstm * typstm
  | Funcall of string * stm list
  | AddrStm of stm   (* &stm *)
  | DerefStm of stm  (* *stm *)
  | NullStm
  | IfStm of stm * stm list * stm list
  | LoopStm of stm * stm list
  | ReturnStm of stm

and typstm =
    Int of int
  | Float of int
;;

type package = {
  name : string;
  funcs : ...;
  globals : ...;
  consts : ...;
  
};;
