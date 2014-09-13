(* This file introduces notions related to the C model in spec CModel.
These notions do not contribute to the C formalization
(i.e. they do not formalize C features not already formalized in spec CModel)
but are useful to specify requirements on C programs
and to derive C programs from requirement specifications via refinement. *)

spec

import CModel

(* Lift writeObject to (non-null) pointers. *)

op writePointer (state:State) (ptr:NNPointer) (newVal:Value): Option State =
  case ptr of
  | object obj -> writeObject state obj newVal
  | past1 _ -> None

theorem writePointerObject is
  fa (state:State, obj:ObjectDesignator, newVal:Value)
    writePointer state (object obj) newVal = writeObject state obj newVal

(* Lift writePointer to pointer values. *)

op writePointerValue
   (state:State) (pval:PointerValue) (newVal:Value): Option State =
  case pval of
  | nnpointer (_, ptr) -> writePointer state ptr newVal
  | nullpointer _ -> None

theorem writePointerValueNonNull is
  fa (state:State, ty:Type, ptr:NNPointer, newVal:Value)
    writePointerValue state (nnpointer (ty, ptr)) newVal =
      writePointer state ptr newVal

endspec
