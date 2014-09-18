(* This file introduces notions related to the C model in spec CModel.
These notions do not contribute to the C formalization
(i.e. they do not formalize C features not already formalized in spec CModel)
but are useful to specify requirements on C programs
and to derive C programs from requirement specifications via refinement. *)

spec

import CModel

(* Read value from object pointed to by pointer value. *)

op readPointed (state:State) (pval:PointerValue): Option Value =
  case pval of
  | nnpointer (ty, object obj) ->
    (case readObject state obj of
    | Some val -> if typeOfValue val = ty then Some val else None
    | None -> None)
  | _ -> None

(* Check if pointer value points to object. *)

op pointsToObject? (state:State) (pval:PointerValue): Bool =
  readPointed state pval ~= None

(* Write value to object pointed to by pointer value. *)

op writePointed (state:State) (pval:PointerValue) (val:Value): Option State =
  case pval of
  | nnpointer (ty, object obj) ->
    if ty = typeOfValue val then writeObject state obj val else None
  | _ -> None

(* Writing a value of the right type via a pointer value succeeds
if the pointer points to an object. *)

theorem writePointedObject is
  fa (state:State, pval:PointerValue, val:Value)
    pointsToObject? state pval &&
    typeOfValue pval = pointer (typeOfValue val) =>
    writePointed state pval val ~= None

endspec
