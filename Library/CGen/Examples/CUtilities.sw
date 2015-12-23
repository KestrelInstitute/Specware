(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* This file introduces notions related to the C model in spec CModel.
These notions do not contribute to the C formalization
(i.e. they do not formalize C features not already formalized in spec CModel)
but are useful to specify requirements on C programs
and to derive C programs from requirement specifications via refinement. *)

spec

import CModel

(* Writing a value via an object designator succeeds
if the object designates an object of the same type as the value. *)

theorem writeDesignatedObject is
  fa (state:State, obj:ObjectDesignator, val:Value)
    (ex (val0:Value)
      readObject state obj = Some val0 &&
      typeOfValue val0 = typeOfValue val) =>
    writeObject state obj val ~= None

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

(* Monadic version of writePointed. *)

op writePointedM (pval:PointerValue) (val:Value): Monad () =
  fn state:State ->
    case writePointed state pval val of
    | Some state' -> Some (state', ())
    | None -> None

(* When the pointer points to an object,
writePointedM can be reduced to writePointed as follows. *)

theorem writePointedM_writePointed is
  fa (state:State, pval:PointerValue, val:Value)
    pointsToObject? state pval &&
    typeOfValue pval = pointer (typeOfValue val) =>
    writePointedM pval val state =
      Some (unwrap (writePointed state pval val), ())

(* Lift value to expression. *)

op valueExpr (val:Value): Expression =
  fn state:State -> Some (value val)

theorem convertLA_valueExpr is
  fa (val:Value)
    convertLA (valueExpr val) = valueExpr val

theorem convertA_valueExpr is
  fa (val:Value)
    convertA (valueExpr val) = valueExpr val

(* Lift writePointedM to expressions. *)

op writePointedE (pe:Expression) (e:Expression): Monad () =
  fn state:State ->
    case (convertLA pe state, convertLA e state) of
    | (Some (value pval), Some (value val)) ->
      if pointerValue? pval
      then writePointedM pval val state
      else None
    | _ -> None

(* Specialization of writePointedE to value expressions. *)

theorem writePointedE_valueExpr is
  fa (pval:PointerValue, val:Value)
    writePointedE (valueExpr pval) (valueExpr val) = writePointedM pval val

endspec
