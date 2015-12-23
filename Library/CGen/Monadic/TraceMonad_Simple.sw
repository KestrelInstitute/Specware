(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


(* A simple version of TranceMonad.sw, with no concurrency or allocation *)

TraceMonad_Simple qualifying spec


(***
 *** The C types in our subset of C
 ***)

(* The types *)
type CType =
   | CType_Void
   | CType_Bool
   | CType_Int32
   | CType_Ptr (CType * Bool) % The flag says whether the pointer is atomic


(***
 *** The C values in our subset of C
 ***)

(* Typed pointers *)
type CPtr
op CPtr_type : CPtr -> CType
op CPtr_atomic? : CPtr -> Bool

(* The C values; intuitively these are things that can go in a register *)
type CValue =
   | CValue_Void
   | CValue_Bool Bool
   | CValue_Int32 Int (* FIXME: change to 32-bit integers *)
   | CValue_Null
   | CValue_Ptr CPtr


(***
 *** Type-checking a value against a type
 ***)

(* Returns true iff val has type typ *)
op CHasType (typ : CType) (val : CValue) : Bool =
  case (val, typ) of
    | (CValue_Void, CType_Void) -> true
    | (CValue_Bool _, CType_Bool) -> true
    | (CValue_Int32 _, CType_Int32) -> true
    | (CValue_Null, CType_Ptr _) -> true
    | (CValue_Ptr ptr, CType_Ptr (ptype, atomic?)) ->
      CPtr_type ptr = ptype && CPtr_atomic? ptr = atomic?
    | _ -> false

(* FIXME: projection functions on typed values *)


(***
 *** The side-effects, or "actions", that can be performed by a C program
 ***)

(* The simple actions are just pointer reads and writes *)
type CAction =
   | CAction_Read (CPtr * CValue) % non-atomic read
   | CAction_Write (CPtr * CValue) % non-atomic write

type CPtrAndValue = { p : CPtr * CValue | CHasType (CPtr_type p.1) p.2 }

op validActions_helper (acts : List CAction) (vals : List CPtrAndValue) : Bool =
  case acts of
    | [] -> true
    | act :: acts' ->
      (case act of
         | CAction_Read (ptr, v) ->
           CHasType (CPtr_type ptr) v &&
           findLeftmost (fn (ptr', _) -> ptr' = ptr) vals = Some (ptr, v) &&
           validActions_helper acts' vals
         | CAction_Write (ptr, v) ->
           CHasType (CPtr_type ptr) v &&
           validActions_helper acts' ((ptr, v)::vals))

(* A trace is valid iff each read sees the most recent previous write *)
op validActions (acts : List CAction) : Bool =
  validActions_helper acts []


(***
 *** Monadic semantics of C as sets of traces, i.e., action sequences
 ***)

(* C program errors *)
type CError =
   | NullPointerError

(* A C computation result *)
type CPgmResult a =
   | CRes_OK (List CAction * a) % Success, returning result + unconsumed actions
   | CRes_Error CError % Error result
   | CRes_BadActions % Sequence of actions did not fit this computation
   | CRes_NonTerm % Computation still needs more actions

(* A C computation consumes some actions and returns a result *)
type CMonad a = List CAction -> CPgmResult a

(* Return always returns a success result *)
op [a] return (x : a) : CMonad a = fn acts -> CRes_OK (acts, x)

(* Bind propagates suceesses and raises any failures *)
op [a,b] monadBind (m : CMonad a, f : a -> CMonad b) : CMonad b =
  fn acts ->
    case m acts of
      | CRes_OK (acts', a) -> f a acts'
      | CRes_Error err -> CRes_Error err
      | CRes_BadActions -> CRes_BadActions
      | CRes_NonTerm -> CRes_NonTerm

(* Pointer reads consume a read action for the pointer in question *)
op readCPtr (ptr : CPtr) : CMonad (CValue | CHasType (CPtr_type ptr)) =
  fn acts ->
    case acts of
      | [] -> CRes_NonTerm
      | (CAction_Read (ptr', v)) :: acts' ->
        if ptr' = ptr && CHasType (CPtr_type ptr) v then CRes_OK (acts', v)
        else CRes_BadActions
      | _ -> CRes_BadActions

(* Pointer writes consume a write action for the pointer in question *)
op writeCPtr (ptr : CPtr) (v : CValue | CHasType (CPtr_type ptr) v) : CMonad () =
  fn acts ->
    case acts of
      | [] -> CRes_NonTerm
      | (CAction_Write (ptr', v')) :: acts' ->
        if ptr' = ptr && v = v' then CRes_OK (acts', ())
        else CRes_BadActions
      | _ -> CRes_BadActions

end-spec
