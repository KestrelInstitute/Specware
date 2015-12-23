(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)


(* A trace-monad-based semantics of a typed subset of C *)

TraceMonad qualifying spec


(***
 *** The C types in our subset of C
 ***)

(* The types *)
type CType =
   | CType_Void
   | CType_Bool
   | CType_Int32
   | CType_Ptr (CType * Bool) % The flag says whether the pointer is atomic
   | CType_StructPtr CStructType
   | CType_ArrayPtr CType
   | CType_Lock

type CStructType = | CStructType (List (String * CType))

op CStructType_lookup (t : CStructType, f : String) : Option CType =
  case t of
    | CStructType ([]) -> None
    | CStructType ((f', t') :: fields) ->
      if f = f' then Some t' else CStructType_lookup (CStructType fields, f)


(***
 *** The C values in our subset of C
 ***)

(* Typed pointers *)
type CPtr
op CPtr_type : CPtr -> CType
op CPtr_atomic? : CPtr -> Bool

(* Struct pointers; CStructPtr_field (ptr, "f") takes the lvalue &(ptr->f) *)
(*
type CStructPtr
op CStructPtr_type : CStructPtr -> CStructType
op CStructPtr_field (struct : CStructPtr)
    (f : String | CStructType_lookup (CStructPtr_type struct, f) ~= None) :
  { ptr : CPtr | CStructType_lookup (CStructPtr_type struct, f) = Some (CPtr_type ptr)  }
*)

(* Array pointer: CArrayPtr_field(ptr,i) takes the lvalue &(ptr[i]) *)
(*
type CArrayPtr
op CArrayPtr_type : CArrayPtr -> CType
op CArrayPtr_field (arr : CArrayPtr) (i : Nat) :
  { ptr : CPtr | CPtr_type ptr = CArrayPtr_type arr }
*)


(* A struct is just a set of named pointers to its fields *)
type CStructPtr = List (String * CPtr)
op CStructPtr_type (sptr : CStructPtr) : CStructType =
  CStructType (map (fn (f, ptr) -> (f, CPtr_type ptr)) sptr)

(* An array is just a list of pointers to its elements *)
type CArrayPtr = { p : CType * List CPtr | forall? (fn ptr -> CPtr_type ptr = p.1) p.2 }
op CArrayPtr_type (arr : CArrayPtr) : CType = arr.1

(* A lock pointer; contains no visible structure *)
type CLock

(* The C values; intuitively these are things that can go in a register *)
type CValue =
   | CValue_Void
   | CValue_Bool Bool
   | CValue_Int32 Int (* FIXME: change to 32-bit integers *)
   | CValue_Null
   | CValue_Ptr CPtr
   | CValue_StructPtr CStructPtr
   % | CValue_StructPtr (List (String * CPtr))
   | CValue_ArrayPtr CArrayPtr
   | CValue_Lock CLock


(***
 *** Type-checking a value against a type
 ***)

(* Returns true iff val has type typ *)
op CHasType (val : CValue, typ : CType) : Bool =
  case (val, typ) of
    | (CValue_Void, CType_Void) -> true
    | (CValue_Bool _, CType_Bool) -> true
    | (CValue_Int32 _, CType_Int32) -> true
    | (CValue_Null, CType_Ptr _) -> true
    | (CValue_Null, CType_StructPtr _) -> true
    | (CValue_Null, CType_ArrayPtr _) -> true
    | (CValue_Ptr ptr, CType_Ptr (ptype, atomic?)) ->
      CPtr_type ptr = ptype && CPtr_atomic? ptr = atomic?
    | (CValue_StructPtr sptr, CType_StructPtr stype) ->
      CStructPtr_type sptr = stype
    | (CValue_ArrayPtr arr, CType_ArrayPtr atype) ->
      CArrayPtr_type arr = atype
    | (CValue_Lock _, CType_Lock) -> true
    | _ -> false


(***
 *** The side-effects, or "actions", that can be performed by a C program
 ***)

(* A thread id is either the "top-most" thread, represented as the
 * empty list, or the Nth child of thread tid, represented as tid++[N]
 *)
type ThreadId = List Nat
op topThreadId : ThreadId = []
op childThreadId (tid : ThreadId) (n : Nat) : ThreadId = tid++[n]

(* Memory orders give the ordering strength of atomic operations; See
 * Batty et al., "Mathematizing C++ Concurrency", POPL'11 for a
 * detailed explanation *)
type MemoryOrder =
   | MO_Seq_Cst % Sequential Consistency
   | MO_Acq_Rel % Acquire and Release
   | MO_Acquire % Just an acquire
   | MO_Release % Just a release
   | MO_Relaxed % No ordering constraints

(* The actions a C computation can perform; the memory access and
 * concurrency operations are those defined by Batty et al. *)
type CAction =
   (* Memory actions of Batty et al. *)
   | CAction_Read (ThreadId * CPtr * CValue) % non-atomic read
   | CAction_Write (ThreadId * CPtr * CValue) % non-atomic write
   | CAction_ARead (ThreadId * MemoryOrder * CPtr * CValue) % atomic read
   | CAction_AWrite (ThreadId * MemoryOrder * CPtr * CValue) % atomic write
   | CAction_AReadWrite (ThreadId * MemoryOrder * CPtr * CValue * CValue) % atomic read-modify-write
   | CAction_Lock (ThreadId * CLock) % lock operation
   | CAction_Unlock (ThreadId * CLock) % unlock operation
   | CAction_Fence (ThreadId * MemoryOrder) % memory fence

   (* Malloc and free *)
   | CAction_Malloc (ThreadId * List CPtr) % malloc a sequence of (contiguous) pointers
   | CAction_Free (ThreadId * List CPtr) % free a sequence of (contiguous) pointers

   (* Thread operations *)
   | CAction_Fork (ThreadId * Nat) % create the Nth child of the current thread
   | CAction_ThreadExit ThreadId % thread exit
   | CAction_Join (ThreadId * ThreadId) % thread id 1 waits for thread id 2 to complete


(***
 *** Monadic semantics of C as sets of traces, i.e., action sequences
 ***)

(* C program errors *)
type CError =
   | NullPointerError
   | DoubleFreeError

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



end-spec
