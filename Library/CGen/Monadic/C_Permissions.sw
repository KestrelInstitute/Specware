(* This spec defines an approach to proving functional correctness properties of
monadic C computations by relating these computations to  *)

C_Permissions qualifying spec
  import C_Predicates


  (***
   *** Functional values
   ***)

  (* To represent C values in logic, we define a universal type for "functional
     values", i.e., values in MetaSlang proper that represent C values. This
     type can be refined to an actual type using finalizeInductiveType *)
  type FValue

  (* FValue includes lists (FIXME: add other ops for FValue_list) *)
  op FValue_list : List FValue -> FValue


  (***
   *** Value Representations
   ***)

  (* FIXME: document all of this! *)

  type StorageFValues = Map (ObjectDesignator, FValue)

  type ValueReprH =
    {repr_type_name : TypeName,
     repr_rel : SplittingWord -> StorageFValues -> Value -> FValue -> Bool,
     repr_combines_to : FValue * FValue -> FValue -> Bool}

  type ValueRepr =
    ValueReprH * (Storage -> Value -> Map (ObjectDesignator, ValueReprH))

  (* Well-formedness of a ValueReprH w.r.t. a predicate on the R type *)
  op valueReprH_well_formed (r_pred : R -> Bool) (reprh : ValueReprH) : Bool =
    (* The any Value related by the relation has the correct type *)
    (fa (w,s,v,fv,r)
       r_pred r && reprh.repr_rel w s v fv =>
       expandTypeName (r.r_xenv, reprh.repr_type_name) = Some (typeOfValue v))
    &&
    (* The combine function commutes with the relation; note that the
    implication only goes one way, because, e.g., fv1 and fv2 might combine to
    fv at some other word that is not w *)
    (fa (w,s,v,fv1,fv2,fv)
       reprh.repr_rel (SplitL::w) s v fv1 &&
       reprh.repr_rel (SplitR::w) s v fv2 &&
       reprh.repr_combines_to (fv1,fv2) fv =>
       reprh.repr_rel w s v fv
       )
    &&
    (* There is always a way to split an FValue relative to the relation; this
    is somewhat like a converse to the last condition *)
    (fa (w,s,v,fv)
       reprh.repr_rel w s v fv =>
       (ex (fv1,fv2)
          reprh.repr_rel (SplitL::w) s v fv1 &&
          reprh.repr_rel (SplitR::w) s v fv2 &&
          reprh.repr_combines_to (fv1,fv2) fv
          ))

  (* Well-formedness of a ValueRepr; requires the top-level ValueReprH and all
  the dependent ValueReprHs to be well-formed *)
  op valueRepr_well_formed (r_pred : R -> Bool) (repr : ValueRepr) : Bool =
    valueReprH_well_formed r_pred repr.1 &&
    (fa (s,v,d,reprh)
       repr.2 s v d = Some reprh => valueReprH_well_formed r_pred reprh)


  (***
   *** Storage representations
   ***)

  (* A representation of a Storage gives an FValue for each object permission,
     as well as a flag indicating whether the Storage (if true) or the process /
     current frame (if false) holds that permission *)
  type StorageRepr = Map (ObjectPerm, FValue * Bool)

  (* Convert a StorageRepr to a "slice", for a particular splitting word, of
     FValues for each permission on each object in the Storage. *)
  op storage_repr_values (w : SplittingWord) (r : StorageRepr) : StorageFValues =
    fn d -> case r (ObjectPerm (d,w)) of
              | Some (fv, _) -> Some fv
              | None -> None

  (* Convert a StorageRepr to a "slice", for a particular splitting word, of
     FValues for each permission held by the Storage on each object. *)
  op storage_repr_values_heap (w : SplittingWord) (srepr : StorageRepr) : StorageFValues =
    fn d -> case srepr (ObjectPerm (d,w)) of
              | Some (fv, true) -> Some fv
              | _ -> None

  (* FIXME: document this! *)
  op storage_repr_as_h? (heap : PermSet, my_held : PermSet, other_held : PermSet)
                        (s : Storage, srepr : StorageRepr) : Bool =
    perm_sets_compatible? (my_held, other_held) &&
    perm_sets_compatible? (heap, combine_perm_sets (my_held, other_held)) &&
    (let held = combine_perm_sets (my_held, other_held) in
     let perms = combine_perm_sets (heap, held) in
     (fa (d,w)
        let p = ObjectPerm (d,w) in
        case (perm_set_lookup (p, perms), srepr p) of
          | (None, None) -> true
          | (None, Some _) -> false
          | (Some _, None) -> false
          | (Some repr, Some (fv, flag)) ->
            (if flag then perm_set_lookup (p, heap) = Some repr
             else perm_set_lookup (p, heap) = None) &&
            (ex (v)
               (* There is a value v at object designator d *)
               objectHasValue s d v &&
               (* v and fv satisfy the predicate *)
               repr.1.repr_rel w (storage_repr_values_heap w srepr) v fv &&
               (* The two values below fv combine to fv *)
               (case (srepr (ObjectPerm (d,SplitL :: w)),
                      srepr (ObjectPerm (d,SplitR :: w))) of
                  | (Some (fv_l, _), Some (fv_r, _)) ->
                    repr.1.repr_combines_to (fv_l, fv_r) fv
                  | _ -> false) &&
               (* The perm set uses the required relations repr depends on *)
               (fa (d',reprh)
                  repr.2 s v d' = Some reprh =>
                  (ex (deps')
                     perm_set_lookup (ObjectPerm (d', w), perms)
                     = Some (reprh, deps')))
               )
            ))

  (***
   *** Permission Set Terms
   ***)

  (* FIXME HERE: write this stuff! *)

  type SplittingTerm = | AllPerms | PermVar Nat
  type ObjTerm = | VarObj Identifier | ValueObj Nat
  type PermSetTerm = SplittingTerm * ObjTerm

  op permSetTerm_well_formed (r_pred : R -> Bool) (t : PermSetTerm) : Bool

  op evalPermSetTerm (r : R, ws : List SplittingWord) (t : PermSetTerm) : PermSet

  op valsForPermSetTerm (r : R, ws : List SplittingWord)
                        (srepr : StorageRepr, t : PermSetTerm) : List FValue

  op storage_repr_as? (r : R, ws : List SplittingWord)
                      (heap : PermSetTerm, my_held : PermSetTerm,
                       other_held : PermSetTerm)
                      (s : Storage, srepr : StorageRepr) : Bool


  (***
   *** Correctness w.r.t. Permissions
   ***)

  op stmt_correct (r_pred : R -> Bool)
                  (perms_in : PermSetTerm, perms_out : PermSetTerm)
                  (f : List FValue -> List FValue) (m : Monad ()) () : Bool =
    fa (other_held,heap_in,srepr_in,ws)
      ex (heap_out,srepr_out)
        totally_correct
        (fn r -> fn s_in ->
           (* The r_predicate holds *)
           r_pred r &&
           (* srepr_in is a valid representation of s_in *)
           storage_repr_as? (r,ws) (heap_in, perms_in, other_held) (s_in, srepr_in)
           )
        m
        (fn r -> fn s_in -> fn s_out ->
           (* The pre-conditions still hold on the input state *)
           r_pred r &&
           storage_repr_as? (r,ws) (heap_in, perms_in, other_held) (s_in, srepr_in) &&
           (* srepr_out is a valid representation of s_out *)
           storage_repr_as? (r,ws) (heap_out, perms_out, other_held) (s_out, srepr_out) &&
           (* The function f relates my input and output representations *)
           valsForPermSetTerm (r, ws) (srepr_out, perms_out)
           = valsForPermSetTerm (r, ws) (srepr_in, perms_in) &&
           (* The other representations do not change on output *)
           valsForPermSetTerm (r, ws) (srepr_in, other_held)
           = valsForPermSetTerm (r, ws) (srepr_out, other_held)
           )

end-spec
