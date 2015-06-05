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
   *** Splitting Words
   ***)

  (* A splitting word is an abstract representation of a portion of an entity
  that can be "split" in two zero or more times. The entire entity (with no
  splitting) is represented by the empty list, and if w represents some portion
  of the entity then SplitL :: w and, respectively, SplitR:: w represent the
  "left half" and the "right half" of the result of splitting the w portion. *)
  type SplittingLetter = | SplitL | SplitR
  type SplittingWord = List SplittingLetter

  (* The natural partial order on splitting words orders w1 before w2 iff w1
  represents a sub-portion of what w2 represents. This can be decided by testing
  whether w2 is a suffix of w1 *)
  op splitting_word_leq : CPO.PartialOrder SplittingWord =
  (fn (w1, w2) ->
     w1 = w2 ||
     (case w1 of
        | [] -> false
        | _ :: w1' -> splitting_word_leq (w1', w2)))

  (* Two splitting words are compatible iff they represent non-overlapping
  portions; i.e., iff they are incomparable w.r.t. the above partial order *)
  op splitting_words_compatible (w1: SplittingWord, w2: SplittingWord) : Bool =
    ~(splitting_word_leq (w1, w2)) && ~(splitting_word_leq (w2, w1))

  (* Two splitting words are combinable iff their two portions can be combined
  into a whole; i.e., iff they are the left and right splits of the same w *)
  op splitting_words_combinable (w1: SplittingWord, w2: SplittingWord) : Bool =
    case (w1, w2) of
      | (SplitL :: w1', SplitR :: w2') -> w1' = w2'
      | (SplitR :: w1', SplitL :: w2') -> w1' = w2'
      | _ -> false

  (* Combine two combinable splitting words *)
  op combine_splitting_words (w1: SplittingWord, w2: SplittingWord |
                                splitting_words_combinable (w1,w2)) : SplittingWord =
    case (w1, w2) of
      | (SplitL :: w1', SplitR :: w2') -> w1'
      | (SplitR :: w1', SplitL :: w2') -> w1'
      | _ -> []


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
   *** Permissions
   ***)

  type ObjectPerm = | ObjectPerm ObjectDesignator * SplittingWord
  type Perm = ObjectPerm * ValueRepr

  (* The extension of splitting_word_leq to object permissions *)
  op object_perm_leq : CPO.PartialOrder ObjectPerm =
  (fn tup ->
     case tup of
       | (ObjectPerm (d1,w1), ObjectPerm (d2,w2)) ->
         d1 = d2 && splitting_word_leq (w1, w2))

  (* Whether two permissions are compatible *)
  op perms_compatible? (combinable?:Bool) (perm1 : Perm, perm2 : Perm) : Bool =
    case (perm1, perm2) of
      | ((ObjectPerm (d1,w1), repr1), (ObjectPerm (d2,w2), repr2)) ->
        d1 = d2 && splitting_words_compatible (w1,w2) &&
        (combinable? || ~(splitting_words_combinable (w1,w2)))

  (* Whether two permissions can be combined *)
  op perms_combinable? (perm1 : Perm, perm2 : Perm) : Bool =
    case (perm1, perm2) of
      | ((ObjectPerm (d1,w1), repr1), (ObjectPerm (d2,w2), repr2)) ->
        d1 = d2 && repr1 = repr2 && splitting_words_combinable (w1, w2)

  (* Whether two permissions can be combined *)
  op combine_perms (perm1 : Perm, perm2 : Perm |
                      perms_combinable? (perm1, perm2)) : Perm =
    case (perm1, perm2) of
      | ((ObjectPerm (d,w1), repr), (ObjectPerm (_,w2), _)) ->
        (ObjectPerm (d,combine_splitting_words (w1, w2)), repr)

  (* Whether a single permission is compatible with a list of permissions, where
  the combinable? flag indicates whether it can be combinable with them *)
  op perm_compatible_with_set? (combinable?:Bool) (perm : Perm, perms : List Perm) : Bool =
    forall? (fn perm' -> perms_compatible? combinable? (perm, perm')) perms

  (* Whether a list of permissions is valid, meaning all permissions in it are
  compatible and not combinable *)
  op valid_perm_set? (perms : List Perm) : Bool =
    case perms of
      | [] -> true
      | perm :: perms' ->
        perm_compatible_with_set? false (perm, perms') && valid_perm_set? perms'

  type PermSet = { perms : List Perm | valid_perm_set? perms }

  (* Whether an object permission, or some larger object permission that
  includes the input object permission, is in a permission set *)
  op in_perm_set? (operm : ObjectPerm, perms : PermSet) : Bool =
    exists? (fn (operm', _) -> object_perm_leq (operm, operm')) perms

  (* Look up the value representation for an object permission *)
  op perm_set_lookup (operm : ObjectPerm, perms : PermSet) : Option ValueRepr =
    case (findLeftmost (fn (operm', _) -> object_perm_leq (operm, operm')) perms) of
      | None -> None
      | Some (_, repr) -> Some repr

  (* True iff s1 and s2 are compatible, which means each has only permissions
  that are compatible with the other *)
  op perm_sets_compatible? (perms1 : PermSet, perms2 : PermSet) : Bool =
    case perms1 of
      | [] -> true
      | perm :: perms1' ->
        perm_compatible_with_set? true (perm, perms2) &&
        perm_sets_compatible? (perms1', perms2)

  (* Compatibility is symmetric *)
  theorem perm_sets_compatible?_sym is
    fa (perms1,perms2)
      perm_sets_compatible? (perms1,perms2) =>
      perm_sets_compatible? (perms2,perms1)

  (* Add a permission to a permission set *)
  op add_perm_to_set (perm : Perm, perms : PermSet |
                        perm_compatible_with_set? true (perm, perms)) : PermSet =
    case perms of
      | [] -> [perm]
      | perm' :: perms' ->
        if perms_combinable? (perm, perm') then
          combine_perms (perm, perm') :: perms'
        else
          perm' :: add_perm_to_set (perm, perms')

  (* Combine two permission sets *)
  op combine_perm_sets (perms1 : PermSet, perms2 : PermSet |
                          perm_sets_compatible? (perms1, perms2)) : PermSet =
    case perms1 of
      | [] -> perms2
      | perm :: perms1' ->
        add_perm_to_set (perm, combine_perm_sets (perms1', perms2))

  (* Combining perm sets is symmetric *)
  theorem combine_perm_sets_sym is
    fa (perms1,perms2)
      perm_sets_compatible? (perms1,perms2) =>
      combine_perm_sets (perms1,perms2) = combine_perm_sets (perms2,perms1)

  (* 3 permission sets are compatible with each other *)
  op perm_sets_compatible3? (perms1 : PermSet, perms2 : PermSet, perms3 : PermSet) : Bool =
    perm_sets_compatible? (perms2, perms3) &&
    perm_sets_compatible? (perms1, combine_perm_sets (perms2, perms3))


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
