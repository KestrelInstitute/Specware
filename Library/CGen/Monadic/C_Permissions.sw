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
   *** Value representations and permissions
   ***)

  (* FIXME: document all of this! *)

  type PermName = String
  type StorageFValues = Map (ObjectDesignator * PermName, FValue)

  type ValueReprRel = SplittingWord -> StorageFValues -> Value -> FValue -> Bool

  type ReprCombineRel = FValue * FValue -> FValue -> Bool

  type ValueRepr =
    {repr_type_name : TypeName,
     repr_xenv_pred : TranslationEnv -> Bool,
     repr_rel : ValueReprRel,
     repr_combines_to : ReprCombineRel,
     repr_deps : (Storage -> Value -> Map (ObjectDesignator * PermName,
                                           ValueReprRel * ReprCombineRel))}

  type ObjectPerm = | ObjectPerm ObjectDesignator * PermName * SplittingWord
  type Perm = ObjectPerm * ValueRepr

  (* The extension of splitting_word_leq to object permissions *)
  op object_perm_leq : CPO.PartialOrder ObjectPerm =
  (fn tup ->
     case tup of
       | (ObjectPerm (d1,n1,w1), ObjectPerm (d2,n2,w2)) ->
         d1 = d2 && n1 = n2 && splitting_word_leq (w1, w2))

  (* Whether two permissions are compatible *)
  op perms_compatible? (combinable?:Bool) (perm1 : Perm, perm2 : Perm) : Bool =
    case (perm1, perm2) of
      | ((ObjectPerm (d1,n1,w1), repr1), (ObjectPerm (d2,n2,w2), repr2)) ->
        d1 = d2 && n1 = n2 && splitting_words_compatible (w1,w2) &&
        (combinable? || ~(splitting_words_combinable (w1,w2)))

  (* Whether two permissions can be combined *)
  op perms_combinable? (perm1 : Perm, perm2 : Perm) : Bool =
    case (perm1, perm2) of
      | ((ObjectPerm (d1,n1,w1), repr1), (ObjectPerm (d2,n2,w2), repr2)) ->
        d1 = d2 && n1 = n2 && repr1 = repr2 && splitting_words_combinable (w1, w2)

  (* Whether two permissions can be combined *)
  op combine_perms (perm1 : Perm, perm2 : Perm |
                      perms_combinable? (perm1, perm2)) : Perm =
    case (perm1, perm2) of
      | ((ObjectPerm (d,n,w1), repr), (ObjectPerm (_,_,w2), _)) ->
        (ObjectPerm (d,n,combine_splitting_words (w1, w2)), repr)

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
    fn (d,n) -> case r (ObjectPerm (d,n,w)) of
                  | Some (fv, _) -> Some fv
                  | None -> None

  (* Convert a StorageRepr to a "slice", for a particular splitting word, of
     FValues for each permission held by the Storage on each object. *)
  op storage_repr_values_heap (w : SplittingWord) (srepr : StorageRepr) : StorageFValues =
    fn (d,n) -> case srepr (ObjectPerm (d,n,w)) of
                  | Some (fv, true) -> Some fv
                  | _ -> None

  (* FIXME: document this! *)
  op storage_repr_as? (heap : PermSet, held : PermSet |
                         perm_sets_compatible? (heap, held))
                      (s : Storage, srepr : StorageRepr) : Bool =
    let perms = combine_perm_sets (heap, held) in
    (fa (d,n,w)
       let p = ObjectPerm (d,n,w) in
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
              (* v has the right type for all xenvs that satisfy the predicate *)
              (fa (xenv) repr.repr_xenv_pred xenv =>
                 expandTypeName (xenv, repr.repr_type_name) = Some (typeOfValue v)) &&
              (* v and fv satisfy the predicate *)
              repr.repr_rel w (storage_repr_values_heap w srepr) v fv &&
              (* The two values below fv combine to fv *)
              (case (srepr (ObjectPerm (d,n,SplitL :: w)),
                     srepr (ObjectPerm (d,n,SplitR :: w))) of
                 | (Some (fv_l, _), Some (fv_r, _)) ->
                   repr.repr_combines_to (fv_l, fv_r) fv
                 | _ -> false) &&
              (* The perms set uses the required relations repr depends on *)
              (fa (d',n',rel',combine')
                 repr.repr_deps s v (d',n') = Some (rel', combine') =>
                 (case (perm_set_lookup (ObjectPerm (d', n', w), perms)) of
                    | Some repr' ->
                      rel' = repr'.repr_rel && combine' = repr'.repr_combines_to
                    | None -> false))
              )
           )

  (***
   *** Permission Set Terms
   ***)

  (* FIXME HERE: write this stuff! *)

  type PermSetTerm

  op evalPermSetTerm (r : R, ws : List SplittingWord) (t : PermSetTerm) : PermSet

  op valsForPermSetTerm (r : R, ws : List SplittingWord)
                        (t : PermSetTerm) (srepr : StorageRepr) : List FValue


  (***
   *** Correctness w.r.t. Permissions
   ***)

  op stmt_correct (r_pred : R -> Bool)
                  (perms_in : PermSetTerm, perms_out : PermSetTerm)
                  (f : List FValue -> List FValue) (m : Monad ()) () : Bool =
    fa (other_held,heap,srepr_in,ws)
      ex (heap',srepr_out)
        totally_correct
        (fn r -> fn s_in ->
           r_pred r &&
           (let my_held_in = evalPermSetTerm (r,ws) perms_in in
            perm_sets_compatible? (my_held_in, other_held) &&
            (let held_in = combine_perm_sets (my_held_in, other_held) in
             perm_sets_compatible? (heap, held_in) &&
             storage_repr_as? (heap, held_in) (s_in, srepr_in))))
        m
        (fn r -> fn s_in -> fn s_out ->
           r_pred r &&
           (let my_held_in = evalPermSetTerm (r,ws) perms_in in
            perm_sets_compatible? (my_held_in, other_held) &&
            (let held_in = combine_perm_sets (my_held_in, other_held) in
             perm_sets_compatible? (heap, held_in) &&
             storage_repr_as? (heap, held_in) (s_in, srepr_in) &&
             (let my_held_out = evalPermSetTerm (r,ws) perms_out in
              perm_sets_compatible? (my_held_out, other_held) &&
              (let held_out = combine_perm_sets (my_held_out, other_held) in
               storage_repr_as? (heap, held_out) (s_out, srepr_out) &&
               valsForPermSetTerm (r,ws) perms_out srepr_out
               = f (valsForPermSetTerm (r,ws) perms_in srepr_in)))))
           )

end-spec
