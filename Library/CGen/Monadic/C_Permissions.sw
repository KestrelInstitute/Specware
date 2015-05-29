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
   *** Value representations and permissions
   ***)

  (* FIXME: document all of this! *)

  type PermName = String
  type SplittingLetter = | SplitL | SplitR
  type SplittingWord = List SplittingLetter

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

  type PermSet = { s : Map (ObjectPerm, ValueRepr) |
                    (* Same object / perm name => same ValueRepr *)
                    (fa (d,n,w1,w2,repr1,repr2)
                       s (ObjectPerm (d, n, w1)) = Some repr1 &&
                       s (ObjectPerm (d, n, w2)) = Some repr2 =>
                       repr1 = repr2) &&
                    (* s is downward closed *)
                    (fa (d,n,w,l,repr)
                       s (ObjectPerm (d, n, w)) = Some repr =>
                       s (ObjectPerm (d, n, l :: w)) = Some repr) &&
                    (* s is closed under combining permissions *)
                    (fa (d,n,w,repr)
                       s (ObjectPerm (d, n, SplitL :: w)) = Some repr &&
                       s (ObjectPerm (d, n, SplitR :: w)) = Some repr =>
                       s (ObjectPerm (d, n, w)) = Some repr) }

  (* True iff s1 and s2 have no overlapping permissions, but agree on ValueReprs
  for all object and PermName pairs *)
  op perm_sets_compatible? (s1 : PermSet, s2 : PermSet) : Bool =
    (fa (obj_perm) s1 obj_perm = None || s2 obj_perm = None) &&
    (fa (d,n,w1,w2,repr1,repr2)
     s1 (ObjectPerm (d, n, w1)) = Some repr1 &&
     s2 (ObjectPerm (d, n, w2)) = Some repr2 =>
     repr1 = repr2)

  (* Partial-order on PermSets *)
  op perm_set_leq : CPO.PartialOrder PermSet =
    fn (s1,s2) -> (fa (obj_perm,repr)
                     s1 obj_perm = Some repr || s2 obj_perm = Some repr)

  (* True iff s1 and s2 combine to s. This is written as a relation because it
  is not definable as a decidable function (e.g., if s1 contains Lw and s2
  contains Rw for all words w of length greater than the number of steps for
  Turing machine M to halt, then s1 combined with s2 contains the empty word iff
  M halts), but could be defined if we changed the representation of PermSets to
  be a finite list of the maximal ObjectPerms in a set... *)
  op perm_sets_combine_to? (s1 : PermSet, s2 : PermSet |
                              perm_sets_compatible? (s1, s2))
                           (s : PermSet) : Bool =
    perm_set_leq (s1, s) && perm_set_leq (s2, s) &&
    (fa (s') perm_set_leq (s1, s') && perm_set_leq (s2, s') => perm_set_leq (s,s'))

  (* All compatible perm sets can be combined *)
  theorem perm_sets_combine_to?_exists is
    fa (s1,s2) perm_sets_compatible? (s1, s2) =>
      (ex (s) perm_sets_combine_to? (s1,s2) s)

  (* Combining perm sets is a functional relation *)
  theorem perm_sets_combine_to?_functional is
    fa (s1,s2,s,s')
      perm_sets_compatible? (s1, s2) &&
      perm_sets_combine_to? (s1,s2) s && perm_sets_combine_to? (s1,s2) s' =>
      s = s'


  (***
   *** Storage representations
   ***)

  (* A representation of a Storage gives an FValue for each object permission,
     as well as a flag indicating whether the Storage holds that permission *)
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
  op storage_repr_as? (heap : PermSet, held : PermSet)
                      (s : Storage, srepr : StorageRepr) : Bool =
    let perms = the (perms) perm_sets_combine_to? (heap, held) perms in
    (fa (d,n,w)
       let p = ObjectPerm (d,n,w) in
       case (perms p, srepr p) of
         | (None, None) -> true
         | (None, Some _) -> false
         | (Some _, None) -> false
         | (Some repr, Some (fv, flag)) ->
           (if flag then heap p = Some repr else heap p = None) &&
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
              (* The perms set uses the required relations repr is dependent on *)
              (fa (d',n')
                 case (repr.repr_deps s v (d',n'), perms (ObjectPerm (d', n', w))) of
                   | (None, _) -> true
                   | (Some (rel', combine'), Some repr') ->
                     rel' = repr'.repr_rel && combine' = repr'.repr_combines_to
                   | (Some _, None) -> false)
              )
           )

end-spec
