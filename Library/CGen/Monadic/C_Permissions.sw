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
   *** Permissions and permission sets
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
     repr_combine : ReprCombineRel,
     repr_deps : (Storage -> Value -> Map (ObjectDesignator * PermName,
                                           ValueReprRel * ReprCombineRel))}

  type ObjectPerm = | ObjectPerm ObjectDesignator * PermName * SplittingWord

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
  op storage_repr_values_heap (w : SplittingWord) (r : StorageRepr) : StorageFValues =
    fn (d,n) -> case r (ObjectPerm (d,n,w)) of
                  | Some (fv, true) -> Some fv
                  | _ -> None

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

  op perm_sets_compatible? (s1 : PermSet, s2 : PermSet) : Bool =
    (fa (obj_perm) s1 obj_perm = None || s2 obj_perm = None) &&
    (fa (d,n,w1,w2,repr1,repr2)
     s1 (ObjectPerm (d, n, w1)) = Some repr1 &&
     s2 (ObjectPerm (d, n, w2)) = Some repr2 =>
     repr1 = repr2)

  (* FIXME: this still isn't right: s1 could contain L :: w and s2 could contain
     R :: w for each w in L+; combining them would have to give all words! *)
  (* Maybe PermSets need to be lists of the top-most words? *)
  op combine_perm_sets (s1 : PermSet, s2 : PermSet |
                          perm_sets_compatible? (s1, s2)) : PermSet =
    fn (p as ObjectPerm (d,n,w)) ->
      if some? (s1 p) then s1 p
      else if some? (s2 p) then s2 p
      else if (some? (s1 (ObjectPerm (d,n,SplitL :: w)))
                 && some? (s2 (ObjectPerm (d,n,SplitR :: w)))) then
        s1 (ObjectPerm (d,n,SplitL :: w))
      else if (some? (s1 (ObjectPerm (d,n,SplitR :: w)))
                 && some? (s2 (ObjectPerm (d,n,SplitL :: w)))) then
        s2 (ObjectPerm (d,n,SplitL :: w))
      else None


  op satisfies_perm_sets? (heap : PermSet, held : PermSet) (sr : StorageRepr) : Bool

end-spec
