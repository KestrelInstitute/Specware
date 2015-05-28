(* This spec defines an approach to proving functional correctness properties of
monadic C computations by relating these computations to  *)

C_Permissions qualifying spec
  import C_Predicates


  (***
   *** Value representations
   ***)

  (* To represent C values in logic, we define a universal type for representing
     C values; can be refined to an actual type using finalizeInductiveType *)
  type VRepr

  (* VRepr includes lists (FIXME: add other ops for VRepr_list) *)
  op VRepr_list : List VRepr -> VRepr


  (***
   *** Permissions and permission domains
   ***)

  (* FIXME: document these types! *)

  type PermName = String

  type ValueReprRel =
     | SplittableReprRel
       TypeName * TypedefTable * StructTable *
       (Map (ObjectDesignator * PermName, VRepr) -> Value -> VRepr -> Bool) *
       (VRepr * VRepr -> VRepr -> Bool)
     | NonSplittableReprRel
       TypeName * TypedefTable * StructTable *
       (Map (ObjectDesignator * PermName, VRepr) -> Value -> VRepr -> Bool)


  type SplittingLetter = | SplitL | SplitR
  type SplittingWord = List SplittingLetter
  type ObjectPerm = | ObjectPerm ObjectDesignator * PermName * Option SplittingWord

  type PermSet = { s : ObjectPerm -> Bool |
                    (fa (d,n,w,l)
                       s (ObjectPerm (d, n, Some w)) =>
                       s (ObjectPerm (d, n, Some (l :: w)))) &&
                    (fa (d,n,w)
                       s (ObjectPerm (d, n, Some (SplitL :: w))) &&
                       s (ObjectPerm (d, n, Some (SplitR :: w))) =>
                       s (ObjectPerm (d, n, Some w))) }

  op perm_sets_compatible? (s1 : PermSet, s2 : PermSet) : Bool =
    fa (obj_perm) ~(s1 obj_perm && s2 obj_perm)

  op combine_perm_sets (s1 : PermSet, s2 : PermSet | perm_sets_compatible? (s1, s2)) : PermSet =
    fn obj_perm -> s1 obj_perm || s2 obj_perm


  type PermDomElem =
    | SplittablePermRepr
      (Storage -> ObjectDesignator -> VRepr -> Bool) *
      (Storage -> Value -> List (ObjectDesignator * List PermDomElem)) *
      (VRepr * VRepr -> VRepr -> Bool)
    | NonSplittablePermRepr
      (Storage -> ObjectDesignator -> VRepr -> Bool) *
      (Storage -> Value -> List (ObjectDesignator * List PermDomElem))
  type PermDom = List PermDomElem
  type PermDomAssignment = Map (ObjectDesignator, PermDom)

  type StorageRepr = Map (ObjectPerm, VRepr)

end-spec
