(* This spec defines an approach to proving functional correctness properties of
monadic C computations by relating these computations to  *)

C_Permissions qualifying spec
  import C_Predicates


  (* Universal type for representing C values; can be refined to an actual type
  using finalizeInductiveType *)
  type VRepr

  (* VRepr includes lists (FIXME: add other ops for mklist_VRepr) *)
  op VRepr_mklist : List VRepr -> VRepr



end-spec
