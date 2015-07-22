CGen qualifying spec
  import C_Permissions, C_DSL


  (***
   *** Combinators for MetaSlang functions that we can translate to C
   ***)

  (* FIXME: document all these! *)

  op [a,b] RETURN (vperm: ValuePerm b) (e: a -> b) : a -> a * b =
    fn a -> (a, e a)

  theorem RETURN_correct is [a,b]
    fa (perms_in: PermSet a,perms_out: PermSet (a*b) * Option (ValuePerm (a*b)),
        vperm:ValuePerm b,e:a->b,expr,stmt)
      stmt = RETURN_m expr &&
      Some (val_perm_map (invert_biview proj2_biview) vperm) = perms_out.2 &&
      abstracts_expression perms_in (perm_set_map proj1_biview perms_out.1,
                                     vperm) e expr =>
      abstracts_ret_statement
        perms_in perms_out
        (RETURN vperm e)
        stmt
                            

end-spec