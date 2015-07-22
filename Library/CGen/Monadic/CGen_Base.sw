CGen_Base qualifying spec
  import C_Permissions, C_DSL


  (***
   *** Combinators for MetaSlang functions that we can translate to C
   ***)

  (* FIXME: document all these! *)

  op [a,b] RETURN (abs: ValueAbs b) (f: a -> b) : a -> a * b =
    fn a -> (a, f a)

  theorem RETURN_correct is [a,b]
    fa (perms_in: PermSet a,perms_out: PermSet (a*b) * Option (ValuePerm (a*b)),abs,f:a->b,expr,stmt)
      stmt = C_DSL.RETURN expr && Some abs = perms_out.2 &&
      abstracts_expression perms_in (perm_set_map proj1_biview perms_out.1,
                                     val_perm_map proj2_biview abs) f expr =>
      abstracts_ret_statement
        perms_in perms_out
        (CGen_Base.RETURN abs f)
        stmt
                            

end-spec