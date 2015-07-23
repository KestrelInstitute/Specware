CGen qualifying spec
  import C_Permissions, C_DSL


  (***
   *** Boolean Expressions
   ***)

  op bool_valueabs : ValueAbs Bool =
    scalar_value_abstraction (fn (v,b) -> zeroScalarValue? v = return b)

  theorem true_correct is [a]
    fa (perms:PermSet a,m)
      m = ICONST_m "1" =>
      abstracts_expression perms (perms, ([], bool_valueabs)) (fn _ -> true) m

  theorem false_correct is [a]
    fa (perms:PermSet a,m)
      m = ICONST_m "0" =>
      abstracts_expression perms (perms, ([], bool_valueabs)) (fn _ -> false) m


  (***
   *** Return Statements and Assignments to Output Variables
   ***)

  (* FIXME: document all these! *)

  op [a,b] RETURN (e: a -> b) : a -> a * b =
    fn a -> (a, e a)

  theorem RETURN_correct is [a,b]
    fa (perms_in,perms_out,eperms_out,e:a->b,expr,stmt)
      stmt = RETURN_m expr &&
      perms_out = (perm_set_map (invert_biview proj1_biview) eperms_out.1,
                   Some (val_perm_map (invert_biview proj2_biview) eperms_out.2)) &&
      abstracts_expression perms_in eperms_out e expr =>
      abstracts_ret_statement
        perms_in perms_out
        (RETURN e)
        stmt

  op [a] RETURN_VOID : a -> a * () = fn a -> (a, ())

  theorem RETURN_VOID_correct is [a]
    fa (perms_in:PermSet a,perms_out,stmt)
      stmt = RETURN_VOID_m &&
      perms_out = (perm_set_map (invert_biview proj1_biview) perms_in, None) &&
      abstracts_ret_statement
        perms_in perms_out
        RETURN_VOID
        stmt


  (***
   *** Functions
   ***)


end-spec