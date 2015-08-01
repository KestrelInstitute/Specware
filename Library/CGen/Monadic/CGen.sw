CGen qualifying spec
  import C_Permissions, C_DSL


  (***
   *** Boolean Expressions
   ***)

  op bool_valueabs : ValueAbs Bool =
    scalar_value_abstraction (fn (v,b) -> zeroScalarValue? v = return b)

  theorem true_correct is [a]
    fa (envp,perms_in:PermSet a,perms_out,m)
      m = ICONST_m "1" &&
      perms_out = (perms_in, [ValPerm ([], bool_valueabs)]) =>
      abstracts_expression envp perms_in perms_out (fn _ -> true) m

  theorem false_correct is [a]
    fa (envp,perms_in:PermSet a,perms_out,m)
      m = ICONST_m "0" &&
      perms_out = (perms_in, [ValPerm ([], bool_valueabs)]) =>
      abstracts_expression envp perms_in perms_out (fn _ -> false) m


  (***
   *** Return Statements and Assignments to Output Variables
   ***)

  (* FIXME: document all these! *)

  (*
  op [a,b] RETURN (e: a -> b) : a -> a * b =
    fn a -> (a, e a)
   *)

  theorem RETURN_correct is [a,b]
    fa (envp,perms_in,perms_out,eperms_out,e:a->b,expr,stmt)
      stmt = RETURN_m expr &&
      perms_out = (perm_set_add_lens (eperms_out.1, proj1_lens),
                   Some (val_perms_add_lens (eperms_out.2, proj2_lens))) &&
      abstracts_expression envp perms_in eperms_out e expr =>
      abstracts_ret_statement
        envp perms_in perms_out
        (fn x -> (x, e x))
        stmt

  theorem RETURN_correct_unit_l is [b]
    fa (envp,perms_in,perms_out,eperms_out,e:()->b,expr,stmt)
      stmt = RETURN_m expr &&
      perms_out = (perm_set_add_lens (eperms_out.1, proj1_lens),
                   Some (val_perms_add_lens (eperms_out.2, proj2_lens))) &&
      abstracts_expression envp perms_in eperms_out e expr =>
      abstracts_ret_statement
        envp perms_in perms_out
        (fn () -> ((), e ()))
        stmt

  op [a] RETURN_VOID : a -> a * () = fn a -> (a, ())

  theorem RETURN_VOID_correct is [a]
    fa (envp,perms_in:PermSet a,perms_out,stmt)
      stmt = RETURN_VOID_m &&
      perms_out = (perm_set_add_lens (perms_in, proj1_lens),None) =>
      abstracts_ret_statement
        envp perms_in perms_out
        RETURN_VOID
        stmt


  (***
   *** Functions
   ***)

  (* FIXME: this should actually do some sort of unification... *)
  (*
  theorem perms_weaker_can_be_tested is [a]
    fa (perms1,perms2:PermSet a)
      forall? (fn perm2 ->
                 exists? (fn perm1 ->
                            perm1.1 = perm2.1 &&
                            splset_expr_leq (perm1.2.1,perm2.2.1) &&
                            perm1.2.2 = perm2.2.2) perms1) perms2 =>
      perms_weaker? (perms1,perms2)
      *)

  (* FIXME: also need a value_abs_has_type precondition *)
  theorem FUNCTION_correct is [a,b]
    fa (envp,perms_in,perms_out,perms_out_sub,f:a->b,m,prototype,body)
      m = FUNCTION_m (prototype.1, prototype.2, prototype.3, body) &&
      equiLong (perms_in.2, prototype.3) &&
      equiLong (perms_out.1.2, prototype.3) &&
      perm_set_weaker? (perms_out_sub.1,
                        perm_set_of_arg_perms (perms_out.1,
                                               map (fn x -> x.2) prototype.3)) &&
      perms_out.2 = perms_out_sub.2 &&
      abstracts_ret_statement
        envp
        (perm_set_of_arg_perms (perms_in, map (fn x -> x.2) prototype.3))
        perms_out_sub
        f
        body =>
      abstracts_c_function_decl envp perms_in perms_out f prototype m

end-spec
