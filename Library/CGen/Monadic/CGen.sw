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
   *** Extracting LValue Perms from the Current Permission Set
   ***)

  (* This predicate says it is allowable (as in, it does not result in any more
  perms) to go from perms_in to perms_out plus the given perms on the lvalue lv,
  and that the given perms actually allow reading the given lvalue; the latter
  is ensured by requiring at least on permission on the lvalue.  This predicate
  is used below to search for all the permissions in perms_in that correspond to
  a given lens. *)
  op [a,b] lens_perms_extract_to? (perms_in: PermSet a, lens: Lens (a,b),
                                   lv: LValue, vperms: List (ValPerm b),
                                   perms_out: PermSet a) : Bool =
    length vperms > 0 &&
    perm_set_weaker? (perms_in,
                      perms_out ++
                        map_exec (fn vperm ->
                                    (perm_of_val_perm lv
                                       (val_perm_add_lens (vperm, lens)))) vperms)

  (* Helper predicate for the rules below, that allows vperms = [] *)
  op [a,b] lens_perms_extract_toH (perms_in: PermSet a, lens: Lens (a,b),
                                   lv: LValue, vperms: List (ValPerm b),
                                   perms_out: PermSet a) : Bool =
    perm_set_weaker? (perms_in,
                      perms_out ++
                        map_exec (fn vperm ->
                                    (perm_of_val_perm lv
                                       (val_perm_add_lens (vperm, lens)))) vperms)

  (* The following rules essentially form a logic program for proving
  lens_perms_extract_to? for a given perms_in and lens *)

  theorem lens_perms_extract_from_H is [a,b]
    fa (perms_in,lens:Lens (a,b),lv,vperms,perms_out)
      lens_perms_extract_toH (perms_in,lens,lv,vperms,perms_out) &&
      length vperms > 0 =>
      lens_perms_extract_to? (perms_in,lens,lv,vperms,perms_out)

(*
  theorem lens_perms_extract_nil is [a,b]
    fa (lens:Lens (a,b),lv)
      true => lens_perms_extract_toH ([],lens,lv,[],[])

  theorem lens_perms_extract_cons is [a,b]
    fa (perm,perms_in,lens:Lens (a,b),lv,vperms,perms_out,
        sub_lv,sub_vperms,sub_perms_out,splexpr,vabs)
      lens_perms_extract_toH (perms_in,lens,sub_lv,sub_vperms,sub_perms_out) &&
      (
       (* Option 1: the head perm is an lvalue perm with the lens we want *)
       (perm = LVPerm (sub_lv, splexpr, value_abs_add_lens (vabs, lens)) &&
        vperms = ValPerm (splexpr, vabs)::sub_vperms &&
        perms_out = sub_perms_out)
       ||
       (* Option 2: the head perm can be anything, and is copied to perms_out *)
       (perms_out = perm::sub_perms_out && vperms = sub_vperms && lv = sub_lv)
       ) =>
      lens_perms_extract_toH (perm::perms_in,lens,lv,vperms,perms_out)
*)

  theorem prove_lens_perms_extract_H is [a,b]
    fa (perm,perms_in,lens:Lens (a,b),lv,vperms,perms_out,vabs,
        sub_lv,sub_vperms,sub_perms_out)
      (case perms_in of
         | [] -> vperms = [] && perms_out = []
         | (LVPerm (lv', splexpr, vabs')) :: perms_in' ->
           (vabs' = value_abs_add_lens (vabs, lens) &&
              lens_perms_extract_toH (perms_in',lens,lv,sub_vperms,sub_perms_out) &&
              lv = lv' &&
              vperms = ValPerm (splexpr, vabs)::sub_vperms &&
              perms_out = sub_perms_out)
           ||
             (lens_perms_extract_toH (perms_in',lens,sub_lv,sub_vperms,sub_perms_out) &&
                perms_out = perm::sub_perms_out && vperms = sub_vperms && lv = sub_lv))
      =>
      lens_perms_extract_toH (perms_in,lens,lv,vperms,perms_out)


  (***
   *** Variable Expressions
   ***)

  (* The following theorems all prove that a variable expression is correct. The
  general form is var_i_j_correct, which proves that the jth variable in a
  context with i variables (represented as an i-tuple) is correct. *)

  theorem var_1_1_correct is [a]
    fa (envp,perms_in:PermSet a,eperms_out,perms_out,vperms,m,x)
      m = VAR_m x &&
      lens_perms_extract_to? (perms_in, id_lens,
                              LV_ident x, vperms, perms_out) &&
      eperms_out = (perms_out, vperms) =>
      abstracts_expression envp perms_in eperms_out (fn a -> a) m

  theorem var_2_1_correct is [a,b]
    fa (envp,perms_in:PermSet (a*b),eperms_out,perms_out,vperms,m,x)
      m = VAR_m x &&
      lens_perms_extract_to? (perms_in, proj1_lens,
                              LV_ident x, vperms, perms_out) &&
      eperms_out = (perms_out, vperms) =>
      abstracts_expression envp perms_in eperms_out (fn (a,b) -> a) m

  theorem var_2_2_correct is [a,b]
    fa (envp,perms_in:PermSet (a*b),eperms_out,perms_out,vperms,m,x)
      m = VAR_m x &&
      lens_perms_extract_to? (perms_in, proj2_lens,
                              LV_ident x, vperms, perms_out) &&
      eperms_out = (perms_out, vperms) =>
      abstracts_expression envp perms_in eperms_out (fn (a,b) -> b) m


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

  (* FIXME: need permissions to deallocate the current stack from at the end of body *)
  (* FIXME: also need a value_abs_has_type precondition *)
  theorem FUNCTION_correct is [a,b]
    fa (envp,perms_in,perms_out,perms_out_sub,f:a->b,m,prototype,body)
      m = FUNCTION_m (prototype.1, prototype.2, prototype.3, body) &&
      FunStIPerm auto_allocation_perm in? perms_out.1.1 &&
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
