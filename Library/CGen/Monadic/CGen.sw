CGen qualifying spec
  import C_Permissions, C_DSL


  (***
   *** Extracting LValue Perms from the Current Permission Set
   ***)

  op [a] ifequal (x:a,y:a,res1:Bool,res2:Bool) : Bool =
    if x = y then res1 else res2

  theorem ifequal_eq is [a]
    fa (x:a,res1,res2)
      res1 => ifequal (x,x,res1,res2)

  theorem ifequal_neq is [a]
    fa (x:a,y,res1,res2)
      x ~= y && res2 => ifequal (x,y,res1,res2)

  (* When an expression reads the value of an lvalue, the resulting value might
  have some aliasing with the lvalue, specifically if the value is a pointer
  value. This splits a value abstraction that was originally on an lvalue into
  value abstractions for the expression and to remain with the lvalue. *)
  (* FIXME HERE: figure out how to define this!! *)
  op [a] lvalue_expr_and_lvalue_abses? (lv:LValue, vabs: ValueAbs a,
                                        expr_vabs: ValueAbs a,
                                        lv_vabs: ValueAbs a) : Bool

  (* This predicate says it is allowable (as in, it does not result in any more
  perms) to go from perms_in to perms_out plus the given perms on the lvalue lv,
  and that the given perms actually allow reading the given lvalue; the latter
  is ensured by requiring at least on permission on the lvalue.  This predicate
  is used below to search for all the permissions in perms_in that correspond to
  a given biview. *)
  op [a,b] view_perms_extract_to? (perms_in: PermSet a, lens: BisimView (a,b),
                                   lv: LValue, vperms: List (ValPerm b),
                                   perms_out: PermSet a) : Bool =
    length vperms > 0 &&
    perm_set_weaker? (perms_in,
                      perms_out ++
                        map_exec (fn vperm ->
                                    (perm_of_val_perm lv
                                       (val_perm_add_view (vperm, lens)))) vperms)

  (* Helper predicate for the rules below, that allows vperms = [] *)
  op [a,b] view_perms_extract_toH (perms_in: PermSet a, lens: BisimView (a,b),
                                   lv: LValue, vperms: List (ValPerm b),
                                   perms_out: PermSet a) : Bool =
    perm_set_weaker? (perms_in,
                      perms_out ++
                        map_exec (fn vperm ->
                                    (perm_of_val_perm lv
                                       (val_perm_add_view (vperm, lens)))) vperms)

  (* The following rules essentially form a logic program for proving
  view_perms_extract_to? for a given perms_in and lens *)

  theorem view_perms_extract_from_H is [a,b]
    fa (perms_in,lens:BisimView (a,b),lv,vperms,perms_out)
      view_perms_extract_toH (perms_in,lens,lv,vperms,perms_out) &&
      length vperms > 0 =>
      view_perms_extract_to? (perms_in,lens,lv,vperms,perms_out)

  theorem view_perms_extract_nil is [a,b]
    fa (lens:BisimView (a,b),lv,vperms,perms_out)
      vperms = [] && perms_out = [] =>
      view_perms_extract_toH ([],lens,lv,vperms,perms_out)

  theorem view_perms_extract_cons_lv is [a,b]
    fa (lv1,splexpr,vabs,lens1,perms_in,lens:BisimView (a,b),lv,vperms,perms_out,
        vperms',perms_out',expr_vabs,lv_vabs)
      view_perms_extract_toH (perms_in,lens,lv,vperms',perms_out') &&
      ifequal (lens,lens1,
               (lv = lv1 &&
                  lvalue_expr_and_lvalue_abses? (lv, vabs, expr_vabs, lv_vabs) &&
                  vperms = ValPerm (splexpr, expr_vabs)::vperms' &&
                  perms_out = LVPerm (lv,splexpr,
                                      value_abs_add_view (lv_vabs, lens1))::perms_out'),
               (vperms = vperms' &&
                  perms_out = LVPerm (lv1, splexpr,
                                      value_abs_add_view (vabs, lens1))::perms_out')
               ) =>
      view_perms_extract_toH (LVPerm (lv1, splexpr,
                                      value_abs_add_view (vabs, lens1))::perms_in,
                              lens,lv,vperms,perms_out)

  (* FIXME: give implicational permissions to the value *)
  theorem view_perms_extract_cons_lvi is [a,b]
    fa (lv1,impl,perms_in,lens:BisimView (a,b),lv,vperms,perms_out,perms_out')
      perms_out = LVIPerm (lv1, impl)::perms_out' &&
      view_perms_extract_toH (perms_in,lens,lv,vperms,perms_out') =>
      view_perms_extract_toH (LVIPerm (lv1, impl)::perms_in,
                              lens,lv,vperms,perms_out)

  theorem view_perms_extract_cons_st is [a,b]
    fa (splexpr,uabs,perms_in,lens:BisimView (a,b),lv,vperms,perms_out,perms_out')
      perms_out = StPerm (splexpr, uabs)::perms_out' &&
      view_perms_extract_toH (perms_in,lens,lv,vperms,perms_out') =>
      view_perms_extract_toH (StPerm (splexpr, uabs)::perms_in,
                              lens,lv,vperms,perms_out)

  theorem view_perms_extract_cons_sti is [a,b]
    fa (impl,perms_in,lens:BisimView (a,b),lv,vperms,perms_out,perms_out')
      perms_out = StIPerm impl::perms_out' &&
      view_perms_extract_toH (perms_in,lens,lv,vperms,perms_out') =>
      view_perms_extract_toH (StIPerm impl::perms_in,
                              lens,lv,vperms,perms_out)


  (***
   *** Relational Versions of Operations on Permissions
   ***)

  (* lens_compose *)

  op [a,b,c] is_compose_biviews (bv1: BisimView (a,b), bv2: BisimView (b,c),
                              bv_out: BisimView (a,c)) : Bool =
    compose_biviews (bv1, bv2) = bv_out

  theorem prove_is_compose_biviews is [a,b,c]
    fa (l1: Lens (a,b), l2: Lens (b,c), l_out)
      l_out = biview_of_lens
                {lens_get = (fn a -> l2.lens_get (l1.lens_get a)),
                 lens_set = (fn a -> fn c ->
                               l1.lens_set a (l2.lens_set (l1.lens_get a) c))} =>
      is_compose_biviews (biview_of_lens l1, biview_of_lens l2, l_out)


  (* perm_add_view *)

  op [a,b] is_perm_add_view (perm: Perm a, bv: BisimView (b,a),
                             perm_out: Perm b) : Bool =
    perm_add_view (perm, bv) = perm_out

  theorem is_perm_add_view_lv is [a,b,c]
    fa (lv,splexpr,vabs:ValueAbs c,bv1,bv:BisimView (b,a),bv_out,perm_out)
      is_compose_biviews (bv, bv1, bv_out) &&
      perm_out = LVPerm (lv, splexpr, value_abs_add_view (vabs, bv_out)) =>
      is_perm_add_view (LVPerm (lv, splexpr,
                                value_abs_add_view (vabs, bv1)),
                        bv, perm_out)

  theorem is_perm_add_view_lvi is [a,b]
    fa (lv,impl,bv:BisimView (b,a),perm_out)
      perm_out = LVIPerm (lv, impl) =>
      is_perm_add_view (LVIPerm (lv, impl), bv, perm_out)

  theorem is_perm_add_view_sti is [a,b,c]
    fa (splexpr,uabs:UnitAbs c,bv1,bv:BisimView (b,a),bv_out,perm_out)
      is_compose_biviews (bv, bv1, bv_out) &&
      perm_out = StPerm (splexpr, unit_abs_add_view (uabs, bv_out)) =>
      is_perm_add_view (StPerm (splexpr,
                                unit_abs_add_view (uabs, bv1)),
                        bv, perm_out)

  theorem is_perm_add_view_sti is [a,b]
    fa (impl,bv:BisimView (b,a),perm_out)
      perm_out = StIPerm impl =>
      is_perm_add_view (StIPerm impl, bv, perm_out)


  (* perm_set_add_view *)

  op [a,b] is_perm_set_add_view (perms: PermSet a, bv: BisimView (b,a),
                                 perms_out: PermSet b) : Bool =
    perm_set_add_view (perms, bv) = perms_out

  theorem is_perm_set_add_view_cons is [a,b]
    fa (perm,perms,bv:BisimView (b,a),perms_out,perms_out',perm')
      is_perm_add_view (perm, bv, perm') &&
      is_perm_set_add_view (perms, bv, perms_out') &&
      perms_out = perm'::perms_out' =>
      is_perm_set_add_view (perm::perms, bv, perms_out)

  theorem is_perm_set_add_view_nil is [a,b]
    fa (bv:BisimView (b,a),perms_out)
      perms_out = [] =>
      is_perm_set_add_view ([], bv, perms_out)


  (* perm_set_of_arg_perms *)

  op [a] is_perm_set_of_arg_perms (perms: ArgListPerms a, vars: ParameterList,
                                   perm_set: PermSet a) : Bool =
    equiLong (perms.2, vars) &&
    perm_set = perm_set_of_arg_perms (perms, map (fn x -> x.2) vars)

  theorem is_perm_set_of_arg_perms_cons1 is [a]
    fa (splexpr,uabs,fst_perms,argperms,vars,perm_set,perm_set':PermSet a)
      perm_set = StPerm (splexpr, uabs) :: perm_set' &&
      is_perm_set_of_arg_perms ((fst_perms,argperms),vars, perm_set') =>
      is_perm_set_of_arg_perms ((FunStPerm (splexpr, uabs)::fst_perms,argperms),
                                vars, perm_set)

  theorem is_perm_set_of_arg_perms_cons2 is [a]
    fa (impl,fst_perms,argperms,vars,perm_set,perm_set':PermSet a)
      perm_set = StIPerm impl :: perm_set' &&
      is_perm_set_of_arg_perms ((fst_perms,argperms),vars, perm_set') =>
      is_perm_set_of_arg_perms ((FunStIPerm impl::fst_perms,argperms),
                                vars, perm_set)

  theorem is_perm_set_of_arg_perms_cons3 is [a]
    fa (splexpr,vabs,vperms,argperms,x,tp,vars,perm_set,perm_set':PermSet a)
      perm_set = LVPerm (LV_ident x, splexpr, vabs) :: perm_set' &&
      is_perm_set_of_arg_perms (([], vperms::argperms),(tp,x)::vars, perm_set') =>
      is_perm_set_of_arg_perms (([], (ValPerm (splexpr, vabs)::vperms)::argperms),
                                (tp,x)::vars, perm_set)

  theorem is_perm_set_of_arg_perms_cons4 is [a]
    fa (argperms,var,vars,perm_set:PermSet a)
      is_perm_set_of_arg_perms (([], argperms),vars, perm_set) =>
      is_perm_set_of_arg_perms (([], []::argperms),
                                var::vars, perm_set)

  theorem is_perm_set_of_arg_perms_nil is [a]
    fa (perm_set:PermSet a)
      perm_set = [] =>
      is_perm_set_of_arg_perms (([],[]), [], perm_set)


  op [a,b] is_val_perm_add_view (vperm: ValPerm a, bv: BisimView (b,a),
                                 vperm_out: ValPerm b) : Bool =
    val_perm_add_view (vperm, bv) = vperm_out


  op [a,b] is_val_perms_add_view (vperms: List (ValPerm a), bv: BisimView (b,a),
                                  vperms_out: List (ValPerm b)) : Bool =
    val_perms_add_view (vperms, bv) = vperms_out


  (***
   *** Canonicalizing Permission Sets by Proving perm_set_weaker?
   ***)


  (***
   *** Boolean Expressions
   ***)

  op bool_valueabs : ValueAbs Bool =
    scalar_value_abstraction (fn (v,b) -> zeroScalarValue? v = return b)

  (* No aliasing between a Boolean value and the lvalue it came from *)
  theorem bool_valueabs_expr_and_lvalue_abses is
    fa (lv, expr_vabs, lv_vabs)
      expr_vabs = bool_valueabs && lv_vabs = bool_valueabs =>
      lvalue_expr_and_lvalue_abses? (lv, bool_valueabs, expr_vabs, lv_vabs)

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
   *** Variable Expressions
   ***)

  (* The following theorems all prove that a variable expression is correct. The
  general form is var_i_j_correct, which proves that the jth variable in a
  context with i variables (represented as an i-tuple) is correct. *)

  theorem var_1_1_correct is [a]
    fa (envp,perms_in:PermSet a,eperms_out,perms_out,vperms,m,x)
      m = VAR_m x &&
      view_perms_extract_to? (perms_in, identity_biview,
                              LV_ident x, vperms, perms_out) &&
      eperms_out = (perms_out, vperms) =>
      abstracts_expression envp perms_in eperms_out (fn a -> a) m

  theorem var_2_1_correct is [a,b]
    fa (envp,perms_in:PermSet (a*b),eperms_out,perms_out,vperms,m,x)
      m = VAR_m x &&
      view_perms_extract_to? (perms_in, proj1_biview,
                              LV_ident x, vperms, perms_out) &&
      eperms_out = (perms_out, vperms) =>
      abstracts_expression envp perms_in eperms_out (fn (a,b) -> a) m

  theorem var_2_2_correct is [a,b]
    fa (envp,perms_in:PermSet (a*b),eperms_out,perms_out,vperms,m,x)
      m = VAR_m x &&
      view_perms_extract_to? (perms_in, proj2_biview,
                              LV_ident x, vperms, perms_out) &&
      eperms_out = (perms_out, vperms) =>
      abstracts_expression envp perms_in eperms_out (fn (a,b) -> b) m


  (***
   *** Return Statements and Assignments to Output Variables
   ***)

  (* FIXME: documentation! *)

  (* Abstraction for blocks, which are lists of unit computations *)
  op [a,b] abstracts_block (env_pred : EnvPred)
                           (perms_in: PermSet a)
                           (perms_out: PermSet b)
                           (f: a -> b) (ms: List BlockItem_m) : Bool =
    abstracts_statement env_pred perms_in perms_out f (BLOCK_m ms)


  (* Relation to turn a list of statements into a statement, omitting the block
  for the special case of a list of length 1 *)
  op block_as_statement? (block: List BlockItem_m, stmt: Monad ()) : Bool =
    BLOCK_m block = stmt

  theorem block_as_statement_1 is
    fa (stmt,stmt_out)
      stmt_out = stmt => block_as_statement? ([STMT_m stmt], stmt_out)
  theorem block_as_statement_nil is
    fa (stmt_out)
      stmt_out = BLOCK_m [] => block_as_statement? ([], stmt_out)
  theorem block_as_statement_N is
    fa (stmt1,stmt2,stmts,stmt_out)
      stmt_out = BLOCK_m (stmt1::stmt2::stmts) =>
      block_as_statement? (stmt1::stmt2::stmts, stmt_out)

(*
  theorem return_1_2_correct is [a,b,c]
    fa (envp,perms_in,perms1,perms_out,eperms_out,f:a->b,e:a->c,
        expr,block,stmt,perms_out1,perms_out2)
      abstracts_block envp perms_in perms1 f block &&
      abstracts_expression envp perms1 eperms_out e expr &&
      is_perm_set_add_view (eperms_out.1, proj1_biview, perms_out1) &&
      is_val_perms_add_view (eperms_out.2, proj2_biview, perms_out2) &&
      perms_out = (perms_out1, perms_out2) &&
      block_as_statement? (block ++ [STMT_m (RETURN_m expr)], stmt) =>
      abstracts_ret_statement
        envp perms_in perms_out
        (fn x -> (f x, e x))
        stmt

  theorem RETURN_correct_unit_l is [b]
    fa (envp,perms_in,perms_out,eperms_out,e:()->b,expr,stmt)
      stmt = RETURN_m expr &&
      perms_out = (perm_set_add_view (eperms_out.1, proj1_biview),
                   Some (val_perms_add_view (eperms_out.2, proj2_biview))) &&
      abstracts_expression envp perms_in eperms_out e expr =>
      abstracts_ret_statement
        envp perms_in perms_out
        (fn () -> ((), e ()))
        stmt

  op [a] RETURN_VOID : a -> a * () = fn a -> (a, ())

  theorem RETURN_VOID_correct is [a]
    fa (envp,perms_in:PermSet a,perms_out,stmt)
      stmt = RETURN_VOID_m &&
      perms_out = (perm_set_add_view (perms_in, proj1_biview),None) =>
      abstracts_ret_statement
        envp perms_in perms_out
        RETURN_VOID
        stmt
*)

  (***
   *** Functions
   ***)


  (* FIXME: need permissions to deallocate the current stack from at the end of body *)
  (* FIXME: also need a value_abs_has_type precondition *)
  theorem FUNCTION_correct is [a,b]
    fa (envp,perms_in,perms_in_sub,perms_out,perms_out_sub,perms_out_sub',
        f:a->b,m,prototype,body)
      m = FUNCTION_m (prototype.1, prototype.2, prototype.3, body) &&
      FunStIPerm auto_allocation_perm in? perms_out.1.1 &&
      is_perm_set_of_arg_perms (perms_out.1, prototype.3, perms_out_sub') &&
      is_perm_set_of_arg_perms (perms_in, prototype.3, perms_in_sub) &&
      perm_set_weaker? (perms_out_sub.1, perms_out_sub') &&
      perms_out.2 = perms_out_sub.2 &&
      abstracts_ret_statement
        envp
        perms_in_sub
        perms_out_sub
        f
        body =>
      abstracts_c_function_decl envp perms_in perms_out f prototype m

end-spec
