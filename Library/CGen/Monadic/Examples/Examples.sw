Examples_spec = spec
  import ../CGen, ../CPrettyPrinter

  (* Function that just returns true, as the statement "return 1" *)
  op just_return_true () : () * Bool = ((), true)
  op just_return_true_m :
    {m:ExtDecl |
       abstracts_c_function_decl
         (fn _ -> true)
         ([FunStIPerm auto_allocation_perm], [])
         (([FunStIPerm auto_allocation_perm], []),
          Some [ValPerm ([], value_abs_add_lens (bool_valueabs, proj2_lens))])
         just_return_true
         (TN_sint, "just_return_true", [])
         m}
  op just_return_true_C :
    {elem:TranslationUnitElem |
       evalTranslationUnitElem elem = just_return_true_m }
  op just_return_true_String : String = runPP0 (printTranslationUnitElem just_return_true_C)

  (* Function that just returns false, as the statement "return 0" *)
  op just_return_false () : () * Bool = ((), false)
  op just_return_false_m :
    {m:ExtDecl |
       abstracts_c_function_decl
         (fn _ -> true)
         ([FunStIPerm auto_allocation_perm], [])
         (([FunStIPerm auto_allocation_perm], []),
          Some [ValPerm ([], value_abs_add_lens (bool_valueabs, proj2_lens))])
         just_return_false
         (TN_sint, "just_return_false", [])
         m}
  op just_return_false_C :
    {elem:TranslationUnitElem |
       evalTranslationUnitElem elem = just_return_false_m }
  op just_return_false_String : String = runPP0 (printTranslationUnitElem just_return_false_C)

  (* The identity function on Booleans *)
  op boolean_identity (b:Bool) : Bool * Bool = (b, b)
  op boolean_identity_m :
    {m:ExtDecl |
       abstracts_c_function_decl
         (fn _ -> true)
         ([FunStIPerm auto_allocation_perm],
          [[ValPerm ([], value_abs_add_lens (bool_valueabs, id_lens))]])
         (([FunStIPerm auto_allocation_perm],
           [[ValPerm ([], value_abs_add_lens (bool_valueabs, proj1_lens))]]),
          Some [ValPerm ([], value_abs_add_lens (bool_valueabs, proj2_lens))])
         boolean_identity
         (TN_sint, "boolean_identity", [(TN_sint, "b")])
         m}
  op boolean_identity_C :
    {elem:TranslationUnitElem |
       evalTranslationUnitElem elem = boolean_identity_m }
  op boolean_identity_String : String = runPP0 (printTranslationUnitElem boolean_identity_C)


  (* Function that negates its Boolean-valued input using an if statement *)
  op negate_bool (b:Bool) : () * Bool =
    if b then ((), false) else ((), true)
  op negate_bool_m :
    {m:ExtDecl |
       abstracts_c_function_decl
         (fn _ -> true)
         ([], [[ValPerm ([], bool_valueabs)]])
         (([], [[]]),
          Some [ValPerm ([], value_abs_add_lens (bool_valueabs, proj2_lens))])
         negate_bool
         (TN_sint, "just_return_true", [(TN_sint, "b")])
         m}
end-spec


(* Synthesize the monadic versions of the examples *)
Examples_m =
transform Examples_spec by
{at just_return_true_m
   {unfold just_return_true;
    rewrite [strengthen CGen._] {allowUnboundVars? = true, depth = 10000}}
   ;
 makeDefsFromPostConditions [just_return_true_m]
   ;
 at just_return_false_m
   {unfold just_return_false;
    rewrite [strengthen CGen._] {allowUnboundVars? = true, depth = 10000}}
   ;
 makeDefsFromPostConditions [just_return_false_m]
   ;
 at boolean_identity_m
   {unfold boolean_identity;
    rewrite [strengthen CGen._] {allowUnboundVars? = true, depth = 10000}}
   ;
 makeDefsFromPostConditions [boolean_identity_m]
 }


(* Synthesize the C code from the monadic definitions *)
Examples_impl =
transform Examples_m by
{at just_return_true_C
   {unfold just_return_true_m;
    rewrite [strengthen C_DSL._] {allowUnboundVars? = true, depth = 10000}}
   ;
 makeDefsFromPostConditions [just_return_true_C]
   ;
 at just_return_false_C
   {unfold just_return_false_m;
    rewrite [strengthen C_DSL._] {allowUnboundVars? = true, depth = 10000}}
   ;
 makeDefsFromPostConditions [just_return_false_C]
 }


(* Pretty-print the examples as C code *)
Examples_printed = transform Examples_impl by
{at just_return_true_String {simplify};
 at just_return_false_String {simplify}}
