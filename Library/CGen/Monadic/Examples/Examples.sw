Examples_spec = spec
  import ../CGen, ../CPrettyPrinter

  (* Function that just returns true, as the statement "return 1" *)
  op just_return_true (x:()) : () * Bool = ((), true)
  op just_return_true_m :
    {m:ExtDecl |
       abstracts_c_function_decl
         (fn _ -> true)
         ([StPerm ([([], None)], cperm_add_lens (auto_allocation_perm, unit_lens))], [])
         ([StPerm ([([], None)], cperm_add_lens (auto_allocation_perm, unit_lens))], [])
         (Some [ValPerm ([([], None)], cperm_add_lens (non_heap_cperm bool_R, proj2_lens))])
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
         ([StPerm ([([], None)], cperm_add_lens (auto_allocation_perm, unit_lens))], [])
         ([StPerm ([([], None)], cperm_add_lens (auto_allocation_perm, unit_lens))], [])
         (Some [ValPerm ([([], None)], cperm_add_lens (non_heap_cperm bool_R, proj2_lens))])
         just_return_false
         (TN_sint, "just_return_false", [])
         m}
  op just_return_false_C :
    {elem:TranslationUnitElem |
       evalTranslationUnitElem elem = just_return_false_m }
  op just_return_false_String : String = runPP0 (printTranslationUnitElem just_return_false_C)

  (* The identity function on Booleans *)
  op boolean_identity (b:Bool) : () * Bool = ((), b)
  op boolean_identity_m :
    {m:ExtDecl |
       abstracts_c_function_decl
         (fn _ -> true)
         ([StPerm ([([], None)], cperm_add_lens (auto_allocation_perm, unit_lens))],
          [[ValPerm ([], cperm_add_lens (non_heap_cperm bool_R, id_lens))]])
         ([StPerm ([([], None)], cperm_add_lens (auto_allocation_perm, unit_lens))],[[]])
         (Some [ValPerm ([], cperm_add_lens (non_heap_cperm bool_R, proj2_lens))])
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
         ([StPerm ([([], None)], cperm_add_lens (auto_allocation_perm, unit_lens))],
          [[ValPerm ([], cperm_add_lens (non_heap_cperm bool_R, id_lens))]])
         ([StPerm ([([], None)], cperm_add_lens (auto_allocation_perm, unit_lens))],[[]])
         (Some [ValPerm ([], cperm_add_lens (non_heap_cperm bool_R, proj2_lens))])
         negate_bool
         (TN_sint, "negate_bool", [(TN_sint, "b")])
         m}
  op negate_bool_C :
    {elem:TranslationUnitElem |
       evalTranslationUnitElem elem = negate_bool_m }
  op negate_bool_String : String = runPP0 (printTranslationUnitElem negate_bool_C)
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
   ;
 at negate_bool_m
   {unfold negate_bool;
    rewrite [strengthen CGen._] {allowUnboundVars? = true, depth = 10000}}
   ;
 makeDefsFromPostConditions [negate_bool_m]
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
   ;
 at boolean_identity_C
   {unfold boolean_identity_m;
    rewrite [strengthen C_DSL._] {allowUnboundVars? = true, depth = 10000}}
   ;
 makeDefsFromPostConditions [boolean_identity_C]
   ;
 at negate_bool_C
   {unfold negate_bool_m;
    rewrite [strengthen C_DSL._] {allowUnboundVars? = true, depth = 10000}}
   ;
 makeDefsFromPostConditions [negate_bool_C]
 }


(* Pretty-print the examples as C code *)
Examples_printed = transform Examples_impl by
{at just_return_true_String {simplify};
 at just_return_false_String {simplify};
 at boolean_identity_String {simplify};
 at negate_bool_String {simplify}}
