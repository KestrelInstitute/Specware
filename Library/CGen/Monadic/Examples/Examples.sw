Examples_spec = spec
  import ../CGen, ../CPrettyPrinter

  (* Function that just returns true, as the statement "return 1" *)
  op just_return_true : () -> () * Bool = RETURN (fn _ -> true)
  op just_return_true_m :
    {m:Monad () |
       abstracts_ret_statement
         (fn _ -> true)
         []
         ([], Some ([], value_abs_map (invert_biview proj2_biview) bool_valueabs))
         just_return_true m}
  op just_return_true_C :
    { stmt: Statement |
       evalStatement stmt = just_return_true_m }
  op just_return_true_String : String = runPP0 (printStatement just_return_true_C)

  (* Function that just returns false, as the statement "return 0" *)
  op just_return_false : () -> () * Bool = RETURN (fn _ -> false)
  op just_return_false_m :
    {m:Monad () |
       abstracts_ret_statement
         (fn _ -> true)
         []
         ([], Some ([], value_abs_map (invert_biview proj2_biview) bool_valueabs))
         just_return_false m}
  op just_return_false_C :
    { stmt: Statement |
       evalStatement stmt = just_return_false_m }
  op just_return_false_String : String = runPP0 (printStatement just_return_false_C)

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
