(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* Substitution (Prototype) *)

%% Dialog about adding this feature is at end of file

SpecCalc qualifying spec
  import Signature
  import /Library/Legacy/DataStructures/ListUtilities % for listUnion
  import UnitId/Utilities                             % for uidToString, if used...
  import SpecSubst   
  import SpecPrismSubst  

  def SpecCalc.evaluateSubstitute (spec_tm, subst_tm, pragmas) term_pos = % subst_tm could be morphism or prism
   {
    unitId <- getCurrentUID;  % this seems to refer to an outer term, e.g. the "X" in "X = S[M]"
    print (";;; Elaborating spec-substitution at " ^ uidToString unitId ^ "\n");

    spec_value_info  as (spec_value,  spec_timestamp,  spec_dep_UIDs)  <- evaluateTermInfo spec_tm;
    subst_value_info as (subst_value, subst_timestamp, subst_dep_UIDs) <- evaluateTermInfo subst_tm;

    coercedSpecValue <- return (coerceToSpec spec_value);
    case (coercedSpecValue, subst_value) of % TODO: coerceToMorphismOrPrism subst_value ??

      | (Spec spc, Morph sm) ->
        let timeStamp = max (spec_timestamp, subst_timestamp)     in
        let dep_UIDs  = listUnion (spec_dep_UIDs, subst_dep_UIDs) in 
        {
         new_spec   <- applySpecMorphismSubstitution sm spc subst_tm spec_tm term_pos;
         compressed <- complainIfAmbiguous new_spec term_pos;  %(compressDefs new_spec)   term_pos;
         new_spec <- return(setElements(compressed, compressed.elements ++ map SMPragmaToElement pragmas));
         return (Spec new_spec, timeStamp, dep_UIDs)
         }

      | (Spec spc, SpecPrism prsm) ->
        let timeStamp = max (spec_timestamp, subst_timestamp)     in
        let dep_UIDs  = listUnion (spec_dep_UIDs, subst_dep_UIDs) in 
        {
         new_spec   <- applySpecPrismSubstitution prsm spc subst_tm spec_tm term_pos;
         compressed <- complainIfAmbiguous new_spec term_pos;  %(compressDefs new_spec)   term_pos;
         new_spec <- return(setElements(compressed, compressed.elements ++ map SMPragmaToElement pragmas));
         return (Spec new_spec, timeStamp, dep_UIDs)
         }

      | (Other _, Other _) ->
        evaluateOtherSubstitute spec_tm spec_value_info subst_tm subst_value_info term_pos

      | (Spec _, _)           -> raise (TypeCheck (positionOf subst_tm, "substitution is not a morphism or prism"))
      | (_,      Morph     _) -> raise (TypeCheck (positionOf spec_tm,  "substitution attempted on a non-spec"))
      | (_,      SpecPrism _) -> raise (TypeCheck (positionOf spec_tm,  "prism substitution attempted on a non-spec"))
      | _                     -> raise (TypeCheck (term_pos,            "substitution is not a morphism or a prism, and is attempted on a non-spec"))
    }

end-spec

(*
From  AC :

 While the exact syntax still needs to be pinned down, in the end today 
 everybody (even I!) agreed that the substitution operation should take 
 two arguments, a spec and a morphism. So, conceptually it's:
 
   S' = substitute(S,M)
 
 This was mostly motivated by the fact that often M is available in the 
 library (e.g., the morphism SetsAsListsRef from Sets to SetsAsLists), 
 its proof obligations have hopefully being discharged already, so it 
 seems advantageous to be able to just refer to it by its name.
 
 Here's the semantics, again.
 
 First, of course S and M must be a valid spec and a valid morphism.
 
 The domain of M must be a sub-spec of S (not just signature inclusion; 
 also axioms etc.), otherwise it is an error.
 
 S' is obtained as follows:
 
   S' = M(S - dom(M)) U cod(M)
 
 What this means is that we take S, and we remove the domain of M from it 
 (which, as required above, must be a portion of S): this is S - dom(M), 
 which in general is not a spec, but a fragment. Next, we apply the 
 morphism M to this fragment (of course, if M sends each name to itself 
 there's no change). Finally, we union the result with the codomain of M.
 
 An important detail is that union semantics is required. This is best 
 seen through an example:
 
 Maps = spec ...
 
 A = spec { }
 
 B = spec {
    import A
    import Maps
 }
 
 A' = spec {
    import Maps
 }
 
 B' = substitute (B, morphism A -> A' {})
 
 According to the above semantics, B' contains just one copy of Maps.
 
 This means that we can't just implement it as a pushout of
 
   A -----> B
   |
   |
   |
   V
   A'
 
 because since Maps is not in A, the pushout would give two copies of Maps.
 
 Why do we want union semantics for this substitution operation? For the 
 same reason why we wanted union semantics for import. Been there, 
 discussed that.
 
 As a side note, in Specware 2, or at least in Srinivas's paper on 
 pspecs, there was provision for the case when the body of a pspec needs 
 to share something with the actual parameter of the instantiation, but 
 not with the formal parameter of the pspec. There was a baroque 
 construction that I can't even draw in ASCII, where basically the shared 
 spec SH was drawn above and to the left of the A in the diagram above, 
 and there were two extra arrows, one from SH to B, the other from SH to 
 A'. Pspec refinement was also designed to possibly take SH into account, 
 with an extra arrow going down to a refined SH', yielding a fairly 
 complicated 3D diagram, with certain commutativity conditions, etc. etc.
 

From Lindsay:
 Perhaps it would have been a simpler presentation in the slice category 
 over SH. The formal parameter lifts in a canonical way into an object in 
 the slice. Then I think ts looks like any other pushout square. Perhaps 
 this suggests having something in the syntax (eg a variant of import), 
 that indicates the context of a spec that can be shared). This has been 
 discussed before.
 
 I'm not suggesting that things should be implemented that way nor do I 
 think it is the right way to explain it to NSA people (nor anybody else) 
 but I find the pushout much easier to understand than the full blown 
 set-theoretic explanation. One is forced to be precise about what is 
 being shared and the relationships between the respective specs. I 
 suspect most people see it differently.

From  AC :
 As mentioned above, A is a sub-spec of S (not just signature inclusion; 
 also axioms etc.). Thus, proof obligations for that (implicit) morphism 
 are trivial and need not be generated.

From Lambert
 
 On second thoughts, for roughly the same kind of reason why it is useful
 to use a morphism for the "control" parameter of the operation, it may
 be useful to have the substitution operation return a morphism (with,
 in the above parlance, domain S and codomain S').  For example, I can
 imagine something like
 
    M' = substitute(S,M)
    M" = substitute(T,M')
 
 where T imports S.  (The "Design Decisions" document suggests a way to
 retrieve M' from S and S', which however requires white magic.)
 
 Perhaps we can have some rule that a morphism can be "coerced" to its
 codomain when a spec is expected, reminiscent of the way a cocone is
 coerced to its apex in the diction "colimit of ...".

From AC
 
 It's conceivable, but:
 
 1) I'd definitely hate to write cod(substitute(S,M)) to get S';
 
 2) the coercion of a colimit to an apex is expected, but I don't see any 
 intrinsic, general reason why a morphism should be coerced to its 
 codomain as opposed to its domain, since a morphism is a triple 
 <dom,cod,map>... In a colimit, there is one spec and a bunch of 
 morphisms from the diagram, so it seems more natural to coerce to a 
 spec. Is there a reason why the codomain of a morphism should be 
 preferred to its domain? (maybe there is one)

From Lindsay:
 would also make sense for translate to return a morphism instead of a 
 spec .. and here again it would make sense to coerce that morphism to 
 its codomain when a spec is expected.
 
 translate S <some map>  = S to S <some map>
 
 Also seems like there would be occasions when we might want to coerce a 
 spec to a morphism (the identity).

From Lambert
 
 In this case, yes :)  In general, I think there is a certain
 human tendency to think in terms of destination in preference
 to origin; e.g. if someone says "The train that just passed by
 was the Paris train", you'd assume they meant the train TO
 Paris.
 
 But, a coercion as suggested is incompatible with the untyped
 "VAR = TERM" notation of the present spec "calculus": nothing
 is "expected" of the term.
 
 So, although I expect that it is desirable that users can have
 access to the "substitute morphism", we'll have to think of
 some other way of making it available.
 
   get the morphism of the substitute of the spec S
       by the library morphism called SetsAsListsRef ?

From Lindsay
 Don't see what you mean? why is it untyped? When TERM is evaluated, it 
 is assigned a type: spec, morphism, diagram etc?
 
 I'm missing something.

From AC
 We can have:
 
   S' = substitute(S,M)
   M' = substitute_morph(S,M)


From JLM
 I think natural language intuitions are at best subtle and at worst
 confounding here.
 
 But I also think we should try to be sensitive to the NL intuitions of
 readers.
 
 Having said all that, I came to the conclusion back in NASL days that it
 made sense to coerce a morphism to the codomain if the context was
 clear.   E.g. I assumed that "translation of X by {....}" returned a
 morphism, and "import translation of X by {...}" imported the codomain
 of that morphism.  In retrospect I might have been influenced by NL
 ambiguities with "translation" being either a process or a result, but I
 still think it seems reasonable.
 
 Consider "import [cod of] M;N;P;Q" .  In this case I think it's a bit
 jarring to leave out "cod of", but one quickly deduces the obvious
 meaning.
 Given "import [cod of] translation of X by {a |-> b}", it seems
 pendantic to include "cod of", but programmers are used to adhering to
 pendantic rules.  Making it optional, with perhaps a style-guide, seems
 like a good compromise.
*)
