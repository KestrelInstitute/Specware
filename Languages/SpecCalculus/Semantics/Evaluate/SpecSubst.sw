(** Substitution (Prototype) **)

(* Dialog about adding this feature is at end of file *)

SpecCalc qualifying spec
  import /Library/Legacy/DataStructures/ListUtilities % for listUnion
  import Translate                                    % for auxTranslateSpec
  import SpecUnion                                    % for specUnion

  op applySpecMorphismSubstitution    : Morphism -> Spec -> SCTerm -> Position -> SpecCalc.Env Spec
  op auxApplySpecMorphismSubstitution : Morphism -> Spec -> SCTerm -> Position -> SpecCalc.Env Spec

  def applySpecMorphismSubstitution sm original_spec sm_tm term_pos =
    let sub_spec             = SpecCalc.dom sm in
    let should_be_empty_spec = subtractSpec sub_spec original_spec in
    let sorts_msg = printNamesInAQualifierMap should_be_empty_spec.sorts in
    let ops_msg   = printNamesInAQualifierMap should_be_empty_spec.ops   in
    let props_msg = (foldl (fn (el,str) ->
			    case el of
			      | Property(_, prop_name, _, _) ->
			        if str = "" then printQualifiedId(prop_name)
				  else str^", "^printQualifiedId(prop_name)
			      | _ -> str) % Should check other items?
		       ""			 
		       should_be_empty_spec.elements)
    in
    case (sorts_msg, ops_msg, props_msg) of
      | ("", "", "") ->
        auxApplySpecMorphismSubstitution sm original_spec sm_tm term_pos
      | _ ->
	raise (TypeCheck (term_pos, warnAboutMissingItems sorts_msg ops_msg props_msg))

  def auxApplySpecMorphismSubstitution sm spc sm_tm position = 
    %% Warning: this assumes that dom_spec is a subspec of spc
    %%    S' = M(S - dom(M)) U cod(M)
    let dom_spec           = SpecCalc.dom sm            in     % dom(M)
    let dom_spec_term      = case sm_tm of
			       | (SpecMorph (dom_spec_tm,_,_),_) -> 
				  dom_spec_tm
			       | _ -> 
				 %% sm_tm could be a UnitId, which isn't very helpful
				 %% in which case, see if sm cached a term used to construct it
				 case sm.sm_tm of
				   | Some (SpecMorph (dom_spec_tm,_,_),_) -> dom_spec_tm
				   | _ -> 
				     %% TODO: determine true timestamp and dependencies
				     let dom_value_info = (Spec dom_spec, oldestTimeStamp, []) in
				     (Quote dom_value_info, sm_tm.2) % could check cache first

    in
    let cod_spec           = SpecCalc.cod sm            in     % cod(M)
    let cod_spec_term      = case sm_tm of
			       | (SpecMorph (_,cod_spec_tm,_),_) -> 
				  cod_spec_tm
			       | _ -> 
				 %% sm_tm could be a UnitId, which isn't very helpful
				 %% in which case, see if sm cached a term used to construct it
				 case sm.sm_tm of
				   | Some (SpecMorph (_,cod_spec_tm,_),_) -> cod_spec_tm
				   | _ -> sm_tm
    in
    %% S - dom(M)

    let residue = subtractSpecLeavingStubs (spc, sm_tm, dom_spec, dom_spec_term, cod_spec, cod_spec_term) in
    {
     translated_residue <- applySpecMorphism sm residue position;  % M(S - dom(M))
     %% Add the elements separately so we can put preserve order
     new_spec <- specUnion [translated_residue, cod_spec << {elements = []}];     % M(S - dom(M)) U cod(M)
     new_spec <- return (removeDuplicateImports
			 (new_spec << {elements = 
				       replaceImportStub (new_spec.elements,
							  Import(cod_spec_term, cod_spec, cod_spec.elements))}));
     return new_spec
     }

  %% Version of subtractSpec that leaves stubs of replaced imports so that targets can be replaced at
  %% The same place as originals. 
  op  subtractSpecLeavingStubs: Spec * SCTerm * Spec * SCTerm * Spec * SCTerm -> Spec
  def subtractSpecLeavingStubs (spc, sm_tm, dom_spec, dom_spec_term, cod_spec, cod_spec_term) = 
    let import_dom_spec = Import (dom_spec_term, dom_spec, []) in    
    let 
      def revise_elements elements =
	map (fn el ->
	     case el of
	       | Import (tm, spc, import_elts) ->
	         if sameSpecElement? (el, import_dom_spec) then
		   Import (cod_spec_term, cod_spec, [])
		 else if existsSpecElement? (fn el -> sameSpecElement? (el, import_dom_spec)) import_elts then
		   Import ((Subst (tm, sm_tm), noPos),
			   cod_spec, 
			   revise_elements import_elts)
		 else
		   el % Import (tm, spc, [])
	       | _ -> 
		 el)
	    elements
    in
    spc << {
	    elements = revise_elements       spc.elements,
	    ops      = mapDiffOps            spc.ops       dom_spec.ops,
	    sorts    = mapDiffSorts          spc.sorts     dom_spec.sorts
	   }

  %% 
  op  replaceImportStub: SpecElements * SpecElement -> SpecElements
  def replaceImportStub (elements, new_import) =
    let 
      def revise_elements elements =
	map (fn el ->
	     case el of
	       | Import (tm, spc, imported_elements) ->
	         if imported_elements = [] && sameSpecElement? (el, new_import) then
		   new_import
		 else if existsSpecElement? (fn imported_element -> 
					     sameSpecElement? (imported_element, new_import)) 
		                            imported_elements 
			then
		   Import (tm, spc, revise_elements imported_elements)
		 else
		   el
	       | _ ->
		 el)
	    elements
    in
      revise_elements elements

  op  convertIdMap: QualifiedIdMap -> AQualifierMap (QualifiedId * Aliases)
  def convertIdMap m =
    foldMap (fn op_renaming -> fn (Qualified (dom_qualifier, dom_id)) -> fn cod_qid ->
	     insertAQualifierMap (op_renaming, dom_qualifier, dom_id, (cod_qid, [cod_qid])))
      emptyAQualifierMap m

  op  applySpecMorphism : Morphism -> Spec -> Position -> Env Spec 
  def applySpecMorphism sm spc position =
   %% The opMap and sortMap in sm are PolyMap's  :  dom_qid -> cod_qid
   %% but auxTranslateSpec wants AQualifierMap's :  dom_qid -> (cod_qid, cod_aliases)
   %%  so we first convert formats...
   let renamings = {
		    op_renaming     = convertIdMap (opMap   sm),
		    sort_renaming   = convertIdMap (sortMap sm),
		    other_renamings = None
		   }
   in
   %% Note that auxTranslateSpec is not expected to raise any errors.
     auxTranslateSpec spc renamings None position
    
  %% ======================================================================  
  %%  Error handling...
  %% ======================================================================  

  def warnAboutMissingItems sorts_msg ops_msg props_msg =
    %% At least one of the messages should be non-empty
    "\n" ^
    (if sorts_msg = "" then 
       ""  
     else
       "  These sorts from the domain of the morphism are not in the source spec: " ^ sorts_msg ^ "\n")
    ^
    (if ops_msg = "" then 
       ""  
     else
       "  These ops from the domain of the morphism are not in the source spec: " ^ ops_msg  ^ "\n")
    ^
    (if props_msg = "" then 
       ""  
     else
       "  These axioms, etc. from the domain of the morphism are not in the source spec: " ^ props_msg  ^ "\n")
    ^
    "  in substitution term"


  op printNamesInAQualifierMap : fa (a) AQualifierMap a -> String
  def printNamesInAQualifierMap qmap =
    foldriAQualifierMap (fn (qualifier, id, _, str) ->
			 let qid = printQualifierDotId (qualifier, id) in
			 if str = "" then qid else str^", "^qid)
                        ""
			qmap 

%%%  %% As of 11/18/02, no one uses this...
%%%  op countKeysInAQualifierMap : fa (a) AQualifierMap a -> Nat
%%%  def countKeysInAQualifierMap qmap =
%%%    foldriAQualifierMap (fn (_, _, _, n) -> n + 1) 0 qmap


endspec

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
 this suggests having something in the syntax (eg a variant of import, 
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
    M'' = substitute(T,M')
 
 where T imports S.  (The "Design Decisions" document suggests a way to
 retrieve M' from S and S', which however requires white magic.)
 
 Perhaps we can have some rule that a morphism can be "coerced" to its
 codomain when a spec is expected, reminiscent of the way a cocone is
 coerced to its apex in the diction "colimit of ...".

From AC
 
 It's conceivable, but:
 
 (1) I'd definitely hate to write cod(substitute(S,M)) to get S';
 
 (2) the coercion of a colimit to an apex is expected, but I don't see any 
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
 
 In this case, yes ( :)  In general, I think there is a certain
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