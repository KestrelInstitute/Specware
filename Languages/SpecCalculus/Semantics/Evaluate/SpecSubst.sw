%% Substitution (Prototype)
%% Dialog about adding this feature is at end of file

SpecCalc qualifying spec

import /Library/Legacy/DataStructures/ListUtilities  % for listUnion
import Translate                                     % for auxTranslateSpec
import SpecUnion                                     % for specUnion
import /Languages/MetaSlang/Specs/SubtractSpec       % for subtractSpec
import /Languages/SpecCalculus/Semantics/Evaluate/Obligations % SCTerm addMorphismTheorems
import /Languages/MetaSlang/CodeGen/DebuggingSupport % compressWhiteSpace

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op verify_subspec (dom_spc : Spec) 
                  (spc     : Spec) 
                  (sm_tm   : SCTerm) 
                  (spec_tm : SCTerm)
                  (pos     : Position)
 : SpecCalc.Env () =
 let should_be_empty_spec = subtractSpec1 dom_spc spc true                       in
 let types_msg            = printNamesInAQualifierMap should_be_empty_spec.types in
 let ops_msg              = printNamesInAQualifierMap should_be_empty_spec.ops   in
 let 
   def aux (elts, types, ops, props) =
     foldl (fn ((types, ops, props), el) ->
              case el of
                | Type     (qid,          _) -> (if qid in? types then types else types ++ [qid], ops, props)
                | TypeDef  (qid,          _) -> (if qid in? types then types else types ++ [qid], ops, props)
                | Op       (qid,_,        _) -> (types, if qid in? ops then ops else ops ++ [qid],     props)
                | OpDef    (qid,_,_,      _) -> (types, if qid in? ops then ops else ops ++ [qid],     props)
                | Property (_, qid, _, _, _) -> (types, ops, if qid in? props then props else props ++ [qid])
                | Import   (_,_,elts,     _) -> aux (elts, types, props, ops)
                | _ -> (types, ops, props))
           (types, ops, props)
           elts
 in
 let (type_ids, op_ids, prop_ids) = aux (should_be_empty_spec.elements, [], [], []) in
 case (types_msg, ops_msg) of
   | ("", "") ->
     let _ = 
         (case (type_ids, op_ids, prop_ids) of
            | ([], [], []) -> ()
            | _ ->
              let _ = writeLine ("------------------------------------------") in 
              let _ = writeLine ("ERROR: for now, ignoring these problems:") in
              let _ = writeLine (warnAboutMissingItems "" "" type_ids op_ids prop_ids sm_tm spec_tm) in
              let _ = writeLine ("------------------------------------------") in 
              ())
     in
     return ()
   | _ ->
     let msg = warnAboutMissingItems types_msg ops_msg type_ids op_ids prop_ids sm_tm spec_tm in
     raise (TypeCheck (pos, msg))

op applySpecMorphismSubstitution (sm            : Morphism) 
                                 (original_spec : Spec)
                                 (sm_tm         : SCTerm) 
                                 (spec_tm       : SCTerm) 
                                 (term_pos      : Position) 
 : SpecCalc.Env Spec =
 {
  verify_subspec (SpecCalc.dom sm) original_spec sm_tm spec_tm term_pos;
  auxApplySpecMorphismSubstitution sm original_spec sm_tm term_pos
 }

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op liftSpecTerm(tm: SCTerm, par: SCTerm): SCTerm =
 case (tm, par) of
   | ((UnitId(UnitId_Relative{path = [rel_name], hashSuffix = None  }), pos),
      (UnitId(UnitId_Relative{path = par_path,   hashSuffix = Some _}), _)) ->
     (UnitId(UnitId_Relative{path = par_path, hashSuffix = Some rel_name}), pos)
   | _ -> tm

op auxApplySpecMorphismSubstitution (sm    : Morphism)
                                    (spc   : Spec)
                                    (sm_tm : SCTerm)
                                    (pos   : Position)
 : SpecCalc.Env Spec =
 if sm.dom = spc then
   return (addMorphismTheorems sm.cod sm)
 else
   %% Warning: this assumes that dom_spec is a subspec of spc
   %%    S' = M(S - dom(M)) U cod(M)
   let dom_spec           = SpecCalc.dom sm            in     % dom(M)
   let dom_spec_term      = case sm_tm of
                              | (SpecMorph (dom_spec_tm,_,_,_),_) -> 
                                dom_spec_tm
                              | _ -> 
                                %% sm_tm could be a UnitId, which isn't very helpful
                                %% in which case, see if sm cached a term used to construct it
                                case sm.sm_tm of
                                  | Some (SpecMorph (dom_spec_tm,_,_,_),_) -> dom_spec_tm
                                  | _ -> 
                                    %% TODO: determine true timestamp and dependencies
                                    let dom_value_info = (Spec dom_spec, oldestTimeStamp, []) in
                                    (Quote dom_value_info, sm_tm.2) % could check cache first
                                    
   in
   let cod_spec           = SpecCalc.cod sm            in     % cod(M)
   let cod_spec_term      = case sm_tm of

                              | (SpecMorph (_,cod_spec_tm,_,_),_) -> 
                                %% Given a normal spec morphism term, just extract the codomain spec term.
                                cod_spec_tm 

                              | (Quote (Morph sm, ts, uids), pos) ->  
                                %% Given a quoted spec morphism, build a quoted spec of the codomain.
                                (Quote (Spec sm.cod, ts, uids), pos)

                              | _ -> 
                                %% Given an obscure sm_tm (e.g. a UnitId), see if it contains a term used 
                                %% to construct it, in which case deconstruct that as above.
                                case sm.sm_tm of
                                  | Some (SpecMorph (_,cod_spec_tm,_,_),_) ->
                                    liftSpecTerm (cod_spec_tm, sm_tm)
                                  | Some (Quote (Morph sm, ts, uids), pos) ->  
                                    (Quote (Spec sm.cod, ts, uids), pos)
                                  | _ -> 
                                    %% Give up -- cite the morphism term as the import target
                                    sm_tm
   in
   %% S - dom(M)

   {spec_replacements <- findSubSpecReplacements(dom_spec, cod_spec);
    spec_replacements <- return((dom_spec, sm_tm, cod_spec, cod_spec_term) :: spec_replacements);
    % print("orig spec:\n"^printSpecFlat spc^"\n");
    residue <- return(subtractSpecLeavingStubs (spc, 
                                                sm_tm, 
                                                dom_spec, 
                                                dom_spec_term, 
                                                cod_spec, 
                                                cod_spec_term,
                                                spec_replacements));
    % print("residue spec:\n"^printSpecFlat residue^"\n");
    translated_residue <- applySpecMorphism sm residue;  % M(S - dom(M))
    % print("translated residue spec:\n"^printSpecFlat translated_residue^"\n");
    %% Add the elements separately so we can put preserve order
    new_spec <- specUnion [cod_spec << {elements = []}, translated_residue] pos;     % M(S - dom(M)) U cod(M)
    new_spec <- return (new_spec << {elements = 
                                       replaceImportStub (new_spec.elements,
                                                          Import (cod_spec_term, cod_spec, cod_spec.elements, noPos))});
    % print("reconstructed spec:\n"^printSpecFlat translated_residue^"\n");
    new_spec <- return (removeDuplicateImports new_spec);
    % print("slimmed spec:\n"^printSpecFlat translated_residue^"\n");
    new_spec <- return (markQualifiedStatus new_spec);
    new_spec <- return (removeVarOpCaptures    new_spec);
    %% new_spec <- return (compressDefs           new_spec);
    new_spec <- complainIfAmbiguous new_spec pos;
    new_spec <- return(addMorphismTheorems new_spec sm);
    return new_spec
    }

op findSubSpecReplacements (dom_spec: Spec, cod_spec: Spec) 
 : SpecCalc.Env (List (Spec * SCTerm * Spec * SCTerm)) =
 let sub_morphisms =
     foldlSpecElements (fn (result, el1) ->
                          case el1 of
                            | Import ((Subst (spc_tm, sm_tm, pragmas), _), spc, _, _) ->
                              let new = (sm_tm, spc) in
                              if new in? result then 
                                result
                              else 
                                new :: result
                            | _ -> result)
                       [] 
                       cod_spec.elements
 in
 mapM (fn (sm_tm, spc) ->
         {saveUID                         <- setCurrentUIDfromPos (positionOf sm_tm) ;      % Better than nothing -- scheme needs rethinking
          sm_info as (Morph sm, ts, uids) <- evaluateTermInfo sm_tm;
          setCurrentUID saveUID;
          cod_spc                         <- return(SpecCalc.cod sm);
          % print(printSpec cod_spc);
          cod_value_info                  <- return(Spec(SpecCalc.cod sm), ts, uids);
          return (SpecCalc.dom sm, 
                  (Quote sm_info, sm_tm.2), 
                  cod_spc, 
                  (Quote cod_value_info, sm_tm.2))})
      sub_morphisms

%% Version of subtractSpec that leaves stubs of replaced imports so that targets can be replaced at
%% The same place as originals. 
%% The top? parameter in these two functions is to ensure the substitution is done on
%% the immediate imports so that the correct Subst terms can be constructed, but below that
%% it is probably not necessary and would involve exponential work without caching

op subtractSpecLeavingStubs (spc               : Spec, 
                             sm_tm             : SCTerm, 
                             dom_spec          : Spec, 
                             _                 : SCTerm, 
                             cod_spec          : Spec, 
                             cod_spec_term     : SCTerm, 
                             spec_replacements : List (Spec * SCTerm * Spec * SCTerm)) 
 : Spec =
 let 
   def revise_elements elements top? =
     map (fn el ->
            case el of
              | Import (tm, spc, import_elts, pos) ->
                % let _ = writeLine("r_e: "^show top?^"\n"^anyToPrettyString el) in
                (case findLeftmost (fn (dom_spec, sm_tm, cod_spec, cod_spec_term) -> spc = dom_spec) spec_replacements of
                   | Some(dom_spec, sm_tm, cod_spec, cod_spec_term) -> Import (cod_spec_term, cod_spec, [], pos)
                   | None ->
                     case findLeftmost (fn (dom_spec, sm_tm, cod_spec, cod_spec_term) ->
                                          existsSpecElement? (fn el -> 
                                                                case el of
                                                                  | Import (tm, spc, _, _) -> spc = dom_spec 
                                                                  | _ -> false)
                                            (if top? then spc.elements else import_elts))
                            spec_replacements
                       | Some (dom_spec, sm_tm, cod_spec, cod_spec_term) ->
                         let new_spec = if top? then
                                          spc << {elements = revise_elements spc.elements false}
                                        else 
                                          spc 
                         in
                         Import ((Subst (tm, sm_tm, []), noPos),
                                 new_spec,
                                 revise_elements import_elts top?, 
                                 pos)
                       | _ -> Import (tm, spc, import_elts, pos))   %  el     % Import (tm, spc, [])
              | _ -> el)
         elements
 in
 spc << {
         types    = mapDiffTypes          spc.types     dom_spec.types,
         ops      = deleteChangedOpinfos  spc.ops       dom_spec.ops cod_spec.ops,  % Old: mapDiffOps   spc.ops       dom_spec.ops, 
         elements = revise_elements       spc.elements  true
         }

%% Ideally we don't want to modify any ops that are the same in source and target specs
op deleteChangedOpinfos(orig_ops: OpMap) (source_ops: OpMap) (target_ops: OpMap): OpMap =
 mapiPartialAQualifierMap (fn (q, id, op_info) ->
                             case findAQualifierMap (source_ops, q, id) of
                               | None -> Some op_info
                               | Some src_info ->
                                 if ~(equalTerm? (op_info.dfn, src_info.dfn)) then 
                                   Some op_info
                                 else
                                   case findAQualifierMap (target_ops, q, id) of
                                     | Some trg_info | trg_info = src_info -> Some op_info
                                     | _ -> None)
   orig_ops

op replaceImportStub (elements   : SpecElements, 
                      new_import : SpecElement) 
 : SpecElements =
 let Import (new_import_tm, new_import_spc, _, _) = new_import in
 let 
   def revise_elements elements top? =
     map (fn el ->
            case el of
              | Import (tm, spc, import_elts, pos) ->
                if import_elts = [] && spc = new_import_spc then
                  new_import
                else if existsSpecElement? (fn imported_element -> 
                                              case imported_element of
                                                | Import (import_tm, spc, import_elts, _) ->
                                                  import_elts = [] && spc = new_import_spc
                                                | _ -> false)
		                           (if top? then spc.elements else import_elts) 
                       then
                         let new_elts = revise_elements import_elts top? in
                         let new_elts = if top? then
                                          revise_elements spc.elements false
                                        else 
                                          new_elts
                         in
                         Import (tm,
                                 spc << {elements = new_elts},
                                 new_elts, pos)
                     else 
                       el
	       | _ -> el)
	    elements
 in
 revise_elements elements true

op convertIdMap (m : QualifiedIdMap) : AQualifierMap (QualifiedId * Aliases) =
 foldMap (fn translator -> fn (Qualified (dom_q, dom_id)) -> fn cod_qid ->
            insertAQualifierMap (translator, dom_q, dom_id, (cod_qid, [cod_qid])))
         emptyTranslator
         m

op convertOpIdMap (m : QualifiedIdMap, spc: Spec): OpTranslator =
 foldMap (fn translator -> fn (Qualified (dom_q, dom_id)) -> fn cod_qid ->
            let fixity = case findTheOp(spc, cod_qid) of
                           | Some opinfo -> opinfo.fixity
                           | None -> Unspecified
            in
            insertAQualifierMap (translator, dom_q, dom_id, (cod_qid, [cod_qid], fixity)))
         emptyOpTranslator
         m

op applySpecMorphism (sm : Morphism) (spc : Spec) : Env Spec =
 %% The opMap and typeMap in sm are PolyMap's  :  dom_qid -> cod_qid
 %% but auxTranslateSpec wants AQualifierMap's :  dom_qid -> (cod_qid, cod_aliases)
 %%  so we first convert formats...
 let op_translator   = convertOpIdMap (opMap sm, cod sm) in
 let prop_translator = opToPropTranslator op_translator in  % TODO: fix evil hack
 let translators = {
                    ambigs = emptyTranslator,
                    types  = convertIdMap (typeMap sm),
                    ops    = op_translator,
                    props  = prop_translator,
                    others = None
                    }
 in
 %% Note that auxTranslateSpec is not expected to raise any errors.
 runMemoMonad (auxTranslateSpec spc translators None None)
    
%% ======================================================================  
%%  Error handling...
%% ======================================================================  

def warnAboutMissingItems types_msg ops_msg type_ids op_ids prop_ids sm_tm spec_tm =
  %% At least one of the messages should be non-empty
  "\n" ^
  (if types_msg = "" then 
     ""  
   else
     "  These types from the domain of the morphism are not in the source spec: " ^ types_msg ^ "\n")
  ^
  (if ops_msg = "" then 
     ""  
   else
     "  These ops   from the domain of the morphism are not in the source spec: " ^ ops_msg  ^ "\n")
  ^
  (if type_ids = [] then
     ""  
   else
     "  These types from the domain of the morphism are defined differently in the source spec: " ^ 
     (foldl (fn (s,qid) -> (if s = "" then "" else s ^ ", ") ^ printQualifiedId qid) "" type_ids)
     ^ "\n")
  ^
  (if op_ids = [] then
     ""  
   else
     "  These ops   from the domain of the morphism are defined differently in the source spec: " ^ 
     (foldl (fn (s,qid) -> (if s = "" then "" else s ^ ", ") ^ printQualifiedId qid) "" op_ids)
     ^ "\n")
  ^
  (if prop_ids = [] then 
     ""  
   else
     "  These axioms, etc. from the morphism domain are not in the source spec: " ^ 
     (foldl (fn (s,qid) -> (if s = "" then "" else s ^ ", ") ^ printQualifiedId qid) "" prop_ids)
     ^ "\n")
  ^
  "\n  in " ^ showSCTerm spec_tm ^ "[" ^ showSCTerm sm_tm ^ "]" ^
  "\n  at " ^ compressWhiteSpace (printAll spec_tm.2)

op [a] printNamesInAQualifierMap (qmap : AQualifierMap a) : String =
 foldriAQualifierMap (fn (qualifier, id, _, str) ->
                        let qid = printQualifierDotId (qualifier, id) in
                        if str = "" then qid else str^", "^qid)
                     ""
                     qmap 
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
