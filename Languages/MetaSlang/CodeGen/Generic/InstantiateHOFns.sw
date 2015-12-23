(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

InstantiateHO qualifying
spec
 import /Languages/MetaSlang/Transformations/Simplify
 import /Languages/MetaSlang/Transformations/CurryUtils
 import /Languages/MetaSlang/Specs/AnalyzeRecursion
 import /Languages/MetaSlang/Specs/MSTerm

% op CodeGenTransforms.stripSubtypesAndBaseDefs (spc : Spec) (typ : MSType) : MSType  % in CodeGenTransforms

 % type Term    = MS.Term  % disambiguate from SpecCalc.Term
 % type MS.Type = MS.Type  % also have JGen.Type and MetaslangProofChecker.Type (sigh)

 %% (params, defn body, indices of applied fn args, curried?, recursive?)
 type DefInfo = MSPatterns * MSTerm * MSType * List Nat * Bool * Bool

(*
 * calling pattern: 
 *
 * instantiateHOFns 
 *   aux_instantiateHOFns
 *
 *     normalizeCurriedDefinitions
 *       normalizeCurriedDefn
 *
 *     makeUnfoldMap
 *
 *       HOFnType?
 *       HOType?
 *       analyzeCurriedDefn
 *       analyzeUnCurriedDefn
 *         analyzeDefn
 *           indices_for
 *           recursiveCallsPreserveHOParameters?
 *             indices_for *
 *             HOParamsSame?
 *               indices_for *
 *               patternMatchesTerm?
 *                 lookupId
 *
 *     unFoldTerms
 * 
 *       mapSpecNotingOpNames 
 *         mapSpecOpsNotingName
 *
 *       maybeUnfoldTerm 
 *         getTupleArg
 *         exploitableTerm?
 *
 *         makeUnfoldedTerm
 * 
 *           matchPairs
 *             lookupId *
 *
 *           makeRecursiveLocalDef
 *             locallyUniqueName
 *               idReferenced?
 *             unfoldInTerm
 *               maybeUnfoldTerm *
 *
 *           adjustBindingsToAvoidCapture
 *
 *           makeLet
 *
 *           simplifyUnfoldCase 
 *             tryUnfold
 *               typeMatch
 *                 matchL
 *             patternMatchRulesToLet 
 *
 *           unfoldInTerm *
 * 
 *)

 %% ================================================================================
 %% instantiate higher order functions
 %% ================================================================================

 op SpecTransform.instantiateHOFns (spc : Spec) : Spec =
   aux_instantiateHOFns spc false

 %% snark interface can call this directly to set flag to true
 op aux_instantiateHOFns (spc : Spec) (snark_hack? : Bool) : Spec =
   (*
    * Some context:
    *
    * The objective here is to inline explicit functional arguments that have 
    * been passed to routines such as map.
    *
    * For example, map has an executable definition in List_Executable.sw, 
    * as follows:
    *
    *  refine def [a,b] map (f: a -> b) (l: List a): List b =
    *    reverse (foldl (fn (result, x) -> f x::result) [] l)
    *
    * Note that not much can be done to optimize an expression such as this:
    *
    *  'fn (f : X -> Y, l : List X) -> ... (map f l) ...',
    *
    * However, the following expression contains an explicit functional argument
    * (namely '(fn n -> g n)') which can be inlined and simplified if we expand 
    * the call to map:
    *
    *  'fn l -> ... (map (fn n -> g n) l) ...'
    *    
    *     =>
    *    
    *  'fn l -> ... (reverse (foldl (fn (result, x) -> ((fn n -> g n) x))::result) [] l)) ...'
    * 
    *    simplifying to:
    *    
    *  'fn l -> ... (reverse (foldl (fn (result, x) -> (g x)::result) [] l)) ...'
    * 
    * In doing this, we must be careful to avoid all the usual pitfalls associated
    * with substitutions, to ensure that (unfortunately perverse) expressions such 
    * as the following will expand properly:
    * 
    *  'fn (f: List X) -> ... (map (fn n -> g n) f) ...'
    * 
    * The danger to avoid is conflation of the 'f' (of type 'List X') from our 
    * expression here with the 'f' (of type 'a -> b') from the definition of map.
    *
    * Such conflations can lead to nonsense, e.g, the 'f' from the definition of map 
    * will be replaced by '(fn n -> g n)', but then the 'f' in our expression 
    * could also be bound [erroneously] to the same value, producing gibberish:
    * 
    *   (reverse (foldl (fn (result, x) -> (g x)::result)
    *                   []
    *                   (fn n -> g n)))  % gibberish
    *
    * Note that such gibberish is created after the type-checker has run, 
    * so it will not be detected staticly, thus silently leading to bogus code.
    *
    * The moral is that this code needs to be very carefully vetted.
    *)
   let spc = normalizeCurriedDefinitions spc             in
   let spc = simplifySpec                spc             in
   let mp  = makeUnfoldMap               spc snark_hack? in
   let result = unFoldTerms (spc, mp) in
   result

 %% ================================================================================
 %% normalize 
 %% ================================================================================

 op normalizeCurriedDefinitions (spc : Spec) : Spec =
   let normOps =
       mapiAQualifierMap 
         (fn (q, id, info) ->
            let pos                   = termAnn            info.dfn in
            let (old_decls, old_defs) = opInfoDeclsAndDefs info     in
            case old_defs of
              | [] -> info
              | _ ->
                let new_defs =
                    map (fn dfn ->
                           let pos              = termAnn         dfn in
                           let (tvs, typ, def1) = unpackFirstTerm dfn in
                           let numCurryArgs     = curryShapeNum   (spc, typ) in
                           let arg_types        = curryArgTypes   (spc, typ) in
                           let normDef1         = normalizeCurriedDefn (def1, arg_types) in
                           maybePiTerm (tvs, TypedTerm (normDef1, typ, pos)))
                        old_defs
                in
                info << {dfn = maybeAndTerm (old_decls ++ new_defs, pos)})
         spc.ops
   in 
   setOps (spc, normOps)

 op normalizeCurriedDefn (dfn : MSTerm, curry_arg_types : MSTypes) : MSTerm =
   let 
     def 
       aux (dfn, curry_arg_types, arg_num) = 
         case curry_arg_types of

           | [] -> dfn

           | arg_type :: remaining_types ->
             case dfn of

               | Lambda([(pat, pred, body                                    )], a) ->
                 Lambda([(pat, pred, aux (body, remaining_types, arg_num + 1))], a)

               | Lambda _ -> dfn

               | _ ->
                 if arg_num = 0 && remaining_types = [] && product? arg_type then
                   % Uncurried
                   let Product(fields, _) = arg_type in
                   let (vars, _) = foldl (fn ((result, i), (label, typ)) ->
                                            (result ++ [(label, ("xxx-" ^ Nat.show i, typ))],
                                             i+1))
                                         ([], 0) 
                                         fields
                   in
                   mkLambda (mkRecordPat (map (fn (l, v) -> (l, mkVarPat v)) vars),
                             mkApply (dfn,
                                      mkRecord (map (fn (l, v) -> (l, mkVar v)) vars)))
                 else 
                   let nv = ("yyy-" ^ Nat.show arg_num, arg_type) in
                   mkLambda (mkVarPat nv, 
                             aux (mkApply (dfn, mkVar nv), 
                                  remaining_types, 
                                  arg_num + 1))
   in 
   aux (dfn, curry_arg_types, 0)

 %% ================================================================================
 %% make unfold map
 %% ================================================================================

 op makeUnfoldMap (spc : Spec) (snark_hack? : Bool) : AQualifierMap DefInfo =
   let ref_map = opUsesOpsMap spc in
   mapiPartialAQualifierMap
     (fn (q, id, info) -> 
        let (decls, defs) = opInfoDeclsAndDefs info in
        case defs of

          | [] -> None

          | dfn :: _ ->
            let qid = Qualified (q, id) in
            let (tvs, typ, tm) = unpackFirstTerm dfn in
            
            %% would like to remove tvs ~= [] condition but currently causes problem in Snark translation
            let snark_problem? = if snark_hack? then tvs = [] else false in
            if ~ snark_problem? && q nin? dontUnfoldQualifiers
                && HOFnType? (typ, spc) && unfoldable? tm then
              
              let numCurryArgs = curryShapeNum (spc, typ) in
              % see note below about debugging indexing error
              let arg_types = (if numCurryArgs > 1 then
                                 curryArgTypes    (spc, typ)
                               else 
                                 noncurryArgTypes (spc, typ))
              in
              let HOArgs? = map (fn s -> HOType? (s, spc)) arg_types in
              if numCurryArgs > 1 then
                analyzeCurriedDefn   (qid, tm, HOArgs?, typ, ref_map, numCurryArgs)
              else 
                analyzeUnCurriedDefn (qid, tm, HOArgs?, typ, ref_map)
                
            else 
              None)
     spc.ops

op dontUnfoldQualifiers: Ids = ["String"]

 %% has an argument that is HO. Arguments are either curried or product
 op HOFnType? (typ : MSType, spc : Spec) : Bool =
   case arrowOpt (spc, typ) of
     | Some (dom, rng) ->
       HOType? (dom, spc) ||
       (case arrowOpt (spc, rng) of
          | Some _ -> HOFnType? (rng, spc)
          | None ->
            case productOpt (spc, dom) of
              | None -> false
              | Some fields ->
                exists? (fn (_, s) -> arrow? (spc, s)) fields)
     | _ -> false

 op HOType? (typ : MSType, spc : Spec) : Bool =
   case stripSubtypes(spc, typ) of
     | Arrow _ -> true
     | Product (fields, _) ->
       exists? (fn (_, s) -> HOType? (s, spc)) fields
     | _ -> false

 op unfoldCostThreshold   : Nat = 30
 op unfoldHOCostThreshold : Nat = 60
  
 op unfoldable? (dfn : MSTerm) : Bool =
   termCost dfn < unfoldHOCostThreshold

 op sizeTerm (tm : MSTerm) : Nat = 
   foldSubTerms (fn (_, sum) -> sum + 1) 0 tm

 op curryFnTerm?(tm: MSTerm): Bool =
   case tm of
     | Fun _ -> true
     | Apply(fn_tm, _, _) -> curryFnTerm? fn_tm
     | _ -> false

%% Could be made arbitrarily more sophisticated, but want it to be fast
 op termCost (tm : MSTerm) : Nat = 
   foldSubTerms (fn (tm, sum) ->
                   case tm of
                     | Var _ -> sum
                     | Let _ -> sum
                     | IfThenElse _ -> sum
                     | Fun(Op(Qualified(_,monadBind), _), _, _) -> sum + 3
                     | Apply(Lambda _, _, _) -> sum   % With default means case is 1
                     %% No penalty for fully applied curry fn -- would prefer penalty for partially applied fn
                     | Apply(Apply(fn_tm, _, _), _, _) | curryFnTerm? fn_tm -> sum
                     | _ -> sum + 1)
     0 tm


 op analyzeCurriedDefn (qid          : QualifiedId,
                        dfn          : MSTerm,
                        HOArgs?      : List Bool,
                        typ          : MSType,
                        ref_map      : RefMap,
                        numCurryArgs : Nat)
   : Option DefInfo =
   let (params, body) = curriedParams dfn in
   if length params ~= numCurryArgs then 
     None
   else
     let 
       def normalizeCurriedAppl tm =
         case getCurryArgs tm of

           | Some (f as Fun (Op (nqid, _), _, _), args) ->
             if nqid = qid && length args = numCurryArgs then
               mkAppl (f, args)
             else 
               tm

           | _ -> tm
     in
     let normalizedBody = mapSubTerms normalizeCurriedAppl body in
     analyzeDefn (qid, params, normalizedBody, HOArgs?, true, typ, ref_map)

 op analyzeUnCurriedDefn (qid     : QualifiedId,
                          dfn     : MSTerm,
                          HOArgs? : List Bool,
                          typ     : MSType,
                          ref_map : RefMap)
   : Option DefInfo =
   case dfn of

     | Lambda ([(pat, _, body)], _) ->
       analyzeDefn (qid, getParams pat, body, HOArgs?, false, typ, ref_map)

     | _ -> None

 op analyzeDefn (qid      : QualifiedId,
                 params   : MSPatterns,
                 body     : MSTerm,
                 HOArgs?  : List Bool,
                 curried? : Bool,
                 typ      : MSType,
                 ref_map  : RefMap)
   : Option DefInfo =
   if anyTerm? body || nonExecutableTerm1? body then None
   else
   if recursiveCallsPreserveHOParameters? (body, qid, params, HOArgs?, curried?) then
     let patinds = indices_for params in
     % possibly useful to help debug current indexing error that happens with:  proc MatchingProofs
     % Confusion with Functions.o  (possibly because it is typed using Function(a, b) instead of a -> b)
     % let _ = toScreen ("\n:Params  [" ^ (Nat.toString (List.length params))  ^ "]= " ^ (anyToString params) ^ "\n") in
     % let _ = toScreen ("\n:Patinds [" ^ (Nat.toString (List.length patinds)) ^ "]= " ^ (anyToString patinds) ^ "\n") in
     % let _ = toScreen ("\n:HOARgs  [" ^ (Nat.toString (List.length HOArgs))  ^ "]= " ^ (anyToString HOArgs)  ^ "\n") in
     let max_depth = 8 in % TODO: why 8?
     Some (params, 
           body, 
           typ,
           filter (fn i -> HOArgs? @ i) patinds,
           curried?,
           recursiveOp? (qid, ref_map, max_depth))
   else
     None

 op [a] indices_for (l : List a) : List Nat =
   tabulate (length l, id)

 op recursiveCallsPreserveHOParameters? (body     : MSTerm, 
                                         qid      : QualifiedId,
                                         params   : MSPatterns,
                                         HOArgs?  : List Bool,
                                         curried? : Bool)
  : Bool =
  ~ (existsSubTerm
       (fn tm ->
	  case tm of

            | Apply (Fun (Op (inner_qid, _), _, _), args, _) | ~curried? && inner_qid = qid ->
              ~ (HOParamsSame? (params, termList args, HOArgs?))

            | Apply _ | curried? ->
              (case getCurryArgs tm of

                 | Some (Fun (Op (inner_qid, _), _, _), args) | inner_qid = qid ->
                   ~ (HOParamsSame? (params, args, HOArgs?))

                 | _ -> false)

            | _ -> false)
       body)

 op HOParamsSame? (params  : MSPatterns, 
                   args    : MSTerms, 
                   HOArgs? : List Bool)
   : Bool =
   length params >= length args
   && 
   forall? (fn i -> if HOArgs? @ i then
                      patternMatchesTerm? (params @ i, args @ i)
                    else 
                      true)
           (indices_for args)

 op patternMatchesTerm? (pat : MSPattern, tm : MSTerm) : Bool =
   case (pat, tm) of

     | (VarPat ((vpid, _), _), Var ((vid, _), _)) -> 
       vid = vpid
       
     | (RecordPat (pattern_fields, _), Record (term_fields, _)) ->
       forall? (fn (id, pat) -> 
                  patternMatchesTerm? (pat, lookupId (id, term_fields))) 
               pattern_fields
       
     | _ -> false

 op lookupId (id : Id, fields : List (Id * MSTerm)) : MSTerm =
   case findLeftmost (fn (id1, tm) -> id = id1) fields of
     | Some (_, tm) -> tm
     | _ -> fail "lookupId: Shouldn't happen"

 %% ================================================================================
 %% simplify and unfold throughout spec
 %% ================================================================================

 %% Generalize the term->term function in TSP_Maps to a function that creates a 
 %% term->term function.
 type Generalized_TSP_Maps = (QualifiedId -> MSTerm -> MSTerm) * 
                             (MSType      -> MSType)           * 
                             (MSPattern   -> MSPattern)

 op unFoldTerms (spc : Spec, info_map : AQualifierMap DefInfo) : Spec =
   let 
     def aux n tm =
       let result1 = simplify           spc tm      in
       let result2 = simplifyUnfoldCase spc result1 in
       if equalTerm? (tm, result2)
         then tm
       else if n < 20 then      % avoid accidental infinite recursions
         aux (n+1) result2      % Overkill, but doesn't seem too expensive
       else
         let _ = writeLine("unFoldTerms: apparent infinite recursion aborted") in
         let _ = writeLine("tm = " ^ printTerm tm) in
         result2
     def simplifyTerm tm =
       aux 0 tm 
   in
   let gtsp = (fn outer_qid -> 
                 fn tm -> 
                   maybeUnfoldTerm (outer_qid, tm, info_map, simplifyTerm, spc),
               id,
               id)
   in
   mapSpecNotingOpNames gtsp spc

 %% mapSpecNotingOpNames is a variant of mapSpec that allows us to use the name
 %% of an op in the tranformations being done on terms within it.
 %% If necessary, it could be generalized to do something similar for types.

 op mapSpecNotingOpNames (gtsp : Generalized_TSP_Maps) (spc : Spec) : Spec =
   let (make_op_map, typ_map, pat_map) = gtsp in
   let outer_tsp = (make_op_map (mkUnQualifiedId "outside_of_any_op"), typ_map, pat_map) in
   spc << {
	   types    = mapSpecTypes         outer_tsp spc.types,
	   ops      = mapSpecOpsNotingName gtsp      spc.ops,
	   elements = mapSpecProperties    outer_tsp spc.elements
	  }

 op mapSpecOpsNotingName (gtsp : Generalized_TSP_Maps) (ops : AOpMap Position)
   : AOpMap Position =
   let (make_op_map, typ_map, pat_map) = gtsp in
   mapOpInfos (fn info -> 
                 let inner_tsp = (make_op_map (primaryOpName info), typ_map, pat_map) in
                 %% now the the tsp knows the name of the op
                 let new_dfn = mapTerm inner_tsp info.dfn in
                 % let _ = if (primaryOpName info) = Qualified("Size","doTestForSize")
                 %          then writeLine("Orig def:\n"^printTerm info.dfn^"\nNew def:\n"^printTerm new_dfn) else ()
                 % in
                 info << {dfn = new_dfn})
              ops

 %% ================================================================================
 %% unfold
 %% ================================================================================

 op maybeUnfoldTerm (outer_qid    : QualifiedId,
                     tm           : MSTerm,
                     unfold_map   : AQualifierMap DefInfo,
                     simplifyTerm : MSTerm -> MSTerm,
                     spc          : Spec)
   : MSTerm =
   case tm of
     | Apply (f, arg, _) ->
       (case f of
	
	  | Fun (Op (qid as Qualified (q, id), _), typ, _) ->
            %% Uncurried case
	    (case findAQualifierMap (unfold_map, q, id) of
	       | Some (vs, defn, deftyp, fnIndices, curried?, recursive?) ->
		 if ~curried?
                    && length (termList arg) > foldr max 0 fnIndices
		    && exists? (fn i -> exploitableTerm? (getTupleArg (arg, i), unfold_map))
                               fnIndices
                   then
                     % let _ = writeLine("maybeUnfoldTerm:\n"^printTerm f) in
                     makeUnfoldedTerm (outer_qid, 
                                       tm, 
                                       f, 
                                       termToList arg, 
                                       inferType (spc, tm),
                                       typeMatch (deftyp, typ, spc),
                                       vs, 
                                       defn, 
                                       fnIndices, 
                                       recursive?, 
                                       qid, 
                                       id,
                                       unfold_map, 
                                       simplifyTerm, 
                                       false, 
                                       spc)
                 else 
                   tm
               | _ -> 
                 tm)

	  | Apply _ ->
            %% Curried case
	    (case getCurryArgs tm of
	       | Some(f, args) ->
		 (case f of
		    | Fun (Op (qid as Qualified (q, id), _), typ, _) ->
		      (case findAQualifierMap(unfold_map, q, id) of
			 | Some (vs, defn, deftyp, fnIndices, curried?, recursive?) ->
                           % let _ = writeLine("maybeUnfoldTerm:\n"^printTerm f) in
			   if curried? 
                              && (length args = length vs)
                              && exists? (fn i -> exploitableTerm? (args @ i, unfold_map))
			                 fnIndices
                             then 
                               makeUnfoldedTerm (outer_qid, 
                                                 tm, 
                                                 f, 
                                                 args, 
                                                 inferType (spc, tm),
                                                 typeMatch (deftyp, typ, spc),
                                                 vs, 
                                                 defn, 
                                                 fnIndices, 
                                                 recursive?,
                                                 qid,
                                                 id, 
                                                 unfold_map, 
                                                 simplifyTerm, 
                                                 true, 
                                                 spc)
                           else
                             tm
                         | _ -> tm)
		    | _ -> tm)
	       | _ -> tm)
	  | _ -> tm)
     | _ -> tm

 op getTupleArg (tm : MSTerm, i : Nat) : MSTerm =
   case tm of
     | Record (tms, _) -> (tms @ i).2
     | _ -> (if i = 0 then tm else fail("Illegal getTupleArg call"))

 op exploitableTerm? (tm : MSTerm, unfoldMap : AQualifierMap DefInfo) : Bool =
   case tm of
     | Var _ -> false
     | Apply(Fun(Project _, _, _), _, _) -> false
     %% Add other cases?
     | _ -> true

 op termToList (tm : MSTerm) : MSTerms =
   case tm of
     | Record (fields, _) -> map (fn (_, tm) -> tm) fields
     | _ -> [tm]

 %% ================================================================================
 %% The heart of the matter.
 %% Everything else is arranged so that this routine has the right information
 %% to do the appropriate transformations.
 %% ================================================================================

 op makeUnfoldedTerm (outer_qid    : QualifiedId,
                      orig_tm      : MSTerm,
                      f            : MSTerm,
                      args         : MSTerms,
                      result_type  : MSType,
                      tv_subst     : TyVarSubst,
                      params       : MSPatterns,
                      def_body     : MSTerm,
                      fn_indices   : List Nat,
                      recursive?   : Bool,
                      qid          : QualifiedId,
                      nm           : String,
                      unfold_map   : AQualifierMap DefInfo,
                      simplifyTerm : MSTerm -> MSTerm,
                      curried?     : Bool,
                      spc          : Spec)
   : MSTerm =
   % let trace? = outer_qid = Qualified("Size","doTestForSize--") in  % Qualified(UnQualified,"f") in
   % let _ = if trace? then writeLine("makeUnfoldedTerm:\n"^printTerm orig_tm^ "\ndef_body: "^printTerm def_body) else () in
   let replacement_indices = filter (fn i -> constantTerm? (args @ i) && i in? fn_indices)
                                    (indices_for args)
   in
   let p_subst             = foldl (fn (r, i) -> r ++ matchPairs (params @ i, args @ i))
                                   []
                                   replacement_indices
   in
   let remaining_indices   = filter (fn i -> i nin? replacement_indices)
                                    (indices_for args)
   in
   let remaining_params    = map (fn i -> params @ i) remaining_indices in
   let remaining_args      = map (fn i -> args   @ i) remaining_indices in

   if recursive? then
     makeRecursiveLocalDef (outer_qid, 
                            qid,
                            nm,
                            def_body, 
                            result_type, 
                            tv_subst,
                            remaining_params, 
                            remaining_args,
                            remaining_indices,
                            p_subst, 
                            curried?, 
                            length args, 
                            unfold_map, 
                            simplifyTerm, 
                            spc)
   else
     let def_body             = instantiateTyVarsInTerm (def_body, tv_subst) in
     let remaining_params     = map (fn p -> instantiateTyVarsInPattern(p, tv_subst))
                                    remaining_params
     in
     %% sjw: This is unnecessary as makeLetBinds no longer does substitutions
     %%      which is where capture could occur
     % let (remaining_params, remaining_args) = 
     %     adjustBindingsToAvoidCapture (remaining_params, remaining_args, args, def_body, spc)
     % in
     let new_body = simplifyTerm def_body in
     % let _ = if trace? then writeLine("new_body: "^printTerm new_body) else () in
     let (new_let_binds, new_subst) = makeLetBinds (remaining_params, remaining_args) in
     let new_fn = mkLambda(mkTuplePat(map (project 1) new_let_binds), new_body) in
     let new_args = mkTuple(map (project 2) new_let_binds) in
     % let _ = if trace? then writeLine("new_args: "^printTerm new_args) else () in
     let new_fn = substitute (new_fn, p_subst ++ new_subst)                     in
     % let _ = if trace? then writeLine("new_fn: "^printTerm new_fn) else () in

     %% The substitutions in p_subst only make sense in the body of the definition.
     %% Once they are done there, do not propagate them into makeLet.
     %%
     %% Instead, makeLet may create an entirely new set of substitutions to be applied to the body.
     %% Alternatively, it might just add the corrseponding let bindings.

     let new_tm               = simplifyTerm(mkApply(new_fn, new_args))                                            in
     % let _ = writeLine("new_tm: "^printTerm new_tm) in
     let trans_new_tm         = unfoldInTerm (outer_qid, new_tm, unfold_map, simplifyTerm, spc) in
     % let _ = if trace? then writeLine("orig_tm: "^printTerm orig_tm) else () in

     % let _ = if trace? then writeLine("cost new_tm: "^show(termCost new_tm)^" "^show(termCost orig_tm))else () in
     %% TODO: The following test is just weird.  Explain it.
     %% Note that if avoid_bindings? (used by makeLet) is true, the resulting form looks the 
     %% same but the freeVars test gives a different result (huh?), changing the sense of the test.

     if (trans_new_tm = new_tm
           && termCost new_tm > termCost orig_tm
           && ~(exists? (fn (_,t) -> embed? Apply t || freeVars t ~= []) new_subst))
       then 
         orig_tm
     else 
       trans_new_tm

 op matchPairs (pat : MSPattern, tm : MSTerm) : MSVarSubst =
   case (pat, tm) of

     | (VarPat(pv, _), _) -> [(pv, tm)]

     | (RecordPat (pattern_fields, _), Record (term_fields, _)) ->
       foldl (fn (pairs, (id, p1)) -> pairs ++ matchPairs (p1, lookupId (id, term_fields)))
             [] 
             pattern_fields

     | _ -> fail "matchPairs: Shouldn't happen"

 op makeRecursiveLocalDef (outer_qid         : QualifiedId,
                           qid               : QualifiedId,
                           nm                : String,
                           def_body          : MSTerm,
                           result_type       : MSType,
                           tv_subst          : TyVarSubst,
                           remaining_params  : MSPatterns,
                           remaining_args    : MSTerms,
                           remaining_indices : List Nat,
                           param_subst       : MSVarSubst,
                           curried?          : Bool,
                           numargs           : Nat,
                           unfold_map        : AQualifierMap DefInfo,
                           simplifyTerm      : MSTerm -> MSTerm,
                           spc               : Spec)
  : MSTerm =

  %% check name conflict with args and defbody. defbody should be safe
  %% because user can't put "--" in identifier, but to be safe

  let prefix               = (let Qualified(q, xid) = outer_qid in 
                              if q = UnQualified then xid else q ^ "_" ^ xid)
  in
  let local_fn_name        = locallyUniqueName (prefix ^ "_" ^nm ^ "--local",
                                                %% Just to give context of var names to avoid
                                                mkTuple (def_body :: remaining_args))
  in
  let combined_arg         = mkTuple remaining_args                       in
  let instantiated_fn_type = mkArrow (inferType(spc, combined_arg), result_type) in
  let local_fn             = (local_fn_name, instantiated_fn_type)        in
  let 
    def foldRecursiveCall tm =
      case tm of

        | Apply (Fun (Op (inner_qid, _), _, _), arg, pos) | inner_qid = qid && List.length (termToList arg) = numargs ->
          let args = termToList arg in
          Apply (mkVar local_fn,
                 mkTuple (map (fn i -> args @ i) remaining_indices),
                 pos)

        | Apply _ | curried? ->
          (case getCurryArgs tm of

             | Some (Fun (Op (inner_qid, _), _, _), args) | inner_qid = qid && length args = numargs ->
               mkApply (mkVar local_fn,
                        mkTuple (map (fn i -> args @ i) remaining_indices))

             | _ -> tm)

        | _ -> tm
  in
  let instantiateTyVars = fn s -> instantiateTyVars(s, tv_subst) in
  let def_body          = mapTerm (id, instantiateTyVars, id) def_body in
  let unfold_map        = let Qualified (q, id) = qid in removeAQualifierMap (unfold_map, q, id) in
  let def_body          = unfoldInTerm (outer_qid, simplifyTerm def_body, unfold_map, simplifyTerm, spc) in
  let local_def_body    = mapSubTerms foldRecursiveCall def_body in

  let new_params  = map (mapPattern (id, instantiateTyVars, id)) remaining_params in
  let new_lambda  = mkLambda (mkTuplePat new_params, local_def_body) in
  % let _ = if outer_qid = Qualified(UnQualified,"f") then writeLine("new_lambda: "^printTerm new_lambda) else () in
  let local_def   = substitute (new_lambda, param_subst) in
  % let _ = if outer_qid = Qualified("Size","doTestForSize") then writeLine("local_def: "^printTerm local_def) else () in
  

  %% Need to repeat as substitution may have introduced new opportunities
  let local_def   = unfoldInTerm (outer_qid, simplifyTerm local_def, unfold_map, simplifyTerm, spc) in
  let new_letrec  = mkLetRec ([(local_fn, local_def)], 
                              mkApply (mkVar local_fn, 
                                       combined_arg))
  in
  simplifyTerm new_letrec

 op locallyUniqueName (base_id : Id, tm : MSTerm) : Id =
   let 
     def aux i =
       let new_id = base_id ^ "-" ^ show i in
       if idReferenced? (new_id, tm) then
         aux (i + 1)
       else 
         new_id
   in 
   aux 0

 op idReferenced? (id : Id, tm : MSTerm) : Bool =
   existsSubTerm
     (fn subtm -> case subtm of
                    | Var ((vid, _), _) -> vid = id
                    | _ -> false)
     tm

 op unfoldInTerm (outer_qid    : QualifiedId,
                  tm           : MSTerm,
                  info_map     : AQualifierMap DefInfo,
                  simplifyTerm : MSTerm -> MSTerm,
                  spc          : Spec)
   : MSTerm =
   mapSubTerms (fn tm -> maybeUnfoldTerm (outer_qid, tm, info_map, simplifyTerm, spc))
               tm

 op adjustBindingsToAvoidCapture (remaining_params : MSPatterns, 
                                  remaining_args   : MSTerms,
                                  args             : MSTerms,
                                  defbody          : MSTerm,
                                  spc              : Spec)
   : (MSPatterns * MSTerms) =

   %% If a parameter var could capture a free var in an arg, introduce temp vars to 
   %% avoid the capture:
   %%   First bind the new temp vars to all the args (no capture possible).
   %%   Then bind the parameter vars to the new temp vars (no capture possible).
   let 

     def similar? (param, arg) =
       case (param, arg) of

         | (VarPat ((param_id, _), _), Var ((arg_id, _), _)) -> 
           param_id = arg_id

         | (RecordPat (p_fields, _), Record (a_fields, _)) ->
           forall? (fn (pat, arg) -> similar? (pat, arg)) 
                   (zip ((map (fn (_,pat) -> pat) p_fields),
                         (map (fn (_,arg) -> arg) a_fields)))

         | _ -> false
   in
   let (remaining_params, remaining_args) = 
       unzip (filter (fn (param, arg) -> ~ (similar? (param, arg)))
                     (zip (remaining_params, remaining_args)))
   in
   let pattern_vars  : List MSVars = map patVars  remaining_params in
   let arg_free_vars : List MSVars = map freeVars remaining_args   in
   let possible_capture? =
       case reverse pattern_vars of

         | [] -> false

         | _ :: outer_pattern_vars ->
           let (capture?, _) =
               foldl (fn ((capture?, outer_pattern_vars_list), arg_vars) ->
                        if capture? then
                          (true, [])
                        else if exists? (fn av -> 
                                           exists? (fn outer_pat_vars -> 
                                                      exists? (fn pv -> av.1 = pv.1) 
                                                              outer_pat_vars)
                                                   outer_pattern_vars_list)
                                        arg_vars 
                        then
                          (true, [])
                        else
                          (false,
                           case outer_pattern_vars_list of
                             | [] -> []
                             | _ :: outer_list -> outer_list))
                     (false, outer_pattern_vars)
                     (reverse arg_free_vars)
           in
           capture?
   in
   if possible_capture? then
     %% Note: This is a rare occurrence.  It seems to happen once(!) in the Forges PSL
     %% sources, and never in Specware, Accord, Planware, JFlaws, JavaCard, ...
     let 
       def find_unused_id index =
         let new_id = "temp-" ^ (show index) ^ "-" in
         if idReferenced? (new_id, defbody) || (exists? (fn arg -> idReferenced? (new_id, arg)) args) then
           find_unused_id (index + 1)
         else
           (index + 1, new_id)
     in
     let (_, temp_vars) = 
         foldl (fn ((index, new_vars), arg) ->
                  let (index, new_id) = find_unused_id index in
                  let new_var = ((new_id, inferType(spc, arg)), noPos) in
                  (index,  new_vars ++ [new_var]))
               (0, [])
               remaining_args
     in
     let revised_params = (map (fn v -> VarPat v) temp_vars) ++ remaining_params               in
     let revised_args   = remaining_args                     ++ map (fn v -> Var v) temp_vars in
     let _ = writeLine("revised_params:\n"^anyToString revised_params^"\n"
                       ^"revised_params:\n"^anyToString revised_args^"\n")
     in
     (revised_params, revised_args)
   else	
     (remaining_params, remaining_args)

 op avoid_bindings? : Bool = false % not clear if this helps or hurts

 op makeLetBinds (params : MSPatterns, args : MSTerms) 
   : List (MSPattern * MSTerm) * MSVarSubst =
   let
     def aux (params, args, binds, sbst) =
       case (params, args) of
         | (param :: params, arg :: args) -> aux (params, args, (param, arg) :: binds, sbst)
         | _ -> (binds, sbst)
   in
   aux (params, args, [], [])

 %% ================================================================================
 %% simplify
 %% ================================================================================

 op simplifyUnfoldCase (spc: Spec) (tm: TransTerm): MSTerm =
   case MSRule.simplifyUnfoldCase spc tm of
     | Some s_tm -> s_tm
     | None -> tm

 op MSRule.simplifyUnfoldCase (spc: Spec) (tm: TransTerm): Option MSTerm =
   case tm of
     | Apply (Lambda (rules, _), arg, _) | length rules > 1 ->
       %% Unfold if function constructs term that matches one case
       (let uf_arg = case tryUnfold (spc, arg) of
                      | Some uf_arg -> uf_arg
                      | None -> arg
        in
        case simplify spc uf_arg of
          | Let (binds, let_body, pos) ->
            (case patternMatchRulesToLet (rules, let_body, spc) of
               | Some exp_tm -> Some(Let (binds, exp_tm, pos))
               | None -> None)
          | Apply (Lambda (arg_rules, a1), arg1, a2) ->
            let s_arg_rule_tms = map (fn (_, _, rule_tm) ->
                                        patternMatchRulesToLet(rules, rule_tm, spc))
                                   arg_rules
            in
            if forall? some? s_arg_rule_tms
              then let n_arg_rules = map (fn ((pati, predi, _), Some bodi) ->
                                            (pati, predi, bodi))
                                       (zip(arg_rules, s_arg_rule_tms))
                   in
                   % let _ = writeLine("suf:\n"^printTerm tm) in
                   Some(Apply (Lambda (n_arg_rules, a1), arg1, a2))
              else None
          | simp_uf_arg ->
            patternMatchRulesToLet (rules, simp_uf_arg, spc))
     | Let (binds, bod, pos) ->
       (case MSRule.simplifyUnfoldCase spc bod of
         | None -> None
         | Some s_bod ->
           Some(simplifyOne spc (Let (binds, s_bod, pos))))
     | _ -> None

 %% ================================================================================
 %% unfold one term
 %% ================================================================================

 % FIXME: This should avoid unfolding uninterpreted functions (those with Any somewhere in the body).
 op tryUnfold (spc: Spec, tm: MSTerm) : Option MSTerm =
   case tm of

     | Apply (f, arg, _) ->
       (case f of

          | Fun (Op (qid, _), fun_type, _) -> 
            %% Uncurried case
            (case findTheOp (spc, qid) of

               | Some opinfo | termCost opinfo.dfn <= unfoldCostThreshold ->
                 let (tvs, op_type, dfn) = unpackFirstOpDef opinfo in
                 % let _ = writeLine("unpack = "^printTerm dfn) in
                 (case (dfn, typeMatch (op_type, fun_type, spc, true, true)) of

                    | (t as Lambda body, Some tv_subst) ->
                        if anyTerm? t
                          then None
                          else let inst_dfn = instantiateTyVarsInTerm (dfn, tv_subst) in
                                    Some (simplifiedApply (inst_dfn, arg, spc))

                    | _ -> None)
               | _ -> None)

          | Apply _ ->
	    (case getCurryArgs tm of

	       | Some (f, args) ->
		 (case f of

		    | Fun (Op (qid, _), fun_type, _) ->
		      (case findTheOp (spc, qid) of

                         | Some opinfo | termCost opinfo.dfn <= unfoldCostThreshold ->
                           let (tvs, op_type, dfn) = unpackFirstOpDef opinfo in
                           (case (dfn, typeMatch (op_type, fun_type, spc, true, true)) of

                              | (Lambda _, Some tv_subst) ->
                                let inst_dfn = instantiateTyVarsInTerm (dfn, tv_subst) in
                                let inst_tm = mkCurriedApply (inst_dfn, args) in
                                Some (simplify spc inst_tm)

                              | _ -> None)
                         | _ -> None)
                    | _ -> None)
	       | _ -> None)
          | _ -> None)
     | _ -> None
               
 op typeMatch (t1 : MSType, t2 : MSType, spc : Spec) : TyVarSubst =
   let 
     def match (t1, t2, tv_subst) =
       case (t1, t2) of

         | (TyVar (id1, _), t2) -> 
           if some? (findLeftmost (fn (id, _) -> id = id1) tv_subst) then
             tv_subst
           else 
             (id1, t2) :: tv_subst
             
         | (Arrow (d1, r1, _), Arrow (d2, r2, _)) -> 
           match (r1, r2, match (d1, d2, tv_subst))
           
         | (Product (ts1, _), Product (ts2, _)) -> 
           matchL (ts1, ts2, tv_subst,
                   fn ((_,t1), (_,t2), tv_subst) -> match (t1, t2, tv_subst))
           
         | (CoProduct (ts1, _), CoProduct (ts2, _)) -> 
           matchL (ts1, ts2, tv_subst,
                   fn ((id1, t1), (id2, t2), tv_subst) ->
                     if id1 = id2 then
                       case (t1, t2) of
                         | (None, None) -> tv_subst 
                         | (Some t1, Some t2) -> match (t1, t2, tv_subst)
                     else 
                       tv_subst)
           
         | (Quotient (t1, _, _), Quotient(t2, _, _)) -> 
           match (t1, t2, tv_subst)
           
         | (Subtype (t1, _, _), t2) -> match (t1, t2, tv_subst)
           
         | (t1, Subtype (t2, _, _)) -> match (t1, t2, tv_subst)
           
         | (Base (id1, ts1, pos1), Base (id2, ts2, pos2)) ->
           if id1 = id2 then
             matchL (ts1, ts2, tv_subst, match)
           else
             let t2x = unfoldBase(spc, t2) in
             if equalType? (t2, t2x) then % also reasonable: equivType? spc (typ2, t2x)
               tv_subst
             else 
               match (t1, t2x, tv_subst)
               
         | (_, Base _) ->
           let t2x = unfoldBase(spc, t2) in
           if equalType? (t2, t2x) then % also reasonable: equivType? spc (typ2, t2x)
             tv_subst
           else
             match(t1, t2x, tv_subst)
             
         | _ -> tv_subst
   in 
   match (t1, t2, [])

 op [a] matchL (l1       : List a, 
                l2       : List a, 
                tv_subst : TyVarSubst, 
                matchElt : a * a * TyVarSubst -> TyVarSubst)
   : TyVarSubst =
   case (l1, l2) of
     | (e1 :: l1, e2 :: l2) -> matchL (l1, l2, matchElt (e1, e2, tv_subst), matchElt)
     | _ -> tv_subst


 op patternMatchRulesToLet (rules : MSMatch, tm : MSTerm, spc : Spec) : Option MSTerm =
   case patternMatchRules (rules, tm) of
     | Some (vsubst, body) ->
       let bindings = map (fn (var, val) -> (mkVarPat var, val)) vsubst in
       Some (simplifyOne spc (mkLet (bindings, body)))
     | _ -> None


 %% ================================================================================

 %% unused?
 %%
 %% op termHead (tm : MSTerm) : MSTerm =
 %%    case tm of
 %%     | Apply (f, _, _) -> termHead f
 %%     | _ -> tm
 %%
 %%  op  my_x_counter : () -> Nat

 %%  %% Returns nm if it is not referenced in t, otherwise adds -i to
 %%  %% to make it unique
 %%
 %%  op  transparentRenaming: Qualifier * Id * MSTerm * Spec -> Qualifier * Id * MSTerm
 %%  %% If definition is just a renaming then "unfold"
 %%  def transparentRenaming (q, id, def1, spc) =
 %%    case def1 of
 %%      | Fun (Op (Qualified (q2, id2), _), _, _) ->
 %%        (case findAQualifierMap (spc.ops, q2, id2) of
 %%	  | Some info -> 
 %%	    (let (decls, defs) = opInfoDeclsAndDefs info in
 %%	     case defs of
 %%	       | [def2] -> (q2, id2, def2)
 %%	       | _ -> (q, id, def1))
 %%	  | _ -> (q, id, def1))
 %%      | _ -> (q, id, def1)

end-spec
