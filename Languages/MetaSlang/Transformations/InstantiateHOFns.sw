tyInstantiateHO qualifying
spec
 import Simplify
 import CurryUtils
 import ../Specs/AnalyzeRecursion

 type Term    = MS.Term  % disambiguate from SpecCalc.Term
 type MS.Type = MS.Sort  % also have JGen.Type and MetaslangProofChecker.Type (sigh)

 %% (params, defn body, indices of applied fn args, curried?, recursive?)
 type DefInfo = List Pattern * Term * Type * List Nat * Bool * Bool

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

 op instantiateHOFns (spc : Spec) : Spec =
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
   unFoldTerms (spc, mp)

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
                           let arg_types        = curryArgSorts   (spc, typ) in
                           let normDef1         = normalizeCurriedDefn (def1, arg_types) in
                           maybePiTerm (tvs, SortedTerm (normDef1, typ, pos)))
                        old_defs
                in
                info << {dfn = maybeAndTerm (old_decls ++ new_defs, pos)})
         spc.ops
   in 
   setOps (spc, normOps)

 op normalizeCurriedDefn (dfn : Term, curry_arg_types : List Type) : Term =
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
            
            if (~ snark_problem?) && HOFnType? (typ, spc) && unfoldable? tm then
              
              let numCurryArgs = curryShapeNum (spc, typ) in
              % see note below about debugging indexing error
              let arg_types = (if numCurryArgs > 1 then
                                 curryArgSorts    (spc, typ)
                               else 
                                 noncurryArgSorts (spc, typ))
              in
              let HOArgs? = map (fn s -> HOType? (s, spc)) arg_types in
              if numCurryArgs > 1 then
                analyzeCurriedDefn   (qid, tm, HOArgs?, typ, ref_map, numCurryArgs)
              else 
                analyzeUnCurriedDefn (qid, tm, HOArgs?, typ, ref_map)
                
            else 
              None)
     spc.ops

 %% has an argument that is HO. Arguments are either curried or product
 op HOFnType? (typ : Type, spc : Spec) : Bool =
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

 op HOType? (typ : Type, spc : Spec) : Bool =
   case stripSubsorts (spc, typ) of
     | Arrow _ -> true

     | Product (fields, _) ->
       exists? (fn (_, s) -> HOType? (s, spc)) fields

     | _ -> false

 op unfoldSizeThreshold   : Nat = 40
 op unfoldHOSizeThreshold : Nat = 80
  
 op unfoldable? (dfn : Term) : Bool =
   sizeTerm dfn < unfoldHOSizeThreshold

 op sizeTerm (tm : Term) : Nat = 
   foldSubTerms (fn (_, sum) -> sum + 1) 0 tm

 op analyzeCurriedDefn (qid          : QualifiedId,
                        dfn          : Term,
                        HOArgs?      : List Bool,
                        typ          : Type,
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
                          dfn     : Term,
                          HOArgs? : List Bool,
                          typ     : Type,
                          ref_map : RefMap)
   : Option DefInfo =
   case dfn of

     | Lambda ([(pat, _, body)], _) ->
       analyzeDefn (qid, getParams pat, body, HOArgs?, false, typ, ref_map)

     | _ -> None

 op analyzeDefn (qid      : QualifiedId,
                 params   : List Pattern,
                 body     : Term,
                 HOArgs?  : List Bool,
                 curried? : Bool,
                 typ      : Type,
                 ref_map  : RefMap)
   : Option DefInfo =
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

 op recursiveCallsPreserveHOParameters? (body     : Term, 
                                         qid      : QualifiedId,
                                         params   : List Pattern,
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

 op HOParamsSame? (params  : List Pattern, 
                   args    : List Term, 
                   HOArgs? : List Bool)
   : Bool =
   length params >= length args
   && 
   forall? (fn i -> if HOArgs? @ i then
                      patternMatchesTerm? (params @ i, args @ i)
                    else 
                      true)
           (indices_for args)

 op patternMatchesTerm? (pat : Pattern, tm : Term) : Bool =
   case (pat, tm) of

     | (VarPat ((vpid, _), _), Var ((vid, _), _)) -> 
       vid = vpid
       
     | (RecordPat (pattern_fields, _), Record (term_fields, _)) ->
       forall? (fn (id, pat) -> 
                  patternMatchesTerm? (pat, lookupId (id, term_fields))) 
               pattern_fields
       
     | _ -> false

 op lookupId (id : Id, fields : List (Id * Term)) : Term =
   case findLeftmost (fn (id1, tm) -> id = id1) fields of
     | Some (_, tm) -> tm
     | _ -> fail "lookupId: Shouldn't happen"

 %% ================================================================================
 %% simplify and unfold throughout spec
 %% ================================================================================

 %% Generalize the term->term function in TSP_Maps to a function that creates a 
 %% term->term function.
 type Generalized_TSP_Maps = (QualifiedId -> Term -> Term) * 
                             (Type    -> Type)             * 
                             (Pattern -> Pattern)

 op unFoldTerms (spc : Spec, info_map : AQualifierMap DefInfo) : Spec =
   let 
     def simplifyTerm tm =
       let result = simplify           spc tm     in
       let result = simplifyUnfoldCase spc result in
       result
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
	   sorts    = mapSpecSorts         outer_tsp spc.sorts,
	   ops      = mapSpecOpsNotingName gtsp      spc.ops,
	   elements = mapSpecProperties    outer_tsp spc.elements
	  }

 op mapSpecOpsNotingName (gtsp : Generalized_TSP_Maps) (ops : AOpMap Position)
   : AOpMap Position =
   let (make_op_map, typ_map, pat_map) = gtsp in
   mapOpInfos (fn info -> 
                 let inner_tsp = (make_op_map (primaryOpName info), typ_map, pat_map) in
                 %% now the the tsp knows the name of the op
                 info << {dfn = mapTerm inner_tsp info.dfn})
              ops

 %% ================================================================================
 %% unfold
 %% ================================================================================

 op maybeUnfoldTerm (outer_qid    : QualifiedId,
                     tm           : Term,
                     unfold_map   : AQualifierMap DefInfo,
                     simplifyTerm : Term -> Term,
                     spc          : Spec)
   : Term =
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
                     makeUnfoldedTerm (outer_qid, 
                                       tm, 
                                       f, 
                                       termToList arg, 
                                       inferType (spc, tm),
                                       sortMatch (deftyp, typ, spc),
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
               | _ -> tm)

	  | Apply _ ->
            %% Curried case
	    (case getCurryArgs tm of
	       | Some(f, args) ->
		 (case f of

		    | Fun (Op (qid as Qualified (q, id), _), typ, _) ->
		      (case findAQualifierMap(unfold_map, q, id) of

			 | Some (vs, defn, deftyp, fnIndices, curried?, recursive?) ->
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
                                                 sortMatch (deftyp, typ, spc),
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

 op getTupleArg (tm : Term, i : Nat) : Term =
   case tm of
     | Record (tms, _) -> (tms @ i).2
     | _ -> (if i = 0 then tm else fail("Illegal getTupleArg call"))

 op exploitableTerm? (tm : Term, unfoldMap : AQualifierMap DefInfo) : Bool =
   ~(embed? Var tm)

 op termToList (tm : Term) : List Term =
   case tm of
     | Record (fields, _) -> map (fn (_, tm) -> tm) fields
     | _ -> [tm]

 %% ================================================================================
 %% The heart of the matter.
 %% Everything else is arranged so that this routine has the right information
 %% to do the appropriate transformations.
 %% ================================================================================

 op makeUnfoldedTerm (outer_qid    : QualifiedId,
                      orig_tm      : Term,
                      f            : Term,
                      args         : List Term,
                      result_type  : Type,
                      tv_subst     : TyVarSubst,
                      params       : List Pattern,
                      def_body     : Term,
                      fn_indices   : List Nat,
                      recursive?   : Bool,
                      qid          : QualifiedId,
                      nm           : String,
                      unfold_map   : AQualifierMap DefInfo,
                      simplifyTerm : Term -> Term,
                      curried?     : Bool,
                      spc          : Spec)
   : Term =
  
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
     let def_body             = instantiateTyVarsInTerm (def_body, tv_subst)                    in
     let remaining_params     = map (fn p -> instantiateTyVarsInPattern(p, tv_subst))
                                    remaining_params
     in
     let (remaining_params, remaining_args) = 
         adjustBindingsToAvoidCapture (remaining_params, remaining_args, args, def_body)
     in
     let new_body             = simplifyTerm def_body                                           in
     let new_body             = substitute (new_body, p_subst)                                  in

     %% The substitutions in p_subst only make sense in the body of the definition.
     %% Once they are done there, do not propagate them into makeLet.
     %%
     %% Instead, makeLet may create an entirely new set of substitutions to be applied to the body.
     %% Alternatively, it might just add the corrseponding let bindings.

     let (new_let, new_subst) = makeLet (remaining_params, remaining_args, new_body)            in
     let new_let              = substitute (new_let, new_subst)                                 in
     let new_tm               = simplifyTerm new_let                                            in
     let trans_new_tm         = unfoldInTerm (outer_qid, new_tm, unfold_map, simplifyTerm, spc) in

     %% TODO: The following test is just weird.  Explain it.
     %% Note that if avoid_bindings? (used by makeLet) is true, the resulting form looks the 
     %% same but the freeVars test gives a different result (huh?), changing the sense of the test.

     if (trans_new_tm = new_tm 
           && sizeTerm new_tm > sizeTerm orig_tm
           && ~(exists? (fn (_,t) -> embed? Apply t || freeVars t ~= []) new_subst))
       then 
         orig_tm
     else 
       trans_new_tm

 op matchPairs (pat : Pattern, tm : Term) : List (Var * Term) =
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
                           def_body          : Term,
                           result_type       : Type,
                           tv_subst          : TyVarSubst,
                           remaining_params  : List Pattern,
                           remaining_args    : List Term,
                           remaining_indices : List Nat,
                           param_subst       : List (Var * Term),
                           curried?          : Bool,
                           numargs           : Nat,
                           unfold_map        : AQualifierMap DefInfo,
                           simplifyTerm      : Term -> Term,
                           spc               : Spec)
  : Term =

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
  let instantiated_fn_type = mkArrow (termSort combined_arg, result_type) in
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

  %% TODO: what is this all about?
  let _ = if outer_qid = Qualified("<unqualified>","inferTypeOfExprs") then
            writeLine ("loc_body:\n" ^ printTerm def_body ^ "\n\n" ^ printTerm local_def_body) 
          else 
            () 
  in

  let new_params  = map (mapPattern (id, instantiateTyVars, id)) remaining_params in
  let new_lambda  = mkLambda (mkTuplePat new_params, local_def_body) in
  let local_def   = substitute (new_lambda, param_subst) in
  %% Need to repeat as substitution may have introduced new opportunities
  let local_def   = unfoldInTerm (outer_qid, simplifyTerm local_def, unfold_map, simplifyTerm, spc) in
  let new_letrec  = mkLetRec ([(local_fn, local_def)], 
                              mkApply (mkVar local_fn, 
                                       combined_arg))
  in
  simplifyTerm new_letrec

 op locallyUniqueName (base_id : Id, tm : Term) : Id =
   let 
     def aux i =
       let new_id = base_id ^ "-" ^ show i in
       if idReferenced? (new_id, tm) then
         aux (i + 1)
       else 
         new_id
   in 
   aux 0

 op idReferenced? (id : Id, tm : Term) : Bool =
   existsSubTerm
     (fn subtm -> case subtm of
                    | Var ((vid, _), _) -> vid = id
                    | _ -> false)
     tm

 op unfoldInTerm (outer_qid    : QualifiedId,
                  tm           : Term,
                  info_map     : AQualifierMap DefInfo,
                  simplifyTerm : Term -> Term,
                  spc          : Spec)
   : Term =
   mapSubTerms (fn tm -> maybeUnfoldTerm (outer_qid, tm, info_map, simplifyTerm, spc))
               tm

 op adjustBindingsToAvoidCapture (remaining_params : List Pattern, 
                                  remaining_args   : List Term,
                                  args             : List Term,
                                  defbody          : Term)
   : (List Pattern * List Term) =

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
   let pattern_vars  : List (List Var) = map patVars  remaining_params in
   let arg_free_vars : List (List Var) = map freeVars remaining_args   in
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
                  let new_var = ((new_id, termSort arg), noPos) in
                  (index,  new_vars ++ [new_var]))
               (0, [])
               remaining_args
     in
     let revised_params = (map (fn v -> VarPat v) temp_vars) ++ remaining_params               in
     let revised_args   = remaining_args                     ++ map (fn v -> Var v) temp_vars in
     (revised_params, revised_args)
   else	
     (remaining_params, remaining_args)

 op avoid_bindings? : Bool = false % not clear if this helps or hurts

 op makeLet (params : List Pattern, args : List Term, body : Term) 
   : Term * VarSubst =
   let
     def aux (params, args, body, sbst) =
       case (params, args) of

         | (param :: params, arg :: args) ->
           let (newbod, sbst) = aux (params, args, body, sbst) in
           (case (param, arg) of
              | (VarPat (v,_), Var _) | avoid_bindings? -> (newbod, (v, arg)::sbst) % TODO: figure out which is best
              | _ -> (mkLet ([(param, arg)], newbod), sbst))

         | _ -> (body, sbst)
   in
   aux (params, args, body, [])

 %% ================================================================================
 %% simplify
 %% ================================================================================

 op simplifyUnfoldCase (spc: Spec) (tm: Term): Term =
   case tm of

     | Apply (Lambda (rules, _), arg, _) | length rules > 1 ->
       %% Unfold if function constructs term that matches one case
       (let uf_tm = case tryUnfold (spc, arg) of
                      | Some uf_tm -> uf_tm
                      | _ -> tm
        in
          case simplify spc uf_tm of

            | Let (binds, let_body, pos) ->
              (case patternMatchRulesToLet (rules, let_body, spc) of
                 | Some exp_tm -> Let (binds, exp_tm, pos)
                 | _ -> tm)

            | simp_uf_tm ->
              (case patternMatchRulesToLet (rules, simp_uf_tm, spc) of
                 | Some exp_tm -> exp_tm
                 | _ -> tm))

     | Let (binds, bod, pos) ->
       simplifyOne spc (Let (binds, simplifyUnfoldCase spc bod, pos))

     | _ -> tm

 %% ================================================================================
 %% unfold one term
 %% ================================================================================

 op tryUnfold (spc: Spec, tm: Term) : Option Term =
   case tm of

     | Apply (f, arg, _) ->
       (case f of

          | Fun (Op (qid, _), fun_type, _) -> 
            %% Uncurried case
            (case findTheOp (spc, qid) of

               | Some opinfo | sizeTerm opinfo.dfn <= unfoldSizeThreshold ->
                 let (tvs, op_type, dfn) = unpackFirstOpDef opinfo in
                 (case (dfn, typeMatch (op_type, fun_type, spc, true)) of

                    | (Lambda _, Some tv_subst) ->
                      let inst_dfn = instantiateTyVarsInTerm (dfn, tv_subst) in
                      Some (simplifiedApply (inst_dfn, arg, spc))

                    | _ -> None)
               | _ -> None)

          | Apply _ ->
	    (case getCurryArgs tm of

	       | Some (f, args) ->
		 (case f of

		    | Fun (Op (qid, _), fun_type, _) ->
		      (case findTheOp (spc, qid) of

                         | Some opinfo | sizeTerm opinfo.dfn <= unfoldSizeThreshold ->
                           let (tvs, op_type, dfn) = unpackFirstOpDef opinfo in
                           (case (dfn, typeMatch (op_type, fun_type, spc, true)) of

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
               
 op sortMatch (t1 : Type, t2 : Type, spc : Spec) : TyVarSubst =
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
           
         | (Subsort (t1, _, _), t2) -> match (t1, t2, tv_subst)
           
         | (t1, Subsort (t2, _, _)) -> match (t1, t2, tv_subst)
           
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


 op patternMatchRulesToLet (rules : Match, tm : Term, spc : Spec) : Option Term =
   case patternMatchRules (rules, tm) of
     | Some (vsubst, body) ->
       let bindings = map (fn (var, val) -> (mkVarPat var, val)) vsubst in
       Some (simplifyOne spc (mkLet (bindings, body)))
     | _ -> None


 %% ================================================================================

 %% unused?
 %%
 %% op termHead (tm : Term) : Term =
 %%    case tm of
 %%     | Apply (f, _, _) -> termHead f
 %%     | _ -> tm
 %%
 %%  op  my_x_counter : () -> Nat

 %%  %% Returns nm if it is not referenced in t, otherwise adds -i to
 %%  %% to make it unique
 %%
 %%  op  transparentRenaming: Qualifier * Id * Term * Spec -> Qualifier * Id * Term
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

endspec
