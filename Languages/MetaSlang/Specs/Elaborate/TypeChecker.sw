(* This structure adds type checking and 
   inference to the abstract syntax tree.
      - It infers types of each subterm.
      - Resolves record projection from structure accessing.
 *)

(*
   TODO:

   Syntactic well-formedness checks:
        - duplicate variables in patterns
        - distinguish recursive calls.
        - capture free variables.
        - no free variables in quotient, subtypes.
        
*)

TypeChecker qualifying spec

  %% The TypeChecker function is elaboratePosSpec 

  import Infix
  import Utilities
  import PosSpecToSpec
  import TypeToTerm    % XML hacks

  %% ========================================================================

  type Message  = String
  type Result = | Spec Spec | Errors (List(String * Position))

  %% ========================================================================

  op elaboratePosSpec           : Spec * Position.Filename -> Result

  op unlinkRec                  : MSType -> MSType
  op undeterminedType?          : MSType -> Bool
  op elaborateType              : LocalEnv * MSType    * MSType            -> MSType
  op elaborateCheckTypeForTerm  : LocalEnv * MSTerm    * MSType * MSType   -> MSType 
  op elaborateTypeForTerm       : LocalEnv * MSTerm    * MSType * MSType   -> MSType
  op resolveNameFromType        : LocalEnv * MSTerm*Id * MSType * Position -> MSTerm
  op single_pass_elaborate_term : LocalEnv * MSTerm    * MSType            -> MSTerm
  op elaboratePattern           : LocalEnv * MSPattern * MSType            -> MSPattern * LocalEnv

  op mkEmbed0                   : LocalEnv * MSType          * Id            -> Option Id
  op mkEmbed1                   : LocalEnv * MSType * MSTerm * Id * Position -> Option MSTerm
  op lookupEmbedId              : LocalEnv * Id * MSType                     -> Option (Option MSType)
  op isCoproduct                : LocalEnv * MSType                          -> Option (List (Id * Option MSType))
  op mkProject                  : LocalEnv * Id * MSType * Position          -> Option MSTerm

  op undeclaredName             : LocalEnv * MSTerm      * Id * MSType * Position -> MSTerm
  op ambiguousCons              : LocalEnv * MSTerm      * Id * MSType * Position -> MSTerm
  op undeclaredResolving        : LocalEnv * MSTerm      * Id * MSType * Position -> MSTerm
  op undeclared2                : LocalEnv * MSTerm * Id * Id * MSType * Position -> MSTerm

  op pass2Error                 : LocalEnv * MSType * Message * Position -> ()

  %% ========================================================================

  def type_nat    = natType
  def type_bool   = boolType 
  def type_char   = charType
  def type_string = stringType

  %% ========================================================================
  %% The main type-checking function is elaboratePosSpec.

  def elaboratePosSpec (given_spec, filename) = 
    let _ = initializeMetaTyVarCounter () in

    %% ======================================================================
    %%                           PASS ZERO  [ 0 => 1 ]
    %% ======================================================================

    %% ---------- INITIALIZE SPEC (see ast-environment.sl) ----------
    %%   AstEnvironment.init adds default imports, etc.
    %%
    let initial_env  = initialEnv (given_spec, filename) in
    let {types     = given_types, 
	 ops       = given_ops, 
	 elements  = given_elts,
	 qualifier = qualifier} 
        = given_spec
    in
    let 

      def elaborate_local_op_types (ops, env) =
	mapOpInfos (fn info ->
		    if someOpAliasIsLocal? (info.names, given_spec) then
		      let def elaborate_srt dfn =
		            let pos = termAnn dfn in
			    let (tvs, srt, tm) = unpackTerm dfn in
			    let _ = checkTyVars (env, tvs, pos) in
                            let env_s = if allowDependentSubTypes? then addLambdaVarsToEnv(env, tm) else env in
			    let srt1 = checkType (env_s, srt) in
                            % let _ = writeLine("elos "^show(head info.names)^": "^printType srt^"\n -->\n"^printType srt1) in
                            % let _ = writeLine(printTermWithTypes tm^"\n") in
			    maybePiTerm (tvs, TypedTerm (tm, srt1, pos))
		      in
			let new_defs = map elaborate_srt (opInfoAllDefs info) in
			let new_dfn = maybeAndTerm (new_defs, termAnn info.dfn) in
			let new_info = info << {dfn = new_dfn} in
			new_info
		    else
		      info)
	  ops

      def elaborate_local_types (types, env) =
	if ~(hasLocalType? given_spec) then types
	else
	mapTypeInfos (fn info ->
		      if someTypeAliasIsLocal? (info.names, given_spec) then
			let
                          def elaborate_dfn dfn =
			    let (tvs, srt) = unpackType dfn in
			    let _ = checkTyVars (env, tvs, typeAnn dfn) in
			    maybePiType (tvs, checkType (env, srt))
			in
			let (old_decls, old_defs) = typeInfoDeclsAndDefs info in
			let new_defs = map elaborate_dfn old_defs in
			let new_dfn = maybeAndType (old_decls ++ new_defs, typeAnn info.dfn) in
			info << {dfn = new_dfn}
		      else 
			info)
	             types 

      def elaborate_local_ops (ops, env, poly?) =
	foldl (fn (ops,el) ->
	       case getQIdIfOp el of
		 | None -> ops
		 | Some(Qualified(q,id)) ->
	       case findAQualifierMap(ops,q,id) of
		 | Some info ->
		   let def elaborate_dfn dfn =
			 let pos = termAnn dfn in
                         % let _ = writeLine("elaborate_local_ops:\n"^printTermWithTypes dfn) in
			 let (tvs, srt, tm) = unpackTerm dfn in
			 if poly? = (tvs ~= []) then
			   let _ = checkTyVars (env, tvs, pos) in
                           let env_s = if allowDependentSubTypes? then addLambdaVarsToEnv(env, tm) else env in
			   let srt1 = checkType (env_s, srt) in
			   let xx = single_pass_elaborate_term_top (env, tm, srt1) in
			   maybePiTerm (tvs, TypedTerm (xx, srt1, pos))
			 else 
			   dfn
		   in
		   let new_defs = map elaborate_dfn (opInfoAllDefs info) in
		   let new_dfn = maybeAndTerm (new_defs, termAnn info.dfn) in
		   let new_info = info << {dfn = new_dfn} in
		   insertAQualifierMap(ops,q,id,new_info))
	   ops given_spec.elements

      def elaborate_local_props (elts, env, last_time?) =
	map (fn el ->
	     case el of
	       | Property (prop_type, name, tvs, fm, a) ->
	         let elaborated_fm = single_pass_elaborate_term_top (env, fm, type_bool) in
                 let _ = if last_time? then checkForUnboundMetaTyVars (fm, env) else () in
	         Property(prop_type, name, tvs, elaborated_fm, a)
	       | _ -> el)
	    elts


      def reelaborate_local_ops (ops, env) =
	foldl (fn (ops,el) ->
	       case getQIdIfOp el of
		 | None -> ops
		 | Some(Qualified(q,id)) ->
	       case findAQualifierMap(ops,q,id) of
		 | Some info ->
                   % let _ = writeLine("Checking "^q^"."^id) in
                   insertAQualifierMap(ops,q,id,checkOp(info, env)))
	   ops given_spec.elements

%	if localOps = [] then ops
%	else
%	mapOpInfos (fn info ->
%		    if someAliasIsLocal? (info.names, localOps) then
%		      checkOp (info, env)
%		    else
%		      info)
%	           ops

    in
    %% ======================================================================
    %%                           PASS ONE  
    %% ======================================================================
    %% Add constructors to environment
    let env_with_constrs = addConstrsEnv (initial_env, given_spec) in



    %% Elaborate types of ops
    let elaborated_ops_0 = elaborate_local_op_types (given_ops,env_with_constrs) in

    %% Elaborate types
    let elaborated_types = elaborate_local_types (given_types, env_with_constrs) in
    let env_with_elaborated_types = setEnvTypes (env_with_constrs, elaborated_types) in

    %% Elaborate types of ops pass 2 so that subtypes are resolved before instantiation
    % Second pass of local op types doesn't seem needed in normal cases
    %let elaborated_ops_0a = elaborate_local_op_types(elaborated_ops_0, env_with_elaborated_types) in

    let env_with_elaborated_types = setEnvOps(env_with_elaborated_types, elaborated_ops_0) in

    %% Elaborate ops (do polymorphic definitions first)
    let elaborated_ops_a = elaborate_local_ops (elaborated_ops_0, env_with_elaborated_types, true)  in
    let elaborated_ops_b = elaborate_local_ops (elaborated_ops_a, env_with_elaborated_types, false) in
    % let _ = printIncr elaborated_ops_b in
    let elaborated_ops_c = elaborate_local_ops (elaborated_ops_b, env_with_elaborated_types, true)  in
    let elaborated_ops   = elaborate_local_ops (elaborated_ops_c, env_with_elaborated_types, false) in
    %% Elaborate properties
    let elaborated_elts = elaborate_local_props (given_elts, env_with_elaborated_types, false) in

    %% ======================================================================
    %%                           PASS TWO  
    %% ======================================================================

    %% sjw: 7/17/01 Added a second pass so that order is not so important
    let second_pass_env = secondPass env_with_elaborated_types in

    let final_types = elaborate_local_types (elaborated_types, second_pass_env) in
    let final_ops   = reelaborate_local_ops (elaborated_ops,   second_pass_env) in
    let final_elts  = elaborate_local_props (elaborated_elts,  second_pass_env, true) in
    let final_spec  = given_spec << {types      = final_types, 
                                     ops        = final_ops, 
                                     elements   = final_elts}
    in
    %% We no longer check that all metaTyVars have been resolved,
    %% because we don't need to know the type for _
    case checkErrors second_pass_env of
      | []   -> Spec (convertPosSpecToSpec final_spec)
      | msgs -> Errors msgs

(* Debugging fun
op printIncr(ops: AOpMap StandardAnnotation): () =
  case findAQualifierMap (ops, "Foo", "increasingNats1?") of
    | None -> ()
    | Some info -> writeLine("increasingNats1?:\n"^printTermWithTypes info.dfn)
*)

  % ========================================================================
  %% ---- called inside TYPES : PASS 0  -----
  % ========================================================================
 
  def TypeChecker.checkType (env, srt) =
    checkType1(env, srt, true)

  op checkType1(env: LocalEnv, srt: MSType, checkTerms?: Bool): MSType =
    %% checkType calls single_pass_elaborate_term, which calls checkType
    case srt of

      | TyVar _ -> srt

      | MetaTyVar (v, _) ->
        (case ! v of
	   | {link = Some other_type, uniqueId, name} -> checkType1 (env, other_type, checkTerms?)
	   | _ -> srt)

      | Boolean _ -> srt

      | Base (given_type_qid, instance_types, pos) ->
	let 
          def given_type_str () =
	    (printQualifiedId given_type_qid)
	    ^ (case instance_types of
		 | []     -> ""    
		 | hd::tl -> "("^ "??" ^ (foldl (fn (str, instance_type) ->
						 str^", "^ "??")
					  ""
					  tl) 
		             ^ ")")
	in
	  (case findAllTypes (env.internal, given_type_qid) of
	     | [] -> 
               (error (env, 
		       "Type name "^(given_type_str ())^" has not been declared", 
		       pos);
		Base (given_type_qid, instance_types, pos))

	     | info :: other_infos -> 
	       let _ =
	           (%% Check for errors...
		    %% Note: If multiple candidates are returned, then given_type_qid must be unqualified,
		    %%       so if some candidate has given_type_qid as an exact alias, then that
		    %%       candidate will be first in the list (see comments for findAllTypes),
		    %%       in which case choose it.
		    if ((empty? other_infos) || exists? (fn alias -> alias = given_type_qid) info.names) then
		      let (tvs, srt) = unpackFirstTypeDef info in
		      if length tvs ~= length instance_types then
			let found_type_str =
			    (printAliases info.names)
			    ^ (case tvs of
				 | [] -> ""    
				 | hd::tl -> 
				   "("^ hd ^ (foldl (fn (str, tv) -> str^", "^ tv) "" tl) ^ ")")
			in                                
			let msg = "Type reference " ^ (given_type_str ())
			          ^" does not match declared type " ^ found_type_str
			in
			  error (env, msg, pos)
		      else 
			%%  Normal case goes through here:
			%%  either there are no other infos or the first info has as unqualified
			%%   alias, and the number of type vars equals the number of instance types.
			()
		    else
		      %% We know that there are multiple options 
		      %% (which implies that the given_type_qid is unqualified), 
		      %% and that none of them are unqualified, so complain.
		      let candidates_str = foldl (fn (str, other_info) -> 
						  str ^", "^  printAliases other_info.names)
		                                 (printAliases info.names)
						 other_infos
		      in
			error (env, 
			       "Type reference " ^ (given_type_str ())
			       ^" is ambiguous among " ^ candidates_str,
			       pos))
	       in
	       let new_type_qid = primaryTypeName info in
	       let new_instance_types = 
	           map (fn instance_type -> checkType1 (env, instance_type, checkTerms?))
		       instance_types
	       in
		 if given_type_qid = new_type_qid && instance_types = new_instance_types then 
		   srt
		 else 
		   Base (new_type_qid, new_instance_types, pos))
		
      | CoProduct (fields, pos) ->
	let nfields = map (fn (id, None)   -> (id, None) 
                            | (id, Some s) -> (id, Some (checkType1 (env, s, checkTerms?))))
                       fields
	in
	if nfields = fields then 
	  srt
	else 
	  CoProduct (nfields, pos)

      | Product (fields, pos) ->
	let nfields = map (fn (id, s) -> (id, checkType1 (env, s, checkTerms?))) fields in
        if nfields = fields then 
	  srt
	else 
	  Product (nfields, pos)

      | Quotient (given_base_type, given_relation, pos) ->
        let new_base_type = checkType1 (env, given_base_type, checkTerms?) in
        let new_rel_type = Arrow (Product ([("1", new_base_type), 
                                            ("2", new_base_type)], 
                                           pos), 
                                  type_bool, 
                                  pos) 
	in
        let new_relation = if checkTerms?
                              then single_pass_elaborate_term (env, given_relation, new_rel_type)
                              else given_relation
        in
	if given_base_type = new_base_type && given_relation = new_relation then 
	  srt
	else 
	  Quotient (new_base_type, new_relation, pos)

      | Subtype (given_super_type, given_predicate, pos) -> 
        let new_super_type = checkType1 (env, given_super_type, checkTerms?) in
        let new_pred_type  = Arrow (new_super_type, type_bool, pos) in
        let new_predicate  = if checkTerms?
                              then single_pass_elaborate_term (env, given_predicate, new_pred_type)
                              else given_predicate
        in
	if given_super_type = new_super_type && given_predicate = new_predicate then 
	  srt
	else 
	  Subtype (new_super_type, new_predicate, pos)

      | Arrow (t1, t2, pos) ->
	let nt1 = checkType1 (env, t1, checkTerms?) in
	let nt2 = checkType1 (env, t2, checkTerms?) in
	if t1 = nt1 && t2 = nt2 then 
	  srt
	else 
	  Arrow (nt1, nt2, pos)

      | And (srts, pos) ->
	let (new_srts, changed?) =  
            foldl (fn ((new_srts, changed?), srt) ->
		   let new_srt = checkType1 (env, srt, checkTerms?) in
		   (new_srts ++ [new_srt],
		    changed? || (new_srt ~= srt)))
	          ([], false)
		  srts
	in
	if changed? then
	  maybeAndType (new_srts, pos)
	else
	  srt

      | Any _ -> srt

      | mystery -> 
        let _ = toScreen ("\ncheckType, Unrecognized type: " ^ (anyToString mystery) ^ "\n") in
	mystery

  % ========================================================================
  %% ---- called inside OPS : PASS 0  -----
  % ========================================================================

  def undeterminedType? srt =
    case unlinkType srt of
      | MetaTyVar _ -> true
      | _           -> false

  % ========================================================================
  %% ---- called inside OPS        : PASS 1 -----
  %% ---- called inside PROPERTIES : PASS 1 -----
  %% ---- called inside OPS        : PASS 2 -----
  %% ---- called inside AXIOMS     : PASS 2 -----
  %% ---- called inside CheckType 
  % ========================================================================

  %op TypeChecker.resolveMetaTyVar: MSType -> MSType % see TypeToTerm
  def TypeChecker.resolveMetaTyVar (srt : MSType) : MSType =
    case srt of
      | MetaTyVar(tv,_) -> 
        let {name=_,uniqueId=_,link} = ! tv in
	(case link
	   of None -> srt
	    | Some ssrt -> resolveMetaTyVar ssrt)
      | _ -> srt

  op resolveMetaTyVars: MSTerm -> MSTerm
  def resolveMetaTyVars trm =
    mapTerm (id,resolveMetaTyVar,id) trm

  %% single_pass_elaborate_term calls elaborateCheckTypeForTerm, 
  %% which calls elaborateTypeForTerm, 
  %% which calls unifyTypes, 
  %%  which side-effects links for metaTyVar's via 

  def fixateOneName (id_fixity : Id * Fixity, explicit_fixity : Fixity) 
    : Id * Fixity =
    (id_fixity.1, 
     case explicit_fixity of
       | Unspecified -> id_fixity.2
       | _           -> explicit_fixity)

  def fixateTwoNames (q_id_fixity : Id * Id * Fixity, explicit_fixity : Fixity) 
    : Id * Id * Fixity =
    (q_id_fixity.1, 
     q_id_fixity.2, 
     case explicit_fixity of
       | Unspecified -> q_id_fixity.3
       | _           -> explicit_fixity)

  def resolveNameFromType(env, trm, id, srt, pos) =
    case mkEmbed0 (env, srt, id) of
      | Some id -> Fun (Embed (id, false), checkType (env, srt), pos)
      | None -> 
    case mkEmbed1 (env, srt, trm, id, pos) of
      | Some term -> term
      | None ->
    case uniqueConstr (env, trm, id, pos) of
      | Some term -> term
      | _ ->
    case StringMap.find (env.constrs, id) of
      | None -> undeclaredName (env, trm, id, srt, pos)
      | _    -> ambiguousCons (env, trm, id, srt, pos)

  op tryResolveNameFromType(env: LocalEnv, trm:MSTerm, id: String, srt: MSType, pos: Position): Option MSTerm =
    case mkEmbed0 (env, srt, id) of
      | Some id -> Some(Fun (Embed (id, false), checkType (env, srt), pos))
      | None -> mkEmbed1 (env, srt, trm, id, pos) 

 def checkOp (info, env) =
   let (old_decls, old_defs) = opInfoDeclsAndDefs info in
   let new_decls_and_defs  = map (fn tm -> checkOpDef  (tm, info, env))
                                 (old_decls ++ old_defs)
   in
   let new_dfn = maybeAndTerm (new_decls_and_defs, termAnn info.dfn) in
   info << {dfn = new_dfn}

 op allowDependentSubTypes?: Bool = true

 op addLambdaVarsToEnv(env: LocalEnv, tm: MSTerm): LocalEnv =
   % let _ = writeLine("alvte: "^printTerm tm^"\n"^anyToString env.vars) in
   case tm of
     | Lambda([(pat, _, bod)], pos) ->
       let alpha = freshMetaTyVar ("Lambda_0", pos) in
       let (_, env) = elaboratePattern (env, pat, alpha) in
       addLambdaVarsToEnv(env, bod)
     | Pi(_, tm1, _) -> addLambdaVarsToEnv(env, tm1)
     | And(tm1::_, _) -> addLambdaVarsToEnv(env, tm1)
     | _ -> env

 def checkOpDef (dfn, info, env) =
   % let _ = writeLine("checkOpDef:\n"^printTermWithTypes dfn) in
   let pos = termAnn dfn in
   let (tvs, srt, tm) = unpackTerm dfn in
   let _ = checkTyVars (env, tvs, pos) in
   let env_s = if allowDependentSubTypes? then addLambdaVarsToEnv(env, tm) else env in
   let srt = checkType (env_s, srt) in
   let elaborated_tm = single_pass_elaborate_term_top (env, tm, srt) in
   %% If tm is Any (as in an Op declaration), then elaborated_tm will be tm.
   let tvs_used = collectUsedTyVars (srt, info, dfn, env) in
   let _ = if  false % allowDependentSubTypes?
             then writeLine("chk: "^printTerm elaborated_tm^"\n"^printTypeWithTypes srt) else ()
   in
   let new_tvs =
       if empty? tvs then
	 tvs_used
       else if equalTyVarSets?(tvs_used, tvs) then
	 tvs  (* Probably correct ;-*)
       else 
	 (error (env, 
		 "mismatch between bound vars [" ^ (foldl (fn (s, tv) -> s ^ " " ^ tv) "" tvs) ^ "]"
		 ^            " and free vars [" ^ (foldl (fn (s, tv) -> s ^ " " ^ tv) "" tvs_used) ^ "]",
		 termAnn dfn);
	  tvs)
   in
     maybePiTerm (new_tvs, TypedTerm (elaborated_tm, srt, pos))

 %%% Bound to false in swe in toplevel.lisp because not a problem with the interpreter
 op complainAboutImplicitPolymorphicOps?: Bool = true

 op collectUsedTyVars (srt: MSType, info: OpInfo, dfn: MSTerm, env: LocalEnv): List TyVar =
   let tv_cell = Ref [] : Ref TyVars in
   let 
   
     def insert tv = 
       tv_cell := ListUtilities.insert (tv, ! tv_cell) 

     def scan srt = 
       case srt of
	 | TyVar     (tv,      _) -> insert tv
	 | Product   (fields,  _) -> app (fn (_, s)      -> scan s)           fields
	 | CoProduct (fields,  _) -> app (fn (_, Some s) -> scan s | _ -> ()) fields
	 | Subtype   (s, _,    _) -> scan s
	 | Quotient  (s, _,    _) -> scan s
	 | Arrow     (s1, s2,  _) -> (scan s1; scan s2)
	 | Base      (_, srts, _) -> app scan srts
	 | Boolean              _ -> ()
	 | MetaTyVar (mtv,     _) -> 
	   (let {name = _, uniqueId, link} = ! mtv in
	    case link of
	      | Some s -> scan s
	      | None ->
                if complainAboutImplicitPolymorphicOps? then
	        error (env, 
		       "Incomplete type for op " ^ (printQualifiedId (primaryOpName info)) ^ ":\n" ^(printType srt), 
		       termAnn dfn)
                else ())
	 | And (srts, _) -> app scan srts
	 | Any _ -> ()

   in                        
     let _ = scan srt in
     ! tv_cell

  op checkForUnboundMetaTyVars(tm: MSTerm, env: LocalEnv): () =
    let warned? = Ref false in
    let def cType ty =
          case ty of
            | MetaTyVar (mtv,     _) -> 
              (let {name = _, uniqueId, link} = ! mtv in
                 case link of
                   | None | ~ (!warned?) ->
                     (error (env, 
                             "Incomplete type for " ^ (printTerm tm) ^ ":\n" ^(printType ty), 
                             termAnn tm);
                      warned? := true)
                   | _ -> ())
            | _ -> ()
    in                        
      appTerm (fn _ -> (), cType, fn _ -> ()) tm

  op ambiguousTerm?(tm: MSTerm): Bool =
    let def ambig?(tm, count) =
          if count = 0 then false
            else
              let count = count - 1 in
              case tm of
                | Fun(OneName _, _, _) -> true
                | ApplyN(tms, _) -> exists? (fn tm -> ambig?(tm, count)) tms
                | Record(id_prs, _) -> exists? (fn (_, tm) -> ambig?(tm, count)) id_prs
                | Var((nm, ty), _) -> undeterminedType? ty
                % | Lambda(matches, _) -> exists? (fn (_, _, tm) -> ambig?(tm, count)) matches
                | _ -> false
    in
    ambig?(tm, 2)

  op  elaborateTerm : LocalEnv * MSTerm    * MSType            -> MSTerm                       % backward compatibility for Forges Legacy
  def elaborateTerm (env, trm, term_type) = single_pass_elaborate_term_top (env, trm, term_type)  % backward compatibility for Forges Legacy

  def single_pass_elaborate_term_top (env, trm, term_type) =
    let trm = single_pass_elaborate_term (env, trm, term_type) in
    %% Resolve now rather than later to release space
    resolveMetaTyVars trm

  def single_pass_elaborate_term (env, trm, term_type) =
    % let _ = writeLine("tc: "^printType term_type^"\n"^printTerm trm) in
    case trm of
      | Fun (OneName (id, fixity), srt, pos) ->
        (let _ = elaborateCheckTypeForTerm (env, trm, srt, term_type) in 
	 %% resolve type from environment
         % let _ = writeLine("Trying to resolve name "^id^": "^printType srt) in
         case findVar(env, id, pos) of
           | Some(term as Var ((id, srt), a)) ->
             let srt = elaborateCheckTypeForTerm (env, term, srt, term_type) in
             Var ((id, srt), pos)
           | None ->
         case tryResolveNameFromType(env, trm, id, srt, pos) of
           | Some t -> t
           | _ -> 
	 case findVarOrOps (env, id, pos) of
	   | terms as _::_ ->
	     %% selectTermWithConsistentType calls consistentTypeOp?, which calls unifyTypes 
	     (case selectTermWithConsistentType (env, id, pos, terms, term_type) of
		| None -> trm
		| Some term ->
		  let srt = termType term in
		  let srt = elaborateCheckTypeForTerm (env, term, srt, term_type) in
		  (case term of
		     | Var ((id, _),          pos) -> Var ((id, srt),         pos)  % Now handled above
		     | Fun (OneName  idf,  _, pos) -> Fun (OneName  (fixateOneName  (idf,  fixity)), srt, pos)
		     | Fun (TwoNames qidf, _, pos) -> Fun (TwoNames (fixateTwoNames (qidf, fixity)), srt, pos)
		     | _ -> System.fail "Variable or constant expected"))
	   | [] ->
	     resolveNameFromType (env, trm, id, srt, pos))

      | Fun (TwoNames (id1, id2, fixity), srt, pos) -> 
	(let _ = elaborateCheckTypeForOpRef (env, trm, srt, term_type) in 
	 %% Either Qualified (id1, id2) or field selection
	 case findTheOp2 (env, id1, id2) of
           | Some info -> 
	     %% If Qualified (id1, id2) refers to an op, use the canonical name for that op.
	     let Qualified (q, id) = primaryOpName info in
	     let (tvs, srt, tm) = unpackFirstOpDef info in
	     let (_, srt) = metafyType (Pi (tvs, srt, typeAnn srt)) in
	     let term = Fun (TwoNames (q, id, info.fixity), srt, pos) in
	     let srt = elaborateCheckTypeForOpRef (env, term, srt, term_type) in
	     (case term of
		| Fun (TwoNames xx, _, pos) -> Fun (TwoNames xx, srt, pos)
		| _ -> System.fail ("Op expected for elaboration of "^id1^"."^id2^" as resolved to "^q^"."^id))
	   | None -> 
	     %% If Qualified (id1, id2) does not refer to an op, check for field selection
	     (case findVarOrOps (env, id1, pos) of
		| [big_term] ->
		  %% unqualified id1 refers to big_term
		  let big_type = termType big_term in
		  let big_type = checkType (env, big_type) in
		  let 
                    def projectRow (big_term, big_type, row, id2) =
		      %% See if id2 is one of the field selectors for the big type.
		      case row of
			| [] -> undeclared2 (env, trm, id1, id2, term_type, pos)
			| (field_id, field_type) :: row -> 
			  if id2 = field_id then
			    let field_type = checkType (env, field_type) in
			    let projector : MSTerm = Fun (Project id2, Arrow (big_type, field_type, pos), pos) in
			    let projection = (ApplyN ([projector, big_term], pos)) : MSTerm in
			    let _ = elaborateTypeForTerm (env, projection, field_type, term_type) in
			    projection
			  else
			    projectRow (big_term, big_type, row, id2)
		    def getProduct srt : Option (List (String * MSType)) = 
		      (case unfoldType (env, srt) of
			 | Product (row,       _) -> Some row
			 | Subtype (srt, pred, _) -> getProduct srt
			 | _ -> None)
		  in          
		    %% See if big_term is a product or a subtype of a product
		    (case getProduct big_type of
		       | Some row -> projectRow (big_term, big_type, row, id2)
		       | _ ->
		         %% Specware just reports an error here
		         %% Accord checks to see if id2 refers to a function whose domain is big_type
		         undeclared2 (env, trm, id1, id2, term_type, pos))
	        | [] -> 
		  %% both id1.id2 id1 fail to refer to anything
		  undeclared2 (env, trm, id1, id2, term_type, pos)
		| big_terms ->
		  %% id1 is ambiguous
		  %% Specware just reports an error here
		  %% Accord checks to see if id2 (id1) typechecks
		  undeclared2 (env, trm, id1, id2, term_type, pos)))

      | Fun (Embed (id, _), srt, pos) -> 
	let _  (* srt *) = elaborateCheckTypeForTerm (env, trm, srt, term_type) in
	%% using term_type instead of srt in the following was cause of bug 110 : "[] read as bogus Nil"
	resolveNameFromType (env, trm, id, srt, pos) 

      | Fun (Project id,srt,pos) -> 
	let srt = elaborateCheckTypeForTerm (env, trm, srt, term_type) in
	(case mkProject (env,id,srt,pos) of
	   | Some term -> term
	   | None -> undeclaredResolving (env,trm,id,term_type,pos))

    % | Fun (Select id,srt,pos) -> Fun (Select id,srt,pos)      (*** Not checked ***)
      | Fun (Embedded id, srt, pos) ->
	let a = freshMetaTyVar ("Embedded", pos) in
	let ty = Arrow(a, type_bool, pos) in
	(elaborateTypeForTerm (env, trm, ty, term_type);
	 elaborateTypeForTerm (env, trm, srt, ty);
	 (case unfoldType (env, srt) of
	    | Arrow (dom, _, _) -> 
	      (case isCoproduct (env, dom) of
		 | Some fields -> 
		   if exists? (fn (id2, _) -> id = id2) fields then
		     ()
		   else
		     error (env, 
			    "Name "^id^" is not among the constructors of "^ printType dom, 
			    pos)
		 | None -> 
		   pass2Error (env, dom, 
			       newLines ["Sum type with constructor "^id^" expected", 
					 "found instead "^printType dom], 
			       pos))
	    | _ -> pass2Error (env, srt, "Function type expected ", pos));
	 Fun (Embedded id, srt, pos))

      | Fun (PChoose qid, srt, pos) -> 
	%% Has type:  {f: base_type -> result_type | fa(m,n) equiv(m,n) => f m = f n} -> quot_type -> result_type
        %%   quot_type -- quotient type referenced by qid
        %%   equiv     -- equivalence relation in definition of quot_type
        (case findTheType (env.internal, qid) of
           | Some info ->
             (case unpackFirstTypeDef info of
                | (tvs, Quotient (base_body, equiv, _)) ->
                  %% In general, base_body and equiv will have free references to tvs
                  let base_type             = Pi (tvs, base_body, noPos)                      in
                  let (new_mtvs, base_type) = metafyType base_type                            in
                  let base_body             = typeInnerType base_type                         in
                  let new_type_args         = map (fn mtv -> MetaTyVar (mtv, noPos)) new_mtvs in
                  let quot_type             = Base (qid, new_type_args, noPos)                in
                  let result_type           = freshMetaTyVar ("PChoose_result", pos)          in
                  let high_arrow            = Arrow (quot_type, result_type, pos)             in
                  %% --
                  let low_arrow             = Arrow (base_type, result_type, pos)             in
                  let fvar = ("f",low_arrow) in
                  let mvar = ("m",base_type) in
                  let nvar = ("n",base_type) in
                  let lhs  = mkAppl (equiv, [mkVar mvar, mkVar nvar]) in % free refs to tvs
                  let rhs  = mkEquality (result_type, 
                                         mkApply (mkVar fvar, mkVar mvar),
                                         mkApply (mkVar fvar, mkVar nvar)) 
                  in
                  let body = mkBind (Forall,[mvar, nvar], mkImplies (lhs, rhs)) in  % free refs to tvs
                  let restricted_low_arrow  = Subtype (low_arrow, mkLambda (mkVarPat fvar, body), pos) in  % free refs to tvs
                  %% --
                  let lifting_arrow         = Arrow (restricted_low_arrow, high_arrow, pos)            in  % free refs to tvs
                  (elaborateTypeForTerm (env, trm, lifting_arrow, term_type);
                   elaborateTypeForTerm (env, trm, srt,           lifting_arrow);
                   %% now srt = term_type = lifting_arrow
                   Fun (PChoose qid, srt, pos))

                | _ ->
                  let ss = show qid in
                  (error (env, 
                          "In choose[" ^ ss ^ "], " ^ ss ^ " refers to a type that is not a quotient",
                          pos);
                   Fun (PChoose qid, srt, pos)))
           | _ ->
             let ss = show qid in
             (error (env, 
                     "In choose[" ^ ss ^ "], " ^ ss ^ " does not refer to a type",
                     pos);
              Fun (PChoose qid, srt, pos)))
              

      | Fun (PQuotient qid, srt, pos) ->  
        %% Has type:   base_type -> Quotient(base_type, equiv)
        %%   quot_type -- quotient type referenced by qid
        %%   equiv     -- equivalence relation in definition of quot_type
        (case findTheType (env.internal, qid) of
           | Some info ->
             (case unpackFirstTypeDef info of
                | (tvs, Quotient (base_body, equiv, _)) ->
                  %% In general, base_body and equiv will have free references to the tvs
                  let base_type             = Pi (tvs, base_body, noPos)                      in
                  let (new_mtvs, base_type) = metafyType base_type                            in
                  let new_type_args         = map (fn mtv -> MetaTyVar (mtv, noPos)) new_mtvs in
                  let quot_type             = Base (qid, new_type_args, noPos)                in              
                  let lifting_arrow         = Arrow (base_type, quot_type, pos)               in
                  (elaborateTypeForTerm (env, trm, lifting_arrow, term_type);
                   elaborateTypeForTerm (env, trm, srt,           lifting_arrow);
                   %% now srt = term_type = lifting_arrow
                   Fun (PQuotient qid, srt, pos))
                | _ ->
                  let ss = show qid in
                  (error (env, 
                          "In quotient[" ^ ss ^ "], " ^ ss ^ " refers to a type that is not a quotient",
                          pos);
                   Fun (PQuotient qid, srt, pos)))
           | _ ->
             let ss = show qid in
             (error (env, 
                     "In quotient[" ^ ss ^ "], " ^ ss ^ " does not refer to a type",
                     pos);
              Fun (PQuotient qid, srt, pos)))

      | Fun (Bool b, srt, pos) -> 
	(elaborateTypeForTerm (env, trm, type_bool, term_type) ; 
	 elaborateCheckTypeForTerm (env, trm, srt, type_bool);
	 Fun (Bool b, srt, pos))
	
      | Fun (Nat n, srt, pos) ->  
	(elaborateTypeForTerm (env, trm, type_nat, term_type);
	 elaborateCheckTypeForTerm (env, trm, srt, type_nat);
	 Fun (Nat n, srt, pos))
	
      | Fun (String s, srt, pos) -> 
	(elaborateTypeForTerm (env, trm, type_string, term_type);
	 elaborateCheckTypeForTerm (env, trm, srt, type_string);
	 Fun (String s, srt, pos))
	
      | Fun (Char ch, srt, pos) -> 
	(elaborateTypeForTerm (env, trm, type_char, term_type);
	 elaborateCheckTypeForTerm (env, trm, srt, type_char);
	 Fun (Char ch, srt, pos))
	
      | Var ((id, srt), pos) -> 
	let srt = elaborateCheckTypeForTerm (env, trm, srt, term_type) in
	Var ((id, srt), pos)

      | LetRec (decls, body, pos) -> 
	let 

          def declareFun (((id, srt), bdy), env) = 
	    addVariable (env, id, srt)

          def elaborateDecl env ((id, srt), bdy) = 
	    let terms = findVarOrOps (env, id, pos) in
	    let srt = checkType(env, srt) in
	    let bdy = single_pass_elaborate_term (env, bdy, srt) in
	    ((id, srt), bdy)
	in
	let env = foldr declareFun env decls in
	let decls = map (elaborateDecl env) decls in
	let bdy = single_pass_elaborate_term (env, body, term_type) in
	LetRec (decls, bdy, pos)

      | Let (decls, body, pos) -> 
	let env0 = env in
        let 
          def doDeclaration ((pat, bdy), (decls, env)) = 
	    let alpha = freshMetaTyVar ("Let", pos) in
	    (* In case the pattern is has a type constraint, move
	       this to the body such that the type constraint is 
	       attatched to alpha.
	       *)
	    let (pat, bdy) = 
	        case pat of
		  | TypedPat (pat, srt, pos) -> 
		    (pat, (TypedTerm (bdy, srt, pos)):MSTerm)
		  | _ -> (pat, bdy)
	    in             
	    let bdy = single_pass_elaborate_term (env0, bdy, alpha) in
	    let (pat, env) = elaboratePattern (env, pat, alpha) in
	    (Cons ((pat, bdy), decls), env)
          def maybeRedoDeclaration ((pat, bdy), decls) =
            let new_bdy = if ambiguousTerm? bdy
                           then single_pass_elaborate_term (env0, bdy, patternType pat)
                           else bdy
            in
            (pat, new_bdy) :: decls
	in         
	let (decls, body_env) = foldr doDeclaration ([], env) decls in
	let body = single_pass_elaborate_term (body_env, body, term_type) in
        let decls = foldr maybeRedoDeclaration [] decls in
	Let (decls, body, pos)

      | IfThenElse (test, thenTrm, elseTrm, pos) -> 
	let test = single_pass_elaborate_term (env, test, type_bool) in
	let thenTrm = single_pass_elaborate_term (env, thenTrm, term_type) in 
	let elseTrm = single_pass_elaborate_term (env, elseTrm, term_type) in
	IfThenElse (test, thenTrm, elseTrm, pos)

      | Record (row, pos) -> 
        let 
	  def unfoldConstraint (srt) = 
	    (case unfoldType (env, srt) of
	       | Product (rows, _) -> 
	         (if ~(length (row) = length (rows)) then
		    error (env, 
			   newLines [printTerm trm, "is incompatible with constraint", printType term_type], 
			   pos)
		  else 
		    ();
		  rows)
	       | MetaTyVar (mtv, _) ->
                 let row = map (fn (id, _)-> (id, freshMetaTyVar ("Record", pos))) row in
		 (linkMetaTyVar mtv ((Product (row, pos)));
		  row)
                        
	       | Subtype (srt, term, _) -> 
		 unfoldConstraint (srt)        

	       | And (srt :: _, _) -> % TODO: be smarter about choosing among alternatives
		 unfoldConstraint srt        

	       | sv -> 
		 (pass2Error (env, 
			      sv, 
			      printTerm trm^" is constrained to be of an incompatible type "^newline^ printType term_type, 
			      pos);
		  map (fn (id, _)-> (id, freshMetaTyVar ("Record_incompatible", pos))) row))
	in
	let tyrows = unfoldConstraint (term_type) in
        if length tyrows ~= length row
          then (error(env, "Mismatch in number of fields", pos);
                Record (row, pos))
        else
	let trow = zip (row, tyrows) in 
	let row = map (fn ((id, t), (id2, ty))->
		       if id = id2 then
			 (id, single_pass_elaborate_term (env, t, ty))
		       else 
			 (error (env, "Field-name "^id^
				 " is not the one imposed by type constraint.  Expected field-name is: "^
				 id2, pos);
                          (id, t)))
	              trow
	in
	  Record (row, pos)

      | Lambda (rules, pos) -> 
	let alpha = freshMetaTyVar ("Lambda_a", pos) in
	let beta  = freshMetaTyVar ("Lambda_b", pos) in
	let ty    = (Arrow (alpha, beta, pos)) in
	let _     = elaborateType (env, ty, term_type) in 
	Lambda (map (fn (pat, cond, term)->
		     let (pat, env) = elaboratePattern (env, pat, alpha) in
		     let term = single_pass_elaborate_term (env, term, beta) in
		     let cond = single_pass_elaborate_term (env, cond, type_bool) in
		     (pat, cond, term)) 
		    rules,
	       pos)

      | The ((id,srt), term, pos) ->
	let srt = checkType(env, srt) in
        let env = addVariable (env,id,srt) in
	let _ = elaborateType (env, srt, term_type) in
	let term = single_pass_elaborate_term (env, term, type_bool) in
	The ((id,srt), term, pos)

      | Bind (bind, vars, term, pos) ->
	let _ = elaborateType (env, term_type, type_bool) in
	let (vars, env) = 
	    foldl (fn ((vars, env), (id, srt)) ->
		   let srt = checkType (env, srt) in
		   (Cons ((id, srt), vars), 
		    addVariable (env, id, srt)))
	          ([], env) 
		  vars 
	in
        let vars = reverse vars in
	Bind (bind, vars, single_pass_elaborate_term (env, term, term_type), pos)

      | TypedTerm (term, srt, _) ->
        let srt  = elaborateType (env, srt, term_type) in
	let term = single_pass_elaborate_term (env, term, srt) in
	term

      | Seq (terms, pos) -> 
	let
          def elab ts = 
	    case ts of
	      | [] -> []
	      | [t] -> [single_pass_elaborate_term (env, t, term_type)]
	      | (t::ts) -> 
	        let alpha = freshMetaTyVar ("Seq", pos) in
		let t = single_pass_elaborate_term (env, t, alpha) in
		Cons (t, elab ts)
	in
	  Seq (elab terms, pos)

      | ApplyN ([t1 as Fun (Embedded _, _, _), t2], pos) -> 
        let alpha = freshMetaTyVar ("ApplyN_Embedded", pos) in
	let ty    = Arrow (alpha, term_type, pos) in
	let t2    = single_pass_elaborate_term (env, t2, alpha) in
	let t1    = single_pass_elaborate_term (env, t1, ty) in
	ApplyN ([t1, t2], pos)

      | ApplyN ([t1 as Fun (Project _, _, _), t2], pos) -> 
	let alpha = freshMetaTyVar ("ApplyN_Project", pos) in
	let ty    = Arrow (alpha, term_type, pos) in
	let t2    = single_pass_elaborate_term (env, t2, alpha) in
	let t1    = single_pass_elaborate_term (env, t1, ty) in
	ApplyN ([t1, t2], pos)
	
      | ApplyN ([t1 as Fun (f1, s1, _), t2], pos) -> 
        let alpha = freshMetaTyVar ("ApplyN_Fun", pos) in
	let ty    = Arrow (alpha, term_type, pos) in
        let (t1, t2) =
            if env.firstPass?
              then
                let t2 = single_pass_elaborate_term      (env, t2, alpha) in
                let t1    = single_pass_elaborate_term_head (env, t1, ty, trm) in
                %% Repeated for help in overload resolution once argument type is known
                if ambiguousTerm? t2 then
                  let t2 = single_pass_elaborate_term (env, t2, alpha) in
                  %let t1  = case t1 of
                  %             | Fun(OneName _,_,_) -> single_pass_elaborate_term (env, t1, ty)
                  %             | _ -> t1
                  % in
                  (t1, t2)
                else (t1, t2)
              else
                let t1 = single_pass_elaborate_term_head (env, t1, ty, trm) in
                let t2 = single_pass_elaborate_term      (env, t2, alpha) in
                (t1, t2)
        in
	%% This is same effect as old code, but restructured
	%% so it's easier to intercept the XML references
	if env.firstPass? then
	  ApplyN ([t1, t2], pos)
	else if f1 = Equals then
	  %let t1 = adjustEqualityType (env, s1, t1, t2) in
	  ApplyN ([t1, t2], pos)
	else if f1 = NotEquals then
	  %let t1 = adjustEqualityType (env, s1, t1, t2) in
	  ApplyN ([t1, t2], pos)
	else if typeCognizantOperator? f1 then
	  addTypeAsLastTerm (env, 
			     trm,
			     ApplyN ([t1, t2], pos),
			     term_type)
        else
	  ApplyN ([t1, t2], pos)

      | ApplyN ([t1, t2], pos) ->
	let alpha = freshMetaTyVar ("ApplyN_2", pos) in
	let ty    = Arrow (alpha, term_type, pos) in
	let t2    = single_pass_elaborate_term (env, t2, alpha) in
	let t1    = single_pass_elaborate_term (env, t1, ty) in
	ApplyN ([t1, t2], pos)

      %% Allow for partially type-checked terms
      | Apply(t1, t2, pos) -> single_pass_elaborate_term (env, ApplyN ([t1, t2], pos), term_type)

      | ApplyN (terms, pos) ->
	let 
          def tagTermWithInfixInfo (term : MSTerm) : FixatedTerm =
	    case term of
	      | Fun (OneName (_,  Nonfix),  _, pos) -> Nonfix term
	      | Fun (OneName (_,  Infix p), _, pos) -> Infix (term, p)
              | Fun (OneName ("Cons",  _), _, pos) -> Infix(term, (Right, 24))
	      | Fun (OneName (id, _),       _, pos) ->
	        (case consistentTag (findVarOrOps (env, id, pos)) of
		   | (true, (Some p)) -> Infix (term, p)
		   | (true, _)      -> Nonfix term
		   | _ ->
		     (error (env, "Inconsistent infix information for overloaded op: " ^ id,
			     pos);
		      Nonfix term))
	      | Fun (TwoNames (_ , _, Nonfix),  _, pos) -> Nonfix term
	      | Fun (TwoNames (_ , _, Infix p), _, pos) -> Infix (term, p)
	      | Fun (TwoNames (id1, id2, _),    _, pos) ->
		%% If, due to union semantics, findOps always returns 0 or 1 hits for Q.Id, 
		%% then consistentTag will necessarily return (true, priority).
		(case findTheOp2 (env, id1, id2) of
		   | Some info ->
		     (case info.fixity of
			| Infix p -> Infix  (term, p)
			| _ -> Nonfix term)
		   | _                    -> Nonfix term)
	      | Fun (And,       _, _) -> Infix (term, (Right, 15))
	      | Fun (Or,        _, _) -> Infix (term, (Right, 14))
	      | Fun (Implies,   _, _) -> Infix (term, (Right, 13))
	      | Fun (Iff,       _, _) -> Infix (term, (Right, 12))
	      | Fun (Equals,    _, _) -> Infix (term, (Left, 20))
	      | Fun (NotEquals, _, _) -> Infix (term, (Left, 20))
	      | Fun (RecordMerge,_,_) -> Infix (term, (Left, 25))
	      | _ -> Nonfix term
	in 
	let term = resolveInfixes (Some env, tagTermWithInfixInfo, pos, terms) in
	let new = single_pass_elaborate_term (env, term, term_type) in
	new

      %% These should only appear as the head of an apply (see one of the ApplyN cases above):
      | Fun (Not,       srt, pos) -> (error (env, cantuse "~",   pos); trm)
      | Fun (And,       srt, pos) -> (error (env, cantuse "&&",  pos); trm)
      | Fun (Or,        srt, pos) -> (error (env, cantuse "||",  pos); trm)
      | Fun (Implies,   srt, pos) -> (error (env, cantuse "=>",  pos); trm)
      | Fun (Iff,       srt, pos) -> (error (env, cantuse "<=>", pos); trm)
      | Fun (Equals,    srt, pos) -> (error (env, cantuse "=",   pos); trm)
      | Fun (NotEquals, srt, pos) -> (error (env, cantuse "~=",  pos); trm)
       
      | And (tms, pos) -> And (map (fn tm -> single_pass_elaborate_term(env, tm, term_type)) tms, pos)
	
      | term -> (%System.print term;
		 term)

  def cantuse inbuilt = "Can't use inbuilt operator '"^inbuilt^"' as an expression -- use '("^inbuilt^")' instead."

  def single_pass_elaborate_term_head (env, t1, ty, trm) =
    case t1 of
      | Fun (Not, srt, pos) -> 
	(elaborateTypeForTerm (env, trm, srt, ty);
	 Fun (Not, srt, pos))

      | Fun (And, srt, pos) -> 
	(elaborateTypeForTerm (env, trm, srt, ty);
	 Fun (And, srt, pos))

      | Fun (Or, srt, pos) -> 
	(elaborateTypeForTerm (env, trm, srt, ty);
	 Fun (Or, srt, pos))

      | Fun (Implies, srt, pos) -> 
	(elaborateTypeForTerm (env, trm, srt, ty);
	 Fun (Implies, srt, pos))

      | Fun (Iff, srt, pos) -> 
	(elaborateTypeForTerm (env, trm, srt, ty);
	 Fun (Iff, srt, pos))

      | Fun (Equals, srt, pos) -> 
	(elaborateTypeForTerm (env, trm, srt, ty);
	 Fun (Equals, srt, pos))

      | Fun (NotEquals, srt, pos) -> 
	(elaborateTypeForTerm (env, trm, srt, ty);
	 Fun (NotEquals, srt, pos))

      | Fun (RecordMerge, srt, pos) ->
	(let a = freshMetaTyVar ("RecordMerge_a", pos) in
	 let b = freshMetaTyVar ("RecordMerge_b", pos) in
	 let c = freshMetaTyVar ("RecordMerge_c", pos) in
	 let fresh_merge_type = Arrow(Product ([("1", a), ("2", b)], pos), c, pos) in
	 (elaborateTypeForTerm(env, trm, srt, fresh_merge_type);
	  elaborateTypeForTerm(env, trm, fresh_merge_type, ty);
	  let def notEnoughInfo() =
		if env.firstPass? then 
		  t1
		else 
		  (error(env, "Can't determine suitable type for <<: " ^ printType srt, pos);
		   t1)
	  in
	  case isArrow(env,srt) of
	    | Some (dom,rng) ->
	      (case isProduct (env,dom) of
		 | Some [("1",s1),("2",s2)] ->
		   (case (isProduct(env,s1),isProduct(env,s2)) of
		      | (Some row1,Some row2) ->
			let merged_type = Product(mergeFields(env,row1,row2,pos),pos) in
			(elaborateTypeForTerm(env,trm,rng,merged_type);
			 Fun(RecordMerge, srt, pos))
		      | _ -> notEnoughInfo())
		 | _ -> notEnoughInfo())
	    | None -> notEnoughInfo()))

      | _ ->
	single_pass_elaborate_term (env, t1, ty)

   op makeEqualityType : MSType * Position -> MSType
  def makeEqualityType (srt, pos) =
    %% let a = freshMetaTyVar noPos in 
    %% parser has it's own sequence of metaTyVar's, which are distinguished
    %% from those produced by freshMetaTyVar:
    %% they will be named "#parser-xxx" instead of "#fresh-xxx"
    Arrow (Product ([("1", srt), ("2", srt)], noPos), 
	   type_bool,
	   pos)

  % ========================================================================

  %% express as table to simplify ad hoc additions via lisp code:
  def typeCognizantOperators : List (Id * Id) =
    [ %% input

      ("XML" ,          "readXMLFile"),
      ("<unqualified>", "readXMLFile"),

      ("XML" ,          "parseXML"),
      ("<unqualified>", "parseXML"),

      ("XML" ,          "parseUnicodeXML"),
      ("<unqualified>", "parseUnicodeXML"),

      ("XML",           "internalize_Document"), 
      ("<unqualified>", "internalize_Document"), 

      ("XML",           "internalize_Element"), 
      ("<unqualified>", "internalize_Element"), 

      %% output

      ("XML" ,          "writeXMLFile"),
      ("<unqualified>", "writeXMLFile"),

      ("XML" ,          "printXML"),
      ("<unqualified>", "printXML"),

      ("XML" ,          "printUnicodeXML"),
      ("<unqualified>", "printUnicodeXML")

     ]

  def typeCognizantOperator? (f1 : MS.Fun) : Bool = 
    case f1 of
      | TwoNames (id1, id2, _) ->
        (id1, id2) in? typeCognizantOperators
      | _ -> false


  % ========================================================================

  op  selectTermWithConsistentType: LocalEnv * Id * Position * List MSTerm * MSType -> Option MSTerm
  def selectTermWithConsistentType (env, id, pos, terms, srt) =
    %% calls consistentTypeOp?, which calls unifyTypes 
    case terms of
      | [term] -> Some term
      | _ ->
        let def findUnqualified tms =
	      case tms of
		| [] -> None
		| tm::rtms ->
		  (case tm of
		     | Fun (OneName  (     _,_), _, _) -> Some tm
		     | Fun (TwoNames (id1, _,_), _, _) ->
		       if id1 = UnQualified then
			 Some tm
		       else
			 findUnqualified rtms
		     | _ -> findUnqualified rtms)
	in
        case unlinkType srt of
	  | MetaTyVar _ ->
	    if env.firstPass? then 
	      None
	    else
	      (case findUnqualified terms of
		| Some term -> Some term
		| None ->
	          (error (env,
			  "Several matches for overloaded op " ^ id ^ " of " ^
			  (printMaybeAndType srt) ^
			  (foldl (fn (str, tm) -> str ^
				  (case tm of
				     | Fun (OneName  (     id2, _), _, _) -> " "^id2
				     | Fun (TwoNames (id1, id2, _), _, _) -> " "^id1^"."^id2))
				 " : "
				 terms),
			  pos);
		   None))
	  | rtype ->
	    let srtPos = typeAnn srt in
	    (case filter (consistentTypeOp? (env, withAnnS (rtype, srtPos),true)) terms of
	       | [] -> (error (env,
			       "No matches for op " ^ id ^ " of " ^ (printMaybeAndType srt),
			       pos);
			None)
	       | [term] -> Some term
	       | consistent_terms ->
	         if env.firstPass? then
		   None
		 else
		   (let consistent_terms_with_exactly_matching_subtypes = 
		        filter (consistentTypeOp? (env, withAnnS (rtype, srtPos), false)) 
			       consistent_terms
		    in
		    let plausible_terms = if consistent_terms_with_exactly_matching_subtypes = [] then 
		                            consistent_terms 
					  else 
					    consistent_terms_with_exactly_matching_subtypes 
		    in
		    case plausible_terms of
		      %% If only one term matches including subtypes, choose it
	              | [term] -> Some term
		      | _ ->
		        %% If there is a valid unqualified term then prefer that because you
		        %% cannot explicitly qualify with unqualified!
			case findUnqualified plausible_terms of
			  | Some term -> Some term
			  | None ->
			    %% Specware just reports an error here
			    %% Accord looks to see if there is a unique most-precise term,
			    %% preferring f : A|p -> B to f : A -> B
			    (error (env,
				    "Several matches for overloaded op " ^ id ^ " of " ^
				    (printMaybeAndType srt) ^
				    (foldl (fn (str, tm) -> str ^
					    (case tm of
					       | Fun (OneName  (     id2, _), _, _) -> " "^id2
					       | Fun (TwoNames (id1, id2, _), _, _) -> " "^id1^"."^id2))
				           " : "
					   consistent_terms),
				    pos);
			     None)))

  def printMaybeAndType srt =
    case srt of
      | And (srt :: srts, _) ->
        foldl (fn (s, srt) -> s ^ " and type " ^ (printType srt) ^ "\n")
	("type " ^ (printType srt) ^ "\n")
	srts
      | _ ->
	"type " ^ (printType srt) 

  def consistentTypeOp? (env, srt1, ignoreSubtypes?) (Fun (_, srt2, _)) =
   %% calls unifyTypes, but then resets metatyvar links to None...
   consistentTypes? (env, srt1, srt2, ignoreSubtypes?)

  % ========================================================================

  def elaborateCheckTypeForTerm (env, term, givenType, expectedType) = 
   elaborateTypeForTerm (env, term, checkType (env, givenType), expectedType)

  op elaborateCheckTypeForOpRef (env: LocalEnv, term: MSTerm, givenType: MSType, expectedType: MSType): MSType =
    if allowDependentSubTypes? && ~env.firstPass?
      then elaborateTypeForTerm(env, term, checkType1(env, givenType, false), expectedType)
      else elaborateCheckTypeForTerm(env, term, givenType, expectedType)

  def elaborateTypeForTerm (env, term, givenType, expectedType) = 
    %% unifyTypes has side effect of modifying metaTyVar links
    let success = unifyTypes env true givenType expectedType in
    ((if success || env.firstPass? then
	()
      else
	let pos        = termAnn   term in
	let termString = printTerm term in
	let tsLength   = length termString in
	let fillerA    = blankString (10 - tsLength) in
	let fillerB    = blankString (tsLength - 10) in
	let msg        = newLines ["Could not match type constraint", 
				   fillerA ^ termString ^ " of " ^ (printMaybeAndType givenType), 
				   fillerB ^ "with expected " ^ (printMaybeAndType expectedType)]
	in
          % let _ = fail msg in
	  error (env, msg, pos));
     givenType)

   % If f : A -> B, and x : C, then for f(x) we want to see
   % an error message like:
   %
   % Could not match type constraint
   %       x of type C
   %       with expected type A
   %
   % Most of the time, givenType is C (the type of the argument)
   % while expectedType is A (the domain type of the function).
   %
   % ---
   %
   % Apparently the sense of givenType and expectedType used to be 
   %  reversed for some obscure reason, but they seem ok now here.
   %  If there are problems, fix them elsewhere, and don't mangle 
   %  this code!

  op elaborateTypeForPat (env: LocalEnv, pat: MSPattern, givenType: MSType, expectedType: MSType): MSType =
    let givenTypeChecked = checkType (env, givenType) in
    %% unifyTypes has side effect of modifying metatyvar links
    let success = unifyTypes env true givenTypeChecked expectedType in
    ((if success then
	()
      else             
	let msg = newLines ["Could not match type " ^ printType givenType, 
			    "                with " ^ printType expectedType]
	in
	  error (env, msg, patAnn pat));
     givenTypeChecked)

  def elaborateType (env, s1, s2) = 
    let s1Checked = checkType (env, s1) in
    %% unifyTypes has side effect of modifying metatyvar links
    let success = unifyTypes env true s1Checked s2 in
    ((if success then
	()
      else             
	let msg = newLines ["Could not match type " ^ printType s1, 
			    "                with " ^ printType s2]
	in
	  error (env, msg, chooseNonZeroPos (typeAnn s1, typeAnn s2)));
     s1Checked)

  % ========================================================================
  %% Called inside single_pass_elaborate_term 

  def mkEmbed0 (env, srt, id) =
    case lookupEmbedId (env, id, srt) of
      | Some None -> Some id
      | _   -> None
        
  def lookupEmbedId (env, id, srt) = 
    case unfoldType (env, srt) of
      | CoProduct(row, _) -> 
        let def lookup row =
	      case row of
		| [] -> None : Option (Option MSType)
		| (found_id, entry) :: row ->  
		  if id = found_id then
		    Some (case entry of
			    | None   -> None
			    | Some s -> Some (checkType (env, s)))
		  else 
		    lookup row
	in
	  lookup row
      | Subtype (srt, pred, _) -> lookupEmbedId (env, id, srt)
      | _ -> None

  def mkEmbed1 (env, srt, trm, id, pos) = 
    case isArrowCoProduct (env, srt) of
      | Some (sum_type, row) ->
        let 
	  %% This checks that a sum-type constructor is given the proper type
          def findId ls = 
	    case ls of
	      | [] -> None   % Some (undeclaredName (env, trm, id, srt, pos))
	      | (constructor_id, Some constructor_dom_type) :: row -> 
	        if id = constructor_id then
		  %%  let _ = String.writeLine ("coprod: "^printType (Arrow (s, CoProduct (row, pos0)), pos0)) in
		  %%  let _ = String.writeLine ("srt:  "^printType srt) in
		  %%  let _ = String.writeLine ("srt1: "^printType found_type) in
		  %%  let _ = String.writeLine ("dom:  "^printType (sum_type, pos)) in
		  let constructor_dom_type = checkType (env, constructor_dom_type) in
		  let _ (* dom *) = elaborateType (env, constructor_dom_type, withAnnS (sum_type, pos)) in
		  Some (Fun (Embed (id, true), checkType (env, srt), pos))
		else 
		  findId row
	      | _ :: row -> findId row
	in
	  findId row
      | _ -> None

  def isArrowCoProduct (env, srt) : Option (MSType * List (Id * Option MSType)) =
    case unfoldType (env, srt) of
      | Arrow (dom, rng, _) -> 
        (case isCoproduct (env, rng) of
	   | Some row -> Some (dom, row)
	   | None -> None)
      | _ -> None

  def isCoproduct (env, srt)  = 
    case unfoldType (env, srt) of
      | CoProduct (row, _)    -> Some row
      | Subtype   (srt, _, _) -> isCoproduct (env, srt)
      | _ -> None

  op  isProduct: LocalEnv * MSType -> Option(List (Id * MSType))
  def isProduct (env, srt)  = 
    case unfoldType (env, srt) of
      | Product (fields, _) -> Some fields
      | Subtype (srt, _, _) -> isProduct (env, srt)
      | _ -> None

  def isArrow (env, srt): Option (MSType * MSType)  = 
    case unfoldType (env, srt) of
      | Arrow (dom, rng, _) -> Some (dom, rng)
      | Subtype(ssrt, _, _) -> isArrow (env, ssrt)
      | _ -> None

  def mergeFields(env,row1,row2,pos) =
    let 
      def loop(row1,row2,merged) =
	case (row1, row2) of
	  | ([], _)  -> merged ++ row2
	  | (_,  []) -> merged ++ row1
	  | (e1::r1, e2::r2) ->
	    case compare (e1.1, e2.1) of
	      | Less    -> loop (r1, row2, merged ++ [e1])
	      | Greater -> loop (row1, r2, merged ++ [e2])
	      | Equal   -> (elaborateType(env,
					  Product([e1], pos),
					  Product([e2], pos));
			    loop (r1, r2, merged ++ [e2]))
    in 
      loop(row1,row2,[])

  %% If id is the unique name of a constructor, use that constructor
  def uniqueConstr (env, trm, id, pos) =
    case StringMap.find (env.constrs, id) of
      | Some [(qid, srt_info)] ->
        let (v_srt, c_srt) = metafyBaseType (qid, srt_info, termAnn trm) in
	let id_srt = case c_srt of
		       | CoProduct (fields, pos) ->
	                 (case findLeftmost (fn (id2, _) -> id = id2) fields of
			    | Some (_, Some dom_srt) -> Arrow (dom_srt, v_srt, pos)
			    | _ -> v_srt)
		       | _ -> v_srt
	in
	(case mkEmbed0 (env, id_srt, id) of
	   | Some id -> Some (Fun (Embed (id, false), checkType (env, id_srt), pos))
	   | None -> mkEmbed1 (env, id_srt, trm, id, pos))
      | _ -> None

  def mkProject (env, id, srt, pos) = 
    case unfoldType (env, srt) of
      | Arrow (dom, rng, _) -> 
        (let 
           def analyzeDom dom =
	     case unfoldType (env, dom) of
	       | Product (row, _) -> 
                 (let def findId ls = 
                        case ls of
                          | [] -> None : Option MSTerm
                          | (selector_id, selector_rng_srt) :: ids -> 
                            if id = selector_id then
                              (elaborateType (env, selector_rng_srt, withAnnS (rng, pos));
                               Some (Fun (Project id, srt, pos)))
                            else 
                              findId ids
		  in
		    findId row)
	       | Subtype (ssrt, _, _) -> analyzeDom ssrt
	       | _ -> None
	 in 
	   analyzeDom dom)
      | Subtype (ssrt, _, _) -> mkProject (env, id, ssrt, pos)
      | _ -> None
      
  def consistentTag competing_pterms =
    %% If one of the alternatives (found by findVarOrOps) has optional infix priority
    %% and the others either have the same infix priority or are not infix ops then,
    %% return (true, priority), otherwise return (false, None).
    %% In other words, we will complain if F or Foo.F is ambigous among terms that
    %% have differing infix priorities, but allow prefix versions.
    %% findVarOrOps should never return any OneName
    case competing_pterms of
      | (Fun (OneName  (_,    Infix priority), _, pos))::r -> consistentInfixMSTerms (r, Some priority)
      | (Fun (TwoNames (_, _, Infix priority), _, pos))::r -> consistentInfixMSTerms (r, Some priority) % r must be []
      | _::r                                               -> consistentInfixMSTerms (r, None)
      | _                                                  -> (true, None)

  def consistentInfixMSTerms (competing_pterms, optional_priority) = 
    case competing_pterms of
      | [] -> (true, optional_priority)
      | (Fun (OneName (_, Infix element_priority), _, pos))::tail ->
        (case optional_priority of
	   | None -> consistentInfixMSTerms (tail, Some element_priority)
	   | Some priority -> (if element_priority = priority then
				 consistentInfixMSTerms (tail, optional_priority)
			       else 
				 (false, None)))
      | (Fun (TwoNames (_, _, Infix element_priority), _, pos))::tail ->
	(case optional_priority of
	   | None -> consistentInfixMSTerms (tail, Some element_priority)
	   | Some priority -> (if element_priority = priority then
				 consistentInfixMSTerms (tail, optional_priority)
			       else 
				 (false, None)))
      | _::tail -> consistentInfixMSTerms (tail, optional_priority)
       
   def undeclaredName (env, trm, id, srt, pos) =
    if env.firstPass? then %&& undeterminedType? s 
      trm
    else
      (error (env, "Name "^id^" could not be identified", pos);
       % raise (TypeCheck (pos, "Name "^id^" could not be identified"));
       Fun (OneName (id, Nonfix), srt, pos))

  def ambiguousCons (env, trm, id, srt, pos) =
    if env.firstPass? then %&& undeterminedType? s 
      trm
    else
      (error (env, "Constructor "^id^" could not be disambiguated", pos);
       Fun (OneName (id, Nonfix), srt, pos))

  def undeclared2 (env, trm, id1, id2, srt, pos) =
    if env.firstPass? then %&& undeterminedType? s 
      trm
    else
      (error (env, id1^"."^id2^" has not been declared as a qualified name or as a field selection", pos);
       % raise (TypeCheck (pos, id1^"."^id2^" has not been declared as a qualified name or as a field selection"));
       Fun (TwoNames (id1, id2, Nonfix), srt, pos))

  def undeclaredResolving (env, trm, id, srt, pos) = 
    if env.firstPass? then %&& undeterminedType? s
      trm
    else
      (error (env, "Name "^id^" could not be identified; resolving with "^printType srt, pos);
       % raise (TypeCheck (pos, "Name "^id^" could not be identified; resolving with "^printType srt));
       (Fun (OneName (id, Nonfix), srt, pos)) : MSTerm)

  % ========================================================================
  %% Called inside single_pass_elaborate_term 
  % ========================================================================

  def elaboratePattern (env, p, type1) =
    let (pat, env, _) = elaboratePatternRec (env, p, type1, []) in
    (pat,env)

  op  elaboratePatternRec: LocalEnv * MSPattern * MSType * List Id -> MSPattern * LocalEnv *  List Id 
  def elaboratePatternRec (env, p, type1, seenVars) =
    let type1 = checkType (env, type1) in
    let 
      def addSeenVar(id, seenVars, env, pos) =
	if id in? seenVars then
	  (error (env, "Variable "^id^" repeated in pattern.", pos);
	   (env,seenVars))
	else 
	  (env, Cons (id, seenVars))
    in
    case p of
      | WildPat (s, pos) -> (WildPat (elaborateTypeForPat (env, p, s, type1), pos), env, seenVars)
      | BoolPat   _ -> (elaborateTypeForPat (env, p, type_bool, type1);   (p, env, seenVars))
      | NatPat    _ -> (elaborateTypeForPat (env, p, type_nat, type1);    (p, env, seenVars))
      | StringPat _ -> (elaborateTypeForPat (env, p, type_string, type1); (p, env, seenVars))
      | CharPat   _ -> (elaborateTypeForPat (env, p, type_char, type1);   (p, env, seenVars))
      | VarPat ((id, srt), pos) -> 
        let srt = elaborateTypeForPat (env, p, srt, type1)  in 
	(case lookupEmbedId (env, id, srt) of
	   | Some None -> (EmbedPat (id, None, srt, pos), env, seenVars)
	   | Some _ -> 
	     (error (env, "Constructor "^id^" expects an argument, but was given none", pos);
	      % raise (TypeCheck (pos, "Constructor "^id^" expects an argument, but was given none"));
	      (VarPat ((id, srt), pos), env, seenVars))
	   | None ->
	     if undeterminedType? srt then
	       (case StringMap.find (env.constrs, id) of
		  | None ->
		    let (env,seenVars) = addSeenVar(id,seenVars,env,pos) in
		    (VarPat ((id, srt), pos), addVariable (env, id, srt), seenVars)
		  | Some [(qid, srt_info)] ->
		    let (v_srt, c_srt) = metafyBaseType (qid,srt_info,pos) in
		    (VarPat ((id, v_srt), pos), env, seenVars)
		  | Some _ -> (VarPat ((id, srt), pos), env, seenVars))
	     else
	       let (env,seenVars) = addSeenVar(id,seenVars,env,pos) in
	       (VarPat ((id, srt), pos), addVariable (env, id, srt), seenVars))
      | TypedPat (pat, srt, _) -> 
	let srt = elaborateTypeForPat (env, p, srt, type1) in
	let (p, env, seenVars) = elaboratePatternRec (env, pat, srt, seenVars) in
	(p, env, seenVars)
      | AliasPat (pat1, pat2, pos) ->
	let (pat1, env, seenVars) = elaboratePatternRec (env, pat1, type1, seenVars) in
	let (pat2, env, seenVars) = elaboratePatternRec (env, pat2, type1, seenVars) in
	(AliasPat (pat1, pat2, pos), env, seenVars)
      | EmbedPat (embedId, pattern, type0, pos) ->
	let type0 = elaborateTypeForPat (env, p, type0, type1) in
	let type0 =
	    if undeterminedType? type0 then
	       %% See if there is only one constructor with this name
	       (case StringMap.find (env.constrs, embedId) of
		  | Some [(qid,srt_info)] ->
		    let (v_srt, c_srt) = metafyBaseType (qid, srt_info, pos) in
		    elaborateTypeForPat (env, p, v_srt, type1)
		  | _ -> type0)
	     else
	       type0
	in
	  if env.firstPass? && undeterminedType? type0 then
	    let (env, epat, seenVars) =
	        case pattern of
		  | None -> (env,None, seenVars)
		  | Some pat ->
	            let alpha = freshMetaTyVar ("EmbedPat_a", pos) in
		    let (pat, env, seenVars) = elaboratePatternRec (env, pat, alpha, seenVars) in
		    (env, Some pat, seenVars)
	    in
	    (EmbedPat (embedId, epat, type0, pos), env, seenVars)
	  else
	    let srt = lookupEmbedId (env, embedId, type0) in
	    let (env, pat, seenVars) = 
	        (case (srt, pattern) of
		   | (Some (Some srt), Some pat) -> 
		     let (pat, env, seenVars) = elaboratePatternRec (env, pat, srt, seenVars) in
		     (env, Some pat, seenVars)

		   | (Some None, None) -> (env, None, seenVars)
		   | (None, None) -> 
		     (error (env, "Type for constructor "
			     ^ embedId
			     ^ " not found. Resolving with type "
			     ^ printType type1, pos);
		      (env, None, seenVars))
		   | (None, Some pat) -> 
		     let alpha = freshMetaTyVar ("EmbedPat_b", pos) in
		     let (pat, env, seenVars) = elaboratePatternRec (env, pat, alpha, seenVars)
		     in
		     (error (env, "Type for constructor "
			     ^ embedId
			     ^ " not found. Resolving with type "
			     ^ printType type1, pos);
		      (env, None, seenVars))
		   | (Some None, Some pat) -> 
		     (error (env, newLines ["Constructor "
					    ^ embedId
					    ^ " takes no argument", 
					    "but was given "
					    ^ printPattern pat], pos);
		      (env, Some pat, seenVars))
		   | (Some (Some _), None) -> 
		     (error (env, "Argument expected for constructor "
			     ^ embedId, pos);
		      (env, None, seenVars)))
	    in
	      (EmbedPat (embedId, pat, type1, pos), env, seenVars)
      | RecordPat (row, pos) ->
	let r = map (fn (id, srt)-> (id, freshMetaTyVar ("RecordPat", pos))) row in
	let _ = elaborateTypeForPat (env, p, (Product (r, pos)), type1) in
	let r = zip (r, row) in
	let (r, env, seenVars) = 
	    foldl (fn ((row, env, seenVars), ((id, srt), (_, p))) ->
		   let (p, env, seenVars) = elaboratePatternRec (env, p, srt, seenVars) in
		   (Cons ((id, p), row), env, seenVars))
	      ([], env, seenVars) r
	in
          (RecordPat (reverse r, pos), env, seenVars)

      | QuotientPat (pat, qid, pos) ->
	let v = freshMetaTyVar ("QuotientPat", pos) in
        let (pat, env, seenVars) = elaboratePatternRec (env, pat, v, seenVars) in
        (case findTheType (env.internal, qid) of
           | Some info ->
             (case unpackFirstTypeDef info of
                | (tvs, Quotient (base_body, equiv, _)) ->
                  %% In general, base_body and equiv will have free references to the tvs
                  %% TODO: More checking needed here?
                  (QuotientPat (pat, qid, pos), env, seenVars)
                | _ ->
                  let ss = show qid in
                  (error (env, 
                          "In pattern quotient[" ^ ss ^ "], " ^ ss ^ " refers to a type that is not a quotient",
                          pos);
                   (QuotientPat (pat, qid, pos), env, seenVars)))

           | _ ->
             let ss = show qid in
             (error (env, 
                     "In pattern quotient[" ^ ss ^ "], " ^ ss ^ " does not refer to a type",
                     pos);
              (QuotientPat (pat, qid, pos), env, seenVars)))

      | RestrictedPat (pat, term, pos) ->
	let (pat, env, seenVars) = elaboratePatternRec (env, pat, type1, seenVars) in
	let term = single_pass_elaborate_term (env, term,  type_bool) in
	(RestrictedPat (pat, term, pos), env, seenVars)

      | p -> (System.print p; System.fail "Nonexhaustive")


  % ========================================================================

  def pass2Error (env, _(* s *), msg, pos) =
    if env.firstPass? then %&& undeterminedType? s 
      ()
    else 
      error (env, msg, pos)

  def blankString (n:Int) =
    if n <= 0 then 
      "" 
    else
      let oneHundredSpaces = "                                                                                                    " in
      if n < 100 then
	subFromTo (oneHundredSpaces, 0, n)
      else
	oneHundredSpaces ^ blankString (n - 100)

  def newLines lines = 
    case lines of
      | [] -> ""
      | [line] -> line
      | line :: lines -> 
        line ^ Char.show (Char.chr 10) ^ "          " ^ (newLines lines)
     
  %% ---- called inside OPS : PASS 2  -----

  def checkTyVars (env, tvs, pos) =
    let 
      def aux (tvs, already_seen) =
	case tvs of
	  | []      -> ()
	  | id::tvs ->  
	    if StringSet.member (already_seen, id) then
	      error (env, 
		     "Repeated type variables : " ^ (foldl (fn (str, tv) -> str ^ " " ^ tv) "" tvs),
		     pos)
	    else 
	      aux (tvs, StringSet.add (already_seen, id))
    in 
      aux (tvs, StringSet.empty)

endspec
 
