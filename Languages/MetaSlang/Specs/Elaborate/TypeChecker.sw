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
  import SortToTerm    % XML hacks

  %% ========================================================================

  type Message  = String
  type Result = | Spec Spec | Errors (List(String * Position))

  %% ========================================================================

  op elaboratePosSpec         : Spec * Filename -> Result

  op unlinkRec                : MS.Sort -> MS.Sort
  op undeterminedSort?        : MS.Sort -> Boolean
  op elaborateSort            : LocalEnv * MS.Sort    * MS.Sort            -> MS.Sort
  op elaborateCheckSortForTerm: LocalEnv * MS.Term    * MS.Sort * MS.Sort  -> MS.Sort 
  op elaborateSortForTerm     : LocalEnv * MS.Term    * MS.Sort * MS.Sort  -> MS.Sort
  op resolveNameFromSort      : LocalEnv * MS.Term*Id * MS.Sort * Position -> MS.Term
  op elaborateTerm            : LocalEnv * MS.Term    * MS.Sort            -> MS.Term
  op elaboratePattern         : LocalEnv * MS.Pattern * MS.Sort            -> MS.Pattern * LocalEnv

  op mkEmbed0                 : LocalEnv * MS.Sort         * Id              -> Option Id
  op mkEmbed1                 : LocalEnv * MS.Sort * MS.Term * Id * Position -> Option MS.Term
  op lookupEmbedId            : LocalEnv * Id * MS.Sort                      -> Option (Option MS.Sort)
  op isCoproduct              : LocalEnv * MS.Sort                           -> Option (List (Id * Option MS.Sort))
  op mkProject                : LocalEnv * Id * MS.Sort * Position           -> Option MS.Term

  op undeclaredName           : LocalEnv * MS.Term      * Id * MS.Sort * Position -> MS.Term
  op ambiguousCons            : LocalEnv * MS.Term      * Id * MS.Sort * Position -> MS.Term
  op undeclaredResolving      : LocalEnv * MS.Term      * Id * MS.Sort * Position -> MS.Term
  op undeclared2              : LocalEnv * MS.Term * Id * Id * MS.Sort * Position -> MS.Term

  op pass2Error               : LocalEnv * MS.Sort * Message * Position -> ()

  %% ========================================================================

  def type_nat    = natSort
  def type_bool   = boolSort 
  def type_char   = charSort
  def type_string = stringSort

  %% ========================================================================
  %% The main type-checking function is elaboratePosSpec.

  def elaboratePosSpec (given_spec, filename) = 
    let _ = initializeMetaTyVar ("tc", 0) in

    %% ======================================================================
    %%                           PASS ZERO  [ 0 => 1 ]
    %% ======================================================================

    %% ---------- INITIALIZE SPEC (see ast-environment.sl) ----------
    %%   AstEnvironment.init adds default imports, etc.
    %%
    let initial_env  = initialEnv (given_spec, filename) in
    let {importInfo = importInfo as {imports = _, localOps, localSorts, localProperties},
	 sorts      = given_sorts, 
	 ops        = given_ops, 
	 properties = given_props} 
        = given_spec
    in
    let 

      def elaborate_local_sorts (sorts, env) =
	if localSorts = [] then sorts
	else
	mapSortInfos (fn info ->
		      if someAliasIsLocal? (info.names, localSorts) then
			let
                          def elaborate_dfn dfn =
			    let (tvs, srt) = unpackSort dfn in
			    let _ = checkTyVars (env, tvs, sortAnn dfn) in
			    maybePiSort (tvs, checkSort (env, srt))
			in
			let (old_decls, old_defs) = sortInfoDeclsAndDefs info in
			let new_defs = map elaborate_dfn old_defs in
			let new_dfn = maybeAndSort (old_decls ++ new_defs, sortAnn info.dfn) in
			info << {dfn = new_dfn}
		      else 
			info)
	             sorts 

      def elaborate_local_ops (ops, env, poly?) =
	if localOps = [] then ops
	else
	mapOpInfos (fn info ->
		    if someAliasIsLocal? (info.names, localOps) then
		      let
		        def elaborate_dfn dfn =
			  let pos = termAnn dfn in
			  let (tvs, srt, tm) = unpackTerm dfn in
			  let _ = checkTyVars (env, tvs, pos) in
			  let srt = checkSort (env, srt) in
			  if poly? = (tvs ~= []) then
			    let xx = elaborateTermTop (env, tm, srt) in
			    maybePiTerm (tvs, SortedTerm (xx, srt, pos))
			  else 
			    dfn
		      in
		      let (old_decls, old_defs) = opInfoDeclsAndDefs info in
		      let new_defs = map elaborate_dfn old_defs in
		      let new_dfn = maybeAndTerm (old_decls ++ new_defs, termAnn info.dfn) in
		      let new_info = info << {dfn = new_dfn} in
		      new_info
		    else
		      info)
	           ops

      def elaborate_local_props (props, env) =
	if localProperties = [] then props
	else
	map (fn (prop as (prop_type, name, tvs, fm)) ->
	     if member (name, localProperties) then 
	       let elaborated_fm = elaborateTermTop (env, fm, type_bool) in
	       (prop_type, name, tvs, elaborated_fm)
	     else
	       prop)
	    props


      def reelaborate_local_ops (ops, env) =
	if localOps = [] then ops
	else
	mapOpInfos (fn info ->
		    if someAliasIsLocal? (info.names, localOps) then
		      checkOp (info, env)
		    else
		      info)
	           ops

    in
    %% ======================================================================
    %%                           PASS ONE  
    %% ======================================================================

    %% Add constructors to environment
    let env_with_constrs = addConstrsEnv (initial_env, given_spec) in

    %% Elaborate sorts
    let elaborated_sorts = elaborate_local_sorts (given_sorts, env_with_constrs) in
    let env_with_elaborated_sorts = setEnvSorts (env_with_constrs, elaborated_sorts) in

    %% Elaborate ops (do polymorphic definitions first)
    let elaborated_ops_a = elaborate_local_ops (given_ops,        env_with_elaborated_sorts, true)  in
    let elaborated_ops_b = elaborate_local_ops (elaborated_ops_a, env_with_elaborated_sorts, false) in
    let elaborated_ops_c = elaborate_local_ops (elaborated_ops_b, env_with_elaborated_sorts, true)  in
    let elaborated_ops   = elaborate_local_ops (elaborated_ops_c, env_with_elaborated_sorts, false) in

    %% Elaborate properties
    let elaborated_props = elaborate_local_props (given_props, env_with_elaborated_sorts) in

    %% ======================================================================
    %%                           PASS TWO  
    %% ======================================================================

    %% sjw: 7/17/01 Added a second pass so that order is not so important
    let second_pass_env = secondPass env_with_elaborated_sorts in

    let final_sorts =   elaborate_local_sorts (elaborated_sorts, second_pass_env) in
    let final_ops   = reelaborate_local_ops   (elaborated_ops,   second_pass_env) in
    let final_props =   elaborate_local_props (elaborated_props, second_pass_env) in
    let final_spec = {importInfo   = importInfo,   
		      sorts        = final_sorts, 
		      ops          = final_ops, 
		      properties   = final_props}
    in
    %% We no longer check that all metaTyVars have been resolved,
    %% because we don't need to know the type for _
    case checkErrors second_pass_env of
      | []   -> Spec (convertPosSpecToSpec final_spec)
      | msgs -> Errors msgs

  % ========================================================================
  %% ---- called inside SORTS : PASS 0  -----
  % ========================================================================
 
  def TypeChecker.checkSort (env, srt) = 
    %% checkSort calls elaborateTerm, which calls checkSort
    case srt of

      | TyVar _ -> srt

      | MetaTyVar (v, _) ->
        (case ! v of
	   | {link = Some other_sort, uniqueId, name} -> checkSort (env, other_sort)
	   | _ -> srt)

      | Boolean _ -> srt

      | Base (given_sort_qid, instance_sorts, pos) ->
	let 
          def given_sort_str () =
	    (printQualifiedId given_sort_qid)
	    ^ (case instance_sorts of
		 | []     -> ""    
		 | hd::tl -> "("^ "??" ^ (foldl (fn (instance_sort, str) ->
						 str^", "^ "??")
					  ""
					  tl) 
		             ^ ")")
	in
	  (case findAllSorts (env.internal, given_sort_qid) of
	     | [] -> 
               (error (env, 
		       "Type identifier in "^(given_sort_str ())^" has not been declared", 
		       pos);
		Base (given_sort_qid, instance_sorts, pos))

	     | info :: other_infos -> 
	       let _ =
	           (%% Check for errors...
		    %% Note: If multiple candidates are returned, then given_sort_qid must be unqualified,
		    %%       so if some candidate has given_sort_qid as an exact alias, then that
		    %%       candidate will be first in the list (see comments for findAllSorts),
		    %%       in which case choose it.
		    if ((null other_infos) or exists (fn alias -> alias = given_sort_qid) info.names) then
		      let (tvs, srt) = unpackFirstSortDef info in
		      if length tvs ~= length instance_sorts then
			let found_sort_str =
			    (printAliases info.names)
			    ^ (case tvs of
				 | [] -> ""    
				 | hd::tl -> 
				   "("^ hd ^ (foldl (fn (tv, str) -> str^", "^ tv) "" tl) ^ ")")
			in                                
			let msg = "Type reference " ^ (given_sort_str ())
			          ^" does not match declared type " ^ found_sort_str
			in
			  error (env, msg, pos)
		      else 
			%%  Normal case goes through here:
			%%  either there are no other infos or the first info has as unqualified
			%%   alias, and the number of type vars equals the number of instance sorts.
			()
		    else
		      %% We know that there are multiple options 
		      %% (which implies that the given_sort_qid is unqualified), 
		      %% and that none of them are unqualified, so complain.
		      let candidates_str = foldl (fn (other_info, str) -> 
						  str ^", "^  printAliases other_info.names)
		                                 (printAliases info.names)
						 other_infos
		      in
			error (env, 
			       "Type reference " ^ (given_sort_str ())
			       ^" is ambiguous among " ^ candidates_str,
			       pos))
	       in
	       let new_sort_qid = primarySortName info in
	       let new_instance_sorts = 
	           map (fn instance_sort -> checkSort (env, instance_sort))
		       instance_sorts
	       in
		 if given_sort_qid = new_sort_qid && instance_sorts = new_instance_sorts then 
		   srt
		 else 
		   Base (new_sort_qid, new_instance_sorts, pos))
		
      | CoProduct (fields, pos) ->
	let nfields = map (fn (id, None)   -> (id, None) 
                            | (id, Some s) -> (id, Some (checkSort (env, s))))
                       fields
	in
	if nfields = fields then 
	  srt
	else 
	  CoProduct (nfields, pos)

      | Product (fields, pos) ->
	let nfields = map (fn (id, s) -> (id, checkSort (env, s))) fields in
        if nfields = fields then 
	  srt
	else 
	  Product (nfields, pos)

      | Quotient (given_base_sort, given_relation, pos) ->
        let new_base_sort = checkSort (env, given_base_sort) in
        let new_rel_sort = Arrow (Product ([("1", new_base_sort), 
                                            ("2", new_base_sort)], 
                                           pos), 
                                  type_bool, 
                                  pos) 
	in
        let new_relation = elaborateTerm (env, given_relation, new_rel_sort) in
	if given_base_sort = new_base_sort && given_relation = new_relation then 
	  srt
	else 
	  Quotient (new_base_sort, new_relation, pos)

      | Subsort (given_super_sort, given_predicate, pos) -> 
        let new_super_sort = checkSort (env, given_super_sort) in
        let new_pred_sort  = Arrow (new_super_sort, type_bool, pos) in
        let new_predicate  = elaborateTerm (env, given_predicate, new_pred_sort) in
	if given_super_sort = new_super_sort && given_predicate = new_predicate then 
	  srt
	else 
	  Subsort (new_super_sort, new_predicate, pos)

      | Arrow (t1, t2, pos) ->
	let nt1 = checkSort (env, t1) in
	let nt2 = checkSort (env, t2) in
	if t1 = nt1 && t2 = nt2 then 
	  srt
	else 
	  Arrow (nt1, nt2, pos)

      | And (srts, pos) ->
	let (new_srts, changed?) =  
            foldl (fn (srt, (new_srts, changed?)) ->
		   let new_srt = checkSort (env, srt) in
		   (new_srts ++ [new_srt],
		    changed? || (new_srt ~= srt)))
	          ([], false)
		  srts
	in
	if changed? then
	  maybeAndSort (new_srts, pos)
	else
	  srt

      | Any _ -> srt

      | mystery -> 
        let _ = toScreen ("\ncheckSort, Unrecognized sort: " ^ (anyToString mystery) ^ "\n") in
	mystery

  % ========================================================================
  %% ---- called inside OPS : PASS 0  -----
  % ========================================================================

  def undeterminedSort? srt =
    case unlinkSort srt of
      | MetaTyVar _ -> true
      | _           -> false

  % ========================================================================
  %% ---- called inside OPS        : PASS 1 -----
  %% ---- called inside PROPERTIES : PASS 1 -----
  %% ---- called inside OPS        : PASS 2 -----
  %% ---- called inside AXIOMS     : PASS 2 -----
  %% ---- called inside CheckSort 
  % ========================================================================

  % op resolveMetaTyVar: MS.Sort -> MS.Sort % see SortToTerm
  def resolveMetaTyVar (srt : MS.Sort) : MS.Sort =
    case srt of
      | MetaTyVar(tv,_) -> 
        let {name=_,uniqueId=_,link} = ! tv in
	(case link
	   of None -> srt
	    | Some ssrt -> resolveMetaTyVar ssrt)
      | _ -> srt

  op resolveMetaTyVars: MS.Term -> MS.Term
  def resolveMetaTyVars trm =
    mapTerm (id,resolveMetaTyVar,id) trm

  %% elaborateTerm calls elaborateCheckSortForTerm, 
  %% which calls elaborateSortForTerm, 
  %% which calls unifySorts, 
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

  def resolveNameFromSort(env, trm, id, srt, pos) =
    case mkEmbed0 (env, srt, id) of
      | Some id -> Fun (Embed (id, false), checkSort (env, srt), pos)
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

  op my_break : () -> ()


 def checkOp (info, env) =
   let (old_decls, old_defs) = opInfoDeclsAndDefs info in
   let new_decls_and_defs  = map (fn tm -> checkOpDef  (tm, info, env)) 
                                 (old_decls ++ old_defs)
   in
   let new_dfn = maybeAndTerm (new_decls_and_defs, termAnn info.dfn) in
   info << {dfn = new_dfn}

 def checkOpDef (dfn, info, env) =
   let pos = termAnn dfn in
   let (tvs, srt, tm) = unpackTerm dfn in
   let _ = checkTyVars (env, tvs, pos) in
   let srt = checkSort (env, srt) in
   let elaborated_tm = elaborateTermTop (env, tm, srt) in
   %% If tm is Any (as in an Op declaration), then elaborated_tm will be tm.
   let tvs_used = collectUsedTyVars (srt, info, dfn, env) in
   let new_tvs =
       if null tvs then
	 tvs_used
       else if length tvs_used = length tvs then
	 tvs_used  (* Probably correct ;-*)
       else 
	 (error (env, 
		 "mismatch between bound vars [" ^ (foldl (fn (tv, s) -> s ^ " " ^ tv) "" tvs) ^ "]"
		 ^            " and free vars [" ^ (foldl (fn (tv, s) -> s ^ " " ^ tv) "" tvs_used) ^ "]",
		 termAnn dfn);
	  tvs)
   in
     maybePiTerm (new_tvs, SortedTerm (elaborated_tm, srt, pos))

 def collectUsedTyVars (srt, info, dfn, env) =
   let tv_cell = Ref [] : Ref TyVars in
   let 
   
     def insert tv = 
       tv_cell := ListUtilities.insert (tv, ! tv_cell) 

     def scan srt = 
       case srt of
	 | TyVar     (tv,      _) -> insert tv
	 | Product   (fields,  _) -> app (fn (_, s)      -> scan s)           fields
	 | CoProduct (fields,  _) -> app (fn (_, Some s) -> scan s | _ -> ()) fields
	 | Subsort   (s, _,    _) -> scan s
	 | Quotient  (s, _,    _) -> scan s
	 | Arrow     (s1, s2,  _) -> (scan s1; scan s2)
	 | Base      (_, srts, _) -> app scan srts
	 | Boolean              _ -> ()
	 | MetaTyVar (mtv,     _) -> 
	   (let {name = _, uniqueId, link} = ! mtv in
	    case link of
	      | Some s -> scan s
	      | None   -> error (env, 
				 "Incomplete type for op "^(printQualifiedId (primaryOpName info))
				 ^":"^newline
				 ^(printSort srt), 
				 termAnn dfn))
	 | And (srts, _) -> app scan srts
	 | Any _ -> ()

   in                        
     let _ = scan srt in
     ! tv_cell

  def elaborateTermTop (env, trm, term_sort) =
    let trm = elaborateTerm(env, trm, term_sort) in
    %% Resolve now rather than later to release space
    resolveMetaTyVars trm

  def elaborateTerm (env, trm, term_sort) =
    case trm of

      | Fun (OneName (id, fixity), srt, pos) ->
        (let _ = elaborateCheckSortForTerm (env, trm, srt, term_sort) in 
	 %% resolve sort from environment
	 case findVarOrOps (env, id, pos) of
	   | terms as _::_ ->
	     %% selectTermWithConsistentSort calls consistentSortOp?, which calls unifySorts 
	     (case selectTermWithConsistentSort (env, id, pos, terms, term_sort) of
		| None -> trm
		| Some term ->
		  let srt = termSort term in
		  let srt = elaborateCheckSortForTerm (env, term, srt, term_sort) in
		  (case term of
		     | Var ((id, _),          pos) -> Var ((id, srt),         pos)
		     | Fun (OneName  idf,  _, pos) -> Fun (OneName  (fixateOneName  (idf,  fixity)), srt, pos)
		     | Fun (TwoNames qidf, _, pos) -> Fun (TwoNames (fixateTwoNames (qidf, fixity)), srt, pos)
		     | _ -> System.fail "Variable or constant expected"))
	   | [] -> 
	     resolveNameFromSort (env, trm, id, srt, pos))
      | Fun (TwoNames (id1, id2, fixity), srt, pos) -> 
	(let _ = elaborateCheckSortForTerm (env, trm, srt, term_sort) in 
	 %% Either Qualified (id1, id2) or field selection
	 case findTheOp2 (env, id1, id2) of
           | Some info -> 
	     %% If Qualified (id1, id2) refers to an op, use the canonical name for that op.
	     let Qualified (q, id) = primaryOpName info in
	     let (tvs, srt, tm) = unpackFirstOpDef info in
	     let (_, srt) = metafySort (Pi (tvs, srt, sortAnn srt)) in
	     let term = Fun (TwoNames (q, id, info.fixity), srt, pos) in
	     let srt = elaborateCheckSortForTerm (env, term, srt, term_sort) in
	     (case term of
		| Fun (TwoNames xx, _, pos) -> Fun (TwoNames xx, srt, pos)
		| _ -> System.fail ("Op expected for elaboration of "^id1^"."^id2^" as resolved to "^q^"."^id))
	   | None -> 
	     %% If Qualified (id1, id2) does not refer to an op, check for field selection
	     (case findVarOrOps (env, id1, pos) of
		| [big_term] ->
		  %% unqualified id1 refers to big_term
		  let big_sort = termSort big_term in
		  let big_sort = checkSort (env, big_sort) in
		  let 
                    def projectRow (big_term, big_sort, row, id2) =
		      %% See if id2 is one of the field selectors for the big sort.
		      (case row of
			 | [] -> undeclared2 (env, trm, id1, id2, term_sort, pos)
			 | (field_id, field_sort) :: row -> 
			   if id2 = field_id then
			     let field_sort = checkSort (env, field_sort) in
			     let projector : MS.Term = Fun (Project id2, Arrow (big_sort, field_sort, pos), pos) in
			     let projection = (ApplyN ([projector, big_term], pos)) : MS.Term in
			     let _ = elaborateSortForTerm (env, projection, field_sort, term_sort) in
			     projection
			   else
			     projectRow (big_term, big_sort, row, id2))
		    def getProduct srt : Option (List (String * MS.Sort)) = 
		      (case unfoldSort (env, srt) of
			 | Product (row,       _) -> Some row
			 | Subsort (srt, pred, _) -> getProduct srt
			 | _ -> None)
		  in          
		    %% See if big_term is a product or a subsort of a product
		    (case getProduct big_sort of
		       | Some row -> projectRow (big_term, big_sort, row, id2)
		       | None     -> undeclared2 (env, trm, id1, id2, term_sort, pos)
		       | _        -> undeclared2 (env, trm, id1, id2, term_sort, pos))
	   | _ -> 
	     %% Both id1.id2 and id1 fail to refer to anything
	     undeclared2 (env, trm, id1, id2, term_sort, pos)
          )
        | _ -> 
          %% id1.id2 is ambiguous??  That shouldn't be possible.
	  undeclared2 (env, trm, id1, id2, term_sort, pos)
	 )
      | Fun (Embed (id, _), srt, pos) -> 
	let _  (* srt *) = elaborateCheckSortForTerm (env, trm, srt, term_sort) in
	%% using term_sort instead of srt in the following was cause of bug 110 : "[] read as bogus Nil"
	resolveNameFromSort (env, trm, id, srt, pos) 

      | Fun (Project id,srt,pos) -> 
	let srt = elaborateCheckSortForTerm (env, trm, srt, term_sort) in
	(case mkProject (env,id,srt,pos) of
	   | Some term -> term
	   | None -> undeclaredResolving (env,trm,id,term_sort,pos))

    % | Fun (Select id,srt,pos) -> Fun (Select id,srt,pos)      (*** Not checked ***)
      | Fun (Embedded id, srt, pos) -> 
	let srt = elaborateCheckSortForTerm (env, trm, srt, term_sort) in
	((case unfoldSort (env, srt) of
	    | Arrow (dom, _, _) -> 
	      (case isCoproduct (env, dom) of
		 | Some fields -> 
	           if exists (fn (id2, _) -> id = id2) fields then
		     ()
		   else
		     error (env, 
			    "Name "^id^" is not among the constructors of "^ printSort dom, 
			    pos)
		 | None -> 
		   pass2Error (env, dom, 
			       newLines ["Sum type with constructor "^id^" expected", 
					 "found instead "^printSort dom], 
			       pos))
	    | _ -> pass2Error (env, srt, "Function type expected ", pos));
	 Fun (Embedded id, srt, pos))

      | Fun (PChoose equiv, srt, pos) ->
	(* Has sort {f: a -> b | fa(m,n) equiv(m,n) => f m = f n} -> a \ equiv -> b *)
	let a = freshMetaTyVar ("PChoose_a", pos) in
	let b = freshMetaTyVar ("PChoose_b", pos) in
	let ty1 = Arrow (Product ([("1", a), ("2", a)], pos), type_bool, pos) in
	let equiv = elaborateTerm (env, equiv, ty1) in
	let ty2 = Arrow (Quotient (a, equiv, pos), b, pos) in
	let ty3 = Arrow (a, b, pos) in
	let fv = ("F",ty3) in
	let mv = ("M",a) in
	let nv = ("N",a) in
	let lhs = mkAppl(equiv,[mkVar mv,mkVar nv]) in
	let rhs = mkEquality(a,mkApply(mkVar fv,mkVar mv),mkApply(mkVar fv,mkVar nv)) in
	let body = mkBind(Forall,[mv,nv],mkImplies(lhs,rhs)) in
	let tys = Subsort(ty3,mkLambda(mkVarPat fv,body),pos) in
	let ty4 = Arrow (tys, ty2, pos) in
	(elaborateSortForTerm (env, trm, ty4, term_sort);
	 elaborateSortForTerm (env, trm, srt, ty4);
	 Fun (PChoose equiv, ty4, pos))

      | Fun (PQuotient equiv, srt, pos) ->  % Has sort a -> Quotient(a, equiv)
	let a = freshMetaTyVar ("PQuotient", pos) in
	let ty1 = Arrow (Product ([("1", a), ("2", a)], pos), type_bool, pos) in
	let equiv = elaborateTerm (env, equiv, ty1) in 
	let ty2 = Arrow (a, Quotient (a, equiv, pos), pos) in
	(elaborateSortForTerm (env, trm, ty2, term_sort);
	 elaborateSortForTerm (env, trm, srt, ty2);
	 Fun (PQuotient equiv, srt, pos))  

      | Fun (Bool b, srt, pos) -> 
	(elaborateSortForTerm (env, trm, type_bool, term_sort) ; 
	 elaborateCheckSortForTerm (env, trm, srt, type_bool);
	 Fun (Bool b, srt, pos))
	
      | Fun (Nat n, srt, pos) ->  
	(elaborateSortForTerm (env, trm, type_nat, term_sort);
	 elaborateCheckSortForTerm (env, trm, srt, type_nat);
	 Fun (Nat n, srt, pos))
	
      | Fun (String s, srt, pos) -> 
	(elaborateSortForTerm (env, trm, type_string, term_sort);
	 elaborateCheckSortForTerm (env, trm, srt, type_string);
	 Fun (String s, srt, pos))
	
      | Fun (Char ch, srt, pos) -> 
	(elaborateSortForTerm (env, trm, type_char, term_sort);
	 elaborateCheckSortForTerm (env, trm, srt, type_char);
	 Fun (Char ch, srt, pos))
	
      | Fun (PRelax pred, srt, pos) -> % Has sort Subsort(a, pred) -> a
	let a = freshMetaTyVar ("PRelax", pos) in
	let ty1 = Arrow (a, type_bool, pos) in
	let pred = elaborateTerm (env, pred, ty1) in
	let ty2 = Arrow (Subsort (a, pred, pos), a, pos) in
	(elaborateSortForTerm (env, trm, ty2, term_sort);
	 elaborateSortForTerm (env, trm, srt, ty2);
	 Fun (PRelax pred, srt, pos))

	%% FINISH THIS
	%% 
	%%          let _ = elaborateSortForTerm (env, trm, srt, term_sort) in
	%%          (Fun (PRelax, srt), pos)

      | Fun (PRestrict pred, srt, pos) -> % Has sort a -> Subsort(a, pred)
	let a = freshMetaTyVar ("PRestrict", pos) in
	let ty1 = Arrow (a, type_bool, pos) in
	let pred = elaborateTerm (env, pred, ty1) in
	let ty2 = Arrow (a, Subsort (a, pred, pos), pos) in
	(elaborateSortForTerm (env, trm, ty2, term_sort);
	 elaborateSortForTerm (env, trm, srt, ty2);
	 Fun (PRestrict pred, srt, pos))

	%% FINISH THIS
	%%
	%        | Fun (Spec _ (* spc *), _ (* srt *), _) -> trm
	
      | Var ((id, srt), pos) -> 
	let srt = elaborateCheckSortForTerm (env, trm, srt, term_sort) in
	Var ((id, srt), pos)

      | LetRec (decls, body, pos) -> 
	let 

          def declareFun (((id, srt), bdy), env) = 
	    addVariable (env, id, srt)

          def elaborateDecl env ((id, srt), bdy) = 
	    let terms = findVarOrOps (env, id, pos) in
	    let srt = termSort (hd terms) in
	    let bdy = elaborateTerm (env, bdy, srt) in
	    ((id, srt), bdy)
	in
	let env = foldr declareFun env decls in
	let decls = map (elaborateDecl env) decls in
	let bdy = elaborateTerm (env, body, term_sort) in
	LetRec (decls, bdy, pos)

      | Let (decls, body, pos) -> 
	let env0 = env in
        let 
          def doDeclaration ((pat, bdy), (decls, env)) = 
	    let alpha = freshMetaTyVar ("Let", pos) in
	    (* In case the pattern is has a sort constraint, move
	       this to the body such that the sort constraint is 
	       attatched to alpha.
	       *)
	    let (pat, bdy) = 
	        case pat:MS.Pattern of
		  | SortedPat (pat, srt, pos) -> 
		    (pat, (SortedTerm (bdy, srt, pos)):MS.Term)
		  | _ -> (pat, bdy)
	    in             
	    let bdy = elaborateTerm (env0, bdy, alpha) in
	    let (pat, env) = elaboratePattern (env, pat, alpha) in
	    (cons ((pat, bdy), decls), env)
	in         
	let (decls, env) = foldr doDeclaration ([], env) decls in
	let body = elaborateTerm (env, body, term_sort) in 
	Let (decls, body, pos)

      | IfThenElse (test, thenTrm, elseTrm, pos) -> 
	let test = elaborateTerm (env, test, type_bool) in
	let thenTrm = elaborateTerm (env, thenTrm, term_sort) in 
	let elseTrm = elaborateTerm (env, elseTrm, term_sort) in
	IfThenElse (test, thenTrm, elseTrm, pos)

      | Record (row, pos) -> 
        let 
	  def unfoldConstraint (srt) = 
	    (case unfoldSort (env, srt) of
	       | Product (rows, _) -> 
	         (if ~(length (row) = length (rows)) then
		    error (env, 
			   newLines [printTerm trm, "is incompatible with constraint", printSort term_sort], 
			   pos)
		  else 
		    ();
		  rows)
	       | MetaTyVar (mtv, _) ->
                 let row = map (fn (id, _)-> (id, freshMetaTyVar ("Record", pos))) row in
		 (linkMetaTyVar mtv ((Product (row, pos)));
		  row)
                        
	       | Subsort (srt, term, _) -> 
		 unfoldConstraint (srt)        

	       | And (srt :: _, _) -> % TODO: be smarter about choosing among alternatives
		 unfoldConstraint srt        

	       | sv -> 
		 (pass2Error (env, 
			      sv, 
			      printTerm trm^" is constrained to be of an incompatible type "^newline^ printSort term_sort, 
			      pos);
		  map (fn (id, _)-> (id, freshMetaTyVar ("Record_incompatible", pos))) row))
	in
	let tyrows = unfoldConstraint (term_sort) in
	let trow = ListPair.zip (row, tyrows) in
	let row = map (fn ((id, t), (id_, ty))->
		       if id = id_ then
			 (id, elaborateTerm (env, t, ty))
		       else 
			 (error (env, "Field-name "^id^
				 " is not the one imposed by sort constraint.  Expected field-name is: "^
				 id_, pos);
		      (id, t)))
	              trow
	in
	  Record (row, pos)

      | Lambda (rules, pos) -> 
	let alpha = freshMetaTyVar ("Lambda_a", pos) in
	let beta  = freshMetaTyVar ("Lambda_b", pos) in
	let ty    = (Arrow (alpha, beta, pos)) in
	let _     = elaborateSort (env, ty, term_sort) in 
	Lambda (map (fn (pat, cond, term)->
		     let (pat, env) = elaboratePattern (env, pat, alpha) in
		     let term = elaborateTerm (env, term, beta) in
		     let cond = elaborateTerm (env, cond, type_bool) in
		     (pat, cond, term)) 
		    rules,
	       pos)

      | Bind (bind, vars, term, pos) ->
	let _ = elaborateSort (env, term_sort, type_bool) in
	let (vars, env) = 
	    foldl (fn ((id, srt), (vars, env)) ->
		   let srt = checkSort (env, srt) in
		   (cons ((id, srt), vars), 
		    addVariable (env, id, srt)))
	          ([], env) 
		  vars 
	in
        let vars = rev vars in
	Bind (bind, vars, elaborateTerm (env, term, term_sort), pos)

      | SortedTerm (term, srt, _) ->
        let srt  = elaborateSort (env, srt, term_sort) in
	let term = elaborateTerm (env, term, srt) in
	term

      | Seq (terms, pos) -> 
	let
          def elab ts = 
	    case ts of
	      | [] -> []
	      | [t] -> [elaborateTerm (env, t, term_sort)]
	      | (t::ts) -> 
	        let alpha = freshMetaTyVar ("Seq", pos) in
		let t = elaborateTerm (env, t, alpha) in
		cons (t, elab ts)
	in
	  Seq (elab terms, pos)

      | ApplyN ([t1 as Fun (Embedded _, _, _), t2], pos) -> 
        let alpha = freshMetaTyVar ("ApplyN_Embedded", pos) in
	let ty    = Arrow (alpha, term_sort, pos) in
	let t2    = elaborateTerm (env, t2, alpha) in
	let t1    = elaborateTerm (env, t1, ty) in
	ApplyN ([t1, t2], pos)

      | ApplyN ([t1 as Fun (Project _, _, _), t2], pos) -> 
	let alpha = freshMetaTyVar ("ApplyN_Project", pos) in
	let ty    = Arrow (alpha, term_sort, pos) in
	let t2    = elaborateTerm (env, t2, alpha) in
	let t1    = elaborateTerm (env, t1, ty) in
	ApplyN ([t1, t2], pos)
	
      | ApplyN ([t1 as Fun (f1, s1, _), t2], pos) -> 
        let alpha = freshMetaTyVar ("ApplyN_Fun", pos) in
	let ty    = Arrow (alpha, term_sort, pos) in
	let t1    = elaborateTermHead(env,t1,ty,trm) in
	let t2    = elaborateTerm (env, t2, alpha) in
	%% Repeated for help in overload resolution once argument type is known
	let t1    = (if env.firstPass? then
		       case t1 of
			 | Fun(OneName _,_,_) -> elaborateTerm (env, t1, ty)
			 | _ -> t1
		     else 
		       t1)
	in
	%% This is same effect as old code, but restructured
	%% so it's easier to intercept the XML references
	if env.firstPass? then
	  ApplyN ([t1, t2], pos)
	else if f1 = Equals then
	  let t1 = adjustEqualitySort (env, s1, t1, t2) in
	  ApplyN ([t1, t2], pos)
	else if f1 = NotEquals then
	  let t1 = adjustEqualitySort (env, s1, t1, t2) in
	  ApplyN ([t1, t2], pos)
	else if sortCognizantOperator? f1 then
	  addSortAsLastTerm (env, 
			     trm,
			     ApplyN ([t1, t2], pos),
			     term_sort)
        else
	  ApplyN ([t1, t2], pos)

      | ApplyN ([t1, t2], pos) ->
	let alpha = freshMetaTyVar ("ApplyN_2", pos) in
	let ty    = Arrow (alpha, term_sort, pos) in
	let t2    = elaborateTerm (env, t2, alpha) in
	let t1    = elaborateTerm (env, t1, ty) in
	ApplyN ([t1, t2], pos)

      | ApplyN (terms, pos) ->
	let 
          def tagTermWithInfixInfo (term : MS.Term) : FixatedTerm = 
	    case term of
	      | Fun (OneName (_,  Nonfix),  _, pos) -> Nonfix term
	      | Fun (OneName (_,  Infix p), _, pos) -> Infix (term, p)
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
	let new = elaborateTerm (env, term, term_sort) in
	new

      %% These should only appear as the head of an apply (see one of the ApplyN cases above):
      | Fun (Not,       srt, pos) -> (error (env, "Can't refer to syntactic operator '~' as an arg -- use '(~)' instead.",     pos); trm)
      | Fun (And,       srt, pos) -> (error (env, "Can't refer to syntactic operator '&&' as an arg -- use '(&&)' instead.",   pos); trm)
      | Fun (Or,        srt, pos) -> (error (env, "Can't refer to syntactic operator '||' as an arg -- use '(||)' instead.",   pos); trm)
      | Fun (Implies,   srt, pos) -> (error (env, "Can't refer to syntactic operator '=>' as an arg -- use '(=>)' instead.",   pos); trm)
      | Fun (Iff,       srt, pos) -> (error (env, "Can't refer to syntactic operator '<=>' as an arg -- use '(<=>)' instead.", pos); trm)
      | Fun (Equals,    srt, pos) -> (error (env, "Can't refer to syntactic operator '=' as an arg -- use '(=)' instead.",     pos); trm)
      | Fun (NotEquals, srt, pos) -> (error (env, "Can't refer to syntactic operator '~=' as an arg -- use '(~=)' instead.",   pos); trm)
	
      | term -> (%System.print term;
		 term)

  def elaborateTermHead(env,t1,ty,trm) =
    case t1 of
      | Fun (Not, srt, pos) -> 
	(elaborateSortForTerm (env, trm, srt, ty);
	 Fun (Not, srt, pos))

      | Fun (And, srt, pos) -> 
	(elaborateSortForTerm (env, trm, srt, ty);
	 Fun (And, srt, pos))

      | Fun (Or, srt, pos) -> 
	(elaborateSortForTerm (env, trm, srt, ty);
	 Fun (Or, srt, pos))

      | Fun (Implies, srt, pos) -> 
	(elaborateSortForTerm (env, trm, srt, ty);
	 Fun (Implies, srt, pos))

      | Fun (Iff, srt, pos) -> 
	(elaborateSortForTerm (env, trm, srt, ty);
	 Fun (Iff, srt, pos))

      | Fun (Equals, srt, pos) -> 
	(elaborateSortForTerm (env, trm, srt, ty);
	 Fun (Equals, srt, pos))

      | Fun (NotEquals, srt, pos) -> 
	(elaborateSortForTerm (env, trm, srt, ty);
	 Fun (NotEquals, srt, pos))

      | Fun (RecordMerge, srt, pos) ->
	(let a = freshMetaTyVar ("RecordMerge_a", pos) in
	 let b = freshMetaTyVar ("RecordMerge_b", pos) in
	 let c = freshMetaTyVar ("RecordMerge_c", pos) in
	 let fresh_merge_type = Arrow(Product ([("1", a), ("2", b)], pos), c, pos) in
	 (elaborateSortForTerm(env, trm, srt, fresh_merge_type);
	  elaborateSortForTerm(env, trm, fresh_merge_type, ty);
	  let def notEnoughInfo() =
		if env.firstPass? then 
		  t1
		else 
		  (error(env, "Can't determine suitable type for <<: " ^ printSort srt, pos);
		   t1)
	  in
	  case isArrow(env,srt) of
	    | Some (dom,rng) ->
	      (case isProduct (env,dom) of
		 | Some [("1",s1),("2",s2)] ->
		   (case (isProduct(env,s1),isProduct(env,s2)) of
		      | (Some row1,Some row2) ->
			let merged_sort = Product(mergeFields(env,row1,row2,pos),pos) in
			(elaborateSortForTerm(env,trm,rng,merged_sort);
			 Fun(RecordMerge, srt, pos))
		      | _ -> notEnoughInfo())
		 | _ -> notEnoughInfo())
	    | None -> notEnoughInfo()))

      | _ ->
	elaborateTerm (env, t1, ty)

   op makeEqualityType : Sort * Position -> Sort
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
  def sortCognizantOperators : List (Id * Id) =
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

  def sortCognizantOperator? (f1 : MS.Fun) : Boolean = 
    case f1 of
      | TwoNames (id1, id2, _) ->
        member ((id1, id2), sortCognizantOperators)
      | _ -> false


  % ========================================================================

  op  selectTermWithConsistentSort: LocalEnv * Id * Position * List MS.Term * Sort -> Option MS.Term
  def selectTermWithConsistentSort (env, id, pos, terms, srt) =
    %% calls consistentSortOp?, which calls unifySorts 
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
        case unlinkSort srt of
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
			  (foldl (fn (tm, str) -> str ^
				  (case tm of
				     | Fun (OneName  (     id2, _), _, _) -> " "^id2
				     | Fun (TwoNames (id1, id2, _), _, _) -> " "^id1^"."^id2))
				 " : "
				 terms),
			  pos);
		   None))
	  | rsort ->
	    let srtPos = sortAnn srt in
	    (case filter (consistentSortOp? (env, withAnnS (rsort, srtPos),true)) terms of
	       | [] -> (error (env,
			       "No matches for op " ^ id ^ " of " ^ (printMaybeAndType srt),
			       pos);
			None)
	       | [term] -> Some term
	       | tms ->
	         if env.firstPass? then
		   None
		 else
		   (let exactTerms = filter (consistentSortOp? (env, withAnnS (rsort, srtPos),false)) terms in
		    let remTerms = if exactTerms = [] then tms else exactTerms in
		    case remTerms of
		      %% If only one term matches including subsorts, choose it
	              | [term] -> Some term
		      | _ ->
		        %% If there is a valid unqualified term then prefer that because you
		        %% cannot explicitly qualify with unqualified!
			case findUnqualified remTerms of
			  | Some term -> Some term
			  | None ->
			    (error (env,
				    "Several matches for overloaded op " ^ id ^ " of " ^
				    (printMaybeAndType srt) ^
				    (foldl (fn (tm, str) -> str ^
					    (case tm of
					       | Fun (OneName  (     id2, _), _, _) -> " "^id2
					       | Fun (TwoNames (id1, id2, _), _, _) -> " "^id1^"."^id2))
				           " : "
					   tms),
				    pos);
			     None)))

  def printMaybeAndType srt =
    case srt of
      | And (srt :: srts, _) ->
        foldl (fn (srt, s) -> s ^ " and type " ^ (printSort srt) ^ "\n")
	("type " ^ (printSort srt) ^ "\n")
	srts
      | _ ->
	"type " ^ (printSort srt) 

  def consistentSortOp? (env, srt1, ignoreSubsorts?) (Fun (_, srt2, _)) =
   %% calls unifySorts, but then resets metatyvar links to None...
   consistentSorts? (env, srt1, srt2, ignoreSubsorts?)

  % ========================================================================

  def elaborateCheckSortForTerm (env, term, givenSort, expectedSort) = 
   elaborateSortForTerm (env, term, (checkSort (env, givenSort)), expectedSort)

  def elaborateSortForTerm (env, term, givenSort, expectedSort) = 
    %% unifySorts has side effect of modifying metaTyVar links
    let (success, msg) = unifySorts env true givenSort expectedSort in
    ((if success || env.firstPass? then
	()
      else
	let pos        = termAnn   term in
	let termString = printTerm term in
	let tsLength   = length termString in
	let fillerA    = blankString (10 - tsLength) in  % ### why the qualifier? why the coercion?
	let fillerB    = blankString (tsLength - 10) in
	let msg        = newLines ["Could not match type constraint", 
				   fillerA ^ termString ^ " of " ^ (printMaybeAndType givenSort), 
				   fillerB ^ "with expected " ^ (printMaybeAndType expectedSort)]
	in
	  error (env, msg, pos));
     givenSort)

   % If f : A -> B, and x : C, then for f(x) we want to see
   % an error message like:
   %
   % Could not match sort constraint
   %       x of sort C
   %       with expected sort A
   %
   % Most of the time, givenSort is C (the sort of the argument)
   % while expectedSort is A (the domain sort of the function).
   %
   % ---
   %
   % Apparently the sense of givenSort and expectedSort used to be 
   %  reversed for some obscure reason, but they seem ok now here.
   %  If there are problems, fix them elsewhere, and don't mangle 
   %  this code!
   %
   % Obsolete comment:
   %   Here, most of the time, expectedSort is C (the sort of the argument)
   %   while givenSort is A (the domain sort of the function); rather
   %   ill-chosen names.

  def elaborateSort (env, s1, s2) = 
    let s1Checked = checkSort (env, s1) in
    %% unifySorts has side effect of modifying metatyvar links
    let (success, msg) = unifySorts env true s1Checked s2 in
    ((if success then
	()
      else             
	let msg = newLines ["Could not match type " ^ printSort s1, 
			    "                with " ^ printSort s2]
	in
	  let _ = mybreak () in
	  error (env, msg, chooseNonZeroPos (sortAnn s1, sortAnn s2)));
     s1Checked)

  def mybreak () = ()
    
  % ========================================================================
  %% Called inside elaborateTerm 

  def mkEmbed0 (env, srt, id) =
    case lookupEmbedId (env, id, srt) of
      | Some None -> Some id
      | _   -> None
        
  def lookupEmbedId (env, id, srt) = 
    case unfoldSort (env, srt) of
      | CoProduct(row, _) -> 
        let def lookup row =
	      case row of
		| [] -> None : Option (Option MS.Sort)
		| (found_id, entry) :: row ->  
		  if id = found_id then
		    Some (case entry of
			    | None   -> None
			    | Some s -> Some (checkSort (env, s)))
		  else 
		    lookup row
	in
	  lookup row
      | Subsort (srt, pred, _) -> lookupEmbedId (env, id, srt)
      | _ -> None

  def mkEmbed1 (env, srt, trm, id, pos) = 
    case isArrowCoProduct (env, srt) of
      | Some (sum_sort, row) ->
        let 
	  %% This checks that a sum-sort constructor is given the proper sort
          def findId ls = 
	    case ls of
	      | [] -> Some (undeclaredName (env, trm, id, srt, pos))
	      | (constructor_id, Some constructor_dom_sort) :: row -> 
	        if id = constructor_id then
		  %%  let _ = String.writeLine ("coprod: "^printSort (Arrow (s, CoProduct (row, pos0)), pos0)) in
		  %%  let _ = String.writeLine ("srt:  "^printSort srt) in
		  %%  let _ = String.writeLine ("srt1: "^printSort found_sort) in
		  %%  let _ = String.writeLine ("dom:  "^printSort (sum_sort, pos)) in
		  let constructor_dom_sort = checkSort (env, constructor_dom_sort) in
		  let _ (* dom *) = elaborateSort (env, withAnnS (sum_sort, pos), constructor_dom_sort) in
		  Some (Fun (Embed (id, true), checkSort (env, srt), pos))
		else 
		  findId row
	      | _ :: row -> findId row
	in
	  findId row
      | _ -> None

  def isArrowCoProduct (env, srt) : Option (MS.Sort * List (Id * Option MS.Sort)) =
    case unfoldSort (env, srt) of
      | Arrow (dom, rng, _) -> 
        (case isCoproduct (env, rng) of
	   | Some row -> Some (dom, row)
	   | None -> None)
      | _ -> None

  def isCoproduct (env, srt)  = 
    case unfoldSort (env, srt) of
      | CoProduct (row, _)    -> Some row
      | Subsort   (srt, _, _) -> isCoproduct (env, srt)
      | _ -> None

  op  isProduct: LocalEnv * Sort -> Option(List (Id * Sort))
  def isProduct (env, srt)  = 
    case unfoldSort (env, srt) of
      | Product (fields, _) -> Some fields
      | Subsort (srt, _, _) -> isProduct (env, srt)
      | _ -> None

  def isArrow (env, srt): Option (Sort * Sort)  = 
    case unfoldSort (env, srt) of
      | Arrow (dom, rng, _) -> Some (dom, rng)
      | Subsort(ssrt, _, _) -> isArrow (env, ssrt)
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
	      | Equal   -> (elaborateSort(env,
					  Product([e1], pos),
					  Product([e2], pos));
			    loop (r1, r2, merged ++ [e2]))
    in 
      loop(row1,row2,[])

  %% If id is the unique name of a constructor, use that constructor
  def uniqueConstr (env, trm, id, pos) =
    case StringMap.find (env.constrs, id) of
      | Some [srt_info] ->
        let (_, c_srt) = metafySort srt_info in
	let id_srt = case c_srt of
		       | CoProduct (fields, pos) ->
	                 (case find (fn (id2, _) -> id = id2) fields of
			    | Some (_, Some dom_srt) -> Arrow (dom_srt, c_srt, pos)
			    | _ -> c_srt)
		       | _ -> c_srt
	in
	(case mkEmbed0 (env, id_srt, id) of
	   | Some id -> Some (Fun (Embed (id, false), checkSort (env, id_srt), pos))
	   | None -> mkEmbed1 (env, id_srt, trm, id, pos))
      | _ -> None

  def mkProject (env, id, srt, pos) = 
    case unfoldSort (env, srt) of
      | Arrow (dom, rng, _) -> 
        (let 
           def analyzeDom dom =
	     case unfoldSort (env, dom) of
	       | Product (row, _) -> 
                 (let def findId ls = 
		  case ls of
		    | [] -> None : Option MS.Term
		    | (selector_id, selector_rng_srt) :: ids -> 
		      if id = selector_id then
			(elaborateSort (env, withAnnS (rng, pos), selector_rng_srt);
			 Some (Fun (Project id, srt, pos)))
		      else 
			findId ids
		  in
		    findId row)
	       | Subsort (ssrt, _, _) -> analyzeDom ssrt
	       | _ -> None
	 in 
	   analyzeDom dom)
      | Subsort (ssrt, _, _) -> mkProject (env, id, ssrt, pos)
      | _ -> None
      

  def consistentTag competing_pterms =
    %% If one of the alternatives (found by findVarOrOps) has optional infix priority
    %% and the others either have the same infix priority or are not infix ops then,
    %% return (true, priority), otherwise return (false, None).
    %% In other words, we will complain if F or Foo.F is ambigous among terms that
    %% have differing infix priorities, but allow prefix versions.
    %% findVarOrOps should never return any OneName
    case competing_pterms of
      | (Fun (OneName  (_,    Infix priority), _, pos))::r -> consistentInfixMS.Terms (r, Some priority)
      | (Fun (TwoNames (_, _, Infix priority), _, pos))::r -> consistentInfixMS.Terms (r, Some priority) % r must be []
      | _::r                                               -> consistentInfixMS.Terms (r, None)
      | _                                                  -> (true, None)

  def consistentInfixMS.Terms (competing_pterms, optional_priority) = 
    case competing_pterms of
      | [] -> (true, optional_priority)
      | (Fun (OneName (_, Infix element_priority), _, pos))::tail ->
        (case optional_priority of
	   | None -> consistentInfixMS.Terms (tail, Some element_priority)
	   | Some priority -> (if element_priority = priority then
				 consistentInfixMS.Terms (tail, optional_priority)
			       else 
				 (false, None)))
      | (Fun (TwoNames (_, _, Infix element_priority), _, pos))::tail ->
	(case optional_priority of
	   | None -> consistentInfixMS.Terms (tail, Some element_priority)
	   | Some priority -> (if element_priority = priority then
				 consistentInfixMS.Terms (tail, optional_priority)
			       else 
				 (false, None)))
      | _::tail -> consistentInfixMS.Terms (tail, optional_priority)
       
  def adjustEqualitySort (env, srt, t1, eq_args) =
    case (eq_args, unlinkSort srt) of
      | (_,  % consider "let A = (true, false) in =(A)"
	 Arrow (Product ([("1", _), ("2", _)], _), _, _)) -> 
        t1

     %| (Record ([("1", e1), ("2", e2)], _), 
     %  Arrow (Product ([("1", elSrt1), ("2", _)], _), _, _)) -> 
     % t1
     %% This code is correct except that termSort doesn't take account of defined sorts and gives an error
     %       let
     %         def subsort? (srt1_, srt2_) = 
     %           srt1_ = srt2_
     %           or (case srt1_
     %                of Subsort ((s1_, _), _) -> subsort? (s1_, srt2_)
     %                 | _ -> false)
     %         def commonAnc (s1_, s2_) =
     %           if subsort? (s1_, s2_) then s2_ else
     %           if subsort? (s2_, s1_) then s1_ else
     %           case s1_
     %             of Subsort ((ss1_, _), _) -> commonAnc (ss1_, s2_)
     %              | _ -> s2_                        % Shouldn't happen
     %             
     % in
     %       let (s1_, s2_) = (unfold (env, termSort e1), unfold (env, termSort e2)) in
     %       let expElSrt_ = unfold (env, elSrt1) in
     %       let elSrt = if subsort? (s1_, expElSrt_) && subsort? (s2_, expElSrt_)
     %                    then elSrt1 else (commonAnc (s1_, s2_), pos) in
     %       (Fun (Equals, (Arrow ((Product [("1", elSrt), ("2", elSrt)], pos), type_bool), pos)), pos)

      | _ -> (error (env, 
		     "Illegal Equality on " ^ printTerm eq_args, 
		     sortAnn srt);
	      t1)

  def undeclaredName (env, trm, id, srt, pos) =
    if env.firstPass? then %&& undeterminedSort? s 
      trm
    else
      (error (env, "Name "^id^" could not be identified", pos);
       % raise (TypeCheck (pos, "Name "^id^" could not be identified"));
       Fun (OneName (id, Nonfix), srt, pos))

  def ambiguousCons (env, trm, id, srt, pos) =
    if env.firstPass? then %&& undeterminedSort? s 
      trm
    else
      (error (env, "Constructor "^id^" could not be disambiguated", pos);
       Fun (OneName (id, Nonfix), srt, pos))

  def undeclared2 (env, trm, id1, id2, srt, pos) =
    if env.firstPass? then %&& undeterminedSort? s 
      trm
    else
      (error (env, id1^"."^id2^" has not been declared as a qualified name or as a field selection", pos);
       % raise (TypeCheck (pos, id1^"."^id2^" has not been declared as a qualified name or as a field selection"));
       Fun (TwoNames (id1, id2, Nonfix), srt, pos))

  def undeclaredResolving (env, trm, id, srt, pos) = 
    if env.firstPass? then %&& undeterminedSort? s
      trm
    else
      (error (env, "Name "^id^" could not be identified; resolving with "^printSort srt, pos);
       % raise (TypeCheck (pos, "Name "^id^" could not be identified; resolving with "^printSort srt));
       (Fun (OneName (id, Nonfix), srt, pos)) : MS.Term)

  % ========================================================================
  %% Called inside elaborateTerm 
  % ========================================================================

  def elaboratePattern (env, p, sort1) =
    let (pat, env, _) = elaboratePatternRec (env, p, sort1, []) in
    (pat,env)

  op  elaboratePatternRec: LocalEnv * MS.Pattern * MS.Sort * List Id -> MS.Pattern * LocalEnv *  List Id 
  def elaboratePatternRec (env, p, sort1, seenVars) =
    let sort1 = checkSort (env, sort1) in
    let 
      def addSeenVar(id, seenVars, env, pos) =
	if member(id,seenVars) then
	  (error (env, "Variable "^id^" repeated in pattern.", pos);
	   (env,seenVars))
	else 
	  (env, Cons (id, seenVars))
    in
    case p of
      | WildPat (s, pos) -> (WildPat (elaborateSort (env, s, sort1), pos), env, seenVars)
      | BoolPat   _ -> (elaborateSort (env, sort1, type_bool);   (p, env, seenVars))
      | NatPat    _ -> (elaborateSort (env, sort1, type_nat);    (p, env, seenVars))
      | StringPat _ -> (elaborateSort (env, sort1, type_string); (p, env, seenVars))
      | CharPat   _ -> (elaborateSort (env, sort1, type_char);   (p, env, seenVars))
      | VarPat ((id, srt), pos) -> 
         let srt = elaborateSort (env, srt, sort1)  in 
           (case lookupEmbedId (env, id, srt) of
              | Some None -> (EmbedPat (id, None, srt, pos), env, seenVars)
              | Some _ -> 
                     (error (env, "Constructor "^id^" expects an argument, but was given none", pos);
                      % raise (TypeCheck (pos, "Constructor "^id^" expects an argument, but was given none"));
                      (VarPat ((id, srt), pos), env, seenVars))
              | None ->
                 if undeterminedSort? srt then
                   (case StringMap.find (env.constrs, id) of
                     | None ->
		       let (env,seenVars) = addSeenVar(id,seenVars,env,pos) in
		       (VarPat ((id, srt), pos), addVariable (env, id, srt), seenVars)
                     | Some [srt_info] ->
                                 let (_, c_srt) = metafySort srt_info in
                                 (VarPat ((id, c_srt), pos), env, seenVars)
                     | Some _ -> (VarPat ((id, srt), pos), env, seenVars))
                 else
		   let (env,seenVars) = addSeenVar(id,seenVars,env,pos) in
                   (VarPat ((id, srt), pos), addVariable (env, id, srt), seenVars))
      | SortedPat (pat, srt, _) -> 
	let srt = elaborateSort (env, srt, sort1) in
	let (p, env, seenVars) = elaboratePatternRec (env, pat, srt, seenVars) in
	(p, env, seenVars)
      | AliasPat (pat1, pat2, pos) ->
	let (pat1, env, seenVars) = elaboratePatternRec (env, pat1, sort1, seenVars) in
	let (pat2, env, seenVars) = elaboratePatternRec (env, pat2, sort1, seenVars) in
	(AliasPat (pat1, pat2, pos), env, seenVars)
      | EmbedPat (embedId, pattern, sort0, pos) ->
	let sort0 = elaborateSort (env, sort0, sort1) in
	let sort0 =
	    if undeterminedSort? sort0 then
	       %% See if there is only one constructor with this name
	       (case StringMap.find (env.constrs, embedId) of
		  | Some [srt_info] ->
		    let (_, c_srt) = metafySort srt_info in
		    elaborateSort (env, c_srt, sort1)
		  | _ -> sort0)
	     else
	       sort0
	in
	  if env.firstPass? && undeterminedSort? sort0 then
	    let (env, epat, seenVars) =
	        case pattern of
		  | None -> (env,None, seenVars)
		  | Some pat ->
	            let alpha = freshMetaTyVar ("EmbedPat_a", pos) in
		    let (pat, env, seenVars) = elaboratePatternRec (env, pat, alpha, seenVars) in
		    (env, Some pat, seenVars)
	    in
	    (EmbedPat (embedId, epat, sort0, pos), env, seenVars)
	  else
	    let srt = lookupEmbedId (env, embedId, sort0) in
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
			     ^ printSort sort1, pos);
		      (env, None, seenVars))
		   | (None, Some pat) -> 
		     let alpha = freshMetaTyVar ("EmbedPat_b", pos) in
		     let (pat, env, seenVars) = elaboratePatternRec (env, pat, alpha, seenVars)
		     in
		     (error (env, "Type for constructor "
			     ^ embedId
			     ^ " not found. Resolving with sort "
			     ^ printSort sort1, pos);
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
	      (EmbedPat (embedId, pat, sort1, pos), env, seenVars)
      | RecordPat (row, pos) ->
	let r = map (fn (id, srt)-> (id, freshMetaTyVar ("RecordPat", pos))) row in
	let _ = elaborateSort (env, (Product (r, pos)), sort1) in
	let r = ListPair.zip (r, row) in
	let (r, env, seenVars) = 
	    foldl (fn (((id, srt), (_, p)), (row, env, seenVars)) ->
		   let (p, env, seenVars) = elaboratePatternRec (env, p, srt, seenVars) in
		   (cons ((id, p), row), env, seenVars))
	      ([], env, seenVars) r
	in
	  (RecordPat (rev r, pos), env, seenVars)
      | RelaxPat (pat, term, pos) -> 
	let term = elaborateTerm (env, term, 
				 Arrow (sort1, type_bool, pos)) in
	let sort2 = (Subsort (sort1, term, pos)) in
	let (pat, env, seenVars) = elaboratePatternRec (env, pat, sort2, seenVars) in
	(RelaxPat (pat, term, pos), env, seenVars)
      | QuotientPat (pat, term, pos) ->
	let v = freshMetaTyVar ("QuotientPat", pos) in
	let sort2 = (Quotient (v, term, pos)) in
	let _ = elaborateSort (env, sort2, sort1) in
	let term = elaborateTerm (env, term, 
				  Arrow (Product ([("1", v), ("2", v)], pos), 
					 type_bool, pos)) in
	let (pat, env, seenVars) = elaboratePatternRec (env, pat, v, seenVars) in
	(QuotientPat (pat, term, pos), env, seenVars)
      | p -> (System.print p; System.fail "Nonexhaustive")


  % ========================================================================

  def pass2Error (env, _(* s *), msg, pos) =
    if env.firstPass? then %&& undeterminedSort? s 
      ()
    else 
      error (env, msg, pos)

  def blankString (n:Integer) =
    if n <= 0 then 
      "" 
    else
      let oneHundredSpaces = "                                                                                                    " in
      if n < 100 then
	substring (oneHundredSpaces, 0, n)
      else
	oneHundredSpaces ^ blankString (n - 100)

  def newLines lines = 
    case lines of
      | [] -> ""
      | [line] -> line
      | line :: lines -> 
        line ^ Char.toString (Char.chr 10) ^ "          " ^ (newLines lines)
     
  %% ---- called inside OPS : PASS 2  -----

  def checkTyVars (env, tvs, pos) =
    let 
      def aux (tvs, already_seen) =
	case tvs of
	  | []      -> ()
	  | id::tvs ->  
	    if StringSet.member (already_seen, id) then
	      error (env, 
		     "Repeated type variables : " ^ (foldl (fn (tv, str) -> str ^ " " ^ tv) "" tvs),
		     pos)
	    else 
	      aux (tvs, StringSet.add (already_seen, id))
    in 
      aux (tvs, StringSet.empty)

endspec
