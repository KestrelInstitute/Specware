% Synchronized with version 1.8 of  SW4/Languages/MetaSlang/TypeChecker/TypeCheckUtilities.sl 

Utilities qualifying spec
 import SpecToPosSpec                                   % for PosSpec's, plus convertSort[Info]ToPSort[Info]
 import ../Printer                                      % error messages
 import /Library/Legacy/DataStructures/MergeSort        % combining error messages
 import /Library/Legacy/DataStructures/ListPair         % misc utility
 import /Library/Unvetted/StringUtilities               % search
 import /Languages/MetaSlang/AbstractSyntax/Equalities  % equalType?

 sort Environment = StringMap Spec
 sort LocalEnv = 
      {importMap  : Environment,
       internal   : Spec,
       errors     : Ref (List (String * Position)),
       vars       : StringMap MS.Sort,
       firstPass? : Boolean,
       constrs    : StringMap (List Sort),
       file       : String}
 
 op initialEnv     : (* SpecRef * *) Spec * String -> LocalEnv
 op addConstrsEnv  : LocalEnv * Spec -> LocalEnv

 op addVariable    : LocalEnv * String * Sort -> LocalEnv
 op secondPass     : LocalEnv                 -> LocalEnv
 op setEnvSorts    : LocalEnv * SortMap       -> LocalEnv
 op unfoldSort     : LocalEnv * Sort          -> Sort
 op findVarOrOps   : LocalEnv * Id * Position -> List MS.Term

 op error          : LocalEnv * String * Position -> ()

 op unifyTerm?     : Spec -> (MS.Term * MS.Term) -> Boolean % hack to avoid circularity

 (* Auxiliary functions: *)

 % Generate a fresh type variable at a given position.
 op freshMetaTyVar : String * Position -> MS.Sort

 def metaTyVarCounter = (Ref 0) : Ref Nat

 def initializeMetaTyVarCounter () =
   metaTyVarCounter := 0

 def freshMetaTyVar (name, pos) = 
   let new_counter = 1 + (! metaTyVarCounter) in
   (metaTyVarCounter := new_counter;
    MetaTyVar (Ref {link     = None,
		    name     = name,
		    uniqueId = new_counter},
	       pos))

  op unlinkSort : MS.Sort -> MS.Sort
 def unlinkSort srt = 
  case srt of
   | MetaTyVar (mtv, _) -> 
     (case (! mtv).link of
       | Some srt -> unlinkSort srt
       | _ -> srt)
   | _ -> srt 

 %% sjw: unused?
 def unlinkMetaTyVar (mtv : MS.MetaTyVar) = 
   case ! mtv of
     | {link = Some (MetaTyVar (tw, _)), name, uniqueId} -> unlinkMetaTyVar tw
     | _ -> mtv

 %% create a copy of srt, but replace type vars by meta type vars
  op metafySort : Sort -> MetaSortScheme
 def metafySort srt =
   let (tvs, srt) = unpackSort srt in
   if null tvs then
     ([],srt)
   else
     let mtvar_position = Internal "metafySort" in
     let tv_map = List.map (fn tv -> (tv, freshMetaTyVar ("metafy", mtvar_position))) tvs in
     let
        def mapTyVar (tv, tvs, pos) : MS.Sort = 
	  case tvs of
	    | [] -> TyVar (tv, pos)
	    | (tv1, s) :: tvs -> 
	      if tv = tv1 then s else mapTyVar (tv, tvs, pos)

        def cp (srt : MS.Sort) = 
	  case srt of
	    | TyVar (tv, pos) -> mapTyVar (tv, tv_map, pos)
	    | srt -> srt
     in
     let srt = mapSort (id, cp, id) srt in
     let mtvs = List.map (fn (_, (MetaTyVar (y, _))) -> y) tv_map in
     (mtvs, srt)


 def initialEnv (spc, file) = 
   let errs : List (String * Position) = [] in
   let {sorts, ops, elements, qualifier} = spc in
   let MetaTyVar (tv,_)  = freshMetaTyVar ("initialEnv", Internal "ignored") in
   let spc = {%importInfo = importInfo,
	      sorts      = sorts,
	      ops        = ops,
	      elements   = elements,
	      qualifier  = qualifier
	     } : Spec
   in
   let env = {importMap  = StringMap.empty, % importMap,
              internal   = spc,
              errors     = Ref errs,
              vars       = StringMap.empty,
              firstPass? = true,
              constrs    = StringMap.empty,
              file       = file
             } : LocalEnv
   in
   env

 def sameCPSort? (s1 : MS.Sort, s2 : MS.Sort) : Boolean =
   case (s1, s2) of
    | (CoProduct (row1, _), CoProduct (row2, _)) ->
      length row1 = length row2
      && all (fn (id1, cs1) ->
	      exists (fn (id2, cs2) -> id1 = id2 & cs1 = cs2) row2)
             row1
    | _ -> false

 def addConstrsEnv (env, sp) =
   env << {internal = sp, 
	   constrs  = computeConstrMap sp % importMap
	   }

 %% Computes a map from constructor names to set of sorts for them
 def computeConstrMap spc : StringMap (List Sort) =
   let sorts = spc.sorts in
   let 

     def addConstr (id, cp_srt, constrMap) =
       case StringMap.find (constrMap, id) of
	 | None -> StringMap.insert (constrMap, id, [cp_srt])
	 | Some srt_prs ->
	   if exists (fn o_srt -> sameCPSort? (o_srt, cp_srt)) srt_prs then
	     constrMap
	   else 
	     StringMap.insert (constrMap, id, cons (cp_srt, srt_prs))

     def addSort (dfn, constrMap) =
       let (tvs, srt) = unpackSort dfn in
       case srt : MS.Sort of
	 | CoProduct (row, _) ->
	   foldl (fn ((id, _), constrMap) -> addConstr (id, dfn, constrMap)) 
	         constrMap
		 row
	   %% | Base (Qualified (qid, id), _, _) ->
	   %%   (let matching_entries : List(String * QualifiedId * SortInfo) = 
	   %%           lookupSortInImports(importMap, qid, id)
	   %%       in
	   %%       case matching_entries
	   %%  of [(_, _, (_, e_tvs, Some e_srt))] ->
	   %%     addSort(e_tvs, convertSortToPSort e_srt)
	   %%   | _ -> ())
	 | _ -> constrMap
   in
     foldSortInfos (fn (info, constrMap) -> 
		    foldl addSort constrMap (sortInfoDefs info))
                   StringMap.empty 
		   sorts


 %% These errors are more likely to be the primary cause of a type error than other errors
 def priorityErrorStrings = ["could not be identified","No matches for "]

 op  checkErrors : LocalEnv -> List (String * Position)
 def checkErrors (env : LocalEnv) = 
   let errors = env.errors in
   let 
     def compare (em1 as (msg_1, pos_1), em2 as (msg_2, pos_2)) =
       case (pos_1, pos_2) of
         | (File (file_1, left_1, right_1),
	    File (file_2, left_2, right_2)) ->
	   if file_1 = file_2 & left_1.1 = left_2.1 then
	     % If messages are on same line then prefer unidentified name error
	     let unid1 = exists (fn str -> some? (search (str,msg_1))) priorityErrorStrings in
	     let unid2 = exists (fn str -> some? (search (str,msg_2))) priorityErrorStrings in 
	     case (unid1,unid2) of
	       | (false, false) -> compare1 (em1,em2)
	       | (true,  false) -> Less
	       | (false, true)  -> Greater
	       | (true,  true)  -> compare1 (em1,em2)
	   else 
	     compare1 (em1, em2)
	  | _ -> compare1 (em1, em2)
     def compare1 ((msg_1, pos_1), (msg_2, pos_2)) =
       case Position.compare (pos_1, pos_2) of
	 | Equal -> String.compare (msg_1, msg_2)     
	 | c -> c     
   in
     let errors = MergeSort.uniqueSort compare (! errors) in
     errors

 % Pass error handling upward
 %   %% TODO:  UGH -- this could all be functional...
 %   let errMsg    = (Ref "") : Ref String in
 %   let last_file = (Ref "") : Ref Filename in
 %   let def printError(msg,pos) = 
 %       let same_file? = (case pos of
 %                           | File (filename, left, right) ->
 %                             let same? = (filename = (! last_file)) in
 %                             (last_file := filename;                       
 %			      same?)
 %                           | _ -> false)
 %       in
 %         errMsg := (! errMsg) ^
 %	           ((if same_file? then print else printAll) pos)
 %                   ^" : "^msg^PrettyPrint.newlineString()
               
 %   in
 %   if null(errors) then 
 %     None
 %   else
 %     (gotoErrorLocation errors;
 %      app printError errors;
 %      %               StringMap.app
 %      %                (fn spc -> MetaSlangPrint.printSpecToTerminal 
 %      %                                (convertPosSpecToSpec spc)) env.importMap;
 %      Some(! errMsg)
 %     )
 
 %  def gotoErrorLocation errors = 
 %   case errors of
 %     | (first_msg, first_position)::other_errors ->
 %        (case first_position of
 %          | File (file, (left_line, left_column, left_byte), right) ->   
 %            IO.gotoFilePosition (file, left_line, left_column)
 %          | _ -> 
 %            gotoErrorLocation other_errors)
 %     | _ -> ()
 
 def error (env, msg, pos) =
   let errors = env.errors in
   errors := cons ((msg, pos), ! errors)

 def addVariable (env, id, srt) =
   env << {vars = StringMap.insert (env.vars, id, srt)}

        
 def secondPass env =
   env << {firstPass? = false}

 def setEnvSorts (env, newSorts) =
   env << {internal = setSorts (env.internal, newSorts)}

 (* Unlink and unfold recursive sort declarations *)

 def compareQId (Qualified (q1, id1), Qualified (q2, id2)) : Comparison = 
   case String.compare (q1, q2) of
     | Equal  -> String.compare (id1, id2)
     | result -> result

 %% sjw: Replace base srt by its instantiated definition
 def unfoldSort (env,srt) = 
   unfoldSortRec (env, srt, SplaySet.empty compareQId) 
   
 def unfoldSortRec (env, srt, qids) : MS.Sort = 
   let unlinked_sort = unlinkSort srt in
   case unlinked_sort of
    | Base (qid, ts, pos) -> 
      if SplaySet.member (qids, qid) then
	(error (env,
		"The sort " ^ (printQualifiedId qid) ^ " is recursively defined using itself",
		pos);
	 unlinked_sort)
      else
        (case findAllSorts (env.internal, qid) of
          | info :: r ->
	    (if ~ (definedSortInfo? info) then
	       let tvs = firstSortDefTyVars info in
	       let l1 = length tvs in
	       let l2 = length ts  in
	       ((if l1 ~= l2 then
		   error (env,
			  "\nInstantiation list (" ^ 
			  (foldl (fn (arg, s) -> s ^ " " ^ (printSort arg)) "" ts) ^
			  " ) does not match argument list (" ^ 
			  (foldl (fn (tv, s) -> s ^ " " ^ tv) "" tvs) ^
			  " )",
			  pos)
		 else 
		   ());
		%% Use the primary name, even if the reference was via some alias.
                %% This normalizes all references to be via the same name.
		Base (primarySortName info, ts, pos))
	     else
	       let defs = sortInfoDefs info in
	       let base_defs = filter (fn srt ->
				       let (tvs, srt) = unpackSort srt in
				       case srt of
					 | Base _ -> true
					 | _      -> false)
	                              defs
	       in
		 case base_defs of
		   | [] ->
		     let dfn = maybeAndSort (defs, sortAnn info.dfn) in
		     instantiateScheme (env, pos, ts, dfn)
		   | _ ->
		     %% A base sort can be defined in terms of other base sorts.
   		     %% So we unfold recursively here.
		     let dfn = maybeAndSort (base_defs, sortAnn info.dfn) in
		     unfoldSortRec (env,
				    instantiateScheme (env, pos, ts, dfn),
				    %% Watch for self-references, even via aliases: 
				    foldl (fn (qid, qids) -> SplaySet.add (qids, qid))
				          qids
					  info.names))
          | [] -> 
	    (error (env, "Could not find sort "^ printQualifiedId qid, pos);
	     unlinked_sort))
   %| Boolean is the same as default case
    | s -> s 

 %% sjw: Returns srt with all  sort variables dereferenced
 def unlinkRec srt = 
   mapSort (fn x -> x, 
            fn s -> unlinkSort s,
            fn x -> x)
           srt
    
 %% findTheFoo2 is just a variant of findTheFoo, 
 %%  but taking Qualifier * Id instead of QualifiedId
 op findTheSort2 : LocalEnv * Qualifier * Id -> Option SortInfo
 op findTheOp2   : LocalEnv * Qualifier * Id -> Option OpInfo

 def findTheSort2 (env, qualifier, id) =
  %% We're looking for precisely one sort,
  %% which we might have specified as being unqualified.
  %% (I.e., unqualified is not a wildcard here.)
  findAQualifierMap (env.internal.sorts, qualifier, id)

 def findTheOp2 (env, qualifier, id) =
  %% We're looking for precisely one op,
  %% which we might have specified as being unqualified.
  %% (I.e., unqualified is not a wildcard here.)
  findAQualifierMap (env.internal.ops, qualifier, id)

 def findVarOrOps (env, id, a) =
  let 
    def mkTerm (a, info) =
      let (tvs, srt, tm) = unpackFirstOpDef info in
      let (_,srt) = metafySort (Pi (tvs, srt, noPos)) in
      let Qualified (q, id) = primaryOpName info in
      Fun (%% Allow (UnQualified, x) through as TwoNames term ...
	   %% if qualifier = UnQualified
	   %%  then OneName (id, fixity) 
	   %% else 
	   TwoNames (q, id, info.fixity),
	   srt,
	   a)
    def mkTerms infos =
      List.map (fn info -> mkTerm (a, info)) infos
  in
    case StringMap.find (env.vars, id) of
      | Some srt -> [Var ((id, srt), a)]
      | None     -> mkTerms (wildFindUnQualified (env.internal.ops, id))


 def instantiateScheme (env, pos, types, srt) = 
   let (tvs, sss) = unpackSort srt in
   if ~(length types = length tvs) then
     (error (env, 
	     "\nInstantiation list (" ^ 
	     (foldl (fn (arg, s) -> s ^ " " ^ (printSort arg)) "" types) ^
	     " ) does not match argument list (" ^ 
	     (foldl (fn (tv, s) -> s ^ " " ^ tv) "" tvs) ^
	     " )",
	     pos);
      sss)
   else
     let (new_mtvs, new_srt) = metafySort srt in
     (ListPair.app (fn (typ, mtv) -> 
                    let cell = ! mtv in
                    mtv := cell << {link = Some typ})
                   (types, new_mtvs);
      new_srt)


 sort Unification = | NotUnify  MS.Sort * MS.Sort 
                    | Unify List (MS.Sort * MS.Sort)

  op unifyL : [a] LocalEnv * MS.Sort * MS.Sort * 
                  List a * List a * 
                  List (MS.Sort * MS.Sort) * Boolean * 
                  (LocalEnv * a * a *  List (MS.Sort * MS.Sort) * Boolean -> Unification)
		  -> Unification
 def unifyL (env, srt1, srt2, l1, l2, pairs, ignoreSubsorts?, unify) : Unification = 
   %% ignoreSubsorts? really should be called ignoreSubsortPreds? 
   case (l1, l2) of
     | ([], []) -> Unify pairs
     | (e1 :: l1, e2 :: l2) -> 
       (case unify (env, e1, e2, pairs, ignoreSubsorts?) of
	  | Unify pairs -> unifyL (env, srt1, srt2, l1, l2, pairs, ignoreSubsorts?, unify)
	  | notUnify    -> notUnify)
     | _ -> NotUnify (srt1, srt2)

  op unifySorts : LocalEnv -> Boolean -> Sort -> Sort -> Boolean
 def unifySorts env ignoreSubsorts? s1 s2 =
   %% ignoreSubsorts? really should be called ignoreSubsortPreds? 

   (* Unify possibly recursive sorts s1 and s2.
      The auxiliary list "pairs" is a list of pairs of 
      sorts that can be assumed unified. The list avoids
      indefinite expansion of recursive sorts.
           
      Let for instance:

      sort T[x] = A + T[x]
      sort S = A + S

      then T[A] unifies with S
      because (T[A],S) is inserted to the list "pairs" in the
      first recursive invocation of the unification and 
      prevents further recursive calls.

      sort S = A + (A + S)
      sort T = A+T

      These also unify.

      More generally  sorts unify just in case that their
      unfoldings are bisimilar.

      *)

   case unify (env, s1, s2, [], ignoreSubsorts?) of
     | Unify     _       -> true
     | NotUnify (s1, s2) -> false

  op unifyCP : LocalEnv * Sort * Sort * 
               List (Id * Option Sort) * List (Id * Option Sort) * 
	       List (Sort * Sort) * Boolean
	       -> Unification
 def unifyCP (env, srt1, srt2, r1, r2, pairs, ignoreSubsorts?) = 
   unifyL (env,srt1, srt2, r1, r2, pairs,ignoreSubsorts?,
	   fn (env, (id1, s1), (id2, s2), pairs, ignoreSubsorts?) -> 
	   if id1 = id2 then
	     case (s1, s2) of
	       | (None,    None)    -> Unify pairs 
	       | (Some s1, Some s2) -> unify (env, s1, s2, pairs, ignoreSubsorts?)
	       | _                  -> NotUnify (srt1, srt2)
	   else
	     NotUnify (srt1, srt2))

  op unifyP : LocalEnv * Sort * Sort * 
              List (Id * Sort) * List (Id * Sort) * 
              List (Sort * Sort) * Boolean
	      -> Unification
 def unifyP (env, srt1, srt2, r1, r2, pairs, ignoreSubsorts?) = 
     unifyL (env, srt1, srt2, r1, r2, pairs, ignoreSubsorts?,
	     fn (env, (id1, s1), (id2, s2), pairs, ignoreSubsorts?) -> 
	     if id1 = id2 then
	       unify (env, s1, s2, pairs, ignoreSubsorts?)
	     else 
	       NotUnify (srt1, srt2))

  op unify : LocalEnv * Sort * Sort * List (Sort * Sort) * Boolean -> Unification
 def unify (env, s1, s2, pairs, ignoreSubsorts?) = 
   let spc  = env.internal in
   let pos1 = sortAnn s1  in
   let pos2 = sortAnn s2  in
   let srt1 = withAnnS (unlinkSort s1, pos1) in % ? DerivedFrom pos1 ?
   let srt2 = withAnnS (unlinkSort s2, pos2) in % ? DerivedFrom pos2 ?
   if equalType? (srt1, srt2) then 
     Unify pairs 
   else
     case (srt1, srt2) of

       | (And (srts1, _), _) ->
         foldl (fn (s1, result) ->
		case result of
		  | Unify _ -> result
		  | _ -> unify (env, s1, srt2, pairs, ignoreSubsorts?))
	       (NotUnify (srt1, srt2))
	       srts1
       
       | (_, And (srts2, _)) ->
         foldl (fn (s2, result) ->
		case result of
		  | Unify _ -> result
		  | _ -> unify (env, srt1, s2, pairs, ignoreSubsorts?))
	       (NotUnify (srt1, srt2))
	       srts2
       
       | (CoProduct (r1, _), CoProduct (r2, _)) -> 
         unifyCP (env, srt1, srt2, r1, r2, pairs, ignoreSubsorts?)

       | (Product (r1, _), Product (r2, _)) -> 
	 unifyP (env, srt1, srt2, r1, r2, pairs, ignoreSubsorts?)

       | (Arrow (t1, t2, _), Arrow (s1, s2, _)) -> 
	 (case unify (env, t1, s1, pairs, ignoreSubsorts?) of
	    | Unify pairs -> unify (env, t2, s2, pairs, ignoreSubsorts?)
	    | notUnify -> notUnify)

       | (Quotient (ty, trm, _), Quotient (ty2, trm2, _)) ->
	 if equalTermStruct? (trm, trm2) then
	   unify (env, ty, ty2, pairs, ignoreSubsorts?)
	 else 
	   NotUnify (srt1, srt2)

	   %                 if trm = trm_ then
	   %                   unify (ty, ty2, pairs, ignoreSubsorts?) 
	   %                 else 
	   %                   NotUnify (srt1, srt2)
	   %               | (Subsort (ty, trm, _), Subsort (ty2, trm2, _)) -> 
	   %                  if trm = trm_ then
	   %                    unify (ty, ty_, pairs) 
	   %                  else 
	   %                    NotUnify (srt1, srt2)

	| (Base (id, ts, pos1), Base (id2, ts2, pos2)) -> 
	  if exists (fn (p1, p2) -> 
		     %% p = (srt1, srt2) 
		     %% need predicate that chases metavar links
		     equalType? (p1, srt1) &
		     equalType? (p2, srt2))
	            pairs 
	    then
	      Unify pairs
	  else if id = id2 then
	    unifyL (env, srt1, srt2, ts, ts2, pairs, ignoreSubsorts?, unify)
	  else 
	    let s1x = unfoldSort (env, srt1) in
	    let s2x = unfoldSort (env, srt2) in
	    if equalType? (s1, s1x) & equalType? (s2x, s2) then
	      NotUnify  (srt1, srt2)
	    else 
	      unify (env, withAnnS (s1x, pos1), 
		     withAnnS (s2x, pos2), 
		     cons ((s1, s2), pairs), 
		     ignoreSubsorts?)

	| (Boolean _, Boolean _) -> Unify pairs

	| (TyVar (id1, _), TyVar (id2, _)) -> 
	  if id1 = id2 then
	    Unify pairs
	  else 
	    NotUnify (srt1, srt2)

	| (MetaTyVar (mtv, _), _) -> 
	   let s3 = unfoldSort (env, srt2) in
	   let s4 = unlinkSort s3 in
	   if equalType? (s4, s1) then
	     Unify pairs
	   else if occurs (mtv, s4) then
	     NotUnify (srt1, srt2)
	   else 
	     (linkMetaTyVar mtv (withAnnS (s2, pos2)); 
	      Unify pairs)

	| (s3, MetaTyVar (mtv, _)) -> 
	  let s4 = unfoldSort (env, s3) in
	  let s5 = unlinkSort s4 in
	  if equalType? (s5, s2) then
	    Unify pairs
	  else if occurs (mtv, s5) then
	    NotUnify (srt1, srt2)
	  else
	    (linkMetaTyVar mtv (withAnnS (s1, pos1)); 
	     Unify pairs)

	% TODO: alpha equivalence...
	% | (Pi _, Pi _) -> alpha equivalence directly
        % or convert callers of unify to convert TyVars to MetaTyVars??

	| (Pi _, _) ->
	  % TODO: or perhaps alpha equivalence by converting vars to meta-ty-vars here...
	  unify (env, sortInnerSort srt1, srt2, pairs, ignoreSubsorts?)

	| (_, Pi _) ->
	  unify (env, srt1, sortInnerSort srt2, pairs, ignoreSubsorts?)

	| (Any _, _) -> Unify pairs
	| (_, Any _) -> Unify pairs

	| _ ->
	  if ignoreSubsorts? then
	    case (srt1, srt2) of
	      | (Subsort (ty, _, _), ty2) -> unify (env, ty, ty2, pairs, ignoreSubsorts?)
	      | (ty, Subsort (ty2, _, _)) -> unify (env, ty, ty2, pairs, ignoreSubsorts?)
	      | (Base _, _) -> 
	        let s1x = unfoldSort (env, srt1) in
		if equalType? (s1, s1x) then
		  NotUnify (srt1, srt2)
		else 
		  unify (env, s1x, s2, pairs, ignoreSubsorts?)
	      | (_, Base _) ->
		let s3 = unfoldSort (env, srt2) in
		if equalType? (s2, s3) then
		  NotUnify (srt1, srt2)
		else 
		  unify (env, s1, s3, pairs, ignoreSubsorts?)
	      | _ -> NotUnify (srt1, srt2)
	  else 
	    case (srt1, srt2) of
	      | (Subsort (s1, p1, _), Subsort (s2, p2, _)) ->
		if unifyTerm? env.internal (p1, p2) then 
		  unify (env, s1, s2, pairs, ignoreSubsorts?)
		else
		  NotUnify (srt1, srt2)
	      | (Base _, _) -> 
	        let  s3 = unfoldSort (env, srt1) in
		if equalType? (s1, s3) then 
		  NotUnify (srt1, srt2)
		else 
		  unify (env, s3, s2, pairs, ignoreSubsorts?)
	      | (_, Base _) ->
		let s3 = unfoldSort (env, srt2) in
		if equalType? (s2, s3) then
		  NotUnify (srt1, srt2)
		else 
		  unify (env, s1, s3, pairs, ignoreSubsorts?)
	      | _ -> NotUnify (srt1, srt2)

  op consistentSorts? : LocalEnv * MS.Sort * MS.Sort * Boolean -> Boolean
 def consistentSorts? (env, srt1, srt2, ignoreSubsorts?) =
   let free_mtvs = freeMetaTyVars (srt1) ++ freeMetaTyVars (srt2) in
   let val = (unifySorts env ignoreSubsorts? srt1 srt2) in
   (clearMetaTyVarLinks free_mtvs;
    val)

 def clearMetaTyVarLinks mtvs =
  app (fn mtv -> 
       let cell = ! mtv in
       mtv := cell << {link = None})
      mtvs

 def freeMetaTyVars srt = 
   let vars = (Ref []) : Ref MS.MetaTyVars in
   let 
     def vr srt = 
       case srt of
	 | MetaTyVar (tv, pos) -> 
	   (case unlinkSort srt of
	      | MetaTyVar (tv, _) -> (vars := cons (tv, ! vars); srt)
	      | s -> mapSort (fn x -> x, vr, fn x -> x) (withAnnS (s, pos)))
	 | _ -> srt
   in
   let _ = mapSort (fn x -> x, vr, fn x -> x) srt in
   ! vars

 def occurs (mtv : MS.MetaTyVar, srt : MS.Sort) : Boolean = 
   let
      def occursOptRow (mtv, row) =
       case row of
	 | [] -> false
	 | (_, Some t) :: rRow -> occurs (mtv, t) or occursOptRow (mtv, rRow)
	 | (_, None)   :: rRow -> occursOptRow (mtv, rRow)
     def occursRow (mtv, row) =
       case row of
	 | [] -> false
	 | (_, t) :: rRow -> occurs (mtv, t) or occursRow (mtv, rRow)
   in
   case srt of
     | CoProduct (row,     _) -> occursOptRow (mtv, row)
     | Product   (row,     _) -> occursRow    (mtv, row)
     | Arrow     (t1, t2,  _) -> occurs (mtv, t1) or occurs (mtv, t2)
     %% sjw 3/404 It seems safe to ignore the predicates and it fixes bug 82
     | Quotient  (t, pred, _) -> occurs (mtv, t)  %or occursT (mtv, pred)
     | Subsort   (t, pred, _) -> occurs (mtv, t)  %or occursT (mtv, pred)
     | Base      (_, srts, _) -> exists (fn s -> occurs (mtv, s)) srts
     | Boolean             _  -> false
     | TyVar               _  -> false 
     | MetaTyVar           _  -> (case unlinkSort srt of
				    | MetaTyVar (mtv1, _) -> mtv = mtv1 
				    | t -> occurs (mtv, t))
     | And       (srts,    _) -> exists (fn s -> occurs (mtv, s)) srts
     | Any                  _ -> false

 def occursT (mtv, pred) =
   case pred of
     | ApplyN     (ms,            _) -> exists (fn M -> occursT (mtv, M)) ms
     | Record     (fields,        _) -> exists (fn (_, M) -> occursT (mtv, M)) fields
     | Bind       (_, vars, body, _) -> exists (fn (_, s) -> occurs (mtv, s)) vars or occursT (mtv, body)
     | The        ((_,s), body,   _) -> occurs (mtv, s) or occursT (mtv, body)
     | IfThenElse (M, N, P,       _) -> occursT (mtv, M) or occursT (mtv, N) or occursT (mtv, P)
     | Var        ((_, s),        _) -> occurs (mtv, s)
     | Fun        (_, s,          _) -> occurs (mtv, s)
     | Seq        (ms,            _) -> exists (fn M -> occursT (mtv, M)) ms
     | Let        (decls, body,   _) -> occursT (mtv, body) or exists (fn (p, M) -> occursT (mtv, M)) decls
     | LetRec     (decls, body,   _) -> occursT (mtv, body) or exists (fn (p, M) -> occursT (mtv, M)) decls
     | Lambda     (rules,         _) -> exists (fn (p, c, M) -> occursT (mtv, M)) rules
     | And        (tms,           _) -> exists (fn t -> occursT (mtv, t)) tms
     | _  -> false

 (* Apply substitution as variable linking *)
  op linkMetaTyVar : MS.MetaTyVar -> MS.Sort -> ()
 def linkMetaTyVar (mtv : MS.MetaTyVar) tm = 
   let cell = ! mtv in
   (%%String.writeLine ("Linking "^name^Nat.toString uniqueId^" with "^printSort t);
    mtv := cell << {link = Some tm})

  op simpleTerm : MS.Term -> Boolean
 def simpleTerm term = 
   case term of
     | Var _ -> true
     | Fun _ -> true
     | _ -> false

 %% Used by the Accord extension to typechecker that considers f(x) to be a 
 %% possible interpretation of x.f (if type of x is a subsort of domain of f)
 %% Don't do any unification, to avoid coercing undeclared x to bogus type.
  op subsort? : LocalEnv -> MS.Sort -> MS.Sort -> Boolean
 def subsort? env x y =
   let spc = env.internal in
   let 
     def aux x =
       equalType? (x, y) ||
       (let x = unfoldSort (env, x) in
        case x of
	  | Subsort (x, _, _) -> aux x 
	  | _ -> false)
   in
     aux x

endspec
