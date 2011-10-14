% Synchronized with version 1.8 of  SW4/Languages/MetaSlang/TypeChecker/TypeCheckUtilities.sl 

Utilities qualifying spec
 import SpecToPosSpec                                   % for PosSpec's, plus convertType[Info]ToPType[Info]
 import ../Printer                                      % error messages
 import /Library/Legacy/DataStructures/MergeSort        % combining error messages
 import /Library/Legacy/DataStructures/ListPair         % misc utility
 import /Library/Unvetted/StringUtilities               % search
 import /Languages/MetaSlang/AbstractSyntax/Equalities  % equalType?

 type Environment = StringMap Spec
 type LocalEnv = 
      {importMap  : Environment,
       internal   : Spec,
       errors     : Ref (List (String * Position)),
       vars       : StringMap MSType,
       firstPass? : Bool,
       constrs    : StringMap (List (QualifiedId * MSType)),
       file       : String}
 
 op initialEnv     : (* SpecRef * *) Spec * String -> LocalEnv
 op addConstrsEnv  : LocalEnv * Spec -> LocalEnv

 op addVariable    : LocalEnv * String * MSType -> LocalEnv
 op secondPass     : LocalEnv                   -> LocalEnv
 op setEnvTypes    : LocalEnv * TypeMap         -> LocalEnv
 op unfoldType     : LocalEnv * MSType          -> MSType
 op findVarOrOps   : LocalEnv * Id * Position   -> List MSTerm

 op error          : LocalEnv * String * Position -> ()

 op unifyTerm?     : Spec -> (MSTerm * MSTerm) -> Bool % hack to avoid circularity

 (* Auxiliary functions: *)

 % Generate a fresh type variable at a given position.
 op freshMetaTyVar : String * Position -> MSType

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

  op unlinkType : MSType -> MSType
 def unlinkType srt = 
  case srt of
   | MetaTyVar (mtv, _) -> 
     (case (! mtv).link of
       | Some srt -> unlinkType srt
       | _ -> srt)
   | _ -> srt 

 %% sjw: unused?
 def unlinkMetaTyVar (mtv : MS.MetaTyVar) = 
   case ! mtv of
     | {link = Some (MetaTyVar (tw, _)), name, uniqueId} -> unlinkMetaTyVar tw
     | _ -> mtv

 %% create a copy of srt, but replace type vars by meta type vars
  op metafyType : MSType -> MetaTypeScheme
 def metafyType srt =
   let (tvs, srt) = unpackType srt in
   if empty? tvs then
     ([],srt)
   else
     let mtvar_position = Internal "metafyType" in
     let tv_map = List.map (fn tv -> (tv, freshMetaTyVar ("metafy", mtvar_position))) tvs in
     let
        def mapTyVar (tv, tvs, pos) : MSType = 
	  case tvs of
	    | [] -> TyVar (tv, pos)
	    | (tv1, s) :: tvs -> 
	      if tv = tv1 then s else mapTyVar (tv, tvs, pos)

        def cp (srt : MSType) = 
	  case srt of
	    | TyVar (tv, pos) -> mapTyVar (tv, tv_map, pos)
	    | srt -> srt
     in
     let srt = mapType (id, cp, id) srt in
     let mtvs = List.map (fn (_, (MetaTyVar (y, _))) -> y) tv_map in
     (mtvs, srt)

 op metafyBaseType(qid: QualifiedId, ty: MSType, pos: Position): MSType * MSType =
   let (tvs, srt) = unpackType ty in
   if empty? tvs then
     (Base(qid,[],pos),srt)
   else
   let mtvar_position = pos in          % Internal "metafyType"
   let tv_map = List.map (fn tv -> (tv, freshMetaTyVar ("metafy", mtvar_position))) tvs in
   let  def mapTyVar (tv, tvs, pos) : MSType = 
	  case tvs of
	    | [] -> TyVar (tv, pos)
	    | (tv1, s) :: tvs -> 
	      if tv = tv1 then s else mapTyVar (tv, tvs, pos)

        def cp (srt : MSType) = 
	  case srt of
	    | TyVar (tv, pos) -> mapTyVar (tv, tv_map, pos)
	    | srt -> srt
     in
     let srt = mapType (id, cp, id) srt in
     let mtvs = List.map (fn (_, mv) -> mv) tv_map in
     (Base(qid,mtvs,pos), srt)

 def initialEnv (spc, file) = 
   let errs : List (String * Position) = [] in
   let {types, ops, elements, qualifier} = spc in
   let MetaTyVar (tv,_)  = freshMetaTyVar ("initialEnv", Internal "ignored") in
   let spc = {%importInfo = importInfo,
	      types      = types,
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

 def sameCPType? (s1 : MSType, s2 : MSType) : Bool =
   case (s1, s2) of
    | (CoProduct (row1, _), CoProduct (row2, _)) ->
      length row1 = length row2
      && forall? (fn (id1, cs1) ->
                    exists? (fn (id2, cs2) -> id1 = id2 && cs1 = cs2) row2)
             row1
    | _ -> false

 def addConstrsEnv (env, sp) =
   env << {internal = sp, 
	   constrs  = computeConstrMap sp % importMap
	   }

 %% Computes a map from constructor names to set of types for them
 def computeConstrMap spc : StringMap (List (QualifiedId * MSType)) =
   let types = spc.types in
   let 

     def addConstr (id, qid, cp_srt, constrMap) =
       case StringMap.find (constrMap, id) of
	 | None -> StringMap.insert (constrMap, id, [(qid, cp_srt)])
	 | Some srt_prs ->
	   if exists? (fn (o_qid,o_srt) -> qid = o_qid) srt_prs then
	     constrMap
	   else
	     StringMap.insert (constrMap, id,  (qid, cp_srt) :: srt_prs)

     def addType qid (constrMap, dfn) =
       let (tvs, srt) = unpackType dfn in
       case srt of
	 | CoProduct (row, _) ->
	   foldl (fn (constrMap, (id,_)) -> addConstr (id, qid, dfn, constrMap)) 
	         constrMap
		 row
	   %% | Base (Qualified (qid, id), _, _) ->
	   %%   (let matching_entries : List(String * QualifiedId * TypeInfo) = 
	   %%           lookupTypeInImports(importMap, qid, id)
	   %%       in
	   %%       case matching_entries
	   %%  of [(_, _, (_, e_tvs, Some e_srt))] ->
	   %%     addType(e_tvs, convertTypeToPType e_srt)
	   %%   | _ -> ())
	 | _ -> constrMap
   in
     foldTypeInfos (fn (info, constrMap) -> 
		    foldl (addType (primaryTypeName info)) constrMap (typeInfoDefs info))
                   StringMap.empty 
		   types


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
	   if file_1 = file_2 && left_1.1 = left_2.1 then
	     % If messages are on same line then prefer unidentified name error
	     let unid1 = exists? (fn str -> some? (search (str,msg_1))) priorityErrorStrings in
	     let unid2 = exists? (fn str -> some? (search (str,msg_2))) priorityErrorStrings in 
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

 op traceErrors?: Bool = false
 
 def error (env, msg, pos) =
   let _ = if traceErrors? then writeLine(msg^" at\n"^Position.print pos) else () in
   let errors = env.errors in
   errors := (msg, pos) :: !errors

 def addVariable (env, id, srt) =
   env << {vars = StringMap.insert (env.vars, id, srt)}

        
 def secondPass env =
   env << {firstPass? = false}

 def setEnvTypes (env, newTypes) =
   env << {internal = setTypes (env.internal, newTypes)}

 op setEnvOps (env: LocalEnv, newOps: OpMap): LocalEnv =
   env << {internal = setOps (env.internal, newOps)}

 (* Unlink and unfold recursive type declarations *)

 def compareQId (Qualified (q1, id1), Qualified (q2, id2)) : Comparison = 
   case String.compare (q1, q2) of
     | Equal  -> String.compare (id1, id2)
     | result -> result

 %% sjw: Replace base srt by its instantiated definition
 def unfoldType (env,srt) = 
   unfoldTypeRec (env, srt, SplaySet.empty compareQId) 
   
 def unfoldTypeRec (env, srt, qids) : MSType = 
   let unlinked_type = unlinkType srt in
   case unlinked_type of
    | Base (qid, ts, pos) -> 
      if SplaySet.member (qids, qid) then
	(error (env,
		"The type " ^ (printQualifiedId qid) ^ " is recursively defined using itself",
		pos);
	 unlinked_type)
      else
        (case findAllTypes (env.internal, qid) of
          | info :: r ->
	    (if ~ (definedTypeInfo? info) then
	       let tvs = firstTypeDefTyVars info in
	       let l1 = length tvs in
	       let l2 = length ts  in
	       ((if l1 ~= l2 then
		   error (env,
			  "\nInstantiation list (" ^ 
			  (foldl (fn (s,arg) -> s ^ " " ^ (printType arg)) "" ts) ^
			  " ) does not match argument list (" ^ 
			  (foldl (fn (s,tv) -> s ^ " " ^ tv) "" tvs) ^
			  " )",
			  pos)
		 else 
		   ());
		%% Use the primary name, even if the reference was via some alias.
                %% This normalizes all references to be via the same name.
		Base (primaryTypeName info, ts, pos))
	     else
	       let defs = typeInfoDefs info in
	       let base_defs = filter (fn srt ->
				       let (tvs, srt) = unpackType srt in
				       case srt of
					 | Base _ -> true
					 | _      -> false)
	                              defs
	       in
		 case base_defs of
		   | [] ->
		     let dfn = maybeAndType (defs, typeAnn info.dfn) in
		     instantiateScheme (env, pos, ts, dfn)
		   | _ ->
		     %% A base type can be defined in terms of other base types.
   		     %% So we unfold recursively here.
		     let dfn = maybeAndType (base_defs, typeAnn info.dfn) in
		     unfoldTypeRec (env,
				    instantiateScheme (env, pos, ts, dfn),
				    %% Watch for self-references, even via aliases: 
				    foldl (fn (qids,qid) -> SplaySet.add (qids, qid))
				          qids
					  info.names))
          | [] -> 
	    (error (env, "Could not find type "^ printQualifiedId qid, pos);
	     unlinked_type))
   %| Boolean is the same as default case
    | s -> s 

 %% sjw: Returns srt with all  type variables dereferenced
 def unlinkRec srt = 
   mapType (fn x -> x, 
            fn s -> unlinkType s,
            fn x -> x)
           srt
    
 %% findTheFoo2 is just a variant of findTheFoo, 
 %%  but taking Qualifier * Id instead of QualifiedId
 op findTheType2 : LocalEnv * Qualifier * Id -> Option TypeInfo
 op findTheOp2   : LocalEnv * Qualifier * Id -> Option OpInfo

 def findTheType2 (env, qualifier, id) =
  %% We're looking for precisely one type,
  %% which we might have specified as being unqualified.
  %% (I.e., unqualified is not a wildcard here.)
  findAQualifierMap (env.internal.types, qualifier, id)

 def findTheOp2 (env, qualifier, id) =
  %% We're looking for precisely one op,
  %% which we might have specified as being unqualified.
  %% (I.e., unqualified is not a wildcard here.)
  findAQualifierMap (env.internal.ops, qualifier, id)

 op findVar(env: LocalEnv, id: Id, a: Position): Option MSTerm =
   case StringMap.find (env.vars, id) of
      | Some srt -> Some(Var ((id, srt), a))
      | None -> None

 def findVarOrOps (env, id, a) =
  let 
    def mkTerm (a, info) =
      let (tvs, srt, tm) = unpackFirstOpDef info in
      let (_,srt) = metafyType (Pi (tvs, srt, noPos)) in
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
   let (tvs, sss) = unpackType srt in
   if ~(length types = length tvs) then
     (error (env, 
	     "\nInstantiation list (" ^ 
	     (foldl (fn (s,arg) -> s ^ " " ^ (printType arg)) "" types) ^
	     " ) does not match argument list (" ^ 
	     (foldl (fn (s,tv) -> s ^ " " ^ tv) "" tvs) ^
	     " )",
	     pos);
      sss)
   else
     let (new_mtvs, new_srt) = metafyType srt in
     (ListPair.app (fn (typ, mtv) -> 
                    let cell = ! mtv in
                    mtv := cell << {link = Some typ})
                   (types, new_mtvs);
      new_srt)


 type Unification = | NotUnify  MSType * MSType 
                    | Unify List (MSType * MSType)

  op unifyL : [a] LocalEnv * MSType * MSType * 
                  List a * List a * 
                  List (MSType * MSType) * Bool * 
                  (LocalEnv * a * a *  List (MSType * MSType) * Bool -> Unification)
		  -> Unification
 def unifyL (env, srt1, srt2, l1, l2, pairs, ignoreSubtypes?, unify) : Unification = 
   %% ignoreSubtypes? really should be called ignoreSubtypePreds? 
   case (l1, l2) of
     | ([], []) -> Unify pairs
     | (e1 :: l1, e2 :: l2) -> 
       (case unify (env, e1, e2, pairs, ignoreSubtypes?) of
	  | Unify pairs -> unifyL (env, srt1, srt2, l1, l2, pairs, ignoreSubtypes?, unify)
	  | notUnify    -> notUnify)
     | _ -> NotUnify (srt1, srt2)

  op unifyTypes : LocalEnv -> Bool -> MSType -> MSType -> Bool
 def unifyTypes env ignoreSubtypes? s1 s2 =
   %% ignoreSubtypes? really should be called ignoreSubtypePreds? 

   (* Unify possibly recursive types s1 and s2.
      The auxiliary list "pairs" is a list of pairs of 
      types that can be assumed unified. The list avoids
      indefinite expansion of recursive types.
           
      Let for instance:

      type T[x] = A + T[x]
      type S = A + S

      then T[A] unifies with S
      because (T[A],S) is inserted to the list "pairs" in the
      first recursive invocation of the unification and 
      prevents further recursive calls.

      type S = A + (A + S)
      type T = A+T

      These also unify.

      More generally  types unify just in case that their
      unfoldings are bisimilar.

      *)

   case unify (env, s1, s2, [], ignoreSubtypes?) of
     | Unify     _       -> true
     | NotUnify (s1, s2) -> false

  op unifyCP : LocalEnv * MSType * MSType * 
               List (Id * Option MSType) * List (Id * Option MSType) * 
	       List (MSType * MSType) * Bool
	       -> Unification
 def unifyCP (env, srt1, srt2, r1, r2, pairs, ignoreSubtypes?) = 
   unifyL (env,srt1, srt2, r1, r2, pairs,ignoreSubtypes?,
	   fn (env, (id1, s1), (id2, s2), pairs, ignoreSubtypes?) -> 
	   if id1 = id2 then
	     case (s1, s2) of
	       | (None,    None)    -> Unify pairs 
	       | (Some s1, Some s2) -> unify (env, s1, s2, pairs, ignoreSubtypes?)
	       | _                  -> NotUnify (srt1, srt2)
	   else
	     NotUnify (srt1, srt2))

  op unifyP : LocalEnv * MSType * MSType * 
              List (Id * MSType) * List (Id * MSType) * 
              List (MSType * MSType) * Bool
	      -> Unification
 def unifyP (env, srt1, srt2, r1, r2, pairs, ignoreSubtypes?) = 
     unifyL (env, srt1, srt2, r1, r2, pairs, ignoreSubtypes?,
	     fn (env, (id1, s1), (id2, s2), pairs, ignoreSubtypes?) -> 
	     if id1 = id2 then
	       unify (env, s1, s2, pairs, ignoreSubtypes?)
	     else 
	       NotUnify (srt1, srt2))

 op debugUnify?: Bool = false

  op unify : LocalEnv * MSType * MSType * List (MSType * MSType) * Bool -> Unification
 def unify (env, s1, s2, pairs, ignoreSubtypes?) = 
   let _ = if debugUnify? then writeLine("Unifying "^printType s1^" with "^printType s2) else () in
   let spc  = env.internal in
   let pos1 = typeAnn s1  in
   let pos2 = typeAnn s2  in
   let srt1 = withAnnS (unlinkType s1, pos1) in % ? DerivedFrom pos1 ?
   let srt2 = withAnnS (unlinkType s2, pos2) in % ? DerivedFrom pos2 ?
   if equalType? (srt1, srt2) then 
     Unify pairs 
   else
     case (srt1, srt2) of

       | (And (srts1, _), _) ->
         foldl (fn (result,s1) ->
		case result of
		  | Unify _ -> result
		  | _ -> unify (env, s1, srt2, pairs, ignoreSubtypes?))
	       (NotUnify (srt1, srt2))
	       srts1
       
       | (_, And (srts2, _)) ->
         foldl (fn (result,s2) ->
		case result of
		  | Unify _ -> result
		  | _ -> unify (env, srt1, s2, pairs, ignoreSubtypes?))
	       (NotUnify (srt1, srt2))
	       srts2
       
       | (CoProduct (r1, _), CoProduct (r2, _)) -> 
         unifyCP (env, srt1, srt2, r1, r2, pairs, ignoreSubtypes?)

       | (Product (r1, _), Product (r2, _)) -> 
	 unifyP (env, srt1, srt2, r1, r2, pairs, ignoreSubtypes?)

       | (Arrow (t1, t2, _), Arrow (s1, s2, _)) -> 
	 (case unify (env, t1, s1, pairs, ignoreSubtypes?) of
	    | Unify pairs -> unify (env, t2, s2, pairs, ignoreSubtypes?)
	    | notUnify -> notUnify)

       | (Quotient (ty, trm, _), Quotient (ty2, trm2, _)) ->
	 if equalTermStruct? (trm, trm2) then
	   unify (env, ty, ty2, pairs, ignoreSubtypes?)
	 else 
	   NotUnify (srt1, srt2)

	   %                 if trm = trm_ then
	   %                   unify (ty, ty2, pairs, ignoreSubtypes?) 
	   %                 else 
	   %                   NotUnify (srt1, srt2)
	   %               | (Subtype (ty, trm, _), Subtype (ty2, trm2, _)) -> 
	   %                  if trm = trm_ then
	   %                    unify (ty, ty_, pairs) 
	   %                  else 
	   %                    NotUnify (srt1, srt2)

	| (Boolean _, Boolean _) -> Unify pairs

	| (TyVar (id1, _), TyVar (id2, _)) -> 
	  if id1 = id2 then
	    Unify pairs
	  else 
	    NotUnify (srt1, srt2)

	| (MetaTyVar (mtv, _), _) -> 
	   let s3 = unfoldType (env, srt2) in
	   let s4 = unlinkType s3 in
	   if equalType? (s4, s1) then
	     Unify pairs
	   else if occurs (mtv, s4) then
	     NotUnify (srt1, srt2)
	   else 
	     (linkMetaTyVar mtv (withAnnS (s2, pos2)); 
	      Unify pairs)

	| (s3, MetaTyVar (mtv, _)) -> 
	  let s4 = unfoldType (env, s3) in
	  let s5 = unlinkType s4 in
	  if equalType? (s5, s2) then
	    Unify pairs
	  else if occurs (mtv, s5) then
	    NotUnify (srt1, srt2)
	  else
	    (linkMetaTyVar mtv (withAnnS (s1, pos1)); 
	     Unify pairs)

	| (Base (id, ts, pos1), Base (id2, ts2, pos2)) -> 
	  if exists? (fn (p1, p2) -> 
                        %% p = (srt1, srt2) 
                        %% need predicate that chases metavar links
                        equalType? (p1, srt1) &&
                        equalType? (p2, srt2))
	            pairs 
	    then
	      Unify pairs
	  else if id = id2 then
	    unifyL (env, srt1, srt2, ts, ts2, pairs, ignoreSubtypes?, unify)
	  else 
	    let s1x = unfoldType (env, srt1) in
	    let s2x = unfoldType (env, srt2) in
	    if equalType? (s1, s1x) && equalType? (s2x, s2) then
	      NotUnify  (srt1, srt2)
	    else 
	      unify (env, withAnnS (s1x, pos1), 
		     withAnnS (s2x, pos2), 
		     Cons ((s1, s2), pairs), 
		     ignoreSubtypes?)

	% TODO: alpha equivalence...
	% | (Pi _, Pi _) -> alpha equivalence directly
        % or convert callers of unify to convert TyVars to MetaTyVars??

	| (Pi _, _) ->
	  % TODO: or perhaps alpha equivalence by converting vars to meta-ty-vars here...
	  unify (env, typeInnerType srt1, srt2, pairs, ignoreSubtypes?)

	| (_, Pi _) ->
	  unify (env, srt1, typeInnerType srt2, pairs, ignoreSubtypes?)

	| (Any _, _) -> Unify pairs
	| (_, Any _) -> Unify pairs

	| _ ->
	  if ignoreSubtypes? then
	    case (srt1, srt2) of
	      | (Subtype (ty, _, _), ty2) -> unify (env, ty, ty2, pairs, ignoreSubtypes?)
	      | (ty, Subtype (ty2, _, _)) -> unify (env, ty, ty2, pairs, ignoreSubtypes?)
	      | (Base _, _) -> 
	        let s1x = unfoldType (env, srt1) in
		if equalType? (s1, s1x) then
		  NotUnify (srt1, srt2)
		else 
		  unify (env, s1x, s2, pairs, ignoreSubtypes?)
	      | (_, Base _) ->
		let s3 = unfoldType (env, srt2) in
		if equalType? (s2, s3) then
		  NotUnify (srt1, srt2)
		else 
		  unify (env, s1, s3, pairs, ignoreSubtypes?)
	      | _ -> NotUnify (srt1, srt2)
	  else 
	    case (srt1, srt2) of
	      | (Subtype (s1, p1, _), Subtype (s2, p2, _)) ->
		if unifyTerm? env.internal (p1, p2) then 
		  unify (env, s1, s2, pairs, ignoreSubtypes?)
		else
		  NotUnify (srt1, srt2)
	      | (Base _, _) -> 
	        let  s3 = unfoldType (env, srt1) in
		if equalType? (s1, s3) then 
		  NotUnify (srt1, srt2)
		else 
		  unify (env, s3, s2, pairs, ignoreSubtypes?)
	      | (_, Base _) ->
		let s3 = unfoldType (env, srt2) in
		if equalType? (s2, s3) then
		  NotUnify (srt1, srt2)
		else 
		  unify (env, s1, s3, pairs, ignoreSubtypes?)
	      | _ -> NotUnify (srt1, srt2)

  op consistentTypes? : LocalEnv * MSType * MSType * Bool -> Bool
 def consistentTypes? (env, srt1, srt2, ignoreSubtypes?) =
   let free_mtvs = freeMetaTyVars (srt1) ++ freeMetaTyVars (srt2) in
   let val = (unifyTypes env ignoreSubtypes? srt1 srt2) in
   (clearMetaTyVarLinks free_mtvs;
    val)

 op clearMetaTyVarLinks(mtvs: MetaTyVars): () =
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
	   (case unlinkType srt of
	      | MetaTyVar (tv, _) -> (vars := Cons (tv, ! vars); srt)
	      | s -> mapType (fn x -> x, vr, fn x -> x) (withAnnS (s, pos)))
	 | _ -> srt
   in
   let _ = mapType (fn x -> x, vr, fn x -> x) srt in
   ! vars

 def occurs (mtv : MS.MetaTyVar, srt : MSType) : Bool = 
   let
      def occursOptRow (mtv, row) =
       case row of
	 | [] -> false
	 | (_, Some t) :: rRow -> occurs (mtv, t) || occursOptRow (mtv, rRow)
	 | (_, None)   :: rRow -> occursOptRow (mtv, rRow)
     def occursRow (mtv, row) =
       case row of
	 | [] -> false
	 | (_, t) :: rRow -> occurs (mtv, t) || occursRow (mtv, rRow)
   in
   case srt of
     | CoProduct (row,     _) -> occursOptRow (mtv, row)
     | Product   (row,     _) -> occursRow    (mtv, row)
     | Arrow     (t1, t2,  _) -> occurs (mtv, t1) || occurs (mtv, t2)
     %% sjw 3/404 It seems safe to ignore the predicates and it fixes bug 82
     | Quotient  (t, pred, _) -> occurs (mtv, t)  %or occursT (mtv, pred)
     | Subtype   (t, pred, _) -> occurs (mtv, t)  %or occursT (mtv, pred)
     | Base      (_, srts, _) -> exists? (fn s -> occurs (mtv, s)) srts
     | Boolean             _  -> false
     | TyVar               _  -> false 
     | MetaTyVar           _  -> (case unlinkType srt of
				    | MetaTyVar (mtv1, _) -> mtv = mtv1 
				    | t -> occurs (mtv, t))
     | And       (srts,    _) -> exists? (fn s -> occurs (mtv, s)) srts
     | Any                  _ -> false

 def occursT (mtv, pred) =
   case pred of
     | ApplyN     (ms,            _) -> exists? (fn M -> occursT (mtv, M)) ms
     | Record     (fields,        _) -> exists? (fn (_, M) -> occursT (mtv, M)) fields
     | Bind       (_, vars, body, _) -> exists? (fn (_, s) -> occurs (mtv, s)) vars || occursT (mtv, body)
     | The        ((_,s), body,   _) -> occurs (mtv, s) || occursT (mtv, body)
     | IfThenElse (M, N, P,       _) -> occursT (mtv, M) || occursT (mtv, N) || occursT (mtv, P)
     | Var        ((_, s),        _) -> occurs (mtv, s)
     | Fun        (_, s,          _) -> occurs (mtv, s)
     | Seq        (ms,            _) -> exists? (fn M -> occursT (mtv, M)) ms
     | Let        (decls, body,   _) -> occursT (mtv, body) || exists? (fn (p, M) -> occursT (mtv, M)) decls
     | LetRec     (decls, body,   _) -> occursT (mtv, body) || exists? (fn (p, M) -> occursT (mtv, M)) decls
     | Lambda     (rules,         _) -> exists? (fn (p, c, M) -> occursT (mtv, M)) rules
     | And        (tms,           _) -> exists? (fn t -> occursT (mtv, t)) tms
     | _  -> false

 op break(s: String): () = ()

 (* Apply substitution as variable linking *)
  op linkMetaTyVar : MS.MetaTyVar -> MSType -> ()
 def linkMetaTyVar (mtv : MS.MetaTyVar) tm = 
   let cell = ! mtv in
   (if debugUnify? then writeLine ("Linking "^cell.name^Nat.show cell.uniqueId^" with "^printType tm) else ();
    if embed? CoProduct tm then break("copr") else ();
    mtv := cell << {link = Some tm})

  op simpleTerm : MSTerm -> Bool
 def simpleTerm term = 
   case term of
     | Var _ -> true
     | Fun _ -> true
     | _ -> false

 %% Used by the Accord extension to typechecker that considers f(x) to be a 
 %% possible interpretation of x.f (if type of x is a subtype of domain of f)
 %% Don't do any unification, to avoid coercing undeclared x to bogus type.
  op Accord.subtypeOf? : LocalEnv -> MSType -> MSType -> Bool
 def Accord.subtypeOf? env x y =
   let spc = env.internal in
   let 
     def aux x =
       equalType? (x, y) ||
       (let x = unfoldType (env, x) in
        case x of
	  | Subtype (x, _, _) -> aux x 
	  | _ -> false)
   in
     aux x

endspec
