(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

% Synchronized with version 1.8 of  SW4/Languages/MetaSlang/TypeChecker/TypeCheckUtilities.sl 

Utilities qualifying spec
 %import SpecToPosSpec                                   % for PosSpec's, plus convertType[Info]ToPType[Info]
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
       passNum    : Nat,
       constrs    : StringMap (List (QualifiedId * MSType)),
       file       : String}
 
 op initialEnv     : (* SpecRef * *) Spec * String -> LocalEnv

 op addVariable    : LocalEnv * String * MSType -> LocalEnv
 op secondPass     : LocalEnv                   -> LocalEnv
 op setEnvTypes    : LocalEnv * TypeMap         -> LocalEnv
 op unfoldType     : LocalEnv * MSType          -> MSType
 op findVarOrOps   : LocalEnv * Id * Position   -> MSTerms

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

 op unlinkMetaTyVar (mtv : MS.MetaTyVar): MSType = 
   case ! mtv of
     | {link = Some (MetaTyVar (tw, _)), name, uniqueId} -> unlinkMetaTyVar tw
     | {link = Some (ty), name, uniqueId} -> ty
     | _ -> MetaTyVar(mtv, noPos)

 %% create a copy of srt, but replace type vars by meta type vars
  op metafyType : MSType -> MetaTypeScheme
 def metafyType srt0 =
   let (tvs0, srt) = unpackType srt0 in
   if empty? tvs0 then
     ([],srt)
   else
     let mtvar_position = Internal "metafyType" in
     let tv_map = map (fn tv -> (tv, freshMetaTyVar ("metafy", mtvar_position))) tvs0 in
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
     let mtvs = map (fn (_, (MetaTyVar (y, _))) -> y) tv_map in
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

 op initialEnv (spc, file) : LocalEnv = 
   % let MetaTyVar (tv,_)  = freshMetaTyVar ("initialEnv", Internal "ignored") in  % TODO: is this needed?
   % let spc = copySpec spc in                                                     % TODO: is this needed?
   {importMap  = StringMap.empty, % importMap,
    internal   = spc,
    errors     = Ref [],
    vars       = StringMap.empty,
    passNum    = 0,
    constrs    = StringMap.empty,
    file       = file
    } 

 def sameCPType? (s1 : MSType, s2 : MSType) : Bool =
   case (s1, s2) of
    | (CoProduct (row1, _), CoProduct (row2, _)) ->
      length row1 = length row2
      && forall? (fn (id1, cs1) ->
                    exists? (fn (id2, cs2) -> id1 = id2 && cs1 = cs2) row2)
             row1
    | _ -> false

 op addConstrsEnv (env: LocalEnv, sp: Spec): LocalEnv =
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
	   foldl (fn (constrMap, (Qualified(_,id),_)) -> addConstr (id, qid, dfn, constrMap)) 
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
	   else if file_1 ~= file_2 then   % Prefer errors in current file
             if file_1 = env.file then Less else Greater
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

 op firstPass?(env: LocalEnv): Bool = env.passNum = 1
 op secondPass?(env: LocalEnv): Bool = env.passNum = 2
 op finalPass?(env: LocalEnv): Bool = env.passNum = 3
 op notFinalPass?(env: LocalEnv): Bool = env.passNum ~= 3

 op secondPass(env: LocalEnv): LocalEnv =
   env << {passNum = 2}

 op finalPass(env: LocalEnv): LocalEnv =
   env << {passNum = 3}

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
   unfoldTypeRec (env, srt, false, SplaySet.empty compareQId)
   % withAnnS(unfoldTypeRec (env, srt, false, SplaySet.empty compareQId),
   %          typeAnn srt)

 op unfoldTypeCoProd (env: LocalEnv, srt: MSType): MSType = 
   unfoldTypeRec (env, srt, true, SplaySet.empty compareQId)
   % withAnnS(unfoldTypeRec (env, srt, true, SplaySet.empty compareQId),
   %          typeAnn srt)
   
 op unfoldTypeRec (env: LocalEnv, srt: MSType, coprod?: Bool, qids: SplaySet.Set TypeName) : MSType = 
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
                     % let _ = if debugUnify? then writeLine("dfn: "^printType dfn) else () in
                     if ~coprod? && coproduct?(dfn) then unlinked_type
		       else instantiateScheme (env, pos, ts, dfn)
		   | _ ->
		     %% A base type can be defined in terms of other base types.
   		     %% So we unfold recursively here.
		     let dfn = maybeAndType (base_defs, typeAnn info.dfn) in
		     unfoldTypeRec (env,
				    instantiateScheme (env, pos, ts, dfn),
                                    coprod?,
				    %% Watch for self-references, even via aliases: 
				    foldl (fn (qids,qid) -> SplaySet.add (qids, qid))
				          qids
					  info.names))
          | [] -> 
	    (error (env, "Could not find type "^ printQualifiedId qid, pos);
	     unlinked_type))
   %| Boolean is the same as default case
    | s -> s 

 op coproduct?(ty: MSType): Bool =
   case ty of
     | CoProduct _ -> true
     | Pi(_, s_ty, _) -> coproduct? s_ty
     | And(s_ty :: _, _) -> coproduct? s_ty
     | _ -> false

 op equalTypeIds?(env: LocalEnv, qid1 as Qualified(q1,id1): QualifiedId, qid2 as Qualified(q2,id2)): Bool =
   id1 = id2
     && (q1 = q2
           || (q1 = UnQualified && length(findAllTypes(env.internal, qid1)) = 1)
           || (q2 = UnQualified && length(findAllTypes(env.internal, qid2)) = 1))

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


 op instantiateScheme (env: LocalEnv, pos: Position, types: MSTypes, srt: MSType): MSType = 
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

 type SubtypeMode = | Ignore | Ignore1 | Ignore2 | DontIgnore

 op showSubtypeMode(m: SubtypeMode): String =
   case m of
     | Ignore -> "Ignore"
     | Ignore1 ->"Ignore1"
     | Ignore2 -> "Ignore2"
     | DontIgnore -> "DontIgnore"

  op unifyL : [a] LocalEnv * MSType * MSType * 
                  List a * List a * 
                  List (MSType * MSType) * SubtypeMode * Nat *
                  (LocalEnv * a * a *  List (MSType * MSType) * SubtypeMode * Nat -> Unification)
		  -> Unification
 def unifyL (env, srt1, srt2, l1, l2, pairs, subtype_mode, dom_count, unify) : Unification = 
   case (l1, l2) of
     | ([], []) -> Unify pairs
     | (e1 :: l1, e2 :: l2) -> 
       (case unify (env, e1, e2, pairs, subtype_mode, dom_count) of
	  | Unify pairs -> unifyL (env, srt1, srt2, l1, l2, pairs, subtype_mode, dom_count, unify)
	  | notUnify    -> notUnify)
     | _ -> NotUnify (srt1, srt2)

  op unifyTypes : LocalEnv -> SubtypeMode -> MSType -> MSType -> Bool
 def unifyTypes env subtype_mode s1 s2 =

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

   case unify (env, s1, s2, [], subtype_mode, 0) of
     | Unify     _       -> true
     | NotUnify (s1, s2) -> false

  op unifyCP : LocalEnv * MSType * MSType * 
               List (QualifiedId * Option MSType) * List (QualifiedId * Option MSType) * 
	       List (MSType * MSType) * SubtypeMode * Nat
	       -> Unification
 def unifyCP (env, srt1, srt2, r1, r2, pairs, subtype_mode, dom_count) = 
   unifyL (env,srt1, srt2, r1, r2, pairs, subtype_mode, dom_count,
	   fn (env, (id1, s1), (id2, s2), pairs, subtype_mode, dom_count) -> 
	   if id1 = id2 then
	     case (s1, s2) of
	       | (None,    None)    -> Unify pairs 
	       | (Some s1, Some s2) -> unify (env, s1, s2, pairs, subtype_mode, dom_count)
	       | _                  -> NotUnify (srt1, srt2)
	   else
	     NotUnify (srt1, srt2))

  op unifyP : LocalEnv * MSType * MSType * 
              List (Id * MSType) * List (Id * MSType) * 
              List (MSType * MSType) * SubtypeMode * Nat
	      -> Unification
 def unifyP (env, srt1, srt2, r1, r2, pairs, subtype_mode, dom_count) = 
     unifyL (env, srt1, srt2, r1, r2, pairs, subtype_mode, dom_count,
	     fn (env, (id1, s1), (id2, s2), pairs, subtype_mode, dom_count) -> 
	     if id1 = id2 then
	       unify (env, s1, s2, pairs, subtype_mode, dom_count)
	     else 
	       NotUnify (srt1, srt2))

 op debugUnify?: Bool = false

  op unify : LocalEnv * MSType * MSType * List (MSType * MSType) * SubtypeMode * Nat -> Unification
 def unify (env, s1, s2, pairs, subtype_mode, dom_count) = 
   let _ = if debugUnify? then writeLine("Unifying "^printType s1^" with "^printType s2) else () in
   let spc  = env.internal in
   let pos1 = typeAnn s1  in
   let pos2 = typeAnn s2  in
   let unlnk_srt1 = withAnnS (unlinkType s1, pos1) in % ? DerivedFrom pos1 ?
   let unlnk_srt2 = withAnnS (unlinkType s2, pos2) in % ? DerivedFrom pos2 ?
   let result =
       if equalType? (unlnk_srt1, unlnk_srt2) then 
         Unify pairs 
       else
         case (s1, s2) of
            | (MetaTyVar (mtv1, _), _) ->
              (case (! mtv1).link of
                 | Some srt1 -> % unify (env, srt1, s2, pairs, subtype_mode, dom_count)
                   maybeUpdateLink(unify (env, srt1, s2, pairs, subtype_mode, dom_count), s1, srt1, s2, dom_count, env)
                 | _ ->
               let s3 = unfoldType (env, unlnk_srt2) in  % s2 ?
               let s4 = unlinkType s3 in
               if equalType? (s4, s1) then
                 Unify pairs
               else if occurs (mtv1, s4) then
                 NotUnify (unlnk_srt1, unlnk_srt2)
               else 
                 (linkMetaTyVar mtv1 (withAnnS (s2, pos2)); 
                  Unify pairs))

            | (_, MetaTyVar (mtv2, _)) ->
              (case (! mtv2).link of
                 | Some srt2 -> unify(env, s1, srt2, pairs, subtype_mode, dom_count)
                   %maybeUpdateLink(unify (env, s1, srt2, pairs, subtype_mode, dom_count), s2, srt2, s1, env)
                 | _ ->
               let s4 = unfoldType (env, s1) in
               let s5 = unlinkType s4 in
               if equalType? (s5, s2) then
                 Unify pairs
               else if occurs (mtv2, s5) then
                 NotUnify (unlnk_srt1, unlnk_srt2)
               else
                 (linkMetaTyVar mtv2 (withAnnS (s1, pos1)); 
                  Unify pairs))

           | (And (srts1, _), _) ->
             foldl (fn (result,ss1) ->
                    case result of
                      | Unify _ -> result
                      | _ -> unify (env, ss1, s2, pairs, subtype_mode, dom_count))
                   (NotUnify (unlnk_srt1, unlnk_srt2))
                   srts1

           | (_, And (srts2, _)) ->
             foldl (fn (result,ss2) ->
                    case result of
                      | Unify _ -> result
                      | _ -> unify (env, s1, ss2, pairs, subtype_mode, dom_count))
                   (NotUnify (unlnk_srt1, unlnk_srt2))
                   srts2

           | (Product (r1, _), Product (r2, _)) -> 
             unifyP (env, s1, s2, r1, r2, pairs, subtype_mode, dom_count)

           | (Arrow (t1, t2, _), Arrow (s1, s2, _)) ->
             let _ = if debugUnify? then writeLine("dom_count: "^show dom_count) else () in
             (case unify (env, t1, s1, pairs, subtype_mode, dom_count + 1) of
                | Unify pairs -> unify (env, t2, s2, pairs, subtype_mode, 2  %if dom_count = 0 then 0 else dom_count + 1
                                        )
                | notUnify -> notUnify)

           | (Quotient (ty, trm, _), Quotient (ty2, trm2, _)) ->
             if equalTermStruct? (trm, trm2) then
               unify (env, ty, ty2, pairs, subtype_mode, dom_count)
             else 
               NotUnify (unlnk_srt1, unlnk_srt2)

               %                 if trm = trm_ then
               %                   unify (ty, ty2, pairs, subtype_mode, dom_count) 
               %                 else 
               %                   NotUnify (unlnk_srt1, unlnk_srt2)
               %               | (Subtype (ty, trm, _), Subtype (ty2, trm2, _)) -> 
               %                  if trm = trm_ then
               %                    unify (ty, ty_, pairs) 
               %                  else 
               %                    NotUnify (unlnk_srt1, unlnk_srt2)

            | (Boolean _, Boolean _) -> Unify pairs

            | (TyVar (id1, _), TyVar (id2, _)) -> 
              if id1 = id2 then
                Unify pairs
              else 
                NotUnify (unlnk_srt1, unlnk_srt2)

            | (CoProduct (r1, _), CoProduct (r2, _)) -> 
              unifyCP (env, s1, s2, r1, r2, pairs, subtype_mode, dom_count)

            | (Base (id1, ts1, pos1), Base (id2, ts2, pos2)) -> 
              if exists? (fn (p1, p2) -> 
                            %% p = (unlnk_srt1, unlnk_srt2) 
                            %% need predicate that chases metavar links
                            equalType? (p1, s1) &&
                            equalType? (p2, s2))
                        pairs 
                then
                  Unify pairs
              else if equalTypeIds?(env, id1, id2) then
                unifyL (env, s1, s2, ts1, ts2, pairs, subtype_mode, dom_count, unify)
              else
                if subtypeOf?(s1, id2, spc)
                  then let s1x = unfoldType (env, s1) in
                       let _ = if debugUnify? then writeLine("s1x: "^printType s1x^"  s2: "^printType s2) else () in
                       unify (env, withAnnS(s1x, pos1), s2, 
                              pairs, subtype_mode, dom_count)
                else if subtypeOf?(s2, id1, spc)
                  then let s2x = unfoldType (env, s2) in
                       let _ = if debugUnify? then writeLine("s1: "^printType s1^"  s2x: "^printType s2x) else () in
                       unify (env, s1, withAnnS(s2x, pos2), 
                              pairs, subtype_mode, dom_count)
                else
                let s1x = unfoldType (env, s1) in
                let s2x = unfoldType (env, s2) in
                let _ = if debugUnify? then writeLine("s1x: "^printType s1x^"  s2x: "^printType s2x) else () in
                if equalType? (s1, s1x) && equalType? (s2x, s2) then
                  NotUnify  (unlnk_srt1, unlnk_srt2)
                else
                  unify (env,
                         withAnnS(s1x, pos1), 
                         withAnnS(s2x, pos2), 
                         (s1, s2) :: pairs, 
                         subtype_mode, dom_count)

            % TODO: alpha equivalence...
            % | (Pi _, Pi _) -> alpha equivalence directly
            % or convert callers of unify to convert TyVars to MetaTyVars??

            | (Pi _, _) ->
              % TODO: or perhaps alpha equivalence by converting vars to meta-ty-vars here...
              unify (env, typeInnerType s1, s2, pairs, subtype_mode, dom_count)

            | (_, Pi _) ->
              unify (env, s1, typeInnerType s2, pairs, subtype_mode, dom_count)

            | (Any _, _) -> Unify pairs
            | (_, Any _) -> Unify pairs

            | _ ->
          case (s1, s2) of
            | (Subtype (ss1, p1, _), Subtype (ss2, p2, _)) ->
              let _ = if debugUnify?
                       then writeLine("unifyTerm?: "^printTermWithTypes p1
                                        ^(if equalTerm? (p1, p2) then " = " else " ~= ")
                                        ^printTermWithTypes p2)
                       else () in
              if subtype_mode = Ignore || unifyTerm? env.internal (p1, p2) then 
                unify (env, ss1, ss2, pairs, subtype_mode, dom_count)
              else
                (case subtype_mode of
                   | Ignore1 -> unify (env, ss1, s2, pairs, subtype_mode, dom_count)
                   | Ignore2 -> unify (env, s1, ss2, pairs, subtype_mode, dom_count)
                   | DontIgnore -> NotUnify (unlnk_srt1, unlnk_srt2))
            | (Subtype (ss1, p1, _), _) | subtype_mode = Ignore || subtype_mode = Ignore1 ->
              unify (env, ss1, s2, pairs, subtype_mode, dom_count)
            | (_, Subtype (ss2, p2, _)) | subtype_mode = Ignore || subtype_mode = Ignore2 ->
              unify (env, s1, ss2, pairs, subtype_mode, dom_count)
            | (Base _, _) -> 
              let s1x = unfoldType (env, s1) in
              if equalType? (s1, s1x) then
                NotUnify (unlnk_srt1, unlnk_srt2)
              else 
                unify (env, s1x, s2, pairs, subtype_mode, dom_count)
            | (_, Base _) ->
              let s2x = unfoldType (env, s2) in
              if equalType? (s2, s2x) then
                NotUnify (unlnk_srt1, unlnk_srt2)
              else 
                unify (env, s1, s2x, pairs, subtype_mode, dom_count)
            | _ -> NotUnify (unlnk_srt1, unlnk_srt2)
  in
  let _ = if debugUnify? then writeLine(if embed? Unify result then "Succeeded!"
                                        else printType unlnk_srt1^" <~> "^printType unlnk_srt2)
           else () in
  result

(*
 op subtypeOfEnv?(ty1: MSType, ty2: MSType, env: LocalEnv): Bool =
   if equalType?(ty1, ty2) then true
   else
   % let _ = if debugUnify? then writeLine(printType ty1^" <= "^printType ty2) else () in
   case ty1 of
     | Subtype(sty1, _, _) -> subtypeOfEnv?(sty1, ty2, env)
     | Base _ -> let ty1x = unfoldType(env, ty1) in
                 if equalType?(ty1x, ty1) then false
                   else subtypeOfEnv?(ty1x, ty2, env)
     | MetaTyVar(mtv1, _) ->
       (case (! mtv1).link of
          | Some ty1l -> subtypeOfEnv?(ty1l, ty2, env)
          | _ -> false)
     | _ -> false
*)

 op tyVarInstantiationNames: List String = ["metafy", "parser-poly", "gen"]

 op fromTyVar?(ty: MSType): Bool =
   case ty of
     | MetaTyVar(mtv, _) -> (!mtv).name in? tyVarInstantiationNames
     | _ -> false

 op maybeUpdateLink(result: Unification, mtv_ty: MSType, old_ty: MSType, new_ty: MSType, dom_count: Nat, env: LocalEnv): Unification =
   if embed? NotUnify result
       || (%let _ = if debugUnify? then writeLine(show dom_count^" "^printType old_ty^" <?= "^printType new_ty) else () in
           dom_count ~= 1)
       || equalType?(new_ty, old_ty)
       || ~(fromTyVar? mtv_ty)
       %|| ~(subtypeOf? env old_ty (unlinkType new_ty))
     then result
   else
   %% commonSuperType assumes types are well-formed, so we need to avoid calling it if checkTypes generates an error
   let old_errs = !env.errors in
   let _ = (unfoldType(env, old_ty); unfoldType(env, unlinkType new_ty)) in
   let gen_ty = if old_errs = !env.errors then commonSuperType(old_ty, unlinkType new_ty, env.internal) else old_ty in
   let _ = if debugUnify? then writeLine("Common supertype of "^printType old_ty^" and "^printType new_ty^": "^printType gen_ty) else () in
   if equalType?(gen_ty, old_ty) then result
   else
   let _ = if debugUnify? then writeLine("Relinking!"^" "^show dom_count) else () in
   case mtv_ty of
   | MetaTyVar (mtv, pos) -> 
     (linkMetaTyVar mtv (withAnnS(gen_ty, pos));
      result)
   | _ -> result 

  op consistentTypes? : LocalEnv * MSType * MSType * SubtypeMode -> Bool
 def consistentTypes? (env, srt1, srt2, subtype_mode) =
   let free_mtvs = freeMetaTyVars (srt1) ++ freeMetaTyVars (srt2) in
   let val = (unifyTypes env subtype_mode srt1 srt2) in
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
   (if debugUnify? then writeLine ("Linking "^cell.name^"%"^Nat.show cell.uniqueId^" with "^printType tm) else ();
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
   let _ = if debugUnify? then writeLine(printType x^" <?= "^printType y) else () in
   let 
     def aux x =
       let _ = if debugUnify? then writeLine(printType x) else () in
       equalType? (x, y) ||
       (let uf_x = unfoldType (env, x) in
        case uf_x of
	  | Subtype (sx, _, _) -> aux sx
          | MetaTyVar(mtv1, _) ->
            (case (! mtv1).link of
               | Some ty1l -> subtypeOf? env ty1l y
               | _ -> false)
	  | _ -> if equalType?(uf_x, x) then false else aux uf_x)
   in
     let result = aux x in
     let _ = if debugUnify? then writeLine(show result) else () in
     result

 op  unfoldBaseOne : Spec * MSType -> MSType 
 def unfoldBaseOne (sp, srt) = 
  case srt of
    | Base (qid, srts, a) ->
      (case findTheType (sp, qid) of
	 | None -> srt
	 | Some info ->
	   if definedTypeInfo? info then
	     let (tvs, srt1) = unpackFirstTypeDef info in
             let _ = if length tvs ~= length srts
                       then (writeLine("Zip error: "^show(length tvs)^" ~= "^show(length srts));
                             writeLine(printType srt);
                             writeLine(printType srt1^"  "^printTyVars tvs);
                             writeLine(print a))
                       else ()
             in
	     let ssrt = substType (zip (tvs, srts), srt1) in
	     ssrt
	   else
	     srt)
    | _ -> srt

  op tryUnfoldBase (spc: Spec) (ty: MSType): Option MSType =
    let exp_ty = unfoldBaseOne(spc, ty) in
    if embed? CoProduct exp_ty || embed? Quotient exp_ty || equalType?(exp_ty, ty)
      then None
      else Some exp_ty

 op substType : [a] List (Id * AType a) * AType a -> AType a
 def substType (S, srt) =
  let def find (name, S, a) =  
       case S 
         of []            -> TyVar(name,a)
          | (id, srt) ::S -> if name = id then srt else find (name, S, a) 
  in 
  let def subst1 srt =  
       case srt of
          | TyVar (name, a) -> find (name, S, a)
          | _ -> srt
  in 
  mapType (id, subst1, id) srt
 
  op  subtypeOf?: MSType * QualifiedId * Spec -> Bool
  def subtypeOf? (ty,qid,spc) =
    % let _ = toScreen(printQualifiedId qid^" <:? "^printType ty^"\n") in
    let result =
    case unlinkType ty of
      | Base(qid1,srts,_) ->
        qid1 = qid
	 || (case findTheType (spc, qid1) of
	      | None -> false
	      | Some info ->
		if definedTypeInfo? info then
		  let (tvs, srt) = unpackFirstTypeDef info in
                  if length tvs = length srts then
                    let ssrt = substType (zip (tvs, srts), srt) in
                    subtypeOf?(ssrt,qid,spc)
                  else
                    false
		else
		  false)
      | Subtype(t1,_,_) -> subtypeOf?(t1,qid,spc)
      | _ -> false
    in
    % let _ = writeLine("= "^ (if result then "true" else "false")) in
    result

   op commonSuperType(ty1: MSType, ty2: MSType, spc: Spec): MSType =
     %% Experimental version
     let def cst(rty1, rty2, ty1, ty2) =
       if equalType?(rty1, rty2) then ty1
       else
       case (rty1, rty2) of  %raiseSubtypes(rty1, rty2, spc) of
         | (rrty1, rrty2) ->
       % let _ = writeLine("cst: "^printType rrty1^"\n"^printType rrty2) in
       case (rrty1, rrty2) of
         | (Subtype(sty1, p1, _), Subtype(sty2, p2, _)) ->
           if equalTermAlpha?(p1, p2) then ty1
             else cst(sty1, sty2, sty1, sty2)
         | (Subtype(sty1, p1, _), rty2) -> cst(sty1, rty2, sty1, ty2)
         | (rty1, Subtype(sty2, p2, _)) -> cst(rty1, sty2, ty1, sty2)
         | (Arrow(d1, r1, a), Arrow(d2, r2, _)) ->
           Arrow(cst(d1, d2, d1, d2), cst(r1, r2, r1, r2), a)
         | (Base(qid1, args1, a), Base(qid2, args2, _)) | qid1 = qid2 ->
           let comm_args = map (fn (tya1, tya2) -> cst(tya1, tya2, tya1, tya2)) (zip(args1, args2)) in
           Base(qid1, comm_args, a)
         | (Base(qid1, _, a), ty2) | subtypeOf?(ty2, qid1, spc) -> ty1
         | (ty1, Base(qid2, _, a)) | subtypeOf?(ty1, qid2, spc) -> ty2
         | (Base(Qualified(_,id),_,_), _) ->
           (case tryUnfoldBase spc rrty1 of
            | Some uf_ty1 -> cst(uf_ty1, rrty2, ty1, ty2)
            | None -> rrty1)
         | (_, Base(Qualified(_,id),_,_)) ->
           (case tryUnfoldBase spc rrty2 of
            | Some uf_ty2 -> cst(rrty1, uf_ty2, ty1, ty2)
            | None -> rrty2)
         | (Product(flds1, a), Product(flds2, _)) ->
           if length flds1 ~= length flds2 then ty1 % Shouldn't happen
             else let new_flds = map (fn ((id, t1), (_, t2)) -> (id, cst(t1, t2, t1, t2)))
                                   (zip(flds1, flds2))
                  in
                  Product(new_flds, a)
         | _ -> ty1
     in
     let result = cst(ty1, ty2, ty1, ty2) in
     % let _ = writeLine("cst: "^printType ty1^" <?> "^printType ty2^"\n"^printType result) in
     result

op leastGeneral(t1: MSType, t2: MSType): MSType =
  let def generalize(t1: MSType, t2: MSType, unifieds: List(MSType * MSType * MSType)) =
        let _ = if debugUnify? then writeLine("gen: "^printType t1^" and "^printType t2) else () in
        if equalType?(t1, t2) then (t1, unifieds)
        else
        case (t1, t2) of
          | (Arrow(x1, y1,  a), Arrow(x2, y2,  _)) ->
            let (x, unifieds) = generalize (x1, x2, unifieds) in
            let (y, unifieds) = generalize (y1, y2, unifieds) in
            (Arrow(x, y,  a), unifieds)
          | (Product(xs1, a), Product(xs2, _)) ->
            let (xs, unifieds) = foldr (fn (((l1, x1), (l2, x2)), (xs, unifieds)) ->
                                          if l1 = l2
                                            then let (x, unifieds) = generalize (x1, x2, unifieds) in
                                                 ((l1,x)::xs, unifieds)
                                            else ([], []))
                                   ([], unifieds) (zip(xs1, xs2))
            in
            (Product(xs, a), unifieds)
          | (CoProduct (xs1, a), CoProduct (xs2, _)) ->
            let (xs, unifieds) = foldr (fn (((l1, ox1), (l2, ox2)), (xs, unifieds)) ->
                                          if l1 = l2
                                            then let (ox, unifieds) =
                                                     case (ox1, ox2) of
                                                       | (Some x1, Some x2) ->
                                                         let (x, unifieds) = generalize (x1, x2, unifieds) in
                                                         (Some x, unifieds)
                                                       | _ -> (None, unifieds)
                                                 in
                                                 ((l1,ox)::xs, unifieds)
                                            else ([], []))
                                   ([], unifieds) (zip(xs1, xs2))
            in
            (CoProduct(xs, a), unifieds)
          | (Quotient(x1, t1, a), Quotient  (x2, t2, _)) | equalTermAlpha? (t1, t2) ->
            let (x, unifieds) = generalize (x1, x2, unifieds) in
            (Quotient(x, t1, a), unifieds)
          | (Subtype(x1, Lambda([(VarPat((v1, v_ty1), a1), c, bod)], _), a), Subtype(x2, Lambda([(VarPat((v2, v_ty2), _), _, _)], _), _)) | v1 = v2 ->
            let (x, unifieds) = generalize (x1, x2, unifieds) in
            let (v_ty, unifieds) = generalize (v_ty1, v_ty2, unifieds) in
            (Subtype(x, Lambda([(VarPat((v1, v_ty1), a1), c, bod)], a), a), unifieds)
          | (Subtype(x1, t1, a), Subtype(x2, t2, _)) -> %| equalTerm? (t1, t2) ->
            let (x, unifieds) = generalize (x1, x2, unifieds) in
            (Subtype(x, t1, a), unifieds)
          | (Base(q1, xs1, a), Base(q2, xs2, _)) | q1 = q2 ->
            let (xs, unifieds) = foldr (fn ((x1, x2), (xs, unifieds)) ->
                                          let  (x, unifieds) = generalize (x1, x2, unifieds) in
                                          (x::xs, unifieds))
                                   ([], unifieds) (zip(xs1, xs2))
            in
            (Base(q1, xs, a), unifieds)
          | (Boolean _, Boolean _) -> (t1, unifieds)
          | (TyVar(v1, _), TyVar(v2, _)) | v1 = v2 -> (t1, unifieds)
          | (MetaTyVar (mtv1, _), _) | some?((! mtv1).link) ->
            let ({link=Some ls1, uniqueId=id1, name}) = ! mtv1 in
            generalize (ls1, t2, unifieds)
          | ( _, MetaTyVar (mtv2, _)) | some?((! mtv2).link)  ->
            let ({link=Some ls2, uniqueId=id2, name}) = ! mtv2 in
            generalize (t1, ls2, unifieds)
          | (Pi(tvs1, s1, a), Pi(tvs2, s2, _)) | tvs1 = tvs2 ->
            let (s, unifieds) = generalize (s1, s2, unifieds) in
            (Pi(tvs1, s, a), unifieds)
          | _ ->
            let _ = if debugUnify? then writeLine("differ") else () in
            case findLeftmost(fn (s1, s2, _) -> equalType?(t1, s1) && equalType?(t2, s2)) unifieds of
              | Some(_, _, mtv) -> (mtv, unifieds)
              | None  ->
                let mtv = freshMetaTyVar("gen", typeAnn t1) in
                (mtv, (t1, t2, mtv) :: unifieds)
  in
  let (generalized_ty, unifieds) = generalize(t1, t2, []) in
  generalized_ty

end-spec
