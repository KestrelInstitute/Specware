% Synchronized with version 1.8 of  SW4/Languages/MetaSlang/TypeChecker/TypeCheckUtilities.sl 

Utilities qualifying
spec
 import /Library/Base
 import SpecToPosSpec   % for PosSpec's, plus convertSort[Info]ToPSort[Info]
 import ../Printer        % for error messages
 import /Library/Legacy/DataStructures/MergeSort % for combining error messages
 import /Library/Legacy/DataStructures/ListPair  % misc utility

 sort Environment = StringMap Spec
 sort LocalEnv = 
      {importMap  : Environment,
       internal   : Spec,
       errors     : Ref(List (String * Position)),
       vars       : StringMap MS.Sort,
       firstPass? : Boolean,
       constrs    : StringMap (List SortScheme),
       file       : String}
 
 op initialEnv     : (* SpecRef * *) Spec * String -> LocalEnv
 op addConstrsEnv  : LocalEnv * Spec -> LocalEnv

 op addVariable    : LocalEnv * String * Sort -> LocalEnv
 op secondPass     : LocalEnv                 -> LocalEnv
 op setEnvSorts    : LocalEnv * SortMap       -> LocalEnv
 op unfoldSort     : LocalEnv * Sort          -> Sort
 op findVarOrOps   : LocalEnv * Id * Position -> List MS.Term

 op error          : LocalEnv * String * Position -> ()

 (* Auxiliary functions: *)

 % Generate a fresh type variable at a given position.
 op freshMetaTyVar : Position -> MS.Sort
 def counter = (Ref 0) : Ref Nat
 def freshMetaTyVar pos = 
   (counter := 1 + (! counter);
    MetaTyVar (Ref {link = None,uniqueId = ! counter,name = "#fresh"}, pos))
 def initializeMetaTyVar() = counter := 0

 op copySort : SortScheme -> MetaSortScheme

 op  unlinkSort : MS.Sort -> MS.Sort
 %% sjw: Dereferences the link recursively
 def unlinkSort srt = 
  case srt of
   | MetaTyVar (tv, _) -> 
     (case ! tv of
       | {link = Some srt, name, uniqueId} -> unlinkSort srt
       | _ -> srt)
   | _ -> srt 

 %% sjw: unused?
 def unlinkMetaTyVar (tv : MS.MetaTyVar) = 
   case ! tv
     of {link = Some (MetaTyVar (tw, _)), name, uniqueId} -> unlinkMetaTyVar tw
      | _ -> tv

 def copySort (tyVars, srt) = 
   if null tyVars then
     ([],srt)
   else
     let mtvar_position = Internal "copySort" in
     let tyVarMap = List.map (fn tv -> (tv, freshMetaTyVar mtvar_position)) tyVars in
     let
        def mapTyVar (tv, tvs, pos) : MS.Sort = 
            case tvs
              of [] -> TyVar(tv,pos)
               | (tv1,s)::tvs -> 
                 if tv = tv1 then s else mapTyVar (tv, tvs, pos)
     in
     let
        def cp (srt : MS.Sort) = 
            case srt
              of TyVar (tv, pos) -> mapTyVar (tv, tyVarMap, pos)
               | srt -> srt
     in
     let srt = mapSort (id, cp, id) srt in
     let metaTyVars = List.map (fn(_, (MetaTyVar (y,_))) -> y) tyVarMap in
     (metaTyVars,srt)


  op initPrimitiveSpec : Qualifier -> Id -> List String -> Spec
  def initPrimitiveSpec qualifier id tyvars =
    %% we expect the qualifier to be the same as id, e.g. Boolean.Boolean
    {importInfo       = emptyImportInfo,
     sorts            = insertAQualifierMap (emptyAQualifierMap, qualifier, id,
					     ([Qualified (qualifier, id)], tyvars, [])),
     ops              = emptyAQualifierMap,
     properties       = emptyProperties
    } 

  def stringSpec  = initPrimitiveSpec "String"  "String"  []
  def charSpec    = initPrimitiveSpec "Char"    "Char"    []
  def boolSpec    = initPrimitiveSpec "Boolean" "Boolean" []
  def listSpec    = initPrimitiveSpec "List"    "List"    ["a"]
  def generalSpec = initPrimitiveSpec "General" "General" ["a"]
  def natSpec     = initPrimitiveSpec "Nat"     "Nat"     []
  def intSpec     = initPrimitiveSpec "Integer" "Integer" []

 %
 % Boot strapping environment
 %        
 def baseSpec : Spec = 
     {importInfo       = emptyImportInfo,
      sorts            = emptyAQualifierMap,
      ops              = emptyAQualifierMap,
      properties       = emptyProperties
     }

 def initialEnv (spc, file) = 
   let errs : List (String * Position) = [] in
   let {importInfo, sorts, ops, properties} = spc in
   let MetaTyVar(tv,_)  = freshMetaTyVar (Internal "ignored") in
   %% importedSpecs is the subset of external used
   %% let importMap = importedSpecs in
   let spc = {importInfo   = importInfo,
	      sorts        = sorts,
	      ops          = ops,
	      properties   = properties
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

 def sameCPSort? (s1: MS.Sort, s2: MS.Sort): Boolean =
   case (s1,s2) of
    | (CoProduct(row1,_), CoProduct(row2,_)) ->
      length row1 = length row2
      & all (fn (id1,cs1) ->
             exists (fn (id2,cs2) -> id1 = id2 & cs1 = cs2) row2)
            row1
   | _ -> false

 def addConstrsEnv({importMap, internal, vars, errors, firstPass?,
                    constrs, file},
                   sp) =
   {importMap  = importMap,
    internal   = sp,
    vars       = vars,
    errors     = errors,
    firstPass? = firstPass?,
    constrs    = computeConstrMap(sp), % importMap
    file       = file}

 %% Computes a map from constructor names to set of sorts for them
 def computeConstrMap (spc) : StringMap (List SortScheme) =
  let sorts = spc.sorts in
   let constrMap : Ref (StringMap (List SortScheme)) = Ref StringMap.empty 
   in
   let def addConstr (id, tvs, cp_srt, constrMap) =
         let cMap = ! constrMap in
	 case StringMap.find (cMap, id)
	   of None -> constrMap := StringMap.insert(cMap, id, [(tvs,cp_srt)])
	    | Some srt_prs ->
	      if exists (fn(_,o_srt) -> sameCPSort?(o_srt, cp_srt)) srt_prs
	       then ()
	       else constrMap := StringMap.insert(cMap, id,
						  cons((tvs,cp_srt),srt_prs))
   in
   let def addSort (tvs, srt, constrMap) =
        case srt : MS.Sort of
	 | CoProduct (row, _) ->
	   app (fn (id,_) -> addConstr (id, tvs, srt, constrMap)) row
	 %% | Base (Qualified (qid, id), _, _) ->
	 %%   (let matching_entries : List(String * QualifiedId * SortInfo) = 
         %%           lookupSortInImports(importMap, qid, id)
         %%       in
	 %%       case matching_entries
         %%  of [(_, _, (_, e_tvs, Some e_srt))] ->
         %%     addSort(e_tvs, convertSortToPSort e_srt)
         %%   | _ -> ())
	 | _ -> ()
   in
   let _ = appAQualifierMap 
	     (fn (sort_names, tyvars, defs) -> 
	      app (fn (type_vars, srt) ->
		   addSort (type_vars, srt, constrMap))
	          defs)
	     sorts
   %% in
   %% Look at at all sorts mentioned in spec
   %% Doesn't work unless we recognize which ones are instances of ones we already have
   %% let _ = appSpec (fn x -> (), fn s -> addSort([],s,sorts, constrMap), fn p -> ()) spc
   in ! constrMap

 op  checkErrors : LocalEnv -> List(String * Position)

 def checkErrors(env:LocalEnv) = 
   let errors = env.errors in
   let def compare ((msg_1, pos_1), (msg_2, pos_2)) =
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

      
  def error(env as {errors,importMap,internal, (* specName, *) vars,
                    firstPass?,constrs,file},
            msg,
            pos) 
    = 
    errors := cons((msg,pos),! errors)


  def addVariable({importMap,internal,vars,errors,
                   firstPass?,constrs,file},
                  id,
                  srt) = 
    {importMap  = importMap,
     internal   = internal,
     vars       = StringMap.insert(vars,id,srt),
     errors     = errors,
     firstPass? = firstPass?,
     constrs    = constrs,
     file       = file
    }
        
  def secondPass({importMap,internal,vars, errors,
                  firstPass?=_,constrs,file}) = 
    {importMap  = importMap,
     internal   = internal,
     vars       = vars,
     errors     = errors,
     firstPass? = false,
     constrs    = constrs,
     file       = file
    }

  def setEnvSorts ({importMap,internal,vars,errors,
		    firstPass?,constrs,file},
		   newSorts) =
    {importMap  = importMap,
     internal   = setSorts(internal,newSorts),
     vars       = vars,
     errors     = errors,
     firstPass? = firstPass?,
     constrs    = constrs,
     file       = file
    }

 (* Unlink and unfold recursive sort declarations *)

 def compareQId (Qualified (q1, id1), Qualified (q2, id2)): Comparison = 
  case String.compare (q1, q2) of
   | Equal  -> String.compare (id1, id2)
   | result -> result

 %% sjw: Replace base srt by its instantiated definition
 def unfoldSort (env,srt) = unfoldSortRec(env, srt, SplaySet.empty compareQId)

 def unfoldSortRec (env, srt, qids) : MS.Sort = 
   let unlinked_sort = unlinkSort srt in
   case unlinked_sort of
    | Base (qid, ts, pos) -> 
      if SplaySet.member (qids, qid) then
         (error(env,
                "The sort "^(printQualifiedId qid)^" is recursively defined using itself",
                pos);
          unlinked_sort)
      else
        (case findAllSorts (env.internal, qid) of
          | sort_info::r ->
            (case sort_info of
              | (main_qid::_, tvs, []) ->        % sjw: primitive sort
                let l1 = length tvs in
                let l2 = length ts  in
                ((if ~(l1 = l2) then
                    error(env,
			  "\n  [A] Instantiation list (" ^ 
			  (foldl (fn (arg, s) -> s ^ " " ^ (anyToString arg)) "" ts) ^
			  " ) does not match argument list (" ^ 
			  (foldl (fn (tv, s) -> s ^ " " ^ (anyToString tv)) "" tvs) ^
			  " )",
                          pos)
                  else 
                    ());
                 %% Use the primary name, even if the reference was via some alias.
                 %% This normalizes all references to be via the same name.
                 Base (main_qid, ts, pos))
              | (aliases, tvs, defs) ->
		let possible_base_def = find (fn srt_def ->
					      case srt_def of
						| (_, Base _) -> true
						| _           -> false)
		                             defs
		in
		case possible_base_def of
		  | Some (type_vars, srt as (Base (_,_,pos))) ->
		    %% A base sort can be defined in terms of another base sort.
   		    %% So we unfold recursively here.
		    unfoldSortRec(env,
				   instantiateScheme (env, pos, ts, type_vars, srt),
				   %% Watch for self-references, even via aliases: 
				   foldl (fn (qid, qids) -> SplaySet.add (qids, qid))
				         qids
					 aliases)
		  | _ ->
		    let (some_type_vars, some_def) = hd defs in % if multiple defs, pick first def arbitrarily
		    instantiateScheme(env, pos, ts, some_type_vars, some_def))
          | [] -> 
               (error (env, "Could not find definition of sort "^ printQualifiedId qid, pos);
                unlinked_sort))
    | s -> s 

 %% sjw: Returns srt with all  sort variables dereferenced
 def unlinkRec(srt) = 
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

 def findVarOrOps ({errors, importMap, internal, vars, (* specName, *) firstPass?, constrs, file}: LocalEnv,
                   id,
                   a)
  =
  let 
     def mkTerm (a, (qids, fixity, (tyvars,srt), _)) = 
      let (_,srt) = copySort(tyvars,srt) in
      case qids of
       | (Qualified (qualifier, id))::misc ->
         Fun (%% Allow (UnQualified, x) through as TwoNames term ...
              %% if qualifier = UnQualified
              %%  then OneName  (           id, fixity) 
              %% else 
              TwoNames (qualifier, id, fixity),
              srt, 
              a)
    def mkTerms infos =
      List.map (fn info -> mkTerm  (a, info)) infos
  in
  case StringMap.find (vars, id) of
   | Some srt -> [Var((id, srt), a)]
   | None     -> mkTerms (wildFindUnQualified (internal.ops, id))


 def instantiateScheme (env, pos, types, type_vars, srt) = 
   if ~(length types = length type_vars) then
     (error (env, 
	     "\n  [B] Instantiation list (" ^ 
	     (foldl (fn (arg, s) -> s ^ " " ^ (anyToString arg)) "" types) ^
	     " ) does not match argument list (" ^ 
	     (foldl (fn (tv, s) -> s ^ " " ^ (anyToString tv)) "" type_vars) ^
	     " )",
	     pos);
      srt)
   else
     let (new_type_vars, new_srt) = copySort (type_vars, srt) in
     (ListPair.app (fn (typ, new_type_var) -> 
                    let {uniqueId,name,link} = ! new_type_var in
                    new_type_var := {link     = Some typ,
                                     uniqueId = uniqueId,
                                     name     = name})
                   (types, new_type_vars);
      new_srt)


 sort Unification = | NotUnify  MS.Sort * MS.Sort 
                    | Unify List(MS.Sort * MS.Sort)

 op  unifyL : fa(a) LocalEnv * MS.Sort * MS.Sort * List(a) * List(a) * List(MS.Sort * MS.Sort)
                     * Boolean * (LocalEnv * a * a *  List(MS.Sort * MS.Sort) * Boolean -> Unification) 
	      -> Unification
 def unifyL(env,srt1,srt2,l1,l2,pairs,ignoreSubsorts?,unify):Unification = 
   case (l1,l2)
     of ([],[]) -> Unify pairs
      | (e1::l1,e2::l2) -> 
	(case unify(env,e1,e2,pairs,ignoreSubsorts?) of
	    | Unify pairs -> unifyL(env,srt1,srt2,l1,l2,pairs,ignoreSubsorts?,unify)
	    | notUnify    -> notUnify)
      | _ -> NotUnify(srt1,srt2)

 op  unifySorts: LocalEnv -> Boolean -> Sort -> Sort -> Boolean * String
 def unifySorts env ignoreSubsorts? s1 s2 =

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

   %%    let _ = String.writeLine "Unifying"     in
   %%    let _ = System.print s1 in
   %%    let _ = System.print s2 in
   %%    let _ = String.writeLine (printSort s1) in
   %%    let _ = String.writeLine (printSort s2) in

     case unify(env,s1,s2,[],ignoreSubsorts?)
       of Unify _ -> (true,"")
        | NotUnify(s1,s2) -> (false,printSort s1^" ! = "^printSort s2)

 op  unifyCP: LocalEnv * Sort * Sort * List(Id * Option Sort) * List(Id * Option Sort)
                * List(Sort * Sort) * Boolean
               -> Unification
 def unifyCP (env,srt1,srt2,r1,r2,pairs,ignoreSubsorts?) = 
     unifyL (env,srt1, srt2, r1, r2, pairs,ignoreSubsorts?,
	     fn (env,(id1,s1),(id2,s2),pairs,ignoreSubsorts?) -> 
	       if id1 = id2 then
		 (case (s1,s2) of
		     | (None,None) -> Unify pairs 
		     | (Some s1,Some s2) -> unify (env,s1,s2,pairs,ignoreSubsorts?)
		     | _ -> NotUnify (srt1,srt2))
	       else
		 NotUnify(srt1,srt2))

 op  unifyP: LocalEnv * Sort * Sort * List(Id * Sort) * List(Id * Sort) * List(Sort * Sort) * Boolean
               -> Unification
 def unifyP (env,srt1,srt2,r1,r2,pairs,ignoreSubsorts?) = 
     unifyL (env,srt1,srt2,r1,r2,pairs,ignoreSubsorts?,
	     fn(env,(id1,s1),(id2,s2),pairs,ignoreSubsorts?) -> 
	       if id1 = id2 
	       then unify(env,s1,s2,pairs,ignoreSubsorts?)
	       else NotUnify(srt1,srt2))

 op  unify: LocalEnv * Sort * Sort * List(Sort * Sort) * Boolean -> Unification
 def unify (env,s1,s2,pairs,ignoreSubsorts?) = 
   let pos1 = sortAnn s1  in
   let pos2 = sortAnn s2  in
   let srt1 = withAnnS (unlinkSort s1, pos1) in % ? DerivedFrom pos1 ?
   let srt2 = withAnnS (unlinkSort s2, pos2) in % ? DerivedFrom pos2 ?
   if equalSort?(srt1,srt2) then 
     Unify pairs 
   else
     case (srt1,srt2) of
	| (CoProduct(r1,_),CoProduct(r2,_)) -> 
	  unifyCP(env,srt1,srt2,r1,r2,pairs,ignoreSubsorts?)
	| (Product(r1,_),Product(r2,_)) -> 
	  unifyP(env,srt1,srt2,r1,r2,pairs,ignoreSubsorts?)
	| (Arrow(t1,t2,_),Arrow(s1,s2,_)) -> 
	  (case unify(env,t1,s1,pairs,ignoreSubsorts?)
	     of Unify pairs -> unify(env,t2,s2,pairs,ignoreSubsorts?)
	      | notUnify -> notUnify)
	| (Quotient(ty,trm,_),Quotient(ty_,trm_,_)) ->
	     if equalTermStruct?(trm,trm_)
	       then unify(env,ty,ty_,pairs,ignoreSubsorts?)
	       else NotUnify(srt1,srt2)
	     %                 if trm = trm_ 
	     %                     then unify(ty,ty_,pairs,ignoreSubsorts?) 
	     %                    else NotUnify(srt1,srt2)
	     %               | (Subsort(ty,trm,_),Subsort(ty_,trm_,_)) -> 
	     %                  if trm = trm_ 
	     %                      then unify(ty,ty_,pairs) 
	     %                  else NotUnify(srt1,srt2)
	| (Base(id,ts,pos1),Base(id_,ts_,pos2)) -> 
	     if exists (fn (p1,p2) -> 
			%% p = (srt1,srt2) 
			%% need predicate that chases metavar links
			equalSort?(p1, srt1) &
			equalSort?(p2, srt2))
			pairs 
	     then
	       Unify pairs
	     else 
	       if id = id_ then
		 unifyL(env,srt1,srt2,ts,ts_,pairs,ignoreSubsorts?,unify)
	       else 
		 let s1_ = unfoldSort(env,srt1) in
		 let s2_ = unfoldSort(env,srt2) in
		 if equalSort?(s1,s1_) & equalSort?(s2_,s2) then
		   NotUnify (srt1,srt2)
		 else 
		   unify(env,withAnnS(s1_,pos1),
			 withAnnS(s2_,pos2),
			 cons((s1,s2), pairs),
			 ignoreSubsorts?)
	| (TyVar(id1,_), TyVar(id2,_)) -> 
	  if id1 = id2 
	  then Unify pairs
	  else NotUnify (srt1,srt2)
	| (MetaTyVar(mtv,_), _) -> 
	   let s2_ = unfoldSort(env,srt2) in
	   let t = unlinkSort s2_ in
	   if equalSort?(t,s1)
	       then Unify pairs
	   else
	       if occurs(mtv,t) 
		   then NotUnify (srt1,srt2)
	       else (linkMetaTyVar mtv (withAnnS(s2,pos2)); Unify pairs)
	| (t, MetaTyVar (mtv, _)) -> 
	  let t = unfoldSort (env, t) in
	  let t = unlinkSort t in
	  if equalSort? (t, s2) then
	    Unify pairs
	  else
	    if occurs (mtv, t) then
	      NotUnify (srt1,srt2)
	    else
	      (linkMetaTyVar mtv (withAnnS(s1,pos1)); Unify pairs)
	| _ ->
	  if ignoreSubsorts?
	    then (case (srt1,srt2) of
		    | (Subsort(ty,_,_),ty2) -> unify(env,ty,ty2,pairs,ignoreSubsorts?)
		    | (ty,Subsort(ty2,_,_)) -> unify(env,ty,ty2,pairs,ignoreSubsorts?)
		    | (Base _,_) -> 
		      let  s1_ = unfoldSort(env,srt1) in
		      if equalSort?(s1,s1_)
		      then NotUnify (srt1,srt2)
		      else unify(env,s1_,s2,pairs,ignoreSubsorts?)
		    | (_,Base _) ->
		      let s2_ = unfoldSort(env,srt2) in
		      if equalSort?(s2,s2_)
		      then NotUnify (srt1,srt2)
		      else unify(env,s1,s2_,pairs,ignoreSubsorts?)
		    | _ -> NotUnify(srt1,srt2))
	    else (case (srt1,srt2) of
		    | (Base _,_) -> 
		      let  s1_ = unfoldSort(env,srt1) in
		      if equalSort?(s1,s1_)
		      then NotUnify (srt1,srt2)
		      else unify(env,s1_,s2,pairs,ignoreSubsorts?)
		    | (_,Base _) ->
		      let s2_ = unfoldSort(env,srt2) in
		      if equalSort?(s2,s2_)
		      then NotUnify (srt1,srt2)
		      else unify(env,s1,s2_,pairs,ignoreSubsorts?)
		    | _ -> NotUnify(srt1,srt2))

 op consistentSorts?: LocalEnv * MS.Sort * MS.Sort * Boolean -> Boolean
 def consistentSorts?(env,srt1,srt2,ignoreSubsorts?) =
   let free_meta_ty_vars = freeMetaTypeVars(srt1) ++ freeMetaTypeVars(srt2) in
   let (val,_) = (unifySorts env ignoreSubsorts? srt1 srt2) in
   (clearMetaTyVarLinks free_meta_ty_vars;
    val)

 def clearMetaTyVarLinks meta_ty_vars =
  app (fn mtv -> 
        let {link, uniqueId, name} = ! mtv in
        mtv := {link = None, uniqueId = uniqueId, name = name})
      meta_ty_vars


 def freeMetaTypeVars(srt) = 
   let vars = (Ref []) : Ref(MS.MetaTyVars) in
   let def vr(srt) = 
         case srt
           of MetaTyVar(tv,pos) -> 
              (case unlinkSort srt of
                | MetaTyVar(tv,_) -> (vars := cons (tv,! vars); srt)
                | s -> mapSort (fn x -> x,vr,fn x -> x) (withAnnS (s, pos)))
            | _ -> srt
   in
   let _ = mapSort(fn x -> x,vr,fn x -> x) srt in
   ! vars

 def occurs(v: MS.MetaTyVar,srt: MS.Sort): Boolean = 
   let
      def occursOptRow(v,row) =
       case row of
	 | [] -> false
	 | (_,Some t)::rRow -> occurs(v,t) or occursOptRow(v,rRow)
	 | (_,None)::rRow -> occursOptRow(v,rRow)
     def occursRow(v,row) =
       case row of
	 | [] -> false
	 | (_,t)::rRow -> occurs(v,t) or occursRow(v,rRow)
   in
   case srt
     of CoProduct(row,_)   -> occursOptRow(v,row)
      | Product(row,_)     -> occursRow(v,row)
      | Arrow(t1,t2,_)     -> occurs(v,t1) or occurs(v,t2)
      %% sjw 3/404 It seems safe to ignore the predicates and it fixes bug 82
      | Quotient(t,pred,_) -> occurs(v,t)  %or occursT(v,pred)
      | Subsort(t,pred,_)  -> occurs(v,t)  %or occursT(v,pred)
      | Base(_,srts,_)     -> exists (fn s -> occurs(v,s)) srts
      | TyVar _            -> false 
      | MetaTyVar _        -> (case unlinkSort srt of
                               | MetaTyVar(w1,_) -> v = w1 
                               | t -> occurs(v,t))

 def occursT(v,pred) =
   case pred
     of ApplyN(ms,_)         -> exists (fn M -> occursT(v,M)) ms
      | Record(fields,_)     -> exists (fn (_,M) -> occursT(v,M)) fields
      | Bind(_,vars,body,_)  -> exists (fn (_,s) -> occurs(v,s)) vars or occursT(v,body)
      | IfThenElse(M,N,P,_)  -> occursT(v,M) or occursT(v,N) or occursT(v,P)
      | Var((_,s),_)         -> occurs(v,s)
      | Fun(_,s,_)           -> occurs(v,s)
      | Seq(ms,_)            -> exists (fn M -> occursT(v,M)) ms
      | Let(decls,body,_)    -> occursT(v,body) or exists (fn (p,M) -> occursT(v,M)) decls
      | LetRec(decls,body,_) -> occursT(v,body) or exists (fn (p,M) -> occursT(v,M)) decls
      | Lambda(rules,_)      -> exists (fn (p,c,M) -> occursT(v,M)) rules
      | _                    -> false

 (* Apply substitution as variable linking *)
 op linkMetaTyVar : MS.MetaTyVar -> MS.Sort -> ()
 def linkMetaTyVar (v:MS.MetaTyVar) t = 
   let {link,uniqueId,name} = ! v in
   (%%String.writeLine ("Linking "^name^Nat.toString uniqueId^" with "^printSort t);
   v := {link = Some t, uniqueId = uniqueId, name = name})
endspec
