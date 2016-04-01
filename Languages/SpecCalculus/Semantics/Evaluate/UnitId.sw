(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%%% Evalution of a UnitId term in the Spec Calculus

SpecCalc qualifying spec
  import Signature                 % including SCTerm
  import ../SpecPath 
  import ../../Parser/Parse

(*
We are given a relative UnitId. To evaluate it, we first look in the local
context. If we find it we are done. If not then it will either be in
the global context or in the filesystem. We first convert the relative
UnitId into a list of candidate canonical UIDs. We then try to find each
canonical unitId in the global context. If we find it we are done.

If not, then the unitId list is converted into a list of pairs. A pair
consists of a UnitId and a candidate file for the UnitId (there are two
candidates for each canonical unitId). We then walk down the list. We load
successive files and then check to see if the UnitId is then defined.
If we get to the end of the list then we have failed.
*)
% See also Specware.evaluateUnitId.
  def evaluateUID position unitId = {
      (value,_) <- evaluateReturnUID position unitId false;
      return value
    }
(*
evaluateReturnUID is the same as evaluateUID except it also returns
the canonical UnitId found.
*)
  def evaluateReturnUID position unitId notFromCache? = {
    % let dscr = showRelativeUID unitId in 
    % print ("evaluateUID: " ^ dscr ^ "\n");
    optValue <- lookupInLocalContext unitId;
    currentUID <- getCurrentUID;
    case optValue of
      | Some valueInfo -> return (valueInfo,currentUID)
      | None -> {
          uidList <- generateUIDList unitId;
          when notFromCache?
            (removeUIDsFromCache uidList);
          optValue <- searchContextForUID uidList;
          (case optValue of      
             | Some value -> return value
             | None -> {
               uidPathPairs <-
                 foldM
                  (fn l -> fn unitId -> {
                     pair <- generateFileList unitId;
                     return (l ++ pair)})
                  [] uidList;
                searchFileSystemForUID (position, unitId, uidPathPairs, currentUID)
              })
        }
    }
(*
These are called only from evaluateReturnUID
*)
  op  searchContextForUID : List UnitId -> Env (Option (ValueInfo * UnitId))
  def searchContextForUID uids =
    let def searchForUID unitId =
          {optValue <- lookupInGlobalContext unitId;
	   (case optValue of      
	      | Some (value,timeStamp,_,_) ->
                (case value of
		   | InProcess _ -> raise (CircularDefinition unitId)
		   | _ ->
		   {cacheTS <- validateCache unitId;
		    if cacheTS <= timeStamp
		      then
			(case value of
			   | UnEvaluated term ->
			     {saveUID <- getCurrentUID;
			      setCurrentUID unitId;
			      bindInGlobalContext unitId (InProcess(makeMutex "import"),0,[],term);
			      (value,rTimeStamp,depUIDs) <- evaluateTermInfo term;
			      setCurrentUID saveUID;
			      let val = (value,max(timeStamp,rTimeStamp),depUIDs,term) in
			      {bindInGlobalContext unitId val;
			       newval <- return (val.1, val.2, [unitId]);
			       return (Some (newval,unitId))}}
			   | _ -> return (Some ((value,timeStamp,[unitId]), unitId)))
		    else return None})
	      | None -> return None)}
    in
    case uids of
      | [] -> return None
      | unitId::rest ->
        {optValue <- searchForUID unitId;
         case optValue of
	   | Some v -> return (Some v)
	   | None ->
	 case unitId of
	   | {path = path as _::_, hashSuffix = None} ->
	     %% Allow .../foo as abbreviation for .../foo#foo
	     {optValue <- searchForUID {path = path, hashSuffix = lastElt path};
	      case optValue of
	      | Some v -> return (Some v)
	      | None -> searchContextForUID rest}
	   | None -> searchContextForUID rest}

  op  searchFileSystemForUID : Position * RelativeUID * List (UnitId * String) * UnitId
                                -> Env (ValueInfo * UnitId)
  def searchFileSystemForUID (position, relUID, pairs, currentUID) =
    case pairs of
      | [] -> raise (FileNotFound (position,relUID))
      | ((unitId,fileName)::rest) -> {
            test <- fileExistsAndReadable? fileName;
            if test && ~(inSameFile?(unitId,currentUID)) then {
	      saveUID <- getCurrentUID;
	      saveLocalContext <- getLocalContext;
	      setCurrentUID unitId;
	      clearLocalContext;
              subUnitNames <- loadFile unitId fileName;
              % The desired side effect of loadFile is that
              % the UnitId is now bound in the global context.
	      let def lookup (unitId: UnitId): Env (Option(ValueInfo * UnitId)) =
	            {optValue <- lookupInGlobalContext unitId;
		     % Either return found value or keep looking:
		     case optValue of
		     | Some (value,timeStamp,_,_)
		       -> (case value of
			     | UnEvaluated term ->
			       {setCurrentUID unitId;
				bindInGlobalContext unitId (InProcess(makeMutex "import"),0,[],term);
				(value,rTimeStamp,depUIDs) <- evaluateTermInfo term;
				let timeStamp = max(timeStamp,rTimeStamp) in
				let val = (value,timeStamp,depUIDs,term) in
				{bindInGlobalContext unitId val;
				 return (Some((value,timeStamp,[unitId]),unitId))}}
			     | _ -> return (Some((value, timeStamp, [unitId]), unitId)))
		     | None -> return None}
	      in
	      {optValue <- lookup unitId;
	       case optValue of
		 | Some val ->
		   {setCurrentUID saveUID;
		    setLocalContext saveLocalContext;
		    return val}
		 | None ->
	       case unitId of
		 | {path = path as _::_, hashSuffix = None} ->
		   %% Allow .../foo as abbreviation for .../foo#foo
		   {optValue <- lookup {path = path, hashSuffix = lastElt path};
		    case optValue of
		      | Some val ->
		        {setCurrentUID saveUID;
			 setLocalContext saveLocalContext;
			 return val}
		      | None ->
			%% :sw .../foo processes all subunits but doesn't return any
		        {valprs <- mapPartialM (fn name ->
                                                  {optValue <- lookup {path = path, hashSuffix = Some name};
                                                   case optValue
                                                     | Some (val_info_unitid) -> return(Some (name, val_info_unitid))
                                                     | None -> return None})
			             subUnitNames;
			 case valprs
                           | [] -> raise (UIDNotFound (position,relUID))
                           | (_, ((_, ts, _), unitId0)) :: _ ->
                             let val_prs: List(String * Value) = map (fn (nm, ((val, _, _), _)) -> (nm, val)) valprs in
                             return ((Values val_prs, ts, [unitId]), unitId0)}}
		 | _ -> raise (UIDNotFound (position,relUID))}
            } else
              searchFileSystemForUID (position, relUID, rest, currentUID)
          }

  %% Don't want to try loading from file you are currently processing
  op  inSameFile?: UnitId * UnitId -> Bool
  def inSameFile?(unitId,currentUID) =
    case (unitId,currentUID) of
      | ({path = path1, hashSuffix = Some _},
         {path = path2, hashSuffix = _}) ->
        path1 = path2
      | _ -> false

  op  lastElt: [a] List a -> Option a
  def lastElt l = if l = [] then None else Some(l@(length l - 1))

(*
The following converts a relative UnitId into a list of candidate canonical
UIDs.

The inner case in the function below is temporary. It is there to make
it easy to experiment with different UnitId path resolution strategies..
*)

  op generateUIDList (uid : RelativeUID) : Env (List UnitId) =
    case uid of
      | SpecPath_Relative {path, hashSuffix} ->
        if absolutePath? path
	  then return([{path       = path, 
			hashSuffix = hashSuffix}])
	else
        {
	 roots <- getSpecPath;
	 foldM (fn uids -> fn root ->
		return (uids 
			++
			map (fn shadow_root ->
			     normalizeUID {path       = shadow_root ++ path, 
					   hashSuffix = hashSuffix})
			    (pathShadows root.path)))
	       []
	       roots
        }
      | UnitId_Relative {path, hashSuffix} ->
        {
	 current_uid   <- getCurrentUID;                       % could be /tmp/...
	 adjusted_path <- return (pathAlias current_uid.path); % :swe etc. adjust back to connected dir
	 shadow_paths  <- return (pathShadows adjusted_path);  % shadowing works from there
	 %% each path in shadow_paths is a UIDPath shadowing those following it
	 foldM (fn uids -> fn shadow_path ->
		{shadow_root <- removeLast shadow_path;
		 % for example, shadow_path could be ["A" "B" "C]
		 %          and shadow_root would be ["A" "B"]
		 return (uids 
			 ++ 
			 (case (current_uid.hashSuffix, path, hashSuffix) of
			    | (Some _, [elem], None) ->
			    % "A/B/C#D referencing E" => ["A/B/C#E"] and see below
			    [normalizeUID {path = shadow_path, hashSuffix = Some elem}]
			    | (_,_,_) -> 
			    [])
			 ++
			 % "A/B/C   referencing #G"    #G is rejected by parser
			 % "A/B/C#D referencing #G"    #G is rejected by parser
			 % "A/B/C   referencing E"     => ["A/B/E"]
			 % "A/B/C#D referencing E"     => ["A/B/E"] and see above
			 % "A/B/C   referencing E/F"   => ["A/B/E/F"]
			 % "A/B/C#D referencing E/F"   => ["A/B/E/F"]
			 % "A/B/C   referencing E/F#G" => ["A/B/E/F#G"]
			 % "A/B/C#D referencing E/F#G" => ["A/B/E/F#G"]
			 [normalizeUID {path       = shadow_root ++ path, 
					hashSuffix = hashSuffix}])
	         })
	       []
	       shadow_paths
         }

  %% this is set by norm-unitid-str in toplevel.lisp
  %% It allows a command-line spec to be put into a temporary file but have
  %% any ids be relative to the shell environment and not the local file's unitid
  op  aliasPaths: List (UIDPath * UIDPath)
  def aliasPaths = []

  op  pathAlias: UIDPath -> UIDPath
  def pathAlias path =
    let
      def applyAliases aliasPaths =
	case aliasPaths of
	  | [] -> path
	  | (p,ap)::rpath ->
	    (case findAlias(path,p,ap) of
	      | Some tr_path -> tr_path
	      | None -> applyAliases rpath)
      def findAlias(path,p,ap) =
	case (path,p) of
	  | (_,[]) -> Some(ap ++ path)
	  | ([],_) -> None
	  | (p1::rp1,p2::rp2) ->
	    if p1 = p2
	      then findAlias(rp1,rp2,ap)
	      else None
    in
    applyAliases aliasPaths
     
  %% this is set by user when creating a shadow version 
  %% It allows files on other directory trees to shadow 
  %% corresponding files in a base tree.
  op shadowingPaths : Shadowings = []

  op pathShadows (uid_path : UIDPath) : Shadowing =
    let
      def expand shadow =
	%% shadow is a list of UID paths
	case find_suffix_wrt shadow of
	  | Some suffix ->
            %% we arrive here if some path in shadow is a prefix of uid_path,
	    %% so we know that some path++suffix will reconstitute uid_path
	    map (fn path -> path ++ suffix) shadow
	  | _ ->
	    []
      def find_suffix_wrt shadow =
	foldl (fn (opt_suffix, shadow_path) -> 
	       case opt_suffix of
		 | Some _ -> opt_suffix
		 | _ -> 
		   case leftmostPositionOfSublistAndFollowing (shadow_path, uid_path) of
		     | Some (_, suffix) -> Some suffix
		     | _ -> None)
	      None
	      shadow
    in
      case (foldl (fn (paths,shadow) ->
		   paths ++ expand shadow)
	          []
		  shadowingPaths) 
	of
	| [] -> [uid_path]
	% if there are any paths at all, we know that some 
	%  path++suffix in the map up above reconstituted uid_path
	| paths -> paths  

(*   
The following converts a canonical UnitId into a list of candidate files
where the object may reside. It returns a list of pairs. The first in
each pair is the UnitId (unchanged) and the second is the candidate file.
Recall that a file may contain a list of bindings to terms or a single
anonymous terms.

Following Stephen suggestion the current scheme should be changed.
There should be a separate syntax for referring to UIDs that resolve
to one of many bindings in a file. For example \verb|/a/b#c|.
*)
  op  generateFileList : UnitId -> Env (List (UnitId * String))
  def generateFileList unitId =
      return [(unitId, (uidToFullPath unitId) ^ ".sw")]
(*      
Given a term find a canonical UnitId for it.
*)
  op  getUID : SCTerm -> Env UnitId
  def getUID term =
    case (valueOf term) of
      | UnitId unitId -> {(_,r_uid) <- evaluateReturnUID (positionOf term) unitId false;
                          return r_uid}
      | _ -> getCurrentUID                % Not sure what to do here
(*
Having resolved a UnitId to a file in the file system, this loads and
evaluates the file. The file may contain a single term, or a list
of definitions. If the former, then we bind the value of the term
to the given UnitId. If the latter then we assume that the names being bound
are relative to the given UnitId less its last element. So we construct
the bindings relative to such a path.

Some care must be taken to ensure that the local context is discarded
before we evaluate the contents of the file and restored after.  A local
context does not extend beyond the file in which it appears.

Also, we make sure that when we evaluate the terms in the file, we
must set the current unitId (in the state) to the unitId being bound to the
term. This is to ensure that relative UIDs within the term are
handled correctly.
*)
  op  loadFile : UnitId -> String -> Env (List String)
  def loadFile unitId fileName = %{
    % print ("Loading: " ^ fileName ^ "\n");
    case (parseSpecwareFile fileName) of
      | None -> raise (ParserError fileName)
      | Some specFile -> 
	(case (valueOf specFile) of
	   | Term term ->
	     %% This test fixes Bug 002: "Processing a non-existent spec in existent file does not produce any errors"
  	     (case unitId.hashSuffix of
		| Some name -> 
		  %%  Loading Foo#Bogus is an error if Foo contains just a term (as opposed to decls).
                  %%  We assume the caller of loadFile (e.g. searchFileSystemForUID) will raise an
		  %%   exception when it cannot find the unitId.
		  return []
		| _ -> 
		  { bindInGlobalContext unitId (InProcess(makeMutex "import"),0,[],term);
		    (value,timeStamp,depUIDs) <- evaluateTermInfo term;
		    bindInGlobalContext unitId (value, max(timeStamp,fileWriteTime fileName), depUIDs, term);
		    return []
		   })
	   | Decls decls -> storeGlobalDecls unitId fileName decls)
  %  }

  op storeGlobalDecls : UnitId -> String -> SCDecls -> Env (List String)
  def storeGlobalDecls {path, hashSuffix=_} fileName decls =
    let def storeGlobalDecl (name,term) =
	  let newUID = {path=path,hashSuffix=Some name} in
	  {setCurrentUID newUID;
	   bindInGlobalContext newUID (UnEvaluated term,fileWriteTime fileName,[],term);
	   return name}
    in {checkForMultipleDefs decls;
	mapM storeGlobalDecl decls}

  op checkForMultipleDefs: SCDecls -> Env ()
  def checkForMultipleDefs decls =
    case foldl (fn (result as (seenNames,duplicate?), (name,term)) ->
	        case duplicate? of
		 | None -> if name in? seenNames
		            then (seenNames,Some(name,term))
			    else (Cons(name,seenNames),None)
                 | _ -> result)
           ([],None) decls
      of (_,Some(name,(_,pos))) ->
	 raise (SpecError (pos,"Name \"" ^ name ^ "\" defined twice in file."))
       | _ -> return ()
(*
Used so toplevel UI functions can find out whether a unitId has up-to-date version in cache. 
*)
  op  checkInCache? : RelativeUID -> Env Bool
  def checkInCache? unitId =
    { uidList <- generateUIDList unitId;
      optValue <- searchContextForUID uidList;
      return(some? optValue)}
(*
validateCache takes a UnitId (absolute) and checks that it and all its
dependents are up-to-date, returning false if they are not. Those that
aren't are removed from the environment.
*)
  op validateCache : UnitId -> Env TimeStamp
  def validateCache unitId =
    {optValue <- lookupInGlobalContext unitId;
     case optValue of
       | None -> return futureTimeStamp   % Not in cache
       | Some (_,timeStamp,depUIDs,_) ->
         if unitId in? depUIDs then
	   raise (CircularDefinition unitId)
	 else      
	   {
	    validated? <- validatedUID? unitId;   % True if already validated
	    if validated? then
	      return timeStamp
	    else 
	      %% the foldM finds the max of the timeStamps of the dependents and its own
	      %% "infinity" if invalid
	      {rVal <- foldM (fn val -> fn depUID -> 
			      {dVal <- validateCache depUID;
			       return (max(val, dVal))})
	                     timeStamp 
			     depUIDs;
	       if timeStamp >= rVal && upToDateOrNotPresent?(unitId,rVal) then
		 {setValidatedUID unitId;  % Remember that this unitId has been validated
		  return rVal}
	       else 
		 {removeFromGlobalContext unitId;
		  return futureTimeStamp}}
	     }
	  }

  op  upToDateOrNotPresent?: UnitId * TimeStamp -> Bool
  def upToDateOrNotPresent?(unitId,timeStamp) =
    let fileName = (uidToFullPath unitId) ^ ".sw" in
    let writeTime = fileWriteTime fileName in
    writeTime <= timeStamp || writeTime = nullFileWriteTime

  op removeUIDfromCache (unitId: RelativeUID): Env () =
    {uidList <- generateUIDList unitId;
     removeUIDsFromCache uidList}

  op removeUIDsFromCache (uids: List UnitId): Env () =
    case uids of
      | [] -> return ()
      | unitId::rest ->
        {removeFromGlobalContext unitId;
         case unitId of
           | {path = path as _::_, hashSuffix = None} ->
	     %% Consider .../foo could be abbreviation for .../foo#foo
	     removeUIDsFromCache({path = path, hashSuffix = lastElt path} :: rest)
           | _ -> removeUIDsFromCache rest}

end-spec
