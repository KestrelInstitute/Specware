\subsection{Evalution of a UnitId term in the Spec Calculus}

\begin{spec}
SpecCalc qualifying spec
  import Signature 
  import ../SpecPath 
  import ../../Parser/Parse
\end{spec}

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

\begin{spec}
  def SpecCalc.evaluateUID position unitId = {
      (value,_) <- evaluateReturnUID position unitId;
      return value
    }
\end{spec}

evaluateReturnUID is the same as evaluateUID except it also returns
the canonical UnitId found.

\begin{spec}
  def evaluateReturnUID position unitId = {
    % let dscr = showRelativeUID unitId in 
    % print ("evaluateUID: " ^ dscr ^ "\n");
    optValue <- lookupInLocalContext unitId;
    currentUID <- getCurrentUID;
    case optValue of
      | Some valueInfo -> return (valueInfo,currentUID)
      | None -> {
          % trace "evaluateUID: not found in local context\n";
          uidList <- generateUIDList unitId;
          % trace ("evaluateUID: resolved to \n\n   "
          %     ^ (List.show "\n   " (map showUID uidList))
          %     ^ "\n\n");
          optValue <- searchContextForUID uidList;
          (case optValue of      
             | Some value -> return value
             | None -> {
               % trace "evaluateUID: not found in global context\n";
               uidPathPairs <-
                 foldM
                  (fn l -> fn unitId -> {
                     pair <- generateFileList unitId;
                     return (l ++ pair)})
                  [] uidList;
                  % trace ("evaluateUID: uidPathPairs =\n  "
                  %        ^ (List.show "\n   "
                  %            (map (fn (unitId,path) -> "\n   " ^ (showUID unitId) ^ "\n   path: " ^ path)
                  %           uidPathPairs))
                  %        ^ "\n\n");
                searchFileSystemForUID (position, unitId, uidPathPairs, currentUID)
              })
        }
    }
\end{spec}

These are called only from evaluateUID.

\begin{spec}
  op searchContextForUID : List UnitId -> Env (Option (ValueInfo * UnitId))
  def searchContextForUID uids =
    case uids of
      | [] -> return None
      | unitId::rest -> {
          optValue <- lookupInGlobalContext unitId;
          (case optValue of      
            | Some (value,timeStamp,_) ->
              (case value of
                 | InProcess -> raise (CircularDefinition unitId)
                 | _ -> {cacheTS <- validateCache unitId;
                         return (if cacheTS <= timeStamp
				   then Some ((value,timeStamp,[unitId]), unitId)
                                 else None)})
            | None -> searchContextForUID rest)
        }

  op searchFileSystemForUID : Position * RelativeUID * List (UnitId * String) * UnitId
                                -> Env (ValueInfo * UnitId)
  def searchFileSystemForUID (position, relUID, pairs, currentUID) =
    case pairs of
      | [] -> raise (FileNotFound (position,relUID))
      | ((unitId,fileName)::rest) -> {
            test <- fileExistsAndReadable? fileName;
            if test & ~(inSameFile?(unitId,currentUID)) then {
              loadFile unitId fileName;
              % The desired side effect of loadFile is that
              % the UnitId is now bound in the global context.
              optValue <- lookupInGlobalContext unitId;
              % Either return found value or keep looking:
              case optValue of
                | Some (value,timeStamp,_)
                   -> return ((value, timeStamp, [unitId]), unitId)
                % | None -> searchFileSystemForUID (position, relUID, rest, currentUID)
                | None -> raise (UIDNotFound (position,relUID))
            } else
              searchFileSystemForUID (position, relUID, rest, currentUID)
          }

  %% Don't want to try loading from file you are currently processing
  op inSameFile?: UnitId * UnitId -> Boolean
  def inSameFile?(unitId,currentUID) =
    case (unitId,currentUID) of
      | ({path = path1, hashSuffix = Some _},
         {path = path2, hashSuffix = _}) ->
        path1 = path2
      | _ -> false
      
\end{spec}

The following converts a relative UnitId into a list of candidate canonical
UIDs.

The inner case in the function below is temporary. It is there to make
it easy to experiment with different UnitId path resolution strategies..

\begin{spec}
  op generateUIDList : RelativeUID -> Env (List UnitId)
  def generateUIDList unitId =
    case unitId of
      | SpecPath_Relative {path,hashSuffix} -> {
            specPath <- getSpecPath;
            return (map (fn {path=root,hashSuffix=_} ->
                 normalizeUID {path = root ++ path,
                               hashSuffix = hashSuffix})
                 specPath)
          }
      | UnitId_Relative {path=newPath,hashSuffix=newSuffix} -> {
            {path=currentPath,hashSuffix=currentSuffix} <- getCurrentUID;
            root <- removeLast currentPath;
            (case (currentPath,currentSuffix,newPath,newSuffix) of
              | (_,Some _,[elem],None) ->
                    return [normalizeUID {path=currentPath,hashSuffix=Some elem},
                            normalizeUID {path=root++newPath,hashSuffix=None}]
              | (_,_,_,_) -> 
                    return [normalizeUID {path=root++newPath,hashSuffix=newSuffix}]
                 )
          }
\end{spec}
   
The following converts a canonical UnitId into a list of candidate files
where the object may reside. It returns a list of pairs. The first in
each pair is the UnitId (unchanged) and the second is the candidate file.
Recall that a file may contain a list of bindings to terms or a single
anonymous terms.

Following Stephen suggestion the current scheme should be changed.
There should be a separate syntax for referring to UIDs that resolve
to one of many bindings in a file. For example \verb|/a/b#c|.

\begin{spec}
  op generateFileList : UnitId -> Env (List (UnitId * String))
  def generateFileList unitId =
      return [(unitId, (uidToFullPath unitId) ^ ".sw")]
\end{spec}
      
Given a term find a canonical UnitId for it.

\begin{spec}
  op SpecCalc.getUID : SpecCalc.Term Position -> Env UnitId
  def SpecCalc.getUID term =
    case (valueOf term) of
      | UnitId unitId -> {(_,r_uid) <- evaluateReturnUID (positionOf term) unitId;
                    return r_uid}
      | _ -> getCurrentUID                % Not sure what to do here
\end{spec}

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

\begin{spec}
  op loadFile : UnitId -> String -> Env ()
  def loadFile unitId fileName = %{
    % print ("Loading: " ^ fileName ^ "\n");
    case (parseFile fileName) of
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
		  return ()
		| _ -> 
		  { saveUID <- getCurrentUID;
		    saveLocalContext <- getLocalContext;
		    setCurrentUID unitId;
		    clearLocalContext;
		    bindInGlobalContext unitId (InProcess,0,[]);
		    (value,timeStamp,depUIDs) <- SpecCalc.evaluateTermInfo term;
		    setCurrentUID saveUID;
		    setLocalContext saveLocalContext;
		    bindInGlobalContext unitId (value, max(timeStamp,fileWriteTime fileName), depUIDs)
		   })
	   | Decls decls -> evaluateGlobalDecls unitId fileName decls)
  %  }

  op evaluateGlobalDecls : UnitId -> String -> List (Decl Position) -> Env ()
  def evaluateGlobalDecls {path, hashSuffix=_} fileName decls =
    let def evaluateGlobalDecl (name,term) =
      let newUID = {path=path,hashSuffix=Some name} in {
        setCurrentUID newUID;
        (value,timeStamp,depUIDs) <- SpecCalc.evaluateTermInfo term;
        bindInGlobalContext newUID (value,max(timeStamp,fileWriteTime fileName),depUIDs)
    }
    in {
      checkForMultipleDefs decls;
      saveUID <- getCurrentUID;
      saveLocalContext <- getLocalContext;
      clearLocalContext;
      mapM evaluateGlobalDecl decls;
      setCurrentUID saveUID;
      setLocalContext saveLocalContext
    }

  op checkForMultipleDefs: List (Decl Position) -> Env ()
  def checkForMultipleDefs decls =
    case foldl (fn ((name,term),result as (seenNames,duplicate?)) ->
	        case duplicate? of
		 | None -> if member(name,seenNames)
		            then (seenNames,Some(name,term))
			    else (cons(name,seenNames),None)
                 | _ -> result)
           ([],None) decls
      of (_,Some(name,(_,pos))) ->
	 raise (SpecError (pos,"Name \"" ^ name ^ "\" defined twice in file."))
       | _ -> return ()
\end{spec}

Used so toplevel UI functions can find out whether a unitId has up-to-date version in cache. 

\begin{spec}
  op  checkInCache? : RelativeUnitId -> Env Boolean
  def checkInCache? unitId =
    { uidList <- generateUIDList unitId;
      optValue <- searchContextForUID uidList;
      return(some? optValue)}
\end{spec}


validateCache takes a UnitId (absolute) and checks that it and all its
dependents are up-to-date, returning false if they are not. Those that
are not are removed from the environment.

\begin{spec}
  op validateCache : UnitId -> Env TimeStamp
  def validateCache unitId =
    {validated? <- validatedUID? unitId;
     if validated?
       then return 0
     else
       {optValue <- lookupInGlobalContext unitId;
	case optValue of
	  | None -> return futureTimeStamp
	  | Some (_,timeStamp,depUIDs) ->
	    %% the foldM finds the max of the timeStamps of the dependents and its own
	    %% "infinity" if invalid
	    {rVal <- foldM (fn val -> (fn depUID -> {dVal <- validateCache depUID;
						     return (max(val, dVal))}))
		       timeStamp depUIDs;
	     if timeStamp >= rVal & upToDate?(unitId,rVal)
	      then {setValidatedUID unitId;
		    return rVal}
	      else {removeFromGlobalContext unitId;
		    return futureTimeStamp}}}}

  op upToDate?: UnitId * TimeStamp -> Boolean
  def upToDate?(unitId,timeStamp) =
    let fileName = (uidToFullPath unitId) ^ ".sw" in
    (fileWriteTime fileName) <= timeStamp
endspec
\end{spec}
