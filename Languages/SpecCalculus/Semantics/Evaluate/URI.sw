\subsection{Evalution of a URI term in the Spec Calculus}

Derived from r1.9 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalURI.sl

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import ../SpecPath 
  import ../../Parser/Parse
\end{spec}

We are given a relative URI. To evaluate it, we first look in the local
context. If we find it we are done. If not then it will either be in
the global context or in the filesystem. We first convert the relative
URI into a list of candidate canonical URIs. We then try to find each
canonical uri in the global context. If we find it we are done.

If not, then the uri list is converted into a list of pairs. A pair
consists of a URI and a candidate file for the URI (there are two
candidates for each canonical uri). We then walk down the list. We load
successive files and then check to see if the URI is then defined.
If we get to the end of the list then we have failed.

\begin{spec}
  op existsAndReadable? : String -> Env Boolean

  def SpecCalc.evaluateURI position uri = {
      (value,_) <- evaluateReturnURI position uri;
      return value
    }
\end{spec}

evaluateReturnURI is the same as evaluateURI except it also returns
the canonical URI found.

\begin{spec}
  op evaluateReturnURI : Position -> RelativeURI -> Env (ValueInfo * URI)
  def evaluateReturnURI position uri = {
    % let dscr = showRelativeURI uri in 
    % print ("evaluateURI: " ^ dscr ^ "\n");
    optValue <- lookupInLocalContext uri;
    currentURI <- getCurrentURI;
    case optValue of
      | Some valueInfo -> return (valueInfo,currentURI)
      | None -> {
          % trace "evaluateURI: not found in local context\n";
          uriList <- generateURIList uri;
          % trace ("evaluateURI: resolved to \n\n   "
          %     ^ (List.show "\n   " (map showURI uriList))
          %     ^ "\n\n");
          optValue <- searchContextForURI uriList;
          (case optValue of      
             | Some value -> return value
             | None -> {% trace "evaluateURI: not found in global context\n";
               uriPathPairs <-
                 foldM
                  (fn l -> fn uri -> {
                     pair <- generateFileList uri;
                     return (l ++ pair)})
                  [] uriList;
%                 trace ("evaluateURI: uriPathPairs =\n  "
%                        ^ (List.show "\n   "
%                            (map (fn (uri,path) -> "\n   " ^ (showURI uri) ^ "\n   path: " ^ path)
%                           uriPathPairs))
%                        ^ "\n\n");
                searchFileSystemForURI (position, uri, uriPathPairs, currentURI)
              })
        }
    }
\end{spec}

These are called only from evaluateURI.

\begin{spec}
  op searchContextForURI : List URI -> Env (Option (ValueInfo * URI))
  def searchContextForURI uris =
    case uris of
      | [] -> return None
      | uri::rest -> {
          optValue <- lookupInGlobalContext uri;
          (case optValue of      
            | Some (value,timeStamp,_) ->
              (case value of
                 | InProcess -> raise (CircularDefinition uri)
                 | _ -> {cacheTS <- validateCache uri;
                         return (if cacheTS <= timeStamp
				   then Some ((value,timeStamp,[uri]), uri)
                                 else None)})
            | None -> searchContextForURI rest)
        }

  op searchFileSystemForURI : Position * RelativeURI * List (URI * String) * URI
                                -> Env (ValueInfo * URI)
  def searchFileSystemForURI (position, relURI, pairs, currentURI) =
    case pairs of
      | [] -> raise (URINotFound (position,relURI))
      | ((uri,fileName)::rest) -> {
            test <- fileExistsAndReadable? fileName;
            if test & ~(inSameFile?(uri,currentURI)) then {
              loadFile uri fileName;
              % The desired side effect of loadFile is that
              % the URI is now bound in the global context.
              optValue <- lookupInGlobalContext uri;
              % Either return found value or keep looking:
              case optValue of
                | Some (value,timeStamp,_)
                   -> return ((value, timeStamp, [uri]), uri)
                | None -> searchFileSystemForURI (position, relURI, rest, currentURI)
            } else
              searchFileSystemForURI (position, relURI, rest, currentURI)
          }

  %% Don't want to try loading from file you are currently processing
  op inSameFile?: URI * URI -> Boolean
  def inSameFile?(uri,currentURI) =
    case (uri,currentURI) of
      | ({path = path1, hashSuffix = Some _},
         {path = path2, hashSuffix = _}) ->
        path1 = path2
      | _ -> false
      
\end{spec}

The following converts a relative URI into a list of candidate canonical
URIs.

The inner case in the function below is temporary. It is there to make
it easy to experiment with different URI path resolution strategies..

\begin{spec}
  op generateURIList : RelativeURI -> Env (List URI)
  def generateURIList uri =
    case uri of
      | SpecPath_Relative {path,hashSuffix} -> {
            specPath <- getSpecPath;
            return (map (fn {path=root,hashSuffix=_} ->
                 normalizeURI {path = root ++ path,
                               hashSuffix = hashSuffix})
                 specPath)
          }
      | URI_Relative {path=newPath,hashSuffix=newSuffix} -> {
            {path=currentPath,hashSuffix=currentSuffix} <- getCurrentURI;
            root <- removeLast currentPath;
            (case (currentPath,currentSuffix,newPath,newSuffix) of
              | (_,Some _,[elem],None) ->
                    return [normalizeURI {path=currentPath,hashSuffix=Some elem},
                            normalizeURI {path=root++newPath,hashSuffix=None}]
              | (_,_,_,_) -> 
                    return [normalizeURI {path=root++newPath,hashSuffix=newSuffix}]
                 )
          }
\end{spec}
   
The following converts a canonical URI into a list of candidate files
where the object may reside. It returns a list of pairs. The first in
each pair is the URI (unchanged) and the second is the candidate file.
Recall that a file may contain a list of bindings to terms or a single
anonymous terms.

Following Stephen suggestion the current scheme should be changed.
There should be a separate syntax for referring to URIs that resolve
to one of many bindings in a file. For example \verb|/a/b#c|.

\begin{spec}
  op generateFileList : URI -> Env (List (URI * String))
  def generateFileList uri =
      return [(uri, (uriToPath uri) ^ ".sw")]
\end{spec}
      
Given a term find a canonical URI for it.

\begin{spec}
  def SpecCalc.getURI term =
    case (valueOf term) of
      | URI uri -> {(_,r_uri) <- evaluateReturnURI (positionOf term) uri;
                    return r_uri}
      | _ -> getCurrentURI                % Not sure what to do here
\end{spec}

Having resolved a URI to a file in the file system, this loads and
evaluates the file. The file may contain a single term, or a list
of definitions. If the former, then we bind the value of the term
to the given URI. If the latter then we assume that the names being bound
are relative to the given URI less its last element. So we construct
the bindings relative to such a path.

Some care must be taken to ensure that the local context is discarded
before we evaluate the contents of the file and restored after.  A local
context does not extend beyond the file in which it appears.

Also, we make sure that when we evaluate the terms in the file, we
must set the current uri (in the state) to the uri being bound to the
term. This is to ensure that relative URIs within the term are
handled correctly.

\begin{spec}
  op loadFile : URI -> String -> Env ()
  def loadFile uri fileName = %{
    % print ("Loading: " ^ fileName ^ "\n");
    case (parseFile fileName) of
      | None -> raise (ParserError fileName)
      | Some specFile -> 
	(case (valueOf specFile) of
	   | Term term ->
	     %% This test fixes Bug 002: "Processing a non-existent spec in existent file does not produce any errors"
  	     (case uri.hashSuffix of
		| Some name -> 
		  %%  Loading Foo#Bogus is an error if Foo contains just a term (as opposed to decls).
                  %%  We assume the caller of loadFile (e.g. searchFileSystemForURI) will raise an
		  %%   exception when it cannot find the uri.
		  return ()
		| _ -> 
		  { saveURI <- getCurrentURI;
		    saveLocalContext <- getLocalContext;
		    setCurrentURI uri;
		    clearLocalContext;
		    bindInGlobalContext uri (InProcess,0,[]);
		    (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo term;
		    setCurrentURI saveURI;
		    setLocalContext saveLocalContext;
		    bindInGlobalContext uri (value, max(timeStamp,fileWriteTime fileName), depURIs)
		   })
	   | Decls decls -> evaluateGlobalDecls uri fileName decls)
  %  }

  op evaluateGlobalDecls : URI -> String -> List (Decl Position) -> Env ()
  def evaluateGlobalDecls {path, hashSuffix=_} fileName decls =
    let def evaluateGlobalDecl (name,term) =
      let newURI = {path=path,hashSuffix=Some name} in {
        setCurrentURI newURI;
        (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo term;
        bindInGlobalContext newURI (value,max(timeStamp,fileWriteTime fileName),depURIs)
    }
    in {
      saveURI <- getCurrentURI;
      saveLocalContext <- getLocalContext;
      clearLocalContext;
      mapM evaluateGlobalDecl decls;
      setCurrentURI saveURI;
      setLocalContext saveLocalContext
    }
\end{spec}

validateCache takes a URI (absolute) and checks that it and all its
dependents are up-to-date, returning false if they are not. Those that
are not are removed from the environment.

\begin{spec}
  op validateCache : URI -> Env TimeStamp
  def validateCache uri =
    {validated? <- validatedURI? uri;
     if validated?
       then return 0
     else
       {optValue <- lookupInGlobalContext uri;
	case optValue of
	  | None -> return futureTimeStamp
	  | Some (_,timeStamp,depURIs) ->
	    %% the foldM finds the max of the timeStamps of the dependents and its own
	    %% "infinity" if invalid
	    {rVal <- foldM (fn val -> (fn depURI -> {dVal <- validateCache depURI;
						     return (max(val, dVal))}))
		       timeStamp depURIs;
	     if timeStamp >= rVal & upToDate?(uri,rVal)
	      then {setValidatedURI uri;
		    return rVal}
	      else {removeFromGlobalContext uri;
		    return futureTimeStamp}}}}

  op upToDate?: URI * TimeStamp -> Boolean
  def upToDate?(uri,timeStamp) =
    let fileName = (uriToPath uri) ^ ".sw" in
    (fileWriteTime fileName) <= timeStamp
}
\end{spec}
