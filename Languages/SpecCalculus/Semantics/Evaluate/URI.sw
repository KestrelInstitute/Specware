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
      | Some valueInfo -> % {
            % trace "evaluateURI: found in local context\n";
	    % No dependency information needed
            return (valueInfo,currentURI)
          % }
      | None -> {
          % trace "evaluateURI: not found in local context\n";
          uriList <- generateURIList uri;
          % trace ("evaluateURI: resolved to \n\n   "
          %     ^ (showList "\n   " showURI uriList)
          %     ^ "\n\n");
          optValue <- searchContextForURI uriList;
          (case optValue of      
              | Some value -> % {
                    % trace "evaluateURI: found in global context\n";
                    return value
                  % } 
              | None -> {
                    % trace "evaluateURI: not found in global context\n";
                    uriPathPairs <- foldM
                      (fn l -> fn uri -> {
                         pair <- generateFileList uri;
                         return (l ++ pair)}) [] uriList;
                    % trace ("evaluateURI: uriPathPairs =\n  "
                    %        ^ (showList "\n   "
                    %            (fn (uri,path) -> "\n   "
                    %               ^ (showURI uri)
                    %               ^ "\n   path: "
                    %               ^ path)
                    %           uriPathPairs)
                    %        ^ "\n\n");
                    searchFileSystemForURI position uri uriPathPairs
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
	      {valid? <- validateCache uri;
	       return (if valid? then Some ((value,timeStamp,[uri]), uri)
		        else None)}
            | None -> searchContextForURI rest)
        }

  op searchFileSystemForURI : Position -> RelativeURI -> List (URI * String)
                                -> Env (ValueInfo * URI)
  def searchFileSystemForURI position relURI pairs =
    case pairs of
      | [] -> raise (URINotFound (position,relURI))
      | ((uri,fileName)::rest) -> {
            test <- fileExistsAndReadable? fileName;
            if test then {
              loadFile uri fileName;
              % The desired side effect of loadFile is that
              % the URI is now bound in the global context.
              optValue <- lookupInGlobalContext uri;
              % Either return found value or keep looking:
              case optValue of
                | Some (value,timeStamp,_)
		   -> return ((value, timeStamp, [uri]),
			      uri)
                | None -> searchFileSystemForURI position relURI rest
            } else
              searchFileSystemForURI position relURI rest
          }
\end{spec}

The following converts a relative URI into a list of candidate canonical
URIs.

\begin{spec}
  op generateURIList : RelativeURI -> Env (List URI)
  def generateURIList uri =
    case uri of
      | SpecPath_Relative elems -> {
            specPath <- getSpecPath;
            return (map (fn root -> normalizeURI (root ++ elems)) specPath)
          }
      | URI_Relative elems -> {
            currentURI <- getCurrentURI;
            root <- removeLastElem currentURI;
            return [normalizeURI (root ++ elems)]
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
  def generateFileList uri = {
      prefix <- removeLastElem uri;
      return [(uri, (uriToPath uri) ^ ".sw"),
              (uri, (uriToPath prefix) ^ ".sw")]
    }
\end{spec}
      
Given a term find a canonical URI for it.

\begin{spec}
  def SpecCalc.getURI term =
    case (valueOf term) of
      | URI uri -> {(_,r_uri) <- evaluateReturnURI (positionOf term) uri;
		    return r_uri}
      | _ -> getCurrentURI		% Not sure what to do here
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
  def loadFile uri fileName = {
      print ("Loading: " ^ fileName ^ "\n");
      case (parseFile fileName) of
        | None -> raise (SyntaxError fileName)
        | Some specFile -> 
           (case (valueOf specFile) of
             | Term term -> {
                   saveURI <- getCurrentURI;
                   saveLocalContext <- getLocalContext;
                   setCurrentURI uri;
                   clearLocalContext;
                   (value,timeStamp,depURIs) <- SpecCalc.evaluateTermInfo term;
                   setCurrentURI saveURI;
                   setLocalContext saveLocalContext;
                   bindInGlobalContext uri
                     (value,max(timeStamp,fileWriteTime fileName),depURIs)
                 }
             | Decls decls -> {
                   rootURI <- removeLastElem uri;
                   evaluateGlobalDecls rootURI decls
                 })
    }

  op evaluateGlobalDecls : URI -> (List (Decl Position)) -> Env ()
  def evaluateGlobalDecls rootURI decls =
    let def evaluateGlobalDecl (name,term) =
      let newURI = rootURI ++ [name] in {
        setCurrentURI newURI;
        valueInfo <- SpecCalc.evaluateTermInfo term;
        bindInGlobalContext newURI valueInfo
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
  op validateCache : URI -> Env Boolean
  def validateCache uri =
    {optValue <- lookupInGlobalContext uri;
     case optValue of
       | None -> return false
       | Some (_,timeStamp,depURIs) ->
         %% the foldM does a forall, but no early stop
         {rVal <- foldM (fn val -> (fn depURI -> {dVal <- validateCache depURI;
						  return (val & dVal)}))
	            true depURIs;
	  let val = rVal & upToDate?(uri,timeStamp) in
	  if val then return true
	   else {removeFromGlobalContext uri;
		 return false}}}
         
  op upToDate?: URI * TimeStamp -> Boolean
  def upToDate?(uri,timeStamp) =
    let fileName = (uriToPath uri) ^ ".sw" in
    (fileExistsAndReadable fileName)
      & (fileWriteTime fileName) <= timeStamp
\end{spec}

\begin{spec}
}
\end{spec}
