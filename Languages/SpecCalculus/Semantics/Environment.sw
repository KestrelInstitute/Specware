\section{The Specware Environment}

The environment is the monadic context for the spec calculus interpreter. 
The monad handles, state, (very primitive) IO, and exceptions. In principle,
the datatype should be defined compositionally but this isn't supported as
yet. In the meantime, the monad and the operations for dealing with it
are described monolithically ... everything appears below. Ugh!

\begin{spec}
SpecCalc qualifying spec
  import ../AbstractSyntax/Types   
  import ../AbstractSyntax/Printer
  import Monad
\end{spec}

The Monad/Base spec supplies declarations of
ths sort Monad and the operators monadSeq, monadBind and return. 

All terms in the calculus have a value.  A value is a specification, a
diagram, morphism etc.  We combine them with a coproduct.

\begin{spec}
  sort Info
\end{spec}

The interpreter maintains state.  The state of the interpreter includes
two maps assigning a value to a URI. We call these \emph{name contexts}
(but some thought should go into the nomenclature for contexts,
environments, state \emph{etc}). One context is a global context. This
are names of URIs that resolve to objects in the file system. The other
is a local context. These are names bound by \verb+let+ expressions. The
scope of such names is limited.

A name is a URI, a let bound name or a name bound by one amongst a list
of definitions in a file. The latter two are cast into URIs.

By recording the binding of a name to a value in an environment, we seek
to avoid re-elaborating spec terms.

The state also includes the URI for the object currently being evaluated.
This is needed to resolve relative URIs found within the object. A
\emph{relative} URI is resolved relative to the \emph{canonical} URI for
the object containing the reference. A canonical path is always relative
to the root of the filesystem. A URI in the environment should always be
a canonical path.  See \url{Languages/SpecCalculus/AbstractSyntax/Types}.

TimeStamps are the universal time values as returned by the lisp
function file-write-date. URI_Dependency are the URIs that a value
depends on. ValueInfo is a value plus its URI_Dependency and a
TimeStamp that is latest of the TimeStamps of the files of its
URI_Dependency.

\begin{spec}
  sort TimeStamp = Time          % Not a fixnum
  op futureTimeStamp: TimeStamp		% > than any TimeStamp in foreseeable future
  def futureTimeStamp = 9999999999
  sort URI_Dependency = List URI
  sort ValidatedURIs = List URI
  sort ValueInfo = Value * TimeStamp * URI_Dependency
  sort GlobalContext = PolyMap.Map (URI, ValueInfo)
  sort LocalContext  = PolyMap.Map (RelativeURI, ValueInfo)
  % sort State = GlobalContext * LocalContext * Option URI * ValidatedURIs

  op ppValueInfo : ValueInfo -> Doc
  def ppValueInfo (value,timeStamp,depURIs) =
    ppConcat([ppValue value,
              ppString (Nat.toString timeStamp)]
             ++ map ppURI depURIs)
\end{spec}

\begin{spec}
  op initGlobalVars : ()
  def initGlobalVars =
    run {
      print "Declaring globals ...";
      newGlobalVar ("BaseInfo", (None : Option RelativeUnitId, emptySpec));
      newGlobalVar ("GlobalContext", PolyMap.emptyMap);
      newGlobalVar ("LocalContext", PolyMap.emptyMap);
      newGlobalVar ("CurrentUnitId", Some {path=["/"], hashSuffix=None} : Option.Option UnitId);
      newGlobalVar ("ValidatedUnitIds",[]);
      return ()
    }

  op getBase : Env ((Option RelativeUnitId) * Spec)
  def getBase = readGlobalVar "BaseInfo"

  op setBase : ((Option RelativeUnitId) * Spec) -> Env ()
  def setBase baseInfo = writeGlobalVar ("BaseInfo", baseInfo)

  op showGlobalContext : Env String
  def showGlobalContext = {
      globalContext <- readGlobalVar "GlobalContext";
      return (ppFormat (ppMap (fn uri -> ppString (showURI uri)) ppValueInfo globalContext))
    }

  op printGlobalContext : Env ()
  def printGlobalContext = {
      str <- showGlobalContext;
      print ("global context: " ^ str ^ "\n")
    }

  op emptyGlobalContext : Env ()
  def emptyGlobalContext = setGlobalContext PolyMap.emptyMap

  op setGlobalContext : GlobalContext -> Env ()
  def setGlobalContext globalContext = writeGlobalVar ("GlobalContext",globalContext)

  op getGlobalContect : Env GlobalContext
  def getGlobalContext = readGlobalVar "GlobalContext"

  op bindInGlobalContext : URI -> ValueInfo -> Env ()
  def bindInGlobalContext unitId value = {
      globalContext <- getGlobalContext;
      setGlobalContext (update globalContext unitId value)
    }

  op lookupInGlobalContext : URI -> Env (Option ValueInfo)
  def lookupInGlobalContext unitId = {
      globalContext <- getGlobalContext;
      return (evalPartial globalContext unitId)
    }

  op removeFromGlobalContext : URI -> Env ()
  def removeFromGlobalContext unitId = {
      globalContext <- getGlobalContext;
      setGlobalContext (remove globalContext unitId)
    }

  op cleanupGlobalContext : Env ()
  def cleanupGlobalContext =
    { gCtxt <- getGlobalContext;
      setGlobalContext (mapPartial (fn x as (val,_,_) ->
				     case val of
				      | InProcess -> None
				      | _ -> Some x)
		          gCtxt)
     }
\end{spec}

The local context is where "let" bindings are deposied

\begin{spec}
  op bindInLocalContext : RelativeURI -> ValueInfo -> Env ()
  def bindInLocalContext relativeUnitId value = {
      localContext <- readGlobalVar "LocalContext";
      writeGlobalVar ("LocalContext", update localContext relativeUnitId value)
    }

  op lookupInLocalContext : RelativeURI -> Env (Option ValueInfo)
  def lookupInLocalContext relativeUnitId = {
      localContext <- readGlobalVar "LocalContext";
      return (evalPartial localContext relativeUnitId)
    }

  op showLocalContext : Env String
  def showLocalContext = {
      localContext <- readGlobalVar "LocalContext";
      return (ppFormat (ppMap ppRelativeURI ppValueInfo localContext))
    }

  op printLocalContext : Env ()
  def printLocalContext = {
      str <- showLocalContext;
      print ("local context: " ^ str ^ "\n")
    }
\end{spec}

When evaluating new locally scoped bindings, we need to be able to
retrieve the local context and restore it later. Also, when we evaluate
a new UnitId, we must abandon the local context in the UnitId.

\begin{spec}
  op getLocalContext : Env LocalContext
  def getLocalContext = readGlobalVar "LocalContext"

  op setLocalContext : LocalContext -> Env ()
  def setLocalContext newLocalContext = writeGlobalVar ("LocalContext",newLocalContext)

  op clearLocalContext : Env ()
  def clearLocalContext = setLocalContext emptyMap
\end{spec}

The corresponding retrieve and set the current UnitId. They are duplicated
while there is a transition from names with "URI" to "UnitId".

\begin{spec}
  op getCurrentURI : Env UnitId
  def getCurrentURI = getCurrentUnitId

  op setCurrentURI : UnitId -> Env ()
  def setCurrentURI = setCurrentUnitId

  op getCurrentUnitId : Env UnitId
  def getCurrentUnitId = {
      optUnitId <- readGlobalVar "CurrentUnitId";
      case optUnitId of
        | None -> raise (Fail "No current Unit Id")
        | Some unitId -> return unitId
    }

  op setCurrentUnitId : UnitId -> Env ()
  def setCurrentUnitId newUnitId = writeGlobalVar ("CurrentUnitId", Some newUnitId)
\end{spec}

\begin{spec}
  op  validatedURI? : UnitId -> Env Boolean
  def validatedURI? = validatedUnitId?

  op setValidatedURI : UnitId -> Env ()
  def setValidatedURI = setValidatedUnitId

  op validatedUnitId? : UnitId -> Env Boolean
  def validatedUnitId? unitId = {
      validatedUnitIds <- readGlobalVar "ValidatedUnitIds";
      return (member(unitId,validatedUnitIds))
    }

  op setValidatedUnitId : UnitId -> Env ()
  def setValidatedUnitId unitId = {
      validatedUnitIds <- readGlobalVar "ValidatedUnitIds";
      writeGlobalVar ("ValidatedUnitIds", cons(unitId,validatedUnitIds))
    }
\end{spec}

I'm not sure the following is necessary. It is called at the start of
the toplevel functions. 

\begin{spec}
  op resetGlobals : Env ()
  def resetGlobals =
      % writeGlobalVar ("LocalContext", PolyMap.emptyMap);
      % writeGlobalVar ("CurrentUnitId", Some {path=["/"], hashSuffix=None} : Option.Option UnitId);
      writeGlobalVar ("ValidatedUnitIds",[])
endspec
\end{spec}
