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
two maps assigning a value to a UnitId. We call these \emph{name contexts}
(but some thought should go into the nomenclature for contexts,
environments, state \emph{etc}). One context is a global context. This
are names of UIDs that resolve to objects in the file system. The other
is a local context. These are names bound by \verb+let+ expressions. The
scope of such names is limited.

A name is a UnitId, a let bound name or a name bound by one amongst a list
of definitions in a file. The latter two are cast into UIDs.

By recording the binding of a name to a value in an environment, we seek
to avoid re-elaborating spec terms.

The state also includes the UnitId for the object currently being evaluated.
This is needed to resolve relative UIDs found within the object. A
\emph{relative} UnitId is resolved relative to the \emph{canonical} UnitId for
the object containing the reference. A canonical path is always relative
to the root of the filesystem. A UnitId in the environment should always be
a canonical path.  See \url{Languages/SpecCalculus/AbstractSyntax/Types}.

TimeStamps are the universal time values as returned by the lisp
function file-write-date. UnitId_Dependency are the UIDs that a value
depends on. ValueInfo is a value plus its UnitId_Dependency and a
TimeStamp that is latest of the TimeStamps of the files of its
UnitId_Dependency.

\begin{spec}
  sort TimeStamp = Time          % Not a fixnum
  op futureTimeStamp: TimeStamp		% > than any TimeStamp in foreseeable future
  def futureTimeStamp = 9999999999
  sort UnitId_Dependency = List UnitId
  sort ValidatedUIDs = List UnitId
  sort ValueInfo = Value * TimeStamp * UnitId_Dependency
  %% See validateCache in Evaluate/UnitId.sw -- it chases dependencies recursively,
  %% so we should not need to take unions of dependencies.

  sort GlobalContext = PolyMap.Map (UnitId, ValueInfo)
  sort LocalContext  = PolyMap.Map (RelativeUID, ValueInfo)
  % sort State = GlobalContext * LocalContext * Option UnitId * ValidatedUIDs

  op ppValueInfo : ValueInfo -> Doc
  def ppValueInfo (value,timeStamp,depUIDs) =
    ppConcat([ppValue value,
              ppString (Nat.toString timeStamp)]
             ++
	     (map ppUID depUIDs))
\end{spec}

\begin{spec}
  op initGlobalVars : ()
  def initGlobalVars =
    run {
      print "\nDeclaring globals ...";
      newGlobalVar ("BaseInfo", (None : Option RelativeUnitId, initialSpecInCat)); % as opposed to emptySpec, which doesn't contain Boolean, etc.
      newGlobalVar ("BaseNames", ([] : QualifiedIds)); % cache for quick access
      newGlobalVar ("GlobalContext", PolyMap.emptyMap);
      newGlobalVar ("LocalContext", PolyMap.emptyMap);
      newGlobalVar ("CurrentUnitId", Some {path=["/"], hashSuffix=None} : Option.Option UnitId);
      newGlobalVar ("ValidatedUnitIds",[]);
      newGlobalVar ("CommandInProgress?",false);
      return ()
    }

  op setBase : ((Option RelativeUnitId) * Spec) -> Env ()
  def setBase (baseInfo as (_, base_spec)) = 
    {
     writeGlobalVar ("BaseInfo",  baseInfo);
     setBaseNames base_spec
    }

  op getBase : Env ((Option RelativeUnitId) * Spec)
  def getBase = readGlobalVar "BaseInfo"

% op getBaseSpec : () -> Spec % declared in /Languages/MetaSlang/Specs/Printer
  def getBaseSpec() =
    let prog = {
       (optBaseUnitId,baseSpec) <- getBase;
       case optBaseUnitId of
         | None -> raise (Fail "No Base Spec")
         | Some _ -> return baseSpec
      } in
      run prog 


  op getBaseSpecUID : () -> RelativeUnitId
  def getBaseSpecUID() =
    let prog = {
       (optBaseUnitId,baseSpec) <- getBase;
       case optBaseUnitId of
         | None -> raise (Fail "No Base Spec")
         | Some uid -> return uid
      } in
      run prog 


  op clearBaseNames : Env ()
  def clearBaseNames =  writeGlobalVar ("BaseNames", [])

  op clearBaseNames_fromLisp : () -> ()
  def clearBaseNames_fromLisp () =
    run clearBaseNames

  op getBaseNames : () -> QualifiedIds * QualifiedIds
  def getBaseNames () =
    let prog = {x <- readGlobalVar "BaseNames"; 
		return x}
    in
      run prog

  op setBaseNames : Spec -> Env ()
  def setBaseNames base_spec =
    let base_sort_names = 
        foldriAQualifierMap (fn (q, id, _, names) ->
			     cons (Qualified(q, id), names))
	                    [mkQualifiedId("Boolean", "Boolean"),
			     mkUnQualifiedId "Boolean"] 
			    base_spec.sorts
    in
    let base_op_names = 
        foldriAQualifierMap (fn (q, id, _, names) ->
			     cons (Qualified(q, id), names))
	                    [] 
			    base_spec.ops
    in			    
    let base_names = (base_sort_names, base_op_names) in			   
    writeGlobalVar ("BaseNames", base_names)  % cache for quick access

  op setBaseNames_fromLisp : () -> ()
  def setBaseNames_fromLisp () =
    let prog = {(_, base_spec) <- getBase;
		setBaseNames base_spec}
    in 
      run prog

  op showGlobalContext : Env String
  def showGlobalContext = {
      globalContext <- readGlobalVar "GlobalContext";
      return (ppFormat (ppMap (fn unitId -> ppString (showUID unitId)) ppValueInfo globalContext))
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

  op bindInGlobalContext : UnitId -> ValueInfo -> Env ()
  def bindInGlobalContext unitId value = {
      globalContext <- getGlobalContext;
      setGlobalContext (update globalContext unitId value)
    }

  op lookupInGlobalContext : UnitId -> Env (Option ValueInfo)
  def lookupInGlobalContext unitId = {
      globalContext <- getGlobalContext;
      return (evalPartial globalContext unitId)
    }

  op removeFromGlobalContext : UnitId -> Env ()
  def removeFromGlobalContext unitId = {
      globalContext <- getGlobalContext;
      setGlobalContext (remove globalContext unitId)
    }

  op cleanupGlobalContext : Env ()
  def cleanupGlobalContext =
    {lastCommandAborted? <- readGlobalVar "CommandInProgress?";
     if ~ lastCommandAborted? then return ()
     else
       { gCtxt <- getGlobalContext;
	 setGlobalContext (mapPartial (fn x as (val,_,_) ->
				       case val of
					 | InProcess -> None
					 | _ -> Some x)
		           gCtxt)
       };
     writeGlobalVar("CommandInProgress?",true)}
\end{spec}

The local context is where "let" bindings are deposied

\begin{spec}
  op bindInLocalContext : RelativeUID -> ValueInfo -> Env ()
  def bindInLocalContext relativeUnitId value = {
      localContext <- readGlobalVar "LocalContext";
      writeGlobalVar ("LocalContext", update localContext relativeUnitId value)
    }

  op lookupInLocalContext : RelativeUID -> Env (Option ValueInfo)
  def lookupInLocalContext relativeUnitId = {
      localContext <- readGlobalVar "LocalContext";
      return (evalPartial localContext relativeUnitId)
    }

  op showLocalContext : Env String
  def showLocalContext = {
      localContext <- readGlobalVar "LocalContext";
      return (ppFormat (ppMap ppRelativeUID ppValueInfo localContext))
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
while there is a transition from names with "UnitId" to "UnitId".

\begin{spec}
  op getCurrentUID : Env UnitId
  def getCurrentUID = getCurrentUnitId

  op setCurrentUID : UnitId -> Env ()
  def setCurrentUID = setCurrentUnitId

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
  op  validatedUID? : UnitId -> Env Boolean
  def validatedUID? = validatedUnitId?

  op setValidatedUID : UnitId -> Env ()
  def setValidatedUID = setValidatedUnitId

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
