(* {The Specware Environment}

The environment is the monadic context for the spec calculus interpreter. 
The monad handles, state, (very primitive) IO, and exceptions. In principle,
the datatype should be defined compositionally but this isn't supported as
yet. In the meantime, the monad and the operations for dealing with it
are described monolithically ... everything appears below. Ugh!
*)

SpecCalc qualifying spec
  import ../AbstractSyntax/Types   
  import ../AbstractSyntax/Printer
  import Monad

(*
The Monad/Base spec supplies declarations of
ths type Monad and the operators monadSeq, monadBind and return. 

All terms in the calculus have a value.  A value is a specification, a
diagram, morphism etc.  We combine them with a coproduct.
*)
  type Info

(*
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
*)

  type GlobalContext = PolyMap.Map (UnitId, ValueTermInfo)
  type LocalContext  = PolyMap.Map (RelativeUID, ValueTermInfo)
  % type State = GlobalContext * LocalContext * Option UnitId * ValidatedUIDs

  %% ppValueInfo uses Printer, which uses Types,
  %% so this can't easily be defined in Types.sw
  op ppValueInfo : ValueTermInfo -> Doc
  def ppValueInfo (value,timeStamp,depUIDs,_) =
    ppConcat([ppString "[Value: ",
	      ppValue value,
	      ppString "]",
	      ppNewline,
	      ppString "[Timestamp: ",
              ppString (Nat.toString timeStamp),
	      ppString "]",
	      ppNewline,
	      ppString "[Dependencies: "]
             ++
	     (foldl (fn (uid, docs) -> 
		     case docs of
		       | [] -> [ppUID uid]
		       | _  -> docs ++ [ppNewline, ppUID uid])
	            [] 
		    depUIDs)
	     ++
	     [ppString "]"])

(*

*)
  op initGlobalVars : ()
  def initGlobalVars =
    run {
      print "\nDeclaring globals ...";
      newGlobalVar ("BaseInfo", (None : Option RelativeUID, initialSpecInCat)); % as opposed to emptySpec, which doesn't contain Boolean, etc.
      newGlobalVar ("BaseNames", ([] : QualifiedIds)); % cache for quick access
      newGlobalVar ("GlobalContext", PolyMap.emptyMap);
      newGlobalVar ("LocalContext", PolyMap.emptyMap);
      newGlobalVar ("CurrentUnitId", Some {path=["/"], hashSuffix=None} : Option.Option UnitId);
      newGlobalVar ("ValidatedUnitIds",[]);
      newGlobalVar ("CommandInProgress?",false);
      newGlobalVar ("PrismChoices",[]);
      newGlobalVar ("Counter",0);
      return ()
    }

  op setBase : ((Option RelativeUID) * Spec) -> Env ()
  def setBase (baseInfo as (_, base_spec)) = 
    {
     writeGlobalVar ("BaseInfo",  baseInfo);
     setBaseNames base_spec
    }

  op getBase : Env ((Option RelativeUID) * Spec)
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


  op getBaseSpecUID : () -> RelativeUID
  def getBaseSpecUID() =
    let prog = {
       (optBaseUnitId,baseSpec) <- getBase;
       case optBaseUnitId of
         | None -> raise (Fail "No Base Spec")
         | Some uid -> return uid
      } in
      run prog 

  op  getBaseImportSpec : () -> Spec
  def getBaseImportSpec() =
    let prog = {
      (optBaseUnitId,baseSpec) <- getBase;
      case optBaseUnitId of
       | None -> raise (Fail "No Base Spec")
       | Some uid -> return (baseSpec << {elements = [Import((UnitId uid,noPos),baseSpec,baseSpec.elements)]})
      } in
    run prog 

  op  importOfSpec: Option RelativeUID * Spec -> Spec
  def importOfSpec(optUnitId,spc) =
    spc << {elements = case optUnitId of
			 | None -> []
			 | Some unitid ->
	                   [Import((UnitId unitid,noPos), spc, spc.elements)]}

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

  op bindInGlobalContext : UnitId -> ValueTermInfo -> Env ()
  def bindInGlobalContext unitId value = {
      globalContext <- getGlobalContext;
      setGlobalContext (update globalContext unitId value)
    }

  op lookupInGlobalContext : UnitId -> Env (Option ValueTermInfo)
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
	 setGlobalContext (mapPartial (fn x as (val,_,_,_) ->
				       case val of
					 | InProcess -> None
					 | _ -> Some x)
		           gCtxt)
       };
     writeGlobalVar("CommandInProgress?",true)}
(*

The local context is where "let" bindings are deposied

*)
  op bindInLocalContext : RelativeUID -> ValueInfo -> Env ()
  def bindInLocalContext relative_uid value = {
      localContext <- readGlobalVar "LocalContext";
      writeGlobalVar ("LocalContext", update localContext relative_uid value)
    }

  op lookupInLocalContext : RelativeUID -> Env (Option ValueInfo)
  def lookupInLocalContext relative_uid = {
      localContext <- readGlobalVar "LocalContext";
      return (evalPartial localContext relative_uid)
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
(*

When evaluating new locally scoped bindings, we need to be able to
retrieve the local context and restore it later. Also, when we evaluate
a new UnitId, we must abandon the local context in the UnitId.

*)
  op getLocalContext : Env LocalContext
  def getLocalContext = readGlobalVar "LocalContext"

  op setLocalContext : LocalContext -> Env ()
  def setLocalContext newLocalContext = writeGlobalVar ("LocalContext",newLocalContext)

  op clearLocalContext : Env ()
  def clearLocalContext = setLocalContext emptyMap
(*

The corresponding retrieve and set the current UnitId. They are duplicated
while there is a transition from names with "UnitId" to "UnitId".

*)
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

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

  % retrieves a fresh natural number (used for variable name generation in proof checker)
  op freshNat : Env Nat
  def freshNat = {
      n <- readGlobalVar "Counter";
      writeGlobalVar ("Counter", n+1);
      return n
    }

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  type PrismChoice  = {uid : UnitId, n : Nat, max : Nat}
  type PrismChoices = List PrismChoice

  op  getPrismChoices : Env PrismChoices
  def getPrismChoices = 
    readGlobalVar "PrismChoices"

  op  setPrismChoices : PrismChoices -> Env ()
  def setPrismChoices ps = 
    writeGlobalVar ("PrismChoices", ps)

  op  initialPrismChoice : UnitId * Nat -> PrismChoice
  def initialPrismChoice (uid, max) =
    %% indexing is [0 .. n)
    {uid = uid, n = 0, max = max}

  op  incrPrismChoices : PrismChoices -> Option PrismChoices
  def incrPrismChoices pcs =
    %% compute next set of indices in cartesian product
    %% return None when past end of all possiblities
    %% indexing is [0 .. n)
    case pcs of
      | [] -> None
      | pc :: pcs ->
        let n = pc.n + 1 in
	if n < pc.max then
	  %% normal case
	  Some (cons (pc << {n = n}, pcs))
	else
	  %% "carry" case
	  case incrPrismChoices pcs of
	    | Some pcs -> Some (cons (pc << {n = 0}, pcs))
	    | None -> None

(*

I'm not sure the following is necessary. It is called at the start of
the toplevel functions. 

*)
  op resetGlobals : Env ()
  def resetGlobals =
      % writeGlobalVar ("LocalContext", PolyMap.emptyMap);
      % writeGlobalVar ("CurrentUnitId", Some {path=["/"], hashSuffix=None} : Option.Option UnitId);
      % writeGlobalVar ("PrismChoices", []);
      writeGlobalVar ("ValidatedUnitIds",[])
endspec

