(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)


%% Beginning to factor MetaSlang bootstrap engine out from general Specware product
%% Specware   = Bootstrap + OtherStuff
%% Bootstrap  = basic MetaSlang and SpecCalculus, plus Lisp code generation
%% OtherStuff = Prover, Java code generation, C code generation, Interpreter, XML, etc.

%% Bootstap and non-bootstrap things are still rather intertwined
%% in the source tree, but this is a start towards clarification.

Specware qualifying spec
  import Evaluate/Term 
  import Evaluate/Base 
  import Environment 
  import SpecPath
  import ../../MetaSlang/Specs/Position

  %% The following is what starts Specware. It initializes the state and
  %% enters the read/eval/print loop. 
  %% 
  %% I would like to remove the dummy argument from the following but
  %% then it seems to be executed at compile time ... and fails
  %% immediately. Perhaps it won't be a problem when the bootstrap
  %% changes and when the toplevel loop actually does something.
  %% 
  %% This is not used at present.
  %% 
  %%   op runSpecware : () -> Bool
  %%   def runSpecware () =
  %%     case run (catch toplevelLoop toplevelHandler) of
  %%       | (Ok val,_)      -> fail "Specware toplevel loop terminated unexpectedly"
  %%       | (Exception _,_) -> fail "Specware toplevel handler failed"
  %% 
  %% For the near term, we have a variation of the above which evaluates
  %% a given UnitId without looping.
  %% 
  %% evaluateTerm has the side effect of parsing, loading, and
  %% caching the unit referenced by the unitId, plus all the units that unit
  %% depends on.  
  %% 
  %% Roadmap:
  %% evaluateTerm calls evaluateUID, which calls searchFileSystemForUID,
  %% which calls loadFile, which calls evaluateTerm on expressions parsed.
  %% 
  %% In all of the following, we set the initial value of the currentUID to
  %% the current directory suffixed with "/.". The current UnitId is used to resolve
  %% relative UnitId references. These are UIDs that do no begin with "/". Setting
  %% the current UnitId in this way means that the user can provide a top level
  %% relative path. If a relative path is given at the toplevel, then the canonical 
  %% path is obtained by discarding the "." in the current UnitId and appending
  %% the relative path. See UnitId.sl. In fact any non-empty string would do
  %% in place of ".".
  %% 
  %% The toplevel functions that follow are all meant to be called from
  %% Lisp. They return a boolean. Returning true means the that unit has been
  %% evaluated without raising an exception. They return false only when the
  %% toplevel handler is called.
  %% 
  %% Returning a boolean is useful in order to convey whether the request
  %% to evaluate something was successful. At present, the failure of the
  %% toplevel is used within the bootstrap. If the toplevel fails, then lisp
  %% exits with a non-zero status and hence the bootstrap fails.

  op  runSpecwareUID : String -> Bool
  def runSpecwareUID path = 
    let prog = {
		cleanEnv;
		currentUID <- pathToCanonicalUID ".";
		setCurrentUID currentUID;
		path_body  <- return (removeSWsuffix path);
		unitId     <- pathToRelativeUID path_body;
		position   <- return (String (path, 
					      startLineColumnByte, 
					      endLineColumnByte path_body));
		evaluateUID position unitId;
		return true
	       } 
    in
      runSpecCommand (catch prog toplevelHandler)

  %% evaluateUnitId is designed to be called from application programs to
  %% get a unit from a unit id string.

  op Specware.evaluateUnitIdWithErrors (path: String): Option Value * List(String * Position) =
    let prog = {
		cleanEnv;
		currentUID <- pathToCanonicalUID ".";
		setCurrentUID currentUID;
		path_body  <- return (removeSWsuffix path);
		unitId     <- pathToRelativeUID path_body;
		position   <- return (String (path, 
					      startLineColumnByte, 
					      endLineColumnByte path_body));
		(val,_,_)  <- evaluateUID position unitId;
		return (Some val, [])
	       }
    in
    let def handler except =
          case except
            | TypeCheckErrors(errs, err_spc) -> return(Some(Spec err_spc), errs)
            | _ ->
          case decodeException except
            | (Some(pos, _), str) -> return(None, [(str, pos)])
            | (None, str) -> return(None, [(str, noPos)])
    in
      runSpecCommand (catch prog handler)

 % op  evaluateUnitId : String -> Option SpecCalc.Value
  def Specware.evaluateUnitId path =
    let (opt_val, errs) = evaluateUnitIdWithErrors path in
    if errs = [] then opt_val else None

  op  initializeInterpreterBase : () -> () % defined in toplevel.lisp

  op  intializeSpecware : () -> Bool
  def initializeSpecware () =
    let prog = { 
		(optBaseUnitId,_) <- getBase;
		case optBaseUnitId of
		  | None   -> 
		    { 
		     emptyGlobalContext;
		     setBaseToPath "/Library/Base";
		     return (initializeInterpreterBase ()); 
		     return true 
		    }
		  | Some _ -> return false
	       }
    in
      run (catch prog toplevelHandler)

  op  reintializeSpecware : () -> Bool
  def reinitializeSpecware () =
    let prog = {
		%% maybe following two should be invoked inseparably...
		emptyGlobalContext;
		reloadBase;
		return (initializeInterpreterBase ()); 
		return true
	       } 
    in
      run (catch prog toplevelHandler)

  op  unitIDCurrentInCache? : String -> Bool
  def unitIDCurrentInCache? path =
    let prog = {
		cleanEnv;
		currentUID <- pathToCanonicalUID ".";
		setCurrentUID currentUID;
		path_body  <- return (removeSWsuffix path);
		unitId     <- pathToRelativeUID path_body;
		checkInCache? unitId 
	       }
    in 
      runSpecCommand (catch prog toplevelHandler)

  %% We provide two functions (callable from the Lisp read-eval-print loop)
  %% that invoke the corresponding evaluation functions for the Spec Calculus.
  %% The first just evaluates a UnitId. The second evaluates a UnitId and then
  %% compiles the resulting specification to lisp.

  op evaluateUID_fromLisp (path : String) (notFromCache? : Bool) : Bool = 
    let prog = {
		cleanEnv;
		currentUID <- pathToCanonicalUID ".";
		setCurrentUID currentUID;
		path_body  <- return (removeSWsuffix path);
		unitId     <- pathToRelativeUID path_body;
		position   <- return (String (path, 
					      startLineColumnByte, 
					      endLineColumnByte path_body));
		catch { evaluateReturnUID position unitId notFromCache?; return () } 
		      (fileNameHandler unitId);
		return true
	       } 
    in
      runSpecCommand (catch prog toplevelHandler)
(*
  op parseEvaluateString (expr_str : String) (spc : Spec) : Bool = 
    let prog = {
		cleanEnv;
		currentUID <- pathToCanonicalUID ".";
		setCurrentUID currentUID;
		ptm <- parseTermFromString expr_str spc;
                tm <- (case elaboratePosTerm(ptm, spc, freePatternVars ptm) of
                         | (tm, []) -> 
                           % let _ = writeLine("qtm: "^printTermWithTypes tm) in
                           return tm
                         | (_, msgs) ->
                           raise (TypeCheckErrors msgs));
                val <- return(reduceTerm(tm, spc));
		return true
	       } 
    in
      runSpecCommand (catch prog toplevelHandler)
*)

  op fileNameHandler (unitId : RelativeUID) (except : Exception) : SpecCalc.Env () =
    case except of
      | UIDNotFound (position, badUnitId) ->
        if badUnitId = unitId && ~(hasHashSuffix? unitId) then
	  return ()
	else
	  raise except
      | _ -> raise except

  %% There is a problem with the next function. We store as part of the base
  %% info, the relative UnitId of the spec. This is so that it can be reloaded.
  %% The problem is that if the user gives a UnitId relative path, then reloading
  %% will fail if the user changes directory from the time he/she sets the base to
  %% when it is reloaded. On the other hand, if the user sets a canonical UnitId,
  %% then unless they have "/" in there SWPATH, the canonical UnitId may not be found.

  op  setBase_fromLisp : String -> Bool
  def setBase_fromLisp path =
    let prog = {
		cleanEnv;
		unitId       <- pathToCanonicalUID ".";
		setCurrentUnitId unitId;
		path_body    <- return (removeSWsuffix path);
		relative_uid <- pathToRelativeUID path_body;
		setBaseToRelativeUID relative_uid;
		return true
	       } 
    in
      runSpecCommand (catch prog toplevelHandler) 

  op  showBase_fromLisp : () -> Bool
  def showBase_fromLisp () =
    let prog = {
		(optBaseUnitId,baseSpec) <- getBase;
		case optBaseUnitId of
		  | None -> print "There is no base specification."
		  | Some relative_uid ->
		    print ("Identifier of base spec: " ^ showRelativeUID relative_uid);
		return true
	       } 
    in
      run (catch prog toplevelHandler) 

   %%% show and showx commands:

  op evaluatePrint_fromLisp (path: String, names: List QualifiedId): Bool = 
    let prog = {
		cleanEnv;
		currentUID <- pathToCanonicalUID ".";
		setCurrentUID currentUID;
		path_body  <- return (removeSWsuffix path);
		unitId     <- pathToRelativeUID path_body;
		position   <- return (String (path, 
					      startLineColumnByte, 
					      endLineColumnByte path_body));
		(if names = []
                  then {evaluatePrint ((UnitId unitId, position), false); return ()}
                  else {value <- evaluateTerm (UnitId unitId, position);
                        spc_value <- return(coerceToSpec value);
                        when (~(embed? Spec spc_value))
                          (SpecCalc.raise(Fail "not a spec."));
                        Spec spc <- return spc_value;
                        return(app (printOpTypeOrTheorem spc) names)});
		return true
	       } 
    in
      runSpecCommand (catch prog toplevelHandler) 

 op writeLine?(str: String): () =
   if str = "" then ()
     else writeLine str

 op printOpTypeOrTheorem (spc: Spec) (qid: QualifiedId): () =
   (writeLine?(printOpInSpec spc qid);
    writeLine?(printTypeInSpec spc qid);
    printPropertiesMatching spc qid)

 op printPropertiesMatching (spc: Spec) (qid: QualifiedId): () =
   app (fn prop -> writeLine(printPropertyInSpec spc prop))
     (findMatchingTheorems(spc, qid))


 op printOpInSpec (spc: Spec) (qid: QualifiedId): String =
   toString (format (AnnSpecPrinter.printWidth, ppOpInSpec spc qid))

 op ppOpInSpec (spc: Spec) (qid: QualifiedId): PrettyPrint.Pretty =
   case findMatchingOps(spc, qid) of
     | [] -> string ""
     | opinfos ->
       let context = initialize (asciiPrinter, false) in
       blockAll(0, map (fn opinfo ->
                          let num_defs = length (unpackTypedTerms opinfo.dfn) in
                          (0, blockAll(0, (ppOpDeclAux context (num_defs = 1, num_defs > 1, true, num_defs) false (opinfo, (0, []))).2)))
                     opinfos)

 op printTypeInSpec (spc: Spec) (qid: QualifiedId): String =
   toString (format (AnnSpecPrinter.printWidth, ppTypeInSpec spc qid))

 op ppTypeInSpec (spc: Spec) (qid: QualifiedId): PrettyPrint.Pretty =
   case findMatchingTypes(spc, qid) of
     | [] -> string ""
     | typeinfos ->
       let context = initialize (asciiPrinter, false) in
       blockAll(0, map (fn typeinfo ->
                          let defn? = definedType? typeinfo.dfn in
                          (0, blockAll(0, (AnnSpecPrinter.ppTypeDecl context defn? false (typeinfo, (0, []))).2)))
                     typeinfos)

 op printPropertyInSpec (spc: Spec) (prop: Property): String =
   toString (format (AnnSpecPrinter.printWidth, ppPropertyInSpec spc prop))

 op ppPropertyInSpec (spc: Spec) (prop: Property): PrettyPrint.Pretty =
   let context = initialize (asciiPrinter, false) in
   (ppProperty context (0, prop)).2

  %% The following corresponds to the :show command.

  op  listLoadedUnits : () -> Bool
  def listLoadedUnits () = 
    let prog = {
		globalContext <- getGlobalContext;
		uidList       <- return (foldMap (fn lst -> fn dom -> fn _ (* cod *) -> 
						  Cons (dom, lst)) 
					         [] 
						 globalContext);
		print (ppFormat (ppSep ppNewline 
				 (List.map (fn unitId -> 
					    ppString (uidToString unitId)) 
				           uidList)));
		return true
	       } 
    in
      run (catch prog toplevelHandler) 

  op  evaluateLispCompile_fromLisp : String * Option String * Bool -> Bool
  def evaluateLispCompile_fromLisp (path,targetFile,slicing?) = 
    let target =
      case targetFile of
        | None -> None
        | Some name -> Some (maybeAddSuffix name ".lisp") in
    let prog = {
		cleanEnv;
		currentUID <- pathToCanonicalUID ".";
		setCurrentUID currentUID;
		path_body  <- return (removeSWsuffix path);
		unitId     <- pathToRelativeUID path_body;
		position   <- return (String (path, 
					      startLineColumnByte, 
					      endLineColumnByte path_body));
		spcInfo    <- evaluateUID position unitId;
		evaluateLispCompile (spcInfo, (UnitId unitId, position), target, slicing?);
		return true
	       }
    in
      runSpecCommand (catch prog toplevelHandler) 

  %% Second argument is interpreted as spec containing options for the code generation.

  op  evaluateLispCompileLocal_fromLisp : String * Option String -> Bool
  def evaluateLispCompileLocal_fromLisp (path,targetFile) = 
    let target =
      case targetFile of
        | None -> None
        | Some name -> Some (maybeAddSuffix name ".lisp") in
    let prog = {
		cleanEnv;
		currentUID <- pathToCanonicalUID ".";
		setCurrentUID currentUID;
		path_body  <- return (removeSWsuffix path);
		unitId     <- pathToRelativeUID path_body;
		pos        <- return (String (path, 
					      startLineColumnByte, 
					      endLineColumnByte path_body));
		spcInfo    <- evaluateUID pos unitId;
		evaluateLispCompileLocal (spcInfo, (UnitId unitId, pos), target);
		return true
	       } 
    in
      runSpecCommand (catch prog toplevelHandler)


  op makeScript_fromLisp(trans: TransformExpr, spc: Spec): Option Script =
    let prog = {scr <- makeScript spc trans;
                return(Some scr)} 
    in
      run (catch prog toplevelHandlerOption)

  %% getOptSpec returns Some spc if the given string evaluates to a spec

  %op Specware.getOptSpec : Option String -> Option Spec
  def Specware.getOptSpec optpath =
    case optpath of
      | None -> None
      | Some path ->
        let prg = {
		   resetGlobals;
		   currentUID <- pathToCanonicalUID ".";
		   setCurrentUID currentUID;
		   path_body  <- return (removeSWsuffix path);
		   unitId     <- pathToRelativeUID path_body;
		   position   <- return (String (path,
						 startLineColumnByte, 
						 endLineColumnByte path_body));
		   (value,_,_):ValueInfo <- evaluateUID position unitId;
		   return (case coerceToSpec value of
			     | Spec spc -> Some spc
			     | _ -> None)
		  }
	in
	  run (catch prg toplevelHandlerOption)

  %% removeSWsuffix could be generalized to extractUIDpath
  %% and then the code to create the position would use the
  %% start and end positions of path_body within path

  op  removeSWsuffix : String -> String
  def removeSWsuffix path =
    case (reverse (explode path)) of
      | #w :: #s :: #. :: rest -> implode (reverse rest)
      | _ -> path

  %% Maybe this belongs in Evaluate/Generate.sw and applied to
  %% in all cases where a Generate term is evaluated rather
  %% than only at toplevel invocations?

  op  maybeAddSuffix : String -> String -> String
  def maybeAddSuffix path suffix =
     %% Scan for period from end of string back until
     %% first slash is encountered.
    case foldl (fn (result, char) ->
	        case result of
                  | Some _ -> result 
                  | _ ->
                    case char of
                      | #.  -> Some true
                      | #/  -> Some false
                      | #\\ -> Some false
                      | _   -> result)
               None
               (reverse (explode path))
     of
      | Some true -> path
      | _         -> path ^ suffix


  %% Eventually, this will be a read/eval/print loop for Specware.
  %% At present we are using the Lisp interface and the following is
  %% not used.
  %% 
  %% Right now this returns a boolean to be consistent with the hander.
  %% When written, this should never return. All the Bool's should
  %% become unit types.

  op  toplevelLoop : SpecCalc.Env Bool
  def toplevelLoop = return true

  %% This is the toplevel exception handler. Eventually, when we have our own
  %% read-eval-print loop, this will be used only for uncaught exceptions. For
  %% now, this handles all exceptions, For all exceptions except Fail, it
  %% constructs and prints a message.  For Fail exceptions, it calls fail to
  %% enter the Lisp debugger as this indicates an internal (Specware) error.
  %% 
  %% Note that the toplevel handler is now monomorphic. All toplevel
  %% functions have unit type (within the monad). It seems to make
  %% sense that no toplevel functions return anything.

  %op Specware.toplevelHandler : Exception -> SpecCalc.Env Bool % See Signature.sw
  def Specware.toplevelHandler except =
    {
     cleanupGlobalContext;		% Remove InProcess entries
     message <- return (printException except);
     return (gotoErrorLocation except);
     if specwareWizard? then
       fail message
     else
       print message;
     return false
    }

  %op Specware.toplevelHandlerOption : [a] Exception -> SpecCalc.Env (Option a)% See Signature.sw
  def [a] Specware.toplevelHandlerOption (except) : SpecCalc.Env (Option a) =
    {
     cleanupGlobalContext;		% Remove InProcess entries
     message <- return (printException except);
     return (gotoErrorLocation except);
     if specwareWizard? then
       fail message
     else
       print (message);
     return None
    }

  op stringErrorByte: Ref Int = mkRef(-1)

  op  gotoErrorLocation : Exception -> ()
  def gotoErrorLocation except = 
   case getFirstErrorLocation except of
     | Some (File (file, (left_line, left_column, left_byte), right)) ->   
       IO.gotoFilePosition (file, left_line, left_column)
     | Some (String (_, (_, _, error_byte), _)) -> (stringErrorByte := error_byte)
     | _ -> ()

  op  getFirstErrorLocation : Exception -> Option Position
  def getFirstErrorLocation except =
    case except of
      | Unsupported      (position,_) -> Some position
      | UIDNotFound      (position,_) -> Some position
      | FileNotFound     (position,_) -> Some position
      | SpecError        (position,_) -> Some position
      | MorphError       (position,_) -> Some position
      | DiagError        (position,_) -> Some position
      | ColimitError     (position,_) -> Some position
      | TranslationError (_,position) -> Some position
      | TypeCheck        (position,_) -> Some position
      | Proof            (position,_) -> Some position
      | TransformError   (position,_) -> Some position
      | TypeCheckErrors  (errs, err_spc) ->
        (case getFirstRealPosition errs of
           | None ->
             (case errs of
                | [] -> None
                | (_, position)::_ -> Some position)
           | o_pos -> o_pos)
      | _ -> None

  op  getFirstRealPosition : List (String * Position) -> Option Position
  def getFirstRealPosition errs =
    case errs of
      | [] -> None
      | (err, pos) :: rest ->
        (case pos of
           | File (file, (left_line, left_column, left_byte), right) ->
             if left_line = 0 && left_column = 0 then
	       getFirstRealPosition rest
	     else 
	       Some pos
           | _ -> getFirstRealPosition rest)
 
   %% Ensure everything is clean at beginning of command processing

  % op  Specware.cleanEnv : SpecCalc.Env ()
  def Specware.cleanEnv =
    {
     resetGlobals;
     ensureBase;
     cleanupGlobalContext
    }
     
  op  ensureBase : SpecCalc.Env ()
  def ensureBase =
    {
     (optBaseUnitId,_) <- getBase;
     (case optBaseUnitId of
	| None   -> setBaseToPath "/Library/Base"
	| Some _ -> return ())
    }

  % op  Specware.runSpecCommand : [a] SpecCalc.Env a -> a
  def Specware.runSpecCommand f =
    let val = run f in
    %% CommandInProgress? is used to detect (by cleanupGlobalContext currently) whether command aborted
    let _ = MonadicStateInternal.writeGlobalVar ("CommandInProgress?", false) in
    val

end-spec
