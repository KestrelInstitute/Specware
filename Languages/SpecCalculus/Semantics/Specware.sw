\section{Specware toplevel}

It seems clear now that some of specs that make up the calculus need
some amount of refactoring.

\begin{spec}
Specware qualifying spec
  import Evaluate/Term 
  import Evaluate/Base 
  import Environment 
  import SpecPath
  import ../../MetaSlang/Specs/Position
  import ../../MetaSlang/Transformations/Interpreter % for MSInterpreter.eval
  import ../AbstractSyntax/Printer % for showUI
  import /Languages/XML/XML        % for XML I/O

\end{spec}

The following is what starts Specware. It initializes the state and
enters the read/eval/print loop. 

I would like to remove the dummy argument from the following but
then it seems to be executed at compile time ... and fails
immediately. Perhaps it won't be a problem when the bootstrap
changes and when the toplevel loop actually does something.

This is not used at present.

begin{spec}
  op runSpecware : () -> Boolean
  def runSpecware () =
    case run (catch toplevelLoop toplevelHandler) of
      | (Ok val,_)      -> fail "Specware toplevel loop terminated unexpectedly"
      | (Exception _,_) -> fail "Specware toplevel handler failed"
end{spec}

For the near term, we have a variation of the above which evaluates
a given UnitId without looping.

evaluateTerm has the side effect of parsing, loading, and
caching the unit referenced by the unitId, plus all the units that unit
depends on.  

Roadmap:
evaluateTerm calls evaluateUID, which calls searchFileSystemForUID,
which calls loadFile, which calls evaluateTerm on expressions parsed.

In all of the following, we set the initial value of the currentUID to
the current directory suffixed with "/.". The current UnitId is used to resolve
relative UnitId references. These are UIDs that do no begin with "/". Setting
the current UnitId in this way means that the user can provide a top level
relative path. If a relative path is given at the toplevel, then the canonical 
path is obtained by discarding the "." in the current UnitId and appending
the relative path. See UnitId.sl. In fact any non-empty string would do
in place of ".".

The toplevel functions that follow are all meant to be called from
Lisp. They return a boolean. Returning true means the that unit has been
evaluated without raising an exception. They return false only when the
toplevel handler is called.

Returning a boolean is useful in order to convey whether the request
to evaluate something was successful. At present, the failure of the
toplevel is used within the bootstrap. If the toplevel fails, then lisp
exists with a non-zero status and hence the bootstrap fails.

\begin{spec}
  op runSpecwareUID : String -> Boolean
  def runSpecwareUID path = 
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      evaluateUID position unitId;
      return true
    } in
    runSpecCommand (catch prog toplevelHandler)
\end{spec}

evaluateUnitId is designed to be called from application programs to
get a unit from a unit id string.

\begin{spec}
  op evaluateUnitId : String -> Option SpecCalc.Value
  def evaluateUnitId path =
    let
      % TODO: do we really intend to ignore exceptions here?
      % old (generates compiler warning about unused var: except):
      % def handler except =
      % case except of
      %   | _ -> return (None : Option SpecCalc.Value)
      % 
      def handler _ (* except *) =
        return (None : Option SpecCalc.Value)
    in
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      (val,_,_) <- evaluateUID position unitId;
      return (Some val)
    } in
    runSpecCommand (catch prog handler)
\end{spec}

\begin{spec}
  op initializeInterpreterBase : () -> () % defined in toplevel.lisp

  op intializeSpecware : () -> Boolean
  def initializeSpecware () =
    let prog = { (optBaseUnitId,_) <- getBase;
		 case optBaseUnitId of
		   | None   -> 
		     { 
		      emptyGlobalContext;
		      setBaseToPath "/Library/Base";
		      return (initializeInterpreterBase ()); 
		      return true }
		   | Some _ -> return false }
    in
    run (catch prog toplevelHandler)
\end{spec}

\begin{spec}
  op reintializeSpecware : () -> Boolean
  def reinitializeSpecware () =
    let prog = {
      %% maybe following two should be invoked inseparably...
      emptyGlobalContext;
      reloadBase;
      return (initializeInterpreterBase ()); 
      return true
    } in
    run (catch prog toplevelHandler)
\end{spec}

\begin{spec}
  op  unitIDCurrentInCache? : String -> Boolean
  def unitIDCurrentInCache? path =
    let prog = { cleanEnv;
		 currentUID <- pathToCanonicalUID ".";
		 setCurrentUID currentUID;
		 path_body <- return (removeSWsuffix path);
		 unitId <- pathToRelativeUID path_body;
		 checkInCache? unitId }
    in runSpecCommand (catch prog toplevelHandler)
\end{spec}



We provide two functions (callable from the Lisp read-eval-print loop)
that invoke the corresponding evaluation functions for the Spec Calculus.
The first just evaluates a UnitId. The second evaluates a UnitId and then
compiles the resulting specification to lisp.

\begin{spec}
  op evaluateUID_fromLisp : String -> Boolean
  def evaluateUID_fromLisp path = 
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      catch {
        evaluateUID position unitId;
        return ()
      } (fileNameHandler unitId);
      return true
    } in
    runSpecCommand (catch prog toplevelHandler)
\end{spec}

\begin{spec}
  op fileNameHandler : RelativeUID -> Exception -> SpecCalc.Env ()
  def fileNameHandler unitId except =
    case except of
      | UIDNotFound (position, badUnitId) ->
         if badUnitId = unitId && ~(hasHashSuffix? unitId) then
           return ()
         else
           raise except
      | _ -> raise except
\end{spec}

There is a problem with the next function. We store as part of the base
info, the relative UnitId of the spec. This is so that it can be reloaded.
The problem is that if the user gives a UnitId relative path, then reloading
will fail if the user changes directory from the time he/she sets the base to
when it is reloaded. On the other hand, if the user sets a canonical UnitId,
then unless they have "/" in there SWPATH, the canonical UnitId may not be found.

\begin{spec}
  op setBase_fromLisp : String -> Boolean
  def setBase_fromLisp path =
    let prog = {
      cleanEnv;
      unitId <- pathToCanonicalUID ".";
      setCurrentUnitId unitId;
      path_body <- return (removeSWsuffix path);
      relativeUnitId <- pathToRelativeUID path_body;
      setBaseToRelativeUnitId relativeUnitId;
      return true
    } in
    runSpecCommand (catch prog toplevelHandler) 

  op showBase_fromLisp : () -> Boolean
  def showBase_fromLisp () =
    let prog = {
      (optBaseUnitId,baseSpec) <- getBase;
      case optBaseUnitId of
        | None -> print "There is no base specification."
        | Some relativeUnitId ->
            print ("Identifier of base spec: " ^ (showRelativeUID relativeUnitId));
      return true
    } in
    run (catch prog toplevelHandler) 
\end{spec}

\begin{spec}  %%% show command
  op evaluatePrint_fromLisp : String -> Boolean
  def evaluatePrint_fromLisp path = 
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      evaluatePrint (UnitId unitId, position);
      return true
    } in
    runSpecCommand (catch prog toplevelHandler) 
\end{spec}

The following corresponds to the :show command.

\begin{spec}
  op listLoadedUnits : () -> Boolean
  def listLoadedUnits () = 
    let prog = {
      globalContext <- getGlobalContext;
      uidList <-
        return (foldMap (fn lst -> fn dom -> fn _ (* cod *) -> Cons (dom, lst)) 
		        [] 
			globalContext);
      print (ppFormat (ppSep ppNewline (map (fn unitId -> ppString (uidToString unitId)) uidList)));
      return true
    } in
    run (catch prog toplevelHandler) 
\end{spec}

\begin{spec}
  op evaluateLispCompile_fromLisp : String * Option String -> Boolean
  def evaluateLispCompile_fromLisp (path,targetFile) = 
    let target =
      case targetFile of
        | None -> None
        | Some name -> Some (maybeAddSuffix name ".lisp") in
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      spcInfo <- evaluateUID position unitId;
      evaluateLispCompile (spcInfo, (UnitId unitId, position), target);
      return true
    } in
    runSpecCommand (catch prog toplevelHandler) 
\end{spec}

Second argument is interpreted as spec containing options for the code generation.

\begin{spec}
  op evaluateLispCompileLocal_fromLisp : String * Option String -> Boolean
  def evaluateLispCompileLocal_fromLisp (path,targetFile) = 
    let target =
      case targetFile of
        | None -> None
        | Some name -> Some (maybeAddSuffix name ".lisp") in
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      pos <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      spcInfo <- evaluateUID pos unitId;
      evaluateLispCompileLocal (spcInfo, (UnitId unitId, pos), target);
      return true
    } in
    runSpecCommand (catch prog toplevelHandler)
\end{spec}

getOptSpec returns Some spc if the given string evaluates to a spec
\begin{spec}
%  op getOptSpec: Option String -> Option Spec
  def getOptSpec(optpath) =
    case optpath of
      | None -> None
      | Some path ->
      let prg = {
		  resetGlobals;
		  currentUID <- pathToCanonicalUID ".";
		  setCurrentUID currentUID;
		  path_body <- return (removeSWsuffix path);
		  unitId <- pathToRelativeUID path_body;
		  position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
		  spcInfo:ValueInfo <- evaluateUID position unitId;
		  res <- return (let (value,_,_) = spcInfo in
				 case coerceToSpec value of
				   | Spec spc -> Some spc
				   | _ -> None);
		  return res
		 }
      in
      run (catch prg toplevelHandlerOption)
\end{spec}

\begin{spec}
  op  evalDefInSpec: String * QualifiedId -> Option MSInterpreter.Value
  def evalDefInSpec(path,qid) =
    let prg = {
	       cleanEnv;
	       currentUID <- pathToCanonicalUID ".";
	       setCurrentUID currentUID;
	       path_body <- return (removeSWsuffix path);
	       unitId <- pathToRelativeUID path_body;
	       position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
	       spcInfo:ValueInfo <- evaluateUID position unitId;
	       return (let (value,_,_) = spcInfo in
		       case coerceToSpec value of
			 | Spec spc ->
			   (case AnnSpec.findTheOp (spc, qid) of
			      | Some info -> 
			        (if definedOpInfo? info then
				   let tm = firstOpDefInnerTerm info in
				   Some (MSInterpreter.eval (tm, spc))
				 else
				   None)
			      | _ -> None) % Dummy
			 | _ -> None)
	      }
      in
      runSpecCommand (catch prg toplevelHandlerOption)
\end{spec}


\begin{spec}
  op evaluateJavaGen_fromLisp : String * Option String -> Boolean
  def evaluateJavaGen_fromLisp (path,optopath) = 
    %let optspec = getOptSpec optopath in
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      spcInfo <- evaluateUID position unitId;
      evaluateJavaGen (spcInfo, (UnitId unitId, position), optopath);
      return true
    } in
    runSpecCommand (catch prog toplevelHandler) 
\end{spec}

\begin{spec}
  op evaluateUID_fromJava : String -> Boolean
  def evaluateUID_fromJava path = 
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      catch {
        evaluateUID position unitId;
        return ()
      } (fileNameHandler unitId);
      return true
    } in
    runSpecCommand (catch prog toplevelHandlerForJava)
\end{spec}

\begin{spec}
  op evaluateCGen_fromLisp : String * Option String -> Boolean
  def evaluateCGen_fromLisp (path,targetFile) = 
    let target =
      case targetFile of
        | None -> None
        | Some name -> Some (maybeAddSuffix name ".c") in
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      evaluateGenerate ("c", (UnitId unitId, position), target) position;
      return true
    } in
    runSpecCommand (catch prog toplevelHandler)
\end{spec}

\begin{spec}
  op evaluateProofGen_fromLisp : String * Option String * Boolean -> Boolean
  def evaluateProofGen_fromLisp (path,targetFile, fromObligations?) = 
    let target =
      case targetFile of
        | None -> None
        | Some name -> Some (name^".sw") in
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      spcInfo <- evaluateUID position unitId;
      evaluateProofGen (spcInfo, (UnitId unitId, position), target, fromObligations?);
      return true
    } in
    runSpecCommand (catch prog toplevelHandler) 
\end{spec}

Second argument is interpreted as spec containing options for the code generation.


\begin{spec}
  op evaluateProofGenLocal_fromLisp : String * Option String * Boolean -> Boolean
  def evaluateProofGenLocal_fromLisp (path,targetFile, fromObligations?) = 
    let target =
      case targetFile of
        | None -> None
        | Some name -> Some (name ^ ".sw") in
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      pos <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      spcInfo <- evaluateUID pos unitId;
      evaluateProofGenLocal (spcInfo, (UnitId unitId, pos), target, fromObligations?);
      return true
    } in
    runSpecCommand (catch prog toplevelHandler)
\end{spec}

removeSWsuffix could be generalized to extractUIDpath
and then the code to create the position would use the
start and end positions of path_body within path

\begin{spec}
  op removeSWsuffix : String -> String
  def removeSWsuffix path =
    case (rev (explode path)) of
      | #w :: #s :: #. ::rest -> implode (rev rest)
      | _ -> path
\end{spec}

Maybe this belongs in Evaluate/Generate.sw and applied to
in all cases where a Generate term is evaluated rather
than only at toplevel invocations?

\begin{spec}
  op maybeAddSuffix : String -> String -> String
  def maybeAddSuffix path suffix =
    if (List.member (#., explode path)) then
      path
    else
      path ^ suffix
\end{spec}

Eventually, this will be a read/eval/print loop for Specware.
At present we are using the Lisp interface and the following is
not used.

Right now this returns a boolean to be consistent with the hander.
When written, this should never return. All the Boolean's should
become unit types.

\begin{spec}
  op toplevelLoop : SpecCalc.Env Boolean
  def toplevelLoop = return true
\end{spec}

This is the toplevel exception handler. Eventually, when we have our own
read-eval-print loop, this will be used only for uncaught exceptions. For
now, this handles all exceptions, For all exceptions except Fail, it
constructs and prints a message.  For Fail exceptions, it calls fail to
enter the Lisp debugger as this indicates an internal (Specware) error.

Note that the toplevel handler is now monomorphic. All toplevel
functions have unit type (within the monad). It seems to make
sense that no toplevel functions return anything.

\begin{spec}
  % op Specware.toplevelHandler : Exception -> SpecCalc.Env Boolean % See Signature.sw
  def toplevelHandler except =
    {cleanupGlobalContext;		% Remove InProcess entries
     message <- return (printException except);
     return (gotoErrorLocation except);
     if specwareWizard? then
       fail message
     else
       print message;
     return false}

  op toplevelHandlerOption : fa(a) Exception -> SpecCalc.Env (Option a)
  def toplevelHandlerOption except =
    {cleanupGlobalContext;		% Remove InProcess entries
     message <- return (printException except);
     return (gotoErrorLocation except);
     if specwareWizard? then
       fail message
     else
       print message;
     return None}

  op gotoErrorLocation: Exception -> ()
  def gotoErrorLocation except = 
   case getFirstErrorLocation except of
     | Some (File (file, (left_line, left_column, left_byte), right)) ->   
       IO.gotoFilePosition (file, left_line, left_column)
     | _ -> ()

  op getFirstErrorLocation : Exception -> Option Position
  def getFirstErrorLocation except =
    case except of
      | Unsupported  (position,_) -> Some position
      | UIDNotFound  (position,_) -> Some position
      | FileNotFound (position,_) -> Some position
      | SpecError    (position,_) -> Some position
      | MorphError   (position,_) -> Some position
      | DiagError    (position,_) -> Some position
      | TypeCheck    (position,_) -> Some position
      | Proof        (position,_) -> Some position
      | TypeCheckErrors errs      -> getFirstRealPosition errs
      | _ -> None

  op getFirstRealPosition : List (String * Position) -> Option Position
  def getFirstRealPosition errs =
    case errs of
      | [] -> None
      | (err,pos)::rest ->
        (case pos of
           | File (file, (left_line, left_column, left_byte), right) ->
             if left_line = 0 & left_column = 0
               then getFirstRealPosition rest
              else Some pos
           | _ -> getFirstRealPosition rest)
\end{spec}

\begin{spec}
  op toplevelHandlerForJava: Exception -> SpecCalc.Env Boolean
  def toplevelHandlerForJava except =
    {cleanupGlobalContext;		% Remove InProcess entries
     % saveSpecwareState;			% So work done before error is not lost
     return (reportExceptionToJava except);
     return false}

  op reportExceptionToJava: Exception -> ()
  def reportExceptionToJava except =
    case except of
      | Unsupported  (position,msg) -> 
        reportErrorAtPosToJava(position,"Unsupported operation: " ^ msg)
      | UIDNotFound  (position,unitId) ->
        reportErrorAtPosToJava(position,"Unknown unit " ^ (showRelativeUID unitId))
      | FileNotFound (position,unitId) ->
        reportErrorAtPosToJava(position,"Unknown unit " ^ (showRelativeUID unitId))
      | SpecError    (position,msg) ->
        reportErrorAtPosToJava(position,"Error in specification: " ^ msg)
      | MorphError   (position,msg) ->
        reportErrorAtPosToJava(position,"Error in morphism: " ^ msg)
      | DiagError    (position,msg) ->
        reportErrorAtPosToJava(position,"Diagram error: " ^ msg)
      | TypeCheck    (position,msg) ->
        reportErrorAtPosToJava(position,"Type error: " ^ msg)
      | Proof        (position,msg) ->
        reportErrorAtPosToJava(position,"Proof error: " ^ msg)
      | TypeCheckErrors errs      -> reportTypeErrorsToJava errs
      | _ -> reportErrorToJava("",0,0,printException except)

  op reportTypeErrorsToJava : List(String * Position) -> ()
  def reportTypeErrorsToJava errs =
    app (fn (msg,pos) -> reportErrorAtPosToJava(pos,msg)) errs

  op reportErrorAtPosToJava: Position * String -> ()
  def reportErrorAtPosToJava(pos,msg) =
    case pos of
      | File (file, (left_line, left_column, left_byte), right) ->
        reportErrorToJava(file,left_line,left_column,msg)
      | _ -> reportErrorToJava("",0,0,msg)

  op reportErrorToJava: String * Nat * Nat * String -> ()
  %% redefined in /Gui/src/Lisp/init-java-connection.lisp
  def reportErrorToJava (file, line, col, msg) =
    let _ = toScreen ("call to reportErrorToJava, but java connection not initialized: ") in
    let _ = toScreen (" File:   " ^ file)              in
    let _ = toScreen (" Line:   " ^ Nat.toString line) in  
    let _ = toScreen (" Column: " ^ Nat.toString col)  in
    let _ = toScreen (" Msg:    " ^ msg)               in
    ()
 
  %% Ensure everything is clean at beginning of command processing
  op  cleanEnv: SpecCalc.Env ()
  def cleanEnv =
    {resetGlobals;
     ensureBase;
     cleanupGlobalContext}
     
  op  ensureBase: SpecCalc.Env ()
  def ensureBase =
    {(optBaseUnitId,_) <- getBase;
     (case optBaseUnitId of
	| None   -> setBaseToPath "/Library/Base"
	| Some _ -> return ())}

  op  runSpecCommand: fa(a) SpecCalc.Env a -> a
  def runSpecCommand f =
    let val = run f in
    %% CommandInProgress? is used to detect (by cleanupGlobalContext currently) whether command aborted
    let _ = MonadicStateInternal.writeGlobalVar("CommandInProgress?",false) in
    val

\end{spec}

\begin{spec}
endspec
\end{spec}
