\section{Specware toplevel}

Synchronized with r1.11 SW4/Languages/SpecCalculus/Semantics/Specware.sl

It seems clear now that some of specs that make up the calculus need
some amount of refactoring.

\begin{spec}
Specware qualifying spec {
  import Evaluate/Term 
  import Environment 
  import SpecPath
  import ../../MetaSlang/Specs/PosSpec     % for pos0
  import ../AbstractSyntax/Printer % for showUI
\end{spec}

The following is what starts Specware. It initializes the state and
enters the read/eval/print loop. 

I would like to remove the dummy argument from the following but
then it seems to be executed at compile time ... and fails
immediately. Perhaps it won't be a problem when the bootstrap
changes and when the toplevel loop actually does something.

This is not used at present.

\begin{spec}
  op runSpecware : () -> ()
  def runSpecware () =
    case catch toplevelLoop toplevelHandler initialSpecwareState of
      | (Ok val,_)      -> fail "Specware toplevel loop terminated unexpectedly"
      | (Exception _,_) -> fail "Specware toplevel handler failed"
\end{spec}

For the near term, we have a variation of the above which evaluates
a given URI without looping.

evaluateTerm has the side effect of parsing, loading, and
caching the unit referenced by the uri, plus all the units that unit
depends on.  

Roadmap:
evaluateTerm calls evaluateURI, which calls searchFileSystemForURI,
which calls loadFile, which calls evaluateTerm on expressions parsed.

In all of the following, we set the initial value of the currentURI to
the current directory suffixed with "/.". The current URI is used to resolve
relative URI references. These are URIs that do no begin with "/". Setting
the current URI in this way means that the user can provide a top level
relative path. If a relative path is given at the toplevel, then the canonical 
path is obtained by discarding the "." in the current URI and appending
the relative path. See URI.sl. In fact any non-empty string would do
in place of ".".

\begin{spec}
  op runSpecwareURI : String -> ()
  def runSpecwareURI path = 
    let run = {
      currentURI <- pathToCanonicalURI ".";
      setCurrentURI currentURI;
      uri <- pathToRelativeURI (removeSWsuffix path); 
      evaluateURI pos0 uri;
      return ()
    } in
    case catch run toplevelHandler initialSpecwareState of
      | (Ok val,_) -> ()
      | (Exception _,_) -> fail "Specware toplevel handler failed"
\end{spec}

We provide two functions (callable from the Lisp read-eval-print loop)
that invoke the corresponding evaluation functions for the Spec Calculus.
The first just evaluates a URI. The second evaluates a URI and then
compiles the resulting specification to lisp.

\begin{spec}
  op evaluateURI_fromLisp : String -> ()
  def evaluateURI_fromLisp path = 
    let run = {
      restoreSavedSpecwareState;
      currentURI <- pathToCanonicalURI ".";
      setCurrentURI currentURI;
      uri <- pathToRelativeURI (removeSWsuffix path); 
      evaluateURI pos0 uri;
      saveSpecwareState
    } in
    case catch run toplevelHandler ignoredState of
      | (Ok val,_) -> ()
      | (Exception _,_) -> fail "Specware toplevel handler failed"
\end{spec}

\begin{spec}
  op evaluatePrint_fromLisp : String -> ()
  def evaluatePrint_fromLisp path = 
    let run = {
      restoreSavedSpecwareState;
      currentURI <- pathToCanonicalURI ".";
      setCurrentURI currentURI;
      uri <- pathToRelativeURI (removeSWsuffix path); 
      evaluatePrint (URI uri, pos0);
      saveSpecwareState
    } in
    case catch run toplevelHandler ignoredState of
      | (Ok val,_) -> ()
      | (Exception _,_) -> fail "Specware toplevel handler failed"
\end{spec}

The following corresponds to the :show command.

\begin{spec}
  op listLoadedUnits : () -> ()
  def listLoadedUnits () = 
    let run = {
      restoreSavedSpecwareState;
      globalContext <- getGlobalContext;
      uriList <-
        return (foldMap
          (fn lst -> fn dom -> fn cod -> Cons (dom, lst)) [] globalContext);
      print (ppFormat (ppSep ppNewline (map ppURI uriList)));
      saveSpecwareState     % shouldn't change anything
    } in
    case catch run toplevelHandler ignoredState of
      | (Ok val,_) -> ()
      | (Exception _,_) -> fail "Specware toplevel handler failed"
\end{spec}

\begin{spec}
  op evaluateLispCompile_fromLisp : String * Option String -> ()
  def evaluateLispCompile_fromLisp (path,targetFile) = 
    let target =
      case targetFile of
        | None -> None
        | Some name -> Some (maybeAddSuffix name ".lisp") in
    let run = {
      restoreSavedSpecwareState;
      currentURI <- pathToCanonicalURI ".";
      setCurrentURI currentURI;
      uri <- pathToRelativeURI (removeSWsuffix path); 
      spcInfo <- evaluateURI pos0 uri;
      evaluateLispCompile (spcInfo,(URI uri,pos0), target);
      saveSpecwareState
    } in
    case catch run toplevelHandler ignoredState of
      | (Ok val,_) -> ()
      | (Exception _,_) -> fail "Specware toplevel handler failed"
\end{spec}

When the lisp file for Specware is compiled and loaded, the following
will initialize a lisp variable holding the initial state for the
Specware environment. Subsequent invocations of the evaluate functions
above, retrieve and restore the saved state, do some work, and save the
state again in the lisp variable.

\begin{spec}
  op initializeSavedSpecwareState : ()
  def initializeSavedSpecwareState = 
    case saveSpecwareState initialSpecwareState of
      | (Ok val,_) -> toScreen "Initializing Specware state ..."
      | (Exception _,_) -> fail "initializeSavedSpecwareState failed"

  op ignoredState : State
  def ignoredState = initialSpecwareState
\end{spec}

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

\begin{spec}
  op toplevelLoop : SpecCalc.Env ()
  def toplevelLoop = return ()
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
  op toplevelHandler : Exception -> SpecCalc.Env ()
  def toplevelHandler except =
    {cleanupGlobalContext;		% Remove InProcess entries
     saveSpecwareState;			% So work done before error is not lost
     let message = % "Uncaught exception: " ++
       (case except of
         | Fail str -> "Fail: " ^ str
         | SpecError (position,msg) ->
               "Error in specification: "
             ^ msg
             ^ " at "
             ^ (showPosition position)
         | DiagError (position,msg) ->
               "Diagram error: "
             ^ msg
             ^ " at "
             ^ (showPosition position)
         | ParserError fileName ->
               "Syntax error: file "
             ^ fileName
         | CircularDefinition uri ->
               "Circular definition: " ^ showURI uri
         | SyntaxError msg ->
               "Syntax error: "
             ^ msg
         | URINotFound (position,uri) ->
               "Unknown unit error: "
             ^ (showRelativeURI uri)
             ^ (if position = pos0 then
                  ""
                else
                  (" referenced from " ^ (showPosition position)))
         | TypeCheck (position,str) ->
               "Type error: "
             ^ str
             ^ (if position = pos0 then
                  ""
                else
                  (" referenced from " ^ (showPosition position)))
         %% OldTypeCheck is a temporary hack to avoid gratuitous 0.0-0.0 for position
         | OldTypeCheck str ->
               "Type errors:\n"
             ^ str
         | Unsupported (position,str) ->
               "Unsupported operation: "
             ^ str
             ^ " at "
             ^ (showPosition position)
         | _ -> 
               "Unknown exception" 
             ^ (System.toString except))
     in
       if specwareWizard? then
         fail message
       else
         print message}
\end{spec}

These are hooks to handwritten function that save and restore the
Specware state in a lisp environment Successive invocations of the
evaluate functions above retrieve the save state, do some work and then
save it. In this way, the work done to load, elaborate and store specs
in the Specware environment, is saved.

\begin{spec}
  op saveSpecwareState: SpecCalc.Env ()
  op restoreSavedSpecwareState: SpecCalc.Env ()
\end{spec}

This doesn't belong here. Perhaps it belongs in the instance
of the MetaSlang terms used for parsing.

\begin{spec}
  op showPosition : Position -> String
  def showPosition (p1,p2) = 
    let def printPos (l,r) = (Nat.toString l) ^ "." ^ (Nat.toString r) in
    (printPos p1) ^ "-" ^ (printPos p2)
\end{spec}

\begin{spec}
}
\end{spec}
