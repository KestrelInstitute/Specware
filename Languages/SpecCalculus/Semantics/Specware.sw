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
      uri <- pathToRelativeURI path; 
      evaluateTerm (URI uri,pos0)
    } in
    case catch run toplevelHandler initialSpecwareState of
      | (Ok val,_) -> ()
      | (Exception _,_) -> fail "Specware toplevel handler failed"
\end{spec}

The following is designed to allow for use by a lisp read-eval-print loop.

\begin{spec}
  op runSpecwareURIenv : String * State -> (SpecCalc.Result Value) * State
  def runSpecwareURIenv (path,specwareState) = 
    let run = {
      currentURI <- pathToCanonicalURI ".";
      setCurrentURI currentURI;
      uri <- pathToRelativeURI path; 
      evaluateTerm (URI uri,pos0)
    } in
    catch run toplevelHandler specwareState
\end{spec}

An experimental alternative to the above.

\begin{spec}
  op removeSWsuffix : String -> String
  def removeSWsuffix path =
    case (rev (explode path)) of
      | #w :: #s :: #. ::rest -> implode (rev rest)
      | _ -> path
\end{spec}

\begin{spec}
  op evaluateURIfromLisp : String -> ()
  def evaluateURIfromLisp path = 
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
  op initializeSavedSpecwareState : ()
  def initializeSavedSpecwareState = 
    case saveSpecwareState initialSpecwareState of
      | (Ok val,_) -> toScreen "Initializing Specware state ..."
      | (Exception _,_) -> fail "initializeSavedSpecwareState failed"

  op ignoredState : State
  def ignoredState = initialSpecwareState
\end{spec}

Allow the user to compile a URI from the lisp interface.

\begin{spec}
  op compileSpecwareURIenv : String * Option String * State
                            -> (SpecCalc.Result Value) * State
  def compileSpecwareURIenv (path,targetfile,specwareState) = 
    let run = {
      currentURI <- pathToCanonicalURI ".";
      setCurrentURI currentURI;
      uri <- pathToRelativeURI path; 
      evaluateAndLispCompile (uri, targetfile)
    } in
    catch run toplevelHandler specwareState

  op evaluateAndLispCompile: RelativeURI * Option String -> SpecCalc.Env Value
  def evaluateAndLispCompile (uri, targetfile) =
    {spcInfo <- evaluateTermInfo(URI uri,pos0);
     (value,_,_) <- evaluateLispCompile(spcInfo,(URI uri,pos0), targetfile);
     return value}
\end{spec}

Eventually, this will be a read/eval/print loop for Specware.
At present we are using the Lisp interface.

\begin{spec}
  op toplevelLoop : SpecCalc.Env ()
  def toplevelLoop = return ()
\end{spec}

This is the toplevel exception handler. Eventually, when we have our own
read-eval-print loop, this will be used only for uncaught exceptions. For
now, this handles all exceptions, For all exceptions except Fail, it
constructs and prints a message.  For Fail exceptions, it calls fail to
enter the Lisp debugger as this indicates an internal (Specware) error.

\begin{spec}
  op toplevelHandler : fa (a) Exception -> SpecCalc.Env a
  def toplevelHandler except =
    {cleanupGlobalContext;		% Remove InProcess entries
     saveSpecwareState;			% So work done before error is not lost
     let message = % "Uncaught exception: " ++
       (case except of
         | Fail str -> "Fail: " ^ str
         | DiagError (position,msg) ->
               "Diagram error: "
             ^ msg
             ^ " at "
             ^ (showPosition position)
         | ParserError fileName ->
               "Syntax error in file "
             ^ fileName
         | CircularDefinition uri ->
               "Circular definition: " ^ showURI uri
         | SyntaxError msg ->
               "Syntax error: "
             ^ msg
         | URINotFound (position,uri) ->
               "Could not find unit: "
             ^ (showRelativeURI uri)
             ^ (if position = pos0 then
                  ""
                else
                  (" referenced from " ^ (showPosition position)))
         | TypeCheck (position,str) ->
               "Type error: "
             ^ str
             ^ " at "
             ^ (showPosition position)
         %% OldTypeCheck is a temporary hack to avoid gratuitous 0.0-0.0 for position
         | OldTypeCheck str ->
               "Type errors:\n"
             ^ str
         | Unsupported (position,str) ->
               "Unsupported operation: "
             ^ str
             ^ " at "
             ^ (showPosition position)
         | _ -> "Unknown exception")
     in
       mFail message}
\end{spec}

This handwritten functions save and set the state in the lisp environment
so that the successful work you have done before the error is kept.

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
