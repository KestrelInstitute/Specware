\section{SPECPATH handling}

This will be moved.

\begin{spec}
SpecCalc qualifying spec {
  import Environment
  import Evaluate/UnitId/Utilities
\end{spec}

The \verb+SWPATH+ environment variable holds a ":" separated list
of path names. Names may be relative or absolute. An absolute path
begins with "/". A relative path does not. A relative path is taken
with respect to the directory in which \Specware\ was inoked.

We attempt to construct a canonical form for each UnitId. This is to avoid
the situation where there may be distinct relative unitId names to the
same object. If there isn't a canonical unitId, each such unitId would give
rise to a different entry in the environment. Unfortunately, this is
not entirely robust. Because of symbolic links, a UNIX file may have
several full path names.

It is silly to reconstruct the SpecPath every time. It should
be done once at initialization and then added to the monadic state.

This retrieves the value of the \verb+SWPATH+ environment variable,
parses it and returns a list of canonical UIDs. If the variable is
not defined, then it returns the singleton list where the UnitId is the
directory in which \Specware\ was invoked.

Changed my mind. To be consistent, the \Specware\ starting directory is
\emph{always} added to the \verb+SWPATH+ as the last element.

This means that if the user adds the current path to the environment
variable, then it will appear twice is the list of UnitId's we generate.

\begin{spec}
  op getSpecPath : Env (List UnitId)
  def getSpecPath =
    let specware4Dirs = case getEnv "SPECWARE4" of
                         | Some d -> [d]
                         | None -> []
    in
    let currDir = getCurrentDirectory () in
    let strings =
      case getEnv "SWPATH" of
        | Some str ->
          let paths = splitStringAtChar specPathSeparator str in
          paths
            ++ [currDir]
            ++ (if specware4Dirs = [] or List.member(hd specware4Dirs,paths)
                 then [] else specware4Dirs)
        | _ -> [currDir,"/"] ++ specware4Dirs
    in
      mapM pathToCanonicalUID strings

 op specPathSeparator: Char
 def specPathSeparator = (if msWindowsSystem? then #; else #:)

 op checkSpecPathsExistence?: Boolean
 def checkSpecPathsExistence? = true

 op checkSpecPathsExistence: String -> ()
 def checkSpecPathsExistence str =
   if checkSpecPathsExistence?
     then app (fn dir -> if fileExists? dir
	                  then ()
			  else warn("Directory does not exist: " ^ dir))
            (splitStringAtChar specPathSeparator str)
     else ()

}
\end{spec}
