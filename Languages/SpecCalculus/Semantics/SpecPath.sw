\section{SPECPATH handling}

Derived from r1.2 SW4/Languages/SpecCalculus/Semantics/SpecPath.sl

This will be moved.

\begin{spec}
SpecCalc qualifying spec {
  import Environment
  import Evaluate/URI/Utilities
\end{spec}

The \verb+SPECPATH+ environment variable holds a ":" separated list
of path names. Names may be relative or absolute. An absolute path
begins with "/". A relative path does not. A relative path is taken
with respect to the directory in which \Specware\ was inoked.

We attempt to construct a canonical form for each URI. This is to avoid
the situation where there may be distinct relative uri names to the
same object. If there isn't a canonical uri, each such uri would give
rise to a different entry in the environment. Unfortunately, this is
not entirely robust. Because of symbolic links, a UNIX file may have
several full path names.

It is silly to reconstruct the SpecPath every time. It should
be done once at initialization and then added to the monadic state.

This retrieves the value of the \verb+SPECPATH+ environment variable,
parses it and returns a list of canonical URIs. If the variable is
not defined, then it returns the singleton list where the URI is the
directory in which \Specware\ was invoked.

Changed my mind. To be consistent, the \Specware\ starting directory is
\emph{always} added to the \verb+SPECPATH+ as the last element.

This means that if the user adds the current path to the environment
variable, then it will appear twice is the list of URI's we generate.

\begin{spec}
  op getSpecPath : Env (List URI)
  def getSpecPath =
    let strings =
      case getEnv "SPECPATH" of
        | None -> [getCurrentDirectory ()]
        | Some str -> (splitAtChar #: str) ++ [getCurrentDirectory ()]
    in
      mapM pathToCanonicalURI strings
}
\end{spec}
