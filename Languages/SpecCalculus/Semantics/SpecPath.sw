(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%%% SPECPATH handling

SpecCalc qualifying spec
  import Environment
  import Evaluate/UnitId/Utilities

(*
The SWPATH environment variable holds a ":" separated list
of path names. Names may be relative or absolute. An absolute path
begins with "/". A relative path does not. A relative path is taken
with respect to the directory in which \Specware\ was invoked.

We attempt to construct a canonical form for each UnitId. This is to avoid
the situation where there may be distinct relative unitId names to the
same object. If there isn't a canonical unitId, each such unitId would give
rise to a different entry in the environment. Unfortunately, this is
not entirely robust. Because of symbolic links, a UNIX file may have
several full path names.

It is silly to reconstruct the SpecPath every time. It should
be done once at initialization and then added to the monadic state.

This retrieves the value of the SWPATH environment variable,
parses it and returns a list of canonical UIDs. If the variable is
not defined, then it returns the singleton list where the UnitId is the
directory in which \Specware\ was invoked.

Changed my mind. To be consistent, the \Specware\ starting directory is
\emph{always} added to the SWPATH as the last element.

This means that if the user adds the current path to the environment
variable, then it will appear twice is the list of UnitId's we generate.
*)

%% Seems odd to use unitIDs here, since there will never be a hash suffix (the elements of SWPATH are directories).
op SpecCalc.getSpecPath0(): List UnitId =
  let specware4Dirs = case getEnv "SPECWARE4" of
                        | Some d -> [d]
                        | None -> []
  in
  %% 8/9/04 sjw: Core decided that it did not make sense to have . implicitly in specPath
  %let currDir = getCurrentDirectory () in
  let strings =
    case getEnv "SWPATH" of
      | Some str ->
        let paths = splitStringAt(str, specPathSeparator) in
        ["/"] ++ paths ++
        (if specware4Dirs = [] || head specware4Dirs in? paths then
           [] 
         else 
           specware4Dirs)
      | _ -> 
        ["/"] ++ specware4Dirs
  in
    map (fn str -> pathStringToCanonicalUID(str,true)) strings

op getSpecPath : Env (List UnitId) =
  return(getSpecPath0())

op specPathSeparator: String = (if msWindowsSystem? then ";" else ":")

op checkSpecPathsExistence? : Bool = true

op checkSpecPathsExistence (str : String) : Bool =
  if checkSpecPathsExistence?
    then forall? (fn dir -> if fileExists? dir
                              then true
                            else (warn("Directory does not exist: " ^ dir); false))
           (splitStringAt(str, specPathSeparator))
    else true

endspec
