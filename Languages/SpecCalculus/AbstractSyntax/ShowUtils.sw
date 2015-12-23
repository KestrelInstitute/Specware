(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

ShowUtils qualifying spec

%% This file contains utility functions that are used in ShowData,
%% ShowDeps, ShowImports, etc.

import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities
%op  SpecCalc.findUnitIdForUnit: Value * GlobalContext -> Option UnitId

%% Give the signature of utilities so we don't have to import them:
op  Specware.evaluateUnitId: String -> Option Value
%import /Languages/SpecCalculus/Semantics/Bootstrap


op enquote (str:String) : String = ("\""^str^"\"")


%%TODO duplicate
%% Replace leading ~/ (if present) with the user's home dir.
op substHomeDir (path : String, homedir : String) : String =
  case (explode path) of
  | #~ :: #/ :: rest -> homedir ^ "/" ^ (implode rest)
  | _ -> path

%% Used because the use of "#" causes problems with syntax coloring.
op numberSignString : String = implode [##]


% Interpose subDirName before the unit name.
% Example: If subDirName="data", the result for foo/bar/baz#suf is foo/bar/data/baz#suf
op fileNameInSubDir ({path, hashSuffix} : UnitId, subDirName : String) : String =
  let hash_and_suffix = case hashSuffix of | Some suf -> [numberSignString, suf] | None -> [] in
  let file_name = List.last path in
  let dir = butLast path in
  let dir_with_slashes = List.foldr (fn (elem,result) -> Cons("/",Cons(elem,result)))
                                        []
                                        dir in
  let result_path = dir_with_slashes ++ ["/", subDirName, "/", file_name] ++ hash_and_suffix in
    flatten result_path

  op uidForValue (val:Value) : Option UnitId =
    case MonadicStateInternal.readGlobalVar "GlobalContext" of
    | None -> None
    | Some global_context -> findUnitIdForUnit(val, global_context)


%TODO update ShowDeps and ShowImports to use this.
%Given the argument to a Specware shell command, figure out the unit being refered to (if none, use the last unit loaded, and use the user's home dir for ~/).
op UIDStringFromArgString (optional_argstring : Option String, lastUnitIdLoaded : Option String, homedir : String) : Option String = 
  let opt_uid_str =
    (case optional_argstring of
       %% No arguments given at all, so use the last unit loaded, if there is one.
     | None -> (case lastUnitIdLoaded of
                | None -> let _ = writeLine("ERROR: No unit given and no previous unit loaded.") in None
                | Some uid_str -> lastUnitIdLoaded)
       %% Otherwise, the argument string is the unit ID to process:
     | Some argstring -> optional_argstring) in
    %% Now handle the home directory:
    (case opt_uid_str of
     | None -> None %% fail
     | Some uid_str -> Some (substHomeDir(uid_str, homedir)))


end-spec
