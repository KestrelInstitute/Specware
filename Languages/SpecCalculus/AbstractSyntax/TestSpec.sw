%% This utility tests a spec for well-formedness.  It is available as
%% the Specware shell command 'testspec'.  The actual well-formedness
%% predicate is in: Languages/MetaSlang/Specs/AnnSpec.sw

TestSpec qualifying spec 

import ShowUtils
import ../../MetaSlang/Specs/AnnSpec

%% Evaluate the given unit and print it to a file.
%% Returns a success flag.
op testSpec (uid_str : String) : Boolean =
let _ = writeLine "Testing spec." in
let _ = writeLine ("uid_str:"^uid_str) in
case evaluateUnitId uid_str of
  | None -> let _ = writeLine("Error in testspec: Unknown UID " ^ uid_str) in false
  | Some val ->
    case val of
    | Spec spc -> let _ = specOkay? "Spec is okay." "ERROR: Ill-formed spec." spc in true

% This is the top-level function for the testspec command.
op evaluateTestSpec (optional_argstring : Option String, lastUnitIdLoaded : Option String, homedir : String) : Option String = 
  let _ = writeLine "Calling evaluateTestSpec." in
  let _ = writeLine ("The user's home directory: "^homedir) in
  let _ = writeLine ("arg string: "^(case optional_argstring of Some str -> enquote str | None -> "No arg string supplied.")) in
  let _ = writeLine ("Last unit ID: "^(case lastUnitIdLoaded of | Some str -> str | None ->  "No last uid processed.")) in
  case UIDStringFromArgString(optional_argstring, lastUnitIdLoaded, homedir) of
  | None -> None % fail and don't change *last-unit-Id-_loaded*
  | Some uid_str ->
    %% Check the spec and return a new value for *last-unit-Id-_loaded* if the spec was found:
    let success? = testSpec uid_str in
    if success? then Some uid_str else None

end-spec
