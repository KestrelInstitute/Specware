(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)



Specware qualifying spec
  import Specware
  import /Languages/SpecCalculus/Semantics/Evaluate/GenAll

  %% When starting Prism, we can execute the following in lisp:
  %%  (setq SpecCalc::shadowingPaths SpecCalc::shadowingPathsForPrism)

  def shadowingPathsForPrism : Shadowings = 
    let Some prism_str = getEnv "PRISM"     in  % e.g. "/usr/home/kestrel/mcdonald/Work/Generic/Prism"
    let Some sw_str    = getEnv "SPECWARE4" in  % e.g. "/usr/home/kestrel/mcdonald/Work/Generic/Specware4"
    let prism_dir      = splitStringAtChars (prism_str, [#/]) in
    let sw_dir         = splitStringAtChars (sw_str,    [#/]) in
    [[prism_dir ++ ["Sources"], sw_dir]]

  %% experimental loop to generate all implementations of a spec
  op  Specware.evaluateGenAll_fromLisp : String -> Bool
  def Specware.evaluateGenAll_fromLisp path = 
    let prog = {
      cleanEnv;
      currentUID <- pathToCanonicalUID ".";
      setCurrentUID currentUID;
      path_body <- return (removeSWsuffix path);
      unitId <- pathToRelativeUID path_body;
      position <- return (String (path, startLineColumnByte, endLineColumnByte path_body));
      catch {
        genAll position unitId; % see 
        return ()
      } (fileNameHandler unitId);
      return true
    } in
    runSpecCommand (catch prog Specware.toplevelHandler)

endspec

