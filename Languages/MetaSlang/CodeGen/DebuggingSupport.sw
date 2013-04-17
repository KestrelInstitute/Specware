Debugging qualifying spec

 import /Languages/MetaSlang/Specs/Printer % printSpec

 op verbosity : Nat = 0

 op temporaryTargets : Ids = ["setTgt", "newGraph", "selectSupply1", "nextState", "foo", "foo2"] % TODO: flush this soon

 op showIfVerbose (strings : List String) : () =
  if verbosity > 0 then 
    let _ = map writeLine strings in
    ()
  else
    ()

 op showInternals (spc : Spec) : () =
  appSpec ((fn tm  -> writeLine (printTermWithTypes tm)), 
           (fn typ -> writeLine (printType          typ)),
           (fn pat -> writeLine (printPattern       pat)))
          spc

 op showSpecIfVerbose (msg : String) (spc : Spec) : () =
  if verbosity > 0 then 
    let _ = writeLine "--------------------" in
    let _ = writeLine ("### " ^ msg)         in
    let _ = writeLine (if verbosity = 1 then
                         printSpec spc
                       else
                         printSpecFlat spc)  in
    % let _ = writeLine "----"               in
    % let _ = if (verbosity > 2) then showInternals spc else () in
    let _ = writeLine "--------------------" in
    ()
  else
    ()

 op SpecTransform.showSpec (spc : Spec) (msg : String) : Spec =
  let _ = writeLine "--------------------" in
  let _ = writeLine ("### " ^ msg)         in
  let _ = writeLine (printSpec spc)        in
  let _ = writeLine "--------------------" in
  spc

 op SpecTransform.showSpecFlat (spc : Spec) (msg : String) : Spec =
  let _ = writeLine "--------------------" in
  let _ = writeLine ("### " ^ msg)         in
  let _ = writeLine (printSpecFlat spc)    in
  let _ = writeLine "--------------------" in
  spc

 op compressWhiteSpace (s : String) : String =
  let 
    def whitespace? char = 
      char = #\s || char = #\n || char = #\t

    def compress (chars, have_whitespace?) =
      %% avoid deep recursions...
      let (chars, _) = 
          foldl (fn ((chars, have_whitespace?), char) ->
                   if whitespace? char then
                     if have_whitespace? then
                       (chars, have_whitespace?)
                     else
                       ([#\s] ++ chars, true)
                   else
                     ([char] ++ chars, false))
                ([], true)
                chars
      in
      reverse chars
  in
  implode (compress (explode s, true))

end-spec
