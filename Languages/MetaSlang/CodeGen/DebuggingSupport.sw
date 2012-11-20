Debugging qualifying spec

 import /Languages/MetaSlang/Specs/Printer % printSpec

 op verbosity : Nat = 0

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
    let _ = writeLine "----"                 in
    % let _ = if (verbosity > 2) then showInternals spc else () in
    let _ = writeLine "--------------------" in
    ()
  else
    ()

end-spec
