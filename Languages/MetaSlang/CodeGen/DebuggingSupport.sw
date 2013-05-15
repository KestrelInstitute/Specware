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

 %% useful for indented debugging....

 op indentation      : Ref Int = Ref 0
 op indentationLimit : Ref Int = Ref 40  

 op getIndentationLimit () : Int = (! indentationLimit)          % use this to accesss indentationLimit
 op getIndentation      () : Int = (! indentation)               % use this to accesss indentation

 op setIndentationLimit (n : Int) : () = (indentationLimit := n) % use this to change indentationLimit
 op setIndentation      (n : Int) : () = (indentation      := n) % use this to change indentation

 op changeIndentation   (n : Int) : () = setIndentation ((! indentation) + n)

 op whiteSpace (n : Nat) : String = implode (repeat #\s n)

 op writeAt (s : String) : () =
  let n = getIndentation () in
  if (n < getIndentationLimit ()) then
    writeLine (whiteSpace(n) ^ s) 
  else
    ()

 op writeIn (s : String) : () =
  let _ = writeAt s in
  let _ = changeIndentation 2 in
  ()

 op writeOut (s : String) : () =
  let _ = changeIndentation (-2) in
  let _ = writeAt s in
  ()

end-spec
