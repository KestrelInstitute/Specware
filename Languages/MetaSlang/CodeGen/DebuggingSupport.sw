(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Debugging qualifying spec

import /Languages/MetaSlang/Specs/Printer                  % printSpec
import /Languages/MetaSlang/Transformations/CountTermTypes % initTermTypeCounter, countTermTypes

op verbosity : Nat = 0

op temporaryTargets : Ids = ["setTgt", "newGraph", "selectSupply1", "nextState", "foo", "foo2"] % TODO: flush this soon

op showIfVerbose (strings : List String) : () =
 if verbosity > 0 then 
   let _ = map writeLine strings in
   ()
 else
   ()

op showElements (spc : Spec) (msg : String) (depth : Nat) (verbose? : Bool) : () =
 let _ = writeLine "-Elements-----------" in
 let _ = writeLine ("##1 " ^ msg)         in  % "##1" is just a convenient pattern to search for
 let
   def aux level elements =
     if level > depth then
       ()
     else
       let prefix = whiteSpace (2 * level) in
       app (fn el ->
              case el of
                | Import   (s_tm, _, elts, _) -> let _ = writeLine (prefix ^ "Import: " ^ showSCTerm s_tm) in
                                                 aux (level + 1) elts
                | Type     (qid,           _) -> writeLine (prefix ^ "Type:    " ^ show qid) 
                | TypeDef  (qid,           _) -> writeLine (prefix ^ "TypeDef: " ^ show qid) 
                | Op       (qid, false,    _) -> writeLine (prefix ^ "Op:      " ^ show qid) 
                | Op       (qid, true,     _) -> writeLine (prefix ^ "OpDecl:  " ^ show qid) 
                | OpDef    (qid, _, _,     _) -> writeLine (prefix ^ "OpDef:   " ^ show qid) 
                | Property _                  -> if verbose? then writeLine (prefix ^ "Property") else ()
                | Comment  _                  -> if verbose? then writeLine (prefix ^ "Comment")  else ()
                | Pragma   _                  -> if verbose? then writeLine (prefix ^ "Pragma")   else ())
           elements
 in
 let _ = aux 0 spc.elements in
 let _ = writeLine "--------------------" in
 ()

op showSpec (spc : Spec) (msg : String) : () =
 let _ = writeLine "-showSpec-----------" in
 let _ = writeLine ("##4 " ^ msg)         in  % "##4" is just a convenient pattern to search for
 let _ = writeLine (printSpec spc)        in
 let _ = writeLine "--------------------" in
 ()

op showSpecFlat (spc : Spec) (msg : String) : () =
 let _ = writeLine "-showSpecFlat-------" in
 let _ = writeLine ("##5 " ^ msg)         in  % "##5" is just a convenient pattern to search for
 let _ = writeLine (printSpecFlat spc)        in
 let _ = writeLine "--------------------" in
 ()

op showSpecInternals (spc : Spec) (msg : String) : () =
 let _ = writeLine "-showSpecInternals--" in
 let _ = writeLine ("##6 " ^ msg)         in  % "##6" is just a convenient pattern to search for
 let _ = showInternals spc                in
 let _ = writeLine "--------------------" in
 ()

op showInternals (spc : Spec) : () =
 appSpec ((fn tm  -> writeLine (printTermWithTypes tm)), 
          (fn typ -> writeLine (printType          typ)),
          (fn pat -> writeLine (printPattern       pat)))
         spc

op maybeShowSpecIfVerbose (pred? : Bool) (msg : String) (spc : Spec) : () =
 if pred? then
   showSpecIfVerbose msg spc
 else
   ()

op showSpecIfVerbose (msg : String) (spc : Spec) : () =
 %% verbosity is just a selector, higher values are not necessarily more verbose
 case verbosity of

   %% show names of types and ops:
   | 1 -> showElements      spc msg 0    false  % just names of top-level types and op
   | 2 -> showElements      spc msg 1000 false  % all names of types and op
   | 3 -> showElements      spc msg 1000 true   % everything, but each tersely

   %% show definitions of types and ops:
   | 4 -> showSpec          spc msg 
   | 5 -> showSpecFlat      spc msg 

   %% show more than you want to see:
   | 6 -> showSpecInternals spc msg
     
   | _ -> ()

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

%%% ================================================================================
%%% Transforms invocable by user
%%% ================================================================================

op SpecTransform.showSpec (spc : Spec) (msg : String) : () =
 let _ = Debugging.showSpec spc msg in
 ()

op SpecTransform.showSpecFlat (spc : Spec) (msg : String) : () =
 let _ = Debugging.showSpecFlat spc msg in
 ()

op SpecTransform.showSpecInternals (spc : Spec) (msg : String) : () =
 let _ = Debugging.showSpecInternals spc msg in
 ()

op SpecTransform.showElements (spc : Spec) (msg : String) (depth : Nat) (verbose? : Bool) : () =
 let _ = Debugging.showElements spc msg depth verbose? in
 ()

op SpecTransform.showOps (spc : Spec) (msg : String) (names : QualifiedIds) : () =
 let _ = writeLine "-showOps------------" in
 let _ = writeLine ("##9 " ^ msg)         in  % "##9" is just a convenient pattern to search for
 let _ = app (fn qid -> 
                writeLine (show qid ^ " =\n" ^
                             (case findTheOp (spc, qid) of
                                | Some info -> 
                                  let tm = case info.dfn of
                                             | And (tm :: _, _) -> tm
                                             | tm -> tm
                                  in
                                  printTerm tm
                                | _ -> "not found")))
             names
 in
 let _ = writeLine "--------------------" in
 ()

op SpecTransform.showAllTypes (spc : Spec) (msg : String) : () =
 let _ = writeLine "-showAllTypes-------" in
 let _ = writeLine ("## " ^ msg)          in
 let
   def showit qid =
     writeLine (show qid ^ " =\n" ^
                  (case findTheType (spc, qid) of
                     | Some info -> 
                       let typ = case info.dfn of
                                   | And (typ :: _, _) -> typ
                                   | typ -> typ
                       in
                       printType typ
                     | _ -> "not found"))
   def scan elts =
     app (fn elt -> 
            case elt of
              | Type    (qid, _) -> showit qid
              | TypeDef (qid, _) -> showit qid
              | Import  (_, _, elts, _) -> scan elts 
              | _ -> writeLine("ignore: " ^ anyToString elt))
         elts
 in
 let _ = scan spc.elements in
 let _ = writeLine "--------------------" in
 ()

op MetaRule.showTerm (spc : Spec) (msg : String) (term : MSTerm) : Option MSTerm =
 let _ = writeLine "-showTerm-----------" in
 let _ = writeLine (msg ^ printTerm term) in
 let _ = writeLine "--------------------" in
 None

op SpecTransform.showPragmas (s : Spec, msg : String) : () =
 let _ = writeLine "====================" in
 let _ = writeLine ("Pragmas: " ^ msg) in
 let _ = writeLine "--------------------" in
 let _ = mapSpecElements (fn elt ->
                            case elt of
                              | Pragma (prefix, body, postfix, _) ->
                                let _ = writeLine "--------------------" in
                                let _ = writeLine prefix in
                                let _ = writeLine body in
                                let _ = writeLine postfix in
                                let _ = writeLine "====================" in
                                elt
                              | _ ->
                                elt)
                         s.elements
  in
  let _ = writeLine "====================" in
  ()

end-spec
