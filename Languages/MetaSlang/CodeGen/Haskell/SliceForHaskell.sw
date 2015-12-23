(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

HaskellGen qualifying spec

 import /Languages/MetaSlang/Transformations/OldSlice  % TODO: deprecated
%import /Languages/MetaSlang/Transformations/SliceSpec % replace with this

op haskellElement? (el: SpecElement) : Bool =
 case el of
   | Pragma("#translate", prag_str, "#end", _) | haskellPragma? prag_str -> true
   | Pragma _ -> false
   | _ -> true

op haskellPragma? (s: String) : Bool =
 let s = stripOuterSpaces s in
 let len = length s in
 len > 2 && (let pr_type = subFromTo(s, 0, 7) in
             pr_type = "Haskell" || 
             pr_type = "haskell")

end-spec
