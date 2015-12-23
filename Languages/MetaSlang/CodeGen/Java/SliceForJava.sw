(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

JavaGen qualifying spec

 import /Languages/MetaSlang/Transformations/OldSlice   % TODO: deprecated
%import /Languages/MetaSlang/Transformations/SliceSpec  % use this instead

op builtinJavaOp? (Qualified (q, id) : QualifiedId) : Bool =
 case q of

   %% Base specs:
   | "Bool"       -> id in? ["show", "toString", "true", "false", "~", "&&", "||", "=>", "<=>", "~="]
   | "Integer"    -> id in? ["show", "toString", "intToString", "stringToInt", 
                             "+", "-", "*", "div", "mod", "<=", "<", "~", ">", ">=", "**", 
                             "isucc", "ipred", "positive?", "negative?", "zero", "one"]
   | "IntegerAux" -> id in? ["-"]  % unary minus
   | "Nat"        -> id in? ["show", "toString", "natToString", "stringToNat"]
   | "Char"       -> id in? ["show", "toString", "chr", "ord", "compare",
                             "isUpperCase", "isLowerCase", "isAlpha", "isNum", "isAlphaNum", "isAscii", 
                             "toUpperCase", "toLowerCase"]
   | "String"     -> id in? ["compare", "append", "++", "^", "<", "newline", "length", "implode",
                             "concat", "subFromTo", "substring", "@", "sub"]
   | "System"     -> id in? ["writeLine", "toScreen"]

   %% Non-constructive
   | "Function"   -> id in? ["inverse", "surjective?", "injective?", "bijective?"]  % "Bijection" removed but transparent
   | "List"       -> id in? ["lengthOfListFunction", "definedOnInitialSegmentOfLength", "list", "list_1", "ListFunction"]

   %% Explicitly handcoded
   | "Handcoded"  -> true

   | _ -> false

op builtinJavaType? (Qualified (q, id) : QualifiedId) : Bool =
  case q of
    | "Bool"       -> id in? ["Bool"]
    | "Integer"    -> id in? ["Int", "Int0"]
    | "Nat"        -> id in? ["Nat", "PosNat"]
    | "Char"       -> id in? ["Char"]
    | "String"     -> id in? ["String"]
    | _ -> false

op SpecTransform.sliceSpecForJava (spc             : Spec)
                                  (root_ops        : QualifiedIds)
                                  (root_types      : QualifiedIds)
 : Spec =
 sliceSpecForCode (spc, root_ops, root_types, builtinJavaOp?, builtinJavaType?)

end-spec
