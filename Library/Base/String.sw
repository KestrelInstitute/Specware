String qualifying spec

  % refinement of base spec String

  import Char
  import List

  % sorts:

  % sort String

  % ops whose Lisp code is hand-written:

 %op explode       : String -> List Char
  op implode       : List Char -> String
  op length        : String -> Nat
  op concat        : String * String -> String
  op ++ infixl 11  : String * String -> String
  op ^  infixl 11  : String * String -> String
  op map           : (Char -> Char) -> String -> String
  op exists        : (Char -> Boolean) -> String -> Boolean
  op all           : (Char -> Boolean) -> String -> Boolean
  op sub           : {(s,n) : String * Nat | n < length s} -> Char
  op substring     : {(s,i,j) : String * Nat * Nat | i < j & j <= length s} ->
                     String
  op concatList    : List String -> String
  op translate     : (Char -> String) -> String -> String
  op lt  infixl 20 : String * String -> Boolean
  op leq infixl 20 : String * String -> Boolean
  op newline       : String
  op toScreen      : String -> ()  % deprecated
  op writeLine     : String -> ()  % deprecated

  % axioms copied from base spec String:

  axiom implode_def is
    fa (s : String) implode(explode s) = s

  axiom length_def is
    fa (s : String) length s = List.length(explode s)

  axiom concat_def is
    fa (s1,s2 : String)
       concat(s1,s2) = implode(List.concat(explode s1,explode s2))

  axiom concat2_def is
    fa (s1,s2 : String) (s1 ++ s2) = concat(s1,s2)

  axiom concat3_def is
    fa (s1,s2 : String) (s1 ^ s2) = concat(s1,s2)

  axiom map_def is
    fa (f : Char -> Char, s : String)
       map f s = implode(List.map f (explode s))

  axiom exists_def is
    fa (p : Char -> Boolean, s : String)
       exists p s = List.exists p (explode s)

  axiom all_def is
    fa (p : Char -> Boolean, s : String)
       all p s = List.all p (explode s)

  axiom sub_def is
    fa (s : String, n : Nat) n < length s =>
       sub(s,n) = nth(explode s,n)

  axiom substring_def is
    fa (s : String, i : Nat, j : Nat) i < j & j < length s =>
       substring(s,i,j) = implode(sublist(explode s,i,j))

  axiom concatList_def is
    fa (ss : List String)
       concatList ss = (case ss of
                           | []     -> ""
                           | s::ss1 -> s ^ (concatList ss1))

  axiom translate_def is
    fa (subst : Char -> String, s : String)
       translate subst s = concatList(map subst (explode s))

  axiom lt_def is
    fa (s1,s2 : String) s1 lt s2 <=> compare(s1,s2) = Less

  axiom leq_def is
    fa (s1,s2 : String)  s1 leq s2  <=>  s1 lt s2  or  s1 = s2

  axiom newline_def is  newline = "\n"

  % ops whose Lisp code is generated:

  op compare : String * String -> Comparison

  def compare(s1,s2) = if s1 lt s2 then Less
                  else if s2 lt s1 then Greater
                  else (* s1 = s2 *)    Equal

  % ops conceptually belonging to other specs but introduced here,
  % whose Lisp code is hand-written:

  op Boolean.toString : Boolean -> String  % deprecated
  op Integer.toString : Integer -> String  % deprecated
  op Nat.toString     : Nat -> String      % deprecated
  op Char.toString    : Char -> String     % deprecated

  op Integer.intToString    : Integer -> String
  op Integer.stringToInt    : (String | Integer.intConvertible) -> Integer

  op Nat.natToString  : Nat -> String
  op Nat.stringToNat  :
     {s : String | length s > 0 & all isNum (explode s)} -> Nat

  % axioms copied from base spec String:

  axiom boolean_toString_def is
    fa (x : Boolean) Boolean.toString x = (if x then "true" else "false")

  axiom int_toString_def is
    fa (x : Integer) Integer.toString x =
                     (if x >= 0 then Nat.toString x
                                else "-" ^ Nat.toString(~x))

  axiom nat_toString_def is
    fa (x : Nat) Nat.toString x =
                 (let def digitToString (d : {d : Nat | d < 10}) : String =
                          case d of
                             | 0 -> "0"
                             | 1 -> "1"
                             | 2 -> "2"
                             | 3 -> "3"
                             | 4 -> "4"
                             | 5 -> "5"
                             | 6 -> "6"
                             | 7 -> "7"
                             | 8 -> "8"
                             | 9 -> "9" in
                  let def toStringAux (x : Nat, res : String) : String =
                          if x < 10 then (digitToString x) ^ res
                                    else toStringAux
                                          (x div 10,
                                           digitToString(x rem 10) ^ res) in
                  toStringAux(x,""))

  axiom char_toString_def is
    fa (c : Char) Char.toString c = implode [c]

  axiom intToString_def is  intToString = Integer.toString

  axiom stringToInt_def is
    fa (s : String) intConvertible s =>
       stringToInt s = (let firstchar::_ = explode s in
                        if firstchar = #-
                        then ~(stringToNat(substring(s,1,length s)))
                        else stringToNat s)

  axiom natToString_def is  natToString = Nat.toString

  axiom stringToNat_def is
    fa (s : String) (all isNum (explode s)) =>
       stringToNat s =
       (let def charToDigit (c : (Char | isNum)) : Nat =
                case c of
                   | #0 -> 0
                   | #1 -> 1
                   | #2 -> 2
                   | #3 -> 3
                   | #4 -> 4
                   | #5 -> 5
                   | #6 -> 6
                   | #7 -> 7
                   | #8 -> 8
                   | #9 -> 9 in
        let def stringToNatAux (chars : {chars : List Char | all isNum chars},
                                res : Nat) : Nat =
                case chars of
                   | []     -> res
                   | hd::tl -> stringToNatAux
                                (tl, res * 10 + charToDigit hd) in
        stringToNatAux(explode s, 0))

  % ops conceptually belonging to other specs but introduced here,
  % whose Lisp code is generated:

  op Integer.intConvertible : String -> Boolean  % auxiliary predicate

  op Boolean.show : Boolean -> String
  op Compare.show : Comparison -> String
  op Option.show  : fa(a) (a -> String) -> Option a -> String
  op Integer.show : Integer -> String
  op Nat.show     : Nat -> String
  op List.show    : String -> List String -> String
  op Char.show    : Char -> String

  def Integer.intConvertible s =
    let cs = explode s in
      (exists isNum cs) &
      ((all isNum cs) or (hd cs = #- & all isNum (tl cs)))

  def Boolean.show b = Boolean.toString b

  def Compare.show cmp =
    case cmp of
       | Greater -> "Greater"
       | Equal   -> "Equal"
       | Less    -> "Less"

  def Option.show shw opt =
    case opt of
       | None   -> "None"
       | Some x -> "(Some " ^ (shw x) ^ ")"

  def Integer.show i = Integer.toString i

  def Nat.show n = Nat.toString n

  def List.show sep l =
    case l of
       | []     -> ""
       | hd::[] -> hd
       | hd::tl -> hd ^ sep ^ (List.show sep tl)

  def Char.show c = Char.toString c

endspec
