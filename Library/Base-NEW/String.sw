String qualifying spec

  import Char, List

  (* A string is a finite sequence of characters (of type Char). Thus, we
  define type String by isomorphism with lists of characters. *)

  type String.String  % qualifier required for internal parsing reasons

  % map string to list of component characters:

  op explode : String -> List Char

  axiom explode_is_isomorphism is bijective? explode

  % other ops on strings:

  op implode : List Char -> String
  def implode = inverse explode

  op length : String -> Nat
  def length s = List.length(explode s)

  op concat : String * String -> String
  def concat(s1,s2) = implode(List.concat(explode s1,explode s2))

  op ++ infixl 25 : String * String -> String
  def ++ (s1,s2) = concat(s1,s2)

  op ^  infixl 25 : String * String -> String
  def ^ (s1,s2) = concat(s1,s2)

  op map : (Char -> Char) -> String -> String
  def map f s = implode(List.map f (explode s))

  op exists : (Char -> Boolean) -> String -> Boolean
  def exists p s = List.exists p (explode s)

  op all : (Char -> Boolean) -> String -> Boolean
  def all p s = List.all p (explode s)

  op sub : {(s,n) : String * Nat | n < length s} -> Char
  def sub(s,n) = nth(explode s,n)

  op substring : {(s,i,j) : String * Nat * Nat | i <= j && j <= length s} ->
                 String
  def substring(s,i,j) = implode(sublist(explode s,i,j))

  op concatList : List String -> String
  def concatList = fn
    | []     -> ""
    | s::ss1 -> s ^ (concatList ss1)

  op translate : (Char -> String) -> String -> String
  def translate subst s = concatList(map subst (explode s))

  op compare : String * String -> Comparison
  def compare(s1,s2) = if s1 < s2 then Less
                  else if s2 < s1 then Greater
                  else (* s1 = s2 *)    Equal

  op < infixl 20 : String * String -> Boolean
  def < (s1,s2) = (compare(s1,s2) = Less)

  op <= infixl 20 : String * String -> Boolean
  def <= (s1,s2) = s1 < s2 || s1 = s2

  op >= infixl 20 : String * String -> Boolean
  def >= (x,y) = y <= x

  op > infixl 20 : String * String -> Boolean
  def > (x,y) = y <  x

  op newline : String
  def newline = "\n"

  op lt infixl 20 : String * String -> Boolean  % deprecated
  def lt (s1,s2) = s1 < s2

  op leq infixl 20 : String * String -> Boolean  % deprecated
  def leq (s1,s2) = s1 <= s2

  op toScreen : String -> ()  % deprecated
  op writeLine : String -> ()  % deprecated

  theorem toScreen_def is
    fa (s : String) toScreen s = ()

  theorem writeLine_def is
    fa (s : String) writeLine s = ()

  % ops with different qualifiers:

  op Boolean.toString : Boolean -> String  % deprecated
  def Boolean.toString x = if x then "true" else "false"

  op Integer.toString : Integer -> String  % deprecated
  def Integer.toString x = if x >= 0 then Nat.toString x
                                     else "-" ^ Nat.toString(- x)

  op Nat.toString : Nat -> String  % deprecated
  def Nat.toString x =
    let def digitToString (d : {d : Nat | d < 10}) : String =
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
    toStringAux(x,"")

  op Char.toString : Char -> String  % deprecated
  def Char.toString c = implode [c]

  op Integer.intToString : Integer -> String
  def Integer.intToString = Integer.toString

  op Integer.intConvertible : String -> Boolean
  def Integer.intConvertible s =
    let cs = explode s in
      (exists isNum cs) &&
      ((all isNum cs) || (hd cs = #- && all isNum (tl cs)))

  op Integer.stringToInt : (String | Integer.intConvertible) -> Integer
  def Integer.stringToInt s =
    let firstchar::_ = explode s in
    if firstchar = #-
    then Integer_.- (stringToNat(substring(s,1,length s)))
    else stringToNat s

  op Nat.natToString : Nat -> String
  def Nat.natToString = Nat.toString

  op Nat.natConvertible : String -> Boolean
  def Nat.natConvertible s =
    let cs = explode s in
      (exists isNum cs) && (all isNum cs)

  op Nat.stringToNat : (String | Nat.natConvertible) -> Nat
  def Nat.stringToNat s =
    let def charToDigit (c : (Char | isNum)) : Nat =
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
    stringToNatAux(explode s, 0)

  op Boolean.show : Boolean -> String
  def Boolean.show b = Boolean.toString b

  op Compare.show : Comparison -> String
  def Compare.show cmp =
    case cmp of
       | Greater -> "Greater"
       | Equal   -> "Equal"
       | Less    -> "Less"

  op Option.show : [a] (a -> String) -> Option a -> String
  def Option.show shw opt =
    case opt of
       | None   -> "None"
       | Some x -> "(Some " ^ (shw x) ^ ")"

  op Integer.show : Integer -> String
  def Integer.show i = Integer.toString i

  op Nat.show : Nat -> String
  def Nat.show n = Nat.toString n

  op List.show : String -> List String -> String
  def List.show sep l =
    case l of
       | []     -> ""
       | hd::[] -> hd
       | hd::tl -> hd ^ sep ^ (List.show sep tl)

  op Char.show : Char -> String
  def Char.show c = Char.toString c

endspec
