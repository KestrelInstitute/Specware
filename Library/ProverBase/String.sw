(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

PrString qualifying spec

  import ../Base/String

  (* A string is a finite sequence of characters (of type Char). Thus, we
  define type String by isomorphism with lists of characters. *)

  %type String.String  % qualifier required for internal parsing reasons

  % maps string to list of component characters:
  axiom explode_is_isomorphism is
    bijective? explode


  axiom implode_def is
    implode = inverse explode

  axiom length_def is
    fa (s : String) length s = List.length(explode s)

  axiom concat_def is
    fa (s1 : String, s2 : String)
       s1^s2 = implode(List.++(explode s1,explode s2))

  axiom map_def is
    fa (f : Char -> Char, s : String)
       map f s = implode(List.map f (explode s))

  axiom exists_def is
    fa (p : Char -> Bool, s : String)
       exists? p s = List.exists? p (explode s)

  axiom all_def is
    fa (p : Char -> Bool, s : String)
       forall? p s = List.forall? p (explode s)

  axiom sub_def is
    fa (s : String, n : Nat) n < length s =>
       @(s,n) = @(explode s,n)

  axiom subFromTo_def is
    fa (s : String, i : Nat, j : Nat)
      i <= j && j <= length s 
      =>
      subFromTo(s,i,j) = implode(subFromTo(explode s,i,j))

  axiom flatten_def is
    fa (ss : List String)
       flatten ss = (case ss of
                           | []     -> ""
                           | s::ss1 -> s ^ (flatten ss1))

  axiom translate_def is
    fa (subst : Char -> String, s : String)
       translate subst s = flatten(map subst (explode s))

  axiom lt_def is
    fa (s1 : String, s2 : String) s1 < s2 <=> compare(s1,s2) = Less

  axiom leq_def is
    fa (s1 : String, s2 : String)  s1 <= s2  <=>  s1 < s2  || s1 = s2

  axiom newline_def is
    newline = "\n"

  axiom greater_equal_def is
    fa (x: String, y: String) >= (x,y) = (y <= x)

  axiom greate_than_def is
    fa (x: String, y: String) > (x,y) = (y < x)

  axiom compare_def1 is
    fa (s1: String, s2: String) s1 < s2 => compare(s1,s2) = Less

  axiom compare_def2 is
    fa (s1: String, s2: String) s2 < s1 => compare(s1,s2) = Greater

  axiom compare_def3 is
    fa (s1: String, s2: String) s1 = s2 => compare(s1,s2) = Equal

  % ops with different qualifiers:
(*
  op Bool.show : Bool -> String  % deprecated
  op Integer.show : Int  -> String  % deprecated
  op Nat.show     : Nat  -> String  % deprecated
  op Char.show    : Char -> String  % deprecated

  op Integer.intToString : Int -> String
  op Integer.stringToInt : (String | Integer.intConvertible) -> Int

  op Nat.natToString  : Nat -> String
  op Nat.stringToNat  : (String | Nat.natConvertible) -> Nat

  op Option.show            : [a] (a -> String) -> Option a -> String
  op List.show              : String -> List String         -> String

  op Bool.show              : Bool       -> String
  op Compare.show           : Comparison -> String
  op Char.show              : Char       -> String
  op Integer.show           : Int        -> String
  op Nat.show               : Nat        -> String
  op Integer.intConvertible : String     -> Bool
  op Nat.natConvertible     : String     -> Bool
*)
  axiom boolean_show_def is
    fa (x : Bool) Bool.show x = (if x then "true" else "false")

  axiom int_show_def is
    fa (x : Int) Integer.show x =
                     (if x >= 0 then Nat.show x
                                else "-" ^ Nat.show(- x))

  axiom nat_show_def is
    fa (x : Nat) Nat.show x =
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
                  let def showAux (x : Nat, res : String) : String =
                          if x < 10 then (digitToString x) ^ res
                                    else showAux
                                          (x div 10,
                                           digitToString(x mod 10) ^ res) in
                  showAux(x,""))

  axiom char_show_def is
    fa (c : Char) Char.show c = implode [c]

  axiom intToString_def is
    intToString = Integer.show

  axiom stringToInt_def is
    fa (s : String) intConvertible s =>
       stringToInt s = (let firstchar::_ = explode s in
                        if firstchar = #-
                        then -(stringToNat(subFromTo(s,1,length s)))
                        else stringToNat s)

  axiom natToString_def is
    natToString = Nat.show

  axiom stringToNat_def is
    fa (s : String) natConvertible s =>
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
        let def stringToNatAux (chars : {chars : List Char | forall? isNum chars},
                                res : Nat) : Nat =
                case chars of
                   | []     -> res
                   | hd::tl -> stringToNatAux
                                (tl, res * 10 + charToDigit hd) in
        stringToNatAux(explode s, 0))

  axiom show is fa (b: Bool) Bool.show b = Bool.show b

  axiom compare_show_def1 is
    fa (cmp) cmp = Greater => Compare.show cmp = "Greater"

  axiom compare_show_def2 is
    fa (cmp) cmp = Equal => Compare.show cmp = "Equal"

  axiom compare_show_def is
    fa (cmp) cmp = Less => Compare.show cmp = "Less"

  axiom option_show_def1 is [a]
    fa (opt:Option a, shw) opt = None => Option.show shw opt = "None"

  axiom option_show_def2 is
    fa (opt, shw, x) opt = Some x => Option.show shw opt = "(Some " ^ (shw x) ^ ")"

  axiom intConvertible_def is
    fa (s) Integer.intConvertible s =
    (let cs = explode s in
      (exists? isNum cs) &&
      ((forall? isNum cs) || (head cs = #- && forall? isNum (tail cs))))

  axiom integer_show_def is
    fa(i) Integer.show i = Integer.show i

  axiom natConvertible_def is
    fa(s) Nat.natConvertible s =
    (let cs = explode s in
      (exists? isNum cs) && (forall? isNum cs))

  axiom nat_show_def is
    fa (n) Nat.show n = Nat.show n

  axiom list_show_def is
    fa(l, sep)  List.show sep l =
    (case l of
       | []     -> ""
       | hd::[] -> hd
       | hd::tl -> hd ^ sep ^ (List.show sep tl))

  axiom char_show_def is
    fa(c) Char.show c = Char.show c

endspec
