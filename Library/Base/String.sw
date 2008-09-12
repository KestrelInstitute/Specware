String qualifying spec

 import Character, List

 (* A string is a finite sequence of characters (of type Char). Thus, we define
 type String by isomorphism with lists of characters. *)

 type String.String  % qualifier required for internal parsing reasons

 % string that consists of argument list of characters:

 op implode : Bijection (List Char, String)

 (* Metaslang's string literals are simply syntactic shortcuts for expressions
 of the form implode l, where l is a list of characters. For example,
 "Specware" stands for implode [#S,#p,#e,#c,#w,#a,#r,#e]. *)

 % list of constituent characters of a string:

 op explode : String -> List Char = inverse implode

 % analogues of some list ops:

 op length (s:String) : Nat = length (explode s)

 op @ (s:String, i:Nat | i < length s) infixl 30 : Char = (explode s) @ i

 op subFromTo (s:String, i:Nat, j:Nat | i <= j && j <= length s) : String =
   implode (subFromTo (explode s, i, j))

 op ++ (s1:String, s2:String) infixl 25 : String =
   implode ((explode s1) ++ (explode s2))

 op forall? (p: Char -> Boolean) (s: String) : Boolean =
   forall? p (explode s)

 op exists? (p: Char -> Boolean) (s: String) : Boolean =
   exists? p (explode s)

 op map (f: Char -> Char) (s: String) : String =
   implode (map f (explode s))

 op flatten (ss: List String) : String = implode (flatten (map explode ss))

 % replace each character with a string and concatenate:

 op translate (subst: Char -> String) (s: String) : String =
   flatten (map subst (explode s))

 % strings can be linearly ordered and compared element-wise and regarding
 % the empty string smaller than any non-empty string:

 op compare (s1:String, s2:String) : Comparison =
   compare Char.compare (explode s1, explode s2)

 % linear ordering relations:

 op <  (s1:String, s2:String) infixl 20 : Boolean = (compare(s1,s2) = Less)

 op <= (s1:String, s2:String) infixl 20 : Boolean = (s1 < s2 || s1 = s2)

 op >  (s1:String, s2:String) infixl 20 : Boolean = (s2 <  s1)

 op >= (s1:String, s2:String) infixl 20 : Boolean = (s2 <= s1)

 % string consisting of just the newline character:

 op newline : String = "\n"

 % convert booleans to strings:

 op Boolean.show (x:Boolean) : String = if x then "true" else "false"

 % convert naturals to strings:

 op Nat.digitToString (d:Nat | d < 10) : String =
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
   | 9 -> "9"

 op Nat.natToString (x:Nat) : String =
   if x < 10 then digitToString x
   else natToString (x div 10) ++ digitToString (x rem 10)

 op Nat.show : Nat -> String = natToString

 % convert strings to naturals (if convertible):

 op Nat.natConvertible (s:String) : Boolean =
   ex(x:Nat) natToString x = s

 op Nat.stringToNat (s:String | natConvertible s) : Nat =
   the(x:Nat) natToString x = s

 % convert integers to strings:

 op Integer.intToString (x:Integer) : String =
   if x >= 0 then        natToString   x
             else "-" ++ natToString (-x)

 % In the translation of the following theorem we MUST add the type constraint
 % to x to make the proof go through
 proof Isa intToString_Obligation_subsort
  sorry
 end-proof

 op Integer.show : Integer -> String = intToString

 % convert strings to integers (if convertible):

 op Integer.intConvertible (s:String) : Boolean =
   ex(x:Integer) intToString x = s

 op Integer.stringToInt (s:String | intConvertible s) : Integer =
   the(x:Integer) intToString x = s

 % convert characters to strings:

 op Char.show (c:Char) : String = implode [c]

 % convert comparisons to strings:

 op Compare.show : Comparison -> String = fn
   | Greater -> "Greater"
   | Equal   -> "Equal"
   | Less    -> "Less"

 % given conversion from type a to String, convert Option a to String:

 op [a] Option.show (shw: a -> String) : Option a -> String = fn
   | None   -> "None"
   | Some x -> "(Some " ^ (shw x) ^ ")"

 % convert list of strings to string, using given separator:

 op List.show (sep:String) (l: List String) : String =
   case l of
      | []     -> ""
      | hd::[] -> hd
      | hd::tl -> hd ++ sep ++ (List.show sep tl)

 % deprecated:

 op sub : {(s,n) : String * Nat | n < length s} -> Char = (@)

 op substring : {(s,i,j) : String * Nat * Nat |
                 i <= j && j <= length s} -> String = subFromTo

 op concat : String * String -> String = (++)

 op ^ infixl 25 : String * String -> String = (++)

 op all : (Char -> Boolean) -> String -> Boolean = forall?

 op exists : (Char -> Boolean) -> String -> Boolean = exists?

 op concatList : List String -> String = flatten

 op toScreen (s:String) : () = ()

 op writeLine (s:String) : () = ()

 op lt infixl 20 : String * String -> Boolean = (<)

 op leq infixl 20 : String * String -> Boolean = (<=)

 op Boolean.toString : Boolean -> String = Boolean.show

 op Nat.toString : Nat -> String = Nat.show

 op Integer.toString : Integer -> String = Integer.show

 op Char.toString : Char -> String = Char.show

 % mapping to Isabelle:

 proof Isa ThyMorphism
   type String.String \_rightarrow string
   String.explode \_rightarrow id
   String.implode \_rightarrow id
   String.length \_rightarrow length
   String.concat \_rightarrow @ Left 25
   String.++ \_rightarrow @ Left 25
   String.^ \_rightarrow @ Left 25
   String.map \_rightarrow map
   String.exists? \_rightarrow list_ex
   String.exists \_rightarrow list_ex
   String.forall? \_rightarrow list_all
   String.all \_rightarrow list_all
   String.@ \_rightarrow ! Left 40
   String.sub \_rightarrow ! Left 40
   String.concatList \_rightarrow concat
   String.lt  \_rightarrow <  Left 20
   String.leq \_rightarrow <= Left 20
   String.<  \_rightarrow <  Left 20
   String.<= \_rightarrow <= Left 20
   String.>  \_rightarrow >  Left 20
   String.>= \_rightarrow >= Left 20
 end-proof

endspec
