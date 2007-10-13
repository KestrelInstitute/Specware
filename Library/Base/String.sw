String qualifying spec

  import Char, List

  (* A string is a finite sequence of characters (of type Char). Thus, we define
  type String by isomorphism with lists of characters. *)

  type String.String  % qualifier required for internal parsing reasons

  % string that consists of argument list of characters:
  op implode : Bijection (List Char, String)

  (* Metaslang's string literals are simply syntactic shortcuts for expressions
  implode l, where l is a list of characters. For example, "Spec" stands for
  implode [#S,#p,#e,#c]. *)

  % list of constituent characters of strings:
  op explode : String -> List Char = inverse implode

  % number of constituent characters:

  op length (s:String) : Nat = List.length (explode s)

  % concatenation:

  op concat (s1:String, s2:String) : String =
    implode (List.concat (explode s1, explode s2))

  op ++ infixl 25 : String * String -> String = concat

  op ^  infixl 25 : String * String -> String = concat

  % apply function to characters element-wise:

  op map (f: Char -> Char) (s: String) : String =
    implode (List.map f (explode s))

  % true iff some/each character satisfies p:

  op exists (p: Char -> Boolean) (s: String) : Boolean =
    List.exists p (explode s)

  op all    (p: Char -> Boolean) (s: String) : Boolean =
    List.all    p (explode s)

  % n-th character of string (counting from 0, left-to-right):

  op sub (s:String, n:Nat | n < length s) : Char = nth (explode s, n)

  % substring from the i-th character (inclusive) to the j-th character
  % (exclusive):

  op substring (s:String, i:Nat, j:Nat | i <= j && j <= length s) : String =
    implode (sublist (explode s, i, j))

  % concatenate all the strings in the list, in order:

  op concatList (ss: List String) : String =
    case ss of
      | []     -> ""
      | s::ss1 -> s ^ (concatList ss1)

  % replace each character with a string and concatenate:

  op translate (subst: Char -> String) (s: String) : String =
    concatList (map subst (explode s))

  % strings can be linearly ordered and compared element-wise and regarding
  % the empty string smaller than any non-empty string:

  op compare (s1:String, s2:String) : Comparison =
    List.compare Char.compare (explode s1, explode s2)

  % linear ordering relations:

  op <  (s1:String, s2:String) infixl 20 : Boolean = (compare(s1,s2) = Less)

  op <= (s1:String, s2:String) infixl 20 : Boolean = (s1 < s2 || s1 = s2)

  op >  (s1:String, s2:String) infixl 20 : Boolean = (s2 <  s1)

  op >= (s1:String, s2:String) infixl 20 : Boolean = (s2 <= s1)

  op lt  infixl 20 : String * String -> Boolean = (<)   % deprecated

  op leq infixl 20 : String * String -> Boolean = (<=)  % deprecated

  % string consisting of just newline character:

  op newline : String = "\n"

  % deprecated:

  op toScreen  (s:String) : () = ()
  op writeLine (s:String) : () = ()

  % convert booleans to strings:

  op Boolean.show (x:Boolean) : String = if x then "true" else "false"

  op Boolean.toString : Boolean -> String = Boolean.show  % deprecated

  % convert naturals to strings:

  op Nat.natToString (x:Nat) : String =
    let def digitToString (d:Nat | d < 10) : String =
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
    let def natToStringAux (x:Nat, res:String) : String =
        if x < 10 then (digitToString x) ^ res
        else natToStringAux (x div 10, digitToString (x rem 10) ^ res) in
    natToStringAux (x, "")
  proof Isa natToString__natToStringAux "measure (\_lambda (x,res). x)"
  end-proof

  op Nat.show     : Nat -> String = Nat.natToString
  op Nat.toString : Nat -> String = Nat.natToString  % deprecated

  % convert naturals to strings (if convertible):

  op Nat.natConvertible (s:String) : Boolean =
    let cs = explode s in
    (exists isNum cs) && (all isNum cs)

  op Nat.stringToNat (s:String | Nat.natConvertible s) : Nat =
    let def charToDigit (c:Char | isNum c) : Nat =
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
    let def stringToNatAux (chars: List Char, res:Nat | all isNum chars) : Nat =
        case chars of
           | []     -> res
           | hd::tl -> stringToNatAux (tl, res * 10 + charToDigit hd) in
    stringToNatAux (explode s, 0)
  proof Isa stringToNat__stringToNatAux "measure (\_lambda(chars,res). length chars)"
  end-proof

  % convert integers to strings:

  op Integer.intToString (x:Integer) : String =
    if x >= 0 then       Nat.natToString   x
              else "-" ^ Nat.natToString (-x)

  op Integer.show     : Integer -> String = Integer.intToString
  op Integer.toString : Integer -> String = Integer.intToString  % deprecated

  % convert strings to integers (if convertible):

  op Integer.intConvertible (s:String) : Boolean =
    let cs = explode s in
    (exists isNum cs) &&
    ((all isNum cs) || (hd cs = #- && all isNum (tl cs)))

  op Integer.stringToInt (s:String | Integer.intConvertible s) : Integer =
    let firstchar::_ = explode s in
    if firstchar = #- then - (stringToNat (substring (s,1,length s)))
                      else    stringToNat s

  % convert characters to strings:

  op Char.show (c:Char) : String = implode [c]

  op Char.toString : Char -> String = Char.show  % deprecated

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
       | hd::tl -> hd ^ sep ^ (List.show sep tl)

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
    String.exists \_rightarrow list_ex
    String.all \_rightarrow list_all
    String.sub \_rightarrow ! Left 40
    String.concatList \_rightarrow concat
    String.lt  \_rightarrow <  Left 20
    String.leq \_rightarrow <= Left 20
  end-proof

endspec
