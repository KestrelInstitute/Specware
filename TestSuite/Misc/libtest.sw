spec
  import /Library/Legacy/Utilities/System  % writeLine

  def verbose? = false
  op tester (what : String, success? : Bool) : () =
    if verbose? then
      writeLine((if success? then "P: " else "F: ")^what)
    else if success? then 
      ()
    else 
      writeLine("F: "^what)

  def alltests : () = (% Bool [  1]:  op ~             : Bool -> Bool
    tester ("(~ ( true )) = false", (~ ( true )) = false);
    tester ("(~ ( false )) = true", (~ ( false )) = true);
% Bool [  2]:  op &&   infixr 15 : Bool * Bool -> Bool 
    tester ("(&& ( false, false )) = false", (&& ( false, false )) = false);
    tester ("let A = id ( false, false ) in (&& A) = false", let A = id ( false, false ) in (&& A) = false);
    tester ("(&& ( false, true )) = false", (&& ( false, true )) = false);
    tester ("let A = id ( false, true ) in (&& A) = false", let A = id ( false, true ) in (&& A) = false);
    tester ("(&& ( true, false )) = false", (&& ( true, false )) = false);
    tester ("let A = id ( true, false ) in (&& A) = false", let A = id ( true, false ) in (&& A) = false);
    tester ("(&& ( true, true )) = true", (&& ( true, true )) = true);
    tester ("let A = id ( true, true ) in (&& A) = true", let A = id ( true, true ) in (&& A) = true);
% Bool [  3]:  op ||  infixr 14 : Bool * Bool -> Bool 
    tester ("(|| ( false, false )) = false", (|| ( false, false )) = false);
    tester ("let A = id ( false, false ) in (|| A) = false", let A = id ( false, false ) in (|| A) = false);
    tester ("(|| ( false, true )) = true", (|| ( false, true )) = true);
    tester ("let A = id ( false, true ) in (|| A) = true", let A = id ( false, true ) in (|| A) = true);
    tester ("(|| ( true, false )) = true", (|| ( true, false )) = true);
    tester ("let A = id ( true, false ) in (|| A) = true", let A = id ( true, false ) in (|| A) = true);
    tester ("(|| ( true, true )) = true", (|| ( true, true )) = true);
    tester ("let A = id ( true, true ) in (|| A) = true", let A = id ( true, true ) in (|| A) = true);
% Bool [  4]:  op =>  infixr 13 : Bool * Bool -> Bool 
    tester ("(=> ( false, false )) = true", (=> ( false, false )) = true);
    tester ("let A = id ( false, false ) in (=> A) = true", let A = id ( false, false ) in (=> A) = true);
    tester ("(=> ( false, true )) = true", (=> ( false, true )) = true);
    tester ("let A = id ( false, true ) in (=> A) = true", let A = id ( false, true ) in (=> A) = true);
    tester ("(=> ( true, false )) = false", (=> ( true, false )) = false);
    tester ("let A = id ( true, false ) in (=> A) = false", let A = id ( true, false ) in (=> A) = false);
    tester ("(=> ( true, true )) = true", (=> ( true, true )) = true);
    tester ("let A = id ( true, true ) in (=> A) = true", let A = id ( true, true ) in (=> A) = true);
% Bool [  5]:  op <=> infixr 12 : Bool * Bool -> Bool 
    tester ("(<=> ( false, false )) = true", (<=> ( false, false )) = true);
    tester ("let A = id ( false, false ) in (<=> A) = true", let A = id ( false, false ) in (<=> A) = true);
    tester ("(<=> ( false, true )) = false", (<=> ( false, true )) = false);
    tester ("let A = id ( false, true ) in (<=> A) = false", let A = id ( false, true ) in (<=> A) = false);
    tester ("(<=> ( true, false )) = false", (<=> ( true, false )) = false);
    tester ("let A = id ( true, false ) in (<=> A) = false", let A = id ( true, false ) in (<=> A) = false);
    tester ("(<=> ( true, true )) = true", (<=> ( true, true )) = true);
    tester ("let A = id ( true, true ) in (<=> A) = true", let A = id ( true, true ) in (<=> A) = true);
% Bool [  6]:  op ~=  infixr 20 : fa(a) a * a -> Bool
    tester ("(~= ( 4, 4 )) = false", (~= ( 4, 4 )) = false);
    tester ("let A = id ( 4, 4 ) in (~= A) = false", let A = id ( 4, 4 ) in (~= A) = false);
    tester ("(~= ( 4, 5 )) = true", (~= ( 4, 5 )) = true);
    tester ("let A = id ( 4, 5 ) in (~= A) = true", let A = id ( 4, 5 ) in (~= A) = true);
% Bool [  7]:  op compare  : Bool * Bool -> Comparison
    tester ("(compare ( false, false )) = Equal", (compare ( false, false )) = Equal);
    tester ("let A = id ( false, false ) in (compare A) = Equal", let A = id ( false, false ) in (compare A) = Equal);
    tester ("(compare ( false, true )) = Less", (compare ( false, true )) = Less);
    tester ("let A = id ( false, true ) in (compare A) = Less", let A = id ( false, true ) in (compare A) = Less);
    tester ("(compare ( true, false )) = Greater", (compare ( true, false )) = Greater);
    tester ("let A = id ( true, false ) in (compare A) = Greater", let A = id ( true, false ) in (compare A) = Greater);
    tester ("(compare ( true, true )) = Equal", (compare ( true, true )) = Equal);
    tester ("let A = id ( true, true ) in (compare A) = Equal", let A = id ( true, true ) in (compare A) = Equal);
% Bool [129]:  op show : Bool -> String
    tester ("(show ( true )) = \"true\"", (show ( true )) = "true");
    tester ("(show ( false )) = \"false\"", (show ( false )) = "false");

% Char [ 10]:  op ord : Char -> {n : Nat | n < 256}
    tester ("(ord ( #A )) = 65", (ord ( #A )) = 65);
% Char [ 11]:  op chr : {n : Nat | n < 256} -> Char
    tester ("(chr ( 65 )) = #A", (chr ( 65 )) = #A);
% Char [ 12]:  op isUpperCase : Char -> Bool
    tester ("(isUpperCase ( #! )) = false", (isUpperCase ( #! )) = false);
    tester ("(isUpperCase ( #3 )) = false", (isUpperCase ( #3 )) = false);
    tester ("(isUpperCase ( #A )) = true", (isUpperCase ( #A )) = true);
    tester ("(isUpperCase ( #a )) = false", (isUpperCase ( #a )) = false);
    tester ("(isUpperCase ( #\\xdd )) = true", (isUpperCase ( #\xdd )) = true);
    tester ("(isUpperCase ( #\\xff )) = false", (isUpperCase ( #\xff )) = false);
% Char [ 13]:  op isLowerCase : Char -> Bool
    tester ("(isLowerCase ( #! )) = false", (isLowerCase ( #! )) = false);
    tester ("(isLowerCase ( #3 )) = false", (isLowerCase ( #3 )) = false);
    tester ("(isLowerCase ( #A )) = false", (isLowerCase ( #A )) = false);
    tester ("(isLowerCase ( #a )) = true", (isLowerCase ( #a )) = true);
    tester ("(isLowerCase ( #\\xdd )) = false", (isLowerCase ( #\xdd )) = false);
    tester ("(isLowerCase ( #\\xff )) = true", (isLowerCase ( #\xff )) = true);
% Char [ 14]:  op isAlpha     : Char -> Bool
    tester ("(isAlpha ( #! )) = false", (isAlpha ( #! )) = false);
    tester ("(isAlpha ( #3 )) = false", (isAlpha ( #3 )) = false);
    tester ("(isAlpha ( #A )) = true", (isAlpha ( #A )) = true);
    tester ("(isAlpha ( #a )) = true", (isAlpha ( #a )) = true);
    tester ("(isAlpha ( #\\xff )) = true", (isAlpha ( #\xff )) = true);
% Char [ 15]:  op isNum       : Char -> Bool
    tester ("(isNum ( #! )) = false", (isNum ( #! )) = false);
    tester ("(isNum ( #3 )) = true", (isNum ( #3 )) = true);
    tester ("(isNum ( #A )) = false", (isNum ( #A )) = false);
    tester ("(isNum ( #a )) = false", (isNum ( #a )) = false);
    tester ("(isNum ( #\\xff )) = false", (isNum ( #\xff )) = false);
% Char [ 16]:  op isAlphaNum  : Char -> Bool
    tester ("(isAlphaNum ( #! )) = false", (isAlphaNum ( #! )) = false);
    tester ("(isAlphaNum ( #3 )) = true", (isAlphaNum ( #3 )) = true);
    tester ("(isAlphaNum ( #A )) = true", (isAlphaNum ( #A )) = true);
    tester ("(isAlphaNum ( #a )) = true", (isAlphaNum ( #a )) = true);
    tester ("(isAlphaNum ( #\\xff )) = true", (isAlphaNum ( #\xff )) = true);
% Char [ 17]:  op isAscii     : Char -> Bool
    tester ("(isAscii ( #! )) = true", (isAscii ( #! )) = true);
    tester ("(isAscii ( #3 )) = true", (isAscii ( #3 )) = true);
    tester ("(isAscii ( #A )) = true", (isAscii ( #A )) = true);
    tester ("(isAscii ( #a )) = true", (isAscii ( #a )) = true);
    tester ("(isAscii ( #\\xff )) = true", (isAscii ( #\xff )) = true); % was false, but ascii now considered 0--255
% Char [ 18]:  op toUpperCase : Char -> Char
    tester ("(toUpperCase ( #! )) = #!", (toUpperCase ( #! )) = #!);
    tester ("(toUpperCase ( #3 )) = #3", (toUpperCase ( #3 )) = #3);
    tester ("(toUpperCase ( #A )) = #A", (toUpperCase ( #A )) = #A);
    tester ("(toUpperCase ( #a )) = #A", (toUpperCase ( #a )) = #A);
    tester ("(toUpperCase ( #\\xfc )) = #\\xdc", (toUpperCase ( #\xfc )) = #\xdc);
% Char [ 19]:  op toLowerCase : Char -> Char
    tester ("(toLowerCase ( #! )) = #!", (toLowerCase ( #! )) = #!);
    tester ("(toLowerCase ( #3 )) = #3", (toLowerCase ( #3 )) = #3);
    tester ("(toLowerCase ( #A )) = #a", (toLowerCase ( #A )) = #a);
    tester ("(toLowerCase ( #a )) = #a", (toLowerCase ( #a )) = #a);
    tester ("(toLowerCase ( #\\xdc )) = #\\xfc", (toLowerCase ( #\xdc )) = #\xfc);
% Char [ 20]:  op compare : Char * Char -> Comparison
    tester ("(compare ( #3, #4 )) = Less", (compare ( #3, #4 )) = Less);
    tester ("let A = id ( #3, #4 ) in (compare A) = Less", let A = id ( #3, #4 ) in (compare A) = Less);
    tester ("(compare ( #4, #4 )) = Equal", (compare ( #4, #4 )) = Equal);
    tester ("let A = id ( #4, #4 ) in (compare A) = Equal", let A = id ( #4, #4 ) in (compare A) = Equal);
    tester ("(compare ( #5, #4 )) = Greater", (compare ( #5, #4 )) = Greater);
    tester ("let A = id ( #5, #4 ) in (compare A) = Greater", let A = id ( #5, #4 ) in (compare A) = Greater);
% Char [135]:  op show    : Char -> String
    tester ("(show ( #A )) = \"A\"", (show ( #A )) = "A");

% Compare [ 23]:  op compare : Comparison * Comparison -> Comparison
    tester ("(compare ( Less, Less )) = Equal", (compare ( Less, Less )) = Equal);
    tester ("let A = id ( Less, Less ) in (compare A) = Equal", let A = id ( Less, Less ) in (compare A) = Equal);
    tester ("(compare ( Less, Equal )) = Less", (compare ( Less, Equal )) = Less);
    tester ("let A = id ( Less, Equal ) in (compare A) = Less", let A = id ( Less, Equal ) in (compare A) = Less);
    tester ("(compare ( Less, Greater )) = Less", (compare ( Less, Greater )) = Less);
    tester ("let A = id ( Less, Greater ) in (compare A) = Less", let A = id ( Less, Greater ) in (compare A) = Less);
    tester ("(compare ( Equal, Less )) = Greater", (compare ( Equal, Less )) = Greater);
    tester ("let A = id ( Equal, Less ) in (compare A) = Greater", let A = id ( Equal, Less ) in (compare A) = Greater);
    tester ("(compare ( Equal, Equal )) = Equal", (compare ( Equal, Equal )) = Equal);
    tester ("let A = id ( Equal, Equal ) in (compare A) = Equal", let A = id ( Equal, Equal ) in (compare A) = Equal);
    tester ("(compare ( Equal, Greater )) = Less", (compare ( Equal, Greater )) = Less);
    tester ("let A = id ( Equal, Greater ) in (compare A) = Less", let A = id ( Equal, Greater ) in (compare A) = Less);
    tester ("(compare ( Greater, Less )) = Greater", (compare ( Greater, Less )) = Greater);
    tester ("let A = id ( Greater, Less ) in (compare A) = Greater", let A = id ( Greater, Less ) in (compare A) = Greater);
    tester ("(compare ( Greater, Equal )) = Greater", (compare ( Greater, Equal )) = Greater);
    tester ("let A = id ( Greater, Equal ) in (compare A) = Greater", let A = id ( Greater, Equal ) in (compare A) = Greater);
    tester ("(compare ( Greater, Greater )) = Equal", (compare ( Greater, Greater )) = Equal);
    tester ("let A = id ( Greater, Greater ) in (compare A) = Equal", let A = id ( Greater, Greater ) in (compare A) = Equal);
% Compare [130]:  op show : Comparison -> String
    tester ("(show ( Less )) = \"Less\"", (show ( Less )) = "Less");
    tester ("(show ( Equal )) = \"Equal\"", (show ( Equal )) = "Equal");
    tester ("(show ( Greater )) = \"Greater\"", (show ( Greater )) = "Greater");

% Functions [ 25]:  op id          : fa(a) a -> a
    tester ("(id ( 3 )) = 3", (id ( 3 )) = 3);
    tester ("(id ( #3 )) = #3", (id ( #3 )) = #3);
% Functions [ 26]:  op o infixl 24 : fa(a,b,c) (b -> c) * (a -> b) -> (a -> c)
    tester ("((o(succ,succ))3) = 5", ((o(succ,succ))3) = 5);
    tester ("(let(ss)=(succ,succ)in(o(ss))3) = 5", (let(ss)=(succ,succ)in(o(ss))3) = 5);
% Functions [ 27]:  op injective?  : fa(a,b) (a -> b) -> Bool
% Functions [ 28]:  op surjective? : fa(a,b) (a -> b) -> Bool
% Functions [ 29]:  op bijective?  : fa(a,b) (a -> b) -> Bool
% Functions [ 30]:  op inverse     : fa(a,b) Bijective(a,b) -> Bijective(b,a)

% Int [ 31]:  op ~             : Int -> Int
    tester ("(- ( 3 )) = 0-3", (- ( 3 )) = 0-3);
% Int [ 32]:  op +   infixl 25 : Int * Int -> Int
    tester ("(+ ( 3, 4 )) = 7", (+ ( 3, 4 )) = 7);
    tester ("let A = id ( 3, 4 ) in (+ A) = 7", let A = id ( 3, 4 ) in (+ A) = 7);
% Int [ 33]:  op -   infixl 25 : Int * Int -> Int
    tester ("(- ( 7, 4 )) = 3", (- ( 7, 4 )) = 3);
    tester ("let A = id ( 7, 4 ) in (- A) = 3", let A = id ( 7, 4 ) in (- A) = 3);
% Int [ 34]:  op *   infixl 27 : Int * Int -> Int
    tester ("( * ( 3, 4 )) = 12", ( * ( 3, 4 )) = 12);
    tester ("let A = id ( 3, 4 ) in ( * A) = 12", let A = id ( 3, 4 ) in ( * A) = 12);
% Int [ 35]:  op div infixl 26 : Int * NZInt -> Int
    tester ("(div ( 27, 10 )) = 2", (div ( 27, 10 )) = 2);
    tester ("let A = id ( 27, 10 ) in (div A) = 2", let A = id ( 27, 10 ) in (div A) = 2);
% Int [ 36]:  op mod infixl 26 : Int * NZInt -> Int
    tester ("(mod ( 27, 10 )) = 7", (mod ( 27, 10 )) = 7);
    tester ("let A = id ( 27, 10 ) in (mod A) = 7", let A = id ( 27, 10 ) in (mod A) = 7);
% Int [ 37]:  op <   infixl 20 : Int * Int -> Bool
    tester ("(< ( 3, 4 )) = true", (< ( 3, 4 )) = true);
    tester ("let A = id ( 3, 4 ) in (< A) = true", let A = id ( 3, 4 ) in (< A) = true);
    tester ("(< ( 4, 4 )) = false", (< ( 4, 4 )) = false);
    tester ("let A = id ( 4, 4 ) in (< A) = false", let A = id ( 4, 4 ) in (< A) = false);
% Int [ 38]:  op <=  infixl 20 : Int * Int -> Bool
    tester ("(<= ( 3, 3 )) = true", (<= ( 3, 3 )) = true);
    tester ("let A = id ( 3, 3 ) in (<= A) = true", let A = id ( 3, 3 ) in (<= A) = true);
    tester ("(<= ( 4, 3 )) = false", (<= ( 4, 3 )) = false);
    tester ("let A = id ( 4, 3 ) in (<= A) = false", let A = id ( 4, 3 ) in (<= A) = false);
% Int [ 39]:  op >  infixl 20 : Int * Int -> Bool
    tester ("(> ( 4, 3 )) = true", (> ( 4, 3 )) = true);
    tester ("let A = id ( 4, 3 ) in (> A) = true", let A = id ( 4, 3 ) in (> A) = true);
    tester ("(> ( 4, 4 )) = false", (> ( 4, 4 )) = false);
    tester ("let A = id ( 4, 4 ) in (> A) = false", let A = id ( 4, 4 ) in (> A) = false);
% Int [ 40]:  op >= infixl 20 : Int * Int -> Bool
    tester ("(>= ( 3, 3 )) = true", (>= ( 3, 3 )) = true);
    tester ("let A = id ( 3, 3 ) in (>= A) = true", let A = id ( 3, 3 ) in (>= A) = true);
    tester ("(>= ( 3, 4 )) = false", (>= ( 3, 4 )) = false);
    tester ("let A = id ( 3, 4 ) in (>= A) = false", let A = id ( 3, 4 ) in (>= A) = false);
% Int [ 41]:  op abs          : Int -> Int
    tester ("(abs ( - 3 )) = 3", (abs ( - 3 )) = 3);
    tester ("(abs ( 3 )) = 3", (abs ( 3 )) = 3);
% Int [ 42]:  op min          : Int * Int -> Int
    tester ("(min ( 3, 4 )) = 3", (min ( 3, 4 )) = 3);
    tester ("let A = id ( 3, 4 ) in (min A) = 3", let A = id ( 3, 4 ) in (min A) = 3);
% Int [ 43]:  op max          : Int * Int -> Int
    tester ("(max ( 3, 4 )) = 4", (max ( 3, 4 )) = 4);
    tester ("let A = id ( 3, 4 ) in (max A) = 4", let A = id ( 3, 4 ) in (max A) = 4);
% Int [ 44]:  op compare      : Int * Int -> Comparison
    tester ("(compare ( 3, 4 )) = Less", (compare ( 3, 4 )) = Less);
    tester ("let A = id ( 3, 4 ) in (compare A) = Less", let A = id ( 3, 4 ) in (compare A) = Less);
    tester ("(compare ( 4, 4 )) = Equal", (compare ( 4, 4 )) = Equal);
    tester ("let A = id ( 4, 4 ) in (compare A) = Equal", let A = id ( 4, 4 ) in (compare A) = Equal);
    tester ("(compare ( 5, 4 )) = Greater", (compare ( 5, 4 )) = Greater);
    tester ("let A = id ( 5, 4 ) in (compare A) = Greater", let A = id ( 5, 4 ) in (compare A) = Greater);
% Int [132]:  op show : Int -> String
    tester ("(show ( 123 )) = \"123\"", (show ( 123 )) = "123");
% Int [124]:  op intToString    : Int -> String
    tester ("(intToString ( 123 )) = \"123\"", (intToString ( 123 )) = "123");
% Int [124.5]:  op intConvertible : String -> Bool
    tester ("(intConvertible ( \"123\" )) = true", (intConvertible ( "123" )) = true);
    tester ("(intConvertible ( \"-123\" )) = true", (intConvertible ( "-123" )) = true);
    tester ("(intConvertible ( \"000\" )) = true", (intConvertible ( "000" )) = true);
    tester ("(intConvertible ( \"\" )) = false", (intConvertible ( "" )) = false);
    tester ("(intConvertible ( \"123.00\" )) = false", (intConvertible ( "123.00" )) = false);
% Int [125]:  op stringToInt    : (String | intConvertible) -> Int
    tester ("(stringToInt ( \"123\" )) = 123", (stringToInt ( "123" )) = 123);
    tester ("(stringToInt ( \"-123\" )) = -123", (stringToInt ( "-123" )) = -123);
% List [ 49]:  op Nil             : fa(a)   List a
    tester ("(Nil) = []", (Nil) = []);
% List [ 50]:  op Cons            : fa(a)   a * List a -> List a
    tester ("(Cons ( 3, [4] )) = [3,4]", (Cons ( 3, [4] )) = [3,4]);
    tester ("let A = id ( 3, [4] ) in (Cons A) = [3,4]", let A = id ( 3, [4] ) in (Cons A) = [3,4]);
% List [ 51]:  op [a] |> (x:a, l: List a) infixr 25 : List1 a
    tester ("( 3 |> [4]) = [3,4]", ( 3 |> [4] ) = [3,4]);
    tester ("let A = id ( 3, [4] ) in (|> A) = [3,4]", let A = id ( 3, [4] ) in (|> A) = [3,4]);
% List [ 52]:  op length          : fa(a)   List a -> Nat
    tester ("(length ( [3,4] )) = 2", (length ( [3,4] )) = 2);
% List [ 53]:  op empty?           : fa(a)   List a -> Bool
    tester ("(empty? ( Nil )) = true", (empty? ( Nil )) = true);
    tester ("(empty? ( [3] )) = false", (empty? ( [3] )) = false);
% List [ 54]:  op [a] head (l: List1 a) : a"
    tester ("(head ( [3,4] )) = 3", (head ( [3,4] )) = 3);
% List [ 55]:  op [a] tail (l: List1 a) : List a"
    tester ("(tail ( [3,4] )) = [4]", (tail ( [3,4] )) = [4]);
% List [ 57]:  op ++ infixl 25    : fa(a)   List a * List a -> List a
    tester ("(++ ( [3], [4] )) = [3,4]", (++ ( [3], [4] )) = [3,4]);
    tester ("let A = id ( [3], [4] ) in (++ A) = [3,4]", let A = id ( [3], [4] ) in (++ A) = [3,4]);
% List [ 58]:  op @  infixl 25    : fa(a)   List a * List a -> List a
%    tester ("(@ ( [3], [4] )) = [3,4]", (@ ( [3], [4] )) = [3,4]);
%    tester ("let A = id ( [3], [4] ) in (@ A) = [3,4]", let A = id ( [3], [4] ) in (@ A) = [3,4]);
% List [ 59]:  op [a] @ (l: List a, i:Nat | i < length l) infixl 30 : a 
    tester ("( [3,4,5] @ 1 ) = 4", ( [3,4,5] @ 1 ) = 4);
    tester ("let A = id ( [3,4,5], 1 ) in (@ A) = 4", let A = id ( [3,4,5], 1 ) in (@ A) = 4);
% List [ 60]:  op [a] removePrefix (l: List a, n:Nat | n <= length l) : List a 
    tester ("(removePrefix ( [3,4,5], 2 )) = [5]", (removePrefix ( [3,4,5], 2 )) = [5]);
    tester ("let A = id ( [3,4,5], 2 ) in (removePrefix A) = [5]", let A = id ( [3,4,5], 2 ) in (removePrefix A) = [5]);
% List [ 61]:  op [a] in? (x:a, l: List a) infixl 20 : Bool 
    tester ("( 4 in? [3,5,7] ) = false", ( 4 in? [3,5,7]) = false);
    tester ("let A = id ( 4, [3,5,7] ) in (in? A) = false", let A = id ( 4, [3,5,7] ) in (in? A) = false);
    tester ("( 5 in? [3,5,7] ) = true", ( 5 in? [3,5,7] ) = true);
    tester ("let A = id ( 5, [3,5,7] ) in (in? A) = true", let A = id ( 5, [3,5,7] ) in (in? A) = true);
% List [ 62]:  op [a] subFromTo (l: List a, i:Nat, j:Nat | i <= j && j <= length l) : List a
    tester ("(subFromTo ( [3,1,4,1,5,9], 2, 4 )) = [4,1]", subFromTo ([3,1,4,1,5,9], 2, 4) = [4,1]);
    tester ("let A = id ( [3,1,4,1,5,9], 2, 4 ) in (subFromTo A) = [4,1]", let A = id ( [3,1,4,1,5,9], 2, 4 ) in (subFromTo A) = [4,1]);
% List [ 63]:  op map             : fa(a,b) (a -> b) -> List a -> List b
    tester ("(map ( succ ) ( [3,4,5] )) = [4,5,6]", (map ( succ ) ( [3,4,5] )) = [4,5,6]);
    tester ("let F = id ( map ( succ )) in (F ( [3,4,5] )) = [4,5,6]", let F = id ( map ( succ )) in (F ( [3,4,5] )) = [4,5,6]);
% List [ 64]:  op mapPartial      : fa(a,b) (a -> Option b) -> List a -> List b
    tester ("(mapPartial ( fn(n)->if(n<1)then(None)else(Some(pred(n))) ) ( [5,0,2] )) = [4,1]", (mapPartial ( fn(n)->if(n<1)then(None)else(Some(pred(n))) ) ( [5,0,2] )) = [4,1]);
    tester ("let F = id ( mapPartial ( fn(n)->if(n<1)then(None)else(Some(pred(n))) )) in (F ( [5,0,2] )) = [4,1]", let F = id ( mapPartial ( fn(n)->if(n<1)then(None)else(Some(pred(n))) )) in (F ( [5,0,2] )) = [4,1]);
% List [ 65]:  op foldl           : fa(a,b) (b * a -> b) -> b -> List a -> b
    tester ("(foldl ( fn(m,n)->(n)mod(m) ) ( 20 ) ( [77,47] )) = 13", (foldl ( fn(m,n)->(n)mod(m) ) ( 20 ) ( [77,47] )) = 13);
    tester ("let F = id ( foldl ( fn(m,n)->(n)mod(m) )) in (F ( 20 ) ( [77,47] )) = 13", let F = id ( foldl ( fn(m,n)->(n)mod(m) )) in (F ( 20 ) ( [77,47] )) = 13);
% List [ 66]:  op foldr           : fa(a,b) (a * b -> b) -> b -> List a -> b
    tester ("(foldr ( fn(m,n)->(m)mod(n) ) ( 77 ) ( [27,91] )) = 13", (foldr ( fn(m,n)->(m)mod(n) ) ( 77 ) ( [27,91] )) = 13);
    tester ("let F = id ( foldr ( fn(m,n)->(m)mod(n) )) in (F ( 77 ) ( [27,91] )) = 13", let F = id ( foldr ( fn(m,n)->(m)mod(n) )) in (F ( 77 ) ( [27,91] )) = 13);
% List [ 67]:  op [a] exists? (p: a -> Bool) (l: List a) : Bool
    tester ("(exists? posNat? []) = false", (exists? posNat? []) = false);
    tester ("let F = id ( exists? posNat?) in (F []) = false", let F = id ( exists? posNat?) in (F []) = false);
    tester ("(exists? posNat? [0,0,0]) = false", (exists? posNat? ( [0,0,0] )) = false);
    tester ("let F = id ( exists? posNat?) in (F ( [0,0,0] )) = false", let F = id ( exists? posNat?) in (F [0,0,0]) = false);
    tester ("(exists? posNat? [0,1,0]) = true", (exists? posNat? ( [0,1,0] )) = true);
    tester ("let F = id ( exists? posNat?) in (F ( [0,1,0] )) = true", let F = id ( exists? posNat?) in (F [0,1,0]) = true);
% List [ 68]:  op [a] forall? (p: a -> Bool) (l: List a) : Bool 
    tester ("(forall? posNat? []) = true", (forall? posNat? []) = true);
    tester ("let F = id ( forall? posNat? ) in (F ( [] )) = true", let F = id ( forall? posNat? ) in (F ( [] )) = true);
    tester ("(forall? posNat? [1,1,1] ) = true", (forall? posNat? [1,1,1] ) = true);
    tester ("let F = id ( forall? posNat? ) in (F ( [1,1,1] )) = true", let F = id ( forall? posNat? ) in (F ( [1,1,1] )) = true);
    tester ("(forall? posNat? [1,0,1] ) = false", (forall? posNat? [1,0,1] ) = false);
    tester ("let F = id ( forall? posNat? ) in (F ( [1,0,1] )) = false", let F = id ( forall? posNat? ) in (F ( [1,0,1] )) = false);
% List [ 69]:  op filter          : fa(a)   (a -> Bool) -> List a -> List a
    tester ("(filter posNat? ( [5,0,2] )) = [5,2]", (filter posNat? ( [5,0,2] )) = [5,2]);
    tester ("let F = id ( filter posNat?) in (F ( [5,0,2] )) = [5,2]", let F = id ( filter posNat?) in (F ( [5,0,2] )) = [5,2]);
% List [ 70]:  op diff            : fa(a)   List a * List a -> List a
    tester ("(diff ( [3,1,4,1,5,9], [5,9,2,1] )) = [3,4]", (diff ( [3,1,4,1,5,9], [5,9,2,1] )) = [3,4]);
    tester ("let A = id ( [3,1,4,1,5,9], [5,9,2,1] ) in (diff A) = [3,4]", let A = id ( [3,1,4,1,5,9], [5,9,2,1] ) in (diff A) = [3,4]);
% List [ 71]:  op [a] reverse (l: List a) : List a
    tester ("(reverse [1,2,3] ) = [3,2,1]", (reverse [1,2,3]) = [3,2,1]);
% List [ 73]:  op flatten         : fa(a)   List(List a) -> List a
    tester ("(flatten ( [[3,1],[4,1],[5,9]] )) = [3,1,4,1,5,9]", (flatten ( [[3,1],[4,1],[5,9]] )) = [3,1,4,1,5,9]);
% List [ 74]:  op [a] findLeftmost (p: a -> Bool) (l: List a) : Option a
    tester ("(findLeftmost posNat? [0,0,0] ) = None", (findLeftmost posNat? [0,0,0]) = None);
    tester ("let F = id (findLeftmost posNat?) in (F [0,0,0]) = None", let F = id (findLeftmost posNat?) in (F [0,0,0]) = None);
    tester ("(findLeftmost posNat? ( [0,1,0] )) = Some(1)", (findLeftmost posNat? ( [0,1,0] )) = Some(1));
    tester ("let F = id (findLeftmost posNat?) in (F [0,1,0]) = Some(1)", let F = id (findLeftmost posNat?) in (F [0,1,0]) = Some(1));
% List [ 75]:  op tabulate        : fa(a)   Nat * (Nat -> a) -> List a
    tester ("(tabulate ( 3, succ )) = [1,2,3]", (tabulate ( 3, succ )) = [1,2,3]);
    tester ("let A = id ( 3, succ ) in (tabulate A) = [1,2,3]", let A = id ( 3, succ ) in (tabulate A) = [1,2,3]);
% List [ 76]:  op [a] findLeftmostAndPreceding (p: a -> Bool) (l: List a) : Option (a * List a)
    tester ("(findLeftmostAndPreceding empty? ( [[1],[2,3],[],[4]] )) = Some([],[[1],[2,3]])", (findLeftmostAndPreceding empty? ( [[1],[2,3],[],[4]] )) = Some([],[[1],[2,3]]));
    tester ("let F = id ( findLeftmostAndPreceding empty?) in (F ( [[1],[2,3],[],[4]] )) = Some([],[[1],[2,3]])", let F = id ( findLeftmostAndPreceding empty?) in (F ( [[1],[2,3],[],[4]] )) = Some([],[[1],[2,3]]));
    tester ("(findLeftmostAndPreceding empty? ( [[1],[2,3],[4]] )) = None", (findLeftmostAndPreceding empty? ( [[1],[2,3],[4]] )) = None);
    tester ("let F = id ( findLeftmostAndPreceding empty?) in (F ( [[1],[2,3],[4]] )) = None", let F = id ( findLeftmostAndPreceding empty?) in (F ( [[1],[2,3],[4]] )) = None);
% List [ 78]:  op [a] splitAtLeftmost (p: a -> Bool) (l: List a) : Option (List a * a * List a)
    tester ("(splitAtLeftmost empty? ( [[1],[2,3],[],[4]] )) = Some([[1],[2,3]],[],[[4]])", (splitAtLeftmost empty? ( [[1],[2,3],[],[4]] )) = Some([[1],[2,3]],[],[[4]]));
    tester ("let F = id (splitAtLeftmost empty?) in (F ( [[1],[2,3],[],[4]] )) = Some([[1],[2,3]],[],[[4]])", let F = id (splitAtLeftmost empty?) in (F ( [[1],[2,3],[],[4]] )) = Some([[1],[2,3]],[],[[4]]));
    tester ("(splitAtLeftmost empty? ( [[1],[2,3],[4]] )) = None", (splitAtLeftmost empty? ( [[1],[2,3],[4]] )) = None);
    tester ("let F = id (splitAtLeftmost empty?) in (F ( [[1],[2,3],[4]] )) = None", let F = id (splitAtLeftmost empty?) in (F ( [[1],[2,3],[4]] )) = None);
% List [ 80]:  op [a] leftmostPositionOfSublistAndFollowing (subl: List a, supl: List a) : Option (Nat * List a)
    tester ("(leftmostPositionOfSublistAndFollowing ([],[3,1,4,1,5])) = Some(0,[3,1,4,1,5])", (leftmostPositionOfSublistAndFollowing ( [], [3,1,4,1,5] )) = Some(0,[3,1,4,1,5]));
    tester ("let A = id ([], [3,1,4,1,5]) in (leftmostPositionOfSublistAndFollowing A) = Some(0,[3,1,4,1,5])", let A = id ( [], [3,1,4,1,5] ) in (leftmostPositionOfSublistAndFollowing A) = Some(0,[3,1,4,1,5]));
    tester ("(leftmostPositionOfSublistAndFollowing ( [1,4], [3,1,4,1,5] )) = Some(1,[1,5])", (leftmostPositionOfSublistAndFollowing ( [1,4], [3,1,4,1,5] )) = Some(1,[1,5]));
    tester ("let A = id ( [1,4], [3,1,4,1,5] ) in (leftmostPositionOfSublistAndFollowing A) = Some(1,[1,5])", let A = id ( [1,4], [3,1,4,1,5] ) in (leftmostPositionOfSublistAndFollowing A) = Some(1,[1,5]));
    tester ("(leftmostPositionOfSublistAndFollowing ( [1,3], [3,1,4,1,5] )) = None", (leftmostPositionOfSublistAndFollowing ( [1,3], [3,1,4,1,5] )) = None);
    tester ("let A = id ( [1,3], [3,1,4,1,5] ) in (leftmostPositionOfSublistAndFollowing A) = None", let A = id ( [1,3], [3,1,4,1,5] ) in (leftmostPositionOfSublistAndFollowing A) = None);
% List [ 81]:  op compare         : fa(a)  (a * a -> Comparison) -> List a * List a -> Comparison
    tester ("(compare ( compare ) ( [], [1] )) = Less", (compare ( compare ) ( [], [1] )) = Less);
    tester ("let F = id ( compare ( compare )) in (F ( [], [1] )) = Less", let F = id ( compare ( compare )) in (F ( [], [1] )) = Less);
    tester ("(compare ( compare ) ( [0,9], [1] )) = Less", (compare ( compare ) ( [0,9], [1] )) = Less);
    tester ("let F = id ( compare ( compare )) in (F ( [0,9], [1] )) = Less", let F = id ( compare ( compare )) in (F ( [0,9], [1] )) = Less);
    tester ("(compare ( compare ) ( [1], [1] )) = Equal", (compare ( compare ) ( [1], [1] )) = Equal);
    tester ("let F = id ( compare ( compare )) in (F ( [1], [1] )) = Equal", let F = id ( compare ( compare )) in (F ( [1], [1] )) = Equal);
    tester ("(compare ( compare ) ( [1,0], [1] )) = Greater", (compare ( compare ) ( [1,0], [1] )) = Greater);
    tester ("let F = id ( compare ( compare )) in (F ( [1,0], [1] )) = Greater", let F = id ( compare ( compare )) in (F ( [1,0], [1] )) = Greater);
% List [134]:  op show    : String -> List String -> String
    tester ("(show ( \"ns\" ) ( [\"no\",\"e\",\"e\"] )) = \"nonsense\"", (show ( "ns" ) ( ["no","e","e"] )) = "nonsense");
    tester ("let F = id ( show ( \"ns\" )) in (F ( [\"no\",\"e\",\"e\"] )) = \"nonsense\"", let F = id ( show ( "ns" )) in (F ( ["no","e","e"] )) = "nonsense");

% Nat [ 84]:  op succ    : Nat -> Nat
    tester ("(succ ( 6 )) = 7", (succ ( 6 )) = 7);
% Nat [ 85]:  op pred    : Nat -> Int
    tester ("(pred ( 7 )) = 6", (pred ( 7 )) = 6);
% Nat [ 86]:  op zero    : Nat 
    tester ("(zero) = 0", (zero) = 0);
% Nat [ 87]:  op one     : Nat
    tester ("(one) = 1", (one) = 1);
%% % Nat [ 88]:  op two     : Nat
%% %    tester ("(two) = 2", (two) = 2);
% Nat [ 89]:  op posNat? : Nat -> Bool
    tester ("(posNat? ( 0 )) = false", (posNat? ( 0 )) = false);
    tester ("(posNat? ( 1 )) = true", (posNat? ( 1 )) = true);
% Nat [133]:  op show     : Nat -> String
    tester ("(Nat.show ( 123 )) = \"123\"", (Nat.show ( 123 )) = "123");
% Nat [126]:  op natToString  : Nat -> String
    tester ("(natToString ( 123 )) = \"123\"", (natToString ( 123 )) = "123");
% Nat [126.5]:  op natConvertible : String -> Bool
    tester ("(natConvertible ( \"123\" )) = true", (natConvertible ( "123" )) = true);
    tester ("(natConvertible ( \"-123\" )) = false", (natConvertible ( "-123" )) = false);
    tester ("(natConvertible ( \"000\" )) = true", (natConvertible ( "000" )) = true);
    tester ("(natConvertible ( \"\" )) = false", (natConvertible ( "" )) = false);
    tester ("(natConvertible ( \"123.00\" )) = false", (natConvertible ( "123.00" )) = false);
% Nat [127]:  op stringToNat  : (String | natConvertible) -> Nat

% Option [ 96]:  op some?     : fa(a) Option a -> Bool
    tester ("(some? ( None )) = false", (some? ( None )) = false);
    tester ("(some? ( Some(1) )) = true", (some? ( Some(1) )) = true);
% Option [ 97]:  op none?     : fa(a) Option a -> Bool
    tester ("(none? ( None )) = true", (none? ( None )) = true);
    tester ("(none? ( Some(1) )) = false", (none? ( Some(1) )) = false);
% Option [ 98]:  op compare   : fa(a) (a * a -> Comparison) -> Option a * Option a -> Comparison
    tester ("(compare ( compare ) ( None, None )) = Equal", (compare ( Integer.compare ) ( None, None )) = Equal);
    tester ("let F = id ( compare ( compare )) in (F ( None, None )) = Equal", let F = id ( compare ( Integer.compare )) in (F ( None, None )) = Equal);
    tester ("(compare ( compare ) ( None, Some(1) )) = Less", (compare ( compare ) ( None, Some(1) )) = Less);
    tester ("let F = id ( compare ( compare )) in (F ( None, Some(1) )) = Less", let F = id ( compare ( compare )) in (F ( None, Some(1) )) = Less);
    tester ("(compare ( compare ) ( Some(1), None )) = Greater", (compare ( compare ) ( Some(1), None )) = Greater);
    tester ("let F = id ( compare ( compare )) in (F ( Some(1), None )) = Greater", let F = id ( compare ( compare )) in (F ( Some(1), None )) = Greater);
    tester ("(compare ( compare ) ( Some(0), Some(1) )) = Less", (compare ( compare ) ( Some(0), Some(1) )) = Less);
    tester ("let F = id ( compare ( compare )) in (F ( Some(0), Some(1) )) = Less", let F = id ( compare ( compare )) in (F ( Some(0), Some(1) )) = Less);
    tester ("(compare ( compare ) ( Some(1), Some(1) )) = Equal", (compare ( compare ) ( Some(1), Some(1) )) = Equal);
    tester ("let F = id ( compare ( compare )) in (F ( Some(1), Some(1) )) = Equal", let F = id ( compare ( compare )) in (F ( Some(1), Some(1) )) = Equal);
    tester ("(compare ( compare ) ( Some(2), Some(1) )) = Greater", (compare ( compare ) ( Some(2), Some(1) )) = Greater);
    tester ("let F = id ( compare ( compare )) in (F ( Some(2), Some(1) )) = Greater", let F = id ( compare ( compare )) in (F ( Some(2), Some(1) )) = Greater);
% Option [ 99]:  op mapOption : fa(a,b) (a -> b) -> Option a -> Option b
    tester ("(mapOption ( succ ) ( None )) = None", (mapOption ( succ ) ( None )) = None);
    tester ("let F = id ( mapOption ( succ )) in (F ( None )) = None", let F = id ( mapOption ( succ )) in (F ( None )) = None);
    tester ("(mapOption ( succ ) ( Some(0) )) = Some(1)", (mapOption ( succ ) ( Some(0) )) = Some(1));
    tester ("let F = id ( mapOption ( succ )) in (F ( Some(0) )) = Some(1)", let F = id ( mapOption ( succ )) in (F ( Some(0) )) = Some(1));
% Option [131]:  op show  : fa(a) (a -> String) -> Option a -> String
    tester ("(show ( natToString ) ( None )) = \"None\"", (show ( natToString ) ( None )) = "None");
    tester ("let F = id ( show ( natToString )) in (F ( None )) = \"None\"", let F = id ( show ( natToString )) in (F ( None )) = "None");
    tester ("(show ( natToString ) ( Some(1) )) = \"(Some\\s1)\"", (show ( natToString ) ( Some(1) )) = "(Some\s1)");
    tester ("let F = id ( show ( natToString )) in (F ( Some(1) )) = \"(Some\\s1)\"", let F = id ( show ( natToString )) in (F ( Some(1) )) = "(Some\s1)");

% String [100]:  op explode : String -> List Char
    tester ("(explode ( \"\" )) = []", (explode ( "" )) = []);
    tester ("(explode ( \"abc\" )) = [#a,#b,#c]", (explode ( "abc" )) = [#a,#b,#c]);
% String [102]:  op implode       : List Char -> String
    tester ("(implode ( [] )) = \"\"", (implode ( [] )) = "");
    tester ("(implode ( [#a,#b,#c] )) = \"abc\"", (implode ( [#a,#b,#c] )) = "abc");
% String [103]:  op length        : String -> Nat
    tester ("(length ( \"\" )) = 0", (length ( "" )) = 0);
    tester ("(length ( \"abc\" )) = 3", (length ( "abc" )) = 3);
% String [106]:  op ^  infixl 25  : String * String -> String
    tester ("(^ ( \"now\", \"here\" )) = \"nowhere\"", (^ ( "now", "here" )) = "nowhere");
    tester ("let A = id ( \"now\", \"here\" ) in (^ A) = \"nowhere\"", let A = id ( "now", "here" ) in (^ A) = "nowhere");
% String [107]:  op map           : (Char -> Char) -> String -> String
    tester ("(map ( fn(c)->chr(96+(let(v)=(ord(c)-96)in((v+13)mod(26)))) ) ( \"terra\" )) = \"green\"", (map ( fn(c)->chr(96+(let(v)=(ord(c)-96)in((v+13)mod(26)))) ) ( "terra" )) = "green");
    tester ("let F = id ( map ( fn(c)->chr(96+(let(v)=(ord(c)-96)in((v+13)mod(26)))) )) in (F ( \"terra\" )) = \"green\"", let F = id ( map ( fn(c)->chr(96+(let(v)=(ord(c)-96)in((v+13)mod(26)))) )) in (F ( "terra" )) = "green");
% String [108]:  op exists? (p: Char -> Bool) (s: String) : Bool
    tester ("(exists? isNum \"\") = false", (exists? isNum "") = false);
    tester ("let F = id ( exists? isNum) in (F ( \"\" )) = false", let F = id ( exists? isNum) in (F "") = false);
    tester ("(exists? isNum \"c3po\") = true", (exists? isNum "c3po") = true);
    tester ("let F = id ( exists? isNum) in (F ( \"c3po\" )) = true", let F = id ( exists? isNum) in (F "c3po" ) = true);
% String [109]:  op forall?           : (Char -> Bool) -> String -> Bool
    tester ("(forall? isAlpha \"\" ) = true", (forall? isAlpha "" ) = true);
    tester ("let F = id ( forall? isAlpha ) in (F ( \"\" )) = true", let F = id ( forall? isAlpha ) in (F "" ) = true);
    tester ("(forall? isAlpha \"c3po\" ) = false", (forall? isAlpha "c3po" ) = false);
    tester ("let F = id ( forall? isAlpha ) in (F ( \"c3po\" )) = false", let F = id ( forall? isAlpha ) in (F "c3po" ) = false);
% String [110]:  op @ (s:String, i:Nat | i < length s) infixl 30 : Char
    tester ("(\"afn\" @ 1) = #f", ("afn" @ 1) = #f);
    tester ("let A = id ( \"afn\", 1 ) in (@ A) = #f", let A = id ( "afn", 1 ) in (@ A) = #f);
% String [111]:  op subFromTo (s:String, i:Nat, j:Nat | i <= j && j <= length s) : String
    tester ("(subFromTo ( \"twitchy\", 2, 6 )) = \"itch\"", subFromTo ( "twitchy", 2, 6 ) = "itch");
    tester ("let A = id ( \"twitchy\", 2, 6 ) in (subFromTo A) = \"itch\"", let A = id ( "twitchy", 2, 6 ) in (subFromTo A) = "itch");
% String [112]:  op flatten (ss: List String) : String
    tester ("(flatten []) = \"\"", (flatten []) = "");
    tester ("(flatten [\"now\",\"here\"]) = \"nowhere\"", flatten ["now","here"] = "nowhere");
% String [113]:  op translate     : (Char -> String) -> String -> String
    tester ("(translate ( fn(c)->implode[c,c] ) ( \"2B\" )) = \"22BB\"", (translate ( fn(c)->implode[c,c] ) ( "2B" )) = "22BB");
    tester ("let F = id ( translate ( fn(c)->implode[c,c] )) in (F ( \"2B\" )) = \"22BB\"", let F = id ( translate ( fn(c)->implode[c,c] )) in (F ( "2B" )) = "22BB");
% String [114]:  op <  infixl 20 : String * String -> Bool
    tester ("(< ( \"\", \"\" )) = false", (< ( "", "" )) = false);
    tester ("let A = id ( \"\", \"\" ) in (< A) = false", let A = id ( "", "" ) in (< A) = false);
    tester ("(< ( \"\", \"1\" )) = true", (< ( "", "1" )) = true);
    tester ("let A = id ( \"\", \"1\" ) in (< A) = true", let A = id ( "", "1" ) in (< A) = true);
    tester ("(< ( \"0\", \"1\" )) = true", (< ( "0", "1" )) = true);
    tester ("let A = id ( \"0\", \"1\" ) in (< A) = true", let A = id ( "0", "1" ) in (< A) = true);
    tester ("(< ( \"09\", \"1\" )) = true", (< ( "09", "1" )) = true);
    tester ("let A = id ( \"09\", \"1\" ) in (< A) = true", let A = id ( "09", "1" ) in (< A) = true);
    tester ("(< ( \"1\", \"\" )) = false", (< ( "1", "" )) = false);
    tester ("let A = id ( \"1\", \"\" ) in (< A) = false", let A = id ( "1", "" ) in (< A) = false);
    tester ("(< ( \"1\", \"1\" )) = false", (< ( "1", "1" )) = false);
    tester ("let A = id ( \"1\", \"1\" ) in (< A) = false", let A = id ( "1", "1" ) in (< A) = false);
    tester ("(< ( \"10\", \"1\" )) = false", (< ( "10", "1" )) = false);
    tester ("let A = id ( \"10\", \"1\" ) in (< A) = false", let A = id ( "10", "1" ) in (< A) = false);
    tester ("(< ( \"2\", \"1\" )) = false", (< ( "2", "1" )) = false);
    tester ("let A = id ( \"2\", \"1\" ) in (< A) = false", let A = id ( "2", "1" ) in (< A) = false);
% String [115]:  op <= infixl 20 : String * String -> Bool
    tester ("(<= ( \"\", \"\" )) = true", (<= ( "", "" )) = true);
    tester ("let A = id ( \"\", \"\" ) in (<= A) = true", let A = id ( "", "" ) in (<= A) = true);
    tester ("(<= ( \"\", \"1\" )) = true", (<= ( "", "1" )) = true);
    tester ("let A = id ( \"\", \"1\" ) in (<= A) = true", let A = id ( "", "1" ) in (<= A) = true);
    tester ("(<= ( \"0\", \"1\" )) = true", (<= ( "0", "1" )) = true);
    tester ("let A = id ( \"0\", \"1\" ) in (<= A) = true", let A = id ( "0", "1" ) in (<= A) = true);
    tester ("(<= ( \"09\", \"1\" )) = true", (<= ( "09", "1" )) = true);
    tester ("let A = id ( \"09\", \"1\" ) in (<= A) = true", let A = id ( "09", "1" ) in (<= A) = true);
    tester ("(<= ( \"1\", \"\" )) = false", (<= ( "1", "" )) = false);
    tester ("let A = id ( \"1\", \"\" ) in (<= A) = false", let A = id ( "1", "" ) in (<= A) = false);
    tester ("(<= ( \"1\", \"1\" )) = true", (<= ( "1", "1" )) = true);
    tester ("let A = id ( \"1\", \"1\" ) in (<= A) = true", let A = id ( "1", "1" ) in (<= A) = true);
    tester ("(<= ( \"10\", \"1\" )) = false", (<= ( "10", "1" )) = false);
    tester ("let A = id ( \"10\", \"1\" ) in (<= A) = false", let A = id ( "10", "1" ) in (<= A) = false);
    tester ("(<= ( \"2\", \"1\" )) = false", (<= ( "2", "1" )) = false);
    tester ("let A = id ( \"2\", \"1\" ) in (<= A) = false", let A = id ( "2", "1" ) in (<= A) = false);
% String [116]:  op newline       : String
    tester ("(newline) = \"\\n\"", (newline) = "\n");
% String [119]:  op compare : String * String -> Comparison
    tester ("(compare ( \"\", \"\" )) = Equal", (compare ( "", "" )) = Equal);
    tester ("let A = id ( \"\", \"\" ) in (compare A) = Equal", let A = id ( "", "" ) in (compare A) = Equal);
    tester ("(compare ( \"\", \"1\" )) = Less", (compare ( "", "1" )) = Less);
    tester ("let A = id ( \"\", \"1\" ) in (compare A) = Less", let A = id ( "", "1" ) in (compare A) = Less);
    tester ("(compare ( \"0\", \"1\" )) = Less", (compare ( "0", "1" )) = Less);
    tester ("let A = id ( \"0\", \"1\" ) in (compare A) = Less", let A = id ( "0", "1" ) in (compare A) = Less);
    tester ("(compare ( \"09\", \"1\" )) = Less", (compare ( "09", "1" )) = Less);
    tester ("let A = id ( \"09\", \"1\" ) in (compare A) = Less", let A = id ( "09", "1" ) in (compare A) = Less);
    tester ("(compare ( \"1\", \"\" )) = Greater", (compare ( "1", "" )) = Greater);
    tester ("let A = id ( \"1\", \"\" ) in (compare A) = Greater", let A = id ( "1", "" ) in (compare A) = Greater);
    tester ("(compare ( \"1\", \"1\" )) = Equal", (compare ( "1", "1" )) = Equal);
    tester ("let A = id ( \"1\", \"1\" ) in (compare A) = Equal", let A = id ( "1", "1" ) in (compare A) = Equal);
    tester ("(compare ( \"10\", \"1\" )) = Greater", (compare ( "10", "1" )) = Greater);
    tester ("let A = id ( \"10\", \"1\" ) in (compare A) = Greater", let A = id ( "10", "1" ) in (compare A) = Greater);
    tester ("(compare ( \"2\", \"1\" )) = Greater", (compare ( "2", "1" )) = Greater);
    tester ("let A = id ( \"2\", \"1\" ) in (compare A) = Greater", let A = id ( "2", "1" ) in (compare A) = Greater);
    () )

endspec
