spec
  def verbose = false
  op tester : String * Boolean -> ()
  def tester (what, test) =
    if verbose then
      writeLine((if test then "P: " else "F: ")^what)
    else
      if test then ()
      else writeLine("F: "^what)

  def alltests : () = (% Boolean [  1]:  op ~             : Boolean -> Boolean
    tester ("(~ ( true )) = false", (~ ( true )) = false);
    tester ("(~ ( false )) = true", (~ ( false )) = true);
% Boolean [  2]:  op &   infixr 15 : Boolean * Boolean -> Boolean 
    tester ("(& ( false , false )) = false", (& ( false , false )) = false);
    tester ("let A = id ( false , false ) in (& A) = false", let A = id ( false , false ) in (& A) = false);
    tester ("(& ( false , true )) = false", (& ( false , true )) = false);
    tester ("let A = id ( false , true ) in (& A) = false", let A = id ( false , true ) in (& A) = false);
    tester ("(& ( true , false )) = false", (& ( true , false )) = false);
    tester ("let A = id ( true , false ) in (& A) = false", let A = id ( true , false ) in (& A) = false);
    tester ("(& ( true , true )) = true", (& ( true , true )) = true);
    tester ("let A = id ( true , true ) in (& A) = true", let A = id ( true , true ) in (& A) = true);
% Boolean [  3]:  op or  infixr 14 : Boolean * Boolean -> Boolean 
    tester ("(or ( false , false )) = false", (or ( false , false )) = false);
    tester ("let A = id ( false , false ) in (or A) = false", let A = id ( false , false ) in (or A) = false);
    tester ("(or ( false , true )) = true", (or ( false , true )) = true);
    tester ("let A = id ( false , true ) in (or A) = true", let A = id ( false , true ) in (or A) = true);
    tester ("(or ( true , false )) = true", (or ( true , false )) = true);
    tester ("let A = id ( true , false ) in (or A) = true", let A = id ( true , false ) in (or A) = true);
    tester ("(or ( true , true )) = true", (or ( true , true )) = true);
    tester ("let A = id ( true , true ) in (or A) = true", let A = id ( true , true ) in (or A) = true);
% Boolean [  4]:  op =>  infixr 13 : Boolean * Boolean -> Boolean 
    tester ("(=> ( false , false )) = true", (=> ( false , false )) = true);
    tester ("let A = id ( false , false ) in (=> A) = true", let A = id ( false , false ) in (=> A) = true);
    tester ("(=> ( false , true )) = true", (=> ( false , true )) = true);
    tester ("let A = id ( false , true ) in (=> A) = true", let A = id ( false , true ) in (=> A) = true);
    tester ("(=> ( true , false )) = false", (=> ( true , false )) = false);
    tester ("let A = id ( true , false ) in (=> A) = false", let A = id ( true , false ) in (=> A) = false);
    tester ("(=> ( true , true )) = true", (=> ( true , true )) = true);
    tester ("let A = id ( true , true ) in (=> A) = true", let A = id ( true , true ) in (=> A) = true);
% Boolean [  5]:  op <=> infixr 12 : Boolean * Boolean -> Boolean 
    tester ("(<=> ( false , false )) = true", (<=> ( false , false )) = true);
    tester ("let A = id ( false , false ) in (<=> A) = true", let A = id ( false , false ) in (<=> A) = true);
    tester ("(<=> ( false , true )) = false", (<=> ( false , true )) = false);
    tester ("let A = id ( false , true ) in (<=> A) = false", let A = id ( false , true ) in (<=> A) = false);
    tester ("(<=> ( true , false )) = false", (<=> ( true , false )) = false);
    tester ("let A = id ( true , false ) in (<=> A) = false", let A = id ( true , false ) in (<=> A) = false);
    tester ("(<=> ( true , true )) = true", (<=> ( true , true )) = true);
    tester ("let A = id ( true , true ) in (<=> A) = true", let A = id ( true , true ) in (<=> A) = true);
% Boolean [  6]:  op ~=  infixr 20 : fa(a) a * a -> Boolean
    tester ("(~= ( 4 , 4 )) = false", (~= ( 4 , 4 )) = false);
    tester ("let A = id ( 4 , 4 ) in (~= A) = false", let A = id ( 4 , 4 ) in (~= A) = false);
    tester ("(~= ( 4 , 5 )) = true", (~= ( 4 , 5 )) = true);
    tester ("let A = id ( 4 , 5 ) in (~= A) = true", let A = id ( 4 , 5 ) in (~= A) = true);
% Boolean [  7]:  op compare  : Boolean * Boolean -> Comparison
    tester ("(compare ( false , false )) = Equal", (compare ( false , false )) = Equal);
    tester ("let A = id ( false , false ) in (compare A) = Equal", let A = id ( false , false ) in (compare A) = Equal);
    tester ("(compare ( false , true )) = Less", (compare ( false , true )) = Less);
    tester ("let A = id ( false , true ) in (compare A) = Less", let A = id ( false , true ) in (compare A) = Less);
    tester ("(compare ( true , false )) = Greater", (compare ( true , false )) = Greater);
    tester ("let A = id ( true , false ) in (compare A) = Greater", let A = id ( true , false ) in (compare A) = Greater);
    tester ("(compare ( true , true )) = Equal", (compare ( true , true )) = Equal);
    tester ("let A = id ( true , true ) in (compare A) = Equal", let A = id ( true , true ) in (compare A) = Equal);
% Boolean [120]:  op toString : Boolean -> String  % deprecated
    tester ("(toString ( true )) = \"true\"", (toString ( true )) = "true");
    tester ("(toString ( false )) = \"false\"", (toString ( false )) = "false");
% Boolean [129]:  op show : Boolean -> String
    tester ("(show ( true )) = \"true\"", (show ( true )) = "true");
    tester ("(show ( false )) = \"false\"", (show ( false )) = "false");

% Char [ 10]:  op ord : Char -> {n : Nat | n < 256}
    tester ("(ord ( #A )) = 65", (ord ( #A )) = 65);
% Char [ 11]:  op chr : {n : Nat | n < 256} -> Char
    tester ("(chr ( 65 )) = #A", (chr ( 65 )) = #A);
% Char [ 12]:  op isUpperCase : Char -> Boolean
    tester ("(isUpperCase ( #! )) = false", (isUpperCase ( #! )) = false);
    tester ("(isUpperCase ( #3 )) = false", (isUpperCase ( #3 )) = false);
    tester ("(isUpperCase ( #A )) = true", (isUpperCase ( #A )) = true);
    tester ("(isUpperCase ( #a )) = false", (isUpperCase ( #a )) = false);
    tester ("(isUpperCase ( #\\xdd )) = true", (isUpperCase ( #\xdd )) = true);
    tester ("(isUpperCase ( #\\xff )) = false", (isUpperCase ( #\xff )) = false);
% Char [ 13]:  op isLowerCase : Char -> Boolean
    tester ("(isLowerCase ( #! )) = false", (isLowerCase ( #! )) = false);
    tester ("(isLowerCase ( #3 )) = false", (isLowerCase ( #3 )) = false);
    tester ("(isLowerCase ( #A )) = false", (isLowerCase ( #A )) = false);
    tester ("(isLowerCase ( #a )) = true", (isLowerCase ( #a )) = true);
    tester ("(isLowerCase ( #\\xdd )) = false", (isLowerCase ( #\xdd )) = false);
    tester ("(isLowerCase ( #\\xff )) = true", (isLowerCase ( #\xff )) = true);
% Char [ 14]:  op isAlpha     : Char -> Boolean
    tester ("(isAlpha ( #! )) = false", (isAlpha ( #! )) = false);
    tester ("(isAlpha ( #3 )) = false", (isAlpha ( #3 )) = false);
    tester ("(isAlpha ( #A )) = true", (isAlpha ( #A )) = true);
    tester ("(isAlpha ( #a )) = true", (isAlpha ( #a )) = true);
    tester ("(isAlpha ( #\\xff )) = true", (isAlpha ( #\xff )) = true);
% Char [ 15]:  op isNum       : Char -> Boolean
    tester ("(isNum ( #! )) = false", (isNum ( #! )) = false);
    tester ("(isNum ( #3 )) = true", (isNum ( #3 )) = true);
    tester ("(isNum ( #A )) = false", (isNum ( #A )) = false);
    tester ("(isNum ( #a )) = false", (isNum ( #a )) = false);
    tester ("(isNum ( #\\xff )) = false", (isNum ( #\xff )) = false);
% Char [ 16]:  op isAlphaNum  : Char -> Boolean
    tester ("(isAlphaNum ( #! )) = false", (isAlphaNum ( #! )) = false);
    tester ("(isAlphaNum ( #3 )) = true", (isAlphaNum ( #3 )) = true);
    tester ("(isAlphaNum ( #A )) = true", (isAlphaNum ( #A )) = true);
    tester ("(isAlphaNum ( #a )) = true", (isAlphaNum ( #a )) = true);
    tester ("(isAlphaNum ( #\\xff )) = true", (isAlphaNum ( #\xff )) = true);
% Char [ 17]:  op isAscii     : Char -> Boolean
    tester ("(isAscii ( #! )) = true", (isAscii ( #! )) = true);
    tester ("(isAscii ( #3 )) = true", (isAscii ( #3 )) = true);
    tester ("(isAscii ( #A )) = true", (isAscii ( #A )) = true);
    tester ("(isAscii ( #a )) = true", (isAscii ( #a )) = true);
    tester ("(isAscii ( #\\xff )) = false", (isAscii ( #\xff )) = false);
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
    tester ("(compare ( #3 , #4 )) = Less", (compare ( #3 , #4 )) = Less);
    tester ("let A = id ( #3 , #4 ) in (compare A) = Less", let A = id ( #3 , #4 ) in (compare A) = Less);
    tester ("(compare ( #4 , #4 )) = Equal", (compare ( #4 , #4 )) = Equal);
    tester ("let A = id ( #4 , #4 ) in (compare A) = Equal", let A = id ( #4 , #4 ) in (compare A) = Equal);
    tester ("(compare ( #5 , #4 )) = Greater", (compare ( #5 , #4 )) = Greater);
    tester ("let A = id ( #5 , #4 ) in (compare A) = Greater", let A = id ( #5 , #4 ) in (compare A) = Greater);
% Char [123]:  op toString    : Char -> String     % deprecated
    tester ("(toString ( #A )) = \"A\"", (toString ( #A )) = "A");
% Char [135]:  op show    : Char -> String
    tester ("(show ( #A )) = \"A\"", (show ( #A )) = "A");

% Compare [ 23]:  op compare : Comparison * Comparison -> Comparison
    tester ("(compare ( Less , Less )) = Equal", (compare ( Less , Less )) = Equal);
    tester ("let A = id ( Less , Less ) in (compare A) = Equal", let A = id ( Less , Less ) in (compare A) = Equal);
    tester ("(compare ( Less , Equal )) = Less", (compare ( Less , Equal )) = Less);
    tester ("let A = id ( Less , Equal ) in (compare A) = Less", let A = id ( Less , Equal ) in (compare A) = Less);
    tester ("(compare ( Less , Greater )) = Less", (compare ( Less , Greater )) = Less);
    tester ("let A = id ( Less , Greater ) in (compare A) = Less", let A = id ( Less , Greater ) in (compare A) = Less);
    tester ("(compare ( Equal , Less )) = Greater", (compare ( Equal , Less )) = Greater);
    tester ("let A = id ( Equal , Less ) in (compare A) = Greater", let A = id ( Equal , Less ) in (compare A) = Greater);
    tester ("(compare ( Equal , Equal )) = Equal", (compare ( Equal , Equal )) = Equal);
    tester ("let A = id ( Equal , Equal ) in (compare A) = Equal", let A = id ( Equal , Equal ) in (compare A) = Equal);
    tester ("(compare ( Equal , Greater )) = Less", (compare ( Equal , Greater )) = Less);
    tester ("let A = id ( Equal , Greater ) in (compare A) = Less", let A = id ( Equal , Greater ) in (compare A) = Less);
    tester ("(compare ( Greater , Less )) = Greater", (compare ( Greater , Less )) = Greater);
    tester ("let A = id ( Greater , Less ) in (compare A) = Greater", let A = id ( Greater , Less ) in (compare A) = Greater);
    tester ("(compare ( Greater , Equal )) = Greater", (compare ( Greater , Equal )) = Greater);
    tester ("let A = id ( Greater , Equal ) in (compare A) = Greater", let A = id ( Greater , Equal ) in (compare A) = Greater);
    tester ("(compare ( Greater , Greater )) = Equal", (compare ( Greater , Greater )) = Equal);
    tester ("let A = id ( Greater , Greater ) in (compare A) = Equal", let A = id ( Greater , Greater ) in (compare A) = Equal);
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
% Functions [ 27]:  op injective?  : fa(a,b) (a -> b) -> Boolean
% Functions [ 28]:  op surjective? : fa(a,b) (a -> b) -> Boolean
% Functions [ 29]:  op bijective?  : fa(a,b) (a -> b) -> Boolean
% Functions [ 30]:  op inverse     : fa(a,b) Bijective(a,b) -> Bijective(b,a)

% Integer [ 31]:  op ~             : Integer -> Integer
    tester ("(- ( 3 )) = 0-3", (- ( 3 )) = 0-3);
% Integer [ 32]:  op +   infixl 25 : Integer * Integer -> Integer
    tester ("(+ ( 3 , 4 )) = 7", (+ ( 3 , 4 )) = 7);
    tester ("let A = id ( 3 , 4 ) in (+ A) = 7", let A = id ( 3 , 4 ) in (+ A) = 7);
% Integer [ 33]:  op -   infixl 25 : Integer * Integer -> Integer
    tester ("(- ( 7 , 4 )) = 3", (- ( 7 , 4 )) = 3);
    tester ("let A = id ( 7 , 4 ) in (- A) = 3", let A = id ( 7 , 4 ) in (- A) = 3);
% Integer [ 34]:  op *   infixl 27 : Integer * Integer -> Integer
    tester ("( * ( 3, 4 )) = 12", ( * ( 3, 4 )) = 12);
    tester ("let A = id ( 3, 4 ) in ( * A) = 12", let A = id ( 3, 4 ) in ( * A) = 12);
% Integer [ 35]:  op div infixl 26 : Integer * NZInteger -> Integer
    tester ("(div ( 27 , 10 )) = 2", (div ( 27 , 10 )) = 2);
    tester ("let A = id ( 27 , 10 ) in (div A) = 2", let A = id ( 27 , 10 ) in (div A) = 2);
% Integer [ 36]:  op rem infixl 26 : Integer * NZInteger -> Integer
    tester ("(rem ( 27 , 10 )) = 7", (rem ( 27 , 10 )) = 7);
    tester ("let A = id ( 27 , 10 ) in (rem A) = 7", let A = id ( 27 , 10 ) in (rem A) = 7);
% Integer [ 37]:  op <   infixl 20 : Integer * Integer -> Boolean
    tester ("(< ( 3 , 4 )) = true", (< ( 3 , 4 )) = true);
    tester ("let A = id ( 3 , 4 ) in (< A) = true", let A = id ( 3 , 4 ) in (< A) = true);
    tester ("(< ( 4 , 4 )) = false", (< ( 4 , 4 )) = false);
    tester ("let A = id ( 4 , 4 ) in (< A) = false", let A = id ( 4 , 4 ) in (< A) = false);
% Integer [ 38]:  op <=  infixl 20 : Integer * Integer -> Boolean
    tester ("(<= ( 3 , 3 )) = true", (<= ( 3 , 3 )) = true);
    tester ("let A = id ( 3 , 3 ) in (<= A) = true", let A = id ( 3 , 3 ) in (<= A) = true);
    tester ("(<= ( 4 , 3 )) = false", (<= ( 4 , 3 )) = false);
    tester ("let A = id ( 4 , 3 ) in (<= A) = false", let A = id ( 4 , 3 ) in (<= A) = false);
% Integer [ 39]:  op >  infixl 20 : Integer * Integer -> Boolean
    tester ("(> ( 4 , 3 )) = true", (> ( 4 , 3 )) = true);
    tester ("let A = id ( 4 , 3 ) in (> A) = true", let A = id ( 4 , 3 ) in (> A) = true);
    tester ("(> ( 4 , 4 )) = false", (> ( 4 , 4 )) = false);
    tester ("let A = id ( 4 , 4 ) in (> A) = false", let A = id ( 4 , 4 ) in (> A) = false);
% Integer [ 40]:  op >= infixl 20 : Integer * Integer -> Boolean
    tester ("(>= ( 3 , 3 )) = true", (>= ( 3 , 3 )) = true);
    tester ("let A = id ( 3 , 3 ) in (>= A) = true", let A = id ( 3 , 3 ) in (>= A) = true);
    tester ("(>= ( 3 , 4 )) = false", (>= ( 3 , 4 )) = false);
    tester ("let A = id ( 3 , 4 ) in (>= A) = false", let A = id ( 3 , 4 ) in (>= A) = false);
% Integer [ 41]:  op abs          : Integer -> Integer
    tester ("(abs ( - 3 )) = 3", (abs ( - 3 )) = 3);
    tester ("(abs ( 3 )) = 3", (abs ( 3 )) = 3);
% Integer [ 42]:  op min          : Integer * Integer -> Integer
    tester ("(min ( 3 , 4 )) = 3", (min ( 3 , 4 )) = 3);
    tester ("let A = id ( 3 , 4 ) in (min A) = 3", let A = id ( 3 , 4 ) in (min A) = 3);
% Integer [ 43]:  op max          : Integer * Integer -> Integer
    tester ("(max ( 3 , 4 )) = 4", (max ( 3 , 4 )) = 4);
    tester ("let A = id ( 3 , 4 ) in (max A) = 4", let A = id ( 3 , 4 ) in (max A) = 4);
% Integer [ 44]:  op compare      : Integer * Integer -> Comparison
    tester ("(compare ( 3 , 4 )) = Less", (compare ( 3 , 4 )) = Less);
    tester ("let A = id ( 3 , 4 ) in (compare A) = Less", let A = id ( 3 , 4 ) in (compare A) = Less);
    tester ("(compare ( 4 , 4 )) = Equal", (compare ( 4 , 4 )) = Equal);
    tester ("let A = id ( 4 , 4 ) in (compare A) = Equal", let A = id ( 4 , 4 ) in (compare A) = Equal);
    tester ("(compare ( 5 , 4 )) = Greater", (compare ( 5 , 4 )) = Greater);
    tester ("let A = id ( 5 , 4 ) in (compare A) = Greater", let A = id ( 5 , 4 ) in (compare A) = Greater);
% Integer [121]:  op toString : Integer -> String  % deprecated
    tester ("(toString ( 123 )) = \"123\"", (toString ( 123 )) = "123");
% Integer [132]:  op show : Integer -> String
    tester ("(Integer.show ( 123 )) = \"123\"", (Integer.show ( 123 )) = "123");
% Integer [124]:  op intToString    : Integer -> String
    tester ("(intToString ( 123 )) = \"123\"", (intToString ( 123 )) = "123");
% Integer [124.5]:  op intConvertible : String -> Boolean
    tester ("(intConvertible ( \"123\" )) = true", (intConvertible ( "123" )) = true);
    tester ("(intConvertible ( \"-123\" )) = true", (intConvertible ( "-123" )) = true);
    tester ("(intConvertible ( \"000\" )) = true", (intConvertible ( "000" )) = true);
    tester ("(intConvertible ( \"\" )) = false", (intConvertible ( "" )) = false);
    tester ("(intConvertible ( \"123.00\" )) = false", (intConvertible ( "123.00" )) = false);
% Integer [125]:  op stringToInt    : (String | intConvertible) -> Integer
    tester ("(stringToInt ( \"123\" )) = 123", (stringToInt ( "123" )) = 123);
    tester ("(stringToInt ( \"-123\" )) = -123", (stringToInt ( "-123" )) = -123);
% List [ 49]:  op nil             : fa(a)   List a
    tester ("(nil) = []", (nil) = []);
% List [ 50]:  op cons            : fa(a)   a * List a -> List a
    tester ("(cons ( 3 , [4] )) = [3,4]", (cons ( 3 , [4] )) = [3,4]);
    tester ("let A = id ( 3 , [4] ) in (cons A) = [3,4]", let A = id ( 3 , [4] ) in (cons A) = [3,4]);
% List [ 51]:  op insert          : fa(a)   a * List a -> List a
    tester ("(insert ( 3 , [4] )) = [3,4]", (insert ( 3 , [4] )) = [3,4]);
    tester ("let A = id ( 3 , [4] ) in (insert A) = [3,4]", let A = id ( 3 , [4] ) in (insert A) = [3,4]);
% List [ 52]:  op length          : fa(a)   List a -> Nat
    tester ("(length ( [3,4] )) = 2", (length ( [3,4] )) = 2);
% List [ 53]:  op null            : fa(a)   List a -> Boolean
    tester ("(null ( nil )) = true", (null ( nil )) = true);
    tester ("(null ( [3] )) = false", (null ( [3] )) = false);
% List [ 54]:  op hd              : fa(a)   {l : List a | ~(null l)} -> a
    tester ("(hd ( [3,4] )) = 3", (hd ( [3,4] )) = 3);
% List [ 55]:  op tl              : fa(a)   {l : List a | ~(null l)} -> List a
    tester ("(tl ( [3,4] )) = [4]", (tl ( [3,4] )) = [4]);
% List [ 56]:  op concat          : fa(a)   List a * List a -> List a
    tester ("(concat ( [3] , [4] )) = [3,4]", (concat ( [3] , [4] )) = [3,4]);
    tester ("let A = id ( [3] , [4] ) in (concat A) = [3,4]", let A = id ( [3] , [4] ) in (concat A) = [3,4]);
% List [ 57]:  op ++ infixl 11    : fa(a)   List a * List a -> List a
    tester ("(++ ( [3] , [4] )) = [3,4]", (++ ( [3] , [4] )) = [3,4]);
    tester ("let A = id ( [3] , [4] ) in (++ A) = [3,4]", let A = id ( [3] , [4] ) in (++ A) = [3,4]);
% List [ 58]:  op @  infixl 11    : fa(a)   List a * List a -> List a
    tester ("(@ ( [3] , [4] )) = [3,4]", (@ ( [3] , [4] )) = [3,4]);
    tester ("let A = id ( [3] , [4] ) in (@ A) = [3,4]", let A = id ( [3] , [4] ) in (@ A) = [3,4]);
% List [ 59]:  op nth             : fa(a)   {(l,i) : List a * Nat | i < length l} -> a
    tester ("(nth ( [3,4,5] , 1 )) = 4", (nth ( [3,4,5] , 1 )) = 4);
    tester ("let A = id ( [3,4,5] , 1 ) in (nth A) = 4", let A = id ( [3,4,5] , 1 ) in (nth A) = 4);
% List [ 60]:  op nthTail         : fa(a)   {(l,i) : List a * Nat | i < length l} -> List a
    tester ("(nthTail ( [3,4,5] , 1 )) = [5]", (nthTail ( [3,4,5] , 1 )) = [5]);
    tester ("let A = id ( [3,4,5] , 1 ) in (nthTail A) = [5]", let A = id ( [3,4,5] , 1 ) in (nthTail A) = [5]);
% List [ 61]:  op member          : fa(a)   a * List a -> Boolean
    tester ("(member ( 4 , [3,5,7] )) = false", (member ( 4 , [3,5,7] )) = false);
    tester ("let A = id ( 4 , [3,5,7] ) in (member A) = false", let A = id ( 4 , [3,5,7] ) in (member A) = false);
    tester ("(member ( 5 , [3,5,7] )) = true", (member ( 5 , [3,5,7] )) = true);
    tester ("let A = id ( 5 , [3,5,7] ) in (member A) = true", let A = id ( 5 , [3,5,7] ) in (member A) = true);
% List [ 62]:  op sublist         : fa(a)   {(l,i,j) : List a * Nat * Nat | i < j & j <= length l} -> List a
    tester ("(sublist ( [3,1,4,1,5,9] , 2 , 4 )) = [4,1]", (sublist ( [3,1,4,1,5,9] , 2 , 4 )) = [4,1]);
    tester ("let A = id ( [3,1,4,1,5,9] , 2 , 4 ) in (sublist A) = [4,1]", let A = id ( [3,1,4,1,5,9] , 2 , 4 ) in (sublist A) = [4,1]);
% List [ 63]:  op map             : fa(a,b) (a -> b) -> List a -> List b
    tester ("(map ( succ ) ( [3,4,5] )) = [4,5,6]", (map ( succ ) ( [3,4,5] )) = [4,5,6]);
    tester ("let F = id ( map ( succ )) in (F ( [3,4,5] )) = [4,5,6]", let F = id ( map ( succ )) in (F ( [3,4,5] )) = [4,5,6]);
% List [ 64]:  op mapPartial      : fa(a,b) (a -> Option b) -> List a -> List b
    tester ("(mapPartial ( fn(n)->if(n<1)then(None)else(Some(pred(n))) ) ( [5,0,2] )) = [4,1]", (mapPartial ( fn(n)->if(n<1)then(None)else(Some(pred(n))) ) ( [5,0,2] )) = [4,1]);
    tester ("let F = id ( mapPartial ( fn(n)->if(n<1)then(None)else(Some(pred(n))) )) in (F ( [5,0,2] )) = [4,1]", let F = id ( mapPartial ( fn(n)->if(n<1)then(None)else(Some(pred(n))) )) in (F ( [5,0,2] )) = [4,1]);
% List [ 65]:  op foldl           : fa(a,b) (a * b -> b) -> b -> List a -> b
    tester ("(foldl ( fn(m,n)->(m)rem(n) ) ( 20 ) ( [77,47] )) = 13", (foldl ( fn(m,n)->(m)rem(n) ) ( 20 ) ( [77,47] )) = 13);
    tester ("let F = id ( foldl ( fn(m,n)->(m)rem(n) )) in (F ( 20 ) ( [77,47] )) = 13", let F = id ( foldl ( fn(m,n)->(m)rem(n) )) in (F ( 20 ) ( [77,47] )) = 13);
% List [ 66]:  op foldr           : fa(a,b) (a * b -> b) -> b -> List a -> b
    tester ("(foldr ( fn(m,n)->(m)rem(n) ) ( 77 ) ( [27,91] )) = 13", (foldr ( fn(m,n)->(m)rem(n) ) ( 77 ) ( [27,91] )) = 13);
    tester ("let F = id ( foldr ( fn(m,n)->(m)rem(n) )) in (F ( 77 ) ( [27,91] )) = 13", let F = id ( foldr ( fn(m,n)->(m)rem(n) )) in (F ( 77 ) ( [27,91] )) = 13);
% List [ 67]:  op exists          : fa(a)   (a -> Boolean) -> List a -> Boolean
    tester ("(exists ( posNat? ) ( [] )) = false", (exists ( posNat? ) ( [] )) = false);
    tester ("let F = id ( exists ( posNat? )) in (F ( [] )) = false", let F = id ( exists ( posNat? )) in (F ( [] )) = false);
    tester ("(exists ( posNat? ) ( [0,0,0] )) = false", (exists ( posNat? ) ( [0,0,0] )) = false);
    tester ("let F = id ( exists ( posNat? )) in (F ( [0,0,0] )) = false", let F = id ( exists ( posNat? )) in (F ( [0,0,0] )) = false);
    tester ("(exists ( posNat? ) ( [0,1,0] )) = true", (exists ( posNat? ) ( [0,1,0] )) = true);
    tester ("let F = id ( exists ( posNat? )) in (F ( [0,1,0] )) = true", let F = id ( exists ( posNat? )) in (F ( [0,1,0] )) = true);
% List [ 68]:  op all             : fa(a)   (a -> Boolean) -> List a -> Boolean
    tester ("(all ( posNat? ) ( [] )) = true", (all ( posNat? ) ( [] )) = true);
    tester ("let F = id ( all ( posNat? )) in (F ( [] )) = true", let F = id ( all ( posNat? )) in (F ( [] )) = true);
    tester ("(all ( posNat? ) ( [1,1,1] )) = true", (all ( posNat? ) ( [1,1,1] )) = true);
    tester ("let F = id ( all ( posNat? )) in (F ( [1,1,1] )) = true", let F = id ( all ( posNat? )) in (F ( [1,1,1] )) = true);
    tester ("(all ( posNat? ) ( [1,0,1] )) = false", (all ( posNat? ) ( [1,0,1] )) = false);
    tester ("let F = id ( all ( posNat? )) in (F ( [1,0,1] )) = false", let F = id ( all ( posNat? )) in (F ( [1,0,1] )) = false);
% List [ 69]:  op filter          : fa(a)   (a -> Boolean) -> List a -> List a
    tester ("(filter ( posNat? ) ( [5,0,2] )) = [5,2]", (filter ( posNat? ) ( [5,0,2] )) = [5,2]);
    tester ("let F = id ( filter ( posNat? )) in (F ( [5,0,2] )) = [5,2]", let F = id ( filter ( posNat? )) in (F ( [5,0,2] )) = [5,2]);
% List [ 70]:  op diff            : fa(a)   List a * List a -> List a
    tester ("(diff ( [3,1,4,1,5,9] , [5,9,2,1] )) = [3,4]", (diff ( [3,1,4,1,5,9] , [5,9,2,1] )) = [3,4]);
    tester ("let A = id ( [3,1,4,1,5,9] , [5,9,2,1] ) in (diff A) = [3,4]", let A = id ( [3,1,4,1,5,9] , [5,9,2,1] ) in (diff A) = [3,4]);
% List [ 71]:  op rev             : fa(a)   List a -> List a
    tester ("(rev ( [1,2,3] )) = [3,2,1]", (rev ( [1,2,3] )) = [3,2,1]);
% List [ 72]:  op rev2            : fa(a)   List a * List a -> List a
    tester ("(rev2 ( [1,2,3] , [4,5,6] )) = [3,2,1,4,5,6]", (rev2 ( [1,2,3] , [4,5,6] )) = [3,2,1,4,5,6]);
    tester ("let A = id ( [1,2,3] , [4,5,6] ) in (rev2 A) = [3,2,1,4,5,6]", let A = id ( [1,2,3] , [4,5,6] ) in (rev2 A) = [3,2,1,4,5,6]);
% List [ 73]:  op flatten         : fa(a)   List(List a) -> List a
    tester ("(flatten ( [[3,1],[4,1],[5,9]] )) = [3,1,4,1,5,9]", (flatten ( [[3,1],[4,1],[5,9]] )) = [3,1,4,1,5,9]);
% List [ 74]:  op find            : fa(a)   (a -> Boolean) -> List a -> Option(a)
    tester ("(find ( posNat? ) ( [0,0,0] )) = None", (find ( posNat? ) ( [0,0,0] )) = None);
    tester ("let F = id ( find ( posNat? )) in (F ( [0,0,0] )) = None", let F = id ( find ( posNat? )) in (F ( [0,0,0] )) = None);
    tester ("(find ( posNat? ) ( [0,1,0] )) = Some(1)", (find ( posNat? ) ( [0,1,0] )) = Some(1));
    tester ("let F = id ( find ( posNat? )) in (F ( [0,1,0] )) = Some(1)", let F = id ( find ( posNat? )) in (F ( [0,1,0] )) = Some(1));
% List [ 75]:  op tabulate        : fa(a)   Nat * (Nat -> a) -> List a
    tester ("(tabulate ( 3 , succ )) = [1,2,3]", (tabulate ( 3 , succ )) = [1,2,3]);
    tester ("let A = id ( 3 , succ ) in (tabulate A) = [1,2,3]", let A = id ( 3 , succ ) in (tabulate A) = [1,2,3]);
% List [ 76]:  op firstUpTo       : fa(a)   (a -> Boolean) -> List a -> Option (a * List a)
    tester ("(firstUpTo ( null ) ( [[1],[2,3],[],[4]] )) = Some([],[[1],[2,3]])", (firstUpTo ( null ) ( [[1],[2,3],[],[4]] )) = Some([],[[1],[2,3]]));
    tester ("let F = id ( firstUpTo ( null )) in (F ( [[1],[2,3],[],[4]] )) = Some([],[[1],[2,3]])", let F = id ( firstUpTo ( null )) in (F ( [[1],[2,3],[],[4]] )) = Some([],[[1],[2,3]]));
    tester ("(firstUpTo ( null ) ( [[1],[2,3],[4]] )) = None", (firstUpTo ( null ) ( [[1],[2,3],[4]] )) = None);
    tester ("let F = id ( firstUpTo ( null )) in (F ( [[1],[2,3],[4]] )) = None", let F = id ( firstUpTo ( null )) in (F ( [[1],[2,3],[4]] )) = None);
% List [ 78]:  op splitList       : fa(a)  (a -> Boolean) -> List a -> Option(List a * a * List a)
    tester ("(splitList ( null ) ( [[1],[2,3],[],[4]] )) = Some([[1],[2,3]],[],[[4]])", (splitList ( null ) ( [[1],[2,3],[],[4]] )) = Some([[1],[2,3]],[],[[4]]));
    tester ("let F = id ( splitList ( null )) in (F ( [[1],[2,3],[],[4]] )) = Some([[1],[2,3]],[],[[4]])", let F = id ( splitList ( null )) in (F ( [[1],[2,3],[],[4]] )) = Some([[1],[2,3]],[],[[4]]));
    tester ("(splitList ( null ) ( [[1],[2,3],[4]] )) = None", (splitList ( null ) ( [[1],[2,3],[4]] )) = None);
    tester ("let F = id ( splitList ( null )) in (F ( [[1],[2,3],[4]] )) = None", let F = id ( splitList ( null )) in (F ( [[1],[2,3],[4]] )) = None);
% List [ 80]:  op locationOf      : fa(a)  List a * List a -> Option(Nat * List a)
    tester ("(locationOf ( [] , [3,1,4,1,5] )) = Some(0,[3,1,4,1,5])", (locationOf ( [] , [3,1,4,1,5] )) = Some(0,[3,1,4,1,5]));
    tester ("let A = id ( [] , [3,1,4,1,5] ) in (locationOf A) = Some(0,[3,1,4,1,5])", let A = id ( [] , [3,1,4,1,5] ) in (locationOf A) = Some(0,[3,1,4,1,5]));
    tester ("(locationOf ( [1,4] , [3,1,4,1,5] )) = Some(1,[1,5])", (locationOf ( [1,4] , [3,1,4,1,5] )) = Some(1,[1,5]));
    tester ("let A = id ( [1,4] , [3,1,4,1,5] ) in (locationOf A) = Some(1,[1,5])", let A = id ( [1,4] , [3,1,4,1,5] ) in (locationOf A) = Some(1,[1,5]));
    tester ("(locationOf ( [1,3] , [3,1,4,1,5] )) = None", (locationOf ( [1,3] , [3,1,4,1,5] )) = None);
    tester ("let A = id ( [1,3] , [3,1,4,1,5] ) in (locationOf A) = None", let A = id ( [1,3] , [3,1,4,1,5] ) in (locationOf A) = None);
% List [ 81]:  op compare         : fa(a)  (a * a -> Comparison) -> List a * List a -> Comparison
    tester ("(compare ( Integer.compare ) ( [] , [1] )) = Less", (compare ( Integer.compare ) ( [] , [1] )) = Less);
    tester ("let F = id ( compare ( Integer.compare )) in (F ( [] , [1] )) = Less", let F = id ( compare ( Integer.compare )) in (F ( [] , [1] )) = Less);
    tester ("(compare ( Integer.compare ) ( [0,9] , [1] )) = Less", (compare ( Integer.compare ) ( [0,9] , [1] )) = Less);
    tester ("let F = id ( compare ( Integer.compare )) in (F ( [0,9] , [1] )) = Less", let F = id ( compare ( Integer.compare )) in (F ( [0,9] , [1] )) = Less);
    tester ("(compare ( Integer.compare ) ( [1] , [1] )) = Equal", (compare ( Integer.compare ) ( [1] , [1] )) = Equal);
    tester ("let F = id ( compare ( Integer.compare )) in (F ( [1] , [1] )) = Equal", let F = id ( compare ( Integer.compare )) in (F ( [1] , [1] )) = Equal);
    tester ("(compare ( Integer.compare ) ( [1,0] , [1] )) = Greater", (compare ( Integer.compare ) ( [1,0] , [1] )) = Greater);
    tester ("let F = id ( compare ( Integer.compare )) in (F ( [1,0] , [1] )) = Greater", let F = id ( compare ( Integer.compare )) in (F ( [1,0] , [1] )) = Greater);
% List [ 82]:  op app             : fa(a)  (a -> ()) -> List a -> ()  % deprecated
% List [134]:  op show    : String -> List String -> String
    tester ("(show ( \"ns\" ) ( [\"no\",\"e\",\"e\"] )) = \"nonsense\"", (show ( "ns" ) ( ["no","e","e"] )) = "nonsense");
    tester ("let F = id ( show ( \"ns\" )) in (F ( [\"no\",\"e\",\"e\"] )) = \"nonsense\"", let F = id ( show ( "ns" )) in (F ( ["no","e","e"] )) = "nonsense");

% Nat [ 84]:  op succ    : Nat -> Nat
    tester ("(succ ( 6 )) = 7", (succ ( 6 )) = 7);
% Nat [ 85]:  op pred    : Nat -> Integer
    tester ("(pred ( 7 )) = 6", (pred ( 7 )) = 6);
% Nat [ 86]:  op zero    : Nat 
    tester ("(zero) = 0", (zero) = 0);
% Nat [ 87]:  op one     : Nat
    tester ("(one) = 1", (one) = 1);
% Nat [ 88]:  op two     : Nat
    tester ("(two) = 2", (two) = 2);
% Nat [ 89]:  op posNat? : Nat -> Boolean
    tester ("(posNat? ( 0 )) = false", (posNat? ( 0 )) = false);
    tester ("(posNat? ( 1 )) = true", (posNat? ( 1 )) = true);
% Nat [122]:  op toString     : Nat -> String      % deprecated
    tester ("(toString ( 123 )) = \"123\"", (toString ( 123 )) = "123");
% Nat [133]:  op show     : Nat -> String
    tester ("(Nat.show ( 123 )) = \"123\"", (Nat.show ( 123 )) = "123");
% Nat [126]:  op natToString  : Nat -> String
    tester ("(natToString ( 123 )) = \"123\"", (natToString ( 123 )) = "123");
% Nat [126.5]:  op natConvertible : String -> Boolean
    tester ("(natConvertible ( \"123\" )) = true", (natConvertible ( "123" )) = true);
    tester ("(natConvertible ( \"-123\" )) = false", (natConvertible ( "-123" )) = false);
    tester ("(natConvertible ( \"000\" )) = true", (natConvertible ( "000" )) = true);
    tester ("(natConvertible ( \"\" )) = false", (natConvertible ( "" )) = false);
    tester ("(natConvertible ( \"123.00\" )) = false", (natConvertible ( "123.00" )) = false);
% Nat [127]:  op stringToNat  : (String | natConvertible) -> Nat

% Option [ 94]:  op some      : fa(a) a -> Option a
    tester ("(some ( 1 )) = Some(1)", (some ( 1 )) = Some(1));
% Option [ 95]:  op none      : fa(a) Option a
    tester ("(none) = None", (none) = None);
% Option [ 96]:  op some?     : fa(a) Option a -> Boolean
    tester ("(some? ( None )) = false", (some? ( None )) = false);
    tester ("(some? ( Some(1) )) = true", (some? ( Some(1) )) = true);
% Option [ 97]:  op none?     : fa(a) Option a -> Boolean
    tester ("(none? ( None )) = true", (none? ( None )) = true);
    tester ("(none? ( Some(1) )) = false", (none? ( Some(1) )) = false);
% Option [ 98]:  op compare   : fa(a) (a * a -> Comparison) -> Option a * Option a -> Comparison
    tester ("(compare ( Integer.compare ) ( None , None )) = Equal", (compare ( Integer.compare ) ( None , None )) = Equal);
    tester ("let F = id ( compare ( Integer.compare )) in (F ( None , None )) = Equal", let F = id ( compare ( Integer.compare )) in (F ( None , None )) = Equal);
    tester ("(compare ( Integer.compare ) ( None , Some(1) )) = Less", (compare ( Integer.compare ) ( None , Some(1) )) = Less);
    tester ("let F = id ( compare ( Integer.compare )) in (F ( None , Some(1) )) = Less", let F = id ( compare ( Integer.compare )) in (F ( None , Some(1) )) = Less);
    tester ("(compare ( Integer.compare ) ( Some(1) , None )) = Greater", (compare ( Integer.compare ) ( Some(1) , None )) = Greater);
    tester ("let F = id ( compare ( Integer.compare )) in (F ( Some(1) , None )) = Greater", let F = id ( compare ( Integer.compare )) in (F ( Some(1) , None )) = Greater);
    tester ("(compare ( Integer.compare ) ( Some(0) , Some(1) )) = Less", (compare ( Integer.compare ) ( Some(0) , Some(1) )) = Less);
    tester ("let F = id ( compare ( Integer.compare )) in (F ( Some(0) , Some(1) )) = Less", let F = id ( compare ( Integer.compare )) in (F ( Some(0) , Some(1) )) = Less);
    tester ("(compare ( Integer.compare ) ( Some(1) , Some(1) )) = Equal", (compare ( Integer.compare ) ( Some(1) , Some(1) )) = Equal);
    tester ("let F = id ( compare ( Integer.compare )) in (F ( Some(1) , Some(1) )) = Equal", let F = id ( compare ( Integer.compare )) in (F ( Some(1) , Some(1) )) = Equal);
    tester ("(compare ( Integer.compare ) ( Some(2) , Some(1) )) = Greater", (compare ( Integer.compare ) ( Some(2) , Some(1) )) = Greater);
    tester ("let F = id ( compare ( Integer.compare )) in (F ( Some(2) , Some(1) )) = Greater", let F = id ( compare ( Integer.compare )) in (F ( Some(2) , Some(1) )) = Greater);
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
% String [104]:  op concat        : String * String -> String
    tester ("(concat ( \"now\" , \"here\" )) = \"nowhere\"", (concat ( "now" , "here" )) = "nowhere");
    tester ("let A = id ( \"now\" , \"here\" ) in (concat A) = \"nowhere\"", let A = id ( "now" , "here" ) in (concat A) = "nowhere");
% String [105]:  op ++ infixl 11  : String * String -> String
    tester ("(++ ( \"now\" , \"here\" )) = \"nowhere\"", (++ ( "now" , "here" )) = "nowhere");
    tester ("let A = id ( \"now\" , \"here\" ) in (++ A) = \"nowhere\"", let A = id ( "now" , "here" ) in (++ A) = "nowhere");
% String [106]:  op ^  infixl 11  : String * String -> String
    tester ("(^ ( \"now\" , \"here\" )) = \"nowhere\"", (^ ( "now" , "here" )) = "nowhere");
    tester ("let A = id ( \"now\" , \"here\" ) in (^ A) = \"nowhere\"", let A = id ( "now" , "here" ) in (^ A) = "nowhere");
% String [107]:  op map           : (Char -> Char) -> String -> String
    tester ("(map ( fn(c)->chr(96+(let(v)=(ord(c)-96)in((v+13)rem(26)))) ) ( \"terra\" )) = \"green\"", (map ( fn(c)->chr(96+(let(v)=(ord(c)-96)in((v+13)rem(26)))) ) ( "terra" )) = "green");
    tester ("let F = id ( map ( fn(c)->chr(96+(let(v)=(ord(c)-96)in((v+13)rem(26)))) )) in (F ( \"terra\" )) = \"green\"", let F = id ( map ( fn(c)->chr(96+(let(v)=(ord(c)-96)in((v+13)rem(26)))) )) in (F ( "terra" )) = "green");
% String [108]:  op exists        : (Char -> Boolean) -> String -> Boolean
    tester ("(exists ( isNum ) ( \"\" )) = false", (exists ( isNum ) ( "" )) = false);
    tester ("let F = id ( exists ( isNum )) in (F ( \"\" )) = false", let F = id ( exists ( isNum )) in (F ( "" )) = false);
    tester ("(exists ( isNum ) ( \"c3po\" )) = true", (exists ( isNum ) ( "c3po" )) = true);
    tester ("let F = id ( exists ( isNum )) in (F ( \"c3po\" )) = true", let F = id ( exists ( isNum )) in (F ( "c3po" )) = true);
% String [109]:  op all           : (Char -> Boolean) -> String -> Boolean
    tester ("(all ( isAlpha ) ( \"\" )) = true", (all ( isAlpha ) ( "" )) = true);
    tester ("let F = id ( all ( isAlpha )) in (F ( \"\" )) = true", let F = id ( all ( isAlpha )) in (F ( "" )) = true);
    tester ("(all ( isAlpha ) ( \"c3po\" )) = false", (all ( isAlpha ) ( "c3po" )) = false);
    tester ("let F = id ( all ( isAlpha )) in (F ( \"c3po\" )) = false", let F = id ( all ( isAlpha )) in (F ( "c3po" )) = false);
% String [110]:  op sub           : {(s,n) : String * Nat | n < length s} -> Char
    tester ("(sub ( \"afn\" , 1 )) = #f", (sub ( "afn" , 1 )) = #f);
    tester ("let A = id ( \"afn\" , 1 ) in (sub A) = #f", let A = id ( "afn" , 1 ) in (sub A) = #f);
% String [111]:  op substring     : {(s,i,j) : String * Nat * Nat | i < j & j <= length s} ->
    tester ("(substring ( \"twitchy\" , 2, 6 )) = \"itch\"", (substring ( "twitchy" , 2, 6 )) = "itch");
    tester ("let A = id ( \"twitchy\" , 2, 6 ) in (substring A) = \"itch\"", let A = id ( "twitchy" , 2, 6 ) in (substring A) = "itch");
% String [112]:  op concatList    : List String -> String
    tester ("(concatList ( [] )) = \"\"", (concatList ( [] )) = "");
    tester ("(concatList ( [\"now\",\"here\"] )) = \"nowhere\"", (concatList ( ["now","here"] )) = "nowhere");
% String [113]:  op translate     : (Char -> String) -> String -> String
    tester ("(translate ( fn(c)->implode[c,c] ) ( \"2B\" )) = \"22BB\"", (translate ( fn(c)->implode[c,c] ) ( "2B" )) = "22BB");
    tester ("let F = id ( translate ( fn(c)->implode[c,c] )) in (F ( \"2B\" )) = \"22BB\"", let F = id ( translate ( fn(c)->implode[c,c] )) in (F ( "2B" )) = "22BB");
% String [114]:  op lt  infixl 20 : String * String -> Boolean
    tester ("(lt ( \"\" , \"\" )) = false", (lt ( "" , "" )) = false);
    tester ("let A = id ( \"\" , \"\" ) in (lt A) = false", let A = id ( "" , "" ) in (lt A) = false);
    tester ("(lt ( \"\" , \"1\" )) = true", (lt ( "" , "1" )) = true);
    tester ("let A = id ( \"\" , \"1\" ) in (lt A) = true", let A = id ( "" , "1" ) in (lt A) = true);
    tester ("(lt ( \"0\" , \"1\" )) = true", (lt ( "0" , "1" )) = true);
    tester ("let A = id ( \"0\" , \"1\" ) in (lt A) = true", let A = id ( "0" , "1" ) in (lt A) = true);
    tester ("(lt ( \"09\" , \"1\" )) = true", (lt ( "09" , "1" )) = true);
    tester ("let A = id ( \"09\" , \"1\" ) in (lt A) = true", let A = id ( "09" , "1" ) in (lt A) = true);
    tester ("(lt ( \"1\" , \"\" )) = false", (lt ( "1" , "" )) = false);
    tester ("let A = id ( \"1\" , \"\" ) in (lt A) = false", let A = id ( "1" , "" ) in (lt A) = false);
    tester ("(lt ( \"1\" , \"1\" )) = false", (lt ( "1" , "1" )) = false);
    tester ("let A = id ( \"1\" , \"1\" ) in (lt A) = false", let A = id ( "1" , "1" ) in (lt A) = false);
    tester ("(lt ( \"10\" , \"1\" )) = false", (lt ( "10" , "1" )) = false);
    tester ("let A = id ( \"10\" , \"1\" ) in (lt A) = false", let A = id ( "10" , "1" ) in (lt A) = false);
    tester ("(lt ( \"2\" , \"1\" )) = false", (lt ( "2" , "1" )) = false);
    tester ("let A = id ( \"2\" , \"1\" ) in (lt A) = false", let A = id ( "2" , "1" ) in (lt A) = false);
% String [115]:  op leq infixl 20 : String * String -> Boolean
    tester ("(leq ( \"\" , \"\" )) = true", (leq ( "" , "" )) = true);
    tester ("let A = id ( \"\" , \"\" ) in (leq A) = true", let A = id ( "" , "" ) in (leq A) = true);
    tester ("(leq ( \"\" , \"1\" )) = true", (leq ( "" , "1" )) = true);
    tester ("let A = id ( \"\" , \"1\" ) in (leq A) = true", let A = id ( "" , "1" ) in (leq A) = true);
    tester ("(leq ( \"0\" , \"1\" )) = true", (leq ( "0" , "1" )) = true);
    tester ("let A = id ( \"0\" , \"1\" ) in (leq A) = true", let A = id ( "0" , "1" ) in (leq A) = true);
    tester ("(leq ( \"09\" , \"1\" )) = true", (leq ( "09" , "1" )) = true);
    tester ("let A = id ( \"09\" , \"1\" ) in (leq A) = true", let A = id ( "09" , "1" ) in (leq A) = true);
    tester ("(leq ( \"1\" , \"\" )) = false", (leq ( "1" , "" )) = false);
    tester ("let A = id ( \"1\" , \"\" ) in (leq A) = false", let A = id ( "1" , "" ) in (leq A) = false);
    tester ("(leq ( \"1\" , \"1\" )) = true", (leq ( "1" , "1" )) = true);
    tester ("let A = id ( \"1\" , \"1\" ) in (leq A) = true", let A = id ( "1" , "1" ) in (leq A) = true);
    tester ("(leq ( \"10\" , \"1\" )) = false", (leq ( "10" , "1" )) = false);
    tester ("let A = id ( \"10\" , \"1\" ) in (leq A) = false", let A = id ( "10" , "1" ) in (leq A) = false);
    tester ("(leq ( \"2\" , \"1\" )) = false", (leq ( "2" , "1" )) = false);
    tester ("let A = id ( \"2\" , \"1\" ) in (leq A) = false", let A = id ( "2" , "1" ) in (leq A) = false);
% String [116]:  op newline       : String
    tester ("(newline) = \"\\n\"", (newline) = "\n");
% String [117]:  op toScreen      : String -> ()  % deprecated
% String [118]:  op writeLine     : String -> ()  % deprecated
% String [119]:  op compare : String * String -> Comparison
    tester ("(compare ( \"\" , \"\" )) = Equal", (compare ( "" , "" )) = Equal);
    tester ("let A = id ( \"\" , \"\" ) in (compare A) = Equal", let A = id ( "" , "" ) in (compare A) = Equal);
    tester ("(compare ( \"\" , \"1\" )) = Less", (compare ( "" , "1" )) = Less);
    tester ("let A = id ( \"\" , \"1\" ) in (compare A) = Less", let A = id ( "" , "1" ) in (compare A) = Less);
    tester ("(compare ( \"0\" , \"1\" )) = Less", (compare ( "0" , "1" )) = Less);
    tester ("let A = id ( \"0\" , \"1\" ) in (compare A) = Less", let A = id ( "0" , "1" ) in (compare A) = Less);
    tester ("(compare ( \"09\" , \"1\" )) = Less", (compare ( "09" , "1" )) = Less);
    tester ("let A = id ( \"09\" , \"1\" ) in (compare A) = Less", let A = id ( "09" , "1" ) in (compare A) = Less);
    tester ("(compare ( \"1\" , \"\" )) = Greater", (compare ( "1" , "" )) = Greater);
    tester ("let A = id ( \"1\" , \"\" ) in (compare A) = Greater", let A = id ( "1" , "" ) in (compare A) = Greater);
    tester ("(compare ( \"1\" , \"1\" )) = Equal", (compare ( "1" , "1" )) = Equal);
    tester ("let A = id ( \"1\" , \"1\" ) in (compare A) = Equal", let A = id ( "1" , "1" ) in (compare A) = Equal);
    tester ("(compare ( \"10\" , \"1\" )) = Greater", (compare ( "10" , "1" )) = Greater);
    tester ("let A = id ( \"10\" , \"1\" ) in (compare A) = Greater", let A = id ( "10" , "1" ) in (compare A) = Greater);
    tester ("(compare ( \"2\" , \"1\" )) = Greater", (compare ( "2" , "1" )) = Greater);
    tester ("let A = id ( \"2\" , \"1\" ) in (compare A) = Greater", let A = id ( "2" , "1" ) in (compare A) = Greater);
    () )

endspec
