(test  ("(~ ( true )) = false" :swe "(~ ( true )) = false" :value t)
       ("(~ ( false )) = true" :swe "(~ ( false )) = true" :value t)
       ;; Boolean [  2]:  op &   infixr 15 : Boolean * Boolean -> Boolean 
       ("(& ( false , false )) = false" :swe "(& ( false , false )) = false" :value t)
       ("let A = id ( false , false ) in (& A) = false" :swe "let A = id ( false , false ) in (& A) = false" :value t)
       ("(& ( false , true )) = false" :swe "(& ( false , true )) = false" :value t)
       ("let A = id ( false , true ) in (& A) = false" :swe "let A = id ( false , true ) in (& A) = false" :value t)
       ("(& ( true , false )) = false" :swe "(& ( true , false )) = false" :value t)
       ("let A = id ( true , false ) in (& A) = false" :swe "let A = id ( true , false ) in (& A) = false" :value t)
       ("(& ( true , true )) = true" :swe "(& ( true , true )) = true" :value t)
       ("let A = id ( true , true ) in (& A) = true" :swe "let A = id ( true , true ) in (& A) = true" :value t)
       ;; Boolean [  3]:  op or  infixr 14 : Boolean * Boolean -> Boolean 
       ("(or ( false , false )) = false" :swe "(or ( false , false )) = false" :value t)
       ("let A = id ( false , false ) in (or A) = false" :swe "let A = id ( false , false ) in (or A) = false" :value t)
       ("(or ( false , true )) = true" :swe "(or ( false , true )) = true" :value t)
       ("let A = id ( false , true ) in (or A) = true" :swe "let A = id ( false , true ) in (or A) = true" :value t)
       ("(or ( true , false )) = true" :swe "(or ( true , false )) = true" :value t)
       ("let A = id ( true , false ) in (or A) = true" :swe "let A = id ( true , false ) in (or A) = true" :value t)
       ("(or ( true , true )) = true" :swe "(or ( true , true )) = true" :value t)
       ("let A = id ( true , true ) in (or A) = true" :swe "let A = id ( true , true ) in (or A) = true" :value t)
       ;; Boolean [  4]:  op =>  infixr 13 : Boolean * Boolean -> Boolean 
       ("(=> ( false , false )) = true" :swe "(=> ( false , false )) = true" :value t)
       ("let A = id ( false , false ) in (=> A) = true" :swe "let A = id ( false , false ) in (=> A) = true" :value t)
       ("(=> ( false , true )) = true" :swe "(=> ( false , true )) = true" :value t)
       ("let A = id ( false , true ) in (=> A) = true" :swe "let A = id ( false , true ) in (=> A) = true" :value t)
       ("(=> ( true , false )) = false" :swe "(=> ( true , false )) = false" :value t)
       ("let A = id ( true , false ) in (=> A) = false" :swe "let A = id ( true , false ) in (=> A) = false" :value t)
       ("(=> ( true , true )) = true" :swe "(=> ( true , true )) = true" :value t)
       ("let A = id ( true , true ) in (=> A) = true" :swe "let A = id ( true , true ) in (=> A) = true" :value t)
       ;; Boolean [  5]:  op <=> infixr 12 : Boolean * Boolean -> Boolean 
       ("(<=> ( false , false )) = true" :swe "(<=> ( false , false )) = true" :value t)
       ("let A = id ( false , false ) in (<=> A) = true" :swe "let A = id ( false , false ) in (<=> A) = true" :value t)
       ("(<=> ( false , true )) = false" :swe "(<=> ( false , true )) = false" :value t)
       ("let A = id ( false , true ) in (<=> A) = false" :swe "let A = id ( false , true ) in (<=> A) = false" :value t)
       ("(<=> ( true , false )) = false" :swe "(<=> ( true , false )) = false" :value t)
       ("let A = id ( true , false ) in (<=> A) = false" :swe "let A = id ( true , false ) in (<=> A) = false" :value t)
       ("(<=> ( true , true )) = true" :swe "(<=> ( true , true )) = true" :value t)
       ("let A = id ( true , true ) in (<=> A) = true" :swe "let A = id ( true , true ) in (<=> A) = true" :value t)
       ;; Boolean [  6]:  op ~=  infixr 20 : fa(a) a * a -> Boolean
       ("(~= ( 4 , 4 )) = false" :swe "(~= ( 4 , 4 )) = false" :value t)
       ("let A = id ( 4 , 4 ) in (~= A) = false" :swe "let A = id ( 4 , 4 ) in (~= A) = false" :value t)
       ("(~= ( 4 , 5 )) = true" :swe "(~= ( 4 , 5 )) = true" :value t)
       ("let A = id ( 4 , 5 ) in (~= A) = true" :swe "let A = id ( 4 , 5 ) in (~= A) = true" :value t)
       ;; Boolean [  7]:  op compare  : Boolean * Boolean -> Comparison
       ("(compare ( false , false )) = Equal" :swe "(compare ( false , false )) = Equal" :value t)
       ("let A = id ( false , false ) in (compare A) = Equal" :swe "let A = id ( false , false ) in (compare A) = Equal" :value t)
       ("(compare ( false , true )) = Less" :swe "(compare ( false , true )) = Less" :value t)
       ("let A = id ( false , true ) in (compare A) = Less" :swe "let A = id ( false , true ) in (compare A) = Less" :value t)
       ("(compare ( true , false )) = Greater" :swe "(compare ( true , false )) = Greater" :value t)
       ("let A = id ( true , false ) in (compare A) = Greater" :swe "let A = id ( true , false ) in (compare A) = Greater" :value t)
       ("(compare ( true , true )) = Equal" :swe "(compare ( true , true )) = Equal" :value t)
       ("let A = id ( true , true ) in (compare A) = Equal" :swe "let A = id ( true , true ) in (compare A) = Equal" :value t)
       ;; Boolean [120]:  op toString : Boolean -> String  ;; deprecated
       ("(toString ( true )) = \"true\"" :swe "(toString ( true )) = \"true\"" :value t)
       ("(toString ( false )) = \"false\"" :swe "(toString ( false )) = \"false\"" :value t)
       ;; Boolean [129]:  op show : Boolean -> String
       ("(show ( true )) = \"true\"" :swe "(show ( true )) = \"true\"" :value t)
       ("(show ( false )) = \"false\"" :swe "(show ( false )) = \"false\"" :value t)

       ;; Char [ 10]:  op ord : Char -> {n : Nat | n < 256}
       ("(ord ( #A )) = 65" :swe "(ord ( #A )) = 65" :value t)
       ;; Char [ 11]:  op chr : {n : Nat | n < 256} -> Char
       ("(chr ( 65 )) = #A" :swe "(chr ( 65 )) = #A" :value t)
       ;; Char [ 12]:  op isUpperCase : Char -> Boolean
       ("(isUpperCase ( #! )) = false" :swe "(isUpperCase ( #! )) = false" :value t)
       ("(isUpperCase ( #3 )) = false" :swe "(isUpperCase ( #3 )) = false" :value t)
       ("(isUpperCase ( #A )) = true" :swe "(isUpperCase ( #A )) = true" :value t)
       ("(isUpperCase ( #a )) = false" :swe "(isUpperCase ( #a )) = false" :value t)
       ("(isUpperCase ( #\\xdd )) = true" :swe "(isUpperCase ( #\\xdd )) = true" :value t)
       ("(isUpperCase ( #\\xff )) = false" :swe "(isUpperCase ( #\\xff )) = false" :value t)
       ;; Char [ 13]:  op isLowerCase : Char -> Boolean
       ("(isLowerCase ( #! )) = false" :swe "(isLowerCase ( #! )) = false" :value t)
       ("(isLowerCase ( #3 )) = false" :swe "(isLowerCase ( #3 )) = false" :value t)
       ("(isLowerCase ( #A )) = false" :swe "(isLowerCase ( #A )) = false" :value t)
       ("(isLowerCase ( #a )) = true" :swe "(isLowerCase ( #a )) = true" :value t)
       ("(isLowerCase ( #\\xdd )) = false" :swe "(isLowerCase ( #\\xdd )) = false" :value t)
       ("(isLowerCase ( #\\xff )) = true" :swe "(isLowerCase ( #\\xff )) = true" :value t)
       ;; Char [ 14]:  op isAlpha     : Char -> Boolean
       ("(isAlpha ( #! )) = false" :swe "(isAlpha ( #! )) = false" :value t)
       ("(isAlpha ( #3 )) = false" :swe "(isAlpha ( #3 )) = false" :value t)
       ("(isAlpha ( #A )) = true" :swe "(isAlpha ( #A )) = true" :value t)
       ("(isAlpha ( #a )) = true" :swe "(isAlpha ( #a )) = true" :value t)
       ("(isAlpha ( #\\xff )) = true" :swe "(isAlpha ( #\\xff )) = true" :value t)
       ;; Char [ 15]:  op isNum       : Char -> Boolean
       ("(isNum ( #! )) = false" :swe "(isNum ( #! )) = false" :value t)
       ("(isNum ( #3 )) = true" :swe "(isNum ( #3 )) = true" :value t)
       ("(isNum ( #A )) = false" :swe "(isNum ( #A )) = false" :value t)
       ("(isNum ( #a )) = false" :swe "(isNum ( #a )) = false" :value t)
       ("(isNum ( #\\xff )) = false" :swe "(isNum ( #\\xff )) = false" :value t)
       ;; Char [ 16]:  op isAlphaNum  : Char -> Boolean
       ("(isAlphaNum ( #! )) = false" :swe "(isAlphaNum ( #! )) = false" :value t)
       ("(isAlphaNum ( #3 )) = true" :swe "(isAlphaNum ( #3 )) = true" :value t)
       ("(isAlphaNum ( #A )) = true" :swe "(isAlphaNum ( #A )) = true" :value t)
       ("(isAlphaNum ( #a )) = true" :swe "(isAlphaNum ( #a )) = true" :value t)
       ("(isAlphaNum ( #\\xff )) = true" :swe "(isAlphaNum ( #\\xff )) = true" :value t)
       ;; Char [ 17]:  op isAscii     : Char -> Boolean
       ("(isAscii ( #! )) = true" :swe "(isAscii ( #! )) = true" :value t)
       ("(isAscii ( #3 )) = true" :swe "(isAscii ( #3 )) = true" :value t)
       ("(isAscii ( #A )) = true" :swe "(isAscii ( #A )) = true" :value t)
       ("(isAscii ( #a )) = true" :swe "(isAscii ( #a )) = true" :value t)
       ("(isAscii ( #\\xff )) = false" :swe "(isAscii ( #\\xff )) = false" :value t)
       ;; Char [ 18]:  op toUpperCase : Char -> Char
       ("(toUpperCase ( #! )) = #!" :swe "(toUpperCase ( #! )) = #!" :value t)
       ("(toUpperCase ( #3 )) = #3" :swe "(toUpperCase ( #3 )) = #3" :value t)
       ("(toUpperCase ( #A )) = #A" :swe "(toUpperCase ( #A )) = #A" :value t)
       ("(toUpperCase ( #a )) = #A" :swe "(toUpperCase ( #a )) = #A" :value t)
       ("(toUpperCase ( #\\xfc )) = #\\xdc" :swe "(toUpperCase ( #\\xfc )) = #\\xdc" :value t)
       ;; Char [ 19]:  op toLowerCase : Char -> Char
       ("(toLowerCase ( #! )) = #!" :swe "(toLowerCase ( #! )) = #!" :value t)
       ("(toLowerCase ( #3 )) = #3" :swe "(toLowerCase ( #3 )) = #3" :value t)
       ("(toLowerCase ( #A )) = #a" :swe "(toLowerCase ( #A )) = #a" :value t)
       ("(toLowerCase ( #a )) = #a" :swe "(toLowerCase ( #a )) = #a" :value t)
       ("(toLowerCase ( #\\xdc )) = #\\xfc" :swe "(toLowerCase ( #\\xdc )) = #\\xfc" :value t)
       ;; Char [ 20]:  op compare : Char * Char -> Comparison
       ("(compare ( #3 , #4 )) = Less" :swe "(compare ( #3 , #4 )) = Less" :value t)
       ("let A = id ( #3 , #4 ) in (compare A) = Less" :swe "let A = id ( #3 , #4 ) in (compare A) = Less" :value t)
       ("(compare ( #4 , #4 )) = Equal" :swe "(compare ( #4 , #4 )) = Equal" :value t)
       ("let A = id ( #4 , #4 ) in (compare A) = Equal" :swe "let A = id ( #4 , #4 ) in (compare A) = Equal" :value t)
       ("(compare ( #5 , #4 )) = Greater" :swe "(compare ( #5 , #4 )) = Greater" :value t)
       ("let A = id ( #5 , #4 ) in (compare A) = Greater" :swe "let A = id ( #5 , #4 ) in (compare A) = Greater" :value t)
       ;; Char [123]:  op toString    : Char -> String     ;; deprecated
       ("(toString ( #A )) = \"A\"" :swe "(toString ( #A )) = \"A\"" :value t)
       ;; Char [135]:  op show    : Char -> String
       ("(show ( #A )) = \"A\"" :swe "(show ( #A )) = \"A\"" :value t)

       ;; Compare [ 23]:  op compare : Comparison * Comparison -> Comparison
       ("(compare ( Less , Less )) = Equal" :swe "(compare ( Less , Less )) = Equal" :value t)
       ("let A = id ( Less , Less ) in (compare A) = Equal" :swe "let A = id ( Less , Less ) in (compare A) = Equal" :value t)
       ("(compare ( Less , Equal )) = Less" :swe "(compare ( Less , Equal )) = Less" :value t)
       ("let A = id ( Less , Equal ) in (compare A) = Less" :swe "let A = id ( Less , Equal ) in (compare A) = Less" :value t)
       ("(compare ( Less , Greater )) = Less" :swe "(compare ( Less , Greater )) = Less" :value t)
       ("let A = id ( Less , Greater ) in (compare A) = Less" :swe "let A = id ( Less , Greater ) in (compare A) = Less" :value t)
       ("(compare ( Equal , Less )) = Greater" :swe "(compare ( Equal , Less )) = Greater" :value t)
       ("let A = id ( Equal , Less ) in (compare A) = Greater" :swe "let A = id ( Equal , Less ) in (compare A) = Greater" :value t)
       ("(compare ( Equal , Equal )) = Equal" :swe "(compare ( Equal , Equal )) = Equal" :value t)
       ("let A = id ( Equal , Equal ) in (compare A) = Equal" :swe "let A = id ( Equal , Equal ) in (compare A) = Equal" :value t)
       ("(compare ( Equal , Greater )) = Less" :swe "(compare ( Equal , Greater )) = Less" :value t)
       ("let A = id ( Equal , Greater ) in (compare A) = Less" :swe "let A = id ( Equal , Greater ) in (compare A) = Less" :value t)
       ("(compare ( Greater , Less )) = Greater" :swe "(compare ( Greater , Less )) = Greater" :value t)
       ("let A = id ( Greater , Less ) in (compare A) = Greater" :swe "let A = id ( Greater , Less ) in (compare A) = Greater" :value t)
       ("(compare ( Greater , Equal )) = Greater" :swe "(compare ( Greater , Equal )) = Greater" :value t)
       ("let A = id ( Greater , Equal ) in (compare A) = Greater" :swe "let A = id ( Greater , Equal ) in (compare A) = Greater" :value t)
       ("(compare ( Greater , Greater )) = Equal" :swe "(compare ( Greater , Greater )) = Equal" :value t)
       ("let A = id ( Greater , Greater ) in (compare A) = Equal" :swe "let A = id ( Greater , Greater ) in (compare A) = Equal" :value t)
       ;; Compare [130]:  op show : Comparison -> String
       ("(show ( Less )) = \"Less\"" :swe "(show ( Less )) = \"Less\"" :value t)
       ("(show ( Equal )) = \"Equal\"" :swe "(show ( Equal )) = \"Equal\"" :value t)
       ("(show ( Greater )) = \"Greater\"" :swe "(show ( Greater )) = \"Greater\"" :value t)

       ;; Functions [ 25]:  op id          : fa(a) a -> a
       ("(id ( 3 )) = 3" :swe "(id ( 3 )) = 3" :value t)
       ("(id ( #3 )) = #3" :swe "(id ( #3 )) = #3" :value t)
       ;; Functions [ 26]:  op o infixl 24 : fa(a,b,c) (b -> c) * (a -> b) -> (a -> c)
       ("((o(succ,succ))3) = 5" :swe "((o(succ,succ))3) = 5" :value t)
       ("(let(ss)=(succ,succ)in(o(ss))3) = 5" :swe "(let(ss)=(succ,succ)in(o(ss))3) = 5" :value t)
       ;; Functions [ 27]:  op injective?  : fa(a,b) (a -> b) -> Boolean
       ;; Functions [ 28]:  op surjective? : fa(a,b) (a -> b) -> Boolean
       ;; Functions [ 29]:  op bijective?  : fa(a,b) (a -> b) -> Boolean
       ;; Functions [ 30]:  op inverse     : fa(a,b) Bijective(a,b) -> Bijective(b,a)

       ;; Integer [ 31]:  op ~             : Integer -> Integer
       ("(~ ( 3 )) = 0-3" :swe "(~ ( 3 )) = 0-3" :value t)
       ;; Integer [ 32]:  op +   infixl 25 : Integer * Integer -> Integer
       ("(+ ( 3 , 4 )) = 7" :swe "(+ ( 3 , 4 )) = 7" :value t)
       ("let A = id ( 3 , 4 ) in (+ A) = 7" :swe "let A = id ( 3 , 4 ) in (+ A) = 7" :value t)
       ;; Integer [ 33]:  op -   infixl 25 : Integer * Integer -> Integer
       ("(- ( 7 , 4 )) = 3" :swe "(- ( 7 , 4 )) = 3" :value t)
       ("let A = id ( 7 , 4 ) in (- A) = 3" :swe "let A = id ( 7 , 4 ) in (- A) = 3" :value t)
       ;; Integer [ 34]:  op *   infixl 27 : Integer * Integer -> Integer
       ("( * ( 3, 4 )) = 12" :swe "( * ( 3, 4 )) = 12" :value t)
       ("let A = id ( 3, 4 ) in ( * A) = 12" :swe "let A = id ( 3, 4 ) in ( * A) = 12" :value t)
       ;; Integer [ 35]:  op div infixl 26 : Integer * NZInteger -> Integer
       ("(div ( 27 , 10 )) = 2" :swe "(div ( 27 , 10 )) = 2" :value t)
       ("let A = id ( 27 , 10 ) in (div A) = 2" :swe "let A = id ( 27 , 10 ) in (div A) = 2" :value t)
       ;; Integer [ 36]:  op rem infixl 26 : Integer * NZInteger -> Integer
       ("(rem ( 27 , 10 )) = 7" :swe "(rem ( 27 , 10 )) = 7" :value t)
       ("let A = id ( 27 , 10 ) in (rem A) = 7" :swe "let A = id ( 27 , 10 ) in (rem A) = 7" :value t)
       ;; Integer [ 37]:  op <   infixl 20 : Integer * Integer -> Boolean
       ("(< ( 3 , 4 )) = true" :swe "(< ( 3 , 4 )) = true" :value t)
       ("let A = id ( 3 , 4 ) in (< A) = true" :swe "let A = id ( 3 , 4 ) in (< A) = true" :value t)
       ("(< ( 4 , 4 )) = false" :swe "(< ( 4 , 4 )) = false" :value t)
       ("let A = id ( 4 , 4 ) in (< A) = false" :swe "let A = id ( 4 , 4 ) in (< A) = false" :value t)
       ;; Integer [ 38]:  op <=  infixl 20 : Integer * Integer -> Boolean
       ("(<= ( 3 , 3 )) = true" :swe "(<= ( 3 , 3 )) = true" :value t)
       ("let A = id ( 3 , 3 ) in (<= A) = true" :swe "let A = id ( 3 , 3 ) in (<= A) = true" :value t)
       ("(<= ( 4 , 3 )) = false" :swe "(<= ( 4 , 3 )) = false" :value t)
       ("let A = id ( 4 , 3 ) in (<= A) = false" :swe "let A = id ( 4 , 3 ) in (<= A) = false" :value t)
       ;; Integer [ 39]:  op >  infixl 20 : Integer * Integer -> Boolean
       ("(> ( 4 , 3 )) = true" :swe "(> ( 4 , 3 )) = true" :value t)
       ("let A = id ( 4 , 3 ) in (> A) = true" :swe "let A = id ( 4 , 3 ) in (> A) = true" :value t)
       ("(> ( 4 , 4 )) = false" :swe "(> ( 4 , 4 )) = false" :value t)
       ("let A = id ( 4 , 4 ) in (> A) = false" :swe "let A = id ( 4 , 4 ) in (> A) = false" :value t)
       ;; Integer [ 40]:  op >= infixl 20 : Integer * Integer -> Boolean
       ("(>= ( 3 , 3 )) = true" :swe "(>= ( 3 , 3 )) = true" :value t)
       ("let A = id ( 3 , 3 ) in (>= A) = true" :swe "let A = id ( 3 , 3 ) in (>= A) = true" :value t)
       ("(>= ( 3 , 4 )) = false" :swe "(>= ( 3 , 4 )) = false" :value t)
       ("let A = id ( 3 , 4 ) in (>= A) = false" :swe "let A = id ( 3 , 4 ) in (>= A) = false" :value t)
       ;; Integer [ 41]:  op abs          : Integer -> Integer
       ("(abs ( ~3 )) = 3" :swe "(abs ( ~3 )) = 3" :value t)
       ("(abs ( 3 )) = 3" :swe "(abs ( 3 )) = 3" :value t)
       ;; Integer [ 42]:  op min          : Integer * Integer -> Integer
       ("(min ( 3 , 4 )) = 3" :swe "(min ( 3 , 4 )) = 3" :value t)
       ("let A = id ( 3 , 4 ) in (min A) = 3" :swe "let A = id ( 3 , 4 ) in (min A) = 3" :value t)
       ;; Integer [ 43]:  op max          : Integer * Integer -> Integer
       ("(max ( 3 , 4 )) = 4" :swe "(max ( 3 , 4 )) = 4" :value t)
       ("let A = id ( 3 , 4 ) in (max A) = 4" :swe "let A = id ( 3 , 4 ) in (max A) = 4" :value t)
       ;; Integer [ 44]:  op compare      : Integer * Integer -> Comparison
       ("(compare ( 3 , 4 )) = Less" :swe "(compare ( 3 , 4 )) = Less" :value t)
       ("let A = id ( 3 , 4 ) in (compare A) = Less" :swe "let A = id ( 3 , 4 ) in (compare A) = Less" :value t)
       ("(compare ( 4 , 4 )) = Equal" :swe "(compare ( 4 , 4 )) = Equal" :value t)
       ("let A = id ( 4 , 4 ) in (compare A) = Equal" :swe "let A = id ( 4 , 4 ) in (compare A) = Equal" :value t)
       ("(compare ( 5 , 4 )) = Greater" :swe "(compare ( 5 , 4 )) = Greater" :value t)
       ("let A = id ( 5 , 4 ) in (compare A) = Greater" :swe "let A = id ( 5 , 4 ) in (compare A) = Greater" :value t)
       ;; Integer [121]:  op toString : Integer -> String  ;; deprecated
       ("(toString ( 123 )) = \"123\"" :swe "(toString ( 123 )) = \"123\"" :value t)
       ;; Integer [132]:  op show : Integer -> String
       ("(Integer.show ( 123 )) = \"123\"" :swe "(Integer.show ( 123 )) = \"123\"" :value t)
       ;; Integer [124]:  op intToString    : Integer -> String
       ("(intToString ( 123 )) = \"123\"" :swe "(intToString ( 123 )) = \"123\"" :value t)
       ;; Integer [124.5]:  op intConvertible : String -> Boolean
       ("(intConvertible ( \"123\" )) = true" :swe "(intConvertible ( \"123\" )) = true" :value t)
       ("(intConvertible ( \"-123\" )) = true" :swe "(intConvertible ( \"-123\" )) = true" :value t)
       ("(intConvertible ( \"000\" )) = true" :swe "(intConvertible ( \"000\" )) = true" :value t)
       ("(intConvertible ( \"\" )) = false" :swe "(intConvertible ( \"\" )) = false" :value t)
       ("(intConvertible ( \"123.00\" )) = false" :swe "(intConvertible ( \"123.00\" )) = false" :value t)
       ;; Integer [125]:  op stringToInt    : (String | intConvertible) -> Integer
       ("(stringToInt ( \"123\" )) = 123" :swe "(stringToInt ( \"123\" )) = 123" :value t)
       ("(stringToInt ( \"-123\" )) = ~123" :swe "(stringToInt ( \"-123\" )) = ~123" :value t)
       ;; List [ 49]:  op nil             : fa(a)   List a

       ("(nil) = []" :swe "(nil) = []" :value t)
       ;; List [ 50]:  op cons            : fa(a)   a * List a -> List a
       ("(cons ( 3 , [4] )) = [3,4]" :swe "(cons ( 3 , [4] )) = [3,4]" :value t)
       ("let A = id ( 3 , [4] ) in (cons A) = [3,4]" :swe "let A = id ( 3 , [4] ) in (cons A) = [3,4]" :value t)
       ;; List [ 51]:  op insert          : fa(a)   a * List a -> List a
       ("(insert ( 3 , [4] )) = [3,4]" :swe "(insert ( 3 , [4] )) = [3,4]" :value t)
       ("let A = id ( 3 , [4] ) in (insert A) = [3,4]" :swe "let A = id ( 3 , [4] ) in (insert A) = [3,4]" :value t)
       ;; List [ 52]:  op length          : fa(a)   List a -> Nat
       ("(length ( [3,4] )) = 2" :swe "(length ( [3,4] )) = 2" :value t)
       ;; List [ 53]:  op null            : fa(a)   List a -> Boolean
       ("(null ( nil )) = true" :swe "(null ( nil )) = true" :value t)
       ("(null ( [3] )) = false" :swe "(null ( [3] )) = false" :value t)
       ;; List [ 54]:  op hd              : fa(a)   {l : List a | ~(null l)} -> a
       ("(hd ( [3,4] )) = 3" :swe "(hd ( [3,4] )) = 3" :value t)
       ;; List [ 55]:  op tl              : fa(a)   {l : List a | ~(null l)} -> List a
       ("(tl ( [3,4] )) = [4]" :swe "(tl ( [3,4] )) = [4]" :value t)
       ;; List [ 56]:  op concat          : fa(a)   List a * List a -> List a
       ("(concat ( [3] , [4] )) = [3,4]" :swe "(concat ( [3] , [4] )) = [3,4]" :value t)
       ("let A = id ( [3] , [4] ) in (concat A) = [3,4]" :swe "let A = id ( [3] , [4] ) in (concat A) = [3,4]" :value t)
       ;; List [ 57]:  op ++ infixl 11    : fa(a)   List a * List a -> List a
       ("(++ ( [3] , [4] )) = [3,4]" :swe "(++ ( [3] , [4] )) = [3,4]" :value t)
       ("let A = id ( [3] , [4] ) in (++ A) = [3,4]" :swe "let A = id ( [3] , [4] ) in (++ A) = [3,4]" :value t)
       ;; List [ 58]:  op @  infixl 11    : fa(a)   List a * List a -> List a
       ("(@ ( [3] , [4] )) = [3,4]" :swe "(@ ( [3] , [4] )) = [3,4]" :value t)
       ("let A = id ( [3] , [4] ) in (@ A) = [3,4]" :swe "let A = id ( [3] , [4] ) in (@ A) = [3,4]" :value t)
       ;; List [ 59]:  op nth             : fa(a)   {(l,i) : List a * Nat | i < length l} -> a
       ("(nth ( [3,4,5] , 1 )) = 4" :swe "(nth ( [3,4,5] , 1 )) = 4" :value t)
       ("let A = id ( [3,4,5] , 1 ) in (nth A) = 4" :swe "let A = id ( [3,4,5] , 1 ) in (nth A) = 4" :value t)
       ;; List [ 60]:  op nthTail         : fa(a)   {(l,i) : List a * Nat | i < length l} -> List a
       ("(nthTail ( [3,4,5] , 1 )) = [5]" :swe "(nthTail ( [3,4,5] , 1 )) = [5]" :value t)
       ("let A = id ( [3,4,5] , 1 ) in (nthTail A) = [5]" :swe "let A = id ( [3,4,5] , 1 ) in (nthTail A) = [5]" :value t)
       ;; List [ 61]:  op member          : fa(a)   a * List a -> Boolean
       ("(member ( 4 , [3,5,7] )) = false" :swe "(member ( 4 , [3,5,7] )) = false" :value t)
       ("let A = id ( 4 , [3,5,7] ) in (member A) = false" :swe "let A = id ( 4 , [3,5,7] ) in (member A) = false" :value t)
       ("(member ( 5 , [3,5,7] )) = true" :swe "(member ( 5 , [3,5,7] )) = true" :value t)
       ("let A = id ( 5 , [3,5,7] ) in (member A) = true" :swe "let A = id ( 5 , [3,5,7] ) in (member A) = true" :value t)
       ;; List [ 62]:  op sublist         : fa(a)   {(l,i,j) : List a * Nat * Nat | i < j & j <= length l} -> List a
       ("(sublist ( [3,1,4,1,5,9] , 2 , 4 )) = [4,1]" :swe "(sublist ( [3,1,4,1,5,9] , 2 , 4 )) = [4,1]" :value t)
       ("let A = id ( [3,1,4,1,5,9] , 2 , 4 ) in (sublist A) = [4,1]" :swe "let A = id ( [3,1,4,1,5,9] , 2 , 4 ) in (sublist A) = [4,1]" :value t)
       ;; List [ 63]:  op map             : fa(a,b) (a -> b) -> List a -> List b
       ("(map ( succ ) ( [3,4,5] )) = [4,5,6]" :swe "(map ( succ ) ( [3,4,5] )) = [4,5,6]" :value t)
       ("let F = map ( succ ) in (F ( [3,4,5] )) = [4,5,6]" :swe "let F = map ( succ ) in (F ( [3,4,5] )) = [4,5,6]" :value t)
       ;; List [ 64]:  op mapPartial      : fa(a,b) (a -> Option b) -> List a -> List b
       ("(mapPartial ( fn(n)->if(n<1)then(None)else(Some(pred(n))) ) ( [5,0,2] )) = [4,1]" :swe "(mapPartial ( fn(n)->if(n<1)then(None)else(Some(pred(n))) ) ( [5,0,2] )) = [4,1]" :value t)
       ("let F = mapPartial ( fn(n)->if(n<1)then(None)else(Some(pred(n))) ) in (F ( [5,0,2] )) = [4,1]" :swe "let F = mapPartial ( fn(n)->if(n<1)then(None)else(Some(pred(n))) ) in (F ( [5,0,2] )) = [4,1]" :value t)
       ;; List [ 65]:  op foldl           : fa(a,b) (a * b -> b) -> b -> List a -> b
       ("(foldl ( fn(m,n)->(m)rem(n) ) ( 20 ) ( [77,47] )) = 13" :swe "(foldl ( fn(m,n)->(m)rem(n) ) ( 20 ) ( [77,47] )) = 13" :value t)
       ("let F = foldl ( fn(m,n)->(m)rem(n) ) in (F ( 20 ) ( [77,47] )) = 13" :swe "let F = foldl ( fn(m,n)->(m)rem(n) ) in (F ( 20 ) ( [77,47] )) = 13" :value t)
       ;; List [ 66]:  op foldr           : fa(a,b) (a * b -> b) -> b -> List a -> b
       ("(foldr ( fn(m,n)->(m)rem(n) ) ( 77 ) ( [27,91] )) = 13" :swe "(foldr ( fn(m,n)->(m)rem(n) ) ( 77 ) ( [27,91] )) = 13" :value t)
       ("let F = foldr ( fn(m,n)->(m)rem(n) ) in (F ( 77 ) ( [27,91] )) = 13" :swe "let F = foldr ( fn(m,n)->(m)rem(n) ) in (F ( 77 ) ( [27,91] )) = 13" :value t)
       ;; List [ 67]:  op exists          : fa(a)   (a -> Boolean) -> List a -> Boolean
       ("(exists ( posNat? ) ( [] )) = false" :swe "(exists ( posNat? ) ( [] )) = false" :value t)
       ("let F = exists ( posNat? ) in (F ( [] )) = false" :swe "let F = exists ( posNat? ) in (F ( [] )) = false" :value t)
       ("(exists ( posNat? ) ( [0,0,0] )) = false" :swe "(exists ( posNat? ) ( [0,0,0] )) = false" :value t)
       ("let F = exists ( posNat? ) in (F ( [0,0,0] )) = false" :swe "let F = exists ( posNat? ) in (F ( [0,0,0] )) = false" :value t)
       ("(exists ( posNat? ) ( [0,1,0] )) = true" :swe "(exists ( posNat? ) ( [0,1,0] )) = true" :value t)
       ("let F = exists ( posNat? ) in (F ( [0,1,0] )) = true" :swe "let F = exists ( posNat? ) in (F ( [0,1,0] )) = true" :value t)
       ;; List [ 68]:  op all             : fa(a)   (a -> Boolean) -> List a -> Boolean
       ("(all ( posNat? ) ( [] )) = true" :swe "(all ( posNat? ) ( [] )) = true" :value t)
       ("let F = all ( posNat? ) in (F ( [] )) = true" :swe "let F = all ( posNat? ) in (F ( [] )) = true" :value t)
       ("(all ( posNat? ) ( [1,1,1] )) = true" :swe "(all ( posNat? ) ( [1,1,1] )) = true" :value t)
       ("let F = all ( posNat? ) in (F ( [1,1,1] )) = true" :swe "let F = all ( posNat? ) in (F ( [1,1,1] )) = true" :value t)
       ("(all ( posNat? ) ( [1,0,1] )) = false" :swe "(all ( posNat? ) ( [1,0,1] )) = false" :value t)
       ("let F = all ( posNat? ) in (F ( [1,0,1] )) = false" :swe "let F = all ( posNat? ) in (F ( [1,0,1] )) = false" :value t)
       ;; List [ 69]:  op filter          : fa(a)   (a -> Boolean) -> List a -> List a
       ("(filter ( posNat? ) ( [5,0,2] )) = [5,2]" :swe "(filter ( posNat? ) ( [5,0,2] )) = [5,2]" :value t)
       ("let F = filter ( posNat? ) in (F ( [5,0,2] )) = [5,2]" :swe "let F = filter ( posNat? ) in (F ( [5,0,2] )) = [5,2]" :value t)
       ;; List [ 70]:  op diff            : fa(a)   List a * List a -> List a
       ("(diff ( [3,1,4,1,5,9] , [5,9,2,1] )) = [3,4]" :swe "(diff ( [3,1,4,1,5,9] , [5,9,2,1] )) = [3,4]" :value t)
       ("let A = id ( [3,1,4,1,5,9] , [5,9,2,1] ) in (diff A) = [3,4]" :swe "let A = id ( [3,1,4,1,5,9] , [5,9,2,1] ) in (diff A) = [3,4]" :value t)
       ;; List [ 71]:  op rev             : fa(a)   List a -> List a
       ("(rev ( [1,2,3] )) = [3,2,1]" :swe "(rev ( [1,2,3] )) = [3,2,1]" :value t)
       ;; List [ 72]:  op rev2            : fa(a)   List a * List a -> List a
       ("(rev2 ( [1,2,3] , [4,5,6] )) = [3,2,1,4,5,6]" :swe "(rev2 ( [1,2,3] , [4,5,6] )) = [3,2,1,4,5,6]" :value t)
       ("let A = id ( [1,2,3] , [4,5,6] ) in (rev2 A) = [3,2,1,4,5,6]" :swe "let A = id ( [1,2,3] , [4,5,6] ) in (rev2 A) = [3,2,1,4,5,6]" :value t)
       ;; List [ 73]:  op flatten         : fa(a)   List(List a) -> List a
       ("(flatten ( [[3,1],[4,1],[5,9]] )) = [3,1,4,1,5,9]" :swe "(flatten ( [[3,1],[4,1],[5,9]] )) = [3,1,4,1,5,9]" :value t)
       ;; List [ 74]:  op find            : fa(a)   (a -> Boolean) -> List a -> Option(a)
       ("(find ( posNat? ) ( [0,0,0] )) = None" :swe "(find ( posNat? ) ( [0,0,0] )) = None" :value t)
       ("let F = find ( posNat? ) in (F ( [0,0,0] )) = None" :swe "let F = find ( posNat? ) in (F ( [0,0,0] )) = None" :value t)
       ("(find ( posNat? ) ( [0,1,0] )) = Some(1)" :swe "(find ( posNat? ) ( [0,1,0] )) = Some(1)" :value t)
       ("let F = find ( posNat? ) in (F ( [0,1,0] )) = Some(1)" :swe "let F = find ( posNat? ) in (F ( [0,1,0] )) = Some(1)" :value t)
       ;; List [ 75]:  op tabulate        : fa(a)   Nat * (Nat -> a) -> List a
       ("(tabulate ( 3 , succ )) = [1,2,3]" :swe "(tabulate ( 3 , succ )) = [1,2,3]" :value t)
       ("let A = id ( 3 , succ ) in (tabulate A) = [1,2,3]" :swe "let A = id ( 3 , succ ) in (tabulate A) = [1,2,3]" :value t)
       ;; List [ 76]:  op firstUpTo       : fa(a)   (a -> Boolean) -> List a -> Option (a * List a)
       ("(firstUpTo ( null ) ( [[1],[2,3],[],[4]] )) = Some([],[[1],[2,3]])" :swe "(firstUpTo ( null ) ( [[1],[2,3],[],[4]] )) = Some([],[[1],[2,3]])" :value t)
       ("let F = firstUpTo ( null ) in (F ( [[1],[2,3],[],[4]] )) = Some([],[[1],[2,3]])" :swe "let F = firstUpTo ( null ) in (F ( [[1],[2,3],[],[4]] )) = Some([],[[1],[2,3]])" :value t)
       ("(firstUpTo ( null ) ( [[1],[2,3],[4]] )) = None" :swe "(firstUpTo ( null ) ( [[1],[2,3],[4]] )) = None" :value t)
       ("let F = firstUpTo ( null ) in (F ( [[1],[2,3],[4]] )) = None" :swe "let F = firstUpTo ( null ) in (F ( [[1],[2,3],[4]] )) = None" :value t)
       ;; List [ 78]:  op splitList       : fa(a)  (a -> Boolean) -> List a -> Option(List a * a * List a)
       ("(splitList ( null ) ( [[1],[2,3],[],[4]] )) = Some([[1],[2,3]],[],[[4]])" :swe "(splitList ( null ) ( [[1],[2,3],[],[4]] )) = Some([[1],[2,3]],[],[[4]])" :value t)
       ("let F = splitList ( null ) in (F ( [[1],[2,3],[],[4]] )) = Some([[1],[2,3]],[],[[4]])" :swe "let F = splitList ( null ) in (F ( [[1],[2,3],[],[4]] )) = Some([[1],[2,3]],[],[[4]])" :value t)
       ("(splitList ( null ) ( [[1],[2,3],[4]] )) = None" :swe "(splitList ( null ) ( [[1],[2,3],[4]] )) = None" :value t)
       ("let F = splitList ( null ) in (F ( [[1],[2,3],[4]] )) = None" :swe "let F = splitList ( null ) in (F ( [[1],[2,3],[4]] )) = None" :value t)
       ;; List [ 80]:  op locationOf      : fa(a)  List a * List a -> Option(Nat * List a)
       ("(locationOf ( [] , [3,1,4,1,5] )) = Some(0,[3,1,4,1,5])" :swe "(locationOf ( [] , [3,1,4,1,5] )) = Some(0,[3,1,4,1,5])" :value t)
       ("let A = id ( [] , [3,1,4,1,5] ) in (locationOf A) = Some(0,[3,1,4,1,5])" :swe "let A = id ( [] , [3,1,4,1,5] ) in (locationOf A) = Some(0,[3,1,4,1,5])" :value t)
       ("(locationOf ( [1,4] , [3,1,4,1,5] )) = Some(1,[1,5])" :swe "(locationOf ( [1,4] , [3,1,4,1,5] )) = Some(1,[1,5])" :value t)
       ("let A = id ( [1,4] , [3,1,4,1,5] ) in (locationOf A) = Some(1,[1,5])" :swe "let A = id ( [1,4] , [3,1,4,1,5] ) in (locationOf A) = Some(1,[1,5])" :value t)
       ("(locationOf ( [1,3] , [3,1,4,1,5] )) = None" :swe "(locationOf ( [1,3] , [3,1,4,1,5] )) = None" :value t)
       ("let A = id ( [1,3] , [3,1,4,1,5] ) in (locationOf A) = None" :swe "let A = id ( [1,3] , [3,1,4,1,5] ) in (locationOf A) = None" :value t)
       ;; List [ 81]:  op compare         : fa(a)  (a * a -> Comparison) -> List a * List a -> Comparison
       ("(compare ( Integer.compare ) ( [] , [1] )) = Less" :swe "(compare ( Integer.compare ) ( [] , [1] )) = Less" :value t)
       ("let F = compare ( Integer.compare ) in (F ( [] , [1] )) = Less" :swe "let F = compare ( Integer.compare ) in (F ( [] , [1] )) = Less" :value t)
       ("(compare ( Integer.compare ) ( [0,9] , [1] )) = Less" :swe "(compare ( Integer.compare ) ( [0,9] , [1] )) = Less" :value t)
       ("let F = compare ( Integer.compare ) in (F ( [0,9] , [1] )) = Less" :swe "let F = compare ( Integer.compare ) in (F ( [0,9] , [1] )) = Less" :value t)
       ("(compare ( Integer.compare ) ( [1] , [1] )) = Equal" :swe "(compare ( Integer.compare ) ( [1] , [1] )) = Equal" :value t)
       ("let F = compare ( Integer.compare ) in (F ( [1] , [1] )) = Equal" :swe "let F = compare ( Integer.compare ) in (F ( [1] , [1] )) = Equal" :value t)
       ("(compare ( Integer.compare ) ( [1,0] , [1] )) = Greater" :swe "(compare ( Integer.compare ) ( [1,0] , [1] )) = Greater" :value t)
       ("let F = compare ( Integer.compare ) in (F ( [1,0] , [1] )) = Greater" :swe "let F = compare ( Integer.compare ) in (F ( [1,0] , [1] )) = Greater" :value t)
       ;; List [ 82]:  op app             : fa(a)  (a -> ()) -> List a -> ()  ;; deprecated
       ;; List [134]:  op show    : String -> List String -> String
       ("(show ( \"ns\" ) ( [\"no\",\"e\",\"e\"] )) = \"nonsense\"" :swe "(show ( \"ns\" ) ( [\"no\",\"e\",\"e\"] )) = \"nonsense\"" :value t)
       ("let F = show ( \"ns\" ) in (F ( [\"no\",\"e\",\"e\"] )) = \"nonsense\"" :swe "let F = show ( \"ns\" ) in (F ( [\"no\",\"e\",\"e\"] )) = \"nonsense\"" :value t)

       ;; Nat [ 84]:  op succ    : Nat -> Nat
       ("(succ ( 6 )) = 7" :swe "(succ ( 6 )) = 7" :value t)
       ;; Nat [ 85]:  op pred    : Nat -> Integer
       ("(pred ( 7 )) = 6" :swe "(pred ( 7 )) = 6" :value t)
       ;; Nat [ 86]:  op zero    : Nat 
       ("(zero) = 0" :swe "(zero) = 0" :value t)
       ;; Nat [ 87]:  op one     : Nat
       ("(one) = 1" :swe "(one) = 1" :value t)
       ;; Nat [ 88]:  op two     : Nat
       ("(two) = 2" :swe "(two) = 2" :value t)
       ;; Nat [ 89]:  op posNat? : Nat -> Boolean
       ("(posNat? ( 0 )) = false" :swe "(posNat? ( 0 )) = false" :value t)
       ("(posNat? ( 1 )) = true" :swe "(posNat? ( 1 )) = true" :value t)
       ;; Nat [122]:  op toString     : Nat -> String      ;; deprecated
       ("(toString ( 123 )) = \"123\"" :swe "(toString ( 123 )) = \"123\"" :value t)
       ;; Nat [133]:  op show     : Nat -> String
       ("(Nat.show ( 123 )) = \"123\"" :swe "(Nat.show ( 123 )) = \"123\"" :value t)
       ;; Nat [126]:  op natToString  : Nat -> String
       ("(natToString ( 123 )) = \"123\"" :swe "(natToString ( 123 )) = \"123\"" :value t)
       ;; Nat [127]:  op stringToNat  : {s : String | length s > 0 & all isNum (explode s)} -> Nat

       ;; Option [ 94]:  op some      : fa(a) a -> Option a
       ("(some ( 1 )) = Some(1)" :swe "(some ( 1 )) = Some(1)" :value t)
       ;; Option [ 95]:  op none      : fa(a) Option a
       ("(none) = None" :swe "(none) = None" :value t)
       ;; Option [ 96]:  op some?     : fa(a) Option a -> Boolean
       ("(some? ( None )) = false" :swe "(some? ( None )) = false" :value t)
       ("(some? ( Some(1) )) = true" :swe "(some? ( Some(1) )) = true" :value t)
       ;; Option [ 97]:  op none?     : fa(a) Option a -> Boolean
       ("(none? ( None )) = true" :swe "(none? ( None )) = true" :value t)
       ("(none? ( Some(1) )) = false" :swe "(none? ( Some(1) )) = false" :value t)
       ;; Option [ 98]:  op compare   : fa(a) (a * a -> Comparison) -> Option a * Option a -> Comparison
       ("(compare ( Integer.compare ) ( None , None )) = Equal" :swe "(compare ( Integer.compare ) ( None , None )) = Equal" :value t)
       ("let F = compare ( Integer.compare ) in (F ( None , None )) = Equal" :swe "let F = compare ( Integer.compare ) in (F ( None , None )) = Equal" :value t)
       ("(compare ( Integer.compare ) ( None , Some(1) )) = Less" :swe "(compare ( Integer.compare ) ( None , Some(1) )) = Less" :value t)
       ("let F = compare ( Integer.compare ) in (F ( None , Some(1) )) = Less" :swe "let F = compare ( Integer.compare ) in (F ( None , Some(1) )) = Less" :value t)
       ("(compare ( Integer.compare ) ( Some(1) , None )) = Greater" :swe "(compare ( Integer.compare ) ( Some(1) , None )) = Greater" :value t)
       ("let F = compare ( Integer.compare ) in (F ( Some(1) , None )) = Greater" :swe "let F = compare ( Integer.compare ) in (F ( Some(1) , None )) = Greater" :value t)
       ("(compare ( Integer.compare ) ( Some(0) , Some(1) )) = Less" :swe "(compare ( Integer.compare ) ( Some(0) , Some(1) )) = Less" :value t)
       ("let F = compare ( Integer.compare ) in (F ( Some(0) , Some(1) )) = Less" :swe "let F = compare ( Integer.compare ) in (F ( Some(0) , Some(1) )) = Less" :value t)
       ("(compare ( Integer.compare ) ( Some(1) , Some(1) )) = Equal" :swe "(compare ( Integer.compare ) ( Some(1) , Some(1) )) = Equal" :value t)
       ("let F = compare ( Integer.compare ) in (F ( Some(1) , Some(1) )) = Equal" :swe "let F = compare ( Integer.compare ) in (F ( Some(1) , Some(1) )) = Equal" :value t)
       ("(compare ( Integer.compare ) ( Some(2) , Some(1) )) = Greater" :swe "(compare ( Integer.compare ) ( Some(2) , Some(1) )) = Greater" :value t)
       ("let F = compare ( Integer.compare ) in (F ( Some(2) , Some(1) )) = Greater" :swe "let F = compare ( Integer.compare ) in (F ( Some(2) , Some(1) )) = Greater" :value t)
       ;; Option [ 99]:  op mapOption : fa(a,b) (a -> b) -> Option a -> Option b
       ("(mapOption ( succ ) ( None )) = None" :swe "(mapOption ( succ ) ( None )) = None" :value t)
       ("let F = mapOption ( succ ) in (F ( None )) = None" :swe "let F = mapOption ( succ ) in (F ( None )) = None" :value t)
       ("(mapOption ( succ ) ( Some(0) )) = Some(1)" :swe "(mapOption ( succ ) ( Some(0) )) = Some(1)" :value t)
       ("let F = mapOption ( succ ) in (F ( Some(0) )) = Some(1)" :swe "let F = mapOption ( succ ) in (F ( Some(0) )) = Some(1)" :value t)
       ;; Option [131]:  op show  : fa(a) (a -> String) -> Option a -> String
       ("(show ( natToString ) ( None )) = \"None\"" :swe "(show ( natToString ) ( None )) = \"None\"" :value t)
       ("let F = show ( natToString ) in (F ( None )) = \"None\"" :swe "let F = show ( natToString ) in (F ( None )) = \"None\"" :value t)
       ("(show ( natToString ) ( Some(1) )) = \"(Some\\s1)\"" :swe "(show ( natToString ) ( Some(1) )) = \"(Some\\s1)\"" :value t)
       ("let F = show ( natToString ) in (F ( Some(1) )) = \"(Some\\s1)\"" :swe "let F = show ( natToString ) in (F ( Some(1) )) = \"(Some\\s1)\"" :value t)

       ;; String [100]:  op explode : String -> List Char
       ("(explode ( \"\" )) = []" :swe "(explode ( \"\" )) = []" :value t)
       ("(explode ( \"abc\" )) = [#a,#b,#c]" :swe "(explode ( \"abc\" )) = [#a,#b,#c]" :value t)
       ;; String [102]:  op implode       : List Char -> String
       ("(implode ( [] )) = \"\"" :swe "(implode ( [] )) = \"\"" :value t)
       ("(implode ( [#a,#b,#c] )) = \"abc\"" :swe "(implode ( [#a,#b,#c] )) = \"abc\"" :value t)
       ;; String [103]:  op length        : String -> Nat
       ("(length ( \"\" )) = 0" :swe "(length ( \"\" )) = 0" :value t)
       ("(length ( \"abc\" )) = 3" :swe "(length ( \"abc\" )) = 3" :value t)
       ;; String [104]:  op concat        : String * String -> String
       ("(concat ( \"now\" , \"here\" )) = \"nowhere\"" :swe "(concat ( \"now\" , \"here\" )) = \"nowhere\"" :value t)
       ("let A = id ( \"now\" , \"here\" ) in (concat A) = \"nowhere\"" :swe "let A = id ( \"now\" , \"here\" ) in (concat A) = \"nowhere\"" :value t)
       ;; String [105]:  op ++ infixl 11  : String * String -> String
       ("(++ ( \"now\" , \"here\" )) = \"nowhere\"" :swe "(++ ( \"now\" , \"here\" )) = \"nowhere\"" :value t)
       ("let A = id ( \"now\" , \"here\" ) in (++ A) = \"nowhere\"" :swe "let A = id ( \"now\" , \"here\" ) in (++ A) = \"nowhere\"" :value t)
       ;; String [106]:  op ^  infixl 11  : String * String -> String
       ("(^ ( \"now\" , \"here\" )) = \"nowhere\"" :swe "(^ ( \"now\" , \"here\" )) = \"nowhere\"" :value t)
       ("let A = id ( \"now\" , \"here\" ) in (^ A) = \"nowhere\"" :swe "let A = id ( \"now\" , \"here\" ) in (^ A) = \"nowhere\"" :value t)
       ;; String [107]:  op map           : (Char -> Char) -> String -> String
       ("(map ( fn(c)->chr(96+(let(v)=(ord(c)-96)in((v+13)rem(26)))) ) ( \"terra\" )) = \"green\"" :swe "(map ( fn(c)->chr(96+(let(v)=(ord(c)-96)in((v+13)rem(26)))) ) ( \"terra\" )) = \"green\"" :value t)
       ("let F = map ( fn(c)->chr(96+(let(v)=(ord(c)-96)in((v+13)rem(26)))) ) in (F ( \"terra\" )) = \"green\"" :swe "let F = map ( fn(c)->chr(96+(let(v)=(ord(c)-96)in((v+13)rem(26)))) ) in (F ( \"terra\" )) = \"green\"" :value t)
       ;; String [108]:  op exists        : (Char -> Boolean) -> String -> Boolean
       ("(exists ( isNum ) ( \"\" )) = false" :swe "(exists ( isNum ) ( \"\" )) = false" :value t)
       ("let F = exists ( isNum ) in (F ( \"\" )) = false" :swe "let F = exists ( isNum ) in (F ( \"\" )) = false" :value t)
       ("(exists ( isNum ) ( \"c3po\" )) = true" :swe "(exists ( isNum ) ( \"c3po\" )) = true" :value t)
       ("let F = exists ( isNum ) in (F ( \"c3po\" )) = true" :swe "let F = exists ( isNum ) in (F ( \"c3po\" )) = true" :value t)
       ;; String [109]:  op all           : (Char -> Boolean) -> String -> Boolean
       ("(all ( isAlpha ) ( \"\" )) = true" :swe "(all ( isAlpha ) ( \"\" )) = true" :value t)
       ("let F = all ( isAlpha ) in (F ( \"\" )) = true" :swe "let F = all ( isAlpha ) in (F ( \"\" )) = true" :value t)
       ("(all ( isAlpha ) ( \"c3po\" )) = false" :swe "(all ( isAlpha ) ( \"c3po\" )) = false" :value t)
       ("let F = all ( isAlpha ) in (F ( \"c3po\" )) = false" :swe "let F = all ( isAlpha ) in (F ( \"c3po\" )) = false" :value t)
       ;; String [110]:  op sub           : {(s,n) : String * Nat | n < length s} -> Char
       ("(sub ( \"afn\" , 1 )) = #f" :swe "(sub ( \"afn\" , 1 )) = #f" :value t)
       ("let A = id ( \"afn\" , 1 ) in (sub A) = #f" :swe "let A = id ( \"afn\" , 1 ) in (sub A) = #f" :value t)
       ;; String [111]:  op substring     : {(s,i,j) : String * Nat * Nat | i < j & j <= length s} ->
       ("(substring ( \"twitchy\" , 2, 6 )) = \"itch\"" :swe "(substring ( \"twitchy\" , 2, 6 )) = \"itch\"" :value t)
       ("let A = id ( \"twitchy\" , 2, 6 ) in (substring A) = \"itch\"" :swe "let A = id ( \"twitchy\" , 2, 6 ) in (substring A) = \"itch\"" :value t)
       ;; String [112]:  op concatList    : List String -> String
       ("(concatList ( [] )) = \"\"" :swe "(concatList ( [] )) = \"\"" :value t)
       ("(concatList ( [\"now\",\"here\"] )) = \"nowhere\"" :swe "(concatList ( [\"now\",\"here\"] )) = \"nowhere\"" :value t)
       ;; String [113]:  op translate     : (Char -> String) -> String -> String
       ("(translate ( fn(c)->implode[c,c] ) ( \"2B\" )) = \"22BB\"" :swe "(translate ( fn(c)->implode[c,c] ) ( \"2B\" )) = \"22BB\"" :value t)
       ("let F = translate ( fn(c)->implode[c,c] ) in (F ( \"2B\" )) = \"22BB\"" :swe "let F = translate ( fn(c)->implode[c,c] ) in (F ( \"2B\" )) = \"22BB\"" :value t)
       ;; String [114]:  op lt  infixl 20 : String * String -> Boolean
       ("(lt ( \"\" , \"\" )) = false" :swe "(lt ( \"\" , \"\" )) = false" :value t)
       ("let A = id ( \"\" , \"\" ) in (lt A) = false" :swe "let A = id ( \"\" , \"\" ) in (lt A) = false" :value t)
       ("(lt ( \"\" , \"1\" )) = true" :swe "(lt ( \"\" , \"1\" )) = true" :value t)
       ("let A = id ( \"\" , \"1\" ) in (lt A) = true" :swe "let A = id ( \"\" , \"1\" ) in (lt A) = true" :value t)
       ("(lt ( \"0\" , \"1\" )) = true" :swe "(lt ( \"0\" , \"1\" )) = true" :value t)
       ("let A = id ( \"0\" , \"1\" ) in (lt A) = true" :swe "let A = id ( \"0\" , \"1\" ) in (lt A) = true" :value t)
       ("(lt ( \"09\" , \"1\" )) = true" :swe "(lt ( \"09\" , \"1\" )) = true" :value t)
       ("let A = id ( \"09\" , \"1\" ) in (lt A) = true" :swe "let A = id ( \"09\" , \"1\" ) in (lt A) = true" :value t)
       ("(lt ( \"1\" , \"\" )) = false" :swe "(lt ( \"1\" , \"\" )) = false" :value t)
       ("let A = id ( \"1\" , \"\" ) in (lt A) = false" :swe "let A = id ( \"1\" , \"\" ) in (lt A) = false" :value t)
       ("(lt ( \"1\" , \"1\" )) = false" :swe "(lt ( \"1\" , \"1\" )) = false" :value t)
       ("let A = id ( \"1\" , \"1\" ) in (lt A) = false" :swe "let A = id ( \"1\" , \"1\" ) in (lt A) = false" :value t)
       ("(lt ( \"10\" , \"1\" )) = false" :swe "(lt ( \"10\" , \"1\" )) = false" :value t)
       ("let A = id ( \"10\" , \"1\" ) in (lt A) = false" :swe "let A = id ( \"10\" , \"1\" ) in (lt A) = false" :value t)
       ("(lt ( \"2\" , \"1\" )) = false" :swe "(lt ( \"2\" , \"1\" )) = false" :value t)
       ("let A = id ( \"2\" , \"1\" ) in (lt A) = false" :swe "let A = id ( \"2\" , \"1\" ) in (lt A) = false" :value t)
       ;; String [115]:  op leq infixl 20 : String * String -> Boolean
       ("(leq ( \"\" , \"\" )) = true" :swe "(leq ( \"\" , \"\" )) = true" :value t)
       ("let A = id ( \"\" , \"\" ) in (leq A) = true" :swe "let A = id ( \"\" , \"\" ) in (leq A) = true" :value t)
       ("(leq ( \"\" , \"1\" )) = true" :swe "(leq ( \"\" , \"1\" )) = true" :value t)
       ("let A = id ( \"\" , \"1\" ) in (leq A) = true" :swe "let A = id ( \"\" , \"1\" ) in (leq A) = true" :value t)
       ("(leq ( \"0\" , \"1\" )) = true" :swe "(leq ( \"0\" , \"1\" )) = true" :value t)
       ("let A = id ( \"0\" , \"1\" ) in (leq A) = true" :swe "let A = id ( \"0\" , \"1\" ) in (leq A) = true" :value t)
       ("(leq ( \"09\" , \"1\" )) = true" :swe "(leq ( \"09\" , \"1\" )) = true" :value t)
       ("let A = id ( \"09\" , \"1\" ) in (leq A) = true" :swe "let A = id ( \"09\" , \"1\" ) in (leq A) = true" :value t)
       ("(leq ( \"1\" , \"\" )) = false" :swe "(leq ( \"1\" , \"\" )) = false" :value t)
       ("let A = id ( \"1\" , \"\" ) in (leq A) = false" :swe "let A = id ( \"1\" , \"\" ) in (leq A) = false" :value t)
       ("(leq ( \"1\" , \"1\" )) = true" :swe "(leq ( \"1\" , \"1\" )) = true" :value t)
       ("let A = id ( \"1\" , \"1\" ) in (leq A) = true" :swe "let A = id ( \"1\" , \"1\" ) in (leq A) = true" :value t)
       ("(leq ( \"10\" , \"1\" )) = false" :swe "(leq ( \"10\" , \"1\" )) = false" :value t)
       ("let A = id ( \"10\" , \"1\" ) in (leq A) = false" :swe "let A = id ( \"10\" , \"1\" ) in (leq A) = false" :value t)
       ("(leq ( \"2\" , \"1\" )) = false" :swe "(leq ( \"2\" , \"1\" )) = false" :value t)
       ("let A = id ( \"2\" , \"1\" ) in (leq A) = false" :swe "let A = id ( \"2\" , \"1\" ) in (leq A) = false" :value t)
       ;; String [116]:  op newline       : String
       ("(newline) = \"\\n\"" :swe "(newline) = \"\\n\"" :value t)
       ;; String [117]:  op toScreen      : String -> ()  ;; deprecated
       ;; String [118]:  op writeLine     : String -> ()  ;; deprecated
       ;; String [119]:  op compare : String * String -> Comparison
       ("(compare ( \"\" , \"\" )) = Equal" :swe "(compare ( \"\" , \"\" )) = Equal" :value t)
       ("let A = id ( \"\" , \"\" ) in (compare A) = Equal" :swe "let A = id ( \"\" , \"\" ) in (compare A) = Equal" :value t)
       ("(compare ( \"\" , \"1\" )) = Less" :swe "(compare ( \"\" , \"1\" )) = Less" :value t)
       ("let A = id ( \"\" , \"1\" ) in (compare A) = Less" :swe "let A = id ( \"\" , \"1\" ) in (compare A) = Less" :value t)
       ("(compare ( \"0\" , \"1\" )) = Less" :swe "(compare ( \"0\" , \"1\" )) = Less" :value t)
       ("let A = id ( \"0\" , \"1\" ) in (compare A) = Less" :swe "let A = id ( \"0\" , \"1\" ) in (compare A) = Less" :value t)
       ("(compare ( \"09\" , \"1\" )) = Less" :swe "(compare ( \"09\" , \"1\" )) = Less" :value t)
       ("let A = id ( \"09\" , \"1\" ) in (compare A) = Less" :swe "let A = id ( \"09\" , \"1\" ) in (compare A) = Less" :value t)
       ("(compare ( \"1\" , \"\" )) = Greater" :swe "(compare ( \"1\" , \"\" )) = Greater" :value t)
       ("let A = id ( \"1\" , \"\" ) in (compare A) = Greater" :swe "let A = id ( \"1\" , \"\" ) in (compare A) = Greater" :value t)
       ("(compare ( \"1\" , \"1\" )) = Equal" :swe "(compare ( \"1\" , \"1\" )) = Equal" :value t)
       ("let A = id ( \"1\" , \"1\" ) in (compare A) = Equal" :swe "let A = id ( \"1\" , \"1\" ) in (compare A) = Equal" :value t)
       ("(compare ( \"10\" , \"1\" )) = Greater" :swe "(compare ( \"10\" , \"1\" )) = Greater" :value t)
       ("let A = id ( \"10\" , \"1\" ) in (compare A) = Greater" :swe "let A = id ( \"10\" , \"1\" ) in (compare A) = Greater" :value t)
       ("(compare ( \"2\" , \"1\" )) = Greater" :swe "(compare ( \"2\" , \"1\" )) = Greater" :value t)
       ("let A = id ( \"2\" , \"1\" ) in (compare A) = Greater" :swe "let A = id ( \"2\" , \"1\" ) in (compare A) = Greater" :value t)
       )
