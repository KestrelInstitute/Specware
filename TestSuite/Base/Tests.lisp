(test  ("(~ ( true )) = false" :swe "(~ ( true )) = false" :value '(:|Bool| . t))
       ("(~ ( false )) = true" :swe "(~ ( false )) = true" :value '(:|Bool| . t))
       ("[true, false, (true), (false)] = [(true), (false), true, false]" :swe "[true, false, (true), (false)] = [(true), (false), true, false]" :value '(:|Bool| . t))
       ;; Boolean [  2]:  op ~   : Boolean -> Boolean 
       ("~ true = false"    :swe "~ true = false"    :value '(:|Bool| . t))
       ("~ false = true"    :swe "~ false = true"    :value '(:|Bool| . t))
       ("~ (~ true) = true"   :swe "~ (~ true) = true"   :value '(:|Bool| . t))
       ("~ (~ false) = false" :swe "~ (~ false) = false" :value '(:|Bool| . t))
       ("[(~)(true)] = [(~)(true)]"     :swe "[(~)(true)] = [(~)(true)]"     :value '(:|Bool| . t))
       ;; Boolean [  2]:  op &   infixr 15 : Boolean * Boolean -> Boolean 
       ("(&& ( false , false )) = false" :swe "(&& ( false , false )) = false" :value '(:|Bool| . t))
       ("let A = id ( false , false ) in (&& A) = false" :swe "let A = id ( false , false ) in (&& A) = false" :value '(:|Bool| . t))
       ("(&& ( false , true )) = false" :swe "(&& ( false , true )) = false" :value '(:|Bool| . t))
       ("let A = id ( false , true ) in (&& A) = false" :swe "let A = id ( false , true ) in (&& A) = false" :value '(:|Bool| . t))
       ("(&& ( true , false )) = false" :swe "(&& ( true , false )) = false" :value '(:|Bool| . t))
       ("let A = id ( true , false ) in (&& A) = false" :swe "let A = id ( true , false ) in (&& A) = false" :value '(:|Bool| . t))
       ("(&& ( true , true )) = true" :swe "(&& ( true , true )) = true" :value '(:|Bool| . t))
       ("let A = id ( true , true ) in (&& A) = true" :swe "let A = id ( true , true ) in (&& A) = true" :value '(:|Bool| . t))
       ("[(&&)(true,true)] = [(&&)(true,true)]"     :swe "[(&&)(true,true)] = [(&&)(true,true)]"     :value '(:|Bool| . t))
       ;; Boolean [  3]:  op ||  infixr 14 : Boolean * Boolean -> Boolean 
       ("(|| ( false , false )) = false" :swe "(|| ( false , false )) = false" :value '(:|Bool| . t))
       ("let A = id ( false , false ) in (|| A) = false" :swe "let A = id ( false , false ) in (|| A) = false" :value '(:|Bool| . t))
       ("(|| ( false , true )) = true" :swe "(|| ( false , true )) = true" :value '(:|Bool| . t))
       ("let A = id ( false , true ) in (|| A) = true" :swe "let A = id ( false , true ) in (|| A) = true" :value '(:|Bool| . t))
       ("(|| ( true , false )) = true" :swe "(|| ( true , false )) = true" :value '(:|Bool| . t))
       ("let A = id ( true , false ) in (|| A) = true" :swe "let A = id ( true , false ) in (|| A) = true" :value '(:|Bool| . t))
       ("(|| ( true , true )) = true" :swe "(|| ( true , true )) = true" :value '(:|Bool| . t))
       ("let A = id ( true , true ) in (|| A) = true" :swe "let A = id ( true , true ) in (|| A) = true" :value '(:|Bool| . t))
       ("[(||)(true,true)] = [(||)(true,true)]"     :swe "[(||)(true,true)] = [(||)(true,true)]"     :value '(:|Bool| . t))
       ;; Boolean [  4]:  op =>  infixr 13 : Boolean * Boolean -> Boolean 
       ("(=> ( false , false )) = true" :swe "(=> ( false , false )) = true" :value '(:|Bool| . t))
       ("let A = id ( false , false ) in (=> A) = true" :swe "let A = id ( false , false ) in (=> A) = true" :value '(:|Bool| . t))
       ("(=> ( false , true )) = true" :swe "(=> ( false , true )) = true" :value '(:|Bool| . t))
       ("let A = id ( false , true ) in (=> A) = true" :swe "let A = id ( false , true ) in (=> A) = true" :value '(:|Bool| . t))
       ("(=> ( true , false )) = false" :swe "(=> ( true , false )) = false" :value '(:|Bool| . t))
       ("let A = id ( true , false ) in (=> A) = false" :swe "let A = id ( true , false ) in (=> A) = false" :value '(:|Bool| . t))
       ("(=> ( true , true )) = true" :swe "(=> ( true , true )) = true" :value '(:|Bool| . t))
       ("let A = id ( true , true ) in (=> A) = true" :swe "let A = id ( true , true ) in (=> A) = true" :value '(:|Bool| . t))
       ("[(=>)(true,true)] = [(=>)(true,true)]"     :swe "[(=>)(true,true)] = [(=>)(true,true)]"     :value '(:|Bool| . t))
       ;; Boolean [  5]:  op <=> infixr 12 : Boolean * Boolean -> Boolean 
       ("(<=> ( false , false )) = true" :swe "(<=> ( false , false )) = true" :value '(:|Bool| . t))
       ("let A = id ( false , false ) in (<=> A) = true" :swe "let A = id ( false , false ) in (<=> A) = true" :value '(:|Bool| . t))
       ("(<=> ( false , true )) = false" :swe "(<=> ( false , true )) = false" :value '(:|Bool| . t))
       ("let A = id ( false , true ) in (<=> A) = false" :swe "let A = id ( false , true ) in (<=> A) = false" :value '(:|Bool| . t))
       ("(<=> ( true , false )) = false" :swe "(<=> ( true , false )) = false" :value '(:|Bool| . t))
       ("let A = id ( true , false ) in (<=> A) = false" :swe "let A = id ( true , false ) in (<=> A) = false" :value '(:|Bool| . t))
       ("(<=> ( true , true )) = true" :swe "(<=> ( true , true )) = true" :value '(:|Bool| . t))
       ("let A = id ( true , true ) in (<=> A) = true" :swe "let A = id ( true , true ) in (<=> A) = true" :value '(:|Bool| . t))
       ("[(<=>)(true,true)] = [(<=>)(true,true)]"     :swe "[(<=>)(true,true)] = [(<=>)(true,true)]"     :value '(:|Bool| . t))
       ;; Boolean [  6]:  op ~=  infixr 20 : fa(a) a * a -> Boolean
       ("(~= ( 4 , 4 )) = false" :swe "(~= ( 4 , 4 )) = false" :value '(:|Bool| . t))
       ("let A = id ( 4 , 4 ) in (~= A) = false" :swe "let A = id ( 4 , 4 ) in (~= A) = false" :value '(:|Bool| . t))
       ("(~= ( 4 , 5 )) = true" :swe "(~= ( 4 , 5 )) = true" :value '(:|Bool| . t))
       ("let A = id ( 4 , 5 ) in (~= A) = true" :swe "let A = id ( 4 , 5 ) in (~= A) = true" :value '(:|Bool| . t))
       ("[(~=)(4, 5)] = [(~=)(4, 5)]"     :swe "[(~=)(4, 5)] = [(~=)(4, 5)]"     :value '(:|Bool| . t))
       ;; Boolean [  7]:  op compare  : Boolean * Boolean -> Comparison
       ("(compare ( false , false )) = Equal" :swe "(compare ( false , false )) = Equal" :value '(:|Bool| . t))
       ("let A = id ( false , false ) in (compare A) = Equal" :swe "let A = id ( false , false ) in (compare A) = Equal" :value '(:|Bool| . t))
       ("(compare ( false , true )) = Less" :swe "(compare ( false , true )) = Less" :value '(:|Bool| . t))
       ("let A = id ( false , true ) in (compare A) = Less" :swe "let A = id ( false , true ) in (compare A) = Less" :value '(:|Bool| . t))
       ("(compare ( true , false )) = Greater" :swe "(compare ( true , false )) = Greater" :value '(:|Bool| . t))
       ("let A = id ( true , false ) in (compare A) = Greater" :swe "let A = id ( true , false ) in (compare A) = Greater" :value '(:|Bool| . t))
       ("(compare ( true , true )) = Equal" :swe "(compare ( true , true )) = Equal" :value '(:|Bool| . t))
       ("let A = id ( true , true ) in (compare A) = Equal" :swe "let A = id ( true , true ) in (compare A) = Equal" :value '(:|Bool| . t))
       ;; Boolean [120]:  op show : Boolean -> String  ;; deprecated
       ("(show ( true )) = \"true\"" :swe "(show ( true )) = \"true\"" :value '(:|Bool| . t))
       ("(show ( false )) = \"false\"" :swe "(show ( false )) = \"false\"" :value '(:|Bool| . t))
       ;; Boolean [129]:  op show : Boolean -> String
       ("(show ( true )) = \"true\"" :swe "(show ( true )) = \"true\"" :value '(:|Bool| . t))
       ("(show ( false )) = \"false\"" :swe "(show ( false )) = \"false\"" :value '(:|Bool| . t))

       ;; Char [ 10]:  op ord : Char -> {n : Nat | n < 256}
       ("(ord ( #A )) = 65" :swe "(ord ( #A )) = 65" :value '(:|Bool| . t))
       ;; Char [ 11]:  op chr : {n : Nat | n < 256} -> Char
       ("(chr ( 65 )) = #A" :swe "(chr ( 65 )) = #A" :value '(:|Bool| . t))
       ;; Char [ 12]:  op isUpperCase : Char -> Boolean
       ("(isUpperCase ( #! )) = false" :swe "(isUpperCase ( #! )) = false" :value '(:|Bool| . t))
       ("(isUpperCase ( #3 )) = false" :swe "(isUpperCase ( #3 )) = false" :value '(:|Bool| . t))
       ("(isUpperCase ( #A )) = true" :swe "(isUpperCase ( #A )) = true" :value '(:|Bool| . t))
       ("(isUpperCase ( #a )) = false" :swe "(isUpperCase ( #a )) = false" :value '(:|Bool| . t))
       ("(isUpperCase ( #\\xdd )) = true" :swe "(isUpperCase ( #\\xdd )) = true" :value '(:|Bool| . t))
       ("(isUpperCase ( #\\xff )) = false" :swe "(isUpperCase ( #\\xff )) = false" :value '(:|Bool| . t))
       ;; Char [ 13]:  op isLowerCase : Char -> Boolean
       ("(isLowerCase ( #! )) = false" :swe "(isLowerCase ( #! )) = false" :value '(:|Bool| . t))
       ("(isLowerCase ( #3 )) = false" :swe "(isLowerCase ( #3 )) = false" :value '(:|Bool| . t))
       ("(isLowerCase ( #A )) = false" :swe "(isLowerCase ( #A )) = false" :value '(:|Bool| . t))
       ("(isLowerCase ( #a )) = true" :swe "(isLowerCase ( #a )) = true" :value '(:|Bool| . t))
       ("(isLowerCase ( #\\xdd )) = false" :swe "(isLowerCase ( #\\xdd )) = false" :value '(:|Bool| . t))
       ("(isLowerCase ( #\\xff )) = true" :swe "(isLowerCase ( #\\xff )) = true" :value '(:|Bool| . t))
       ;; Char [ 14]:  op isAlpha     : Char -> Boolean
       ("(isAlpha ( #! )) = false" :swe "(isAlpha ( #! )) = false" :value '(:|Bool| . t))
       ("(isAlpha ( #3 )) = false" :swe "(isAlpha ( #3 )) = false" :value '(:|Bool| . t))
       ("(isAlpha ( #A )) = true" :swe "(isAlpha ( #A )) = true" :value '(:|Bool| . t))
       ("(isAlpha ( #a )) = true" :swe "(isAlpha ( #a )) = true" :value '(:|Bool| . t))
       ("(isAlpha ( #\\xff )) = true" :swe "(isAlpha ( #\\xff )) = true" :value '(:|Bool| . t))
       ;; Char [ 15]:  op isNum       : Char -> Boolean
       ("(isNum ( #! )) = false" :swe "(isNum ( #! )) = false" :value '(:|Bool| . t))
       ("(isNum ( #3 )) = true" :swe "(isNum ( #3 )) = true" :value '(:|Bool| . t))
       ("(isNum ( #A )) = false" :swe "(isNum ( #A )) = false" :value '(:|Bool| . t))
       ("(isNum ( #a )) = false" :swe "(isNum ( #a )) = false" :value '(:|Bool| . t))
       ("(isNum ( #\\xff )) = false" :swe "(isNum ( #\\xff )) = false" :value '(:|Bool| . t))
       ;; Char [ 16]:  op isAlphaNum  : Char -> Boolean
       ("(isAlphaNum ( #! )) = false" :swe "(isAlphaNum ( #! )) = false" :value '(:|Bool| . t))
       ("(isAlphaNum ( #3 )) = true" :swe "(isAlphaNum ( #3 )) = true" :value '(:|Bool| . t))
       ("(isAlphaNum ( #A )) = true" :swe "(isAlphaNum ( #A )) = true" :value '(:|Bool| . t))
       ("(isAlphaNum ( #a )) = true" :swe "(isAlphaNum ( #a )) = true" :value '(:|Bool| . t))
       ("(isAlphaNum ( #\\xff )) = true" :swe "(isAlphaNum ( #\\xff )) = true" :value '(:|Bool| . t))
       ;; Char [ 17]:  op isAscii     : Char -> Boolean
       ("(isAscii ( #! )) = true" :swe "(isAscii ( #! )) = true" :value '(:|Bool| . t))
       ("(isAscii ( #3 )) = true" :swe "(isAscii ( #3 )) = true" :value '(:|Bool| . t))
       ("(isAscii ( #A )) = true" :swe "(isAscii ( #A )) = true" :value '(:|Bool| . t))
       ("(isAscii ( #a )) = true" :swe "(isAscii ( #a )) = true" :value '(:|Bool| . t))
       ("(isAscii ( #\\xff )) = true" :swe "(isAscii ( #\\xff )) = true" :value '(:|Bool| . t))
       ;; Char [ 18]:  op toUpperCase : Char -> Char
       ("(toUpperCase ( #! )) = #!" :swe "(toUpperCase ( #! )) = #!" :value '(:|Bool| . t))
       ("(toUpperCase ( #3 )) = #3" :swe "(toUpperCase ( #3 )) = #3" :value '(:|Bool| . t))
       ("(toUpperCase ( #A )) = #A" :swe "(toUpperCase ( #A )) = #A" :value '(:|Bool| . t))
       ("(toUpperCase ( #a )) = #A" :swe "(toUpperCase ( #a )) = #A" :value '(:|Bool| . t))
       ("(toUpperCase ( #\\xfc )) = #\\xdc" :swe "(toUpperCase ( #\\xfc )) = #\\xdc" :value '(:|Bool| . t))
       ;; Char [ 19]:  op toLowerCase : Char -> Char
       ("(toLowerCase ( #! )) = #!" :swe "(toLowerCase ( #! )) = #!" :value '(:|Bool| . t))
       ("(toLowerCase ( #3 )) = #3" :swe "(toLowerCase ( #3 )) = #3" :value '(:|Bool| . t))
       ("(toLowerCase ( #A )) = #a" :swe "(toLowerCase ( #A )) = #a" :value '(:|Bool| . t))
       ("(toLowerCase ( #a )) = #a" :swe "(toLowerCase ( #a )) = #a" :value '(:|Bool| . t))
       ("(toLowerCase ( #\\xdc )) = #\\xfc" :swe "(toLowerCase ( #\\xdc )) = #\\xfc" :value '(:|Bool| . t))
       ;; Char [ 20]:  op compare : Char * Char -> Comparison
       ("(compare ( #3 , #4 )) = Less" :swe "(compare ( #3 , #4 )) = Less" :value '(:|Bool| . t))
       ("let A = id ( #3 , #4 ) in (compare A) = Less" :swe "let A = id ( #3 , #4 ) in (compare A) = Less" :value '(:|Bool| . t))
       ("(compare ( #4 , #4 )) = Equal" :swe "(compare ( #4 , #4 )) = Equal" :value '(:|Bool| . t))
       ("let A = id ( #4 , #4 ) in (compare A) = Equal" :swe "let A = id ( #4 , #4 ) in (compare A) = Equal" :value '(:|Bool| . t))
       ("(compare ( #5 , #4 )) = Greater" :swe "(compare ( #5 , #4 )) = Greater" :value '(:|Bool| . t))
       ("let A = id ( #5 , #4 ) in (compare A) = Greater" :swe "let A = id ( #5 , #4 ) in (compare A) = Greater" :value '(:|Bool| . t))
       ;; Char [123]:  op show    : Char -> String     ;; deprecated
       ("(show ( #A )) = \"A\"" :swe "(show ( #A )) = \"A\"" :value '(:|Bool| . t))
       ;; Char [135]:  op show    : Char -> String
       ("(show ( #A )) = \"A\"" :swe "(show ( #A )) = \"A\"" :value '(:|Bool| . t))

       ;; Compare [ 23]:  op compare : Comparison * Comparison -> Comparison
       ("(compare ( Less , Less )) = Equal" :swe "(compare ( Less , Less )) = Equal" :value '(:|Bool| . t))
       ("let A = id ( Less , Less ) in (compare A) = Equal" :swe "let A = id ( Less , Less ) in (compare A) = Equal" :value '(:|Bool| . t))
       ("(compare ( Less , Equal )) = Less" :swe "(compare ( Less , Equal )) = Less" :value '(:|Bool| . t))
       ("let A = id ( Less , Equal ) in (compare A) = Less" :swe "let A = id ( Less , Equal ) in (compare A) = Less" :value '(:|Bool| . t))
       ("(compare ( Less , Greater )) = Less" :swe "(compare ( Less , Greater )) = Less" :value '(:|Bool| . t))
       ("let A = id ( Less , Greater ) in (compare A) = Less" :swe "let A = id ( Less , Greater ) in (compare A) = Less" :value '(:|Bool| . t))
       ("(compare ( Equal , Less )) = Greater" :swe "(compare ( Equal , Less )) = Greater" :value '(:|Bool| . t))
       ("let A = id ( Equal , Less ) in (compare A) = Greater" :swe "let A = id ( Equal , Less ) in (compare A) = Greater" :value '(:|Bool| . t))
       ("(compare ( Equal , Equal )) = Equal" :swe "(compare ( Equal , Equal )) = Equal" :value '(:|Bool| . t))
       ("let A = id ( Equal , Equal ) in (compare A) = Equal" :swe "let A = id ( Equal , Equal ) in (compare A) = Equal" :value '(:|Bool| . t))
       ("(compare ( Equal , Greater )) = Less" :swe "(compare ( Equal , Greater )) = Less" :value '(:|Bool| . t))
       ("let A = id ( Equal , Greater ) in (compare A) = Less" :swe "let A = id ( Equal , Greater ) in (compare A) = Less" :value '(:|Bool| . t))
       ("(compare ( Greater , Less )) = Greater" :swe "(compare ( Greater , Less )) = Greater" :value '(:|Bool| . t))
       ("let A = id ( Greater , Less ) in (compare A) = Greater" :swe "let A = id ( Greater , Less ) in (compare A) = Greater" :value '(:|Bool| . t))
       ("(compare ( Greater , Equal )) = Greater" :swe "(compare ( Greater , Equal )) = Greater" :value '(:|Bool| . t))
       ("let A = id ( Greater , Equal ) in (compare A) = Greater" :swe "let A = id ( Greater , Equal ) in (compare A) = Greater" :value '(:|Bool| . t))
       ("(compare ( Greater , Greater )) = Equal" :swe "(compare ( Greater , Greater )) = Equal" :value '(:|Bool| . t))
       ("let A = id ( Greater , Greater ) in (compare A) = Equal" :swe "let A = id ( Greater , Greater ) in (compare A) = Equal" :value '(:|Bool| . t))
       ;; Compare [130]:  op show : Comparison -> String
       ("(show ( Less )) = \"Less\"" :swe "(show ( Less )) = \"Less\"" :value '(:|Bool| . t))
       ("(show ( Equal )) = \"Equal\"" :swe "(show ( Equal )) = \"Equal\"" :value '(:|Bool| . t))
       ("(show ( Greater )) = \"Greater\"" :swe "(show ( Greater )) = \"Greater\"" :value '(:|Bool| . t))

       ;; Functions [ 25]:  op id          : fa(a) a -> a
       ("(id ( 3 )) = 3" :swe "(id ( 3 )) = 3" :value '(:|Bool| . t))
       ("(id ( #3 )) = #3" :swe "(id ( #3 )) = #3" :value '(:|Bool| . t))
       ;; Functions [ 26]:  op o infixl 24 : fa(a,b,c) (b -> c) * (a -> b) -> (a -> c)
       ("((o(succ,succ))3) = 5" :swe "((o(succ,succ))3) = 5" :value '(:|Bool| . t))
       ("(let(ss)=(succ,succ)in(o(ss))3) = 5" :swe "(let(ss)=(succ,succ)in(o(ss))3) = 5" :value '(:|Bool| . t))
       ;; Functions [ 27]:  op injective?  : fa(a,b) (a -> b) -> Boolean
       ;; Functions [ 28]:  op surjective? : fa(a,b) (a -> b) -> Boolean
       ;; Functions [ 29]:  op bijective?  : fa(a,b) (a -> b) -> Boolean
       ;; Functions [ 30]:  op inverse     : fa(a,b) Bijective(a,b) -> Bijective(b,a)

       ;; Integer [ 31]:  op ~             : Integer -> Integer
       ("(- ( 3 )) = 0-3" :swe "(- ( 3 )) = 0-3" :value '(:|Bool| . t))
       ;; Integer [ 32]:  op +   infixl 25 : Integer * Integer -> Integer
       ("(+ ( 3 , 4 )) = 7" :swe "(+ ( 3 , 4 )) = 7" :value '(:|Bool| . t))
       ("let A = id ( 3 , 4 ) in (+ A) = 7" :swe "let A = id ( 3 , 4 ) in (+ A) = 7" :value '(:|Bool| . t))
       ;; Integer [ 33]:  op -   infixl 25 : Integer * Integer -> Integer
       ("(- ( 7 , 4 )) = 3" :swe "(- ( 7 , 4 )) = 3" :value '(:|Bool| . t))
       ("let A = id ( 7 , 4 ) in (- A) = 3" :swe "let A = id ( 7 , 4 ) in (- A) = 3" :value '(:|Bool| . t))
       ;; Integer [ 34]:  op *   infixl 27 : Integer * Integer -> Integer
       ("( * ( 3, 4 )) = 12" :swe "( * ( 3, 4 )) = 12" :value '(:|Bool| . t))
       ("let A = id ( 3, 4 ) in ( * A) = 12" :swe "let A = id ( 3, 4 ) in ( * A) = 12" :value '(:|Bool| . t))
       ;; Integer [ 35]:  op div infixl 26 : Integer * NZInteger -> Integer
       ("(div ( 27 , 10 )) = 2" :swe "(div ( 27 , 10 )) = 2" :value '(:|Bool| . t))
       ("let A = id ( 27 , 10 ) in (div A) = 2" :swe "let A = id ( 27 , 10 ) in (div A) = 2" :value '(:|Bool| . t))
       ;; Integer [ 36]:  op mod infixl 26 : Integer * NZInteger -> Integer
       ("(mod ( 27 , 10 )) = 7" :swe "(mod ( 27 , 10 )) = 7" :value '(:|Bool| . t))
       ("let A = id ( 27 , 10 ) in (mod A) = 7" :swe "let A = id ( 27 , 10 ) in (mod A) = 7" :value '(:|Bool| . t))
       ;; Integer [ 37]:  op <   infixl 20 : Integer * Integer -> Boolean
       ("(< ( 3 , 4 )) = true" :swe "(< ( 3 , 4 )) = true" :value '(:|Bool| . t))
       ("let A = id ( 3 , 4 ) in (< A) = true" :swe "let A = id ( 3 , 4 ) in (< A) = true" :value '(:|Bool| . t))
       ("(< ( 4 , 4 )) = false" :swe "(< ( 4 , 4 )) = false" :value '(:|Bool| . t))
       ("let A = id ( 4 , 4 ) in (< A) = false" :swe "let A = id ( 4 , 4 ) in (< A) = false" :value '(:|Bool| . t))
       ;; Integer [ 38]:  op <=  infixl 20 : Integer * Integer -> Boolean
       ("(<= ( 3 , 3 )) = true" :swe "(<= ( 3 , 3 )) = true" :value '(:|Bool| . t))
       ("let A = id ( 3 , 3 ) in (<= A) = true" :swe "let A = id ( 3 , 3 ) in (<= A) = true" :value '(:|Bool| . t))
       ("(<= ( 4 , 3 )) = false" :swe "(<= ( 4 , 3 )) = false" :value '(:|Bool| . t))
       ("let A = id ( 4 , 3 ) in (<= A) = false" :swe "let A = id ( 4 , 3 ) in (<= A) = false" :value '(:|Bool| . t))
       ;; Integer [ 39]:  op >  infixl 20 : Integer * Integer -> Boolean
       ("(> ( 4 , 3 )) = true" :swe "(> ( 4 , 3 )) = true" :value '(:|Bool| . t))
       ("let A = id ( 4 , 3 ) in (> A) = true" :swe "let A = id ( 4 , 3 ) in (> A) = true" :value '(:|Bool| . t))
       ("(> ( 4 , 4 )) = false" :swe "(> ( 4 , 4 )) = false" :value '(:|Bool| . t))
       ("let A = id ( 4 , 4 ) in (> A) = false" :swe "let A = id ( 4 , 4 ) in (> A) = false" :value '(:|Bool| . t))
       ;; Integer [ 40]:  op >= infixl 20 : Integer * Integer -> Boolean
       ("(>= ( 3 , 3 )) = true" :swe "(>= ( 3 , 3 )) = true" :value '(:|Bool| . t))
       ("let A = id ( 3 , 3 ) in (>= A) = true" :swe "let A = id ( 3 , 3 ) in (>= A) = true" :value '(:|Bool| . t))
       ("(>= ( 3 , 4 )) = false" :swe "(>= ( 3 , 4 )) = false" :value '(:|Bool| . t))
       ("let A = id ( 3 , 4 ) in (>= A) = false" :swe "let A = id ( 3 , 4 ) in (>= A) = false" :value '(:|Bool| . t))
       ;; Integer [ 41]:  op abs          : Integer -> Integer
       ("(abs ( - 3 )) = 3" :swe "(abs ( - 3 )) = 3" :value '(:|Bool| . t))
       ("(abs ( 3 )) = 3" :swe "(abs ( 3 )) = 3" :value '(:|Bool| . t))
       ;; Integer [ 42]:  op min          : Integer * Integer -> Integer
       ("(min ( 3 , 4 )) = 3" :swe "(min ( 3 , 4 )) = 3" :value '(:|Bool| . t))
       ("let A = id ( 3 , 4 ) in (min A) = 3" :swe "let A = id ( 3 , 4 ) in (min A) = 3" :value '(:|Bool| . t))
       ;; Integer [ 43]:  op max          : Integer * Integer -> Integer
       ("(max ( 3 , 4 )) = 4" :swe "(max ( 3 , 4 )) = 4" :value '(:|Bool| . t))
       ("let A = id ( 3 , 4 ) in (max A) = 4" :swe "let A = id ( 3 , 4 ) in (max A) = 4" :value '(:|Bool| . t))
       ;; Integer [ 44]:  op compare      : Integer * Integer -> Comparison
       ("(compare ( 3 , 4 )) = Less" :swe "(compare ( 3 , 4 )) = Less" :value '(:|Bool| . t))
       ("let A = id ( 3 , 4 ) in (compare A) = Less" :swe "let A = id ( 3 , 4 ) in (compare A) = Less" :value '(:|Bool| . t))
       ("(compare ( 4 , 4 )) = Equal" :swe "(compare ( 4 , 4 )) = Equal" :value '(:|Bool| . t))
       ("let A = id ( 4 , 4 ) in (compare A) = Equal" :swe "let A = id ( 4 , 4 ) in (compare A) = Equal" :value '(:|Bool| . t))
       ("(compare ( 5 , 4 )) = Greater" :swe "(compare ( 5 , 4 )) = Greater" :value '(:|Bool| . t))
       ("let A = id ( 5 , 4 ) in (compare A) = Greater" :swe "let A = id ( 5 , 4 ) in (compare A) = Greater" :value '(:|Bool| . t))
       ;; Integer [121]:  op show : Integer -> String  ;; deprecated
       ("(show ( 123 )) = \"123\"" :swe "(show ( 123 )) = \"123\"" :value '(:|Bool| . t))
       ;; Integer [132]:  op show : Integer -> String
       ("(Integer.show ( 123 )) = \"123\"" :swe "(Integer.show ( 123 )) = \"123\"" :value '(:|Bool| . t))
       ;; Integer [124]:  op intToString    : Integer -> String
       ("(intToString ( 123 )) = \"123\"" :swe "(intToString ( 123 )) = \"123\"" :value '(:|Bool| . t))
       ;; Integer [124.5]:  op intConvertible : String -> Boolean
       ("(intConvertible ( \"123\" )) = true" :swe "(intConvertible ( \"123\" )) = true" :value '(:|Bool| . t))
       ("(intConvertible ( \"-123\" )) = true" :swe "(intConvertible ( \"-123\" )) = true" :value '(:|Bool| . t))
       ("(intConvertible ( \"000\" )) = true" :swe "(intConvertible ( \"000\" )) = true" :value '(:|Bool| . t))
       ("(intConvertible ( \"\" )) = false" :swe "(intConvertible ( \"\" )) = false" :value '(:|Bool| . t))
       ("(intConvertible ( \"123.00\" )) = false" :swe "(intConvertible ( \"123.00\" )) = false" :value '(:|Bool| . t))
       ;; Integer [125]:  op stringToInt    : (String | intConvertible) -> Integer
       ("(stringToInt ( \"123\" )) = 123" :swe "(stringToInt ( \"123\" )) = 123" :value '(:|Bool| . t))
       ("(stringToInt ( \"-123\" )) = - 123" :swe "(stringToInt ( \"-123\" )) = - 123" :value '(:|Bool| . t))
       ;; List [ 49]:  op empty             : fa(a)   List a

       ("(empty) = []" :swe "(empty) = []" :value '(:|Bool| . t))
       ;; List [ 50]:  op Cons            : fa(a)   a * List a -> List a
       ("(Cons ( 3 , [4] )) = [3,4]" :swe "(Cons ( 3 , [4] )) = [3,4]" :value '(:|Bool| . t))
       ("let A = id ( 3 , [4] ) in (Cons A) = [3,4]" :swe "let A = id ( 3 , [4] ) in (Cons A) = [3,4]" :value '(:|Bool| . t))
       ;; List [ 51]:  op |>          : fa(a)   a * List a -> List a
       ("( 3 |> [4] ) = [3,4]" :swe "( 3 |> [4] ) = [3,4]" :value '(:|Bool| . t))
       ("let A = id ( 3 , [4] ) in (|> A) = [3,4]" :swe "let A = id ( 3 , [4] ) in (|> A) = [3,4]" :value '(:|Bool| . t))
       ;; List [ 52]:  op length          : fa(a)   List a -> Nat
       ("(length ( [3,4] )) = 2" :swe "(length ( [3,4] )) = 2" :value '(:|Bool| . t))
       ;; List [ 53]:  op empty?            : fa(a)   List a -> Boolean
       ("(empty? ( empty )) = true" :swe "(empty? ( empty )) = true" :value '(:|Bool| . t))
       ("(empty? ( [3] )) = false" :swe "(empty? ( [3] )) = false" :value '(:|Bool| . t))
       ;; List [ 54]:  op head              : fa(a)   {l : List a | ~(empty? l)} -> a
       ("(head ( [3,4] )) = 3" :swe "(head ( [3,4] )) = 3" :value '(:|Bool| . t))
       ;; List [ 55]:  op tail              : fa(a)   {l : List a | ~(empty? l)} -> List a
       ("(tail ( [3,4] )) = [4]" :swe "(tail ( [3,4] )) = [4]" :value '(:|Bool| . t))
       ;; List [ 56]:  op ++          : fa(a)   List a * List a -> List a
       ("(++ ( [3] , [4] )) = [3,4]" :swe "(++ ( [3] , [4] )) = [3,4]" :value '(:|Bool| . t))
       ("let A = id ( [3] , [4] ) in (++ A) = [3,4]" :swe "let A = id ( [3] , [4] ) in (++ A) = [3,4]" :value '(:|Bool| . t))
       ;; List [ 57]:  op ++ infixl 11    : fa(a)   List a * List a -> List a
       ("(++ ( [3] , [4] )) = [3,4]" :swe "(++ ( [3] , [4] )) = [3,4]" :value '(:|Bool| . t))
       ("let A = id ( [3] , [4] ) in (++ A) = [3,4]" :swe "let A = id ( [3] , [4] ) in (++ A) = [3,4]" :value '(:|Bool| . t))
;; @ for ++ is obsolete
;;       ;; List [ 58]:  op @  infixl 11    : fa(a)   List a * List a -> List a
;;       ("(@ ( [3] , [4] )) = [3,4]" :swe "(@ ( [3] , [4] )) = [3,4]" :value '(:|Bool| . t))
;;       ("let A = id ( [3] , [4] ) in (@ A) = [3,4]" :swe "let A = id ( [3] , [4] ) in (@ A) = [3,4]" :value '(:|Bool| . t))
       ;; List [ 59]:  op @             : fa(a)   {(l,i) : List a * Nat | i < length l} -> a
       ("( [3,4,5] @ 1 ) = 4" :swe "( [3,4,5] @ 1 ) = 4" :value '(:|Bool| . t))
       ("let A = id ( [3,4,5] , 1 ) in (@ A) = 4" :swe "let A = id ( [3,4,5] , 1 ) in (@ A) = 4" :value '(:|Bool| . t))
       ;; List [ 60]:  op removePrefix         : fa(a)   {(l,i) : List a * Nat | i < length l} -> List a
       ("(removePrefix ( [3,4,5] , 2 )) = [5]" :swe "(removePrefix ( [3,4,5] , 2 )) = [5]" :value '(:|Bool| . t))
       ("let A = id ( [3,4,5] , 2 ) in (removePrefix A) = [5]" :swe "let A = id ( [3,4,5] , 2 ) in (removePrefix A) = [5]" :value '(:|Bool| . t))
       ;; List [ 61]:  op in?          : fa(a)   a * List a -> Boolean
       ("( 4 in? [3,5,7] ) = false" :swe "( 4 in? [3,5,7] ) = false" :value '(:|Bool| . t))
       ("let A = id ( 4 , [3,5,7] ) in (in? A) = false" :swe "let A = id ( 4 , [3,5,7] ) in (in? A) = false" :value '(:|Bool| . t))
       ("(in? ( 5 , [3,5,7] )) = true" :swe "(in? ( 5 , [3,5,7] )) = true" :value '(:|Bool| . t))
       ("let A = id ( 5 , [3,5,7] ) in (in? A) = true" :swe "let A = id ( 5 , [3,5,7] ) in (in? A) = true" :value '(:|Bool| . t))
       ;; List [ 62]:  op subFromTo         : fa(a)   {(l,i,j) : List a * Nat * Nat | i < j && j <= length l} -> List a
       ("(subFromTo ( [3,1,4,1,5,9] , 2 , 4 )) = [4,1]" :swe "(subFromTo ( [3,1,4,1,5,9] , 2 , 4 )) = [4,1]" :value '(:|Bool| . t))
       ("let A = id ( [3,1,4,1,5,9] , 2 , 4 ) in (subFromTo A) = [4,1]" :swe "let A = id ( [3,1,4,1,5,9] , 2 , 4 ) in (subFromTo A) = [4,1]" :value '(:|Bool| . t))
       ;; List [ 63]:  op map             : fa(a,b) (a -> b) -> List a -> List b
       ("(map ( succ ) ( [3,4,5] )) = [4,5,6]" :swe "(map ( succ ) ( [3,4,5] )) = [4,5,6]" :value '(:|Bool| . t))
       ("let F = map ( succ ) in (F ( [3,4,5] )) = [4,5,6]" :swe "let F = map ( succ ) in (F ( [3,4,5] )) = [4,5,6]" :value '(:|Bool| . t))
       ;; List [ 64]:  op mapPartial      : fa(a,b) (a -> Option b) -> List a -> List b
       ("(mapPartial ( fn(n)->if(n<1)then(None)else(Some(pred(n))) ) ( [5,0,2] )) = [4,1]" :swe "(mapPartial ( fn(n)->if(n<1)then(None)else(Some(pred(n))) ) ( [5,0,2] )) = [4,1]" :value '(:|Bool| . t))
       ("let F = mapPartial ( fn(n)->if(n<1)then(None)else(Some(pred(n))) ) in (F ( [5,0,2] )) = [4,1]" :swe "let F = mapPartial ( fn(n)->if(n<1)then(None)else(Some(pred(n))) ) in (F ( [5,0,2] )) = [4,1]" :value '(:|Bool| . t))
       ;; List [ 65]:  op foldl           : fa(a,b) (a * b -> b) -> b -> List a -> b
       ("(foldl ( fn(n,m)->(m)mod(n) ) ( 20 ) ( [77,47] )) = 13" :swe "(foldl ( fn(n,m)->(m)mod(n) ) ( 20 ) ( [77,47] )) = 13" :value '(:|Bool| . t))
       ("let F = foldl ( fn(n,m)->(m)mod(n) ) in (F ( 20 ) ( [77,47] )) = 13" :swe "let F = foldl ( fn(n,m)->(m)mod(n) ) in (F ( 20 ) ( [77,47] )) = 13" :value '(:|Bool| . t))
       ;; List [ 66]:  op foldr           : fa(a,b) (a * b -> b) -> b -> List a -> b
       ("(foldr ( fn(m,n)->(m)mod(n) ) ( 77 ) ( [27,91] )) = 13" :swe "(foldr ( fn(m,n)->(m)mod(n) ) ( 77 ) ( [27,91] )) = 13" :value '(:|Bool| . t))
       ("let F = foldr ( fn(m,n)->(m)mod(n) ) in (F ( 77 ) ( [27,91] )) = 13" :swe "let F = foldr ( fn(m,n)->(m)mod(n) ) in (F ( 77 ) ( [27,91] )) = 13" :value '(:|Bool| . t))
       ;; List [ 67]:  op exists?          : fa(a)   (a -> Boolean) -> List a -> Boolean
       ("(exists? ( posNat? ) ( [] )) = false" :swe "(exists? ( posNat? ) ( [] )) = false" :value '(:|Bool| . t))
       ("let F = exists? ( posNat? ) in (F ( [] )) = false" :swe "let F = exists? ( posNat? ) in (F ( [] )) = false" :value '(:|Bool| . t))
       ("(exists? ( posNat? ) ( [0,0,0] )) = false" :swe "(exists? ( posNat? ) ( [0,0,0] )) = false" :value '(:|Bool| . t))
       ("let F = exists? ( posNat? ) in (F ( [0,0,0] )) = false" :swe "let F = exists? ( posNat? ) in (F ( [0,0,0] )) = false" :value '(:|Bool| . t))
       ("(exists? ( posNat? ) ( [0,1,0] )) = true" :swe "(exists? ( posNat? ) ( [0,1,0] )) = true" :value '(:|Bool| . t))
       ("let F = exists? ( posNat? ) in (F ( [0,1,0] )) = true" :swe "let F = exists? ( posNat? ) in (F ( [0,1,0] )) = true" :value '(:|Bool| . t))
       ;; List [ 68]:  op forall?            : fa(a)   (a -> Boolean) -> List a -> Boolean
       ("(forall?( posNat? ) ( [] )) = true" :swe "(forall?( posNat? ) ( [] )) = true" :value '(:|Bool| . t))
       ("let F = forall?( posNat? ) in (F ( [] )) = true" :swe "let F = forall?( posNat? ) in (F ( [] )) = true" :value '(:|Bool| . t))
       ("(forall?( posNat? ) ( [1,1,1] )) = true" :swe "(forall?( posNat? ) ( [1,1,1] )) = true" :value '(:|Bool| . t))
       ("let F = forall?( posNat? ) in (F ( [1,1,1] )) = true" :swe "let F = forall?( posNat? ) in (F ( [1,1,1] )) = true" :value '(:|Bool| . t))
       ("(forall?( posNat? ) ( [1,0,1] )) = false" :swe "(forall?( posNat? ) ( [1,0,1] )) = false" :value '(:|Bool| . t))
       ("let F = forall?( posNat? ) in (F ( [1,0,1] )) = false" :swe "let F = forall?( posNat? ) in (F ( [1,0,1] )) = false" :value '(:|Bool| . t))
       ;; List [ 69]:  op filter          : fa(a)   (a -> Boolean) -> List a -> List a
       ("(filter ( posNat? ) ( [5,0,2] )) = [5,2]" :swe "(filter ( posNat? ) ( [5,0,2] )) = [5,2]" :value '(:|Bool| . t))
       ("let F = filter ( posNat? ) in (F ( [5,0,2] )) = [5,2]" :swe "let F = filter ( posNat? ) in (F ( [5,0,2] )) = [5,2]" :value '(:|Bool| . t))
       ;; List [ 70]:  op diff            : fa(a)   List a * List a -> List a
       ("(diff ( [3,1,4,1,5,9] , [5,9,2,1] )) = [3,4]" :swe "(diff ( [3,1,4,1,5,9] , [5,9,2,1] )) = [3,4]" :value '(:|Bool| . t))
       ("let A = id ( [3,1,4,1,5,9] , [5,9,2,1] ) in (diff A) = [3,4]" :swe "let A = id ( [3,1,4,1,5,9] , [5,9,2,1] ) in (diff A) = [3,4]" :value '(:|Bool| . t))
       ;; List [ 71]:  op reverse             : fa(a)   List a -> List a
       ("(reverse ( [1,2,3] )) = [3,2,1]" :swe "(reverse ( [1,2,3] )) = [3,2,1]" :value '(:|Bool| . t))
;; No longer in Base
       ;; List [ 72]:  op rev2            : fa(a)   List a * List a -> List a
;       ("(rev2 ( [1,2,3] , [4,5,6] )) = [3,2,1,4,5,6]" :swe "(rev2 ( [1,2,3] , [4,5,6] )) = [3,2,1,4,5,6]" :value '(:|Bool| . t))
;       ("let A = id ( [1,2,3] , [4,5,6] ) in (rev2 A) = [3,2,1,4,5,6]" :swe "let A = id ( [1,2,3] , [4,5,6] ) in (rev2 A) = [3,2,1,4,5,6]" :value '(:|Bool| . t))
       ;; List [ 73]:  op flatten         : fa(a)   List(List a) -> List a
       ("(flatten ( [[3,1],[4,1],[5,9]] )) = [3,1,4,1,5,9]" :swe "(flatten ( [[3,1],[4,1],[5,9]] )) = [3,1,4,1,5,9]" :value '(:|Bool| . t))
       ;; List [ 74]:  op findLeftmost            : fa(a)   (a -> Boolean) -> List a -> Option(a)
       ("(findLeftmost ( posNat? ) ( [0,0,0] )) = None" :swe "(findLeftmost ( posNat? ) ( [0,0,0] )) = None" :value '(:|Bool| . t))
       ("let F = findLeftmost ( posNat? ) in (F ( [0,0,0] )) = None" :swe "let F = findLeftmost ( posNat? ) in (F ( [0,0,0] )) = None" :value '(:|Bool| . t))
       ("(findLeftmost ( posNat? ) ( [0,1,0] )) = Some(1)" :swe "(findLeftmost ( posNat? ) ( [0,1,0] )) = Some(1)" :value '(:|Bool| . t))
       ("let F = findLeftmost ( posNat? ) in (F ( [0,1,0] )) = Some(1)" :swe "let F = findLeftmost ( posNat? ) in (F ( [0,1,0] )) = Some(1)" :value '(:|Bool| . t))
       ;; List [ 75]:  op tabulate        : fa(a)   Nat * (Nat -> a) -> List a
       ("(tabulate ( 3 , succ )) = [1,2,3]" :swe "(tabulate ( 3 , succ )) = [1,2,3]" :value '(:|Bool| . t))
       ("let A = id ( 3 , succ ) in (tabulate A) = [1,2,3]" :swe "let A = id ( 3 , succ ) in (tabulate A) = [1,2,3]" :value '(:|Bool| . t))
       ;; List [ 76]:  op findLeftmostAndPreceding       : fa(a)   (a -> Boolean) -> List a -> Option (a * List a)
       ("(findLeftmostAndPreceding ( empty? ) ( [[1],[2,3],[],[4]] )) = Some([],[[1],[2,3]])" :swe "(findLeftmostAndPreceding ( empty ) ( [[1],[2,3],[],[4]] )) = Some([],[[1],[2,3]])" :value '(:|Bool| . t))
       ("let F = findLeftmostAndPreceding ( empty? ) in (F ( [[1],[2,3],[],[4]] )) = Some([],[[1],[2,3]])" :swe "let F = findLeftmostAndPreceding ( empty ) in (F ( [[1],[2,3],[],[4]] )) = Some([],[[1],[2,3]])" :value '(:|Bool| . t))
       ("(findLeftmostAndPreceding ( empty? ) ( [[1],[2,3],[4]] )) = None" :swe "(findLeftmostAndPreceding ( empty? ) ( [[1],[2,3],[4]] )) = None" :value '(:|Bool| . t))
       ("let F = findLeftmostAndPreceding ( empty? ) in (F ( [[1],[2,3],[4]] )) = None" :swe "let F = findLeftmostAndPreceding ( empty? ) in (F ( [[1],[2,3],[4]] )) = None" :value '(:|Bool| . t))
       ;; List [ 78]:  op splitAtLeftmost       : fa(a)  (a -> Boolean) -> List a -> Option(List a * a * List a)
       ("(splitAtLeftmost ( empty? ) ( [[1],[2,3],[],[4]] )) = Some([[1],[2,3]],[],[[4]])" :swe "(splitAtLeftmost ( empty? ) ( [[1],[2,3],[],[4]] )) = Some([[1],[2,3]],[],[[4]])" :value '(:|Bool| . t))
       ("let F = splitAtLeftmost ( empty? ) in (F ( [[1],[2,3],[],[4]] )) = Some([[1],[2,3]],[],[[4]])" :swe "let F = splitAtLeftmost ( empty? ) in (F ( [[1],[2,3],[],[4]] )) = Some([[1],[2,3]],[],[[4]])" :value '(:|Bool| . t))
       ("(splitAtLeftmost ( empty? ) ( [[1],[2,3],[4]] )) = None" :swe "(splitAtLeftmost ( empty? ) ( [[1],[2,3],[4]] )) = None" :value '(:|Bool| . t))
       ("let F = splitAtLeftmost ( empty? ) in (F ( [[1],[2,3],[4]] )) = None" :swe "let F = splitAtLeftmost ( empty? ) in (F ( [[1],[2,3],[4]] )) = None" :value '(:|Bool| . t))
       ;; List [ 80]:  op leftmostPositionOfSublistAndFollowing      : fa(a)  List a * List a -> Option(Nat * List a)
       ("(leftmostPositionOfSublistAndFollowing ( [] , [3,1,4,1,5] )) = Some(0,[3,1,4,1,5])" :swe "(leftmostPositionOfSublistAndFollowing ( [] , [3,1,4,1,5] )) = Some(0,[3,1,4,1,5])" :value '(:|Bool| . t))
       ("let A = id ( [] , [3,1,4,1,5] ) in (leftmostPositionOfSublistAndFollowing A) = Some(0,[3,1,4,1,5])" :swe "let A = id ( [] , [3,1,4,1,5] ) in (leftmostPositionOfSublistAndFollowing A) = Some(0,[3,1,4,1,5])" :value '(:|Bool| . t))
       ("(leftmostPositionOfSublistAndFollowing ( [1,4] , [3,1,4,1,5] )) = Some(1,[1,5])" :swe "(leftmostPositionOfSublistAndFollowing ( [1,4] , [3,1,4,1,5] )) = Some(1,[1,5])" :value '(:|Bool| . t))
       ("let A = id ( [1,4] , [3,1,4,1,5] ) in (leftmostPositionOfSublistAndFollowing A) = Some(1,[1,5])" :swe "let A = id ( [1,4] , [3,1,4,1,5] ) in (leftmostPositionOfSublistAndFollowing A) = Some(1,[1,5])" :value '(:|Bool| . t))
       ("(leftmostPositionOfSublistAndFollowing ( [1,3] , [3,1,4,1,5] )) = None" :swe "(leftmostPositionOfSublistAndFollowing ( [1,3] , [3,1,4,1,5] )) = None" :value '(:|Bool| . t))
       ("let A = id ( [1,3] , [3,1,4,1,5] ) in (leftmostPositionOfSublistAndFollowing A) = None" :swe "let A = id ( [1,3] , [3,1,4,1,5] ) in (leftmostPositionOfSublistAndFollowing A) = None" :value '(:|Bool| . t))
       ;; List [ 81]:  op compare         : fa(a)  (a * a -> Comparison) -> List a * List a -> Comparison
       ("(compare ( Integer.compare ) ( [] , [1] )) = Less" :swe "(compare ( Integer.compare ) ( [] , [1] )) = Less" :value '(:|Bool| . t))
       ("let F = compare ( Integer.compare ) in (F ( [] , [1] )) = Less" :swe "let F = compare ( Integer.compare ) in (F ( [] , [1] )) = Less" :value '(:|Bool| . t))
       ("(compare ( Integer.compare ) ( [0,9] , [1] )) = Less" :swe "(compare ( Integer.compare ) ( [0,9] , [1] )) = Less" :value '(:|Bool| . t))
       ("let F = compare ( Integer.compare ) in (F ( [0,9] , [1] )) = Less" :swe "let F = compare ( Integer.compare ) in (F ( [0,9] , [1] )) = Less" :value '(:|Bool| . t))
       ("(compare ( Integer.compare ) ( [1] , [1] )) = Equal" :swe "(compare ( Integer.compare ) ( [1] , [1] )) = Equal" :value '(:|Bool| . t))
       ("let F = compare ( Integer.compare ) in (F ( [1] , [1] )) = Equal" :swe "let F = compare ( Integer.compare ) in (F ( [1] , [1] )) = Equal" :value '(:|Bool| . t))
       ("(compare ( Integer.compare ) ( [1,0] , [1] )) = Greater" :swe "(compare ( Integer.compare ) ( [1,0] , [1] )) = Greater" :value '(:|Bool| . t))
       ("let F = compare ( Integer.compare ) in (F ( [1,0] , [1] )) = Greater" :swe "let F = compare ( Integer.compare ) in (F ( [1,0] , [1] )) = Greater" :value '(:|Bool| . t))
       ;; List [ 82]:  op app             : fa(a)  (a -> ()) -> List a -> ()  ;; deprecated
       ;; List [134]:  op show    : String -> List String -> String
       ("(show ( \"ns\" ) ( [\"no\",\"e\",\"e\"] )) = \"nonsense\"" :swe "(show ( \"ns\" ) ( [\"no\",\"e\",\"e\"] )) = \"nonsense\"" :value '(:|Bool| . t))
       ("let F = show ( \"ns\" ) in (F ( [\"no\",\"e\",\"e\"] )) = \"nonsense\"" :swe "let F = show ( \"ns\" ) in (F ( [\"no\",\"e\",\"e\"] )) = \"nonsense\"" :value '(:|Bool| . t))

       ;; Nat [ 84]:  op succ    : Nat -> Nat
       ("(succ ( 6 )) = 7" :swe "(succ ( 6 )) = 7" :value '(:|Bool| . t))
       ;; Nat [ 85]:  op pred    : Nat -> Integer
       ("(pred ( 7 )) = 6" :swe "(pred ( 7 )) = 6" :value '(:|Bool| . t))
       ;; Nat [ 86]:  op zero    : Nat 
       ("(zero) = 0" :swe "(zero) = 0" :value '(:|Bool| . t))
       ;; Nat [ 87]:  op one     : Nat
       ("(one) = 1" :swe "(one) = 1" :value '(:|Bool| . t))
       ;; ;; Nat [ 88]:  op two     : Nat
       ;; ("(two) = 2" :swe "(two) = 2" :value '(:|Bool| . t))
       ;; Nat [ 89]:  op posNat? : Nat -> Boolean
       ("(posNat? ( 0 )) = false" :swe "(posNat? ( 0 )) = false" :value '(:|Bool| . t))
       ("(posNat? ( 1 )) = true" :swe "(posNat? ( 1 )) = true" :value '(:|Bool| . t))
       ;; Nat [122]:  op show     : Nat -> String      ;; deprecated
       ("(show ( 123 )) = \"123\"" :swe "(show ( 123 )) = \"123\"" :value '(:|Bool| . t))
       ;; Nat [133]:  op show     : Nat -> String
       ("(Nat.show ( 123 )) = \"123\"" :swe "(Nat.show ( 123 )) = \"123\"" :value '(:|Bool| . t))
       ;; Nat [126]:  op natToString  : Nat -> String
       ("(natToString ( 123 )) = \"123\"" :swe "(natToString ( 123 )) = \"123\"" :value '(:|Bool| . t))
       ;; Nat [127]:  op stringToNat  : {s : String | length s > 0 && forall?isNum (explode s)} -> Nat

       ;; some and none are obsolete
       ;; Option [ 94]:  op some      : fa(a) a -> Option a
       ;("(some ( 1 )) = Some(1)" :swe "(some ( 1 )) = Some(1)" :value '(:|Bool| . t))
       ;; Option [ 95]:  op none      : fa(a) Option a
       ;("(none) = None" :swe "(none) = None" :value '(:|Bool| . t))
       ;; Option [ 96]:  op some?     : fa(a) Option a -> Boolean
       ("(some? ( None )) = false" :swe "(some? ( None )) = false" :value '(:|Bool| . t))
       ("(some? ( Some(1) )) = true" :swe "(some? ( Some(1) )) = true" :value '(:|Bool| . t))
       ;; Option [ 97]:  op none?     : fa(a) Option a -> Boolean
       ("(none? ( None )) = true" :swe "(none? ( None )) = true" :value '(:|Bool| . t))
       ("(none? ( Some(1) )) = false" :swe "(none? ( Some(1) )) = false" :value '(:|Bool| . t))
       ;; Option [ 98]:  op compare   : fa(a) (a * a -> Comparison) -> Option a * Option a -> Comparison
       ("(compare ( Integer.compare ) ( None , None )) = Equal" :swe "(compare ( Integer.compare ) ( None , None )) = Equal" :value '(:|Bool| . t))
       ("let F = compare ( Integer.compare ) in (F ( None , None )) = Equal" :swe "let F = compare ( Integer.compare ) in (F ( None , None )) = Equal" :value '(:|Bool| . t))
       ("(compare ( Integer.compare ) ( None , Some(1) )) = Less" :swe "(compare ( Integer.compare ) ( None , Some(1) )) = Less" :value '(:|Bool| . t))
       ("let F = compare ( Integer.compare ) in (F ( None , Some(1) )) = Less" :swe "let F = compare ( Integer.compare ) in (F ( None , Some(1) )) = Less" :value '(:|Bool| . t))
       ("(compare ( Integer.compare ) ( Some(1) , None )) = Greater" :swe "(compare ( Integer.compare ) ( Some(1) , None )) = Greater" :value '(:|Bool| . t))
       ("let F = compare ( Integer.compare ) in (F ( Some(1) , None )) = Greater" :swe "let F = compare ( Integer.compare ) in (F ( Some(1) , None )) = Greater" :value '(:|Bool| . t))
       ("(compare ( Integer.compare ) ( Some(0) , Some(1) )) = Less" :swe "(compare ( Integer.compare ) ( Some(0) , Some(1) )) = Less" :value '(:|Bool| . t))
       ("let F = compare ( Integer.compare ) in (F ( Some(0) , Some(1) )) = Less" :swe "let F = compare ( Integer.compare ) in (F ( Some(0) , Some(1) )) = Less" :value '(:|Bool| . t))
       ("(compare ( Integer.compare ) ( Some(1) , Some(1) )) = Equal" :swe "(compare ( Integer.compare ) ( Some(1) , Some(1) )) = Equal" :value '(:|Bool| . t))
       ("let F = compare ( Integer.compare ) in (F ( Some(1) , Some(1) )) = Equal" :swe "let F = compare ( Integer.compare ) in (F ( Some(1) , Some(1) )) = Equal" :value '(:|Bool| . t))
       ("(compare ( Integer.compare ) ( Some(2) , Some(1) )) = Greater" :swe "(compare ( Integer.compare ) ( Some(2) , Some(1) )) = Greater" :value '(:|Bool| . t))
       ("let F = compare ( Integer.compare ) in (F ( Some(2) , Some(1) )) = Greater" :swe "let F = compare ( Integer.compare ) in (F ( Some(2) , Some(1) )) = Greater" :value '(:|Bool| . t))
       ;; Option [ 99]:  op mapOption : fa(a,b) (a -> b) -> Option a -> Option b
       ("(mapOption ( succ ) ( None )) = None" :swe "(mapOption ( succ ) ( None )) = None" :value '(:|Bool| . t))
       ("let F = mapOption ( succ ) in (F ( None )) = None" :swe "let F = mapOption ( succ ) in (F ( None )) = None" :value '(:|Bool| . t))
       ("(mapOption ( succ ) ( Some(0) )) = Some(1)" :swe "(mapOption ( succ ) ( Some(0) )) = Some(1)" :value '(:|Bool| . t))
       ("let F = mapOption ( succ ) in (F ( Some(0) )) = Some(1)" :swe "let F = mapOption ( succ ) in (F ( Some(0) )) = Some(1)" :value '(:|Bool| . t))
       ;; Option [131]:  op show  : fa(a) (a -> String) -> Option a -> String
       ("(show ( natToString ) ( None )) = \"None\"" :swe "(show ( natToString ) ( None )) = \"None\"" :value '(:|Bool| . t))
       ("let F = show ( natToString ) in (F ( None )) = \"None\"" :swe "let F = show ( natToString ) in (F ( None )) = \"None\"" :value '(:|Bool| . t))
       ("(show ( natToString ) ( Some(1) )) = \"(Some\\s1)\"" :swe "(show ( natToString ) ( Some(1) )) = \"(Some\\s1)\"" :value '(:|Bool| . t))
       ("let F = show ( natToString ) in (F ( Some(1) )) = \"(Some\\s1)\"" :swe "let F = show ( natToString ) in (F ( Some(1) )) = \"(Some\\s1)\"" :value '(:|Bool| . t))

       ;; String [100]:  op explode : String -> List Char
       ("(explode ( \"\" )) = []" :swe "(explode ( \"\" )) = []" :value '(:|Bool| . t))
       ("(explode ( \"abc\" )) = [#a,#b,#c]" :swe "(explode ( \"abc\" )) = [#a,#b,#c]" :value '(:|Bool| . t))
       ;; String [102]:  op implode       : List Char -> String
       ("(implode ( [] )) = \"\"" :swe "(implode ( [] )) = \"\"" :value '(:|Bool| . t))
       ("(implode ( [#a,#b,#c] )) = \"abc\"" :swe "(implode ( [#a,#b,#c] )) = \"abc\"" :value '(:|Bool| . t))
       ;; String [103]:  op length        : String -> Nat
       ("(length ( \"\" )) = 0" :swe "(length ( \"\" )) = 0" :value '(:|Bool| . t))
       ("(length ( \"abc\" )) = 3" :swe "(length ( \"abc\" )) = 3" :value '(:|Bool| . t))
;; concat is obsolete
       ;; String [104]:  op concat        : String * String -> String
;       ("(concat ( \"now\" , \"here\" )) = \"nowhere\"" :swe "(concat ( \"now\" , \"here\" )) = \"nowhere\"" :value '(:|Bool| . t))
;       ("let A = id ( \"now\" , \"here\" ) in (concat A) = \"nowhere\"" :swe "let A = id ( \"now\" , \"here\" ) in (concat A) = \"nowhere\"" :value '(:|Bool| . t))
       ;; String [105]:  op ^ infixl 11  : String * String -> String
       ("(^ ( \"now\" , \"here\" )) = \"nowhere\"" :swe "(^ ( \"now\" , \"here\" )) = \"nowhere\"" :value '(:|Bool| . t))
       ("let A = id ( \"now\" , \"here\" ) in (^ A) = \"nowhere\"" :swe "let A = id ( \"now\" , \"here\" ) in (^ A) = \"nowhere\"" :value '(:|Bool| . t))
       ;; String [106]:  op ^  infixl 11  : String * String -> String
       ("(^ ( \"now\" , \"here\" )) = \"nowhere\"" :swe "(^ ( \"now\" , \"here\" )) = \"nowhere\"" :value '(:|Bool| . t))
       ("let A = id ( \"now\" , \"here\" ) in (^ A) = \"nowhere\"" :swe "let A = id ( \"now\" , \"here\" ) in (^ A) = \"nowhere\"" :value '(:|Bool| . t))
       ;; String [107]:  op map           : (Char -> Char) -> String -> String
       ("(map ( fn(c)->chr(96+(let(v)=(ord(c)-96)in((v+13)mod(26)))) ) ( \"terra\" )) = \"green\"" :swe "(map ( fn(c)->chr(96+(let(v)=(ord(c)-96)in((v+13)mod(26)))) ) ( \"terra\" )) = \"green\"" :value '(:|Bool| . t))
       ("let F = map ( fn(c)->chr(96+(let(v)=(ord(c)-96)in((v+13)mod(26)))) ) in (F ( \"terra\" )) = \"green\"" :swe "let F = map ( fn(c)->chr(96+(let(v)=(ord(c)-96)in((v+13)mod(26)))) ) in (F ( \"terra\" )) = \"green\"" :value '(:|Bool| . t))
       ;; String [108]:  op exists?        : (Char -> Boolean) -> String -> Boolean
       ("(exists? ( isNum ) ( \"\" )) = false" :swe "(exists? ( isNum ) ( \"\" )) = false" :value '(:|Bool| . t))
       ("let F = exists? ( isNum ) in (F ( \"\" )) = false" :swe "let F = exists? ( isNum ) in (F ( \"\" )) = false" :value '(:|Bool| . t))
       ("(exists? ( isNum ) ( \"c3po\" )) = true" :swe "(exists? ( isNum ) ( \"c3po\" )) = true" :value '(:|Bool| . t))
       ("let F = exists? ( isNum ) in (F ( \"c3po\" )) = true" :swe "let F = exists? ( isNum ) in (F ( \"c3po\" )) = true" :value '(:|Bool| . t))
       ;; String [109]:  op forall?          : (Char -> Boolean) -> String -> Boolean
       ("(forall?( isAlpha ) ( \"\" )) = true" :swe "(forall?( isAlpha ) ( \"\" )) = true" :value '(:|Bool| . t))
       ("let F = forall?( isAlpha ) in (F ( \"\" )) = true" :swe "let F = forall?( isAlpha ) in (F ( \"\" )) = true" :value '(:|Bool| . t))
       ("(forall?( isAlpha ) ( \"c3po\" )) = false" :swe "(forall?( isAlpha ) ( \"c3po\" )) = false" :value '(:|Bool| . t))
       ("let F = forall?( isAlpha ) in (F ( \"c3po\" )) = false" :swe "let F = forall?( isAlpha ) in (F ( \"c3po\" )) = false" :value '(:|Bool| . t))
       ;; String [110]:  op @          : {(s,n) : String * Nat | n < length s} -> Char
       ("( \"afn\" @ 1 ) = #f" :swe "( \"afn\" @ 1 ) = #f" :value '(:|Bool| . t))
       ("let A = id ( \"afn\" , 1 ) in (@ A) = #f" :swe "let A = id ( \"afn\" , 1 ) in (@ A) = #f" :value '(:|Bool| . t))
       ;; String [111]:  op subFromTo     : {(s,i,j) : String * Nat * Nat | i < j && j <= length s} ->
       ("(subFromTo ( \"twitchy\" , 2, 6 )) = \"itch\"" :swe "(subFromTo ( \"twitchy\" , 2, 6 )) = \"itch\"" :value '(:|Bool| . t))
       ("let A = id ( \"twitchy\" , 2, 6 ) in (subFromTo A) = \"itch\"" :swe "let A = id ( \"twitchy\" , 2, 6 ) in (substring A) = \"itch\"" :value '(:|Bool| . t))
       ;; String [112]:  op flatten    : List String -> String
       ("(flatten ( [] )) = \"\"" :swe "(flatten ( [] )) = \"\"" :value '(:|Bool| . t))
       ("(flatten ( [\"now\",\"here\"] )) = \"nowhere\"" :swe "(flatten ( [\"now\",\"here\"] )) = \"nowhere\"" :value '(:|Bool| . t))
       ;; String [113]:  op translate     : (Char -> String) -> String -> String
       ("(translate ( fn(c)->implode[c,c] ) ( \"2B\" )) = \"22BB\"" :swe "(translate ( fn(c)->implode[c,c] ) ( \"2B\" )) = \"22BB\"" :value '(:|Bool| . t))
       ("let F = translate ( fn(c)->implode[c,c] ) in (F ( \"2B\" )) = \"22BB\"" :swe "let F = translate ( fn(c)->implode[c,c] ) in (F ( \"2B\" )) = \"22BB\"" :value '(:|Bool| . t))
       ;; String [114]:  op <  infixl 20 : String * String -> Boolean
       ("(< ( \"\" , \"\" )) = false" :swe "(< ( \"\" , \"\" )) = false" :value '(:|Bool| . t))
       ("let A = id ( \"\" , \"\" ) in (< A) = false" :swe "let A = id ( \"\" , \"\" ) in (< A) = false" :value '(:|Bool| . t))
       ("(< ( \"\" , \"1\" )) = true" :swe "(< ( \"\" , \"1\" )) = true" :value '(:|Bool| . t))
       ("let A = id ( \"\" , \"1\" ) in (< A) = true" :swe "let A = id ( \"\" , \"1\" ) in (< A) = true" :value '(:|Bool| . t))
       ("(< ( \"0\" , \"1\" )) = true" :swe "(< ( \"0\" , \"1\" )) = true" :value '(:|Bool| . t))
       ("let A = id ( \"0\" , \"1\" ) in (< A) = true" :swe "let A = id ( \"0\" , \"1\" ) in (< A) = true" :value '(:|Bool| . t))
       ("(< ( \"09\" , \"1\" )) = true" :swe "(< ( \"09\" , \"1\" )) = true" :value '(:|Bool| . t))
       ("let A = id ( \"09\" , \"1\" ) in (< A) = true" :swe "let A = id ( \"09\" , \"1\" ) in (< A) = true" :value '(:|Bool| . t))
       ("(< ( \"1\" , \"\" )) = false" :swe "(< ( \"1\" , \"\" )) = false" :value '(:|Bool| . t))
       ("let A = id ( \"1\" , \"\" ) in (< A) = false" :swe "let A = id ( \"1\" , \"\" ) in (< A) = false" :value '(:|Bool| . t))
       ("(< ( \"1\" , \"1\" )) = false" :swe "(< ( \"1\" , \"1\" )) = false" :value '(:|Bool| . t))
       ("let A = id ( \"1\" , \"1\" ) in (< A) = false" :swe "let A = id ( \"1\" , \"1\" ) in (< A) = false" :value '(:|Bool| . t))
       ("(< ( \"10\" , \"1\" )) = false" :swe "(< ( \"10\" , \"1\" )) = false" :value '(:|Bool| . t))
       ("let A = id ( \"10\" , \"1\" ) in (< A) = false" :swe "let A = id ( \"10\" , \"1\" ) in (< A) = false" :value '(:|Bool| . t))
       ("(< ( \"2\" , \"1\" )) = false" :swe "(< ( \"2\" , \"1\" )) = false" :value '(:|Bool| . t))
       ("let A = id ( \"2\" , \"1\" ) in (< A) = false" :swe "let A = id ( \"2\" , \"1\" ) in (< A) = false" :value '(:|Bool| . t))
       ;; String [115]:  op <= infixl 20 : String * String -> Boolean
       ("(<= ( \"\" , \"\" )) = true" :swe "(<= ( \"\" , \"\" )) = true" :value '(:|Bool| . t))
       ("let A = id ( \"\" , \"\" ) in (<= A) = true" :swe "let A = id ( \"\" , \"\" ) in (<= A) = true" :value '(:|Bool| . t))
       ("(<= ( \"\" , \"1\" )) = true" :swe "(<= ( \"\" , \"1\" )) = true" :value '(:|Bool| . t))
       ("let A = id ( \"\" , \"1\" ) in (<= A) = true" :swe "let A = id ( \"\" , \"1\" ) in (<= A) = true" :value '(:|Bool| . t))
       ("(<= ( \"0\" , \"1\" )) = true" :swe "(<= ( \"0\" , \"1\" )) = true" :value '(:|Bool| . t))
       ("let A = id ( \"0\" , \"1\" ) in (<= A) = true" :swe "let A = id ( \"0\" , \"1\" ) in (<= A) = true" :value '(:|Bool| . t))
       ("(<= ( \"09\" , \"1\" )) = true" :swe "(<= ( \"09\" , \"1\" )) = true" :value '(:|Bool| . t))
       ("let A = id ( \"09\" , \"1\" ) in (<= A) = true" :swe "let A = id ( \"09\" , \"1\" ) in (<= A) = true" :value '(:|Bool| . t))
       ("(<= ( \"1\" , \"\" )) = false" :swe "(<= ( \"1\" , \"\" )) = false" :value '(:|Bool| . t))
       ("let A = id ( \"1\" , \"\" ) in (<= A) = false" :swe "let A = id ( \"1\" , \"\" ) in (<= A) = false" :value '(:|Bool| . t))
       ("(<= ( \"1\" , \"1\" )) = true" :swe "(<= ( \"1\" , \"1\" )) = true" :value '(:|Bool| . t))
       ("let A = id ( \"1\" , \"1\" ) in (<= A) = true" :swe "let A = id ( \"1\" , \"1\" ) in (<= A) = true" :value '(:|Bool| . t))
       ("(<= ( \"10\" , \"1\" )) = false" :swe "(<= ( \"10\" , \"1\" )) = false" :value '(:|Bool| . t))
       ("let A = id ( \"10\" , \"1\" ) in (<= A) = false" :swe "let A = id ( \"10\" , \"1\" ) in (<= A) = false" :value '(:|Bool| . t))
       ("(<= ( \"2\" , \"1\" )) = false" :swe "(<= ( \"2\" , \"1\" )) = false" :value '(:|Bool| . t))
       ("let A = id ( \"2\" , \"1\" ) in (<= A) = false" :swe "let A = id ( \"2\" , \"1\" ) in (<= A) = false" :value '(:|Bool| . t))
       ;; String [116]:  op newline       : String
       ("(newline) = \"\\n\"" :swe "(newline) = \"\\n\"" :value '(:|Bool| . t))
       ;; String [117]:  op toScreen      : String -> ()  ;; deprecated
       ;; String [118]:  op writeLine     : String -> ()  ;; deprecated
       ;; String [119]:  op compare : String * String -> Comparison
       ("(compare ( \"\" , \"\" )) = Equal" :swe "(compare ( \"\" , \"\" )) = Equal" :value '(:|Bool| . t))
       ("let A = id ( \"\" , \"\" ) in (compare A) = Equal" :swe "let A = id ( \"\" , \"\" ) in (compare A) = Equal" :value '(:|Bool| . t))
       ("(compare ( \"\" , \"1\" )) = Less" :swe "(compare ( \"\" , \"1\" )) = Less" :value '(:|Bool| . t))
       ("let A = id ( \"\" , \"1\" ) in (compare A) = Less" :swe "let A = id ( \"\" , \"1\" ) in (compare A) = Less" :value '(:|Bool| . t))
       ("(compare ( \"0\" , \"1\" )) = Less" :swe "(compare ( \"0\" , \"1\" )) = Less" :value '(:|Bool| . t))
       ("let A = id ( \"0\" , \"1\" ) in (compare A) = Less" :swe "let A = id ( \"0\" , \"1\" ) in (compare A) = Less" :value '(:|Bool| . t))
       ("(compare ( \"09\" , \"1\" )) = Less" :swe "(compare ( \"09\" , \"1\" )) = Less" :value '(:|Bool| . t))
       ("let A = id ( \"09\" , \"1\" ) in (compare A) = Less" :swe "let A = id ( \"09\" , \"1\" ) in (compare A) = Less" :value '(:|Bool| . t))
       ("(compare ( \"1\" , \"\" )) = Greater" :swe "(compare ( \"1\" , \"\" )) = Greater" :value '(:|Bool| . t))
       ("let A = id ( \"1\" , \"\" ) in (compare A) = Greater" :swe "let A = id ( \"1\" , \"\" ) in (compare A) = Greater" :value '(:|Bool| . t))
       ("(compare ( \"1\" , \"1\" )) = Equal" :swe "(compare ( \"1\" , \"1\" )) = Equal" :value '(:|Bool| . t))
       ("let A = id ( \"1\" , \"1\" ) in (compare A) = Equal" :swe "let A = id ( \"1\" , \"1\" ) in (compare A) = Equal" :value '(:|Bool| . t))
       ("(compare ( \"10\" , \"1\" )) = Greater" :swe "(compare ( \"10\" , \"1\" )) = Greater" :value '(:|Bool| . t))
       ("let A = id ( \"10\" , \"1\" ) in (compare A) = Greater" :swe "let A = id ( \"10\" , \"1\" ) in (compare A) = Greater" :value '(:|Bool| . t))
       ("(compare ( \"2\" , \"1\" )) = Greater" :swe "(compare ( \"2\" , \"1\" )) = Greater" :value '(:|Bool| . t))
       ("let A = id ( \"2\" , \"1\" ) in (compare A) = Greater" :swe "let A = id ( \"2\" , \"1\" ) in (compare A) = Greater" :value '(:|Bool| . t))
       ("{a=1,b=2} << {a=3,c=4} = {a=3,b=2,c=4}" :swe "{a=1,b=2} << {a=3,c=4} = {a=3,b=2,c=4}" :value '(:|Bool| . t)))
