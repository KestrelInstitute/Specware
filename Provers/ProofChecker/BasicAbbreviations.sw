(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

MetaslangProofChecker qualifying
spec

  % API public default

  import TypesAndExpressions

  (* This spec defines meta ops that capture the abbreviations introduced in
  Section 2 of LD. The abbreviations introduced in Section 6 of LD are covered
  in spec OtherAbreviations. *)

  % return sequence [prod 1 ... prod n] of fields (empty if n=0):
  op firstNProductFields : Nat -> Fields
  def firstNProductFields n =
    list (fn(i:Nat) -> if i < n then Some (prod (i+1)) else None)

  % product type:
  op PRODUCT : Types -> Type
  def PRODUCT tS = RECORD (firstNProductFields (length tS), tS)

  % binary product type:
  % API private:
  op PRODUCT2 : Type * Type -> Type
  def PRODUCT2 (t1,t2) = PRODUCT (single t1 <| t2)

  % unit type:
  op UNIT : Type
  def UNIT = PRODUCT empty

  % combine n>1 expressions via application, i.e. e1 @ ... @ en:
  % API private
  op APPLYn : List1 Expression -> Expression
  def APPLYn eS = if length eS = 1 then theElement eS
                  else  APPLYn (butLast eS)  @  last eS

  % multi-variable lambda abstraction:
  % API private
  op FNN : Variables * Types * Expression -> Expression
  def FNN (vS,tS,e) =
    if vS = empty || tS = empty then e
    else FN (head vS, head tS, FNN (tail vS, tail tS, e))
    % if length vS ~= length tS, excess variables or types are ignored
    % (we avoid subtypes in public ops)

  % 2-variable lambda abstraction:
  % API private
  op FN2 : Variable * Type * Variable * Type * Expression -> Expression
  def FN2 (v1,t1,v2,t2,e) = FN (v1, t1, FN (v2, t2, e))

  % truth:
  op TRUE : Expression
  def TRUE = let x:Variable = abbr 0 in
             FN (x, BOOL, VAR x) == FN (x, BOOL, VAR x)

  % falsehood:
  op FALSE : Expression
  def FALSE = let x:Variable = abbr 0 in
              FN (x, BOOL, VAR x) == FN (x, BOOL, TRUE)

  % negation:
  op NOT : Expression
  def NOT = let x:Variable = abbr 0 in
            FN (x, BOOL, VAR x == FALSE)

  % applied negation:
  op ~~ : Expression -> Expression
  def ~~ e = NOT @ e

  % conjunction:
  op &&& infixr 25 : Expression * Expression -> Expression
  def &&& (e1,e2) = IF (e1, e2, FALSE)

  % n-ary conjunction:
  % API private
  op ANDn : Expressions -> Expression
  def ANDn eS = if eS = empty then TRUE
                else if ofLength? 1 eS then theElement eS
                else  head eS  &&&  ANDn (tail eS)

  % disjunction:
  op ||| infixr 24 : Expression * Expression -> Expression
  def ||| (e1,e2) = IF (e1, TRUE, e2)

  % n-ary disjunction:
  % API private
  op ORn : Expressions -> Expression
  def ORn eS = if eS = empty then FALSE
               else if ofLength? 1 eS then theElement eS
               else  head eS  |||  ORn (tail eS)

  % implication:
  op ==> infixr 23 : Expression * Expression -> Expression
  def ==> (e1,e2) = IF (e1, e2, TRUE)

  % equivalence:
  op IFF : Expression
  def IFF = let x:Variable = abbr 0 in
            let y:Variable = abbr 1 in
            FN (x, BOOL, FN (y, BOOL, VAR x == VAR y))

  % applied equivalence:
  op <==> infixr 22 : Expression * Expression -> Expression
  def <==> (e1,e2) = IFF @ e1 @ e2

  % non-equality:
  op ~== infixl 29 : Expression * Expression -> Expression
  def ~== (e1,e2) = ~~ (e1 == e2)

  % description:
  op THE : Variable * Type * Expression -> Expression
  def THE (v,t,e) =  IOTA t  @  FN (v, t, e)

  % universal quantifier:
  op FAq : Type -> Expression
  def FAq t = let p:Variable = abbr 0 in
              let x:Variable = abbr 1 in
              FN (p, t --> BOOL, VAR p == FN (x, t, TRUE))

  % universal quantification:
  op FA : Variable * Type * Expression -> Expression
  def FA (v,t,e) =  FAq t  @  FN (v, t, e)

  % multi-variable universal quantification:
  op FAA : Variables * Types * Expression -> Expression
  def FAA (vS,tS,e) = if vS = empty || tS = empty then e
                      else FA (head vS, head tS, FAA (tail vS, tail tS, e))
    % if length vS ~= length tS, excess variables or types are ignored
    % (we avoid subtypes in public ops)

  % 2-variable universal quantification:
  % API private
  op FA2 : Variable * Type * Variable * Type * Expression -> Expression
  def FA2 (v1,t1,v2,t2,e) = FA (v1, t1, FA (v2, t2, e))

  % 3-variable universal quantification:
  % API private
  op FA3 : Variable * Type * Variable * Type * Variable * Type *
           Expression -> Expression
  def FA3 (v1,t1,v2,t2,v3,t3,e) = FA (v1, t1, FA (v2, t2, FA (v3, t3, e)))

  % existential quantifier:
  op EXq : Type -> Expression
  def EXq t = let p:Variable = abbr 0 in
              let x:Variable = abbr 1 in
              FN (p, t --> BOOL, ~~ (FA (x, t, ~~ (VAR p @ VAR x))))

  % existential quantification:
  op EX : Variable * Type * Expression -> Expression
  def EX (v,t,e) =  EXq t  @  FN (v, t, e)

  % multi-variable existential quantification:
  op EXX : Variables * Types * Expression -> Expression
  def EXX (vS,tS,e) = if vS = empty || tS = empty then e
                      else EX (head vS, head tS, EXX (tail vS, tail tS, e))
    % if length vS ~= length tS, excess variables or types are ignored
    % (we avoid subtypes in public ops)

  % unique existential quantifier:
  op EX1q : Type -> Expression
  def EX1q t = let p:Variable = abbr 0 in
               let x:Variable = abbr 1 in
               let y:Variable = abbr 2 in
               FN (p,
                   t --> BOOL,
                   EX (x, t, VAR p @ VAR x &&&
                             FA (y, t, VAR p @ VAR y ==> VAR y == VAR x)))

  % unique existential quantification:
  op EX1 : Variable * Type * Expression -> Expression
  def EX1 (v,t,e) =  EX1q t  @  FN (v, t, e)

  % dotted projection:
  op DOT : Expression * Type * Field -> Expression
  def DOT (e,t,f) = PROJECT(t,f) @ e

endspec
