Symbols = spec
  type Symbol = (Char | isUpperCase)

  def use_support_list = 
    "(use-resolution t)
    (use-paramodulation t)
    (use-hyperresolution nil)
    (use-negative-hyperresolution nil)
    (assert-supported nil)
    (use-term-ordering :rpo)
    (use-default-ordering nil)
    (use-literal-ordering-with-resolution 'literal-ordering-a)
    (use-literal-ordering-with-paramodulation 'literal-ordering-a)
    (use-literal-ordering-with-hyperresolution 'literal-ordering-p)
    (use-literal-ordering-with-negative-hyperresolution 'literal-ordering-n)
    (declare-predicate-symbol '>= 2 :sort '(boolean number number)
    :alias 'gte)
    (declare-function '+ :any 
     :commutative t :associative t)
    (declare-function '- 2 :alias 'minusBinary)
    (declare-ordering-greaterp 'minusBinary '+ '|Nat.one| '1 '|Nat.zero| '0)   ;;  
    (declare-ordering-greaterp 'snark::< 'snark::=<)
    (declare-ordering-greaterp 'snark::> 'snark::=<)
    (declare-ordering-greaterp 'snark::gte  'snark::=<)
    (declare-ordering-greaterp 'snark::|List.length_Symbol| '+)
    (declare-ordering-greaterp 'snark::|List.length_Symbol| '1)
    (declare-ordering-greaterp 'snark::|List.length_Option_Symbol| '+)
    (declare-ordering-greaterp 'snark::|List.length_Option_Symbol| '1)
    (declare-ordering-greaterp 'snark::|embed_Cons| 'snark::|List.length|)
    (declare-ordering-greaterp 'snark::|embed_Cons| '+)
    (declare-ordering-greaterp 'snark::|embed_Cons| '1)
    (declare-ordering-greaterp 'snark::|List.cons| 'snark::|embed_Cons|)
    (run-time-limit 10)
"
endspec


Symbols_Ref = morphism MatchingSpecs#Symbols ->
                       MatchingRefinements#Symbols {}

WordMatching0 = spec

  import MatchingSpecs#Words
  import MatchingSpecs#Messages
  import MatchingSpecs#SymbolMatching

  op word_matches_at? : Word * Message * Nat -> Boolean
  def word_matches_at?(wrd,msg,pos) =
      if pos + length wrd > length msg
      then false
      else word_matches_aux?(wrd, nthTail(msg, pos))

  op word_matches_aux? :
     {(wrd,msg) : Word * Message | length wrd <= length msg}
     -> Boolean
  def word_matches_aux?(wrd,msg) =
      case wrd of Nil -> true
                | Cons(wsym,wrd1) ->
                  let Cons(msym,msg1) = msg in
                  if symb_matches?(wsym,msym)
                  then word_matches_aux?(wrd1,msg1)
                  else false

endspec


WordMatching_Ref0 = morphism MatchingSpecs#WordMatching ->
                             WordMatching0 {}


WordMatching = WordMatching0[Symbols_Ref]


WordMatching_Ref =
   morphism MatchingSpecs#WordMatching ->
            MatchingRefinements#WordMatching {}


FindMatches0 = spec

  import MatchingSpecs#WordMatching
  import MatchingSpecs#Matches

  op find_matches : Message * List Word -> List Match
  def find_matches(msg,wrds) =
      foldl (fn(wrd,mtchs) ->
               case find_matches_aux(msg,wrd,0)
                 of Some pos ->
                    Cons({word = wrd, position = pos},
                         mtchs)
                  | None -> mtchs)
            Nil
            wrds

  op find_matches_aux : Message * Word * Nat -> Option Nat
  def find_matches_aux(msg,wrd,pos) =
      if pos + length wrd > length msg
      then None
      else if word_matches_at?(wrd,msg,pos)
           then Some pos
           else find_matches_aux(msg, wrd, pos + 1)

endspec


FindMatches_Ref0 = morphism MatchingSpecs#FindMatches ->
                            FindMatches0 {}


FindMatches = FindMatches0[WordMatching_Ref]


FindMatches_Ref = morphism MatchingSpecs#FindMatches ->
                           MatchingRefinements#FindMatches {}

