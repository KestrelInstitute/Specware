Symbols = spec

  op upcase? : Integer -> Boolean
  def upcase?(i) = (65 <= i & i <= 90)
  % characters represented as ASCII codes

  sort Symbol = (Integer | upcase?)

endspec


Symbols_Ref = morphism MatchingSpecs#Symbols ->
                       MatchingRefinements# Symbols {}


WordMatching0 = spec

  import MatchingSpecs#Words
  import MatchingSpecs#Messages
  import MatchingSpecs#SymbolMatching

  op word_matches_at? : Word * Message * Integer -> Boolean
  def word_matches_at?(wrd,msg,pos) =
      if pos + lenW(wrd) > lenM(msg)
      then false
      else word_matches_aux?
            (wrd, if pos = 0 then msg else nthtailM(msg,pos-1))

  op word_matches_aux? :
     {(wrd,msg) : Word * Message | lenW(wrd) <= lenM(msg)} -> Boolean
  def word_matches_aux?(wrd,msg) =
      case wrd of
         | nnil -> true
         | ccons(wsym,wrd1) ->
             (case msg of
                 | ccons(msym,msg1) -> if symb_matches?(wsym,msym)
                                       then word_matches_aux?(wrd1,msg1)
                                       else false)

endspec


WordMatching_Ref0 = morphism MatchingSpecs#WordMatching ->
                             WordMatching0 {}


WordMatching = WordMatching0[Symbols_Ref]


WordMatching_Ref =
   morphism MatchingSpecs#WordMatching ->
            MatchingRefinements#WordMatching {}


FindMatches0 = spec

  import MatchingSpecs#WordMatching
  import MatchingSpecs#WordLists
  import MatchingSpecs#MatchLists

  op find_matches : Message * WordList -> MatchList
  def find_matches(msg,wrds) =
      case wrds of
         | nnil -> nnil
         | ccons(wrd,wrds1) ->
             let pos = find_matches_aux(msg,wrd,0) in
             if pos = ~1 then find_matches(msg,wrds1)
             else ccons({word = wrd, position = pos},find_matches(msg,wrds1))

  op find_matches_aux :
     {(m,w,i) : Message * Word * Integer | i >= 0} -> Integer
                                                      % ~1 means not found
  def find_matches_aux(msg,wrd,pos) =
      if pos + lenW(wrd) > lenM(msg) then ~1
      else if word_matches_at?(wrd,msg,pos) then pos
           else find_matches_aux(msg,wrd,pos+1)

endspec


FindMatches_Ref0 = morphism MatchingSpecs#FindMatches -> 
		            FindMatches0 {}


FindMatches = FindMatches0[WordMatching_Ref]


FindMatches_Ref = morphism MatchingSpecs#FindMatches ->
                           MatchingRefinements#FindMatches {}
