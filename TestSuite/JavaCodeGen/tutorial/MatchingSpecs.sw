OneSort = spec
  sort X
endspec


Lists = spec

  % (parameterized) spec for monomorphic lists

  import OneSort  % parameter

  sort LList = | nnil | ccons X * LList
  % we double the initial letters to avoid conflict with built-in lists

  op len : LList -> Integer
  def len(l) = case l of
                  | nnil -> 0
                  | ccons(hd,tl) -> 1 + len(tl)

  op nthelem : {(l,n) : LList * Integer | 0 <= n & n < len(l)} -> X
  def nthelem(l,n) = case l of
                        | ccons(hd,tl) -> if n = 0 then hd
                                          else nthelem(tl,n-1)

  op nthtail : {(l,n) : LList * Integer | 0 <= n & n < len(l)} -> LList
  def nthtail(l,n) = case l of
                        | ccons(hd,tl) -> if n = 0 then tl
                                          else nthtail(tl,n-1)

  op haselem : LList * X -> Boolean
  def haselem(l,x) = case l of
                        | nnil -> false
                        | ccons(hd,tl) -> if x = hd then true
                                          else haselem(tl,x)

endspec


Symbols = spec
  sort Symbol
endspec


PossiblyObscuredSymbols = spec

  import Symbols

  sort POSymbol = | obscured
                  | clear Symbol

endspec


Words =  % lists of symbols, via instantiation
  translate
    Lists[morphism OneSort -> Symbols {X +-> Symbol}]
    by {LList   +-> Word,
        len     +-> lenW,
        nthelem +-> nthelemW,
        nthtail +-> nthtailW,
        haselem +-> haselemW}


Messages =  % lists of possibly obscured symbols, via instantiation
  translate
    Lists[morphism OneSort -> PossiblyObscuredSymbols {X +-> POSymbol}]
    by {LList   +-> Message,
        len     +-> lenM,
        nthelem +-> nthelemM,
        nthtail +-> nthtailM,
        haselem +-> haselemM}


SymbolMatching = spec

  import PossiblyObscuredSymbols

  op symb_matches? : Symbol * POSymbol -> Boolean
  def symb_matches?(s,os) = case os of
                               | clear s1 -> s = s1
                               | obscured -> true

endspec


WordMatching = spec
 
  import Words
  import Messages
  import SymbolMatching

  op word_matches_at? : Word * Message * Integer -> Boolean
  axiom word_matching is
        fa(wrd,msg,pos)
          word_matches_at?(wrd,msg,pos) <=>
          pos >= 0 &
          pos + lenW(wrd) <= lenM(msg) &
          (fa(i) i < lenW(wrd) =>
                 symb_matches?(nthelemW(wrd,i),
                               nthelemM(msg,pos+i)))

endspec


Matches = spec

  import Words

  sort Match = {word : Word, position : Integer}

endspec


MatchLists =  % lists of matches, via instantiation
  translate
    Lists[morphism OneSort -> Matches {X +-> Match}]
    by {LList   +-> MatchList,
        len     +-> lenML,
        nthelem +-> nthelemML,
        nthtail +-> nthtailML,
        haselem +-> haselemML}


WordLists =  % lists of words, via instantiation
  translate
    Lists[morphism OneSort -> Words {X +-> Word}]
    by {LList   +-> WordList,
        len     +-> lenWL,
        nthelem +-> nthelemWL,
        nthtail +-> nthtailWL,
        haselem +-> haselemWL}


FindMatches = spec

  import WordMatching
  import MatchLists
  import WordLists

  op find_matches : Message * WordList -> MatchList
  axiom match_finding is
        fa(msg,wrds,mtch)
          haselemML(find_matches(msg,wrds),mtch) <=>
          haselemWL(wrds,mtch.word) &
          word_matches_at?(mtch.word,msg,mtch.position) &
          (fa(pos) word_matches_at?(mtch.word,msg,pos) =>
                   pos >= mtch.position)

endspec
