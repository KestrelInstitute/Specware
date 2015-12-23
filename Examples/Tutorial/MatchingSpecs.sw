(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Symbols = spec
  type Symbol
endspec


Words = spec
  import Symbols
  type Word = List Symbol
endspec


Messages = spec
  import Symbols
  type Message = List (Option Symbol)
endspec


SymbolMatching = spec
  import Symbols
  op symb_matches?(s: Symbol, os: Option Symbol): Bool
    = case os of
        | Some s1 -> s = s1
        | None    -> true
endspec


WordMatching = spec

  import Words
  import Messages
  import SymbolMatching

  op word_matches_at?(wrd: Word, msg: Message, pos: Nat): Bool =
    pos + length wrd <= length msg &&
    (fa(i:Nat) i < length wrd => symb_matches?(wrd@i, msg@(pos+i)))

endspec


Matches = spec
  import Words
  type Match = {word : Word, position : Nat}
endspec


FindMatches = spec

  import WordMatching
  import Matches

  op find_matches : Message * List Word -> List Match
  axiom match_finding is
    fa(msg,wrds,mtch)
      mtch in? find_matches(msg,wrds)
       <=>
      mtch.word in? wrds
       && word_matches_at?(mtch.word,msg,mtch.position)
       && (fa(pos) word_matches_at?(mtch.word,msg,pos)
             => pos >= mtch.position)

endspec
