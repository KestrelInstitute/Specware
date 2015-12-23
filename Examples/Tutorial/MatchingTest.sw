(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Test = spec

  import MatchingRefinements#FindMatches

  op word_char?(ch: Char): Bool = isUpperCase ch

  op msg_char?(ch: Char): Bool = isUpperCase ch || ch = #*

  type WordString = (String | forall? word_char?)

  type MessageString = (String | forall? msg_char?)

  op word2string(wrd: Word): WordString = implode wrd

  op string2word(wstr: WordString): Word = explode wstr

  op message2string(msg: Message): MessageString =
      implode(map (fn Some ch -> ch | None -> #*) msg)

  op string2message(mstr: MessageString): Message =
      map (fn ch -> if ch = #* then None else Some ch) (explode mstr)

  type MatchString = {word : WordString, position : Nat}

  op match2string(mtch: Match): MatchString =
      {word = word2string mtch.word, position = mtch.position}

  op test_find_matches(mstr: MessageString, wstrs: List WordString): List MatchString =
      map match2string
          (find_matches(string2message mstr, map string2word wstrs))

 def implode l = foldl (fn (s,c) -> s ^ show c) "" l
 def explode s =
   if s = "" then []
     else s@0 :: explode(subFromTo(s,1,length s))

end-spec

Data = spec
  import Test, /Library/Legacy/Utilities/System
  op msg: MessageString = "**V*ALN**EC*E*S"
  op words: List WordString =
    ["CERAMIC", "CHESS", "DECREE", "FOOTMAN",
     "INLET"," MOLOCH", "OCELOT", "PROFUSE",
     "RESIDE", "REVEAL", "SECRET", "SODIUM",
     "SPECIES", "VESTIGE", "WALNUT", "YOGURT"]

  op main(): () =
    let results = test_find_matches(msg,words) in
    app (fn {position,word} ->
           writeLine("Word "^word^" matches at "^ show position))
      results
    
end-spec
