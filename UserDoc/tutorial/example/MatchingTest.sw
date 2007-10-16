Test = spec

  import MatchingRefinements#FindMatches

  op word_char?(ch: Char): Boolean = isUpperCase ch

  op msg_char?(ch: Char): Boolean = isUpperCase ch or ch = #*

  type WordString = (String | all word_char?)

  type MessageString = (String | all msg_char?)

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

 def implode l = foldl (fn (c,s) -> s ^ toString c) "" l
 def explode s =
   if s = "" then []
     else Cons(sub(s,0),explode(substring(s,1,length s)))

endspec

Data = spec
  import Test
  op msg: MessageString = "**V*ALN**EC*E*S"
  op words: List WordString =
    ["CERAMIC","CHESS","DECREE","FOOTMAN",
     "INLET","MOLOCH","OCELOT","PROFUSE",
     "RESIDE", "REVEAL", "SECRET", "SODIUM",
     "SPECIES", "VESTIGE", "WALNUT", "YOGURT"]

  def main(): () =
    let results = test_find_matches(msg,words) in
    app (fn {position,word} ->
           writeLine("Word "^word^" matches at "^ toString position))
      results
    
endspec

JavaInfo = spec
  def package = "Match"
  def moduleClassName = "MatchMod"
  def public = ["main"]
endspec

(* To generate, compile and run Java version
* gen-java MatchingTest#Data MatchingTest#JavaInfo

In bash shell
: javac -source 1.4 Match/*.java
: java Match/Primitive
*)
