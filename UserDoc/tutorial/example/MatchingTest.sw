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

endspec

Data = spec
  import Test
  def msg = "**V*ALN**EC*E*S"
  def words = ["CERAMIC","CHESS","DECREE","FOOTMAN",
	       "INLET","MOLOCH","OCELOT","PROFUSE",
	       "RESIDE", "REVEAL", "SECRET", "SODIUM",
	       "SPECIES", "VESTIGE", "WALNUT", "YOGURT"]
endspec