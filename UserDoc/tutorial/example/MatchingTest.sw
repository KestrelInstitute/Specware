Test = spec

  import MatchingRefinements#FindMatches

  op word_char? : Char -> Boolean
  def word_char? ch = isUpperCase ch

  op msg_char? : Char -> Boolean
  def msg_char? ch = isUpperCase ch or ch = #*

  sort WordString = (String | all word_char?)

  sort MessageString = (String | all msg_char?)

  op word2string : Word -> WordString
  def word2string wrd = implode wrd

  op string2word : WordString -> Word
  def string2word wstr = explode wstr

  op message2string : Message -> MessageString
  def message2string msg =
      implode(map (fn Some ch -> ch | None -> #*) msg)

  op string2message : MessageString -> Message
  def string2message mstr =
      map (fn ch -> if ch = #* then None else Some ch) (explode mstr)

  sort MatchString = {word : WordString, position : Nat}

  op match2string : Match -> MatchString
  def match2string mtch =
      {word = word2string mtch.word, position = mtch.position}

  op test_find_matches : MessageString * List WordString -> List MatchString
  def test_find_matches(mstr,wstrs) =
      map match2string
          (find_matches(string2message mstr, map string2word wstrs))

endspec
