spec
  import ParseGrammar
  import RawSmartSlangGrammar2

  op  theGrammar : Grammar
  def theGrammar = case parseGrammar rawGrammar of
    | OK g -> g
    | KO m -> (writeLine m; [])

endspec
