(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec
  import ParseGrammar
  import RawSmartSlangGrammar2

  op  theGrammar : Grammar
  def theGrammar = case parseGrammar rawGrammar of
    | OK g -> g
    | KO m -> (writeLine m; [])

endspec
