
XML qualifying spec
  import XML_Parser_Monad
  import ../Utilities/XML_Unicode
  import ../XML_Sig

  type Possible X = Env (Option X * UChars)
  type Required X = Env (       X * UChars)


endspec