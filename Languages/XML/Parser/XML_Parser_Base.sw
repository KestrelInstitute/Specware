
XML qualifying spec
  import XML_Parser_Monad
  import ../Utilities/XML_Unicode
  import ../XML_Sig

  sort Possible X = Env (Option X * UChars)
  sort Required X = Env (       X * UChars)

  def bad_name  msg : Env () = raise (Name  msg)
  def bad_value msg : Env () = raise (Value msg)

endspec