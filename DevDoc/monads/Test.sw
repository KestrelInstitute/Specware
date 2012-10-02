Test qualifying spec
  import translate (translate Echo
    by {Monad.Monad +-> SpecCalc.Env})
    by {Monad._ +-> SpecCalc._}

  import /Languages/SpecCalculus/Semantics/Monad

  def IO.eof str = Fail str
  def IO.fileError (opt,s1,s2) = Fail (s1 ++ " " ++ s2)

  op tst : () -> ()
  def tst () = SpecCalc.run echo
endspec

