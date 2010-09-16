IO qualifying spec
  import Exception
  import /Library/Legacy/Utilities/System

  op print : String -> Monad ()
  def print str = return (toScreen str)

#translate Haskell -morphism
  type IO.Monad -> IO
  IO.print -> print
#end

endspec
