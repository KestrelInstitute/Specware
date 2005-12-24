spec

  import /Library/Structures/Data/Monad

  type IO a = Monad a

  op read: IO String

  op print: String -> IO ()

  op while: IO Boolean -> IO () -> IO ()
  def while pred body =
    { 
      t <- pred;
      if t
	then {body; while pred body}
	else return ()
	 }

  op eval: String -> IO Boolean

  op readEvalPrint: IO ()
  def readEvalPrint =
    {
     print "Hi";
     cmd <- read;
     done <- eval cmd;
     if done
       then return ()
     else readEvalPrint
    }

endspec

    