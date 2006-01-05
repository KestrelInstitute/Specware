spec

  import Monad[/Library/General/FiniteSequencesAsListsMorphism]
  import /Library/Structures/Data/Monad/ImpureIO

  type IO a = M a

  op ReadError: Exception

  op read: IO String
  def read =
    {
     val <- return (readLine(IO.stdin));
     case val of
       | Ok a -> return a
       | _ -> throw ReadError
    }

  op WriteError: Exception

  op print: String -> IO ()
  def print(s) =
    {
     ss <- print;
     val <- return (String.writeLine ss);
     return ()
      }

  op while: IO Boolean -> IO () -> IO ()
  def while pred body =
    { 
      t <- pred;
      if t
	then {body; while pred body}
	else return ()
	 }

  op eval: String -> IO Boolean
  def eval s = 
    case s of
      | "split" -> evalSplit
      | "propax" -> evalPropax
      | _ -> return true

  op evalSplit: IO Boolean
  def evalSplit =
    {
     tx <- treeX;
     n <- return (focus(tx));
     f <- return (n.formula);
     case (andStep(f)) of
       | Some (sgs, vf) -> addSubgoals(sgs)
       | None -> return ();
     return false
    }

  op evalPropax: IO Boolean
  def evalPropax =
    {
     tx <- treeX;
     n <- return (focus(tx));
     f <- return (n.formula);
     case (trueStep(f)) of
       | Some(sgs, vf) -> {addSubgoals(sgs); nextGoal}
       | None -> return ();
     return false
    }

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

    