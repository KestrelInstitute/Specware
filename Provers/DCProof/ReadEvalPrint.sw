spec

  import Monad%[/Library/General/FiniteSequencesAsListsMorphism]
  import ProofGoals
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
      | "triv" -> evalTriv
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

  op evalTriv: IO Boolean
  def evalTriv =
    {
     tx <- treeX;
     n <- return (focus(tx));
     f <- return (n.formula);
     case (trueStep(f)) of
       | Some(sgs, vf) -> addSubgoals(sgs)
       | None -> return ();
     done <- proven;
     if done
       then return true
     else
       {nextGoal;
	return false}
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

  op testProof: () -> Boolean
  def testProof () =
    let _ = readEvalPrint initialState in
    true

endspec

    