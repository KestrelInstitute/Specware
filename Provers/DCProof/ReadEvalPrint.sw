(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

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
     ss <- print s;
     val <- return (String.writeLine ss);
     return ()
      }

  op while: IO Bool -> IO () -> IO ()
  def while pred body =
    { 
      t <- pred;
      if t
	then {body; while pred body}
	else return ()
	 }

  type SStep = Goal -> Option (FSeq Goal * String)

  op conv: String * Step -> SStep
  def conv (sn, s) =
    fn f ->
    case s f of
      | Some (sgs, v) -> Some (sgs, sn)
      | None -> None
  
  op eval: String -> IO StepRes
  def eval s = 
    case s of
      | "split" -> evalStep(conv("andElim", andStep))
      | "triv" -> evalStep(conv("trueTh", trueStep))
      | "refl" -> evalStep(conv("thRefl", reflStep))
      | "subst" -> evalStep(conv("thSubst", thSubstTrue))
      | "symm" -> evalStep(conv("thSymm", thSymmStep))
      | "if" -> evalStep(conv("thIf", thIfStep))
      | "try" -> evalTry(conv("andElim", andStep), conv("trueTh", trueStep))
      | "repeat" -> evalRepeat (try(conv("andElim",andStep), conv("trueth",trueStep)))
      | _ -> return Exit

  op try: SStep * SStep -> SStep
  def try(s1, s2) =
    fn f ->
    case s1 f of
      | Some res -> Some res
      | None -> s2 f

  op evalTry: SStep * SStep -> IO StepRes
  def evalTry(s1, s2) =
    {
     res0 <- evalStep s1;
     case res0 of
       | Proven -> return Proven
       | Unchanged -> evalStep s2
       | Changed -> return Changed
       | Exit -> return Exit
    }
     

(*  op repeat: Step -> Step
  def repeat(s) =
    fn f ->
    case s f of
      | Some res -> (repeat(s))res
      | None -> None
*)

  type StepRes = | Proven | Unchanged | Changed | Exit
  
  op evalRepeat: SStep -> IO StepRes
  def evalRepeat step =
    {
     res0 <- evalStep step;
     case res0 of
       | Proven -> return Proven
       | Unchanged -> return Unchanged
       | Changed -> evalRepeat step
       | Exit -> return Exit
    }

  op evalStep: SStep -> IO StepRes
  def evalStep step =
    {
     tx <- treeX;
     n <- return (focus(tx));
     f <- return (n.formula);
     case (step(f)) of
       | Some (sgs, vf) -> 
          {
	   stepName <- return vf;
	   addSubgoals(sgs, stepName);
	   propagateProven;
	   done <- proven;
	   if done
	     then
	       {
		 _ <- return (writeLine("QED"));
		 setStep stepName;
		 pt <- printTree;
		 _ <- return (writeLine pt);
		 return Proven
		}
	   else
	     {setStep stepName;
	      nextGoal;
	      return Changed}}
       | None -> return (Unchanged)
    }

  op evalSplit: IO Bool
  def evalSplit =
    {
     tx <- treeX;
     n <- return (focus(tx));
     f <- return (n.formula);
     case (andStep(f)) of
       | Some (sgs, vf) -> addSubgoals(sgs, "split")
       | None -> return ();
     return false
    }

  op evalTriv: IO Bool
  def evalTriv =
    {
     tx <- treeX;
     n <- return (focus(tx));
     f <- return (n.formula);
     case (trueStep(f)) of
       | Some(sgs, vf) -> addSubgoals(sgs, "triv")
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
     print "Goal ";
     cmd <- read;
     evalRes <- eval cmd;
     case evalRes of
       | Exit -> return ()
       | Proven -> return ()
       | _ -> readEvalPrint
    }

  op testProof: () -> Bool
  def testProof () =
    let _ = readEvalPrint initialState in
    true

endspec

    
