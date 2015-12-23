(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Check qualifying spec

  % API private default

  import ../DPGen/StateAndExceptionMonads, State

  type Exception = String

  (* To improve the readability of the checking function defined in spec
  Checker, we introduce a monad whose states are the ones defined in spec
  States and whose exceptions are the failures defined in spec Failures. It is
  not appropriate to explain monads here; so, the unfamiliar reader is
  referred to the literature, for instance Philip Wadler's "Monads for
  functional programming".

  We use the name "M", despite its shortness, because it is inconspicuous.
  After all, the purpose of monads is exactly to "hide" certain details. *)

  % API public
  type M a = Monad (State, Exception, a)

  (* It is convenient to introduce shorter synonyms for the constructors of
  the exception monad for normal and exceptional results. *)

  % API public
  op OK : [a] a -> M a
  def OK = return

  % API public
  op FAIL : [a] Exception -> M a
  def FAIL = throw

  % monadic ops to provide access to the state of the monad:

  op MonadC.getInfo: Proof -> M Info
  def MonadC.getInfo (p) =
    fn state ->
    (RETURN(StateC.getInfo p state), state)

  op MonadC.putInfo: Proof * Info -> M ()
  def MonadC.putInfo (p, info) =
    fn state ->
    (RETURN(()), (StateC.putInfo(p, info) state))

(*
  op Monad.print: String -> M String
  def Monad.print s =
    fn state ->
    (RETURN(s^State.print(state)), state)

  op Monad.printTree: M String
  def Monad.printTree =
    fn state ->
    (RETURN(printTree(state)), state)

  op Monad.treeX: M TreeX
  def Monad.treeX =
    fn state ->
    (RETURN(state.treeX), state)

  op Monad.addSubgoals: FSeq Goal * String -> M ()
  def Monad.addSubgoals(gs, step) =
    fn state ->
    ((RETURN()), (addSubgoals(state, gs, step)))

  op Monad.setStep: String -> M ()
  def Monad.setStep(step) =
    fn state ->
    ((RETURN()), (setStep(state, step)))

  op Monad.nextGoal: M ()
  def Monad.nextGoal =
    fn state ->
    ((RETURN()), (nextGoal(state)))

  op Monad.propagateProven: M ()
  def Monad.propagateProven =
    fn state ->
    ((RETURN()), (propagateProven(state)))

  op Monad.proven: M Bool
  def Monad.proven =
    fn state ->
    ((RETURN (proven(state))), state)
*)
  (*
  op memo?: Proof -> M Bool
  def memo?(p) =
    fn state ->
    (RETURN (memoS? p state), state)

  op checkMemo: Proof -> M (Option (Judgement))
  def checkMemo(p) =
    fn state ->
    (RETURN (checkMemoS p state), state)

  op putMemo: Proof * Judgement -> M Judgement
  def putMemo(p, j) =
    fn state ->
    (RETURN j, (putMemoS (p, j) state))

*)

  (* Op run provides a mechanism to transform a proof checker internal monadic
  function into a function appropriate for calling externally by ignoring the
  internal monadic state, cf. runCheck in Checker.sw *)

  op run: [a, b] (a -> M b) -> a -> Result (Exception, b)
  def run f x =
    let (res,_) = f x initialState in
    res

endspec
