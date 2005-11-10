(*
2005:11:04
DC

*)


spec

  import /Library/Unvetted/StateAndExceptionMonad
  %import %State%, %Failures
  import State

  type PCMonad(exc, a) = Monad(State,exc,a)

  (* To improve the readability of the checking function defined in spec
  Checker, we introduce a monad whose exceptions are the failures
  defined in Failures. It is not appropriate to explain (exception) monads
  here; so, the unfamiliar reader is referred to the literature, for instance
  Philip Wadler's "Monads for functional programming".

  We use the name "M", despite its shortness, because it is inconspicuous.
  After all, the purpose of monads is exactly to "hide" certain details. *)

  type M a = Monad (State, Failure, a)

  (* It is convenient to introduce shorter synonyms for the constructors of
  the exception monad for normal and exceptional results. *)

  op OK : [a] a -> M a
  def OK = return

  op FAIL : [a] Failure -> M a
  def FAIL = throw

  op memo?: Proof -> M Boolean
  def memo?(p) =
    fn state ->
    (RETURN (memo? p state), state)

  op checkMemo: Proof -> M (Option (Judgement))
  def checkMemo(p) =
    fn state ->
    (RETURN (checkMemo p state), state)

  op putMemo: Proof * Judgement -> M Judgement
  def putMemo(p, j) =
    fn state ->
    (RETURN j, (putMemo (p, j) state))

endspec
