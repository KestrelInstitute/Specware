(* 2005:11:14 DC

 This spec defines the state that the proof checker monad uses.
 Currently the state only includes a Memo for caching the results of
 the check function defined in Checker.sw.  Over time additional state
 variables can be added here as our necessary.

 When adding a state variable it is important to update the type
 State, the definition for initial state and to provide functions that
 constitute the api to those state variables, cf, memoS, checkMemoS,
 and putMemoS.  Note that the S at the end of these names is used to
 distinguish them from the functions with similar names defined in
 ProofCheckerMonad.  Ideally qualification would be used to
 distinguish these functions. *)

spec

  % API private

  import Proofs, Failures

  type State =
    {Memo: Map.Map(Proof, Judgement)}

  op initialState: State
  def initialState = {Memo = emptyMap}

  op memoS?: Proof -> State -> Boolean
  def memoS?(p) =
    fn state ->
    let memo = state.Memo in
    let res =
    case apply(memo, p) of
      | Some _ -> true
      | None -> false in
    res

  op checkMemoS: Proof -> State -> Option (Judgement)
  def checkMemoS(p) =
    fn state ->
    let memo = state.Memo in
    let res = apply(memo, p) in
    res

  op putMemoS: Proof * Judgement -> State -> State
  def putMemoS(p, j) =
    fn state ->
    let memo = state.Memo in
    let memo = update(memo, p, j) in
    let state = {Memo = memo} in
    state

endspec

