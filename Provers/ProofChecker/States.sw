(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

MetaslangProofChecker qualifying
spec

  % API private all

  import Proofs

  (* This spec defines the state that the proof checker monad uses. Currently
  the state only includes a Memo for caching the results of the check function
  defined in Checker.sw. Over time additional state variables can be added
  here as our necessary.

  When adding a state variable it is important to update the type State, the
  definition for initial state and to provide functions that constitute the
  API to those state variables, like memoS, checkMemoS, and putMemoS. Note
  that the "S" at the end of these names is used to distinguish them from the
  functions with similar names defined in Monad. *)

  type State =
    {Memo: MapL.Map(Proof, Judgement)}
           % from /Library/Structures/Data/Maps/SimpleAsAlist

  op initialState: State
  def initialState = {Memo = emptyMap}

  op memoS?: Proof -> State -> Bool
  def memoS?(p) =
    fn state ->
    let memo = state.Memo in
    let res =
    case apply(memo, p) of
      | Some _ -> true
      | None -> false in
    res

  op checkMemoS: Proof -> State -> Option Judgement
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
