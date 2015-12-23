(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec

  % API private all

  import /Library/Structures/Data/Maps/SimpleAsAlist
  import IR qualifying (../DPGen/InferenceRules[../DPGen/InferenceRulesI#IRInterface])

  (* This spec defines the state that the proof checker monad uses. Currently
  the state only includes a Memo for caching the results of the check function
  defined in Checker.sw. Over time additional state variables can be added
  here as our necessary.

  When adding a state variable it is important to update the type State, the
  definition for initial state and to provide functions that constitute the
  API to those state variables, like memoS, checkMemoS, and putMemoS. Note
  that the "S" at the end of these names is used to distinguish them from the
  functions with similar names defined in Monad. *)

  type Info = Ineq
  type State =
    {proofInfo: Map(Proof, Info)}

  op initialState: State
  def initialState = {proofInfo = emptyMap}

(*
  op memoS?: Proof -> State -> Bool
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
*)

  op StateC.getInfo: Proof -> State -> Info
  def StateC.getInfo(i) =
    fn state ->
    %let _ = writeLine("get: "^(print(i))) in
    let proofInfo = state.proofInfo in
    let Some res = apply(proofInfo, i) in
    res

  op StateC.putInfo: Proof * Info -> State -> State
  def StateC.putInfo(i, info) =
    fn state ->
    %let _ = writeLine("put: "^(print(i))) in
    let proofInfo = state.proofInfo in
    let proofInfo = update(proofInfo, i, info) in
    let state = {proofInfo = proofInfo} in
    state

endspec
