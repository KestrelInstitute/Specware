(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec

  % API private all

  import /Library/Structures/Data/Maps/SimpleAsSTHarray
  import IR qualifying (InferenceRules[InferenceRulesI#IRInterface])

  (* This spec defines the state that the proof checker monad uses. Currently
  the state only includes a Memo for caching the results of the check function
  defined in Checker.sw. Over time additional state variables can be added
  here as our necessary.

  When adding a state variable it is important to update the type State, the
  definition for initial state and to provide functions that constitute the
  API to those state variables, like memoS, checkMemoS, and putMemoS. Note
  that the "S" at the end of these names is used to distinguish them from the
  functions with similar names defined in Monad. *)

  type Info = Proof
  type State =
    {ineqInfo: Map(Ineq, Info)}
           % from /Library/Structures/Data/Maps/SimpleAsAlist

  op initialState: State
  def initialState = {ineqInfo = emptyMap}

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

  op State.getInfo: Ineq -> State -> Info
  def State.getInfo(i) =
    fn state ->
    %let _ = writeLine("get: "^(print(i))) in
    let ineqInfo = state.ineqInfo in
    let Some res = apply(ineqInfo, i) in
    res

  op State.putInfo: Ineq * Info -> State -> State
  def State.putInfo(i, info) =
    fn state ->
    %let _ = writeLine("put: "^(print(i))) in
    let ineqInfo = state.ineqInfo in
    let ineqInfo = update(ineqInfo, i, info) in
    let state = {ineqInfo = ineqInfo} in
    state

endspec
