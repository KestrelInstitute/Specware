spec

  import /Library/Structures/Data/Maps/SimpleAsAlist, Proofs, Failures

  type State =
    {Memo: Map.Map(Proof, Judgement)}

  op initialState: State
  def initialState = {Memo = emptyMap}

  op PCState.memo?: Proof -> State -> Boolean
  def PCState.memo?(p) =
    fn state ->
    let memo = state.Memo in
    let res =
    case apply(memo, p) of
      | Some _ -> true
      | None -> false in
    res

  op PCState.checkMemo: Proof -> State -> Option (Judgement)
  def PCState.checkMemo(p) =
    fn state ->
    let memo = state.Memo in
    let res = apply(memo, p) in
    res

  op PCState.putMemo: Proof * Judgement -> State -> State
  def PCState.putMemo(p, j) =
    fn state ->
    let memo = state.Memo in
    let memo = update(memo, p, j) in
    let state = {Memo = memo} in
    state

endspec

