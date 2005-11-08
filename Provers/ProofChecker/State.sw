spec

  import ProofCheckerMonad, /Library/Structures/Data/Maps/SimpleAsAlist, Proofs, Failures

  type PCMonad.State =
    {Memo: Map.Map(Proof, Judgement)}

  def PCMonad.initialState = {Memo = emptyMap}

  op memo?: Proof -> M Boolean
  def memo?(p) =
    fn state ->
    let memo = state.Memo in
    let res =
    case apply(memo, p) of
      | Some _ -> true
      | None -> false in
    (RETURN res, state)

  op checkMemo: Proof -> M (Option (Judgement))
  def checkMemo(p) =
    fn state ->
    let memo = state.Memo in
    let res = apply(memo, p) in
    (RETURN res, state)

  op putMemo: Proof * Judgement -> M Judgement
  def putMemo(p, j) =
    fn state ->
    let memo = state.Memo in
    let memo = update(memo, p, j) in
    let state = {Memo = memo} in
    (RETURN j, state)

endspec

