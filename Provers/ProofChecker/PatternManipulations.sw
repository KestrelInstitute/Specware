spec

  (* This spec defines some operations on patterns, e.g. to transform them
  into expressions. *)

  import Judgements

  op patt2expr : Pattern -> Expression
  def patt2expr = fn
    | variable(v,_)    -> nullary (variable v)
    | embedding(t,c,p) -> binary (application,
                                  embedder (t, c),
                                  patt2expr p)
    | record(fS,pS)    -> let eS = map (patt2expr, pS) in
                          nary (record fS, eS)
    | alias(_,_,p)     -> patt2expr p

  op pattBindings : Pattern -> FSeq BoundVar
  def pattBindings = fn
    | variable(v,t)    -> singleton (v,t)
    | embedding(t,c,p) -> pattBindings p
    | record(_,pS)     -> flatten (map (pattBindings, pS))
    | alias(v,t,p)     -> (v,t) |> pattBindings p

  op pattAliasAssumptions : Pattern -> Expression
  def pattAliasAssumptions = fn
    | variable _       -> nullary tru
    | embedding(_,_,p) -> pattAliasAssumptions p
    | record(_,pS)     -> conjoinAll (map (pattAliasAssumptions, pS))
    | alias(v,_,p)     -> binary (conjunction,
                                  binary (equation,
                                          nullary (variable v),
                                          patt2expr p),
                                  pattAliasAssumptions p)

  op pattAssumptions : Pattern * Expression -> Expression
  def pattAssumptions(p,e) =
    binary (conjunction,
            binary (equation, e, patt2expr p),
            pattAliasAssumptions p)

endspec
