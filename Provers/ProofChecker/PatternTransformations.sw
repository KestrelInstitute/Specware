spec

  (* This spec defines some operations on patterns, e.g. to transform them
  into expressions. *)

  import Judgements

  op patt2expr : Pattern -> Expression
  def patt2expr = fn
    | variable(v,_)           -> nullary (variable v)
    | embedding(typ,constr,p) -> binary (application,
                                         embedder (typ, constr),
                                         patt2expr p)
    | record comps            -> let (fields, patts) = unzip comps in
                                 let exprs = map (patt2expr, patts) in
                                 nary (record fields, exprs)
    | alias(_,p)              -> patt2expr p

  op pattBindings : Pattern -> FSeq TypedVar
  def pattBindings = fn
    | variable tvar           -> singleton tvar
    | embedding(typ,constr,p) -> pattBindings p
    | record comps            -> let (_, patts) = unzip comps in
                                 flatten (map (pattBindings, patts))
    | alias(tvar,p)           -> tvar |> pattBindings p

  op pattAliasAssumptions : Pattern -> Expression
  def pattAliasAssumptions = fn
    | variable _       -> nullary tru
    | embedding(_,_,p) -> pattAliasAssumptions p
    | record comps     -> let (_, patts) = unzip comps in
                          conjoinAll (map (pattAliasAssumptions, patts))
    | alias((v,_),p)   -> binary (conjunction,
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
