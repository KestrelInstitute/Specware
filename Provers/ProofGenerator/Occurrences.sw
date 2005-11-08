spec

 import ../ProofChecker/Spec

  op typeVarsInType: Type -> TypeVariables
  op typeVarsInExpr: Expression -> TypeVariables
  
  op +++ infixl 25 : [a] FSeq a * FSeq a -> FSeq a
  def +++(s1, s2) =
    let s2Unique = removeNones(map (fn (e2) -> if e2 in? s1 then None else Some e2) s2) in
    s1 ++ s2Unique

  op uniqueConcat: [a] FSeq (FSeq a) -> FSeq a
  def uniqueConcat(seqOfSeqs) =
    if empty?(seqOfSeqs)
      then empty
    else
      let s1 = first seqOfSeqs in
      let seqOfSeqsRest = rtail seqOfSeqs in
      let restSeq = uniqueConcat seqOfSeqsRest in
      s1 +++ restSeq
  
  def typeVarsInType = fn
    | BOOL          -> empty
    | VAR tv        -> single tv
    | TYPE(tn,tS)   -> uniqueConcat (map typeVarsInType tS)
    | ARROW(t1,t2)  -> typeVarsInType t1 +++ typeVarsInType t2
    | RECORD(fS,tS) -> uniqueConcat (map typeVarsInType tS)
    | SUM(cS,tS)    -> uniqueConcat (map typeVarsInType tS)
    | RESTR(t,r)    -> typeVarsInType t +++ typeVarsInExpr r
    | QUOT(t,q)     -> typeVarsInType t +++ typeVarsInExpr q

  def typeVarsInExpr = fn
    | VAR v              -> empty
    | OPI(o,tS)          -> uniqueConcat (map typeVarsInType tS)
    | APPLY(e1,e2)       -> typeVarsInExpr e1 +++ typeVarsInExpr e2
    | FN(v,t,e)          -> typeVarsInType t +++ typeVarsInExpr e
    | EQ(e1,e2)          -> typeVarsInExpr e1 +++ typeVarsInExpr e2
    | IF(e0,e1,e2)       -> typeVarsInExpr e0 +++ typeVarsInExpr e1 +++ typeVarsInExpr e2
    | IOTA t             -> typeVarsInType t
    | PROJECT(t,f)       -> typeVarsInType t
    | EMBED(t,c)         -> typeVarsInType t
    | QUOT t             -> typeVarsInType t

endspec
