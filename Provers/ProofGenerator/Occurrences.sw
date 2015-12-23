(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

ProofGenerator qualifying
spec

 import ../ProofChecker/Spec

  op typeVarsInType: Type -> TypeVariables
  op typeVarsInExpr: Expression -> TypeVariables
  
  op +++ infixl 25 : [a] List a * List a -> List a
  def +++(s1, s2) =
    let s2Unique = removeNones(map (fn (e2) -> if e2 in? s1 then None else Some e2) s2) in
    s1 ++ s2Unique

  op uniqueConcat: [a] List (List a) -> List a
  def uniqueConcat(seqOfSeqs) =
    if empty?(seqOfSeqs)
      then empty
    else
      let s1 = head seqOfSeqs in
      let seqOfSeqsRest = tail seqOfSeqs in
      let restSeq = uniqueConcat seqOfSeqsRest in
      s1 +++ restSeq
  
  def typeVarsInType = fn
    | BOOL          -> empty
    | VAR tv        -> single tv
    | TYPE(tn,tS)   -> uniqueConcat (map typeVarsInType tS)
    | ARROW(t1,t2)  -> typeVarsInType t1 +++ typeVarsInType t2
    | RECORD(fS,tS) -> uniqueConcat (map typeVarsInType tS)
    | RESTR(t,r)    -> typeVarsInType t +++ typeVarsInExpr r

  def typeVarsInExpr = fn
    | VAR v              -> empty
    | OPI(o,tS)          -> uniqueConcat (map typeVarsInType tS)
    | APPLY(e1,e2)       -> typeVarsInExpr e1 +++ typeVarsInExpr e2
    | FN(v,t,e)          -> typeVarsInType t +++ typeVarsInExpr e
    | EQ(e1,e2)          -> typeVarsInExpr e1 +++ typeVarsInExpr e2
    | IF(e0,e1,e2)       -> typeVarsInExpr e0 +++ typeVarsInExpr e1 +++ typeVarsInExpr e2
    | IOTA t             -> typeVarsInType t
    | PROJECT(t,f)       -> typeVarsInType t

endspec
