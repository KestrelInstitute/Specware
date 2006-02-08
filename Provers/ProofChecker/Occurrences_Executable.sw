spec

  % API private all

  import Contexts

  (* This spec is an executable version of spec Occurrences. Actually, only
  two ops in spec Occurrences are not executable, namely ops
  contextDefinesType? and contextDefinesOp?. Since currently Specware provides
  no way of refining individual ops in a spec, we have to copy the other ops
  and their (executable) definitions from spec Occurrences. This, which is
  clearly not ideal, will change as soon as Specware provides better
  refinement capabilities. *)

  % the following are copied verbatim from spec Occurrences:

  op exprFreeVars : Expression -> FSet Variable
  def exprFreeVars = fn
    | VAR v              -> single v
    | APPLY(e1,e2)       -> exprFreeVars e1 \/ exprFreeVars e2
    | FN(v,t,e)          -> exprFreeVars e -- single v
    | EQ(e1,e2)          -> exprFreeVars e1 \/ exprFreeVars e2
    | IF(e0,e1,e2)       -> exprFreeVars e0 \/ exprFreeVars e1 \/ exprFreeVars e2
    | _                  -> empty

  op contextElementTypes    : ContextElement -> FSet TypeName
  op contextElementOps      : ContextElement -> FSet Operation
  op contextElementTypeVars : ContextElement -> FSet TypeVariable
  op contextElementVars     : ContextElement -> FSet Variable
  op contextElementAxioms   : ContextElement -> FSet AxiomName
  op contextElementLemmas   : ContextElement -> FSet LemmaName

  def contextElementTypes = fn
    | typeDeclaration(tn,_) -> single tn
    | _                     -> empty

  def contextElementOps = fn
    | opDeclaration(o,_,_) -> single o
    | _                    -> empty

  def contextElementTypeVars = fn
    | typeVarDeclaration tv -> single tv
    | _                     -> empty

  def contextElementVars = fn
    | varDeclaration(v,_) -> single v
    | _                   -> empty

  def contextElementAxioms = fn
    | axioM(an,_,_) -> single an
    | _             -> empty

  def contextElementLemmas = fn
    | lemma(ln,_,_) -> single ln
    | _             -> empty

  op contextTypes    : Context -> FSet TypeName
  op contextOps      : Context -> FSet Operation
  op contextTypeVars : Context -> FSet TypeVariable
  op contextVars     : Context -> FSet Variable
  op contextAxioms   : Context -> FSet AxiomName
  op contextLemmas   : Context -> FSet LemmaName

  def contextTypes    cx = \\// (map contextElementTypes    cx)
  def contextOps      cx = \\// (map contextElementOps      cx)
  def contextTypeVars cx = \\// (map contextElementTypeVars cx)
  def contextVars     cx = \\// (map contextElementVars     cx)
  def contextAxioms   cx = \\// (map contextElementAxioms   cx)
  def contextLemmas   cx = \\// (map contextElementLemmas   cx)

  % the following is an executable version of the homonymous op in spec
  % Occurrences:

  op contextDefinesType? : Context * TypeName -> Boolean
  def contextDefinesType?(cx,tn) =
    nonEmpty? cx &&
    (case first cx of
       | typeDefinition(tn1,_,_) ->
         tn1 = tn || contextDefinesType? (rtail cx, tn)
       | _ -> contextDefinesType? (rtail cx, tn))

  % the following are copied verbatim from spec Occurrences:

  op opInstancesInType : Operation -> Type       -> FSet Types
  op opInstancesInExpr : Operation -> Expression -> FSet Types

  def opInstancesInType o = fn
    | BOOL          -> empty
    | VAR tv        -> empty
    | TYPE(tn,tS)   -> \\// (map (opInstancesInType o) tS)
    | ARROW(t1,t2)  -> opInstancesInType o t1 \/ opInstancesInType o t2
    | RECORD(fS,tS) -> \\// (map (opInstancesInType o) tS)
    | SUM(cS,tS)    -> \\// (map (opInstancesInType o) tS)
    | RESTR(t,r)    -> opInstancesInType o t \/ opInstancesInExpr o r
    | QUOT(t,q)     -> opInstancesInType o t \/ opInstancesInExpr o q

  def opInstancesInExpr o = fn
    | VAR v        -> empty
    | OPI(o1,tS)   -> (if o1 = o then single tS else empty) \/
                      \\// (map (opInstancesInType o) tS)
    | APPLY(e1,e2) -> opInstancesInExpr o e1 \/ opInstancesInExpr o e2
    | FN(v,t,e)    -> opInstancesInType o t \/ opInstancesInExpr o e
    | EQ(e1,e2)    -> opInstancesInExpr o e1 \/ opInstancesInExpr o e2
    | IF(e0,e1,e2) -> opInstancesInExpr o e0 \/
                      opInstancesInExpr o e1 \/ opInstancesInExpr o e2
    | IOTA t       -> opInstancesInType o t
    | PROJECT(t,f) -> opInstancesInType o t
    | EMBED(t,c)   -> opInstancesInType o t
    | QUOT t       -> opInstancesInType o t

endspec
