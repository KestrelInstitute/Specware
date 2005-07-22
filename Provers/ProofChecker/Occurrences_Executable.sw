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

  op typeOps : Type       -> FSet Operation
  op exprOps : Expression -> FSet Operation

  def typeOps = fn
    | BOOL          -> empty
    | VAR tv        -> empty
    | TYPE(tn,tS)   -> \\// (map typeOps tS)
    | ARROW(t1,t2)  -> typeOps t1 \/ typeOps t2
    | RECORD(fS,tS) -> \\// (map typeOps tS)
    | SUM(cS,tS)    -> \\// (map typeOps tS)
    | RESTR(t,r)    -> typeOps t \/ exprOps r
    | QUOT(t,q)     -> typeOps t \/ exprOps q

  def exprOps = fn
    | VAR v              -> empty
    | OPI(o,tS)          -> single o \/ \\// (map typeOps tS)
    | APPLY(e1,e2)       -> exprOps e1 \/ exprOps e2
    | FN(v,t,e)          -> typeOps t \/ exprOps e
    | EQ(e1,e2)          -> exprOps e1 \/ exprOps e2
    | IF(e0,e1,e2)       -> exprOps e0 \/ exprOps e1 \/ exprOps e2
    | IOTA t             -> typeOps t
    | PROJECT(t,f)       -> typeOps t
    | EMBED(t,c)         -> typeOps t
    | QUOT t             -> typeOps t

  op contextElementTypes    : ContextElement -> FSet TypeName
  op contextElementOps      : ContextElement -> FSet Operation
  op contextElementTypeVars : ContextElement -> FSet TypeVariable
  op contextElementVars     : ContextElement -> FSet Variable
  op contextElementAxioms   : ContextElement -> FSet AxiomName

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

  op contextTypes    : Context -> FSet TypeName
  op contextOps      : Context -> FSet Operation
  op contextTypeVars : Context -> FSet TypeVariable
  op contextVars     : Context -> FSet Variable
  op contextAxioms   : Context -> FSet AxiomName

  def contextTypes    cx = \\// (map contextElementTypes    cx)
  def contextOps      cx = \\// (map contextElementOps      cx)
  def contextTypeVars cx = \\// (map contextElementTypeVars cx)
  def contextVars     cx = \\// (map contextElementVars     cx)
  def contextAxioms   cx = \\// (map contextElementAxioms   cx)

  % the following are executable versions of the homonymous ops
  % in spec Occurrences:

  op contextDefinesType? : Context * TypeName -> Boolean
  def contextDefinesType?(cx,tn) =
    nonEmpty? cx &&
    (case first cx of
       | typeDefinition(tn1,_,_) ->
         tn1 = tn || contextDefinesType? (rtail cx, tn)
       | _ -> contextDefinesType? (rtail cx, tn))

  op contextDefinesOp? : Context * Operation -> Boolean
  def contextDefinesOp?(cx,o) =
    nonEmpty? cx &&
    (case first cx of
       | opDefinition(o1,_,_) ->
         o1 = o || contextDefinesOp? (rtail cx, o)
       | _ -> contextDefinesOp? (rtail cx, o))

endspec
