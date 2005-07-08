spec

  % API private all

  (* This spec defines various ops related to syntactic entities that occur in
  other syntactic entities, e.g. the free variables that occur in an
  expression. *)

  import Contexts

  % free variables in expressions:

  op exprFreeVars : Expression -> FSet Variable
  def exprFreeVars = fn
    | VAR v              -> single v
    | APPLY(e1,e2)       -> exprFreeVars e1 \/ exprFreeVars e2
    | FN(v,t,e)          -> exprFreeVars e -- single v
    | EQ(e1,e2)          -> exprFreeVars e1 \/ exprFreeVars e2
    | IF(e0,e1,e2)       -> exprFreeVars e0 \/ exprFreeVars e1 \/ exprFreeVars e2
    | _                  -> empty

  % ops in types and expressions:

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

  % items declared or defined in contexts:

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

  op contextDefinesType? : Context * TypeName -> Boolean
  def contextDefinesType?(cx,tn) =
    (ex (tvS:TypeVariables, t:Type) typeDefinition (tn, tvS, t) in? cx)

  op contextDefinesOp? : Context * Operation -> Boolean
  def contextDefinesOp?(cx,o) =
    (ex (tvS:TypeVariables, e:Expression) opDefinition (o, tvS, e) in? cx)

endspec
