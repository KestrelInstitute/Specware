spec

  import Primitives


  % types:

  type Type =
    | boolean
    | named TypeName
    | arrow Type * Type

  op BOOL : Type
  def BOOL = boolean

  op TYP : TypeName -> Type
  def TYP tn = named tn

  op --> infixr 25 : Type * Type -> Type
  def --> = arrow

  axiom Type_induction is
    fa (pred : Type -> Boolean)
      pred BOOL
      &&
      (fa(tn:TypeName) pred (TYP tn))
      &&
      (fa(t1:Type,t2:Type) pred t1 && pred t2 => pred (t1 --> t2))
      =>
      (fa(t:Type) pred t)


  % expressions:

  type Expression =
    | var Variable
    | opp Operation
    | app Expression * Expression
    | abs Variable * Type * Expression
    | eq  Expression * Expression

  op VAR : Variable -> Expression
  def VAR = embed var

  op OP : Operation -> Expression
  def OP = embed opp

  op @ infixl 30 : Expression * Expression -> Expression
  def @ = embed app

  op FN : Variable -> Type -> Expression -> Expression
  def FN v t e = embed abs (v, t, e)

  op == infixl 29 : Expression * Expression -> Expression
  def == = embed eq

  axiom Expression_induction is
    fa (pred : Expression -> Boolean)
      (fa(v:Variable) pred (VAR v))
      &&
      (fa(o:Operation) pred (OP o))
      &&
      (fa(e1:Expression,e2:Expression) pred e1 && pred e2 => pred (e1 @ e2))
      &&
      (fa(v:Variable,t:Type,e:Expression) pred e => pred (FN v t e))
      &&
      (fa(e1:Expression,e2:Expression) pred e1 && pred e2 => pred (e1 == e2))
      =>
      (fa(e:Expression) pred e)


  % contexts:

  type ContextElement =
    | typeDeclaration TypeName
    | opDeclaration   Operation * Type
    | typeDefinition  TypeName * Type
    | opDefinition    Operation * Expression
    | axioM           AxiomName * Expression
    | varDeclaration  Variable * Type

  type Context = FSeq ContextElement


  % specs:

  op contextWithoutVarDeclarations? : Context -> Boolean
  def contextWithoutVarDeclarations? cx =
    ~(exists? (embed? varDeclaration) cx)

  type Spec = (Context | contextWithoutVarDeclarations?)


  % judgements:

  type Judgement =
    | wellFormedContext Context
    | wellFormedSpec    Spec
    | wellFormedType    Context * Type
    | typeEquivalence   Context * Type * Type
    | wellTypedExpr     Context * Expression * Type
    | theoreM           Context * Expression

endspec
