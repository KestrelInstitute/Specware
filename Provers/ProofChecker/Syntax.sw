spec

  import PrimitivesWithAbbreviations


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % types, expressions, and patterns:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Types depend on expressions, which depend on types and patterns, which
  depend on types. So, we first declare the meta types for these syntactic
  entities, and then define each of them below. *)

  type Type        % defined below
  type Expression  % defined below
  type Pattern     % defined below

  % useful abbreviations:

  type Type?    = Option Type
  type Pattern? = Option Pattern

  type BoundVar  = Variable * Type

  type Types       = FSeq Type
  type Expressions = FSeq Expression
  type Patterns    = FSeq Pattern
  type Type?s      = FSeq Type?
  type BoundVars   = FSeq BoundVar


  %%%%%%%%
  % types:
  %%%%%%%%

  (* Unlike LD, we model product types directly, as opposed to viewing them as
  abbreviations of record types with predefined fields.

  Another difference with LD is that we do not impose certain requirements
  (e.g. that the fields of a record type must be distinct) in the syntax. We
  incorporate such requirements in the inference rules, thus keeping the
  syntax simpler.

  A third difference is that here we explicitly model components of sum types
  that have no type (using `Option'), as opposed to implicitly assuming the
  empty record type as in LD. *)

  type NaryTypeConstruct =
    | instance TypeName
    | record   Fields
    | product

  type SubOrQuotientTypeConstruct =
    | sub
    | quotien(*t*)

  type Type =
    | boolean
    | variable TypeVariable
    | arrow    Type * Type
    | sum      Constructors * Type?s
    | nary     NaryTypeConstruct * Types
    | subQuot  SubOrQuotientTypeConstruct * Type * Expression


  %%%%%%%%%%%%%%
  % expressions:
  %%%%%%%%%%%%%%

  (* Unlike LD, we model all expression abbreviations (e.g. universal and
  existential quantification) explicitly.

  Another difference with LD is that we do not impose certain requirements
  (e.g. that the fields of a record must be distinct) in the syntax. We
  incorporate such requirements in the inference rules, thus keeping the
  syntax simpler.

  A third difference is that here embedders are decorated by types, not
  necessarily sum types. The inference rules require the decorating type of
  an embedder to be a sum type.

  A fourth difference is that here we allow lambda abstractions and unique
  existentials to bind multiple variables. *)

  type NullaryExprOperator =
    | variable Variable
    | tru(*e*)
    | fals(*e*)

  type UnaryExprOperator =
    | recordProjection Field
    | tupleProjection  PosNat
    | relaxator
    | quotienter
    | negation

  type BinaryExprOperator =
    | application
    | equation
    | inequation
    | recordUpdate
    | restriction
    | choice
    | conjunction
    | disjunction
    | implication
    | equivalence

  type NaryExprOperator =
    | record Fields
    | tuple

  type BindingExprOperator =
    | abstraction
    | universal
    | existential
    | existential1

  type Expression =
    | nullary         NullaryExprOperator
    | unary           UnaryExprOperator * Expression
    | binary          BinaryExprOperator * Expression * Expression
    | ifThenElse      Expression * Expression * Expression
    | nary            NaryExprOperator * Expressions
    | binding         BindingExprOperator * BoundVars * Expression
    | opInstance      Operation * Types
    | embedder        Type * Constructor
    | cas(*e*)        Expression * FSeq (Pattern * Expression)
    | recursiveLet    BoundVars * Expressions * Expression
    | nonRecursiveLet Pattern * Expression * Expression


  %%%%%%%%%%%
  % patterns:
  %%%%%%%%%%%

  (* Unlike LD, we do not require the fields of a record pattern to be
  distinct. Such a requirement is incorporated in the inference rules, thus
  keeping the syntax simpler.

  Another difference with LD is that here embedding patterns are decorated by
  types, not necessarily sum types. The inference rules require the decorating
  type of an embedding pattern to be a sum type.

  A third difference is that, since we model product types explicitly and not
  as abbreviations of record types with predefined fields, we must model tuple
  patterns, accordingly.

  A fourth difference is that since we explictly model components of sum types
  that have no type, we also have to model embedding patterns with no argument
  pattern. We use `Option' for that. *)

  type Pattern =
    | variable  BoundVar
    | embedding Type * Constructor * Pattern?
    | record    Fields * Patterns
    | tuple     Patterns
    | alias     BoundVar * Pattern


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % induction on types, expressions, and patterns:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* The recursive meta type definitions above only express fixpoints, not
  necessarily least ones. We enforce least ones by means of a (quite verbose)
  induction axiom on types, expressions, and patterns. *)

  axiom inductionTypesExpressionsPatterns is
    fa (predT : Predicate Type,
        predE : Predicate Expression,
        predP : Predicate Pattern)

  %%%%% induction base and step for types:
      predT boolean
   && (fa (tv:TypeVariable) predT (variable tv))
   && (fa (t1:Type, t2:Type)
         predT t1 && predT t2
      => predT (arrow (t1, t2)))
   && (fa (cS:Constructors, t?S:Type?s)
         (fa(t) Some t in? t?S => predT t)
      => predT (sum (cS, t?S)))
   && (fa (tc:NaryTypeConstruct, tS:Types)
         (fa(t) t in? tS => predT t)
      => predT (nary (tc, tS)))
   && (fa (tc:SubOrQuotientTypeConstruct, t:Type, e:Expression)
         predT t && predE e
      => predT (subQuot (tc, t, e)))

  %%%%% induction base and step for expressions:
   && (fa (eo:NullaryExprOperator)
         predE (nullary eo))
   && (fa (eo:UnaryExprOperator, e:Expression)
         predE e
      => predE (unary(eo, e)))
   && (fa (eo:BinaryExprOperator, e1:Expression, e2:Expression)
         predE e1 && predE e2
      => predE (binary (eo, e1, e2)))
   && (fa (e0:Expression, e1:Expression, e2:Expression)
         predE e0 && predE e1 && predE e2
      => predE (ifThenElse (e0, e1, e2)))
   && (fa (eo:NaryExprOperator, eS:Expressions)
         (fa(e) e in? eS => predE e)
      => predE (nary (eo, eS)))
   && (fa (eo:BindingExprOperator, vS:Variables, tS:Types, e:Expression)
         length vS = length tS
      && (fa(t) t in? tS => predT t)
      && predE e
      => predE (binding (eo, zip (vS, tS), e)))
   && (fa (o:Operation, tS:Types)
         (fa(t) t in? tS => predT t)
      => predE (opInstance (o, tS)))
   && (fa (t:Type, c:Constructor)
         predT t
      => predE (embedder (t, c)))
   && (fa (e:Expression, pS:Patterns, eS:Expressions)
         length pS = length eS
      && (fa(p) p in? pS => predP p)
      && (fa(e1) e1 in? eS => predE e1)
      => predE (cas (e, zip (pS, eS))))
   && (fa (vS:Variables, tS:Types, eS:Expressions, e:Expression)
         length vS  = length tS
      && (fa(t) t in? tS => predT t)
      && (fa(e1) e1 in? eS => predE e1)
      && predE e
      => predE (recursiveLet (zip (vS, tS), eS, e)))
   && (fa (p:Pattern, e:Expression, e1:Expression)
         predP p
      && predE e
      && predE e1
      => predE (nonRecursiveLet (p, e, e1)))

  %%%%% induction base and step for patterns:
   && (fa (v:Variable, t:Type)
         predT t
      => predP (variable (v, t)))
   && (fa (t:Type, c:Constructor)
         predT t
      => predP (embedding (t, c, None)))
   && (fa (t:Type, c:Constructor, p:Pattern)
         predT t
      && predP p
      => predP (embedding (t, c, Some p)))
   && (fa (fS:Fields, pS:Patterns)
         (fa(p) p in? pS => predP p)
      => predP (record (fS, pS)))
   && (fa (pS:Patterns)
         (fa(p) p in? pS => predP p)
      => predP (tuple pS))
   && (fa (v:Variable, t:Type, p:Pattern)
         predT t
      && predP p
      => predP (alias ((v, t), p)))

  %%%%% induction conclusion:
   => (fa(t) predT t)
   && (fa(e) predE e)
   && (fa(p) predP p)


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % more readable meta ops to construct types, expressions, and patterns:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


  (* The meta syntax to represent object syntax, as defined above, is not very
  readable. For instance, an equation is represented as `binary (equation, e1,
  e2)'. This readability problem is due to (1) the factoring of types and
  expressions (which is, on the other hand, convenient to process them; see
  spec `SyntacticOperations') and (2) prefix notation (vs. infix).

  So, we define some meta ops to construct types, expressions, and patterns in
  a more readable way. The names and fixities of these ops are meant to
  resemble object Metaslang syntax as much as possible, e.g. prefix `RELAX'
  for `relax' and infix `==' for `='. The relative priorities of the infix
  meta ops are the same as the relative priorities of their object
  counterparts (with an offset of 10). We also use currying as much as
  possible, to reduce the number of extra parentheses and commas and thus
  improve readability. *)

  % types:

  op BOOL : Type
  def BOOL = embed boolean

  op TVAR : TypeVariable -> Type
  def TVAR = embed variable

  op --> infixl 30 : Type * Type -> Type
  def --> = embed arrow

  op SUM : Constructors -> Type?s -> Type
  def SUM cS t?S = sum (cS, t?S)

  op TYPE : TypeName -> Types -> Type
  def TYPE tn tS = nary (instance tn, tS)

  op TYPEmt : TypeName -> Type  % for monomorphic types
  def TYPEmt tn = TYPE tn empty

  op TRECORD : Fields -> Types -> Type
  def TRECORD fS tS = nary (record fS, tS)

  op PRODUCT : Types -> Type
  def PRODUCT tS = nary (product, tS)

  op \\ infixl 30 : Type * Expression -> Type
     % can't use `||'
  def \\ (t,e) = subQuot (embed sub, t, e)

  op // infixl 30 : Type * Expression -> Type
  def // (t,e) = subQuot (quotien, t, e)

  % expressions:

  op VAR : Variable -> Expression
  def VAR v = nullary (variable v)

  op TRUE : Expression
  def TRUE = nullary tru

  op FALSE : Expression
  def FALSE = nullary fals

  op DOTr infixl 40 : Expression * Field -> Expression
  def DOTr (e,f) = unary (recordProjection f, e)

  op DOTt infixl 40 : Expression * PosNat -> Expression
  def DOTt (e,i) = unary (tupleProjection i, e)

  op RELAX : Expression -> Expression
  def RELAX r = unary (relaxator, r)

  op QUOTIENT : Expression -> Expression
  def QUOTIENT q = unary (quotienter, q)

  op ~~ : Expression -> Expression
  def ~~ e = unary (negation, e)

  op __ infixl 40 : Expression * Expression -> Expression
     % double underscore is incospicuous enough to look almost like blank
  def __ (e1,e2) = binary (application, e1, e2)

  op == infixl 30 : Expression * Expression -> Expression
  def == (e1,e2) = binary (equation, e1, e2)

  op =/= infixl 30 : Expression * Expression -> Expression
  def =/= (e1,e2) = binary (inequation, e1, e2)

  op <<< infixl 35 : Expression * Expression -> Expression
  def <<< (e1,e2) = binary (recordUpdate, e1, e2)

  op RESTRICT : Expression -> Expression -> Expression
  def RESTRICT r e = binary (restriction, r, e)

  op CHOOSE : Expression -> Expression -> Expression
  def CHOOSE q e = binary (choice, q, e)

  op &&& infixl 25 : Expression * Expression -> Expression
  def &&& (e1,e2) = binary (conjunction, e1, e2)

  op ||| infixl 24 : Expression * Expression -> Expression
  def ||| (e1,e2) = binary (disjunction, e1, e2)

  op ==> infixl 23 : Expression * Expression -> Expression
  def ==> (e1,e2) = binary (implication, e1, e2)

  op <==> infixl 22 : Expression * Expression -> Expression
  def <==> (e1,e2) = binary (equivalence, e1, e2)

  op IF : Expression -> Expression -> Expression -> Expression
  def IF e0 e1 e2 = ifThenElse (e0, e1, e2)

  op RECORD : Fields -> Expressions -> Expression
  def RECORD fS eS = nary (record fS, eS)

  op TUPLE : Expressions -> Expression
  def TUPLE eS = nary (tuple, eS)

  op PAIR : Expression -> Expression -> Expression
  def PAIR e1 e2 = TUPLE (e1 |> e2 |> empty)

  op FN : BoundVar -> Expression -> Expression
  def FN bv e = binding (abstraction, singleton bv, e)

  op FNN : BoundVars -> Expression -> Expression
  def FNN bvS e = binding (abstraction, bvS, e)

  op FA : BoundVar -> Expression -> Expression
  def FA bv e = binding (universal, singleton bv, e)

  op FAA : BoundVars -> Expression -> Expression
  def FAA bvS e = binding (universal, bvS, e)

  op EX : BoundVar -> Expression -> Expression
  def EX bv e = binding (existential, singleton bv, e)

  op EXX : BoundVars -> Expression -> Expression
  def EXX bvS e = binding (existential, bvS, e)

  op EX1 : BoundVar -> Expression -> Expression
  def EX1 bv e = binding (existential1, singleton bv, e)

  op EXX1 : BoundVars -> Expression -> Expression
  def EXX1 bvS e = binding (existential1, bvS, e)

  op OP : Operation -> Types -> Expression
  def OP o tS = opInstance(o,tS)

  op OPmt : Operation -> Expression  % for monomorphic ops
  def OPmt o = OP o empty

  op EMBED : Type -> Constructor -> Expression
  def EMBED t c = embedder (t, c)

  op CASE : Expression -> FSeq (Pattern * Expression) -> Expression
  def CASE e branches = cas (e, branches)

  op LETDEF : BoundVars -> Expressions -> Expression -> Expression
  def LETDEF bvS eS e = recursiveLet (bvS, eS, e)

  op LET : Pattern -> Expression -> Expression -> Expression
  def LET p e e1 = nonRecursiveLet (p, e, e1)

  % patterns:

  op PVAR : BoundVar -> Pattern
  def PVAR = embed variable

  op PEMBED0 : Type -> Constructor -> Pattern
  def PEMBED0 t c = embedding (t, c, None)

  op PEMBED : Type -> Constructor -> Pattern -> Pattern
  def PEMBED t c p = embedding (t, c, Some p)

  op PRECORD : Fields -> Patterns -> Pattern
  def PRECORD fS pS = record (fS, pS)

  op PTUPLE : Patterns -> Pattern
  def PTUPLE pS = tuple pS

  op AS infixl 30 : BoundVar * Pattern -> Pattern
  def AS (bv,p) = alias (bv, p)


  %%%%%%%%%%%
  % contexts:
  %%%%%%%%%%%

  (* Unlike LD, we do not require the type variables appearing in an op
  declaration, type definition, op definition, or axiom to be distinct. This
  requirement is captured in the inference rules for well-formed contexts, thus
  keeping the syntax simpler. *)

  type ContextElement =
    | typeDeclaration TypeName * Nat
    | opDeclaration   Operation * TypeVariables * Type
    | typeDefinition  TypeName * TypeVariables * Type
    | opDefinition    TypeVariables * Operation * Expression
    | axio(*m*)       AxiomName * TypeVariables * Expression
    | tVarDeclaration TypeVariable
    | varDeclaration  Variable * Type

  type Context = FSeq ContextElement


  %%%%%%%%
  % specs:
  %%%%%%%%

  % no top-level (type) variable declarations:
  op noVariables? : Context -> Boolean
  def noVariables? cx =
    ~(exists? (cx, embed? tVarDeclaration)) &&
    ~(exists? (cx, embed? varDeclaration))

  type Spec = (Context | noVariables?)


  %%%%%%%%%%%%%
  % judgements:
  %%%%%%%%%%%%%

  (* In LD, judgements are not syntactic entities, but just meta-statements
  that certain syntactic entities (contexts, types, etc.) belong to a certain
  relation (e.g. the binary relation (_ |- _ : TYPE) for well-formed types in
  context. Here, instead, we model judgements explicitly as syntactic
  entities. *)

  type Judgement =
    | wellFormedContext Context
    | wellFormedSpec    Spec
    | wellFormedType    Context * Type
    | typeEquivalence   Context * Type * Type
    | wellTypedExpr     Context * Expression * Type
    | wellTypedPatt     Context * Pattern    * Type
    | theore(*m*)       Context * Expression

endspec
