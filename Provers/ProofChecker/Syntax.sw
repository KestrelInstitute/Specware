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

  type Type?       = Option Type
  type Expression? = Option Expression
  type Pattern?    = Option Pattern

  type Types       = FSeq Type
  type Expressions = FSeq Expression
  type Patterns    = FSeq Pattern
  type Type?s      = FSeq Type?


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
    | quotienT

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
    | truE
    | falsE

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
    | binding         BindingExprOperator * Variables * Types * Expression
    | opInstance      Operation * Types
    | embedder        Type * Constructor
    | casE            Expression * Patterns * Expressions
    | recursiveLet    Variables * Types * Expressions * Expression
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
    | variable  Variable * Type
    | embedding Type * Constructor * Pattern?
    | record    Fields * Patterns
    | tuple     Patterns
    | alias     Variable * Type * Pattern


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
   && (fa (tv:TypeVariable)
         predT (variable tv))
   && (fa (t1:Type, t2:Type)
         predT t1 && predT t2
      => predT (arrow (t1, t2)))
   && (fa (cS:Constructors, t?S:Type?s)
         forall? (removeNones t?S, predT)
      => predT (sum (cS, t?S)))
   && (fa (tc:NaryTypeConstruct, tS:Types)
         forall? (tS, predT)
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
         forall? (eS, predE)
      => predE (nary (eo, eS)))
   && (fa (eo:BindingExprOperator, vS:Variables, tS:Types, e:Expression)
         length vS = length tS
      && forall? (tS, predT)
      && predE e
      => predE (binding (eo, vS, tS, e)))
   && (fa (o:Operation, tS:Types)
         forall? (tS, predT)
      => predE (opInstance (o, tS)))
   && (fa (t:Type, c:Constructor)
         predT t
      => predE (embedder (t, c)))
   && (fa (e:Expression, pS:Patterns, eS:Expressions)
         predE e
      && forall? (pS, predP)
      && forall? (eS, predE)
      => predE (casE (e, pS, eS)))
   && (fa (vS:Variables, tS:Types, eS:Expressions, e:Expression)
         length vS  = length tS
      && forall? (tS, predT)
      && forall? (eS, predE)
      && predE e
      => predE (recursiveLet (vS, tS, eS, e)))
   && (fa (p:Pattern, e:Expression, e1:Expression)
         predP p
      && predE e
      && predE e1
      => predE (nonRecursiveLet (p, e, e1)))

  %%%%% induction base and step for patterns:
   && (fa (v:Variable, t:Type)
         predT t
      => predP (variable (v,t)))
   && (fa (t:Type, c:Constructor)
         predT t
      => predP (embedding (t, c, None)))
   && (fa (t:Type, c:Constructor, p:Pattern)
         predT t
      && predP p
      => predP (embedding (t, c, Some p)))
   && (fa (fS:Fields, pS:Patterns)
         forall? (pS, predP)
      => predP (record (fS, pS)))
   && (fa (pS:Patterns)
         forall? (pS, predP)
      => predP (tuple pS))
   && (fa (v:Variable, t:Type, p:Pattern)
         predT t
      && predP p
      => predP (alias (v, t, p)))

  %%%%% induction conclusion:
   => (fa(t) predT t)
   && (fa(e) predE e)
   && (fa(p) predP p)


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % more readable types, expressions, and patterns:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* The meta syntax to represent object syntax, as defined above, is not very
  readable. For instance, an equation is represented as `binary (equation, e1,
  e2)'. This readability problem is due to (1) the factoring of types and
  expressions (which is, on the other hand, convenient to process them,
  e.g. to collect free variables from expressions) and (2) prefix notation
  (vs. infix).

  So, we define some meta ops to construct types, expressions, and patterns in
  a more readable way. The names and fixities of these ops are meant to
  resemble object Metaslang syntax as much as possible, e.g. prefix `RELAX'
  for `relax' and infix `==' for `='. The priorities of the infix meta ops are
  the same as the relative priorities of their object counterparts. We also
  use currying as much as possible, to reduce the number of extra parentheses
  and commas and thus improve readability. *)

  % types:

  op BOOL : Type
  def BOOL = boolean

  op TVAR : TypeVariable -> Type
  def TVAR = variable

  op --> infixl 20 : Type * Type -> Type
  def --> = arrow

  op SUM : Constructors -> Type?s -> Type
  def SUM cS t?S = sum (cS, t?S)

  op TYPE : TypeName -> Types -> Type
  def TYPE tn tS = nary (instance tn, tS)

  op TYP : TypeName -> Type  % for monomorphic types
  def TYP tn = TYPE tn empty

  op TRECORD : Fields -> Types -> Type
  def TRECORD fS tS = nary (record fS, tS)

  op PRODUCT : Types -> Type
  def PRODUCT tS = nary (product, tS)

  op \ infixl 30 : Type * Expression -> Type
     % `|' causes syntax error
  def \ (t,e) = subQuot (embed sub, t, e)
                         % without `embed', type checker complains

  op / infixl 30 : Type * Expression -> Type
  def / (t,e) = subQuot (quotienT, t, e)

  % expressions:

  op VAR : Variable -> Expression
  def VAR v = nullary (variable v)

  op TRUE : Expression
  def TRUE = nullary truE

  op FALSE : Expression
  def FALSE = nullary falsE

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

  op @ infixl 30 : Expression * Expression -> Expression
  def @ (e1,e2) = binary (application, e1, e2)

  op == infixl 20 : Expression * Expression -> Expression
  def == (e1,e2) = binary (equation, e1, e2)

  op ~== infixl 20 : Expression * Expression -> Expression
  def ~== (e1,e2) = binary (inequation, e1, e2)

  op <<< infixl 25 : Expression * Expression -> Expression
  def <<< (e1,e2) = binary (recordUpdate, e1, e2)

  op RESTRICT : Expression -> Expression -> Expression
  def RESTRICT r e = binary (restriction, r, e)

  op CHOOSE : Expression -> Expression -> Expression
  def CHOOSE q e = binary (choice, q, e)

  op &&& infixl 15 : Expression * Expression -> Expression
  def &&& (e1,e2) = binary (conjunction, e1, e2)

  op ||| infixl 14 : Expression * Expression -> Expression
  def ||| (e1,e2) = binary (disjunction, e1, e2)

  op ==> infixl 13 : Expression * Expression -> Expression
  def ==> (e1,e2) = binary (implication, e1, e2)

  op <==> infixl 12 : Expression * Expression -> Expression
  def <==> (e1,e2) = binary (equivalence, e1, e2)

  op IF : Expression -> Expression -> Expression -> Expression
  def IF e0 e1 e2 = ifThenElse (e0, e1, e2)

  op RECORD : Fields -> Expressions -> Expression
  def RECORD fS eS = nary (record fS, eS)

  op TUPLE : Expressions -> Expression
  def TUPLE eS = nary (tuple, eS)

  op PAIR : Expression -> Expression -> Expression
  def PAIR e1 e2 = TUPLE (seq2 (e1, e2))

  op FN : Variable -> Type -> Expression -> Expression
  def FN v t e = binding (abstraction, singleton v, singleton t, e)

  op FNN : Variables -> Types -> Expression -> Expression
  def FNN vS tS e = binding (abstraction, vS, tS, e)

  op FA : Variable -> Type -> Expression -> Expression
  def FA v t e = binding (universal, singleton v, singleton t, e)

  op FAA : Variables -> Types -> Expression -> Expression
  def FAA vS tS e = binding (universal, vS, tS, e)

  op EX : Variable -> Type -> Expression -> Expression
  def EX v t e = binding (existential, singleton v, singleton t, e)

  op EXX : Variables -> Types -> Expression -> Expression
  def EXX vS tS e = binding (existential, vS, tS, e)

  op EX1 : Variable -> Type -> Expression -> Expression
  def EX1 v t e = binding (existential1, singleton v, singleton t, e)

  op EXX1 : Variables -> Types -> Expression -> Expression
  def EXX1 vS tS e = binding (existential1, vS, tS, e)

  op OPP : Operation -> Types -> Expression
  def OPP o tS = opInstance(o,tS)

  op OP : Operation -> Expression  % for monomorphic ops
  def OP o = OPP o empty

  op EMBED : Type -> Constructor -> Expression
  def EMBED t c = embedder (t, c)

  op CASE : Expression -> Patterns -> Expressions -> Expression
  def CASE e pS eS = casE (e, pS, eS)

  op LETDEF : Variables -> Types -> Expressions -> Expression -> Expression
  def LETDEF vS tS eS e = recursiveLet (vS, tS, eS, e)

  op LET : Pattern -> Expression -> Expression -> Expression
  def LET p e e1 = nonRecursiveLet (p, e, e1)

  % patterns:

  op PVAR : Variable -> Type -> Pattern
  def PVAR v t = variable (v, t)

  op PEMBE : Type -> Constructor -> Pattern
  def PEMBE t c = embedding (t, c, None)

  op PEMBED : Type -> Constructor -> Pattern -> Pattern
  def PEMBED t c p = embedding (t, c, Some p)

  op PRECORD : Fields -> Patterns -> Pattern
  def PRECORD fS pS = record (fS, pS)

  op PTUPLE : Patterns -> Pattern
  def PTUPLE pS = tuple pS

  op AS : Variable -> Type -> Pattern -> Pattern
  def AS v t p = alias (v, t, p)


  %%%%%%%%%%%
  % contexts:
  %%%%%%%%%%%

  (* Unlike LD, we do not require the type variables appearing in an op
  declaration, type definition, op definition, or axiom to be distinct. This
  requirement is captured in the inference rules for well-formed contexts, thus
  keeping the syntax simpler. *)

  type ContextElement =
    | typeDeclaration    TypeName * Nat
    | opDeclaration      Operation * TypeVariables * Type
    | typeDefinition     TypeName * TypeVariables * Type
    | opDefinition       Operation * TypeVariables * Expression
    | axioM              AxiomName * TypeVariables * Expression
    | typeVarDeclaration TypeVariable
    | varDeclaration     Variable * Type

  type Context = FSeq ContextElement


  %%%%%%%%
  % specs:
  %%%%%%%%

  op contextWithoutTypeVarOrVarDeclarations? : Context -> Boolean
  def contextWithoutTypeVarOrVarDeclarations? cx =
    ~(exists? (cx, embed? typeVarDeclaration)) &&
    ~(exists? (cx, embed? varDeclaration))

  type Spec = (Context | contextWithoutTypeVarOrVarDeclarations?)


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
    | theoreM           Context * Expression

endspec
