spec

  (* Types depend on expressions, which depend on types and patterns, which
  depend on types. So, we define (meta) types for these syntactic entities all
  together in this spec, along with auxiliary types and ops. *)


  import Primitives

  type Variables    = FSeq Variable
  type Fields       = FSeq Field
  type Constructors = FSeq Constructor


  type Type        % defined below
  type Expression  % defined below
  type Pattern     % defined below

  type Types       = FSeq Type
  type Expressions = FSeq Expression
  type Patterns    = FSeq Pattern


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

  type Type? = Option Type
  type Type?s = FSeq Type?

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
    | tupleProjection  Nat
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

  type BoundVar  = Variable * Type
  type BoundVars = FSeq BoundVar

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
  type of an embedding pattern to be a sum type. *)

  type Pattern =
    | variable  BoundVar
    | embedding Type * Constructor * Pattern
    | record    Fields * Patterns
    | alias     BoundVar * Pattern


  %%%%%%%%%%%%
  % induction:
  %%%%%%%%%%%%

  (* The (meta) type definitions above only express fixpoints, not necessarily
  least ones. We enforce least ones by means of a (quite verbose) induction
  axiom on types, expressions, and patterns. *)

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
   && (fa (t:Type, c:Constructor, p:Pattern)
         predT t
      && predP p
      => predP (embedding (t, c, p)))
   && (fa (fS:Fields, pS:Patterns)
         (fa(p) p in? pS => predP p)
      => predP (record (fS, pS)))
   && (fa (v:Variable, t:Type, p:Pattern)
         predT t
      && predP p
      => predP (alias ((v, t), p)))
  %%%%% induction conclusion:
   => (fa(t) predT t)
   && (fa(e) predE e)
   && (fa(p) predP p)

endspec
