spec

  % API public all

  import Primitives

  (* As mentioned in spec Primitives, we add the distinguished fields and
  variables to the user ones via meta type sums.

  LD postulates "pi" names, indexed by positive natural numbers, to capture
  natural literal fields for product types. Since, as explained in README.txt,
  we avoid subtypes such as PosNat, we use integers.

  LD postulates "gamma", "psi", and "phi" names, used as bound variables in
  the expressions that define abbreviations. The "gamma" names may be primed,
  indexed by positive natural numbers, and indexed by (sequences of) variables
  and expressions. This variety is motivated by clarity of exposition in LD,
  but here it is sufficient to introduce variable names for abbreviations that
  are indexed by integers (again, we avoid naturals or positive naturals). *)

  type Field =
    | user UserField
    | prod Integer

  type Variable =
    | user UserVariable
    | abbr Integer

  % useful definitions:

  type TypeVariables = FSeq TypeVariable
  type Variables     = FSeq Variable
  type Fields        = FSeq Field
  type Constructors  = FSeq Constructor

  type Variable?     = Option Variable

  (* Types depend on expressions, which depend on types. So, we first declare
  the meta types for types and expressions, and then define them below. *)

  type Type        % defined below
  type Expression  % defined below

  % useful definitions:

  type Types  = FSeq Type
  type Type?  = Option Type
  type Type?s = FSeq Type?

  type Expressions = FSeq Expression

  (* Unlike LD, we do not impose certain requirements (e.g. that the fields of
  a record type must be distinct) in the syntax. We incorporate such
  requirements into the inference rules, thus keeping the syntax simpler.

  Another difference is that we factor fields/constructors separately from the
  component types of record/sum types, i.e. we have two sequences instead of a
  sequence of pairs. This makes the syntax a little simpler. The requirement
  that the two sequences have the same length are incorporated into the
  inference rules.

  A third difference is that here we explicitly model components of sum types
  that have no type (using Option), as opposed to implicitly assuming the
  empty record type as in LD. *)

  type Type =
    | BOOL                          % boolean
    | VAR    TypeVariable           % type variable
    | TYPE   TypeName * Types       % type instance
    | ARROW  Type * Type            % arrow type
    | RECORD Fields * Types         % record type
    | SUM    Constructors * Type?s  % sum type
    | RESTR  Type * Expression      % restriction type
    | QUOT   Type * Expression      % quotient type

  % infix arrow type constructor:
  op --> infixl 20 : Type * Type -> Type
  def --> = ARROW

  % infix restriction type constructor ("|" is disallowed):
  op \ infixl 30 : Type * Expression -> Type
  def \ = RESTR

  % infix quotient type constructor:
  op / infixl 30 : Type * Expression -> Type
  def / = QUOT

  (* Unlike LD, here projectors/embedders/quotienters/etc. are decorated by
  types, not necessarily record/sum/quotient types. Again, this keeps the
  syntax simpler. The inference rules require the decorating types to be of
  the appropriate form. *)

  type Expression =
    | VAR     Variable                              % variable
    | OPI     Operation * Types                     % op instance
    | APPLY   Expression * Expression               % application
    | FN      Variable * Type * Expression          % lambda abstraction
    | EQ      Expression * Expression               % equality
    | IF      Expression * Expression * Expression  % conditional
    | IOTA    Type                                  % descriptor
    | PROJECT Type * Field                          % projector
    | EMBED   Type * Constructor                    % embedder
    | QUOT    Type                                  % quotienter

  % infix application (we cannot use juxtaposition):
  op @ infixl 30 : Expression * Expression -> Expression
  def @ = APPLY

  % infix equality:
  op == infixl 29 : Expression * Expression -> Expression
  def == = EQ

  (* The recursive meta type definitions above only express fixpoints, not
  necessarily least ones. We enforce least ones by means of a (quite verbose)
  induction axiom on types and expressions. *)

  axiom induction_on_types_and_expressions is
    fa (predT : Type       -> Boolean,
        predE : Expression -> Boolean)
  %%%%% induction base and step:
   (fa (tn  : TypeName,
        o   : Operation,
        tv  : TypeVariable,
        v   : Variable,
        f   : Field,
        fS  : Fields,
        c   : Constructor,
        cS  : Constructors,
        t   : Type,
        t1  : Type,
        t2  : Type,
        tS  : Types,
        t?S : Type?s,
        e   : Expression,
        e0  : Expression,
        e1  : Expression,
        e2  : Expression,
        r   : Expression,
        q   : Expression)
         predT t
      && predT t1
      && predT t2
      && forall? predT tS
      && forall? predT (removeNones t?S)
      && predE e
      && predE e0
      && predE e1
      && predE e2
      && predE r
      && predE q
      => predT BOOL
      && predT (VAR tv)
      && predT (TYPE (tn, tS))
      && predT (t1 --> t2)
      && predT (RECORD (fS, tS))
      && predT (SUM (cS, t?S))
      && predT (t \ r)
      && predT (t / q)
      && predE (VAR v)
      && predE (OPI (o, tS))
      && predE (e1 @ e2)
      && predE (FN (v, t, e))
      && predE (e1 == e2)
      && predE (IF (e0, e1, e2))
      && predE (IOTA t)
      && predE (PROJECT (t, f))
      && predE (EMBED (t, c))
      && predE (QUOT t))
  %%%%% induction conclusion:
   => (fa(t) predT t)
   && (fa(e) predE e)

endspec
