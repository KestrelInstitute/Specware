(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

MetaslangProofChecker qualifying
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
  indexed by positive natural numbers, and indexed by variables and
  expressions. This variety is motivated by clarity of exposition in LD, but
  here it is sufficient to introduce variable names for abbreviations that are
  indexed by integers (again, we avoid naturals or positive naturals). *)

  type Field =
    | user UserField
    | prod Int

  type Variable =
    | user UserVariable
    | abbr Int

  % useful definitions:
  type Operations    = List Operation
  type TypeVariables = List TypeVariable
  type Variables     = List Variable
  type Fields        = List Field
  type AxiomNames    = List AxiomName

  (* Types depend on expressions, which depend on types. So, we first declare
  the meta types for types and expressions, and then define them below. *)

  type Type        % defined below
  type Expression  % defined below

  % useful definitions:
  type Types       = List Type
  type Expressions = List Expression

  (* Unlike LD, we do not impose certain requirements (e.g. that the fields of
  a record type must be distinct) in the syntax. We incorporate such
  requirements into the inference rules, thus keeping the syntax simpler and
  avoiding subtypes, as explained in README.txt.

  Another difference with LD is that we factor fields separately from the
  component types of record types, i.e. we have two sequences instead of a
  sequence of pairs. This makes the syntax a little simpler. The requirement
  that the two sequences have the same length are incorporated into the
  inference rules. *)

  type Type =
    | BOOL                      % boolean
    | VAR    TypeVariable       % type variable
    | TYPE   TypeName * Types   % type instance
    | ARROW  Type * Type        % arrow type
    | RECORD Fields * Types     % record type
    | RESTR  Type * Expression  % restriction type

  % infix arrow type constructor:
  op --> infixl 20 : Type * Type -> Type
  def --> = ARROW

  % infix restriction type constructor ("|" is disallowed):
  op \ infixl 30 : Type * Expression -> Type
  def \ = RESTR

  (* Unlike LD, here projectors are decorated by types, not necessarily record
  types. Again, this keeps the syntax simpler. The inference rules require the
  decorating types to be of the appropriate form. *)

  type Expression =
    | VAR     Variable                              % variable
    | OPI     Operation * Types                     % op instance
    | APPLY   Expression * Expression               % application
    | FN      Variable * Type * Expression          % lambda abstraction
    | EQ      Expression * Expression               % equality
    | IF      Expression * Expression * Expression  % conditional
    | IOTA    Type                                  % descriptor
    | PROJECT Type * Field                          % projector

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
    fa (predT : Type       -> Bool,
        predE : Expression -> Bool)
  %%%%% induction base and step:
   (fa (tn  : TypeName,
        o   : Operation,
        tv  : TypeVariable,
        v   : Variable,
        f   : Field,
        fS  : Fields,
        t   : Type,
        t1  : Type,
        t2  : Type,
        tS  : Types,
        e   : Expression,
        e0  : Expression,
        e1  : Expression,
        e2  : Expression,
        r   : Expression)
         predT t
      && predT t1
      && predT t2
      && forall? predT tS
      && predE e
      && predE e0
      && predE e1
      && predE e2
      && predE r
      => predT BOOL
      && predT (VAR tv)
      && predT (TYPE (tn, tS))
      && predT (t1 --> t2)
      && predT (RECORD (fS, tS))
      && predT (t \ r)
      && predE (VAR v)
      && predE (OPI (o, tS))
      && predE (e1 @ e2)
      && predE (FN (v, t, e))
      && predE (e1 == e2)
      && predE (IF (e0, e1, e2))
      && predE (IOTA t)
      && predE (PROJECT (t, f)))
  %%%%% induction conclusion:
   => (fa(t) predT t)
   && (fa(e) predE e)

endspec
