spec

  import ../ProofChecker/Spec

  (* This spec defines an extension of types and expressions, in which the
  abbreviations defined in specs BasicAbbreviations and OtherAbbreviations are
  first-class (extended) types and expressions. Extended types and
  expressions, when printed, are more readable than the core types and
  expressions defined in spec TypesAndExpressions, in which all abbreviations
  are expanded.

  Why not use this extended syntax everywhere in the proof checker, instead of
  the core syntax with abbreviations? For greater simplicity. If we used the
  extended syntax defined in this spec in the proof checker, we would have to
  add inference rules for all the additional types and expressions. By
  defining abbreviations instead, we keep the logic simple and minimal, and we
  completely formalize the meaning of abbreviations by means of their
  definitions (in specs BasicAbbreviations and OtherAbbreviations).

  The constructors used in this spec are the same as the ones in spec
  TypesAndExpressions and as the ops in specs BasicAbbreviations and
  OtherAbbreviations, whenever possible. The only case in which it is not
  possible is when the ops in specs BasicAbbreviations and OtherAbbreviations
  are non-word symbols, which cannot be used as constructors. This is clearly
  indicated in the type definition below. *)

  type ExtType
  type ExtExpression

  type ExtTypes       = FSeq ExtType
  type ExtExpressions = FSeq ExtExpression

  % we need to extend binding branches too:
  type ExtBindingBranch =
       Variables * ExtTypes * ExtExpression * ExtExpression
  type ExtBindingBranches = NonEmptyFSeq ExtBindingBranch
       % since this type is private, we can use the subtype for non-empty
       % sequences (recall that we avoid subtypes in public ops)

  type ExtType =
    % core:
    | BOOL
    | VAR     TypeVariable
    | TYPE    TypeName * ExtTypes
    | ARROW   ExtType * ExtType
    | RECORD  Fields * ExtTypes
    | SUM     Constructors * ExtTypes
    | RESTR   ExtType * ExtExpression
    | QUOT    ExtType * ExtExpression
    % extension:
    | PRODUCT ExtTypes  % product type

  type ExtExpression =
    % core:
    | VAR     Variable
    | OPI     Operation * ExtTypes
    | APPLY   ExtExpression * ExtExpression
    | FN      Variable * ExtType * ExtExpression
    | EQ      ExtExpression * ExtExpression
    | IF      ExtExpression * ExtExpression * ExtExpression
    | IOTA    ExtType
    | PROJECT ExtType * Field
    | EMBED   ExtType * Constructor
    | QUOT    ExtType
    % extension:
    | TRUE
    | FALSE
    | NOT
    | NEG        ExtExpression  % cannot use "~~"
    | AND        ExtExpression * ExtExpression  % cannot use "&&&"
    | OR         ExtExpression * ExtExpression  % cannot use "|||"
    | IMPLIES    ExtExpression * ExtExpression  % cannot use "==>"
    | IFF
    | EQUIV      ExtExpression * ExtExpression  % cannot use "~=="
    | NEQ        ExtExpression * ExtExpression
    | THE        Variable * ExtType * ExtExpression
    | FAq        ExtType
    | FA         Variable * ExtType * ExtExpression
    | FAA        Variables * ExtTypes * ExtExpression
    | EXq        ExtType
    | EX         Variable * ExtType * ExtExpression
    | EXX        Variables * ExtTypes * ExtExpression
    | EX1q       ExtType
    | EX1        Variable * ExtType * ExtExpression
    | DOT        ExtExpression * ExtType * Field
    | RECC       Fields * ExtTypes
    | REC        Fields * ExtTypes * ExtExpressions
    | TUPLE      ExtTypes * ExtExpressions
    | RECUPDATER Fields * ExtTypes * Fields * ExtTypes * Fields * ExtTypes
    | RECUPDATE  Fields * ExtTypes * Fields * ExtTypes * Fields * ExtTypes *
                 ExtExpression * ExtExpression
    | LETSIMP    Variable * ExtType * ExtExpression * ExtExpression
    | COND       ExtType * ExtBindingBranches
    | CASE       ExtType * ExtType * ExtExpression * ExtBindingBranches
    | LET        ExtType * ExtType * Variables * ExtTypes *
                 ExtExpression * ExtExpression * ExtExpression
    | LETDEF     ExtType * Variables * ExtTypes * ExtExpressions * ExtExpression
    | CHOOSE     ExtType * ExtExpression * ExtType
    | EMBED?     Constructors * ExtTypes * Constructor

  axiom induction_on_extended_types_and_expressions is
    fa (predT : ExtType       -> Boolean,
        predE : ExtExpression -> Boolean)
  %%%%% induction base and step:
   (fa (tn  : TypeName,
        o   : Operation,
        tv  : TypeVariable,
        v   : Variable,
        vS  : Variables,
        f   : Field,
        fS  : Fields,
        fS1 : Fields,
        fS2 : Fields,
        c   : Constructor,
        cS  : Constructors,
        t   : ExtType,
        t1  : ExtType,
        t2  : ExtType,
        tS  : ExtTypes,
        tS1 : ExtTypes,
        tS2 : ExtTypes,
        e   : ExtExpression,
        e0  : ExtExpression,
        e1  : ExtExpression,
        e2  : ExtExpression,
        eS  : ExtExpressions,
        p   : ExtExpression,
        r   : ExtExpression,
        q   : ExtExpression,
        brS : ExtBindingBranches)
         predT t
      && predT t1
      && predT t2
      && forall? predT tS
      && predE e
      && predE e0
      && predE e1
      && predE e2
      && predE r
      && predE q
      && forall? (fn(br:ExtBindingBranch) -> let (vS, tS, p, e) = br in
                    forall? predT tS && predE p && predE e) brS
      => predT BOOL
      && predT (VAR tv)
      && predT (TYPE (tn, tS))
      && predT (ARROW (t1, t2))
      && predT (RECORD (fS, tS))
      && predT (SUM (cS, tS))
      && predT (RESTR (t, r))
      && predT (QUOT (t, q))
      && predT (embed PRODUCT tS)
      && predE (VAR v)
      && predE (OPI (o, tS))
      && predE (APPLY (e1, e2))
      && predE (FN (v, t, e))
      && predE (EQ (e1, e2))
      && predE (IF (e0, e1, e2))
      && predE (IOTA t)
      && predE (PROJECT (t, f))
      && predE (EMBED (t, c))
      && predE (QUOT t)
      && predE (embed TRUE)
      && predE (embed FALSE)
      && predE (embed NOT)
      && predE (NEG e)
      && predE (AND (e1, e2))
      && predE (OR (e1, e2))
      && predE (IMPLIES (e1, e2))
      && predE (embed IFF)
      && predE (EQUIV (e1, e2))
      && predE (NEQ (e1, e2))
      && predE (embed THE (v, t, e))
      && predE (embed FAq t)
      && predE (embed FA (v, t, e))
      && predE (embed FAA (vS, tS, e))
      && predE (embed EXq t)
      && predE (embed EX (v, t, e))
      && predE (embed EXX (vS, tS, e))
      && predE (embed EX1q t)
      && predE (embed EX1 (v, t, e))
      && predE (embed DOT (e, t, f))
      && predE (embed RECC (fS, tS))
      && predE (embed REC (fS, tS, eS))
      && predE (embed TUPLE (tS, eS))
      && predE (embed RECUPDATER (fS, tS, fS1, tS1, fS2, tS2))
      && predE (embed RECUPDATE (fS, tS, fS1, tS1, fS2, tS2, e1, e2))
      && predE (embed LETSIMP (v, t, e, e1))
      && predE (embed COND (t, brS))
      && predE (embed CASE (t, t1, e, brS))
      && predE (embed LET (t, t1, vS, tS, p, e, e1))
      && predE (embed LETDEF (t, vS, tS, eS, e))
      && predE (embed CHOOSE (t, e, t1))
      && predE (embed EMBED? (cS, tS, c)))
  %%%%% induction conclusion:
   => (fa(t) predT t)
   && (fa(e) predE e)

endspec
