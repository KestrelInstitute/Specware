(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

ProofDebugger qualifying
spec

  % API public all

  import ProofChecker#Spec

  (* This spec defines an extension of the core types and expressions used by
  the proof checker. In this extension, abbreviations such as TRUE are
  first-class types and expressions. Extended types and expressions, when
  printed, are more readable than the core types and expressions of the proof
  checker, into which all abbreviations are expanded.

  Why not use this extended syntax also in the proof checker, instead of the
  core syntax with abbreviations? For greater simplicity. If we used the
  extended syntax defined in this spec in the proof checker, we would have to
  add inference rules for all the additional types and expressions. By
  defining abbreviations instead, we keep the logic simple and minimal, and we
  completely formalize the meaning of abbreviations by means of their
  definitions.

  The constructors used in this spec are the same as the constructors of the
  core types and expressions (e.g. VAR) and the ops that define the
  abbreviations (e.g. TRUE), whenever possible. The only cases in which this
  is not possible is when the ops that define the abbreviations are non-word
  symbols (e.g. &&&), which cannot be used as constructors. These cases are
  clearly indicated in the type definition below. *)

  type ExtType
  type ExtExpression

  type ExtTypes       = List ExtType
  type ExtExpressions = List ExtExpression

  % we need to extend binding branches too:
  type ExtBindingBranch =
       Variables * ExtTypes * ExtExpression * ExtExpression
  type ExtBindingBranches = List ExtBindingBranch

  type ExtType =
    % core:
    | BOOL
    | VAR     TypeVariable
    | TYPE    TypeName * ExtTypes
    | ARROW   ExtType * ExtType
    | RECORD  Fields * ExtTypes
    | RESTR   ExtType * ExtExpression
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
    % extension:
    | TRUE
    | FALSE
    | NOT
    | NEG        ExtExpression  % cannot use "~~"
    | AND        ExtExpression * ExtExpression  % cannot use "&&&"
    | OR         ExtExpression * ExtExpression  % cannot use "|||"
    | IMPLIES    ExtExpression * ExtExpression  % cannot use "==>"
    | IFF
    | EQV        ExtExpression * ExtExpression  % cannot use "~=="
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
    | COND       ExtType * ExtBindingBranches
    | CASE       ExtType * ExtType * ExtExpression * ExtBindingBranches
    | LET        ExtType * ExtType * Variables * ExtTypes *
                 ExtExpression * ExtExpression * ExtExpression
    | LETSIMP    ExtType * Variable * ExtType * ExtExpression * ExtExpression
    | LETDEF     ExtType * Variables * ExtTypes * ExtExpressions * ExtExpression

  axiom induction_on_extended_types_and_expressions is
    fa (predT : ExtType       -> Bool,
        predE : ExtExpression -> Bool)
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
      && forall? (fn(br:ExtBindingBranch) -> let (vS, tS, p, e) = br in
                    forall? predT tS && predE p && predE e) brS
      => predT BOOL
      && predT (VAR tv)
      && predT (TYPE (tn, tS))
      && predT (ARROW (t1, t2))
      && predT (RECORD (fS, tS))
      && predT (RESTR (t, r))
      && predT (embed PRODUCT tS)
      && predE (VAR v)
      && predE (OPI (o, tS))
      && predE (APPLY (e1, e2))
      && predE (FN (v, t, e))
      && predE (EQ (e1, e2))
      && predE (IF (e0, e1, e2))
      && predE (IOTA t)
      && predE (PROJECT (t, f))
      && predE (embed TRUE)
      && predE (embed FALSE)
      && predE (embed NOT)
      && predE (NEG e)
      && predE (AND (e1, e2))
      && predE (OR (e1, e2))
      && predE (IMPLIES (e1, e2))
      && predE (embed IFF)
      && predE (EQV (e1, e2))
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
      && predE (embed COND (t, brS))
      && predE (embed CASE (t, t1, e, brS))
      && predE (embed LET (t, t1, vS, tS, p, e, e1))
      && predE (embed LETSIMP (t1, v, t, e, e1))
      && predE (embed LETDEF (t, vS, tS, eS, e)))
  %%%%% induction conclusion:
   => (fa(t) predT t)
   && (fa(e) predE e)

  % free variables in extended expressions and binding branches:

  op exprFreeVars   : ExtExpression    -> FSet Variable
  op branchFreeVars : ExtBindingBranch -> FSet Variable

  def exprFreeVars = fn
    | VAR v          -> single v
    | APPLY(e1,e2)   -> exprFreeVars e1 \/ exprFreeVars e2
    | FN(v,t,e)      -> exprFreeVars e -- single v
    | EQ(e1,e2)      -> exprFreeVars e1 \/ exprFreeVars e2
    | IF(e0,e1,e2)   -> exprFreeVars e0 \/ exprFreeVars e1 \/ exprFreeVars e2
    | NEG e          -> exprFreeVars e
    | AND    (e1,e2) -> exprFreeVars e1 \/ exprFreeVars e2
    | OR     (e1,e2) -> exprFreeVars e1 \/ exprFreeVars e2
    | IMPLIES(e1,e2) -> exprFreeVars e1 \/ exprFreeVars e2
    | EQV    (e1,e2) -> exprFreeVars e1 \/ exprFreeVars e2
    | NEQ    (e1,e2) -> exprFreeVars e1 \/ exprFreeVars e2
    | THE(v,t,e)     -> exprFreeVars e -- single v
    | FA(v,t,e)      -> exprFreeVars e -- single v
    | FAA(vS,tS,e)   -> exprFreeVars e -- toSet vS
    | EX(v,t,e)      -> exprFreeVars e -- single v
    | EXX(vS,tS,e)   -> exprFreeVars e -- toSet vS
    | EX1(v,t,e)     -> exprFreeVars e -- single v
    | DOT(e,t,f)     -> exprFreeVars e
    | REC(fS,tS,eS)  -> \\// (map exprFreeVars eS)
    | TUPLE(tS,eS)   -> \\// (map exprFreeVars eS)
    | RECUPDATE(fS,tS,fS1,tS1,fS2,tS2,e1,e2) -> exprFreeVars e1 \/
                                                exprFreeVars e2
    | COND(t,brS)            -> \\// (map branchFreeVars brS)
    | CASE(t,t1,e,brS)       -> exprFreeVars e \/
                                \\// (map branchFreeVars brS)
    | LET(t,t1,vS,tS,p,e,e1) -> exprFreeVars e \/
                                ((exprFreeVars p \/ exprFreeVars e1)
                                 -- toSet vS)
    | LETSIMP(t1,v,t,e,e1)   -> exprFreeVars e \/ (exprFreeVars e1 -- single v)
    | LETDEF(t,vS,tS,eS,e)   -> exprFreeVars e \/
                                (\\// (map exprFreeVars eS) -- toSet vS)
    | _                      -> empty

  def branchFreeVars (vS,_(*ts*),e1,e2) =
    (exprFreeVars e1 \/ exprFreeVars e2) -- toSet vS

endspec
