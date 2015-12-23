(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

MetaslangProofChecker qualifying
spec

  % API public default

  import Occurrences

  type TypeSubstitution = FMap (TypeVariable, Type)

  % substitute type variables with types in types and expressions:

  op typeSubstInType : TypeSubstitution -> Type       -> Type
  op typeSubstInExpr : TypeSubstitution -> Expression -> Expression

  def typeSubstInType sbs = fn
    | BOOL          -> BOOL
    | VAR tv        -> if sbs definedAt tv then sbs @ tv else VAR tv
    | TYPE(tn,tS)   -> TYPE (tn, map (typeSubstInType sbs) tS)
    | ARROW(t1,t2)  -> ARROW (typeSubstInType sbs t1, typeSubstInType sbs t2)
    | RECORD(fS,tS) -> RECORD (fS, map (typeSubstInType sbs) tS)
    | RESTR(t,r)    -> RESTR (typeSubstInType sbs t, typeSubstInExpr sbs r)

  def typeSubstInExpr sbs = fn
    | VAR v        -> VAR v
    | OPI(o,tS)    -> OPI (o, map (typeSubstInType sbs) tS)
    | APPLY(e1,e2) -> APPLY (typeSubstInExpr sbs e1, typeSubstInExpr sbs e2)
    | FN(v,t,e)    -> FN (v, typeSubstInType sbs t, typeSubstInExpr sbs e)
    | EQ(e1,e2)    -> EQ (typeSubstInExpr sbs e1, typeSubstInExpr sbs e2)
    | IF(e0,e1,e2) -> IF (typeSubstInExpr sbs e0,
                          typeSubstInExpr sbs e1,
                          typeSubstInExpr sbs e2)
    | IOTA t       -> IOTA (typeSubstInType sbs t)
    | PROJECT(t,f) -> PROJECT (typeSubstInType sbs t, f)

  % true iff tsbs is substitution of tvS@i with tS@i:

  % API private
  op isTypeSubstFrom? : TypeSubstitution * TypeVariables * Types -> Bool
  def isTypeSubstFrom?(tsbs,tvS,tS) =
    noRepetitions? tvS && length tvS = length tS && tsbs = fromLists (tvS, tS)

  % substitute variable with expression in expressions:

  op exprSubst : Variable -> Expression -> Expression -> Expression
  def exprSubst u d = fn
    | VAR v        -> if u = v then d else VAR v
    | APPLY(e1,e2) -> APPLY (exprSubst u d e1, exprSubst u d e2)
    | FN(v,t,e)    -> if u = v then FN (v, t, e)
                      else FN (v, t, exprSubst u d e)
    | EQ(e1,e2)    -> EQ (exprSubst u d e1, exprSubst u d e2)
    | IF(e0,e1,e2) -> IF (exprSubst u d e0, exprSubst u d e1, exprSubst u d e2)
    | e            -> e

  % variables captured at free occurrences of given variable in expression:

  % API private
  op captVars : Variable -> Expression -> FSet Variable
  def captVars u = fn
    | APPLY(e1,e2) -> captVars u e1 \/ captVars u e2
    | FN(v,t,e)    -> if u in? (exprFreeVars e - v)
                      then captVars u e <| v
                      else empty
    | EQ(e1,e2)    -> captVars u e1 \/ captVars u e2
    | IF(e0,e1,e2) -> captVars u e0 \/ captVars u e1 \/ captVars u e2
    | _            -> empty

  % true iff substitution of u with d in e causes no variable capture:

  % API private
  op exprSubstOK? : Variable -> Expression -> Expression -> Bool
  def exprSubstOK? u d e =
    exprFreeVars d /\ captVars u e = empty

  (* The following ops replace an expression d1 with an expression d2 in a
  type or expression. These ops are implicit in LD (in the definition of
  certain abbreviations), but of course need to be made explicit here.

  Note that op exprSubst defined above is not quite a special case of op
  exprSubstInExpr because the latter (1) applies the substitution to all
  bodies of lambda abstractions regardless of whether the bound variables
  (wrapped by VAR) coincide with d1 and (2) applies the substitution to the
  types that occur in expressions. *)

  op exprSubstInType : Expression -> Expression -> Type       -> Type
  op exprSubstInExpr : Expression -> Expression -> Expression -> Expression

  def exprSubstInType d1 d2 = fn
    | BOOL          -> BOOL
    | VAR tv        -> VAR tv
    | TYPE(tn,tS)   -> TYPE (tn, map (exprSubstInType d1 d2) tS)
    | ARROW(t1,t2)  -> ARROW (exprSubstInType d1 d2 t1, exprSubstInType d1 d2 t2)
    | RECORD(fS,tS) -> RECORD (fS, map (exprSubstInType d1 d2) tS)
    | RESTR(t,r)    -> RESTR (exprSubstInType d1 d2 t, exprSubstInExpr d1 d2 r)

  def exprSubstInExpr d1 d2 e =
    if e = d1 then d2 else
    case e of
    | VAR v        -> VAR v
    | OPI(o,tS)    -> OPI (o, map (exprSubstInType d1 d2) tS)
    | APPLY(e1,e2) -> APPLY (exprSubstInExpr d1 d2 e1, exprSubstInExpr d1 d2 e2)
    | FN(v,t,e)    -> FN (v, exprSubstInType d1 d2 t, exprSubstInExpr d1 d2 e)
    | EQ(e1,e2)    -> EQ (exprSubstInExpr d1 d2 e1, exprSubstInExpr d1 d2 e2)
    | IF(e0,e1,e2) -> IF (exprSubstInExpr d1 d2 e0,
                          exprSubstInExpr d1 d2 e1,
                          exprSubstInExpr d1 d2 e2)
    | IOTA t       -> IOTA (exprSubstInType d1 d2 t)
    | PROJECT(t,f) -> PROJECT (exprSubstInType d1 d2 t, f)

endspec
