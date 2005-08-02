spec

  % API public default

  import Occurrences

  (* While in LD a type substitution is described by a sequence of distinct
  type variables and a sequence of types of the same length, here we use a
  finite map from type variables to types, which is more convenient. *)

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
    | SUM(cS,tS)    -> SUM (cS, map (typeSubstInType sbs) tS)
    | RESTR(t,r)    -> RESTR (typeSubstInType sbs t, typeSubstInExpr sbs r)
    | QUOT(t,q)     -> QUOT (typeSubstInType sbs t, typeSubstInExpr sbs q)

  def typeSubstInExpr sbs = fn
    | VAR v              -> VAR v
    | OPI(o,tS)          -> OPI (o, map (typeSubstInType sbs) tS)
    | APPLY(e1,e2)       -> APPLY (typeSubstInExpr sbs e1,
                                   typeSubstInExpr sbs e2)
    | FN(v,t,e)          -> FN (v, typeSubstInType sbs t, typeSubstInExpr sbs e)
    | EQ(e1,e2)          -> EQ (typeSubstInExpr sbs e1,
                                typeSubstInExpr sbs e2)
    | IF(e0,e1,e2)       -> IF (typeSubstInExpr sbs e0,
                                typeSubstInExpr sbs e1,
                                typeSubstInExpr sbs e2)
    | IOTA t             -> IOTA (typeSubstInType sbs t)
    | PROJECT(t,f)       -> PROJECT (typeSubstInType sbs t, f)
    | EMBED(t,c)         -> EMBED (typeSubstInType sbs t, c)
    | QUOT t             -> QUOT (typeSubstInType sbs t)

  % true iff tsbs is substitution of tvS@i with tS@i:

  % API private
  op isTypeSubstFrom? : TypeSubstitution * TypeVariables * Types -> Boolean
  def isTypeSubstFrom?(tsbs,tvS,tS) =
    noRepetitions? tvS && length tvS = length tS && tsbs = fromSeqs (tvS, tS)

  % substitute variable with expression in expressions:

  op exprSubst : Variable -> Expression -> Expression -> Expression
  def exprSubst u d = fn
    | VAR v              -> if u = v then d else VAR v
    | APPLY(e1,e2)       -> APPLY (exprSubst u d e1, exprSubst u d e2)
    | FN(v,t,e)          -> if u = v then FN (v, t, e)
                            else FN (v, t, exprSubst u d e)
    | EQ(e1,e2)          -> EQ (exprSubst u d e1, exprSubst u d e2)
    | IF(e0,e1,e2)       -> IF (exprSubst u d e0,
                                exprSubst u d e1, exprSubst u d e2)
    | e                  -> e

  % variables captured at free occurrences of given variable in expression:

  % API private
  op captVars : Variable -> Expression -> FSet Variable
  def captVars u = fn
    | APPLY(e1,e2)       -> captVars u e1 \/ captVars u e2
    | FN(v,t,e)          -> if u in? (exprFreeVars e - v)
                            then captVars u e <| v
                            else empty
    | EQ(e1,e2)          -> captVars u e1 \/ captVars u e2
    | IF(e0,e1,e2)       -> captVars u e0 \/ captVars u e1 \/ captVars u e2
    | _                  -> empty

  % true iff substitution of u with d in e causes no variable capture:

  % API private
  op exprSubstOK? : Variable -> Expression -> Expression -> Boolean
  def exprSubstOK? u d e =
    exprFreeVars d /\ captVars u e = empty

endspec
