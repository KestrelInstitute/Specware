spec

  import Syntax, Positions


  % free variables in an expression:

  op exprFreeVars : Expression -> FSet Variable
  def exprFreeVars = fn
    | var v      -> single v
    | opp o      -> empty
    | app(e1,e2) -> exprFreeVars e1 \/ exprFreeVars e2
    | abs(v,t,e) -> exprFreeVars e - v
    | eq(e1,e2)  -> exprFreeVars e1 \/ exprFreeVars e2


  % ops in an expression:

  op exprOps : Expression -> FSet Operation
  def exprOps = fn
    | var v      -> empty
    | opp o      -> single o
    | app(e1,e2) -> exprOps e1 \/ exprOps e2
    | abs(v,t,e) -> exprOps e
    | eq(e1,e2)  -> exprOps e1 \/ exprOps e2


  % items declared or defined in a context:

  op contextElementTypes    : ContextElement -> FSet TypeName
  op contextElementOps      : ContextElement -> FSet Operation
  op contextElementVars     : ContextElement -> FSet Variable
  op contextElementAxioms   : ContextElement -> FSet AxiomName

  def contextElementTypes = fn
    | typeDeclaration tn -> single tn
    | _                  -> empty

  def contextElementOps = fn
    | opDeclaration(o,_) -> single o
    | _                  -> empty

  def contextElementVars = fn
    | varDeclaration(v,_) -> single v
    | _                   -> empty

  def contextElementAxioms = fn
    | axioM(an,_) -> single an
    | _           -> empty

  op contextTypes    : Context -> FSet TypeName
  op contextOps      : Context -> FSet Operation
  op contextVars     : Context -> FSet Variable
  op contextAxioms   : Context -> FSet AxiomName

  def contextTypes    cx = \\// (map contextElementTypes    cx)
  def contextOps      cx = \\// (map contextElementOps      cx)
  def contextVars     cx = \\// (map contextElementVars     cx)
  def contextAxioms   cx = \\// (map contextElementAxioms   cx)

  op contextDefinesType? : Context * TypeName -> Boolean
  def contextDefinesType?(cx,tn) =
    (ex (t:Type) typeDefinition (tn, t) in? cx)

  op contextDefinesOp? : Context * Operation -> Boolean
  def contextDefinesOp?(cx,o) =
    (ex (e:Expression) opDefinition (o, e) in? cx)


  % expression substitution:

  type ExprSubstitution = FMap (Variable, Expression)

  op exprSubst : ExprSubstitution -> Expression -> Expression
  def exprSubst sbs = fn
    | var v      -> if sbs definedAt v
                    then sbs @ v
                    else VAR v
    | opp o      -> OP o
    | app(e1,e2) -> exprSubst sbs e1 @ exprSubst sbs e2
    | abs(v,t,e) -> let bodySbs = sbs - v in
                    FN v t (exprSubst bodySbs e)
    | eq(e1,e2)  -> exprSubst sbs e1 == exprSubst sbs e2

  % abbreviation for replacing one variable with an expression:
  op exprSubst1 : Variable -> Expression -> Expression -> Expression
  def exprSubst1 v d e = exprSubst (single v d) e

  % captured variables at free occurrences of given variable:
  op captVars : Variable -> Expression -> FSet Variable
  def captVars u = fn
    | var v      -> empty
    | opp o      -> empty
    | app(e1,e2) -> captVars u e1 \/ captVars u e2
    | abs(v,t,e) -> if u in? exprFreeVars e && u ~= v
                    then (captVars u e) <| v
                    else empty
    | eq(e1,e2)  -> captVars u e1 \/ captVars u e2

  op exprSubstOK? : Expression * ExprSubstitution -> Boolean
  def exprSubstOK?(e,sbs) =
    (fa(v) v in? domain sbs =>
           exprFreeVars (sbs @ v) /\ captVars v e = empty)


  % positional type substitution:

  op isTypeSubstInTypeAt? :
     Type * Type * Type * Position * Type -> Boolean

  op isTypeSubstInExprAt? :
     Expression * Type * Type * Position * Expression -> Boolean

  def isTypeSubstInTypeAt? = min (fn isTypeSubstInTypeAt? ->
    (fa (old:Type, new:Type)
       isTypeSubstInTypeAt? (old, old, new, empty, new))
    &&
    (fa (old:Type, new:Type, pos:Position, t1:Type, t2:Type, newT1:Type)
       isTypeSubstInTypeAt? (t1, old, new, pos, newT1) =>
       isTypeSubstInTypeAt? (t1 --> t2, old, new, 1 |> pos,
                             newT1 --> t2))
    &&
    (fa (old:Type, new:Type, pos:Position, t1:Type, t2:Type, newT2:Type)
       isTypeSubstInTypeAt? (t2, old, new, pos, newT2) =>
       isTypeSubstInTypeAt? (t1 --> t2, old, new, 2 |> pos,
                             t1 --> newT2)))

  def isTypeSubstInExprAt? = min (fn isTypeSubstInExprAt? ->
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE1:Expression)
       isTypeSubstInExprAt? (e1, old, new, pos, newE1) =>
       isTypeSubstInExprAt? (e1 @ e2, old, new, 1 |> pos,
                             newE1 @ e2))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE2:Expression)
       isTypeSubstInExprAt? (e2, old, new, pos, newE2) =>
       isTypeSubstInExprAt? (e1 @ e2, old, new, 2 |> pos,
                             e1 @ newE2))
    &&
    (fa (old:Type, new:Type, pos:Position,
         v:Variable, t:Type, e:Expression, newT:Type)
       isTypeSubstInTypeAt? (t, old, new, pos, newT) =>
       isTypeSubstInExprAt? (FN v t e, old, new, 0 |> pos,
                             FN v newT e))
    &&
    (fa (old:Type, new:Type, pos:Position,
         v:Variable, t:Type, e:Expression, newE:Expression)
       isTypeSubstInExprAt? (e, old, new, pos, newE) =>
       isTypeSubstInExprAt? (FN v t e, old, new, 1 |> pos,
                             FN v t newE))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE1:Expression)
       isTypeSubstInExprAt? (e1, old, new, pos, newE1) =>
       isTypeSubstInExprAt? (e1 == e2, old, new, 1 |> pos,
                             newE1 == e2))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE2:Expression)
       isTypeSubstInExprAt? (e2, old, new, pos, newE2) =>
       isTypeSubstInExprAt? (e1 == e2, old, new, 2 |> pos,
                             e1 == newE2)))


  % positional expression substitution:

  op isExprSubstAt? :
     Expression * Expression * Expression * Position * Expression -> Boolean

  def isExprSubstAt? = min (fn isExprSubstAt? ->
    (fa (old:Expression, new:Expression)
       isExprSubstAt? (old, old, new, empty, new))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e1:Expression, e2:Expression, newE1:Expression)
       isExprSubstAt? (e1, old, new, pos, newE1) =>
       isExprSubstAt? (e1 @ e2, old, new, 1 |> pos,
                       newE1 @ e2))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e1:Expression, e2:Expression, newE2:Expression)
       isExprSubstAt? (e2, old, new, pos, newE2) =>
       isExprSubstAt? (e1 @ e2, old, new, 2 |> pos,
                       e1 @ newE2))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         v:Variable, t:Type, e:Expression, newE:Expression)
       isExprSubstAt? (e, old, new, pos, newE) =>
       isExprSubstAt? (FN v t e, old, new, 0 |> pos,
                       FN v t newE))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e1:Expression, e2:Expression, newE1:Expression)
       isExprSubstAt? (e1, old, new, pos, newE1) =>
       isExprSubstAt? (e1 == e2, old, new, 1 |> pos,
                       newE1 == e2))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e1:Expression, e2:Expression, newE2:Expression)
       isExprSubstAt? (e2, old, new, pos, newE2) =>
       isExprSubstAt? (e1 == e2, old, new, 2 |> pos,
                       e1 == newE2)))

  % valid position in expression:
  op positionInExpr? : Position * Expression -> Boolean
  def positionInExpr?(pos,e) =
    (ex (old:Expression, new:Expression, newE:Expression)
       isExprSubstAt? (e, old, new, pos, newE))

  % variables captured at position:
  op captVarsAt : ((Position * Expression) | positionInExpr?) -> FSet Variable
  def captVarsAt(pos,e) =
    if pos = empty then empty
    else let i = first pos in
         let pos = rtail pos in
         case e of
           | app(e1,e2) -> if i = 1 then captVarsAt(pos,e1)
                           else (assert (i = 2); captVarsAt(pos,e2))
           | abs(v,t,e) -> (assert (i = 0); captVarsAt(pos,e) <| v)
           | eq(e1,e2)  -> if i = 1 then captVarsAt(pos,e1)
                           else (assert (i = 2); captVarsAt(pos,e2))

  op exprSubstAtOK? : Expression * Expression * Expression * Position -> Boolean
  def exprSubstAtOK?(e,old,new,pos) =
    (ex (newE:Expression)
       isExprSubstAt? (e, old, new, pos, newE) &&
       exprFreeVars old /\ captVarsAt(pos,e) = empty &&
       exprFreeVars new /\ captVarsAt(pos,e) = empty)


  % abbreviations:

  % return some variable not in set of used ones:
  op pickUnusedVar : FSet Variable -> Variable
  axiom pickUnusedVar is
    fa(vS:FSet Variable) (pickUnusedVar vS) nin? vS

  op TRUE : Expression
  def TRUE =
    let v:Variable = pickUnusedVar empty in
    FN v boolean (var v) == FN v boolean (var v)

  op FALSE : Expression
  def FALSE =
    let v:Variable = pickUnusedVar empty in
    FN v boolean (var v) == FN v boolean TRUE

  op ~~ : Expression -> Expression
  def ~~ e = (e == FALSE)

  op FA : Variable -> Type -> Expression -> Expression
  def FA v t e = (FN v t e == FN v t TRUE)

  op EX : Variable -> Type -> Expression -> Expression
  def EX v t e = ~~ (FA v t (~~e))

  op &&& infixr 25 : Expression * Expression -> Expression
  def &&& (e1,e2) =
    let v:Variable = pickUnusedVar (exprFreeVars e1 \/ exprFreeVars e2) in
    (FA v (boolean --> boolean --> boolean)
       (var v @ TRUE @ TRUE == var v @ e1 @ e2))
    ==
    TRUE

  op ||| infixr 24 : Expression * Expression -> Expression
  def ||| (e1,e2) = ~~ (~~e1 &&& ~~e2)

  op ==> infixr 23 : Expression * Expression -> Expression
  def ==> (e1,e2) = ~~e1 ||| e2

  op <==> infixr 22 : Expression * Expression -> Expression
  def <==> (e1,e2) = (e1 == e2)

  op EX1 : Variable -> Type -> Expression -> Expression
  def EX1 v t e =
    let v1:Variable = pickUnusedVar (exprFreeVars e <| v) in
    let e1 = exprSubst1 v (var v1) e in
    EX v t (e &&& FA v1 t (e1 ==> var v1 == var v))

endspec
