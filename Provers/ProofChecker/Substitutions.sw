spec

  import OccurrenceCollectors


  %%%%%%%%%%%%%%%%%%%%%
  % type substitutions:
  %%%%%%%%%%%%%%%%%%%%%

  (* While in LD substitutions are describes by a sequence of type variables
  and a sequence of types of the same length, here we use finite maps from
  type variables to types. *)

  type TypeSubstitution = FMap(TypeVariable,Type)

  op typeSubstInType : TypeSubstitution -> Type       -> Type
  op typeSubstInExpr : TypeSubstitution -> Expression -> Expression
  op typeSubstInPatt : TypeSubstitution -> Pattern    -> Pattern

  def typeSubstInType sbs = fn
    | boolean         -> boolean
    | variable tv     -> if definedAt?(sbs,tv)
                         then apply(sbs,tv)
                         else variable tv
    | arrow(t1,t2)    -> arrow (typeSubstInType sbs t1,
                                typeSubstInType sbs t2)
    | sum(cS,tS?)     -> let newTS? =
                             map (mapOption (typeSubstInType sbs), tS?) in
                         sum (cS, newTS?)
    | nary(tc,tS)     -> let newTS = map (typeSubstInType sbs, tS) in
                         nary (tc, newTS)
    | subQuot(tc,t,e) -> subQuot (tc,
                                  typeSubstInType sbs t,
                                  typeSubstInExpr sbs e)

  def typeSubstInExpr sbs = fn
    | unary(eo,e)              -> unary (eo, typeSubstInExpr sbs e)
    | binary(eo,e1,e2)         -> binary (eo,
                                          typeSubstInExpr sbs e1,
                                          typeSubstInExpr sbs e2)
    | ifThenElse(e0,e1,e2)     -> ifThenElse (typeSubstInExpr sbs e0,
                                              typeSubstInExpr sbs e1,
                                              typeSubstInExpr sbs e2)
    | nary(eo,eS)            -> let newES =
                                    map (typeSubstInExpr sbs, eS) in
                                nary (eo, newES)
    | binding(eo,bvS,e)      -> let (vS,tS) = unzip bvS in
                                let newTS =
                                    map (typeSubstInType sbs, tS) in
                                binding (eo,
                                         zip (vS, newTS),
                                         typeSubstInExpr sbs e)
    | opInstance(o,tS)         -> opInstance
                                   (o, map (typeSubstInType sbs, tS))
    | embedder(t,c)            -> embedder (typeSubstInType sbs t, c)
    | cas(e,branches)          -> let (pS,eS) = unzip branches in
                                  let newPS =
                                      map (typeSubstInPatt sbs, pS) in
                                  let newES =
                                      map (typeSubstInExpr sbs, eS) in
                                  cas (typeSubstInExpr sbs e,
                                       zip (newPS, newES))
    | recursiveLet(asgments,e) -> let (bvS,eS) = unzip asgments in
                                  let (vS,tS) = unzip bvS in
                                  let newTS =
                                      map (typeSubstInType sbs, tS) in
                                  let newES =
                                      map (typeSubstInExpr sbs, eS) in
                                  let newBvS = zip (vS, newTS) in
                                  let newAsgments = zip (newBvS, newES) in
                                  recursiveLet
                                   (newAsgments, typeSubstInExpr sbs e)
    | nonRecursiveLet(p,e,e1)  -> nonRecursiveLet (typeSubstInPatt sbs p,
                                                   typeSubstInExpr sbs e,
                                                   typeSubstInExpr sbs e1)
    | e                        -> e

  def typeSubstInPatt sbs = fn
    | variable(v,t)    -> variable (v, typeSubstInType sbs t)
    | embedding(t,c,p) -> embedding (typeSubstInType sbs t,
                                     c,
                                     typeSubstInPatt sbs p)
    | record(fS,pS)    -> let newPS =
                              map (typeSubstInPatt sbs, pS) in
                          record (fS, newPS)
    | alias(v,t,p)     -> alias (v,
                                 typeSubstInType sbs t,
                                 typeSubstInPatt sbs p)


  %%%%%%%%%%%%%%%%%%%%%%%%%%%
  % expression substitutions:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* While LD only defines only the substitution of a single variable with an
  expression, here we consider multi-variable substitutions (like for
  types). We model them as finite maps.

  Another difference with LD is that in LD no substitution is performed in
  subtype and quotient type predicates, because well-typed ones have no free
  variables. Here it is easier to perform the substitution in those
  predicates, because of the way we have factored expressions. *)

  type ExpressionSubstitution = FMap(Variable,Expression)

  op exprSubst : ExpressionSubstitution -> Expression -> Expression
  def exprSubst sbs = fn
    | nullary(variable v)      -> if definedAt?(sbs,v)
                                  then apply(sbs,v)
                                  else nullary(variable v)
    | unary(eo,e)              -> unary (eo, exprSubst sbs e)
    | binary(eo,e1,e2)         -> binary (eo,
                                          exprSubst sbs e1,
                                          exprSubst sbs e2)
    | ifThenElse(e0,e1,e2)     -> ifThenElse (exprSubst sbs e0,
                                              exprSubst sbs e1,
                                              exprSubst sbs e2)
    | nary(eo,eS)              -> let newES =
                                      map (exprSubst sbs, eS) in
                                  nary (eo, newES)
    | binding(eo,bvS,e)        -> let (vS,_) = unzip bvS in
                                  let bodySbs =
                                      undefineMulti (sbs, toSet vS) in
                                  binding (eo,
                                           bvS,
                                           exprSubst bodySbs e)
    | opInstance(o,tS)          -> opInstance(o,tS)
    | embedder(t,c)             -> embedder (t, c)
    | cas(e,branches)           -> let (pS,eS) = unzip branches in
                                   let branchSbss =
                                       seqSuchThat (fn(i:Nat) ->
                                         if i < length branches
                                         then Some
                                                (undefineMulti
                                                  (sbs, pattVars (pS elem i)))
                                         else None) in
                                   let newES =
                                       seqSuchThat (fn(i:Nat) ->
                                         if i < length branches
                                         then Some
                                               (exprSubst (branchSbss elem i)
                                                          (eS         elem i))
                                         else None) in
                                   cas (exprSubst sbs e,
                                        zip (pS, newES))
    | recursiveLet(asgments,e)  -> let (bvS,eS) = unzip asgments in
                                   let (vS,_) = unzip bvS in
                                   let bodySbs =
                                       undefineMulti (sbs, toSet vS) in
                                   let newES =
                                       map (exprSubst bodySbs, eS) in
                                   let newAsgments = zip (bvS, newES) in
                                   recursiveLet
                                    (newAsgments, exprSubst sbs e)
    | nonRecursiveLet(p,e,e1)   -> let bodySbs =
                                       undefineMulti (sbs, pattVars p) in
                                   nonRecursiveLet (p,
                                                    exprSubst sbs e,
                                                    exprSubst bodySbs e1)
    | e                         -> e


  % captured variables at free occurrences of given variable:
  op captVars : Variable -> Expression -> FSet Variable
  def captVars u = fn
    | unary(_,e)               -> captVars u e
    | binary(_,e1,e2)          -> captVars u e1 \/ captVars u e2
    | ifThenElse(e0,e1,e2)     -> captVars u e0 \/
                                  captVars u e1 \/
                                  captVars u e2
    | nary(_,eS)               -> unionAll (map (captVars u, eS))
    | binding(_,bvS,e)         -> let (vS,_) = unzip bvS in
                                  if u in? exprFreeVars e && ~(u in? vS)
                                  then toSet vS \/ captVars u e
                                  else empty
    | cas(e,branches)          -> let (pS,eS) = unzip branches in
                                  let varSets =
                                    seqSuchThat (fn(i:Nat) ->
                                      if i < length branches
                                      then if u in? exprFreeVars (eS elem i) &&
                                              ~(u in? pattVars (pS elem i))
                                           then Some (pattVars (pS elem i) \/
                                                      captVars u (eS elem i))
                                           else Some empty
                                      else None) in
                                  unionAll varSets \/ captVars u e
    | recursiveLet(asgments,e) -> let (bvS,eS) = unzip asgments in
                                  let (vS,_) = unzip bvS in
                                  if (u in? exprFreeVars e ||
                                      (ex(i:Nat)
                                         i < length eS &&
                                         u in? exprFreeVars (eS elem i))) &&
                                     ~(u in? toSet vS)
                                  then toSet vS \/
                                       captVars u e \/
                                       unionAll (map (captVars u, eS))
                                  else empty
    | nonRecursiveLet(p,e,e1)  -> if u in? exprFreeVars e ||
                                     (u in? exprFreeVars e1 -- pattVars p)
                                  then captVars u e \/
                                       pattVars p \/
                                       captVars u e1
                                  else empty
    | _                        -> empty

  op exprSubstOK? : Expression * ExpressionSubstitution -> Boolean
  def exprSubstOK?(e,sbs) =
    (fa(v) v in? domain sbs =>
           exprFreeVars (apply(sbs,v)) /\ captVars v e = empty)


  %%%%%%%%%%%%%%%%%%%%%%%%
  % pattern substitutions:
  %%%%%%%%%%%%%%%%%%%%%%%%

  type PatternSubstitution = Variable * Variable

  op pattSubst : PatternSubstitution -> Pattern -> Pattern
  def pattSubst (old,new) = fn
    | variable(v,t)    -> if v = old
                          then variable(new,t)
                          else variable(v,  t)
    | embedding(t,c,p) -> embedding (t, c, pattSubst (old,new) p)
    | record(fS,pS)    -> let newPS = map (pattSubst (old,new), pS) in
                          record (fS, newPS)
    | alias(v,t,p)     -> if v = old
                          then alias (new, t, pattSubst (old,new) p)
                          else alias (v,   t, pattSubst (old,new) p)


  %%%%%%%%%%%%
  % positions:
  %%%%%%%%%%%%

  type Position = FSeq Nat


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % type substitutions at position:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op typeSubstAt :
     TypeOrExprOrPatt * Type * Type * Position * TypeOrExprOrPatt -> Boolean

  def typeSubstAt = min (fn typeSubstAt ->
  %%%%% types:
    (fa (old:Type, new:Type)
       typeSubstAt (typ old, old, new, empty, typ new))
    &&
    (fa (old:Type, new:Type, pos:Position, t1:Type, t2:Type, newT1:Type)
       typeSubstAt (typ t1, old, new, pos, typ newT1) =>
       typeSubstAt (typ (arrow(t1,t2)), old, new, 1 |> pos,
                    typ (arrow(newT1,t2))))
    &&
    (fa (old:Type, new:Type, pos:Position, t1:Type, t2:Type, newT2:Type)
       typeSubstAt (typ t2, old, new, pos, typ newT2) =>
       typeSubstAt (typ (arrow(t1,t2)), old, new, 2 |> pos,
                    typ (arrow(t1,newT2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, cS:FSeqNE Constructor, tS?:FSeqNE(Option Type),
         ti:Type, newTi:Type)
       i < length tS? &&
       tS? elem i = Some ti &&
       typeSubstAt (typ ti, old, new, pos, typ newTi) =>
       typeSubstAt (typ (sum (cS, tS?)), old, new, (i+1) |> pos,
                    typ (sum (cS, update(tS?,i,Some newTi)))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, tc:NaryTypeConstruct, tS:FSeq Type, newTi:Type)
       i < length tS &&
       typeSubstAt (typ (tS elem i), old, new, pos, typ newTi) =>
       typeSubstAt (typ (nary(tc,tS)), old, new, (i+1) |> pos,
                    typ (nary(tc,update(tS,i,newTi)))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         tc:SubOrQuotientTypeConstruct, t:Type, e:Expression, newT:Type)
       typeSubstAt (typ t, old, new, pos, typ newT) =>
       typeSubstAt (typ (subQuot(tc,t,e)), old, new, 0 |> pos,
                    typ (subQuot(tc,newT,e))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         tc:SubOrQuotientTypeConstruct, t:Type, e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (typ (subQuot(tc,t,e)), old, new, 1 |> pos,
                    typ (subQuot(tc,t,newE))))
  %%%%% expressions:
    &&
    (fa (old:Type, new:Type, pos:Position,
         eo:UnaryExprOperator, e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (unary(eo,e)), old, new, 0 |> pos,
                    expr (unary(eo,newE))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         eo:BinaryExprOperator, e1:Expression, e2:Expression, newE1:Expression)
       typeSubstAt (expr e1, old, new, pos, expr newE1) =>
       typeSubstAt (expr (binary(eo,e1,e2)), old, new, 1 |> pos,
                    expr (binary(eo,newE1,e2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         eo:BinaryExprOperator, e1:Expression, e2:Expression, newE2:Expression)
       typeSubstAt (expr e2, old, new, pos, expr newE2) =>
       typeSubstAt (expr (binary(eo,e1,e2)), old, new, 2 |> pos,
                    expr (binary(eo,e1,newE2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE0:Expression)
       typeSubstAt (expr e0, old, new, pos, expr newE0) =>
       typeSubstAt (expr (ifThenElse(e0,e1,e2)), old, new, 0 |> pos,
                    expr (ifThenElse(newE0,e1,e2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE1:Expression)
       typeSubstAt (expr e1, old, new, pos, expr newE1) =>
       typeSubstAt (expr (ifThenElse(e0,e1,e2)), old, new, 1 |> pos,
                    expr (ifThenElse(e0,newE1,e2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE2:Expression)
       typeSubstAt (expr e2, old, new, pos, expr newE2) =>
       typeSubstAt (expr (ifThenElse(e0,e1,e2)), old, new, 2 |> pos,
                    expr (ifThenElse(e0,e1,newE2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         eo:NaryExprOperator, i:Nat, eS:FSeq Expression, newEi:Expression)
       i < length eS &&
       typeSubstAt (expr (eS elem i), old, new, pos, expr newEi) =>
       typeSubstAt (expr (nary(eo,eS)), old, new, (i+1) |> pos,
                    expr (nary(eo,update(eS,i,newEi)))))
    &&
    (fa (old:Type, new:Type, pos:Position, eo:BindingExprOperator,
         i:Nat, vS:FSeqNE Variable, tS:FSeqNE Type, e:Expression, newTi:Type)
       i < length vS &&
       length vS = length tS &&
       typeSubstAt (typ (tS elem i), old, new, pos, typ newTi) =>
       typeSubstAt (expr (binding (eo, zip (vS, tS), e)),
                    old, new, (i+1) |> pos,
                    expr (binding (eo,
                                   zip (vS, update(tS,i,newTi)),
                                   e))))
    &&
    (fa (old:Type, new:Type, pos:Position, eo:BindingExprOperator,
         bvS:FSeqNE(Variable*Type), e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (binding (eo, bvS, e)), old, new, 0 |> pos,
                    expr (binding (eo, bvS, newE))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, opp:Operation, tS:FSeq Type, newTi:Type)
       i < length tS &&
       typeSubstAt (typ (tS elem i), old, new, pos, typ newTi) =>
       typeSubstAt (expr (opInstance(opp,tS)), old, new, (i+1) |> pos,
                    expr (opInstance(opp,update(tS,i,newTi)))))
    &&
    (* Since here embedders are decorated by types, instead of sum types as in
    LD, the positioning changes slightly: we just use 0 to indicate the type
    that decorates the embedder, as opposed to i to indicate the i-th type
    component as in LD. *)
    (fa (old:Type, new:Type, pos:Position,
         t:Type, c:Constructor, newT:Type)
       typeSubstAt (typ t, old, new, pos, typ newT) =>
       typeSubstAt (expr (embedder(t,c)), old, new, 0 |> pos,
                    expr (embedder(t,c))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e:Expression, branches:FSeqNE(Pattern*Expression), newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (cas(e,branches)), old, new, 0 |> pos,
                    expr (cas(newE,branches))))
    &&
    (fa (old:Type, new:Type, pos:Position, i:Nat, e:Expression,
         pS:FSeqNE Pattern, eS:FSeqNE Expression, newPi:Pattern)
       i < length pS &&
       length pS = length eS &&
       typeSubstAt (patt (pS elem i), old, new, pos, patt newPi) =>
       typeSubstAt (expr (cas (e, (zip (pS, eS)))),
                    old, new, (2*(i+1)-1) |> pos,
                    expr (cas (e, (zip (update(pS,i,newPi), eS))))))
    &&
    (fa (old:Type, new:Type, pos:Position, i:Nat, e:Expression,
         pS:FSeqNE Pattern, eS:FSeqNE Expression, newEi:Expression)
       i < length pS &&
       length pS = length eS &&
       typeSubstAt (expr (eS elem i), old, new, pos, expr newEi) =>
       typeSubstAt (expr (cas (e, (zip (pS, eS)))),
                    old, new, (2*(i+1)) |> pos,
                    expr (cas (e, (zip (pS, update(eS,i,newEi)))))))
    &&
    (fa (old:Type, new:Type, pos:Position, i:Nat, e:Expression,
         vS:FSeqNE Variable, tS:FSeqNE Type, eS:FSeqNE Expression,
         e:Expression, newTi:Type)
       i < length vS &&
       length vS = length tS &&
       length tS = length eS &&
       typeSubstAt (typ (tS elem i), old, new, pos, typ newTi) =>
       typeSubstAt (expr (recursiveLet (zip (zip (vS, tS), eS), e)),
                    old, new, (2*(i+1)-1) |> pos,
                    expr (recursiveLet
                           (zip (zip (vS, update(tS,i,newTi)), eS), e))))
    &&
    (fa (old:Type, new:Type, pos:Position, i:Nat, e:Expression,
         vS:FSeqNE Variable, tS:FSeqNE Type, eS:FSeqNE Expression,
         e:Expression, newEi:Expression)
       i < length vS &&
       length vS = length tS &&
       length tS = length eS &&
       typeSubstAt (expr (eS elem i), old, new, pos, expr newEi) =>
       typeSubstAt (expr (recursiveLet (zip (zip (vS, tS), eS), e)),
                    old, new, (2*(i+1)) |> pos,
                    expr (recursiveLet
                           (zip (zip (vS, tS), update(eS,i,newEi)), e))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         asgments:FSeqNE(BoundVar*Expression), e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (recursiveLet(asgments,e)), old, new, 0 |> pos,
                    expr (recursiveLet(asgments,newE))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         p:Pattern, e:Expression, e1:Expression, newP:Pattern)
       typeSubstAt (patt p, old, new, pos, patt newP) =>
       typeSubstAt (expr (nonRecursiveLet(p,e,e1)), old, new, 0 |> pos,
                    expr (nonRecursiveLet(newP,e,e1))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         p:Pattern, e:Expression, e1:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (nonRecursiveLet(p,e,e1)), old, new, 1 |> pos,
                    expr (nonRecursiveLet(p,newE,e1))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         p:Pattern, e:Expression, e1:Expression, newE1:Expression)
       typeSubstAt (expr e1, old, new, pos, expr newE1) =>
       typeSubstAt (expr (nonRecursiveLet(p,e,e1)), old, new, 2 |> pos,
                    expr (nonRecursiveLet(p,e,newE1))))
  %%%%% patterns:
    &&
    (fa (old:Type, new:Type, pos:Position, v:Variable, t:Type, newT:Type)
       typeSubstAt (typ t, old, new, pos, typ newT) =>
       typeSubstAt (patt (variable(v,t)), old, new, 0 |> pos,
                    patt (variable(v,newT))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         t:Type, c:Constructor, p:Pattern, newT:Type)
       typeSubstAt (typ t, old, new, pos, typ newT) =>
       typeSubstAt (patt (embedding(t,c,p)), old, new, 0 |> pos,
                    patt (embedding(newT,c,p))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         t:Type, c:Constructor, p:Pattern, newP:Pattern)
       typeSubstAt (patt p, old, new, pos, patt newP) =>
       typeSubstAt (patt (embedding(t,c,p)), old, new, 1 |> pos,
                    patt (embedding(t,c,newP))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, fS:FSeq Field, pS:FSeq Pattern, newPi:Pattern)
       i < length fS &&
       length fS = length pS &&
       typeSubstAt (patt (pS elem i), old, new, pos, patt newPi) =>
       typeSubstAt (patt (record (fS, pS)), old, new, i |> pos,
                    patt (record (fS, update(pS,i,newPi)))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         v:Variable, t:Type, p:Pattern, newT:Type)
       typeSubstAt (typ t, old, new, pos, typ newT) =>
       typeSubstAt (patt (alias(v,t,p)), old, new, 0 |> pos,
                    patt (alias(v,newT,p))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         v:Variable, t:Type, p:Pattern, newP:Pattern)
       typeSubstAt (patt p, old, new, pos, patt newP) =>
       typeSubstAt (patt (alias(v,t,p)), old, new, 1 |> pos,
                    patt (alias(v,t,newP)))))

  op typeSubstInTypeAt :
     Type * Type * Type * Position * Type -> Boolean
  def typeSubstInTypeAt(t,old,new,pos,t1) =
    typeSubstAt (typ t, old, new, pos, typ t1)

  op typeSubstInExprAt :
     Expression * Type * Type * Position * Expression -> Boolean
  def typeSubstInExprAt(e,old,new,pos,e1) =
    typeSubstAt (expr e, old, new, pos, expr e1)

  op typeSubstInPattAt :
     Pattern * Type * Type * Position * Pattern -> Boolean
  def typeSubstInPattAt(p,old,new,pos,p1) =
    typeSubstAt (patt p, old, new, pos, patt p1)


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % expression substitutions at position:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op exprSubstAt :
     Expression * Expression * Expression * Position * Expression -> Boolean

  def exprSubstAt = min (fn exprSubstAt ->
    (fa (old:Expression, new:Expression)
       exprSubstAt (old, old, new, empty, new))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         eo:UnaryExprOperator, e:Expression, newE:Expression)
       exprSubstAt (e, old, new, pos, newE) =>
       exprSubstAt (unary(eo,e), old, new, 0 |> pos,
                    unary(eo,newE)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         eo:BinaryExprOperator, e1:Expression, e2:Expression, newE1:Expression)
       exprSubstAt (e1, old, new, pos, newE1) =>
       exprSubstAt (binary(eo,e1,e2), old, new, 1 |> pos,
                    binary(eo,newE1,e2)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         eo:BinaryExprOperator, e1:Expression, e2:Expression, newE2:Expression)
       exprSubstAt (e2, old, new, pos, newE2) =>
       exprSubstAt (binary(eo,e1,e2), old, new, 2 |> pos,
                    binary(eo,e1,newE2)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE0:Expression)
       exprSubstAt (e0, old, new, pos, newE0) =>
       exprSubstAt (ifThenElse(e0,e1,e2), old, new, 0 |> pos,
                    ifThenElse(newE0,e1,e2)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE1:Expression)
       exprSubstAt (e1, old, new, pos, newE1) =>
       exprSubstAt (ifThenElse(e0,e1,e2), old, new, 1 |> pos,
                    ifThenElse(e0,newE1,e2)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE2:Expression)
       exprSubstAt (e2, old, new, pos, newE2) =>
       exprSubstAt (ifThenElse(e0,e1,e2), old, new, 2 |> pos,
                    ifThenElse(e0,e1,newE2)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         eo:NaryExprOperator, eS:FSeq Expression, i:Nat, newEi:Expression)
       exprSubstAt (eS elem i, old, new, pos, newEi) =>
       exprSubstAt (nary(eo,eS), old, new, (i+1) |> pos,
                    nary(eo,update(eS,i,newEi))))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         eo:BindingExprOperator, bvS:FSeqNE BoundVar,
         e:Expression, newE:Expression)
       exprSubstAt (e, old, new, pos, newE) =>
       exprSubstAt (binding(eo,bvS,e), old, new, 0 |> pos,
                    binding(eo,bvS,newE)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e:Expression, branches:FSeqNE(Pattern*Expression), newE:Expression)
       exprSubstAt (e, old, new, pos, newE) =>
       exprSubstAt (cas(e,branches), old, new, 0 |> pos,
                    cas(newE,branches)))
    &&
    (fa (old:Expression, new:Expression, pos:Position, i:Nat, e:Expression,
         pS:FSeqNE Pattern, eS:FSeqNE Expression, newEi:Expression)
       i < length pS &&
       length pS = length eS &&
       exprSubstAt (eS elem i, old, new, pos, newEi) =>
       exprSubstAt (cas (e, (zip (pS, eS))), old, new, (i+1) |> pos,
                    cas (e, (zip (pS, update(eS,i,newEi))))))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         asgments:FSeqNE(BoundVar*Expression), e:Expression, newE:Expression)
       exprSubstAt (e, old, new, pos, newE) =>
       exprSubstAt (recursiveLet(asgments,e), old, new, 0 |> pos,
                    recursiveLet(asgments,newE)))
    &&
    (fa (old:Expression, new:Expression, pos:Position, i:Nat,
         bvS:FSeqNE BoundVar, eS:FSeqNE Expression,
         newEi:Expression, e:Expression)
       i < length bvS &&
       length bvS = length eS &&
       exprSubstAt (eS elem i, old, new, pos, newEi) =>
       exprSubstAt (recursiveLet (zip (bvS, eS), e), old, new, (i+1) |> pos,
                    recursiveLet (zip (bvS, update(eS,i,newEi)), e)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         p:Pattern, e:Expression, e1:Expression, newE:Expression)
       exprSubstAt (e, old, new, pos, newE) =>
       exprSubstAt (nonRecursiveLet(p,e,e1), old, new, 0 |> pos,
                    nonRecursiveLet(p,newE,e1)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         p:Pattern, e:Expression, e1:Expression, newE1:Expression)
       exprSubstAt (e1, old, new, pos, newE1) =>
       exprSubstAt (nonRecursiveLet(p,e,e1), old, new, 1 |> pos,
                    nonRecursiveLet(p,e,newE1))))

  % valid position in expression:
  op positionInExpr? : Position * Expression -> Boolean
  def positionInExpr?(pos,e) =
    (ex (old:Expression, new:Expression, newE:Expression)
       exprSubstAt (e, old, new, pos, newE))

  % variables captured at position:
  op captVarsAt : ((Position * Expression) | positionInExpr?) -> FSet Variable
  def captVarsAt(pos,e) =
    if pos = empty then empty
    else let i = first pos in
         let pos = rtail pos in
         case e of
           | unary(_,e)               -> assert (i = 0)
                                         (captVarsAt(pos,e))
           | binary(_,e1,e2)          -> if i = 1 then captVarsAt(pos,e1)
                                    else assert (i = 2) (captVarsAt(pos,e2))
           | ifThenElse(e0,e1,e2)     -> if i = 0 then captVarsAt(pos,e0)
                                    else if i = 1 then captVarsAt(pos,e1)
                                    else assert (i = 2) (captVarsAt(pos,e2))
           | nary(_,eS)               -> assert (1 <= i && i <= length eS)
                                         (captVarsAt (pos, eS elem (i-1)))
           | binding(_,bvS,e)         -> assert (i = 0)
                                         (let (vS, _) = unzip bvS in
                                          captVarsAt(pos,e) \/ toSet vS)
           | cas(e,branches)          -> if i = 0 then captVarsAt(pos,e)
                                         else
                                           assert (1 <= i && i <= length branches)
                                           (let (pS, eS) = unzip branches in
                                            pattVars (pS elem (i-1)) \/
                                            captVarsAt (pos, eS elem (i-1)))
           | recursiveLet(asgments,e) -> let (bvS, eS) = unzip asgments in
                                         let (vS, _) = unzip bvS in
                                         if i = 0
                                         then toSet vS \/ captVarsAt(pos,e)
                                         else
                                           assert (1 <= i && i <= length asgments)
                                           (toSet vS \/
                                            captVarsAt (pos, eS elem (i-1)))
           | nonRecursiveLet(p,e,e1)  -> if i = 0 then captVarsAt(pos,e)
                                         else
                                           assert (i = 1)
                                           (pattVars p \/ captVarsAt(pos,e1))

  op exprSubstAtOK? : Expression * Expression * Expression * Position -> Boolean
  def exprSubstAtOK?(e,old,new,pos) =
    (ex (newE:Expression)
       exprSubstAt (e, old, new, pos, newE) &&
       exprFreeVars old /\ captVarsAt(pos,e) = empty &&
       exprFreeVars new /\ captVarsAt(pos,e) = empty)

endspec
