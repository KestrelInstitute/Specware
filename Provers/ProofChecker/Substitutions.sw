spec

  import OccurringNames


  %%%%%%%%%%%%%%%%%%%%%
  % type substitutions:
  %%%%%%%%%%%%%%%%%%%%%

  (* While in LD substitutions are describes by a sequence of type variables
  and a sequence of types of the same length, here we use finite maps from
  type variables (i.e. names) to types. *)

  type TypeSubstitution = FMap(Name,Type)

  op typeSubstInType : TypeSubstitution -> Type       -> Type
  op typeSubstInExpr : TypeSubstitution -> Expression -> Expression
  op typeSubstInPatt : TypeSubstitution -> Pattern    -> Pattern

  def typeSubstInType sbs = fn
    | boolean             -> boolean
    | variable tv         -> if definedAt?(sbs,tv)
                             then apply(sbs,tv)
                             else variable tv
    | arrow(t1,t2)        -> arrow (typeSubstInType sbs t1,
                                    typeSubstInType sbs t2)
    | sum(constrs,types?) -> let newTypes? =
                                 map (mapOption (typeSubstInType sbs), types?) in
                             sum (constrs, newTypes?)
    | nary(ntc,types)     -> let newTypes = map (typeSubstInType sbs, types) in
                             nary (ntc, newTypes)
    | subQuot(sqtc,t,e)   -> subQuot (sqtc,
                                      typeSubstInType sbs t,
                                      typeSubstInExpr sbs e)

  def typeSubstInExpr sbs = fn
    | unary(ueo,e)              -> unary (ueo, typeSubstInExpr sbs e)
    | binary(beo,e1,e2)         -> binary (beo,
                                           typeSubstInExpr sbs e1,
                                           typeSubstInExpr sbs e2)
    | ifThenElse(e0,e1,e2)      -> ifThenElse (typeSubstInExpr sbs e0,
                                               typeSubstInExpr sbs e1,
                                               typeSubstInExpr sbs e2)
    | nary(neo,exprs)           -> let newExprs =
                                       map (typeSubstInExpr sbs, exprs) in
                                   nary (neo, newExprs)
    | binding(beo,(v,t),e)      -> binding (beo,
                                            (v, typeSubstInType sbs t),
                                            typeSubstInExpr sbs e)
    | multiBinding(meo,binds,e) -> let (vars,types) = unzip binds in
                                   let newTypes =
                                       map (typeSubstInType sbs, types) in
                                   multiBinding (meo,
                                                 zip (vars, newTypes),
                                                 typeSubstInExpr sbs e)
    | opInstance(opp,types)     -> opInstance
                                    (opp, map (typeSubstInType sbs, types))
    | embedder(t,constr)        -> embedder (typeSubstInType sbs t, constr)
    | cas(e,branches)           -> let (patts,exprs) = unzip branches in
                                   let newPatts =
                                       map (typeSubstInPatt sbs, patts) in
                                   let newExprs =
                                       map (typeSubstInExpr sbs, exprs) in
                                   cas (typeSubstInExpr sbs e,
                                        zip (newPatts, newExprs))
    | recursiveLet(asgments,e)  -> let (binds,exprs) = unzip asgments in
                                   let (vars,types) = unzip binds in
                                   let newTypes =
                                       map (typeSubstInType sbs, types) in
                                   let newExprs =
                                       map (typeSubstInExpr sbs, exprs) in
                                   let newBinds = zip (vars, newTypes) in
                                   let newAsgments = zip (newBinds, newExprs) in
                                   recursiveLet
                                    (newAsgments, typeSubstInExpr sbs e)
    | nonRecursiveLet(p,e,e1)   -> nonRecursiveLet (typeSubstInPatt sbs p,
                                                    typeSubstInExpr sbs e,
                                                    typeSubstInExpr sbs e1)
    | e                         -> e

  def typeSubstInPatt sbs = fn
    | variable(v,t)         -> variable (v, typeSubstInType sbs t)
    | embedding(t,constr,p) -> embedding (typeSubstInType sbs t,
                                          constr,
                                          typeSubstInPatt sbs p)
    | record comps          -> let (fields,patts) = unzip comps in
                               let newPatts =
                                   map (typeSubstInPatt sbs, patts) in
                               record (zip (fields, newPatts))
    | alias((v,t),p)        -> alias ((v, typeSubstInType sbs t),
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

  type ExpressionSubstitution = FMap(Name,Expression)

  op exprSubst : ExpressionSubstitution -> Expression -> Expression
  def exprSubst sbs = fn
    | nullary(variable v)       -> if definedAt?(sbs,v)
                                   then apply(sbs,v)
                                   else nullary(variable v)
    | unary(ueo,e)              -> unary (ueo, exprSubst sbs e)
    | binary(beo,e1,e2)         -> binary (beo,
                                           exprSubst sbs e1,
                                           exprSubst sbs e2)
    | ifThenElse(e0,e1,e2)      -> ifThenElse (exprSubst sbs e0,
                                               exprSubst sbs e1,
                                               exprSubst sbs e2)
    | nary(neo,exprs)           -> let newExprs =
                                       map (exprSubst sbs, exprs) in
                                   nary (neo, newExprs)
    | binding(beo,(v,t),e)      -> let bodySbs = undefine (sbs, v) in
                                   binding (beo, (v, t), exprSubst bodySbs e)
    | multiBinding(meo,binds,e) -> let (vars,_) = unzip binds in
                                   let bodySbs =
                                       undefineMulti (sbs, toSet vars) in
                                   multiBinding (meo,
                                                 binds,
                                                 exprSubst bodySbs e)
    | opInstance(opp,types)     -> opInstance(opp,types)
    | embedder(t,constr)        -> embedder (t, constr)
    | cas(e,branches)           -> let (patts,exprs) = unzip branches in
                                   let branchSbss =
                                       seqSuchThat (fn(i:Nat) ->
                                         if i < length branches
                                         then Some
                                                (undefineMulti
                                                  (sbs, pattVars (patts elem i)))
                                         else None) in
                                   let newExprs =
                                       seqSuchThat (fn(i:Nat) ->
                                         if i < length branches
                                         then Some
                                               (exprSubst (branchSbss elem i)
                                                          (exprs      elem i))
                                         else None) in
                                   cas (exprSubst sbs e,
                                        zip (patts, newExprs))
    | recursiveLet(asgments,e)  -> let (binds,exprs) = unzip asgments in
                                   let (vars,_) = unzip binds in
                                   let bodySbs =
                                       undefineMulti (sbs, toSet vars) in
                                   let newExprs =
                                       map (exprSubst bodySbs, exprs) in
                                   let newAsgments = zip (binds, newExprs) in
                                   recursiveLet
                                    (newAsgments, exprSubst sbs e)
    | nonRecursiveLet(p,e,e1)   -> let bodySbs =
                                       undefineMulti (sbs, pattVars p) in
                                   nonRecursiveLet (p,
                                                    exprSubst sbs e,
                                                    exprSubst bodySbs e1)
    | e                         -> e


  % captured variables at free occurrences of given variable:
  op captVars : Name -> Expression -> FSet Name
  def captVars u = fn
    | unary(_,e)               -> captVars u e
    | binary(_,e1,e2)          -> captVars u e1 \/ captVars u e2
    | ifThenElse(e0,e1,e2)     -> captVars u e0 \/
                                  captVars u e1 \/
                                  captVars u e2
    | nary(_,exprs)            -> unionAll (map (captVars u, exprs))
    | binding(_,(v,_),e)       -> if u in? exprFreeVars e && u ~= v
                                  then captVars u e with v
                                  else empty
    | multiBinding(_,binds,e)  -> let (vars,_) = unzip binds in
                                  if u in? exprFreeVars e &&
                                     ~(u in? vars)
                                  then toSet vars \/ captVars u e
                                  else empty
    | cas(e,branches)          -> let (patts,exprs) = unzip branches in
                                  let varSets =
                                    seqSuchThat (fn(i:Nat) ->
                                      if i < length branches
                                      then if u in? exprFreeVars
                                                      (exprs elem i) &&
                                              ~(u in? pattVars (patts elem i))
                                           then Some (pattVars (patts elem i) \/
                                                      captVars
                                                        u (exprs elem i))
                                           else Some empty
                                      else None) in
                                  unionAll varSets \/ captVars u e
    | recursiveLet(asgments,e) -> let (binds,exprs) = unzip asgments in
                                  let (vars,_) = unzip binds in
                                  if (u in? exprFreeVars e ||
                                      (ex(i:Nat) i < length exprs &&
                                                 u in? exprFreeVars
                                                         (exprs elem i))) &&
                                     ~(u in? toSet vars)
                                  then toSet vars \/
                                       captVars u e \/
                                       unionAll (map (captVars u, exprs))
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

  type PatternSubstitution = Name * Name

  op pattSubst : PatternSubstitution -> Pattern -> Pattern
  def pattSubst (old,new) = fn
    | variable(v,t)         -> if v = old
                               then variable(new,t)
                               else variable(v,  t)
    | embedding(t,constr,p) -> embedding (t, constr, pattSubst (old,new) p)
    | record comps          -> let (fields, patts) = unzip comps in
                               let newPatts = map (pattSubst (old,new), patts) in
                               record (zip (fields, newPatts))
    | alias((v,t),p)        -> if v = old
                               then alias ((new,t), pattSubst (old,new) p)
                               else alias ((v,  t), pattSubst (old,new) p)


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
         i:Nat, constrs:FSeqNE Name, types?:FSeqNE(Option Type),
         ti:Type, newTi:Type)
       i < length types? &&
       types? elem i = Some ti &&
       typeSubstAt (typ ti, old, new, pos, typ newTi) =>
       typeSubstAt (typ (sum (constrs, types?)), old, new, (i+1) |> pos,
                    typ (sum (constrs, update(types?,i,Some newTi)))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, ntc:NaryTypeConstruct, types:FSeq Type, newTi:Type)
       i < length types &&
       typeSubstAt (typ (types elem i), old, new, pos, typ newTi) =>
       typeSubstAt (typ (nary(ntc,types)), old, new, (i+1) |> pos,
                    typ (nary(ntc,update(types,i,newTi)))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         sqtc:SubOrQuotientTypeConstruct, t:Type, e:Expression, newT:Type)
       typeSubstAt (typ t, old, new, pos, typ newT) =>
       typeSubstAt (typ (subQuot(sqtc,t,e)), old, new, 0 |> pos,
                    typ (subQuot(sqtc,newT,e))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         sqtc:SubOrQuotientTypeConstruct, t:Type, e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (typ (subQuot(sqtc,t,e)), old, new, 1 |> pos,
                    typ (subQuot(sqtc,t,newE))))
  %%%%% expressions:
    &&
    (fa (old:Type, new:Type, pos:Position,
         ueo:UnaryExprOperator, e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (unary(ueo,e)), old, new, 0 |> pos,
                    expr (unary(ueo,newE))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         beo:BinaryExprOperator, e1:Expression, e2:Expression, newE1:Expression)
       typeSubstAt (expr e1, old, new, pos, expr newE1) =>
       typeSubstAt (expr (binary(beo,e1,e2)), old, new, 1 |> pos,
                    expr (binary(beo,newE1,e2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         beo:BinaryExprOperator, e1:Expression, e2:Expression, newE2:Expression)
       typeSubstAt (expr e2, old, new, pos, expr newE2) =>
       typeSubstAt (expr (binary(beo,e1,e2)), old, new, 2 |> pos,
                    expr (binary(beo,e1,newE2))))
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
         neo:NaryExprOperator, i:Nat, exprs:FSeq Expression, newEi:Expression)
       i < length exprs &&
       typeSubstAt (expr (exprs elem i), old, new, pos, expr newEi) =>
       typeSubstAt (expr (nary(neo,exprs)), old, new, (i+1) |> pos,
                    expr (nary(neo,update(exprs,i,newEi)))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         beo:BindingExprOperator, v:Name, t:Type, e:Expression, newT:Type)
       typeSubstAt (typ t, old, new, pos, typ newT) =>
       typeSubstAt (expr (binding(beo,(v,t),e)), old, new, 0 |> pos,
                    expr (binding(beo,(v,newT),e))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         beo:BindingExprOperator, v:Name, t:Type, e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (binding(beo,(v,t),e)), old, new, 1 |> pos,
                    expr (binding(beo,(v,t),newE))))
    &&
    (fa (old:Type, new:Type, pos:Position, meo:MultiBindingExprOperator,
         i:Nat, vars:FSeqNE Name, types:FSeqNE Type, e:Expression, newTi:Type)
       i < length vars &&
       length vars = length types &&
       typeSubstAt (typ (types elem i), old, new, pos, typ newTi) =>
       typeSubstAt (expr (multiBinding (meo, zip (vars, types), e)),
                    old, new, (i+1) |> pos,
                    expr (multiBinding (meo,
                                        zip (vars, update(types,i,newTi)),
                                        e))))
    &&
    (fa (old:Type, new:Type, pos:Position, meo:MultiBindingExprOperator,
         binds:FSeqNE(Name*Type), e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (multiBinding (meo, binds, e)), old, new, 0 |> pos,
                    expr (multiBinding (meo, binds, newE))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, opp:Name, types:FSeq Type, newTi:Type)
       i < length types &&
       typeSubstAt (typ (types elem i), old, new, pos, typ newTi) =>
       typeSubstAt (expr (opInstance(opp,types)), old, new, (i+1) |> pos,
                    expr (opInstance(opp,update(types,i,newTi)))))
    &&
    (* Since here embedders are decorated by types, instead of sum types as in
    LD, the positioning changes slightly: we just use 0 to indicate the type
    that decorates the embedder, as opposed to i to indicate the i-th type
    component as in LD. *)
    (fa (old:Type, new:Type, pos:Position,
         t:Type, constr:Name, newT:Type)
       typeSubstAt (typ t, old, new, pos, typ newT) =>
       typeSubstAt (expr (embedder(t,constr)), old, new, 0 |> pos,
                    expr (embedder(t,constr))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e:Expression, branches:FSeqNE(Pattern*Expression), newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (cas(e,branches)), old, new, 0 |> pos,
                    expr (cas(newE,branches))))
    &&
    (fa (old:Type, new:Type, pos:Position, i:Nat, e:Expression,
         patts:FSeqNE Pattern, exprs:FSeqNE Expression, newPi:Pattern)
       i < length patts &&
       length patts = length exprs &&
       typeSubstAt (patt (patts elem i), old, new, pos, patt newPi) =>
       typeSubstAt (expr (cas (e, (zip (patts, exprs)))),
                    old, new, (2*(i+1)-1) |> pos,
                    expr (cas (e, (zip (update(patts,i,newPi), exprs))))))
    &&
    (fa (old:Type, new:Type, pos:Position, i:Nat, e:Expression,
         patts:FSeqNE Pattern, exprs:FSeqNE Expression, newEi:Expression)
       i < length patts &&
       length patts = length exprs &&
       typeSubstAt (expr (exprs elem i), old, new, pos, expr newEi) =>
       typeSubstAt (expr (cas (e, (zip (patts, exprs)))),
                    old, new, (2*(i+1)) |> pos,
                    expr (cas (e, (zip (patts, update(exprs,i,newEi)))))))
    &&
    (fa (old:Type, new:Type, pos:Position, i:Nat, e:Expression,
         vars:FSeqNE Name, types:FSeqNE Type, exprs:FSeqNE Expression,
         e:Expression, newTi:Type)
       i < length vars &&
       length vars = length types &&
       length types = length exprs &&
       typeSubstAt (typ (types elem i), old, new, pos, typ newTi) =>
       typeSubstAt (expr (recursiveLet (zip (zip (vars, types), exprs), e)),
                    old, new, (2*(i+1)-1) |> pos,
                    expr (recursiveLet
                           (zip (zip (vars, update(types,i,newTi)), exprs), e))))
    &&
    (fa (old:Type, new:Type, pos:Position, i:Nat, e:Expression,
         vars:FSeqNE Name, types:FSeqNE Type, exprs:FSeqNE Expression,
         e:Expression, newEi:Expression)
       i < length vars &&
       length vars = length types &&
       length types = length exprs &&
       typeSubstAt (expr (exprs elem i), old, new, pos, expr newEi) =>
       typeSubstAt (expr (recursiveLet (zip (zip (vars, types), exprs), e)),
                    old, new, (2*(i+1)) |> pos,
                    expr (recursiveLet
                           (zip (zip (vars, types), update(exprs,i,newEi)), e))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         asgments:FSeqNE(TypedVar*Expression), e:Expression, newE:Expression)
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
    (fa (old:Type, new:Type, pos:Position, v:Name, t:Type, newT:Type)
       typeSubstAt (typ t, old, new, pos, typ newT) =>
       typeSubstAt (patt (variable(v,t)), old, new, 0 |> pos,
                    patt (variable(v,newT))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         t:Type, constr:Name, p:Pattern, newT:Type)
       typeSubstAt (typ t, old, new, pos, typ newT) =>
       typeSubstAt (patt (embedding(t,constr,p)), old, new, 0 |> pos,
                    patt (embedding(newT,constr,p))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         t:Type, constr:Name, p:Pattern, newP:Pattern)
       typeSubstAt (patt p, old, new, pos, patt newP) =>
       typeSubstAt (patt (embedding(t,constr,p)), old, new, 1 |> pos,
                    patt (embedding(t,constr,newP))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, fields:FSeq Name, patts:FSeq Pattern, newPi:Pattern)
       i < length fields &&
       length fields = length patts &&
       typeSubstAt (patt (patts elem i), old, new, pos, patt newPi) =>
       typeSubstAt (patt (record (zip (fields, patts))), old, new, i |> pos,
                    patt (record (zip (fields, update(patts,i,newPi))))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         v:Name, t:Type, p:Pattern, newT:Type)
       typeSubstAt (typ t, old, new, pos, typ newT) =>
       typeSubstAt (patt (alias((v,t),p)), old, new, 0 |> pos,
                    patt (alias((v,newT),p))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         v:Name, t:Type, p:Pattern, newP:Pattern)
       typeSubstAt (patt p, old, new, pos, patt newP) =>
       typeSubstAt (patt (alias((v,t),p)), old, new, 1 |> pos,
                    patt (alias((v,t),newP)))))

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
         ueo:UnaryExprOperator, e:Expression, newE:Expression)
       exprSubstAt (e, old, new, pos, newE) =>
       exprSubstAt (unary(ueo,e), old, new, 0 |> pos,
                    unary(ueo,newE)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         beo:BinaryExprOperator, e1:Expression, e2:Expression, newE1:Expression)
       exprSubstAt (e1, old, new, pos, newE1) =>
       exprSubstAt (binary(beo,e1,e2), old, new, 1 |> pos,
                    binary(beo,newE1,e2)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         beo:BinaryExprOperator, e1:Expression, e2:Expression, newE2:Expression)
       exprSubstAt (e2, old, new, pos, newE2) =>
       exprSubstAt (binary(beo,e1,e2), old, new, 2 |> pos,
                    binary(beo,e1,newE2)))
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
         neo:NaryExprOperator, exprs:FSeq Expression, i:Nat, newEi:Expression)
       exprSubstAt (exprs elem i, old, new, pos, newEi) =>
       exprSubstAt (nary(neo,exprs), old, new, (i+1) |> pos,
                    nary(neo,update(exprs,i,newEi))))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         beo:BindingExprOperator, bind:TypedVar, e:Expression, newE:Expression)
       exprSubstAt (e, old, new, pos, newE) =>
       exprSubstAt (binding(beo,bind,e), old, new, 0 |> pos,
                    binding(beo,bind,newE)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         meo:MultiBindingExprOperator, binds:FSeqNE TypedVar,
         e:Expression, newE:Expression)
       exprSubstAt (e, old, new, pos, newE) =>
       exprSubstAt (multiBinding(meo,binds,e), old, new, 0 |> pos,
                    multiBinding(meo,binds,newE)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e:Expression, branches:FSeqNE(Pattern*Expression), newE:Expression)
       exprSubstAt (e, old, new, pos, newE) =>
       exprSubstAt (cas(e,branches), old, new, 0 |> pos,
                    cas(newE,branches)))
    &&
    (fa (old:Expression, new:Expression, pos:Position, i:Nat, e:Expression,
         patts:FSeqNE Pattern, exprs:FSeqNE Expression, newEi:Expression)
       i < length patts &&
       length patts = length exprs &&
       exprSubstAt (exprs elem i, old, new, pos, newEi) =>
       exprSubstAt (cas (e, (zip (patts, exprs))), old, new, (i+1) |> pos,
                    cas (e, (zip (patts, update(exprs,i,newEi))))))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         asgments:FSeqNE(TypedVar*Expression), e:Expression, newE:Expression)
       exprSubstAt (e, old, new, pos, newE) =>
       exprSubstAt (recursiveLet(asgments,e), old, new, 0 |> pos,
                    recursiveLet(asgments,newE)))
    &&
    (fa (old:Expression, new:Expression, pos:Position, i:Nat,
         binds:FSeqNE TypedVar, exprs:FSeqNE Expression,
         newEi:Expression, e:Expression)
       i < length binds &&
       length binds = length exprs &&
       exprSubstAt (exprs elem i, old, new, pos, newEi) =>
       exprSubstAt (recursiveLet (zip (binds, exprs), e), old, new, (i+1) |> pos,
                    recursiveLet (zip (binds, update(exprs,i,newEi)), e)))
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
  op captVarsAt : ((Position * Expression) | positionInExpr?) -> FSet Name
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
           | nary(_,exprs)            -> assert (1 <= i && i <= length exprs)
                                         (captVarsAt (pos, exprs elem (i-1)))
           | binding(_,(v,_),e)       -> assert (i = 0)
                                         (captVarsAt(pos,e) with v)
           | multiBinding(_,binds,e)  -> assert (i = 0)
                                         (let (vars, _) = unzip binds in
                                          captVarsAt(pos,e) \/ toSet vars)
           | cas(e,branches)          -> if i = 0 then captVarsAt(pos,e)
                                         else
                                           assert (1 <= i && i <= length branches)
                                           (let (patts, exprs) = unzip branches in
                                            pattVars (patts elem (i-1)) \/
                                            captVarsAt (pos, exprs elem (i-1)))
           | recursiveLet(asgments,e) -> let (binds, exprs) = unzip asgments in
                                         let (vars, _) = unzip binds in
                                         if i = 0
                                         then toSet vars \/ captVarsAt(pos,e)
                                         else
                                           assert (1 <= i && i <= length asgments)
                                           (toSet vars \/
                                            captVarsAt (pos, exprs elem (i-1)))
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
