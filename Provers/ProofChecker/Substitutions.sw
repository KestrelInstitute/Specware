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
    | boolean           -> boolean
    | variable tv       -> if definedAt?(sbs,tv)
                           then apply(sbs,tv)
                           else variable tv
    | instance(n,types) -> let newTypes = map (typeSubstInType sbs, types) in
                           instance(n,newTypes)
    | arrow(t1,t2)      -> arrow (typeSubstInType sbs t1,
                                  typeSubstInType sbs t2)
    | record comps      -> let (fields,types) = unzip comps in
                           let newTypes = map (typeSubstInType sbs, types) in
                           record (zip (fields, newTypes))
    | product types     -> let newTypes = map (typeSubstInType sbs, types) in
                           product newTypes
    | sum comps         -> let (constrs,types?) = unzip comps in
                           let newTypes? =
                               map (mapOption (typeSubstInType sbs), types?) in
                           sum (zip (constrs, newTypes?))
    | sub(t,e)          -> embed sub (typeSubstInType sbs t,
                                      typeSubstInExpr sbs e)
    | quotien(t,e)      -> quotien (typeSubstInType sbs t,
                                    typeSubstInExpr sbs e)

  def typeSubstInExpr sbs = fn
    | variable v                -> variable v
    | opInstance(opp,types)     -> opInstance
                                    (opp, map (typeSubstInType sbs, types))
    | application(e1,e2)        -> application (typeSubstInExpr sbs e1,
                                                typeSubstInExpr sbs e2)
    | abstraction((v,t),e)      -> abstraction ((v, typeSubstInType sbs t),
                                                typeSubstInExpr sbs e)
    | equation(e1,e2)           -> equation (typeSubstInExpr sbs e1,
                                             typeSubstInExpr sbs e2)
    | ifThenElse(e0,e1,e2)      -> ifThenElse (typeSubstInExpr sbs e0,
                                               typeSubstInExpr sbs e1,
                                               typeSubstInExpr sbs e2)
    | record comps              -> let (fields, exprs) = unzip comps in
                                   let newExprs =
                                       map (typeSubstInExpr sbs, exprs) in
                                   record (zip (fields, newExprs))
    | recordProjection(e,field) -> recordProjection
                                    (typeSubstInExpr sbs e, field)
    | recordUpdate(e1,e2)       -> recordUpdate (typeSubstInExpr sbs e1,
                                                 typeSubstInExpr sbs e2)
    | embedder(t,constr)        -> embedder (typeSubstInType sbs t, constr)
    | relaxator r               -> relaxator (typeSubstInExpr sbs r)
    | restriction(r,e)          -> restriction (typeSubstInExpr sbs r,
                                                typeSubstInExpr sbs e)
    | quotienter q              -> quotienter (typeSubstInExpr sbs q)
    | choice(q,e)               -> choice (typeSubstInExpr sbs q,
                                           typeSubstInExpr sbs e)
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
    | tru                       -> tru
    | fals                      -> fals
    | negation e                -> negation (typeSubstInExpr sbs e)
    | conjunction(e1,e2)        -> conjunction (typeSubstInExpr sbs e1,
                                                typeSubstInExpr sbs e2)
    | disjunction(e1,e2)        -> disjunction (typeSubstInExpr sbs e1,
                                                typeSubstInExpr sbs e2)
    | implication(e1,e2)        -> implication (typeSubstInExpr sbs e1,
                                                typeSubstInExpr sbs e2)
    | equivalence(e1,e2)        -> equivalence (typeSubstInExpr sbs e1,
                                                typeSubstInExpr sbs e2)
    | inequation(e1,e2)         -> inequation (typeSubstInExpr sbs e1,
                                               typeSubstInExpr sbs e2)
    | universal(binds,e)        -> let (vars,types) = unzip binds in
                                   let newTypes =
                                       map (typeSubstInType sbs, types) in
                                   universal (zip (vars, newTypes),
                                              typeSubstInExpr sbs e)
    | existential(binds,e)      -> let (vars,types) = unzip binds in
                                   let newTypes =
                                       map (typeSubstInType sbs, types) in
                                   existential (zip (vars, newTypes),
                                                typeSubstInExpr sbs e)
    | existential1((v,t),e)     -> existential1 ((v, typeSubstInType sbs t),
                                                 typeSubstInExpr sbs e)
    | nonRecursiveLet(p,e,e1)   -> nonRecursiveLet (typeSubstInPatt sbs p,
                                                    typeSubstInExpr sbs e,
                                                    typeSubstInExpr sbs e1)
    | tuple(exprs)              -> let newExprs =
                                       map (typeSubstInExpr sbs, exprs) in
                                   tuple newExprs
    | tupleProjection(e,i)      -> tupleProjection (typeSubstInExpr sbs e, i)

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
  types). We model them as finite maps. *)

  type ExpressionSubstitution = FMap(Name,Expression)

  op exprSubst : ExpressionSubstitution -> Expression -> Expression
  def exprSubst sbs = fn
    | variable v                -> if definedAt?(sbs,v)
                                   then apply(sbs,v)
                                   else variable v
    | opInstance(opp,types)     -> opInstance(opp,types)
    | application(e1,e2)        -> application (exprSubst sbs e1,
                                                exprSubst sbs e2)
    | abstraction((v,t),e)      -> let bodySbs = undefine (sbs, v) in
                                   abstraction ((v, t), exprSubst bodySbs e)
    | equation(e1,e2)           -> equation (exprSubst sbs e1,
                                             exprSubst sbs e2)
    | ifThenElse(e0,e1,e2)      -> ifThenElse (exprSubst sbs e0,
                                               exprSubst sbs e1,
                                               exprSubst sbs e2)
    | record comps              -> let (fields, exprs) = unzip comps in
                                   let newExprs =
                                       map (exprSubst sbs, exprs) in
                                   record (zip (fields, newExprs))
    | recordProjection(e,field) -> recordProjection
                                    (exprSubst sbs e, field)
    | recordUpdate(e1,e2)       -> recordUpdate (exprSubst sbs e1,
                                                 exprSubst sbs e2)
    | embedder(t,constr)        -> embedder (t, constr)
    | relaxator r               -> relaxator r
    | restriction(r,e)          -> restriction (r, exprSubst sbs e)
    | quotienter q              -> quotienter q
    | choice(q,e)               -> choice (q, exprSubst sbs e)
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
    | tru                       -> tru
    | fals                      -> fals
    | negation e                -> negation (exprSubst sbs e)
    | conjunction(e1,e2)        -> conjunction (exprSubst sbs e1,
                                                exprSubst sbs e2)
    | disjunction(e1,e2)        -> disjunction (exprSubst sbs e1,
                                                exprSubst sbs e2)
    | implication(e1,e2)        -> implication (exprSubst sbs e1,
                                                exprSubst sbs e2)
    | equivalence(e1,e2)        -> equivalence (exprSubst sbs e1,
                                                exprSubst sbs e2)
    | inequation(e1,e2)         -> inequation (exprSubst sbs e1,
                                               exprSubst sbs e2)
    | universal(binds,e)        -> let (vars,_) = unzip binds in
                                   let bodySbs =
                                       undefineMulti (sbs, toSet vars) in
                                   universal (binds, exprSubst bodySbs e)
    | existential(binds,e)      -> let (vars,_) = unzip binds in
                                   let bodySbs =
                                       undefineMulti (sbs, toSet vars) in
                                   existential (binds, exprSubst bodySbs e)
    | existential1((v,t),e)     -> let bodySbs = undefine (sbs, v) in
                                   existential1 ((v,t), exprSubst bodySbs e)
    | nonRecursiveLet(p,e,e1)   -> let bodySbs =
                                       undefineMulti (sbs, pattVars p) in
                                   nonRecursiveLet (p,
                                                    exprSubst sbs e,
                                                    exprSubst bodySbs e1)
    | tuple(exprs)              -> let newExprs =
                                       map (exprSubst sbs, exprs) in
                                   tuple newExprs
    | tupleProjection(e,i)      -> tupleProjection (exprSubst sbs e, i)

  % captured variables at free occurrences of given variable:
  op captVarsAtVar : Name -> Expression -> FSet Name
  def captVarsAtVar u = fn
    | application(e1,e2)       -> captVarsAtVar u e1 \/ captVarsAtVar u e2
    | abstraction((v,_),e)     -> if u in? exprFreeVars e && u ~= v
                                  then captVarsAtVar u e with v
                                  else empty
    | equation(e1,e2)          -> captVarsAtVar u e1 \/ captVarsAtVar u e2
    | ifThenElse(e0,e1,e2)     -> captVarsAtVar u e0 \/
                                  captVarsAtVar u e1 \/
                                  captVarsAtVar u e2
    | record comps             -> let (_, exprs) = unzip comps in
                                  unionAll (map (captVarsAtVar u, exprs))
    | recordProjection(e,_)    -> captVarsAtVar u e
    | recordUpdate(e1,e2)      -> captVarsAtVar u e1 \/ captVarsAtVar u e2
    | restriction(_,e)         -> captVarsAtVar u e
    | choice(_,e)              -> captVarsAtVar u e
    | cas(e,branches)          -> let (patts,exprs) = unzip branches in
                                  let varSets =
                                    seqSuchThat (fn(i:Nat) ->
                                      if i < length branches
                                      then if u in? exprFreeVars
                                                      (exprs elem i) &&
                                              ~(u in? pattVars (patts elem i))
                                           then Some (pattVars (patts elem i) \/
                                                      captVarsAtVar
                                                        u (exprs elem i))
                                           else Some empty
                                      else None) in
                                  unionAll varSets \/ captVarsAtVar u e
    | recursiveLet(asgments,e) -> let (binds,exprs) = unzip asgments in
                                  let (vars,_) = unzip binds in
                                  if (u in? exprFreeVars e ||
                                      (ex(i:Nat) i < length exprs &&
                                                 u in? exprFreeVars
                                                         (exprs elem i))) &&
                                     ~(u in? toSet vars)
                                  then toSet vars \/
                                       captVarsAtVar u e \/
                                       unionAll (map (captVarsAtVar u, exprs))
                                  else empty
    | negation e               -> captVarsAtVar u e
    | conjunction(e1,e2)       -> captVarsAtVar u e1 \/ captVarsAtVar u e2
    | disjunction(e1,e2)       -> captVarsAtVar u e1 \/ captVarsAtVar u e2
    | implication(e1,e2)       -> captVarsAtVar u e1 \/ captVarsAtVar u e2
    | equivalence(e1,e2)       -> captVarsAtVar u e1 \/ captVarsAtVar u e2
    | inequation(e1,e2)        -> captVarsAtVar u e1 \/ captVarsAtVar u e2
    | universal(binds,e)       -> let (vars,_) = unzip binds in
                                  if u in? exprFreeVars e &&
                                     ~(u in? vars)
                                  then toSet vars \/ captVarsAtVar u e
                                  else empty
    | existential(binds,e)     -> let (vars,_) = unzip binds in
                                  if u in? exprFreeVars e &&
                                     ~(u in? vars)
                                  then toSet vars \/ captVarsAtVar u e
                                  else empty
    | existential1((v,_),e)    -> if u in? exprFreeVars e && u ~= v
                                  then captVarsAtVar u e with v
                                  else empty
    | nonRecursiveLet(p,e,e1)  -> if u in? exprFreeVars e ||
                                     (u in? exprFreeVars e1 -- pattVars p)
                                  then captVarsAtVar u e \/
                                       pattVars p \/
                                       captVarsAtVar u e1
                                  else empty
    | tuple(exprs)             -> unionAll (map (captVarsAtVar u, exprs))
    | tupleProjection(e,_)     -> captVarsAtVar u e
    | _                        -> empty

  op exprSubstOK : Expression * ExpressionSubstitution -> Boolean
  def exprSubstOK(e,sbs) =
    (fa(v) v in? domain sbs =>
           exprFreeVars (apply(sbs,v)) /\ captVarsAtVar v e = empty)


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
    (fa (old:Type, new:Type)
       typeSubstAt (typ old, old, new, empty, typ new))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, n:Name, types:FSeq Type, newTi:Type)
       i < length types &&
       typeSubstAt (typ (types elem i), old, new, pos, typ newTi) =>
       typeSubstAt (typ (instance(n,types)), old, new, i |> pos,
                    typ (instance(n,update(types,i,newTi)))))
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
         i:Nat, fields:FSeq Name, types:FSeq Type, newTi:Type)
       i < length fields &&
       length fields = length types &&
       typeSubstAt (typ (types elem i), old, new, pos, typ newTi) =>
       typeSubstAt (typ (record (zip (fields, types))), old, new, i |> pos,
                    typ (record (zip (fields, update(types,i,newTi))))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, types:FSeq Type, newTi:Type)
       i < length types &&
       typeSubstAt (typ (types elem i), old, new, pos, typ newTi) =>
       typeSubstAt (typ (product types), old, new, i |> pos,
                    typ (product (update(types,i,newTi)))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, constrs:FSeqNE Name, types?:FSeqNE(Option Type),
         ti:Type, newTi:Type)
       i < length constrs &&
       length constrs = length types? &&
       types? elem i = Some ti &&
       typeSubstAt (typ ti, old, new, pos, typ newTi) =>
       typeSubstAt (typ (sum (zip (constrs, types?))), old, new, i |> pos,
                    typ (sum (zip (constrs, update(types?,i,Some newTi))))))
    &&
    (fa (old:Type, new:Type, pos:Position, t:Type, e:Expression, newT:Type)
       typeSubstAt (typ t, old, new, pos, typ newT) =>
       typeSubstAt (typ (embed sub(t,e)), old, new, 0 |> pos,
                    typ (embed sub(newT,e))))
    &&
    (fa (old:Type, new:Type, pos:Position, t:Type, e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (typ (embed sub(t,e)), old, new, 1 |> pos,
                    typ (embed sub(t,newE))))
    &&
    (fa (old:Type, new:Type, pos:Position, t:Type, e:Expression, newT:Type)
       typeSubstAt (typ t, old, new, pos, typ newT) =>
       typeSubstAt (typ (quotien(t,e)), old, new, 0 |> pos,
                    typ (quotien(newT,e))))
    &&
    (fa (old:Type, new:Type, pos:Position, t:Type, e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (typ (quotien(t,e)), old, new, 1 |> pos,
                    typ (quotien(t,newE))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, opp:Name, types:FSeq Type, newTi:Type)
       i < length types &&
       typeSubstAt (typ (types elem i), old, new, pos, typ newTi) =>
       typeSubstAt (expr (opInstance(opp,types)), old, new, i |> pos,
                    expr (opInstance(opp,update(types,i,newTi)))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE1:Expression)
       typeSubstAt (expr e1, old, new, pos, expr newE1) =>
       typeSubstAt (expr (application(e1,e2)), old, new, 1 |> pos,
                    expr (application(newE1,e2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE2:Expression)
       typeSubstAt (expr e2, old, new, pos, expr newE2) =>
       typeSubstAt (expr (application(e1,e2)), old, new, 2 |> pos,
                    expr (application(e1,newE2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         v:Name, t:Type, e:Expression, newT:Type)
       typeSubstAt (typ t, old, new, pos, typ newT) =>
       typeSubstAt (expr (abstraction((v,t),e)), old, new, 0 |> pos,
                    expr (abstraction((v,newT),e))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         v:Name, t:Type, e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (abstraction((v,t),e)), old, new, 1 |> pos,
                    expr (abstraction((v,t),newE))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE1:Expression)
       typeSubstAt (expr e1, old, new, pos, expr newE1) =>
       typeSubstAt (expr (equation(e1,e2)), old, new, 1 |> pos,
                    expr (equation(newE1,e2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE2:Expression)
       typeSubstAt (expr e2, old, new, pos, expr newE2) =>
       typeSubstAt (expr (equation(e1,e2)), old, new, 2 |> pos,
                    expr (equation(e1,newE2))))
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
         i:Nat, fields:FSeq Name, exprs:FSeq Expression, newEi:Expression)
       i < length fields &&
       length fields = length exprs &&
       typeSubstAt (expr (exprs elem i), old, new, pos, expr newEi) =>
       typeSubstAt (expr (record (zip (fields, exprs))), old, new, i |> pos,
                    expr (record (zip (fields, update(exprs,i,newEi))))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e:Expression, field:Name, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (recordProjection(e,field)), old, new, 0 |> pos,
                    expr (recordProjection(e,field))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE1:Expression)
       typeSubstAt (expr e1, old, new, pos, expr newE1) =>
       typeSubstAt (expr (recordUpdate(e1,e2)), old, new, 1 |> pos,
                    expr (recordUpdate(newE1,e2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE2:Expression)
       typeSubstAt (expr e2, old, new, pos, expr newE2) =>
       typeSubstAt (expr (recordUpdate(e1,e2)), old, new, 2 |> pos,
                    expr (recordUpdate(e1,newE2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         t:Type, constr:Name, newT:Type)
       typeSubstAt (typ t, old, new, pos, typ newT) =>
       typeSubstAt (expr (embedder(t,constr)), old, new, 0 |> pos,
                    expr (embedder(t,constr))))
    &&
    (fa (old:Type, new:Type, pos:Position, r:Expression, newR:Expression)
       typeSubstAt (expr r, old, new, pos, expr newR) =>
       typeSubstAt (expr (relaxator r), old, new, 0 |> pos,
                    expr (relaxator newR)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         r:Expression, e:Expression, newR:Expression)
       typeSubstAt (expr r, old, new, pos, expr newR) =>
       typeSubstAt (expr (restriction(r,e)), old, new, 0 |> pos,
                    expr (restriction(newR,e))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         r:Expression, e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (restriction(r,e)), old, new, 1 |> pos,
                    expr (restriction(r,newE))))
    &&
    (fa (old:Type, new:Type, pos:Position, q:Expression, newQ:Expression)
       typeSubstAt (expr q, old, new, pos, expr newQ) =>
       typeSubstAt (expr (quotienter q), old, new, 0 |> pos,
                    expr (quotienter newQ)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         q:Expression, e:Expression, newQ:Expression)
       typeSubstAt (expr q, old, new, pos, expr newQ) =>
       typeSubstAt (expr (choice(q,e)), old, new, 0 |> pos,
                    expr (choice(newQ,e))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         q:Expression, e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (choice(q,e)), old, new, 1 |> pos,
                    expr (choice(q,newE))))
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
    (fa (old:Type, new:Type, pos:Position, e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (negation e), old, new, 0 |> pos,
                    expr (negation newE)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE1:Expression)
       typeSubstAt (expr e1, old, new, pos, expr newE1) =>
       typeSubstAt (expr (conjunction(e1,e2)), old, new, 1 |> pos,
                    expr (conjunction(newE1,e2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE2:Expression)
       typeSubstAt (expr e2, old, new, pos, expr newE2) =>
       typeSubstAt (expr (conjunction(e1,e2)), old, new, 2 |> pos,
                    expr (conjunction(e1,newE2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE1:Expression)
       typeSubstAt (expr e1, old, new, pos, expr newE1) =>
       typeSubstAt (expr (disjunction(e1,e2)), old, new, 1 |> pos,
                    expr (disjunction(newE1,e2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE2:Expression)
       typeSubstAt (expr e2, old, new, pos, expr newE2) =>
       typeSubstAt (expr (disjunction(e1,e2)), old, new, 2 |> pos,
                    expr (disjunction(e1,newE2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE1:Expression)
       typeSubstAt (expr e1, old, new, pos, expr newE1) =>
       typeSubstAt (expr (implication(e1,e2)), old, new, 1 |> pos,
                    expr (implication(newE1,e2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE2:Expression)
       typeSubstAt (expr e2, old, new, pos, expr newE2) =>
       typeSubstAt (expr (implication(e1,e2)), old, new, 2 |> pos,
                    expr (implication(e1,newE2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE1:Expression)
       typeSubstAt (expr e1, old, new, pos, expr newE1) =>
       typeSubstAt (expr (inequation(e1,e2)), old, new, 1 |> pos,
                    expr (inequation(newE1,e2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e1:Expression, e2:Expression, newE2:Expression)
       typeSubstAt (expr e2, old, new, pos, expr newE2) =>
       typeSubstAt (expr (inequation(e1,e2)), old, new, 2 |> pos,
                    expr (inequation(e1,newE2))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, vars:FSeqNE Name, types:FSeqNE Type, e:Expression, newTi:Type)
       i < length vars &&
       length vars = length types &&
       typeSubstAt (typ (types elem i), old, new, pos, typ newTi) =>
       typeSubstAt (expr (universal (zip (vars, types), e)), old, new, i |> pos,
                    expr (universal (zip (vars, update(types,i,newTi)), e))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         binds:FSeqNE(Name*Type), e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (universal (binds, e)), old, new, 0 |> pos,
                    expr (universal (binds, newE))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, vars:FSeqNE Name, types:FSeqNE Type, e:Expression, newTi:Type)
       i < length vars &&
       length vars = length types &&
       typeSubstAt (typ (types elem i), old, new, pos, typ newTi) =>
       typeSubstAt (expr (existential (zip (vars, types), e)), old, new, i |> pos,
                    expr (existential (zip (vars, update(types,i,newTi)), e))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         binds:FSeqNE(Name*Type), e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (existential (binds, e)), old, new, 0 |> pos,
                    expr (existential (binds, newE))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         v:Name, t:Type, e:Expression, newT:Type)
       typeSubstAt (typ t, old, new, pos, typ newT) =>
       typeSubstAt (expr (existential1((v,t),e)), old, new, 0 |> pos,
                    expr (existential1((v,newT),e))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         v:Name, t:Type, e:Expression, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (existential1((v,t),e)), old, new, 1 |> pos,
                    expr (existential1((v,t),newE))))
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
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, exprs:FSeq Expression, newEi:Expression)
       i < length exprs &&
       typeSubstAt (expr (exprs elem i), old, new, pos, expr newEi) =>
       typeSubstAt (expr (tuple exprs), old, new, i |> pos,
                    expr (tuple (update(exprs,i,newEi)))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e:Expression, i:Nat, newE:Expression)
       typeSubstAt (expr e, old, new, pos, expr newE) =>
       typeSubstAt (expr (tupleProjection(e,i)), old, new, 0 |> pos,
                    expr (tupleProjection(e,i))))
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




endspec
