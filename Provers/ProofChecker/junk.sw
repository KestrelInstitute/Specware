(* This file contains stuff that has been written but then eliminated. It is
kept around (in this file) for a while in case it later turns out to be useful
again. *)



%%% unique kind of names:

spec

  import Libs/MyBase

  (* As in LD, we leave names abstract because the logic is parameterized
  over them. In addition, this allows us to refine them in different ways,
  obtaining different instances of the proof checker. *)

  (* We use the library spec for infinite types in order to impose the
  requirement, also present in LD, that there are infinite names. *)

  import translate Libs/Type#Infinite by {X +-> Name}

  (* Unlike LD, we do not set aside particular names for projections, because
  we model product types (vs. record types) explicitly. This also simplifies
  refining names, because there are fewer requirements that their refinement
  must satisfy. *)

endspec



%%% abbreviations for factored expressions:

  op exprVariable : Name -> Expression
  def exprVariable v = nullary (variable v)

  op opInstance : Name * FSeq Type -> Expression
  def opInstance(n,types) = nullary (embed opInstance(n,types))

  op exprEmbedder : Type * Name -> Expression
  def exprEmbedder(t,constr) = nullary (embedder(t,constr))

  op exprTrue : Expression
  def exprTrue = nullary tru

  op exprFalse : Expression
  def exprFalse = nullary fals



%%% non-factored definition of types and expressions, along with ops on them:

  type Type =
    | boolean
    | variable     Name
    | instance     Name * FSeq Type
    | arrow        Type * Type
    | record       FSeq (Name * Type)
    | product      FSeq Type
    | sum          FSeqNE (Name * Option Type)
    | sub          Type * Expression
    | quotien(*t*) Type * Expression

  type Expression =
    | variable         Name
    | opInstance       Name * FSeq Type
    | application      Expression * Expression
    | abstraction      TypedVar * Expression
    | equation         Expression * Expression
    | ifThenElse       Expression * Expression * Expression
    | record           FSeq (Name * Expression)
    | recordProjection Expression * Name
    | recordUpdate     Expression * Expression
    | embedder         Type * Name
    | relaxator        Expression
    | restriction      Expression * Expression
    | quotienter       Expression
    | choice           Expression * Expression
    | cas(*e*)         Expression * FSeqNE (Pattern * Expression)
    | recursiveLet     FSeqNE (TypedVar * Expression) * Expression
    | tru(*e*)
    | fals(*e*)
    | negation         Expression
    | conjunction      Expression * Expression
    | disjunction      Expression * Expression
    | implication      Expression * Expression
    | equivalence      Expression * Expression
    | inequation       Expression * Expression
    | universal        (FSeqNE TypedVar) * Expression
    | existential      (FSeqNE TypedVar) * Expression
    | existential1     TypedVar * Expression
    | nonRecursiveLet  Pattern * Expression * Expression
    | tuple            FSeqNE Expression
    | tupleProjection  Expression * PosNat

  axiom inductionTypesExpressionsPatterns is
    fa (pred : Predicate TypeOrExprOrPatt)
      pred (typ boolean)
   && (fa (tVar:Name) pred (typ (variable tVar)))
   && (fa (tName:Name, types:FSeq Type)
         (fa(t) t in? types => pred (typ t))
      => pred (typ (instance (tName, types))))
   && (fa (t1:Type, t2:Type)
         pred (typ t1) && pred (typ t2)
      => pred (typ (arrow (t1, t2))))
   && (fa (fields:FSeq Name, types:FSeq Type)
         length fields = length types
      && (fa(t) t in? types => pred (typ t))
      => pred (typ (record (zip (fields, types)))))
   && (fa (types:FSeq Type)
         (fa(t) t in? types => pred (typ t))
      => pred (typ (product types)))
   && (fa (constrs:FSeqNE Name, types?:FSeqNE(Option Type))
         length constrs = length types?
      && (fa(t) Some t in? types? => pred (typ t))
      => pred (typ (sum (zip (constrs, types?)))))
   && (fa (t:Type, e:Expression)
         pred (typ t) && pred (expr e)
      => pred (typ (embed sub (t, e)))  % w/o embed, type checker crashes
      && pred (typ (quotien   (t, e))))
   && (fa (var:Name) pred (expr (variable var)))
   && (fa (opp:Name, types:FSeq Type)
         (fa(t) t in? types => pred (typ t))
      => pred (expr (opInstance (opp, types))))
   && (fa (e1:Expression, e2:Expression)
         pred (expr e1) && pred (expr e2)
      => pred (expr (application  (e1, e2)))
      && pred (expr (equation     (e1, e2)))
      && pred (expr (recordUpdate (e1, e2)))
      && pred (expr (restriction  (e1, e2)))
      && pred (expr (choice       (e1, e2)))
      && pred (expr (conjunction  (e1, e2)))
      && pred (expr (disjunction  (e1, e2)))
      && pred (expr (implication  (e1, e2)))
      && pred (expr (equivalence  (e1, e2)))
      && pred (expr (inequation   (e1, e2))))
   && (fa (t:Type, var:Name, e:Expression)
         pred (typ t) && pred (expr e)
      => pred (expr (abstraction ((var, t), e))))
   && (fa (e0:Expression, e1:Expression, e2:Expression)
         pred (expr e0) && pred (expr e1) && pred (expr e2)
      => pred (expr (ifThenElse (e0, e1, e2))))
   && (fa (fields:FSeq Name, exprs:FSeq Expression)
         length fields = length exprs
      && (fa(e) e in? exprs => pred (expr e))
      => pred (expr (record (zip (fields, exprs)))))
   && (fa (e:Expression, field:Name)
         pred (expr e)
      => pred (expr (recordProjection (e, field))))
   && (fa (t:Type, constr:Name)
         pred (typ t)
      => pred (expr (embedder (t, constr))))
   && (fa (e:Expression)
         pred (expr e)
      => pred (expr (relaxator  e))
      && pred (expr (quotienter e))
      && pred (expr (negation   e)))
   && (fa (e:Expression, patts:FSeqNE Pattern, exprs:FSeqNE Expression)
         length patts = length exprs
      && (fa(p) p in? patts => pred (patt p))
      && (fa(e1) e1 in? exprs => pred (expr e1))
      => pred (expr (cas (e, zip (patts, exprs)))))
   && (fa (vars:FSeqNE Name, types:FSeqNE Type, exprs:FSeq Expression,
           e:Expression)
         length vars  = length types
      && length types = length exprs
      && (fa(t) t in? types => pred (typ t))
      && (fa(e1) e1 in? exprs => pred (expr e1))
      && pred (expr e)
      => pred (expr (recursiveLet (zip (zip (vars, types), exprs), e))))
   && pred (expr tru)
   && pred (expr fals)
   && (fa (vars:FSeqNE Name, types:FSeqNE Type, e:Expression)
         (fa(t) t in? types => pred (typ t))
      && pred (expr e)
      => pred (expr (universal   (zip (vars, types), e)))
      && pred (expr (existential (zip (vars, types), e))))
   && (fa (var:Name, t:Type, e:Expression)
         pred (typ t)
      && pred (expr e)
      => pred (expr (existential1 ((var, t), e))))
   && (fa (p:Pattern, e:Expression, e1:Expression)
         pred (patt p)
      && pred (expr e)
      && pred (expr e1)
      => pred (expr (nonRecursiveLet (p, e, e1))))
   && (fa (exprs:FSeqNE Expression)
         (fa(e) e in? exprs => pred (expr e))
      => pred (expr (tuple exprs)))
   && (fa (e:Expression, i:PosNat)
         pred (expr e)
      => pred (expr (tupleProjection (e, i))))
   && (fa (var:Name, t:Type)
         pred (typ t)
      => pred (patt (variable (var, t))))
   && (fa (t:Type, constr:Name, p:Pattern)
         pred (typ t)
      && pred (patt p)
      => pred (patt (embedding (t, constr, p))))
   && (fa (fields:FSeq Name, patts:FSeq Pattern)
         (fa(p) p in? patts => pred (patt p))
      => pred (patt (record (zip (fields, patts)))))
   && (fa (var:Name, t:Type, p:Pattern)
         pred (typ t)
      && pred (patt p)
      => pred (patt (alias ((var, t), p))))

  def exprFreeVars = fn
    | variable v               -> singleton v
    | opInstance _             -> empty
    | application(e1,e2)       -> exprFreeVars e1 \/ exprFreeVars e2
    | abstraction((v,_),e)     -> exprFreeVars e wout v
    | equation(e1,e2)          -> exprFreeVars e1 \/ exprFreeVars e2
    | ifThenElse(e0,e1,e2)     -> exprFreeVars e0 \/
                                  exprFreeVars e1 \/ exprFreeVars e2
    | record comps             -> let (_, exprs) = unzip comps in
                                  exprSeqFreeVars exprs
    | recordProjection(e,_)    -> exprFreeVars e
    | recordUpdate(e1,e2)      -> exprFreeVars e1 \/ exprFreeVars e2
    | embedder _               -> empty
    | relaxator _              -> empty
    | restriction(_,e)         -> exprFreeVars e
    | quotienter _             -> empty
    | choice(_,e)              -> exprFreeVars e
    | cas(e,branches)          -> let (patts,exprs) = unzip branches in
                                  let varSets =
                                      seqSuchThat (fn(i:Nat) ->
                                        if i < length branches
                                        then Some (exprFreeVars (exprs elem i) --
                                                   pattVars     (patts elem i))
                                        else None) in
                                  let def branchVars
                                          (e:Expression, p:Pattern) : FSet Name =
                                          exprFreeVars e -- pattVars p in
                                  unionAll (map2 (branchVars, exprs, patts))
                                  \/ exprFreeVars e
    | recursiveLet(asgments,e) -> let (binds, exprs) = unzip asgments in
                                  let (vars, _) = unzip binds in
                                  (exprSeqFreeVars exprs \/ exprFreeVars e)
                                  -- toSet vars
    | tru                      -> empty
    | fals                     -> empty
    | negation e               -> exprFreeVars e
    | conjunction(e1,e2)       -> exprFreeVars e1 \/ exprFreeVars e2
    | disjunction(e1,e2)       -> exprFreeVars e1 \/ exprFreeVars e2
    | implication(e1,e2)       -> exprFreeVars e1 \/ exprFreeVars e2
    | equivalence(e1,e2)       -> exprFreeVars e1 \/ exprFreeVars e2
    | inequation(e1,e2)        -> exprFreeVars e1 \/ exprFreeVars e2
    | universal(binds,e)       -> let (vars, _) = unzip binds in
                                  exprFreeVars e -- toSet vars
    | existential(binds,e)     -> let (vars, _) = unzip binds in
                                  exprFreeVars e -- toSet vars
    | existential1((v,_),e)    -> exprFreeVars e wout v
    | nonRecursiveLet(p,e,e1)  -> exprFreeVars e \/
                                  (exprFreeVars e1 -- pattVars p)
    | tuple exprs              -> exprSeqFreeVars exprs
    | tupleProjection(e,_)     -> exprFreeVars e

  op patt2expr : Pattern -> Expression
  def patt2expr = fn
    | variable(v,_)           -> variable v
    | embedding(typ,constr,p) -> application (embedder (typ, constr),
                                              patt2expr p)
    | record comps            -> let (fields, patts) = unzip comps in
                                 let exprs = map (patt2expr, patts) in
                                 record (zip (fields, exprs))
    | alias(_,p)              -> patt2expr p

  op pattBindings : Pattern -> FSeq TypedVar
  def pattBindings = fn
    | variable tvar           -> singleton tvar
    | embedding(typ,constr,p) -> pattBindings p
    | record comps            -> let (_, patts) = unzip comps in
                                 flatten (map (pattBindings, patts))
    | alias(tvar,p)           -> tvar |> pattBindings p

  op pattAliasAssumptions : Pattern -> Expression
  def pattAliasAssumptions = fn
    | variable _       -> tru
    | embedding(_,_,p) -> pattAliasAssumptions p
    | record comps     -> let (_, patts) = unzip comps in
                          conjoinAll (map (pattAliasAssumptions, patts))
    | alias((v,_),p)   -> conjunction (equation (variable v,
                                                 patt2expr p),
                                       pattAliasAssumptions p)

  op pattAssumptions : Pattern * Expression -> Expression
  def pattAssumptions(p,e) =
    conjunction (equation (e, patt2expr p), pattAliasAssumptions p)

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


%%% functional version of positional type substitution:

  (* In LD, type substitutions at positions are formalized via a relation. Here,
  we use a function that corresponds to that relation, using an `Option' type
  to model the fact that the substitution is disallowed (e.g. because the
  position is not valid. *)

  op typeSubstInTypeAt : Type       * Type * Type * Position -> Option Type
  op typeSubstInExprAt : Expression * Type * Type * Position -> Option Expression
  op typeSubstInPattAt : Pattern    * Type * Type * Position -> Option Pattern

  def typeSubstInTypeAt(t,t1,t2,pos) =
    if pos = empty
    then if t = t1
         then Some t2
         else None
    else let i = first pos in
         case t of
           | instance(n,types) ->
             if i < length types
             then (case typeSubstInTypeAt (types elem i, t1, t2, rtail pos) of
                     | Some newTi -> Some (instance (n, update(types,i,newTi)))
                     | None       -> None)
             else None
           % TO BE CONTINUED.............


%%% more verbose def of types:

  type VariableType = Name

  type InstanceType = {typ  : Name,
                       args : FSeq Type}

  type ArrowType = {dom : Type,
                    cod : Type}

  type RecordTypeComponent = {field : Name,
                              typ   : Type}

  type RecordType = {comps : FSeq RecordTypeComponent |
                     (let fields = map (project field, comps) in
                      noRepetitions? fields)}

  type SumTypeComponent = {constr : Name, % constr(uctor)
                           typ    : Type}

  type ProductType = {comps : FSeq Type | length comps >= 2}

  type SumType = {comps : FSeqNE SumTypeComponent |
                  (let constrs = map (project constr, comps) in
                  noRepetitions? constrs)}

  type SubType = {base : Type,
                  pred : Expression}

  type QuotientType = {base : Type,
                       pred : Expression}

  type Type =
    | booleanType
    | var  VariableType
    | inst InstanceType
    | arr  ArrowType
    | rec  RecordType
    | prod ProductType
    | sum  SumType
    | sub  SubType
    | quot QuotientType


%%% more verbose def of expressions:


  type VariableExpr = Name

  type OpInstance = {opp    : Name,
                     tyArgs : FSeq Type}

  type FunctionApplication = {func: Expression,
                              arg : Expression}

  type LambdaAbstraction = {arg     : Name,
                            argType : Type,
                            body    : Expression}

  type Equation = {left  : Expression,
                   right : Expression}

  type IfThenElse = {cond : Expression,
                     thn  : Expression,
                     els  : Expression}

  type RecordExprComponent = {field : Name,
                              expr  : Expression}

  type RecordExpr = {comps : FSeq RecordExprComponent |
                     (let fields = map (project field, comps) in
                      noRepetitions? fields)}

  type RecordProjection = {rec   : Expression,
                           field : Name}

  type RecordUpdate = {updatee : Expression,
                       updater : Expression}

  type Embedder = {typ    : SumType,
                   constr : Name}

  type Relaxator = Expression

  type RestrictExpr = {pred : Expression,
                       arg  : Expression}

  type Quotienter = Expression

  type ChooseExpr = {pred : Expression,
                     arg  : Expression}

  type CaseBranch = {pat    : Pattern,
                     result : Expression}

  type CaseExpr = {target   : Expression,
                   branches : FSeq CaseBranch}

  type LetRecBinding = {var  : Name,
                        typ  : Type,
                        expr : Expression}

  type LetRecExpr = {binds : {binds : FSeq LetRecBinding |
                              (let vars = map (project var, binds) in
                               noRepetitions? vars)},
                     body  : Expression}

  type NotExpr = Expression

  type AndExpr = {left  : Expression,
                  right : Expression}

  type OrExpr = {left  : Expression,
                 right : Expression}

  type ImpliesExpr = {antec  : Expression,
                      conseq : Expression}

  type IffExpr = {left  : Expression,
                  right : Expression}

  type Inequation = {left  : Expression,
                     right : Expression}

  type ForAllExpr = {var     : Name,
                     varType : Type,
                     body    : Expression}

  type ExistsExpr = {var     : Name,
                     varType : Type,
                     body    : Expression}

  type Exists1Expr = {var     : Name,
                      varType : Type,
                      body    : Expression}

  type LetExpr = {pat   : Pattern,
                  expr  : Expression,
                  body  : Expression}

  type TupleExpr = {comps : FSeq Expression | length comps >= 2}

  type TupleProjection = {tup   : Expression,
                          field : PosNat}   % like record projection
                                            % but number instead of name

  type Expression =
    | var   VariableExpr
    | opi   OpInstance
    | app   FunctionApplication
    | abs   LambdaAbstraction
    | eq    Equation
    | ifte  IfThenElse
    | rec   RecordExpr
    | rproj RecordProjection
    | rupd  RecordUpdate
    | emb   Embedder
    | relx  Relaxator
    | restr RestrictExpr
    | quot  Quotienter
    | choos ChooseExpr
    | cas   CaseExpr
    | letr  LetRecExpr
    | trueExpr
    | falseExpr
    | neg   NotExpr
    | conj  AndExpr
    | disj  OrExpr
    | impl  ImpliesExpr
    | iff   IffExpr
    | neq   Inequation
    | fall  ForAllExpr
    | exis  ExistsExpr
    | exis1 Exists1Expr
    | tup   TupleExpr
    | tproj TupleProjection
