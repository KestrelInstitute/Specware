spec

  import Judgements


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % N-ary conjunction and disjunction:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op conjoinAll : Expressions -> Expression
  def conjoinAll =
    the (fn (conjoinAll : Expressions -> Expression) ->
      (conjoinAll empty = nullary tru) &&
      (fa(e) conjoinAll (singleton e) = e) &&
      (fa(e,exprs) exprs ~= empty =>
                   conjoinAll (e |> exprs) =
                   binary (conjunction, e, conjoinAll exprs)))

  op disjoinAll : Expressions -> Expression
  def disjoinAll =
    the (fn (disjoinAll : Expressions -> Expression) ->
      (disjoinAll empty = nullary fals) &&
      (fa(e) disjoinAll (singleton e) = e) &&
      (fa(e,exprs) exprs ~= empty =>
                   disjoinAll (e |> exprs) =
                   binary (disjunction, e, disjoinAll exprs)))


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % conversion of a pattern into an expression:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op patt2expr : Pattern -> Expression
  def patt2expr = fn
    | variable(v,_)    -> nullary (variable v)
    | embedding(t,c,p) -> binary (application,
                                  embedder (t, c),
                                  patt2expr p)
    | record(fS,pS)    -> let eS = map (patt2expr, pS) in
                          nary (record fS, eS)
    | alias(_,p)       -> patt2expr p


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % assumptions engendered by a pattern:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op pattAliasAssumptions : Pattern -> Expression
  def pattAliasAssumptions = fn
    | variable _       -> nullary tru
    | embedding(_,_,p) -> pattAliasAssumptions p
    | record(_,pS)     -> conjoinAll (map (pattAliasAssumptions, pS))
    | alias((v,_),p)   -> binary (conjunction,
                                  binary (equation,
                                          nullary (variable v),
                                          patt2expr p),
                                  pattAliasAssumptions p)

  op pattAssumptions : Pattern * Expression -> Expression
  def pattAssumptions(p,e) =
    binary (conjunction,
            binary (equation, e, patt2expr p),
            pattAliasAssumptions p)


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % variables bound by a pattern:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op pattBoundVars : Pattern -> BoundVars
  def pattBoundVars = fn
    | variable bv      -> singleton bv
    | embedding(t,c,p) -> pattBoundVars p
    | record(_,pS)     -> flatten (map (pattBoundVars, pS))
    | alias(bv,p)      -> bv |> pattBoundVars p

  op pattVars : Pattern -> FSet Variable
  def pattVars p =
    let (vS,_) = unzip (pattBoundVars p) in
    toSet vS


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % free variables in an expression:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* In LD, free variables of subtype and quotient type predicates are not
  considered in the syntax because the well-typedness rules for expression
  force such predicates to have no free variables. However, here it is easier
  to consider them because of the way we have factored expressions. *)

  op exprFreeVars : Expression -> FSet Variable
  def exprFreeVars = fn
    | nullary(variable v)     -> singleton v
    | unary(_,e)              -> exprFreeVars e
    | binary(_,e1,e2)         -> exprFreeVars e1 \/ exprFreeVars e2
    | ifThenElse(e0,e1,e2)    -> exprFreeVars e0 \/
                                 exprFreeVars e1 \/
                                 exprFreeVars e2
    | nary(_,eS)              -> unionAll (map (exprFreeVars, eS))
    | binding(_,bvS,e)        -> let (vS, _) = unzip bvS in
                                 exprFreeVars e -- toSet vS
    | cas(e,branches)         -> let (pS, eS) = unzip branches in
                                 let vSets =
                                     seqSuchThat (fn(i:Nat) ->
                                       if i < length branches
                                       then Some (exprFreeVars (eS elem i) --
                                                  pattVars     (pS elem i))
                                       else None) in
                                 unionAll vSets \/ exprFreeVars e
    | recursiveLet(bvS,eS,e)  -> let (vS, _) = unzip bvS in
                                 (unionAll (map (exprFreeVars, eS)) \/
                                  exprFreeVars e) -- toSet vS
    | nonRecursiveLet(p,e,e1) -> exprFreeVars e \/
                                 (exprFreeVars e1 -- pattVars p)
    | _                       -> empty


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % items declared in a context:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op contextElementTypeNames : ContextElement -> FSet TypeName
  op contextElementOps       : ContextElement -> FSet Operation
  op contextElementTypeVars  : ContextElement -> FSet TypeVariable
  op contextElementVars      : ContextElement -> FSet Variable

  def contextElementTypeNames = fn
    | typeDeclaration(tn,_) -> singleton tn
    | _                     -> empty

  def contextElementOps = fn
    | opDeclaration(o,_,_) -> singleton o
    | _                    -> empty

  def contextElementTypeVars = fn
    | tVarDeclaration tv -> singleton tv
    | _                  -> empty

  def contextElementVars = fn
    | varDeclaration(v,_) -> singleton v
    | _                   -> empty

  op contextTypeNames : Context -> FSet TypeName
  op contextOps       : Context -> FSet Operation
  op contextTypeVars  : Context -> FSet TypeVariable
  op contextVars      : Context -> FSet Variable

  def contextTypeNames cx = unionAll (map (contextElementTypeNames, cx))
  def contextOps       cx = unionAll (map (contextElementOps,       cx))
  def contextTypeVars  cx = unionAll (map (contextElementTypeVars,  cx))
  def contextVars      cx = unionAll (map (contextElementVars,      cx))


  %%%%%%%%%%%%%%%%%%%%%
  % type substitutions:
  %%%%%%%%%%%%%%%%%%%%%

  (* While in LD type substitutions are describes by a sequence of distinct
  type variables and a sequence of types of the same length, here we use
  finite maps from type variables to types. *)

  type TypeSubstitution = FMap (TypeVariable, Type)

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
    | sum(cS,t?S)     -> let newT?S =
                             map (mapOption (typeSubstInType sbs), t?S) in
                         sum (cS, newT?S)
    | nary(tc,tS)     -> let newTS = map (typeSubstInType sbs, tS) in
                         nary (tc, newTS)
    | subQuot(tc,t,e) -> subQuot (tc,
                                  typeSubstInType sbs t,
                                  typeSubstInExpr sbs e)

  def typeSubstInExpr sbs = fn
    | unary(eo,e)            -> unary (eo, typeSubstInExpr sbs e)
    | binary(eo,e1,e2)       -> binary (eo,
                                        typeSubstInExpr sbs e1,
                                        typeSubstInExpr sbs e2)
    | ifThenElse(e0,e1,e2)   -> ifThenElse (typeSubstInExpr sbs e0,
                                            typeSubstInExpr sbs e1,
                                            typeSubstInExpr sbs e2)
    | nary(eo,eS)            -> let newES = map (typeSubstInExpr sbs, eS) in
                                nary (eo, newES)
    | binding(eo,bvS,e)      -> let (vS,tS) = unzip bvS in
                                let newTS = map (typeSubstInType sbs, tS) in
                                binding (eo,
                                         zip (vS, newTS),
                                         typeSubstInExpr sbs e)
    | opInstance(o,tS)        -> opInstance
                                  (o, map (typeSubstInType sbs, tS))
    | embedder(t,c)           -> embedder (typeSubstInType sbs t, c)
    | cas(e,branches)         -> let (pS,eS) = unzip branches in
                                 let newPS = map (typeSubstInPatt sbs, pS) in
                                 let newES = map (typeSubstInExpr sbs, eS) in
                                 cas (typeSubstInExpr sbs e,
                                      zip (newPS, newES))
    | recursiveLet(bvS,eS,e)  -> let (vS,tS) = unzip bvS in
                                 let newTS = map (typeSubstInType sbs, tS) in
                                 let newES = map (typeSubstInExpr sbs, eS) in
                                 let newBvS = zip (vS, newTS) in
                                 recursiveLet
                                  (newBvS, newES, typeSubstInExpr sbs e)
    | nonRecursiveLet(p,e,e1) -> nonRecursiveLet (typeSubstInPatt sbs p,
                                                  typeSubstInExpr sbs e,
                                                  typeSubstInExpr sbs e1)
    | e                        -> e

  def typeSubstInPatt sbs = fn
    | variable(v,t)    -> variable (v, typeSubstInType sbs t)
    | embedding(t,c,p) -> embedding (typeSubstInType sbs t,
                                     c,
                                     typeSubstInPatt sbs p)
    | record(fS,pS)    -> let newPS = map (typeSubstInPatt sbs, pS) in
                          record (fS, newPS)
    | alias((v,t),p)   -> alias ((v, typeSubstInType sbs t),
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

  type ExpressionSubstitution = FMap (Variable, Expression)

  op exprSubst : ExpressionSubstitution -> Expression -> Expression
  def exprSubst sbs = fn
    | nullary(variable v)     -> if definedAt?(sbs,v)
                                 then apply(sbs,v)
                                 else nullary(variable v)
    | unary(eo,e)             -> unary (eo, exprSubst sbs e)
    | binary(eo,e1,e2)        -> binary (eo, exprSubst sbs e1, exprSubst sbs e2)
    | ifThenElse(e0,e1,e2)    -> ifThenElse (exprSubst sbs e0,
                                             exprSubst sbs e1,
                                             exprSubst sbs e2)
    | nary(eo,eS)             -> let newES = map (exprSubst sbs, eS) in
                                 nary (eo, newES)
    | binding(eo,bvS,e)       -> let (vS,_) = unzip bvS in
                                 let bodySbs = undefineMulti (sbs, toSet vS) in
                                 binding (eo, bvS, exprSubst bodySbs e)
    | opInstance(o,tS)        -> opInstance(o,tS)
    | embedder(t,c)           -> embedder (t, c)
    | cas(e,branches)         -> let (pS,eS) = unzip branches in
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
                                 cas (exprSubst sbs e, zip (pS, newES))
    | recursiveLet(bvS,eS,e)  -> let (vS,_) = unzip bvS in
                                 let bodySbs = undefineMulti (sbs, toSet vS) in
                                 let newES = map (exprSubst bodySbs, eS) in
                                 recursiveLet (bvS, newES, exprSubst sbs e)
    | nonRecursiveLet(p,e,e1) -> let bodySbs =
                                     undefineMulti (sbs, pattVars p) in
                                 nonRecursiveLet (p,
                                                  exprSubst sbs e,
                                                  exprSubst bodySbs e1)
    | e                       -> e


  % captured variables at free occurrences of given variable:
  op captVars : Variable -> Expression -> FSet Variable
  def captVars u = fn
    | unary(_,e)              -> captVars u e
    | binary(_,e1,e2)         -> captVars u e1 \/ captVars u e2
    | ifThenElse(e0,e1,e2)    -> captVars u e0 \/
                                 captVars u e1 \/
                                 captVars u e2
    | nary(_,eS)              -> unionAll (map (captVars u, eS))
    | binding(_,bvS,e)        -> let (vS,_) = unzip bvS in
                                 if u in? exprFreeVars e && ~(u in? vS)
                                 then toSet vS \/ captVars u e
                                 else empty
    | cas(e,branches)         -> let (pS,eS) = unzip branches in
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
    | recursiveLet(bvS,eS,e)  -> let (vS,_) = unzip bvS in
                                 if (u in? exprFreeVars e ||
                                     (ex(e1)
                                        e1 in? eS && u in? exprFreeVars e1)) &&
                                    ~(u in? toSet vS)
                                 then toSet vS \/
                                      captVars u e \/
                                      unionAll (map (captVars u, eS))
                                 else empty
    | nonRecursiveLet(p,e,e1) -> if u in? exprFreeVars e ||
                                    (u in? exprFreeVars e1 -- pattVars p)
                                 then captVars u e \/
                                      pattVars p \/
                                      captVars u e1
                                 else empty
    | _                       -> empty

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
    | alias((v,t),p)   -> if v = old
                          then alias ((new, t), pattSubst (old,new) p)
                          else alias ((v,   t), pattSubst (old,new) p)


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % type substitution at position:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  type Position = FSeq Nat

  op typeSubstInTypeAt :
     Type * Type * Type * Position * Type -> Boolean

  op typeSubstInExprAt :
     Expression * Type * Type * Position * Expression -> Boolean

  op typeSubstInPattAt :
     Pattern * Type * Type * Position * Pattern -> Boolean

  def typeSubstInTypeAt = min (fn typeSubstInTypeAt ->
    (fa (old:Type, new:Type)
       typeSubstInTypeAt (old, old, new, empty, new))
    &&
    (fa (old:Type, new:Type, pos:Position, t1:Type, t2:Type, newT1:Type)
       typeSubstInTypeAt (t1, old, new, pos, newT1) =>
       typeSubstInTypeAt (arrow (t1, t2), old, new, 1 |> pos,
                          arrow (newT1, t2)))
    &&
    (fa (old:Type, new:Type, pos:Position, t1:Type, t2:Type, newT2:Type)
       typeSubstInTypeAt (t2, old, new, pos, newT2) =>
       typeSubstInTypeAt (arrow (t1, t2), old, new, 2 |> pos,
                          arrow (t1, newT2)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, cS:Constructors, t?S:Type?s,
         ti:Type, newTi:Type)
       i < length t?S &&
       t?S elem i = Some ti &&
       typeSubstInTypeAt (ti, old, new, pos, newTi) =>
       typeSubstInTypeAt (sum (cS, t?S), old, new, (i+1) |> pos,
                          sum (cS, update(t?S,i,Some newTi))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, tc:NaryTypeConstruct, tS:Types, newTi:Type)
       i < length tS &&
       typeSubstInTypeAt (tS elem i, old, new, pos, newTi) =>
       typeSubstInTypeAt (nary (tc, tS), old, new, (i+1) |> pos,
                          nary (tc, update(tS,i,newTi))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         tc:SubOrQuotientTypeConstruct, t:Type, e:Expression, newT:Type)
       typeSubstInTypeAt (t, old, new, pos, newT) =>
       typeSubstInTypeAt (subQuot (tc, t, e), old, new, 0 |> pos,
                          subQuot (tc, newT, e)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         tc:SubOrQuotientTypeConstruct, t:Type, e:Expression, newE:Expression)
       typeSubstInExprAt (e, old, new, pos, newE) =>
       typeSubstInTypeAt (subQuot (tc, t, e), old, new, 1 |> pos,
                          subQuot (tc, t, newE))))

  def typeSubstInExprAt = min (fn typeSubstInExprAt ->
    (fa (old:Type, new:Type, pos:Position,
         eo:UnaryExprOperator, e:Expression, newE:Expression)
       typeSubstInExprAt (e, old, new, pos, newE) =>
       typeSubstInExprAt (unary (eo, e), old, new, 0 |> pos,
                          unary (eo, newE)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         eo:BinaryExprOperator, e1:Expression, e2:Expression, newE1:Expression)
       typeSubstInExprAt (e1, old, new, pos, newE1) =>
       typeSubstInExprAt (binary (eo, e1, e2), old, new, 1 |> pos,
                          binary (eo, newE1, e2)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         eo:BinaryExprOperator, e1:Expression, e2:Expression, newE2:Expression)
       typeSubstInExprAt (e2, old, new, pos, newE2) =>
       typeSubstInExprAt (binary (eo, e1, e2), old, new, 2 |> pos,
                          binary (eo, e1, newE2)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE0:Expression)
       typeSubstInExprAt (e0, old, new, pos, newE0) =>
       typeSubstInExprAt (ifThenElse (e0, e1, e2), old, new, 0 |> pos,
                          ifThenElse (newE0, e1, e2)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE1:Expression)
       typeSubstInExprAt (e1, old, new, pos, newE1) =>
       typeSubstInExprAt (ifThenElse (e0, e1, e2), old, new, 1 |> pos,
                          ifThenElse (e0, newE1, e2)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE2:Expression)
       typeSubstInExprAt (e2, old, new, pos, newE2) =>
       typeSubstInExprAt (ifThenElse (e0, e1, e2), old, new, 2 |> pos,
                          ifThenElse (e0, e1, newE2)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         eo:NaryExprOperator, i:Nat, eS:Expressions, newEi:Expression)
       i < length eS &&
       typeSubstInExprAt (eS elem i, old, new, pos, newEi) =>
       typeSubstInExprAt (nary (eo, eS), old, new, (i+1) |> pos,
                          nary (eo, update(eS,i,newEi))))
    &&
    (fa (old:Type, new:Type, pos:Position, eo:BindingExprOperator,
         i:Nat, vS:Variables, tS:Types, e:Expression, newTi:Type)
       i < length vS &&
       length vS = length tS &&
       typeSubstInTypeAt (tS elem i, old, new, pos, newTi) =>
       typeSubstInExprAt (binding (eo, zip (vS, tS), e), old, new, (i+1) |> pos,
                          binding (eo, zip (vS, update(tS,i,newTi)), e)))
    &&
    (fa (old:Type, new:Type, pos:Position, eo:BindingExprOperator,
         bvS:BoundVars, e:Expression, newE:Expression)
       typeSubstInExprAt (e, old, new, pos, newE) =>
       typeSubstInExprAt (binding (eo, bvS, e), old, new, 0 |> pos,
                          binding (eo, bvS, newE)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, o:Operation, tS:Types, newTi:Type)
       i < length tS &&
       typeSubstInTypeAt (tS elem i, old, new, pos, newTi) =>
       typeSubstInExprAt (opInstance (o, tS), old, new, (i+1) |> pos,
                          opInstance (o, update(tS,i,newTi))))
    &&
    (* Since here embedders are decorated by types, instead of sum types as in
    LD, the positioning changes slightly: we just use 0 to indicate the type
    that decorates the embedder, as opposed to i to indicate the i-th type
    component as in LD. *)
    (fa (old:Type, new:Type, pos:Position,
         t:Type, c:Constructor, newT:Type)
       typeSubstInTypeAt (t, old, new, pos, newT) =>
       typeSubstInExprAt (embedder (t, c), old, new, 0 |> pos,
                          embedder (newT, c)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e:Expression, branches:FSeq(Pattern*Expression), newE:Expression)
       typeSubstInExprAt (e, old, new, pos, newE) =>
       typeSubstInExprAt (cas (e, branches), old, new, 0 |> pos,
                          cas (newE, branches)))
    &&
    (fa (old:Type, new:Type, pos:Position, i:Nat, e:Expression,
         pS:Patterns, eS:Expressions, newPi:Pattern)
       i < length pS &&
       length pS = length eS &&
       typeSubstInPattAt (pS elem i, old, new, pos, newPi) =>
       typeSubstInExprAt (cas (e, (zip (pS, eS))), old, new, (2*(i+1)-1) |> pos,
                          cas (e, (zip (update(pS,i,newPi), eS)))))
    &&
    (fa (old:Type, new:Type, pos:Position, i:Nat, e:Expression,
         pS:Patterns, eS:Expressions, newEi:Expression)
       i < length pS &&
       length pS = length eS &&
       typeSubstInExprAt (eS elem i, old, new, pos, newEi) =>
       typeSubstInExprAt (cas (e, (zip (pS, eS))), old, new, (2*(i+1)) |> pos,
                          cas (e, (zip (pS, update(eS,i,newEi))))))
    &&
    (fa (old:Type, new:Type, pos:Position, i:Nat, e:Expression,
         vS:Variables, tS:Types, eS:Expressions,
         e:Expression, newTi:Type)
       i < length vS &&
       length vS = length tS &&
       typeSubstInTypeAt (tS elem i, old, new, pos, newTi) =>
       typeSubstInExprAt (recursiveLet (zip (vS, tS), eS, e),
                          old, new, (2*(i+1)-1) |> pos,
                          recursiveLet (zip (vS, update(tS,i,newTi)), eS, e)))
    &&
    (fa (old:Type, new:Type, pos:Position, i:Nat, e:Expression,
         vS:Variables, tS:Types, eS:Expressions,
         e:Expression, newEi:Expression)
       i < length vS &&
       length vS = length tS &&
       typeSubstInExprAt (eS elem i, old, new, pos, newEi) =>
       typeSubstInExprAt (recursiveLet (zip (vS, tS), eS, e),
                          old, new, (2*(i+1)) |> pos,
                          recursiveLet (zip (vS, tS), update(eS,i,newEi), e)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         bvS:BoundVars, eS:Expressions, e:Expression, newE:Expression)
       typeSubstInExprAt (e, old, new, pos, newE) =>
       typeSubstInExprAt (recursiveLet (bvS, eS, e), old, new, 0 |> pos,
                          recursiveLet (bvS, eS, newE)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         p:Pattern, e:Expression, e1:Expression, newP:Pattern)
       typeSubstInPattAt (p, old, new, pos, newP) =>
       typeSubstInExprAt (nonRecursiveLet (p, e, e1), old, new, 0 |> pos,
                          nonRecursiveLet (newP, e, e1)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         p:Pattern, e:Expression, e1:Expression, newE:Expression)
       typeSubstInExprAt (e, old, new, pos, newE) =>
       typeSubstInExprAt (nonRecursiveLet (p, e, e1), old, new, 1 |> pos,
                          nonRecursiveLet (p, newE, e1)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         p:Pattern, e:Expression, e1:Expression, newE1:Expression)
       typeSubstInExprAt (e1, old, new, pos, newE1) =>
       typeSubstInExprAt (nonRecursiveLet (p, e, e1), old, new, 2 |> pos,
                          nonRecursiveLet (p, e, newE1))))

  def typeSubstInPattAt = min (fn typeSubstInPattAt ->
    (fa (old:Type, new:Type, pos:Position, v:Variable, t:Type, newT:Type)
       typeSubstInTypeAt (t, old, new, pos, newT) =>
       typeSubstInPattAt (variable (v, t), old, new, 0 |> pos,
                          variable (v, newT)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         t:Type, c:Constructor, p:Pattern, newT:Type)
       typeSubstInTypeAt (t, old, new, pos, newT) =>
       typeSubstInPattAt (embedding (t, c, p), old, new, 0 |> pos,
                          embedding (newT, c, p)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         t:Type, c:Constructor, p:Pattern, newP:Pattern)
       typeSubstInPattAt (p, old, new, pos, newP) =>
       typeSubstInPattAt (embedding (t, c, p), old, new, 1 |> pos,
                          embedding (t, c, newP)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         i:Nat, fS:Fields, pS:Patterns, newPi:Pattern)
       i < length fS &&
       typeSubstInPattAt (pS elem i, old, new, pos, newPi) =>
       typeSubstInPattAt (record (fS, pS), old, new, i |> pos,
                          record (fS, update(pS,i,newPi))))
    &&
    (fa (old:Type, new:Type, pos:Position,
         v:Variable, t:Type, p:Pattern, newT:Type)
       typeSubstInTypeAt (t, old, new, pos, newT) =>
       typeSubstInPattAt (alias ((v, t), p), old, new, 0 |> pos,
                          alias ((v, newT),p)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         v:Variable, t:Type, p:Pattern, newP:Pattern)
       typeSubstInPattAt (p, old, new, pos, newP) =>
       typeSubstInPattAt (alias ((v, t), p), old, new, 1 |> pos,
                          alias ((v, t), newP))))


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % expression substitution at position:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op exprSubstAt :
     Expression * Expression * Expression * Position * Expression -> Boolean

  def exprSubstAt = min (fn exprSubstAt ->
    (fa (old:Expression, new:Expression)
       exprSubstAt (old, old, new, empty, new))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         eo:UnaryExprOperator, e:Expression, newE:Expression)
       exprSubstAt (e, old, new, pos, newE) =>
       exprSubstAt (unary (eo, e), old, new, 0 |> pos,
                    unary (eo, newE)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         eo:BinaryExprOperator, e1:Expression, e2:Expression, newE1:Expression)
       exprSubstAt (e1, old, new, pos, newE1) =>
       exprSubstAt (binary (eo, e1, e2), old, new, 1 |> pos,
                    binary (eo, newE1, e2)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         eo:BinaryExprOperator, e1:Expression, e2:Expression, newE2:Expression)
       exprSubstAt (e2, old, new, pos, newE2) =>
       exprSubstAt (binary (eo, e1, e2), old, new, 2 |> pos,
                    binary (eo, e1, newE2)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE0:Expression)
       exprSubstAt (e0, old, new, pos, newE0) =>
       exprSubstAt (ifThenElse (e0, e1, e2), old, new, 0 |> pos,
                    ifThenElse (newE0, e1, e2)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE1:Expression)
       exprSubstAt (e1, old, new, pos, newE1) =>
       exprSubstAt (ifThenElse (e0, e1, e2), old, new, 1 |> pos,
                    ifThenElse (e0, newE1, e2)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE2:Expression)
       exprSubstAt (e2, old, new, pos, newE2) =>
       exprSubstAt (ifThenElse (e0, e1, e2), old, new, 2 |> pos,
                    ifThenElse (e0, e1, newE2)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         eo:NaryExprOperator, eS:Expressions, i:Nat, newEi:Expression)
       exprSubstAt (eS elem i, old, new, pos, newEi) =>
       exprSubstAt (nary (eo, eS), old, new, (i+1) |> pos,
                    nary (eo, update(eS,i,newEi))))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         eo:BindingExprOperator, bvS:BoundVars,
         e:Expression, newE:Expression)
       exprSubstAt (e, old, new, pos, newE) =>
       exprSubstAt (binding (eo, bvS, e), old, new, 0 |> pos,
                    binding (eo, bvS, newE)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e:Expression, branches:FSeq(Pattern*Expression), newE:Expression)
       exprSubstAt (e, old, new, pos, newE) =>
       exprSubstAt (cas (e, branches), old, new, 0 |> pos,
                    cas (newE, branches)))
    &&
    (fa (old:Expression, new:Expression, pos:Position, i:Nat, e:Expression,
         pS:Patterns, eS:Expressions, newEi:Expression)
       i < length pS &&
       length pS = length eS &&
       exprSubstAt (eS elem i, old, new, pos, newEi) =>
       exprSubstAt (cas (e, (zip (pS, eS))), old, new, (i+1) |> pos,
                    cas (e, (zip (pS, update(eS,i,newEi))))))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         bvS:BoundVars, eS:Expressions, e:Expression, newE:Expression)
       exprSubstAt (e, old, new, pos, newE) =>
       exprSubstAt (recursiveLet(bvS,eS,e), old, new, 0 |> pos,
                    recursiveLet(bvS,eS,newE)))
    &&
    (fa (old:Expression, new:Expression, pos:Position, i:Nat,
         bvS:BoundVars, eS:Expressions, newEi:Expression, e:Expression)
       i < length bvS &&
       exprSubstAt (eS elem i, old, new, pos, newEi) =>
       exprSubstAt (recursiveLet (bvS, eS, e), old, new, (i+1) |> pos,
                    recursiveLet (bvS, update(eS,i,newEi), e)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         p:Pattern, e:Expression, e1:Expression, newE:Expression)
       exprSubstAt (e, old, new, pos, newE) =>
       exprSubstAt (nonRecursiveLet (p, e, e1), old, new, 0 |> pos,
                    nonRecursiveLet (p, newE, e1)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         p:Pattern, e:Expression, e1:Expression, newE1:Expression)
       exprSubstAt (e1, old, new, pos, newE1) =>
       exprSubstAt (nonRecursiveLet (p, e, e1), old, new, 1 |> pos,
                    nonRecursiveLet (p, e, newE1))))

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
           | unary(_,e)              -> (assert (i = 0);
                                         captVarsAt(pos,e))
           | binary(_,e1,e2)         -> if i = 1 then captVarsAt(pos,e1)
                                   else (assert (i = 2); captVarsAt(pos,e2))
           | ifThenElse(e0,e1,e2)    -> if i = 0 then captVarsAt(pos,e0)
                                   else if i = 1 then captVarsAt(pos,e1)
                                   else (assert (i = 2); captVarsAt(pos,e2))
           | nary(_,eS)              -> (assert (1 <= i && i <= length eS);
                                         captVarsAt (pos, eS elem (i-1)))
           | binding(_,bvS,e)        -> (assert (i = 0);
                                         let (vS, _) = unzip bvS in
                                         captVarsAt(pos,e) \/ toSet vS)
           | cas(e,branches)         -> if i = 0 then captVarsAt(pos,e)
                                        else
                                          (assert (1 <= i && i <= length branches);
                                           let (pS, eS) = unzip branches in
                                           pattVars (pS elem (i-1)) \/
                                           captVarsAt (pos, eS elem (i-1)))
           | recursiveLet(bvS,eS,e)  -> let (vS, _) = unzip bvS in
                                        if i = 0
                                        then toSet vS \/ captVarsAt(pos,e)
                                        else
                                          (assert (1 <= i && i <= length bvS);
                                           toSet vS \/
                                           captVarsAt (pos, eS elem (i-1)))
           | nonRecursiveLet(p,e,e1) -> if i = 0 then captVarsAt(pos,e)
                                        else
                                          (assert (i = 1);
                                           pattVars p \/ captVarsAt(pos,e1))

  op exprSubstAtOK? : Expression * Expression * Expression * Position -> Boolean
  def exprSubstAtOK?(e,old,new,pos) =
    (ex (newE:Expression)
       exprSubstAt (e, old, new, pos, newE) &&
       exprFreeVars old /\ captVarsAt(pos,e) = empty &&
       exprFreeVars new /\ captVarsAt(pos,e) = empty)

endspec
