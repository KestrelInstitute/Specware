spec

  (* This spec defines various operations on the syntax, which is defined in
  spec `Syntax'. The ops defined here are tagged as "core" because they are
  the only ones necessary to define the notion of provability, which is done
  in spec `Provability'. *)


  import Syntax, Positions


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % N-ary conjunction and disjunction:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op conjoinAll : Expressions -> Expression
  def conjoinAll = the (fn conjoinAll ->
    (conjoinAll empty = TRUE) &&
    (fa(e) conjoinAll (singleton e) = e) &&
    (fa(e,eS) eS ~= empty =>
       conjoinAll (e |> eS) = (e &&& conjoinAll eS)))

  op disjoinAll : Expressions -> Expression
  def disjoinAll = the (fn disjoinAll ->
    (disjoinAll empty = FALSE) &&
    (fa(e) disjoinAll (singleton e) = e) &&
    (fa(e,eS) eS ~= empty =>
       disjoinAll (e |> eS) = (e ||| disjoinAll eS)))


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % conversion of a pattern into an expression:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op patt2expr : Pattern -> Expression
  def patt2expr = fn
    | variable(v,_)         -> VAR v
    | embedding(t,c,None)   -> EMBED t c
    | embedding(t,c,Some p) -> EMBED t c @ patt2expr p
    | record(fS,pS)         -> RECORD fS (map (patt2expr, pS))
    | tuple pS              -> TUPLE (map (patt2expr, pS))
    | alias(_,_,p)          -> patt2expr p


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % assumptions engendered by a pattern:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op pattAliasAssumptions : Pattern -> Expression
  def pattAliasAssumptions = fn
    | variable _            -> TRUE
    | embedding(_,_,None)   -> TRUE
    | embedding(_,_,Some p) -> pattAliasAssumptions p
    | record(_,pS)          -> conjoinAll (map (pattAliasAssumptions, pS))
    | tuple pS              -> conjoinAll (map (pattAliasAssumptions, pS))
    | alias(v,_,p)          -> VAR v == patt2expr p &&& pattAliasAssumptions p

  op pattAssumptions : Pattern * Expression -> Expression
  def pattAssumptions(p,e) =
    e == patt2expr p &&& pattAliasAssumptions p


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % variables bound by a pattern:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op pattVarsWithTypesZipped : Pattern -> FSeq (Variable * Type)
  def pattVarsWithTypesZipped = fn
    | variable(v,t)         -> singleton (v,t)
    | embedding(t,c,None)   -> empty
    | embedding(t,c,Some p) -> pattVarsWithTypesZipped p
    | record(_,pS)          -> flatten (map (pattVarsWithTypesZipped, pS))
    | tuple pS              -> flatten (map (pattVarsWithTypesZipped, pS))
    | alias(v,t,p)          -> (v,t) |> pattVarsWithTypesZipped p

  op pattVarsWithTypes :
     Pattern -> {(vS,tS) : Variables * Types | length vS = length tS}
  def pattVarsWithTypes p =
    unzip (pattVarsWithTypesZipped p)

  op pattVars : Pattern -> FSet Variable
  def pattVars p =
    let (vS,_) = pattVarsWithTypes p in
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
    | nullary _               -> empty
    | unary(_,e)              -> exprFreeVars e
    | binary(_,e1,e2)         -> exprFreeVars e1 \/ exprFreeVars e2
    | ifThenElse(e0,e1,e2)    -> exprFreeVars e0 \/
                                 exprFreeVars e1 \/
                                 exprFreeVars e2
    | nary(_,eS)              -> unionAll (map (exprFreeVars, eS))
    | binding(_,vS,_,e)       -> exprFreeVars e -- toSet vS
    | opInstance _            -> empty
    | embedder _              -> empty
    | casE(e,pS,eS)           -> let n = min (length pS, length eS) in
                                     % in well-typed expressions,
                                     % n = length pS = length eS
                                 let vSets =
                                     seqSuchThat (fn(i:Nat) ->
                                       if i < n
                                       then Some (exprFreeVars (eS!i)
                                                   -- pattVars (pS!i))
                                       else None) in
                                 exprFreeVars e \/ unionAll vSets
    | recursiveLet(vS,_,eS,e) -> (unionAll (map (exprFreeVars, eS))
                                  \/ exprFreeVars e) -- toSet vS
    | nonRecursiveLet(p,e,e1) -> exprFreeVars e \/
                                 (exprFreeVars e1 -- pattVars p)


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % ops in types, expressions, and patterns:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op typeOps : Type       -> FSet Operation
  op exprOps : Expression -> FSet Operation
  op pattOps : Pattern    -> FSet Operation

  def typeOps = fn
    | boolean        -> empty
    | variable _     -> empty
    | arrow(t1,t2)   -> typeOps t1 \/ typeOps t2
    | sum(_,t?S)     -> unionAll (map (typeOps, removeNones t?S))
    | nary(_,tS)     -> unionAll (map (typeOps, tS))
    | subQuot(_,t,e) -> typeOps t \/ exprOps e

  def exprOps = fn
    | nullary _               -> empty
    | unary(_,e)              -> exprOps e
    | binary(_,e1,e2)         -> exprOps e1 \/ exprOps e2
    | ifThenElse(e0,e1,e2)    -> exprOps e0 \/ exprOps e1 \/ exprOps e2
    | nary(_,eS)              -> unionAll (map (exprOps, eS))
    | binding(_,_,tS,e)       -> unionAll (map (typeOps, tS)) \/ exprOps e
    | opInstance(o,tS)        -> singleton o \/ unionAll (map (typeOps, tS))
    | embedder(t,_)           -> typeOps t
    | casE(e,pS,eS)           -> exprOps e \/ unionAll (map (pattOps, pS))
                                           \/ unionAll (map (exprOps, eS))
    | recursiveLet(_,tS,eS,e) -> unionAll (map (typeOps, tS)) \/
                                 unionAll (map (exprOps, eS)) \/ exprOps e
    | nonRecursiveLet(p,e,e1) -> pattOps p \/ exprOps e \/ exprOps e1

  def pattOps = fn
    | variable(_,t)         -> typeOps t
    | embedding(t,c,None)   -> typeOps t
    | embedding(t,c,Some p) -> typeOps t \/ pattOps p
    | record(_,pS)          -> unionAll (map (pattOps, pS))
    | tuple pS              -> unionAll (map (pattOps, pS))
    | alias(_,t,p)          -> typeOps t \/ pattOps p


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % items declared or defined in a context:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op contextElementTypes    : ContextElement -> FSet TypeName
  op contextElementOps      : ContextElement -> FSet Operation
  op contextElementTypeVars : ContextElement -> FSet TypeVariable
  op contextElementVars     : ContextElement -> FSet Variable
  op contextElementAxioms   : ContextElement -> FSet AxiomName

  def contextElementTypes = fn
    | typeDeclaration(tn,_) -> singleton tn
    | _                     -> empty

  def contextElementOps = fn
    | opDeclaration(o,_,_) -> singleton o
    | _                    -> empty

  def contextElementTypeVars = fn
    | typeVarDeclaration tv -> singleton tv
    | _                     -> empty

  def contextElementVars = fn
    | varDeclaration(v,_) -> singleton v
    | _                   -> empty

  def contextElementAxioms = fn
    | axioM(an,_,_) -> singleton an
    | _             -> empty

  op contextTypes    : Context -> FSet TypeName
  op contextOps      : Context -> FSet Operation
  op contextTypeVars : Context -> FSet TypeVariable
  op contextVars     : Context -> FSet Variable
  op contextAxioms   : Context -> FSet AxiomName

  def contextTypes    cx = unionAll (map (contextElementTypes,    cx))
  def contextOps      cx = unionAll (map (contextElementOps,      cx))
  def contextTypeVars cx = unionAll (map (contextElementTypeVars, cx))
  def contextVars     cx = unionAll (map (contextElementVars,     cx))
  def contextAxioms   cx = unionAll (map (contextElementAxioms,   cx))

  op contextDefinesType? : Context * TypeName -> Boolean
  def contextDefinesType?(cx,tn) =
    (ex (tvS:TypeVariables, t:Type) typeDefinition (tn, tvS, t) in? cx)

  op contextDefinesOp? : Context * Operation -> Boolean
  def contextDefinesOp?(cx,o) =
    (ex (tvS:TypeVariables, e:Expression) opDefinition (o, tvS, e) in? cx)


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % multiple (type) variable declarations:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op multiTypeVarDecls : TypeVariables -> Context
  def multiTypeVarDecls tvS =
    map (embed typeVarDeclaration, tvS)

  op multiVarDecls :
     {(vS,tS) : Variables * Types | length vS = length tS} -> Context
  def multiVarDecls(vS,tS) =
    map (embed varDeclaration, zip(vS,tS))


  %%%%%%%%%%%%%%%%%%%%
  % type substitution:
  %%%%%%%%%%%%%%%%%%%%

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
    | sum(cS,t?S)     -> sum (cS, map (mapOption (typeSubstInType sbs), t?S))
    | nary(tc,tS)     -> nary (tc, map (typeSubstInType sbs, tS))
    | subQuot(tc,t,e) -> subQuot (tc,
                                  typeSubstInType sbs t,
                                  typeSubstInExpr sbs e)

  def typeSubstInExpr sbs = fn
    | nullary eo               -> nullary eo
    | unary(eo,e)              -> unary (eo, typeSubstInExpr sbs e)
    | binary(eo,e1,e2)         -> binary (eo,
                                          typeSubstInExpr sbs e1,
                                          typeSubstInExpr sbs e2)
    | ifThenElse(e0,e1,e2)     -> ifThenElse (typeSubstInExpr sbs e0,
                                              typeSubstInExpr sbs e1,
                                              typeSubstInExpr sbs e2)
    | nary(eo,eS)              -> nary (eo, map (typeSubstInExpr sbs, eS))
    | binding(eo,vS,tS,e)      -> binding (eo, vS, map (typeSubstInType sbs, tS),
                                           typeSubstInExpr sbs e)
    | opInstance(o,tS)         -> opInstance (o, map (typeSubstInType sbs, tS))
    | embedder(t,c)            -> embedder (typeSubstInType sbs t, c)
    | casE(e,pS,eS)            -> casE (typeSubstInExpr sbs e,
                                        map (typeSubstInPatt sbs, pS),
                                        map (typeSubstInExpr sbs, eS))
    | recursiveLet(vS,tS,eS,e) -> recursiveLet
                                    (vS, map (typeSubstInType sbs, tS),
                                     map (typeSubstInExpr sbs, eS),
                                     typeSubstInExpr sbs e)
    | nonRecursiveLet(p,e,e1)  -> nonRecursiveLet (typeSubstInPatt sbs p,
                                                   typeSubstInExpr sbs e,
                                                   typeSubstInExpr sbs e1)

  def typeSubstInPatt sbs = fn
    | variable(v,t)         -> variable (v, typeSubstInType sbs t)
    | embedding(t,c,None)   -> embedding (typeSubstInType sbs t, c, None)
    | embedding(t,c,Some p) -> embedding (typeSubstInType sbs t,
                                          c,
                                          Some (typeSubstInPatt sbs p))
    | record(fS,pS)         -> record (fS, map (typeSubstInPatt sbs, pS))
    | tuple pS              -> tuple (map (typeSubstInPatt sbs, pS))
    | alias(v,t,p)          -> alias
                                 (v, typeSubstInType sbs t, typeSubstInPatt sbs p)

  % true iff `tsbs' is substitution of `tvS!i' with `tS!i':
  op isTypeSubstFrom? : TypeSubstitution * TypeVariables * Types -> Boolean
  def isTypeSubstFrom?(tsbs,tvS,tS) =
    noRepetitions? tvS &&
    length tvS = length tS &&
    tsbs = FMap.fromSequences (tvS, tS)


  %%%%%%%%%%%%%%%%%%%%%%%%%%
  % expression substitution:
  %%%%%%%%%%%%%%%%%%%%%%%%%%

  (* While LD only defines only the substitution of a single variable with an
  expression, here we consider multi-variable substitutions (like for
  types). We model them as finite maps.

  Another difference with LD is that in LD no substitution is performed in
  subtype and quotient type predicates, because well-typed ones have no free
  variables. Here it is easier to perform the substitution in those
  predicates, because of the way we have factored expressions. *)

  type ExprSubstitution = FMap (Variable, Expression)

  op exprSubst : ExprSubstitution -> Expression -> Expression
  def exprSubst sbs = fn
    | nullary(variable v)      -> if definedAt?(sbs,v)
                                  then apply(sbs,v)
                                  else nullary(variable v)
    | nullary truE             -> nullary truE
    | nullary falsE            -> nullary falsE
    | unary(eo,e)              -> unary (eo, exprSubst sbs e)
    | binary(eo,e1,e2)         -> binary (eo, exprSubst sbs e1, exprSubst sbs e2)
    | ifThenElse(e0,e1,e2)     -> ifThenElse (exprSubst sbs e0,
                                              exprSubst sbs e1,
                                              exprSubst sbs e2)
    | nary(eo,eS)              -> nary (eo, map (exprSubst sbs, eS))
    | binding(eo,vS,tS,e)      -> let bodySbs = undefineMulti (sbs, toSet vS) in
                                  binding (eo, vS, tS, exprSubst bodySbs e)
    | opInstance(o,tS)         -> opInstance(o,tS)
    | embedder(t,c)            -> embedder (t, c)
    | casE(e,pS,eS)            -> let n = min (length pS, length eS) in
                                      % in well-typed expressions,
                                      % n = length pS = length eS
                                  let branchSbss =
                                      seqSuchThat (fn(i:Nat) ->
                                        if i < n
                                        then Some (undefineMulti
                                                     (sbs, pattVars (pS!i)))
                                        else None) in
                                  let newES =
                                      seqSuchThat (fn(i:Nat) ->
                                        if i < n
                                        then Some (exprSubst (branchSbss!i) (eS!i))
                                        else None) in
                                  casE (exprSubst sbs e, pS, newES)
    | recursiveLet(vS,tS,eS,e) -> let bodySbs = undefineMulti (sbs, toSet vS) in
                                  recursiveLet (vS, tS,
                                                map (exprSubst bodySbs, eS),
                                                exprSubst sbs e)
    | nonRecursiveLet(p,e,e1)  -> let bodySbs = undefineMulti (sbs, pattVars p) in
                                  nonRecursiveLet (p,
                                                   exprSubst sbs e,
                                                   exprSubst bodySbs e1)

  % abbreviation for replacing one variable with an expression:
  op exprSubst1 : Variable -> Expression -> Expression -> Expression
  def exprSubst1 v d e =
    exprSubst (FMap.singleton (v, d)) e

  % captured variables at free occurrences of given variable:
  op captVars : Variable -> Expression -> FSet Variable
  def captVars u = fn
    | nullary _               -> empty
    | unary(_,e)              -> captVars u e
    | binary(_,e1,e2)         -> captVars u e1 \/ captVars u e2
    | ifThenElse(e0,e1,e2)    -> captVars u e0 \/ captVars u e1 \/ captVars u e2
    | nary(_,eS)              -> unionAll (map (captVars u, eS))
    | binding(_,vS,_,e)       -> if u in? exprFreeVars e && ~(u in? vS)
                                 then toSet vS \/ captVars u e
                                 else empty
    | opInstance _            -> empty
    | embedder _              -> empty
    | casE(e,pS,eS)           -> let n = min (length pS, length eS) in
                                     % in well-typed expressions,
                                     % n = length pS = length eS
                                 let varSets =
                                     seqSuchThat (fn(i:Nat) ->
                                       if i < n
                                       then if u in? exprFreeVars (eS!i) &&
                                               ~(u in? pattVars (pS!i))
                                            then Some (pattVars (pS!i) \/
                                                       captVars u (eS!i))
                                            else Some empty
                                       else None) in
                                 unionAll varSets \/ captVars u e
    | recursiveLet(vS,_,eS,e) -> if (u in? exprFreeVars e ||
                                     (ex(e1) e1 in? eS &&
                                             u in? exprFreeVars e1)) &&
                                    ~(u in? toSet vS)
                                 then toSet vS \/
                                      captVars u e \/
                                      unionAll (map (captVars u, eS))
                                 else empty
    | nonRecursiveLet(p,e,e1) -> captVars u e \/
                                 (if u in? exprFreeVars e1 -- pattVars p
                                  then pattVars p \/ captVars u e1
                                  else empty)

  op exprSubstOK? : Expression * ExprSubstitution -> Boolean
  def exprSubstOK?(e,sbs) =
    (fa(v) v in? domain sbs =>
           exprFreeVars (apply(sbs,v)) /\ captVars v e = empty)

  % true iff `esbs' is substitution of `vS!i' with `eS!i':
  op isExprSubstFrom? : ExprSubstitution * Variables * Expressions -> Boolean
  def isExprSubstFrom?(esbs,vS,eS) =
    noRepetitions? vS &&
    length vS = length eS &&
    esbs = FMap.fromSequences (vS, eS)


  %%%%%%%%%%%%%%%%%%%%%%%
  % pattern substitution:
  %%%%%%%%%%%%%%%%%%%%%%%

  type PattSubstitution = Variable * Variable

  op pattSubst : PattSubstitution -> Pattern -> Pattern
  def pattSubst (old,new) = fn
    | variable(v,t)         -> if v = old
                               then variable (new,t)
                               else variable (v,  t)
    | embedding(t,c,None)   -> embedding (t, c, None)
    | embedding(t,c,Some p) -> embedding (t, c, Some (pattSubst (old,new) p))
    | record(fS,pS)         -> record (fS, map (pattSubst (old,new), pS))
    | tuple pS              -> tuple (map (pattSubst (old,new), pS))
    | alias(v,t,p)          -> if v = old
                               then alias (new, t, pattSubst (old,new) p)
                               else alias (v,   t, pattSubst (old,new) p)


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % type substitution at position:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op isTypeSubstInTypeAt? :
     Type * Type * Type * Position * Type -> Boolean

  op isTypeSubstInExprAt? :
     Expression * Type * Type * Position * Expression -> Boolean

  op isTypeSubstInPattAt? :
     Pattern * Type * Type * Position * Pattern -> Boolean

  def isTypeSubstInTypeAt? = min (fn isTypeSubstInTypeAt? ->
    (fa (old:Type, new:Type)
       isTypeSubstInTypeAt? (old, old, new, empty, new))
    &&
    (fa (old:Type, new:Type, pos:Position, t1:Type, t2:Type, newT1:Type)
       isTypeSubstInTypeAt? (t1, old, new, pos, newT1) =>
       isTypeSubstInTypeAt? (arrow (t1, t2), old, new, 1 |> pos,
                             arrow (newT1, t2)))
    &&
    (fa (old:Type, new:Type, pos:Position, t1:Type, t2:Type, newT2:Type)
       isTypeSubstInTypeAt? (t2, old, new, pos, newT2) =>
       isTypeSubstInTypeAt? (arrow (t1, t2), old, new, 2 |> pos,
                             arrow (t1, newT2)))
    &&
    (fa (old:Type, new:Type, pos:Position, cS:Constructors, t?S:Type?s,
         i:Nat, ti:Type, newTi:Type)
       i < length t?S &&
       t?S!i = Some ti &&
       isTypeSubstInTypeAt? (ti, old, new, pos, newTi) =>
       isTypeSubstInTypeAt? (sum (cS, t?S), old, new, (i+1) |> pos,
                             sum (cS, update(t?S,i,Some newTi))))
    &&
    (fa (old:Type, new:Type, pos:Position, tc:NaryTypeConstruct, tS:Types,
         i:Nat, newTi:Type)
       i < length tS &&
       isTypeSubstInTypeAt? (tS!i, old, new, pos, newTi) =>
       isTypeSubstInTypeAt? (nary (tc, tS), old, new, (i+1) |> pos,
                             nary (tc, update(tS,i,newTi))))
    &&
    (fa (old:Type, new:Type, pos:Position, tc:SubOrQuotientTypeConstruct,
         t:Type, e:Expression, newT:Type)
       isTypeSubstInTypeAt? (t, old, new, pos, newT) =>
       isTypeSubstInTypeAt? (subQuot (tc, t, e), old, new, 0 |> pos,
                             subQuot (tc, newT, e)))
    &&
    (fa (old:Type, new:Type, pos:Position, tc:SubOrQuotientTypeConstruct,
         t:Type, e:Expression, newE:Expression)
       isTypeSubstInExprAt? (e, old, new, pos, newE) =>
       isTypeSubstInTypeAt? (subQuot (tc, t, e), old, new, 1 |> pos,
                             subQuot (tc, t, newE))))

  def isTypeSubstInExprAt? = min (fn isTypeSubstInExprAt? ->
    (fa (old:Type, new:Type, pos:Position, eo:UnaryExprOperator, e:Expression,
         newE:Expression)
       isTypeSubstInExprAt? (e, old, new, pos, newE) =>
       isTypeSubstInExprAt? (unary (eo, e), old, new, 0 |> pos,
                             unary (eo, newE)))
    &&
    (fa (old:Type, new:Type, pos:Position, eo:BinaryExprOperator,
         e1:Expression, e2:Expression, newE1:Expression)
       isTypeSubstInExprAt? (e1, old, new, pos, newE1) =>
       isTypeSubstInExprAt? (binary (eo, e1, e2), old, new, 1 |> pos,
                             binary (eo, newE1, e2)))
    &&
    (fa (old:Type, new:Type, pos:Position, eo:BinaryExprOperator,
         e1:Expression, e2:Expression, newE2:Expression)
       isTypeSubstInExprAt? (e2, old, new, pos, newE2) =>
       isTypeSubstInExprAt? (binary (eo, e1, e2), old, new, 2 |> pos,
                             binary (eo, e1, newE2)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE0:Expression)
       isTypeSubstInExprAt? (e0, old, new, pos, newE0) =>
       isTypeSubstInExprAt? (ifThenElse (e0, e1, e2), old, new, 0 |> pos,
                             ifThenElse (newE0, e1, e2)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE1:Expression)
       isTypeSubstInExprAt? (e1, old, new, pos, newE1) =>
       isTypeSubstInExprAt? (ifThenElse (e0, e1, e2), old, new, 1 |> pos,
                             ifThenElse (e0, newE1, e2)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE2:Expression)
       isTypeSubstInExprAt? (e2, old, new, pos, newE2) =>
       isTypeSubstInExprAt? (ifThenElse (e0, e1, e2), old, new, 2 |> pos,
                             ifThenElse (e0, e1, newE2)))
    &&
    (fa (old:Type, new:Type, pos:Position, eo:NaryExprOperator, eS:Expressions,
         i:Nat, newEi:Expression)
       i < length eS &&
       isTypeSubstInExprAt? (eS!i, old, new, pos, newEi) =>
       isTypeSubstInExprAt? (nary (eo, eS), old, new, (i+1) |> pos,
                             nary (eo, update(eS,i,newEi))))
    &&
    (fa (old:Type, new:Type, pos:Position, eo:BindingExprOperator,
         vS:Variables, tS:Types, e:Expression, i:Nat, newTi:Type)
       i < length vS &&
       length vS = length tS &&
       isTypeSubstInTypeAt? (tS!i, old, new, pos, newTi) =>
       isTypeSubstInExprAt? (binding (eo, vS, tS, e), old, new, (i+1) |> pos,
                             binding (eo, vS, update(tS,i,newTi), e)))
    &&
    (fa (old:Type, new:Type, pos:Position, eo:BindingExprOperator,
         vS:Variables, tS:Types, e:Expression, newE:Expression)
       isTypeSubstInExprAt? (e, old, new, pos, newE) =>
       isTypeSubstInExprAt? (binding (eo, vS, tS, e), old, new, 0 |> pos,
                             binding (eo, vS, tS, newE)))
    &&
    (fa (old:Type, new:Type, pos:Position, o:Operation, tS:Types,
         i:Nat, newTi:Type)
       i < length tS &&
       isTypeSubstInTypeAt? (tS!i, old, new, pos, newTi) =>
       isTypeSubstInExprAt? (opInstance (o, tS), old, new, (i+1) |> pos,
                             opInstance (o, update(tS,i,newTi))))
    &&
    (* Since here embedders are decorated by types, instead of sum types as in
    LD, the positioning changes slightly: we just use 0 to indicate the type
    that decorates the embedder, as opposed to i to indicate the i-th type
    component as in LD. *)
    (fa (old:Type, new:Type, pos:Position, t:Type, c:Constructor, newT:Type)
       isTypeSubstInTypeAt? (t, old, new, pos, newT) =>
       isTypeSubstInExprAt? (embedder (t, c), old, new, 0 |> pos,
                             embedder (newT, c)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e:Expression, pS:Patterns, eS:Expressions, newE:Expression)
       isTypeSubstInExprAt? (e, old, new, pos, newE) =>
       isTypeSubstInExprAt? (casE (e, pS, eS), old, new, 0 |> pos,
                             casE (newE, pS, eS)))
    &&
    (fa (old:Type, new:Type, pos:Position,
         e:Expression, pS:Patterns, eS:Expressions, i:Nat, newPi:Pattern)
       i < length pS &&
       isTypeSubstInPattAt? (pS!i, old, new, pos, newPi) =>
       isTypeSubstInExprAt? (casE (e, pS, eS), old, new, (2*i+1) |> pos,
                             casE (e, update(pS,i,newPi), eS)))
    &&
    (fa (old:Type, new:Type, pos:Position, i:Nat, e:Expression,
         pS:Patterns, eS:Expressions, newEi:Expression)
       i < length pS &&
       length pS = length eS &&
       isTypeSubstInExprAt? (eS!i, old, new, pos, newEi) =>
       isTypeSubstInExprAt? (casE (e, pS, eS), old, new, (2*i+2) |> pos,
                             casE (e, pS, update(eS,i,newEi))))
    &&
    (fa (old:Type, new:Type, pos:Position, e:Expression, vS:Variables, tS:Types,
         eS:Expressions, e:Expression, i:Nat, newTi:Type)
       i < length vS &&
       length vS = length tS &&
       isTypeSubstInTypeAt? (tS!i, old, new, pos, newTi) =>
       isTypeSubstInExprAt? (recursiveLet (vS, tS, eS, e),
                             old, new, (2*i+1) |> pos,
                             recursiveLet (vS, update(tS,i,newTi), eS, e)))
    &&
    (fa (old:Type, new:Type, pos:Position, e:Expression, vS:Variables, tS:Types,
         eS:Expressions, e:Expression, i:Nat, newEi:Expression)
       i < length vS &&
       length vS = length tS &&
       isTypeSubstInExprAt? (eS!i, old, new, pos, newEi) =>
       isTypeSubstInExprAt? (recursiveLet (vS, tS, eS, e),
                             old, new, (2*i+2) |> pos,
                             recursiveLet (vS, tS, update(eS,i,newEi), e)))
    &&
    (fa (old:Type, new:Type, pos:Position, vS:Variables, tS:Types,
         eS:Expressions, e:Expression, newE:Expression)
       isTypeSubstInExprAt? (e, old, new, pos, newE) =>
       isTypeSubstInExprAt? (recursiveLet (vS, tS, eS, e), old, new, 0 |> pos,
                             recursiveLet (vS, tS, eS, newE)))
    &&
    (fa (old:Type, new:Type, pos:Position, p:Pattern, e:Expression, e1:Expression,
         newP:Pattern)
       isTypeSubstInPattAt? (p, old, new, pos, newP) =>
       isTypeSubstInExprAt? (nonRecursiveLet (p, e, e1), old, new, 0 |> pos,
                             nonRecursiveLet (newP, e, e1)))
    &&
    (fa (old:Type, new:Type, pos:Position, p:Pattern, e:Expression, e1:Expression,
         newE:Expression)
       isTypeSubstInExprAt? (e, old, new, pos, newE) =>
       isTypeSubstInExprAt? (nonRecursiveLet (p, e, e1), old, new, 1 |> pos,
                             nonRecursiveLet (p, newE, e1)))
    &&
    (fa (old:Type, new:Type, pos:Position, p:Pattern, e:Expression, e1:Expression,
         newE1:Expression)
       isTypeSubstInExprAt? (e1, old, new, pos, newE1) =>
       isTypeSubstInExprAt? (nonRecursiveLet (p, e, e1), old, new, 2 |> pos,
                             nonRecursiveLet (p, e, newE1))))

  def isTypeSubstInPattAt? = min (fn isTypeSubstInPattAt? ->
    (fa (old:Type, new:Type, pos:Position, v:Variable, t:Type, newT:Type)
       isTypeSubstInTypeAt? (t, old, new, pos, newT) =>
       isTypeSubstInPattAt? (variable (v,t), old, new, 0 |> pos,
                             variable (v,newT)))
    &&
    (fa (old:Type, new:Type, pos:Position, t:Type, c:Constructor, p?:Pattern?,
         newT:Type)
       isTypeSubstInTypeAt? (t, old, new, pos, newT) =>
       isTypeSubstInPattAt? (embedding (t, c, p?), old, new, 0 |> pos,
                             embedding (newT, c, p?)))
    &&
    (fa (old:Type, new:Type, pos:Position, t:Type, c:Constructor, p:Pattern,
         newP:Pattern)
       isTypeSubstInPattAt? (p, old, new, pos, newP) =>
       isTypeSubstInPattAt? (embedding (t, c, Some p), old, new, 1 |> pos,
                             embedding (t, c, Some newP)))
    &&
    (fa (old:Type, new:Type, pos:Position, fS:Fields, pS:Patterns,
         i:Nat, newPi:Pattern)
       i < length pS &&
       isTypeSubstInPattAt? (pS!i, old, new, pos, newPi) =>
       isTypeSubstInPattAt? (record (fS, pS), old, new, (i+1) |> pos,
                             record (fS, update(pS,i,newPi))))
    &&
    (fa (old:Type, new:Type, pos:Position, pS:Patterns, i:Nat, newPi:Pattern)
       i < length pS &&
       isTypeSubstInPattAt? (pS!i, old, new, pos, newPi) =>
       isTypeSubstInPattAt? (tuple pS, old, new, (i+1) |> pos,
                             tuple (update(pS,i,newPi))))
    &&
    (fa (old:Type, new:Type, pos:Position, v:Variable, t:Type, p:Pattern,
         newT:Type)
       isTypeSubstInTypeAt? (t, old, new, pos, newT) =>
       isTypeSubstInPattAt? (alias (v, t, p), old, new, 0 |> pos,
                             alias (v, newT, p)))
    &&
    (fa (old:Type, new:Type, pos:Position, v:Variable, t:Type, p:Pattern,
         newP:Pattern)
       isTypeSubstInPattAt? (p, old, new, pos, newP) =>
       isTypeSubstInPattAt? (alias (v, t, p), old, new, 1 |> pos,
                             alias (v, t, newP))))


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % expression substitution at position:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op isExprSubstAt? :
     Expression * Expression * Expression * Position * Expression -> Boolean

  def isExprSubstAt? = min (fn isExprSubstAt? ->
    (fa (old:Expression, new:Expression)
       isExprSubstAt? (old, old, new, empty, new))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         eo:UnaryExprOperator, e:Expression, newE:Expression)
       isExprSubstAt? (e, old, new, pos, newE) =>
       isExprSubstAt? (unary (eo, e), old, new, 0 |> pos,
                       unary (eo, newE)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         eo:BinaryExprOperator, e1:Expression, e2:Expression, newE1:Expression)
       isExprSubstAt? (e1, old, new, pos, newE1) =>
       isExprSubstAt? (binary (eo, e1, e2), old, new, 1 |> pos,
                       binary (eo, newE1, e2)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         eo:BinaryExprOperator, e1:Expression, e2:Expression, newE2:Expression)
       isExprSubstAt? (e2, old, new, pos, newE2) =>
       isExprSubstAt? (binary (eo, e1, e2), old, new, 2 |> pos,
                       binary (eo, e1, newE2)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE0:Expression)
       isExprSubstAt? (e0, old, new, pos, newE0) =>
       isExprSubstAt? (ifThenElse (e0, e1, e2), old, new, 0 |> pos,
                       ifThenElse (newE0, e1, e2)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE1:Expression)
       isExprSubstAt? (e1, old, new, pos, newE1) =>
       isExprSubstAt? (ifThenElse (e0, e1, e2), old, new, 1 |> pos,
                       ifThenElse (e0, newE1, e2)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e0:Expression, e1:Expression, e2:Expression, newE2:Expression)
       isExprSubstAt? (e2, old, new, pos, newE2) =>
       isExprSubstAt? (ifThenElse (e0, e1, e2), old, new, 2 |> pos,
                       ifThenElse (e0, e1, newE2)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         eo:NaryExprOperator, eS:Expressions, i:Nat, newEi:Expression)
       isExprSubstAt? (eS!i, old, new, pos, newEi) =>
       isExprSubstAt? (nary (eo, eS), old, new, (i+1) |> pos,
                       nary (eo, update(eS,i,newEi))))
    &&
    (fa (old:Expression, new:Expression, pos:Position, eo:BindingExprOperator,
         vS:Variables, tS:Types, e:Expression, newE:Expression)
       isExprSubstAt? (e, old, new, pos, newE) =>
       isExprSubstAt? (binding (eo, vS, tS, e), old, new, 0 |> pos,
                       binding (eo, vS, tS, newE)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         e:Expression, pS:Patterns, eS:Expressions, newE:Expression)
       isExprSubstAt? (e, old, new, pos, newE) =>
       isExprSubstAt? (casE (e, pS, eS), old, new, 0 |> pos,
                       casE (newE, pS, eS)))
    &&
    (fa (old:Expression, new:Expression, pos:Position, e:Expression,
         pS:Patterns, eS:Expressions, i:Nat, newEi:Expression)
       i < length eS &&
       isExprSubstAt? (eS!i, old, new, pos, newEi) =>
       isExprSubstAt? (casE (e, pS, eS), old, new, (i+1) |> pos,
                       casE (e, pS, update(eS,i,newEi))))
    &&
    (fa (old:Expression, new:Expression, pos:Position, vS:Variables, tS:Types,
         eS:Expressions, e:Expression, newE:Expression)
       isExprSubstAt? (e, old, new, pos, newE) =>
       isExprSubstAt? (recursiveLet (vS, tS, eS, e), old, new, 0 |> pos,
                       recursiveLet (vS, tS, eS, newE)))
    &&
    (fa (old:Expression, new:Expression, pos:Position, vS:Variables, tS:Types,
         eS:Expressions, e:Expression, i:Nat, newEi:Expression)
       i < length eS &&
       isExprSubstAt? (eS!i, old, new, pos, newEi) =>
       isExprSubstAt? (recursiveLet (vS, tS, eS, e), old, new, (i+1) |> pos,
                       recursiveLet (vS, tS, update(eS,i,newEi), e)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         p:Pattern, e:Expression, e1:Expression, newE:Expression)
       isExprSubstAt? (e, old, new, pos, newE) =>
       isExprSubstAt? (nonRecursiveLet (p, e, e1), old, new, 0 |> pos,
                       nonRecursiveLet (p, newE, e1)))
    &&
    (fa (old:Expression, new:Expression, pos:Position,
         p:Pattern, e:Expression, e1:Expression, newE1:Expression)
       isExprSubstAt? (e1, old, new, pos, newE1) =>
       isExprSubstAt? (nonRecursiveLet (p, e, e1), old, new, 1 |> pos,
                       nonRecursiveLet (p, e, newE1))))

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
           | unary(_,e)              -> (assert (i = 0);
                                         captVarsAt(pos,e))
           | binary(_,e1,e2)         -> if i = 1 then captVarsAt(pos,e1)
                                   else (assert (i = 2); captVarsAt(pos,e2))
           | ifThenElse(e0,e1,e2)    -> if i = 0 then captVarsAt(pos,e0)
                                   else if i = 1 then captVarsAt(pos,e1)
                                   else (assert (i = 2); captVarsAt(pos,e2))
           | nary(_,eS)              -> (assert (1 <= i && i <= length eS);
                                         captVarsAt (pos, eS!(i-1)))
           | binding(_,vS,_,e)       -> (assert (i = 0);
                                         captVarsAt(pos,e) \/ toSet vS)
           | casE(e,pS,eS)           -> if i = 0 then captVarsAt(pos,e)
                                        else
                                          (assert (1 <= i && i <= length eS);
                                           captVarsAt (pos, eS!(i-1)) \/
                                           (if i <= length pS
                                               % in well-formed expressions,
                                               % i <= length pS = length eS
                                            then pattVars (pS!(i-1))
                                            else empty))
           | recursiveLet(vS,_,eS,e) -> toSet vS \/
                                        (if i = 0
                                         then captVarsAt(pos,e)
                                         else (assert (1 <= i && i <= length eS);
                                               captVarsAt (pos, eS!(i-1))))
           | nonRecursiveLet(p,e,e1) -> if i = 0 then captVarsAt(pos,e)
                                        else
                                          (assert (i = 1);
                                           pattVars p \/ captVarsAt(pos,e1))

  op exprSubstAtOK? : Expression * Expression * Expression * Position -> Boolean
  def exprSubstAtOK?(e,old,new,pos) =
    (ex (newE:Expression)
       isExprSubstAt? (e, old, new, pos, newE) &&
       exprFreeVars old /\ captVarsAt(pos,e) = empty &&
       exprFreeVars new /\ captVarsAt(pos,e) = empty)

endspec
