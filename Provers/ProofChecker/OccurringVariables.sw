spec

  (* This spec defines various ops that collect variables and other names
  occurring in syntactic entities (e.g. free variables in expressions). *)

  import Libs/StructureConversions

  import Judgements

  % variables introduced by pattern:

  op pattVars : Pattern -> FSet Name

  op pattSeqVars : FSeq Pattern -> FSet Name
  def pattSeqVars patts =  % given patts = p1, ..., pn
    % compute pattVars p1, ..., pattVars pn:
    let varSets:FSeq(FSet Name) = map (pattVars, patts) in
    % compute pattVars p1 \/ ... \/ pattVars pn:
    foldl (varSets, empty, (\/))

  def pattVars = fn
    | variable(v,_)    -> singleton v
    | embedding(_,_,p) -> pattVars p
    | record comps     -> let patts = map (project 2, comps) in
                          pattSeqVars patts
    | alias(v,_,p)     -> pattVars p with v

  % free variables in expression:

  op exprFreeVars : Expression -> FSet Name

  op exprSeqFreeVars : FSeq Expression -> FSet Name
  def exprSeqFreeVars exprs =  % given exprs = e1, ..., en
    % compute exprFreeVars e1, ..., exprFreeVars en:
    let varSets:FSeq(FSet Name) = map (exprFreeVars, exprs) in
    % compute exprFreeVars e1 \/ ... \/ exprFreeVars en:
    foldl (varSets, empty, (\/))

  def exprFreeVars = fn
    | variable v               -> singleton v
    | opInstance _             -> empty
    | application(e1,e2)       -> exprFreeVars e1 \/ exprFreeVars e2
    | abstraction((v,_),e)     -> exprFreeVars e wout v
    | equation(e1,e2)          -> exprFreeVars e1 \/ exprFreeVars e2
    | ifThenElse(e0,e1,e2)     -> exprFreeVars e0 \/
                                  exprFreeVars e1 \/ exprFreeVars e2
    | record comps             -> let exprs = map (project 2, comps) in
                                  exprSeqFreeVars exprs
    | recordProjection(e,_)    -> exprFreeVars e
    | recordUpdate(e1,e2)      -> exprFreeVars e1 \/ exprFreeVars e2
    | embedder _               -> empty
    | relaxator _              -> empty
    | restriction(_,e)         -> exprFreeVars e
    | quotienter _             -> empty
    | choice(_,e)              -> exprFreeVars e
    | cas(e,branches)          -> let exprs = map (project 2, branches) in
                                  let patts = map (project 1, branches) in
                                  let def branchVars
                                          (e:Expression, p:Pattern) : FSet Name =
                                          exprFreeVars e -- pattVars p in
                                  let varSets:FSeq(FSet Name) =
                                      map2 (branchVars, exprs, patts) in
                                  foldl (varSets, empty, (\/))
    | recursiveLet(asgments,e) -> let exprs = map (project 2, asgments) in
                                  let binds = map (project 1, asgments) in
                                  let boundVars =
                                      toSet (map (project 1, binds)) in
                                  (exprSeqFreeVars exprs \/ exprFreeVars e)
                                  -- boundVars
    | tru                      -> empty
    | fals                     -> empty
    | negation e               -> exprFreeVars e
    | conjunction(e1,e2)       -> exprFreeVars e1 \/ exprFreeVars e2
    | disjunction(e1,e2)       -> exprFreeVars e1 \/ exprFreeVars e2
    | implication(e1,e2)       -> exprFreeVars e1 \/ exprFreeVars e2
    | equivalence(e1,e2)       -> exprFreeVars e1 \/ exprFreeVars e2
    | inequation(e1,e2)        -> exprFreeVars e1 \/ exprFreeVars e2
    | universal(binds,e)       -> let boundVars =
                                      toSet (map (project 1, binds)) in
                                  exprFreeVars e -- boundVars
    | existential(binds,e)     -> let boundVars =
                                      toSet (map (project 1, binds)) in
                                  exprFreeVars e -- boundVars
    | existential1((v,_),e)    -> exprFreeVars e wout v
    | nonRecursiveLet(p,e,e1)  -> exprFreeVars e \/
                                  (exprFreeVars e1 -- pattVars p)
    | tuple exprs              -> exprSeqFreeVars exprs
    | tupleProjection(e,_)     -> exprFreeVars e

  % types, ops, type variables, and variables declared in context:

  op contextElementTypes    : ContextElement -> FSet Name
  op contextElementOps      : ContextElement -> FSet Name
  op contextElementTypeVars : ContextElement -> FSet Name
  op contextElementVars     : ContextElement -> FSet Name

  def contextElementTypes = fn
    | typeDeclaration(t,_) -> singleton t
    | _                    -> empty

  def contextElementOps = fn
    | opDeclaration(o,_,_) -> singleton o
    | _                    -> empty

  def contextElementTypeVars = fn
    | tVarDeclaration tv -> singleton tv
    | _                  -> empty

  def contextElementVars = fn
    | varDeclaration(v,_) -> singleton v
    | _                   -> empty

  op collectFromContext : Context * (ContextElement -> FSet Name) -> FSet Name
  def collectFromContext (cx, collectFunc) =
    let nameSets:FSeq(FSet Name) = map (collectFunc, cx) in
    foldl (nameSets, empty, (\/))

  op contextTypes    : Context -> FSet Name
  op contextOps      : Context -> FSet Name
  op contextTypeVars : Context -> FSet Name
  op contextVars     : Context -> FSet Name

  def contextTypes    cx = collectFromContext (cx, contextElementTypes)
  def contextOps      cx = collectFromContext (cx, contextElementOps)
  def contextTypeVars cx = collectFromContext (cx, contextElementTypeVars)
  def contextVars     cx = collectFromContext (cx, contextElementVars)

endspec
