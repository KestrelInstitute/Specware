spec

  (* This spec defines various ops that collect occurrences of variables and
  other entities (e.g. free variables in expressions). *)

  import Judgements


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % variables introduced by pattern:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op pattVars : Pattern -> FSet Variable

  op pattSeqVars : FSeq Pattern -> FSet Variable
  def pattSeqVars patts =
    unionAll (map (pattVars, patts))

  def pattVars = fn
    | variable(v,_)    -> singleton v
    | embedding(_,_,p) -> pattVars p
    | record(_,pS)     -> pattSeqVars pS
    | alias(v,_,p)     -> pattVars p with v


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % free variables in expression:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* In LD, free variables of subtype and quotient type predicates are not
  considered in the syntax because the well-typedness rules for expression
  force such predicates to have no free variables. However, here it is easier
  to consider them because of the way we have factored expressions. *)

  op exprFreeVars : Expression -> FSet Variable

  op exprSeqFreeVars : FSeq Expression -> FSet Variable
  def exprSeqFreeVars eS =
    unionAll (map (exprFreeVars, eS))

  def exprFreeVars = fn
    | nullary(variable v)      -> singleton v
    | unary(_,e)               -> exprFreeVars e
    | binary(_,e1,e2)          -> exprFreeVars e1 \/ exprFreeVars e2
    | ifThenElse(e0,e1,e2)     -> exprFreeVars e0 \/
                                  exprFreeVars e1 \/
                                  exprFreeVars e2
    | nary(_,eS)               -> exprSeqFreeVars eS
    | binding(_,bvS,e)         -> let (vS, _) = unzip bvS in
                                  exprFreeVars e -- toSet vS
    | cas(e,branches)          -> let (pS,eS) = unzip branches in
                                  let vSets =
                                      seqSuchThat (fn(i:Nat) ->
                                        if i < length branches
                                        then Some (exprFreeVars (eS elem i) --
                                                   pattVars     (pS elem i))
                                        else None) in
                                  unionAll vSets \/ exprFreeVars e
    | recursiveLet(asgments,e) -> let (bvS, eS) = unzip asgments in
                                  let (vS, _) = unzip bvS in
                                  (exprSeqFreeVars eS \/ exprFreeVars e)
                                  -- toSet vS
    | nonRecursiveLet(p,e,e1)  -> exprFreeVars e \/
                                  (exprFreeVars e1 -- pattVars p)
    | _                        -> empty


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % type names, ops, type variables, and variables declared in context:
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

endspec
