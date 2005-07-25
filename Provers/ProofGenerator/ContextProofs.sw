spec

  % API public contextProof

  import ../ProofChecker/Proofs, ../ProofChecker/Substitutions, ../ProofChecker/BasicAbbreviations
  import TypeProofs
  
  (* In this spec we define a function that takes a context and
  generates a proof that the context is well-formed. *)

  op typeDeclaration?: ContextElement -> Boolean
  def typeDeclaration?(ce) =
    case ce of
      | typeDeclaration _ -> true
      | _ -> false

  op opDeclaration?: ContextElement -> Boolean
  def opDeclaration?(ce) =
    case ce of
      | opDeclaration _ -> true
      | _ -> false

  op typeDefinition?: ContextElement -> Boolean
  def typeDefinition?(ce) =
    case ce of
      | typeDefinition _ -> true
      | _ -> false

  op opDefinition?: ContextElement -> Boolean
  def opDefinition?(ce) =
    case ce of
      | opDefinition _ -> true
      | _ -> false

  op axioM?: ContextElement -> Boolean
  def axioM?(ce) =
    case ce of
      | axioM _ -> true
      | _ -> false

  op typeVarDeclaration?: ContextElement -> Boolean
  def typeVarDeclaration?(ce) =
    case ce of
      | typeVarDeclaration _ -> true
      | _ -> false

  op varDeclaration?: ContextElement -> Boolean
  def varDeclaration?(ce) =
    case ce of
      | varDeclaration _ -> true
      | _ -> false


  type TypeDeclarationContextElement = (ContextElement | typeDeclaration?)
  type OpDeclarationContextElement = (ContextElement | opDeclaration?)
  type TypeDefinitionContextElement = (ContextElement | typeDefinition?)
  type OpDefinitionContextElement = (ContextElement | opDefinition?)
  type AxioMContextElement = (ContextElement | axioM?)
  type TypeVarDeclarationContextElement = (ContextElement | typeVarDeclaration?)
  type VarDeclarationContextElement = (ContextElement | varDeclaration?)
  
  op wellFormedTypeProof: Proof * Context * Type -> Proof
  def wellFormedTypeProof(cxProof, cx, t) =
    typeProof(cxProof, cx, t)
  
  op wellFormedTypeAssumption: Context * Type -> Proof
  def wellFormedTypeAssumption(cx, t) =
    assume (wellFormedType(cx, t))

  (*
   Take a proof that a context is well-formed, a context,
   a type variable, and generate a new context that includes
   the type variable declaration and associated proof of
   well-formedness.
   *)

  op typeVarDeclarationContextAndProof: Proof * Context * TypeVariable -> Proof * Context
  def typeVarDeclarationContextAndProof(cxPrf, cx, tv) =
    let tvd = typeVarDeclaration(tv) in
    let cx = cx <| tvd in
    let cxPrf = cxTVdec(cxPrf, tv) in
    (cxPrf, cx)

  (*
   Take a proof that a context is well-formed, a context, a seq
   of type variables and generate a new context that includes the
   type variable declarations associated proof of well-formedness.
   *)

  op typeVarDeclarationsContextAndProof: Proof * Context * TypeVariables -> Proof * Context
  def typeVarDeclarationsContextAndProof(cxPrf, cx, tvs) =
    if empty?(tvs)
      then (cxPrf, cx)
    else
      let tv = first(tvs) in
      let tvs = rtail(tvs) in
      let (cxPrf, cx) = typeVarDeclarationContextAndProof(cxPrf, cx, tv) in
      typeVarDeclarationsContextAndProof(cxPrf, cx, tvs)
  
  op typeVarDeclarations: TypeVariables -> Context
  def typeVarDeclarations(tvs) =
    if empty?(tvs) then empty
    else typeVarDeclaration (first(tvs)) |> typeVarDeclarations(rtail(tvs))

  op cxMTProof: Context -> Proof
  def cxMTProof(cx) =
    cxMT

  op cxTdecProof: Context * TypeDeclarationContextElement -> Proof
  def cxTdecProof(cx, td) =
    let typeDeclaration(tn, n) = td in
    let cxProof = contextProof(cx) in
    cxTdec(cxProof, tn, n)
    
  op cxOdecProof: Context * OpDeclarationContextElement -> Proof
  def cxOdecProof(cx, od) =
    let opDeclaration(oper, tvs, t) = od in
    let cxProof = contextProof(cx) in
    let (wftCxPrf, wftCx) = typeVarDeclarationsContextAndProof(cxProof, cx, tvs) in
    let wfTProof = wellFormedTypeProof(wftCxPrf, wftCx, t) in
    cxOdec(cxProof, wfTProof, oper)

  op cxTDefProof: Context * TypeDefinitionContextElement -> Proof
  def cxTDefProof(cx, td) =
    let typeDefinition (tn, tvs, t) = td in
    let cxProof = contextProof(cx) in
    let (wftCxPrf, wftCx) = typeVarDeclarationsContextAndProof(cxProof, cx, tvs) in
    let wfTProof = wellFormedTypeProof(wftCxPrf, wftCx, t) in
    cxTdef(cxProof, wfTProof, tn)

  op cxOdefProof: Context * OpDefinitionContextElement -> Proof
  def cxOdefProof(cx, od) =
    let opDefinition(oper, ts, exp) = od in
    let cxProof = contextProof(cx) in
    let opDeclSeq = filter (fn (opDeclaration(o, tvs1, t)) -> o = oper | _ -> false) cx in
    if length(opDeclSeq) ~= 1 then falseProof(cx) else
    let opDeclaration(_, tvs1, t) = theElement(opDeclSeq) in
    let typeVarSubst = fromSeqs(tvs1, map VAR ts) in
    let operVar = uniqueDefVar in
    let wfDefProof = assume (theoreM (cx ++ multiTypeVarDecls tvs1, EX1(operVar, typeSubstInType typeVarSubst t, replaceOperationWithVar(oper, operVar, exp)))) in
    cxOdef(cxProof, wfDefProof, oper)

  op uniqueDefVar: Variable

  op replaceOperationWithVar: Operation * Variable * Expression -> Expression
  def replaceOperationWithVar(oper, var, expr) =
    case expr of
      | VAR _              -> expr
      | OPI (o, t)         -> if o = oper then VAR var else expr
      | APPLY(e1,e2)       -> APPLY (replaceOperationWithVar(oper, var, e1), replaceOperationWithVar(oper, var, e2))
      | FN(v,t,b)          -> FN (v, t, replaceOperationWithVar(oper, var, b))
      | EQ(e1,e2)          -> EQ (replaceOperationWithVar(oper, var, e1), replaceOperationWithVar(oper, var, e2))
      | IF(e0,e1,e2)       -> IF (replaceOperationWithVar(oper, var, e0),
				  replaceOperationWithVar(oper, var, e1),
				  replaceOperationWithVar(oper, var, e2))
      | _                  -> expr

			     

(*
    | cxOdef ->
      (fa (cx:Context, o:Operation, tvS:TypeVariables, t:Type, tvS1:TypeVariables,
           v:Variable, tsbs:TypeSubstitution, e:Expression, e1:Expression)
         pj (wellFormedContext cx)
      && opDeclaration (o, tvS, t) in? cx
      && ~(contextDefinesOp? (cx, o))
      && isTypeSubstFrom? (tsbs, tvS, map VAR tvS1)
      && pj (theoreM (cx ++ multiTypeVarDecls tvS1,
                      EX1 (v, typeSubstInType tsbs t, VAR v == e)))
      && ~(o in? exprOps e)
      && e1 = exprSubst v (OPI (o, map VAR tvS1)) e
         (* Distinctness of tvS is in the syntax in LD. We do not need to add
         it to this inference rule because it is a meta theorem. *)
      => pj (wellFormedContext (cx <| opDefinition (o, tvS1, e1))))

*)

  op cxAxProof: Context * AxioMContextElement -> Proof
  def cxAxProof(cx, axd) =
    let axioM(an, tvs, exp) = axd in
    let cxProof = contextProof(cx) in
    let (wftCxPrf, wftCx) = typeVarDeclarationsContextAndProof(cxProof, cx, tvs) in
    let wfTProof = wellFormedTypeProof(wftCxPrf, wftCx, BOOL) in
    cxAx(cxProof, wfTProof, an)

  op cxTVdecProof: Context * TypeVarDeclarationContextElement -> Proof
  def cxTVdecProof(cx, tvd) =
    let typeVarDeclaration(tv) = tvd in
    let cxProof = contextProof(cx) in
    cxTVdec(cxProof, tv)

  op cxVdecProof: Context * VarDeclarationContextElement -> Proof
  def cxVdecProof(cx, vd) =
    let varDeclaration(v, t) = vd in
    let cxProof = contextProof(cx) in
    let wfTProof = wellFormedTypeProof(cxProof, cx, t) in
    cxVdec(cxProof, wfTProof, v)

  op contextProof: Context -> Proof
  def contextProof(cx) =
    if empty?(cx)
      then cxMTProof(cx)
    else
      let ce = last(cx) in
      let cx = ltail(cx) in
      if typeDeclaration?(ce) then cxTdecProof(cx, ce)
      else if opDeclaration?(ce) then cxOdecProof(cx, ce)
      else if typeDefinition?(ce) then cxTDefProof(cx, ce)
      else if opDefinition?(ce) then cxOdefProof(cx, ce)
      else if axioM?(ce) then cxAxProof(cx, ce)
      else if typeVarDeclaration?(ce) then cxTVdecProof(cx, ce)
      else (* if varDeclaration?(ce) then *) cxVdecProof(cx, ce)

endspec
