spec

  (* This spec defines the recursive function described in spec `Proofs' (see
  that spec for an explanation). The function is called `check', because it
  checks whether a proof is valid, and if it is valid, then it returns the
  judgement proved by the proof. Failure is modeled via the meta type
  `MayFail' defined in spec`Failures'.

  Checking proof steps involves several checks, some by pattern matching (via
  `case') and some by testing conditions (via `if'). If a check fails, `FAIL'
  is returned. Since there can be several such checks one after the other,
  the definitions below we do not always follow the usual Metaslang
  indentation style, because after not many checks we would get too far to the
  right. Rather, all the subsequent checks are left-aligned. After all checks
  have succeeded and an `OK' result is returned, we deal with all the check
  failures, either as `_ -> FAIL' for a failed pattern matching or as `else
  FAIL' for a failed condition test, also all left-aligned. This indentation
  style should be clear when looking at the definitions below.

  The quite verbose handling of failures in the definitions below could be
  made more succint and readable using a monadic approach with specialized
  syntax.

  The definitions in this spec are executable. However, they could be made
  more abstract, but non-executable. *)


  import Proofs, Failures, SyntaxWithCoreOps


  op checkSequence : [a] FSeq (MayFail a) -> MayFail (FSeq a)
  def [a] checkSequence s =
    let def aux (input  : FSeq (MayFail a),
                 output : FSeq a)
                : MayFail (FSeq a) =
          if input = empty then OK output
          else case first input of
                 | OK outputElement ->
                   aux (rtail input, output <| outputElement)
                 | FAIL -> FAIL
    in
    aux (s, empty)

  op checkOptionSequence : [a] FSeq (Option (MayFail a)) ->
                               MayFail (FSeq (Option a))
  def [a] checkOptionSequence s =
    let def aux (input  : FSeq (Option (MayFail a)),
                 output : FSeq (Option a))
                : MayFail (FSeq (Option a)) =
          if input = empty then OK output
          else case first input of
                 | Some (OK outputElement) ->
                   aux (rtail input, output <| Some outputElement)
                 | Some FAIL -> FAIL
                 | None -> aux (rtail input, output <| None)
    in
    aux (s, empty)

  op checkPermutation : FSeq Nat -> MayFail Permutation
  def checkPermutation natS =
    if noRepetitions? natS
    && forall? (natS, fn i:Nat -> i < length natS)
    then OK natS
    else FAIL

  op checkExtraTypeVars : Context -> Context -> MayFail TypeVariables
  def checkExtraTypeVars cx1 cx2 =
    if length cx1 <= length cx2
    && firstN (cx2, length cx1) = cx1 then
    let cxExtra = lastN (cx2, length cx2 - length cx1) in
    if forall? (cxExtra, embed? typeVarDeclaration) then
    let def getTypeVar (ce:ContextElement) : Option TypeVariable =
          case ce of typeVarDeclaration tv -> Some tv
                   | _                     -> None in
    let tvS:TypeVariables = removeNones (map (getTypeVar, cxExtra)) in
    OK tvS
    else FAIL
    else FAIL

  op checkLastNVars : Context -> Nat -> MayFail (Context * Variables * Types)
  def checkLastNVars cx n =
    if length cx >= n then
    let cxTail:Context = lastN (cx, n) in
    if forall? (cxTail, embed? varDeclaration) then
    let def getVarAndType (ce:ContextElement) : Option (Variable * Type) =
          case ce of varDeclaration(v,t) -> Some (v, t)
                   | _                   -> None in
    let vtS:FSeq(Variable*Type) = removeNones (map (getVarAndType, cxTail)) in
    let (vS:Variables, tS:Types) = unzip vtS in
    OK (firstN (cx, length cx - n), vS, tS)
    else FAIL
    else FAIL

  op checkExtraAxiom :
     Context -> Context -> MayFail (AxiomName * TypeVariables * Expression)
  def checkExtraAxiom cx1 cx2 =
    if length cx2 = length cx1 + 1 then
    case last cx2 of
      | axioM (an, tvS, e) -> OK (an, tvS, e)
      | _ -> FAIL
    else FAIL

  op checkTypeDecl : Context -> TypeName -> MayFail Nat
  def checkTypeDecl cx tn =
    if cx = empty then FAIL
    else case first cx of
           | typeDeclaration(tn1,n) ->
             if tn1 = tn then OK n
             else checkTypeDecl (rtail cx) tn
           | _ -> checkTypeDecl (rtail cx) tn

  op checkOpDecl : Context -> Operation -> MayFail (TypeVariables * Type)
  def checkOpDecl cx o =
    if cx = empty then FAIL
    else case first cx of
           | opDeclaration(o1,tvS,t) ->
             if o1 = o then OK (tvS, t)
             else checkOpDecl (rtail cx) o
           | _ -> checkOpDecl (rtail cx) o

  op checkVarDecl : Context -> Variable -> MayFail Type
  def checkVarDecl cx v =
    if cx = empty then FAIL
    else case first cx of
           | varDeclaration(v1,t) ->
             if v1 = v then OK t
             else checkVarDecl (rtail cx) v
           | _ -> checkVarDecl (rtail cx) v

  op checkTypeDef : Context -> TypeName -> MayFail (TypeVariables * Type)
  def checkTypeDef cx tn =
    if cx = empty then FAIL
    else case first cx of
           | typeDefinition(tn1,tvS,t) ->
             if tn1 = tn then OK (tvS, t)
             else checkTypeDef (rtail cx) tn
           | _ -> checkTypeDef (rtail cx) tn

  op checkTypeSubstitution : TypeVariables -> Types -> MayFail TypeSubstitution
  def checkTypeSubstitution tvS tS =
    if noRepetitions? tvS && length tvS = length tS
    then OK (FMap.fromSequences (tvS, tS))
    else FAIL

  op checkFieldType : Type -> Field -> MayFail Type
  def checkFieldType t f =
    case t of
      | nary (record fS, tS) ->
        if noRepetitions? fS then
        let i:Nat = indexOf (fS, f) in
        if i < length tS then
        OK (tS!i)
        else FAIL
        else FAIL
      | _ -> FAIL

  op checkConstructorType? : Type -> Constructor -> MayFail Type?
  def checkConstructorType? t c =
    case t of
      | sum (cS, t?S) ->
        if noRepetitions? cS then
        let i:Nat = indexOf (cS, c) in
        if i < length t?S then
        OK (t?S ! i)
        else FAIL
        else FAIL
      | _ -> FAIL

  op checkRecordTypeUnion : Type -> Type -> MayFail Type
  def checkRecordTypeUnion t1 t2 =
    case (t1, t2) of (nary (record fS1, tS1), nary (record fS2, tS2)) ->
    if length fS1 = length tS1
    && length fS2 = length tS2 then
    let fS = maxCommonPrefix (fS1, fS2) in
    let tS = maxCommonPrefix (tS1, tS2) in
    if toSet (lastN (fS1, length fS1 - length fS)) /\
       toSet (lastN (fS2, length fS2 - length fS)) = empty then
    OK (TRECORD (fS1 ++ lastN (fS2, length fS2 - length fS))
                (tS1 ++ lastN (tS2, length tS2 - length tS)))
    else   FAIL
    else   FAIL
    | _ -> FAIL


  op typeSubstInTypeAt : Type       * Type * Type * Position -> MayFail Type
  op typeSubstInExprAt : Expression * Type * Type * Position -> MayFail Expression
  op typeSubstInPattAt : Pattern    * Type * Type * Position -> MayFail Pattern

  def typeSubstInTypeAt(t,old,new,pos) =
    if pos = empty then
      if old = t then OK new
      else FAIL
    else
      let i   = first pos in
      let pos = rtail pos in
      case t of
        | arrow(t1,t2) ->
          if i = 1 then
            case typeSubstInTypeAt (t1, old, new, pos) of
              | OK newT1 -> OK (arrow (newT1, t2))
              | FAIL     -> FAIL
          else if i = 2 then
            case typeSubstInTypeAt (t2, old, new, pos) of
              | OK newT2 -> OK (arrow (t1, newT2))
              | FAIL     -> FAIL
          else FAIL
        | sum(cS,t?S) ->
          if i < length t?S then
            case t?S ! i of
              | Some ti ->
                (case typeSubstInTypeAt (ti, old, new, pos) of
                   | OK newTi -> OK (sum (cS, update (t?S, i, Some newTi)))
                   | FAIL     -> FAIL)
              | None -> FAIL
          else FAIL
        | nary(tc,tS) ->
          if i < length tS then
            case typeSubstInTypeAt (tS!i, old, new, pos) of
              | OK newTi -> OK (nary (tc, update (tS, i, newTi)))
              | FAIL     -> FAIL
          else FAIL
        | subQuot(tc,t,e) ->
          if i = 0 then
            case typeSubstInTypeAt (t, old, new, pos) of
              | OK newT -> OK (subQuot (tc, newT, e))
              | FAIL    -> FAIL
          else if i = 1 then
            case typeSubstInExprAt (e, old, new, pos) of
              | OK newE -> OK (subQuot (tc, t, newE))
              | FAIL    -> FAIL
          else FAIL
        | _ -> FAIL

  def typeSubstInExprAt(e,old,new,pos) =
    if pos = empty then FAIL
    else
      let i   = first pos in
      let pos = rtail pos in
      case e of
        | unary(eo,e) ->
          if i = 0 then
            case typeSubstInExprAt (e, old, new, pos) of
              | OK newE -> OK (unary (eo, newE))
              | FAIL    -> FAIL
          else FAIL
        | binary(eo,e1,e2) ->
          if i = 1 then
            case typeSubstInExprAt (e1, old, new, pos) of
              | OK newE1 -> OK (binary (eo, newE1, e2))
              | FAIL     -> FAIL
          else if i = 2 then
            case typeSubstInExprAt (e2, old, new, pos) of
              | OK newE2 -> OK (binary (eo, e1, newE2))
              | FAIL     -> FAIL
          else FAIL
        | ifThenElse(e0,e1,e2) ->
          if i = 0 then
            case typeSubstInExprAt (e0, old, new, pos) of
              | OK newE0 -> OK (ifThenElse (newE0, e1, e2))
              | FAIL     -> FAIL
          else if i = 1 then
            case typeSubstInExprAt (e1, old, new, pos) of
              | OK newE1 -> OK (ifThenElse (e0, newE1, e2))
              | FAIL     -> FAIL
          else if i = 2 then
            case typeSubstInExprAt (e2, old, new, pos) of
              | OK newE2 -> OK (ifThenElse (e0, e1, newE2))
              | FAIL     -> FAIL
          else FAIL
        | nary(eo,eS) ->
          if i < length eS then
            case typeSubstInExprAt (eS!i, old, new, pos) of
              | OK newEi -> OK (nary (eo, update (eS, i, newEi)))
              | FAIL     -> FAIL
          else FAIL
        | binding(eo,vS,tS,e) ->
          if i = 0 then
            case typeSubstInExprAt (e, old, new, pos) of
              | OK newE -> OK (binding (eo, vS, tS, newE))
              | FAIL    -> FAIL
          else if i <= length tS then
            case typeSubstInTypeAt (tS!(i-1), old, new, pos) of
              | OK newTi -> OK (binding (eo, vS, update (tS, i-1, newTi), e))
              | FAIL     -> FAIL
          else FAIL
        | opInstance(o,tS) ->
          if i < length tS then
            case typeSubstInTypeAt (tS!i, old, new, pos) of
              | OK newTi -> OK (opInstance (o, update (tS, i, newTi)))
              | FAIL     -> FAIL
          else FAIL
        | embedder(t,c) ->
          if i = 0 then
            case typeSubstInTypeAt (t, old, new, pos) of
              | OK newT -> OK (embedder (newT, c))
              | FAIl    -> FAIL
          else FAIL
        | casE(e,pS,eS) ->
          if i = 0 then
            case typeSubstInExprAt (e, old, new, pos) of
              | OK newE -> OK (casE (newE, pS, eS))
              | FAIL    -> FAIL
          else if i rem 2 = 1 then  % i.e. i is odd
            let j:Nat = i div 2 in
            if j < length pS then
              case typeSubstInPattAt (pS!j, old, new, pos) of
                | OK newPj -> OK (casE (e, update (pS, j, newPj), eS))
                | FAIL     -> FAIL
            else FAIL
          else if i rem 2 = 0 then  % i.e. i is even
            let j:Nat = i div 2 in
            if j < length eS then
              case typeSubstInExprAt (eS!j, old, new, pos) of
                | OK newEj -> OK (casE (e, pS, update (eS, j, newEj)))
                | FAIL     -> FAIL
            else FAIL
          else FAIL
        | recursiveLet(vS,tS,eS,e) ->
          if i = 0 then
            case typeSubstInExprAt (e, old, new, pos) of
              | OK newE -> OK (recursiveLet (vS, tS, eS, newE))
              | FAIL    -> FAIL
          else if i rem 2 = 0 then  % i.e. i is odd
            let j:Nat = i div 2 in
            if j < length tS then
              case typeSubstInTypeAt (tS!j, old, new, pos) of
                | OK newTj -> OK (recursiveLet (vS, update (tS, j, newTj), eS, e))
                | FAIL     -> FAIL
            else FAIL
          else if i rem 2 = 0 then  % i.e. i is even
            let j:Nat = i div 2 in
            if j < length eS then
              case typeSubstInExprAt (eS!j, old, new, pos) of
                | OK newEj -> OK (recursiveLet (vS, tS, update (eS, j, newEj), e))
                | FAIL     -> FAIL
            else FAIL
          else FAIL
        | nonRecursiveLet(p,e,e1) ->
          if i = 0 then
            case typeSubstInPattAt (p, old, new, pos) of
              | OK newP -> OK (nonRecursiveLet (newP, e, e1))
              | FAIL    -> FAIL
          else if i = 1 then
            case typeSubstInExprAt (e, old, new, pos) of
              | OK newE -> OK (nonRecursiveLet (p, newE, e1))
              | FAIL    -> FAIL
          else if i = 2 then
            case typeSubstInExprAt (e1, old, new, pos) of
              | OK newE1 -> OK (nonRecursiveLet (p, e, newE1))
              | FAIL     -> FAIL
          else FAIL
        | _ -> FAIL

  def typeSubstInPattAt(p,old,new,pos) =
    if pos = empty then FAIL
    else
      let i   = first pos in
      let pos = rtail pos in
      case p of
        | variable(v,t) ->
          if i = 0 then
            case typeSubstInTypeAt (t, old, new, pos) of
              | OK newT -> OK (variable (v, newT))
              | FAIL    -> FAIL
          else FAIL
        | embedding(t,c,p?) ->
          if i = 0 then
            case typeSubstInTypeAt (t, old, new, pos) of
              | OK newT -> OK (embedding (newT, c, p?))
              | FAIL    -> FAIL
          else
            (case p? of
               | Some p ->
                 if i = 1 then
                   case typeSubstInPattAt (p, old, new, pos) of
                     | OK newP -> OK (embedding (t, c, Some newP))
                     | FAIL    -> FAIL
                 else FAIL
               | None -> FAIL)
        | record(fS,pS) ->
          if i < length pS then
            case typeSubstInPattAt (pS!i, old, new, pos) of
              | OK newPi -> OK (record (fS, update (pS, i, newPi)))
              | FAIL     -> FAIL
          else FAIL
        | tuple pS ->
          if i < length pS then
            case typeSubstInPattAt (pS!i, old, new, pos) of
              | OK newPi -> OK (tuple (update (pS, i, newPi)))
              | FAIL     -> FAIL
          else FAIL
        | alias(v,t,p) ->
          if i = 0 then
            case typeSubstInTypeAt (t, old, new, pos) of
              | OK newT -> OK (alias (v, newT, p))
              | FAIL    -> FAIL
          else if i = 1 then
            case typeSubstInPattAt (p, old, new, pos) of
              | OK newP -> OK (alias (v, t, newP))
              | FAIL    -> FAIL
          else FAIL


  op check : Proof -> MayFail Judgement   % defined below


  op checkContext : Proof -> MayFail Context
  def checkContext prf =
    case check prf of
      | OK (wellFormedContext cx) -> OK cx
      | _ -> FAIL

  op checkType : Proof -> MayFail (Context * Type)
  def checkType prf =
    case check prf of
      | OK (wellFormedType (cx, t)) -> OK (cx, t)
      | _ -> FAIL

  op checkTypeWithContext : Context -> Proof -> MayFail Type
  def checkTypeWithContext cx prf =
    case check prf of
      | OK (wellFormedType (cx1, t)) ->
        if cx1 = cx then OK t else FAIL
      | _ -> FAIL

  op checkTypesWithContext : Context -> Proofs -> MayFail Types
  def checkTypesWithContext cx prfS =
    checkSequence (map (checkTypeWithContext cx, prfS))

  op checkType?sWithContext : Context -> Proof?s -> MayFail Type?s
  def checkType?sWithContext cx prf?S =
    checkOptionSequence (map (mapOption (checkTypeWithContext cx), prf?S))

  op checkSumType : Proof -> MayFail (Context * Constructors * Type?s)
  def checkSumType prf =
    case check prf of
      | OK (wellFormedType (cx, sum (cS, t?S))) ->
        if length cS = length t?S then OK (cx, cS, t?S) else FAIL
      | _ -> FAIL

  op checkRecordType : Proof -> MayFail (Context * Fields * Types)
  def checkRecordType prf =
    case check prf of
      | OK (wellFormedType (cx, nary (record fS, tS))) ->
        if length fS = length tS then OK (cx, fS, tS) else FAIL
      | _ -> FAIL

  op checkProductType : Proof -> MayFail (Context * Types)
  def checkProductType prf =
    case check prf of
      | OK (wellFormedType (cx, nary (product, tS))) -> OK (cx, tS)
      | _ -> FAIL

  op checkSubType : Proof -> MayFail (Context * Type * Expression)
  def checkSubType prf =
    case check prf of
      | OK (wellFormedType (cx, subQuot (sub, t, r))) -> OK (cx, t, r)
      | _ -> FAIL

  op checkSubType2 : Context -> Type -> Proof -> MayFail (Expression)
  def checkSubType2 cx t prf =
    case check prf of
      | OK (wellFormedType (cx1, subQuot (sub, t1, r))) ->
        if cx1 = cx && t1 = t then OK r else FAIL
      | _ -> FAIL

  op checkQuotientType : Proof -> MayFail (Context * Type * Expression)
  def checkQuotientType prf =
    case check prf of
      | OK (wellFormedType (cx, subQuot (quotienT, t, q))) -> OK (cx, t, q)
      | _ -> FAIL

  op checkQuotientType2 : Context -> Type -> Proof -> MayFail (Expression)
  def checkQuotientType2 cx t prf =
    case check prf of
      | OK (wellFormedType (cx1, subQuot (quotienT, t1, q))) ->
        if cx1 = cx && t1 = t then OK q else FAIL
      | _ -> FAIL

  op checkExpr : Proof -> MayFail (Context * Expression * Type)
  def checkExpr prf =
    case check prf of
      | OK (wellTypedExpr (cx, e, t)) -> OK (cx, e, t)
      | _ -> FAIL

  op checkExprWithContext : Context -> Proof -> MayFail (Expression * Type)
  def checkExprWithContext cx prf =
    case check prf of
      | OK (wellTypedExpr (cx1, e, t)) ->
        if cx1 = cx then OK (e, t) else FAIL
      | _ -> FAIL

  op checkExprWithContextAndType :
     Context -> Type -> Proof -> MayFail Expression
  def checkExprWithContextAndType cx t prf =
    case check prf of
      | OK (wellTypedExpr (cx1, e, t1)) ->
        if cx1 = cx && t1 = t then OK e else FAIL
      | _ -> FAIL

  op checkExprsWithContextAndTypes :
     Context -> Types -> Proofs -> MayFail Expressions
  def checkExprsWithContextAndTypes cx tS prfS =
    case checkSequence (map (checkExprWithContext cx, prfS)) of
      | OK exTyS ->
        let (eS, tS1) = unzip exTyS in
        if tS1 = tS then OK eS else FAIL
      | _ -> FAIL

  op checkPattWithContextAndType : Context -> Type -> Proof -> MayFail Pattern
  def checkPattWithContextAndType cx t prf =
    case check prf of
      | OK (wellTypedPatt (cx1, p, t1)) ->
        if cx1 = cx && t1 = t then OK p else FAIL
      | _ -> FAIL

  op checkTheorem : Proof -> MayFail (Context * Expression)
  def checkTheorem prf =
    case check prf of
      | OK (theoreM (cx, e)) -> OK (cx, e)
      | _ -> FAIL

  op checkTheoremWithContext : Context -> Proof -> MayFail Expression
  def checkTheoremWithContext cx prf =
    case check prf of
      | OK (theoreM (cx1, e)) ->
        if cx1 = cx then OK e else FAIL
      | _ -> FAIL

  op checkTheoremGiven : Context -> Expression -> Proof -> MayFail ()
  def checkTheoremGiven cx e prf =
    case check prf of
      | OK (theoreM (cx1, e1)) ->
        if cx1 = cx && e1 = e then OK () else FAIL
      | _ -> FAIL

  op checkTheoremOpDef : Proof -> MayFail (Context * Variable * Type * Expression)
  def checkTheoremOpDef prf =
    case checkTheorem prf of
      | OK (cx, binding (existential1, vS, tS,
                         binary (equation, nullary (variable v), e))) ->
        if vS = singleton v
        && length tS = 1 then
        let t:Type = first tS in
        OK (cx, v, t, e)
        else FAIL
      | _ -> FAIL

  op checkTheoremReflexivity :
     Proof -> MayFail (Context * Variable * Type * Expression)
  def checkTheoremReflexivity prf =
    case checkTheorem prf of
      | OK (cx, binding (universal, vS, tS, binary (application, q, vv))) ->
        if length vS = 1
        && length tS = 1 then
        let v:Variable = first vS in
        let t:Type     = first tS in
        if exprFreeVars q = empty
        &&  vv = PAIR (VAR v) (VAR v) then
        OK (cx, v, t, q)
        else FAIL
        else FAIL
      | _ -> FAIL

  op checkTheoremSymmetry :
     Context -> Type -> Expression -> Proof -> MayFail ()
  def checkTheoremSymmetry cx t q prf =
    case checkTheorem prf of
      | OK (cx1, binding (universal, vS, tS, e)) ->
        if cx1 = cx
        && length vS = 2 then
        let v1:Variable = vS!0 in
        let v2:Variable = vS!1 in
        if v1 ~= v2
        && tS = seq2 (t, t)
        && e = (q @ PAIR (VAR v1) (VAR v2)
                ==>
                q @ PAIR (VAR v2) (VAR v1)) then
        OK ()
        else FAIL
        else FAIL
      | _ -> FAIL

  op checkTheoremTransitivity :
     Context -> Type -> Expression -> Proof -> MayFail ()
  def checkTheoremTransitivity cx t q prf =
    case checkTheorem prf of
      | OK (cx1, binding (universal, vS, tS, e)) ->
        if cx1 = cx
        && length vS = 3 then
        let v1:Variable = vS!0 in
        let v2:Variable = vS!1 in
        let v3:Variable = vS!2 in
        if v1 ~= v2
        && v2 ~= v3
        && v3 ~= v1
        && tS = seq3 (t, t, t)
        && e = (q @ PAIR (VAR v1) (VAR v2)
                &&&
                q @ PAIR (VAR v2) (VAR v3)
                ==>
                q @ PAIR (VAR v1) (VAR v3)) then
        OK ()
        else FAIL
        else FAIL
      | _ -> FAIL

  op checkTheoremEquation : Proof -> MayFail (Context * Expression * Expression)
  def checkTheoremEquation prf =
    case checkTheorem prf of
      | OK (cx, binary (equation, e1, e2)) -> OK (cx, e1, e2)
      | _ -> FAIL

  op checkTheoremEquationGiven :
     Context -> Expression -> Expression -> Proof -> MayFail ()
  def checkTheoremEquationGiven cx e1 e2 prf =
    case checkTheorem prf of
      | OK (cx1, e) ->
        if cx1 = cx && e = (e1 == e2) then OK () else FAIL
      | _ -> FAIL

  op checkTheoremCongruence :
     Context -> Expression -> Expression -> Proof -> MayFail ()
  def checkTheoremCongruence cx e q prf =
    case checkTheorem prf of
      | OK (cx1, binding (universal, vS, tS, e0)) ->
        if cx1 = cx
        && length vS = 2 then
        let v1:Variable = vS!0 in
        let v2:Variable = vS!1 in
        if v1 ~= v2
        && ~(v1 in? exprFreeVars e)
        && ~(v2 in? exprFreeVars e)
        && e0 = (q @ PAIR (VAR v1) (VAR v2) ==> e @ VAR v1 == e @ VAR v2) then
        OK ()
        else FAIL
        else FAIL
      | _ -> FAIL

  op checkTypeEquivalence : Proof -> MayFail (Context * Type * Type)
  def checkTypeEquivalence prf =
    case check prf of
      | OK (typeEquivalence (cx, t1, t2)) -> OK (cx, t1, t2)
      | _ -> FAIL

  op checkTypeEquivalenceWithContext : Context -> Proof -> MayFail (Type * Type)
  def checkTypeEquivalenceWithContext cx prf =
    case check prf of
      | OK (typeEquivalence (cx1, t1, t2)) ->
        if cx1 = cx then OK (t1, t2) else FAIL
      | _ -> FAIL
(*
  op checkCaseBranchExprs :
     Context -> Expression -> Patterns -> Proofs -> MayFail Expressions
  def checkCaseBranchExprs cx e pS prfS =
    ...
*)

  def check = fn

    %%%%%%%%%% well-formed contexts:
    | cxEmpty ->
      OK (wellFormedContext empty)
    | cxTypeDecl (prf, tn, n) ->
      (case checkContext prf of OK cx ->
      if ~(tn in? contextTypes cx) then
      OK (wellFormedContext (cx <| typeDeclaration (tn, n)))
      else   FAIL
      | _ -> FAIL)
    | cxOpDecl (prfCx, prfTy, o) ->
      (case checkContext prfCx of OK cx ->
      if ~(o in? contextOps cx) then
      (case checkType prfTy of OK (cx1, t) ->
      (case checkExtraTypeVars cx cx1 of OK tvS ->
      OK (wellFormedContext (cx <| opDeclaration (o, tvS, t)))
      | _ -> FAIL)
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | cxTypeDef (prfCx, prfTy, tn) ->
      (case checkContext prfCx of OK cx ->
      (case checkTypeDecl cx tn of OK n ->
      if ~(contextDefinesType? (cx, tn)) then
      (case checkType prfTy of OK (cx1, t) ->
      (case checkExtraTypeVars cx cx1 of OK tvS ->
      if length tvS = n then
      OK (wellFormedContext (cx <| typeDefinition (tn, tvS, t)))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | cxOpDef (prfCx, prfTh, o) ->
      (case checkContext prfCx of OK cx ->
      (case checkOpDecl cx o of OK (tvS, t) ->
      if ~(contextDefinesOp? (cx, o)) then
      (case checkTheoremOpDef prfTh of OK (cx1, v, t1, e) ->
      (case checkExtraTypeVars cx cx1 of OK tvS1 ->
      (case checkTypeSubstitution tvS (map (TVAR, tvS1)) of OK tsbs ->
      if t1 = typeSubstInType tsbs t
      && ~(o in? exprOps e) then
      let esbs:ExprSubstitution = FMap.singleton (v, OPP o (map (TVAR, tvS1))) in
      OK (wellFormedContext (cx <| opDefinition (o, tvS1, exprSubst esbs e)))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | cxAxiom (prfCx, prfEx, an) ->
      (case checkContext prfCx of OK cx ->
      if ~(an in? contextAxioms cx) then
      (case checkExpr prfEx of OK (cx1, e, boolean) ->
      (case checkExtraTypeVars cx cx1 of OK tvS ->
      OK (wellFormedContext (cx <| axioM (an, tvS, e)))
      | _ -> FAIL)
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | cxTypeVarDecl (prf, tv) ->
      (case checkContext prf of OK cx ->
      if ~(tv in? contextTypeVars cx) then
      OK (wellFormedContext (cx <| typeVarDeclaration tv))
      else   FAIL
      | _ -> FAIL)
    | cxVarDecl (prfCx, prfTy, v) ->
      (case checkContext prfCx of OK cx ->
      if ~(v in? contextVars cx) then
      (case checkTypeWithContext cx prfTy of OK t ->
      OK (wellFormedContext (cx <| varDeclaration (v, t)))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)

    %%%%%%%%%% well-formed specs:
    | speC prf ->
      (case checkContext prf of OK cx ->
      if contextTypeVars cx = empty
      && contextVars cx = empty then
      OK (wellFormedSpec cx)
      else   FAIL
      | _ -> FAIL)

    %%%%%%%%%% well-formed types:
    | tyBoolean prf ->
      (case checkContext prf of OK cx ->
      OK (wellFormedType (cx, BOOL))
      | _ -> FAIL)
    | tyVariable (prf, tv) ->
      (case checkContext prf of OK cx ->
      if tv in? contextTypeVars cx then
      OK (wellFormedType (cx, TVAR tv))
      else   FAIL
      | _ -> FAIL)
    | tyArrow (prf1, prf2) ->
      (case checkType prf1 of OK (cx, t1) ->
      (case checkTypeWithContext cx prf2 of OK t2 ->
      OK (wellFormedType (cx, t1 --> t2))
      | _ -> FAIL)
      | _ -> FAIL)
    | tySum (prfCx, prfTy?S, cS) ->
      (case checkContext prfCx of OK cx ->
      if length prfTy?S = length cS
      && noRepetitions? cS
      && length cS > 0 then
      (case checkType?sWithContext cx prfTy?S of OK t?S ->
      OK (wellFormedType (cx, SUM cS t?S))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | tyInstance (prfCx, prfTyS, tn) ->
      (case checkContext prfCx of OK cx ->
      (case checkTypeDecl cx tn of OK n ->
      if length prfTyS = n then
      (case checkTypesWithContext cx prfTyS of OK tS ->
      OK (wellFormedType (cx, TYPE tn tS))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | tyRecord (prfCx, prfTyS, fS) ->
      (case checkContext prfCx of OK cx ->
      if length prfTyS = length fS
      && noRepetitions? fS then
      (case checkTypesWithContext cx prfTyS of OK tS ->
      OK (wellFormedType (cx, TRECORD fS tS))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | tyProduct (prfCx, prfTyS) ->
      (case checkContext prfCx of OK cx ->
      (case checkTypesWithContext cx prfTyS of OK tS ->
      OK (wellFormedType (cx, PRODUCT tS))
      | _ -> FAIL)
      | _ -> FAIL)
    | tySub prf ->
      (case checkExpr prf of OK (cx, r, arrow (t, boolean)) ->
      if exprFreeVars r = empty then
      OK (wellFormedType (cx, t \ r))
      else   FAIL
      | _ -> FAIL)
    | tyQuot (prfRefl, prfSymm, prfTrans) ->
      (case checkTheoremReflexivity prfRefl of OK (cx, v, t, q) ->
      (case checkTheoremSymmetry cx t q prfSymm of OK () ->
      (case checkTheoremTransitivity cx t q prfTrans of OK () ->
      OK (wellFormedType (cx, t / q))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)

    %%%%%%%%%% type equivalence:
    | tyEqDef (prfCx, prfTyS, tn) ->
      (case checkContext prfCx of OK cx ->
      (case checkTypeDef cx tn of OK (tvS, t) ->
      (case checkTypesWithContext cx prfTyS of OK tS ->
      (case checkTypeSubstitution tvS tS of OK tsbs ->
      OK (typeEquivalence (cx, TYPE tn tS, typeSubstInType tsbs t))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | tyEqReflexive prf ->
      (case checkType prf of OK (cx, t) ->
      OK (typeEquivalence (cx, t, t))
      | _ -> FAIL)
    | tyEqSymmetric prf ->
      (case checkTypeEquivalence prf of OK (cx, t1, t2) ->
      OK (typeEquivalence (cx, t2, t1))
      | _ -> FAIL)
    | tyEqTransitive (prf1, prf2) ->
      (case checkTypeEquivalence prf1 of OK (cx, t1, t2) ->
      (case checkTypeEquivalenceWithContext cx prf2 of OK (t, t3) ->
      if t = t2 then
      OK (typeEquivalence (cx, t1, t3))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | tyEqSubstitution (prfTy, prfTyEq, pos) ->
      (case checkType prfTy of OK (cx, t) ->
      (case checkTypeEquivalenceWithContext cx prfTyEq of OK (t1, t2) ->
      (case typeSubstInTypeAt (t, t1, t2, pos) of OK newT ->
      OK (typeEquivalence (cx, t, newT))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | tyEqSumOrder (prf, natS) ->
      (case checkSumType prf of OK (cx, cS, t?S) ->
      (case checkPermutation natS of OK prm ->
      OK (typeEquivalence
            (cx, SUM cS t?S, SUM (permute(cS,prm)) (permute(t?S,prm))))
      | _ -> FAIL)
      | _ -> FAIL)
    | tyEqRecordOrder (prf, natS) ->
      (case checkRecordType prf of OK (cx, fS, tS) ->
      (case checkPermutation natS of OK prm ->
      OK (typeEquivalence
            (cx, TRECORD fS tS, TRECORD (permute(fS,prm)) (permute(tS,prm))))
      | _ -> FAIL)
      | _ -> FAIL)
    | tyEqProductOrder (prf, natS) ->
      (case checkProductType prf of OK (cx, tS) ->
      (case checkPermutation natS of OK prm ->
      OK (typeEquivalence (cx, PRODUCT tS, PRODUCT (permute(tS,prm))))
      | _ -> FAIL)
      | _ -> FAIL)
    | tyEqSubPredicate (prfTy1, prfTy2, prfEq) ->
      (case checkSubType prfTy1 of OK (cx, t, r1) ->
      (case checkSubType2 cx t prfTy2 of OK r2 ->
      (case checkTheoremEquationGiven cx r1 r2 prfEq of OK () ->
      OK (typeEquivalence (cx, t \ r1, t \ r2))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | tyEqQuotientPredicate (prfTy1, prfTy2, prfEq) ->
      (case checkQuotientType prfTy1 of OK (cx, t, q1) ->
      (case checkQuotientType2 cx t prfTy2 of OK q2 ->
      (case checkTheoremEquationGiven cx q1 q2 prfEq of OK () ->
      OK (typeEquivalence (cx, t / q1, t / q2))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)

    % well-typed expressions:
    | exVariable (prf, v) ->
      (case checkContext prf of OK cx ->
      (case checkVarDecl cx v of OK t ->
      OK (wellTypedExpr (cx, VAR v, t))
      | _ -> FAIL)
      | _ -> FAIL)
    | exTrue prf ->
      (case checkContext prf of OK cx ->
      OK (wellTypedExpr (cx, TRUE, BOOL))
      | _ -> FAIL)
    | exFalse prf ->
      (case checkContext prf of OK cx ->
      OK (wellTypedExpr (cx, FALSE, BOOL))
      | _ -> FAIL)
    | exRecordProjection (prf, f) ->
      (case checkExpr prf of OK (cx, e, t) ->
      (case checkFieldType t f of OK ti ->
      OK (wellTypedExpr (cx, e DOTr f, ti))
      | _ -> FAIL)
      | _ -> FAIL)
    | exTupleProjection (prf, i) ->
      (case checkExpr prf of OK (cx, e, nary (product, tS)) ->
      if i <= length tS then
      OK (wellTypedExpr (cx, e DOTt i, tS!(i-1)))
      else   FAIL
      | _ -> FAIL)
    | exRelaxator prf ->
      (case checkSubType prf of OK (cx, t, r) ->
      OK (wellTypedExpr (cx, RELAX r, t\r --> t))
      | _ -> FAIL)
    | exQuotienter prf ->
      (case checkQuotientType prf of OK (cx, t, q) ->
      OK (wellTypedExpr (cx, QUOTIENT q, t --> t/q))
      | _ -> FAIL)
    | exNegation prf ->
      (case checkExpr prf of OK (cx, e, boolean) ->
      OK (wellTypedExpr (cx, ~~ e, BOOL))
      | _ -> FAIL)
    | exApplication (prf1, prf2) ->
      (case checkExpr prf1 of OK (cx, e1, arrow (t1, t2)) ->
      (case checkExprWithContext cx prf2 of OK (e2, t3) ->
      if t3 = t1 then
      OK (wellTypedExpr (cx, e1 @ e2, t2))
      else FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | exEquation (prf1, prf2) ->
      (case checkExpr prf1 of OK (cx, e1, t) ->
      (case checkExprWithContextAndType cx t prf2 of OK e2 ->
      OK (wellTypedExpr (cx, e1 == e2, BOOL))
      | _ -> FAIL)
      | _ -> FAIL)
    | exInequation (prf1, prf2) ->
      (case checkTheoremEquation prf1 of OK (cx, e1, e2) ->
      OK (wellTypedExpr (cx, e1 ~== e2, BOOL))
      | _ -> FAIL)
    | exRecordUpdate (prf1, prf2) ->
      (case checkExpr prf1 of OK (cx, e1, t1) ->
      (case checkExprWithContext cx prf2 of OK (e2, t2) ->
      (case checkRecordTypeUnion t1 t2 of OK t ->
      OK (wellTypedExpr (cx, e1 <<< e2, t))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | exRestriction (prfTy, prfEx, prfTh) ->
      (case checkSubType prfTy of OK (cx, t, r) ->
      (case checkExprWithContext cx prfEx of OK (e, t1) ->
      if t1 = t then
      (case checkTheoremGiven cx (r @ e) prfTh of OK () ->
      OK (wellTypedExpr (cx, RESTRICT r e, t \ r))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | exChoice (prfTy, prfEx, prfTh) ->
      (case checkQuotientType prfTy of OK (cx, t, q) ->
      (case checkExprWithContext cx prfEx of OK (e, arrow (t0, t1)) ->
      if t0 = t then
      (case checkTheoremCongruence cx e q prfTh of OK () ->
      OK (wellTypedExpr (cx, CHOOSE q e, t/q --> t1))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | exConjunction prf ->
      (case checkExpr prf of
         OK (cx, ifThenElse (e1, e2, nullary falsE), boolean) ->
      OK (wellTypedExpr (cx, e1 &&& e2, BOOL))
      | _ -> FAIL)
    | exDisjunction prf ->
      (case checkExpr prf of
         OK (cx, ifThenElse (e1, nullary truE, e2), boolean) ->
      OK (wellTypedExpr (cx, e1 ||| e2, BOOL))
      | _ -> FAIL)
    | exImplication prf ->
      (case checkExpr prf of
         OK (cx, ifThenElse (e1, e2, nullary truE), boolean) ->
      OK (wellTypedExpr (cx, e1 ==> e2, BOOL))
      | _ -> FAIL)
    | exEquivalence (prf1, prf2) ->
      (case checkExpr prf1 of OK (cx, e1, boolean) ->
      (case checkExprWithContext cx prf2 of OK (e2, boolean) ->
      OK (wellTypedExpr (cx, e1 <==> e2, BOOL))
      | _ -> FAIL)
      | _ -> FAIL)
    | exRecord (prf, prfS) ->
      (case checkRecordType prf of OK (cx, fS, tS) ->
      (case checkExprsWithContextAndTypes cx tS prfS of OK eS ->
      OK (wellTypedExpr (cx, RECORD fS eS, TRECORD fS tS))
      | _ -> FAIL)
      | _ -> FAIL)
    | exTuple (prf, prfS) ->
      (case checkProductType prf of OK (cx, tS) ->
      (case checkExprsWithContextAndTypes cx tS prfS of OK eS ->
      OK (wellTypedExpr (cx, TUPLE eS, PRODUCT tS))
      | _ -> FAIL)
      | _ -> FAIL)
    | exAbstraction (prf, nVars) ->
      (case checkExpr prf of OK (cx, e, t) ->
      (case checkLastNVars cx nVars of OK (cx0, vS, tS) ->
      OK (wellTypedExpr (cx0, FNN vS tS e, PRODUCT tS --> t))
      | _ -> FAIL)
      | _ -> FAIL)
    | exUniversal (prf, nVars) ->
      (case checkExpr prf of OK (cx, e, t) ->
      (case checkLastNVars cx nVars of OK (cx0, vS, tS) ->
      OK (wellTypedExpr (cx0, FAA vS tS e, PRODUCT tS --> t))
      | _ -> FAIL)
      | _ -> FAIL)
    | exExistential (prf, nVars) ->
      (case checkExpr prf of OK (cx, e, t) ->
      (case checkLastNVars cx nVars of OK (cx0, vS, tS) ->
      OK (wellTypedExpr (cx0, EXX vS tS e, PRODUCT tS --> t))
      | _ -> FAIL)
      | _ -> FAIL)
    | exExistential1 (prf, nVars) ->
      (case checkExpr prf of OK (cx, e, t) ->
      (case checkLastNVars cx nVars of OK (cx0, vS, tS) ->
      OK (wellTypedExpr (cx0, EXX1 vS tS e, PRODUCT tS --> t))
      | _ -> FAIL)
      | _ -> FAIL)
    | exIfThenElse (prf0, prf1, prf2) ->
      (case checkExpr prf0 of OK (cx, e0, boolean) ->
      (case checkExpr prf1 of OK (cx1, e1, t) ->
      (case checkExtraAxiom cx cx1 of OK (an1, tvS1, ea1) ->
      if tvS1 = empty
      && ea1 = e0 then
      (case checkExpr prf2 of OK (cx2, e2, t2) ->
      if t2 = t then
      (case checkExtraAxiom cx cx2 of OK (an2, tvS2, ea2) ->
      if tvS2 = empty
      && ea2 = ~~ e0 then
      OK (wellTypedExpr (cx, IF e0 e1 e2, t))
      else   FAIL
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | exOpInstance (prfCx, prfTyS, o) ->
      (case checkContext prfCx of OK cx ->
      (case checkOpDecl cx o of OK (tvS, t) ->
      (case checkTypesWithContext cx prfTyS of OK tS ->
      (case checkTypeSubstitution tvS tS of OK tsbs ->
      OK (wellTypedExpr (cx, OPP o tS, typeSubstInType tsbs t))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | exEmbedder0 (prf, c) ->
      (case checkSumType prf of OK (cx, cS, t?S) ->
      (case checkConstructorType? (SUM cS t?S) c of OK None ->
      OK (wellTypedExpr (cx, EMBED (SUM cS t?S) c, SUM cS t?S))
      | _ -> FAIL)
      | _ -> FAIL)
    | exEmbedder1 (prf, c) ->
      (case checkSumType prf of OK (cx, cS, t?S) ->
      (case checkConstructorType? (SUM cS t?S) c of OK (Some ti) ->
      OK (wellTypedExpr (cx, EMBED (SUM cS t?S) c, ti --> SUM cS t?S))
      | _ -> FAIL)
      | _ -> FAIL)

(*@@@
    | exCase (prfTgt, prfPS, prfExh, prfES) ->
      (case checkExpr prfTgt of OK (cx, e, t) ->
      (case checkSequence (map (checkPattWithContextAndType cx t, prfPS)) of
         OK pS ->
      let n:Nat = length pS in
      let caseMatches:Expressions =
        seqSuchThat (fn(i:Nat) ->
          if i < n then Some (let (vS,tS) = pattVarsWithTypes (pS!i) in
                              EXX vS tS (pattAssumptions (pS!i, e)))
          else None) in
      (case checkTheoremGiven cx (disjoinAll caseMatches) of OK () ->

DEFINING checkCaseBranchExprs...

         pj (wellTypedExpr (cx, e, t))
      && length pS = n
      && (fa(i:Nat) i < n =>
            pj (wellTypedPatt (cx, pS!i, t)))
      && length caseMatches = n
      && (fa(i:Nat) i < n =>
            caseMatches!i =
            (let (vS,tS) = pattVarsWithTypes (pS!i) in
             EXX vS tS (pattAssumptions (pS!i, e))))
      && pj (theoreM (cx, disjoinAll caseMatches))
      && length posCxS = n
      && length posAnS = n
      && (fa(i:Nat) i < n =>
            posCxS!i =
            multiVarDecls (pattVarsWithTypes (pS!i))
              <| axioM (posAnS!i, empty, pattAssumptions (pS!i, e)))
      && length negCxS = n
      && length negAnS = n
      && (fa(i:Nat) i < n =>
            (let conjuncts:Expressions = the (fn conjuncts ->
                   length conjuncts = i &&
                   (fa(j:Nat) j < i => conjuncts!j = ~~ (caseMatches!j))) in
             negCxS!i =
             singleton (axioM (negAnS!i, empty, conjoinAll conjuncts))))
      && length eS = n
      && (fa(i:Nat) i < n =>
            pj (wellTypedExpr (cx ++ (negCxS!i) ++ (posCxS!i), eS!i, t1)))
      => pj (wellTypedExpr (cx, CASE e pS eS, t1)))

    | exRecursiveLet         Proof * Proof
    | exNonRecursiveLet      Proof
    | exEquivalentTypes      Proof * Proof
    | exAlphaAbstraction     Proof * Variable * Variable
    | exAlphaCase            Proof * Nat * Variable * Variable
    | exAlphaRecursiveLet    Proof * Variable * Variable
    % well-typed patterns:
    | paVariable        Proof * Variable
    | paEmbedding0      Proof * Constructor
    | paEmbedding1      Proof * Proof * Constructor
    | paRecord          Proof * Proofs
    | paTuple           Proof * Proofs
    | paAlias           Proof * Variable
    | paEquivalentTypes Proof * Proof
    % theorems:
    | thAxiom                       Proof * Proofs * TypeVariables * AxiomName
    | thOpDef                       Proof * Proofs * Operation
    | thSubstitution                Proof * Proof * Position
    | thTypeSubstitution            Proof * Proof * Position
    | thBoolean                     Proof * Variable
    | thCongruence                  Proof * Proof * Proof
    | thExtensionality              Proof * Proof * Variable
    | thAbstraction                 Proof
    | thIfThenElse                  Proof * Proof * Proof
    | thRecord                      Proof * Variable * Variables
    | thTuple                       Proof * Variable * Variables
    | thRecordProjection            Proof * Field
    | thTupleProjection             Proof * PosNat
    | thRecordUpdate1               Proof * Proof * Field
    | thRecordUpdate2               Proof * Proof * Field
    | thEmbedderSurjective          Proof * Constructor * Variable * Variable
    | thEmbeddersDistinct           Proof * Constructor * Constructor
                                          * Variable? * Variable?
    | thEmbedderInjective           Proof * Constructor * Variable * Variable
    | thRelaxatorSatisfiesPredicate Proof * Variable
    | thRelaxatorInjective          Proof * Variable * Variable
    | thRelexatorSurjective         Proof * Variable * Variable
    | thRestriction                 Proof * Variable
    | thQuotienterSurjective        Proof * Variable * Variable
    | thQuotienterEquivClass        Proof * Variable * Variable
    | thChoice                      Proof * Variable
    | thCase                        Proof * Proofs
    | thRecursiveLet                Proof * Proof
    | thAbbrevTrue                  Proof * Variable
    | thAbbrevFalse                 Proof * Variable
    | thAbbrevNegation              Proof
    | thAbbrevInequation            Proof
    | thAbbrevConjunction           Proof
    | thAbbrevDisjunction           Proof
    | thAbbrevImplication           Proof
    | thAbbrevEquivalence           Proof
    | thAbbrevUniversal             Proof
    | thAbbrevExistential           Proof
    | thAbbrevExistential1          Proof * Variables
    | thAbbrevNonRecursiveLet       Proof
*)

endspec
