spec

  (* This spec defines the recursive function described in spec `Proofs' (see
  that spec for an explanation). The function is called `check', because it
  checks whether a proof is valid, and if it is valid, it returns the
  judgement proved by the proof. Failure is modeled via the meta type
  `MayFail' defined in spec `Failures'. In the explanatory comments in this
  file we often call "results" the values of type `MayFail', because those
  values are generally the result of some other operation (e.g. checking a
  proof and obtaining a judgement, or a failure, as result).

  Checking proof steps involves several checks, some by pattern matching (via
  `case') and some by testing conditions (via `if'). If a check fails, `FAIL'
  is returned. Since there can be several such checks one after the other,
  the definitions below do not always follow the usual Metaslang indentation
  style, because after not many checks we would get too far on the right.
  Rather, all the subsequent checks are left-aligned. After all checks have
  succeeded and an `OK' result is returned, we deal with all the check
  failures, either as `_ -> FAIL' for a failed pattern matching or as `else
  FAIL' for a failed condition test, also all left-aligned. This indentation
  style should be clear when looking at the definitions below.

  The quite verbose handling of failures in the definitions below could be
  probably made more succint and readable using a monadic approach with
  specialized syntax.

  The definitions in this spec are executable. However, they could be made
  more abstract and non-executable. *)


  import Proofs, Failures, SyntaxWithCoreOps


  (* Given a sequence of results, return them (without individual `OK'
  wrappers) if they are all successful, otherwise return failure. E.g.:
    checkSequence [OK x, OK y] = OK [x,y]
    checkSequence [OK x, FAIL] = FAIL
  (where we use the pseudo-notation `[...]' for sequences). *)

  op checkSequence : [a] FSeq (MayFail a) -> MayFail (FSeq a)
  def [a] checkSequence s =
    let def aux (input  : FSeq (MayFail a),
                 output : FSeq a)  % accumulator
               : MayFail (FSeq a) =
          if input = empty then OK output
          else case first input of
                 | OK outputElement ->
                   aux (rtail input, output <| outputElement)
                 | FAIL -> FAIL
    in
    aux (s, empty)


  (* Similar to the previous op, but here results are optional (modeled via
  `Option'); `None' values are considered successeful. E.g.:
     checkSequence [Some(OK x), Some(OK y), None] = OK [Some x, Some y, None]
     checkSequence [Some(OK x), Some FAIL, None] = FAIL
  *)

  op checkOptionSequence : [a] FSeq (Option (MayFail a)) ->
                               MayFail (FSeq (Option a))
  def [a] checkOptionSequence s =
    let def aux (input  : FSeq (Option (MayFail a)),
                 output : FSeq (Option a))  % accumulator
               : MayFail (FSeq (Option a)) =
          if input = empty then OK output
          else case first input of
                 | Some (OK outputElement) ->
                   aux (rtail input, output <| Some outputElement)
                 | Some FAIL -> FAIL
                 | None -> aux (rtail input, output <| None)
    in
    aux (s, empty)


  (* Check whether a finite sequence of natural numbers is a permutation
  (see spec `FiniteSequences' in the library. If it is, return it as a
  permutation, i.e. as a value of type `FSeq.Permutation' (there is an
  implicit `restrict'). *)

  op checkPermutation : FSeq Nat -> MayFail Permutation
  def checkPermutation nS =
    if permutation? nS then OK nS
    else FAIL


  (* ... *)

  op checkAllTypeVarDecls : Context -> MayFail TypeVariables
  def checkAllTypeVarDecls cx =
    let def aux (cx  : Context,
                 tvS : TypeVariables)  % accumulator
                : MayFail TypeVariables =
          if cx = empty then OK tvS
          else case first cx of
                 | typeVarDeclaration tv -> aux (rtail cx, tvS <| tv)
                 | _ -> FAIL
    in
    aux (cx, empty)



  (* Check whether `cx2 = cx1 ++ multiTypeVarDecls tvS' for some `tvS' (i.e.
  `cx2' is `cx1' with some extra type variables; if so, return `tvS'. *)

  op checkExtraTypeVars : Context -> Context -> MayFail TypeVariables
  def checkExtraTypeVars cx1 cx2 =
    if length cx1 <= length cx2
    && firstN (cx2, length cx1) = cx1 then
    let cxExtra = lastN (cx2, length cx2 - length cx1) in
    let def collectTypeVars (cx  : Context,
                             tvS : TypeVariables)  % accumulator
                            : MayFail TypeVariables =
          if cx = empty then OK tvS
          else case first cx of
                 | typeVarDeclaration tv ->
                   collectTypeVars (rtail cx, tvS <| tv)
                 | _ -> FAIL
    in
    collectTypeVars (cxExtra, empty)
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

  op checkOpDef : Context -> Operation -> MayFail (TypeVariables * Expression)
  def checkOpDef cx o =
    if cx = empty then FAIL
    else case first cx of
           | opDefinition(o1,tvS,e) ->
             if o1 = o then OK (tvS, e)
             else checkOpDef (rtail cx) o
           | _ -> checkOpDef (rtail cx) o

  op checkAxiom : Context -> AxiomName -> MayFail (TypeVariables * Expression)
  def checkAxiom cx an =
    if cx = empty then FAIL
    else case first cx of
           | axioM(an1,tvS,e) ->
             if an1 = an then OK (tvS, e)
             else checkAxiom (rtail cx) an
           | _ -> checkAxiom (rtail cx) an

  op checkTypeSubstitution : TypeVariables -> Types -> MayFail TypeSubstitution
  def checkTypeSubstitution tvS tS =
    if noRepetitions? tvS && length tvS = length tS
    then OK (FMap.fromSequences (tvS, tS))
    else FAIL

  op checkExprSubstitution : Variables -> Expressions -> MayFail ExprSubstitution
  def checkExprSubstitution vS eS =
    if noRepetitions? vS && length vS = length eS
    then OK (FMap.fromSequences (vS, eS))
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

  op exprSubstAt :
     Expression * Expression * Expression * Position -> MayFail Expression
  def exprSubstAt(e,old,new,pos) =
    if pos = empty then
      if old = e then OK new
      else FAIL
    else
      let i   = first pos in
      let pos = rtail pos in
      case e of
        | unary(eo,e) ->
          if i = 0 then
            case exprSubstAt (e, old, new, pos) of
              | OK newE -> OK (unary (eo, newE))
              | FAIL    -> FAIL
          else FAIL
        | binary(eo,e1,e2) ->
          if i = 1 then
            case exprSubstAt (e1, old, new, pos) of
              | OK newE1 -> OK (binary (eo, newE1, e2))
              | FAIL     -> FAIL
          else if i = 2 then
            case exprSubstAt (e2, old, new, pos) of
              | OK newE2 -> OK (binary (eo, e1, newE2))
              | FAIL     -> FAIL
          else FAIL
        | ifThenElse(e0,e1,e2) ->
          if i = 0 then
            case exprSubstAt (e0, old, new, pos) of
              | OK newE0 -> OK (ifThenElse (newE0, e1, e2))
              | FAIL     -> FAIL
          else if i = 1 then
            case exprSubstAt (e1, old, new, pos) of
              | OK newE1 -> OK (ifThenElse (e0, newE1, e2))
              | FAIL     -> FAIL
          else if i = 2 then
            case exprSubstAt (e2, old, new, pos) of
              | OK newE2 -> OK (ifThenElse (e0, e1, newE2))
              | FAIL     -> FAIL
          else FAIL
        | nary(eo,eS) ->
          if i < length eS then
            case exprSubstAt (eS!i, old, new, pos) of
              | OK newEi -> OK (nary (eo, update (eS, i, newEi)))
              | FAIL     -> FAIL
          else FAIL
        | binding(eo,vS,tS,e) ->
          if i = 0 then
            case exprSubstAt (e, old, new, pos) of
              | OK newE -> OK (binding (eo, vS, tS, newE))
              | FAIL    -> FAIL
          else FAIL
        | casE(e,pS,eS) ->
          if i = 0 then
            case exprSubstAt (e, old, new, pos) of
              | OK newE -> OK (casE (newE, pS, eS))
              | FAIL    -> FAIL
          else if i <= length eS then
            case exprSubstAt (eS!(i-1), old, new, pos) of
                | OK newEi -> OK (casE (e, pS, update (eS, i, newEi)))
                | FAIL     -> FAIL
          else FAIL
        | recursiveLet(vS,tS,eS,e) ->
          if i = 0 then
            case exprSubstAt (e, old, new, pos) of
              | OK newE -> OK (recursiveLet (vS, tS, eS, newE))
              | FAIL    -> FAIL
          else if i <= length eS then
            case exprSubstAt (eS!i, old, new, pos) of
              | OK newEi -> OK (recursiveLet (vS, tS, update (eS, i, newEi), e))
              | FAIL     -> FAIL
          else FAIL
        | nonRecursiveLet(p,e,e1) ->
          if i = 0 then
            case exprSubstAt (e, old, new, pos) of
              | OK newE -> OK (nonRecursiveLet (p, newE, e1))
              | FAIL    -> FAIL
          else if i = 1 then
            case exprSubstAt (e1, old, new, pos) of
              | OK newE1 -> OK (nonRecursiveLet (p, e, newE1))
              | FAIL     -> FAIL
          else FAIL
        | _ -> FAIL


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

  op checkCaseBranchExpr :
     Context -> Context -> Expression -> Expression -> Proof ->
     MayFail (Expression * Type)
  def checkCaseBranchExpr cx varCx negAsm posAsm prf =
    case checkExpr prf of OK (cx1, e, t) ->
    if maxCommonPrefix (cx, cx1) = cx
    && length cx1 = length cx + length varCx + 2 then
    case last cx1 of axioM (_, tvS, e1) ->
    if tvS = empty
    && e1 = posAsm
    && subFromLong (cx1, length cx + 1, length varCx) = varCx then
    case cx1 ! (length cx) of axioM (_, tvS, e1) ->
    if tvS = empty
    && e1 = negAsm then
    OK (e, t)
    else   FAIL
    | _ -> FAIL
    else   FAIL
    | _ -> FAIL
    else   FAIL
    | _ -> FAIL

  op checkCaseBranchTheorem :
     Context -> Context -> Expression -> Expression -> Expression -> Proof ->
     MayFail Expression
  def checkCaseBranchTheorem cx varCx negAsm posAsm e prf =
    case checkTheoremEquation prf of OK (cx1, mustBeE, e0) ->
    if mustBeE = e
    && maxCommonPrefix (cx, cx1) = cx
    && length cx1 = length cx + length varCx + 2 then
    case last cx1 of axioM (_, tvS, e1) ->
    if tvS = empty
    && e1 = posAsm
    && subFromLong (cx1, length cx + 1, length varCx) = varCx then
    case cx1 ! (length cx) of axioM (_, tvS, e1) ->
    if tvS = empty
    && e1 = negAsm then
    OK e0
    else   FAIL
    | _ -> FAIL
    else   FAIL
    | _ -> FAIL
    else   FAIL
    | _ -> FAIL

  op checkPatt : Proof -> MayFail (Context * Pattern * Type)
  def checkPatt prf =
    case check prf of
      | OK (wellTypedPatt (cx, p, t)) -> OK (cx, p, t)
      | _ -> FAIL

  op checkPattWithContext : Context -> Proof -> MayFail (Pattern * Type)
  def checkPattWithContext cx prf =
    case check prf of
      | OK (wellTypedPatt (cx1, p, t)) ->
        if cx1 = cx then OK (p, t) else FAIL
      | _ -> FAIL

  op checkPattWithContextAndType : Context -> Type -> Proof -> MayFail Pattern
  def checkPattWithContextAndType cx t prf =
    case check prf of
      | OK (wellTypedPatt (cx1, p, t1)) ->
        if cx1 = cx && t1 = t then OK p else FAIL
      | _ -> FAIL

  op checkPattsWithContextAndTypes :
     Context -> Types -> Proofs -> MayFail Patterns
  def checkPattsWithContextAndTypes cx tS prfS =
    case checkSequence (map (checkPattWithContext cx, prfS)) of
      | OK paTyS ->
        let (pS, tS1) = unzip paTyS in
        if tS1 = tS then OK pS else FAIL
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

  op checkTheoremRecursiveLet :
     Proof -> MayFail (Context * Variables * Types * Expressions)
  def checkTheoremRecursiveLet prf =
    case check prf of
      | OK (theoreM (cx, binding (existential1, vS, tS,
                                  binary (equation,
                                    nary (tuple, veS), nary (tuple, eS))))) ->
        if veS = map (VAR, vS) then OK (cx, vS, tS, eS) else FAIL
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

    %%%%%%%%%% well-typed expressions:
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
    | exCase (prfTgt, prfPS, prfExh, prfES) ->
      (case checkExpr prfTgt of OK (cx, e, t) ->
      (case checkSequence (map (checkPattWithContextAndType cx t, prfPS)) of
         OK pS ->
      let n:Nat = length pS in
      if n > 0 then
      let caseMatches:Expressions = seqSuchThat (fn(i:Nat) ->
        if i < n then Some (let (vS,tS) = pattVarsWithTypes (pS!i) in
                            EXX vS tS (pattAssumptions (pS!i, e)))
        else None) in
      (case checkTheoremGiven cx (disjoinAll caseMatches) prfExh of OK () ->
      let varCxS:FSeq Context = seqSuchThat (fn(i:Nat) ->
        if i < n then Some (multiVarDecls (pattVarsWithTypes (pS!i)))
        else None) in
      let negAsmS:Expressions = seqSuchThat (fn(i:Nat) ->
        if i < n then Some (conjoinAll (seqSuchThat (fn(j:Nat) ->
                             if j < i then Some (~~ (caseMatches!j))
                                      else None)))
                 else None) in
      let posAsmS:Expressions = seqSuchThat (fn(i:Nat) ->
        if i < n then Some (pattAssumptions (pS!i, e))
                 else None) in
      if length prfES = n then
      let def aux (i:Nat, eS:Expressions, t?:Type?)
                  : MayFail (Expressions * Type) =
            if i = n then
              case t? of Some t -> OK (eS, t)
                       | None   -> FAIL   % never happens
            else
              case checkCaseBranchExpr
                     cx (varCxS!i) (negAsmS!i) (posAsmS!i) (prfES!i) of
                | OK (e, t) ->
                  (case t? of Some t1 -> if t1 = t then aux (i+1, eS <| e, Some t)
                                         else FAIL
                            | None -> aux (i+1, eS <| e, Some t))
                | _ -> FAIL
      in
      (case aux (0, empty, None) of OK (eS, t1) ->
      OK (wellTypedExpr (cx, CASE e pS eS, t1))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | exRecursiveLet (prfTh, prfEx) ->
      (case checkTheoremRecursiveLet prfTh of OK (cx, vS, tS, eS) ->
      if length vS = length tS
      && length tS = length eS then
      (case checkExpr prfEx of OK (cx1, e, t) ->
      if cx1 = cx ++ multiVarDecls (vS, tS) then
      OK (wellTypedExpr (cx, LETDEF vS tS eS e, t))
      else   FAIL
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | exNonRecursiveLet prf ->
      (case checkExpr prf of OK (cx, casE (e, pS, eS), t) ->
      if length pS = 1
      && length eS = 1 then
      OK (wellTypedExpr (cx, LET (first pS) e (first eS), t))
      else   FAIL
      | _ -> FAIL)
    | exEquivalentTypes (prfEx, prfTE) ->
      (case checkExpr prfEx of OK (cx, e, t) ->
      (case checkTypeEquivalenceWithContext cx prfTE of OK (t0, t1) ->
      if t0 = t then
      OK (wellTypedExpr (cx, e, t1))
      else FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | exAlphaAbstraction (prf, oldV, newV) ->
      (case checkExpr prf of OK (cx, binding (abstraction, vS, tS, e), t) ->
      if noRepetitions? vS
      && oldV in? vS then
      let i:Nat = indexOf (vS, oldV) in
      let esbs:ExprSubstitution = FMap.singleton (oldV, VAR newV) in
      if ~(newV in? toSet vS \/ exprFreeVars e \/ captVars oldV e) then
      OK (wellTypedExpr (cx, FNN (update(vS,i,newV)) tS (exprSubst esbs e), t))
      else   FAIL
      else   FAIL
      | _ -> FAIL)
    | exAlphaCase (prf, i, oldV, newV) ->
      (case checkExpr prf of OK (cx, casE (e, pS, eS), t) ->
      if i < length pS
      && i < length eS
      && oldV in? pattVars (pS!i)
      && ~(oldV in?
           pattVars (pS!i) \/ exprFreeVars (eS!i) \/ captVars oldV (eS!i)) then
      let newPi:Pattern = pattSubst (oldV, newV) (pS!i) in
      let esbs:ExprSubstitution = FMap.singleton (oldV, VAR newV) in
      let newEi:Expression = exprSubst esbs (eS!i) in
      OK (wellTypedExpr
           (cx, CASE e (update(pS,i,newPi)) (update(eS,i,newEi)), t))
      else   FAIL
      | _ -> FAIL)
    | exAlphaRecursiveLet (prf, oldV, newV) ->
      (case checkExpr prf of OK (cx, recursiveLet (vS, tS, eS, e), t) ->
      if noRepetitions? vS
      && oldV in? vS then
      let i:Nat = indexOf (vS, oldV) in
      let esbs:ExprSubstitution = FMap.singleton (oldV, VAR newV) in
      if ~(newV in? toSet vS \/ captVars oldV e \/ exprFreeVars e \/
                    unionAll (map (exprFreeVars, eS)) \/
                    unionAll (map (captVars oldV, eS))) then
      OK (wellTypedExpr
           (cx,
            LETDEF (update(vS,i,newV)) tS
                   (map (exprSubst esbs, eS)) (exprSubst esbs e),
            t))
      else   FAIL
      else   FAIL
      | _ -> FAIL)

    %%%%%%%%%% well-typed patterns:
    | paVariable (prf, v) ->
      (case checkType prf of OK (cx, t) ->
      if ~(v in? contextVars cx) then
      OK (wellTypedPatt (cx, PVAR v t, t))
      else   FAIL
      | _ -> FAIL)
    | paEmbedding0 (prf, c) ->
      (case checkSumType prf of OK (cx, cS, t?S) ->
      (case checkConstructorType? (SUM cS t?S) c of OK None ->
      OK (wellTypedPatt (cx, PEMBE (SUM cS t?S) c, SUM cS t?S))
      | _ -> FAIL)
      | _ -> FAIL)
    | paEmbedding1 (prfTy, prfPa, c) ->
      (case checkSumType prfTy of OK (cx, cS, t?S) ->
      (case checkConstructorType? (SUM cS t?S) c of OK (Some ti) ->
      (case checkPattWithContextAndType cx ti prfPa of OK p ->
      OK (wellTypedPatt (cx, PEMBED (SUM cS t?S) c p, SUM cS t?S))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | paRecord (prf, prfS) ->
      (case checkRecordType prf of OK (cx, fS, tS) ->
      (case checkPattsWithContextAndTypes cx tS prfS of OK pS ->
      OK (wellTypedPatt (cx, PRECORD fS pS, TRECORD fS tS))
      | _ -> FAIL)
      | _ -> FAIL)
    | paTuple (prf, prfS) ->
      (case checkProductType prf of OK (cx, tS) ->
      (case checkPattsWithContextAndTypes cx tS prfS of OK pS ->
      OK (wellTypedPatt (cx, PTUPLE pS, PRODUCT tS))
      | _ -> FAIL)
      | _ -> FAIL)
    | paAlias (prf, v) ->
      (case checkPatt prf of OK (cx, p, t) ->
      if ~(v in? contextVars cx) then
      OK (wellTypedPatt (cx, AS v t p, t))
      else   FAIL
      | _ -> FAIL)
    | paEquivalentTypes (prfPa, prfTE) ->
      (case checkPatt prfPa of OK (cx, p, t) ->
      (case checkTypeEquivalenceWithContext cx prfTE of OK (t0, t1) ->
      if t0 = t then
      OK (wellTypedPatt (cx, p, t1))
      else FAIL
      | _ -> FAIL)
      | _ -> FAIL)

    %%%%%%%%%% theorems:
    | thAxiom (prfCx, prfTyS, tvS, an) ->
      (case checkContext prfCx of OK cx ->
      (case checkAxiom cx an of OK (tvS, e) ->
      (case checkTypesWithContext cx prfTyS of OK tS ->
      (case checkTypeSubstitution tvS tS of OK tsbs ->
      OK (theoreM (cx, typeSubstInExpr tsbs e))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | thOpDef (prfCx, prfTyS, o) ->
      (case checkContext prfCx of OK cx ->
      (case checkOpDef cx o of OK (tvS, e) ->
      (case checkTypesWithContext cx prfTyS of OK tS ->
      (case checkTypeSubstitution tvS tS of OK tsbs ->
      OK (theoreM (cx, OPP o tS == typeSubstInExpr tsbs e))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | thSubstitution (prfTh, prfEq, pos) ->
      (case checkTheorem prfTh of OK (cx, e) ->
      (case checkTheoremEquation prfEq of OK (cx1, e1, e2) ->
      if cx1 = cx then
      (case exprSubstAt (e, e1, e2, pos) of OK newE ->
      OK (theoreM (cx, newE))
      | _ -> FAIL)
      else FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | thTypeSubstitution (prfTh, prfTE, pos) ->
      (case checkTheorem prfTh of OK (cx, e) ->
      (case checkTypeEquivalenceWithContext cx prfTE of OK (t1, t2) ->
      (case typeSubstInExprAt (e, t1, t2, pos) of OK newE ->
      OK (theoreM (cx, newE))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | thBoolean (prf, v) ->
      (case checkExpr prf of OK (cx, e, arrow (boolean, boolean)) ->
      if ~(v in? exprFreeVars e) then
      OK (theoreM (cx, e @ TRUE &&& e @ FALSE <==> FA v BOOL e @ VAR v))
      else   FAIL
      | _ -> FAIL)
    | thCongruence (prf1, prf2, prf3) ->
      (case checkExpr prf1 of OK (cx, e1, t) ->
      (case checkExprWithContextAndType cx t prf2 of OK e2 ->
      (case checkExprWithContext cx prf3 of OK (e, arrow (t0, t1)) ->
      if t0 = t then
      OK (theoreM (cx, e1 == e2 ==> e @ e1 == e @ e2))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | thExtensionality (prf1, prf2, v) ->
      (case checkExpr prf1 of OK (cx, e1, arrow (t, t1)) ->
      (case checkExprWithContextAndType cx (t --> t1) prf2 of OK e2 ->
      if ~(v in? exprFreeVars e1 \/ exprFreeVars e2) then
      OK (theoreM (cx, e1 == e2 <==>
                       FA v t e1 @ VAR v == e2 @ VAR v))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | thAbstraction prf ->
      (case checkExpr prf of
         OK (cx, binary (equation, binding (abstraction, vS, tS, e),
                                   nary (tuple, eS)), t) ->
      (case checkExprSubstitution vS eS of OK esbs ->
      if exprSubstOK? (e, esbs) then
      OK (theoreM (cx, FNN vS tS e @ TUPLE eS == exprSubst esbs e))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | thIfThenElse (prf0, prf1, prf2) ->
      (case checkExpr prf0 of OK (cx, ifThenElse (e0, e1, e2), t) ->
      (case checkTheoremEquation prf1 of OK (cx1, mustBeE1, e) ->
      (case checkExtraAxiom cx cx1 of OK (_, mustBeEmpty, mustBeE0) ->
      if mustBeEmpty = empty
      && mustBeE0 = e0
      && mustBeE1 = e1 then
      (case checkTheoremEquation prf1 of OK (cx2, mustBeE2, mustBeE) ->
      (case checkExtraAxiom cx cx2 of OK (_, mustBeEmpty, mustBeNotE0) ->
      if mustBeEmpty = empty
      && mustBeNotE0 = ~~ e0
      && mustBeE2 = e2
      && mustBeE = e then
      OK (theoreM (cx, IF e0 e1 e2 == e))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | thRecord (prf, v, vS) ->
      (case checkRecordType prf of OK (cx, fS, tS) ->
      if noRepetitions? (v |> vS)
      && length vS = length tS then
      OK (theoreM (cx, FA v (TRECORD fS tS)
                          (EXX1 vS tS (VAR v == RECORD fS (map (VAR, vS))))))
      else   FAIL
      | _ -> FAIL)
    | thTuple (prf, v, vS) ->
      (case checkProductType prf of OK (cx, tS) ->
      if noRepetitions? (v |> vS)
      && length vS = length tS then
      OK (theoreM (cx, FA v (PRODUCT tS)
                          (EXX1 vS tS (VAR v == TUPLE (map (VAR, vS))))))
      else   FAIL
      | _ -> FAIL)
    | thRecordProjection (prf, f) ->
      (case checkExpr prf of
         OK (cx, nary (record fS, eS), nary (record mustBeFS, tS)) ->
      if mustBeFS = fS
      && noRepetitions? fS
      && f in? fS then
      let i:Nat = indexOf (fS, f) in
      if i < length eS then
      OK (theoreM (cx, (RECORD fS eS) DOTr f == (eS!i)))
      else   FAIL
      else   FAIL
      | _ -> FAIL)
    | thTupleProjection (prf, i) ->
      (case checkExpr prf of OK (cx, nary (tuple, eS), nary (product, tS)) ->
      if i <= length eS then
      OK (theoreM (cx, (TUPLE eS) DOTt i == (eS!(i-1))))
      else   FAIL
      | _ -> FAIL)
    | thRecordUpdate1 (prf1, prf2, f) ->
      (case checkExpr prf1 of
         OK (cx, nary (record fS1, eS1), nary (record mustBeFS1, tS1)) ->
      if mustBeFS1 = fS1 then
      (case checkExprWithContext cx prf2 of
         OK (nary (record fS2, eS2), nary (record mustBeFS2, tS2)) ->
      if mustBeFS2 = fS2
      && f in? fS1
      && ~(f in? fS2)
      && noRepetitions? fS1 then
      let i:Nat = indexOf (fS1, f) in
      OK (theoreM (cx,
                   (RECORD fS1 eS1 <<< RECORD fS2 eS2) DOTr f == (eS1!i)))
      else   FAIL
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | thRecordUpdate2 (prf1, prf2, f) ->
      (case checkExpr prf1 of
         OK (cx, nary (record fS1, eS1), nary (record mustBeFS1, tS1)) ->
      if mustBeFS1 = fS1 then
      (case checkExprWithContext cx prf2 of
         OK (nary (record fS2, eS2), nary (record mustBeFS2, tS2)) ->
      if mustBeFS2 = fS2
      && f in? fS2
      && noRepetitions? fS2 then
      let i:Nat = indexOf (fS2, f) in
      OK (theoreM (cx,
                   (RECORD fS1 eS1 <<< RECORD fS2 eS2) DOTr f == (eS2!i)))
      else   FAIL
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | thEmbedderSurjective (prf, c, v, v1) ->
      (case checkSumType prf of OK (cx, cS, t?S) ->
      if v ~= v1 then
      let n:Nat = length cS in
      if length t?S = n then
      let disjuncts:Expressions = seqSuchThat (fn(i:Nat) ->
        if i < n then
          Some (case (t?S!i) of
                  | Some t ->
                    EX v1 t (VAR v == EMBED (SUM cS t?S) (cS!i) @ VAR v1)
                  | None ->
                    VAR v == EMBED (SUM cS t?S) (cS!i))
        else None) in
      OK (theoreM (cx, FA v (SUM cS t?S) (disjoinAll disjuncts)))
      else   FAIL
      else   FAIL
      | _ -> FAIL)
    | thEmbeddersDistinct (prf, ci, cj, vi?, vj?) ->
      (case checkSumType prf of OK (cx, cS, t?S) ->
      if noRepetitions? cS
      && ci in? cS
      && cj in? cS
      && length t?S = length cS then
      let i:Nat = indexOf (cS, ci) in
      let j:Nat = indexOf (cS, cj) in
      (case (t?S!i, t?S!j) of
         | (Some ti, Some tj) ->
           (case (vi?, vj?) of
              | (Some vi, Some vj) ->
                if vi ~= vj then
                  OK (theoreM (cx, FAA (seq2(vi,vj)) (seq2(ti,tj))
                                       (EMBED (SUM cS t?S) ci @ VAR vi ~==
                                        EMBED (SUM cS t?S) cj @ VAR vj)))
                else FAIL
              | _ -> FAIL)
         | (Some ti, None) ->
           (case (vi?, vj?) of
              | (Some vi, None) ->
                OK (theoreM (cx, FA vi ti (EMBED (SUM cS t?S) ci @ VAR vi ~==
                                           EMBED (SUM cS t?S) cj)))
              | _ -> FAIL)
         | (None, Some tj) ->
           (case (vi?, vj?) of
              | (None, Some vj) ->
                OK (theoreM (cx, FA vj tj (EMBED (SUM cS t?S) ci ~==
                                           EMBED (SUM cS t?S) cj @ VAR vj)))
              | _ -> FAIL)
         | (None, None) ->
           if (vi?, vj?) = (None, None) then
             OK (theoreM (cx, EMBED (SUM cS t?S) ci ~== EMBED (SUM cS t?S) cj))
           else FAIL)
      else   FAIL
      | _ -> FAIL)
    | thEmbedderInjective (prf, c, v1, v2) ->
      (case checkSumType prf of OK (cx, cS, t?S) ->
      (case checkConstructorType? (SUM cS t?S) c of OK (Some t) ->
      if v1 ~= v2 then
      OK (theoreM (cx, FAA (seq2(v1,v2)) (seq2(t,t))
                           (VAR v1 ~== VAR v2 ==>
                            EMBED (SUM cS t?S) c @ VAR v1 ~==
                            EMBED (SUM cS t?S) c @ VAR v2)))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | thRelaxatorSatisfiesPredicate (prf, v) ->
      (case checkSubType prf of OK (cx, t, r) ->
      OK (theoreM (cx, FA v (t\r) (r @ (RELAX r @ VAR v))))
      | _ -> FAIL)
    | thRelaxatorInjective (prf, v1, v2) ->
      (case checkSubType prf of OK (cx, t, r) ->
      if v1 ~= v2 then
      OK (theoreM (cx, FAA (seq2(v1,v2)) (seq2(t\r,t\r))
                           (VAR v1 ~== VAR v2 ==>
                            RELAX r @ VAR v1 ~== RELAX r @ VAR v2)))
      else   FAIL
      | _ -> FAIL)
    | thRelexatorSurjective (prf, v, v1) ->
      (case checkSubType prf of OK (cx, t, r) ->
      if v ~= v1 then
      OK (theoreM (cx, FA v t
                          (r @ VAR v ==>
                           EX v1 (t\r) (VAR v == RELAX r @ VAR v1))))
      else   FAIL
      | _ -> FAIL)
    | thRestriction (prf, v) ->
      (case checkSubType prf of OK (cx, t, r) ->
      OK (theoreM (cx, FA v (t\r) (RESTRICT r (RELAX r @ VAR v) == VAR v)))
      | _ -> FAIL)
    | thQuotienterSurjective (prf, v, v1) ->
      (case checkQuotientType prf of OK (cx, t, q) ->
      if v ~= v1 then
      OK (theoreM (cx, FA v (t/q) (EX v1 t (QUOTIENT q @ VAR v1 == VAR v))))
      else   FAIL
      | _ -> FAIL)
    | thQuotienterEquivClass (prf, v1, v2) ->
      (case checkQuotientType prf of OK (cx, t, q) ->
      if v1 ~= v2 then
      OK (theoreM (cx, FAA (seq2(v1,v2)) (seq2(t,t))
                           (q @ PAIR (VAR v1) (VAR v2) <==>
                            QUOTIENT q @ VAR v1 == QUOTIENT q @ VAR v2)))
      else   FAIL
      | _ -> FAIL)
    | thChoice (prf, v) ->
      (case checkExpr prf of
         OK (cx, binary (choice, q, e),
                 arrow (subQuot (quotienT, t, mustBeQ), t1)) ->
      if mustBeQ = q
      && ~(v in? exprFreeVars e) then
      OK (theoreM (cx, FA v t
                          (CHOOSE q e @ (QUOTIENT q @ VAR v) == e @ VAR v)))
      else   FAIL
      | _ -> FAIL)
    | thCase (prf, prfS) ->
      (case checkExpr prf of OK (cx, casE (e, pS, eS), t) ->
      let n:Nat = length pS in
      if n > 0
      && length eS = n
      && length prfS = n then
      let caseMatches:Expressions = seqSuchThat (fn(i:Nat) ->
        if i < n then Some (let (vS,tS) = pattVarsWithTypes (pS!i) in
                            EXX vS tS (pattAssumptions (pS!i, e)))
        else None) in
      let varCxS:FSeq Context = seqSuchThat (fn(i:Nat) ->
        if i < n then Some (multiVarDecls (pattVarsWithTypes (pS!i)))
        else None) in
      let negAsmS:Expressions = seqSuchThat (fn(i:Nat) ->
        if i < n then Some (conjoinAll (seqSuchThat (fn(j:Nat) ->
                             if j < i then Some (~~ (caseMatches!j))
                                      else None)))
                 else None) in
      let posAsmS:Expressions = seqSuchThat (fn(i:Nat) ->
        if i < n then Some (pattAssumptions (pS!i, e))
                 else None) in
      let def aux (i:Nat, e0?:Expression?) : MayFail Expression =
            if i = n then
              case e0? of Some e0 -> OK e0
                        | None    -> FAIL   % never happens
            else
              case checkCaseBranchTheorem
                     cx (varCxS!i) (negAsmS!i) (posAsmS!i) (eS!i) (prfS!i) of
                | OK e0 ->
                  (case e0? of Some mustBeE0 -> if mustBeE0 = e0 then
                                                  aux (i+1, Some e0)
                                                else FAIL
                             | None -> aux (i+1, Some e0))
                | _ -> FAIL
      in
      (case aux (0, None) of OK e0 ->
      OK (theoreM (cx, CASE e pS eS == e0))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | thRecursiveLet (prfEx, prfTh) ->
      (case checkExpr prfEx of OK (cx, recursiveLet (vS, tS, eS, e), t) ->
      let n:Nat = length vS in
      if length tS = n
      && length eS = n then
      (case checkTheoremEquation prfTh of OK (cx1, mustBeLetDef, e0) ->
      let conjuncts:Expressions = seqSuchThat (fn(i:Nat) ->
        if i < n then Some (VAR (vS!i) == (eS!i))
        else None) in
      (case checkExtraAxiom (cx ++ multiVarDecls (vS, tS)) cx1 of
         OK (_, mustBeEmpty, mustBeConjoinAllConjuncts) ->
      if mustBeConjoinAllConjuncts = conjoinAll conjuncts
      && toSet vS /\ exprFreeVars e0 = empty then
      OK (theoreM (cx, LETDEF vS tS eS e == e0))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | thAbbrevTrue (prf, v) ->
      (case checkContext prf of OK cx ->
      OK (theoreM (cx, TRUE <==> FN v BOOL (VAR v) == FN v BOOL (VAR v)))
      | _ -> FAIL)
    | thAbbrevFalse (prf, v) ->
      (case checkContext prf of OK cx ->
      OK (theoreM (cx, FALSE <==> FN v BOOL (VAR v) == FN v BOOL TRUE))
      | _ -> FAIL)
    | thAbbrevNegation prf ->
      (case checkExpr prf of OK (cx, unary (negation, e), boolean) ->
      OK (theoreM (cx, ~~e <==> IF e FALSE TRUE))
      | _ -> FAIL)
    | thAbbrevInequation prf ->
      (case checkExpr prf of OK (cx, binary (inequation, e1, e2), boolean) ->
      OK (theoreM (cx, (e1 ~== e2) <==> ~~(e1 == e2)))
      | _ -> FAIL)
    | thAbbrevConjunction prf ->
      (case checkExpr prf of OK (cx, binary (conjunction, e1, e2), boolean) ->
      OK (theoreM (cx, e1 &&& e2 <==> IF e1 e2 FALSE))
      | _ -> FAIL)
    | thAbbrevDisjunction prf ->
      (case checkExpr prf of OK (cx, binary (disjunction, e1, e2), boolean) ->
      OK (theoreM (cx, e1 ||| e2 <==> IF e1 TRUE e2))
      | _ -> FAIL)
    | thAbbrevImplication prf ->
      (case checkExpr prf of OK (cx, binary (implication, e1, e2), boolean) ->
      OK (theoreM (cx, e1 ==> e2 <==> IF e1 e2 TRUE))
      | _ -> FAIL)
    | thAbbrevEquivalence prf ->
      (case checkExpr prf of OK (cx, binary (equivalence, e1, e2), boolean) ->
      OK (theoreM (cx, (e1 <==> e2) == (e1 == e2)))
      | _ -> FAIL)
    | thAbbrevUniversal prf ->
      (case checkExpr prf of OK (cx, binding (universal, vS, tS, e), boolean) ->
      OK (theoreM (cx, FAA vS tS e <==> FNN vS tS e == FNN vS tS TRUE))
      | _ -> FAIL)
    | thAbbrevExistential prf ->
      (case checkExpr prf of OK (cx, binding (existential, vS, tS, e), boolean) ->
      OK (theoreM (cx, EXX vS tS e <==> ~~(FAA vS tS (~~e))))
      | _ -> FAIL)
    | thAbbrevExistential1 (prf, vS1) ->
      (case checkExpr prf of OK (cx, binding (existential1, vS, tS, e), boolean) ->
      if noRepetitions? vS
      && length vS1 = length vS then
      let esbs:ExprSubstitution = FMap.fromSequences (vS, map (VAR, vS1)) in
      if toSet vS /\ toSet vS1 = empty
      && exprSubstOK? (e, esbs) then
      OK (theoreM (cx, EXX1 vS tS e <==>
                       EXX vS tS (e &&&
                                  FAA vS1 tS (exprSubst esbs e ==>
                                              TUPLE (map (VAR, vS)) ==
                                              TUPLE (map (VAR, vS1))))))
      else   FAIL
      else   FAIL
      | _ -> FAIL)
    | thAbbrevNonRecursiveLet prf ->
      (case checkExpr prf of OK (cx, nonRecursiveLet (p, e, e1), t) ->
      OK (theoreM (cx, LET p e e1 == CASE e (singleton p) (singleton e1)))
      | _ -> FAIL)


endspec
