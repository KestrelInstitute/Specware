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


  (* Check whether element belongs to sequence. If it does, return index of
  its (first, i.e. leftmost) occurrence. *)

  op checkIndex : [a] a -> FSeq a -> MayFail Nat
  def [a] checkIndex x s =
    let def aux (x : a,       % element
                 i : Nat,     % current index
                 s : FSeq a)  % remaining sequence
                : MayFail Nat =
          if s = empty then FAIL
          else if x = first s then OK i
          else aux (x, i+1, rtail s)
    in
    aux (x, 0, s)


  (* Check whether a context declares a type. If so, return its arity. *)

  op checkTypeDecl : Context -> TypeName -> MayFail Nat
  def checkTypeDecl cx tn =
    if cx = empty then FAIL
    else case first cx of
           | typeDeclaration (tn1, n) ->
             if tn1 = tn then OK n
             else checkTypeDecl (rtail cx) tn
           | _ -> checkTypeDecl (rtail cx) tn


  (* Like previous op but also check that arity coincides with
  argument. Return nothing, if successful. *)

  op checkTypeDeclWithArity : Context -> TypeName -> Nat -> MayFail ()
  def checkTypeDeclWithArity cx tn n =
    case checkTypeDecl cx tn of
      | OK mustBe_n -> if mustBe_n = n then OK () else FAIL
      | _ -> FAIL


  (* Check whether a context declares an op. If so, return its type
  information. *)

  op checkOpDecl : Context -> Operation -> MayFail (TypeVariables * Type)
  def checkOpDecl cx o =
    if cx = empty then FAIL
    else case first cx of
           | opDeclaration (o1, tvS, t) ->
             if o1 = o then OK (tvS, t)
             else checkOpDecl (rtail cx) o
           | _ -> checkOpDecl (rtail cx) o


  (* Check whether a context declares a variable. If so, return its type. *)

  op checkVarDecl : Context -> Variable -> MayFail Type
  def checkVarDecl cx v =
    if cx = empty then FAIL
    else case first cx of
           | varDeclaration (v1, t) ->
             if v1 = v then OK t
             else checkVarDecl (rtail cx) v
           | _ -> checkVarDecl (rtail cx) v


  (* Check whether a context defines a type. If so, return its definition
  information. *)

  op checkTypeDef : Context -> TypeName -> MayFail (TypeVariables * Type)
  def checkTypeDef cx tn =
    if cx = empty then FAIL
    else case first cx of
           | typeDefinition (tn1, tvS, t) ->
             if tn1 = tn then OK (tvS, t)
             else checkTypeDef (rtail cx) tn
           | _ -> checkTypeDef (rtail cx) tn


  (* Check whether a context defines an op. If so, return its definition
  information. *)

  op checkOpDef : Context -> Operation -> MayFail (TypeVariables * Expression)
  def checkOpDef cx o =
    if cx = empty then FAIL
    else case first cx of
           | opDefinition (o1, tvS, e) ->
             if o1 = o then OK (tvS, e)
             else checkOpDef (rtail cx) o
           | _ -> checkOpDef (rtail cx) o


  (* Check whether a context includes a named axiom. If so, return the rest of
  the axiom information. *)

  op checkAxiom : Context -> AxiomName -> MayFail (TypeVariables * Expression)
  def checkAxiom cx an =
    if cx = empty then FAIL
    else case first cx of
           | axioM (an1, tvS, e) ->
             if an1 = an then OK (tvS, e)
             else checkAxiom (rtail cx) an
           | _ -> checkAxiom (rtail cx) an


  (* Check whether a context consists exclusively of type variable
  declarations. If so, return the declared type variables, in the order they
  are declared. *)

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


  (* Check whether a context consists exclusively of variable declarations. If
  so, return the declared variables along with their types, in the order they
  are declared. *)

  op checkAllVarDecls : Context -> MayFail (Variables * Types)
  def checkAllVarDecls cx =
    let def aux (cx  : Context,
                 vS : Variables,  % accumulator
                 tS : Types)      % accumulator
                : MayFail (Variables * Types) =
          if cx = empty then OK (vS, tS)
          else case first cx of
                 | varDeclaration (v, t) -> aux (rtail cx, vS <| v, tS <| t)
                 | _ -> FAIL
    in
    aux (cx, empty, empty)


  (* Check whether `cx2' is `cx1' plus some extra type variable declarations.
  If so, return the type variables, in the order they are declared. *)

  op checkExtraTypeVars : Context -> Context -> MayFail TypeVariables
  def checkExtraTypeVars cx1 cx2 =
    if length cx1 <= length cx2
    && firstN (cx2, length cx1) = cx1 then
    checkAllTypeVarDecls (lastN (cx2, length cx2 - length cx1))
    else FAIL


  (* Check whether `cx2' is `cx1' plus an extra axiom. If so, return the axiom
  information. *)

  op checkExtraAxiom :
     Context -> Context -> MayFail (AxiomName * TypeVariables * Expression)
  def checkExtraAxiom cx1 cx2 =
    if length cx2 = length cx1 + 1 then
    case last cx2 of
      | axioM (an, tvS, e) -> OK (an, tvS, e)
      | _ -> FAIL
    else FAIL


  (* Check whether the last `n' elements of a context are variable
  declarations. If so, return the declared variables and types, in the order
  they are declared, along with the preceding part of the context. *)

  op checkLastNVars : Context -> Nat -> MayFail (Context * Variables * Types)
  def checkLastNVars cx n =
    if length cx >= n then
    case checkAllVarDecls (lastN (cx, n)) of OK (vS, tS) ->
    OK (firstN (cx, length cx - n), vS, tS)
    | _ -> FAIL
    else   FAIL


  (* Check whether given type variables and types form a valid type
  substitution. If so, return it. *)

  op checkTypeSubstitution : TypeVariables -> Types -> MayFail TypeSubstitution
  def checkTypeSubstitution tvS tS =
    if noRepetitions? tvS
    && length tvS = length tS
    then OK (FMap.fromSequences (tvS, tS))
    else FAIL


  (* Check whether given variables and expressions form a valid expression
  substitution. If so, return it. *)

  op checkExprSubstitution : Variables -> Expressions -> MayFail ExprSubstitution
  def checkExprSubstitution vS eS =
    if noRepetitions? vS
    && length vS = length eS
    then OK (FMap.fromSequences (vS, eS))
    else FAIL


  (* We give a functional version of positional type substitution, which is
  defined relationally in spec `SyntaxWithCoreOps'. If the position is invalid
  or the type at the position is not the one supplied as argument, a failure
  is returned. *)

  op typeSubstInTypeAt : Type       * Type * Type * Position -> MayFail Type
  op typeSubstInExprAt : Expression * Type * Type * Position -> MayFail Expression
  op typeSubstInPattAt : Pattern    * Type * Type * Position -> MayFail Pattern

  def typeSubstInTypeAt(t,old,new,pos) =
    % base case:
    if pos = empty then
      if old = t then OK new
      else FAIL
    % recursive case:
    else
      let i   = first pos in
      let pos = rtail pos in  % `pos' is overwritten
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
          if i ~= 0 && i <= length t?S then
            case t?S ! (i-1) of
              | Some ti ->
                (case typeSubstInTypeAt (ti, old, new, pos) of
                   | OK newTi -> OK (sum (cS, update (t?S, i-1, Some newTi)))
                   | FAIL     -> FAIL)
              | None -> FAIL
          else FAIL
        | nary(tc,tS) ->
          if i ~= 0 && i <= length tS then
            case typeSubstInTypeAt (tS!(i-1), old, new, pos) of
              | OK newTi -> OK (nary (tc, update (tS, i-1, newTi)))
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
    % base case:
    if pos = empty then FAIL
    % recursive case:
    else
      let i   = first pos in
      let pos = rtail pos in  % `pos' is overwritten
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
          if i ~= 0 && i <= length eS then
            case typeSubstInExprAt (eS!(i-1), old, new, pos) of
              | OK newEi -> OK (nary (eo, update (eS, i-1, newEi)))
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
          if i ~= 0 && i <= length tS then
            case typeSubstInTypeAt (tS!(i-1), old, new, pos) of
              | OK newTi -> OK (opInstance (o, update (tS, i-1, newTi)))
              | FAIL     -> FAIL
          else FAIL
        | embedder(t,c) ->
          if i = 0 then
            case typeSubstInTypeAt (t, old, new, pos) of
              | OK newT -> OK (embedder (newT, c))
              | FAIL    -> FAIL
          else FAIL
        | casE(e,pS,eS) ->
          if i = 0 then
            case typeSubstInExprAt (e, old, new, pos) of
              | OK newE -> OK (casE (newE, pS, eS))
              | FAIL    -> FAIL
          else if i rem 2 = 1 then  % i.e. `i' is odd
            let j:Nat = i div 2 in  % `j' in {0,1,2,...}
            if j < length pS then
              case typeSubstInPattAt (pS!j, old, new, pos) of
                | OK newPj -> OK (casE (e, update (pS, j, newPj), eS))
                | FAIL     -> FAIL
            else FAIL
          else if i rem 2 = 0 then  % i.e. `i' is even
            let j:Nat = i div 2 in  % `j' in {0,1,2,...}
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
          else if i rem 2 = 1 then  % i.e. `i' is odd
            let j:Nat = i div 2 in  % `j' in {0,1,2,...}
            if j < length tS then
              case typeSubstInTypeAt (tS!j, old, new, pos) of
                | OK newTj -> OK (recursiveLet (vS, update (tS, j, newTj), eS, e))
                | FAIL     -> FAIL
            else FAIL
          else if i rem 2 = 0 then  % i.e. `i' is even
            let j:Nat = i div 2 in  % `j' in {0,1,2,...}
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
    % base case:
    if pos = empty then FAIL
    % recursive case:
    else
      let i   = first pos in
      let pos = rtail pos in  % `pos' is overwritten
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
          if i ~= 0 && i <= length pS then
            case typeSubstInPattAt (pS!(i-1), old, new, pos) of
              | OK newPi -> OK (record (fS, update (pS, i-1, newPi)))
              | FAIL     -> FAIL
          else FAIL
        | tuple pS ->
          if i ~= 0 && i <= length pS then
            case typeSubstInPattAt (pS!(i-1), old, new, pos) of
              | OK newPi -> OK (tuple (update (pS, i-1, newPi)))
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

  conjecture typeSubstInXXXAt_is_functional_version_of_isTypeSubstInXXXAt? is
                        % `XXX' stands for `Type', `Expr', or `Patt'
    fa (t:Type, e:Expression, p:Pattern,
        newT:Type, newE:Expression, newP:Pattern,
        old:Type, new:Type, pos:Position)
      (isTypeSubstInTypeAt? (t, old, new, pos, newT) <=>
       typeSubstInTypeAt (t, old, new, pos) = OK newT)
      &&
      (isTypeSubstInExprAt? (e, old, new, pos, newE) <=>
       typeSubstInExprAt (e, old, new, pos) = OK newE)
      &&
      (isTypeSubstInPattAt? (p, old, new, pos, newP) <=>
       typeSubstInPattAt (p, old, new, pos) = OK newP)


  (* We give a functional version of positional expression substitution, which
  is defined relationally in spec `SyntaxWithCoreOps'. If the position is
  invalid or the expression at the position is not the one supplied as
  argument, a failure is returned. *)

  op exprSubstAt :
     Expression * Expression * Expression * Position -> MayFail Expression
  def exprSubstAt(e,old,new,pos) =
    % base case:
    if pos = empty then
      if old = e then OK new
      else FAIL
    % recursive case:
    else
      let i   = first pos in
      let pos = rtail pos in  % `pos' is overwritten
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
          if i ~= 0 && i <= length eS then
            case exprSubstAt (eS!(i-1), old, new, pos) of
              | OK newEi -> OK (nary (eo, update (eS, i-1, newEi)))
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
                | OK newEi -> OK (casE (e, pS, update (eS, i-1, newEi)))
                | FAIL     -> FAIL
          else FAIL
        | recursiveLet(vS,tS,eS,e) ->
          if i = 0 then
            case exprSubstAt (e, old, new, pos) of
              | OK newE -> OK (recursiveLet (vS, tS, eS, newE))
              | FAIL    -> FAIL
          else if i <= length eS then
            case exprSubstAt (eS!(i-1), old, new, pos) of
              | OK newEi -> OK (recursiveLet (vS, tS, update (eS, i-1, newEi), e))
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

  conjecture exprSubstAt_is_functional_version_of_isExprSubstAt? is
    fa (e:Expression, newE:Expression,
        old:Expression, new:Expression, pos:Position)
      isExprSubstAt? (e, old, new, pos, newE) <=>
      exprSubstAt (e, old, new, pos) = OK newE


  (* This is the main op of this spec. Before defining it, we define various
  auxiliary checking ops that are mutually recursive with this op. *)

  op check : Proof -> MayFail Judgement   % defined below


  (* Check proof of well-formed context; return context if successful. *)

  op checkWFContext : Proof -> MayFail Context
  def checkWFContext prf =
    case check prf of
      | OK (wellFormedContext cx) -> OK cx
      | _ -> FAIL


  (* Check proof of well-formed type; return context and type if
  successful. *)

  op checkWFType : Proof -> MayFail (Context * Type)
  def checkWFType prf =
    case check prf of
      | OK (wellFormedType (cx, t)) -> OK (cx, t)
      | _ -> FAIL


  (* Like previous op but also check that context coincides with argument.
  Only return type, if successful. *)

  op checkWFTypeWithContext : Context -> Proof -> MayFail Type
  def checkWFTypeWithContext cx prf =
    case checkWFType prf of
      | OK (mustBe_cx, t) -> if mustBe_cx = cx then OK t else FAIL
      | _ -> FAIL


  (* Like previous op but allow context to have extra type variable
  declarations. Besides type, return declared type variables (in the order
  they are declared) if successful. *)

  op checkWFTypeWithContextAndExtraTypeVars :
     Context -> Proof -> MayFail (TypeVariables * Type)
  def checkWFTypeWithContextAndExtraTypeVars cx prf =
    case checkWFType prf of
      | OK (mustBe_cx_plus_tvS, t) ->
        (case checkExtraTypeVars cx mustBe_cx_plus_tvS of
           | OK tvS -> OK (tvS, t)
           | _ -> FAIL)
      | _ -> FAIL


  (* Check proofs of well-formed types with given context; return types if
  successful. *)

  op checkWFTypesWithContext : Context -> Proofs -> MayFail Types
  def checkWFTypesWithContext cx prfS =
    checkSequence (map (checkWFTypeWithContext cx, prfS))


  (* Check optional proofs of well-formed types with given context; return
  optional types according to optional proofs (i.e. `None' proof yields `None'
  type while `Some' proof yields `Some' type) if all proofs successful. *)

  op checkWFType?sWithContext : Context -> Proof?s -> MayFail Type?s
  def checkWFType?sWithContext cx prf?S =
    checkOptionSequence (map (mapOption (checkWFTypeWithContext cx), prf?S))


  (* Check proof of well-formed sum type; return context, constructors, and
  optional component types, if successful. *)

  op checkWFSumType : Proof -> MayFail (Context * Constructors * Type?s)
  def checkWFSumType prf =
    case checkWFType prf of
      | OK (cx, sum (cS, t?S)) -> OK (cx, cS, t?S)
      | _ -> FAIL


  (* Check proof of well-formed record type; return context, fields, and
  component types, if successful. *)

  op checkWFRecordType : Proof -> MayFail (Context * Fields * Types)
  def checkWFRecordType prf =
    case checkWFType prf of
      | OK (cx, nary (record fS, tS)) -> OK (cx, fS, tS)
      | _ -> FAIL


  (* Check proof of well-formed product type; return context and component
  types if successful. *)

  op checkWFProductType : Proof -> MayFail (Context * Types)
  def checkWFProductType prf =
    case checkWFType prf of
      | OK (cx, nary (product, tS)) -> OK (cx, tS)
      | _ -> FAIL


  (* Check proof of well-formed subtype; return context, base type, and
  predicate, if successful. *)

  op checkWFSubType : Proof -> MayFail (Context * Type * Expression)
  def checkWFSubType prf =
    case checkWFType prf of
      | OK (cx, subQuot (sub, t, r)) -> OK (cx, t, r)
      | _ -> FAIL


  (* Like previous op but also check that context and base type coincide with
  arguments. Only return predicate, if successful. *)

  op checkWFSubTypeWithContextAndBaseType :
     Context -> Type -> Proof -> MayFail (Expression)
  def checkWFSubTypeWithContextAndBaseType cx t prf =
    case checkWFSubType prf of
      | OK (mustBe_cx, mustBe_t, r) ->
        if mustBe_cx = cx && mustBe_t = t then OK r else FAIL
      | _ -> FAIL


  (* Check proof of well-formed quotient type; return context, base type, and
  predicate, if successful. *)

  op checkWFQuotientType : Proof -> MayFail (Context * Type * Expression)
  def checkWFQuotientType prf =
    case checkWFType prf of
      | OK (cx, subQuot (quotienT, t, q)) -> OK (cx, t, q)
      | _ -> FAIL


  (* Like previous op but also check that context and base type coincide with
  arguments. Only return predicate, if successful. *)

  op checkWFQuotientTypeWithContextAndBaseType :
     Context -> Type -> Proof -> MayFail (Expression)
  def checkWFQuotientTypeWithContextAndBaseType cx t prf =
    case checkWFQuotientType prf of
      | OK (mustBe_cx, mustBe_t, q) ->
        if mustBe_cx = cx && mustBe_t = t then OK q else FAIL
      | _ -> FAIL


  (* Check proof of well-typed expression; return context, expression, and
  type, if successful. *)

  op checkWTExpr : Proof -> MayFail (Context * Expression * Type)
  def checkWTExpr prf =
    case check prf of
      | OK (wellTypedExpr (cx, e, t)) -> OK (cx, e, t)
      | _ -> FAIL


  (* Like previous op but also check that context coincides with argument.
  Only return expression and type, if successful. *)

  op checkWTExprWithContext : Context -> Proof -> MayFail (Expression * Type)
  def checkWTExprWithContext cx prf =
    case checkWTExpr prf of
      | OK (mustBe_cx, e, t) ->
        if mustBe_cx = cx then OK (e, t) else FAIL
      | _ -> FAIL


  (* Like previous op but allow context to have extra type variable
  declarations. Besides expression and type, return declared type variables
  (in the order they are declared) if successful. *)

  op checkWTExprWithContextAndExtraTypeVars :
     Context -> Proof -> MayFail (TypeVariables * Expression * Type)
  def checkWTExprWithContextAndExtraTypeVars cx prf =
    case checkWTExpr prf of
      | OK (mustBe_cx_plus_tvS, e, t) ->
        (case checkExtraTypeVars cx mustBe_cx_plus_tvS of
           | OK tvS -> OK (tvS, e, t)
           | _ -> FAIL)
      | _ -> FAIL


  (* Like op `checkWTExprWithContext' but also check that type coincides with
  argument. Only return expression, if successful. *)

  op checkWTExprWithContextAndType : Context -> Type -> Proof -> MayFail Expression
  def checkWTExprWithContextAndType cx t prf =
    case checkWTExprWithContext cx prf of
      | OK (e, mustBe_t) ->
        if mustBe_t = t then OK e else FAIL
      | _ -> FAIL


  (* Check proofs of well-typed expressions with given context and types;
  return expressions if successful. *)

  op checkWTExprsWithContextAndTypes : Context -> Types -> Proofs -> MayFail Expressions
  def checkWTExprsWithContextAndTypes cx tS prfS =
    case checkSequence (map (checkWTExprWithContext cx, prfS)) of
      | OK etS ->
        let (eS, mustBe_tS) = unzip etS in
        if mustBe_tS = tS then OK eS else FAIL
      | _ -> FAIL


  (* Check proof of well-typed expression of arrow type; return context,
  expression, and domain and codomain types, if successful. *)

  op checkWTExprOfArrowType :
     Proof -> MayFail (Context * Expression * Type * Type)
  def checkWTExprOfArrowType prf =
    case checkWTExpr prf of
      | OK (cx, e, arrow (t1, t2)) -> OK (cx, e, t1, t2)
      | _ -> FAIL


  (* Check proof of well-typed expression of record type; return context,
  expression, fields, and component types, if successful. *)

  op checkWTExprOfRecordType :
     Proof -> MayFail (Context * Expression * Fields * Types)
  def checkWTExprOfRecordType prf =
    case checkWTExpr prf of
      | OK (cx, e, nary (record fS, tS)) -> OK (cx, e, fS, tS)
      | _ -> FAIL


  (* Check proof of well-typed expression of product type; return context,
  expression, and component types, if successful. *)

  op checkWTExprOfProductType : Proof -> MayFail (Context * Expression * Types)
  def checkWTExprOfProductType prf =
    case checkWTExpr prf of
      | OK (cx, e, nary (product, tS)) -> OK (cx, e, tS)
      | _ -> FAIL


  (* Check proof of well-typed equation; return context and expressions if
  successful. *)

  op checkWTEquation : Proof -> MayFail (Context * Expression * Expression)
  def checkWTEquation prf =
    case checkWTExpr prf of
      | OK (cx, binary (equation, e1, e2), boolean) -> OK (cx, e1, e2)
      | _ -> FAIL


  (* Check proof of well-typed pattern; return context, pattern, and type, if
  successful. *)

  op checkWTPatt : Proof -> MayFail (Context * Pattern * Type)
  def checkWTPatt prf =
    case check prf of
      | OK (wellTypedPatt (cx, p, t)) -> OK (cx, p, t)
      | _ -> FAIL


  (* Like previous op but also check that context coincides with argument.
  Only return pattern and type, if successful. *)

  op checkWTPattWithContext : Context -> Proof -> MayFail (Pattern * Type)
  def checkWTPattWithContext cx prf =
    case checkWTPatt prf of
      | OK (mustBe_cx, p, t) ->
        if mustBe_cx = cx then OK (p, t) else FAIL
      | _ -> FAIL


  (* Like previous op but also check that type coincides with argument. Only
  return pattern, if successful. *)

  op checkWTPattWithContextAndType : Context -> Type -> Proof -> MayFail Pattern
  def checkWTPattWithContextAndType cx t prf =
    case checkWTPattWithContext cx prf of
      | OK (p, mustBe_t) ->
        if mustBe_t = t then OK p else FAIL
      | _ -> FAIL


  (* Check proofs of well-typed patterns with given context and types; return
  patterns if successful. *)

  op checkWTPattsWithContextAndTypes : Context -> Types -> Proofs -> MayFail Patterns
  def checkWTPattsWithContextAndTypes cx tS prfS =
    case checkSequence (map (checkWTPattWithContext cx, prfS)) of
      | OK ptS ->
        let (pS, mustBe_tS) = unzip ptS in
        if mustBe_tS = tS then OK pS else FAIL
      | _ -> FAIL


  (* Check proof of type equivalence; return context and types if
  successful. *)

  op checkTypeEquiv : Proof -> MayFail (Context * Type * Type)
  def checkTypeEquiv prf =
    case check prf of
      | OK (typeEquivalence (cx, t1, t2)) -> OK (cx, t1, t2)
      | _ -> FAIL


  (* Like previous op but also check that context coincides with
  argument. Only return types, if successful. *)

  op checkTypeEquivWithContext : Context -> Proof -> MayFail (Type * Type)
  def checkTypeEquivWithContext cx prf =
    case check prf of
      | OK (typeEquivalence (mustBe_cx, t1, t2)) ->
        if mustBe_cx = cx then OK (t1, t2) else FAIL
      | _ -> FAIL


  (* Like previous op but also check that left type coincides with
  argument. Only return right type, if successful. *)

  op checkTypeEquivWithContextAndLeftType :
     Context -> Type -> Proof -> MayFail Type
  def checkTypeEquivWithContextAndLeftType cx tLeft prf =
    case checkTypeEquivWithContext cx prf of
      | OK (mustBe_tLeft, tRight) ->
        if mustBe_tLeft = tLeft then OK tRight else FAIL
      | _ -> FAIL


  (* Check proof of theorem; return context and formula (expression) if
  successful. *)

  op checkTheorem : Proof -> MayFail (Context * Expression)
  def checkTheorem prf =
    case check prf of
      | OK (theoreM (cx, e)) -> OK (cx, e)
      | _ -> FAIL


  (* Like previous op but also check that context coincides with argument.
  Only return formula, if successful. *)

  op checkTheoremWithContext : Context -> Proof -> MayFail Expression
  def checkTheoremWithContext cx prf =
    case checkTheorem prf of
      | OK (mustBe_cx, e) -> if mustBe_cx = cx then OK e else FAIL
      | _ -> FAIL


  (* Like previous op but allow context to have extra type variable
  declarations. Besides formula, return declared type variables (in the order
  they are declared) if successful. *)

  op checkTheoremWithContextAndExtraTypeVars :
     Context -> Proof -> MayFail (TypeVariables * Expression)
  def checkTheoremWithContextAndExtraTypeVars cx prf =
    case checkTheorem prf of
      | OK (mustBe_cx_plus_tvS, e) ->
        (case checkExtraTypeVars cx mustBe_cx_plus_tvS of
           | OK tvS -> OK (tvS, e)
           | _ -> FAIL)
      | _ -> FAIL


  (* Like op `checkTheoremWithContext' but also check that formula coincides
  with argument. Return nothing if successful. *)

  op checkTheoremWithContextAndFormula :
     Context -> Expression -> Proof -> MayFail ()
  def checkTheoremWithContextAndFormula cx e prf =
    case checkTheoremWithContext cx prf of
      | OK mustBe_e -> if mustBe_e = e then OK () else FAIL
      | _ -> FAIL


  (* Check proof of existence and uniqueness theorem required to extend a
  context with an op definition. More precisely, given arguments `cx', `t',
  and `tvS', check that proof proves `theoreM (cx ++ multiTypeVarDecls tvS1,
  EX1 v (typeSubstInType tsbs t) (VAR v == e))' for some `tvS1', `v', `e', and
  `tsbs' such that `isTypeSubstFrom? (tsbs, tvS, map (TVAR, tvS1))' (see rule
  `cxOpDef' in spec `Provability'); return `tvS1', `v', and `e' if
  successful. *)

  op checkTheoremOpDef : Context -> Type -> TypeVariables -> Proof ->
                         MayFail (TypeVariables * Variable * Expression)
  def checkTheoremOpDef cx t tvS prf =
    case checkTheoremWithContextAndExtraTypeVars cx prf of
      OK (tvS1,
          binding (existential1, mustBe_singleton_v, mustBe_singleton_tsbs_of_t,
                   binary (equation, nullary (variable v), e))) ->
    (case checkTypeSubstitution tvS (map (TVAR, tvS1)) of OK tsbs ->
    if length mustBe_singleton_v = 1 then
    let v:Variable = first mustBe_singleton_v in
    if mustBe_singleton_tsbs_of_t = singleton (typeSubstInType tsbs t) then
    OK (tvS, v, e)
    else   FAIL
    else   FAIL
    | _ -> FAIL)
    | _ -> FAIL


  (* Check proof of reflexivity theorem required to form well-formed quotient
  type. More precisely, check that proof proves `theoreM (cx, FA v t (q @ PAIR
  (VAR v) (VAR v)))' for some `cx', `v', `t', and `q' such that `q' has no
  free variables (see rules `tyQuot' in spec `Provability'); return `cx', `v',
  `t', and `q' if successful. *)

  op checkTheoremReflexivity :
     Proof -> MayFail (Context * Variable * Type * Expression)
  def checkTheoremReflexivity prf =
    case checkTheorem prf of
      OK (cx, binding (universal, mustBe_singleton_v, mustBe_singleton_t,
                       binary (application, q, mustBe_pair_v_v))) ->
    if length mustBe_singleton_v = 1
    && length mustBe_singleton_t = 1 then
    let v:Variable = first mustBe_singleton_v in
    let t:Type     = first mustBe_singleton_t in
    if exprFreeVars q = empty
    &&  mustBe_pair_v_v = PAIR (VAR v) (VAR v) then
    OK (cx, v, t, q)
    else   FAIL
    else   FAIL
    | _ -> FAIL


  (* Check proof of symmetry theorem required to form well-formed quotient
  type. More precisely, given arguments `cx', `t', and `q', check that proof
  proves `theoreM (cx, FAA (seq2(v1,v2)) (seq2(t,t)) (q @ PAIR (VAR v1) (VAR
  v2) ==> q @ PAIR (VAR v2) (VAR v1)))' for some distinct `v1' and `v2' (see
  rule `tyQuot' in spec `Provability'); return nothing if successful. *)

  op checkTheoremSymmetry :
     Context -> Type -> Expression -> Proof -> MayFail ()
  def checkTheoremSymmetry cx t q prf =
    case checkTheoremWithContext cx prf of
      OK (binding (universal, mustBe_seq2_v1_v2, mustBe_seq2_t_t,
                   mustBe_q_pair_v1_v2_implies_q_pair_v2_v1)) ->
    if length mustBe_seq2_v1_v2 = 2 then
    let v1:Variable = mustBe_seq2_v1_v2 ! 0 in
    let v2:Variable = mustBe_seq2_v1_v2 ! 1 in
    if v1 ~= v2
    && mustBe_seq2_t_t = seq2 (t, t)
    && mustBe_q_pair_v1_v2_implies_q_pair_v2_v1 =
       (q @ PAIR (VAR v1) (VAR v2) ==> q @ PAIR (VAR v2) (VAR v1)) then
    OK ()
    else   FAIL
    else   FAIL
    | _ -> FAIL


  (* Check proof of transitivity theorem required to form well-formed quotient
  type. More precisely, given arguments `cx', `t', and `q', check that proof
  proves `theoreM (cx, FAA (seq3(u1,u2,u3)) (seq3(t,t,t)) (q @ PAIR (VAR u1)
  (VAR u2) &&& q @ PAIR (VAR u2) (VAR u3) ==> q @ PAIR (VAR u1) (VAR u3)))'
  for some distinct `u1', `u2', and `u3' (see rule `tyQuot' in spec
  `Provability'); return nothing if successful. *)

  op checkTheoremTransitivity :
     Context -> Type -> Expression -> Proof -> MayFail ()
  def checkTheoremTransitivity cx t q prf =
    case checkTheoremWithContext cx prf of
      OK (binding (universal, mustBe_seq3_u1_u2_u3, mustBe_seq3_t_t_t,
                   mustBe_q_pair_u1_u2_and_q_pair_u2_u3_implies_q_pair_u1_u3)) ->
    if length mustBe_seq3_u1_u2_u3 = 3 then
    let u1:Variable = mustBe_seq3_u1_u2_u3 ! 0 in
    let u2:Variable = mustBe_seq3_u1_u2_u3 ! 1 in
    let u3:Variable = mustBe_seq3_u1_u2_u3 ! 2 in
    if u1 ~= u2
    && u2 ~= u3
    && u3 ~= u1
    && mustBe_seq3_t_t_t = seq3 (t, t, t)
    && mustBe_q_pair_u1_u2_and_q_pair_u2_u3_implies_q_pair_u1_u3 =
       (q @ PAIR (VAR u1) (VAR u2) &&& q @ PAIR (VAR u2) (VAR u3) ==>
        q @ PAIR (VAR u1) (VAR u3)) then
    OK ()
    else   FAIL
    else   FAIL
    | _ -> FAIL


  (* We finally define `check', the main op of this spec. *)

  def check = fn

    %%%%%%%%%% well-formed contexts:
    | cxEmpty ->
      OK (wellFormedContext empty)
    | cxTypeDecl (prf, tn, n) ->
      (case checkWFContext prf of OK cx ->
      if ~(tn in? contextTypes cx) then
      OK (wellFormedContext (cx <| typeDeclaration (tn, n)))
      else   FAIL
      | _ -> FAIL)
    | cxOpDecl (prf, prf1, o) ->
      (case checkWFContext prf of OK cx ->
      if ~(o in? contextOps cx) then
      (case checkWFTypeWithContextAndExtraTypeVars cx prf1 of OK (tvS, t) ->
      OK (wellFormedContext (cx <| opDeclaration (o, tvS, t)))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | cxTypeDef (prf, prf1, tn) ->
      (case checkWFContext prf of OK cx ->
      (case checkTypeDecl cx tn of OK n ->
      if ~(contextDefinesType? (cx, tn)) then
      (case checkWFTypeWithContextAndExtraTypeVars cx prf1 of OK (tvS, t) ->
      if length tvS = n then
      OK (wellFormedContext (cx <| typeDefinition (tn, tvS, t)))
      else   FAIL
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | cxOpDef (prf, prf1, o) ->
      (case checkWFContext prf of OK cx ->
      (case checkOpDecl cx o of OK (tvS, t) ->
      if ~(contextDefinesOp? (cx, o)) then
      (case checkTheoremOpDef cx t tvS prf1 of OK (tvS1, v, e) ->
      if ~(o in? exprOps e) then
      let esbs:ExprSubstitution = FMap.singleton (v, OPP o (map (TVAR, tvS1))) in
      OK (wellFormedContext (cx <| opDefinition (o, tvS1, exprSubst esbs e)))
      else   FAIL
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | cxAxiom (prf, prf1, an) ->
      (case checkWFContext prf of OK cx ->
      if ~(an in? contextAxioms cx) then
      (case checkWTExprWithContextAndExtraTypeVars cx prf1 of
        OK (tvS, e, boolean) ->
      OK (wellFormedContext (cx <| axioM (an, tvS, e)))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | cxTypeVarDecl (prf, tv) ->
      (case checkWFContext prf of OK cx ->
      if ~(tv in? contextTypeVars cx) then
      OK (wellFormedContext (cx <| typeVarDeclaration tv))
      else   FAIL
      | _ -> FAIL)
    | cxVarDecl (prf, prf1, v) ->
      (case checkWFContext prf of OK cx ->
      if ~(v in? contextVars cx) then
      (case checkWFTypeWithContext cx prf1 of OK t ->
      OK (wellFormedContext (cx <| varDeclaration (v, t)))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)

    %%%%%%%%%% well-formed specs:
    | speC prf ->
      (case checkWFContext prf of OK cx ->
      if contextTypeVars cx = empty
      && contextVars cx = empty then
      OK (wellFormedSpec cx)  % implicit `restrict'
      else   FAIL
      | _ -> FAIL)

    %%%%%%%%%% well-formed types:
    | tyBoolean prf ->
      (case checkWFContext prf of OK cx ->
      OK (wellFormedType (cx, BOOL))
      | _ -> FAIL)
    | tyVariable (prf, tv) ->
      (case checkWFContext prf of OK cx ->
      if tv in? contextTypeVars cx then
      OK (wellFormedType (cx, TVAR tv))
      else   FAIL
      | _ -> FAIL)
    | tyArrow (prf1, prf2) ->
      (case checkWFType prf1 of OK (cx, t1) ->
      (case checkWFTypeWithContext cx prf2 of OK t2 ->
      OK (wellFormedType (cx, t1 --> t2))
      | _ -> FAIL)
      | _ -> FAIL)
    | tySum (prf, prf?S, cS) ->
      (case checkWFContext prf of OK cx ->
      if length prf?S = length cS
      && noRepetitions? cS
      && length cS > 0 then
      (case checkWFType?sWithContext cx prf?S of OK t?S ->
      OK (wellFormedType (cx, SUM cS t?S))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | tyInstance (prf, prfS, tn) ->
      (case checkWFContext prf of OK cx ->
      (case checkTypeDeclWithArity cx tn (length prfS) of OK () ->
      (case checkWFTypesWithContext cx prfS of OK tS ->
      OK (wellFormedType (cx, TYPE tn tS))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | tyRecord (prf, prfS, fS) ->
      (case checkWFContext prf of OK cx ->
      if length prfS = length fS
      && noRepetitions? fS then
      (case checkWFTypesWithContext cx prfS of OK tS ->
      OK (wellFormedType (cx, TRECORD fS tS))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | tyProduct (prf, prfS) ->
      (case checkWFContext prf of OK cx ->
      (case checkWFTypesWithContext cx prfS of OK tS ->
      OK (wellFormedType (cx, PRODUCT tS))
      | _ -> FAIL)
      | _ -> FAIL)
    | tySub prf ->
      (case checkWTExprOfArrowType prf of OK (cx, r, t, boolean) ->
      if exprFreeVars r = empty then
      OK (wellFormedType (cx, t \ r))
      else   FAIL
      | _ -> FAIL)
    | tyQuot (prf1, prf2, prf3) ->
      (case checkTheoremReflexivity prf1 of OK (cx, v, t, q) ->
      (case checkTheoremSymmetry cx t q prf2 of OK () ->
      (case checkTheoremTransitivity cx t q prf3 of OK () ->
      OK (wellFormedType (cx, t / q))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)

    %%%%%%%%%% type equivalence:
    | tyEqDef (prf, prfS, tn) ->
      (case checkWFContext prf of OK cx ->
      (case checkTypeDef cx tn of OK (tvS, t) ->
      (case checkWFTypesWithContext cx prfS of OK tS ->
      (case checkTypeSubstitution tvS tS of OK tsbs ->
      OK (typeEquivalence (cx, TYPE tn tS, typeSubstInType tsbs t))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | tyEqReflexive prf ->
      (case checkWFType prf of OK (cx, t) ->
      OK (typeEquivalence (cx, t, t))
      | _ -> FAIL)
    | tyEqSymmetric prf ->
      (case checkTypeEquiv prf of OK (cx, t1, t2) ->
      OK (typeEquivalence (cx, t2, t1))
      | _ -> FAIL)
    | tyEqTransitive (prf1, prf2) ->
      (case checkTypeEquiv prf1 of OK (cx, t1, t2) ->
      (case checkTypeEquivWithContextAndLeftType cx t1 prf2 of OK t3 ->
      OK (typeEquivalence (cx, t1, t3))
      | _ -> FAIL)
      | _ -> FAIL)
    | tyEqSubstitution (prf, prf1, pos) ->
      (case checkWFType prf of OK (cx, oldT) ->
      (case checkTypeEquivWithContext cx prf1 of OK (t1, t2) ->
      (case typeSubstInTypeAt (oldT, t1, t2, pos) of OK newT ->
      OK (typeEquivalence (cx, oldT, newT))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | tyEqSumOrder (prf, nS) ->
      (case checkWFSumType prf of OK (cx, cS, t?S) ->
      (case checkPermutation nS of OK prm ->
      if length nS = length cS then
      OK (typeEquivalence
            (cx, SUM cS t?S, SUM (permute(cS,prm)) (permute(t?S,prm))))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | tyEqRecordOrder (prf, nS) ->
      (case checkWFRecordType prf of OK (cx, fS, tS) ->
      (case checkPermutation nS of OK prm ->
      if length nS = length fS then
      OK (typeEquivalence
            (cx, TRECORD fS tS, TRECORD (permute(fS,prm)) (permute(tS,prm))))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | tyEqProductOrder (prf, nS) ->
      (case checkWFProductType prf of OK (cx, tS) ->
      (case checkPermutation nS of OK prm ->
      if length nS = length tS then
      OK (typeEquivalence (cx, PRODUCT tS, PRODUCT (permute(tS,prm))))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | tyEqSubPredicate (prf1, prf2, prf3) ->
      (case checkWFSubType prf1 of OK (cx, t, r1) ->
      (case checkWFSubTypeWithContextAndBaseType cx t prf2 of OK r2 ->
      (case checkTheoremWithContextAndFormula cx (r1 == r2) prf3 of OK () ->
      OK (typeEquivalence (cx, t \ r1, t \ r2))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | tyEqQuotientPredicate (prf1, prf2, prf3) ->
      (case checkWFQuotientType prf1 of OK (cx, t, q1) ->
      (case checkWFQuotientTypeWithContextAndBaseType cx t prf2 of OK q2 ->
      (case checkTheoremWithContextAndFormula cx (q1 == q2) prf3 of OK () ->
      OK (typeEquivalence (cx, t / q1, t / q2))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)

    %%%%%%%%%% well-typed expressions:
    | exVariable (prf, v) ->
      (case checkWFContext prf of OK cx ->
      (case checkVarDecl cx v of OK t ->
      OK (wellTypedExpr (cx, VAR v, t))
      | _ -> FAIL)
      | _ -> FAIL)
    | exTrue prf ->
      (case checkWFContext prf of OK cx ->
      OK (wellTypedExpr (cx, TRUE, BOOL))
      | _ -> FAIL)
    | exFalse prf ->
      (case checkWFContext prf of OK cx ->
      OK (wellTypedExpr (cx, FALSE, BOOL))
      | _ -> FAIL)
    | exRecordProjection (prf, f) ->
      (case checkWTExprOfRecordType prf of OK (cx, e, fS, tS) ->
      (case checkIndex f fS of OK i ->
      OK (wellTypedExpr (cx, e DOTr f, tS!i))
      | _ -> FAIL)
      | _ -> FAIL)
    | exTupleProjection (prf, pi) ->
      (case checkWTExprOfProductType prf of OK (cx, e, tS) ->
      if pi <= length tS then
      OK (wellTypedExpr (cx, e DOTt pi, tS!(pi-1)))
      else   FAIL
      | _ -> FAIL)
    | exRelaxator prf ->
      (case checkWFSubType prf of OK (cx, t, r) ->
      OK (wellTypedExpr (cx, RELAX r, t\r --> t))
      | _ -> FAIL)
    | exQuotienter prf ->
      (case checkWFQuotientType prf of OK (cx, t, q) ->
      OK (wellTypedExpr (cx, QUOTIENT q, t --> t/q))
      | _ -> FAIL)
    | exNegation prf ->
      (case checkWTExpr prf of OK (cx, e, boolean) ->
      OK (wellTypedExpr (cx, ~~ e, BOOL))
      | _ -> FAIL)
    | exApplication (prf1, prf2) ->
      (case checkWTExprOfArrowType prf1 of OK (cx, e1, t1, t2) ->
      (case checkWTExprWithContextAndType cx t1 prf2 of OK e2 ->
      OK (wellTypedExpr (cx, e1 @ e2, t2))
      | _ -> FAIL)
      | _ -> FAIL)
    | exEquation (prf1, prf2) ->
      (case checkWTExpr prf1 of OK (cx, e1, t) ->
      (case checkWTExprWithContextAndType cx t prf2 of OK e2 ->
      OK (wellTypedExpr (cx, e1 == e2, BOOL))
      | _ -> FAIL)
      | _ -> FAIL)
    | exInequation (prf1, prf2) ->
      (case checkWTEquation prf1 of OK (cx, e1, e2) ->
      OK (wellTypedExpr (cx, e1 ~== e2, BOOL))
      | _ -> FAIL)


%%%%%%%%%%%%%%%%% HERE %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


    | exRecordUpdate (prf1, prf2) ->
      (case checkWTExpr prf1 of OK (cx, e1, t1) ->
      (case checkWTExprWithContext cx prf2 of OK (e2, t2) ->
      (case checkRecordTypeUnion t1 t2 of OK t ->
      OK (wellTypedExpr (cx, e1 <<< e2, t))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | exRestriction (prfTy, prfEx, prfTh) ->
      (case checkWFSubType prfTy of OK (cx, t, r) ->
      (case checkWTExprWithContext cx prfEx of OK (e, t1) ->
      if t1 = t then
      (case checkTheoremWithContextAndFormula cx (r @ e) prfTh of OK () ->
      OK (wellTypedExpr (cx, RESTRICT r e, t \ r))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | exChoice (prfTy, prfEx, prfTh) ->
      (case checkWFQuotientType prfTy of OK (cx, t, q) ->
      (case checkWTExprWithContext cx prfEx of OK (e, arrow (t0, t1)) ->
      if t0 = t then
      (case checkTheoremCongruence cx e q prfTh of OK () ->
      OK (wellTypedExpr (cx, CHOOSE q e, t/q --> t1))
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | exConjunction prf ->
      (case checkWTExpr prf of
         OK (cx, ifThenElse (e1, e2, nullary falsE), boolean) ->
      OK (wellTypedExpr (cx, e1 &&& e2, BOOL))
      | _ -> FAIL)
    | exDisjunction prf ->
      (case checkWTExpr prf of
         OK (cx, ifThenElse (e1, nullary truE, e2), boolean) ->
      OK (wellTypedExpr (cx, e1 ||| e2, BOOL))
      | _ -> FAIL)
    | exImplication prf ->
      (case checkWTExpr prf of
         OK (cx, ifThenElse (e1, e2, nullary truE), boolean) ->
      OK (wellTypedExpr (cx, e1 ==> e2, BOOL))
      | _ -> FAIL)
    | exEquivalence (prf1, prf2) ->
      (case checkWTExpr prf1 of OK (cx, e1, boolean) ->
      (case checkWTExprWithContext cx prf2 of OK (e2, boolean) ->
      OK (wellTypedExpr (cx, e1 <==> e2, BOOL))
      | _ -> FAIL)
      | _ -> FAIL)
    | exRecord (prf, prfS) ->
      (case checkWFRecordType prf of OK (cx, fS, tS) ->
      (case checkWTExprsWithContextAndTypes cx tS prfS of OK eS ->
      OK (wellTypedExpr (cx, RECORD fS eS, TRECORD fS tS))
      | _ -> FAIL)
      | _ -> FAIL)
    | exTuple (prf, prfS) ->
      (case checkWFProductType prf of OK (cx, tS) ->
      (case checkWTExprsWithContextAndTypes cx tS prfS of OK eS ->
      OK (wellTypedExpr (cx, TUPLE eS, PRODUCT tS))
      | _ -> FAIL)
      | _ -> FAIL)
    | exAbstraction (prf, nVars) ->
      (case checkWTExpr prf of OK (cx, e, t) ->
      (case checkLastNVars cx nVars of OK (cx0, vS, tS) ->
      OK (wellTypedExpr (cx0, FNN vS tS e, PRODUCT tS --> t))
      | _ -> FAIL)
      | _ -> FAIL)
    | exUniversal (prf, nVars) ->
      (case checkWTExpr prf of OK (cx, e, t) ->
      (case checkLastNVars cx nVars of OK (cx0, vS, tS) ->
      OK (wellTypedExpr (cx0, FAA vS tS e, PRODUCT tS --> t))
      | _ -> FAIL)
      | _ -> FAIL)
    | exExistential (prf, nVars) ->
      (case checkWTExpr prf of OK (cx, e, t) ->
      (case checkLastNVars cx nVars of OK (cx0, vS, tS) ->
      OK (wellTypedExpr (cx0, EXX vS tS e, PRODUCT tS --> t))
      | _ -> FAIL)
      | _ -> FAIL)
    | exExistential1 (prf, nVars) ->
      (case checkWTExpr prf of OK (cx, e, t) ->
      (case checkLastNVars cx nVars of OK (cx0, vS, tS) ->
      OK (wellTypedExpr (cx0, EXX1 vS tS e, PRODUCT tS --> t))
      | _ -> FAIL)
      | _ -> FAIL)
    | exIfThenElse (prf0, prf1, prf2) ->
      (case checkWTExpr prf0 of OK (cx, e0, boolean) ->
      (case checkWTExpr prf1 of OK (cx1, e1, t) ->
      (case checkExtraAxiom cx cx1 of OK (an1, tvS1, ea1) ->
      if tvS1 = empty
      && ea1 = e0 then
      (case checkWTExpr prf2 of OK (cx2, e2, t2) ->
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
      (case checkWFContext prfCx of OK cx ->
      (case checkOpDecl cx o of OK (tvS, t) ->
      (case checkWFTypesWithContext cx prfTyS of OK tS ->
      (case checkTypeSubstitution tvS tS of OK tsbs ->
      OK (wellTypedExpr (cx, OPP o tS, typeSubstInType tsbs t))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | exEmbedder0 (prf, c) ->
      (case checkWFSumType prf of OK (cx, cS, t?S) ->
      (case checkConstructorType? (SUM cS t?S) c of OK None ->
      OK (wellTypedExpr (cx, EMBED (SUM cS t?S) c, SUM cS t?S))
      | _ -> FAIL)
      | _ -> FAIL)
    | exEmbedder1 (prf, c) ->
      (case checkWFSumType prf of OK (cx, cS, t?S) ->
      (case checkConstructorType? (SUM cS t?S) c of OK (Some ti) ->
      OK (wellTypedExpr (cx, EMBED (SUM cS t?S) c, ti --> SUM cS t?S))
      | _ -> FAIL)
      | _ -> FAIL)
    | exCase (prfTgt, prfPS, prfExh, prfES) ->
      (case checkWTExpr prfTgt of OK (cx, e, t) ->
      (case checkSequence (map (checkWTPattWithContextAndType cx t, prfPS)) of
         OK pS ->
      let n:Nat = length pS in
      if n > 0 then
      let caseMatches:Expressions = seqSuchThat (fn(i:Nat) ->
        if i < n then Some (let (vS,tS) = pattVarsWithTypes (pS!i) in
                            EXX vS tS (pattAssumptions (pS!i, e)))
        else None) in
      (case checkTheoremWithContextAndFormula cx (disjoinAll caseMatches) prfExh of OK () ->
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
      (case checkWTExpr prfEx of OK (cx1, e, t) ->
      if cx1 = cx ++ multiVarDecls (vS, tS) then
      OK (wellTypedExpr (cx, LETDEF vS tS eS e, t))
      else   FAIL
      | _ -> FAIL)
      else   FAIL
      | _ -> FAIL)
    | exNonRecursiveLet prf ->
      (case checkWTExpr prf of OK (cx, casE (e, pS, eS), t) ->
      if length pS = 1
      && length eS = 1 then
      OK (wellTypedExpr (cx, LET (first pS) e (first eS), t))
      else   FAIL
      | _ -> FAIL)
    | exEquivalentTypes (prfEx, prfTE) ->
      (case checkWTExpr prfEx of OK (cx, e, t) ->
      (case checkTypeEquivWithContext cx prfTE of OK (t0, t1) ->
      if t0 = t then
      OK (wellTypedExpr (cx, e, t1))
      else FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | exAlphaAbstraction (prf, oldV, newV) ->
      (case checkWTExpr prf of OK (cx, binding (abstraction, vS, tS, e), t) ->
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
      (case checkWTExpr prf of OK (cx, casE (e, pS, eS), t) ->
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
      (case checkWTExpr prf of OK (cx, recursiveLet (vS, tS, eS, e), t) ->
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
      (case checkWFType prf of OK (cx, t) ->
      if ~(v in? contextVars cx) then
      OK (wellTypedPatt (cx, PVAR v t, t))
      else   FAIL
      | _ -> FAIL)
    | paEmbedding0 (prf, c) ->
      (case checkWFSumType prf of OK (cx, cS, t?S) ->
      (case checkConstructorType? (SUM cS t?S) c of OK None ->
      OK (wellTypedPatt (cx, PEMBE (SUM cS t?S) c, SUM cS t?S))
      | _ -> FAIL)
      | _ -> FAIL)
    | paEmbedding1 (prfTy, prfPa, c) ->
      (case checkWFSumType prfTy of OK (cx, cS, t?S) ->
      (case checkConstructorType? (SUM cS t?S) c of OK (Some ti) ->
      (case checkWTPattWithContextAndType cx ti prfPa of OK p ->
      OK (wellTypedPatt (cx, PEMBED (SUM cS t?S) c p, SUM cS t?S))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | paRecord (prf, prfS) ->
      (case checkWFRecordType prf of OK (cx, fS, tS) ->
      (case checkWTPattsWithContextAndTypes cx tS prfS of OK pS ->
      OK (wellTypedPatt (cx, PRECORD fS pS, TRECORD fS tS))
      | _ -> FAIL)
      | _ -> FAIL)
    | paTuple (prf, prfS) ->
      (case checkWFProductType prf of OK (cx, tS) ->
      (case checkWTPattsWithContextAndTypes cx tS prfS of OK pS ->
      OK (wellTypedPatt (cx, PTUPLE pS, PRODUCT tS))
      | _ -> FAIL)
      | _ -> FAIL)
    | paAlias (prf, v) ->
      (case checkWTPatt prf of OK (cx, p, t) ->
      if ~(v in? contextVars cx) then
      OK (wellTypedPatt (cx, AS v t p, t))
      else   FAIL
      | _ -> FAIL)
    | paEquivalentTypes (prfPa, prfTE) ->
      (case checkWTPatt prfPa of OK (cx, p, t) ->
      (case checkTypeEquivWithContext cx prfTE of OK (t0, t1) ->
      if t0 = t then
      OK (wellTypedPatt (cx, p, t1))
      else FAIL
      | _ -> FAIL)
      | _ -> FAIL)

    %%%%%%%%%% theorems:
    | thAxiom (prfCx, prfTyS, tvS, an) ->
      (case checkWFContext prfCx of OK cx ->
      (case checkAxiom cx an of OK (tvS, e) ->
      (case checkWFTypesWithContext cx prfTyS of OK tS ->
      (case checkTypeSubstitution tvS tS of OK tsbs ->
      OK (theoreM (cx, typeSubstInExpr tsbs e))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | thOpDef (prfCx, prfTyS, o) ->
      (case checkWFContext prfCx of OK cx ->
      (case checkOpDef cx o of OK (tvS, e) ->
      (case checkWFTypesWithContext cx prfTyS of OK tS ->
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
      (case checkTypeEquivWithContext cx prfTE of OK (t1, t2) ->
      (case typeSubstInExprAt (e, t1, t2, pos) of OK newE ->
      OK (theoreM (cx, newE))
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | thBoolean (prf, v) ->
      (case checkWTExpr prf of OK (cx, e, arrow (boolean, boolean)) ->
      if ~(v in? exprFreeVars e) then
      OK (theoreM (cx, e @ TRUE &&& e @ FALSE <==> FA v BOOL e @ VAR v))
      else   FAIL
      | _ -> FAIL)
    | thCongruence (prf1, prf2, prf3) ->
      (case checkWTExpr prf1 of OK (cx, e1, t) ->
      (case checkWTExprWithContextAndType cx t prf2 of OK e2 ->
      (case checkWTExprWithContext cx prf3 of OK (e, arrow (t0, t1)) ->
      if t0 = t then
      OK (theoreM (cx, e1 == e2 ==> e @ e1 == e @ e2))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
      | _ -> FAIL)
    | thExtensionality (prf1, prf2, v) ->
      (case checkWTExpr prf1 of OK (cx, e1, arrow (t, t1)) ->
      (case checkWTExprWithContextAndType cx (t --> t1) prf2 of OK e2 ->
      if ~(v in? exprFreeVars e1 \/ exprFreeVars e2) then
      OK (theoreM (cx, e1 == e2 <==>
                       FA v t e1 @ VAR v == e2 @ VAR v))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | thAbstraction prf ->
      (case checkWTExpr prf of
         OK (cx, binary (equation, binding (abstraction, vS, tS, e),
                                   nary (tuple, eS)), t) ->
      (case checkExprSubstitution vS eS of OK esbs ->
      if exprSubstOK? (e, esbs) then
      OK (theoreM (cx, FNN vS tS e @ TUPLE eS == exprSubst esbs e))
      else   FAIL
      | _ -> FAIL)
      | _ -> FAIL)
    | thIfThenElse (prf0, prf1, prf2) ->
      (case checkWTExpr prf0 of OK (cx, ifThenElse (e0, e1, e2), t) ->
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
      (case checkWFRecordType prf of OK (cx, fS, tS) ->
      if noRepetitions? (v |> vS)
      && length vS = length tS then
      OK (theoreM (cx, FA v (TRECORD fS tS)
                          (EXX1 vS tS (VAR v == RECORD fS (map (VAR, vS))))))
      else   FAIL
      | _ -> FAIL)
    | thTuple (prf, v, vS) ->
      (case checkWFProductType prf of OK (cx, tS) ->
      if noRepetitions? (v |> vS)
      && length vS = length tS then
      OK (theoreM (cx, FA v (PRODUCT tS)
                          (EXX1 vS tS (VAR v == TUPLE (map (VAR, vS))))))
      else   FAIL
      | _ -> FAIL)
    | thRecordProjection (prf, f) ->
      (case checkWTExpr prf of
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
      (case checkWTExpr prf of OK (cx, nary (tuple, eS), nary (product, tS)) ->
      if i <= length eS then
      OK (theoreM (cx, (TUPLE eS) DOTt i == (eS!(i-1))))
      else   FAIL
      | _ -> FAIL)
    | thRecordUpdate1 (prf1, prf2, f) ->
      (case checkWTExpr prf1 of
         OK (cx, nary (record fS1, eS1), nary (record mustBeFS1, tS1)) ->
      if mustBeFS1 = fS1 then
      (case checkWTExprWithContext cx prf2 of
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
      (case checkWTExpr prf1 of
         OK (cx, nary (record fS1, eS1), nary (record mustBeFS1, tS1)) ->
      if mustBeFS1 = fS1 then
      (case checkWTExprWithContext cx prf2 of
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
      (case checkWFSumType prf of OK (cx, cS, t?S) ->
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
      (case checkWFSumType prf of OK (cx, cS, t?S) ->
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
      (case checkWFSumType prf of OK (cx, cS, t?S) ->
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
      (case checkWFSubType prf of OK (cx, t, r) ->
      OK (theoreM (cx, FA v (t\r) (r @ (RELAX r @ VAR v))))
      | _ -> FAIL)
    | thRelaxatorInjective (prf, v1, v2) ->
      (case checkWFSubType prf of OK (cx, t, r) ->
      if v1 ~= v2 then
      OK (theoreM (cx, FAA (seq2(v1,v2)) (seq2(t\r,t\r))
                           (VAR v1 ~== VAR v2 ==>
                            RELAX r @ VAR v1 ~== RELAX r @ VAR v2)))
      else   FAIL
      | _ -> FAIL)
    | thRelexatorSurjective (prf, v, v1) ->
      (case checkWFSubType prf of OK (cx, t, r) ->
      if v ~= v1 then
      OK (theoreM (cx, FA v t
                          (r @ VAR v ==>
                           EX v1 (t\r) (VAR v == RELAX r @ VAR v1))))
      else   FAIL
      | _ -> FAIL)
    | thRestriction (prf, v) ->
      (case checkWFSubType prf of OK (cx, t, r) ->
      OK (theoreM (cx, FA v (t\r) (RESTRICT r (RELAX r @ VAR v) == VAR v)))
      | _ -> FAIL)
    | thQuotienterSurjective (prf, v, v1) ->
      (case checkWFQuotientType prf of OK (cx, t, q) ->
      if v ~= v1 then
      OK (theoreM (cx, FA v (t/q) (EX v1 t (QUOTIENT q @ VAR v1 == VAR v))))
      else   FAIL
      | _ -> FAIL)
    | thQuotienterEquivClass (prf, v1, v2) ->
      (case checkWFQuotientType prf of OK (cx, t, q) ->
      if v1 ~= v2 then
      OK (theoreM (cx, FAA (seq2(v1,v2)) (seq2(t,t))
                           (q @ PAIR (VAR v1) (VAR v2) <==>
                            QUOTIENT q @ VAR v1 == QUOTIENT q @ VAR v2)))
      else   FAIL
      | _ -> FAIL)
    | thChoice (prf, v) ->
      (case checkWTExpr prf of
         OK (cx, binary (choice, q, e),
                 arrow (subQuot (quotienT, t, mustBeQ), t1)) ->
      if mustBeQ = q
      && ~(v in? exprFreeVars e) then
      OK (theoreM (cx, FA v t
                          (CHOOSE q e @ (QUOTIENT q @ VAR v) == e @ VAR v)))
      else   FAIL
      | _ -> FAIL)
    | thCase (prf, prfS) ->
      (case checkWTExpr prf of OK (cx, casE (e, pS, eS), t) ->
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
      (case checkWTExpr prfEx of OK (cx, recursiveLet (vS, tS, eS, e), t) ->
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
      (case checkWFContext prf of OK cx ->
      OK (theoreM (cx, TRUE <==> FN v BOOL (VAR v) == FN v BOOL (VAR v)))
      | _ -> FAIL)
    | thAbbrevFalse (prf, v) ->
      (case checkWFContext prf of OK cx ->
      OK (theoreM (cx, FALSE <==> FN v BOOL (VAR v) == FN v BOOL TRUE))
      | _ -> FAIL)
    | thAbbrevNegation prf ->
      (case checkWTExpr prf of OK (cx, unary (negation, e), boolean) ->
      OK (theoreM (cx, ~~e <==> IF e FALSE TRUE))
      | _ -> FAIL)
    | thAbbrevInequation prf ->
      (case checkWTExpr prf of OK (cx, binary (inequation, e1, e2), boolean) ->
      OK (theoreM (cx, (e1 ~== e2) <==> ~~(e1 == e2)))
      | _ -> FAIL)
    | thAbbrevConjunction prf ->
      (case checkWTExpr prf of OK (cx, binary (conjunction, e1, e2), boolean) ->
      OK (theoreM (cx, e1 &&& e2 <==> IF e1 e2 FALSE))
      | _ -> FAIL)
    | thAbbrevDisjunction prf ->
      (case checkWTExpr prf of OK (cx, binary (disjunction, e1, e2), boolean) ->
      OK (theoreM (cx, e1 ||| e2 <==> IF e1 TRUE e2))
      | _ -> FAIL)
    | thAbbrevImplication prf ->
      (case checkWTExpr prf of OK (cx, binary (implication, e1, e2), boolean) ->
      OK (theoreM (cx, e1 ==> e2 <==> IF e1 e2 TRUE))
      | _ -> FAIL)
    | thAbbrevEquivalence prf ->
      (case checkWTExpr prf of OK (cx, binary (equivalence, e1, e2), boolean) ->
      OK (theoreM (cx, (e1 <==> e2) == (e1 == e2)))
      | _ -> FAIL)
    | thAbbrevUniversal prf ->
      (case checkWTExpr prf of OK (cx, binding (universal, vS, tS, e), boolean) ->
      OK (theoreM (cx, FAA vS tS e <==> FNN vS tS e == FNN vS tS TRUE))
      | _ -> FAIL)
    | thAbbrevExistential prf ->
      (case checkWTExpr prf of OK (cx, binding (existential, vS, tS, e), boolean) ->
      OK (theoreM (cx, EXX vS tS e <==> ~~(FAA vS tS (~~e))))
      | _ -> FAIL)
    | thAbbrevExistential1 (prf, vS1) ->
      (case checkWTExpr prf of OK (cx, binding (existential1, vS, tS, e), boolean) ->
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
      (case checkWTExpr prf of OK (cx, nonRecursiveLet (p, e, e1), t) ->
      OK (theoreM (cx, LET p e e1 == CASE e (singleton p) (singleton e1)))
      | _ -> FAIL)






  %%% TO CHECK..........

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

  op checkCaseBranchExpr :
     Context -> Context -> Expression -> Expression -> Proof ->
     MayFail (Expression * Type)
  def checkCaseBranchExpr cx varCx negAsm posAsm prf =
    case checkWTExpr prf of OK (cx1, e, t) ->
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

  op checkTheoremEquation : Proof -> MayFail (Context * Expression * Expression)
  def checkTheoremEquation prf =
    case checkTheorem prf of
      | OK (cx, binary (equation, e1, e2)) -> OK (cx, e1, e2)
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


  %%% PERHAPS NOT NEEDED:

  (* Like previous op but also check that context coincides with
  argument. Only return expressions, if successful. *)

  op checkWTEquationWithContext :
     Context -> Proof -> MayFail (Expression * Expression)
  def checkWTEquationWithContext cx prf =
    case checkWTEquation prf of
      | OK (mustBe_cx, e1, e2) ->
        if mustBe_cx = cx then OK (e1, e2) else FAIL
      | _ -> FAIL

endspec
