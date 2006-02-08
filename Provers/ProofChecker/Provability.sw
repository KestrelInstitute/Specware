spec

  % API private all

  import Judgements, BasicAbbreviations, Substitutions

  (* It is convenient to define a meta type for rules, so that we can more
  easily refer to them. The names of the rules are the same used in LD. *)

  type InferenceRule =
    % well-formed contexts:
    | cxMT
    | cxTdec
    | cxOdec
    | cxTdef
    | cxAx
    | cxLem
    | cxTVdec
    | cxVdec
    % well-formed specs ("spec" is disallowed):
    | speC
    % well-formed types:
    | tyBool
    | tyVar
    | tyInst
    | tyArr
    | tyRec
    | tySum
    | tyRestr
    | tyQuot
    % type equivalence:
    | teDef
    | teRefl
    | teSymm
    | teTrans
    | teInst
    | teArr
    | teRec
    | teSum
    | teRestr
    | teQuot
    | teRecOrd
    | teSumOrd
    % subtyping:
    | stRestr
    | stRefl
    | stArr
    | stRec
    | stSum
    | stTE
    % well-typed expressions:
    | exVar
    | exOp
    | exApp
    | exAbs
    | exEq
    | exIf
    | exIf0
    | exThe
    | exProj
    | exEmbed
    | exQuot
    | exSuper
    | exSub
    | exAbsAlpha
    % theorems:
    | thAx
    | thRefl
    | thSymm
    | thTrans
    | thOpSubst
    | thAppSubst
    | thAbsSubst
    | thIfSubst
    | thTheSubst
    | thProjSubst
    | thEmbedSubst
    | thQuotSubst
    | thSubst
    | thBool
    | thExt
    | thAbs
    | thIf
    | thThe
    | thRec
    | thEmbSurj
    | thEmbDist
    | thEmbInj
    | thQuotSurj
    | thQuotEqCls
    | thProjSub
    | thEmbSub
    | thSub

  (* The goal is to define a predicate provable? on judgements. This predicate
  is the minimum one satisfying all the inference rules. So, we define an
  auxiliary predicate satisfiesInferenceRule? that says whether a predicate on
  judgements satisfies a given rule. *)

  op satisfiesInferenceRule? : (Judgement -> Boolean) -> InferenceRule -> Boolean
  def satisfiesInferenceRule? pj = fn

    %%%%%%%%%% well-formed contexts:
    | cxMT ->
      pj (wellFormedContext empty)
    | cxTdec ->
      (fa (cx:Context, tn:TypeName, n:Nat)
         pj (wellFormedContext cx)
      && ~(tn in? contextTypes cx)
      => pj (wellFormedContext (cx <| typeDeclaration (tn, n))))
    | cxOdec ->
      (fa (cx:Context, o:Operation, tvS:TypeVariables, t:Type)
         pj (wellFormedContext cx)
      && ~(o in? contextOps cx)
      && pj (wellFormedType (cx ++ multiTypeVarDecls tvS, t))
         (* Distinctness of tvS is in the syntax in LD. We do not need to add
         it to this inference rule because it is a meta theorem. *)
      => pj (wellFormedContext (cx <| opDeclaration (o, tvS, t))))
    | cxTdef ->
      (fa (cx:Context, tn:TypeName, n:Nat, tvS:TypeVariables, t:Type)
         pj (wellFormedContext cx)
      && typeDeclaration (tn, n) in? cx
      && ~(contextDefinesType? (cx, tn))
      && pj (wellFormedType (cx ++ multiTypeVarDecls tvS, t))
      && length tvS = n
         (* Distinctness of tvS is in the syntax in LD. We do not need to add
         it to this inference rule because it is a meta theorem. *)
      => pj (wellFormedContext (cx <| typeDefinition (tn, tvS, t))))
    | cxAx ->
      (fa (cx:Context, tvS:TypeVariables, e:Expression, an:AxiomName)
         pj (wellFormedContext cx)
      && pj (wellTypedExpr (cx ++ multiTypeVarDecls tvS, e, BOOL))
         (* In LD, axioms are unnamed. Here, we require distinct axiom names in
         well-formed contexts. *)
      && ~(an in? contextAxioms cx)
         (* Distinctness of tvS is in the syntax in LD. We do not need to add
         it to this inference rule because it is a meta theorem. *)
      => pj (wellFormedContext (cx <| axioM (an, tvS, e))))
    | cxLem ->
      (fa (cx:Context, tvS:TypeVariables, e:Expression, ln:LemmaName)
         pj (wellFormedContext cx)
      && pj (theoreM (cx ++ multiTypeVarDecls tvS, e))
         (* In LD, lemmas are unnamed. Here, we require distinct lemma names in
         well-formed contexts. *)
      && ~(ln in? contextLemmas cx)
         (* Distinctness of tvS is in the syntax in LD. We do not need to add
         it to this inference rule because it is a meta theorem. *)
      => pj (wellFormedContext (cx <| lemma (ln, tvS, e))))
    | cxTVdec ->
      (fa (cx:Context, tv:TypeVariable)
         pj (wellFormedContext cx)
      && ~(tv in? contextTypeVars cx)
      => pj (wellFormedContext (cx <| typeVarDeclaration tv)))
    | cxVarDecl ->
      (fa (cx:Context, v:Variable, t:Type)
         pj (wellFormedContext cx)
      && ~(v in? contextVars cx)
      && pj (wellFormedType (cx, t))
      => pj (wellFormedContext (cx <| varDeclaration (v, t))))

    %%%%%%%%%% well-formed specs:
    | speC ->
      (fa (cx:Context)
         pj (wellFormedContext cx)
         (* As explained in spec Contexts, here we put absence of (type)
         variable declarations in this inference rule. *)
      && ~(exists? (embed? typeVarDeclaration) cx)
      && ~(exists? (embed? varDeclaration) cx)
      => pj (wellFormedSpec cx))

    %%%%%%%%%% well-formed types:
    | tyBool ->
      (fa (cx:Context)
         pj (wellFormedContext cx)
      => pj (wellFormedType (cx, BOOL)))
    | tyVar ->
      (fa (cx:Context, tv:TypeVariable)
         pj (wellFormedContext cx)
      && tv in? contextTypeVars cx
      => pj (wellFormedType (cx, VAR tv)))
    | tyInst ->
      (fa (cx:Context, tn:TypeName, n:Nat, tS:Types)
         pj (wellFormedContext cx)
      && typeDeclaration (tn, n) in? cx
      && length tS = n
      && (fa(i:Nat) i < n =>
            pj (wellFormedType (cx, tS@i)))
      => pj (wellFormedType (cx, TYPE (tn, tS))))
    | tyArr ->
      (fa (cx:Context, t1:Type, t2:Type)
         pj (wellFormedType (cx, t1))
      && pj (wellFormedType (cx, t2))
      => pj (wellFormedType (cx, t1 --> t2)))
    | tyRec ->
      (fa (cx:Context, fS:Fields, tS:Types)
         pj (wellFormedContext cx)
         (* In LD, the syntax includes that fS are distinct and that fS and tS
         have the same length. Here, we add them to this inference rule. *)
      && noRepetitions? fS
      && length fS = length tS
      && (fa(i:Nat) i < length fS =>
            pj (wellFormedType (cx, tS@i)))
      => pj (wellFormedType (cx, RECORD (fS, tS))))
    | tySum ->
      (fa (cx:Context, cS:Constructors, tS:Types)
         (* In LD, the syntax includes that cS are distinct and that cS and tS
         have the same non-zero length. Here, we add them to this inference
         rule. *)
         noRepetitions? cS
      && length cS = length tS
      && length cS > 0
      && (fa(i:Nat) i < length cS =>
            pj (wellFormedType (cx, tS@i)))
      => pj (wellFormedType (cx, SUM (cS, tS))))
    | tyRestr ->
      (fa (cx:Context, r:Expression, t:Type)
         pj (wellTypedExpr (cx, r, t --> BOOL))
      && exprFreeVars r = empty
      => pj (wellFormedType (cx, t\r)))
    | tyQuot ->
      (fa (cx:Context, v:Variable, v1:Variable, v2:Variable,
           u1:Variable, u2:Variable, u3:Variable, t:Type, q:Expression)
         pj (theoreM (cx, FA (v, t, q @ PAIR (t, t, VAR v, VAR v))))
      && pj (theoreM (cx, FA2 (v1, t, v2, t,
                               q @ PAIR (t, t, VAR v1, VAR v2)
                               ==>
                               q @ PAIR (t, t, VAR v2, VAR v1))))
      && pj (theoreM (cx, FA3 (u1, t, u2, t, u3, t,
                               q @ PAIR (t, t, VAR u1, VAR u2)
                               &&&
                               q @ PAIR (t, t, VAR u2, VAR u3)
                               ==>
                               q @ PAIR (t, t, VAR u1,  VAR u3))))
      && v1 ~= v2 && u1 ~= u2 && u2 ~= u3 && u1 ~= u3
      && exprFreeVars q = empty
      => pj (wellFormedType (cx, t/q)))

    %%%%%%%%%% type equivalence:
    | teDef ->
      (fa (cx:Context, tn:TypeName, tvS:TypeVariables, t:Type,
           tS:Types, tsbs:TypeSubstitution)
         pj (wellFormedContext cx)
      && typeDefinition (tn, tvS, t) in? cx
      && (fa(i:Nat) i < length tvS =>
            pj (wellFormedType (cx, tS@i)))
      && isTypeSubstFrom? (tsbs, tvS, tS)
      => pj (typeEquivalence (cx, TYPE (tn, tS), typeSubstInType tsbs t)))
    | teRefl ->
      (fa (cx:Context, t:Type)
         pj (wellFormedType (cx, t))
      => pj (typeEquivalence (cx, t, t)))
    | teSymm ->
      (fa (cx:Context, t1:Type, t2:Type)
         pj (typeEquivalence (cx, t1, t2))
      => pj (typeEquivalence (cx, t2, t1)))
    | teTrans ->
      (fa (cx:Context, t1:Type, t2:Type, t3:Type)
         pj (typeEquivalence (cx, t1, t2))
      && pj (typeEquivalence (cx, t2, t3))
      => pj (typeEquivalence (cx, t1, t3)))
    | teInst ->
      (fa (cx:Context, tn:TypeName, tS:Types, tS1:Types)
         pj (wellFormedType (cx, TYPE (tn, tS)))
      && length tS = length tS1
      && (fa(i:Nat) i < length tS =>
            pj (typeEquivalence (cx, tS@i, tS1@i)))
      => pj (typeEquivalence (cx, TYPE (tn, tS), TYPE (tn, tS1))))
    | teArr ->
      (fa (cx:Context, t:Type, s:Type, t1:Type, s1:Type)
         pj (typeEquivalence (cx, t, t1))
      && pj (typeEquivalence (cx, s, s1))
      => pj (typeEquivalence (cx, t --> s, t1 --> s1)))
    | teRec ->
      (fa (cx:Context, tS:Types, tS1:Types, fS:Fields)
         pj (wellFormedContext cx)
         (* In LD, the syntax includes that fS are distinct and that fS and tS
         and tS1 have the same length. Here, we add them to this inference
         rule. *)
      && noRepetitions? fS
      && length fS = length tS
      && length tS = length tS1
      && (fa(i:Nat) i < length tS =>
            pj (typeEquivalence (cx, tS@i, tS1@i)))
      => pj (typeEquivalence (cx, RECORD (fS, tS), RECORD (fS, tS1))))
    | teSum ->
      (fa (cx:Context, tS:Types, tS1:Types, cS:Constructors)
         (* In LD, the syntax includes that cS are distinct and that cS and tS
         and tS1 have the same non-zero length. Here, we add them to this
         inference rule. *)
         noRepetitions? cS
      && length cS = length tS
      && length tS = length tS1
      && length cS > 0
      && (fa(i:Nat) i < length tS =>
            pj (typeEquivalence (cx, tS@i, tS1@i)))
      => pj (typeEquivalence (cx, SUM (cS, tS), SUM (cS, tS1))))
    | teRestr ->
      (fa (cx:Context, t:Type, r:Expression, t1:Type, r1:Expression)
         pj (wellFormedType (cx, t\r))
      && pj (typeEquivalence (cx, t, t1))
      && pj (theoreM (cx, r == r1))
      && exprFreeVars r1 = empty
      => pj (typeEquivalence (cx, t\r, t1\r1)))
    | teQuot ->
      (fa (cx:Context, t:Type, q:Expression, t1:Type, q1:Expression)
         pj (wellFormedType (cx, t/q))
      && pj (typeEquivalence (cx, t, t1))
      && pj (theoreM (cx, q == q1))
      && exprFreeVars q1 = empty
      => pj (typeEquivalence (cx, t/q, t1/q1)))
    | teRecOrd ->
      (fa (cx:Context, fS:Fields, tS:Types, prm:Permutation)
         pj (wellFormedType (cx, RECORD (fS, tS)))
         (* In LD, the syntax includes that fS and tS have the same length.
         Here, we need to add it to this inference rule for the application
         of op permute to be well-typed. There is no need to require fS to be
         distinct, because it is a meta theorem. *)
      && length fS = length tS
      && length prm = length fS
      => pj (typeEquivalence (cx, RECORD (fS, tS),
                                  RECORD (permute(fS,prm), (permute(tS,prm))))))
    | teSumOrd ->
      (fa (cx:Context, cS:Constructors, tS:Types, prm:Permutation)
         pj (wellFormedType (cx, SUM (cS, tS)))
         (* In LD, the syntax includes that cS and tS have the same length.
         Here, we need to add it to this inference rule for the application
         of op permute to be well-typed. There is no need to require cS to be
         distinct and non-zero, because it is a meta theorem. *)
      && length cS = length tS
      && length prm = length cS
      => pj (typeEquivalence (cx, SUM (cS, tS),
                                  SUM (permute(cS,prm), permute(tS,prm)))))

    %%%%%%%%%% subtyping:
    | stRestr ->
      (fa (cx:Context, t:Type, r:Expression)
         pj (wellFormedType (cx, t\r))
      => pj (subType (cx, t\r, r, t)))
    | stRefl ->
      (fa (cx:Context, t:Type, r:Expression, v:Variable)
         pj (wellFormedType (cx, t))
      && r = FN (v, t, TRUE)
      => pj (subType (cx, t, r, t)))
    | stArr ->
      (fa (cx:Context, t:Type, t1:Type, t2:Type, r:Expression,
           v:Variable, v1:Variable, r1:Expression)
         pj (wellFormedType (cx, t))
      && pj (subType (cx, t1, r, t2))
      && v ~= v1
      && r1 = FN (v, t --> t2, FA (v1, t, r @ (VAR v @ VAR v1)))
      => pj (subType (cx, t --> t1, r1, t --> t2)))
    | stRec ->
      (fa (cx:Context, fS:Fields, tS:Types, rS:Expressions, tS1:Types,
           r:Expression, v:Variable, conjuncts:Expressions)
         pj (wellFormedType (cx, RECORD (fS, tS)))
         (* In LD, the syntax includes that fS and tS and tS1 have the same
         length. Here, it is a meta theorem but we need to add it to this
         inference rule for the application of @ on finite sequences to be
         well-typed. There is no need to require fS to be distinct, because
         it is a meta theorem and is not needed for meta well-typedness. *)
      && length fS = length tS
      && length tS = length tS1
      && length tS1 = length rS
      && (fa(i:Nat) i < length tS =>
            pj (subType (cx, tS@i, rS@i, tS1@i)))
      && conjuncts = seq (fn(i:Nat) ->
           if i < length fS then Some ((rS@i) @ DOT (VAR v, tS@i, fS@i))
           else None)
      && r = FN (v, RECORD (fS, tS1), ANDn conjuncts)
      => pj (subType (cx, RECORD (fS, tS), r, RECORD (fS, tS1))))
    | stSum ->
      (fa (cx:Context, cS:Constructors, tS:Types, rS:Expressions, tS1:Types,
           r:Expression, v:Variable, v1:Variable, disjuncts:Expressions)
         pj (wellFormedType (cx, SUM (cS, tS)))
         (* In LD, the syntax includes that cS and tS and tS1 have the same
         length. Here, it is a meta theorem but we need to add it to this
         inference rule for the application of @ on finite sequences to be
         well-typed. There is no need to require cS to be distinct and non-zero,
         because it is a meta theorem and is not needed for meta
         well-typedness. *)
      && length cS = length tS
      && length tS = length tS1
      && length tS1 = length rS
      && (fa(i:Nat) i < length cS =>
            pj (subType (cx, tS@i, rS@i, tS1@i)))
      && disjuncts = seq (fn(i:Nat) ->
           if i < length cS then
             Some (EX (v1, tS1@i,
                       VAR v == EMBED (SUM(cS,tS1), cS@i) @ VAR v1
                       &&&
                       (rS@i) @ VAR v1))
           else None)
      && r = FN (v, SUM (cS, tS1), ORn disjuncts)
      => pj (subType (cx, SUM (cS, tS), r, SUM (cS, tS1))))
    | stTE ->
      (fa (cx:Context, t1:Type, r:Expression, t2:Type, s1:Type, s2:Type)
         pj (subType (cx, t1, r, t2))
      && pj (typeEquivalence (cx, t1, s1))
      && pj (typeEquivalence (cx, t2, s2))
      => pj (subType (cx, s1, r, s2)))

    %%%%%%%%%% well-typed expressions:
    | exVar ->
      (fa (cx:Context, v:Variable, t:Type)
         pj (wellFormedContext cx)
      && varDeclaration (v,t) in? cx
      => pj (wellTypedExpr (cx, VAR v, t)))
    | exOp ->
      (fa (cx:Context, o:Operation, tvS:TypeVariables, t:Type, tS:Types,
           tsbs:TypeSubstitution)
         pj (wellFormedContext cx)
      && opDeclaration (o, tvS, t) in? cx
      && (fa(i:Nat) i < length tS =>
            pj (wellFormedType (cx, tS@i)))
      && isTypeSubstFrom? (tsbs, tvS, tS)
      => pj (wellTypedExpr (cx, OPI (o, tS), typeSubstInType tsbs t)))
    | exApp ->
      (fa (cx:Context, e1:Expression, t1:Type, t2:Type, e2:Expression)
         pj (wellTypedExpr (cx, e1, t1 --> t2))
      && pj (wellTypedExpr (cx, e2, t1))
      => pj (wellTypedExpr (cx, e1 @ e2, t2)))
    | exAbs ->
      (fa (cx:Context, v:Variable, t:Type, e:Expression, t1:Type)
         pj (wellTypedExpr (cx <| varDeclaration (v,t), e, t1))
      => pj (wellTypedExpr (cx, FN (v, t, e), t --> t1)))
    | exEq ->
      (fa (cx:Context, e1:Expression, e2:Expression, t:Type)
         pj (wellTypedExpr (cx, e1, t))
      && pj (wellTypedExpr (cx, e2, t))
      => pj (wellTypedExpr (cx, e1 == e2, BOOL)))
    | exIf ->
      (fa (cx:Context, e0:Expression, e1:Expression, e2:Expression, t:Type,
           an1:AxiomName, an2:AxiomName)
         pj (wellTypedExpr (cx, e0, BOOL))
      && pj (wellTypedExpr (cx <| axioM (an1, empty,    e0), e1, t))
      && pj (wellTypedExpr (cx <| axioM (an2, empty, ~~ e0), e2, t))
      => pj (wellTypedExpr (cx, IF (e0, e1, e2), t)))
    | exIf0 ->
      (fa (cx:Context, e0:Expression, e1:Expression, e2:Expression, t:Type)
         pj (wellTypedExpr (cx, e0, BOOL))
      && pj (wellTypedExpr (cx, e1, t))
      && pj (wellTypedExpr (cx, e2, t))
      => pj (wellTypedExpr (cx, IF (e0, e1, e2), t)))
    | exThe ->
      (fa (cx:Context, t:Type)
         pj (wellFormedType (cx, t))
      => pj (wellTypedExpr (cx, IOTA t, ((t --> BOOL) \ EX1q t) --> t)))
    | exProj ->
      (fa (cx:Context, fS:Fields, tS:Types, j:Nat)
         pj (wellFormedType (cx, RECORD (fS, tS)))
         (* In LD, the syntax includes that fS and tS have the same length.
         Here, we need to add it to this inference rule for the application
         of op @ on finite sequences to be well-typed. There is no need to
         require fS to be distinct, because it is a meta theorem. *)
      && length fS = length tS
      && j < length fS
      => pj (wellTypedExpr (cx, PROJECT (RECORD(fS,tS), fS@j),
                                RECORD(fS,tS) --> tS@j)))
    | exEmbed ->
      (fa (cx:Context, cS:Constructors, tS:Types, j:Nat)
         pj (wellFormedType (cx, SUM (cS, tS)))
         (* In LD, the syntax includes that cS and tS have the same length.
         Here, we need to add it to this inference rule for the application
         of op @ on finite sequences to be well-typed. There is no need to
         require cS to be distinct and non-zero, because it is a meta theorem. *)
      && length cS = length tS
      && j < length cS
      => pj (wellTypedExpr (cx, EMBED (SUM(cS,tS), cS@j),
                                tS@j --> SUM (cS, tS))))
    | exQuot ->
      (fa (cx:Context, t:Type, q:Expression)
         pj (wellFormedType (cx, t/q))
      => pj (wellTypedExpr (cx, QUOT (t/q), t --> t/q)))
    | exSuper ->
      (fa (cx:Context, e:Expression, t:Type, t1:Type, r:Expression)
         pj (wellTypedExpr (cx, e, t))
      && pj (subType (cx, t, r, t1))
      => pj (wellTypedExpr (cx, e, t1)))
    | exSub ->
      (fa (cx:Context, e:Expression, t:Type, t1:Type, r:Expression)
         pj (wellTypedExpr (cx, e, t1))
      && pj (subType (cx, t, r, t1))
      && pj (theoreM (cx, r @ e))
      => pj (wellTypedExpr (cx, e, t)))
    | exAlphaAbstraction ->
      (fa (cx:Context, v:Variable, t:Type, e:Expression, t1:Type, v1:Variable)
         pj (wellTypedExpr (cx, FN (v, t, e), t1))
      && v1 nin? exprFreeVars e \/ captVars v e
      => pj (wellTypedExpr (cx, FN (v1, t, exprSubst v (VAR v1) e), t1)))

    %%%%%%%%%% theorems:
    | thAx ->
      (fa (cx:Context, an:AxiomName, tvS:TypeVariables, e:Expression, tS:Types,
           tsbs:TypeSubstitution)
         pj (wellFormedContext cx)
      && axioM (an, tvS, e) in? cx
      && (fa(i:Nat) i < length tS =>
            pj (wellFormedType (cx, tS@i)))
      && isTypeSubstFrom? (tsbs, tvS, tS)
      => pj (theoreM (cx, typeSubstInExpr tsbs e)))
    | thRefl ->
      (fa (cx:Context, e:Expression, t:Type)
         pj (wellTypedExpr (cx, e, t))
      => pj (theoreM (cx, e == e)))
    | thSymm ->
      (fa (cx:Context, e1:Expression, e2:Expression)
         pj (theoreM (cx, e1 == e2))
      => pj (theoreM (cx, e2 == e1)))
    | thTrans ->
      (fa (cx:Context, e1:Expression, e2:Expression, e3:Expression)
         pj (theoreM (cx, e1 == e2))
      && pj (theoreM (cx, e2 == e3))
      => pj (theoreM (cx, e1 == e3)))
    | thOpSubst ->
      (fa (cx:Context, o:Operation, tS:Types, tS1:Types, t:Type)
         pj (wellTypedExpr (cx, OPI (o, tS), t))
      && length tS = length tS1
      && (fa(i:Nat) i < length tS =>
            pj (typeEquivalence (cx, tS@i, tS1@i)))
      => pj (theoreM (cx, OPI (o, tS) == OPI (o, tS1))))
    | thAppSubst ->
      (fa (cx:Context, e1:Expression, e2:Expression, t:Type,
           d1:Expression, d2:Expression)
         pj (wellTypedExpr (cx, e1 @ e2, t))
      && pj (theoreM (cx, e1 == d1))
      && pj (theoreM (cx, e2 == d2))
      => pj (theoreM (cx, e1 @ e2 == d1 @ d2)))
    | thAbsSubst ->
      (fa (cx:Context, v:Variable, t:Type, e:Expression, t1:Type, t2:Type)
         pj (wellTypedExpr (cx, FN (v, t, e), t2))
      && pj (typeEquivalence (cx, t, t1))
      => pj (theoreM (cx, FN (v, t, e) == FN (v, t1, e))))
    | thEqSubst ->
      (fa (cx:Context, e1:Expression, e2:Expression, t:Type,
           d1:Expression, d2:Expression)
         pj (wellTypedExpr (cx, e1 == e2, t))
      && pj (theoreM (cx, e1 == d1))
      && pj (theoreM (cx, e2 == d2))
      => pj (theoreM (cx, (e1 == e2) == (d1 == d2))))
    | thIfSubst ->
      (fa (cx:Context, e0:Expression, e1:Expression, e2:Expression, t:Type,
           an1:AxiomName, an2:AxiomName,
           d0:Expression, d1:Expression, d2:Expression)
         pj (wellTypedExpr (cx, IF (e0, e1, e2), t))
      && pj (theoreM (cx, e0 == d0))
      && pj (theoreM (cx <| axioM (an1, empty,    e0), e1 == d1))
      && pj (theoreM (cx <| axioM (an2, empty, ~~ e0), e2 == d2))
      => pj (theoreM (cx, IF (e0, e1, e2) == IF (d0, d1, d2))))
    | thTheSubst ->
      (fa (cx:Context, t:Type, t1:Type, t2:Type)
         pj (wellTypedExpr (cx, IOTA t, t2))
      && pj (typeEquivalence (cx, t, t1))
      => pj (theoreM (cx, IOTA t == IOTA t1)))
    | thProjSubst ->
      (fa (cx:Context, t:Type, t1:Type, f:Field, t2:Type)
         pj (wellTypedExpr (cx, PROJECT (t, f), t2))
      && pj (typeEquivalence (cx, t, t1))
         % it is a meta theorem that t and t1 are (equivalent to) product types
      => pj (theoreM (cx, PROJECT (t, f) == PROJECT (t1, f))))
    | thEmbedSubst ->
      (fa (cx:Context, t:Type, t1:Type, c:Constructor, t2:Type)
         pj (wellTypedExpr (cx, EMBED (t, c), t2))
      && pj (typeEquivalence (cx, t, t1))
         % it is a meta theorem that t and t1 are (equivalent to) sum types
      => pj (theoreM (cx, EMBED (t, c) == EMBED (t1, c))))
    | thQuotSubst ->
      (fa (cx:Context, t:Type, t1:Type, t2:Type)
         pj (wellTypedExpr (cx, QUOT t, t2))
      && pj (typeEquivalence (cx, t, t1))
         % it is a meta theorem that t and t1 are (equivalent to) quotient types
      => pj (theoreM (cx, QUOT t == QUOT t1)))
    | thSubst ->
      (fa (cx:Context, e:Expression, e1:Expression)
         pj (theoreM (cx, e))
      && pj (theoreM (cx, e == e1))
      => pj (theoreM (cx, e1)))
    | thBool ->
      (fa (cx:Context, v:Variable, v1:Variable)
         pj (wellFormedContext cx)
      && v ~= v1
      => pj (theoreM (cx, FA (v, BOOL --> BOOL,
                              VAR v @ TRUE &&& VAR v @ FALSE
                              <==>
                              FA (v1, BOOL, VAR v @ VAR v1)))))
    | thExt ->
      (fa (cx:Context, t:Type, t1:Type, v:Variable, v1:Variable, v2:Variable)
         pj (wellFormedType (cx, t --> t1))
      && v ~= v1 && v1 ~= v2 && v2 ~= v
      => (pj (theoreM (cx, FA2 (v, t --> t1, v1, t --> t1,
                               VAR v == VAR v1
                               <==>
                               FA (v2, t, VAR v @ VAR v2 == VAR v1 @ VAR v2))))))
    | thAbs ->
      (fa (cx:Context, v:Variable, t:Type, e:Expression, e1:Expression, t1:Type)
         pj (wellTypedExpr (cx, FN (v, t, e) @ e1, t1))
      && exprSubstOK? v e1 e
      => pj (theoreM (cx, FN (v, t, e) @ e1 == exprSubst v e1 e)))
    | thIf ->
      (fa (cx:Context, e0:Expression, e1:Expression, e2:Expression,
           e:Expression, t:Type, an1:AxiomName, an2:AxiomName)
         pj (wellTypedExpr (cx, IF (e0, e1, e2), t))
      && pj (theoreM (cx <| axioM (an1, empty,   e0), e1 == e))
      && pj (theoreM (cx <| axioM (an2, empty, ~~e0), e2 == e))
      => pj (theoreM (cx, IF (e0, e1, e2) == e)))
    | thThe ->
      (fa (cx:Context, t:Type, e:Expression)
         pj (wellTypedExpr (cx, IOTA t @ e, t))
      => pj (theoreM (cx, e @ (IOTA t @ e))))
    | thRec ->
      (fa (cx:Context, fS:Fields, tS:Types, v:Variable, v1:Variable,
           conjuncts:Expressions)
         pj (wellFormedType (cx, RECORD (fS, tS)))
      && v ~= v1
         (* In LD, the syntax includes that fS and tS have the same length.
         Here, we need to add it to this inference rule for the application
         of op @ on finite sequences to be well-typed. There is no need to
         require fS to be distinct, because it is a meta theorem. *)
      && length fS = length tS
      && conjuncts = seq (fn(i:Nat) ->
           if i < length fS then
             Some (DOT (VAR v, tS@i, fS@i) == DOT (VAR v1, tS@i, fS@i))
           else None)
      => pj (theoreM (cx, FA2 (v, RECORD(fS,tS), v1, RECORD(fS,tS),
                               ANDn conjuncts ==> VAR v == VAR v1))))
    | thEmbSurj ->
      (fa (cx:Context, cS:Constructors, tS:Types, v:Variable, v1:Variable,
           disjuncts:Expressions)
         pj (wellFormedType (cx, SUM (cS, tS)))
      && v ~= v1
         (* In LD, the syntax includes that cS and tS have the same length.
         Here, we need to add it to this inference rule for the application
         of op @ on finite sequences to be well-typed. There is no need to
         require cS to be distinct and non-zero, because it is a meta theorem. *)
      && length cS = length tS
      && disjuncts = seq (fn(i:Nat) ->
           if i < length cS then
             Some (EX (v1, tS@i, VAR v == EMBED (SUM(cS,tS), cS@i) @ VAR v1))
           else None)
      => pj (theoreM (cx, FA (v, SUM(cS,tS), ORn disjuncts))))
    | thEmbDist ->
      (fa (cx:Context, cS:Constructors, tS:Types, j:Nat, k:Nat,
           vj:Variable, vk:Variable)
         pj (wellFormedType (cx, SUM (cS, tS)))
      && j ~= k
      && vj ~= vk
      && j < length cS  && k < length cS
      && j < length tS && k < length tS
      => pj (theoreM (cx, FA2 (vj, tS@j, vk, tS@k,
                               EMBED (SUM(cS,tS), cS@j) @ VAR vj ~==
                               EMBED (SUM(cS,tS), cS@k) @ VAR vk))))
    | thEmbInj ->
      (fa (cx:Context, cS:Constructors, tS:Types,
           v:Variable, v1:Variable, j:Nat)
         pj (wellFormedType (cx, SUM (cS, tS)))
      && v ~= v1
      && j < length cS
      && j < length tS
      => pj (theoreM (cx, FA2 (v, tS@j, v1, tS@j,
                               VAR v ~== VAR v1 ==>
                               EMBED (SUM(cS,tS), cS@j) @ VAR v ~==
                               EMBED (SUM(cS,tS), cS@j) @ VAR v1))))
    | thQuotSurj ->
      (fa (cx:Context, t:Type, q:Expression, v:Variable, v1:Variable)
         pj (wellFormedType (cx, t/q))
      && v ~= v1
      => pj (theoreM (cx, FA (v, t/q,
                              EX (v1, t, QUOT (t/q) @ VAR v1 == VAR v)))))
    | thQuotEqCls ->
      (fa (cx:Context, t:Type, q:Expression, v:Variable, v1:Variable)
         pj (wellFormedType (cx, t/q))
      && v ~= v1
      => pj (theoreM (cx, FA2 (v, t, v1, t,
                               q @ PAIR (t, t, VAR v, VAR v1) <==>
                               QUOT (t/q) @ VAR v == QUOT (t/q) @ VAR v1))))
    | thProjSub ->
      (fa (cx:Context, fS:Fields, tS:Types, tS1:Types, r:Expression,
           j:Nat, v:Variable)
         pj (subType (cx, RECORD (fS, tS), r, RECORD (fS, tS1)))
      && j < length fS
      => pj (theoreM (cx, FA (v, RECORD(fS,tS),
                              PROJECT (RECORD(fS,tS),  fS@j) @ VAR v ==
                              PROJECT (RECORD(fS,tS1), fS@j) @ VAR v))))
    | thEmbSub ->
      (fa (cx:Context, cS:Constructors, tS:Types, tS1:Types, r:Expression,
           j:Nat, v:Variable)
         pj (subType (cx, SUM (cS, tS), r, SUM (cS, tS1)))
      && j < length cS
      && j < length tS
      => pj (theoreM (cx, FA (v, tS@j, EMBED (SUM(cS,tS),  cS@j) @ VAR v ==
                                       EMBED (SUM(cS,tS1), cS@j) @ VAR v))))
    | thSub ->
      (fa (cx:Context, t:Type, r:Expression, t1:Type, e:Expression)
         pj (subType (cx, t, r, t1))
      && pj (wellTypedExpr (cx, e, t))
      => pj (theoreM (cx, r @ e)))

  op provable? : Judgement -> Boolean
  def provable? = min (fn provable? ->
    (fa(ir:InferenceRule) satisfiesInferenceRule? provable? ir))

  type ProvableJudgement = (Judgement | provable?)

endspec
