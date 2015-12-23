(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

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
    | tyRestr
    % subtyping:
    | stRestr
    | stRefl
    | stArr
    | stRec
    % well-typed expressions:
    | exVar
    | exOp
    | exApp
    | exAbs
    | exEq
    | exIf
    | exThe
    | exProj
    | exSuper
    | exSub
    | exAbsAlpha
    % theorems:
    | thAx
    | thRefl
    | thSymm
    | thTrans
    | thAppSubst
    | thIfSubst
    | thSubst
    | thBool
    | thExt
    | thAbs
    | thIf
    | thThe
    | thRec
    | thProjSub
    | thSub

  (* The goal is to define a predicate provable? on judgements. This predicate
  is the minimum one satisfying all the inference rules. So, we define an
  auxiliary predicate satisfiesInferenceRule? that says whether a predicate on
  judgements satisfies a given rule. *)

  op satisfiesInferenceRule? : (Judgement -> Bool) -> InferenceRule -> Bool
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
    | tyRestr ->
      (fa (cx:Context, r:Expression, t:Type)
         pj (wellTypedExpr (cx, r, t --> BOOL))
      && exprFreeVars r = empty
      => pj (wellFormedType (cx, t\r)))

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
           prm:Permutation, r:Expression, v:Variable, conjuncts:Expressions)
         pj (wellFormedType (cx, RECORD (fS, tS)))
         (* In LD, the syntax includes that fS and tS and tS1 have the same
         length. Here, they are meta theorems but we need to add them to this
         inference rule for the application of @ on finite sequences to be
         well-typed. There is no need to require fS to be distinct, because it
         is a meta theorem and is not needed for meta well-typedness. *)
      && length fS = length tS
      && length tS = length tS1
      && length tS1 = length rS
      && length rS = length prm
      && (fa(i:Nat) i < length tS =>
            pj (subType (cx, tS@i, rS@i, tS1@i)))
      && conjuncts = seq (fn(i:Nat) ->
           if i < length fS then Some ((rS@i) @ DOT (VAR v, tS@i, fS@i))
           else None)
      && r = FN (v, RECORD (permute(fS,prm), permute(tS1,prm)), ANDn conjuncts)
      => pj (subType (cx, RECORD (fS, tS), r,
                          RECORD (permute(fS,prm), permute(tS1,prm)))))

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
      && pj (wellFormedType (cx, t1))
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
      && pj (wellFormedType (cx, t))
      => pj (wellTypedExpr (cx, IF (e0, e1, e2), t)))
    | exThe ->
      (fa (cx:Context, t:Type)
         pj (wellFormedType (cx, t))
      => pj (wellTypedExpr (cx, IOTA t, ((t --> BOOL) \ EX1q t) --> t)))
    | exProj ->
      (fa (cx:Context, fS:Fields, tS:Types, j:Nat)
         pj (wellFormedType (cx, RECORD (fS, tS)))
         (* In LD, the syntax includes that fS and tS have the same length.
         Here, we need to add it to this inference rule for the application of
         op @ on finite sequences to be well-typed. There is no need to
         require fS to be distinct, because it is a meta theorem. *)
      && length fS = length tS
      && j < length fS
      => pj (wellTypedExpr (cx, PROJECT (RECORD(fS,tS), fS@j),
                                RECORD(fS,tS) --> tS@j)))
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
    | thAppSubst ->
      (fa (cx:Context, e1:Expression, e2:Expression, t:Type,
           d1:Expression, d2:Expression)
         pj (wellTypedExpr (cx, e1 @ e2, t))
      && pj (theoreM (cx, e1 == d1))
      && pj (theoreM (cx, e2 == d2))
      => pj (theoreM (cx, e1 @ e2 == d1 @ d2)))
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
    | thProjSub ->
      (fa (cx:Context, fS:Fields, tS:Types, tS1:Types, r:Expression,
           j:Nat, v:Variable)
         pj (subType (cx, RECORD (fS, tS), r, RECORD (fS, tS1)))
      && j < length fS
      => pj (theoreM (cx, FA (v, RECORD(fS,tS),
                              PROJECT (RECORD(fS,tS),  fS@j) @ VAR v ==
                              PROJECT (RECORD(fS,tS1), fS@j) @ VAR v))))
    | thSub ->
      (fa (cx:Context, t:Type, r:Expression, t1:Type, e:Expression)
         pj (subType (cx, t, r, t1))
      && pj (wellTypedExpr (cx, e, t))
      => pj (theoreM (cx, r @ e)))

  op provable? : Judgement -> Bool
  def provable? = min (fn provable? ->
    (fa(ir:InferenceRule) satisfiesInferenceRule? provable? ir))

  type ProvableJudgement = (Judgement | provable?)

endspec
