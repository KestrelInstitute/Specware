spec

  % API public all

  import Judgements

  (* A proof can be represented as a tree of inference rules. Inference rules
  that have N judgements as premises have N subtrees; in particular, if N = 0,
  the inference rule is a leaf.

  A proof of this form can be checked by means of a recursive function that
  computes a judgement from a tree, the judgement being proved by the tree.
  For each inference rule, the function recursively computes the judgements
  proved by the subtrees and then checks whether the rule can be applied to
  such judgements. If it can, the function computes the judgement resulting
  from applying the rule. Otherwise, the function indicates a failure; of
  course, failures are propagated from subtree to supertrees. This function is
  defined in spec Checker.

  Since not all rules are such that there is a unique conclusion judgement for
  given premise judgements (e.g. rule cxTdec has a different conclusion for
  every type name and arity), proof trees include additional information to
  uniquely determine conclusion judgements from premise judgements (e.g. the
  node for cxTdec includes a type name and an arity).

  Besides inference rules, proof trees may also include assumptions,
  i.e. judgements that are assumed to be true. This feature is useful to
  build, effectively, "partial" proofs that can be "completed" later.

  The constructors of proof trees are named after the inference rules in LD
  (cf. type InferenceRule in spec Provability). *)

  type Proof  % defined below

  % useful definition:
  type Proofs  = FSeq Proof

  type Proof =
    % well-formed contexts:
    | cxMT
    | cxTdec  Proof * TypeName * Integer
    | cxOdec  Proof * Proof * Operation
    | cxTdef  Proof * Proof * TypeName
    | cxOdef  Proof * Proof * Operation
    | cxAx    Proof * Proof * AxiomName
    | cxTVdec Proof * TypeVariable
    | cxVdec  Proof * Proof * Variable
    % well-formed specs ("spec" is disallowed):
    | speC Proof
    % well-formed types:
    | tyBool  Proof
    | tyVar   Proof * TypeVariable
    | tyInst  Proof * Proofs * TypeName
    | tyArr   Proof * Proof
    | tyRec   Proof * Proofs * Fields
    | tySum   Proofs * Constructors
    | tyRestr Proof
    | tyQuot  Proof * Proof * Proof
    % type equivalence:
    | teDef    Proof * Proofs * TypeName
    | teRefl   Proof
    | teSymm   Proof
    | teTrans  Proof * Proof
    | teInst   Proof * Proofs
    | teArr    Proof * Proof
    | teRec    Proof * Proofs * Fields
    | teSum    Proofs * Constructors
    | teRestr  Proof * Proof * Proof
    | teQuot   Proof * Proof * Proof
    | teRecOrd Proof * FSeq Integer
    | teSumOrd Proof * FSeq Integer
    % subtyping:
    | stRestr Proof
    | stRefl  Proof * Variable
    | stArr   Proof * Proof * Variable * Variable
    | stRec   Proof * Proofs * Variable
    | stSum   Proof * Proofs * Variable * Variable
    | stTE    Proof * Proof * Proof
    % well-typed expressions:
    | exVar      Proof * Variable
    | exOp       Proof * Proofs * Operation
    | exApp      Proof * Proof
    | exAbs      Proof
    | exEq       Proof * Proof
    | exIf       Proof * Proof * Proof
    | exThe      Proof
    | exProj     Proof * Field
    | exEmbed    Proof * Constructor
    | exQuot     Proof
    | exSuper    Proof * Proof
    | exSub      Proof * Proof * Proof
    | exAbsAlpha Proof * Variable
    % theorems:
    | thAx         Proof * Proofs * AxiomName
    | thDef        Proof * Proofs * Operation
    | thRefl       Proof
    | thSymm       Proof
    | thTrans      Proof * Proof
    | thOpSubst    Proof * Proofs
    | thAppSubst   Proof * Proof * Proof
    | thAbsSubst   Proof * Proof * Proof
    | thIfSubst    Proof * Proof * Proof * Proof
    | thTheSubst   Proof * Proof
    | thProjSubst  Proof * Proof
    | thEmbedSubst Proof * Proof
    | thQuotSubst  Proof * Proof
    | thSubst      Proof * Proof
    | thBool       Proof * Variable * Variable
    | thExt        Proof * Variable * Variable * Variable
    | thAbs        Proof
    | thIf         Proof * Proof * Proof
    | thThe        Proof
    | thRec        Proof * Variable * Variable
    | thEmbSurj    Proof * Variable * Variable
    | thEmbDist    Proof * Constructor * Constructor * Variable * Variable
    | thEmbInj     Proof * Constructor * Variable * Variable
    | thQuotSurj   Proof * Variable * Variable
    | thQuotEqCls  Proof * Variable * Variable
    | thProjSub    Proof * Variable * Field
    | thEmbSub     Proof * Variable * Constructor
    | thSub        Proof * Proof
    % assumptions:
    | assume Judgement

  (* The recursive type definition above only express a fixpoint, not
  necessarily the least one. We enforce the least one by means of a (quite
  verbose) induction axiom on proofs. *)

  axiom induction_on_proofs is
    fa (pred : Proof -> Boolean)
  %%%%% induction base and step:
   (fa (tn    : TypeName,
        o     : Operation,
        tv    : TypeVariable,
        v     : Variable,
        v1    : Variable,
        v2    : Variable,
        f     : Field,
        fS    : Fields,
        c     : Constructor,
        c1    : Constructor,
        c2    : Constructor,
        cS    : Constructors,
        an    : AxiomName,
        n     : Integer,
        iS    : FSeq Integer,
        jdg   : Judgement,
        prf   : Proof,
        prf1  : Proof,
        prf2  : Proof,
        prf3  : Proof,
        prf4  : Proof,
        prfS  : Proofs)
         pred prf
      && pred prf1
      && pred prf2
      && pred prf3
      && forall? pred prfS
      => pred cxMT
      && pred (cxTdec (prf, tn, n))
      && pred (cxOdec (prf1, prf2, o))
      && pred (cxTdef (prf1, prf2, tn))
      && pred (cxOdef (prf1, prf2, o))
      && pred (cxAx (prf1, prf2, an))
      && pred (cxTVdec (prf, tv))
      && pred (cxVdec (prf1, prf2, v))
      && pred (speC prf)
      && pred (tyBool prf)
      && pred (tyVar (prf, tv))
      && pred (tyInst (prf, prfS, tn))
      && pred (tyArr (prf1, prf2))
      && pred (tyRec (prf, prfS, fS))
      && pred (tySum (prfS, cS))
      && pred (tyRestr prf)
      && pred (tyQuot (prf1, prf2, prf3))
      && pred (teDef (prf, prfS, tn))
      && pred (teRefl prf)
      && pred (teSymm prf)
      && pred (teTrans (prf1, prf2))
      && pred (teInst (prf, prfS))
      && pred (teArr (prf1, prf2))
      && pred (teRec (prf, prfS, fS))
      && pred (teSum (prfS, cS))
      && pred (teRestr (prf1, prf2, prf3))
      && pred (teQuot (prf1, prf2, prf3))
      && pred (teRecOrd (prf, iS))
      && pred (teSumOrd (prf, iS))
      && pred (stRestr prf)
      && pred (stRefl (prf, v))
      && pred (stArr (prf1, prf2, v, v1))
      && pred (stRec (prf, prfS, v))
      && pred (stSum (prf, prfS, v, v1))
      && pred (stTE (prf1, prf2, prf3))
      && pred (exVar (prf, v))
      && pred (exOp (prf, prfS, o))
      && pred (exApp (prf1, prf2))
      && pred (exAbs prf)
      && pred (exEq (prf1, prf2))
      && pred (exIf (prf1, prf2, prf3))
      && pred (exThe prf)
      && pred (exProj (prf, f))
      && pred (exEmbed (prf, c))
      && pred (exQuot prf)
      && pred (exSuper (prf1, prf2))
      && pred (exSub (prf1, prf2, prf3))
      && pred (exAbsAlpha (prf, v))
      && pred (thAx (prf, prfS, an))
      && pred (thDef (prf, prfS, o))
      && pred (thRefl prf)
      && pred (thSymm prf)
      && pred (thTrans (prf1, prf2))
      && pred (thOpSubst (prf, prfS))
      && pred (thAppSubst (prf1, prf2, prf3))
      && pred (thAbsSubst (prf1, prf2, prf3))
      && pred (thIfSubst (prf1, prf2, prf3, prf4))
      && pred (thTheSubst (prf1, prf2))
      && pred (thProjSubst (prf1, prf2))
      && pred (thEmbedSubst (prf1, prf2))
      && pred (thQuotSubst (prf1, prf2))
      && pred (thSubst (prf1, prf2))
      && pred (thBool (prf, v, v1))
      && pred (thExt (prf, v, v1, v2))
      && pred (thAbs prf)
      && pred (thIf (prf1, prf2, prf3))
      && pred (thThe prf)
      && pred (thRec (prf, v, v1))
      && pred (thEmbSurj (prf, v, v1))
      && pred (thEmbDist (prf, c1, c2, v1, v2))
      && pred (thEmbInj (prf, c, v, v1))
      && pred (thQuotSurj (prf, v, v1))
      && pred (thQuotEqCls (prf, v, v1))
      && pred (thProjSub (prf, v, f))
      && pred (thEmbSub (prf, v, c))
      && pred (thSub (prf1, prf2))
      && pred (assume jdg))
  %%%%% induction conclusion:
   => (fa(prf) pred prf)

  (* A proof is closed iff it does not use any assumption, i.e. it does not
  contain constructor assume. *)

  op closedProof? : Proof -> Boolean
  def closedProof? = fn
    | cxMT                                  -> true
    | cxTdec       (prf, _, _)              -> closedProof? prf
    | cxOdec       (prf1, prf2, _)          -> closedProof? prf1
                                            && closedProof? prf2
    | cxTdef       (prf1, prf2, _)          -> closedProof? prf1
                                            && closedProof? prf2
    | cxOdef       (prf1, prf2, _)          -> closedProof? prf1
                                            && closedProof? prf2
    | cxAx         (prf1, prf2, _)          -> closedProof? prf1
                                            && closedProof? prf2
    | cxTVdec      (prf, _)                 -> closedProof? prf
    | cxVdec       (prf1, prf2, _)          -> closedProof? prf1
                                            && closedProof? prf2
    | speC         prf                      -> closedProof? prf
    | tyBool       prf                      -> closedProof? prf
    | tyVar        (prf, _)                 -> closedProof? prf
    | tyInst       (prf, prfS, _)           -> closedProof? prf
                                            && forall? closedProof? prfS
    | tyArr        (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | tyRec        (prf, prfS, _)           -> closedProof? prf
                                            && forall? closedProof? prfS
    | tySum        (prfS, _)                -> forall? closedProof? prfS
    | tyRestr      prf                      -> closedProof? prf
    | tyQuot       (prf1, prf2, prf3)       -> closedProof? prf1
                                            && closedProof? prf2
                                            && closedProof? prf3
    | teDef        (prf, prfS, _)           -> closedProof? prf
                                            && forall? closedProof? prfS
    | teRefl       prf                      -> closedProof? prf
    | teSymm       prf                      -> closedProof? prf
    | teTrans      (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | teInst       (prf, prfS)              -> closedProof? prf
                                            && forall? closedProof? prfS
    | teArr        (prf1, prf2)             -> closedProof? prf1
    | teRec        (prf, prfS, _)           -> closedProof? prf
                                            && forall? closedProof? prfS
    | teSum        (prfS, _)                -> forall? closedProof? prfS
    | teRestr      (prf1, prf2, prf3)       -> closedProof? prf1
                                            && closedProof? prf2
                                            && closedProof? prf3
    | teQuot       (prf1, prf2, prf3)       -> closedProof? prf1
                                            && closedProof? prf2
                                            && closedProof? prf3
    | teRecOrd     (prf, _)                 -> closedProof? prf
    | teSumOrd     (prf, _)                 -> closedProof? prf
    | stRestr      prf                      -> closedProof? prf
    | stRefl       (prf, _)                 -> closedProof? prf
    | stArr        (prf1, prf2, _, _)       -> closedProof? prf1
                                            && closedProof? prf2
    | stRec        (prf, prfS, _)           -> closedProof? prf
                                            && forall? closedProof? prfS
    | stSum        (prf1, prfS, _, _)       -> closedProof? prf1
                                            && forall? closedProof? prfS
    | stTE         (prf1, prf2, prf3)       -> closedProof? prf1
                                            && closedProof? prf2
                                            && closedProof? prf3
    | exVar        (prf, _)                 -> closedProof? prf
    | exOp         (prf, prfS, _)           -> closedProof? prf
                                            && forall? closedProof? prfS
    | exApp        (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | exAbs        prf                      -> closedProof? prf
    | exEq         (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | exIf         (prf1, prf2, prf3)       -> closedProof? prf1
                                            && closedProof? prf2
                                            && closedProof? prf3
    | exThe        prf                      -> closedProof? prf
    | exProj       (prf, _)                 -> closedProof? prf
    | exEmbed      (prf, _)                 -> closedProof? prf
    | exQuot       prf                      -> closedProof? prf
    | exSuper      (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | exSub        (prf1, prf2, prf3)       -> closedProof? prf1
                                            && closedProof? prf2
                                            && closedProof? prf3
    | exAbsAlpha   (prf, _)                 -> closedProof? prf
    | thAx         (prf, prfS, _)           -> closedProof? prf
                                            && forall? closedProof? prfS
    | thDef        (prf, prfS, _)           -> closedProof? prf
                                            && forall? closedProof? prfS
    | thRefl       prf                      -> closedProof? prf
    | thSymm       prf                      -> closedProof? prf
    | thTrans      (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | thOpSubst    (prf, prfS)              -> closedProof? prf
                                            && forall? closedProof? prfS
    | thAppSubst   (prf1, prf2, prf3)       -> closedProof? prf1
                                            && closedProof? prf2
                                            && closedProof? prf3
    | thAbsSubst   (prf1, prf2, prf3)       -> closedProof? prf1
                                            && closedProof? prf2
                                            && closedProof? prf3
    | thIfSubst    (prf1, prf2, prf3, prf4) -> closedProof? prf1
                                            && closedProof? prf2
                                            && closedProof? prf3
    | thTheSubst   (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | thProjSubst  (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | thEmbedSubst (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | thQuotSubst  (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | thSubst      (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | thBool       (prf, _, _)              -> closedProof? prf
    | thExt        (prf, _, _, _)           -> closedProof? prf
    | thAbs        prf                      -> closedProof? prf
    | thIf         (prf1, prf2, prf3)       -> closedProof? prf1
                                            && closedProof? prf2
                                            && closedProof? prf3
    | thThe        prf                      -> closedProof? prf
    | thRec        (prf, _, _)              -> closedProof? prf
    | thEmbSurj    (prf, _, _)              -> closedProof? prf
    | thEmbDist    (prf, _, _, _, _)        -> closedProof? prf
    | thEmbInj     (prf, _, _, _)           -> closedProof? prf
    | thQuotSurj   (prf, _, _)              -> closedProof? prf
    | thQuotEqCls  (prf, _, _)              -> closedProof? prf
    | thProjSub    (prf, _, _)              -> closedProof? prf
    | thEmbSub     (prf, _, _)              -> closedProof? prf
    | thSub        (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | assume       _                        -> false

endspec
