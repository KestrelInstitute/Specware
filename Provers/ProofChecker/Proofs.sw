(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

MetaslangProofChecker qualifying
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

  The proof trees defined here also include a rule thLem that is not present
  in LD. The rule serves to turn a lemma in the context into a theorem in one
  step, analogously to rule thAx for axioms. Rule thLem is not needed in LD
  because lemmas in well-formed contexts are theorems, and so they can be
  turned into theorems by repeating the steps of their proofs. For practical
  purposes, especially given that proof trees, as explained in the previous
  paragraph, include assumptions, it is convenient to have rule thLem here.

  The constructors of proof trees are named after the inference rules in LD
  (cf. type InferenceRule in spec Provability). *)

  type Proof  % defined below

  % useful definition:
  type Proofs  = List Proof

  type Proof =
    % well-formed contexts:
    | cxMT
    | cxTdec  Proof * TypeName * Int
    | cxOdec  Proof * Proof * Operation
    | cxAx    Proof * Proof * AxiomName
    | cxLem   Proof * Proof * LemmaName
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
    | tyRestr Proof
    % subtyping:
    | stRestr Proof
    | stRefl  Proof * Variable
    | stArr   Proof * Proof * Variable * Variable
    | stRec   Proof * Proofs * Variable * List Int
    % well-typed expressions:
    | exVar      Proof * Variable
    | exOp       Proof * Proofs * Operation
    | exApp      Proof * Proof
    | exAbs      Proof * Proof
    | exEq       Proof * Proof
    | exIf       Proof * Proof * Proof * Proof
    | exThe      Proof
    | exProj     Proof * Field
    | exSuper    Proof * Proof
    | exSub      Proof * Proof * Proof
    | exAbsAlpha Proof * Variable
    % theorems:
    | thAx         Proof * Proofs * AxiomName
    | thLem        Proof * Proofs * LemmaName  % not present in LD
    | thRefl       Proof
    | thSymm       Proof
    | thTrans      Proof * Proof
    | thAppSubst   Proof * Proof * Proof
    | thEqSubst    Proof * Proof * Proof
    | thIfSubst    Proof * Proof * Proof * Proof
    | thSubst      Proof * Proof
    | thBool       Proof * Variable * Variable
    | thExt        Proof * Variable * Variable * Variable
    | thAbs        Proof
    | thIf         Proof * Proof * Proof
    | thThe        Proof
    | thRec        Proof * Variable * Variable
    | thProjSub    Proof * Variable * Field
    | thSub        Proof * Proof
    % assumptions:
    | assume Judgement

  (* The recursive type definition above only express a fixpoint, not
  necessarily the least one. We enforce the least one by means of a (quite
  verbose) induction axiom on proofs. *)

  axiom induction_on_proofs is
    fa (pred : Proof -> Bool)
  %%%%% induction base and step:
   (fa (tn    : TypeName,
        o     : Operation,
        tv    : TypeVariable,
        v     : Variable,
        v1    : Variable,
        v2    : Variable,
        f     : Field,
        fS    : Fields,
        an    : AxiomName,
        ln    : LemmaName,
        n     : Int,
        iS    : List Int,
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
      && pred (cxAx (prf1, prf2, an))
      && pred (cxLem (prf1, prf2, ln))
      && pred (cxTVdec (prf, tv))
      && pred (cxVdec (prf1, prf2, v))
      && pred (speC prf)
      && pred (tyBool prf)
      && pred (tyVar (prf, tv))
      && pred (tyInst (prf, prfS, tn))
      && pred (tyArr (prf1, prf2))
      && pred (tyRec (prf, prfS, fS))
      && pred (tyRestr prf)
      && pred (stRestr prf)
      && pred (stRefl (prf, v))
      && pred (stArr (prf1, prf2, v, v1))
      && pred (stRec (prf, prfS, v, iS))
      && pred (exVar (prf, v))
      && pred (exOp (prf, prfS, o))
      && pred (exApp (prf1, prf2))
      && pred (exAbs (prf1, prf2))
      && pred (exEq (prf1, prf2))
      && pred (exIf (prf1, prf2, prf3, prf4))
      && pred (exThe prf)
      && pred (exProj (prf, f))
      && pred (exSuper (prf1, prf2))
      && pred (exSub (prf1, prf2, prf3))
      && pred (exAbsAlpha (prf, v))
      && pred (thAx (prf, prfS, an))
      && pred (thLem (prf, prfS, ln))
      && pred (thRefl prf)
      && pred (thSymm prf)
      && pred (thTrans (prf1, prf2))
      && pred (thAppSubst (prf1, prf2, prf3))
      && pred (thEqSubst (prf1, prf2, prf3))
      && pred (thIfSubst (prf1, prf2, prf3, prf4))
      && pred (thSubst (prf1, prf2))
      && pred (thBool (prf, v, v1))
      && pred (thExt (prf, v, v1, v2))
      && pred (thAbs prf)
      && pred (thIf (prf1, prf2, prf3))
      && pred (thThe prf)
      && pred (thRec (prf, v, v1))
      && pred (thProjSub (prf, v, f))
      && pred (thSub (prf1, prf2))
      && pred (assume jdg))
  %%%%% induction conclusion:
   => (fa(prf) pred prf)

  (* A proof is closed iff it does not use any assumption, i.e. it does not
  contain constructor assume. *)

  op closedProof? : Proof -> Bool
  def closedProof? = fn
    | cxMT                                  -> true
    | cxTdec       (prf, _, _)              -> closedProof? prf
    | cxOdec       (prf1, prf2, _)          -> closedProof? prf1
                                            && closedProof? prf2
    | cxAx         (prf1, prf2, _)          -> closedProof? prf1
                                            && closedProof? prf2
    | cxLem        (prf1, prf2, _)          -> closedProof? prf1
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
    | tyRestr      prf                      -> closedProof? prf
    | stRestr      prf                      -> closedProof? prf
    | stRefl       (prf, _)                 -> closedProof? prf
    | stArr        (prf1, prf2, _, _)       -> closedProof? prf1
                                            && closedProof? prf2
    | stRec        (prf, prfS, _, _)        -> closedProof? prf
                                            && forall? closedProof? prfS
    | exVar        (prf, _)                 -> closedProof? prf
    | exOp         (prf, prfS, _)           -> closedProof? prf
                                            && forall? closedProof? prfS
    | exApp        (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | exAbs        (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | exEq         (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | exIf         (prf1, prf2, prf3, prf4) -> closedProof? prf1
                                            && closedProof? prf2
                                            && closedProof? prf3
                                            && closedProof? prf4
    | exThe        prf                      -> closedProof? prf
    | exProj       (prf, _)                 -> closedProof? prf
    | exSuper      (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | exSub        (prf1, prf2, prf3)       -> closedProof? prf1
                                            && closedProof? prf2
                                            && closedProof? prf3
    | exAbsAlpha   (prf, _)                 -> closedProof? prf
    | thAx         (prf, prfS, _)           -> closedProof? prf
                                            && forall? closedProof? prfS
    | thLem        (prf, prfS, _)           -> closedProof? prf
                                            && forall? closedProof? prfS
    | thRefl       prf                      -> closedProof? prf
    | thSymm       prf                      -> closedProof? prf
    | thTrans      (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | thAppSubst   (prf1, prf2, prf3)       -> closedProof? prf1
                                            && closedProof? prf2
                                            && closedProof? prf3
    | thEqSubst    (prf1, prf2, prf3)       -> closedProof? prf1
                                            && closedProof? prf2
                                            && closedProof? prf3
    | thIfSubst    (prf1, prf2, prf3, prf4) -> closedProof? prf1
                                            && closedProof? prf2
                                            && closedProof? prf3
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
    | thProjSub    (prf, _, _)              -> closedProof? prf
    | thSub        (prf1, prf2)             -> closedProof? prf1
                                            && closedProof? prf2
    | assume       _                        -> false

endspec
