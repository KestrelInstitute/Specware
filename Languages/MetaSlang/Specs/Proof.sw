
% Defines a proof language for Specware. This language is not meant to
% be complete for everything it needs to do, but instead can include
% calls to tactics in an underlying proof assistant (i.e., Isabelle)
% to prove the really difficult theorems.
%
% README: scroll down to the "external interface" to see how to use
% this library.

Proof qualifying spec
  import MSTerm
  import ../AbstractSyntax/PathTerm
  import /Library/Structures/Data/Monad/ErrorMonad

  % Forward references
  op SpecNorm.typePredTermNoSpec(ty0: MSType, tm: MSTerm): MSTerm
  op MergeRules.mapTraceTree (tsp: TSP_Maps_St) (t: TraceTree) : TraceTree

  % A proof tactic
  type Tactic =
    % The simplest tactic: a string, to be interpreted by the prover
    | StringTactic String
    % The "auto" tactic, possibly augmented by some additional proofs
    | AutoTactic (List Proof)

  % The internal form of proofs
  type ProofInternal =
    %% General proof constructs

    % Proof_Cut (P, Q, pf1, pf2) takes pf1 : P=>Q and pf2 : P
    % and creates a proof of Q
    | Proof_Cut (MSTerm * MSTerm * ProofInternal * ProofInternal)

    % Proof_ForallE (x,T,M,N,pf1,pf2) is a proof of [N/x]M from a proof
    % pf1 : fa(x:T)M and a proof pf2 : typePredTermNoSpec(T,M)
    | Proof_ForallE (Id * MSType * MSTerm * MSTerm
                       * ProofInternal * ProofInternal)

    % Proof_EqTrue(M,pf) is a proof of M given a proof pf :: M=true
    | Proof_EqTrue (MSTerm * ProofInternal)

    % Proof_Theorem(x,P) is a proof of P assuming that x is the
    % name of an axiom or theorem that proves P
    | Proof_Theorem (QualifiedId * MSTerm)

    % ProofInternal by an external tactic, along with the predicate it proves
    | Proof_Tactic (Tactic * MSTerm)

    %% Equality proofs

    % Proof_UnfoldDef (T, qid, simps?, vars, M, N) is a proof that
    % fa(vars) M=N at type T by unfolding the definition of qid. The
    % "simps?" flag states whether the Isabelle ".simps" attribute
    % should be used; otherwise, the "_def" of qid is used.
    | Proof_UnfoldDef (MSType * QualifiedId * Bool * MSVars * MSTerm * MSTerm)

    % Proof_EqSubterm(M,N,T,p,pf) is a proof that M = N : T from a
    % proof pf : M.p = N.p, where M.p is the subterm of M at path p
    | Proof_EqSubterm (MSTerm * MSTerm * MSType * Path * ProofInternal)

    % Proof_EqSym(pf) is a proof that N=M from pf : M=N
    | Proof_EqSym ProofInternal

    % Proof by transitivity of equality: proves x0 = x1 = ... = xn,
    % all at type T, where each (pf, t) pair in the list is an xi
    % along with the proof that x(i-1) = xi
    | Proof_EqTrans (MSType * MSTerm * List (ProofInternal * MSTerm))

    %% Implication proofs

    % Proof_ImplTrans(P,pf1,Q,pf2,R) is a proof of P => R from
    % proofs pf1: P=>Q and pf2: Q=>R
    | Proof_ImplTrans (MSTerm * ProofInternal * MSTerm * ProofInternal * MSTerm)

    % Proof_ImplEq(pf) is a proof that P=>Q from pf: P=Q
    | Proof_ImplEq ProofInternal

    % Proof_MergeRules(tree,post,unfolds,smtArgs) is a proof of
    % MergeRules.mergeRulesPredicate(tree,post) by merge rules
    | Proof_MergeRules (TraceTree * MSTerm * List QualifiedId * List QualifiedId)


  % Return the predicate proved by a proof
  op proofPredicate_Internal (p : ProofInternal) : MSTerm =
    case p of
      | Proof_Cut (P, Q, pf1, pf2) -> Q
      | Proof_ForallE (x,T,M,N,pf,tp_pf) -> substitute (M, [((x,T),N)])
      | Proof_EqTrue (M, pf) -> M
      | Proof_Theorem (id, P) -> P
      | Proof_Tactic (tact, P) -> P
      | Proof_EqSubterm(M,N,T,p,pf) -> mkEquality (T,M,N)
      | Proof_UnfoldDef (T, qid, simps?, vars, M, N) ->
        mkBind (Forall, vars, mkEquality (T, M, N))
      | Proof_EqSym(pf) ->
        (case matchEquality (proofPredicate_Internal pf) of
           | Some (T,M,N) -> mkEquality (T,N,M)
           | _ -> fail "Malformed proof: in proofPredicate applied to Proof_EqSym")
      | Proof_EqTrans (T, M1, pfs) ->
        let def getLast Mprev pfs' =
          (case pfs' of
            | [] -> Mprev
            | (_, M) :: pfs'' -> getLast M pfs'')
        in
        mkEquality (T, M1, getLast M1 pfs)
      | Proof_ImplTrans(P,pf1,Q,pf2,R) -> mkImplies (P, R)
      | Proof_ImplEq pf ->
        (case matchEquality (proofPredicate_Internal pf) of
           | Some (T, M, N) -> mkImplies (M, N)
           | _ -> fail "Malformed proof: in proofPredicate applied to Proof_ImplEq")
      | Proof_MergeRules(tree,post,unfolds,smtArgs) ->
        MergeRules.mergeRulesPredicate (tree, post)

  % FIXME: IsaPrinter cannot call functions that begin with "proof"...?
  def getProofPredicate_Internal p = proofPredicate_Internal p

  % Substitute for type variables in a proof
  op substTypes_ProofInternal (s: TyVarSubst, p: ProofInternal): ProofInternal =
    case p of
      | Proof_Cut (P, Q, pf1, pf2) ->
        Proof_Cut (instantiateTyVarsInTerm (P, s),
                   instantiateTyVarsInTerm (Q, s),
                   substTypes_ProofInternal (s, pf1),
                   substTypes_ProofInternal (s, pf2))
      | Proof_ForallE (x,T,M,N,pf,tp_pf) ->
        Proof_ForallE (x,
                       instantiateTyVarsInType (T, s),
                       instantiateTyVarsInTerm (M, s),
                       instantiateTyVarsInTerm (N, s),
                       substTypes_ProofInternal (s, pf),
                       substTypes_ProofInternal (s, tp_pf))
      | Proof_EqTrue (M, pf) ->
        Proof_EqTrue (instantiateTyVarsInTerm (M, s),
                      substTypes_ProofInternal (s, pf))
      | Proof_Theorem (id, P) ->
        Proof_Theorem (id, instantiateTyVarsInTerm (P, s))
      | Proof_Tactic (tact, P) ->
        Proof_Tactic (tact, instantiateTyVarsInTerm (P, s))
      | Proof_EqSubterm(M,N,T,p,pf) ->
        Proof_EqSubterm(instantiateTyVarsInTerm (M, s),
                        instantiateTyVarsInTerm (N, s),
                        instantiateTyVarsInType (T, s),
                        p,
                        substTypes_ProofInternal (s, pf))
      | Proof_UnfoldDef (T, qid, simps?, vars, M, N) ->
        Proof_UnfoldDef (instantiateTyVarsInType (T, s), qid, simps?, vars,
                         instantiateTyVarsInTerm (M, s),
                         instantiateTyVarsInTerm (N, s))
      | Proof_EqSym(pf) ->
        Proof_EqSym(substTypes_ProofInternal (s, pf))
      | Proof_EqTrans (T, M1, pfs) ->
        Proof_EqTrans (instantiateTyVarsInType (T, s),
                       instantiateTyVarsInTerm (M1, s),
                       map (fn (pf, N) ->
                              (substTypes_ProofInternal (s, pf),
                               instantiateTyVarsInTerm (N, s)))
                         pfs)
                         
      | Proof_ImplTrans(P,pf1,Q,pf2,R) ->
        Proof_ImplTrans(instantiateTyVarsInTerm (P, s),
                        substTypes_ProofInternal (s, pf1),
                        instantiateTyVarsInTerm (Q, s),
                        substTypes_ProofInternal (s, pf2),
                        instantiateTyVarsInTerm (R, s))
      | Proof_ImplEq pf ->
        Proof_ImplEq (substTypes_ProofInternal (s, pf))
      | Proof_MergeRules(tree,post,unfolds,smtArgs) ->
        let _ =
          warn ("substTypes_ProofInternal: FIXME: substituting for type variables in a MergeRules proof not (yet) implemented")
        in
        p

  % See mapProof, below
  op mapProof_Internal (tsp: TSP_Maps_St) (pf: ProofInternal) : Proof =
    case pf of
      | Proof_Cut (P, Q, pf1, pf2) ->
        prove_implElim (mapProof_Internal tsp pf1, mapProof_Internal tsp pf2)
      | Proof_ForallE (x,T,M,N,pf,tp_pf) ->
        prove_forallElim (mapProof_Internal tsp pf, mapTerm tsp N,
                          mapProof_Internal tsp tp_pf)
      | Proof_EqTrue (M, pf) ->
        prove_fromEqualTrue (mapTerm tsp M, mapProof_Internal tsp pf)
      | Proof_Theorem (id, P) ->
        prove_withTheorem (id, mapTerm tsp P)
      | Proof_Tactic (tact, P) ->
        prove_withTactic (mapTactic tsp tact, mapTerm tsp P)
      | Proof_EqSubterm(M,N,T,p,pf) ->
        prove_equalSubTerm (mapTerm tsp M, mapTerm tsp N, mapType tsp T, p,
                            mapProof_Internal tsp pf)
      | Proof_UnfoldDef (T, qid, simps?, vars, M, N) ->
        prove_equalUnfold (mapType tsp T, qid, simps?, vars,
                           mapTerm tsp M, mapTerm tsp N)
      | Proof_EqSym (pf) ->
        prove_equalSym (mapProof_Internal tsp pf)
      | Proof_EqTrans (T, M1, pfs) ->
        foldl (fn (prev_pf, (next_pf,_)) ->
                 prove_equalTrans (prev_pf, mapProof_Internal tsp next_pf))
          (prove_equalRefl (T, mapTerm tsp M1))
          pfs
      | Proof_ImplTrans(P,pf1,Q,pf2,R) ->
        prove_implTrans (mapProof_Internal tsp pf1, mapProof_Internal tsp pf2)
      | Proof_ImplEq pf ->
        prove_implEq (mapProof_Internal tsp pf)
      | Proof_MergeRules (tree,post,unfolds,smtArgs) ->
        prove_MergeRules (mapTraceTree tsp tree, mapTerm tsp post,
                          unfolds, smtArgs)

  % See mapProof, below
  op mapTactic (tsp: TSP_Maps_St) (tactic: Tactic) : Tactic =
    case tactic of
      | StringTactic _ -> tactic
      | AutoTactic pfs ->
        AutoTactic (map (mapProof "(recursive mapTactic)" tsp) pfs)

  % Print out a representation of a proof
  op showProof_Internal (p : ProofInternal) : String =
    "(FIXME: write Proof.showProof_Internal!)"


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  % External interface starts here!!
  %
  % The prove_* commands below should be the *only* way proofs are
  % built. The idea of the Proof type here is that you don't have to
  % check for errors at each point, but can instead just write your
  % proof completely ignoring the possibility of errors: errors are
  % handled transparently in monadBind. (This should look familiar to
  % those familiar with the error monad...)

  % The type of proofs that might have been built incorrectly
  type Proof = Monad ProofInternal

  % Proof error-handling has two modes: silent and debug, controlled
  % by the flag proofSilentMode?, below. In silent mode, errors in
  % constructing proofs do not interrupt the program flow, and are
  % only reported when the proof is pretty-printed to Isabelle. In
  % debug mode, errors in proofs immediately become Lisp exceptions,
  % so that you can track down where the proof bug is.
  op proofSilentMode? : Bool = false
  op proofError (err_str: String) : Proof =
    if proofSilentMode? then ErrorFail err_str else
      fail err_str

  % A bogus proof object, which will "percolate up", i.e., which will
  % always produce bogus proofs when combined with other proofs
  op bogusProof : Proof = ErrorFail "Bogus proof!"

  % Print out a representation of a proof
  op showProof (p : Proof) : String =
  case p of
    | ErrorOk p_int -> showProof_Internal p_int
    | ErrorFail str -> "(proof error: " ^ str ^ ")"

  % Return the predicate proved by a proof, or None if there is an
  % error in the proof
  op proofPredicate (p : Proof) : Option MSTerm =
    case p of
      | ErrorOk p -> Some (proofPredicate_Internal p)
      | ErrorFail _ -> None

  % Return true iff p is a proof of true
  op trueProof? (p : Proof) : Bool =
    case proofPredicate p of
      | Some t -> trueTerm? t
      | None -> false

  % FIXME: some specs cannot call ops whose names start with
  % "proof"...?
  op getProofPredicate (p : Proof) : Option MSTerm = proofPredicate p

  % Substitute for free type variables in a proof. Note that
  % substituting for term variables would be more complicated, as it
  % would require proofs that the terms satisfy their type predicates.
  op instantiateTyVarsInProof (subst : TyVarSubst, pf : Proof) : Proof =
    { pf_int <- pf;
      return (substTypes_ProofInternal (subst, pf_int)) }

  % Apply a function to all the terms in a proof, as with mapTerm.
  % README: This will only work if the function does not require a
  % change to the structure of the proof; e.g., the function should
  % not add or remove implications or quantifiers. Also, the function
  % must not change the paths to subterms used in the proof.
  op mapProof (descr: String) (tsp: TSP_Maps_St) (pf: Proof) : Proof =
    case pf of
      | ErrorOk pf_int ->
        (case mapProof_Internal tsp pf_int of
           | ErrorFail err ->
             ErrorFail (descr ^ " failed: " ^ err)
           | res -> res)
      | _ -> pf


  % prove_implElim (pf1, pf2) takes a proof pf1:P=>Q and a proof pf2:P
  % and builds a proof of Q
  op prove_implElim (p1 : Proof, p2 : Proof) : Proof =
    { p1_int <- p1; p2_int <- p2;
      p1_pred <- return (proofPredicate_Internal p1_int);
      p2_pred <- return (proofPredicate_Internal p2_int);
      case matchImplication p1_pred of
        | Some (P, Q) | equalTerm? (P, p2_pred) ->
          return (Proof_Cut (P, Q, p1_int, p2_int))
        | _ -> proofError ("Implication elimination of (" ^ printTerm p1_pred
                             ^ ") against (" ^ printTerm p2_pred ^ ")") }

  % prove_forallElim (pf, N, tp_pf) takes a proof pf1:fa(x:T)M, a term
  % N of type T, and a proof tp_pf that N does indeed have type T, and
  % builds a proof of [N/x]M.
  op prove_forallElim (p : Proof, N : MSTerm, tp_pf : Proof) : Proof =
    { p_int <- p;
      p_pred <- return (proofPredicate_Internal p_int);
      tp_int <- tp_pf;
      tp_pred <- return (proofPredicate_Internal tp_int);
      case matchForall1 p_pred of
        | Some (x, T, M) ->
          let tp_pred_expected = typePredTermNoSpec(T,N) in
          if equalTerm? (tp_pred, tp_pred_expected) then
            return (Proof_ForallE (x, T, M, N, p_int, tp_int))
          else
            proofError ("Bad typing proof in forall elimination: expected ("
                          ^ printTerm tp_pred_expected ^ "), found ("
                          ^ printTerm tp_pred ^ ")")
        | _ -> proofError ("Forall elimination of (" ^ printTerm p_pred
                             ^ ") against term (" ^ printTerm N ^ ")") }

  % prove_forallElimMulti (pf, [(N1, pf1),...,(Nn,pfn)]) takes a proof
  % pf1:fa(x1:T1,...,xn:Tn)M, and a list of terms N1,...,Nn and proofs
  % pf1,...,pfn that each Ni has type Ti and builds a proof of
  % [N1/x1,...,Nn/xn]M.
  op prove_forallElimMulti (p : Proof, args : List (MSTerm * Proof)) : Proof =
    foldl (fn (pf, (N,tp_pf)) -> prove_forallElim (pf, N, tp_pf)) p args

  % build a proof of M given a proof of M=true
  op prove_fromEqualTrue (M : MSTerm, pf : Proof) : Proof =
    { p_int <- pf;
      p_pred <- return (proofPredicate_Internal p_int);
      case matchEquality p_pred of
        | Some (_, M', N) | equalTerm? (M,M') && equalTerm? (N,mkTrue()) ->
          return (Proof_EqTrue (M, p_int))
        | _ -> proofError ("Attempt to prove (" ^ printTerm M
                             ^ ") from a proof of (" ^ printTerm p_pred ^ ")") }

  % build a proof of true
  op prove_true : Proof =
    % prove_fromEqualTrue (mkTrue(), prove_equalRefl (boolType, mkTrue()))
    prove_withTactic (StringTactic "simp", mkTrue())

  % build a proof by applying a theorem or axiom for predicate P
  op prove_withTheorem (qid : QualifiedId, P : MSTerm) : Proof =
    return (Proof_Theorem (qid, P))

  % build a proof by applying a tactic
  op prove_withTactic (tactic : Tactic, P : MSTerm) : Proof =
    return (Proof_Tactic (tactic, P))

  % build an equality proof with a tactic
  op prove_equalWithTactic (tactic : Tactic, M : MSTerm, N : MSTerm, T : MSType) : Proof =
    return (Proof_Tactic (tactic, mkEquality (T,M,N)))

  % build a proof (fa (vars) M=N) at type T by unfolding the
  % definition of qid, where the simps? flag states whether to use the
  % ".simps" Isabelle attribute (if true) or the "_def" theorem (if
  % false) to do the unfolding (NOTE: the assumption that unfolding
  % qid in M results in N is not checked)
  op prove_equalUnfold (T : MSType, qid : QualifiedId, simps? : Bool,
                        vars : MSVars, M : MSTerm, N : MSTerm) : Proof =
    return (Proof_UnfoldDef (T, qid, simps?, vars, M, N))

  % prove_equalSubTerm(M,N,T,p,pf) proves that M=N at type T using a
  % proof pf that the subterms of M and N at path p are equal. NOTE:
  % we assume that M and N both have type T
  op prove_equalSubTerm (M : MSTerm, N : MSTerm, T : MSType, p : Path, pf : Proof) : Proof =
    { pf_int <- pf;
      pf_pred <- return (proofPredicate_Internal pf_int);
      let (varsM, M_sub) = fromPathTermWithBindings (M, p) in
      let (varsN, N_sub_orig) = fromPathTermWithBindings (N, p) in
      let N_sub = if varsM = varsN then N_sub_orig else
                    substitute (N_sub_orig, zip (varsN, map mkVar varsM)) in
      case matchEquality pf_pred of
        | Some (_, M', N') | equalTerm? (M', M_sub) && equalTerm? (N', N_sub) ->
          % Proof optimization
          (case pf_int of
             | Proof_EqSubterm(M',N',T',p',pf_int') ->
               % Collapse nested subterm proofs
               % README: inner path comes before outer path
               prove_equalSubTerm (M,N,T,p'++p, return pf_int')
             | Proof_EqTrans (Tsub, Msub, []) ->
               % Move reflexivity proofs to the outer level
               prove_equalRefl (T, M)
             | _ | p = [] ->
               % Also handle special case where p is the empty path
               return pf_int
             | _ ->
               return (Proof_EqSubterm(M,N,T,p,pf_int)))
        | _ -> proofError ("Attempt to prove equality of subterms (" ^
                             printTerm (fromPathTerm (M,p)) ^
                             ") and (" ^ printTerm (fromPathTerm (N,p)) ^
                             ") from a proof of: " ^ printTerm pf_pred) }

  % build a proof of M=M
  op prove_equalRefl (T : MSType, M : MSTerm) : Proof =
    return (Proof_EqTrans (T, M, []))

  % build a proof of N=M from a proof of M=N
  %
  % FIXME: do proof simplification, pushing the symmetry into
  % transitivity and subterm proofs
  op prove_equalSym (pf : Proof) : Proof =
    { pf_int <- pf;
      let pf_pred = proofPredicate_Internal pf_int in
      case matchEquality pf_pred of
        | Some (T, M, N) -> return (Proof_EqSym pf_int)
        | _ -> proofError ("Attempt to apply symmetry of equality to a non-equality proof: "
                             ^ printTerm pf_pred) }

  % prove M=P from a proof pf1 of M=N and a proof pf2 of N=P
  %
  % NOTE: both equality proofs must be at the same type (it might be
  % ok to take the meet of two different types, but I'm not sure...)
  op prove_equalTrans (pf1 : Proof, pf2 : Proof) : Proof =
    { pf1_int <- pf1; pf2_int <- pf2;
      pf1_pred <- return (proofPredicate_Internal pf1_int);
      pf2_pred <- return (proofPredicate_Internal pf2_int);
      case (matchEquality pf1_pred, matchEquality pf2_pred) of
        | (Some (T1, M, N1), Some (T2, N2, P)) | equalTerm? (N1, N2) ->
          if equalType? (T1, T2) then
            let def mkProof_EqTrans (Tret, Mret, pfs_ret) =
              case pfs_ret of
                % Don't need to build a trans proof with one proof!
                | [(pf_ret, _)] -> return pf_ret
                | _ -> return (Proof_EqTrans (Tret, Mret, pfs_ret))
            in
            (case (pf1_int, pf2_int) of
               | (Proof_EqSubterm(_,_,_,p1,sub_pf1),
                  Proof_EqSubterm(_,_,_,p2,sub_pf2))
               | pathExtends? (p1, p2) ->
                 % If both proofs are at the same subterm, combine
                 % them in the subterm
                 let (Some p1') = pathDifference (p1, p2) in
                 let (Some (Tsub, _, _)) =
                   matchEquality (proofPredicate_Internal sub_pf2)
                 in
                 prove_equalSubTerm (M, P, T1, p2,
                                     prove_equalTrans
                                       (prove_equalSubTerm
                                          (fromPathTerm(M, p2),
                                           fromPathTerm(N1, p2),
                                           Tsub, p1', return sub_pf1),
                                        return sub_pf2))
               | (Proof_EqSubterm(_,_,_,p1,sub_pf1),
                  Proof_EqSubterm(_,_,_,p2,sub_pf2))
               | pathExtends? (p2, p1) ->
                 let (Some p2') = pathDifference (p2, p1) in
                 let (Some (Tsub, _, _)) =
                   matchEquality (proofPredicate_Internal sub_pf2)
                 in
                 prove_equalSubTerm (M, P, T1, p1,
                                     prove_equalTrans
                                       (return sub_pf1,
                                        prove_equalSubTerm
                                          (fromPathTerm(N2, p1),
                                           fromPathTerm(P, p1),
                                           Tsub, p2', return sub_pf2)))
               | (Proof_EqTrans (T, M1, pfs1), Proof_EqTrans (_, _, pfs2)) ->
                 mkProof_EqTrans (T, M1, pfs1 ++ pfs2)
               | (Proof_EqTrans (T, M1, pfs1), _) ->
                 mkProof_EqTrans (T, M1, pfs1 ++ [(pf2_int, P)])
               | (_, Proof_EqTrans (T, _, pfs2)) ->
                 mkProof_EqTrans (T, M, (pf1_int, N1)::pfs2)
               | _ -> mkProof_EqTrans (T1, M, [(pf1_int, N1),(pf2_int, P)]))
          else
          proofError ("Attempt to apply transitivity of equality at different types: proof of ("
                        ^ printTerm pf1_pred ^ ") is at type ("
                        ^ printType T1 ^ ") while proof of ("
                        ^ printTerm pf2_pred ^ ") is at type ("
                        ^ printType T2 ^ ")")
        | _ ->
          proofError ("Attempt to apply transitivity of equality to proofs of ("
                        ^ printTerm pf1_pred ^ ") and (" ^ printTerm pf2_pred ^ ")")
          }

  % prove P=>R from proof pf1 of P=>Q and pf2 of Q=>R
  op prove_implTrans (pf1 : Proof, pf2 : Proof) : Proof =
    { pf1_int <- pf1; pf2_int <- pf2;
      pf1_pred <- return (proofPredicate_Internal pf1_int);
      pf2_pred <- return (proofPredicate_Internal pf2_int);
      case (matchImplication pf1_pred, matchImplication pf2_pred) of
        | (Some (P, Q1), Some (Q2, R)) | equalTerm? (Q1, Q2) ->
          % Proof simplification: if both implications are proved
          % using equality, then combine the equality proofs
          (case (pf1_int, pf2_int) of
             | (Proof_ImplEq pf1_int', Proof_ImplEq pf2_int') ->
               prove_implEq (prove_equalTrans (return pf1_int',
                                               return pf2_int'))
             | _ ->
               return (Proof_ImplTrans (P, pf1_int, Q1, pf2_int, R)))
        | _ ->
          proofError ("Attempt to apply transitivity of implication to proofs of ("
                        ^ printTerm pf1_pred ^ ") and (" ^ printTerm pf2_pred ^ ")")
          }

  % prove P=>Q from a proof of P=Q
  op prove_implEq (pf : Proof) : Proof =
    { pf_int <- pf;
      let pf_pred = proofPredicate_Internal pf_int in
      case matchEquality pf_pred of
        | Some _ -> return (Proof_ImplEq pf_int)
        | _ ->
          proofError ("Attempt to prove implication by equality from a non-equality proof of "
                        ^ printTerm pf_pred) }

  % prove P=>P
  op prove_implRefl (P: MSTerm) : Proof =
    prove_implEq (prove_equalRefl (boolType, P))

  % Build a proof using MergeRules; the actual predicate being proved
  % is MergeRules.mergeRulesPredicate tree
  op prove_MergeRules (tree,post,unfolds,smtArgs) : Proof =
    return (Proof_MergeRules (tree,post,unfolds,smtArgs))


  %%
  %% Proofs that term1 refines to term2, either by showing term1=term2
  %% or that term2=>term1, depending on the context, where the
  %% "context" is given by a flag.
  %%
  %% NOTE: implication proofs for refinement are "backwards" to the
  %% equality proofs. This can mess you up if you aren't careful.
  %%

  % prove_refinesEqualSubTerm(M,N,T,implProof?,p,pf) proves that
  % either M=N at type T, if implProof?=false, or that N=>M, if
  % implProof?=true, using a proof pf that the subterms of M and N at
  % path p are equal. NOTE: we assume that M and N both have type T
  op prove_refinesEqualSubTerm(M: MSTerm, N: MSTerm, T: MSType,
                               implProof?: Bool, p: Path, pf: Proof) : Proof =
    let eq_pf = prove_equalSubTerm (M, N, T, p, pf) in
    if implProof? then prove_implEq (prove_equalSym eq_pf) else eq_pf

  % Compose two refinement proofs pf1 : M=N and pf2 : N=P to a proof
  % that M=P, if implProof?=false, or proofs pf1 : N=>M and pf2 : P=>N
  % to a proof that P=>M, if implProof?=true.
  op prove_refinesTrans (pf1: Proof, pf2: Proof, implProof?: Bool) : Proof =
    if implProof? then
      prove_implTrans (pf2, pf1)
    else
      prove_equalTrans (pf1, pf2)


end-spec
