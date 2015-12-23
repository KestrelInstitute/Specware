(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)


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
  import /Library/PrettyPrinter/BjornerEspinosa
  import /Languages/MetaSlang/Specs/Printer

  % Forward references
  op SpecNorm.typePredTermNoSpec(ty0: MSType, tm: MSTerm): MSTerm
  op MergeRules.mapTraceTree (tsp: TSP_Maps_St) (t: TraceTree) : TraceTree
  op HigherOrderMatching.substituteWithBeta (subst: MSVarSubst) (term: MSTerm) (boundVars:MSVars): MSTerm

  % A proof tactic
  type Tactic =
    % A string, to be interpreted by the prover
    | StringTactic String
    % The "auto" tactic, possibly augmented by some additional proofs
    | AutoTactic (List Proof)
    % An arbitrary tactic possibly augmented by additional proofs,
    % where the "tactic" gets names for the proofs as arguments
    | WithTactic (List Proof * (List String -> String))

  % The internal form of proofs
  type ProofInternal =
    %% General proof constructs

    % Proof_Cut (P, Q, pf1, pf2) takes pf1 : P=>Q and pf2 : P
    % and creates a proof of Q
    | Proof_Cut (MSTerm * MSTerm * ProofInternal * ProofInternal)

    % Proof_ImplIntro (P, Q, nm, pf) takes pf : Q, which can use the
    % named assumption nm : P, and creates a proof of P=>Q
    | Proof_ImplIntro (MSTerm * MSTerm * String * ProofInternal)

    % Proof_Assump (nm, P) takes the name nm of an assumption of P and
    % builds a proof of P
    | Proof_Assump (String * MSTerm)

    % Proof_ForallE (x,T,M,N,pf1,pf2) is a proof of M=[N/x]P from a
    % proof pf1 : fa(x:T)P and a proof pf2 : typePredTermNoSpec(T,N)
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

    % Proof_UnfoldDef (T, qid, vars, M, N) is a proof that
    % fa(vars) M=N at type T by unfolding the definition of qid.
    | Proof_UnfoldDef (MSType * QualifiedId * MSVars * MSTerm * MSTerm)

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
      | Proof_ImplIntro (P, Q, nm, pf) -> mkImplies (P,Q)
      | Proof_Assump (nm, P) -> P
      | Proof_ForallE (x,T,M,N,pf,tp_pf) -> M
      | Proof_EqTrue (M, pf) -> M
      | Proof_Theorem (id, P) -> P
      | Proof_Tactic (tact, P) -> P
      | Proof_EqSubterm(M,N,T,p,pf) -> mkEquality (T,M,N)
      | Proof_UnfoldDef (T, qid, vars, M, N) ->
        let body = mkEquality (T, M, N) in
        if vars = [] then body else mkBind (Forall, vars, body)
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

  % Pretty-print a Tactic
  op printTacticPP (tact : Tactic) : Pretty =
    case tact of
      | StringTactic str -> string str
      | AutoTactic pfs ->
        prBreak 2 [string "auto[",
                   prBreak 0 (addSeparator (string ", ")
                                (map printProofPP pfs)),
                   string "]"]
      | WithTactic(pfs, _) ->
        prBreak 2 [string "WithTactic(",
                   prBreak 0 (addSeparator (string ", ")
                                (map printProofPP pfs)),
                   string ")"]

  % Pretty-print a ProofInternal
  op printProofPP_Internal (p : ProofInternal) : Pretty =
    let def ppList (pps : List Pretty) : Pretty =
      prBreak 2
        [string "[", prBreak 0 (addSeparator (string ", ") pps), string "]"]
    in
    let def printForm ctor elems =
      prBreak 2 [string (ctor ^ "("),
                 prBreak 0 (addSeparator (string ", ") elems),
                 string ")"]
    in
    let def ppQid qid = string (printQualifiedId qid) in
    case p of
      | Proof_Cut (P, Q, pf1, pf2) ->
        printForm "Cut" [printTermPP P, printTermPP Q,
                         printProofPP_Internal pf1,
                         printProofPP_Internal pf2]
      | Proof_ImplIntro (P, Q, nm, pf) ->
        printForm "ImplIntro" [printTermPP P, printTermPP Q,
                               string nm, printProofPP_Internal pf]
      | Proof_Assump (nm, P) ->
        printForm "Assump" [string nm, printTermPP P]
      | Proof_ForallE (x,T,M,N,pf,tp_pf) ->
        printForm "ForallE" [string x, printTypePP T,
                             printTermPP M, printTermPP N,
                             printProofPP_Internal pf,
                             printProofPP_Internal tp_pf]
      | Proof_EqTrue (M, pf) ->
        printForm "EqTrue" [printTermPP M,
                            printProofPP_Internal pf]
      | Proof_Theorem (id, P) ->
        printForm "Theorem" [ppQid id, printTermPP P]
      | Proof_Tactic (tact, P) ->
        printForm "Tactic" [printTacticPP tact, printTermPP P]
      | Proof_EqSubterm(M,N,T,p,pf) ->
        printForm "EqSubterm" [printTermPP M, printTermPP N, printTypePP T,
                               string (printPath p), printProofPP_Internal pf]
      | Proof_UnfoldDef (T, qid, vars, M, N) ->
        printForm "UnfoldDef"
        [printTypePP T, ppQid qid,
         ppList (map (fn (id,_) -> string id) vars),
         printTermPP M, printTermPP N]
      | Proof_EqSym(pf) -> printForm "Sym" [printProofPP_Internal pf]
      | Proof_EqTrans (T, M1, pfs) ->
        printForm "EqTrans"
        [printTypePP T, printTermPP M1,
         ppList (flatten
                   (map (fn (pf,tm) -> [printProofPP_Internal pf,
                                        printTermPP tm]) pfs))]
      | Proof_ImplTrans(P,pf1,Q,pf2,R) ->
        printForm "ImplTrans" [printTermPP P, printProofPP_Internal pf1,
                               printTermPP Q, printProofPP_Internal pf2,
                               printTermPP R]
      | Proof_ImplEq pf ->
        printForm "ImplEq" [printProofPP_Internal pf]
      | Proof_MergeRules(tree,post,unfolds,smtArgs) ->
        printForm "MergeRules" [string "(* TraceTree *)", printTermPP post,
                                ppList (map ppQid unfolds),
                                ppList (map ppQid smtArgs)]

  % Pretty-print a ProofInternal
  op printProof_Internal (p : ProofInternal) : String =
    PrettyPrint.toString (format (80, printProofPP_Internal p))

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
      | Proof_ImplIntro (P, Q, nm, pf) ->
        Proof_ImplIntro (instantiateTyVarsInTerm (P, s),
                         instantiateTyVarsInTerm (Q, s),
                         nm,
                         substTypes_ProofInternal (s, pf))
      | Proof_Assump (nm, P) ->
        Proof_Assump (nm, instantiateTyVarsInTerm (P, s))
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
      | Proof_UnfoldDef (T, qid, vars, M, N) ->
        Proof_UnfoldDef (instantiateTyVarsInType (T, s), qid, vars,
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
      | Proof_ImplIntro (P, Q, nm, pf) ->
        prove_implIntro (nm, mapTerm tsp P, mapProof_Internal tsp pf)
      | Proof_Assump (nm, P) ->
        return (Proof_Assump (nm, mapTerm tsp P))
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
      | Proof_UnfoldDef (T, qid, vars, M, N) ->
        prove_equalUnfold (mapType tsp T, qid, vars,
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
      | WithTactic(pfs, m) ->
        WithTactic (map (mapProof "(recursive mapTactic)" tsp) pfs, m)


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
  op proofSilentMode? : Bool = true
  op proofError (err_str: String) : Proof =
    if proofSilentMode? then ErrorFail err_str else
      fail err_str

  % A bogus proof object, which will "percolate up", i.e., which will
  % always produce bogus proofs when combined with other proofs
  op bogusProof : Proof = ErrorFail "Bogus proof!"

  % Print out a representation of a proof
  op printProofPP (p : Proof) : Pretty =
  case p of
    | ErrorOk p_int ->
      prBreak 2 [string "Ok (",
                 printProofPP_Internal p_int,
                 string ")"]
    | ErrorFail str -> string ("Error (" ^ str ^ ")")

  % Print out a representation of a proof
  op printProof (p : Proof) : String =
    PrettyPrint.toString (format (80, printProofPP p))

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
        | Some (P, Q) | equalTermAlpha? (P, p2_pred) ->
          return (Proof_Cut (P, Q, p1_int, p2_int))
        | _ -> proofError ("Implication elimination of predicate:\n  " ^ printTerm p1_pred
                             ^ "\nagainst\n  " ^ printTerm p2_pred) }

  % prove_implIntro (nm, P, pf) takes an assumption name nm for P, as
  % well as a proof pf:Q that possibly uses nm, and builds a proof of P=>Q
  op prove_implIntro (nm : String, P : MSTerm, p : Proof) : Proof =
    { p_int <- p;
      Q <- return (proofPredicate_Internal p_int);
      return (Proof_ImplIntro (P, Q, nm, p_int)) }

  % prove_assump (nm, P) takes an assumption name nm for P and creates a proof
  % of P. This only makes sense inside a proof p that is passed as the third
  % argument to prove_implIntro (nm,P,p), but it is up to the user to ensure this.
  op prove_assump (nm : String, P : MSTerm) : Proof =
    return (Proof_Assump (nm, P))

  % prove_forallElim (pf, N, tp_pf) takes a proof pf1:fa(x:T)M, a term
  % N of type T, and a proof tp_pf that N does indeed have type T, and
  % builds a proof of [N/x]M.
  op prove_forallElim (p : Proof, N : MSTerm, tp_pf : Proof) : Proof =
    { p_int <- p;
      p_pred <- return (proofPredicate_Internal p_int);
      tp_int <- tp_pf;
      tp_pred <- return (proofPredicate_Internal tp_int);
      case matchForall1 p_pred of
        | Some (x, T, P) ->
          let tp_pred_expected = typePredTermNoSpec(T,N) in
          (case p_int of
             | _ | ~(equalTermAlpha? (tp_pred, tp_pred_expected)) ->
               proofError ("Bad typing proof in forall elimination: expected:\n  "
                             ^ printTerm tp_pred_expected ^ "\nfound\n  "
                             ^ printTerm tp_pred)
             | Proof_UnfoldDef (T_body, qid, var::vars, lhs, rhs) ->
               % Proof optimization: substitute for the first free
               % variable in an "unfold" proof
               return (Proof_UnfoldDef
                         (T_body, qid, vars,
                          substituteWithBeta [(var,N)] lhs (freeVars N),
                          substituteWithBeta [(var,N)] rhs (freeVars N)))
             | Proof_Theorem (qid, _) ->
               % Proof optimization: use the theorem qid to prove
               % [N/x]P (the predicate "_" must equal P)
               return (Proof_Theorem
                         (qid,
                          substituteWithBeta [((x,T),N)] P (freeVars N)))
             | _ ->
               let M = substituteWithBeta [((x,T),N)] P (freeVars N) in
               return (Proof_ForallE (x, T, M, N, p_int, tp_int)))
        | _ -> proofError ("Forall elimination of predicate\n  " ^ printTerm p_pred
                             ^ "\nagainst term\n  " ^ printTerm N ^ ")") }

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
        | Some (_, M', N) | equalTermAlpha? (M,M') && equalTermAlpha? (N,mkTrue()) ->
          return (Proof_EqTrue (M, p_int))
        | _ -> proofError ("Incorrect use of equalTrue rule: attempt to prove:\n  " ^ printTerm M
                             ^ "\nfrom a proof of:\n  " ^ printTerm p_pred) }

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

  op extendProofAuto (tm: MSTerm) (pf: Proof): Proof =
  case  pf of
    | ErrorOk(Proof_Tactic _) -> pf
    | ErrorOk(pf_int) ->
      prove_withTactic (AutoTactic [pf], tm)
    | _ -> pf

%% This is a temporary version. Really want something that will handle
%% relationship between ~b and b = false
 op replaceProofTerm (tm: MSTerm) (pf: Proof): Proof =
   case pf of
     | ErrorOk i_pf -> 
       ErrorOk(case i_pf of
                 | Proof_Assump(str, _) -> Proof_Assump(str, tm)
                 | Proof_Tactic(tct, _) -> Proof_Tactic(tct, tm)
                 | _ -> i_pf)
     | _ -> pf

% build an equality proof with a tactic
  op prove_equalWithTactic (tactic : Tactic, M : MSTerm, N : MSTerm, T : MSType) : Proof =
    return (Proof_Tactic (tactic, mkEquality (T,M,N)))

  % build a proof (fa (vars) M=N) at type T by unfolding the
  % definition of qid (NOTE: the assumption that unfolding qid in M
  % results in N is not checked)
  op prove_equalUnfold (T : MSType, qid : QualifiedId,
                        vars : MSVars, M : MSTerm, N : MSTerm) : Proof =
    return (Proof_UnfoldDef (T, qid, vars, M, N))

  % prove_equalSubTerm(M,N,T,p,pf) proves that M=N at type T using a
  % proof pf that the subterms of M and N at path p are equal. NOTE:
  % we assume that M and N both have type T
  op prove_equalSubTerm (M : MSTerm, N : MSTerm, T : MSType, p : Path, pf : Proof) : Proof =
    let def fromPathTermWithBindingsErr (tm, path) : Monad (MSVars * MSTerm) =
      case validPathTermWithErr (tm, path) of
        | Some (bad_path, bad_subterm, i) ->
          ErrorFail ("prove_equalSubTerm: cannot take subterm " ^ show i
                       ^ " of subterm (" ^ printTerm bad_subterm
                       ^ ") at path " ^ printPath bad_path ^ " in term ("
                       ^ printTerm tm ^ ")")
        | None -> return (fromPathTermWithBindings (tm, path))
    in
    { pf_int <- pf;
      pf_pred <- return (proofPredicate_Internal pf_int);
      (varsM, M_sub) <- fromPathTermWithBindingsErr (M, p);
      (varsN, N_sub_orig) <- fromPathTermWithBindingsErr (N, p);
      let (vars_ok?, N_sub) =
        if length varsM = length varsN then
          if varsM = varsN then (true, N_sub_orig) else
            (true, substitute (N_sub_orig, zip (varsN, map mkVar varsM)))
        else (false, N_sub_orig)
      in
      case matchEquality pf_pred of
        | Some (_, M', N') | vars_ok? && equalTermAlpha? (M', M_sub) && equalTermAlpha? (N', N_sub) ->
          % Proof optimization
          (case pf_int of
             | _ | p = [] ->
               % Handle special case where p is the empty path
               return pf_int
             | Proof_EqSubterm(M',N',T',p',pf_int') ->
               % Collapse nested subterm proofs
               % README: inner path comes before outer path
               prove_equalSubTerm (M,N,T,p'++p, return pf_int')
             | Proof_EqTrans (Tsub, Msub, []) ->
               % Move reflexivity proofs to the outer level
               prove_equalRefl (T, M)
             | _ ->
               return (Proof_EqSubterm(M,N,T,p,pf_int)))
        | _ -> proofError ("Attempt to prove equality of subterms\n  " ^
                             printTermIndent (2, fromPathTerm (M,p)) ^
                             "\nand\n  " ^ printTermIndent (2, fromPathTerm (N,p))
                             ^ "\nfrom a proof of:\n  " ^ printTermIndent (2, pf_pred)
                             ^ "\n(proof:\n" ^ printProof_Internal pf_int ^ ")") }

op matchCondEquality (t : MSTerm) : Option (MSType * MSTerm * MSTerm) =
  case t of
    | Apply(Fun(Equals, typ, _), Record([("1", lhs), ("2", rhs)], _), _) ->
      (case typ of
         | Arrow (_, range, _) -> Some (range, lhs, rhs)
         | _ -> fail ("Unexpected type for =: " ^ printType typ))
    | Apply(Fun(Implies, _, _), Record([("1", lhs), ("2", rhs)], _), _) ->
      matchCondEquality rhs
    | _ -> None

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
        | Some (T, M, N) ->
          % Proof optimization: we try to move symmetry proofs
          % downwards to the leaves of the proof
          (case pf_int of
             | Proof_EqSym pf_int' ->
               % remove double-symmetry
               return pf_int'
             | Proof_EqSubterm (M',N',T',p,pf_int') ->
               % propagate symmetry into subterm proofs
               prove_equalSubTerm (N',M',T',p,prove_equalSym (return pf_int'))
             | Proof_EqTrans (T',M1,pfs_terms) ->
               % propagate symmetry into transitivity proofs as well,
               % by applying symmetry to each sub-proof and composing
               % them in reverse order with transitivity
               foldl (fn (pf, (pf_int,_)) ->
                        prove_equalTrans (prove_equalSym (return pf_int), pf))
                 (prove_equalRefl (T', M1)) pfs_terms
             | _ ->
               return (Proof_EqSym pf_int))
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
        | (Some (T1, M, N1), Some (T2, N2, P)) | equalTermAlpha? (N1, N2) ->
          if equalType? (T1, T2) then
            let def mkProof_EqTrans (Tret, Mret, pfs_ret) =
              case pfs_ret of
                % Don't need to build a trans proof with one proof!
                | [(pf_ret, _)] -> return pf_ret
                | _ -> return (Proof_EqTrans (Tret, Mret, pfs_ret))
            in
            (case (pf1_int, pf2_int) of
               | _ | equalTermAlpha? (M, N1) ->
                 % The first proof is really reflexivity, so drop it
                 return pf2_int
               | _ | equalTermAlpha? (N2, P) ->
                 % The second proof is really reflexivity, so drop it
                 return pf1_int
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
        | (Some (P, Q1), Some (Q2, R)) | equalTermAlpha? (Q1, Q2) ->
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

end-spec
