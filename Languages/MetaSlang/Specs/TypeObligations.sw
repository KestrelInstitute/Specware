(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

TypeObligations qualifying
spec 
 import /Languages/MetaSlang/Transformations/CurryUtils
 import /Languages/MetaSlang/Transformations/Simplify
 import /Languages/MetaSlang/Transformations/ProverPattern
 import /Languages/MetaSlang/Transformations/RenameBound

 import /Languages/MetaSlang/CodeGen/Generic/InstantiateHOFns

 import /Languages/MetaSlang/CodeGen/Generic/PatternMatch
 import /Languages/MetaSlang/CodeGen/Generic/LambdaLift

 import /Languages/SpecCalculus/Semantics/Evaluate/Signature
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/MergeSpecs

 %type SpecElement  = QualifiedId * TyVars * MSTerm 
 type TypeCheckConditions = SpecElements * StringSet.Set

 op makeTypeCheckObligationSpec: Spec * Bool * (String * String -> Bool) * String -> Spec
 op checkSpec : Spec * Bool * (String * String -> Bool) * String -> TypeCheckConditions

 op simplifyObligations?: Bool = true
 op dontGenerateTrueObligs?: Bool = true
 op simplifyFalseObligations?: Bool = false
 op removeExcessAssumptions?: Bool = false
 %% These two should be false for Isabelle conversion
 op generateTerminationConditions? : Bool = true
 op generateExhaustivityConditions?: Bool = true
 op traceObligationSimplify?: Bool = false
 op reportTrivialObligationCount?: Bool = false

 op termSubstSizeLimit: Nat = 20



% Auxiliary variable environment.
% Gamma maps local variables to their types,
% and also accumulates local context assertions.

 type Decl  = 
   | Var    MSVar 
   | Cond   MSTerm                 
   | LetRec List (MSVar     * MSTerm) 
   | Let    List (MSPattern * MSTerm)

 type Gamma = List Decl * TyVars * Spec * Option (QualifiedId * MSPatterns) * QualifiedId
                * Option MSType * NameSupply * Bool * Ref Nat

 op  insert       : MSVar * Gamma -> Gamma
 op  assertCond   : MSTerm * Gamma * String -> Gamma
 op  insertLet    : List (MSPattern * MSTerm) * Gamma -> Gamma
 op  insertLetRec : List (MSVar     * MSTerm) * Gamma -> Gamma

 op  assertSubtypeCond: MSTerm * MSType * Gamma -> Gamma
 def assertSubtypeCond(term, srt, gamma) = 
     case srt
       of Subtype(srt, pred, _) ->
          let (ds, tvs, spc, qid, name, ty, names, lift?, trivs) = gamma in
          assertSubtypeCond(term, srt, (Cons(Cond(mkLetOrApply(pred, term, gamma)), ds),
                                        tvs, spc, qid, name, ty, names, lift?, trivs))
        | _ -> gamma

 op  mkLetOrApply: MSTerm * MSTerm * Gamma -> MSTerm
 def mkLetOrApply(fntm, arg, (ds, tvs, spc, qid, name, ty, names, lift?, trivs)) =
   let fntm = renameTerm (names, emptyEnv()) fntm in
   case fntm of
     | Lambda ([(VarPat(v as (vn,srt),_),Fun(Bool true, _, _), bod)], _) ->
       % mkLet([(VarPat(v, a), arg)], bod)
       let num_refs = countVarRefs(bod, v) in
       if num_refs <= 1 || (num_refs * termSize arg <= termSubstSizeLimit)
         then substitute(bod, [(v, arg)])
         else
           mkBind(Forall, [v], mkSimpImplies(mkEquality(srt, mkVar v, arg), bod))
     | Lambda ([(RecordPat([("1", VarPat(v1 as (vn1, srt1), _)), ("2", VarPat(v2 as (vn2, srt2), _))], _),
                 Fun(Bool true, _, _), bod)], _)
       ->
       % let _ = writeLine("mkLet: "^printTerm arg^"\n"^printTerm bod) in
       let result = 
       if embed? Record arg
         && ((countVarRefs(bod, v1) <= 1 && countVarRefs(bod, v2) <= 1)
             || (simpleTerm? arg && termSize arg <= termSubstSizeLimit)) 
         then 
           let Record([("1", arg1), ("2", arg2)], _) = arg in
           substitute(bod, [(v1, arg1), (v2, arg2)])
         else
           let v1' = (vn1^"__1", srt1) in
           let v2' = (vn2^"__1", srt2) in
           let sb = [(v1, mkVar v1'), (v2, mkVar v2')] in
           mkBind(Forall, [v1', v2'], mkSimpImplies(mkEquality(mkProduct[srt1, srt2],
                                                               mkTuple[mkVar v1', mkVar v2'],
                                                               arg),
                                                  substitute(bod, sb)))
       in
       % let _ = writeLine(" =\n"^printTerm result) in
       result
     | _ -> mkApply(fntm, arg)

 op traceAssert?: Bool = false
 def assertCond(cond, gamma as (ds, tvs, spc, qid, name, ty, names, lift?, trivs), kind) = 
   case cond of
     | Fun((Bool true, _, _)) -> gamma
     | _ ->
       let _ = if traceAssert? then writeLine("Asserting("^ kind ^") "^printTerm cond) else () in 
       (Cons(Cond cond, ds), tvs, spc, qid, name, ty, names, lift?, trivs)
 def insert((x, srt), gamma as (ds, tvs, spc, qid, name, ty, names, lift?, trivs))  = 
     let ds = Cons(Var(x, srt), ds) in
     let i = case apply(!names, x)
              of None   -> 0
               | Some n -> n
     in
     let _ = names := update(!names, x, i) in
     let gamma = (ds, tvs, spc, qid, name, ty, names, lift?, trivs) in
     let gamma = assertSubtypeCond(mkVar(x, srt), srt, gamma) in
     gamma
% Subtype conditions:
 def insertLet(decls, (ds, tvs, spc, qid, name, ty, names, lift?, trivs)) = 
     (Cons(Let decls, ds), tvs, spc, qid, name, ty, names, lift?, trivs)
 def insertLetRec(decls, (ds, tvs, spc, qid, name, ty, names, lift?, trivs)) =
   let _ = app (fn((x, _), _)-> names := update(!names, x, 0)) decls in
   (Cons(LetRec decls, ds), tvs, spc, qid, name, ty, names, lift?, trivs)

 def printDecl(d:Decl) = 
     case d
       of Var (x, srt) -> x^":"^printType srt
        | Cond term -> "assert "^printTerm term
        | LetRec (decls) -> printTerm (LetRec(decls, mkRecord([]), noPos))
        | Let decls -> printTerm (Let(decls, mkRecord([]), noPos))

 op printGamma: Gamma -> ()
 def printGamma(decls, _, _, _, _, _, _, _, _) = 
     let _ = app (fn decl -> 
                (toScreen (printDecl decl);
                 toScreen "; "))
                (reverse decls)
     in
     let _ = writeLine "" in
     ()
 

 op addCondition : TypeCheckConditions * Gamma * MSTerm * String -> 
                   TypeCheckConditions
 op addFailure :   TypeCheckConditions * Gamma * String -> 
                   TypeCheckConditions

 op freshName : Gamma * String -> String

 op  ?? infixl 9 : [a, b] a * b -> a * b
 def ??(x) = x


 op |- infixl 7 : (TypeCheckConditions * Gamma) * (MSTerm * MSType) -> TypeCheckConditions

 op <= : TypeCheckConditions * Gamma * MSTerm * MSType * MSType * Bool -> TypeCheckConditions

 op getSpec    : Gamma -> Spec
 op unfoldBase : Gamma * MSType -> MSType

 def getSpec (_, _, e, _, _, _, _, _, _) = e

 op lifting?((_, _, _, _, _, _, _, lift?, _): Gamma): Bool = lift?

 def unfoldBase((_, _, spc, _, _, _, _, _, _), tau) = 
     unfoldBeforeCoProduct(spc, tau)

 op trivObligCountRef((_, _, _, _, _, _, _, _, triv_count_ref): Gamma): Ref Nat = triv_count_ref

 op notTypePredTerm? (spc: Spec, vs: MSVars) (t: MSTerm): Bool =
   case t of
     | Apply(p, Var(v as (_,ty), _), _) ->
       ~(inVars?(v, vs) && subtypePred?(ty, p, spc))
     | _ -> true

 op removeRedundantTypePredicates (spc: Spec) (tm: MSTerm): MSTerm =
   mapTerm (fn t ->
              case t of
                | Bind(Forall, vs, Apply(Fun (Implies, _, _), Record([(_,lhs), (_,rhs)], _), _), a) ->
                  let lhs_cjs = filter (notTypePredTerm? (spc, vs)) (getConjuncts lhs) in
                  let rhs_cjs = filter (notTypePredTerm? (spc, vs)) (getConjuncts rhs) in
                  Bind(Forall, vs, mkSimpImplies(mkConj lhs_cjs, mkConj rhs_cjs), a)
                | Bind(Exists, vs, bod, a) ->
                  let cjs = filter (notTypePredTerm? (spc, vs)) (getConjuncts bod) in
                  Bind(Exists, vs, mkConj cjs, a)
                | _ -> t,
            id, id)
     tm

 op evaluateGroundRhs(tm: MSTerm, spc: Spec): MSTerm =
   case tm of
     | Bind(Forall, vs, Apply(Fun (Implies, _, _), Record([(_,lhs), (_,rhs)], _), _), a) ->
       let new_rhs = reduceTerm(rhs, spc) in
       if equalTermAlpha?(rhs, new_rhs) then tm
         else Bind(Forall, vs, mkSimpImplies(lhs, new_rhs), a)
     | _ -> reduceTerm(tm, spc)

 op simplifyObligUnfoldSubtypePredicates?: Bool = true
 op simplifyUnfoldSubtypePredicates (spc: Spec) (tm: MSTerm): MSTerm =
   let tm1 = mapTerm (fn t ->
                      case t of
                        | Fun(Op(Qualified(_, nm), _), _, _)
                            | testSubseqEqual?("_subtype_pred", nm, 0, length nm - 13) ->
                          (case unfoldOpRef(t, spc) of
                           | Some ut -> ut
                           | None    -> t)
                        | _ -> t,
                      id, id)
               tm
   in
   % let _ = writeLine("souf: "^printTerm tm^"\n  --> "^printTerm tm1) in
   let r_tm = simplify spc tm1 in
   % let _ = writeLine("  --> "^printTerm r_tm) in
   r_tm

 op simplifyOblig (spc: Spec) (oblig: MSTerm) (bare_oblig: MSTerm): MSTerm =
   let _ = if traceObligationSimplify? then writeLine("Obligation:\n"^printTerm oblig) else () in
   let oblig1 = if simplifyObligations?
                 then
                   if ~simplifyFalseObligations? && falseTerm?(simplify spc bare_oblig)
                     then oblig
                   else
                   let oblig1 = simplify spc (evaluateGroundRhs (oblig, spc)) in
                   let oblig2 = removeRedundantTypePredicates spc oblig1 in
                   let oblig3 = if equalTermAlpha?(oblig1, oblig2) then oblig2
                                else simplify spc (evaluateGroundRhs(oblig2, spc))
                   in
                   let oblig4 = %if simplifyObligUnfoldSubtypePredicates?
            %                     then simplifyUnfoldSubtypePredicates spc oblig3
            %                     else
                                   oblig3
                   in
                   let _ = if traceObligationSimplify? then writeLine("Simplifies to\n"^printTerm oblig3) else () in
                   if trueTerm? oblig4 then oblig4 else oblig3
               else 
                 let simp_oblig = if dontGenerateTrueObligs? then simplify spc oblig else oblig in
                 let _ = if traceObligationSimplify? then writeLine("Simplifies to\n"^printTerm simp_oblig) else () in
                 if trueTerm? simp_oblig then simp_oblig
                  else oblig
   in
   oblig1

 def addFailure((tcc, claimNames), (_, _, _, _, name as Qualified(qid, id), _, _, _, _), description) = 
     let descName = id^" :"^description in
     let name = mkQualifiedId(qid, descName) in
     (Cons(mkConjecture(name, [], mkFalse()), tcc), StringSet.add(claimNames, descName))

 op  makeVerificationCondition: Gamma * MSTerm * String * StringSet.Set -> Option(QualifiedId * TyVars * MSTerm)
 def makeVerificationCondition((decls, tvs, spc, qid, name as Qualified(qual, id), _, _, _, triv_count_ref),
                               term, id_tag, claimNames) = 
     let
        def insert(formula, decl) = 
            case decl
              of Var v ->        
                 if isFree(v, formula)
                    then mkBind(Forall, [v], formula)
                 else formula
               | Cond (Fun(Bool true, _, _)) -> formula
               | Cond c ->       mkSimpImplies(c, formula)
               | Let decls ->    Let(decls, formula, noPos)
               | LetRec decls -> LetRec(decls, formula, noPos)
     in
     % let _ = writeLine(printTerm term) in
     % let _ = app (fn d -> writeLine(printDecl d)) decls in
     let cterm = foldl insert term decls in
     % let _ = writeLine("Simplifying "^printTerm cterm^"\nto\n"^printTerm(simplify spc cterm)) in
     case simplifyOblig spc cterm term of
       | Fun(Bool true, _, _) ->
         (triv_count_ref := !triv_count_ref + 1;
          None) 
       | Fun(Bool false, _, _) | ~simplifyFalseObligations? ->
         %% Unproveable, but original form gives more information
         Some(mkQualifiedId(qual, StringUtilities.freshName(id^id_tag, claimNames)), tvs, cterm)
       %% In general simplify doesn't change e -> true because of strictness, but that should not be
       %% issue here
       | Apply(Fun (Implies, _, _), Record([("1", t1), ("2", t2)], _), _) | trueTerm? t2 || equalTermAlpha?(t1, t2) ->
         None
       | claim ->
         let claim = if removeExcessAssumptions? then removeExcessAssumptions claim else claim in
         Some(mkQualifiedId(qual, StringUtilities.freshName(id^id_tag, claimNames)), tvs, claim)

 def addCondition(tcc as (tccs, claimNames), gamma, term, id_tag) =
   case makeVerificationCondition(gamma, term, id_tag, claimNames) of
     | Some condn -> let Qualified(_, cname) = condn.1 in
                     (Cons(mkConjecture condn, tccs), StringSet.add(claimNames, cname))
     | None       -> tcc

% Generate a fresh name with respect to all the
% names previously used in spec (as ops) and
% for the bound variables.
%
 def freshName((_, _, _, _, _, _, names, lift?, trivs), name) =
   fresh names name

 op  freshVar: Id * MSType * Gamma -> MSTerm * Gamma
 def freshVar(name0, sigma1, gamma) =
   let x = freshName(gamma, name0) in
   let xVar   = mkVar(x, sigma1) in
   let gamma1 = insert((x, sigma1), gamma) in
   (xVar, gamma1)

 %%% If sigma1 is a product produce a product of new vars
 op  freshVars: Id * MSType * Gamma -> MSTerm * Gamma
 def freshVars(name0, sigma1, gamma) =
   case sigma1 of
     | Product(prs, _) ->
       let (vsprs, rgamma)
          = foldl (fn ((vs, gamma), (id, s)) ->
                   let (nv, ngamma) = freshVar(name0, s, gamma) in
                   (Cons((id, nv), vs), ngamma))
              ([], gamma) prs
       in
       (mkRecord(reverse vsprs), rgamma)
     | _ -> freshVar(name0, sigma1, gamma)

% check type well formedness as well...

 def |-((tcc, gamma), (M, tau)) =
   % let _ = writeLine("\n.. |- ("^printTerm M^", "^printType tau^")\n") in
   case M
     of Apply(N1, N2, _) ->
        let spc = getSpec gamma in
        let sigma1 = inferType(spc, N1) in
        (case N1 of 
           | Lambda(rules, _) ->
             let dom_sig = domain(spc, sigma1) in
             let tcc  = (tcc, gamma) |- N2 ?? dom_sig  in
             %% Following is at best redundant, at worst assumes better inferType
             % let tau2 = range(spc, sigma1) in
             % let tcc  = <= (tcc, gamma, M, tau2, tau, true) in
             let lam_tau = mkArrow(dom_sig, tau) in
             checkLambda(tcc, gamma, rules, lam_tau, Some N2)
           | Fun(Restrict, s, _) ->
             let (dom, ran) = arrow(spc, s) in
             let tcc  = (tcc, gamma) |- N2 ?? ran                  in
             let tcc  = <= (tcc, gamma, N2, ran, tau, true)        in
             tcc
           | _ ->
         let tcc  = (tcc, gamma) |- N1 ?? sigma1                   in
         case nonStrictAppl(N1, N2) of
           | Some (p1, p2, polarity) ->
             let tcc   = (tcc, gamma)   |- p1 ?? boolType          in
             let gamma1 = assertCond(if polarity then p1 else negateTerm p1, gamma, "nonStrict") in
             let tcc   = (tcc, gamma1) |- p2 ?? boolType           in
             let tcc   = <= (tcc, gamma, M, boolType, tau, true)   in
             tcc
           | _ ->
             let tcc  = (tcc, gamma) |- N2 ?? domain(spc, sigma1)  in
             let tau2 = range(spc, sigma1)                         in
             let tcc  = <= (tcc, gamma, M, tau2, tau, true)        in
             let tcc  = tcc %% if generateTerminationConditions?
                            %%   then checkRecursiveCall(tcc, gamma, M, N1, N2)
                            %%   else tcc
             in tcc)
      | Record(fields, _) -> 
        let spc = getSpec gamma in
        let tau_types = product(spc, tau) in
        let
            def checkField(tcc, (id, term), (id2, tau)) = 
                (tcc, gamma) |- term ?? tau
        in
        % Check recursively that every element is well typed 
        let tcc = ListPair.foldl checkField tcc (fields, tau_types) in
        % Check possible subtype constraints in tau 
        let tcc = if subtype?(spc, tau)
                    then <= (tcc, gamma, M, inferType(spc, M), tau, false)
                    else tcc
        in
        tcc

      | Bind(binder, vars, body, _) -> 
        let gamma = foldl (fn (x, y) -> insert(y, x))  gamma vars in
        let tcc = (tcc, gamma) |- body ?? boolType  in
        let tcc = <= (tcc, gamma, M, boolType, tau, true) in
        tcc
      | The(v as (_, srt), body, _) ->
        % let _ = writeLine("The_oblig:\n"^printTerm(mkBind(Exists1, [v], body))) in
        let tcc = addCondition(tcc, gamma, mkBind(Exists1, [v], body), "_the") in
        let gamma = insert (v, gamma) in
        let tcc = (tcc, gamma) |- body ?? boolType  in
        let tcc = <= (tcc, gamma, M, srt, tau, true) in
        tcc
      | Let(decls, body, _)    ->
        let (tcc, gamma) =
             foldl (fn ((tcc, ngamma), (pat, trm)) ->
                    let sigma1 = patternType pat in
                    let (ngamma, tp) = bindPattern(ngamma, pat, sigma1) in
                    %% This is alternative to insertLet below
                    let ngamma = assertCond(mkEquality(inferType(getSpec gamma, trm),
                                                       trm,
                                                       tp),
                                            ngamma, "let-pattern")
                    in
                    let spc = getSpec gamma in
                    let tcc = (tcc, gamma) |- trm ?? sigma1 in
                    let tcc = addQuotientCondition(tcc, gamma, pat, body, Some trm) in
                    (tcc, ngamma))
                (tcc, gamma)
                decls
        in
        %let gamma = insertLet(decls, gamma) in
        let tcc = (tcc, gamma) |- body ?? tau in
        tcc

      | LetRec(decls, body, _) ->
        let gamma = foldl (fn (gamma, (v, _)) -> insert(v, gamma))
                      gamma decls
        in
        let tcc =
            foldl (fn (tcc, ((_, srt), t)) ->
                   let spc = getSpec gamma in
                   let tcc = (tcc, gamma) |- t ?? srt in
                   tcc)
              tcc
              decls
        in
        let gamma = insertLetRec(decls, gamma)      in
        let tcc = (tcc, gamma) |- body ?? tau       in
        tcc
      | Var((id, srt), _) -> 
        let tcc = <= (tcc, gamma, M, srt, tau, true)         in
        tcc
      | Fun(f, s, _) -> 
        let tcc = <= (tcc, gamma, M, s, tau, true)           in
%
% List subcases explicitly to leave place for 
% special treatment.
%
        (case f of
           | Not         -> tcc 
           | And         -> tcc 
           | Or          -> tcc 
           | Implies     -> tcc 
           | Iff         -> tcc 
           | Equals      -> tcc 
           | NotEquals   -> tcc 
           | Quotient qid -> tcc  % TODO: anything? (or is this subsumed by treatment of s in Fun(f, s, _)?
           | Choose   qid -> tcc  % TODO: anything? (or is this subsumed by treatment of s in Fun(f, s, _)?
           | Restrict    -> tcc 
           | Relax       -> tcc 
           | Op(id, fx)  -> tcc
           | RecordMerge -> tcc
           | Project n   -> tcc
           | Embed(n, b) -> tcc
           | Embedded  n -> tcc
           | Select    n -> tcc
           | Nat       i -> tcc 
           | Char      c -> tcc
           | String    s -> tcc
           | Bool      b -> tcc
           | _           -> tcc
        )
%%
%% This checks that pattern matching is exhaustive.
%%
      | Lambda(rules, _) | length rules <= 1 ->
        let tau2 = inferType(getSpec gamma, M) in
        let tcc  = <= (tcc, gamma, M, tau2, tau, true)  in
        checkLambda(tcc, gamma, rules, tau, None)

      | Lambda(rules as (pat, _, body)::_, a) ->        % eta-normalize to simple pattern & case
        let (v, gamma) = freshVar("eV", patternType pat, gamma) in
        let Var v_t = v in
        |-((tcc, gamma), (Lambda([(VarPat v_t, mkTrue(), mkApply(M, v))], a), tau))

      | IfThenElse(t1, t2, t3, _) -> 
        let tcc1   = (tcc, gamma)   |- t1 ?? boolType           in
        let gamma1 = assertCond(t1, gamma, "if-true")           in
        let tcc2   = (tcc1, gamma1) |- t2 ?? tau                in
        let gamma2 = assertCond(negateTerm t1, gamma, "if-false") in
        let tcc3   = (tcc2, gamma2) |- t3 ?? tau                in
        tcc3
      | Seq([], _)    -> tcc
      | Seq([M], _)   -> (tcc, gamma) |- (M, tau)       
      | Seq(M::Ms, _) -> 
        let sigma = inferType(getSpec gamma, M)                 in
        let tcc   = (tcc, gamma) |- M ?? sigma                  in
        let tcc   = (tcc, gamma) |- Seq(Ms, noPos) ?? tau       in
        tcc
      | Any _ -> tcc

 op  nonStrictAppl: MSTerm * MSTerm -> Option (MSTerm * MSTerm * Bool)
 def nonStrictAppl(rator, args) =
   case (rator, args) of
     | (Fun(And,     _, _), Record([("1", p), ("2", q)], _)) -> Some (p, q, true)   % p && q  -- can assume  p in q
     | (Fun(Or,      _, _), Record([("1", p), ("2", q)], _)) -> Some (p, q, false)  % p or q -- can assume ~p in q
     | (Fun(Implies, _, _), Record([("1", p), ("2", q)], _)) -> Some (p, q, true)   % p => q -- can assume  p in q
     | _ -> None

 op  checkLambda: TypeCheckConditions * Gamma * MSMatch * MSType * Option MSTerm -> TypeCheckConditions
 def checkLambda(tcc, gamma, rules, tau, optArg) =
   let spc = getSpec gamma in
   let dom = domain(spc, tau) in
   let rng = range (spc, tau) in
   let casesDisjoint? = disjointMatches rules in
   let (tcc, _) = foldl (checkRule(dom, rng, optArg, casesDisjoint?)) (tcc, gamma) rules  in
   let exhaustive? = exhaustivePatterns?(map (project 1) rules, dom, spc) in
   % let _ = writeLine("\nExh "^show exhaustive?^": "^printType dom) in
   % let _ = app (fn (p,_,_) -> writeLine(printPattern p)) rules in
   if exhaustive? then tcc
   else
   let arg = case optArg of
               | Some arg -> arg
               | None -> mkVar(freshName(gamma, "D"), dom)
   in
   let disjs = map (fn(p, c, _) ->
                      let (tm, conds, vs) = patternToTermPlusExConds p in
                      let conds = if trueTerm? c then conds
                                  else
                                    c::conds
                      in
                      let condn = mkConj(mkEquality(dom, arg, tm) :: conds) in
                      if vs = [] then condn
                        else mkBind(Exists, vs, condn))
                rules
   in
   let disj_tm = mkOrs disjs in
   % let _ = writeLine("exh0?: "^printTerm disj_tm) in
   let vs = freeVars arg in
   case simplify spc disj_tm of
     | Fun(Bool true, _, _) -> tcc
     | trm -> if generateExhaustivityConditions?
                 then % let _ = writeLine("exh1?: "^printTerm trm) in
                  let frm = case optArg of
                              | Some(Var (v,_)) -> trm
                              | _ ->
                            case arg of
                              | Var(Dv, _) | Dv in? vs ->
                                mkBind(Forall, [Dv], trm)
                              | _ -> trm
                  in
                  addCondition(tcc, gamma, frm, "_exhaustive")
              else tcc


%   let rules = map (fn(p, c, b) -> ([p], c, mkTrue())) rules in
%    let x = case optArg of
%               | Some(Var (v,_)) -> v
%               | _ -> (freshName(gamma, "D"), dom)
%    in
%    let vs = [mkVar x] in
%    let (_, _, spc, _, Qualified(_, name), _, _, _, _) = gamma in
%    let context = {counter    = Ref 0,
%                 spc        = spc,
%                 funName    = name,
%                 errorIndex = Ref 0,
%                 term       = None}
%    in
%    let trm = match(context, vs, rules, mkFalse(), mkFalse()) in
%     let _ = writeLine("exh0?: "^printTerm trm^"\n"^printTerm (simplifyMatch trm)) in
%    (case simplifyMatch(trm)
%       of Fun(Bool true, _, _) -> tcc
%        | trm -> if generateExhaustivityConditions?
%                 then % let _ = writeLine("exh1?: "^printTerm trm) in
%                        let frm = case optArg of
%                                    | Some(Var (v,_)) -> trm
%                                    | _ -> mkBind(Forall, [x], trm)
%                        in
%                        addCondition(tcc, gamma, frm, "_exhaustive")
%                  else tcc)

 op  useNameFrom: Gamma * Option MSTerm * String -> String
 def useNameFrom(gamma, optTm, default) =
   case optTm of
     | Some(Var((nm, _), _)) -> nm
     | _ -> freshName(gamma, default)

 op  checkRule: MSType * MSType * Option MSTerm * Bool
               -> (TypeCheckConditions * Gamma) * (MSPattern * MSTerm * MSTerm)  
               -> TypeCheckConditions * Gamma
 def checkRule(dom, rng, optArg, casesDisjoint?) ((tcc, gamma), (pat, cond, body)) = 
     let (gamma0, tp) = bindPattern(gamma, pat, dom)      in
     let (condn, gamma1)
        = case optArg of
            | Some arg ->
              let condn = mkEquality(inferType(getSpec gamma, arg), arg, tp) in
              let gamma0 = assertCond(condn, gamma0, "case") in
              (condn, gamma0)
            | _ -> (mkTrue(), gamma0)
     in
     let tcc = (tcc, gamma1) |- cond ?? boolType          in
     let gamma2 = assertCond(cond, gamma1, "case-condn")                  in
     let tcc = (tcc, gamma2) |- body ?? rng               in
     let tcc = addQuotientCondition(tcc, gamma, pat, body, optArg) in
     let nextGamma =
         if casesDisjoint? || trueTerm? condn
           then gamma
           else
             assertCond(negateExistTerm(condn, gamma2, gamma), gamma, "not-case")
     in
     (tcc, nextGamma)

 op  negateExistTerm: MSTerm * Gamma * Gamma -> MSTerm
 def negateExistTerm(c, (decls_new, _, _, _, _, _, _, _, _), (decls_old, _, _, _, _, _, _, _, _)) =
   let vs = mapPartial (fn decl -> case decl of
                                     | Var v | isFree(v, c) ->
                                       Some v
                                     | _ -> None)

              (subFromTo(decls_new, 0, length decls_new - length decls_old))
   in
   negateTerm(mkSimpBind(Exists, vs, c))

 op  addQuotientCondition: TypeCheckConditions * Gamma * MSPattern * MSTerm * Option MSTerm
                          -> TypeCheckConditions
 def addQuotientCondition(tcc, gamma, pat, body, optArg) =
   case optArg of
     | Some arg ->
       (case foldSubPatterns (fn (p, result) -> 
                                case p of 
                                  | QuotientPat (VarPat pv, super_type_name, _, _) -> 
                                    %% If the spec has type-checked, there must be an info for the super_type.
                                    let Some info = findTheType (getSpec gamma, super_type_name) in
                                    let Quotient (base_type, _, _) = info.dfn in
                                    Some (pv, base_type)
                                  | _ -> result)
                             None 
                             pat 
        of
         | Some ((v as (vn, _), vpos), base_type) ->
           %% fa(v1, v2) pat(v1) && pat(v2) => arg(v1) = arg(v2)
           let v1n = (vn^"__1", base_type) in % was type of v, but should be base type of Q
           let v1 = Var(v1n, vpos) in
           let v2n = (vn^"__2", base_type) in % was type of v, but should be base type of Q
           let v2 = Var(v2n, vpos) in
           let (tm, conds, vs) = patternToTermPlusExConds pat in
           let mainCond = [mkEquality(termType arg, arg, tm)] in
           let all_conds = mainCond ++ conds in
           let v1Conds = map (fn c -> substitute(c, [(v, v1)])) all_conds in
           let v2Conds = map (fn c -> substitute(c, [(v, v2)])) all_conds in
           let body_type = termType body in
           let quotCond = mkBind(Forall, [v1n, v2n]++vs,
                                 mkSimpImplies(mkConj(v1Conds ++ v2Conds),
                                               mkEquality(body_type, % was type of v, but should be type of body
                                                          substitute(body, [(v, v1)]),
                                                          substitute(body, [(v, v2)]))))
           in
           addCondition(tcc, gamma, quotCond, "_quotient")
         | _ -> tcc)
     | _ -> tcc

 op  returnPattern: Gamma * MSTerm * MSType * MSType  -> Gamma * MSTerm
 def returnPattern(gamma, t, tau1, tau2) = 
     returnPatternRec([], gamma, t, tau1, tau2)

 def returnPatternRec(pairs, gamma, M, tau, sigma) =
     let spc = getSpec gamma in
     if equalType? (tau, sigma) ||     % equivType? spc
        exists? (fn p -> p = (tau, sigma)) pairs
        then (gamma, M)
     else
     let pairs  = Cons((tau, sigma), pairs)     in 
     let tau1   = unfoldBase(gamma, tau)        in
     let sigma1 = unfoldBase(gamma, sigma)      in
     if tau1 = sigma1
        then (gamma, M)
     else
     case tau1 
       of Subtype(tau2, pred, _) -> 
          let gamma = assertCond(mkLetOrApply(pred, M, gamma), gamma, "pat-subtype1") in
          returnPatternRec(pairs, gamma, M, tau2, sigma1)
        | _ ->
     % let _ = writeLine("returnPattern:\n"^printType sigma1) in
     case sigma1 
       of Subtype(sigma2, pred, _) -> 
          let gamma = assertCond(mkLetOrApply(pred, M, gamma), gamma, "pat-subtype2") in
          returnPatternRec(pairs, gamma, M, tau1, sigma2)
        | _ -> (gamma, M)

 op  bindPattern : Gamma * MSPattern * MSType -> Gamma * MSTerm
 def bindPattern(gamma, pat, tau) = 
   case pat
     of AliasPat(p1, p2, _) -> 
        let (gamma, t1) = bindPattern(gamma, p1, tau) in
        let (gamma, t2) = bindPattern(gamma, p2, tau) in
        let gamma = assertCond(mkEquality(tau, t1, t2), gamma, "alias") in
        (gamma, t1)
      | VarPat(v as (_, srt), _) -> 
        let gamma1 = insert(v, gamma) in
        returnPattern(gamma1, mkVar(v), srt, tau)
      | EmbedPat(constr, Some p, tau2, _) -> 
        let tau1 = patternType p in
        let (gamma1, t1) = bindPattern(gamma, p, tau1) in
        let t2 = mkApply(mkFun(Embed(constr, true),
                               mkArrow(tau1, tau2)),
                         t1) in
        returnPattern(gamma1, t2, tau2, tau)
      | EmbedPat(constr, None, tau2, _) -> 
        returnPattern(gamma, mkFun(Embed(constr, false), tau2), tau2, tau)
      | RecordPat(fields, _) -> 
        let fs     = product(getSpec gamma, tau) in
        let fields = zip(fs, fields)    in
        let (gamma, terms) = 
            List.foldr
              (fn (((_, tau), (id, p)), (g, terms))-> 
               let (gamma, trm) = bindPattern(g, p, tau) in 
               (gamma, Cons((id, trm), terms)))
              (gamma, []) fields
        in
        let trm = mkRecord(terms) in
        returnPattern(gamma, trm, patternType pat, tau)
      | WildPat(sigma, _)       ->
        let (v, gamma1) = freshVar("P", sigma, gamma)in
        (gamma1, v)
     | StringPat(s, _)  ->      
       returnPattern(gamma, mkFun(String s, stringType), stringType, tau)
     | BoolPat(b, _)            ->      
       returnPattern(gamma, mkFun(Bool b, boolType), boolType, tau)
     | CharPat(ch, _)   ->      
       returnPattern(gamma, mkFun(Char ch, charType), charType, tau)
     | NatPat(i, _)             ->      
       returnPattern(gamma, mkFun(Nat i, natType), natType, tau)
     | QuotientPat(p, qid, _, _)        -> 
       let Quotient(tau1, _, _) = unfoldBase(gamma, tau) in
       let (gamma, trm) = bindPattern(gamma, p, tau1)
       in
       (gamma, mkApply(mkFun(Quotient qid, mkArrow(tau1, tau)), trm))
     | RestrictedPat(p, pred, _)        -> 
       let (gamma, trm) = bindPattern(gamma, p, tau) in
       let gamma = assertCond(pred, gamma, "restrict-pat") in
       (gamma, trm)

%% Well-foundedness condition

 op  checkRecursiveCall: TypeCheckConditions * Gamma * MSTerm * MSTerm * MSTerm -> TypeCheckConditions
 (* Don't need to generate obligation if arguments of call are independent of parameters. Normally, if an 
    obligation is generated, it should be trivial to find a WFO because the "recursive" call is made with 
    constant arguments, but if type of call is different from type of def then don't generate condition
    because it would give a type error. *)
 def checkRecursiveCall(tcc, gamma, term, n1, n2) =
   case CurryUtils.getCurryArgs term of
     | Some(f, args) ->
       (case f of
          | Fun(Op(lqid, _), oty, _) ->
            (case gamma of
               | (_, _, spc, Some(qid, vs), _, Some ty, _, _, _) ->
                 if qid = lqid && length args = length vs
                   %% Should be able to deal with length args < length vs
                   then
                     %let vs = map (fn (VarPat(v, _)) -> v) vs in
                     (if vs = []
                        then tcc
                        else if similarType? spc (oty, ty) % TODO: A and A|p are similar -- is this desired here?
                        then add_WFO_Condition(tcc, gamma, mkTuple(map (fn (pat) ->
                                                                      let tm::_ = patternToTerms(pat) in tm) vs),
                                               mkTuple args)
                        else addErrorCondition(tcc, gamma, "IllegalRecursion"))
                   else tcc
               | _ -> tcc)
          | _ -> tcc)
     | _ ->
   case n1 of
     | Fun(Op(lqid, _), oty, _) ->
       (case gamma of
         | (_, _, spc, Some(qid, [p]), _, Some ty, _, _, _) ->
           if qid = lqid
            then
            %let vs = map (fn (VarPat(v, _)) -> v) (getParams p) in
            (let vs = (getParams p) in
             if vs = []
               then tcc
             else if similarType? spc (oty, ty) % TODO: A and A|p are similar -- is this desired here?
             then add_WFO_Condition(tcc, gamma, mkTuple(map (fn (pat) -> let tm::_ = patternToTerms(pat) in tm) vs),
                                    n2)
             else addErrorCondition(tcc, gamma, "IllegalRecursion"))
           else tcc
         | _ -> tcc)
     | _ -> tcc

 op addUniqueExistenceCondition((tccs, claimNames): TypeCheckConditions, gamma: Gamma, body: MSTerm)
      : TypeCheckConditions =
   let (_, tvs, spc, Some(op_qid as Qualified(qual, fn_nm), _), _, Some op_ty, _, _, _) = gamma in
   if ~(containsRefToOp?(body, op_qid)) then (tccs, claimNames)
     else
     let fn_var = (fn_nm, op_ty) in
     let fn_var_tm = mkVar fn_var in
     let (equality, conds, faVars) = mkCondEqualityFromLambdaDef (spc, fn_var_tm, body) in
     let cond_equality = mkSimpImplies(mkSimpConj conds,equality) in
     % let faVars        = delete fn_var (freeVars cond_equality) in
     let cond_equality = mapTerm(fn t -> case t of
                                     | Fun(Op(qid,_), _,_) | qid = op_qid -> fn_var_tm
                                     | _ -> t,
                                 id, id)
                           cond_equality
     in
     let cond_equality = if faVars = [] then cond_equality
                          else mkBind (Forall, faVars, cond_equality)
     in
     let pred = mkBind(Exists1, [fn_var], cond_equality) in
     let sname = StringUtilities.freshName(fn_nm^"_Obligation_uniqueness", claimNames) in
     let name = mkQualifiedId(qual, sname) in
     let condn = (name, tvs, pred) in
     (Cons(mkConjecture condn, tccs), StringSet.add(claimNames, sname))

 %% Obsolete. Replaced by above
 op  add_WFO_Condition: TypeCheckConditions * Gamma * MSTerm * MSTerm
                       -> TypeCheckConditions
 def add_WFO_Condition((tccs, claimNames), (decls, tvs, spc, qid, name as Qualified(qual, id), _, _, _, _),
                       param, recParam) =
   %% ex(pred) (wfo(pred) && fa(params) context(params) => pred(recParams, params))
   let paramType = inferType(spc, recParam) in
   let predType = mkArrow(mkProduct [paramType, paramType], boolType) in
   let pred = ("pred", predType) in
   let rhs = mkAppl(mkVar pred, [recParam, param]) in
   let def insert(formula, decl) = 
         case decl
           of Var v ->        
              if isFree(v, formula)
                 then mkBind(Forall, [v], formula)
              else formula
            | Cond (Fun(Bool true, _, _)) -> formula
            | Cond c ->       mkSimpImplies(c, formula)
            | Let decls ->    Let(decls, formula, noPos)
            | LetRec decls -> LetRec(decls, formula, noPos)
   in
   let form = foldl insert rhs decls in
   let form = simplify spc form in
   let form = mkBind(Exists, [pred], mkConj[mkApply(mkOp(Qualified("Function", "wfo"),
                                                       mkArrow(predType, boolType)),
                                                  mkVar pred),
                                          form])
   in
   let sname = StringUtilities.freshName(id^"_termination", claimNames) in
   let name = mkQualifiedId(qual, sname) in
   let condn = (name, tvs, form) in
   (Cons(mkConjecture condn, tccs), StringSet.add(claimNames, sname))

 op  addErrorCondition: TypeCheckConditions * Gamma * String -> TypeCheckConditions
 %% Impossible obligation str is an indication of the error
 def addErrorCondition((tccs, claimNames), (_, _, _, _, Qualified(qual, id), _, _, _, _), str) =
   let sname = StringUtilities.freshName(id^"_"^str, claimNames) in
   let condn = (mkQualifiedId(qual, sname), [], mkFalse()) in
   (Cons(mkConjecture condn, tccs), StringSet.add(claimNames, sname))

 op includesPredLifter?(spc: Spec): Bool = embed? Some (findTheOp(spc, Qualified("List", "List_P")))

 op maybeRaiseSubtypes(ty1: MSType, ty2: MSType, gamma: Gamma): MSType * MSType =
   %% Temporary backward compatibility until we add these functions at type-check time rather
   %% than just in the Isabelle translator
   if lifting? gamma then
       % let _ = writeLine("Lift tau: "^printType ty1^"\nLift sigma: "^printType ty2) in
       let spc = getSpec gamma in
       let (n_ty1, n_ty2) = raiseSubtypes(ty1, ty2, spc) in
       (if equalType?(n_ty1, ty1) then ty1
         else % let _ = writeLine("Lift tau: "^printType ty1^" --> "^printType n_ty1) in
              case n_ty1 of
                | Subtype(_, p, _) ->
                  % let _ = writeLine("Raised "^printType ty1^"\nstp: "^printTerm p) in
                  n_ty1
                | _ -> n_ty1,
        if equalType?(n_ty2, ty2) then ty2
         else % let _ = writeLine("Lift sigma: "^printType ty2^" --> "^printType n_ty2) in
              case n_ty2 of
                | Subtype(_, p, _) ->
                  % let _ = writeLine("Raised "^printType ty2^"\nstp: "^printTerm p) in
                  n_ty2
                | _ -> n_ty2)
     else (ty1, ty2)

 def <= (tcc, gamma, M, tau, sigma, raise?) = 
   (% if raise? then () else writeLine(printTerm M^ ": "^ printType tau^"\n <= "^ printType sigma);
    if equalType?(tau, sigma) then tcc   % equivType? gamma.3 (tau, sigma) then tcc
    else
    let (tau0, sigma0) = maybeRaiseSubtypes(tau, sigma, gamma) in
    let tau0 = if raise? then tau0 else tau in
    % let _ = if raise? then () else writeLine(printTerm M^ ": \n"^ printType tau0^"\n <= \n"^ printType sigma0) in
    if lifting? gamma then
      let gamma =
          case tau0 of
          | Subtype(_, pred, _) -> 
            let preds = decomposeConjPred pred in
            foldl (fn (gamma, pred) -> assertCond(mkLetOrApply(pred, M, gamma), gamma, "subtype")) gamma preds
          | _ -> gamma
      in
      case sigma0 of
      | Subtype(_, pred, _) ->
        % let _ = writeLine("Verifying "^printTerm pred^" for "^printTerm M) in
        let preds = decomposeConjPred pred in
        foldl (fn (tcc, pred) -> addCondition(tcc, gamma, mkLetOrApply(pred, M, gamma), "_subtype"))
          tcc preds
      | _ -> tcc      
    else
    subtypeRec([], tcc, gamma, M, tau0, sigma0))

 def subtypeRec(pairs, tcc, gamma, M, tau, sigma) =
   let spc = getSpec gamma in
   if equivType? spc (tau, sigma) || 
      exists? (fn p -> p = (tau, sigma)) pairs
      then tcc
   else
%      let _ = writeLine
%                  (printTerm M^ " : "^
%                printType tau^" <= "^
%                       printType sigma)
%      in
   let pairs  = Cons((tau, sigma), pairs) in 
   let tau1   = if lifting? gamma then tau   else unfoldBeforeCoProduct(spc, tau)   in
   let sigma1 = if lifting? gamma then sigma else unfoldBeforeCoProduct(spc, sigma) in
%    let _ = writeLine("tau0: "^printType tau^", "^"tau1: "^printType tau1^", "^
%                      "\nsig0: "^printType sigma^", "^"sig1: "^printType sigma1) in
   if equalType?(tau1, sigma1)
      then tcc
   else
   case tau1 
     of Subtype(tau2, pred, _) -> 
        % let _ = writeLine("Asserting "^printTerm pred^" of "^printTerm M) in
        let preds = decomposeConjPred pred in
        let gamma = foldl (fn (gamma, pred) -> assertCond(mkLetOrApply(pred, M, gamma), gamma, "subtypeR"))
                      gamma preds in
        subtypeRec(pairs, tcc, gamma, M, tau2, sigma1)
      | _ -> 
   case sigma1 
     of Subtype(sigma2, pred, _) -> 
        % let _ = writeLine("Verifying "^printTerm pred^" for "^printTerm M) in
        let tcc = subtypeRec(pairs, tcc, gamma, M, tau1, sigma2) in
        let preds = decomposeConjPred pred in
        let tcc = foldl (fn (tcc, pred) -> addCondition(tcc, gamma, mkLetOrApply(pred, M, gamma), "_subtype"))
                    tcc preds
        in
        tcc
      | _ ->
   case (tau1, sigma1)
     of (Arrow(tau1, tau2, _), Arrow(sigma1, sigma2, _)) ->
        if lifting? gamma then tcc
        else
        let sigma1 = unfoldBeforeCoProduct(spc, sigma1) in
        let (xVarTm, gamma1) = freshVars("X", sigma1, gamma) in
        let tcc    = subtypeRec(pairs, tcc, gamma1, xVarTm, sigma1, tau1) in
        let tcc    = case M of
                       | Lambda _ -> tcc % In this case the extra test would be redundant
                       | _ -> subtypeRec(pairs, tcc, gamma1,
                                         mkApply(M, xVarTm), tau2, sigma2)
        in
        tcc
      | (Product(fields1, _), Product(fields2, _)) -> 
        let tcc = ListPair.foldl 
                    (fn(tcc, (_, t1), (id, t2)) -> 
                     subtypeRec(pairs, tcc, gamma,
                                mkApply(mkFun(Project id, mkArrow(sigma1, t1)),
                                        M),
                                t1, t2))
                    tcc (fields1, fields2)
        in
        tcc
      | (CoProduct(fields1, _), CoProduct(fields2, _)) ->
        let tcc = ListPair.foldl 
              (fn(tcc, (_, t1), (id, t2)) -> 
                 (case (t1, t2)
                    of (Some t1, Some t2) -> 
                       let gamma = assertCond(mkApply(mkFun(Embedded id, mkArrow(sigma, boolType)),
                                                      M),
                                              gamma, "coprod") in
                       subtypeRec(pairs, tcc, gamma,
                                  mkApply(mkFun(Select id, mkArrow(sigma, t1)), M),
                                  t1, t2)
                     | (None, None) -> tcc
                     | _ -> System.fail "CoProduct mismatch"))
               tcc (fields1, fields2)
        in
        tcc
      | (Quotient(tau1, pred1, _), Quotient(sigma2, pred2, _)) -> tcc 
        %%%%%%%%%%%%% FIXME
      | (TyVar(tv1, _), TyVar(tv2, _)) -> tcc
      | (Base(id1, srts1, _), Base(id2, srts2, _)) ->
        if id1 = id2
            then
            %%  let ps1 = ListPair.zip(srts1, srts2) in % unused
            let tcc = ListPair.foldl
                         (fn (tcc, s1, s2) -> 
                             let x = freshName(gamma, "B") in
                             let gamma1 = insert((x, s1), gamma) in
                             %let gamma2 = insert((x, s2), gamma) in
                             let tcc = subtypeRec(pairs, tcc, gamma1,
                                                  mkVar(x, s1), s1, s2) in
                             %% Don't think this is necessary e.g. List Nat < List Int
                             %let tcc = subtypeRec(pairs, tcc, gamma2,
                             %              mkVar(x, s2), s2, s1) in
                             tcc)
                       tcc (srts1, srts2)
            in
            tcc
         else
         addFailure(tcc,
                    gamma,
                    " "^printType tau^
                    " could not be made subtype of "^
                    printType sigma)
      | (Boolean(_), Boolean(_)) -> tcc
      | (Boolean(_), _) ->
         addFailure(tcc,
                    gamma,
                    printType tau1^
                    " could not be made subtype of "^
                    printType sigma1)
      | (_, Boolean(_)) ->
         addFailure(tcc,
                    gamma,
                    printType tau^
                    " could not be made subtype of "^
                    printType sigma)
      | _ -> (%writeLine("subtypeRec: type error in "^printTerm M^"\nat "
              %          ^print(termAnn M)^"\n"^printType tau^" <=? "^printType sigma);
              tcc)

 op  equivalenceConjectures: MSTerm * Spec -> SpecElements
 def equivalenceConjectures (r, spc) =
   let name = nameFromTerm r in
   let qual = qualifierFromTerm r in
   let domty = domain(spc, inferType(spc, r)) in
   let elty = head(productTypes(spc, domty)) in
   let tyVars = freeTyVars elty in
   let x = ("x", elty) in
   let y = ("y", elty) in
   let z = ("z", elty) in
   % fa (x,y) r(x,y) = (fa(z) r(x,z) = r(y,z))
   [mkConjecture (mkQualifiedId(qual, name^"_equiv"), tyVars,
                  mkBind (Forall, [x,y],
                          mkEquality (boolType,
                                      mkAppl (r, [mkVar x, mkVar y]),
                                      mkBind (Forall, [z],
                                              mkEquality (boolType,
                                                          mkAppl (r, [mkVar x, mkVar z]),
                                                          mkAppl (r, [mkVar y, mkVar z]))))))]
   % [%% fa(x, y, z) r(x, y) && r(y, z) => r(x, z)
   %  mkConjecture(mkQualifiedId(qual, name^"_transitive"), tyVars,
   %             mkBind(Forall, [x, y, z],
   %                    mkSimpImplies(MS.mkAnd(mkAppl(r, [mkVar x, mkVar y]),
   %                                             mkAppl(r, [mkVar y, mkVar z])),
   %                                    mkAppl(r, [mkVar x, mkVar z])))),
   %  %% fa(x, y) r(x, y) => r(y, x)
   %  mkConjecture(mkQualifiedId(qual, name^"_symmetric"), tyVars,
   %             mkBind(Forall, [x, y], mkSimpImplies(mkAppl(r, [mkVar x, mkVar y]),
   %                                                    mkAppl(r, [mkVar y, mkVar x])))),
   %  %% fa(x) r(x, x)
   %  mkConjecture(mkQualifiedId(qual, name^"_reflexive"), tyVars,
   %             mkBind(Forall, [x], mkAppl(r, [mkVar x, mkVar x])))]

 op  nameFromTerm: MSTerm -> String
 def nameFromTerm t =
   case t of
     | Fun(Op(Qualified(q, id), _), _, _) -> id
     | _ -> "UnnamedRelation"

 op  qualifierFromTerm: MSTerm -> String
 def qualifierFromTerm t =
   case t of
     | Fun(Op(Qualified(q, id), _), _, _) -> q
     | _ -> UnQualified

 op  insertQID: QualifiedId * NameSupply -> NameSupply
 def insertQID(Qualified(q, id), m) =
   if q = UnQualified
     then m
     else addName (m, id, 0)

% op dontGenerateObligations?(q: String, id: String): Bool =
%   false %endsIn?(id, "__subtype_pred")

 op dontUnfoldTypes: List QualifiedId = [Qualified("Nat", "Nat")]

 def checkSpec (spc, omitDefSubtypeConstrs?, ignoreOpFn?, spc_name) = 
   %let localOps = spc.importInfo.localOps in
   let names = foldl (fn (ns, el) ->
                      case el of
                        | Op    (qid, def?, _) -> insertQID(qid, ns)
                        | OpDef (qid, _, _, _)    -> insertQID(qid, ns)
                        | _ -> ns)
                     (empty()) 
                     spc.elements
   in
   let lift? = includesPredLifter? spc in
   let triv_count_ref = Ref 0 in
   let gamma0 = fn tvs -> fn tau -> fn qid -> fn nm ->
                  ([], tvs, spc, qid, nm, tau, Ref(!names), lift?, triv_count_ref)
   in
   let tcc = ([], empty) in
   %% Use foldr rather than foldl so that we can maintain adjacency of pragmas to defs (see Op case)
   let (tccs, claimNames) =
       foldr (fn (el, (tccs, claimNames)) ->
                case el of
                 | Op (qid as Qualified(q, id), true, pos)  % true means decl includes def
                     | ~(ignoreOpFn?(q, id)) ->
                   (case findTheOp(spc, qid) of
                      | Some opinfo ->
                        let trps = unpackTypedTerms (opinfo.dfn) in
                        let (tvs, tau, term) = nthRefinement(trps, 0) in
                        let usedNames = addLocalVars (term, StringSet.empty) in
                        %let term = etaExpand (spc, usedNames, tau, term) in
                        let term = renameTerm (emptyContext ()) term in 
                        let taus = case tau of
                                     | And (srts, _) -> srts
                                     | _ -> [tau]
                        in
                        let taus = if omitDefSubtypeConstrs?
                                     then map (fn tau -> stripRangeSubtypes(spc, tau, dontUnfoldTypes)) taus
                                   else taus
                        in
                        let (new_tccs, claimNames) =
                            foldr (fn (tau, tcc) ->
                                   let gamma = gamma0 tvs
                                               %% Was unfoldStripType but that cause infinite recursion.
                                               %% Is stripSubtypes sufficient (or necessary)?
                                                 (Some (stripSubtypes(spc, tau)))
                                                 (Some (qid, (curriedParams term).1))
                                                 (Qualified (q, id ^ "_Obligation"))
                                   in
                                   let tcc = if generateTerminationConditions?
                                                then addUniqueExistenceCondition(tcc, gamma, term)
                                                else tcc
                                   in
                                   (tcc, gamma) |- term ?? tau)
                              tcc taus
                         in
                         if new_tccs = [] then (el::tccs, claimNames)
                         else
                         let new_tccs = reverse new_tccs in
                         let op_ref_new_tccs = filter (fn Property(_, _, _, fm, _) ->
                                                         containsRefToOp?(fm, qid))
                                                 new_tccs
                         in
                         let indep_new_tccs = filter (fn p -> p nin? op_ref_new_tccs) new_tccs in
                         let before_pragma? = (tccs ~= [] && embed? Pragma (head tccs)) in
                         if before_pragma?
                           then let prag::tccs = tccs  in
                                (indep_new_tccs ++ [el, prag] ++ op_ref_new_tccs ++ tccs, claimNames)
                           else (indep_new_tccs ++ [el]       ++ op_ref_new_tccs ++ tccs, claimNames))
                 | OpDef (qid as Qualified(q, id), refine_num, _, _) ->
                   (case findTheOp(spc, qid) of
                      | Some opinfo | ~(ignoreOpFn?(q, id)) ->
                        let trps = unpackTypedTerms (opinfo.dfn) in
                        let (tvs, tau, term) = nthRefinement(trps, refine_num) in
                        let usedNames = addLocalVars (term, StringSet.empty) in
                        %let term = etaExpand (spc, usedNames, tau, term) in
                        let term = renameTerm (emptyContext ()) term in 
                        let taus = case tau of
                                     | And (srts, _) -> srts
                                     | _ -> [tau]
                        in
                        let taus = if omitDefSubtypeConstrs?
                                     then map (fn tau -> stripRangeSubtypes(spc, tau, dontUnfoldTypes)) taus
                                   else taus
                        in
                        let ref_qid as Qualified(q, id) = refinedQID refine_num qid in
                        let (new_tccs, claimNames) =
                            foldr (fn (tau, tcc) ->
                                     let gamma = gamma0 tvs
                                     %% Was unfoldStripType but that cause infinite recursion.
                                     %% Is stripSubtypes sufficient (or necessary)?
                                     (Some (stripSubtypes(spc, tau)))
                                     (Some (qid, (curriedParams term).1))
                                     (Qualified (q, id ^ "_Obligation"))
                                     in
                                     let tcc = if generateTerminationConditions?
                                                 then addUniqueExistenceCondition(tcc, gamma, term)
                                               else tcc
                                     in
                                     (tcc, gamma) |- term ?? tau)
                               tcc taus
                        in
                        if new_tccs = [] then (el::tccs, claimNames)
                         else
                         % let new_tccs = reverse new_tccs in
                         let op_ref_new_tccs = filter (fn Property(_, _, _, fm, _) ->
                                                         containsRefToOp?(fm, ref_qid))
                                                 new_tccs
                         in
                         let indep_new_tccs = filter (fn p -> p nin? op_ref_new_tccs) new_tccs in
                         let before_pragma? = (tccs ~= [] && embed? Pragma (head tccs)) in
                         if before_pragma?
                           then let prag::tccs = tccs  in
                                (indep_new_tccs ++ [el, prag] ++ op_ref_new_tccs ++ tccs, claimNames)
                           else (indep_new_tccs ++ [el]       ++ op_ref_new_tccs ++ tccs, claimNames))
                 | TypeDef (qid as Qualified(q, id), _) ->
                   (let tcc = (el::tccs, claimNames) in
                    case findTheType(spc, qid) of
                      | Some typeinfo ->
                        let quotientRelations: Ref MSTerms = Ref [] in
                        let subtypePreds:      Ref (List (TyVars * MSTerm * MSType)) = Ref [] in
                        let _ = app (fn srt ->
                                     let (tvs, srt) = unpackType srt in
                                     appType (fn _ -> (),
                                              fn s ->
                                              case s of
                                                | Quotient(_, r, _) ->
                                                  if exists? (fn rx -> equivTerm? spc (r, rx))
                                                       (!quotientRelations) then ()
                                                  else 
                                                  quotientRelations := r :: !quotientRelations
                                                | Subtype(ss, p, _) ->
                                                  subtypePreds := (tvs, p, mkArrow(ss, boolType)) :: !subtypePreds
                                                | _ -> (),
                                              fn _ -> ())
                                       srt)
                                  (typeInfoDefs typeinfo)
                        in
                        let tcc = foldr (fn (r, (tccs, names)) ->
                                           (equivalenceConjectures(r, spc) ++ tccs, names))
                                    tcc 
                                    (!quotientRelations)
                        in
                        foldr (fn ((tvs, pred, srt), tcc) ->
                               (tcc, gamma0 tvs None None (Qualified(q, id ^ "_Obligation")))
                               |- pred ?? srt)
                          tcc
                          (!subtypePreds))
                 | Property(_, pname as Qualified (q, id), tvs, fm, _)
                     %% Don't generate obligations for refine theorems as proven in original
                     | ~(testSubseqEqual?("__r_def", id, 0, length id - 7))
                     ->
                   let fm = renameTerm (emptyContext()) fm in
                   let (new_tccs, claimNames) =
                       (([], claimNames), gamma0 tvs None None (mkQualifiedId (q, (id^"_Obligation"))))
                          |- fm ?? boolType
                   in
                   (reverse new_tccs ++ (el::tccs), claimNames)
                 | _ -> (el::tccs, claimNames))
         tcc spc.elements
     in
     let _ = if reportTrivialObligationCount?
              then writeLine(spc_name^" has "^show(!triv_count_ref)^" obligations proved by simplification.")
              else ()
     in
     (tccs, claimNames)

% op  wfoSpecTerm: SpecCalc.Term Position
% def wfoSpecTerm = (UnitId (SpecPath_Relative {path       = ["Library", "Base", "WFO"],
%                                              hashSuffix = None}),
%                   noPos)

 def makeTypeCheckObligationSpec (spc, omitDefSubtypeConstrs?, ignoreOpFn?, spc_name) =
   % let _ = writeLine(printSpec spc) in
   let (new_elements, _) = checkSpec (spc, omitDefSubtypeConstrs?, ignoreOpFn?, spc_name) in
   let spc = spc << {elements = new_elements} in
   % let _ = writeLine(printSpec spc) in
   spc

 op obligationSpec (spc: Spec): Spec =
   makeTypeCheckObligationSpec (spc, false, FALSE, "")

% op  boundVars   : Gamma -> List Var
% op  boundTyVars : Gamma -> TyVars
% def boundTyVars(_, tyVars, _, _, _) = tyVars

% def boundVars(decls: List Decl, _, _, _, _) = 
%     let
%       def loopP(p, vs) = patternVars(p) @ vs
%       def loop(decls : List Decl, vars) = 
%           case decls
%             of [] -> vars
%              | (Var v)::decls -> loop(decls, cons(v, vars))
%              | (Cond _)::decls -> loop(decls, vars)
%              | (LetRec(ds))::decls -> loop(decls, (List.map (fn (v, _)-> v) ds) @ vars)
%              | (Let(ds))::decls ->
%                loop(decls, List.foldr (fn ((p, _), vs) -> loopP(p, vs)) vars ds)
%     in
%       loop(decls, [])

end
