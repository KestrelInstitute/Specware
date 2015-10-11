(* Transformations on coalgebraic definitions in specs *)

Coalgebraic qualifying
spec
import Script, /Languages/MetaSlang/CodeGen/Generic/RecordMerge
import /Languages/MetaSlang/CodeGen/Stateful/Setf

op finalizeExcludesDefinedOps?: Bool = false

(*
WS st =  (roots st \/ allSucs st (black st)) -- black st

WS H' = let st = addArc H (x,y) in (roots st \/ allSucs st (black st)) -- black st
Simplify rhs with rules
fa(H, x) x in? nodes H
fa(H,x,y) black(addArc H (x, y)) = H
*)

op mkApplyTermFromLambdas (hd: MSTerm, f: MSTerm): MSTerm =
  case f of
    | Lambda([(param_pat, _, bod)], _) ->
      let Some arg = patternToTerm param_pat in
      mkApplyTermFromLambdas(mkApply(hd, arg), bod)
    | _ -> hd

op addPostCondition(post_condn: MSTerm, ty: MSType): MSType =
  let def replaceInRange ty =
        case ty of
           | Arrow(dom, rng, a) -> Arrow(dom, replaceInRange rng, a)
           | Subtype(sup_ty, Lambda([(v, c, pred)], a1), a2) ->
             % Subtype(sup_ty, Lambda([(v, c, mkConj(getConjuncts pred ++ [post_condn]))], a1), a2)
             Subtype(sup_ty, Lambda([(v, c, replaceInTerm pred)], a1), a2)
      def replaceInTerm tm =
        case tm of
          | IfThenElse(p, q, r, a) ->
            IfThenElse(p, replaceInTerm q, replaceInTerm r, a)
          | Bind(Exists, vs, bod, a) ->
            Bind(Exists, vs, replaceInTerm bod, a)
          | Let(binds, bod, a) ->
            Let(binds, replaceInTerm bod, a)
          | _ ->  Utilities.mkAnd(tm, post_condn)
  in
  replaceInRange ty

% Given a state transformer op of type `ty`, and a state type
% `state_ty` and a spec `spc` return the (nm, others, postcondition),
% where `nm` is the name of the poststate, `others` is (optionally)
% the non-state results and their names, and finally `postcondition`,
% which is the constraint on the tuple of (flattened) (nm * others).
op getStateVarsAndPostCondn (ty: MSType, state_ty: MSType, spc: Spec)
 : Option(MSVars * Option(Ids * List(Id * MSPattern)) * MSTerm) =
  case range_*(spc, ty, false) of
    | Subtype(result_ty, Lambda([(pat, _, condn)], _), _) ->
      (if equivTypeSubType? spc (result_ty, state_ty) true
       then case pat of
              | VarPat(result_var,_) -> Some([result_var], None, condn)
              | _ -> None
       else case (result_ty, pat) of
              | (Product(ty_prs, _), RecordPat(pat_prs, _)) ->
                (case mapPartial (fn (id, ty) -> if equivTypeSubType? spc (ty, state_ty) true
                                                   then Some id else None) ty_prs
                   | [] -> None
                   | ids ->
                 case mapPartial (fn | (id2, VarPat(result_var,_)) | id2 in? ids -> Some result_var
                                     | _ -> None)
                        pat_prs
                   | [] -> None
                   | result_vars -> Some(result_vars, Some(ids, pat_prs), condn))                            
              | _ -> None)
    | _ -> None

op getPostCondn (ty: MSType, spc: Spec) : Option MSTerm =
   case range_*(spc, ty, false) of
    | Subtype(result_ty, Lambda([(pat, _, condn)], _), _) ->
      Some condn
    | _ -> None

op equalitySpecToLambda(lhs: MSTerm, rhs: MSTerm, lam_pats: MSPatterns, fn_qid: QualifiedId): Option (MSPatterns * MSTerm) =
  case lhs of
    | Fun(Op(qid, _), _, _) | qid = fn_qid -> Some (lam_pats, rhs)
    | Apply(n_lhs, arg, _) ->
      (case termToPattern arg of
         | None -> None
         | Some arg_pat -> equalitySpecToLambda(n_lhs, rhs, lam_pats ++ [arg_pat], fn_qid))
    | _ -> None

op commonPattern(p1: MSPattern, p2: MSPattern, spc: Spec): MSPattern =
  case (p1, p2) of
    | (VarPat((v, ty1), a), VarPat((_, ty2), _)) -> VarPat((v, commonSuperType(ty1, ty2, spc)), a)
    | (RecordPat(prs1, a), RecordPat(prs2, _)) ->
      RecordPat(map (fn ((id, pat1), (_, pat2)) -> (id, commonPattern(pat1, pat2, spc))) (zip(prs1, prs2)), a)
    | _ -> p1                           % Shouldn't happen?

op subtypeCondition(p1: MSPattern, p2: MSPattern, spc: Spec): MSTerm =
  let _ = writeLine("subtypeCondition: "^printPatternWithTypes p1^" < "^printPatternWithTypes p2) in
  case (p1, p2) of
    | (VarPat((_, ty1), a), VarPat((v, ty2), _)) ->
      (case subtypePred(ty1, ty2, spc) of
         | Some pred ->
           simplifiedApply(pred, mkVar(v, ty2), spc)
         | None -> trueTerm)
    | (RecordPat(prs1, a), RecordPat(prs2, _)) ->
      foldl (fn (condn, ((_, pat1), (_, pat2))) -> Utilities.mkAnd(condn, subtypeCondition(pat1, pat2, spc)))
        trueTerm (zip(prs1, prs2))
    | _ -> trueTerm

op makeSubstFromPatLists(pats1: MSPatterns, pats2: MSPatterns): MSVarSubst =
  flatten (map (fn (p1, p2) -> let Some sbst = matchPatterns(p1, p2) in sbst) (zip(pats1, pats2)))

op getDefFromTheorem(thm_qid: QualifiedId, intro_qid: QualifiedId, spc: Spec): MSTerm =
  case findMatchingTheorems(spc, thm_qid) of
    | [] -> error("No theorem matching "^show thm_qid)
    | matching_thms ->
      let (_, _, tvs, bod, _) = last matching_thms in
      let def extractDefComps(bod: MSTerm): List (MSPatterns * MSTerm * MSTerm) =
           case bod of
              | Bind(Forall, _, Apply(Fun(Equals,_,_),
                                      Record([(_,lhs),(_,rhs)], _),_),_) ->
                (case equalitySpecToLambda(lhs, rhs, [], intro_qid) of
                   | Some(lam_pats, dfn) -> [(lam_pats, trueTerm, dfn)]
                   | None -> (warn("theorem "^printTerm bod^" doesn't define "^show intro_qid);
                              []))                 
              | Bind(Forall, _, Apply(Fun(Implies,_,_),
                                      Record([(_, condn),(_,Apply(Fun(Equals,_,_),
                                                                  Record([(_,lhs),(_,rhs)], _),_))], _),_),_) ->
                (case equalitySpecToLambda(lhs, rhs, [], intro_qid) of
                   | Some(lam_pats, dfn) -> [(lam_pats, condn, dfn)]
                   | None -> (warn("theorem "^printTerm bod^" doesn't define "^show intro_qid);
                              []))
              | _ ->
                case getConjuncts bod of
                  | [_] -> []
                  | tms -> flatten(map extractDefComps tms)
      in
      let cases = extractDefComps bod in
      let _ = (writeLine("getDefFromTheorem");
               app (fn (pats, c, bod) ->
                      (app (fn p -> writeLine(printPatternWithTypes p)) pats;
                       writeLine(printTerm bod)))
                 cases)
      in                      
      case cases of
        | [] -> error("Can't extract definition from "^show thm_qid)
        | [(lam_pats, _, bod)] -> mkCurriedLambda(lam_pats, bod)
        | (pats1, cond1, bod1) :: r_cases ->
          let lam_pats = foldl (fn (lam_pats, (lam_patsi, _, _)) ->
                                  if length lam_pats = length lam_patsi
                                    then map (fn (pat, pati) -> commonPattern(pat, pati, spc)) (zip(lam_pats, lam_patsi))
                                    else lam_pats) % Shouldn't happen
                           pats1 r_cases
          in
          let _ = (writeLine "lam_pats"; app (fn p -> writeLine(printPatternWithTypes p)) lam_pats) in
          let (p1, bod1) :: r_cases2 =
              map (fn (pats, cond, bod) ->
                     let sbst = makeSubstFromPatLists(lam_pats, pats) in
                     let newCond = foldl (fn (c, (pi, lam_p)) -> Utilities.mkAnd(c, subtypeCondition(pi, lam_p, spc)))
                                     trueTerm (zip(pats, lam_pats)) in
                     (Utilities.mkAnd(newCond, cond), substitute(bod, sbst)))
                cases
          in
          let bod = foldl (fn (bod, (pi, bodi)) ->
                             Utilities.mkIfThenElse(pi, bodi, bod))
                      bod1 r_cases2
          in
          mkCurriedLambda(lam_pats, bod)

op SpecTransform.maintain (spc: Spec) (qids: QualifiedIds) (rules: RuleSpecs) (trace?: TraceFlag): Env Spec =
  maintainOpsCoalgebraically(spc, qids, rules, trace?)

op traceMaintain?: Bool = false

def maintainOpsCoalgebraically
      (spc: Spec, qids: QualifiedIds, rules: List RuleSpec, trace?: TraceFlag): Env Spec =
  let intro_qid as Qualified(intro_q, intro_id) = head qids in
  {info <- findTheOp spc intro_qid;
   let (tvs, intro_ty, intro_fn_def) = unpackFirstTerm info.dfn in
   let intro_fn = mkOp(intro_qid, intro_ty) in
   let state_ty = domain(spc, intro_ty) in
   let (intro_fn_def, fold_rl) = if length qids > 1
                                  then (getDefFromTheorem(qids@1, intro_qid, spc), RightToLeft(qids@1))
                                 else (intro_fn_def, Fold intro_qid)
   in
   let _ = writeLine("\nMaintain "^show intro_qid^": "^printType intro_ty^"\n"^printTerm intro_fn_def) in
   let def addToDef(info, result as (spc, qids)) =
         let qid = primaryOpName info in
         let (tvs, ty, tm) = unpackFirstTerm info.dfn in
         % let _ = if show qid = "mark" then writeLine("dfn: "^printTerm info.dfn^"\n"^printTerm tm) else () in
         if ~(anyTerm? tm) then result
         else
         case getStateVarsAndPostCondn(ty, state_ty, spc) of
           | Some ([result_var], deref?, post_cond)   % !! Need to generalize for multiple result_vars
               % | ~(containsRefToOp?(post_cond, intro_qid)) 
                 ->
             let result_tm0 = mkApplyTermFromLambdas(mkOp(qid, ty), tm) in
             let result_tm = case deref? of
                               | Some ([id], _) -> % !! Need to generalize for multiple ids
                                 mkApply(mkProject(id, range_*(spc, ty, true), state_ty),
                                         result_tm0)
                               | None -> result_tm0
             in
             % let _ = writeLine("\nLooking at "^show qid) in
             % let _ = writeLine("Result var is "^result_var.1) in
             % let _ = writeLine("Result tm is "^printTerm result_tm) in
             let new_lhs = mkApply(intro_fn, mkVar result_var) in
             let intro_fn_rng = inferType(spc, new_lhs) in
             %let raw_rhs = simplifiedApply(intro_fn_def, result_tm, spc) in
             % let _ = writeLine("\nBody to transform:\n"^printTerm raw_rhs) in
             let new_intro_ty = addPostCondition(mkEquality(intro_fn_rng, new_lhs, new_lhs), ty) in
             let spc = addRefinedType(spc, info, new_intro_ty) in
             (spc, qid :: qids)
           | _ -> result
   in
   let (spc, qids) = foldOpInfos addToDef (spc, []) spc.ops in
   let main_script = At(map Def (reverse qids),
                        Repeat(15,
                               mkSteps
                                 [ % Go to rhs of postcondition just added, unfold and simplify
                                  Move [SearchPred (rhsApplication intro_qid)],
                                  %mkSimplify[LeftToRight(mkContextQId "fn value")],
                                  Simplify1([reverseRuleSpec fold_rl] ++ rules),
                                  %mkSimplify [],
                                  mkSimplify([LeftToRight(mkContextQId "fn value")]),
                                  mkSimplify rules,
                                  mkSimplify(fold_rl :: Omit(mkContextQId "fn value") :: rules)])) in
   let script = if traceMaintain? || trace?
                   then Steps[Trace true, main_script]
                 else main_script
   in
   {print "rewriting ... \n";
    print (scriptToString script^"\n"); 
    spc <- interpret(spc, script);
    return spc}}

op SearchPred.rhsApplication (qid: QualifiedId) (tm: MSTerm, pt: PathTerm): Bool =
  case tm of
    | Apply(f, _, _) | applicationOfQId? qid f ->
      (case (pathTermPath pt, grandParentTerm pt) of
         | (1::1::_, Some(gpar_ptm)) ->    % Relies on representation of PathTerms
           (case fromPathTerm gpar_ptm of
              | Apply(Fun(Equals, _, _), _, _) -> true
              | _ -> false)
         | _ -> false)
    | _ -> false

op findHomomorphismFn(tm: MSTerm): Option QualifiedId =
  case tm of
    | Bind(Forall, _, bod,_) -> findHomomorphismFn bod
    | Apply(Fun(Equals,_,_),
            Record([(_,e1),(_,Apply(Fun(Op(qid,_),_,_), _, _))], _),_) ->
      Some qid
    | _ -> None

op SpecTransform.implement (spc: Spec) (qids: QualifiedIds) (rules: RuleSpecs) (trace?: TraceFlag): Env Spec =
  implementOpsCoalgebraically(spc, qids, rules, trace?)

op traceImplement?: Bool = false

def implementOpsCoalgebraically
  (spc: Spec, qids: QualifiedIds, rules: List RuleSpec, trace?: Bool): Env Spec =
  case qids of
    | [replace_op_qid as Qualified(_, r_o_id), assert_qid] ->
      (case findPropertiesNamed(spc, assert_qid) of
         | [] -> raise(Fail("Can't find property named "^show assert_qid))
         | [(_, _, _, body, _)] ->
           (case findHomomorphismFn body of
            | None -> raise(Fail("Can't find homomorphism fn from axiom:\n"^printTerm body))
            | Some homo_fn_qid -> 
              {replace_op_info <- findTheOp spc replace_op_qid;
               let (tvs, replace_op_ty, _) = unpackFirstTerm replace_op_info.dfn in
               let _ = writeLine("Implement "^show replace_op_qid^": "^printType replace_op_ty) in
               % let _ = writeLine("With rewrite: "^printTerm body) in
               let def findStateTransformOps(info, qids) =
                     let (tvs, ty, tm) = unpackFirstTerm info.dfn in
                     case range_*(spc, ty, false) of
                       | Subtype(_, Lambda([(_, _, body)], _), _)
                           | existsSubTerm
                               (fn st -> case st of
                                           | Fun(Op(qid,_), _, _) -> qid = replace_op_qid
                                           | _ -> false)
                               body
                         ->
                         primaryOpName info :: qids
                       | _ ->
                     if existsSubTerm
                         (fn st -> case st of
                                     | Fun(Op(qid,_), _, _) -> qid = replace_op_qid
                                     | _ -> false)
                         tm
                       then primaryOpName info :: qids
                       else qids
               in
               let state_transform_qids = foldOpInfos findStateTransformOps [] spc.ops in
               let defined_qids = filter (definedOp? spc) state_transform_qids in
               let post_condn_qids = filter (~~~(definedOp? spc)) state_transform_qids in
               let script = Steps((if traceImplement? || trace?
                                     then [Trace true]
                                     else [])
                                  ++ [At(map Def (reverse post_condn_qids),
                                         Repeat(15,
                                                Steps [Move [Search r_o_id, ReverseSearchPred childOfConj],
                                                 mkSimplify(RLeibniz homo_fn_qid
                                                             :: LeftToRight assert_qid
                                                             :: rules)])),
                                      At(map Def (reverse defined_qids),
                                         Steps[Move[SearchPred bodyOfFn?],
                                               Repeat
                                                 (15,
                                                  Steps[Move [Search r_o_id, ReverseSearchPred childOfConj],
                                                   mkSimplify(RLeibniz homo_fn_qid
                                                                :: LeftToRight assert_qid
                                                                :: rules)])])])
               in
               {print "rewriting ... \n";
                print (scriptToString script^"\n");
                spc <- interpret(spc, script);
                return spc}
               })
         | props -> raise(Fail("Ambiguous property named "^show assert_qid)))
    | _ -> raise(Fail("implement expects op and theorem QualifiedIds"))

op definedOp?(spc: Spec) (qid: QualifiedId): Bool =
  case findTheOp(spc, qid) of
    | Some info ->
      let (_, _, def_tm) = unpackFirstTerm info.dfn in
      ~(anyTerm? def_tm)
    | None -> false

op SearchPred.childOfConj(tm: MSTerm, pt: PathTerm): Bool =
  if length(pathTermPath pt) < 2 then true
  else
  case tm of
    | Fun _ -> false
    | _ -> 
  let Some par_ptm = parentTerm pt in
  let par_tm = fromPathTerm par_ptm in
  let par_tm = if embed? Record par_tm
                then
                  let Some gpar_ptm = parentTerm par_ptm in
                  fromPathTerm gpar_ptm
                else par_tm
  in                
  case par_tm of
    | Apply(Fun(And, _, _),_,_) ->
      (let Some gpar_ptm = parentTerm par_ptm in
       case fromPathTerm gpar_ptm of
         | IfThenElse(p, _, _, _) -> p ~= par_tm
         | _ -> true)
    | IfThenElse(_, q, r, _) | q = tm || r = tm ->
      childOfConj(par_tm, par_ptm)
    | Lambda _ -> true
    | _ -> false

op SearchPred.bodyOfFn?(tm: MSTerm, pt: PathTerm): Bool =
  ~(embed? Lambda tm)
    &&
    (if length(pathTermPath pt) < 2 then false
      else
      let Some pptm = parentTerm pt in
      case fromPathTerm pptm of
        | Lambda ([(_,_,body)], _) -> body = tm
        | _ -> false)

op hasTypeRefTo?(ty_qid: QualifiedId, ty: MSType): Bool =
  existsInType? (fn sty -> case sty of
                             | Base(qid, _, _) -> qid = ty_qid
                             | _ -> false)
    ty

op getConjoinedEqualities(spc: Spec) (t: MSTerm): MSTerms =
  case t of
    | IfThenElse(_, t1, t2, _) ->
      getConjoinedEqualities spc t1 ++ getConjoinedEqualities spc t2
    | Apply(Fun(And,_,_), Record([("1",t1),("2",t2)],_),_) ->
      getConjoinedEqualities spc t1 ++ getConjoinedEqualities spc t2
    %% case
    | Apply(Lambda(matches, _), _, _) ->
      foldl (fn (eqs, (_, _, bod)) -> eqs ++ getConjoinedEqualities spc bod) [] matches
    | Let(_, bod, _) -> getConjoinedEqualities spc bod
    | _ | unfoldable?(t, spc) ->
      let uf_tm = simplify spc (unfoldTerm(t, spc)) in
      getConjoinedEqualities spc uf_tm 
    | _ -> [t]

op findTypeWithQId(qid: QualifiedId, ty: MSType): MSType =
  case foldTypesInType (fn (r, tyi) ->
                          case r of
                            | Some _ -> r
                            | None -> 
                          case tyi of
                            | Base(qidi, _, _) | qidi = qid -> Some tyi
                            | _ -> None)
        None ty of
    | Some ty -> ty
    | None -> mkBase(qid, [])

op postConditionOpsReferencingOps(spc: Spec, qids: QualifiedIds): QualifiedIds =
  foldOpInfos
    (fn (info, found_qids) ->
      let  (tvs, ty, tm) = unpackFirstTerm info.dfn in
      if ~(anyTerm? tm) then found_qids
      else
      case getPostCondn(ty, spc) of
        | Some condn | containsRefToOps?(condn, qids) ->
          primaryOpName info :: found_qids
        | _ -> found_qids)
    [] spc.ops

op postConditionOpsReferencingType(spc: Spec, qid: QualifiedId): QualifiedIds =
  foldOpInfos
    (fn (info, found_qids) ->
      let  (tvs, ty, tm) = unpackFirstTerm info.dfn in
      if ~(anyTerm? tm) then found_qids
      else
      case getPostCondn(ty, spc) of
        | Some condn | containsRefToType?(condn, qid) ->
          primaryOpName info :: found_qids
        | _ -> found_qids)
    [] spc.ops


op findStoredOps(spc: Spec, state_qid: QualifiedId): QualifiedIds =
  foldOpInfos
    (fn (info, stored_qids) ->
      let  (tvs, ty, tm) = unpackFirstTerm info.dfn in
      if ~(anyTerm? tm) then stored_qids
      else
      let state_ty = findTypeWithQId(state_qid, ty) in
      case getStateVarsAndPostCondn(ty, state_ty, spc) of
        | Some(state_vars, deref?, post_condn) ->
          removeDuplicates
            (mapPartial
               (fn cj ->
                  case cj of
                    | Apply(Fun(Equals,_,_),Record([(_,lhs), (_,rhs)], _),_) ->
                      let def bindTerm lhs =
                           case lhs of
                              | Apply(Fun(Op(qid,_), _, _), Var(v, _), _)
                              | qid nin? stored_qids && inVars?(v, state_vars)
                                && ~(finalizeExcludesDefinedOps? && definedOp?(spc, qid))
                                ->
                                % let _ = if show qid = "deliver_in_udp_opt2" then writeLine(show(primaryOpName info)^" "^printType ty) else () in
                                Some qid
                              | _ -> None
                      in
                      (case bindTerm lhs of
                         | None -> bindTerm rhs
                         | st -> st)
                    | Apply(Fun(Op(qid,_), _, _), Var(v, _), _)    % Bool
                        | qid nin? stored_qids && inVars?(v, state_vars)
                          && ~(finalizeExcludesDefinedOps? && definedOp?(spc, qid)) ->
                      Some qid
                    | Apply(Fun(Not, _, _), Apply(Fun(Op(qid,_), _, _), Var(v, _), _), _)    % Bool
                        | qid nin? stored_qids && inVars?(v, state_vars)
                          && ~(finalizeExcludesDefinedOps? && definedOp?(spc, qid)) ->
                      Some qid
                    | _ -> None)
            (getConjoinedEqualities spc post_condn))
          ++ stored_qids
        | None -> stored_qids)  
    [] spc.ops

op scrubSubtypes(ty: MSType): MSType =
  %% This is necessary because of lack of proper representation of dependent types
  let def scrub1 ty =
        case ty of
          | Subtype(s_ty, pred, _) | freeVars pred ~= [] ->
            scrub1 s_ty
          | _ -> ty
  in
  mapType (id, scrub1, id) ty
           

op qualifiedIdToField(Qualified(_, id): QualifiedId): Id = id

op makeRecordFieldsFromQids(spc: Spec, qids: QualifiedIds): List(Id * MSType) =
  map (fn qid ->
         let Some info = findTheOp(spc, qid) in
         (qualifiedIdToField qid, scrubSubtypes(range(spc, inferType(spc, info.dfn)))))
    qids  

op findSourceVar(cjs: MSTerms, state_var: MSVar, stored_qids: QualifiedIds): Option MSVar

op mkCanonRecordOrSingle (fields : MSRecordFields) : MSTerm =
  case fields of
    | [("0", tm)] -> tm
    | _ -> mkCanonRecord fields

op findSourceTerm(prs: List(Id * MSTerm), lval_tm: MSTerm, params: MSVars, spc: Spec): Option MSTerm =
  let ty = inferType(spc, lval_tm) in
  case foldl (fn (opt_src_tm, (id, tm)) ->
                case tm of
                  | Apply(Fun(f,_,_), arg, _) | projectionFun(f, spc) = Some id -> Some arg
                  | _ -> opt_src_tm)
         None prs of
    | Some tm -> Some tm
    | None -> 
  case foldl (fn (opt_src_tm, (id, tm)) ->
                if some? opt_src_tm then opt_src_tm
                else
                  foldSubTerms
                    (fn (s_tm, opt_src_tm) ->
                       if some? opt_src_tm then opt_src_tm
                       else case s_tm of
                              | Apply(Fun(f,_,_), v as Var _, _) | projectionFun(f, spc) = Some id ->
                                Some v
                              | _ -> None)
                    opt_src_tm tm)
              None prs of
    | Some tm -> Some tm
    | None ->
  let src_tm = mapTerm (fn | Var(v as (_, ty), _) | ~(inVars?(v, params)) ->
                             (case findLeftmost (fn (_, tyi) -> equalType?(tyi, ty)) params of
                                | Some vp -> mkVar vp
                                | None -> mkVar v)
                           | stm -> stm,
                        id, id)
                 lval_tm
  in
  if equalTerm?(src_tm, lval_tm)
    then None
  else Some src_tm

type ItemValList = List(MSTerm * List MSTerm * List MSTerm * MSTerm)

op getExpandedConjuncts(tm: MSTerm, spc: Spec): MSTerms =
  case tm of
    | Apply(Fun(And,_,_), Record([("1",p),("2",q)],_),_) -> getExpandedConjuncts(p, spc) ++ getExpandedConjuncts(q, spc)
    | _ ->
      if unfoldable?(tm, spc) && length(freeVars tm) > 1    % if one arg then it is probably a boolean attribute of state
        then let uf_tm = simplify spc (unfoldTerm(tm, spc)) in
             getExpandedConjuncts(uf_tm, spc) 
      else [tm]

op compatibleItmLists?(p_results_info: ItemValList, q_results_info: ItemValList): Bool =
   length p_results_info = length q_results_info
     && forall? (fn ((vp, fldsp, argsp, _), (vq, fldsq, argsq, _)) ->
                   equalTerm?(vp, vq)
                     && equalList?(fldsp, fldsq, equalTerm?)
                     && equalList?(argsp, argsq, equalTerm?))
          (zip(p_results_info, q_results_info))

op setfInfoForAccesser (setf_entries: SetfEntries) (accesser_nm: QualifiedId): Option SetfEntry =
  findLeftmost (fn setf_entry -> accesser_nm = setf_entry.accesser_name) setf_entries

op recordItemVal (spc: Spec, result_vars: MSVars, op_qid: QualifiedId, setf_entries: SetfEntries, complain?: Bool)
                 (results_info: ItemValList, cj: MSTerm) : ItemValList =
  % let _ = writeLine("recordItemVal:\n"^printTerm cj) in
  case cj of
    | Apply(Fun(Equals,_,_),
            Record([(_, Apply(f as Fun(proj,_,_), lval_tm, _)), (_, rhs)], _), _)
        | projectionFun?(proj, spc) ->
      (lval_tm, [f], [], rhs) :: results_info
    | Apply(Fun(Equals,_,_), Record([(_, lval_tm as Var(v,_)), (_, rhs)], _), _) | inVars?(v, result_vars) ->
      (lval_tm, [], [], rhs) :: results_info
    | Apply(Fun(Equals,_,_),     % Reversed orientation of equality v = o s'
            Record([(_, rhs), (_, Apply(f as Fun(proj,_,_), lval_tm, _))], _), _)
        | projectionFun?(proj, spc) ->
      (lval_tm, [f], [], rhs) :: results_info
    %% Reversed orientation of equality
    | Apply(Fun(Equals,_,_), Record([(_, lhs), (_, lval_tm as Var(v,_))], _), _) | inVars?(v, result_vars) ->
      (lval_tm, [], [], lhs) :: results_info
    | Apply(Fun(Equals,_,_), Record([(_, lhs as Record(flds as ("1", _) :: _, _)), (_, rhs)], _), _) ->
      let projection_cjs = map (fn (id, fld_val) ->
                                  mkEquality(inferType(spc, fld_val),
                                             fld_val, mkProjection(id, rhs, spc)))
                             flds
      in
      foldl (recordItemVal (spc, result_vars, op_qid, setf_entries, complain?)) results_info projection_cjs
    | Apply(Fun(Equals,_,_), Record([(_, lhs), (_, rhs)], _), _) ->
      (case getCurryArgs lhs 
         | Some(f as Fun(proj,_,_), lval_tm :: r_args) | projectionFun?(proj, spc) ->
           (lval_tm, [f], r_args, rhs) :: results_info
         | _ ->
       case getCurryArgs rhs 
         | Some(f as Fun(proj,_,_), lval_tm :: r_args) | projectionFun?(proj, spc) ->
           (lval_tm, [f], r_args, lhs) :: results_info
         | _ ->
       case opAndArgs lhs of                                 % uncurry and split apart
         | Some (name_of_accesser, accesser, (Apply(f as Fun(proj,_,_), lval_tm, _)) :: r_args)
             | projectionFun?(proj, spc) && some?(setfInfoForAccesser setf_entries name_of_accesser) ->
           (lval_tm, [f, accesser], flattenArgs r_args, rhs) :: results_info
         | _ ->
       (if complain? then writeLine("For "^show op_qid^"\nIgnoring conjunct\n"^printTerm cj) else ();
        results_info))
    | Apply(f as Fun(proj,_,_), lval_tm, _) | projectionFun?(proj, spc) ->   % Bool true
      (lval_tm, [f], [], trueTerm) :: results_info
    | Apply(Fun(Not, _, _), Apply(f as Fun(proj,_,_), lval_tm, _), _)                             % Bool false
        | projectionFun?(proj, spc) ->
      (lval_tm, [f], [], falseTerm) :: results_info
    | Let(binds, bod, _) ->
      let bod_results_info = recordItemVal (spc, result_vars, op_qid, setf_entries, complain?) ([], bod) in
      let n_results_info  = map (fn (lval_tm, ids, args, b) -> (lval_tm, ids, args, mkLet(binds, b))) bod_results_info in
      n_results_info ++ results_info
    | IfThenElse(c, p, q, a) ->
      let p_results_info = recordItemVal (spc, result_vars, op_qid, setf_entries, complain?) ([], p) in
      let q_results_info = recordItemVal (spc, result_vars, op_qid, setf_entries, complain?) ([], q) in
      % let _ = (writeLine(printTerm cj);
      %          writeLine("p: "^anyToPrettyString p_results_info);
      %          writeLine("q: "^anyToPrettyString q_results_info);
      %          writeLine("sofar: "^anyToPrettyString results_info)) in
      if compatibleItmLists?(p_results_info, q_results_info)
        then
          let merged_state_items = map (fn ((lval_tm, fi, args, pi), (_, _, _, qi)) ->
                                          (lval_tm, fi, args, IfThenElse(c, pi, qi, a)))
                                     (zip(p_results_info, q_results_info))
          in
          merged_state_items ++ results_info
      else  % Not sure what to do here
      (if complain? then writeLine("For "^show op_qid^"\nIgnoring conditional conjunct\n"^printTerm cj) else ();
       results_info)
    | Apply(Fun(And,_,_), Record([("1",_), ("2",_)],_), _) ->
      foldl (recordItemVal (spc, result_vars, op_qid, setf_entries, complain?)) results_info (getExpandedConjuncts(cj, spc))
    | _ ->
      (if complain? then writeLine("For "^show op_qid^"\nIgnoring conjunct\n"^printTerm cj) else ();
       results_info)

op mkFnUpdate (spc: Spec) (f: MSTerm) (x: MSTerm) (v: MSTerm): MSTerm =
  let f_type = inferType(spc, f) in
  let x_type = inferType(spc, x) in
  let v_type = inferType(spc, v) in
  let lens_ty = mkBase(Qualified("Lens", "Lens"), [f_type, x_type]) in
  let lens_tm = mkApply(mkOp(Qualified("Lens", "fnLens"), mkArrow(x_type, lens_ty)), x) in
  let useLenses? = some?(findTheType(spc, lens_qid)) in
  if useLenses?
    then mkCurriedApply(mkProject("lens_set", lens_ty, mkArrow(f_type, mkArrow(v_type, f_type))), 
                        [lens_tm, f, v])
  else
    mkCurriedApply(mkOp(Qualified("Function", "fnUpdate"),
                        mkArrows([f_type, x_type, v_type], f_type)),
                   [f, x, v])

%% f x y z = v --> fnUpd f x (fnUpd (f x) y (fnUpd (f x y) z v))
op argsToUpdates(f: MSTerm, args: MSTerms, v: MSTerm, spc: Spec): MSTerm =
  case args
    | [] -> v
    | x :: r_args ->
      mkFnUpdate spc f x (argsToUpdates(mkApply(f, x), r_args, v, spc))

op argsValPairsToUpdate(upd_tm: MSTerm, arg_val_pairs: List1(MSTerms * MSTerm), spc: Spec): MSTerm =
  case arg_val_pairs
    | [(args, val_tm)] -> argsToUpdates(upd_tm, args, val_tm, spc)
    | (args, val_tm) :: r_arg_val_pairs ->
      let rec_upd_tm = argsValPairsToUpdate(upd_tm, r_arg_val_pairs, spc) in
      argsToUpdates(rec_upd_tm, args, val_tm, spc)

op lens_compose_qid: QualifiedId = Qualified("Lens", "lens_compose")
op lens_qid: QualifiedId = Qualified("Lens", "Lens")

op applyLensSet (spc: Spec) (lens: MSTerm) (val: MSTerm) (fld_val: MSTerm): MSTerm =
  let lens_ty as Base(Qualified("Lens", "Lens"), [a, b], _) = inferType(spc, lens) in
  let val_ty = inferType(spc, val) in
  let fld_val_ty = inferType(spc, fld_val) in
  case getCurryArgs fld_val
    | Some(Fun(Project "lens_set", Arrow(inner_lens_ty as Base(Qualified("Lens", "Lens"), [_, c], _), _, _), _),
           [inner_lens, inner_val, inner_fld_val]) -> % Need to restrict inner_val
      let inner_fld_val_ty = inferType(spc, inner_fld_val) in
      let composed_lens_ty = mkBase(lens_qid, [a, c]) in
      let composed_lens = mkAppl(mkOp(lens_compose_qid, mkArrow(mkProduct[lens_ty, inner_lens_ty], composed_lens_ty)),
                                 [lens, inner_lens])
      in
      mkCurriedApply(mkProject("lens_set", composed_lens_ty, mkArrows([val_ty, inner_fld_val_ty], val_ty)),
                     [composed_lens, val, inner_fld_val])
    | _ -> mkCurriedApply(mkProject("lens_set", lens_ty, mkArrows([val_ty, fld_val_ty], val_ty)),
                          [lens, val, fld_val])

op mkParallelLensSets (spc: Spec) (lens_exprs: List(MSTerm * MSTerm) | lens_exprs ~= []) (init_tm: MSTerm): MSTerm =
  let (lens_0, arg_0) = last lens_exprs in
  foldr (fn ((lens_i, arg_i), val) ->
           (applyLensSet spc lens_i val arg_i))
    (applyLensSet spc lens_0 init_tm arg_0)
    (butLast lens_exprs)

op makeRecordLens (spc: Spec) (rec_ty: MSType) (id: Id) (fld_ty: MSType): MSTerm =
  let rec_var = ("r", rec_ty) in
  let new_val_var = ("x", fld_ty) in
  mkRecord[("lens_get",
            mkLambda(mkVarPat rec_var, mkProjection(id, mkVar rec_var, spc))),
           ("lens_set",
            mkLambda(mkVarPat rec_var, mkLambda(mkVarPat new_val_var,
                                                mkRecordMerge(mkVar rec_var,
                                                              mkRecord[(id, mkVar new_val_var)]))))]

op makeRecordLensPair (spc: Spec) (rec_ty as Base(rec_qid, _, _): MSType) (id: Id, new_val: MSTerm): MSTerm * MSTerm =
  let rec_var = ("r", rec_ty) in
  let fld_ty = inferType(spc, new_val) in
  let new_val_var = ("x", fld_ty) in
  let (lens_qid, lens_ty) = lensInfoForField(id, rec_qid, rec_ty, fld_ty) in
  (mkOp(lens_qid, lens_ty),
   new_val)

op collectValues(results_info: ItemValList, params: MSVars, setf_entries: SetfEntries, useLenses?: Bool, spc: Spec): TermSubst =
  % let _ = (writeLine("collectStateValues:"); app (fn (lval_tm, fs, args, tm) -> writeLine(printTerm lval_tm^"  "^printTerm tm)) results_info) in
  %% Group results by first and second arguments
  let lval_tms = removeDuplicatesEquiv(map (project 1) results_info, equalTerm?) in
  let grouped_info = map (fn l_tm ->
                            let triples_for_lval =
                                removeDuplicatesEquiv
                                  (mapPartial (fn (l_tm_i, constrs, args, tm) ->
                                                 if equalTerm?(l_tm_i, l_tm) then Some(constrs, args, tm) else None)
                                     results_info,
                                   fn ((constrs1, args1, tm1), (constrs2, args2, tm2)) ->
                                     equalList?(constrs1, constrs2, equalTerm?)
                                       && equalList?(args1, args2, equalTerm?)
                                       && equalTerm?(tm1, tm2))
                            in
                            let constrs_lsts = removeDuplicatesEquiv(map (project 1) triples_for_lval,
                                                                     fn (xs, ys) -> equalList?(xs, ys, equalTerm?)) in
                            let constr_groups =
                                map (fn constrs ->
                                       let pairs_for_constrs =
                                           removeDuplicatesEquiv
                                             (mapPartial (fn (constrs_i, args, tm) ->
                                                            if equalList?(constrs, constrs_i, equalTerm?)
                                                              then Some(args, tm) else None)
                                                triples_for_lval,
                                              fn ((args1, tm1), (args2, tm2)) ->
                                                 equalList?(args1, args2, equalTerm?)
                                                   && equalTerm?(tm1, tm2))
                                       in
                                       (constrs, pairs_for_constrs))
                                  constrs_lsts
                            in
                            (l_tm, constr_groups))
                        lval_tms
  in
  let (non_incr_info, incr_info) = split (fn (_, ([], (args, _)::_)::_) -> true | _ -> false, grouped_info) in
  let non_incr_sbst = map (fn | (lval_tm, (_, arg_val_pairs)::rst) ->
                             let _ = if rst = [] then ()
                                      else let _ = warn("Ignoring extra assignment to "^printTerm lval_tm) in
                                           let _ = app (fn (_, (_, tm)::_) -> writeLine(printTerm tm)) rst in
                                           ()
                             in
                             let val = argsValPairsToUpdate(lval_tm, arg_val_pairs, spc) in
                             (lval_tm, val))
                        non_incr_info
  in
  let incr_sbst = map (fn (lval_tm, constr_groups) ->
                         let id_prs = mapPartial (fn | ([f as Fun(proj, _, _)], arg_val_pairs) ->
                                                       let src_tm =
                                                           case findSourceTerm([], lval_tm, params, spc) of
                                                             | None -> lval_tm
                                                             | Some src_tm -> src_tm
                                                       in
                                                       mapOption (fn id -> (id, argsValPairsToUpdate
                                                                                  (mkApply(f, src_tm), arg_val_pairs, spc)))
                                                         (projectionFun(proj, spc))
                                                     | _ -> None)
                                        constr_groups
                         in
                         let _ = if length id_prs ~= length constr_groups
                                   then warn("Ignoring one or more updates to "^printTerm lval_tm) else ()
                         in
                         let lval_ty = inferType(spc, lval_tm) in
                         case findSourceTerm(id_prs, lval_tm, params, spc)
                           | None -> (lval_tm, mkCanonRecord id_prs)
                           | Some src_tm ->
                         let val = if useLenses?
                                     then mkParallelLensSets spc (map (makeRecordLensPair spc lval_ty) id_prs) src_tm
                                     else makeRecordMerge spc
                                            (translateRecordMerge1 spc false
                                               (mkRecordMerge(src_tm, mkCanonRecord id_prs)))
                         in                                            
                         (lval_tm, val))
                    incr_info
  in
  incr_sbst ++ non_incr_sbst


op makeDefTermFromPostCondition(top_dfn: MSTerm, post_condn: MSTerm, result_tm: MSTerm, result_vars: MSVars,
                                op_qid: QualifiedId, spc: Spec, result_ty: MSType)
     : Option MSTerm =
   % let _ = writeLine("\nmdfuct: "^show op_qid^" "^"\n"^printTerm post_condn) in
   let params = parameterBindings top_dfn in
   let setf_entries = findSetfEntries spc in
   let useLenses? = some?(findTheType(spc, lens_qid)) in
   let def makeDef(tm: MSTerm, inh_cjs: MSTerms, seenQIds: QualifiedIds): Option MSTerm =
         % let _ = writeLine("makeDef:\n"^printTerm tm) in
         case tm of
           | IfThenElse(p, q, r, a) ->
             (case (makeDef(q, inh_cjs, seenQIds), makeDef(r, inh_cjs, seenQIds)) of
                | (Some then_def, Some else_def) -> Some(IfThenElse(p, then_def, else_def, a))
                | _ -> None)
           | Let(binds, bod, a) -> mapOption (fn bod -> Let(binds, bod, a)) (makeDef(bod, inh_cjs, seenQIds))
           | Apply(Lambda(matches, a1), e, a2) ->
             let n_matches = mapPartial (fn (p, c, bod) ->
                                           mapOption (fn nbod -> (p, c, nbod)) (makeDef(bod, inh_cjs, seenQIds)))
                               matches
             in
             if length matches = length n_matches
                then Some(Apply(Lambda(n_matches, a1), e, a2))
                else None
           | Apply(Fun(And,_,_), _, _) ->
             (let cjs = getExpandedConjuncts(tm, spc) in
              let cjs = inh_cjs ++ cjs in
              case findLeftmost (fn cj -> case cj of
                                            | Let _ -> true
                                            | IfThenElse _ -> true
                                            | Apply(Lambda _, _, _) -> true
                                            | _ -> false)
                     cjs of
                | Some complex_cj -> makeDef(complex_cj, delete(complex_cj, cjs), seenQIds)
                | None -> 
              let results_info = foldl (recordItemVal (spc, result_vars, op_qid, setf_entries, true)) [] cjs in
              let results_sbst = collectValues(results_info, params, setf_entries, useLenses?, spc) in
              checkResult(termSubst(result_tm, results_sbst)))
           | _ ->
         if inh_cjs ~= []
           then makeDef(mkConj(inh_cjs ++ [tm]), [], seenQIds)
         else
         case tm of
           | Apply(Fun(Equals,_,_), _, _) ->
             let results_info = recordItemVal (spc, result_vars, op_qid, setf_entries, true) ([], tm) in
             let results_sbst = collectValues(results_info, params, setf_entries, useLenses?, spc) in
             checkResult(termSubst(result_tm, results_sbst))
           | _ -> (warn("makeDefTermFromPostCondition: Unexpected kind of term in "^show op_qid^"\n"
                          ^printTerm tm);
                   None)
       def checkResult(result: MSTerm): Option MSTerm =
         if exists? (fn v -> inVars?(v, result_vars)) (freeVars result)
           then let _ = warn("Unbound variables in body constructed for "^show op_qid^"\n"^printTerm result) in
                Some result
           else Some result
        def replaceBody(dfn, bod) =
         case dfn of
           | Lambda([(binds, p, o_bod)], a) ->
             Lambda([(binds, p, replaceBody(o_bod, bod))], a)
           | _ -> bod
   in
   case makeDef(post_condn, [], []) of
     | None -> None
     | Some new_bod -> 
       let dfn = replaceBody(top_dfn, new_bod) in
       Some dfn

op derefPostCondition (ty: MSType, spc: Spec): Option(MSTerm * MSTerm) =
  case range_*(spc, ty, false)
    | Subtype(result_ty, Lambda([(pat, _, condn)], _), _) ->
      (case patternToTerm pat
         | Some tm -> Some(tm, condn)
         | _ -> None)
    | _ -> None

op realTerm(tm: MSTerm): MSTerm =
  case tm
    | Pi(_, ptm, _) -> realTerm ptm
    | TypedTerm(ptm, _, _) -> realTerm ptm
    | _ -> tm

op MSTermTransform.finalizeUpdates (spc: Spec) (op_qid: TransOpName) (tm: TransTerm) (ptm: PathTerm)
     (stored_qids: QualifiedIds): Option MSTerm =
  if case grandParentTerm ptm of
       | None -> false
       | Some gptm -> conjunction?(fromPathTerm gptm)
    then None
  else
    % let _ = writeLine("fupds: "^printTerm(topTerm ptm)) in
    let params = parameterBindings(realTerm(topTerm ptm)) in
    let setf_entries = findSetfEntries spc in
    let useLenses? = some?(findTheType(spc, lens_qid)) in
    let def stored_qids_updates(cj: MSTerm): ItemValList =
          let raw_updates = recordItemVal (spc, [], op_qid, setf_entries, false) ([], cj) in
          filter (fn (_, updates, args, _) ->
                  case updates
                    | [f as Fun(proj, _, _)] ->
                      (case projectionFun(proj, spc)
                         | None -> false
                         | Some fld_name -> exists? (fn Qualified(_, id) -> id = fld_name) stored_qids)
                    | _ -> false)
            raw_updates
    in
    if conjunction? tm
      then
      let (results_info, unchanged_cjs) =
          foldl (fn ((results_info, unchanged_cjs), cj) ->
                   case stored_qids_updates cj
                     | [] -> (results_info, cj :: unchanged_cjs)
                     | new_results_info -> (results_info ++ new_results_info, unchanged_cjs))
            ([], []) (getConjuncts tm)
      in
      if results_info = [] then None
      else
        Some(mkConj(reverse unchanged_cjs
                      ++ map (makeEquality spc) (collectValues(results_info, params, setf_entries, useLenses?, spc))))
    else
      let results_info = stored_qids_updates tm in
      if results_info = [] then None
      else
        Some(mkConj(map (makeEquality spc) (collectValues(results_info, params, setf_entries, useLenses?, spc))))

op finalizeCoTypeUpdatesInPostCondition
     (spc: Spec) (stored_qids: QualifiedIds) (fn_qids: QualifiedIds): Env Spec =
  let script = At(map Def fn_qids,
                  mkRepeat(50, mkSteps[mkTermTransform("finalizeUpdates") [ListV (map OpNameV stored_qids)],
                                       Move[Search "&&"]]))
  in
   % print "rewriting ... \n";
   % print (scriptToString script^"\n");
   interpret(spc, script)

op SpecTransform.makeDefsFromPostConditions (spc: Spec) (fn_qids: QualifiedIds): Spec =
  foldl (fn (spc, qid) ->
           case findTheOp(spc, qid) of
             | None -> spc
             | Some info ->
               let (tvs, ty, top_tm) = unpackFirstTerm info.dfn in
               if ~(anyTerm? top_tm) then spc
               else
                 (case derefPostCondition(ty, spc) of
                    | None -> spc
                    | Some(result_tm, post_condn) ->
                  case makeDefTermFromPostCondition
                        (top_tm, post_condn, result_tm, freeVars result_tm,
                         primaryOpName info, spc, range_*(spc, ty, true))
                    | None -> spc
                    | Some new_def -> addRefinedDef(spc, info, new_def)))
    spc fn_qids

op addDefForDestructor(spc: Spec, qid: QualifiedId): Spec =
  case findTheOp(spc, qid) of
    | None -> spc
    | Some info ->
      let (tvs, ty, tm) = unpackFirstTerm info.dfn in
      case ty of
        | Arrow(dom, rng, _) ->
          let v = ("st", dom) in
          let new_def = mkLambda(mkVarPat v, mkApply(mkProject(qualifiedIdToField qid, dom, rng), mkVar v)) in
          addDef(spc, info, new_def)
        | _ -> spc

op lensInfoForField(field_id: Id, Qualified(q, ty_id): QualifiedId, rec_ty: MSType, fld_ty: MSType): QualifiedId * MSType =
  let lens_qid = Qualified(q, ty_id^"_"^field_id^"_lens") in
  (lens_qid, mkBase(Qualified("Lens", "Lens"), [rec_ty, fld_ty]))

op makeLensForRecordField(spc: Spec, field_id: Id, rec_qid: QualifiedId, rec_ty: MSType, fld_ty: MSType): Spec =
  let (lens_qid, lens_ty) = lensInfoForField(field_id, rec_qid, rec_ty, fld_ty) in
  let tvs = freeTyVars lens_ty in
  let lens_def = makeRecordLens spc rec_ty field_id fld_ty in
  addNewOp(lens_qid, Nonfix,
           maybePiTerm(tvs, mkTypedTerm(lens_def, lens_ty)),
           spc)

%% op SpecTransform.doNothing(spc: Spec): Spec = spc

op SpecTransform.finalizeCoType(spc: Spec)
     (qids: QualifiedIds, observer_qids: Option(QualifiedIds))
     (dont_make_defs?: Bool): Env Spec =
  let _ = writeLine("finalizeCoType") in
  let useLenses? = some?(findTheType(spc, lens_qid)) in
  case qids of
    | [] -> raise(Fail("No type to realize!"))
    | state_qid :: rest_qids ->
  case findTheType(spc, state_qid) of
    | None -> raise(Fail("type "^show state_qid^" not found!"))
    | Some type_info ->
  {new_spc <- return spc;
   stored_qids <- return(case observer_qids 
                           | Some ids -> ids
                           | _ -> sortFields(findStoredOps(spc, state_qid)));
   (case findLeftmost (fn qid -> none?(findTheOp(spc, qid))) stored_qids
      | Some qid -> raise(Fail("Op "^show qid^" not in spec!"))
      | _ -> return());
   print("stored_qids: "^anyToString (map show stored_qids)^"\n");
   field_pairs <- return(makeRecordFieldsFromQids(new_spc, stored_qids));
   record_ty <- return(mkRecordType(field_pairs));
   new_spc <- return(if stored_qids = [] then new_spc
                     else addTypeDef(new_spc, state_qid,
                                     maybePiType(freeTyVars record_ty, record_ty)));
   new_spc <- return(foldl addDefForDestructor new_spc stored_qids);
   new_spc <- return(if useLenses?
                      then foldl (fn (new_spc, (fld_id, fld_ty)) ->
                                    makeLensForRecordField(new_spc, fld_id, state_qid, mkBase(state_qid, []), fld_ty))
                             new_spc field_pairs
                     else new_spc);
   fn_qids_to_transform <- return(postConditionOpsReferencingType(new_spc, state_qid));
   script <- return(At(map Def fn_qids_to_transform,
                       mkSteps[mkSimplify(map Unfold stored_qids)]));
   new_spc <- interpret(new_spc, script);
   new_spc <- if dont_make_defs?
                then finalizeCoTypeUpdatesInPostCondition new_spc stored_qids fn_qids_to_transform
              else return(makeDefsFromPostConditions new_spc fn_qids_to_transform);
   return new_spc}

op MSTermTransform.mergePostConditions (spc: Spec) (tm: TransTerm): Option MSTerm =
  % let _ = writeLine("mergePostConditions:\n"^printTerm tm) in
  case tm of
    | TypedTerm(orig_tm, orig_ty, a) ->
      (case getPostCondn(orig_ty, spc) of
         | None -> (warn("mergePostConditions: No postcondition.");
                    None)
         | Some(orig_pc_pat, orig_pc) ->
       let (params, bod) = curriedParamsBody orig_tm in
       case getFnArgs bod of
         | Some(Fun(Op(qid, _), _, _), args, _) ->
           (case findTheOp(spc, qid) of
             | None -> None
             | Some info ->
            let (_, ty, sub_dfn) = unpackFirstOpDef info in
            case getPostCondn(ty, spc) of
              | None -> (warn("mergePostConditions: No postcondition.");
                         None)
              | Some(sub_pat, sub_pc) ->
            case matchPatterns(orig_pc_pat, sub_pat) of
              | None -> (warn("mergePostConditions: Incompatible postconditions.");
                         None)
              | Some pc_sbst ->
            % let _ = printVarSubst pc_sbst in
            let (sub_params, _) = curriedParamsBody sub_dfn in
            if length args ~= length sub_params
              then (warn("mergePostConditions: Mismatch in number of args and parameters.");
                         None)
            else
            case foldl (fn (o_sbst, (param, arg)) ->
                          case o_sbst of
                            | None -> None
                            | Some sbst ->
                          case patternMatch(param, arg, sbst, []) of
                            | Match sbst -> Some sbst
                            | _ -> None)
                   (Some pc_sbst) (zip(sub_params, args)) of
                | None -> (warn("mergePostConditions: Can't unfold body -- mismatch with parameters.");
                           None)
                | Some sbst ->
             % let _ = printVarSubst sbst in
             let new_ty = addPostCondition(substitute(sub_pc, sbst), orig_ty) in
             let new_tm = mkCurriedLambda(params, Any noPos) in
             Some(TypedTerm(new_tm, new_ty, a)))
         | None -> (warn("mergePostConditions: Body not a function application.");
                    None))
    | _ -> (warn("mergePostConditions: Must be applied to typed term.");
            None)

end-spec
