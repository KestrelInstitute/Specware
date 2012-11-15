(* Transformations on coalgebraic definitions in specs *)

Coalgebraic qualifying
spec
import Script

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

op getStateVarAndPostCondn(ty: MSType, state_ty: MSType, spc: Spec): Option(Var * Option(Id * List(Id * MSPattern)) * MSTerm) =
  case range_*(spc, ty, false) of
    | Subtype(result_ty, Lambda([(pat, _, condn)], _), _) ->
      (if equivTypeSubType? spc (result_ty, state_ty) true
       then case pat of
              | VarPat(result_var,_) -> Some(result_var, None, condn)
              | _ -> None
       else case (result_ty, pat) of
              | (Product(ty_prs, _), RecordPat(pat_prs, _)) ->
                (case findLeftmost (fn (id, ty) -> equalTypeSubtype?(ty, state_ty, true)) ty_prs of
                   | None -> None
                   | Some(id1,_) ->
                 case findLeftmost (fn (id2, _) -> id1 = id2) pat_prs of
                   | None -> None
                   | Some(_, VarPat(result_var,_)) -> Some(result_var, Some(id1, pat_prs), condn))                            
              | _ -> None)
    | _ -> None

op equalitySpecToLambda(lhs: MSTerm, rhs: MSTerm, lam_pats: List MSPattern, fn_qid: QualifiedId): Option(List MSPattern * MSTerm) =
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

op makeSubstFromPatLists(pats1: List MSPattern, pats2: List MSPattern): VarSubst =
  flatten (map (fn (p1, p2) -> let Some sbst = matchPatterns(p1, p2) in sbst) (zip(pats1, pats2)))

op getDefFromTheorem(thm_qid: QualifiedId, intro_qid: QualifiedId, spc: Spec): MSTerm =
  case findMatchingTheorems(spc, thm_qid) of
    | [] -> error("No theorem matching "^show thm_qid)
    | matching_thms ->
      let (_, _, tvs, bod, _) = last matching_thms in
      let def extractDefComps(bod: MSTerm): List(List MSPattern * MSTerm * MSTerm) =
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
          
      
def Coalgebraic.maintainOpsCoalgebraically
      (spc: Spec, qids: QualifiedIds, rules: List RuleSpec): Env Spec =
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
         case getStateVarAndPostCondn(ty, state_ty, spc) of
           | Some (result_var, deref?, post_cond)
               | ~(containsRefToOp?(post_cond, intro_qid)) ->
             let result_tm0 = mkApplyTermFromLambdas(mkOp(qid, ty), tm) in
             let result_tm = case deref? of
                               | Some (id, _) ->
                                 mkApply(mkProject(id, range_*(spc, ty, true), state_ty),
                                         result_tm0)
                               | None -> result_tm0
             in
             % let _ = writeLine("\nLooking at "^show qid) in
             % let _ = writeLine("Result var is "^result_var.1) in
             % let _ = writeLine("Result tm is "^printTerm result_tm) in
             let new_lhs = mkApply(intro_fn, mkVar result_var) in
             let intro_fn_rng = inferType(spc, new_lhs) in
             let raw_rhs = simplifiedApply(intro_fn_def, result_tm, spc) in
             % let _ = writeLine("\nBody to transform:\n"^printTerm raw_rhs) in
             let new_intro_ty = addPostCondition(mkEquality(intro_fn_rng, new_lhs, raw_rhs), ty) in
             let spc = addRefinedType(spc, info, new_intro_ty) in
             (spc, qid :: qids)
           | _ -> result
   in
   let (spc, qids) = foldOpInfos addToDef (spc, []) spc.ops in
   let script = Steps[Trace true,
                      At(map Def (reverse qids),
                         Repeat [Move [Search intro_id, Next], % Go to postcondition just added and simplify
                                 mkSimplify [],
                                 Simplify1(rules),
                                 mkSimplify(fold_rl :: rules)])]
   in
   {print "rewriting ... \n";
    print (scriptToString script^"\n"); 
    spc <- interpret(spc, script);
    return spc}}

op findHomomorphismFn(tm: MSTerm): Option QualifiedId =
  case tm of
    | Bind(Forall, _, bod,_) -> findHomomorphismFn bod
    | Apply(Fun(Equals,_,_),
            Record([(_,e1),(_,Apply(Fun(Op(qid,_),_,_), _, _))], _),_) ->
      Some qid
    | _ -> None

def Coalgebraic.implementOpsCoalgebraically
  (spc: Spec, qids: QualifiedIds, rules: List RuleSpec): Env Spec =
  case qids of
    | [replace_op_qid, assert_qid] ->
      (case findPropertiesNamed(spc, assert_qid) of
         | [] -> raise(Fail("Can't find property named "^show assert_qid))
         | [(_, _, _, body, _)] ->
           (case findHomomorphismFn body of
            | None -> raise(Fail("Can't find homomorphism fn from axiom:\n"^printTerm body))
            | Some homo_fn_qid -> 
              {replace_op_info <- findTheOp spc replace_op_qid;
               let (tvs, replace_op_ty, _) = unpackFirstTerm replace_op_info.dfn in
               let _ = writeLine("Implement "^show replace_op_qid^": "^printType replace_op_ty) in
               let _ = writeLine("With rewrite: "^printTerm body) in
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
               let script = Steps[Trace true,
                                  At(map Def (reverse state_transform_qids),
                                     Steps [mkSimplify(RLeibniz homo_fn_qid
                                                         :: LeftToRight assert_qid
                                                         :: rules)])]
               in
               {print "rewriting ... \n";
                print (scriptToString script^"\n");
                spc <- interpret(spc, script);
                return spc}
               })
         | props -> raise(Fail("Ambiguous property named "^show assert_qid)))
    | _ -> raise(Fail("implement expects op and theorem QualifiedIds"))

op hasTypeRefTo?(ty_qid: QualifiedId, ty: MSType): Bool =
  existsInType? (fn sty -> case sty of
                             | Base(qid, _, _) -> qid = ty_qid
                             | _ -> false)
    ty

op getConjoinedEqualities(t: MSTerm): MSTerms =
  case t of
    | IfThenElse(_, t1, t2, _) ->
      getConjoinedEqualities t1 ++ getConjoinedEqualities t2
    | Apply(Fun(And,_,_), Record([("1",t1),("2",t2)],_),_) ->
      getConjoinedEqualities t1 ++ getConjoinedEqualities t2
    | _ -> [t]

op findStoredOps(spc: Spec, state_qid: QualifiedId): QualifiedIds =
  let state_ty = mkBase(state_qid, []) in
  foldOpInfos
    (fn (info, stored_qids) ->
      let  (tvs, ty, tm) = unpackFirstTerm info.dfn in
      if ~(anyTerm? tm) then stored_qids
      else
      case getStateVarAndPostCondn(ty, state_ty, spc) of
        | Some(state_var, deref?, post_condn) ->
          removeDuplicates
            (mapPartial
               (fn cj ->
                  case cj of
                    | Apply(Fun(Equals,_,_),Record([(_,lhs),_], _),_) ->
                      (case lhs of
                         | Apply(Fun(Op(qid,_), _, _), Var(v, _), _)
                             | qid nin? stored_qids && equalVar?(v, state_var)
                                  && ~(finalizeExcludesDefinedOps? && definedOp?(spc, qid)) ->
                           % let _ = if show qid = "WS" then writeLine(show(primaryOpName info)^" "^printType ty) else () in
                           Some qid
                         | _ -> None)
                    | Apply(Fun(Op(qid,_), _, _), Var(v, _), _)    % Bool
                        | qid nin? stored_qids && equalVar?(v, state_var)
                          && ~(finalizeExcludesDefinedOps? && definedOp?(spc, qid)) ->
                      Some qid
                    | Apply(Fun(Not, _, _), Apply(Fun(Op(qid,_), _, _), Var(v, _), _), _)    % Bool
                        | qid nin? stored_qids && equalVar?(v, state_var)
                          && ~(finalizeExcludesDefinedOps? && definedOp?(spc, qid)) ->
                      Some qid
                    | _ -> None)
            (getConjoinedEqualities post_condn))
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

op findSourceVar(cjs: MSTerms, state_var: Var, stored_qids: QualifiedIds): Option Var

op makeDefForUpdatingCoType(top_dfn: MSTerm, post_condn: MSTerm, state_var: Var,
                            deref?: Option(Id * List(Id * MSPattern)), op_qid: QualifiedId,
                            spc: Spec, state_ty: MSType, stored_qids: QualifiedIds,
                            field_pairs: List(Id * MSType), result_ty: MSType)
     : MSTerm =
   % let _ = writeLine("mdfuct: "^state_var.1^"\n"^printTerm post_condn) in
   let params = case top_dfn of
                  | Lambda([(binds, p, o_bod)], a) ->
                    patVars binds
                  | _ -> []
   in
   let (state_id, result_tuple_info) =
       case deref? of
         | None -> ("No id", [])
         | Some(state_id, id_pat_prs) ->
           (state_id,
            map (fn (id, p) ->
                   let Some tm = patternToTerm p in
                   (id, tm))
              id_pat_prs)
   in
   let def makeDef(tm) =
         case tm of
           | IfThenElse(p, q, r, a) ->
             IfThenElse(p, makeDef q, makeDef r, a)
           | Let(binds, bod, a) -> Let(binds, makeDef bod, a)
           | Apply(Fun(And,_,_), Record([("1",t1),("2",t2)],_),a) ->
             (let cjs = getConjuncts tm in
              let (state_rec_prs, opt_rec_prs) = foldl recordItemVal ([], []) cjs in
              let state_res = case tryIncrementalize(state_rec_prs) of
                                | (Some src_tm, inc_rec_prs) ->
                                  if inc_rec_prs = [] then src_tm
                                  else mkRecordMerge(src_tm, mkCanonRecord(inc_rec_prs))
                                | (None, _) -> mkCanonRecord(state_rec_prs)
              in
              % let _ = writeLine("makeDef: "^printTerm state_res) in
              if result_tuple_info = []
                then state_res
                else mkCanonRecord((state_id, state_res) :: opt_rec_prs))             
           | Apply(Fun(Equals,_,_), _, _) ->
             (case recordItemVal (([], []), tm) of
                | (state_rec_prs, []) ->
                  (case tryIncrementalize(state_rec_prs) of
                     | (Some src_tm, inc_rec_prs) ->
                       if inc_rec_prs = [] then src_tm
                       else mkRecordMerge(src_tm, mkCanonRecord(inc_rec_prs))
                     | (None, _) -> mkCanonRecord(state_rec_prs))
                | _ -> (warn("makeDefForUpdatingCoType: Unexpected kind of equality in "^show op_qid^"\n"
                               ^printTerm tm);
                        mkVar("Unrecognized_term", state_ty)))
           | _ -> (warn("makeDefForUpdatingCoType: Unexpected kind of term in "^show op_qid^"\n"
                          ^printTerm tm);
                   mkVar("Unrecognized_term", result_ty))
       def recordItemVal((state_itms, result_itms), cj): List(Id * MSTerm) * List(Id * MSTerm) =
         case cj of
           | Apply(Fun(Equals,_,_),
                   Record([(_, Apply(Fun(Op(qid,_),_,_), Var(v,_), _)), (_, rhs)], _), _)
               | qid in? stored_qids && equalVar?(state_var, v) ->
             ((qualifiedIdToField qid, rhs) :: state_itms, result_itms)
           | Apply(Fun(Equals,_,_),Record([(_, lhs), (_, rhs)], _), _)
               | exists? (fn (_,r_tm) -> equalTerm?(r_tm, lhs)) result_tuple_info ->
             let Some(id, _) = findLeftmost (fn (_,r_tm) -> equalTerm?(r_tm, lhs))
                                 result_tuple_info in
             (state_itms, (id, rhs) :: result_itms)
           | Apply(Fun(Op(qid,_),_,_), Var(v,_), _)
               | qid in? stored_qids && equalVar?(state_var, v) ->   % Bool true
             ((qualifiedIdToField qid, trueTerm) :: state_itms, result_itms)
           | Apply(Fun(Not, _, _), Apply(Fun(Op(qid,_),_,_), Var(v,_), _), _)                             % Bool false
               | qid in? stored_qids && equalVar?(state_var, v) ->
             ((qualifiedIdToField qid, falseTerm) :: state_itms, result_itms)
           | IfThenElse(c, p, q, a) ->
             let (p_state_itms, p_result_itms) = recordItemVal(([], []), p) in
             let (q_state_itms, q_result_itms) = recordItemVal(([], []), q) in
             % let _ = (writeLine(printTerm cj);
             %          writeLine("p: "^anyToPrettyString p_state_itms^"\n"^anyToPrettyString p_result_itms);
             %          writeLine("q: "^anyToPrettyString q_state_itms^"\n"^anyToPrettyString q_result_itms);
             %          writeLine("sofar: "^anyToPrettyString state_itms^"\n"^anyToPrettyString result_itms)) in
             if p_result_itms = [] && q_result_itms = []
                 && compatibleItmLists?(p_state_itms, q_state_itms)
               then
                 let merged_state_items = map (fn ((idi, pi), (_, qi)) -> (idi, IfThenElse(c, pi, qi, a)))
                                            (zip(p_state_itms, q_state_itms))
                 in
                 (merged_state_items ++ state_itms, result_itms)
             else  % Not sure what to do here
             (writeLine("For "^show op_qid^"\nIgnoring conditional conjunct\n"^printTerm cj);
              (state_itms, result_itms)) 
           | _ -> (writeLine("For "^show op_qid^"\nIgnoring conjunct\n"^printTerm cj);
                   (state_itms, result_itms))
       def compatibleItmLists?(p_state_itms, q_state_itms) =
         length p_state_itms = length q_state_itms
           && forall? (fn ((idp, _), (idq, _)) -> idp = idq) (zip(p_state_itms, q_state_itms))
       def tryIncrementalize(rec_prs: List(Id * MSTerm)): Option MSTerm * List(Id * MSTerm) =
         let (opt_src_tm, result_prs) =
             foldl (fn ((opt_src_tm, result_prs), (id, tm)) ->
                      case tm of
                        | Apply(Fun(Op(qid,_),_,_), arg, _)
                            | qualifiedIdToField qid = id && (case opt_src_tm of
                                                                | None -> true
                                                                | Some(src_tm) -> equalTerm?(arg, src_tm))
                            -> (Some arg, result_prs)
                        | _ -> (opt_src_tm, (id, tm) :: result_prs))
               (None, [])
               rec_prs
         in
         if some? opt_src_tm || length result_prs = length field_pairs
           then (opt_src_tm, result_prs)
         else
         % let _ = writeLine("Incrementalizing "^show op_qid) in
         let opt_src_tm =
             foldl (fn (result, (id, tm)) ->
                      if some? result then result
                      else
                        % let _ = writeLine(id^": "^printTerm tm) in
                        foldSubTerms
                          (fn (s_tm, result) ->
                             if some? result then result
                             else case s_tm of
                                    | Apply(Fun(Project idi, _, _), v as Var _, _) | idi = id ->
                                      Some v
                                    | Apply(Fun(Op(qidi,_), _, _), v as Var _, _)
                                        | qualifiedIdToField qidi = id ->
                                      Some v
                                    | _ -> None)
                          result tm)
               None result_prs
         in
         let opt_src_tm = if some? opt_src_tm then opt_src_tm
                          else
                             % let _ = writeLine("tryInc: "^ printType state_ty^"\n"^foldl (fn (r, (v, ty)) -> r^", "^v^": "^printType ty) "" params) in
                             case findLeftmost (fn (_, ty) -> equalType?(ty, state_ty)) params of
                                 | Some v -> Some(mkVar v)
                                 | None -> None
         in
             % let _ = writeLine(case opt_src_tm of Some tm -> printTerm tm | None -> "None") in
                       (opt_src_tm, result_prs)
       def replaceBody(dfn, bod) =
         case dfn of
           | Lambda([(binds, p, o_bod)], a) ->
             Lambda([(binds, p, replaceBody(o_bod, bod))], a)
           | _ -> bod
   in
   let dfn = replaceBody(top_dfn, makeDef post_condn) in
   let unfold_tuple_fns = map Unfold stored_qids in
   let (new_dfn_ptm, hist) = rewriteWithRules(spc, unfold_tuple_fns, op_qid, toPathTerm dfn, []) in
   fromPathTerm new_dfn_ptm

op makeDefinitionsForUpdatingCoType
     (spc: Spec, state_ty: MSType, stored_qids: QualifiedIds, field_pairs: List(Id * MSType)): Spec =
  foldOpInfos
    (fn (info, spc) ->
       let (tvs, ty, top_tm) = unpackFirstTerm info.dfn in
       if ~(anyTerm? top_tm) then spc
       else
         (case getStateVarAndPostCondn(ty, state_ty, spc) of
            | None -> spc
            | Some(state_var, deref?, post_condn) ->
              % let _ = writeLine(show(primaryOpName info)^":\n"^printTerm post_condn) in
              addRefinedDef(spc, info,
                            makeDefForUpdatingCoType
                              (top_tm, post_condn, state_var, deref?,
                               primaryOpName info, spc, state_ty, stored_qids,
                               field_pairs, range_*(spc, ty, true)))))
    spc spc.ops
                           
op addDefForDestructor(spc: Spec, qid: QualifiedId): Spec =
  case findTheOp(spc, qid) of
    | None -> spc
    | Some info ->
      let (tvs, ty, tm) = unpackFirstTerm info.dfn in
      case ty of
        | Arrow(dom, rng, _) ->
          let v = ("st", dom) in
          let new_def = mkLambda(mkVarPat v, mkApply(mkProject(qualifiedIdToField qid, dom, rng), mkVar v)) in
          addRefinedDef(spc, info, maybePiTerm(tvs, TypedTerm(new_def, ty, termAnn tm)))
        | _ -> spc

op SpecTransform.finalizeCoType(spc: Spec, qids: QualifiedIds, rules: List RuleSpec): Env Spec =
  let _ = writeLine("finalizeCoType") in
  case qids of
    | [] -> raise(Fail("No type to realize!"))
    | state_qid :: rest_qids ->
  let state_ty = mkBase(state_qid, []) in
  case findTheType(spc, state_qid) of
    | None -> raise(Fail("type "^show state_qid^" not found!"))
    | Some type_info ->
  {new_spc <- return spc;
   stored_qids <- return(reverse(findStoredOps(spc, state_qid)));
   print("stored_qids: "^anyToString (map show stored_qids)^"\n");
   field_pairs <- return(makeRecordFieldsFromQids(new_spc, stored_qids));
   new_spc <- return(addTypeDef(new_spc, state_qid, mkCanonRecordType(field_pairs)));
   new_spc <- return(foldl addDefForDestructor new_spc stored_qids);
   new_spc <- return(makeDefinitionsForUpdatingCoType(new_spc, state_ty, stored_qids, field_pairs));
   return new_spc}

op MetaRule.mergePostConditions (spc: Spec) (tm: MSTerm): Option MSTerm =
  % let _ = writeLine("mergePostConditions:\n"^printTerm tm) in
  case tm of
    | TypedTerm(orig_tm, orig_ty, a) ->
      (case getPostCondn(orig_ty, spc) of
         | None -> (warn("mergePostConditions: No postcondition.");
                    None)
         | Some(orig_pc_pat, orig_pc) ->
       let (params, bod) = curriedParamsBody orig_tm in
       case getFnArgs bod of
         | Some(Fun(Op(qid, _), _, _), args) ->
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
                          case patternMatch(param, arg, sbst) of
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
