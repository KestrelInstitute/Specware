(* Transformations on coalgebraic definitions in specs *)

Coalgebraic qualifying
spec
import Script

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
             Subtype(sup_ty, Lambda([(v, c, MS.mkAnd(pred, post_condn))], a1), a2)
  in
  replaceInRange ty

op getStateVarAndPostCondn(ty: MSType, state_ty: MSType, spc: Spec): Option(Var * Option Id * MSTerm) =
  case range_*(spc, ty, false) of
    | Subtype(result_ty, Lambda([(pat, _, condn)], _), _) ->
      (if equalTypeSubtype?(result_ty, state_ty, true)
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
                   | Some(_, VarPat(result_var,_)) -> Some(result_var, Some id1, condn))                            
              | _ -> None)
    | _ -> None

def Coalgebraic.maintainOpsCoalgebraically(spc: Spec, qids: QualifiedIds, rules: List RuleSpec): Env Spec =
  let intro_qid = head qids in
  {info <- findTheOp spc intro_qid;
   let (tvs, intro_ty, intro_fn_def) = unpackFirstTerm info.dfn in
   let intro_fn = mkOp(intro_qid, intro_ty) in
   let state_ty = domain(spc, intro_ty) in
   let _ = writeLine("\nMaintain "^show intro_qid^": "^printType intro_ty^"\n"^printTerm intro_fn_def) in
   let def addToDef(info, result as (spc, qids)) =
         let qid = primaryOpName info in
         let (tvs, ty, tm) = unpackFirstTerm info.dfn in
         % let _ = if show qid = "mark" then writeLine("dfn: "^printTerm info.dfn^"\n"^printTerm tm) else () in
         case getStateVarAndPostCondn(ty, state_ty, spc) of
           | Some (result_var, deref?, _) ->
             let result_tm0 = mkApplyTermFromLambdas(mkOp(qid, ty), tm) in
             let result_tm = case deref? of
                               | Some id -> mkApply(mkProject(id, range_*(spc, ty, true), state_ty), result_tm0)
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
           | None -> result
   in
   let (spc, qids) = foldOpInfos addToDef (spc, []) spc.ops in
   let script = Steps[%Trace true,
                      At(map Def (reverse qids),
                         Steps [%Trace true,
                                Move [Post, Last, Last], % Go to postcondition just added and simplify
                                Simplify1(rules),
                                mkSimplify(Fold intro_qid ::
                                             rules)])]
   in
   {print "rewriting ... \n";
    print (scriptToString script^"\n"); 
    spc <- interpret(spc, script);
    return spc}}

op findHomomorphismFn(tm: MSTerm): Option QualifiedId =
  case tm of
    | Bind(Forall, _, bod,_) -> findHomomorphismFn bod
    | Apply(Fun(Equals,_,_),Record([(_,e1),(_,Apply(Fun(Op(qid,_),_,_), _, _))], _),_) -> Some qid
    | _ -> None

def Coalgebraic.implementOpsCoalgebraically(spc: Spec, qids: QualifiedIds, rules: List RuleSpec): Env Spec =
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
                           | existsSubTerm (fn st -> case st of
                                                       | Fun(Op(qid,_), _, _) -> qid = replace_op_qid
                                                       | _ -> false)
                               body
                         ->
                         primaryOpName info :: qids
                       | _ ->
                     if existsSubTerm (fn st -> case st of
                                                       | Fun(Op(qid,_), _, _) -> qid = replace_op_qid
                                                       | _ -> false)
                         tm
                       then primaryOpName info :: qids
                       else qids
               in
               let state_transform_qids = foldOpInfos findStateTransformOps [] spc.ops in
               let script = Steps[%Trace true,
                                  At(map Def (reverse state_transform_qids),
                                     Steps [mkSimplify(RLeibniz homo_fn_qid :: LeftToRight assert_qid :: rules)])]
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
    | IfThenElse(_, t1, t2, _) -> getConjoinedEqualities t1 ++ getConjoinedEqualities t2
    | Apply(Fun(And,_,_), Record([("1",t1),("2",t2)],_),_) -> getConjoinedEqualities t1 ++ getConjoinedEqualities t2
    | _ -> [t]

op findStoredOps(spc: Spec, state_qid: QualifiedId): QualifiedIds =
  let state_ty = mkBase(state_qid, []) in
  foldOpInfos (fn (info, stored_qids) ->
               let  (tvs, ty, tm) = unpackFirstTerm info.dfn in
               if ~(anyTerm? tm) then stored_qids
               else
               case getStateVarAndPostCondn(ty, state_ty, spc) of
                 | Some(state_var, deref?, post_condn) ->
                   removeDuplicates
                     (mapPartial (fn cj ->
                                    case cj of
                                      | Apply(Fun(Equals,_,_),Record([(_,lhs),_], _),_) ->
                                        (case lhs of
                                           | Apply(Fun(Op(qid,_), _, _), Var(v, _), _) | qid nin? stored_qids && equalVar?(v, state_var) ->
                                             let _ = if show qid = "WS" then writeLine(show(primaryOpName info)^" "^printType ty) else () in
                                             Some qid
                                           | _ -> None)
                                      | _ -> None)
                     (getConjoinedEqualities post_condn))
                   ++ stored_qids
                 | None -> stored_qids)
  
    [] spc.ops

op qualifiedIdToField(Qualified(_, id): QualifiedId): Id = id

op makeRecordFieldsFromQids(spc: Spec, qids: QualifiedIds): List(Id * MSType) =
  map (fn qid ->
         let Some info = findTheOp(spc, qid) in
         (qualifiedIdToField qid, range(spc, inferType(spc, info.dfn))))
    qids  

op findSourceVar(cjs: MSTerms, state_var: Var, stored_qids: QualifiedIds): Option Var

op makeDefForUpdatingCoType(post_condn: MSTerm, state_var: Var, deref?: Option Id,
                            spc: Spec, state_ty: MSType, stored_qids: QualifiedIds, field_pairs: List(Id * MSType))
     : MSTerm =
   let def makeDef(tm) =
         case tm of
           | IfThenElse(p, q, r, a) ->
             IfThenElse(p, makeDef q, makeDef r, a)
           | Apply(Fun(And,_,_), Record([("1",t1),("2",t2)],_),_) ->
             (let cjs = getConjuncts tm in
              case findSourceVar(cjs, state_var, stored_qids) of
                | Some src_var -> tm
                | None -> tm)
   in
   makeDef post_condn

op makeDefinitionsForUpdatingCoType
     (spc: Spec, state_ty: MSType, stored_qids: QualifiedIds, field_pairs: List(Id * MSType)): Spec =
  foldOpInfos (fn (info, spc) ->
                 let (tvs, ty, tm) = unpackFirstTerm info.dfn in
                 if ~(anyTerm? tm) then spc
                 else
                 (case getStateVarAndPostCondn(ty, state_ty, spc) of
                    | None -> spc
                    | Some(state_var, deref?, post_condn) ->
                      let _ = writeLine(show(primaryOpName info)^":\n"^printTerm post_condn) in
                      addRefinedDef(spc, info, makeDefForUpdatingCoType(post_condn, state_var, deref?,
                                                                        spc, state_ty, stored_qids, field_pairs))))
    spc spc.ops
                           


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
   print("stored_qids: "^anyToString (map show stored_qids));
   field_pairs <- return(makeRecordFieldsFromQids(new_spc, stored_qids));
   new_spc <- return(addTypeDef(new_spc, state_qid, Product(field_pairs, noPos)));
   new_spc <- return(makeDefinitionsForUpdatingCoType(new_spc, state_ty, stored_qids, field_pairs));
   return new_spc}

end-spec
