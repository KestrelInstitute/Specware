SpecNorm qualifying spec
  import /Languages/MetaSlang/Transformations/DefToAxiom
  import Coercions

  %% Polymorphic ops have versions that have a predicate for each polymorphic variable
  type PolyOpTable = AQualifierMap(QualifiedId * List TyVar)

  op mkTruePred(ty: Sort): MS.Term = mkLambda(mkWildPat ty, trueTerm)

  op relativizeTerm (spc: Spec, tb: PolyOpTable) (t: MS.Term): MS.Term =
    case t of
      | Fun(Op(qid as Qualified(q,id),fix?),ty,a) ->
        (case findAQualifierMap(tb,q,id) of
           | None -> t
           | Some(r_qid,used_tvs) ->
         case AnnSpec.findTheOp(spc, qid) of
           | None -> t
           | Some opinfo ->
         let (tvs,ty1,defn) = unpackFirstOpDef opinfo in
         case typeMatch(ty1,ty,spc,false) of
           | None -> t
           | Some tvsubst ->
         %let _ = writeLine("\nRelativizing ref to: "^printQualifiedId qid^": "^printSort ty) in
         let tvsubst = filter (fn (tv,_) -> member(tv, used_tvs)) tvsubst in
         %let _ = writeLine(anyToString tvsubst) in
         if exists (fn (_,s_ty) -> subtype?(spc,s_ty)) tvsubst
           then let predArgs = map (fn tv -> let Some(_,s_ty) = find (fn (tvi,_) -> tv = tvi) tvsubst in
                                             case subtypeComps(spc,s_ty) of
                                               | Some(_,pred) -> pred
                                               | None -> mkTruePred s_ty)
                                 used_tvs
                in
                %let _ = app (fn pred -> writeLine(printTerm pred)) predArgs in
                let predTypes = map (fn pred -> inferType(spc, pred)) predArgs in
                mkAppl(Fun(Op(r_qid,Nonfix), mkArrow(mkProduct predTypes, ty), a),
                       predArgs)
           else t)
      | Bind(bndr,bndVars,bod,a) \_rightarrow
        let bndVarsPred = foldl (fn ((vn,srt), res) ->
                                 let pred_tm = srtPred(spc, srt, mkVar (vn,srt)) in
                                 let pred_tm = mapTerm (relativizeTerm (spc, tb),id,id) pred_tm in
                                 Utilities.mkAnd(pred_tm, res))
                            (mkTrue()) bndVars
        in
        %let _ = toScreen (printTerm bndVarsPred) in
        let new_bod = case bndr of
                        | Forall -> Utilities.mkSimpImplies(bndVarsPred, bod)
                        | Exists -> Utilities.mkAnd(bndVarsPred, bod)
                        | Exists1 -> Utilities.mkAnd(bndVarsPred, bod)
        in
        Bind(bndr,bndVars,new_bod,a)
      | The(theVar as (vn,srt),bod,a) \_rightarrow
        let theVarPred = srtPred(spc, srt, mkVar theVar) in
        let new_bod = Utilities.mkAnd(theVarPred, bod) in
        The((vn,srt),new_bod,a)
      | _ \_rightarrow t

  op maybeRelativize?(t: MS.Term, tb: PolyOpTable): Boolean =
    existsSubTerm (fn tm ->
                     case tm of
                       | Fun(Op(Qualified(q,id),_),_,_) -> some?(findAQualifierMap(tb,q,id))
                       | Bind _ -> true
                       | The _ -> true
                       | _ -> false)
      t

  op substTyVarsWithSubtypes(tv_map: List(TyVar * MS.Term), tm: MS.Term): MS.Term =
    instantiateTyVarsInTerm(tm, map (fn (tv,v) -> (tv, Subsort(mkTyVar tv, v, noPos))) tv_map)
    
  op tryRelativizeTerm(tvs: TyVars, tm: MS.Term, tb: PolyOpTable, spc: Spec): List(Id * MS.Term) =
    if tvs = [] || ~(maybeRelativize?(tm, tb))then []
    else
    let tv_map = map (fn tv -> (tv, mkVar("P__"^tv, mkArrow(mkTyVar tv, boolSort)))) tvs in
    % let _ = writeLine("tv_map: "^anyToString tv_map) in
    let st_tm = substTyVarsWithSubtypes(tv_map,tm) in
    let rel_tm = mapTerm(relativizeTerm (spc,tb),id,id) st_tm in
    % let _ = writeLine("rel_tm: "^printTerm rel_tm) in
    if equalTerm?(rel_tm, st_tm) then []
      else
      let fvs = freeVars rel_tm in
      let opt_tv_map = filter (fn (_,Var(v,_)) -> inVars?(v, fvs)) tv_map in
      % let _ = writeLine("opt_tv_map: "^anyToString opt_tv_map) in
      opt_tv_map

  op addRelativizedOps(spc: Spec): Spec * PolyOpTable =
    let def relativizeElts(elts, top?, op_map, tbl) =
          foldl (fn (el, (new_elts, op_map, tbl)) ->
                 case el of
                   | Import(s_tm, i_sp, im_elts, a) ->
                     let (im_elts, op_map, tbl) = relativizeElts(im_elts, false, op_map, tbl) in
                     (new_elts ++ [Import(s_tm, i_sp, im_elts, a)], op_map, tbl)
                   | Op(qid as Qualified(q,id), _, a) ->
                     % let _ = writeLine("Trying "^printQualifiedId qid) in
                     (case AnnSpec.findTheOp(spc,qid) of
                        | Some opinfo ->
                          let (tvs, ty, dfn) = unpackTerm opinfo.dfn in
                          (case tryRelativizeTerm(tvs, dfn, tbl, spc) of
                             | [] -> (new_elts ++ [el], op_map, tbl)
                             | tv_map ->
                               let new_id = id ^ "__stp" in
                               let new_tbl = insertAQualifierMap(tbl,q,id,
                                                                 (Qualified(q,new_id),
                                                                  map (fn (tv,_) -> tv) tv_map))
                               in
                               let rel_dfn = substTyVarsWithSubtypes (tv_map, dfn) in
                               let rel_tm = mkLambda(mkTuplePat(map (fn (_,Var v) -> VarPat v) tv_map), rel_dfn) in
                               let new_ty = mkArrow(mkProduct(map (fn (_,Var((_,ty),_)) -> ty) tv_map), ty) in
                               let new_opinfo = {names = [Qualified(q,new_id)],
                                                 dfn = Pi(tvs, SortedTerm(rel_tm, new_ty, noPos), noPos),
                                                 fixity = Nonfix,
                                                 fullyQualified? = opinfo.fullyQualified?}
                               in
                               let new_op_map = insertAQualifierMap(op_map,q,new_id,new_opinfo) in
                               let new_el = Op(Qualified(q,new_id), true, a) in
                               (new_elts ++ [new_el, el], new_op_map, new_tbl))
                        | _ -> (new_elts ++ [el], op_map, tbl))
                   | Property(knd, qid as Qualified(q,id), tvs, bod, a) | tvs ~= [] & knd ~= Conjecture ->
                     % let _ = writeLine("Trying "^printQualifiedId qid) in
                     (case tryRelativizeTerm(tvs, bod, tbl, spc) of
                        | [] -> (new_elts ++ [el], op_map, tbl)
                        | tv_map ->
                          let new_id = id ^ "__stp" in
                          let rel_bod = substTyVarsWithSubtypes (tv_map, bod) in
                          let new_bod = Bind(Forall, map (fn (_,Var(v,_)) -> v) tv_map, rel_bod, a) in
                          let new_prop = Property(knd, Qualified(q,new_id), tvs, new_bod, a)in
                          (new_elts ++ [new_prop, el], op_map, tbl))
                   | _ -> (new_elts ++ [el], op_map, tbl))
             ([], op_map, tbl)
             elts
    in
    let (new_elts, new_op_map, tbl) = relativizeElts(spc.elements, true, spc.ops, emptyAQualifierMap) in
    (spc << {elements = new_elts, ops = new_op_map},
     tbl)

  op  removeSubSorts: Spec \_rightarrow TypeCoercionTable \_rightarrow Spec
  def removeSubSorts spc coercions =
    %% Remove subsort definition for directly-implemented subsorts
    let spc = spc << {sorts = mapSortInfos
                                (fn info \_rightarrow
                                 let qid = primarySortName info in
                                 if (exists (\_lambda tb \_rightarrow tb.subtype = qid) coercions)
                                   && embed? Subsort (firstSortDef info)
                                   then info << {dfn = And([],noPos)}
                                   else info)
                                spc.sorts}
    in
    %% Add subtype assertions from op declarations
    let spc = spc << {elements
		       = foldr (fn (el,r) \_rightarrow
				case el of
				 | Op(qid as (Qualified(q,id)), def?, a) \_rightarrow
				   let Some info = AnnSpec.findTheOp(spc,qid) in
				   let srt = firstOpDefInnerSort info in
				   %let _ = toScreen (printSort srt) in
				   let subTypeFmla = opSubsortNoArityAxiom(spc, qid, srt) in
				   %let _ = writeLine (printTerm subTypeFmla) in
				   % ?? let liftedFmlas = removePatternTop(spc, subTypeFmla) in
				   (case simplify spc subTypeFmla of
				      | Fun(Bool true,_,_) \_rightarrow Cons(el,r)
				      | s_fm \_rightarrow
				        %let _ = writeLine (" --> "^printTerm s_fm) in
					let axm = Property(Axiom, 
							   mkQualifiedId
							     (q, id^"_subtype_constr"), 
							   [], 
							   s_fm, a)
					in
					Cons(el,Cons(axm,r)))
				 | _ \_rightarrow Cons(el,r))
		           [] spc.elements}
    in
    let (spc, tbl) = addRelativizedOps(spc) in
    %let _ = writeLine(anyToString tbl) in
    %let _ = writeLine(printSpec spc) in
    let spc = mapSpec (relativizeTerm (spc, tbl), id, id) spc in
    %let _ = writeLine(printSpec spc) in
    mapSpec (id,fn s \_rightarrow
		   case s of
		     | Subsort(supSrt,_,_) \_rightarrow supSrt
		     | _ \_rightarrow s,
             id)
      spc
endspec
