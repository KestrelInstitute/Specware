SpecNorm qualifying spec
  import /Languages/MetaSlang/Transformations/DefToAxiom
  import Coercions
  
  op  removeSubSorts: Spec \_rightarrow TypeCoercionTable \_rightarrow Spec
  def removeSubSorts spc coercions =
    %% Remove subsort definition for directly-implemented subsorts
    let spc = spc << {sorts = mapSortInfos
                                (fn info \_rightarrow
                                 let qid = primarySortName info in
                                 if exists (\_lambda tb \_rightarrow tb.subtype = qid) coercions
                                   then info << {dfn = And([],noPos)}
                                   else info)
                                spc.sorts}
    in                           
    let spc = spc << {elements
		       = foldr (fn (el,r) \_rightarrow
				case el of
				 | Op(qid as (Qualified(q,id)), def?) \_rightarrow
				   let Some info = AnnSpec.findTheOp(spc,qid) in
				   let srt = firstOpDefInnerSort info in
				   %let _ = toScreen (printSort srt) in
				   let subTypeFmla = opSubsortNoArityAxiom(spc, qid, srt) in
				   %let _ = toScreen (printTerm subTypeFmla) in
				   % ?? let liftedFmlas = removePatternTop(spc, subTypeFmla) in
				   (case simplify spc subTypeFmla of
				      | Fun(Bool true,_,_) \_rightarrow Cons(el,r)
				      | s_fm \_rightarrow
				        %let _ = toScreen (printTerm s_fm) in
					let axm = Property(Axiom, 
							   mkQualifiedId
							     (q, id^"_subtype_constr"), 
							   [], 
							   s_fm)
					in
					Cons(el,Cons(axm,r)))
				 | _ \_rightarrow Cons(el,r))
		           [] spc.elements}
    in
    let spc =
        mapSpec (fn t \_rightarrow
		   case t of
		    | Bind(bndr,bndVars,bod,a) \_rightarrow
		      let bndVarsPred = foldl (fn ((vn,srt), res) ->
                                               Utilities.mkAnd(srtPred(spc, srt, mkVar (vn,srt)),
                                                               res))
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
		    | _ \_rightarrow t,
		 id,
		 id)
	  spc
    in
    mapSpec (id,fn s \_rightarrow
		   case s of
		     | Subsort(supSrt,_,_) \_rightarrow supSrt
		     | _ \_rightarrow s,
             id)
      spc
endspec
