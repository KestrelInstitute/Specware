PosSpecToSpec qualifying spec
 %%  convert pos terms to standard terms

 import  ../Environment
 import /Library/Legacy/DataStructures/NatMapSplay  % for metaTyVars

 def correctEqualityType (spc: Spec, eq_or_neq: Fun, ty: Sort, eq_args: MS.Term, pos1: Position)
     : MS.Term =
    case (eq_args, unlinkSort ty) of
     | (Record ([("1", e1), ("2", e2)], _), 
        Arrow (Product ([("1", elTy1), ("2", _)], _), _, pos2)) -> 
        let
          def subsort? (ty1', ty2') = 
            let ty1' = unfoldBase(spc, ty1') in
            let ty2' = unfoldBase(spc, ty2') in
            %let _ = writeLine("subsort?("^printSort ty1'^", "^printSort ty2'^")") in
            let result = equalType?(ty1', ty2')
                       || (case ty1'
                            of Subsort (s1', _, _) -> subsort? (s1', ty2')
                             | _ -> false)
            in
            %let _ = writeLine("  = "^toString result) in
            result
          def commonAnc (s1', s2') =
            %let _ = writeLine("commonAnc("^printSort s1'^", "^printSort s2'^")") in
            let result = if subsort? (s1', s2') then s2' else
                         if subsort? (s2', s1') then s1' else
                         case s1'
                           of Subsort (ss1', _, _) -> commonAnc (ss1', s2')
                            | _ -> s2'                        % Shouldn't happen
            in
            %let _ = writeLine("  = "^printSort result) in
            result
        in
        let (s1', s2') = (inferType (spc,e1), inferType (spc,e2)) in
        let elTy = if subsort? (s1', elTy1) && subsort? (s2', elTy1)
                     then elTy1 else commonAnc (s1', s2') in
        %let _ = writeLine("correctEqualityType: ="^printTerm eq_args^": "^printSort elTy) in
        let fn_tm = Fun (eq_or_neq, Arrow (Product([("1", elTy), ("2", elTy)], pos2), boolSort, pos2), pos1) in
        Apply(fn_tm, eq_args, pos1)
      | _ -> Apply(Fun(eq_or_neq, ty, pos1), eq_args, pos1)

 op  convertPosSpecToSpec: Spec -> Spec
 def convertPosSpecToSpec spc =
   let context = initializeMetaTyVars() in
   let
     def convertPTerm term =
           case term of
             | ApplyN([Fun(eq_or_neq,ty,_),t2],pos) | eq_or_neq = Equals || eq_or_neq = NotEquals ->
               correctEqualityType(spc, eq_or_neq, ty, t2, pos)
	     | ApplyN([t1,t2],pos) -> Apply(t1,t2,pos)
	     | ApplyN (t1::t2::terms,pos) -> 
	       convertPTerm (ApplyN([t1,ApplyN(cons(t2,terms),pos)],pos))
	     | Fun (f,s,pos) -> Fun(convertPFun f,s,pos)
	     | _ -> term
     def convertPSort ty =
           case ty of
	     | MetaTyVar(tv,pos) -> 
	       let {name,uniqueId,link} = ! tv in
	       (case link
		  of None -> TyVar (findTyVar(context,uniqueId),pos)
		   | Some sty -> convertPSort sty)
	     | _ -> ty
     def convertPFun (f) = 
           case f of
	     | PQuotient qid -> Quotient qid
             | PChoose   qid -> Choose   qid
             | OneName(n,fxty)  -> Op(Qualified(UnQualified,n), fxty)
             | TwoNames(qn,n,fxty) -> Op(Qualified(qn,n), fxty)
             | _ -> f
   in
%% mapSpec is correct but unnecessarily maps non-locals
%   mapSpec (convertPTerm, convertPSort, fn x -> x)
%     spc
 
  let {sorts, ops, elements, qualifier} = spc in
%  let {imports = _, localOps, localSorts, localProperties} = importInfo in
  let tsp = (convertPTerm, convertPSort, fn x -> x) in
  spc << { ops = if ~(hasLocalOp? spc) then 
                   ops
		 else
                   mapOpInfosUnqualified (fn info ->
					  if someOpAliasIsLocal? (info.names, spc) then
					    info << {dfn = mapTerm tsp info.dfn}
					  else 
					    info)
			      ops,

          sorts = if ~(hasLocalSort? spc) then 
                   sorts
                  else
		   mapSortInfos (fn info ->
				 if someSortAliasIsLocal? (info.names, spc) then
				   info << {dfn = mapSort tsp info.dfn}
				 else 
				   info)
				sorts,

          elements =  map (fn el ->
                             case el of
                               | Property (pt, qid, tvs, term, a) -> 
                                 Property(pt, qid, tvs, 
                                          mapTerm tsp term, a)
                               | _ -> el)
                           elements
         }


 op  convertPosTermToTerm : MS.Term -> MS.Term
 def convertPosTermToTerm tm =
   let context = initializeMetaTyVars() in
   let
     def convertPTerm term =
           case term of
	     | ApplyN([t1,t2],pos) -> Apply(t1,t2,pos)
	     | ApplyN (t1::t2::terms,pos) -> 
	       convertPTerm (ApplyN([t1,ApplyN(cons(t2,terms),pos)],pos))
	     | Fun (f,s,pos) -> Fun(convertPFun f,s,pos)
	     | _ -> term
     def convertPSort ty =
           case ty of
	     | MetaTyVar(tv,pos) -> 
	       let {name,uniqueId,link} = ! tv in
	       (case link
		  of None -> TyVar (findTyVar(context,uniqueId),pos)
		   | Some sty -> convertPSort sty)
	     | _ -> ty
     def convertPFun (f) = 
           case f of
	     | PQuotient qid -> Quotient qid
             | PChoose   qid -> Choose   qid
             | OneName(n,fxty)  -> Op(Qualified(UnQualified,n), fxty)
             | TwoNames(qn,n,fxty) -> Op(Qualified(qn,n), fxty)
             | _ -> f
   in
   let tsp = (convertPTerm, convertPSort, fn x -> x) in
   mapTerm tsp tm

endspec

