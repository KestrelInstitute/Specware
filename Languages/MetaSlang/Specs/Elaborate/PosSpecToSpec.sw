(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

PosSpecToSpec qualifying spec
 %%  convert pos terms to standard terms

 import  ../Environment
 import /Library/Legacy/DataStructures/NatMapSplay  % for metaTyVars
 import /Languages/MetaSlang/Transformations/NormalizeTypes

 op correctEqualityType (spc: Spec, eq_or_neq: MSFun, ty: MSType, eq_args: MSTerm, pos1: Position)
     : MSTerm =
    case (eq_args, unlinkType ty) of
     | (Record ([("1", e1), ("2", e2)], _), 
        Arrow (Product ([("1", elTy1), ("2", _)], _), _, pos2)) -> 
        let
          def subtype? (ty1', ty2') = 
            let ty1' = unfoldBase(spc, ty1') in
            let ty2' = unfoldBase(spc, ty2') in
            % let _ = writeLine("subtype?("^printType ty1'^", "^printType ty2'^")") in
            let result = equalType?(ty1', ty2')
                       || (case ty1'
                            of Subtype (s1', _, _) -> subtype? (s1', ty2')
                             | _ -> false)
            in
            % let _ = writeLine("  = "^show result) in
            result
          def commonAnc (s1', s2') =
            % let _ = writeLine("commonAnc("^printType s1'^", "^printType s2'^")") in
            let result = if subtype? (s1', s2') then s2' else
                         if subtype? (s2', s1') then s1' else
                         case unfoldBase(spc, s1')
                           of Subtype (ss1', _, _) -> commonAnc (ss1', s2')
                            | _ -> s2'                        % Shouldn't happen
            in
            % let _ = writeLine("  = "^printType result) in
            result
        in
        let (s1', s2') = (inferType (spc,e1), inferType (spc,e2)) in
        let elTy = if subtype? (s1', elTy1) && subtype? (s2', elTy1)
                     then elTy1 else commonAnc (s1', s2') in
        % let _ = writeLine("correctEqualityType: ="^printTerm eq_args^": "^printType elTy) in
        let fn_tm = Fun (eq_or_neq, Arrow (Product([("1", elTy), ("2", elTy)], pos2), boolType, pos2), pos1) in
        Apply(fn_tm, eq_args, pos1)
      | _ -> Apply(Fun(eq_or_neq, ty, pos1), eq_args, pos1)

 op correctMapType(m: MSTerm, l: MSTerm, ty: MSType, spc: Spec, fx: Fixity, a: Position)
     : MSTerm =
   let m_ty = inferType(spc, m) in
   let map_ty =
       case arrowOpt(spc, m_ty) of
       | None -> ty
       | Some(dom, rng) ->
         Arrow(m_ty, Arrow(Base(Qualified("List", "List"), [dom], a),
                           Base(Qualified("List", "List"), [rng], a), a),
               a)
   in
   let result =
   Apply(Apply(Fun(Op(Qualified("List","map"),fx),map_ty,a), m, a),
         l, a)
   in
   % let _ = writeLine(printTerm result) in
   result

 op correctPolyTypes?: Bool = false
 op correctEqualityTypes?: Bool = true

 op convertPTerm (spc: Spec) (term: MSTerm): MSTerm =
   % let _ = writeLine("cvt: "^printTerm term^"\n"^anyToString term) in
   case term of
     | ApplyN([Fun(eq_or_neq,ty,_),t2],pos) | correctEqualityTypes? && (eq_or_neq = Equals || eq_or_neq = NotEquals) ->
       correctEqualityType(spc, eq_or_neq, ty, t2, pos)
     | ApplyN([Apply(Fun(Op(Qualified("List","map"),fx),ty,a), m, _), l], _) | correctPolyTypes? ->
       correctMapType(m, l, ty, spc, fx, a)
     | ApplyN([t1,t2],pos) -> Apply(t1,t2,pos)
     | ApplyN (t1::t2::terms,pos) -> 
       convertPTerm spc (ApplyN([t1,ApplyN(Cons(t2,terms),pos)],pos))
     | Fun (f,s,pos) -> Fun(convertPFun f,s,pos)
     | _ -> term

op convertPFun (f: MSFun): MSFun = 
   case f of
     | PQuotient qid -> Quotient qid
     | PChoose   qid -> Choose   qid
     | OneName(n,fxty)  -> Op(Qualified(UnQualified,n), fxty)
     | TwoNames(qn,n,fxty) -> Op(Qualified(qn,n), fxty)
     | _ -> f

 op  convertPosSpecToSpec: Spec -> Spec
 def convertPosSpecToSpec spc =
   let context = initializeMetaTyVars() in
   let
     def convertPType ty =
           case ty of
	     | MetaTyVar(tv,pos) -> 
	       let {name,uniqueId,link} = ! tv in
	       (case link
		  of None -> TyVar (findTyVar(context,uniqueId),pos)
		   | Some sty -> convertPType sty)
             %% This is to clean-up refine def when there is duplication of subtype predicates
             %% that cannot be detected until after elaboration
             | Subtype(sty, Lambda ([(pat, c, condn as Apply(Fun(And,_,_),_,_))], a1), a2) ->
               let conjs = getConjuncts condn in
               Subtype(sty, Lambda ([(pat, c, mkSimpConj conjs)], a1), a2)
	     | _ -> ty
   in
   let tsp = (convertPTerm spc, convertPType, fn x -> x) in

   %% let spc = mapSpec tsp spc -- would be correct but unnecessarily maps non-locals
   
   let spc = spc << {ops = if ~(hasLocalOp? spc) then 
                             spc.ops
                           else
                             % mapOpInfosUnqualified causes some specs to fail to elaborate properly
                             mapOpInfos (fn info ->
                                           if someOpAliasIsLocal? (info.names, spc) then
                                             info << {dfn = mapTerm tsp info.dfn}
                                           else 
                                             info)
                                        spc.ops,

                     types = if ~(hasLocalType? spc) then 
                              spc.types
                             else
                              mapTypeInfos (fn info ->
                                            if someTypeAliasIsLocal? (info.names, spc) then
                                              info << {dfn = mapType tsp info.dfn}
                                            else 
                                              info)
                                           spc.types,

                     elements =  map (fn el ->
                                        case el of
                                          | Property (pt, qid, tvs, term, a) -> 
                                            Property(pt, qid, tvs, 
                                                     mapTerm tsp term, a)
                                          | _ -> el)
                                      spc.elements
                    }
  in
  normalizeNewTypes(spc, false)

end-spec

