(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%%% Adds coercion functions between subtype and supertype so they can have
%%% different implementations

Coercions qualifying
spec 
  import /Languages/MetaSlang/Specs/Environment
  import /Languages/MetaSlang/Specs/Proof

  op handleOverloading?: Bool = false

  type TypeCoercionInfo = {subtype: QualifiedId,
			   supertype: MSType,
			   coerceToSuper: MSTerm,
			   coerceToSub: MSTerm,
                           overloadedOps: List String}
  type TypeCoercionTable = List TypeCoercionInfo

  op lifterFuns: List(QualifiedId * QualifiedId) =
    [(Qualified("List", "List"), Qualified("List", "map")),
     (Qualified("Option", "Option"), Qualified("Option", "mapOption")),
     (Qualified("Set", "Set"), Qualified("Set", "map")),
     (Qualified("Stream", "Stream"), Qualified("Stream", "map")),
     (Qualified("Seq", "Seq"), Qualified("Seq", "map"))]

 op unfoldBeforeCoProductOrArrow(sp: Spec, srt: MSType): MSType =
   case srt of
     | Base (qid, srts, a) ->
      (case findTheType (sp, qid) of
	 | None -> srt
	 | Some info ->
	   if definedTypeInfo? info then
	     let (tvs, fsrt) = unpackFirstTypeDef info in
	     case fsrt of
	       | CoProduct _ -> srt
               | Arrow _ -> srt
	       | _ ->
                 if length tvs ~= length srts
                   then % let _ = writeLine("Ill-formed type: "^printType srt) in
                        srt
                 else
                 let ssrt = substType (zip (tvs, srts), fsrt) in
		 unfoldBeforeCoProduct (sp, ssrt)
	   else
	     srt)
    | _ -> srt
    
  op needsCoercion?(ctxt_ty: MSType, gen_ty: MSType, coercions: TypeCoercionTable, tm: MSTerm, spc: Spec)
     : Option(Bool * TypeCoercionInfo * List(QualifiedId * QualifiedId)) =
    let result =
          if embed? TyVar ctxt_ty || embed? TyVar gen_ty
            then   %% Shouldn't happen, means something has not unfolded correctly
              None
          else
          case findLeftmost (fn tb -> subtypeOf?(gen_ty, tb.subtype, spc)
                               && ~(subtypeOf?(ctxt_ty, tb.subtype, spc))) coercions of
            | Some tb -> Some(true, tb, [])
            | None ->
          case findLeftmost (fn tb -> subtypeOf?(ctxt_ty, tb.subtype, spc)
                               && ~(subtypeOf?(gen_ty, tb.subtype, spc))) coercions of
            | Some tb -> Some(false, tb, [])
            | None ->
          case unfoldBeforeCoProductOrArrow(spc, ctxt_ty) of
            | Base(ctxt_qid, [ctxt_ty_a], _) ->
              (case unfoldBeforeCoProductOrArrow(spc, gen_ty) of
                 | Base(gen_qid, [gen_ty_a], _) | ctxt_qid = gen_qid ->
                   (case needsCoercion?(ctxt_ty_a, gen_ty_a, coercions, tm, spc) of
                    | None -> None
                    | Some(toSuper?, tb, lifters) ->
                    case findLeftmost(fn (qid, _) -> qid = ctxt_qid) lifterFuns of
                      | Some(lifter) -> Some(toSuper?, tb, lifter :: lifters)
                      | None -> let Qualified(q, _) = ctxt_qid in
                                let norm_qid = Qualified(q, "map") in
                                (warn("Missing coercion map function for type "
                                      ^show ctxt_qid^", guessing "^show norm_qid);
                                 Some(toSuper?, tb, (ctxt_qid, norm_qid) :: lifters)))
                 | _ -> None)
            | _ -> None
    in
    % let _ = if some? result then writeLine(printTerm tm^":\n"^printType gen_ty^" -~-> "^printType ctxt_ty) else () in
    result

  op opaqueTypeQId?(coercions: TypeCoercionTable) (qid: QualifiedId): Bool =
    exists? (fn tb -> qid = tb.subtype) coercions

  op opaqueType?(ty: MSType, coercions: TypeCoercionTable, spc: Spec): Bool =
    exists? (fn tb -> subtypeOf?(ty, tb.subtype, spc)) coercions

  op idFn?(t: MSTerm): Bool =
    case t of
      | Fun(Op(Qualified(_, "id"), _), _, _) -> true
      | _ -> false

  op fixType(coerce_fn: MSTerm, sup_ty: MSType, to_super?, spc: Spec): MSTerm =
    case coerce_fn of
      | Fun(f, f_ty, a) ->
        (case arrowOpt(spc, f_ty) of
           | Some(dom, rng) ->
             %let _ = writeLine("fixType "^show to_super?^": "^printType sup_ty^"\n"^printType f_ty) in
             let tvs = freeTyVars dom in
             let (dom, rng) =
                 if tvs = []
                   then (dom, rng)
                   else
                     case typeMatch(if to_super? then dom else rng, sup_ty, spc, true, true) of
                       | Some(tv_sbst as _ :: _) -> 
                         (instantiateTyVarsInType(dom, tv_sbst), instantiateTyVarsInType(rng, tv_sbst))
                       | _ -> (dom, rng)
             in
             % let _ = if equalType?(f_ty, mkArrow(dom, rng)) then ()
             %     else writeLine("fixType "^show to_super?^": "^printType sup_ty^"\n"^printType f_ty^"\n"
             %                      ^printTermWithTypes(Fun(f, mkArrow(dom, rng), a))) in
             Fun(f, mkArrow(dom, rng), a) 
           | None -> coerce_fn)
      | _ -> coerce_fn
        

  op mkLiftedFun(f: MSTerm, lifterFns: List(QualifiedId * QualifiedId), spc: Spec): MSTerm =
   case lifterFns of
     | [] -> f
     | (lift_ty_qid, lifter_fn) :: r_lifterFns ->
   let rf = mkLiftedFun(f, r_lifterFns, spc) in
   let f_ty = inferType(spc, f) in
   case arrowOpt(spc, f_ty) of
     | Some(dom, rng) -> mkApply(mkOp(lifter_fn,
                                      mkArrow(f_ty, mkArrow(mkBase(lift_ty_qid, [dom]),
                                                            mkBase(lift_ty_qid, [rng])))),
                                 f)
     | None -> fail("mkLiftedFun: "^printTerm f^" not a function type.")

  op patTermVarsForProduct(fields: List(Id * MSType)): MSPattern * MSTerm =
    let (pats, tms, _) = foldr (fn ((fld_i, p_ty), (pats, tms, i)) ->
                                let v = ("x_"^show i, p_ty) in
                                (Cons((fld_i, mkVarPat v), pats),
                                 Cons((fld_i, mkVar    v),  tms),
                                 i-1))
                         ([], [], length fields)
                         fields
    in
    (mkRecordPat pats, mkRecord tms)

  op addCoercionsToTerm_helper (coercions: TypeCoercionTable) (spc: Spec) (tm: MSTerm, ty: MSType) : MSTerm =
    let
      def mapTerm (tm,ty) = addCoercionsToTerm_helper coercions spc (tm,ty)
      def mapSubTerms(tm, ty) =
        % let _ = writeLine("mst: "^printTerm tm^" -> " ^ printType ty) in
	case tm of
	  | Apply (t1, t2, a) ->
	    let fn_ty = inferType(spc, t1) in
            (case findLeftmost (fn tb -> subtypeOf?(fn_ty, tb.subtype, spc)) coercions of
               | Some tb | tb.subtype = Qualified("Set", "Set")->
                 (case subtypeOf(fn_ty, tb.subtype, spc) of
                    | Some(Base(_, [p], _)) ->
                      let t1 = if embed? Fun t1 then t1 else mapTerm(t1, fn_ty) in
                      let t2 = mapTerm(t2, p) in
                      Apply(mkInfixOp(Qualified("Set", "in?"), Infix(Left, 20),
                                      mkArrow(mkProduct[p, fn_ty], boolType)),
                            mkTuple[t2, t1],
                            a))
               | _ ->
                 let dom = domain (spc, fn_ty) in
                 Apply (if embed? Fun t1 then t1
                          else mapTerm(t1, mkArrow(dom, ty)),
                        mapTerm(t2, dom), a))
	  | Record (row, a) ->
	    let srts = map (fn (_, x) -> x) (product (spc, ty)) in
	    Record(map (fn ((idi, tmi), tyi) -> (idi, mapTerm(tmi, tyi))) (zip(row, srts)), a)
	  | Bind (bnd, vars, trm, a) ->
	    Bind (bnd, vars, mapTerm(trm, ty), a)
	  | The (var, trm, a) ->
	    The (var, mapTerm(trm, boolType), a)
	  | Let (decls, bdy, a) ->
	    %Let (map (fn (pat, trm) -> (pat, mapTerm(trm, ty)))   % Assumes no coercions in pattern
	    Let (map (fn (pat, trm) -> (pat, mapTerm(trm, patternType pat)))   % Assumes no coercions in pattern
		   decls,
		 mapTerm(bdy, ty), a)
	  | LetRec (decls, bdy, a) ->
	    LetRec (map (fn ((id, srt), trm) -> ((id, srt), mapTerm(trm, srt))) decls,
		    mapTerm(bdy, ty), a)
	  | Lambda (match, a) ->
	    Lambda (map (fn (pat, condn, trm) ->
			 (pat, mapTerm(condn, boolType), mapTerm(trm, range(spc, ty))))
			 match,
		    a)
	  | IfThenElse (t1, t2, t3, a) ->
	    IfThenElse (mapTerm(t1, boolType), mapTerm(t2, ty), mapTerm(t3, ty), a)
	  | Seq (terms, a) ->
            let pre_trms = butLast terms in
            let lst_trm  =    last terms in 
	    Seq (map (fn trm -> mapTerm(trm, mkProduct [])) pre_trms
                   ++ [mapTerm(lst_trm, ty)], a)
	  | TypedTerm (trm, srt, a) ->
	    TypedTerm (mapTerm(trm, srt), srt, a)
	  | _ -> tm

      def coerceToSuper(tm, tb, lifters, sup_ty) =
        case tm of
          | Apply(f, x, _) | f = tb.coerceToSub && lifters = [] ->
            x
          | Let(m, b, a) -> Let(m, coerceToSuper(b, tb, lifters, sup_ty), a)
          | _ ->
            if idFn? tb.coerceToSuper then tm
              else let coerce_fn = fixType(tb.coerceToSuper, sup_ty, true, spc) in
                   let coerced_term = mkApply(mkLiftedFun(coerce_fn, lifters, spc), tm) in
                   % let _ = writeLine("coerced: "^printTerm coerced_term) in
                   coerced_term
      def coerceToSub(tm, tb, lifters, sup_ty) =
        case tm of
          | Apply(f, x, _) | f = tb.coerceToSuper && lifters = [] ->
            x
          | Let(m, b, a) -> Let(m, coerceToSub(b, tb, lifters, sup_ty), a)
          | _ ->
            if idFn? tb.coerceToSub then tm
              else let coerce_fn = fixType(tb.coerceToSub, sup_ty, false, spc) in
                   let coerced_term = mkApply(mkLiftedFun(coerce_fn, lifters, spc), tm) in
                   % let _ = writeLine("coerced: "^printTerm coerced_term) in
                   coerced_term
    in
    let rm_ty = inferType(spc, tm) in
    let delayCoercion? =
      case tm of
        | Lambda _ ->
          (case rangeOpt(spc, rm_ty) of   % Don't delay set
             | Some r_ty | equalType?(r_ty, boolType) -> false
             | _ -> false)
        | Let _ -> true
        | Apply(Lambda _, _, _) -> true
        | LetRec _ -> true
        | IfThenElse _ -> true
        | Record _ -> true
        | _ -> false
    in
    let n_tm = mapSubTerms(tm, if delayCoercion? || embed? Lambda tm then ty else rm_ty) in
    if delayCoercion? || (handleOverloading? && overloadedTerm? n_tm) then n_tm
    else
      % let _ = writeLine(printTerm tm^": "^printType rm_ty ^"\n--> " ^ printType ty^"\n") in
      case needsCoercion?(ty, rm_ty, coercions, n_tm, spc) of
        | Some(toSuper?, tb, lifters) ->
          (case n_tm of
             | Fun(Nat i, _, a) | tb.subtype = Qualified("Nat", "Nat") -> Fun(Nat i, intType, a)
             | _ -> if toSuper? then coerceToSuper(n_tm, tb, lifters, ty)
                    else coerceToSub(n_tm, tb, lifters, ty))
        | None ->
          if simpleTerm n_tm then         % Var or Op
            case (arrowOpt(spc, ty), arrowOpt(spc, rm_ty)) of
              | (Some(dom, rng), Some(rm_dom, rm_rng))
              | ~(opaqueType?(ty, coercions, spc))
                && (some?(needsCoercion?(dom, rm_dom, coercions, n_tm, spc))
                    || some?(needsCoercion?(rng, rm_rng, coercions, n_tm, spc))) ->
                (case productOpt(spc, dom) of
                   | Some fields ->
                     let (v_pat, v_tm) = patTermVarsForProduct fields in
                     mkLambda(v_pat, mapTerm(mkApply(n_tm, v_tm), rng))
                   | None ->
                     mkLambda(mkVarPat("xz", dom), mapTerm(mkApply(n_tm, mkVar("xz", dom)), rng)))
              | _ ->
                case (productOpt(spc, ty), productOpt(spc, rm_ty)) of
                  | (Some fields, Some rm_fields)
                  | exists? (fn ((_, p_ty), (_, rm_p_ty)) ->
                               some?(needsCoercion?(p_ty, rm_p_ty, coercions, n_tm, spc)))
                    (if length fields = length rm_fields
                       then zip(fields, rm_fields)
                     else let _ = writeLine("ac zip error: "^printTerm n_tm^": "^printType rm_ty^"\n"^printType ty) in
                       []) ->
                    let (v_pat, v_tm) = patTermVarsForProduct rm_fields in
                    mkLet([(v_pat, n_tm)], v_tm)
                  %% !! Need more general cases as well
                  | _ -> n_tm
          else n_tm

  op addCoercionsToType_helper (coercions: TypeCoercionTable) (spc: Spec) (ty: MSType) : MSType =
    case ty of
      | Subtype(s_ty, pred, a) ->
        Subtype(s_ty,
                addCoercionsToTerm_helper coercions spc
                  (pred, mkArrow(s_ty, boolType)),
                a)
      | _ -> ty

  op addCoercionsToPattern_helper (coercions: TypeCoercionTable) (spc: Spec) (pat: MSPattern) : MSPattern =
    case pat of
      | RestrictedPat(pat, pred, a) ->
        RestrictedPat(pat,
                      addCoercionsToTerm_helper coercions spc
                        (pred, inferType(spc, pred)),
                      a)
      | _ -> pat


  % Add the given coercions to a term of a given type
  op addCoercionsToTerm (coercions: TypeCoercionTable) (spc: Spec) (tm: MSTerm, ty: MSType) : MSTerm * MSType =
    let def mapType ty =
      addCoercionsToType_helper coercions spc ty
    in
    let def mapPattern pat =
      addCoercionsToPattern_helper coercions spc pat
    in
    let tm1 = if anyTerm? tm then tm else MetaSlang.mapTerm(id, mapType, mapPattern) tm in
    let new_ty = MetaSlang.mapType(id, mapType, id) ty in
    if anyTerm? tm then (tm, ty) else
      (addCoercionsToTerm_helper coercions spc (tm1, new_ty), new_ty)


  % Add the given coercions to a type
  op addCoercionsToType (coercions: TypeCoercionTable) (spc: Spec) (ty: MSType) : MSType =
    mapType (id, addCoercionsToType_helper coercions spc, id) ty


  % Add the given coercions to a Spec
  op  addCoercions (coercions: TypeCoercionTable) (spc: Spec): Spec =
    let def mapTermTop (opinfo, refine_num) =
          let trps = unpackTypedTerms (opinfo.dfn) in
          let (tvs, ty, tm) = nthRefinement(trps, refine_num) in
          % let _ = writeLine("addCoercions\nfull:\n"^printTerm info.dfn^"\nunpack:\n"^printTerm full_term^"\nref:\n"^printTerm tm) in
          let (result, new_ty) = addCoercionsToTerm coercions spc (tm, ty) in
          if equalTerm?(result, tm) then opinfo.dfn
            else maybePiAndTypedTerm(replaceNthRefinement(trps, refine_num, (tvs, new_ty, result)))

      def mapType ty = addCoercionsToType_helper coercions spc ty
      def mapTerm (tm,ty) = addCoercionsToTerm_helper coercions spc (tm,ty)
      def mapTermNoType tm = mapTerm (tm, inferType (spc, tm))

      def coerceRestrictedPats pat =
        case pat of
          | RestrictedPat(pat, pred, a) ->
            RestrictedPat(pat, mapTerm(pred, inferType(spc, pred)), a)
          | _ -> pat
    in
    % let _ = printSpecWithTypesToTerminal spc in
    let spc =
        spc << {ops = foldl (fn (ops, el) ->
                             case el of
                               | Op (qid as Qualified(q, id), true, _) ->
                                 %% true means decl includes def
                                 (case findAQualifierMap(ops, q, id) of
                                   | Some info ->
                                     insertAQualifierMap (ops, q, id,
                                                          info << {dfn = mapTermTop (info, 0)})
                                   | None -> ops)
                               | OpDef (qid as Qualified(q, id), refine_num, _, _) ->
                                 (case findAQualifierMap(ops, q, id) of
                                   | Some info ->
                                     insertAQualifierMap (ops, q, id,
                                                          info << {dfn = mapTermTop (info, refine_num)})
                                   | None -> ops)
                               | _ -> ops)
                        spc.ops
                        spc.elements,
                %% mapOpInfos (fn info -> info << {dfn = mapTermTop info}) spc.ops,
                elements = map (fn el ->
                                  case el of
                                    | Property(pt, nm, tvs, term, a) ->
                                      let term = mapTerm (term, boolType) in
                                      let term = MetaSlang.mapTerm(id, mapType, coerceRestrictedPats) term in
                                      Property(pt, nm, tvs, term, a)
                                    | OpDef (qid, n, opt_proof, a) ->
                                      OpDef (qid, n,
                                             (case opt_proof of
                                                | None -> None
                                                | Some pf ->
                                                  Some (mapProof "addCoercions"
                                                          (mapTermNoType, mapType, coerceRestrictedPats) pf)
                                              ),
                                             a)
                                    | _ -> el)
                             spc.elements}
    in
    let spc = mapSpec (id, mapType, id) spc in
    % let _ = writeLine(printSpec spc) in
    spc

  op checkCoercions (tm: MSTerm, coercions: TypeCoercionTable): Option(TypeCoercionInfo * MSTerm) =
    % let _ = writeLine("cc: "^printTerm tm) in
    let result = (checkCoercions1 (tm, coercions)).2 in
    % let _ = writeLine("is "^show (some? result)) in
    result

  op checkCoercions1  (tm: MSTerm, coercions: TypeCoercionTable): Bool * Option(TypeCoercionInfo * MSTerm) =
    case tm of
      | Apply(Lambda (match, _), _, _) ->
        foldl (\_lambda (result, (_, _, x)) -> checkCoercions2(result, x, coercions))
          (true, None) match
      | Apply(f, _, _) ->
        (case findLeftmost (fn tb -> equalTerm?(f, tb.coerceToSuper) \_or equalTerm?(f, tb.coerceToSub))
                coercions of
           | Some tb -> (true, Some(tb, f))
           | None -> (false, None))
      | Record(row, _) ->
        (foldl (\_lambda (result, (_, x)) -> checkCoercions2(result, x, coercions))
           (true, None) row)
      | Let(_, x, _) -> checkCoercions1(x, coercions)
      | IfThenElse(_, x, y, _) -> checkCoercions2(checkCoercions1(x, coercions), y, coercions)
      | Fun(Nat _, _, _)  -> (true, None)
      | _ -> (false, None)

  op checkCoercions2(result: Bool * Option(TypeCoercionInfo * MSTerm), tm: MSTerm, coercions: TypeCoercionTable)
       : Bool * Option(TypeCoercionInfo * MSTerm) =
    case checkCoercions1 (tm, coercions) of
      | (false, _) -> (false, None)
      | new_result ->
     case result of
       | (false, _) -> (false, None)
       | (true, Some _) -> result
       | (true, None) -> new_result

  op removeCoercions(tm: MSTerm, f, product?: Bool, coercions: TypeCoercionTable): MSTerm =
    % let _ = writeLine("rc: "^printTerm tm^" cf: "^printTerm f) in
    let result =
        case tm of
          | Apply(Lambda(match, a1), x, a2) ->
            let n_match = map (fn (p, c, b) -> (p, c, removeCoercions(b, f, product?, coercions))) match in
            Apply(Lambda(n_match, a1), x, a2)
          | Apply(f1, x, _) | f = f1 -> x
          | Let(b, x, a) -> Let(b, removeCoercions(x, f, product?, coercions), a)
          | IfThenElse(p, x, y, a) ->
            IfThenElse(p, removeCoercions(x, f, product?, coercions), removeCoercions(y, f, product?, coercions), a)
          | Record(row, a) | product? ->
            Record(map (\_lambda(id, x) -> (id, removeCoercions(x, f, false, coercions))) row, a)
          | Fun(Nat i, _, _) -> mkNat i
          | _ -> tm
     in
     % let _ = writeLine("= "^printTerm result) in
     result

  op equalOpFn?(qid: QualifiedId, tm: MSTerm): Bool =
    case tm of
      | Fun(Op(qid2, _), _, _) -> qid = qid2
      | _ -> false

  % FIXME: update exploitOverloading to update any proofs in the spec as well

  op exploitOverloading  (coercions: TypeCoercionTable) (doMinus?: Bool) (spc: Spec): Spec =
    let def mapTermTop (opinfo, refine_num) =
          let trps = unpackTypedTerms (opinfo.dfn) in
          let (tvs, ty, tm) = nthRefinement(trps, refine_num) in
          % let _ = writeLine("exploitOverloading\nfull:\n"^printTerm info.dfn^"\nunpack:\n"^printTerm full_term^"\nref:\n"^printTerm tm) in
          let tm1 = MetaSlang.mapTerm(id, mapType, coerceRestrictedPats) tm in
          let new_ty = MetaSlang.mapType(id, mapType, id) ty in
          let result = mapTerm(tm1, ty) in
          if equalTerm?(result, tm) then opinfo.dfn
            else
              % let _ = writeLine("\nresult:\n"^printTerm(TypedTerm(full_term, new_ty, termAnn full_term))) in
              maybePiAndTypedTerm(replaceNthRefinement(trps, refine_num, (tvs, new_ty, result)))

      def mapType ty =
        case ty of
          | Subtype(s_ty, pred, a) ->
            Subtype(s_ty, mapTerm(pred, mkArrow(s_ty, boolType)), a)
          | _ -> ty

       def mapTerm(tm, target_ty) =
          let rm_ty = inferType(spc, tm) in
          let tm = mapSubTerms(tm, target_ty) in
          liftCoercion (tm, rm_ty, target_ty)
       def maybeCancelCoercions(f, x, tm, subtype) =
         % let _ = if doMinus? then writeLine("mce "^printQualifiedId subtype^": "^printTerm tm^"\n"^anyToString x) else () in
         case x of
           | Apply(f1, x1, _) | equalTerm?(f, f1) -> x1
           | Apply(Fun(Op(qid, _), _, _), x1, _) | equalOpFn?(qid, f) -> x1
           | Apply(Fun(Op(Qualified("Integer", "-"), fx), _, _),
                   Record([("1", t1), ("2", t2)], _), _)
               | doMinus? ->
             % let _ = writeLine("minus "^printQualifiedId subtype^": "^printTerm x) in
             let nt1 = maybeCancelCoercions(f, t1, t1, subtype) in
             let nt2 = maybeCancelCoercions(f, t2, t2, subtype) in
             % let _ = writeLine(printTerm nt1^" - "^printTerm nt2) in
             let f_type = inferType(spc, f) in
             %% The id call means we get the correct obligation but it disappears in the final translation
             if t1 ~= nt1 && t2 ~= nt2
               then mkApply(mkOp(Qualified("Function", "id"), mkArrow(range(spc, f_type), natType)),
                            mkAppl(mkInfixOp(Qualified("Integer", "-"), fx,
                                             mkArrow(mkProduct[natType, natType], intType)),
                                   [nt1, nt2]))
               else tm
           | Fun(Nat i, _, _) | subtype = Qualified("Nat", "Nat") -> mkNat i
           | _ -> tm
       def liftCoercion (tm, rm_ty, target_ty) =
        % let _ = toScreen("lc: "^ printTerm tm ^": "^ printType rm_ty ^" -> "^ printType target_ty ^"\n ") in
        case tm of
          | Apply(f as Fun(Op(qid as Qualified(qual, idn), fx), f_ty, _), x, a) ->
            % let _ = writeLine("lift?: " ^ printTerm tm) in
            (case findLeftmost (fn tb -> equalOpFn?(qid, tb.coerceToSuper))
                     coercions of
               | Some tb -> maybeCancelCoercions(tb.coerceToSub, x, tm, tb.subtype)
               | None ->
             case findLeftmost (fn tb -> equalOpFn?(qid, tb.coerceToSub))
                     coercions of
               | Some tb ->
                 let result = maybeCancelCoercions(tb.coerceToSuper, x, tm, tb.subtype) in
                 % let _ = writeLine("lift: "^printTerm tm^"\n -->  "^printTerm result) in
                 result
               | None ->
             case checkCoercions (x, coercions) of
               | Some(tb, coerce_fn) | idn in? tb.overloadedOps
                 ->
                 (case x of
                    | Let(m, b, a1) -> Let(m, liftCoercion(Apply(f, b, a), rm_ty, target_ty), a1)
                    | _ ->
                  let coerce_ty = inferType(spc, coerce_fn) in
                  let src_ty = maybeSuperType(range(spc, coerce_ty)) in
                  let repl_ty = maybeSuperType(domain(spc, coerce_ty)) in
                  let new_x = removeCoercions(x, coerce_fn, true, coercions) in
                  let new_f_ty = replaceType(f_ty, src_ty, repl_ty, spc) in
                  % let _ = writeLine("f_ty: "^printType f_ty^"\n"^"---> "^printType new_f_ty
                  %                   ^"\n via "^printType src_ty^" --> "^printType repl_ty) in
                  let new_tm = Apply(mkInfixOp(Qualified(qual, idn), fx, new_f_ty),
                                     new_x, a)
                  in
                  % let _ = writeLine("new_tm: "^printTerm new_tm^"\n: "^printType new_f_ty) in
                  (if possiblySubtypeOf?(rm_ty, tb.supertype, spc)
                    then % let _ = writeLine("Added: "^printTerm (Apply(coerce_fn, new_tm, a))) in
                         Apply(coerce_fn, new_tm, a)
                    else % let _ = writeLine("None: "^printTerm new_tm) in
                         new_tm))
               | _ -> tm)
          | Apply(f as Fun(overloaded_op, _, _), x, a)
              | overloaded_op = Equals \_or overloaded_op = NotEquals ->
                (case checkCoercions (x, coercions) of
                   | Some(tb, coerce_fn) ->
                     (case x of
                        | Let(m, b, a1) -> Let(m, liftCoercion(Apply(f, b, a), rm_ty, target_ty), a1)
                        | _ ->
                          let new_x = removeCoercions(x, coerce_fn, true, coercions) in
                          Apply(f, new_x, a))
                   | _ -> tm)
          | _ -> tm
       def mapSubTerms(tm, ty) =
        % let _ = writeLine("mst: "^printTerm tm^" -> " ^ printType ty) in
	case tm of
	  | Apply (t1, t2, a) ->
	    let fn_ty = inferType(spc, t1) in
            let dom = domain (spc, fn_ty) in
            Apply (if embed? Fun t1 then t1
                     else mapTerm(t1, mkArrow(dom, ty)),
                   mapTerm(t2, dom), a)
	  | Record (row, a) ->
	    let srts = map (fn (_, x) -> x) (product (spc, ty)) in
	    Record(map (fn ((idi, tmi), tyi) -> (idi, mapTerm(tmi, tyi))) (zip(row, srts)), a)
	  | Bind (bnd, vars, trm, a) ->
	    Bind (bnd, vars, mapTerm(trm, ty), a)
	  | The (var, trm, a) ->
	    The (var, mapTerm(trm, boolType), a)
	  | Let (decls, bdy, a) ->
	    %Let (map (fn (pat, trm) -> (pat, mapTerm(trm, ty)))   % Assumes no coercions in pattern
	    Let (map (fn (pat, trm) -> (pat, mapTerm(trm, patternType pat)))   % Assumes no coercions in pattern
		   decls,
		 mapTerm(bdy, ty), a)
	  | LetRec (decls, bdy, a) ->
	    LetRec (map (fn ((id, srt), trm) -> ((id, srt), mapTerm(trm, srt))) decls,
		    mapTerm(bdy, ty), a)
	  | Lambda (match, a) ->
	    Lambda (map (fn (pat, condn, trm) ->
			 (pat, mapTerm(condn, boolType), mapTerm(trm, range(spc, ty))))
			 match,
		    a)
	  | IfThenElse (t1, t2, t3, a) ->
	    IfThenElse (mapTerm(t1, boolType), mapTerm(t2, ty), mapTerm(t3, ty), a)
	  | Seq (terms, a) ->
            let pre_trms = butLast terms in
            let lst_trm  =    last terms in 
	    Seq (map (fn trm -> mapTerm(trm, mkProduct [])) pre_trms
                   ++ [mapTerm(lst_trm, ty)], a)
	  | TypedTerm (trm, srt, a) ->
	    TypedTerm (mapTerm(trm, srt), srt, a)
	  | _ -> tm
      def coerceSubtypePreds (ty: MSType): MSType =
        case ty of
          | Subtype(ss, pred, a) -> Subtype(ss, mapTerm(pred, inferType(spc, pred)), a)
          | _ -> ty
      def coerceRestrictedPats pat =
        case pat of
          | RestrictedPat(pat, pred, a) -> RestrictedPat(pat, mapTerm(pred, inferType(spc, pred)), a)
          | _ -> pat
    in
    % let _ = printSpecWithTypesToTerminal spc in
    let spc =
        spc << {ops = foldl (fn (ops, el) ->
                             case el of
                               | Op (qid as Qualified(q, id), _, _) ->
                                 %% true means decl includes def
                                 (case findAQualifierMap(ops, q, id) of
                                   | Some info ->
                                     insertAQualifierMap (ops, q, id,
                                                          info << {dfn = mapTermTop (info, 0)})
                                   | None -> ops)
                               | OpDef (qid as Qualified(q, id), refine_num, _, _) ->
                                 (case findAQualifierMap(ops, q, id) of
                                   | Some info ->
                                     insertAQualifierMap (ops, q, id,
                                                          info << {dfn = mapTermTop (info, refine_num)})
                                   | None -> ops)
                               | _ -> ops)
                        spc.ops
                        spc.elements,
                %% mapOpInfos (fn info -> info << {dfn = mapTermTop info}) spc.ops,
                elements = map (fn el ->
                                  case el of
                                    | Property(pt, nm, tvs, term, a) ->
                                      let term = mapTerm(term, boolType) in
                                      let term = MetaSlang.mapTerm(id, mapType, coerceRestrictedPats) term in
                                      Property(pt, nm, tvs, term, a)
                                    | _ -> el)
                             spc.elements}
    in
    % let _ = writeLine(printSpec spc) in
    spc

  op coerceLiterals (spc: Spec) (tm: MSTerm): MSTerm =
    let def mapTermTop tm =
              mapTerm(tm, inferType(spc, tm))
        def mapTerm(tm, target_ty) =
          case tm of
            | Fun(Nat i, _, a) ->
              Fun(Nat i, target_ty, a) 
            | _ ->
          mapSubTerms(tm, target_ty)
          
       def mapSubTerms(tm, ty) =
	case tm of
	  | Apply (t1, t2, a) ->
	    let fn_ty = inferType(spc, t1) in
            let dom = domain (spc, fn_ty) in
            Apply (if embed? Fun t1 then t1
                     else mapTerm(t1, mkArrow(dom, ty)),
                   mapTerm(t2, dom), a)
	  | Record (row, a) ->
	    let srts = map (fn (_, x) -> x) (product (spc, ty)) in
	    Record(map (fn ((idi, tmi), tyi) -> (idi, mapTerm(tmi, tyi))) (zip(row, srts)), a)
	  | Bind (bnd, vars, trm, a) ->
	    Bind (bnd, vars, mapTerm(trm, ty), a)
	  | The (var, trm, a) ->
	    The (var, mapTerm(trm, boolType), a)
	  | Let (decls, bdy, a) ->
	    %Let (map (fn (pat, trm) -> (pat, mapTerm(trm, ty)))   % Assumes no coercions in pattern
	    Let (map (fn (pat, trm) -> (pat, mapTerm(trm, patternType pat)))   % Assumes no coercions in pattern
		   decls,
		 mapTerm(bdy, ty), a)
	  | LetRec (decls, bdy, a) ->
	    LetRec (map (fn ((id, srt), trm) -> ((id, srt), mapTerm(trm, srt))) decls,
		    mapTerm(bdy, ty), a)
	  | Lambda (match, a) ->
	    Lambda (map (fn (pat, condn, trm) ->
			 (pat, mapTerm(condn, boolType), mapTerm(trm, range(spc, ty))))
			 match,
		    a)
	  | IfThenElse (t1, t2, t3, a) ->
	    IfThenElse (mapTerm(t1, boolType), mapTerm(t2, ty), mapTerm(t3, ty), a)
	  | Seq (terms, a) ->
            let pre_trms = butLast terms in
            let lst_trm  =    last terms in 
	    Seq (map (fn trm -> mapTerm(trm, mkProduct [])) pre_trms
                   ++ [mapTerm(lst_trm, ty)], a)
	  | TypedTerm (trm, srt, a) ->
	    TypedTerm (mapTerm(trm, srt), srt, a)
	  | _ -> tm
    in
    let tm = MetaSlang.mapTerm (id, fn s -> case s of
                                            | Subtype(ss, t, a) -> Subtype(ss, mapTermTop t, a)
                                            | _ -> s,
                                id)
               tm
    in
    tm

  op coerceLiteralsInCoercions (spc: Spec) (coercions: TypeCoercionTable): TypeCoercionTable =
    let coercions = map (fn ci -> ci << {coerceToSuper = coerceLiterals spc ci.coerceToSuper,
                                         coerceToSub   = coerceLiterals spc ci.coerceToSub})
                      coercions
    in
    coercions

  op  overloadedTerm?: MSTerm -> Bool
  def overloadedTerm? tm =
    case tm of
      | Fun(Nat _, _, _) -> true
      | _ -> false

  op directlyImplementedSubtype? (ty: MSType, coercions: TypeCoercionTable): Bool =
    case ty of
      | Base(qid, _, _) -> opaqueTypeQId? coercions qid
      | _ -> false

  op convertApplyToIn?(spc: Spec) (tm0: MSTerm): MSTerm =
    mapTerm (fn tm -> case tm of
                        | Apply (t1, t2, a) ->
                          let fn_ty = inferType(spc, t1) in
                          % let _ = writeLine("in??: "^printTerm tm^": "^printType fn_ty) in
                          (case subtypeOf(fn_ty, Qualified("Set", "Set"), spc) of
                             | Some(Base(_, [p], _)) ->
                               Apply(mkInfixOp(Qualified("Set", "in?"), Infix(Left, 20),
                                               mkArrow(mkProduct[p, fn_ty], boolType)),
                                     mkTuple[t2, t1], a)
                             | _ -> tm)
                        | _ -> tm,
             id, id)
      tm0


  op replaceType(ty: MSType, src_ty: MSType, repl_ty: MSType, spc: Spec): MSType =
    mapType1 (fn ty ->
               if equalType?(ty, src_ty) then repl_ty
               else
               case ty of
                | Base(qid, ty_args, a) ->
                  let uf_ty = unfoldBase(spc, ty) in
                  if uf_ty = ty then ty
                    else let new_ty = replaceType(uf_ty, src_ty, repl_ty, spc) in
                         if new_ty = uf_ty then ty
                         else new_ty
                | _ -> ty)
      ty
 
 op maybeSuperType(ty: MSType): MSType =
   case ty of
     | Subtype(s_ty, _, _) -> s_ty
     | _ -> ty

end-spec
