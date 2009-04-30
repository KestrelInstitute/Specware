%%% Adds coercion functions between subtype and supertype so they can have
%%% different implementations

Coercions qualifying
spec 
  import /Languages/MetaSlang/Specs/Environment

  type TypeCoercionInfo = {subtype: QualifiedId,
			   supertype: QualifiedId,
			   coerceToSuper: MS.Term,
			   coerceToSub: MS.Term,
                           overloadedOps: List String}
  type TypeCoercionTable = List TypeCoercionInfo

  op needsCoercion?(ctxt_ty: Sort, gen_ty: Sort, coercions: TypeCoercionTable, spc: Spec)
     : Option(Boolean * TypeCoercionInfo) =
    % let _ = writeLine(printSort gen_ty^" -~-> "^printSort ctxt_ty) in
    let result =
          case find (fn tb \_rightarrow subtypeOf?(gen_ty,tb.subtype,spc) \_and \_not(subtypeOf?(ctxt_ty,tb.subtype,spc))) coercions of
            | Some tb \_rightarrow Some(true, tb)
            | None \_rightarrow
          case find (fn tb \_rightarrow subtypeOf?(ctxt_ty,tb.subtype,spc) \_and \_not(subtypeOf?(gen_ty,tb.subtype,spc))) coercions of
            | Some tb \_rightarrow Some(false, tb)
            | None \_rightarrow None
    in
    % let _ = writeLine(if some? result then " Yes" else " No") in
    result

  op opaqueType?(ty: Sort, coercions: TypeCoercionTable, spc: Spec): Boolean =
    exists (fn tb \_rightarrow subtypeOf?(ty,tb.subtype,spc)) coercions

  op idFn?(t: MS.Term): Boolean =
    case t of
      | Fun(Op(Qualified(_, "id"),_),_,_) -> true
      | _ -> false

  op patTermVarsForProduct(fields: List(Id * Sort)): MS.Pattern * MS.Term =
    let (pats,tms,_) = foldr (fn ((fld_i,p_ty), (pats,tms,i)) ->
                                let v = ("x_"^toString i, p_ty) in
                                (Cons((fld_i, mkVarPat v), pats),
                                 Cons((fld_i, mkVar    v),  tms),
                                 i-1))
                         ([], [], length fields)
                         fields
    in
    (mkRecordPat pats, mkRecord tms)

  op  addCoercions: TypeCoercionTable \_rightarrow Spec \_rightarrow Spec
  def addCoercions coercions spc =
    let
      def mapTermTop info =
        % let _ = writeLine("\n") in
	let (tvs,ty,tm) = unpackFirstOpDef info in
	let result = mapTerm(tm,ty) in
        if equalTerm?(result, tm)
          then maybePiTerm(tvs,SortedTerm(tm,ty,termAnn tm)) 
        else
        % let _ = writeLine("Def:\n"^printTerm tm^"\n  changed to\n"^printTerm result) in
        maybePiTerm(tvs,SortedTerm(result,ty,termAnn tm)) 
	
      def mapTerm(tm,ty) =
	let rm_ty = inferType(spc,tm) in
	let delayCoercion? =
	    case tm of
	      | Lambda _ \_rightarrow
                (case rangeOpt(spc,rm_ty) of   % Don't delay set
                   | Some r_ty | equalType?(r_ty, boolSort) \_rightarrow false
                   | _ -> true)
	      | Let _ \_rightarrow true
              | Apply(Lambda _, _, _) \_rightarrow true
	      | LetRec _ \_rightarrow true
	      | IfThenElse _ \_rightarrow true
	      | Record _ \_rightarrow true
	      | _ \_rightarrow false
	in
	let n_tm = mapSubTerms(tm,if delayCoercion? \_or embed? Lambda tm then ty else rm_ty) in
        let n_tm = liftCoercion(n_tm,rm_ty,ty) in
	if delayCoercion? \_or overloadedTerm? n_tm then n_tm
	else
        % let _ = writeLine(printTerm tm^": "^printSort rm_ty ^"\n-> " ^ printSort ty^"\n") in
	case needsCoercion?(ty,rm_ty,coercions,spc) of
          | Some(toSuper?, tb) \_rightarrow
            if toSuper? then coerceToSuper(n_tm,tb) else coerceToSub(n_tm,tb)
          | None \_rightarrow
        if simpleTerm n_tm then         % Var or Op
          case (arrowOpt(spc,ty), arrowOpt(spc,rm_ty)) of
            | (Some(dom,rng), Some(rm_dom, rm_rng))
                | ~(opaqueType?(ty, coercions, spc))
                  && (some?(needsCoercion?(dom,rm_dom,coercions,spc))
                       || some?(needsCoercion?(rng,rm_rng,coercions,spc))) ->
              (case productOpt(spc,dom) of
                | Some fields \_rightarrow
                  let (v_pat,v_tm) = patTermVarsForProduct fields in
                  mkLambda(v_pat, mapTerm(mkApply(n_tm,v_tm), rng))
                | None \_rightarrow
                  mkLambda(mkVarPat("xz",dom), mapTerm(mkApply(n_tm,mkVar("xz",dom)), rng)))
            | _ ->
          case (productOpt(spc,ty), productOpt(spc,rm_ty)) of
            | (Some fields, Some rm_fields)
                | exists (fn ((_,p_ty),(_,rm_p_ty)) ->
                            some?(needsCoercion?(p_ty,rm_p_ty,coercions,spc)))
                    (zip(fields,rm_fields)) \_rightarrow
              let (v_pat,v_tm) = patTermVarsForProduct rm_fields in
              mkLet([(v_pat, n_tm)], v_tm)
            %% !! Need more general cases as well
            | _ \_rightarrow n_tm
        else n_tm

      def mapSubTerms(tm,ty) =
        % let _ = writeLine("mst: "^printTerm tm^" -> " ^ printSort ty) in
	case tm of
	  | Apply (t1, t2, a) \_rightarrow
	    let fn_ty = inferType(spc,t1) in
            (case find (fn tb \_rightarrow subtypeOf?(fn_ty,tb.subtype,spc)) coercions of
               | Some tb | tb.subtype = Qualified("Set","Set")->
                 (case subtypeOf(fn_ty, tb.subtype, spc) of
                    | Some(Base(_,[p],_)) ->
                      let t1 = if embed? Fun t1 then t1 else mapTerm(t1,fn_ty) in
                      let t2 = mapTerm(t2,p) in
                      Apply(mkInfixOp(Qualified("Set","in?"), Infix(Left,20),
                                      mkArrow(mkProduct[p,fn_ty],boolSort)),
                            mkTuple[t2,t1],
                            a))
               | _ ->
                 let dom = domain (spc,fn_ty) in
                 Apply (if embed? Fun t1 then t1
                          else mapTerm(t1, mkArrow(dom,ty)),
                        mapTerm(t2,dom), a))
	  | Record (row, a) ->
	    let srts = map (fn (_,x) -> x) (product (spc,ty)) in
	    Record(map (fn ((idi,tmi),tyi) \_rightarrow (idi, mapTerm(tmi,tyi))) (zip(row,srts)), a)
	  | Bind (bnd, vars, trm, a) ->
	    Bind (bnd, vars, mapTerm(trm,ty), a)
	  | The (var, trm, a) ->
	    The (var, mapTerm(trm,boolSort), a)
	  | Let (decls, bdy, a) ->
	    %Let (map (fn (pat,trm) \_rightarrow (pat,mapTerm(trm,ty)))   % Assumes no coercions in pattern
	    Let (map (fn (pat,trm) \_rightarrow (pat,mapTerm(trm,patternSort pat)))   % Assumes no coercions in pattern
		   decls,
		 mapTerm(bdy,ty), a)
	  | LetRec (decls, bdy, a) ->
	    LetRec (map (fn ((id,srt), trm) \_rightarrow ((id,srt), mapTerm(trm,srt))) decls,
		    mapTerm(bdy,ty), a)
	  | Lambda (match, a) ->
	    Lambda (map (fn (pat,condn,trm) \_rightarrow
			 (pat, mapTerm(condn,boolSort),mapTerm(trm, range(spc,ty))))
			 match,
		    a)
	  | IfThenElse (t1, t2, t3, a) ->
	    IfThenElse (mapTerm(t1,boolSort), mapTerm(t2,ty), mapTerm(t3,ty), a)
	  | Seq (terms, a) ->
            let pre_trms = butLast terms in
            let lst_trm  =    last terms in 
	    Seq (map (fn trm -> mapTerm(trm, mkProduct [])) pre_trms
                   ++ [mapTerm(lst_trm, ty)], a)
	  | SortedTerm (trm, srt, a) ->
	    SortedTerm (mapTerm(trm,srt), srt, a)
	  | _ \_rightarrow tm

      def liftCoercion (tm,ty,target_ty) =
        % let _ = toScreen("lc: "^ printTerm tm ^": "^ printSort ty ^" -> "^ printSort target_ty ^"\n ") in
        case tm of
          | Apply(f as Fun(Op(Qualified(qual,idn),_),_,_),x,a) \_rightarrow
            % let _ = writeLine("lift?: " ^ printTerm tm ^ " with qual: "^qual) in
            (case checkCoercions x of
               | Some(tb,coerce_fn)
                   | member(idn,tb.overloadedOps)
                     \_or %% Special case for minus (probably not worth generalizing)
                       %% minus on nats is equal to minus on integers if we know result is a nat
                     (qual = "Integer" \_and idn = "-" %\_and coerce_fn = int
                        \_and subtypeOf?(target_ty,Qualified("Nat","Nat"),spc))
                 \_rightarrow
                 (case x of
                    | Let(m,b,a1) -> Let(m, liftCoercion(Apply(f,b,a),ty,target_ty), a1)
                    | _ ->
                  let new_x = removeCoercions(x,coerce_fn,true) in
                  let new_tm = Apply(f,new_x,a) in
                  (if subtypeOf?(ty,tb.supertype,spc) % This needs to be modified to not use .supertype!!
                    then Apply(coerce_fn,new_tm,a)
                    else new_tm))
               | _ \_rightarrow tm)
          | Apply(f as Fun(overloaded_op,_,_),x,a)
              | overloaded_op = Equals \_or overloaded_op = NotEquals \_rightarrow
            (case checkCoercions x of
               | Some(tb,coerce_fn) ->
                 (case x of
                    | Let(m,b,a1) -> Let(m, liftCoercion(Apply(f,b,a),ty,target_ty), a1)
                    | _ ->
                  let new_x = removeCoercions(x,coerce_fn,true) in
                  Apply(f,new_x,a))
               | _ \_rightarrow tm)
          | _ \_rightarrow tm
      def checkCoercions tm =
        % let _ = writeLine("cc: "^printTerm tm) in
        let result = (checkCoercions1 tm).2 in
        % let _ = writeLine("is "^toString (some? result)) in
        result
      def checkCoercions1 tm =
        case tm of
          | Apply(Lambda (match, _), _, _) ->
            foldl (\_lambda (result, (_,_,x)) \_rightarrow checkCoercions2(result,x))
              (true, None) match
          | Apply(f,_,_) \_rightarrow
            (case find (fn tb \_rightarrow f = tb.coerceToSuper \_or f = tb.coerceToSub) coercions of
               | Some tb \_rightarrow (true, Some(tb,f))
               | None \_rightarrow (false,None))
          | Record(row, _) \_rightarrow
            (foldl (\_lambda (result, (_,x)) \_rightarrow checkCoercions2(result,x))
               (true, None) row)
          | Let(_,x,_) \_rightarrow checkCoercions1 x
          | IfThenElse(_,x,y,_) \_rightarrow checkCoercions2(checkCoercions1 x,y)
          | _ \_rightarrow (overloadedTerm? tm,None)
      def checkCoercions2(result,tm) =
        case checkCoercions1 tm of
          | (false,_) -> (false,None)
          | new_result ->
         case result of
           | (false,_) -> (false,None)
           | (true,Some _) -> result
           | (true,None) -> new_result
      def removeCoercions(tm,f,product?) =
        % let _ = writeLine("rc: "^printTerm tm^" cf: "^printTerm f) in
        let result =
            case tm of
              | Apply(Lambda(match,a1),x,a2) \_rightarrow
                let n_match = map (fn (p,c,b) -> (p,c,removeCoercions(b,f,product?))) match in
                Apply(Lambda(n_match,a1),x,a2)
              | Apply(f1,x,_) | f = f1 \_rightarrow x
              | Let(b,x,a) \_rightarrow Let(b, removeCoercions(x,f,product?), a)
              | IfThenElse(p,x,y,a) \_rightarrow
                IfThenElse(p,removeCoercions(x,f,product?),removeCoercions(y,f,product?),a)
              | Record(row, a) | product? ->
                Record(map (\_lambda(id,x) -> (id,removeCoercions(x,f,false))) row, a)
              | _ -> tm
        in
        % let _ = writeLine("= "^printTerm result) in
        result
      def coerceToSuper(tm,tb) =
        case tm of
          | Apply(f,x,_) | f = tb.coerceToSub \_rightarrow x
          | Let(m,b,a) \_rightarrow Let(m,coerceToSuper(b,tb),a)
          | _ \_rightarrow
            if idFn? tb.coerceToSuper then tm
              else mkApply(tb.coerceToSuper,tm)
      def coerceToSub(tm,tb) =
        case tm of
          | Apply(f,x,_) | f = tb.coerceToSuper \_rightarrow x
          | Let(m,b,a) \_rightarrow Let(m,coerceToSub(b,tb),a)
          | _ \_rightarrow
            if idFn? tb.coerceToSub then tm
              else mkApply(tb.coerceToSub,tm)
    in
    % let _ = printSpecWithSortsToTerminal spc in
    let spc =
        spc << {ops = foldl (fn (ops,el) \_rightarrow
                             case el of
                               | Op (qid as Qualified(q,id), true, _) \_rightarrow
                                 %% true means decl includes def
                                 (case AnnSpec.findTheOp(spc,qid) of
                                   | Some info \_rightarrow
                                     insertAQualifierMap (ops, q, id,
                                                          info << {dfn = mapTermTop info})
                                   | None \_rightarrow ops)
                               | OpDef (qid as Qualified(q,id), _) \_rightarrow
                                 (case AnnSpec.findTheOp(spc,qid) of
                                   | Some info \_rightarrow
                                     insertAQualifierMap (ops, q, id,
                                                          info << {dfn = mapTermTop info})
                                   | None \_rightarrow ops)
                               | _ \_rightarrow ops)
                        spc.ops
                        spc.elements,
                %% mapOpInfos (fn info \_rightarrow info << {dfn = mapTermTop info}) spc.ops,
                elements = map (fn el \_rightarrow
                                  case el of
                                    | Property(pt,nm,tvs,term,a) \_rightarrow
                                      Property(pt,nm,tvs,mapTerm(term,boolSort),a)
                                    | _ \_rightarrow el)
                             spc.elements}
    in
    % let _ = writeLine(printSpec spc) in
    spc

  op  overloadedTerm?: MS.Term \_rightarrow Boolean
  def overloadedTerm? tm =
    case tm of
      | Fun(Nat _,_,_) \_rightarrow true
      | _ \_rightarrow false

  op directlyImplementedSubsort?(ty: Sort, coercions: TypeCoercionTable): Boolean =
    case ty of
      | Base(qid,_,_) \_rightarrow exists (\_lambda tb \_rightarrow tb.subtype = qid) coercions
      | _ -> false

endspec
