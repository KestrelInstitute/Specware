(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

CurryUtils qualifying spec
  import /Languages/MetaSlang/Specs/Environment

  op  curriedType?: Spec * MSType -> Bool
  def curriedType?(sp,ty) = curryShapeNum(sp,ty) > 1

  op  curryShapeNum: Spec * MSType -> Nat
  def curryShapeNum(sp,ty) =
    let ty = typeInnerType ty in % might not be needed, but ...
    case arrowOpt(sp,ty)
      of Some (_,rng) -> 1 + curryShapeNum(sp,rng)
       | _ -> 0

  op  curryArgTypes: Spec * MSType -> MSTypes
  def curryArgTypes(sp,ty) =
    let ty = typeInnerType ty in % might not be needed, but ...
    case arrowOpt(sp,ty)
      of Some (dom,rng) -> Cons(stripSubtypes(sp,dom),curryArgTypes(sp,rng))
       | _ -> []

  op curryTypes(ty: MSType, spc: Spec): MSTypes * MSType =
    case arrowOpt(spc, ty)
      of Some (dom,rng) -> let (doms, rng) = curryTypes(rng,spc) in (dom :: doms, rng)
       | _ -> ([], ty)


  op foldrPred: [a] (a -> Bool * a) -> Bool -> List a -> (Bool * List a)
  def foldrPred f i l =
    List.foldr (fn (x,(changed?,result)) ->
	   let (nchanged?,nx) = f x in
	   (changed? || nchanged?,Cons(nx,result)))
      (i,[])
      l

  op  getCurryArgs: MSTerm -> Option (MSTerm * MSTerms)
  def getCurryArgs t =
    let def aux(term, i, args) =
        case term
          of Fun(_, ty, _) ->
             if i > 1
               then Some(term, args)
              else None
           | Apply(t1, t2, _) -> aux(t1, i+1, t2::args)
           | _ -> None
  in aux(t, 0, [])

  op numCurryArgs(t: MSTerm): Nat =
    let def aux(term, i) =
          case term of
           | Apply(t1, _, _) -> aux(t1, i+1)
           | _ -> i
    in aux(t, 0)

  op getArgs(term: MSTerm): MSTerms =
    case getCurryArgs term of
      | Some(_, args) -> args
      | None ->
     case term of
      | Apply(_, a1, _) -> termToList a1
      | _ -> []

  op getFnArgs(t: MSTerm): Option (MSTerm * MSTerms * Bool) =
    let def aux(term, args) =
        case term of
          | Apply(t1, t2, _) -> aux(t1, t2::args)
          | _ ->
            (case args of
               | [] -> None
               | [arg] -> Some(term, termToList arg, false)
               | _ -> Some(term, args, true))
    in aux(t, [])

  op applicationOfQId? (qid: QualifiedId) (tm: MSTerm): Bool =
    case tm of
      | Fun(Op(qidi,_),_,_) ->  qidi = qid
      | Apply(f, _, _) -> applicationOfQId? qid f
      | _ -> false

  op mkCurriedLambda(lam_pats: MSPatterns, bod: MSTerm): MSTerm =
    foldr (fn (pat, bod) -> mkLambda(pat, bod)) bod lam_pats

  op unpackCurriedLambda(tm: MSTerm): MSPatterns * MSTerm =
    case tm of
      | Lambda ([(pat,_,bod)],_) ->
        let (r_pats, r_bod) = unpackCurriedLambda bod in
        (pat::r_pats, r_bod)
      | _ -> ([], tm)

  op  curriedParams: MSTerm -> MSPatterns * MSTerm
  def curriedParams defn =
    let def aux(t,vs) =
          case t of
	    | Lambda([(p,_,body)],_) ->
              let p = deRestrict p in
	      if (case p of
		    | VarPat _ -> true
		    | RecordPat _ -> true
                    | QuotientPat _ -> true
		    | _ -> false)
		then aux(body,vs ++ [p])
		else (vs,t)
	    | _ -> (vs,t)
    in
    aux(defn,[])

  op curriedParamsBody(defn: MSTerm): MSPatterns * MSTerm =
    let def aux(vs,t) =
          case t of
	    | Lambda([(p,_,body)],_) -> aux(vs ++ [p], body)
            | _ -> (vs,t)
    in
    aux([],defn)

  op etaExpandCurriedBody(tm: MSTerm, dom_tys: MSTypes): MSTerm =
    case dom_tys of
      | [] -> tm
      | ty1 :: r_tys ->
    case tm of
      | Lambda([(p,p1,body)], a) -> Lambda([(p,p1,etaExpandCurriedBody(body, r_tys))], a)
      | _ ->
    let v = ("cv__"^show(length r_tys), ty1) in
    mkLambda(mkVarPat v, etaExpandCurriedBody(mkApply(tm, mkVar v), r_tys))
 

  op  noncurryArgTypes: Spec * MSType -> MSTypes
  def noncurryArgTypes(sp,ty) =
    case arrowOpt(sp,ty)
      of Some (dom,_) ->
	 (case productOpt(sp,dom) of
	   | Some fields -> map (fn(_,s) -> s) fields
	   | _ -> [dom])
       | _ -> []

  def duplicateString(n,s) =
    case n
      of 0 -> ""
       | _ -> s^duplicateString(n - 1,s)

op uncurryId (id : Id, n : Nat) : Id =
 if n <= 1 then 
   id
 else 
   id ^ duplicateString (n, "-1")

op uncurryName (Qualified (old_q, old_id) : OpName, level : Nat) : OpName =
 mkQualifiedId (old_q, uncurryId (old_id, level))

endspec

