CurryUtils qualifying spec
  import ../Specs/Utilities
  import ../Specs/Environment

  op  curriedSort?: Spec * Sort -> Boolean
  def curriedSort?(sp,srt) = curryShapeNum(sp,srt) > 1

  op  curryShapeNum: Spec * Sort -> Nat
  def curryShapeNum(sp,srt) =
    let srt = sortInnerSort srt in % might not be needed, but ...
    case arrowOpt(sp,srt)
      of Some (_,rng) -> 1 + curryShapeNum(sp,rng)
       | _ -> 0

  op  curryArgSorts: Spec * Sort -> List Sort
  def curryArgSorts(sp,srt) =
    let srt = sortInnerSort srt in % might not be needed, but ...
    case arrowOpt(sp,srt)
      of Some (dom,rng) -> Cons(stripSubsorts(sp,dom),curryArgSorts(sp,rng))
       | _ -> []

  op curryTypes(ty: Sort, spc: Spec): (List Sort) * Sort =
    case arrowOpt(spc, ty)
      of Some (dom,rng) -> let (doms, rng) = curryTypes(rng,spc) in (dom :: doms, rng)
       | _ -> ([], ty)


  op foldrPred: [a] (a -> Boolean * a) -> Boolean -> List a -> (Boolean * List a)
  def foldrPred f i l =
    List.foldr (fn (x,(changed?,result)) ->
	   let (nchanged?,nx) = f x in
	   (changed? || nchanged?,Cons(nx,result)))
      (i,[])
      l

  op  getCurryArgs: MS.Term -> Option(MS.Term * List MS.Term)
  def getCurryArgs t =
    let def aux(term, i, args) =
        case term
          of Fun(_, srt, _) ->
             if i > 1
               then Some(term, args)
              else None
           | Apply(t1, t2, _) -> aux(t1, i+1, t2::args)
           | _ -> None
  in aux(t, 0, [])

  op mkCurriedLambda(params, body): MS.Term =
    case params of
      | [] -> body
      | p::r -> mkLambda(p, mkCurriedLambda(r, body))

  op  curriedParams: MS.Term -> List Pattern * MS.Term
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

  op curriedParamsBody(defn: MS.Term): List Pattern * MS.Term =
    let def aux(vs,t) =
          case t of
	    | Lambda([(p,_,body)],_) -> aux(vs ++ [p], body)
            | _ -> (vs,t)
    in
    aux([],defn)

  op etaExpandCurriedBody(tm: MS.Term, dom_tys: List Sort): MS.Term =
    case dom_tys of
      | [] -> tm
      | ty1 :: r_tys ->
    case tm of
      | Lambda([(p,p1,body)], a) -> Lambda([(p,p1,etaExpandCurriedBody(body, r_tys))], a)
      | _ ->
    let v = ("cv__"^show(length r_tys), ty1) in
    mkLambda(mkVarPat v, etaExpandCurriedBody(mkApply(tm, mkVar v), r_tys))
 

  op  noncurryArgSorts: Spec * Sort -> List Sort
  def noncurryArgSorts(sp,srt) =
    case arrowOpt(sp,srt)
      of Some (dom,_) ->
	 (case productOpt(sp,dom) of
	   | Some fields -> map (fn(_,s) -> s) fields
	   | _ -> [dom])
       | _ -> []

  def duplicateString(n,s) =
    case n
      of 0 -> ""
       | _ -> s^duplicateString(n - 1,s)

  def unCurryName(name,n) =
    if n <= 1 then name
      else name^duplicateString(n,"-1")

endspec

