CurryUtils qualifying spec
  import ../Specs/Utilities
  import ../Specs/Environment

  op  curriedSort?: Spec * Sort -> Boolean
  def curriedSort?(sp,srt) = curryShapeNum(sp,srt) > 1

  op  curryShapeNum: Spec * Sort -> Nat
  def curryShapeNum(sp,srt) =
    case arrowOpt(sp,srt)
      of Some (_,rng) -> 1 + curryShapeNum(sp,rng)
       | _ -> 0

  op  curryArgSorts: Spec * Sort -> List Sort
  def curryArgSorts(sp,srt) =
    case arrowOpt(sp,srt)
      of Some (dom,rng) -> cons(stripSubsorts(sp,dom),curryArgSorts(sp,rng))
       | _ -> []

  op foldrPred: fa(a) (a -> Boolean * a) -> Boolean -> List a -> (Boolean * List a)
  def foldrPred f i l =
    List.foldr (fn (x,(changed?,result)) ->
	   let (nchanged?,nx) = f x in
	   (changed? or nchanged?,cons(nx,result)))
      (i,[])
      l

  op  unCurrySort: Sort * Spec -> Boolean * Sort
  %% Returns transformed sort and whether any change was made
  %% Don't look inside sort definitions except to follow arrows
  %% (otherwise infinitely recursive)
  def unCurrySort(srt,spc) =
    let def unCurryRec s = unCurrySort(s,spc)
        def unCurryArrowAux(rng,accumDomSrts) =
	  (case stripSubsorts(spc,rng) of
	    | Arrow(dom, restRng, _) ->
	      let expandedDomSrts = 
                  foldl (fn (dom_srt, dom_srts) ->
			 case productOpt (spc, dom_srt) of
			   | Some fields -> dom_srts ++ (map (fn (_,s) -> s) fields)
			   | _ -> dom_srts ++ [dom_srt])
		        []
		        accumDomSrts
	      in
	      (true,(unCurryArrowAux(restRng,expandedDomSrts ++ [dom])).2)
	    | _ ->
	      let (changed?,nRng) = unCurryRec rng in
	      let (changed?,nDomSrts) = foldrPred unCurryRec changed? accumDomSrts
	      in (changed?,mkArrow(mkProduct nDomSrts, nRng)))
    in
    case srt of
      | Subsort(srt, _, _) -> unCurryRec srt
      | Arrow(dom, rng, _) ->
        unCurryArrowAux(rng,[dom])
      | Product(xs,a) ->
        let (changed?,nxs)
	   = foldrPred (fn (id,t) ->
			let (changed?,nt) = unCurryRec t in
		        (changed?,(id,nt)))
	       false xs
	in (changed?,Product(nxs,a))
      | CoProduct(xs,a) ->
	let (changed?,nxs)
	   = foldrPred (fn (id,Some t) ->
			   let (changed?,nt) = unCurryRec t in
		           (changed?,(id,Some nt))
			  | pr -> (false,pr))
	       false xs
	in (changed?,CoProduct(nxs,a))
      | Quotient(s,t,a) ->
        let (changed?,ns) = unCurryRec s in
	(changed?,Quotient (ns,t,a))
      | s -> (false,s)

  op  getCurryArgs: MS.Term -> Option(MS.Term * List MS.Term)
  def getCurryArgs t =
    let def aux(term,i,args) =
        case term
          of Fun(_,srt,_) ->
             if i > 1
               then Some(term,args)
              else None
           | Apply(t1,t2,_) -> aux(t1,i+1,cons(t2,args))
           | _ -> None
  in aux(t,0,[])

  op  curriedParams: MS.Term -> List Pattern * MS.Term
  def curriedParams defn =
    let def aux(t,vs) =
          case t of
	    | Lambda([(p,_,body)],_) ->
	      if (case p of
		    | VarPat _ -> true
		    | RecordPat _ -> true
		    | _ -> false)
		then aux(body,vs ++ [p])
		else (vs,t)
	    | _ -> (vs,t)
    in
    aux(defn,[])

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

