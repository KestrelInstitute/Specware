Unifier qualifying
spec
 import /Languages/MetaSlang/Specs/StandardSpec
 sort Subst = List (Var * MS.Term)
 sort Vars = List Var

 op empty: Subst
 def empty = []

 op lookup: Subst * Var -> Option MS.Term
 def lookup(sbst,v) =
   case sbst of
     | [] -> None
     | (vi,vali)::rsbst ->
       if vi = v then Some vali else lookup(rsbst,v)

 op addToSubst: Subst * Var * MS.Term -> Subst
 def addToSubst(sb,v,t) = Cons((v,t),sb)

 op unify: MS.Term * MS.Term * Vars -> Option Subst
 def unify (t1, t2, vs) =
   unifyRec(t1, t2, empty, vs)

 op unifyList: fa(a) List a * List a * Subst * Vars
                     * (a * a * Subst * Vars -> Option Subst)
                   -> Option Subst
 def unifyList(t1s, t2s, sb, vs, subFn) =
   if ~(length t1s = length t2s)
     then None
    else
    case (t1s,t2s) of
      | ([],[]) -> Some sb
      | (t1::rt1s,t2::rt2s) ->
        case subFn(t1,t2,sb,vs) of
	  | None -> None
	  | Some sb -> unifyList(rt1s,rt2s,sb,vs,subFn)

 op unifyRec: MS.Term * MS.Term * Subst * Vars -> Option Subst
 def unifyRec(t1, t2, sb, vs) =
  case (t1, t2) of
     | (Var(v1,_), t2) ->
       if member(v1,vs)
	 then (case lookup(sb,v1) of
	        | Some t1n -> unifyRec(t1n, t2, sb, vs)
	        | None -> Some(addToSubst(sb,v1,t2)))
       else (case t2 of
	       | Var(v2,_) ->
	         if member(v2,vs)
		   then (case lookup(sb,v2) of
	                   | Some t2n -> unifyRec(t1, t2n, sb, vs)
			   | None -> Some(addToSubst(sb,v2,t1)))
		  else if v1 = v2 then Some sb else None)
     | (t1, Var(v2,_)) ->
       if member(v2,vs)
	 then case lookup(sb,v2) of
	       | Some t2n -> unifyRec(t1, t2n, sb, vs)
	       | None -> Some(addToSubst(sb,v2,t1))
        else None      	% Previous case handled t1 as a Var

     | (Apply(x1, y1, _), Apply(x2, y2, _)) ->
       (case unifyRec(x1, x2, sb, vs) of
	 | None -> None
	 | Some sb -> unifyRec(y1, y2, sb, vs))

     | (ApplyN(xs1,_), ApplyN(xs2,_)) ->
       unifyList(xs1, xs2, sb, vs, unifyRec)

     | (Record(xs1,_), Record(xs2,_)) ->
       unifyList (xs1, xs2, sb, vs,
		  fn ((label1,x1), (label2,x2), sb, vs) -> 
		    if label1 = label2
		      then unifyRec(x1, x2, sb, vs)
		      else None)

     %% Fix!:: Currently name clashes with binding constructs are ignored
     | (Bind(b1, vs1, x1, _), Bind(b2, vs2, x2, _))
       -> if ~(b1 = b2)
	   then None
	  else
	    %% Could check modulo alpha conversion...
	    if equalList? (vs1, vs2, equalVar?)
	     then unifyRec(x1, x2, sb,vs)
	     else None

     | (Let(pts1, b1,_), Let(pts2, b2,_)) ->
       (case unifyRec(b1, b2, sb, vs) of
	 | None -> None
	 | Some sb -> unifyList (pts1, pts2, sb, vs,
				 fn ((p1,t1),(p2,t2), sb, vs) -> 
				  if equalPattern? (p1, p2)
				    then unifyRec(t1, t2, sb, vs)
				    else None))

     | (LetRec(vts1, b1,_), LetRec(vts2, b2,_)) ->
       (case unifyRec(b1, b2, sb, vs) of
	 | None -> None
	 | Some sb -> unifyList (vts1, vts2, sb, vs,
				 fn ((v1,t1),(v2,t2), sb, vs) -> 
				  if equalVar?(v1, v2)
				    then unifyRec(t1, t2, sb, vs)
				    else None))

     | (Fun(f1, s1,_), Fun(f2, s2,_)) ->
       if equalFun?(f1,f2) & equalSort?(s1,s2)
	 then Some sb
	 else None

     | (Lambda(xs1,_), Lambda(xs2,_)) ->
       unifyList (xs1, xs2, sb, vs,
		  fn ((p1,c1,b1),(p2,c2,b2), sb, vs) ->
		   if equalPattern?(p1, p2)
		     then case unifyRec(c1, c2, sb, vs) of
		           | None -> None
		           | Some sb -> unifyRec(b1, b2, sb, vs)
		    else None)

     | (IfThenElse (c1, x1, y1,_), IfThenElse (c2, x2, y2,_)) ->
       (case unifyRec(c1, c2, sb, vs) of
	 | None -> None
	 | Some sb ->
        case unifyRec(x1, x2, sb, vs) of 
	 | None -> None
	 | Some sb -> unifyRec(y1, y2, sb, vs))

     | (Seq(xs1,_), Seq(xs2,_)) -> unifyList (xs1, xs2, sb, vs, unifyRec)

     | (SortedTerm (x1, s1,_), SortedTerm (x2, s2,_)) ->
       if equalSort? (s1, s2)
	 then unifyRec(x1, x2, sb, vs)
	 else None

     | _ -> None

endspec