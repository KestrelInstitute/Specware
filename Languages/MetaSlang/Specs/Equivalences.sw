AnnSpec qualifying spec

 import AnnSpec
 import /Languages/MetaSlang/AbstractSyntax/Equalities

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op  equalSortInfo?: [a] ASortInfo a * ASortInfo a -> Boolean
 def equalSortInfo? (info1, info2) =
   info1.names = info2.names
   %% Could take into account substitution of tvs
   && equalSort? (info1.dfn, info2.dfn)

 op  equalOpInfo?: [a] AOpInfo a * AOpInfo a -> Boolean
 def equalOpInfo? (info1, info2) =
   info1.names = info2.names
   && info1.fixity = info2.fixity
   && equalTerm? (info1.dfn, info2.dfn)

 op  equalProperty?: [a] AProperty a * AProperty a -> Boolean
 def equalProperty? ((propType1, propName1, tvs1, fm1),
		     (propType2, propName2, tvs2, fm2))
   =
   propType1 = propType2 && equalTerm? (fm1, fm2) && equalTyVars? (tvs1, tvs2)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op equivTerms?    : Spec -> MS.Term    * MS.Term    -> Boolean
 op equivTypes?    : Spec -> MS.Sort    * MS.Sort    -> Boolean
 op equivPatterns? : Spec -> MS.Pattern * MS.Pattern -> Boolean

 def equivTerms? spc (t1, t2) =
   equalTerm? (t1,t2)

 def equivTypes? spc (t1, t2) =
   equalSort? (t1,t2)

 def equivPatterns? spc (t1, t2) =
   equalPattern? (t1,t2)

 op  sameSpecElement?: [a] ASpec a * ASpecElement a * ASpec a * ASpecElement a -> Boolean
 def sameSpecElement? (s1, e1, s2, e2) =
   case e1 of
     | Import (s1_tm, s1, _) ->
       (case e2 of
	  | Import (s2_tm, s2, _) -> sameSCTerm? (s1_tm, s2_tm) 
	  | _ -> false)
     | Sort qid1 -> 
       (case e2 of
	  | Sort qid2 -> 
	    let Some info1 = findTheSort (s1, qid1) in
	    let Some info2 = findTheSort (s2, qid2) in
	    (info1.names = info2.names
	     &&
	     (case (info1.dfn, info2.dfn) of
		| (Any _, _) -> true
		| (_, Any _) -> true
		| (srt1, srt2) -> equalSort? (srt1, srt2)))
	  | _ -> false)
     | SortDef qid1 -> 
       (case e2 of
	  | SortDef qid2 -> 
	    let Some info1 = findTheSort (s1, qid1) in
	    let Some info2 = findTheSort (s2, qid2) in
	    (info1.names = info2.names
	     &&
	     (case (info1.dfn, info2.dfn) of
		| (Any _, _) -> true
		| (_, Any _) -> true
		| (srt1, srt2) -> equalSort? (srt1, srt2)))
	  | _ -> false)
     | Op qid1 ->
       (case e2 of
	  | Op qid2 -> 
	    let Some info1 = findTheOp (s1, qid1) in
	    let Some info2 = findTheOp (s2, qid2) in
	    (info1.names = info2.names
	     && info1.fixity = info2.fixity
	     && equalSort? (termSort info1.dfn, termSort info2.dfn)
	     && (case (info1.dfn, info2.dfn) of
		   | (Any _,                    _) -> true
		   | (_,                    Any _) -> true
		   | (SortedTerm (Any _, _, _), _) -> true
		   | (_, SortedTerm (Any _, _, _)) -> true
		   | (tm1, tm2) ->  equalTerm? (tm1, tm2)))
	  | _ -> false)
     | OpDef qid1 -> 
       (case e2 of
	  | OpDef qid2 -> 
	    let Some info1 = findTheOp (s1, qid1) in
	    let Some info2 = findTheOp (s2, qid2) in
	    (info1.names = info2.names
	     && info1.fixity = info2.fixity
	     && equalSort? (termSort info1.dfn, termSort info2.dfn)
	     && (case (info1.dfn, info2.dfn) of
		   | (Any _,                    _) -> true
		   | (_,                    Any _) -> true
		   | (SortedTerm (Any _, _, _), _) -> true
		   | (_, SortedTerm (Any _, _, _)) -> true
		   | (tm1, tm2) -> equalTerm? (tm1, tm2)))
	  | _ -> false)
     | Property p1 ->
       (case e2 of
	  | Property p2 -> propertyName p1 = propertyName p2
	  | _ -> false)
     | _ -> e1 = e2

end-spec
