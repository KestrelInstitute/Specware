Transform qualifying
spec
  import ../Specs/Environment
  op  translateRecordMergeInSpec : Spec -> Spec
  def translateRecordMergeInSpec spc =
    mapSpec (fn t -> translateRecordMerge(t,spc),id,id) spc

  op  translateRecordMerge : MS.Term * Spec -> MS.Term
  def translateRecordMerge (t,spc) =
    case t of
      | Apply(Fun(RecordMerge,s,_),Record([("1",t1),("2",t2)],_),a) ->
	(case arrowOpt(spc,s) of
	   | Some(dom,rng) ->
	     (case (productOpt(spc,rng),productOpt(spc,inferType(spc,t2))) of
		| (Some resultFields,Some t2Fields) ->
		  let rawResult = Record(map (fn (field,_) ->
					      (field,if exists (fn (f,_) -> f=field) t2Fields
						       then fieldAcessTerm(t2,field,spc)
						     else fieldAcessTerm(t1,field,spc)))
					 resultFields,
					 a)
		  in
		  maybeIntroduceVarsForTerms(rawResult,[t1,t2],spc)
		| _ -> t)
	   | _ -> t)
      | _ -> t
endspec
