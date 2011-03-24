AddTypeConstructorsToSpec qualifying spec

import CodeGenUtilities

 (**
 * adds for each co-product sort the constructor ops for each element.
 * e.g. for Lists, the following ops are added:
 * op List_cons fa (a) a * List -> List
 * def List_cons (x1, x2) = (embed cons) (x1, x2)
 * op List_nil: () -> List
 * def List_nil () = embed nil
 *)

op addSortConstructorsToSpec : Spec -> Spec * List (QualifiedId)
def addSortConstructorsToSpec spc =
  addSortConstructorsToSpecInternal (spc, false)

op addSortConstructorsToSpecForSnark : Spec -> Spec * List (QualifiedId)
def addSortConstructorsToSpecForSnark spc =
  addSortConstructorsToSpecInternal (spc, true)

op addSortConstructorsToSpecInternal : Spec * Boolean -> Spec * List (QualifiedId)
def addSortConstructorsToSpecInternal (spc, forSnark?) =
  foldriAQualifierMap
   (fn (q, id, sortinfo, (spc, opnames)) ->
     let (spc, opnames0) = addSortConstructorsFromSort (spc, forSnark?, Qualified (q, id), sortinfo) in
    (spc, opnames ++ opnames0))
   (spc, []) 
    spc.sorts

op addSortConstructorsFromSort: Spec * Boolean * QualifiedId * SortInfo -> Spec * List (QualifiedId)
def addSortConstructorsFromSort (spc, forSnark?, qid, info) =
  if ~ (definedSortInfo? info) then
    (spc, [])
  else
    let (tvs, srt) = unpackFirstSortDef info in
    case srt of
      | CoProduct (fields, b) -> 
        (%let _ = writeLine ("generating constructor ops for sort "^ (printQualifiedId qid)^"...") in
	 %let _ = writeLine ("  typevars: "^ (List.show ", " tvs)) in
	 List.foldr (fn ((id, optsrt), (spc, opnames)) ->
		     let opqid as Qualified (opq, opid) = 
		         if forSnark? then 
			   getConstructorOpNameForSnark (qid, id) 
			 else
			   getConstructorOpName (qid, id) 
		     in
		     %let _ = writeLine ("  op "^ (printQualifiedId opqid)) in
		     let tvsrts = map (fn tv -> TyVar (tv, b)) tvs in
		     let codom:Sort  = Base (qid, tvsrts, b) in
		     let opsrt = case optsrt of
				   | None -> Arrow (Product ([], b), codom, b)
				   | Some s -> Arrow (s, codom, b)
		     in
		     let (termsrt, eb) = 
		         case optsrt of
			   | None -> (codom, false)
			   | Some s -> (Arrow (s, codom, b), true)
		     in
		     let pat = patternFromSort (optsrt, b) in
		     let cond = mkTrue () in
		     let funterm = Fun (Embed (id, eb), termsrt, b) in
		     let body = argTermFromSort (optsrt, funterm, b) in
		     let term = Lambda ([(pat, cond, body)], b) in
		     let opinfo = {names  = [opqid], 
				   fixity = Nonfix, 
				   dfn    = maybePiTerm (tvs, SortedTerm (term, opsrt, b)),
				   fullyQualified? = false}
		     in
		     let newops = insertAQualifierMap (spc.ops, opq, opid, opinfo) in
		     let opnames = Cons (opqid, opnames) in
		     (setOps (spc, newops), opnames))
	            (spc, []) 
		    fields)
      | _ -> (spc, [])

 op getConstructorOpName: QualifiedId * String -> QualifiedId
def getConstructorOpName (qid as Qualified (q, id), consid) =
  % the two _'s are important: that how the constructor op names are
  % distinguished from other opnames (hack)
  let sep = "__" in
  Qualified (q, id^sep^consid)

 op getConstructorOpNameForSnark: QualifiedId * String -> QualifiedId
def getConstructorOpNameForSnark (qid as Qualified (q, id), consid) =
  % the two __'s are important: that how the constructor op names are
  % distinguished from other opnames (hack)
  let sep = "__" in
  Qualified (q, "embed"^sep^consid)


 (**
 * adds for each product sort the Constructor op.
 * e.g. for sort P = {a: SortA, b: SortB}, the following op is added:
 * op mk_Record_P: sortA * sortB -> P
 * def mk_Record_P (a, b) = (a, b)
 *)

op addProductSortConstructorsToSpec: Spec -> Spec * List (QualifiedId)
def addProductSortConstructorsToSpec spc =
  foldriAQualifierMap
   (fn (q, id, sortinfo, (spc, opnames)) ->
     let (spc, opnames0) = addProductSortConstructorsFromSort (spc, Qualified (q, id), sortinfo) in
    (spc, opnames ++ opnames0))
   (spc, []) 
    spc.sorts


op addProductSortConstructorsFromSort: Spec * QualifiedId * SortInfo -> Spec * List (QualifiedId)
def addProductSortConstructorsFromSort (spc, qid, info) =
  if ~ (definedSortInfo? info) then
    (spc, [])
  else
    let (tvs, srt) = unpackFirstSortDef info in
    case srt of
      | Product (fields, b) -> 
        (%let _ = writeLine ("generating constructor ops for sort "^ (printQualifiedId qid)^"...") in
	 %let _ = writeLine ("  typevars: "^ (List.show ", " tvs)) in
	 let opqid as Qualified (opq, opid) = getRecordConstructorOpName qid in
	 %let _ = writeLine ("  op "^ (printQualifiedId opqid)) in
	 let tvsrts = map (fn tv -> TyVar (tv, b)) tvs in
	 let codom:Sort  = Base (qid, tvsrts, b) in
	 let opsrt   = Arrow (srt, codom, b) in
	 let termsrt = Arrow (srt, codom, b) in
	 let pat = patternFromSort (Some srt, b) in
	 let cond = mkTrue () in
	 let funterm = Fun (Op (opqid, Nonfix), termsrt, b) in
	 let body = recordTermFromSort (srt, b) in
	 let term = Lambda ([(pat, cond, body)], b) in
	 let opinfo = {names = [opqid], 
		       fixity = Nonfix, 
		       dfn    = maybePiTerm (tvs, SortedTerm (term, opsrt, b)),
		       fullyQualified? = false}
	 in
	 let newops = insertAQualifierMap (spc.ops, opq, opid, opinfo) in
	 let opnames = [opqid] in
	 (addElementAfter (setOps (spc, newops), OpDef (opqid, 0, noPos),
                           SortDef (qid,noPos)), opnames))  % TODO: maybe change "OpDef opqid" to "OpDecl (opqid, true)"
      | _ -> (spc, [])

 (**
 * adds for each product sort the accessor ops for each element.
 * e.g. for sort P = {a: SortA, b: SortB}, the following ops are added:
 * op project_P_a: P -> sortA, and op project_P_b: P -> sortB
 * def project_P_a (p) = project (a) p, ...
 *)

 op addProductAccessorsToSpec : Spec -> Spec * List (QualifiedId)
def addProductAccessorsToSpec spc =
  foldriAQualifierMap
   (fn (q, id, sortinfo, (spc, opnames)) ->
     let (spc, opnames0) = addProductAccessorsFromSort (spc, Qualified (q, id), sortinfo) in
    (spc, opnames ++ opnames0))
   (spc, []) 
    spc.sorts

op addProductAccessorsFromSort: Spec * QualifiedId * SortInfo -> Spec * List (QualifiedId)
def addProductAccessorsFromSort (spc, qid, info) =
  if ~ (definedSortInfo? info) then
    (spc, [])
  else
    let (tvs, srt) = unpackFirstSortDef info in
    let srt = stripSubsortsAndBaseDefs spc srt in
    case srt of
      | Product (fields, b) -> 
        (%let _ = writeLine ("generating accessor ops for sort "^ (printQualifiedId qid)^"...") in
	 %let _ = writeLine ("  typevars: "^ (List.show ", " tvs)) in
	 List.foldr (fn ((id, srt), (spc, opnames)) ->
		     let srtName = primarySortName info in
		     let Qualified (_, srtId) = srtName in
		     let opqid as Qualified (opq, opid) = getAccessorOpName (srtId, qid, id) in
		     %let _ = writeLine ("  op "^ (printQualifiedId opqid)) in
		     let tvsrts = map (fn tv -> TyVar (tv, b)) tvs in
		     let codom:Sort  = Base (qid, tvsrts, b) in
		     let opsrt   = Arrow (codom, srt, b) in
		     let termsrt = Arrow (codom, srt, b) in
		     let pat = patternFromSort (Some srt, b) in
		     let cond = mkTrue () in
		     let funterm = Fun (Project (id), termsrt, b) in
		     let body = argTermFromSort (Some srt, funterm, b) in
		     let term = Lambda ([(pat, cond, body)], b) in
		     let opinfo = {names  = [opqid], 
				   fixity = Nonfix, 
				   dfn    = maybePiTerm (tvs, SortedTerm (term, opsrt, b)),
				   fullyQualified? = false}
		     in
		     let newops = insertAQualifierMap (spc.ops, opq, opid, opinfo) in
		     let opnames = Cons (opqid, opnames) in
		     (addElementAfter (setOps (spc, newops), OpDef (opqid, 0, noPos), SortDef (qid,noPos)), opnames))  % TODO: maybe change "OpDef opqid" to "OpDecl (opqid, true)"
	            (spc, [])
		    fields)
      | _ -> (spc, [])

end-spec
