AddTypeConstructorsToSpec qualifying spec

import CodeGenUtilities

 (**
 * adds for each co-product type the constructor ops for each element.
 * e.g. for Lists, the following ops are added:
 * op List_cons fa (a) a * List -> List
 * def List_cons (x1, x2) = (embed cons) (x1, x2)
 * op List_nil: () -> List
 * def List_nil () = embed nil
 *)

op addTypeConstructorsToSpec : Spec -> Spec
def addTypeConstructorsToSpec spc =
  let (spc, _) = addTypeConstructorsToSpecInternal (spc, false) in 
  % ignore names of constrOps
  spc

op addTypeConstructorsToSpecForSnark : Spec -> Spec * QualifiedIds
def addTypeConstructorsToSpecForSnark spc =
  addTypeConstructorsToSpecInternal (spc, true)

op addTypeConstructorsToSpecInternal : Spec * Bool -> Spec * QualifiedIds
def addTypeConstructorsToSpecInternal (spc, forSnark?) =
  foldriAQualifierMap
   (fn (q, id, typeinfo, (spc, opnames)) ->
     let (spc, opnames0) = addTypeConstructorsFromType (spc, forSnark?, Qualified (q, id), typeinfo) in
    (spc, opnames ++ opnames0))
   (spc, []) 
    spc.types

op addTypeConstructorsFromType: Spec * Bool * QualifiedId * TypeInfo -> Spec * QualifiedIds
def addTypeConstructorsFromType (spc, forSnark?, qid, info) =
  if ~ (definedTypeInfo? info) then
    (spc, [])
  else
    let (tvs, srt) = unpackFirstTypeDef info in
    case srt of
      | CoProduct (fields, b) -> 
        (%let _ = writeLine ("generating constructor ops for type "^ (printQualifiedId qid)^"...") in
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
		     let codom:MSType  = Base (qid, tvsrts, b) in
		     let opsrt = case optsrt of
				   | None -> Arrow (Product ([], b), codom, b)
				   | Some s -> Arrow (s, codom, b)
		     in
		     let (termsrt, eb) = 
		         case optsrt of
			   | None -> (codom, false)
			   | Some s -> (Arrow (s, codom, b), true)
		     in
		     let pat = patternFromType (optsrt, b) in
		     let cond = mkTrue () in
		     let funterm = Fun (Embed (id, eb), termsrt, b) in
		     let body = argTermFromType (optsrt, funterm, b) in
		     let term = Lambda ([(pat, cond, body)], b) in
		     let opinfo = {names  = [opqid], 
				   fixity = Nonfix, 
				   dfn    = maybePiTerm (tvs, TypedTerm (term, opsrt, b)),
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
 * adds for each product type the Constructor op.
 * e.g. for type P = {a: TypeA, b: TypeB}, the following op is added:
 * op mk_Record_P: typeA * typeB -> P
 * def mk_Record_P (a, b) = (a, b)
 *)

op addProductTypeConstructorsToSpec: Spec -> Spec * List (QualifiedId)
def addProductTypeConstructorsToSpec spc =
  foldriAQualifierMap
   (fn (q, id, typeinfo, (spc, opnames)) ->
     let (spc, opnames0) = addProductTypeConstructorsFromType (spc, Qualified (q, id), typeinfo) in
    (spc, opnames ++ opnames0))
   (spc, []) 
    spc.types


op addProductTypeConstructorsFromType: Spec * QualifiedId * TypeInfo -> Spec * List (QualifiedId)
def addProductTypeConstructorsFromType (spc, qid, info) =
  if ~ (definedTypeInfo? info) then
    (spc, [])
  else
    let (tvs, srt) = unpackFirstTypeDef info in
    case srt of
      | Product (fields, b) -> 
        (%let _ = writeLine ("generating constructor ops for type "^ (printQualifiedId qid)^"...") in
	 %let _ = writeLine ("  typevars: "^ (List.show ", " tvs)) in
	 let opqid as Qualified (opq, opid) = getRecordConstructorOpName qid in
	 %let _ = writeLine ("  op "^ (printQualifiedId opqid)) in
	 let tvsrts = map (fn tv -> TyVar (tv, b)) tvs in
	 let codom:MSType  = Base (qid, tvsrts, b) in
	 let opsrt   = Arrow (srt, codom, b) in
	 let termsrt = Arrow (srt, codom, b) in
	 let pat = patternFromType (Some srt, b) in
	 let cond = mkTrue () in
	 let funterm = Fun (Op (opqid, Nonfix), termsrt, b) in
	 let body = recordTermFromType (srt, b) in
	 let term = Lambda ([(pat, cond, body)], b) in
	 let opinfo = {names = [opqid], 
		       fixity = Nonfix, 
		       dfn    = maybePiTerm (tvs, TypedTerm (term, opsrt, b)),
		       fullyQualified? = false}
	 in
	 let newops = insertAQualifierMap (spc.ops, opq, opid, opinfo) in
	 let opnames = [opqid] in
	 (addElementAfter (setOps (spc, newops), OpDef (opqid, 0, [], noPos),
                           TypeDef (qid,noPos)), opnames))  % TODO: maybe change "OpDef opqid" to "OpDecl (opqid, true)"
      | _ -> (spc, [])

 (**
 * adds for each product type the accessor ops for each element.
 * e.g. for type P = {a: TypeA, b: TypeB}, the following ops are added:
 * op project_P_a: P -> typeA, and op project_P_b: P -> typeB
 * def project_P_a (p) = project (a) p, ...
 *)

 op addProductAccessorsToSpec : Spec -> Spec * List (QualifiedId)
def addProductAccessorsToSpec spc =
  foldriAQualifierMap
   (fn (q, id, typeinfo, (spc, opnames)) ->
     let (spc, opnames0) = addProductAccessorsFromType (spc, Qualified (q, id), typeinfo) in
    (spc, opnames ++ opnames0))
   (spc, []) 
    spc.types

op addProductAccessorsFromType: Spec * QualifiedId * TypeInfo -> Spec * List (QualifiedId)
def addProductAccessorsFromType (spc, qid, info) =
  if ~ (definedTypeInfo? info) then
    (spc, [])
  else
    let (tvs, srt) = unpackFirstTypeDef info in
    let srt = stripSubtypesAndBaseDefs spc srt in
    case srt of
      | Product (fields, b) -> 
        (%let _ = writeLine ("generating accessor ops for type "^ (printQualifiedId qid)^"...") in
	 %let _ = writeLine ("  typevars: "^ (List.show ", " tvs)) in
	 List.foldr (fn ((id, srt), (spc, opnames)) ->
		     let srtName = primaryTypeName info in
		     let Qualified (_, srtId) = srtName in
		     let opqid as Qualified (opq, opid) = getAccessorOpName (srtId, qid, id) in
		     %let _ = writeLine ("  op "^ (printQualifiedId opqid)) in
		     let tvsrts = map (fn tv -> TyVar (tv, b)) tvs in
		     let codom:MSType  = Base (qid, tvsrts, b) in
		     let opsrt   = Arrow (codom, srt, b) in
		     let termsrt = Arrow (codom, srt, b) in
		     let pat = patternFromType (Some srt, b) in
		     let cond = mkTrue () in
		     let funterm = Fun (Project (id), termsrt, b) in
		     let body = argTermFromType (Some srt, funterm, b) in
		     let term = Lambda ([(pat, cond, body)], b) in
		     let opinfo = {names  = [opqid], 
				   fixity = Nonfix, 
				   dfn    = maybePiTerm (tvs, TypedTerm (term, opsrt, b)),
				   fullyQualified? = false}
		     in
		     let newops = insertAQualifierMap (spc.ops, opq, opid, opinfo) in
		     let opnames = Cons (opqid, opnames) in
		     (addElementAfter (setOps (spc, newops), OpDef (opqid, 0, [], noPos), TypeDef (qid,noPos)), opnames))  % TODO: maybe change "OpDef opqid" to "OpDecl (opqid, true)"
	            (spc, [])
		    fields)
      | _ -> (spc, [])

end-spec
