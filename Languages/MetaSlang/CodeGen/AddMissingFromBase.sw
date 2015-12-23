(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

AddMissingromBase qualifying spec

import /Languages/MetaSlang/Specs/StandardSpec
import /Languages/MetaSlang/CodeGen/Generic/TypeOpInfos

 (**
 * add the ops and type definitions that are defined in the bspc and used in the
 * spc to the spc, so that the resultung spec is self-contained.
 * ignore is a function that can be used to exclude certain qid's from being added
 * if ignore(qid) evaluates to true, the type/op will be ignored, i.e. it will *not* be added.
 *)

op addMissingFromBase: Spec * Spec * (QualifiedId -> Bool) -> Spec
def addMissingFromBase (bspc, spc, ignore?) = addMissingFromBaseTo (bspc, spc, spc, ignore?)

 (**
 * same as addMissingFromBase, only that a spec just containing the missing ops and types
 * is returned.
 *)
op getMissingFromBase: Spec * Spec * (QualifiedId -> Bool) -> Spec
def getMissingFromBase (bspc, spc, ignore?) = addMissingFromBaseTo (bspc, spc, initialSpecInCat, ignore?)

op addMissingFromBaseTo: Spec * Spec * Spec * (QualifiedId -> Bool) -> Spec
def addMissingFromBaseTo (bspc, spc, initSpec, ignore?) =
  %let _ = writeLine ("---------------------- basespc: ------------------") in
  %let _ = writeLine (printSpec bspc) in
  %let _ = writeLine ("---------------------- end basespc ---------------") in
  %let _ = writeLine ("addMissingFromBaseTo, spc="^ (printSpec spc)) in
  let minfo =
      foldriAQualifierMap
       (fn (q, i, info, minfo) ->
	foldl (fn (minfo, def0) ->
	       let srt = typeInnerType def0 in
	       let minfo = addMissingFromType (bspc, spc, ignore?, srt, minfo) in
	       minfo) 
	      minfo 
	      (typeInfoDefs info))
       emptyMonoInfo 
       spc.types
  in
  let minfo =
      foldriAQualifierMap
       (fn (q, i, info, minfo) ->
	foldl (fn (minfo, dfn) ->
	       let (_, srt, trm) = unpackFirstTerm dfn in
	       let minfo = addMissingFromType (bspc, spc, ignore?, srt, minfo) in
	       addMissingFromTerm (bspc, spc, ignore?, trm, minfo))
	      minfo
	      %% including all the defs, including the vacuous ones represented 
	      %% as "Any" terms, so the types of ops get processed
	      (opInfoAllDefs info)) 
       minfo 
       spc.ops
  in
  let minfo =
      foldrSpecElements
        (fn (el, minfo) ->
	 case el of
	   | Property info -> addMissingFromTerm (bspc, spc, ignore?, info.4, minfo)
	   | _ -> minfo)
	minfo 
	spc.elements
  in
  if isEmptyTypeOpInfos? minfo then 
    initSpec 
  else
    let (srts,elts) = foldr (fn (info, (map,elts)) ->
			     let qid = primaryTypeName info in
			     let Qualified (q, id) = qid in
			     (insertAQualifierMap (map, q, id, info),
			      [TypeDef (qid,noPos)] ++ elts))
                       (initSpec.types,initSpec.elements)
		       minfo.types
    in
    let (ops,elts) = foldr (fn (info, (map,elts)) -> 
                              let qid = primaryOpName info in
                              let Qualified (q, id) = qid in
                              (insertAQualifierMap (map, q, id, info),
                               [Op (qid,true,noPos)] ++ elts))
		       (initSpec.ops,elts)
		       minfo.ops
    in
    let initSpec = setTypes   (initSpec, srts) in
    let initSpec = setOps     (initSpec, ops)  in
    let initSpec = setElements(initSpec, elts) in
    addMissingFromBase (bspc, initSpec, ignore?)


op  addMissingFromType: Spec * Spec * (QualifiedId -> Bool) * MSType * TypeOpInfos -> TypeOpInfos
def addMissingFromType (bspc, spc, ignore?, srt, minfo) =
  case srt of
    | Arrow    (srt1, srt2, _) -> addMissingFromType (bspc, spc, ignore?, srt2, addMissingFromType (bspc, spc, ignore?, srt1, minfo))
    | Product  (fields,     _) -> foldl (fn (minfo, (_, srt)) -> addMissingFromType (bspc, spc, ignore?, srt, minfo)) 
				         minfo 
					 fields
    | CoProduct (fields,     _) -> foldl (fn (minfo, (_, Some srt)) -> addMissingFromType (bspc, spc, ignore?, srt, minfo) 
                                              | _ -> minfo)
				         minfo 
					 fields
    | Quotient (srt, term,  _) -> addMissingFromTerm (bspc, spc, ignore?, term, addMissingFromType (bspc, spc, ignore?, srt, minfo))
    | Subtype  (srt, term,  _) -> % addMissingFromTerm (bspc, spc, ignore?, term, addMissingFromType (bspc, spc, ignore?, srt, minfo))
      addMissingFromType (bspc, spc, ignore?, srt, minfo)
    | Base     (qid as Qualified (q, id), srts, _) ->
      if ignore? qid then 
	minfo 
      else
	let minfo = foldl (fn (minfo, srt) -> addMissingFromType (bspc, spc, ignore?, srt, minfo)) minfo srts in
	(case findTheType (spc, qid) of
	   | Some _ -> 
	     minfo
	   | None -> 
	    (case findTheType (bspc, qid) of
		| None -> minfo %fail ("can't happen: couldn't find type def for "^q^"."^id%printQualifiedId qid
				       %^"\n"^ (printSpec bspc)
				       %^"\n"^ (printSpec spc)
				       %   )
		| Some sinfo ->
		addTypeInfo2TypeOpInfos (qid, sinfo, minfo)))

   %| Boolean is same as default case
    | _ -> minfo


op addMissingFromTerm: Spec * Spec * (QualifiedId -> Bool) * MSTerm * TypeOpInfos -> TypeOpInfos
def addMissingFromTerm (bspc, spc, ignore?, term, minfo) =
  let def amt (t, minfo) = addMissingFromTerm   (bspc, spc, ignore?, t, minfo) in
  let def ams (s, minfo) = addMissingFromType   (bspc, spc, ignore?, s, minfo) in
  let def amp (p, minfo) = addMissingFromPattern (bspc, spc, ignore?, p, minfo) in
  case term of
    | Apply      (t1, t2,      _) -> amt (t2, amt (t1, minfo))
    | Record     (fields,      _) -> foldl (fn (minfo, (_, t)) -> amt (t, minfo)) minfo fields
    | Bind       (_, vlist, t, _) -> let minfo = foldl (fn (minfo, (_, srt)) -> ams (srt, minfo)) minfo vlist in
                                     amt (t, minfo)
    | Let        (ptlist, t,   _) -> let minfo = foldl (fn (minfo, (p, t)) -> amp (p, amt (t, minfo))) minfo ptlist in
				     amt (t, minfo)
    | LetRec     (vtlist, t,   _) -> let minfo = foldl (fn (minfo, ( (id, srt), t)) -> ams (srt, amt (t, minfo))) minfo vtlist in
				     amt (t, minfo)
    | Var        ((id, srt),   _) -> ams (srt, minfo)
    | Lambda     (match,       _) -> foldl (fn (minfo, (p, t1, t2)) -> amt (t2, amt (t1, amp (p, minfo)))) minfo match
    | IfThenElse (t1, t2, t3,  _) -> amt (t3, amt (t2, amt (t1, minfo)))
    | Seq        (tl,          _) -> foldl (fn (minfo, t) -> amt (t, minfo)) minfo tl
    | TypedTerm  (t, s,        _) -> ams (s, amt (t, minfo))
    | Fun        (fun, srt,    _) ->
      (let minfo = ams (srt, minfo) in
         case fun of
           | Op (qid, _) ->
             if ignore? qid then 
               minfo 
             else
               (case findTheOp (spc, qid) of
                  | Some _ -> 
                    minfo
                  | _ -> case findTheOp (bspc, qid) of
                           | Some opinfo -> 
                             addOpInfo2TypeOpInfos (qid, opinfo, minfo)
                           | _ -> 
                             minfo)
           | _ -> minfo)
    | _ -> minfo


op addMissingFromPattern: Spec * Spec * (QualifiedId -> Bool) * MSPattern * TypeOpInfos -> TypeOpInfos
def addMissingFromPattern (bspc, spc, ignore?, pat, minfo) =
  let def amt (t, minfo) = addMissingFromTerm (bspc, spc, ignore?, t, minfo) in
  let def ams (s, minfo) = addMissingFromType (bspc, spc, ignore?, s, minfo) in
  let def amp (p, minfo) = addMissingFromPattern (bspc, spc, ignore?, p, minfo) in
  case pat of
    | AliasPat     (p1, p2,       _) -> amp (p2, amp (p1, minfo))
    | VarPat       ((_, srt),     _) -> ams (srt, minfo)
    | EmbedPat     (_, Some p, s, _) -> amp (p, ams (s, minfo))
    | EmbedPat     (_, None,   s, _) -> ams (s, minfo)
    | RecordPat    (fields,       _) -> foldl (fn (minfo, (_, p)) -> amp (p, minfo)) minfo fields
    | WildPat      (s,            _) -> ams (s, minfo)
    | QuotientPat  (p, qid, _,    _) -> let q = Base (qid, [], noPos) in amp (p, ams (q, minfo))
    | RestrictedPat(p, t,         _) -> amp (p, amt (t, minfo))
    | TypedPat     (p, s,         _) -> amp (p, ams (s, minfo))
    | _ -> minfo

end-spec
