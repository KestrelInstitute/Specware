Poly2Mono qualifying spec

import /Languages/MetaSlang/Specs/StandardSpec
import /Languages/MetaSlang/Specs/Environment
import SortOpInfos

op InstantiateHO.sortMatch (t1 : Type, t2 : Type, spc : Spec) : TyVarSubst 
op Java.sortId: MS.Sort -> Id

 (**
 * transform a polymorphic spec into a monomorphic by instantiating polymorphic sorts
 * and op definitions. For each instantiation of a polymorphic sort/term a corresponding sort/op
 * definition is introduced for the specific instantiation and the constructor/op name is changed
 * by appending the sortid of the instantiation.
 * e.g. List Nat
 * generated: sort ListNat = | ConsNat Nat * ListNat | NilNat
 * uses of the constructors are renamed accordingly.
 * The fullspc is the spc + the base spec; the full spec is need in order to generate the monomorphic
 * sorts/ops for builtin entities (e.g., Lists, Option, etc)
 * @param keepPolyMorphic? controls whether the polymorphic sorts and ops should be included in the
 * resulting spec or not. If keepPolyMorphic? is false, the resulting spec will be free of polymorphic
 * entities.
 *)
op poly2mono: Spec * Boolean -> Spec
def poly2mono (spc, keepPolyMorphic?) =
  poly2monoInternal (spc, keepPolyMorphic?, false) 

op poly2monoForSnark: Spec * Boolean -> Spec
def poly2monoForSnark (spc, keepPolyMorphic?) =
  poly2monoInternal (spc, keepPolyMorphic?, true) 

op poly2monoInternal: Spec * Boolean * Boolean -> Spec
def poly2monoInternal (spc, keepPolyMorphic?, modifyConstructors?) =
  let def processSortinfo (Qualified(q,id), info, sortmap, minfo) =
        let pos = sortAnn info.dfn in
	let (old_decls, old_defs) = sortInfoDeclsAndDefs info in
	let (new_defs, minfo) =
	    foldl (fn ((defs, minfo),def0) ->
		   let (tvs, srt) = unpackSort def0 in
		   let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
		   let ndef = maybePiSort (tvs, srt) in
		   let defs = defs ++ [ndef] in
		   %let minfo = concat (minfo, minfo0) in
		   (defs, minfo)) 
		  ([]:List Sort, minfo) 
		  old_defs
	in
	let dfn = maybeAndSort (old_decls ++ new_defs, pos) in
	(insertAQualifierMap (sortmap, q, id, info << {dfn = dfn}), 
	 minfo)

      def processOpinfo (Qualified(q,id), info, opmap, minfo) =
	let pos = termAnn info.dfn in
	let (tvs, srt, _) = unpackFirstOpDef info in
	let (old_decls, old_defs) = opInfoDeclsAndDefs info in
	let (new_decls_and_defs, minfo) =
	    foldl (fn ((defs, minfo),def0) ->
		   let (tvs, srt, trm) = unpackFirstTerm def0 in
		   let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
		   let (trm, minfo) = p2mTerm (spc, modifyConstructors?, trm, minfo) in
		   let ndef = maybePiTerm (tvs, SortedTerm (trm, srt, termAnn def0)) in
		   let defs = defs ++ [ndef] in
		   %let minfo = concat (minfo, minfo0) in
		   (defs, minfo)) 
		  ([], minfo) 
		  (old_decls ++ old_defs)
	in
	let dfn = maybeAndTerm (new_decls_and_defs, pos) in
	(insertAQualifierMap (opmap, q, id, info << {dfn = dfn}), 
	 minfo)
  in
  let def modElts(elts,minfo,ops,srts) =
        List.foldl (fn ((r_elts,minfo,ops,srts),el) ->
	       case el of
		 | Sort (qid,_) ->
		   let Some sortinfo = findTheSort(spc,qid) in
		   let (srts,new_minfo) = processSortinfo(qid,sortinfo,srts,minfo) in
		   let el_s = if keepPolyMorphic? || firstSortDefTyVars sortinfo = []
		               then [el] else []
		   in
		   incorporateMinfo(r_elts,el_s,new_minfo,minfo,ops,srts)
		 | SortDef (qid,_) ->
		   let Some sortinfo = findTheSort(spc,qid) in
		   let (srts,new_minfo) = processSortinfo(qid,sortinfo,srts,minfo) in
		   let el_s = if keepPolyMorphic? || firstSortDefTyVars sortinfo = []
		               then [el] else []
		   in
		   incorporateMinfo(r_elts,el_s,new_minfo,minfo,ops,srts)
		 | Op (qid,def?,_) ->
		   (case findTheOp (spc, qid) of
		     | Some opinfo ->
		       let (ops,new_minfo) = processOpinfo(qid,opinfo,ops,minfo) in
		       let el_s = if keepPolyMorphic? || firstOpDefTyVars opinfo = []
				    then [el] else []
		       in
			 incorporateMinfo(r_elts,el_s,new_minfo,minfo,ops,srts)
		     | _ ->
		       let infos = findAllOps (spc, qid) in
		       fail ("Cannot find " ^ printQualifiedId qid ^ 
			     "but could find " ^ (foldl (fn (s,info) -> s ^ " " ^ printAliases info.names) "" infos) ^
			     "\nin spec\n" ^ printSpec spc))
		 | OpDef (qid,_,_) ->
		   let Some opinfo = findTheOp(spc,qid) in
		   let (ops,new_minfo) = processOpinfo(qid,opinfo,ops,minfo) in
		   let el_s = if keepPolyMorphic? || firstOpDefTyVars opinfo = []
		               then [el] else []
		   in
		   incorporateMinfo(r_elts,el_s,new_minfo,minfo,ops,srts)
		 | Property(ptype, pname, tv, t, pos) ->
		   let (t, new_minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
		   let nprop = Property(ptype, pname, tv, t, pos) in
		   incorporateMinfo(r_elts,[nprop],new_minfo,minfo,ops,srts)
		 | Import(s_tm,i_sp,elts,pos) ->
		   let (i_elts,minfo,ops,srts) = modElts(elts,minfo,ops,srts) in
		   (Cons(Import(s_tm,i_sp,reverse i_elts,pos),r_elts),minfo,ops,srts)
		 | _ -> (Cons(el,r_elts), minfo,ops,srts))
          ([],minfo,ops,srts) elts
  in
  let (elts, minfo, ops, srts) = modElts(spc.elements,emptyMonoInfo,spc.ops,spc.sorts) in
  let elts = reverse elts in
  let srts = foldl (fn (map, info) -> 
		    let Qualified (q, id) = primarySortName info in
		    insertAQualifierMap (map, q, id, info))
                   srts 
		   minfo.sorts
  in
  let ops = foldl (fn (map,info) -> 
		   let Qualified (q, id) = primaryOpName info in
		   insertAQualifierMap (map, q, id, info))
                  ops 
		  minfo.ops
  in
  % remove polymorphic sort/op defs (disabled)
  let srts = (if keepPolyMorphic? then 
		srts 
	      else 
		foldriAQualifierMap
		  (fn (q, id, info, map) ->
		   if q = "Accord" && id = "Update" then
		     insertAQualifierMap (map, q, id, info)
		   else
		   case firstSortDefTyVars info of
		     | [] -> insertAQualifierMap (map, q, id, info)
		     | _ -> map)
		  emptyASortMap 
		  srts)
  in
  let ops = (if keepPolyMorphic? then 
	       ops 
	     else
	       foldriAQualifierMap
	         (fn (q, id, info, map) ->
		  case firstOpDefTyVars info of
		    | [] -> insertAQualifierMap (map, q, id, info)
		    | _ -> map)
		 emptyAOpMap 
		 ops)
  in
  let spc = setSorts    (spc, srts) in
  let spc = setOps      (spc, ops)  in
  let spc = setElements (spc, elts) in
  spc

op p2mSort: Spec * Boolean * MS.Sort * SortOpInfos -> MS.Sort * SortOpInfos
def p2mSort (spc, modifyConstructors?, srt, minfo) =
  case srt of
    | Base (qid0 as Qualified (q, id), insttv as _::_, b) ->
      %% We are trying to simplify instances of polymorphic sorts where
      %% all the type vars have been instantitated.
      if q = "Accord" && (id = "ProcType" || id = "Update") then 
	%% Process the args to ProcType or Update, but leave the
	%% main type as ProcType or Update.  These types control
	%% later Accord processing and are eliminated by Accord
	%% once their usefulness is over.
	let (new_args,minfo) = 
	    foldl (fn ((new_args,minfo),srt) -> 
		   let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
		   (new_args ++ [srt], minfo))
	          ([], minfo)
		  insttv
	in
	let new_srt =  Base (qid0, new_args, b) in
	(new_srt, minfo) 
      else
      if exists? (fn (TyVar _) -> true | s -> false) insttv then (srt, minfo) else
      let suffix = getSortNameSuffix insttv in
      let qid = Qualified (q, id^suffix) in
      %let _ = writeLine ("instantiated Sort: "^printQualifiedId qid) in
      let minfo = 
          if monoInfosContainSort? (qid, minfo) then 
	    minfo
	  else
	    case findTheSort (spc, qid0) of
	      | Some info ->
	        let names = info.names in
	        let (tvs, srtdef) = unpackFirstSortDef info in
	        (case (tvs, srtdef) of
		  | (_::_, Any _) ->
		    %DAC:  Added this case for uninterpreted types.  After looking at the
		    % code below for the interpreted case I am not sure this is the right
		    % thing to do for code-generation, because in the above code, care is
		    % to exchange the srt definition types for the original types.
		    % However, this case is needed for the Snark translator and to ensure
		    % that the resulting spec is a valid metaslang spec.
		    if modifyConstructors? then % using modifyConstructors? as synonym for "for snark, but not for codeGen"
		      let tvsubst = zip (tvs, insttv) in
		      %let _ = writeLine ("  "^ (printTyVarSubst tvsubst)) in
		      let names = Cons (qid, (filter (fn qid1 -> qid1 ~= qid0) names)) in 
		      let sinfo = {names = names, 
				   dfn   = Any noPos} 
		      in
		      let minfo = addSortInfo2SortOpInfos (qid, sinfo, minfo) in
		      minfo
		    else 
		      minfo
		  | (_::_, _) ->
		    let tvsubst = zip (tvs, insttv) in
		    %let _ = writeLine ("  "^ (printTyVarSubst tvsubst)) in
		    let names = Cons (qid, (filter (fn qid1 -> qid1 ~= qid0) names)) in 
		    let srtdef = applyTyVarSubst2Sort (srtdef, tvsubst) in
		    let srtdef = (if modifyConstructors? then
				    addSortSuffixToConstructors (srtdef, suffix)
				  else 
				    srtdef)
		    in
		    %let _ = writeLine ("after applyTyVarSubst2Sort: "^printSort srtdef) in
		    % add it first to prevent infinite loop:
		    let tmp_sinfo = {names = names, 
				     dfn   = srtdef}
		    in
		    let minfo = addSortInfo2SortOpInfos (qid, tmp_sinfo, minfo) in
		    let (srtdef, minfo) = p2mSort (spc, modifyConstructors?, srtdef, minfo) in
		    %let _ = writeLine ("after p2mSort: "^printSort srtdef) in
		    let sinfo = {names = names, 
				 dfn   = srtdef}
		    in
		    let minfo = exchangeSortInfoInSortOpInfos (qid, sinfo, minfo) in
		    minfo
		  | _ -> minfo)
	      | _ -> minfo
      in
	 (Base (qid, [], b), minfo)
    | Boolean _ -> (srt, minfo) 
    | Arrow (srt1, srt2, b) ->
      let (srt1, minfo) = p2mSort (spc, modifyConstructors?, srt1, minfo) in
      let (srt2, minfo) = p2mSort (spc, modifyConstructors?, srt2, minfo) in
      (Arrow (srt1, srt2, b), minfo)
    | Product (fields, b) ->
      let (fields, minfo) = foldl (fn ((fields, minfo),(id, srt)) ->
				  let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
				  (fields ++ [(id, srt)], minfo))
                                  ([], minfo) fields
      in
      (Product (fields, b), minfo)
    | CoProduct (fields, b) ->
      let (fields, minfo) = foldl (fn ((fields, minfo),(id, optsrt)) ->
				  let (optsrt, minfo) = (case optsrt of
							  | None -> (None, minfo)
							  | Some srt ->
							    let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
							    (Some srt, minfo))
				  in
				  (fields ++ [(id, optsrt)], minfo))
                                  ([], minfo) fields
      in
      (CoProduct (fields, b), minfo)
    | Quotient (srt, t, b) ->
      let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
      let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
      (Quotient (srt, t, b), minfo)
    | Subsort (srt, t, b) ->
      let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
      let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
      (Subsort (srt, t, b), minfo)
    | _ -> (srt, minfo)

op p2mTerm: Spec * Boolean * MS.Term * SortOpInfos -> MS.Term * SortOpInfos
def p2mTerm (spc, modifyConstructors?, term, minfo) =
  case term of
    | Apply (t1, t2, b) ->
      let (t1, minfo) = p2mTerm (spc, modifyConstructors?, t1, minfo) in
      let (t2, minfo) = p2mTerm (spc, modifyConstructors?, t2, minfo) in
      (Apply (t1, t2, b), minfo)
    | Bind (binder, varlist, t, b) ->
      let (varlist, minfo) = foldl (fn ((varlist, minfo),(id, srt)) ->
				   let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
				   (varlist ++ [(id, srt)], minfo))
                                  ([], minfo) varlist
      in
      let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
      (Bind (binder, varlist, t, b), minfo)
    | Record (fields, b) ->
      let (fields, minfo) = foldl (fn ((fields, minfo),(id, t)) ->
				   let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
				   (fields ++ [(id, t)], minfo))
                            ([], minfo) fields
      in
      (Record (fields, b), minfo)
    | Let (patTerms, t, b) ->
      let (patTerms, minfo) = foldl (fn ((patTerms, minfo),(pat, t)) ->
				    let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
				    let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
				    (patTerms ++ [(pat, t)], minfo))
                             ([], minfo) patTerms
      in
      let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
      (Let (patTerms, t, b), minfo)
    | LetRec (varTerms, t, b) ->
      let (varTerms, minfo) = foldl (fn ((varTerms, minfo),((id, srt), t)) ->
				    let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
				    let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
				    (varTerms ++ [((id, srt), t)], minfo))
                             ([], minfo) varTerms
      in
      let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
      (LetRec (varTerms, t, b), minfo)
    | Var ((id, srt), b) ->
      let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
      (Var ((id, srt), b), minfo)
    | Fun (fun, srt, b) -> 
      let (fun, srt, minfo) = p2mFun (spc, modifyConstructors?, fun, srt, minfo) in
      (Fun (fun, srt, b), minfo)
    | Lambda (match, b) ->
      let (match, minfo) = foldl (fn ((match, minfo),(pat, t1, t2)) ->
				    let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
				    let (t1, minfo) = p2mTerm (spc, modifyConstructors?, t1, minfo) in
				    let (t2, minfo) = p2mTerm (spc, modifyConstructors?, t2, minfo) in
				    (match ++ [(pat, t1, t2)], minfo))
                             ([], minfo) match
      in
      (Lambda (match, b), minfo)
    | IfThenElse (t1, t2, t3, b) ->
      let (t1, minfo) = p2mTerm (spc, modifyConstructors?, t1, minfo) in
      let (t2, minfo) = p2mTerm (spc, modifyConstructors?, t2, minfo) in
      let (t3, minfo) = p2mTerm (spc, modifyConstructors?, t3, minfo) in
      (IfThenElse (t1, t2, t3, b), minfo)
    | Seq (terms, b) ->
      let (terms, minfo) = foldl (fn ((terms, minfo),t) ->
				  let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
				  (terms ++ [t], minfo))
                             ([], minfo) terms
      in
      (Seq (terms, b), minfo)
    | SortedTerm (t, srt, b) ->
      let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
      let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
      (SortedTerm (t, srt, b), minfo)
    | _ -> (term, minfo)

op p2mPattern: Spec * Boolean * Pattern * SortOpInfos -> Pattern * SortOpInfos
def p2mPattern (spc, modifyConstructors?, pat, minfo) =
  case pat of
    | EmbedPat (id, optPat, srt, b) ->
      %% Given "| Foo List (Nat)", we might convert to "| Foo_Nat List_Nat"
      let id = (case srt of
		  | Base (_, insttv as _::_, _) ->
		    if exists? (fn (TyVar _) -> true | s -> false) insttv then 
		      id 
		    else if modifyConstructors? then 
		      id^ (getSortNameSuffix insttv)
		    else 
		      id
		 %| Boolean is same as default case
		  | _ -> id)
      in
      let (optPat, minfo) = 
          case optPat of
	    | None -> (None, minfo)
	    | Some pat ->
	      let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
	      (Some pat, minfo)
      in
      let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
      (EmbedPat (id, optPat, srt, b), minfo)
    | AliasPat (pat1, pat2, b) ->
      let (pat1, minfo) = p2mPattern (spc, modifyConstructors?, pat1, minfo) in
      let (pat2, minfo) = p2mPattern (spc, modifyConstructors?, pat2, minfo) in
      (AliasPat (pat1, pat2, b), minfo)
    | VarPat ((id, srt), b) ->
      let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
      (VarPat ((id, srt), b), minfo)
    | WildPat (srt, b) ->
      let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
      (WildPat (srt, b), minfo)
    | RecordPat (fields, b) ->
      let (fields, minfo) = 
          foldl (fn ((fields, minfo), (id, pat)) ->
		 let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
		 (fields ++ [(id, pat)], minfo))
	        ([], minfo) 
		fields
      in
      (RecordPat (fields, b), minfo)
    | QuotientPat (pat, qid, b) ->
      let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
      (QuotientPat (pat, qid, b), minfo)
    | RestrictedPat (pat, t, b) ->
      let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
      let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
      (RestrictedPat (pat, t, b), minfo)
    | SortedPat (pat, s, b) ->
      let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
      let (s, minfo) = p2mSort (spc, modifyConstructors?, s, minfo) in
      (SortedPat (pat, s, b), minfo)
    | _ -> (pat, minfo)

op p2mFun: Spec * Boolean * Fun * MS.Sort * SortOpInfos -> Fun * MS.Sort * SortOpInfos
def p2mFun (spc, modifyConstructors?, fun, srt, minfo) =
  let (srt1, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
  case fun of
    | Embed (id, b?) ->
      %let _ = writeLine ("constructor "^id^" found.") in
      let cpsrt = (case srt of
		     | Arrow (_, srt, _) -> srt
		     | _ -> srt)
      in
      let cpsrt = unfoldBeforeCoProduct(spc, cpsrt) in
      (case cpsrt of
	| Base (sqid, insttv as _::_, _) ->
          %% constructor Cons could become Cons_Nat for List (Nat), etc.
	  if exists? (fn (TyVar _) -> true | s -> false) insttv then (fun, srt1, minfo) else
	  let id2 = id ^ (getSortNameSuffix insttv) in
	  let fun = Embed (if modifyConstructors? then id2 else id, b?) in
	  (fun, srt1, minfo)
       %| Boolean is same as default case
	| _ -> (fun, srt1, minfo))

    | Embedded (id) ->
      %let _ = writeLine ("constructor pred "^id^" found.") in
      let cpsrt = (case srt of
		     | Arrow (srt, _, _) -> srt
		     | _ -> srt)
      in
      let cpsrt = unfoldBeforeCoProduct(spc, cpsrt) in
      %let _ = writeLine("Constuctor pred sort: "^printSort(cpsrt)) in
      (case cpsrt of
	| Base (sqid, insttv as _::_, _) ->
          %% constructor Cons could become Cons_Nat for List (Nat), etc.
	  if exists? (fn (TyVar _) -> true | s -> false) insttv then (fun, srt1, minfo) else
	  let id2 = id ^ (getSortNameSuffix insttv) in
	  let fun = Embedded (if modifyConstructors? then id2 else id) in
	  %let _ = writeLine("Generated: "^ printTerm(mkEmbedded(id2, srt1))) in
	  (fun, srt1, minfo)
       %| Boolean is same as default case
	| _ -> (fun, srt1, minfo))

    | Op (qid as Qualified (q, id), fix) ->
      (case AnnSpec.findTheOp (spc, qid) of
	 | None -> (fun, srt1, minfo)
	 | Some info ->
	   (let (mtvs, asrt, term) = unpackFirstOpDef info in
	    if definedOpInfo? info then
	      %let _ = writeLine ("polymorphic op found: "^printQualifiedId qid) in
	      let tvsubst0 = sortMatch (asrt, srt, spc) in
	      let tvsubst = filter (fn (id, TyVar _) -> false | _ -> true) tvsubst0 in
	      if tvsubst = [] then 
		(fun, srt1, minfo) 
	      else
		let ntvs = map (fn (id, _) -> id) (filter (fn (id, TyVar _) -> true | _ -> false) tvsubst0) in
		let nqid = Qualified (q, id ^ getSortNameFromTyVarSubst tvsubst) in
		let names = Cons (nqid, (filter (fn qid0 -> qid0 ~= qid) info.names)) in
		%let _ = writeLine ("  New op name:"^ (printQualifiedId nqid)) in
		%let _ = writeLine ("  "^ (printTyVarSubst tvsubst)) in
		let nfun = Op (nqid, fix) in
		let minfo = 
		    if monoInfosContainOp? (nqid, minfo) then 
		      minfo
		    else
		      % construct the new opinfo
		      let term = applyTyVarSubst2Term (term, tvsubst) in
		      %let _ = writeLine ("substituted op term[1]: "^printTerm (term)) in
		      let dfn = maybePiTerm (mtvs, SortedTerm (Any noPos, srt1, noPos)) in
		      let tmp_opinfo = info << {names = names, dfn = dfn} in
		      let tmp_minfo = addOpInfo2SortOpInfos (nqid, tmp_opinfo, minfo) in
		      let (term, minfo) = p2mTerm (spc, modifyConstructors?, term, tmp_minfo) in
		      %let _ = writeLine ("substituted op term[2]: "^printTerm (term)) in
		      let dfn = maybePiTerm (ntvs, SortedTerm (term, srt1, termAnn term)) in
		      let nopinfo = info << {names = names, dfn = dfn} in
		      %let _ = writeLine ("adding new opinfo for "^id^" with "^natToString (length (ntvs))^" tyvars...") in
		      let minfo = exchangeOpInfoInSortOpInfos (nqid, nopinfo, minfo) in
		      %let _ = writeLine (printSortOpInfos minfo) in
		      minfo
		in
		  (nfun, srt1, minfo)
	    else
	      if modifyConstructors? then % using modifyConstructors? as synonym for "for snark, but not for codeGen"
		%let _ = writeLine ("polymorphic op found: "^printQualifiedId qid) in
		let tvsubst0 = sortMatch (asrt, srt, spc) in
		let tvsubst = filter (fn (id, TyVar _) -> false | _ -> true) tvsubst0 in
		if tvsubst = [] then 
		  (fun, srt1, minfo)
		else
		  let ntvs = map (fn (id, _) -> id) (filter (fn (id, TyVar _) -> true | _ -> false) tvsubst0) in
		  let nqid = Qualified (q, id ^ getSortNameFromTyVarSubst tvsubst) in
		  let names = Cons (nqid, (filter (fn qid0 -> qid0 ~= qid) info.names)) in
		  %let _ = writeLine ("  New op name:"^ (printQualifiedId nqid)) in
		  %let _ = writeLine ("  "^ (printTyVarSubst tvsubst)) in
		  let nfun = Op (nqid, fix) in
		  let minfo = 
		      if monoInfosContainOp? (nqid, minfo) then 
			minfo
		      else
			% construct the new opinfo
			let dfn = maybePiTerm (mtvs, SortedTerm (Any noPos, srt1, noPos)) in
			let tmp_opinfo = info << {names = names, dfn = dfn} in
			let minfo = addOpInfo2SortOpInfos (nqid, tmp_opinfo, minfo) in
			% let nopinfo = info << {typ = (ntvs, srt1)} in
			%let _ = if id = "empty_seq" then writeLine ("adding new opinfo for "^id^" with "^natToString (length (ntvs))^" tyvars...") else () in
			%let _ = if id = "empty_seq" then writeLine (printSortOpInfos minfo) else () in
			minfo
		  in
		    (nfun, srt1, minfo)
	      else 
		(fun, srt1, minfo))
	 | _ -> (fun, srt1, minfo))

   %| Not/And/Or/Implies/Equals/NotEquals are all same as default
    | _ -> (fun, srt1, minfo)

op  incorporateMinfo: SpecElements * SpecElements * SortOpInfos * SortOpInfos * OpMap * SortMap
       -> SpecElements * SortOpInfos * OpMap * SortMap
%% Add newly added ops and sorts to elts before el (note elts are in reverse of their final order)
def incorporateMinfo(elts,el_s,
		     new_minfo as {ops = new_ops,sorts = new_sorts},
		     old_minfo as {ops = old_ops,sorts = old_sorts},
		     ops,srts) =
  let def newSorts(new_sorts) =
        if new_sorts = old_sorts then []
	  else let srtinfo :: r_sorts = new_sorts in
	       let qid = primarySortName srtinfo in
	       Cons(SortDef (qid,noPos),newSorts r_sorts)
      def newOps(new_ops) =
        if new_ops = old_ops then []
	  else let opinfo :: r_ops = new_ops in
	       let qid = primaryOpName opinfo in
               Cons(OpDef (qid, 0, noPos), 
                    Cons(Op (qid,false,noPos), % false means don't print def as part of decl
                         newOps r_ops))
  in
    (el_s ++ newOps new_ops ++ newSorts new_sorts ++ elts,
     new_minfo,ops,srts)
  
op getSortNameFromTyVarSubst: TyVarSubst -> String
def getSortNameFromTyVarSubst (subst) =
  getSortNameSuffix (map (fn (_, srt) -> srt) subst)

op getSortNameSuffix: List Sort -> String
def getSortNameSuffix (instlist) =
  case instlist of
    | [] -> ""
    | srt::instlist -> "_" ^ (sortId srt)^ (getSortNameSuffix instlist)

op applyTyVarSubst2Term: MS.Term * TyVarSubst -> MS.Term
def applyTyVarSubst2Term (trm, subst) =
  let def inst srt = instantiateTyVars (srt, subst) in
  mapTerm (id, inst, id) trm

op applyTyVarSubst2Sort: MS.Sort * TyVarSubst -> MS.Sort
def applyTyVarSubst2Sort (srt, subst) =
  let def inst srt = instantiateTyVars (srt, subst) in
  mapSort (id, inst, id) srt

op addSortSuffixToConstructors: MS.Sort * String -> MS.Sort
def addSortSuffixToConstructors (srt, suffix) =
  case srt of
    | CoProduct (fields, b) ->
      let fields = map (fn (id, optsrt) -> (id^suffix, optsrt)) fields in
      CoProduct (fields, b)
    | _ -> srt

end-spec
