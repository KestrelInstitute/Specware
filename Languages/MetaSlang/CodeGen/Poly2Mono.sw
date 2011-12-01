Poly2Mono qualifying spec

import /Languages/MetaSlang/Specs/StandardSpec
import /Languages/MetaSlang/Specs/Environment
import TypeOpInfos

op InstantiateHO.typeMatch (t1 : MSType, t2 : MSType, spc : Spec) : TyVarSubst 
op Java.typeId: MSType -> Id

 (**
 * transform a polymorphic spec into a monomorphic by instantiating polymorphic types
 * and op definitions. For each instantiation of a polymorphic type/term a corresponding type/op
 * definition is introduced for the specific instantiation and the constructor/op name is changed
 * by appending the typeid of the instantiation.
 * e.g. List Nat
 * generated: type ListNat = | ConsNat Nat * ListNat | NilNat
 * uses of the constructors are renamed accordingly.
 * The fullspc is the spc + the base spec; the full spec is need in order to generate the monomorphic
 * types/ops for builtin entities (e.g., Lists, Option, etc)
 * @param keepPolyMorphic? controls whether the polymorphic types and ops should be included in the
 * resulting spec or not. If keepPolyMorphic? is false, the resulting spec will be free of polymorphic
 * entities.
 *)
op poly2monoAndDropPoly (spc : Spec) : Spec =
 poly2mono (spc, false)

op poly2mono: Spec * Bool -> Spec
def poly2mono (spc, keepPolyMorphic?) =
  poly2monoInternal (spc, keepPolyMorphic?, false) 

op poly2monoForSnark: Spec * Bool -> Spec
def poly2monoForSnark (spc, keepPolyMorphic?) =
  poly2monoInternal (spc, keepPolyMorphic?, true) 

op poly2monoInternal: Spec * Bool * Bool -> Spec
def poly2monoInternal (spc, keepPolyMorphic?, modifyConstructors?) =
  let def processTypeinfo (Qualified(q,id), info, typemap, minfo) =
        let pos = typeAnn info.dfn in
	let (old_decls, old_defs) = typeInfoDeclsAndDefs info in
	let (new_defs, minfo) =
	    foldl (fn ((defs, minfo),def0) ->
		   let (tvs, srt) = unpackType def0 in
		   let (srt, minfo) = p2mType (spc, modifyConstructors?, srt, minfo) in
		   let ndef = maybePiType (tvs, srt) in
		   let defs = defs ++ [ndef] in
		   %let minfo = concat (minfo, minfo0) in
		   (defs, minfo)) 
		  ([]:MSTypes, minfo) 
		  old_defs
	in
	let dfn = maybeAndType (old_decls ++ new_defs, pos) in
	(insertAQualifierMap (typemap, q, id, info << {dfn = dfn}), 
	 minfo)

      def processOpinfo (Qualified(q,id), info, opmap, minfo) =
	let pos = termAnn info.dfn in
	let (tvs, srt, _) = unpackFirstOpDef info in
	let (old_decls, old_defs) = opInfoDeclsAndDefs info in
	let (new_decls_and_defs, minfo) =
	    foldl (fn ((defs, minfo),def0) ->
		   let (tvs, srt, trm) = unpackFirstTerm def0 in
		   let (srt, minfo) = p2mType (spc, modifyConstructors?, srt, minfo) in
		   let (trm, minfo) = p2mTerm (spc, modifyConstructors?, trm, minfo) in
		   let ndef = maybePiTerm (tvs, TypedTerm (trm, srt, termAnn def0)) in
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
		 | Type (qid,_) ->
                   (case findTheType(spc,qid) of
                      | Some typeinfo ->
                        let (srts,new_minfo) = processTypeinfo(qid,typeinfo,srts,minfo) in
                        let el_s = if keepPolyMorphic? || firstTypeDefTyVars typeinfo = []
                                     then [el] else []
                        in
                         incorporateMinfo(r_elts,el_s,new_minfo,minfo,ops,srts)
                      | _ ->
                        % let infos = findAllTypes (spc, qid) in
                        % let _ = writeLine ("Cannot find type " ^ printQualifiedId qid ^ ", but could find " ^ (foldl (fn (s, info) -> s ^ " " ^ printAliases info.names) "" infos)) in
                        (r_elts, minfo, ops, srts))
		 | TypeDef (qid,_) ->
                   (case findTheType(spc,qid) of
                      | Some typeinfo ->
                        let (srts,new_minfo) = processTypeinfo(qid,typeinfo,srts,minfo) in
                        let el_s = if keepPolyMorphic? || firstTypeDefTyVars typeinfo = []
                                     then [el] else []
                        in
                        incorporateMinfo(r_elts,el_s,new_minfo,minfo,ops,srts)
                      | _ ->
                        % let infos = findAllTypes (spc, qid) in
                        % let _ = writeLine ("Cannot find type " ^ printQualifiedId qid ^ ", but could find " ^ (foldl (fn (s, info) -> s ^ " " ^ printAliases info.names) "" infos)) in
                        (r_elts, minfo, ops, srts))

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
                       % let _ = writeLine ("Cannot find " ^ printQualifiedId qid ^ ", but could find " ^ (foldl (fn (s,info) -> s ^ " " ^ printAliases info.names) "" infos) ^ "\nin spec\n" ^ printSpec spc) in
                       (r_elts, minfo, ops, srts))
		 | OpDef (qid,_,_) ->
                   (case findTheOp(spc,qid) of
                      | Some opinfo ->
                        let (ops,new_minfo) = processOpinfo(qid,opinfo,ops,minfo) in
                        let el_s = if keepPolyMorphic? || firstOpDefTyVars opinfo = []
                                     then [el] else []
                        in
                        incorporateMinfo(r_elts,el_s,new_minfo,minfo,ops,srts)
                      | _ ->
		       let infos = findAllOps (spc, qid) in
                       % let _ = writeLine ("Cannot find " ^ printQualifiedId qid ^ ", but could find " ^ (foldl (fn (s,info) -> s ^ " " ^ printAliases info.names) "" infos) ^ "\nin spec\n" ^ printSpec spc) in
                       (r_elts, minfo, ops, srts))
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
  let (elts, minfo, ops, srts) = modElts(spc.elements,emptyMonoInfo,spc.ops,spc.types) in
  let elts = reverse elts in
  let srts = foldl (fn (map, info) -> 
		    let Qualified (q, id) = primaryTypeName info in
		    insertAQualifierMap (map, q, id, info))
                   srts 
		   minfo.types
  in
  let ops = foldl (fn (map,info) -> 
		   let Qualified (q, id) = primaryOpName info in
		   insertAQualifierMap (map, q, id, info))
                  ops 
		  minfo.ops
  in
  % remove polymorphic type/op defs (disabled)
  let srts = (if keepPolyMorphic? then 
		srts 
	      else 
		foldriAQualifierMap
		  (fn (q, id, info, map) ->
		   if q = "Accord" && id = "Update" then
		     insertAQualifierMap (map, q, id, info)
		   else
		   case firstTypeDefTyVars info of
		     | [] -> insertAQualifierMap (map, q, id, info)
		     | _ -> map)
		  emptyATypeMap 
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
  let spc = setTypes    (spc, srts) in
  let spc = setOps      (spc, ops)  in
  let spc = setElements (spc, elts) in
  spc

op p2mType: Spec * Bool * MSType * TypeOpInfos -> MSType * TypeOpInfos
def p2mType (spc, modifyConstructors?, srt, minfo) =
  case srt of
    | Base (qid0 as Qualified (q, id), insttv as _::_, b) ->
      %% We are trying to simplify instances of polymorphic types where
      %% all the type vars have been instantitated.
      if q = "Accord" && (id = "ProcType" || id = "Update") then 
	%% Process the args to ProcType or Update, but leave the
	%% main type as ProcType or Update.  These types control
	%% later Accord processing and are eliminated by Accord
	%% once their usefulness is over.
	let (new_args,minfo) = 
	    foldl (fn ((new_args,minfo),srt) -> 
		   let (srt, minfo) = p2mType (spc, modifyConstructors?, srt, minfo) in
		   (new_args ++ [srt], minfo))
	          ([], minfo)
		  insttv
	in
	let new_srt =  Base (qid0, new_args, b) in
	(new_srt, minfo) 
      else
      if exists? (fn (TyVar _) -> true | s -> false) insttv then (srt, minfo) else
      let suffix = getTypeNameSuffix insttv in
      let qid = Qualified (q, id^suffix) in
      %let _ = writeLine ("instantiated Type: "^printQualifiedId qid) in
      let minfo = 
          if monoInfosContainType? (qid, minfo) then 
	    minfo
	  else
	    case findTheType (spc, qid0) of
	      | Some info ->
	        let names = info.names in
	        let (tvs, srtdef) = unpackFirstTypeDef info in
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
		      let minfo = addTypeInfo2TypeOpInfos (qid, sinfo, minfo) in
		      minfo
		    else 
		      minfo
		  | (_::_, _) ->
		    let tvsubst = zip (tvs, insttv) in
		    %let _ = writeLine ("  "^ (printTyVarSubst tvsubst)) in
		    let names = Cons (qid, (filter (fn qid1 -> qid1 ~= qid0) names)) in 
		    let srtdef = applyTyVarSubst2Type (srtdef, tvsubst) in
		    let srtdef = (if modifyConstructors? then
				    addTypeSuffixToConstructors (srtdef, suffix)
				  else 
				    srtdef)
		    in
		    %let _ = writeLine ("after applyTyVarSubst2Type: "^printType srtdef) in
		    % add it first to prevent infinite loop:
		    let tmp_sinfo = {names = names, 
				     dfn   = srtdef}
		    in
		    let minfo = addTypeInfo2TypeOpInfos (qid, tmp_sinfo, minfo) in
		    let (srtdef, minfo) = p2mType (spc, modifyConstructors?, srtdef, minfo) in
		    %let _ = writeLine ("after p2mType: "^printType srtdef) in
		    let sinfo = {names = names, 
				 dfn   = srtdef}
		    in
		    let minfo = exchangeTypeInfoInTypeOpInfos (qid, sinfo, minfo) in
		    minfo
		  | _ -> minfo)
	      | _ -> minfo
      in
	 (Base (qid, [], b), minfo)
    | Boolean _ -> (srt, minfo) 
    | Arrow (srt1, srt2, b) ->
      let (srt1, minfo) = p2mType (spc, modifyConstructors?, srt1, minfo) in
      let (srt2, minfo) = p2mType (spc, modifyConstructors?, srt2, minfo) in
      (Arrow (srt1, srt2, b), minfo)
    | Product (fields, b) ->
      let (fields, minfo) = foldl (fn ((fields, minfo),(id, srt)) ->
				  let (srt, minfo) = p2mType (spc, modifyConstructors?, srt, minfo) in
				  (fields ++ [(id, srt)], minfo))
                                  ([], minfo) fields
      in
      (Product (fields, b), minfo)
    | CoProduct (fields, b) ->
      let (fields, minfo) = foldl (fn ((fields, minfo),(id, optsrt)) ->
				  let (optsrt, minfo) = (case optsrt of
							  | None -> (None, minfo)
							  | Some srt ->
							    let (srt, minfo) = p2mType (spc, modifyConstructors?, srt, minfo) in
							    (Some srt, minfo))
				  in
				  (fields ++ [(id, optsrt)], minfo))
                                  ([], minfo) fields
      in
      (CoProduct (fields, b), minfo)
    | Quotient (srt, t, b) ->
      let (srt, minfo) = p2mType (spc, modifyConstructors?, srt, minfo) in
      let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
      (Quotient (srt, t, b), minfo)
    | Subtype (srt, t, b) ->
      let (srt, minfo) = p2mType (spc, modifyConstructors?, srt, minfo) in
      let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
      (Subtype (srt, t, b), minfo)
    | _ -> (srt, minfo)

op p2mTerm: Spec * Bool * MSTerm * TypeOpInfos -> MSTerm * TypeOpInfos
def p2mTerm (spc, modifyConstructors?, term, minfo) =
  case term of
    | Apply (t1, t2, b) ->
      let (t1, minfo) = p2mTerm (spc, modifyConstructors?, t1, minfo) in
      let (t2, minfo) = p2mTerm (spc, modifyConstructors?, t2, minfo) in
      (Apply (t1, t2, b), minfo)
    | Bind (binder, varlist, t, b) ->
      let (varlist, minfo) = foldl (fn ((varlist, minfo),(id, srt)) ->
				   let (srt, minfo) = p2mType (spc, modifyConstructors?, srt, minfo) in
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
				    let (srt, minfo) = p2mType (spc, modifyConstructors?, srt, minfo) in
				    let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
				    (varTerms ++ [((id, srt), t)], minfo))
                             ([], minfo) varTerms
      in
      let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
      (LetRec (varTerms, t, b), minfo)
    | Var ((id, srt), b) ->
      let (srt, minfo) = p2mType (spc, modifyConstructors?, srt, minfo) in
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
    | TypedTerm (t, srt, b) ->
      let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
      let (srt, minfo) = p2mType (spc, modifyConstructors?, srt, minfo) in
      (TypedTerm (t, srt, b), minfo)
    | _ -> (term, minfo)

op p2mPattern: Spec * Bool * MSPattern * TypeOpInfos -> MSPattern * TypeOpInfos
def p2mPattern (spc, modifyConstructors?, pat, minfo) =
  case pat of
    | EmbedPat (id, optPat, srt, b) ->
      %% Given "| Foo List (Nat)", we might convert to "| Foo_Nat List_Nat"
      let id = (case srt of
		  | Base (_, insttv as _::_, _) ->
		    if exists? (fn (TyVar _) -> true | s -> false) insttv then 
		      id 
		    else if modifyConstructors? then 
		      id^ (getTypeNameSuffix insttv)
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
      let (srt, minfo) = p2mType (spc, modifyConstructors?, srt, minfo) in
      (EmbedPat (id, optPat, srt, b), minfo)
    | AliasPat (pat1, pat2, b) ->
      let (pat1, minfo) = p2mPattern (spc, modifyConstructors?, pat1, minfo) in
      let (pat2, minfo) = p2mPattern (spc, modifyConstructors?, pat2, minfo) in
      (AliasPat (pat1, pat2, b), minfo)
    | VarPat ((id, srt), b) ->
      let (srt, minfo) = p2mType (spc, modifyConstructors?, srt, minfo) in
      (VarPat ((id, srt), b), minfo)
    | WildPat (srt, b) ->
      let (srt, minfo) = p2mType (spc, modifyConstructors?, srt, minfo) in
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
    | TypedPat (pat, s, b) ->
      let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
      let (s, minfo) = p2mType (spc, modifyConstructors?, s, minfo) in
      (TypedPat (pat, s, b), minfo)
    | _ -> (pat, minfo)

op p2mFun: Spec * Bool * Fun * MSType * TypeOpInfos -> Fun * MSType * TypeOpInfos
def p2mFun (spc, modifyConstructors?, fun, srt, minfo) =
  let (srt1, minfo) = p2mType (spc, modifyConstructors?, srt, minfo) in
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
	  let id2 = id ^ (getTypeNameSuffix insttv) in
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
      %let _ = writeLine("Constuctor pred type: "^printType(cpsrt)) in
      (case cpsrt of
	| Base (sqid, insttv as _::_, _) ->
          %% constructor Cons could become Cons_Nat for List (Nat), etc.
	  if exists? (fn (TyVar _) -> true | s -> false) insttv then (fun, srt1, minfo) else
	  let id2 = id ^ (getTypeNameSuffix insttv) in
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
	      let tvsubst0 = typeMatch (asrt, srt, spc) in
	      let tvsubst = filter (fn (id, TyVar _) -> false | _ -> true) tvsubst0 in
	      if tvsubst = [] then 
		(fun, srt1, minfo) 
	      else
		let ntvs = map (fn (id, _) -> id) (filter (fn (id, TyVar _) -> true | _ -> false) tvsubst0) in
		let nqid = Qualified (q, id ^ getTypeNameFromTyVarSubst tvsubst) in
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
		      let dfn = maybePiTerm (mtvs, TypedTerm (Any noPos, srt1, noPos)) in
		      let tmp_opinfo = info << {names = names, dfn = dfn} in
		      let tmp_minfo = addOpInfo2TypeOpInfos (nqid, tmp_opinfo, minfo) in
		      let (term, minfo) = p2mTerm (spc, modifyConstructors?, term, tmp_minfo) in
		      %let _ = writeLine ("substituted op term[2]: "^printTerm (term)) in
		      let dfn = maybePiTerm (ntvs, TypedTerm (term, srt1, termAnn term)) in
		      let nopinfo = info << {names = names, dfn = dfn} in
		      %let _ = writeLine ("adding new opinfo for "^id^" with "^natToString (length (ntvs))^" tyvars...") in
		      let minfo = exchangeOpInfoInTypeOpInfos (nqid, nopinfo, minfo) in
		      %let _ = writeLine (printTypeOpInfos minfo) in
		      minfo
		in
		  (nfun, srt1, minfo)
	    else
	      if modifyConstructors? then % using modifyConstructors? as synonym for "for snark, but not for codeGen"
		%let _ = writeLine ("polymorphic op found: "^printQualifiedId qid) in
		let tvsubst0 = typeMatch (asrt, srt, spc) in
		let tvsubst = filter (fn (id, TyVar _) -> false | _ -> true) tvsubst0 in
		if tvsubst = [] then 
		  (fun, srt1, minfo)
		else
		  let ntvs = map (fn (id, _) -> id) (filter (fn (id, TyVar _) -> true | _ -> false) tvsubst0) in
		  let nqid = Qualified (q, id ^ getTypeNameFromTyVarSubst tvsubst) in
		  let names = Cons (nqid, (filter (fn qid0 -> qid0 ~= qid) info.names)) in
		  %let _ = writeLine ("  New op name:"^ (printQualifiedId nqid)) in
		  %let _ = writeLine ("  "^ (printTyVarSubst tvsubst)) in
		  let nfun = Op (nqid, fix) in
		  let minfo = 
		      if monoInfosContainOp? (nqid, minfo) then 
			minfo
		      else
			% construct the new opinfo
			let dfn = maybePiTerm (mtvs, TypedTerm (Any noPos, srt1, noPos)) in
			let tmp_opinfo = info << {names = names, dfn = dfn} in
			let minfo = addOpInfo2TypeOpInfos (nqid, tmp_opinfo, minfo) in
			% let nopinfo = info << {typ = (ntvs, srt1)} in
			%let _ = if id = "empty_seq" then writeLine ("adding new opinfo for "^id^" with "^natToString (length (ntvs))^" tyvars...") else () in
			%let _ = if id = "empty_seq" then writeLine (printTypeOpInfos minfo) else () in
			minfo
		  in
		    (nfun, srt1, minfo)
	      else 
		(fun, srt1, minfo))
	 | _ -> (fun, srt1, minfo))

   %| Not/And/Or/Implies/Equals/NotEquals are all same as default
    | _ -> (fun, srt1, minfo)

op  incorporateMinfo: SpecElements * SpecElements * TypeOpInfos * TypeOpInfos * OpMap * TypeMap
       -> SpecElements * TypeOpInfos * OpMap * TypeMap
%% Add newly added ops and types to elts before el (note elts are in reverse of their final order)
def incorporateMinfo(elts,el_s,
		     new_minfo as {ops = new_ops,types = new_types},
		     old_minfo as {ops = old_ops,types = old_types},
		     ops,srts) =
  let def newTypes(new_types) =
        if new_types = old_types then []
	  else let srtinfo :: r_types = new_types in
	       let qid = primaryTypeName srtinfo in
	       Cons(TypeDef (qid,noPos),newTypes r_types)
      def newOps(new_ops) =
        if new_ops = old_ops then []
	  else let opinfo :: r_ops = new_ops in
	       let qid = primaryOpName opinfo in
               Cons(OpDef (qid, 0, noPos), 
                    Cons(Op (qid,false,noPos), % false means don't print def as part of decl
                         newOps r_ops))
  in
    (el_s ++ newOps new_ops ++ newTypes new_types ++ elts,
     new_minfo,ops,srts)
  
op getTypeNameFromTyVarSubst: TyVarSubst -> String
def getTypeNameFromTyVarSubst (subst) =
  getTypeNameSuffix (map (fn (_, srt) -> srt) subst)

op getTypeNameSuffix: MSTypes -> String
def getTypeNameSuffix (instlist) =
  case instlist of
    | [] -> ""
    | srt::instlist -> "_" ^ (typeId srt)^ (getTypeNameSuffix instlist)

op applyTyVarSubst2Term: MSTerm * TyVarSubst -> MSTerm
def applyTyVarSubst2Term (trm, subst) =
  let def inst srt = instantiateTyVars (srt, subst) in
  mapTerm (id, inst, id) trm

op applyTyVarSubst2Type: MSType * TyVarSubst -> MSType
def applyTyVarSubst2Type (srt, subst) =
  let def inst srt = instantiateTyVars (srt, subst) in
  mapType (id, inst, id) srt

op addTypeSuffixToConstructors: MSType * String -> MSType
def addTypeSuffixToConstructors (srt, suffix) =
  case srt of
    | CoProduct (fields, b) ->
      let fields = map (fn (id, optsrt) -> (id^suffix, optsrt)) fields in
      CoProduct (fields, b)
    | _ -> srt

end-spec
