(**
 * this spec contains code generation related transformations that are performed
 * before the actual code generation step
 *)

CodeGenTransforms qualifying spec

import /Languages/MetaSlang/Specs/StandardSpec
import /Languages/MetaSlang/Transformations/InstantiateHOFns

% --------------------------------------------------------------------------------

% --------------------------------------------------------------------------------

op builtinSortOp: QualifiedId -> Boolean
def builtinSortOp (Qualified (q, i)) =
  %(q="Nat" && (i="Nat" || i="PosNat" || i="toString" || i="natToString" || i="show" || i="stringToNat"))
  %||
  ((q="Integer" || q="Nat" || q="PosNat") && (i="Integer" || i="NonZeroInteger" || i="+" || i="-" || i="*" || i="div" || i="rem" || i="<=" || i="<" || i="~" ||
		  i=">" || i=">=" || i="toString" || i="intToString" || i="show" || i="stringToInt"))
  % || (q="Boolean" && (i="Boolean" || i="true" || i="false" || i="~" || i="&&" || i="||" || i="=>" || i="<=>" || i="~="))
  ||
  (q="Char" && (i="Char" || i="chr" || i="isUpperCase" || i="isLowerCase" || i="isAlpha" ||
	       i="isNum" || i="isAlphaNum" || i="isAscii" || i="toUpperCase" || i="toLowerCase"))
  ||
  (q="String" && (i="String" || i="writeLine" || i="toScreen" || i="concat" || i="++" ||
		 i="^" || i="newline" || i="length" || i="substring"))

% --------------------------------------------------------------------------------
(**
 * identifies the int sorts with the Integer types; this makes sense, if the base spec is not part of the
 * code generation and treated as builtin unit
 *)
op identifyIntSorts: Spec -> Spec
def identifyIntSorts spc =
  let
    def identifyIntSort srt =
      case srt of
	| Base (Qualified (_ (*"Nat"*),     "Nat"),       [], b) -> Base (Qualified ("Integer", "Integer"), [], b)
	| Base (Qualified (_ (*"Nat"*),     "PosNat"),    [], b) -> Base (Qualified ("Integer", "Integer"), [], b)
	| Base (Qualified (_ (*"Integer"*), "NZInteger"), [], b) -> Base (Qualified ("Integer", "Integer"), [], b)
        % the following 6 lines actually do not belong here, they "repair" something that happens in PSL:
        % the qualifier of base types get lost. Thats also the reason why in the above lines the qualifier
        % is commented out
	| Base (Qualified ("String", "String"), _,  b) -> srt
	| Base (Qualified (s,        "String"), tv, b) -> Base (Qualified ("String", "String"), tv, b)
	| Base (Qualified ("Char",   "Char"),   _,  b) -> srt
	| Base (Qualified (s,        "Char"),   tv, b) -> Base (Qualified ("Char", "Char"), tv, b)
	| Base (Qualified ("List",   "List"),   _,  b) -> srt
	| Base (Qualified (s,        "List"),   tv, b) -> Base (Qualified ("List", "List"), tv, b)
	| _ -> srt
  in
  let termid = (fn t -> t) in
  let pattid = (fn p -> p) in
  mapSpec (termid, identifyIntSort, pattid) spc

% --------------------------------------------------------------------------------

(**
 * transforms "let _ = t1 in t2" into "(t1;t2)"
 *)
op letWildPatToSeq: Spec -> Spec
def letWildPatToSeq spc =
  let
    def lettoseq (t) =
      case t of
	| Let ([(WildPat _, t1)], t2, b) -> 
	  lettoseq (Seq ([t1, t2], b))
	| Seq ((Seq (terms0, _))::terms, b) ->
	  lettoseq (Seq (concat (terms0, terms), b))
	| _ -> t
  in
  let sortid = (fn s -> s) in
  let pattid = (fn p -> p) in
  mapSpec (lettoseq, sortid, pattid) spc


op unfoldSortAliases: Spec -> Spec
def unfoldSortAliases spc =
  let srts = sortsAsList spc in
  case find (fn (_, _, info) -> 
	     case sortInfoDefs info of
	       | srt :: _ -> 
	         (case sortInnerSort srt of
		    | Base (_, _, _) -> true
		    | _ -> false)
	       | _ -> false)
            srts 
   of
    | None -> spc
    | Some (q0, id0, info) ->
      let (tvs, srt) = unpackFirstSortDef info in
      let Base (qid, psrts, _) = srt in
      let qid0 = mkQualifiedId (q0, id0) in
      %let _ = writeLine ("sort alias found: "^printQualifiedId qid0^" = "^printQualifiedId qid) in
      let srts = filter (fn (q1, id1, _) -> ~((q1 = q0) && (id1 = id0))) srts in
      let sortmap = foldl (fn ((q, id, info), srtmap) ->
			   insertAQualifierMap (srtmap, q, id, info))
                          emptyASortMap
			  srts
      in
      let spc = setSorts (spc, sortmap) in
      let
        def mapSrt s =
	  case s of
	    | Base (qid2, srts, b) -> if qid2 = qid0 then 
				     Base (qid,  psrts, b)
				   else 
				     Base (qid2, srts,  b)
	    | _ -> s
      in
      let spc = mapSpec (id, mapSrt, id) spc in
      unfoldSortAliases spc

(**
 * looks in the spec for a user type matching the given sort; if a matching
 * user type exists.
 *)
op findMatchingUserTypeOption: Spec * Sort -> Option Sort
def findMatchingUserTypeOption (spc, srtdef) =
  case srtdef of
    | Base    _ -> Some srtdef
    | Boolean _ -> Some srtdef
    | _ ->
      let srts = sortsAsList spc in
      let srtPos = sortAnn srtdef in
      let foundSrt = find (fn (q, id, info) ->
			   case sortInfoDefs info of
			     | [srt] -> 
			       equalSort? (srtdef, sortInnerSort srt)
			     |_ -> false)
                          srts 
      in
	case foundSrt of
	  | Some (q, classId, _) -> 
            %let _ = writeLine("matching user type found: sort "^classId^" = "^printSort srtdef) in
            Some (Base (mkUnQualifiedId (classId), [], srtPos))
	  | None -> None
	    %let _ = writeLine ("no matching user type found for "^printSort srtdef) in
	    %srtdef

(**
 * looks in the spec for a user type matching the given sort; if a matching
 * user type exists, the corresponding sort will be returned, otherwise the sort
 * given as input itself will be returned
 *)
op findMatchingUserType: Spec * Sort -> Sort
def findMatchingUserType (spc, srt) =
  case findMatchingUserTypeOption (spc, srt) of
    | Some s -> s
    | None -> srt



(**
 * this op looks for record sort and tries to fold them using sort definition in the spec
 *)
op foldRecordSorts_internal: Spec -> Spec
def foldRecordSorts_internal spc =
  let
    def foldRecordSort srt =
      case srt of
	| Product _ -> findMatchingUserType (spc, srt)
	| _ -> srt
  in
    mapSpec (id, foldRecordSort, id) spc


op foldRecordSorts: Spec -> Spec
def foldRecordSorts spc =
  let
    def foldRecordSorts0 (spc, visited) =
      let srts = sortsAsList spc in
      case find (fn (q, i, info) -> 
		 case sortInfoDefs info of
		   | dfn :: _ -> 
		     (case sortInnerSort dfn of
			| Product _ -> ~(member (Qualified (q, i), visited))
			| _ -> false)
		   | _ -> false)
	        srts 
	of
	| None -> spc
	| Some (q0, id0, info) ->
	  let psrt = firstSortDefInnerSort info in
	  let qid0 = mkQualifiedId (q0, id0) in
	  %let _ = writeLine ("product sort found: "^printQualifiedId qid0) in
	  let spc = foldRecordSorts_internal spc in
	  let srts = sortsAsList spc in
	  let srts = filter (fn (q1, id1, _) -> ~((q1 = q0) && (id1 = id0))) srts in
	  let sortmap = foldl (fn ((q, id, info), srtmap) ->
			       insertAQualifierMap (srtmap, q, id, info))
	                      emptyASortMap 
			      srts
	  in
	  let spc = setSorts (spc, insertAQualifierMap (sortmap, q0, id0, info)) in
	  foldRecordSorts0 (spc, cons (qid0, visited))
  in
    foldRecordSorts0 (spc, [])


op inferTypeFoldRecords: Spec * MS.Term -> Sort
def inferTypeFoldRecords (spc, term) =
  let srt = inferType (spc, term) in
  %let _ = writeLine ("inferType ("^printTerm (term)^") = "^printSort srt) in
  case srt of
    | Product _ -> 
      let srt0 = findMatchingUserType (spc, srt) in
      %let _ = writeLine ("findMatchingUserType ("^printSort srt^") = "^printSort (srt0)) in
      srt0
    | _ -> srt

op sortId: MS.Sort -> Id

% --------------------------------------------------------------------------------

sort SortOpInfos = {ops : List OpInfo, sorts : List SortInfo}
def emptyMonoInfo = {ops = [], sorts = []}

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
  let srts = spc.sorts in
  let ops = spc.ops in
  let (srts, minfo) =
      foldriAQualifierMap
        (fn (q, id, info, (map, minfo)) ->
	 let pos = sortAnn info.dfn in
	 let (old_decls, old_defs) = sortInfoDeclsAndDefs info in
         let (new_defs, minfo) =
	     foldl (fn (def0, (defs, minfo)) ->
		    let (tvs, srt) = unpackSort def0 in
		    let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
		    let ndef = maybePiSort (tvs, srt) in
		    let defs = concat (defs, [ndef]) in
		    %let minfo = concat (minfo, minfo0) in
		    (defs, minfo)) 
	           ([]:List Sort, minfo) 
		   old_defs
	 in
	 let dfn = maybeAndSort (old_decls ++ new_defs, pos) in
	 (insertAQualifierMap (map, q, id, info << {dfn = dfn}), 
	  minfo))
        (emptyASortMap, emptyMonoInfo) 
	srts
  in
  let (ops, minfo) =
      foldriAQualifierMap
        (fn (q, id, info, (map, minfo)) ->
	 let pos = termAnn info.dfn in
	 let (tvs, srt, _) = unpackFirstOpDef info in
	 let (old_decls, old_defs) = opInfoDeclsAndDefs info in
	 let (new_decls_and_defs, minfo) =
	     foldl (fn (def0, (defs, minfo)) ->
		    let (tvs, srt, trm) = unpackTerm def0 in
		    let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
		    let (trm, minfo) = p2mTerm (spc, modifyConstructors?, trm, minfo) in
		    let ndef = maybePiTerm (tvs, SortedTerm (trm, srt, termAnn def0)) in
		    let defs = concat (defs, [ndef]) in
		    %let minfo = concat (minfo, minfo0) in
		    (defs, minfo)) 
	           ([], minfo) 
		   (old_decls ++ old_defs)
	 in
	 let dfn = maybeAndTerm (new_decls_and_defs, pos) in
	 (insertAQualifierMap (map, q, id, info << {dfn = dfn}), 
	  minfo))
        (emptyAOpMap, minfo)
	ops
  in
  let (props, minfo) =
    foldr (fn ((ptype, pname, tv, t), (props, minfo)) ->
	   let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
	   let nprop = (ptype, pname, tv, t) in
	   (cons (nprop, props), minfo))
          ([], minfo) 
	  spc.properties
  in
  let srts = foldr (fn (info , map) -> 
		    let Qualified (q, id) = primarySortName info in
		    insertAQualifierMap (map, q, id, info))
                   srts 
		   minfo.sorts
  in
  let ops = foldr (fn (info, map) -> 
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
  let spc = setSorts      (spc, srts)  in
  let spc = setOps        (spc, ops)   in
  let spc = setProperties (spc, props) in
  spc

op p2mSort: Spec * Boolean * MS.Sort * SortOpInfos -> MS.Sort * SortOpInfos
def p2mSort (spc, modifyConstructors?, srt, minfo) =
  case srt of
    | Base (qid0 as Qualified (q, id), insttv as _::_, b) ->
      %% We are trying to simplify instances of polymorphic sorts where
      %% all the type vars have been instantitated.
      if exists (fn (TyVar _) -> true | s -> false) insttv then (srt, minfo) else
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
		      let names = cons (qid, (filter (fn qid_ -> qid_ ~= qid0) names)) in 
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
		    let names = cons (qid, (filter (fn qid_ -> qid_ ~= qid0) names)) in 
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
      let (fields, minfo) = foldl (fn ((id, srt), (fields, minfo)) ->
				  let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
				  (concat (fields, [(id, srt)]), minfo))
                                  ([], minfo) fields
      in
      (Product (fields, b), minfo)
    | CoProduct (fields, b) ->
      let (fields, minfo) = foldl (fn ((id, optsrt), (fields, minfo)) ->
				  let (optsrt, minfo) = (case optsrt of
							  | None -> (None, minfo)
							  | Some srt ->
							    let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
							    (Some srt, minfo))
				  in
				  (concat (fields, [(id, optsrt)]), minfo))
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
      let (varlist, minfo) = foldl (fn ((id, srt), (varlist, minfo)) ->
				   let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
				   (concat (varlist, [(id, srt)]), minfo))
                                  ([], minfo) varlist
      in
      let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
      (Bind (binder, varlist, t, b), minfo)
    | Record (fields, b) ->
      let (fields, minfo) = foldl (fn ((id, t), (fields, minfo)) ->
				   let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
				   (concat (fields, [(id, t)]), minfo))
                            ([], minfo) fields
      in
      (Record (fields, b), minfo)
    | Let (patTerms, t, b) ->
      let (patTerms, minfo) = foldl (fn ((pat, t), (patTerms, minfo)) ->
				    let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
				    let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
				    (concat (patTerms, [(pat, t)]), minfo))
                             ([], minfo) patTerms
      in
      let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
      (Let (patTerms, t, b), minfo)
    | LetRec (varTerms, t, b) ->
      let (varTerms, minfo) = foldl (fn (( (id, srt), t), (varTerms, minfo)) ->
				    let (srt, minfo) = p2mSort (spc, modifyConstructors?, srt, minfo) in
				    let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
				    (concat (varTerms, [((id, srt), t)]), minfo))
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
      let (match, minfo) = foldl (fn ((pat, t1, t2), (match, minfo)) ->
				    let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
				    let (t1, minfo) = p2mTerm (spc, modifyConstructors?, t1, minfo) in
				    let (t2, minfo) = p2mTerm (spc, modifyConstructors?, t2, minfo) in
				    (concat (match, [(pat, t1, t2)]), minfo))
                             ([], minfo) match
      in
      (Lambda (match, b), minfo)
    | IfThenElse (t1, t2, t3, b) ->
      let (t1, minfo) = p2mTerm (spc, modifyConstructors?, t1, minfo) in
      let (t2, minfo) = p2mTerm (spc, modifyConstructors?, t2, minfo) in
      let (t3, minfo) = p2mTerm (spc, modifyConstructors?, t3, minfo) in
      (IfThenElse (t1, t2, t3, b), minfo)
    | Seq (terms, b) ->
      let (terms, minfo) = foldl (fn (t, (terms, minfo)) ->
				  let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
				  (concat (terms, [t]), minfo))
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
		    if exists (fn (TyVar _) -> true | s -> false) insttv then 
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
    | RecordPat (fields, b) ->
      let (fields, minfo) = 
          foldl (fn ((id, pat), (fields, minfo)) ->
		 let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
		 (concat (fields, [(id, pat)]), minfo))
	        ([], minfo) 
		fields
      in
      (RecordPat (fields, b), minfo)
    | RelaxPat (pat, t, b) ->
      let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
      let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
      (RelaxPat (pat, t, b), minfo)
    | QuotientPat (pat, t, b) ->
      let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
      let (t, minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
      (QuotientPat (pat, t, b), minfo)
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
      (case cpsrt of
	| Base (sqid, insttv as _::_, _) ->
          %% constructor Cons could become Cons_Nat for List (Nat), etc.
	  if exists (fn (TyVar _) -> true | s -> false) insttv then (fun, srt1, minfo) else
	  let id_ = id ^ (getSortNameSuffix insttv) in
	  let fun = Embed (if modifyConstructors? then id_ else id, b?) in
	  (fun, srt1, minfo)
       %| Boolean is same as default case
	| _ -> (fun, srt1, minfo))

    | Embedded (id) ->
      %let _ = writeLine ("constructor pred "^id^" found.") in
      let cpsrt = (case srt of
		     | Arrow (srt, _, _) -> srt
		     | _ -> srt)
      in
      %let _ = writeLine("Constuctor pred sort: "^printSort(cpsrt)) in
      (case cpsrt of
	| Base (sqid, insttv as _::_, _) ->
          %% constructor Cons could become Cons_Nat for List (Nat), etc.
	  if exists (fn (TyVar _) -> true | s -> false) insttv then (fun, srt1, minfo) else
	  let id_ = id ^ (getSortNameSuffix insttv) in
	  let fun = Embedded (if modifyConstructors? then id_ else id) in
	  %let _ = writeLine("Generated: "^ printTerm(mkEmbedded(id_, srt1))) in
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
		let names = cons (nqid, (filter (fn qid0 -> qid0 ~= qid) info.names)) in
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
		  let names = cons (nqid, (filter (fn qid0 -> qid0 ~= qid) info.names)) in
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

 op printTyVarSubst: TyVarSubst -> String
def printTyVarSubst tvsubst =
  case tvsubst of
    | [] -> ""
    | [(id, srt)] -> id^" -> "^printSort srt
    | (id, srt)::tvsubst ->
      id^" -> "^printSort srt ^ ", "^printTyVarSubst (tvsubst)

 op printSortOpInfos : SortOpInfos -> String
def printSortOpInfos minfo =
  let s1 = foldl (fn (info, s) -> let Qualified (_, id) = primaryOpName   info in s ^ " " ^ id) "" minfo.ops in
  let s2 = foldl (fn (info, s) -> let Qualified (_, id) = primarySortName info in s ^ " " ^ id) "" minfo.sorts in
  "ops: "^s1^newline^"sorts: "^s2
  

op getSortNameFromTyVarSubst: TyVarSubst -> String
def getSortNameFromTyVarSubst (subst) =
  getSortNameSuffix (map (fn (_, srt) -> srt) subst)

op getSortNameSuffix: List Sort -> String
def getSortNameSuffix (instlist) =
  case instlist of
    | [] -> ""
    | srt::instlist -> "_" ^ (sortId srt)^ (getSortNameSuffix instlist)

op addOpInfo2SortOpInfos: QualifiedId * OpInfo * SortOpInfos -> SortOpInfos
def addOpInfo2SortOpInfos (nqid, opinfo, minfo) =
  let ops = minfo.ops in
%  let _ = case opinfo of
%          | (_, _, _, []) -> writeLine ("no definition term!")
%          | _ -> ()
%  in
  case find (fn info -> member (nqid, info.names)) ops of
    | Some _ -> minfo
    | None -> {ops = cons (opinfo, ops), sorts = minfo.sorts}

op exchangeOpInfoInSortOpInfos: QualifiedId * OpInfo * SortOpInfos -> SortOpInfos
def exchangeOpInfoInSortOpInfos (nqid, opinfo, minfo) =
  let ops = minfo.ops in
  let ops = filter (fn info -> ~ (member (nqid, info.names))) ops in
  {ops = cons (opinfo, ops), sorts = minfo.sorts}

op monoInfosContainOp?: QualifiedId * SortOpInfos -> Boolean
def monoInfosContainOp? (nqid, minfo) =
  let ops = minfo.ops in
  case find (fn info -> member (nqid, info.names)) ops of
    | Some _ -> true
    | None -> false

op monoInfosContainSort?: QualifiedId * SortOpInfos -> Boolean
def monoInfosContainSort? (nqid, minfo) =
  let srts = minfo.sorts in
  case find (fn info -> member (nqid, info.names)) srts of
    | Some _ -> true
    | None -> false

op addSortInfo2SortOpInfos: QualifiedId * SortInfo * SortOpInfos -> SortOpInfos
def addSortInfo2SortOpInfos (nqid, sinfo, minfo) =
  if monoInfosContainSort? (nqid, minfo) then 
    minfo 
  else
    {ops   = minfo.ops, 
     sorts = cons (sinfo, minfo.sorts)}

op exchangeSortInfoInSortOpInfos: QualifiedId * SortInfo * SortOpInfos -> SortOpInfos
def exchangeSortInfoInSortOpInfos (nqid, sinfo, minfo) =
  let sorts = minfo.sorts in
  let sorts = filter (fn info -> ~ (member (nqid, info.names))) sorts in
  {ops   = minfo.ops, 
   sorts = cons (sinfo, sorts)}

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

op isEmptySortOpInfos?: SortOpInfos -> Boolean
def isEmptySortOpInfos? (minfo) =
  minfo.ops = [] && minfo.sorts = []

% --------------------------------------------------------------------------------

 (**
 * add the ops and sort definitions that are defined in the bspc and used in the
 * spc to the spc, so that the resultung spec is self-contained.
 * ignore is a function that can be used to exclude certain qid's from being added
 * if ignore(qid) evaluates to true, the sort/op will be ignored, i.e. it will *not* be added.
 *)
op addMissingFromBase: Spec * Spec * (QualifiedId -> Boolean) -> Spec
def addMissingFromBase (bspc, spc, ignore) = addMissingFromBaseTo (bspc, spc, ignore, spc)

 (**
 * same as addMissingFromBase, only that a spec just containing the missing ops and sorts
 * is returned.
 *)
op getMissingFromBase: Spec * Spec * (QualifiedId -> Boolean) -> Spec
def getMissingFromBase (bspc, spc, ignore) = addMissingFromBaseTo (bspc, spc, ignore, initialSpecInCat)

op addMissingFromBaseTo: Spec * Spec * (QualifiedId -> Boolean) * Spec -> Spec
def addMissingFromBaseTo (bspc, spc, ignore, initSpec) =
  %let _ = writeLine ("---------------------- basespc: ------------------") in
  %let _ = writeLine (printSpec bspc) in
  %let _ = writeLine ("---------------------- end basespc ---------------") in
  %let _ = writeLine ("addMissingFromBaseTo, spc="^ (printSpec spc)) in
  let minfo =
      foldriAQualifierMap
       (fn (q, i, info, minfo) ->
	foldl (fn (def0, minfo) ->
	       let srt = sortInnerSort def0 in
	       let minfo = addMissingFromSort (bspc, spc, ignore, srt, minfo) in
	       minfo) 
	      minfo 
	      (sortInfoDefs info))
       emptyMonoInfo 
       spc.sorts
  in
  let minfo =
      foldriAQualifierMap
       (fn (q, i, info, minfo) ->
	foldl (fn (dfn, minfo) ->
	       let (_, srt, trm) = unpackTerm dfn in
	       let minfo = addMissingFromSort (bspc, spc, ignore, srt, minfo) in
	       addMissingFromTerm (bspc, spc, ignore, trm, minfo))
	      minfo
	      (opInfoDefs info))
       minfo 
       spc.ops
  in
  let minfo =
      foldr (fn (info, minfo) -> addMissingFromTerm (bspc, spc, ignore, info.4, minfo))
            minfo 
	    spc.properties
  in
  if isEmptySortOpInfos? minfo then 
    initSpec 
  else
    %let _ = writeLine ("added sorts && ops: "^newline^printSortOpInfos (minfo)) in
    let srts = foldr (fn (info, map) -> 
		      let Qualified (q, id) = primarySortName info in
		      insertAQualifierMap (map, q, id, info))
                     initSpec.sorts 
		     minfo.sorts
    in
    let ops = foldr (fn (info, map) -> 
		     let Qualified (q, id) = primaryOpName info in
		     insertAQualifierMap (map, q, id, info))
                    initSpec.ops 
		    minfo.ops
    in
    let initSpec = setSorts (initSpec, srts) in
    let initSpec = setOps  (initSpec, ops)  in
    addMissingFromBase (bspc, initSpec, ignore)


op  addMissingFromSort: Spec * Spec * (QualifiedId -> Boolean) * MS.Sort * SortOpInfos -> SortOpInfos
def addMissingFromSort (bspc, spc, ignore, srt, minfo) =
  %let _ = writeLine ("addMissingFromSort: "^ (printSort srt)) in
  case srt of
    | Arrow    (srt1, srt2, _) -> addMissingFromSort (bspc, spc, ignore, srt2, addMissingFromSort (bspc, spc, ignore, srt1, minfo))
    | Product  (fields,     _) -> foldl (fn ((_, srt),      minfo) -> addMissingFromSort (bspc, spc, ignore, srt, minfo)) 
				         minfo 
					 fields
    | CoProduct (fields,     _) -> foldl (fn ((_, Some srt), minfo) -> addMissingFromSort (bspc, spc, ignore, srt, minfo) 
                                              | _ -> minfo)
				         minfo 
					 fields
    | Quotient (srt, term,  _) -> addMissingFromTerm (bspc, spc, ignore, term, addMissingFromSort (bspc, spc, ignore, srt, minfo))
    | Subsort  (srt, term,  _) -> addMissingFromTerm (bspc, spc, ignore, term, addMissingFromSort (bspc, spc, ignore, srt, minfo))
    | Base     (qid as Qualified (q, id), srts, _) ->
      if ignore qid then 
	minfo 
      else
	let minfo = foldl (fn (srt, minfo) -> addMissingFromSort (bspc, spc, ignore, srt, minfo)) minfo srts in
	(case findTheSort (spc, qid) of
	   | Some _ -> 
	     %let _ = writeLine ("sort \""^printQualifiedId qid^"\" found in spec.") in
	     minfo
	   | None -> 
	    (case findTheSort (bspc, qid) of
		| None -> minfo %fail ("can't happen: couldn't find sort def for "^q^"."^id%printQualifiedId qid
				       %^"\n"^ (printSpec bspc)
				       %^"\n"^ (printSpec spc)
				       %   )
		| Some sinfo ->
		  %let _ = writeLine ("adding sort \""^printQualifiedId qid^"\" from base spec.") in
		addSortInfo2SortOpInfos (qid, sinfo, minfo)))

   %| Boolean is same as default case
    | _ -> minfo


op addMissingFromTerm: Spec * Spec * (QualifiedId -> Boolean) * MS.Term * SortOpInfos -> SortOpInfos
def addMissingFromTerm (bspc, spc, ignore, term, minfo) =
  let def amt (t, minfo) = addMissingFromTerm   (bspc, spc, ignore, t, minfo) in
  let def ams (s, minfo) = addMissingFromSort   (bspc, spc, ignore, s, minfo) in
  let def amp (p, minfo) = addMissingFromPattern (bspc, spc, ignore, p, minfo) in
  case term of
    | Apply     (t1, t2,      _) -> amt (t2, amt (t1, minfo))
    | Record    (fields,      _) -> foldl (fn ((_, t), minfo) -> amt (t, minfo)) minfo fields
    | Bind      (_, vlist, t, _) -> let minfo = foldl (fn ((_, srt), minfo) -> ams (srt, minfo)) minfo vlist in
                                     amt (t, minfo)
    | Let       (ptlist, t,   _) -> let minfo = foldl (fn ((p, t), minfo) -> amp (p, amt (t, minfo))) minfo ptlist in
				     amt (t, minfo)
    | LetRec    (vtlist, t,   _) -> let minfo = foldl (fn (( (id, srt), t), minfo) -> ams (srt, amt (t, minfo))) minfo vtlist in
				     amt (t, minfo)
    | Var       ((id, srt),   _) -> ams (srt, minfo)
    | Lambda    (match,       _) -> foldl (fn ((p, t1, t2), minfo) -> amt (t2, amt (t1, amp (p, minfo)))) minfo match
    | IfThenElse (t1, t2, t3,  _) -> amt (t3, amt (t2, amt (t1, minfo)))
    | Seq       (tl,          _) -> foldl (fn (t, minfo) -> amt (t, minfo)) minfo tl
    | SortedTerm (t, s,        _) -> ams (s, amt (t, minfo))
    | Fun       (fun, srt,    _) ->
     (let minfo = ams (srt, minfo) in
       case fun of
	 | Op (qid, _) ->
	   if ignore qid then 
	     minfo 
	   else
	    (case findTheOp (spc, qid) of
		| Some _ -> minfo
		| None -> (case findTheOp (bspc, qid) of
			     | None -> minfo
			       %fail ("can't happen: couldn't find op \""^printQualifiedId qid^"\""
				      %^"\n"^ (printSpec bspc)
				      %^"\n"^ (printSpec spc)
				      %)
			       %| Some (opinfo as ((Qualified (_, id))::_, _, _, [])) ->
			       %  let _ = writeLine ("addMissing: no definition term found for "^
			       %			 printQualifiedId qid^".")
			       %  in
			       %  minfo
			     | Some opinfo ->
			       %let _ = writeLine ("adding op "^printQualifiedId qid^" from base spec.") in
			     addOpInfo2SortOpInfos (qid, opinfo, minfo)))
	 | _ -> minfo)
    | _ -> minfo


op addMissingFromPattern: Spec * Spec * (QualifiedId -> Boolean) * MS.Pattern * SortOpInfos -> SortOpInfos
def addMissingFromPattern (bspc, spc, ignore, pat, minfo) =
  let def amt (t, minfo) = addMissingFromTerm (bspc, spc, ignore, t, minfo) in
  let def ams (s, minfo) = addMissingFromSort (bspc, spc, ignore, s, minfo) in
  let def amp (p, minfo) = addMissingFromPattern (bspc, spc, ignore, p, minfo) in
  case pat of
    | AliasPat   (p1, p2,       _) -> amp (p2, amp (p1, minfo))
    | VarPat     ((_, srt),     _) -> ams (srt, minfo)
    | EmbedPat   (_, Some p, s, _) -> amp (p, ams (s, minfo))
    | EmbedPat   (_, None,   s, _) -> ams (s, minfo)
    | RecordPat  (fields,       _) -> foldl (fn ((_, p), minfo) -> amp (p, minfo)) minfo fields
    | WildPat    (s,            _) -> ams (s, minfo)
    | RelaxPat   (p, t,         _) -> amp (p, amt (t, minfo))
    | QuotientPat (p, t,         _) -> amp (p, amt (t, minfo))
    | SortedPat  (p, s,         _) -> amp (p, ams (s, minfo))
    | _ -> minfo

%--------------------------------------------------------------------------------

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
    (spc, concat (opnames, opnames0)))
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
				   dfn    = maybePiTerm (tvs, SortedTerm (term, opsrt, b))}
		     in
		     let newops = insertAQualifierMap (spc.ops, opq, opid, opinfo) in
		     let opnames = cons (opqid, opnames) in
		     (setOps (spc, newops), opnames))
	            (spc, []) 
		    fields)
      | _ -> (spc, [])

 op getConstructorOpName: QualifiedId * String -> QualifiedId
def getConstructorOpName (qid as Qualified (q, id), consid) =
  % the two $'s are important: that how the constructor op names are
  % distinguished from other opnames (hack)
  let sep = "$$" in
  Qualified (q, id^sep^consid)

 op getConstructorOpNameForSnark: QualifiedId * String -> QualifiedId
def getConstructorOpNameForSnark (qid as Qualified (q, id), consid) =
  % the two $'s are important: that how the constructor op names are
  % distinguished from other opnames (hack)
  let sep = "_" in
  Qualified (q, "embed"^sep^consid)

% this is used to distinguish "real" product from "record-products"
 op productfieldsAreNumbered: fa (a) List (String * a) -> Boolean
def productfieldsAreNumbered (fields) =
  let
    def fieldsAreNumbered0 (i, fields) =
      case fields of
	| [] -> true
	| (id, _)::fields -> id = Nat.toString (i) && fieldsAreNumbered0 (i+1, fields)
  in
  fieldsAreNumbered0 (1, fields)


op patternFromSort: Option Sort * Position -> Pattern
def patternFromSort (optsrt, b) =
  let
    def mkVarPat (id, srt) =
      VarPat ((id, srt), b)
  in
  case optsrt of
    | None -> RecordPat ([], b)
    | Some srt -> 
      case srt of
	| Product ([], _) -> RecordPat ([], b)
	| Product (fields, _) ->
	  if productfieldsAreNumbered fields then
	    RecordPat (List.map (fn (id, srt) -> (id, mkVarPat ("x"^id, srt))) fields, b)
	  else mkVarPat ("x", srt)
	| _ -> mkVarPat ("x", srt)

op argTermFromSort: Option Sort * MS.Term * Position -> MS.Term
def argTermFromSort (optsrt, funterm, b) =
  let
    def mkVarTerm (id, srt) =
      Var ((id, srt), b)
  in
  case optsrt of
    | None -> funterm
    | Some srt -> 
      let term = 
        case srt of
	  | Product (fields, _) ->
	    if productfieldsAreNumbered fields then
	      Record (List.map (fn (id, srt) -> (id, mkVarTerm ("x"^id, srt))) fields, b)
	    else mkVarTerm ("x", srt)
	  | _ -> mkVarTerm ("x", srt)
      in
      Apply (funterm, term, b)

op recordTermFromSort: Sort * Position -> MS.Term
def recordTermFromSort (srt, b) =
  let
    def mkVarTerm (id, srt) =
      Var ((id, srt), b)
  in
      let term = 
        case srt of
	  | Product (fields, _) ->
	    if productfieldsAreNumbered fields then
	      Record (List.map (fn (id, srt) -> (id, mkVarTerm ("x"^id, srt))) fields, b)
	    else mkVarTerm ("x", srt)
	  | _ -> mkVarTerm ("x", srt)
      in term

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
    (spc, concat (opnames, opnames0)))
   (spc, []) 
    spc.sorts

op getRecordConstructorOpName: QualifiedId  -> QualifiedId
def getRecordConstructorOpName (qid as Qualified (q, id)) =
  let sep = "_" in
  Qualified (q, "mk_Record"^sep^id)


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
		       dfn    = maybePiTerm (tvs, SortedTerm (term, opsrt, b))}
	 in
	 let newops = insertAQualifierMap (spc.ops, opq, opid, opinfo) in
	 let opnames = [opqid] in
	 (addLocalOpName (setOps (spc, newops), opqid), opnames))
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
    (spc, concat (opnames, opnames0)))
   (spc, []) 
    spc.sorts

op addProductAccessorsFromSort: Spec * QualifiedId * SortInfo -> Spec * List (QualifiedId)
def addProductAccessorsFromSort (spc, qid, info) =
  if ~ (definedSortInfo? info) then
    (spc, [])
  else
    let (tvs, srt) = unpackFirstSortDef info in
    let srt = stripSubsorts (spc, srt) in
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
				   dfn    = maybePiTerm (tvs, SortedTerm (term, opsrt, b))}
		     in
		     let newops = insertAQualifierMap (spc.ops, opq, opid, opinfo) in
		     let opnames = cons (opqid, opnames) in
		     (addLocalOpName (setOps (spc, newops), opqid), opnames))
	            (spc, [])
		    fields)
      | _ -> (spc, [])

 op getAccessorOpName: String * QualifiedId * String -> QualifiedId
def getAccessorOpName (srtName, qid as Qualified (q, id), accid) =
  let sep = "_" in
  Qualified (q, "project"^sep^srtName^sep^accid)
% --------------------------------------------------------------------------------

 (**
 * converts anonymous lambda terms to inner functions, e.g.
 *
 *    (fn (x) -> t)
 *
 *  is tranformed to
 *
 *    let def inner (x) = t in inner
 *
 * The idea is that "inner" is then lifted to the outer level by the
 * general lambda-lifting transformation
 *)

op lambdaToInner: Spec -> Spec
def lambdaToInner spc =
  %let _ = writeLine ("lambdaToInner...") in
  let ops = foldriAQualifierMap
            (fn (q, id, info, newops) ->
	     let (old_decls, old_defs) = opInfoDeclsAndDefs info in
	     let new_defs = 
	         List.map (fn dfn ->
			   let (tvs, srt, term) = unpackTerm dfn in
			   let new_tm = lambdaToInnerToplevelTerm (spc, term) in
			   maybePiTerm (tvs, SortedTerm (new_tm, srt, termAnn term)))
		          old_defs
	     in
	     let new_dfn = maybeAndTerm (old_decls ++ new_defs, termAnn info.dfn) in
	     let new_info = info << {dfn = new_dfn} in
	     insertAQualifierMap (newops, q, id, new_info))
	    emptyAQualifierMap 
	    spc.ops
  in
  setOps (spc, ops)

op lambdaToInnerToplevelTerm: Spec * MS.Term -> MS.Term
def lambdaToInnerToplevelTerm (spc, term) =
  case term of
    | Lambda (match, body) -> 
      let newm = List.map (fn (pat, cond, body) ->
			   (pat, 
			    lambdaToInnerTerm spc cond, 
			    lambdaToInnerTerm spc body))
                          match
      in
	Lambda (newm, body)
    | _ -> lambdaToInnerTerm spc term

op lambdaToInnerTerm: Spec -> MS.Term -> MS.Term
def lambdaToInnerTerm spc t =
  %let _ = writeLine ("lambdaToInnerTerm ("^ (printTerm t)^")") in
  case t of
    | LetRec (vartermlist, body, b) ->
      let vartermlist = List.map (fn (v, t) -> (v, lambdaToInnerToplevelTerm (spc, t))) vartermlist in
      let body = lambdaToInnerTerm spc body in
      LetRec (vartermlist, body, b)
    | Lambda ([(pat, cond, term)], b) ->
      let fname = "inner" in
      let fsrt = inferType (spc, t) in
      let variable = (fname, fsrt) in
      let cond = lambdaToInnerTerm spc cond in
      let term = lambdaToInnerTerm spc term in
      let t = Lambda ([(pat, cond, term)], b) in
      let newt = LetRec ([(variable, t)], Var (variable, b), b) in
      %let _ = writeLine ("lambdaToInner ("^ (printTerm t)^") = "^ (printTerm newt)) in
      newt
    | Apply (t1, t2, b) -> Apply (lambdaToInnerTerm spc t1, lambdaToInnerTerm spc t2, b)
    | Record (fields, b) ->
      let fields = map (fn (id, t) -> (id, lambdaToInnerTerm spc t)) fields in
      Record (fields, b)
    | Let (letlist, t, b) ->
      let letlist = map (fn (pat, term) -> (lambdaToInnerPat spc pat, lambdaToInnerTerm spc term)) letlist in
      let t = lambdaToInnerTerm spc t in
      Let (letlist, t, b)
    | Lambda (m, b) ->
      let m = map (fn (pat, cond, body) -> (lambdaToInnerPat spc pat, lambdaToInnerTerm spc cond, 
					 lambdaToInnerTerm spc body)) m
      in
      Lambda (m, b)
    | IfThenElse (t1, t2, t3, b) ->
      let t1 = lambdaToInnerTerm spc t1 in
      let t2 = lambdaToInnerTerm spc t2 in
      let t3 = lambdaToInnerTerm spc t3 in
      IfThenElse (t1, t2, t3, b)
    | Seq (terms, b) ->
      let terms = map (fn (t) -> lambdaToInnerTerm spc t) terms in
      Seq (terms, b)
    | _ -> t

op lambdaToInnerPat: Spec -> Pattern -> Pattern
def lambdaToInnerPat _  pat = pat


% --------------------------------------------------------------------------------

 (*
 * conformOpDecls checks whether we have an opdef of the form
 *
 * sort P = A * B
 * op foo: P -> Q
 * def foo (a, b) = ...
 *
 * i.e. the declaration contains the user sort name, but the arguments refer to its definition term.
 * ops are transformed to something like
 * 
 * def foo (arg) = 
 *   let a = arg^1 in
 *   let b - arg^2 in
 *   ...
 *)

op conformOpDecls: Spec -> Spec
def conformOpDecls spc =
  %let _ = writeLine ("lambdaToInner...") in
  let ops = foldriAQualifierMap
            (fn (q, id, info, newops) ->
	     let (old_decls, old_defs) = opInfoDeclsAndDefs info in
	     let new_defs = 
	         List.map (fn dfn ->
			   let (tvs, srt, term) = unpackTerm dfn in
			   let new_tm = conformOpDeclsTerm (spc, srt, term, id) in
			   maybePiTerm (tvs, SortedTerm (new_tm, srt, termAnn term)))
		          old_defs
	     in
	     let new_dfn = maybeAndTerm (old_decls ++ new_defs, termAnn info.dfn) in
	     let new_info = info << {dfn = new_dfn} in
	     insertAQualifierMap (newops, q, id, new_info))
	    emptyAQualifierMap spc.ops
  in
  setOps (spc, ops)

op conformOpDeclsTerm: Spec * MS.Sort * MS.Term * Id -> MS.Term
def conformOpDeclsTerm (spc, srt, term, _) =
  let srt = unfoldToArrow (spc, srt) in
  case srt of
    | Arrow (domsrt as (Base _), ransrt, _) ->
    let usrt = unfoldToProduct (spc, domsrt) in
    (case usrt of
       | Product (fields, _) ->
       let termsort = inferType (spc, term) in
       (case termsort of
	  | Arrow (Product (fields0, _), _, _) ->
	  if productfieldsAreNumbered (fields0) then
	    case term of
	      | Lambda ([(pat, _, bodyterm)], b) ->
		let optplist =
		 (case pat of
		   | VarPat ((id, _), _) -> Some[id]
		   | RecordPat (plist, _) -> 
		     if all (fn | (_, VarPat _) -> true | (_, _) -> false) plist then
		       Some (List.map (fn (_, VarPat ((id, _), _)) -> id) plist)
		     else
		       None
		   | _ -> None
		)
		in
		 (case optplist of
		   | None -> term
		   | Some plist -> 
		   if length (fields0) = length (plist) then
		     %let _ = writeLine ("checking "^id^"...") in
		     let argname = "_arg" in
		     let pnamessrts = zip (plist, fields0) in
		     let bodyterm = foldr (fn ((variable, (id, fsrt)), bodyterm) ->
					   let proj = Fun (Project (id), Arrow (srt, fsrt, b), b) in
					   let pterm = Apply (proj, Var ((argname, srt), b), b) in
					   Let ([(VarPat ((variable, fsrt), b), pterm)], bodyterm, b))
		                           bodyterm pnamessrts
		     in
		     let cond = mkTrue () in
		     let newpat = VarPat ((argname, srt), b) in
		     Lambda ([(newpat, cond, bodyterm)], b)
		   else
		     term
		  )
	      | _ ->term
	  else term
	  | _ -> term)
     | _ -> term
      )
    | _ -> term
       

  (**
    unfolds a sort, only if it is an alias for a Product, otherwise it's left unchanged;
    this is used to "normalize" the arrow sorts, i.e. to detect, whether the first argument of
    an arrow sort is a product or not. Only "real" products are unfolded, i.e. sort of the
    form (A1 * A2 * ... * An) are unfolded, not those of the form {x1:A1, x2:A2, ..., xn:An}
  *)
  op unfoldToProduct: Spec * Sort -> Sort
  def unfoldToProduct (spc, srt) =
    let
      def unfoldRec srt =
	let usrt = unfoldBase (spc, srt) in
	if usrt = srt then srt else unfoldRec (usrt)

    in
    let usrt = unfoldRec srt in
    case usrt of
      | Product (fields, _) -> if productfieldsAreNumbered (fields) then usrt else srt
      | _ -> srt


 % --------------------------------------------------------------------------------

 (*
  * returns whether the domain A of an op if it is declared as
  *
  * op foo: A -> B
  *
  * and A is a sort defined as a product sort.
  *)
 op getFoldedDomain: Spec * QualifiedId -> Option (MS.Sort)
 def getFoldedDomain (spc, qid) =
   case findTheOp (spc, qid) of
     | None -> None
     | Some info ->
       let srt = firstOpDefInnerSort info in 
       let srt = unfoldToArrow (spc, srt) in
       case srt of
	 | Arrow (domsrt as (Base _), ransrt, _) ->
	   let usrt = unfoldToProduct (spc, domsrt) in
	   (case usrt of
	      | Product (fields, _) -> Some (domsrt)
	      | _ -> None)
	 | _ -> None


 (*
  * adjustAppl checks for application terms to ops with a folded domain (see
  * above check). If the argument of the application term is a product, then
  * a let variable is introduced and used as argument, e.g.:
  *
  * sort A = B * C
  * op foo: A -> D
  *
  * foo (b, c) would then be transformed into foo (let arg= (b, c) in arg)
  *)

  op adjustAppl: Spec -> Spec
  def adjustAppl spc =
    let
      def adjustApplTerm (t) =
	case t of
	  | Apply (funterm as Fun (Op (qid, _), srt, _), argterm as Record _, b) ->
	    (case getFoldedDomain (spc, qid) of
	       | None -> t
	       | Some opsrt ->
	         let vname = "_arg" in
	         let pat = VarPat ((vname, opsrt), b) in
		 Apply (funterm, Let ([(pat, argterm)], Var ((vname, opsrt), b), b), b)
		)
	  | _ -> t
    in
    mapSpec (adjustApplTerm, id, id) spc

%--------------------------------------------------------------------------------

 (**
 * adds for each user sort the corresponding
 * equality op
 *)

op addEqOpsToSpec : Spec -> Spec
def addEqOpsToSpec spc =
  foldriAQualifierMap
    (fn (q, id, sortinfo, spc) ->
     let spc = addEqOpsFromSort (spc, Qualified (q, id), sortinfo) in
     spc)
    spc 
    spc.sorts

op addEqOpsFromSort: Spec * QualifiedId * SortInfo -> Spec
def addEqOpsFromSort (spc, qid, info) =
  let
    def getLambdaTerm (srt, body, b) =
      let cond = mkTrue () in
      let pat = RecordPat ([("1", VarPat (("x", srt), b)), ("2", VarPat (("y", srt), b))], b) in
      Lambda ([(pat, cond, body)], b)
  in
  let
    def getEqOpSort (srt, b) =
      Arrow (Product ([("1", srt), ("2", srt)], b), Boolean b, b)
  in
  let
    def addEqOp (eqqid as Qualified (eq, eid), osrt, body, b) =
      let term = getLambdaTerm (osrt, body, b) in
      let info = {names  = [eqqid],
		  fixity = Nonfix,
		  dfn    = SortedTerm (term, getEqOpSort (osrt, b), b)}
      in
      let ops = insertAQualifierMap (spc.ops, eq, eid, info) in
      setOps (spc, ops)
  in
  if ~ (definedSortInfo? info) then
    spc
  else
    let (tvs, srt) = unpackFirstSortDef info in
    let usrt = unfoldStripSort (spc, srt, false) in
    case usrt of
      | Boolean _ -> spc
      | Base (Qualified (_, "Nat"),     [], _) -> spc
      | Base (Qualified (_, "Integer"), [], _) -> spc
      | Base (Qualified (_, "Char"),    [], _) -> spc
      | Base (Qualified (_, "String"),  [], _) -> spc
     %| Base (Qualified (_, "Float"),   [], _) -> spc
      | _ ->
        let b = sortAnn srt in
	let osrt = Base (qid, map (fn tv -> TyVar (tv, b)) tvs, b) in
	%let _ = writeLine ("generating eq-op for \""^ (printQualifiedId qid)^"\", unfolded sort="^ (printSort osrt)) in
	let varx = Var (("x", osrt), b) in
	let vary = Var (("y", osrt), b) in
	let eqqid as Qualified (eq, eid) = getEqOpQid qid in
	let
          def getEqTermFromProductFields (fields, osrt, varx, vary) =
	    foldr (fn ((fid, fsrt), body) ->
		   let projsrt = Arrow (osrt, fsrt, b) in
		   let eqsort = Arrow (Product ([("1", fsrt), ("2", fsrt)], b), Boolean b, b) in
		   let proj = Fun (Project (fid), projsrt, b) in
		   let t1 = Apply (proj, varx, b) in
		   let t2 = Apply (proj, vary, b) in
		   let t = Apply (Fun (Equals, eqsort, b), Record ([("1", t1), ("2", t2)], b), b) in
		   if body = mkTrue () then 
		     t
		   else
		     let andSrt = Arrow (Product ([("1", Boolean b), ("2", Boolean b)], b), Boolean b, b) in
		     let andTerm = mkAndOp b in
		     Apply (andTerm, Record ([("1", t), ("2", body)], b), b)
		     %IfThenElse (t, body, mkFalse (), b)
		    )
	          (mkTrue ()) 
		  fields
	in
	% check for aliases first
	case srt of
	  | Base (aqid, _, b) ->
	    % define the eq-op in terms of the aliased sort
	    let aeqqid = getEqOpQid (aqid) in
	    let fun = Fun (Op (aeqqid, Nonfix), getEqOpSort (osrt, b), b) in
	    let args = Record ([("1", varx), ("2", vary)], b) in
	    let body = Apply (fun, args, b) in
	    addEqOp (eqqid, osrt, body, b)
          %% Boolean is same as default case
	  | _ ->
	    %let _ = writeLine ("srt="^printSort srt) in
	    case srt of
	      | Product (fields, _) -> 
	        let body = getEqTermFromProductFields (fields, osrt, varx, vary) in
		addEqOp (eqqid, osrt, body, b)
	      | CoProduct (fields, _) ->
		(let applysrt = Arrow (osrt, Boolean b, b) in
		 let match =
		     foldr (fn ((fid, optfsrt), match) ->
			    let xpat = EmbedPat (fid, 
						 case optfsrt of 
						   | None -> None 
						   | Some fsrt -> Some (VarPat (("x0", fsrt), b)), osrt, b) 
			    in
			    let ypat = EmbedPat (fid, 
						 case optfsrt of 
						   | None -> None 
						   | Some fsrt -> Some (VarPat (("y0", fsrt), b)), osrt, b) 
			    in
			    let eqFsrt =
			        let 
                                  def bcase fsrt =
				    let eqsrt = getEqOpSort (fsrt, b) in
				    Apply (Fun (Equals, eqsrt, b), 
					   Record ([("1", Var (("x0", fsrt), b)), 
						    ("2", Var (("y0", fsrt), b))],
						   b), 
					   b)
				in
				  case optfsrt of
				    | None -> mkTrue ()
				    | Some (fsrt as Base _) -> bcase fsrt
				    | Some fsrt ->
				      let ufsrt = unfoldStripSort (spc, fsrt, false) in
				      case fsrt of
					| Product (fields, _) -> 
					  getEqTermFromProductFields (fields, fsrt, 
								      Var (("x0", fsrt), b), 
								      Var (("y0", fsrt), b))
					| _ -> bcase (fsrt)
			    in
			    let ymatch = [(ypat, mkTrue (), eqFsrt), (WildPat (osrt, b), mkTrue (), mkFalse ())] in
			    let caseTerm = Apply (Lambda (ymatch, b), vary, b) in
			    cons ((xpat, mkTrue (), caseTerm), match))
		           []
			   fields
		 in
		 let body = Apply (Lambda (match, b), varx, b) in
		 addEqOp (eqqid, osrt, body, b))
	      | _ -> spc

op getEqOpQid: QualifiedId -> QualifiedId
def getEqOpQid (Qualified (q, id)) =
  Qualified (q, "eq$" ^ id)

% --------------------------------------------------------------------------------

op findTheSort: Spec * QualifiedId -> Option (SortInfo)
def findTheSort = findTheOpSort AnnSpec.findTheSort AnnSpec.findAllSorts

op findTheOp: Spec * QualifiedId -> Option (OpInfo)
def findTheOp = findTheOpSort AnnSpec.findTheOp AnnSpec.findAllOps

op findTheOpSort: fa (a) (Spec * QualifiedId -> Option (a)) -> (Spec * QualifiedId -> List (a)) -> Spec * QualifiedId -> Option (a)
def findTheOpSort origFindThe origFindAll (spc, qid as Qualified (q, id)) =
  let res1 = origFindThe (spc, qid) in
  case res1 of
    | Some _ -> res1
    | None ->
      if q = UnQualified then None
      else
	case origFindAll (spc, Qualified (UnQualified, id)) of
	  | [] -> None
	  | res::_ -> Some res

% --------------------------------------------------------------------------------
% debug

op showSorts: Spec -> ()
def showSorts spc =
  appSpec ((fn _ -> ()), (fn srt -> writeLine (printSort srt)), (fn _ -> ())) spc


endspec
