(**
 * this spec contains code generation related transformations that are performed
 * before the actual code generation step
 *)

CodeGenTransforms qualifying spec

import /Languages/MetaSlang/Specs/StandardSpec
import /Languages/MetaSlang/Transformations/InstantiateHOFns
% --------------------------------------------------------------------------------

(**
 * identifies the int sorts with the Integer types; this makes sense, if the base spec is not part of the
 * code generation and treated as builtin unit
 *)
op identifyIntSorts: Spec -> Spec
def identifyIntSorts(spc) =
  let
    def identifyIntSort(srt) =
      case srt of
	| Base(Qualified("Nat","Nat"),[],b) -> Base(Qualified("Integer","Integer"),[],b)
	| Base(Qualified("Nat","PosNat"),[],b) -> Base(Qualified("Integer","Integer"),[],b)
	| Base(Qualified("Integer","NZInteger"),[],b) -> Base(Qualified("Integer","Integer"),[],b)
	| _ -> srt
  in
  let termid = (fn(t) -> t) in
  let pattid = (fn(p) -> p) in
  mapSpec (termid,identifyIntSort,pattid) spc

% --------------------------------------------------------------------------------

(**
 * transforms "let _ = t1 in t2" into "(t1;t2)"
 *)
op letWildPatToSeq: Spec -> Spec
def letWildPatToSeq(spc) =
  let
    def lettoseq(t) =
      case t of
	| Let([(WildPat _,t1)],t2,b) -> 
	  lettoseq(Seq([t1,t2],b))
	| Seq((Seq(terms0,_))::terms,b) ->
	  lettoseq(Seq(concat(terms0,terms),b))
	| _ -> t
  in
  let sortid = (fn(s) -> s) in
  let pattid = (fn(p) -> p) in
  mapSpec (lettoseq,sortid,pattid) spc


op unfoldSortAliases: Spec -> Spec
def unfoldSortAliases(spc) =
  let srts = sortsAsList(spc) in
  case find (fn(_,_,sortinfo) -> 
	     case sortinfo of
	       | (_,_,(_,Base(qid,psrts,_))::_) -> true
	       | _ -> false) srts of
    | None -> spc
    | Some (q0,id0,(_,_,(_,Base(qid,psrts,_))::_)) ->
      let qid0 = mkQualifiedId(q0,id0) in
      %let _ = writeLine("sort alias found: "^printQualifiedId(qid0)^" = "^printQualifiedId(qid)) in
      let srts = filter (fn(q1,id1,_) -> ~((q1=q0)&(id1=id0))) srts in
      let sortmap = foldl (fn((q,id,sinfo),srtmap) ->
			    insertAQualifierMap(srtmap,q,id,sinfo))
                           emptyASortMap srts
      in
      let spc = setSorts(spc,sortmap) in
      let
        def mapSrt(s) = 
	  case s of
	    | Base(qid2,srts,b) -> %let srts = psrts in
	                           if (qid2 = qid0) then Base(qid,psrts,b)
				   else Base(qid2,srts,b)
	    | _ -> s
      in
      let spc = mapSpec (id,mapSrt,id) spc in
      unfoldSortAliases spc

(**
 * looks in the spec for a user type matching the given sort; if a matching
 * user type exists.
 *)
op findMatchingUserTypeOption: Spec * Sort -> Option Sort
def findMatchingUserTypeOption(spc,srtdef) =
  case srtdef of
    | Base _ -> Some srtdef
    | _ ->
    let srts = sortsAsList(spc) in
    let srtPos = sortAnn srtdef in
    let foundSrt = find (fn |(qualifier, id, (_, _, [(_,srt)])) -> equalSort?(srtdef, srt)|_ -> false) srts in
    case foundSrt of
      | Some (q, classId, _) -> 
      %let _ = writeLine("matching user type found: sort "^classId^" = "^printSort(srtdef)) in
      Some (Base(mkUnQualifiedId(classId),[],srtPos))
      | None -> None
      %let _ = writeLine("no matching user type found for "^printSort(srtdef)) in
      %srtdef

(**
 * looks in the spec for a user type matching the given sort; if a matching
 * user type exists, the corresponding sort will be returned, otherwise the sort
 * given as input itself will be returned
 *)
op findMatchingUserType: Spec * Sort -> Sort
def findMatchingUserType(spc,srt) =
  case findMatchingUserTypeOption(spc,srt) of
    | Some s -> s
    | None -> srt



(**
 * this op looks for record sort and tries to fold them using sort definition in the spec
 *)
op foldRecordSorts_internal: Spec -> Spec
def foldRecordSorts_internal(spc) =
  let
    def foldRecordSort(srt) =
      case srt of
	| Product _ -> findMatchingUserType(spc,srt)
	| _ -> srt
  in
    mapSpec(id,foldRecordSort,id) spc


op foldRecordSorts: Spec -> Spec
def foldRecordSorts(spc) =
  let
    def foldRecordSorts0(spc,visited) =
      let srts = sortsAsList(spc) in
      case find (fn(q,i,sortinfo) -> 
		 case sortinfo of
		   | (_,_,(_,Product _)::_) -> ~(member(mkQualifiedId(q,i),visited))
		   | _ -> false) srts of
	| None -> spc
	| Some (q0,id0,sortinfo as (_,_,(_,psrt)::_)) ->
	  let qid0 = mkQualifiedId(q0,id0) in
	  %let _ = writeLine("product sort found: "^printQualifiedId(qid0)) in
	  let spc = foldRecordSorts_internal spc in
	  let srts = sortsAsList(spc) in
	  let srts = filter (fn(q1,id1,_) -> ~((q1=q0)&(id1=id0))) srts in
	  let sortmap = foldl (fn((q,id,sinfo),srtmap) ->
			       insertAQualifierMap(srtmap,q,id,sinfo))
	                emptyASortMap srts
	  in
	  let spc = setSorts(spc,insertAQualifierMap(sortmap,q0,id0,sortinfo)) in
	  foldRecordSorts0(spc,cons(qid0,visited))
  in
    foldRecordSorts0(spc,[])


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
def poly2mono(spc,keepPolyMorphic?) =
  let srts = spc.sorts in
  let ops = spc.ops in
  let (srts,minfo) =
    foldriAQualifierMap
    (fn(qu,i,(names,tyvars,defs),(map,minfo)) ->
     let (defs,minfo) =
       foldl (fn(def0 as (tv,srt),(defs,minfo)) ->
	      let (srt,minfo) = p2mSort(spc,srt,minfo) in
	      let ndef = (tv,srt) in
	      let defs = concat(defs,[ndef]) in
	      %let minfo = concat(minfo,minfo0) in
	      (defs,minfo)) ([]:List SortScheme,minfo) defs
     in
     (insertAQualifierMap(map,qu,i,(names,tyvars,defs)),minfo)
     ) (emptyASortMap,emptyMonoInfo) srts
  in
  let (ops,minfo) =
    foldriAQualifierMap
    (fn(qu,i,(names,fix,(mtv,srt),defs),(map,minfo)) ->
     let (defs,minfo) =
       foldl (fn(def0 as (tv,trm),(defs,minfo)) ->
	      let (trm,minfo) = p2mTerm(spc,trm,minfo) in
	      let ndef = (tv,trm) in
	      let defs = concat(defs,[ndef]) in
	      %let minfo = concat(minfo,minfo0) in
	      (defs,minfo)) ([],minfo) defs
     in
     let (srt,minfo) = p2mSort(spc,srt,minfo) in
     let nsortscheme = (mtv,srt) in
     (insertAQualifierMap(map,qu,i,(names,fix,nsortscheme,defs)),minfo)
     ) (emptyAOpMap,minfo) ops
  in
  let srts = foldr (fn(sinfo as ((Qualified(q,id))::_,_,_),map) -> insertAQualifierMap(map,q,id,sinfo))
            srts minfo.sorts
  in
  let ops = foldr (fn(opinfo as ((Qualified(q,id))::_,_,_,_),map) -> insertAQualifierMap(map,q,id,opinfo))
            ops minfo.ops
  in
  % remove polymorphic sort/op defs (disabled)
  let srts = if keepPolyMorphic? then srts else 
             foldriAQualifierMap
             (fn(q,id,info,map) ->
	      case info of
	       | (_,[],_) -> insertAQualifierMap(map,q,id,info)
	       | _ -> map) emptyASortMap srts
  in
  let ops = if keepPolyMorphic? then ops else
            foldriAQualifierMap
            (fn(q,id,info,map) ->
	     case info of
	       | (_,_,([],_),_) -> insertAQualifierMap(map,q,id,info)
	       | _ -> map) emptyAOpMap ops
  in
  let spc = setSorts(spc,srts) in
  let spc = setOps(spc,ops) in
  spc

op p2mSort: Spec * MS.Sort * SortOpInfos -> MS.Sort * SortOpInfos
def p2mSort(spc,srt,minfo) =
  case srt of
    | Base(qid0 as Qualified(q,id),insttv as _::_,b) ->
      if exists (fn(TyVar _) -> true | s -> false) insttv then (srt,minfo) else
      let suffix = getSortNameSuffix insttv in
      let qid = Qualified(q,id^suffix) in
      %let _ = writeLine("instantiated Sort: "^printQualifiedId(qid)) in
      let minfo = if monoInfosContainSort?(qid,minfo) then minfo
		  else
		    (case findTheSort(spc,qid0) of
		      | Some (names,tv as _::_,(_,srtdef)::_) ->
		        let tvsubst = zip(tv,insttv) in
			%let _ = writeLine("  "^(printTyVarSubst tvsubst)) in
			let names = cons(qid,(filter (fn(qid_) -> ~(qid_=qid0)) names)) in 
			let srtdef = applyTyVarSubst2Sort(srtdef,tvsubst) in
			let srtdef = addSortSuffixToConstructors(srtdef,suffix) in
			%let _ = writeLine("after applyTyVarSubst2Sort: "^printSort(srtdef)) in
			% add it first to prevent infinite loop:
			let tmp_sinfo = (names,[],[([],srtdef)]) in
			let minfo = addSortInfo2SortOpInfos(qid,tmp_sinfo,minfo) in
			let (srtdef,minfo) = p2mSort(spc,srtdef,minfo) in
			%let _ = writeLine("after p2mSort: "^printSort(srtdef)) in
			let sinfo = (names,[],[([],srtdef)]) in
			let minfo = exchangeSortInfoInSortOpInfos(qid,sinfo,minfo) in
			minfo
		      | _ -> minfo)
      in
      (Base(qid,[],b),minfo)
    | Arrow(srt1,srt2,b) ->
      let (srt1,minfo) = p2mSort(spc,srt1,minfo) in
      let (srt2,minfo) = p2mSort(spc,srt2,minfo) in
      (Arrow(srt1,srt2,b),minfo)
    | Product(fields,b) ->
      let (fields,minfo) = foldl (fn((id,srt),(fields,minfo)) ->
				  let (srt,minfo) = p2mSort(spc,srt,minfo) in
				  (concat(fields,[(id,srt)]),minfo))
                                  ([],minfo) fields
      in
      (Product(fields,b),minfo)
    | CoProduct(fields,b) ->
      let (fields,minfo) = foldl (fn((id,optsrt),(fields,minfo)) ->
				  let (optsrt,minfo) = (case optsrt of
							  | None -> (None,minfo)
							  | Some srt ->
							    let (srt,minfo) = p2mSort(spc,srt,minfo) in
							    (Some(srt),minfo))
				  in
				  (concat(fields,[(id,optsrt)]),minfo))
                                  ([],minfo) fields
      in
      (CoProduct(fields,b),minfo)
    | Quotient(srt,t,b) ->
      let (srt,minfo) = p2mSort(spc,srt,minfo) in
      let (t,minfo) = p2mTerm(spc,t,minfo) in
      (Quotient(srt,t,b),minfo)
    | Subsort(srt,t,b) ->
      let (srt,minfo) = p2mSort(spc,srt,minfo) in
      let (t,minfo) = p2mTerm(spc,t,minfo) in
      (Subsort(srt,t,b),minfo)
    | _ -> (srt,minfo)

op p2mTerm: Spec * MS.Term * SortOpInfos -> MS.Term * SortOpInfos
def p2mTerm(spc,term,minfo) =
  case term of
    | Apply(t1,t2,b) ->
      let (t1,minfo) = p2mTerm(spc,t1,minfo) in
      let (t2,minfo) = p2mTerm(spc,t2,minfo) in
      (Apply(t1,t2,b),minfo)
    | Bind(binder,varlist,t,b) ->
      let (varlist,minfo) = foldl (fn((id,srt),(varlist,minfo)) ->
				   let (srt,minfo) = p2mSort(spc,srt,minfo) in
				   (concat(varlist,[(id,srt)]),minfo))
                                  ([],minfo) varlist
      in
      let (t,minfo) = p2mTerm(spc,t,minfo) in
      (Bind(binder,varlist,t,b),minfo)
    | Record(fields,b) ->
      let (fields,minfo) = foldl (fn((id,t),(fields,minfo)) ->
				   let (t,minfo) = p2mTerm(spc,t,minfo) in
				   (concat(fields,[(id,t)]),minfo))
                            ([],minfo) fields
      in
      (Record(fields,b),minfo)
    | Let(patTerms,t,b) ->
      let (patTerms,minfo) = foldl (fn((pat,t),(patTerms,minfo)) ->
				    let (pat,minfo) = p2mPattern(spc,pat,minfo) in
				    let (t,minfo) = p2mTerm(spc,t,minfo) in
				    (concat(patTerms,[(pat,t)]),minfo))
                             ([],minfo) patTerms
      in
      let (t,minfo) = p2mTerm(spc,t,minfo) in
      (Let(patTerms,t,b),minfo)
    | LetRec(varTerms,t,b) ->
      let (varTerms,minfo) = foldl (fn(((id,srt),t),(varTerms,minfo)) ->
				    let (srt,minfo) = p2mSort(spc,srt,minfo) in
				    let (t,minfo) = p2mTerm(spc,t,minfo) in
				    (concat(varTerms,[((id,srt),t)]),minfo))
                             ([],minfo) varTerms
      in
      let (t,minfo) = p2mTerm(spc,t,minfo) in
      (LetRec(varTerms,t,b),minfo)
    | Var((id,srt),b) ->
      let (srt,minfo) = p2mSort(spc,srt,minfo) in
      (Var((id,srt),b),minfo)
    | Fun(fun,srt,b) -> 
      let (fun,srt,minfo) = p2mFun(spc,fun,srt,minfo) in
      (Fun(fun,srt,b),minfo)
    | Lambda(match,b) ->
      let (match,minfo) = foldl (fn((pat,t1,t2),(match,minfo)) ->
				    let (pat,minfo) = p2mPattern(spc,pat,minfo) in
				    let (t1,minfo) = p2mTerm(spc,t1,minfo) in
				    let (t2,minfo) = p2mTerm(spc,t2,minfo) in
				    (concat(match,[(pat,t1,t2)]),minfo))
                             ([],minfo) match
      in
      (Lambda(match,b),minfo)
    | IfThenElse(t1,t2,t3,b) ->
      let (t1,minfo) = p2mTerm(spc,t1,minfo) in
      let (t2,minfo) = p2mTerm(spc,t2,minfo) in
      let (t3,minfo) = p2mTerm(spc,t3,minfo) in
      (IfThenElse(t1,t2,t3,b),minfo)
    | Seq(terms,b) ->
      let (terms,minfo) = foldl (fn(t,(terms,minfo)) ->
				  let (t,minfo) = p2mTerm(spc,t,minfo) in
				  (concat(terms,[t]),minfo))
                             ([],minfo) terms
      in
      (Seq(terms,b),minfo)
    | SortedTerm(t,srt,b) ->
      let (t,minfo) = p2mTerm(spc,t,minfo) in
      let (srt,minfo) = p2mSort(spc,srt,minfo) in
      (SortedTerm(t,srt,b),minfo)
    | _ -> (term,minfo)

op p2mPattern: Spec * Pattern * SortOpInfos -> Pattern * SortOpInfos
def p2mPattern(spc,pat,minfo) =
  case pat of
    | EmbedPat(id,optPat,srt,b) ->
      let id = (case srt of
		  | Base(qid,insttv as _::_,_) ->
		    if exists (fn(TyVar _) -> true | s -> false) insttv then id else
		    id^(getSortNameSuffix insttv)
		  | _ -> id)
      in
      let (optPat,minfo) = (case optPat of
			      | None -> (None,minfo)
			      | Some pat ->
			        let (pat,minfo) = p2mPattern(spc,pat,minfo) in
				(Some pat,minfo))
      in
      let (srt,minfo) = p2mSort(spc,srt,minfo) in
      (EmbedPat(id,optPat,srt,b),minfo)
    | AliasPat(pat1,pat2,b) ->
      let (pat1,minfo) = p2mPattern(spc,pat1,minfo) in
      let (pat2,minfo) = p2mPattern(spc,pat2,minfo) in
      (AliasPat(pat1,pat2,b),minfo)
    | VarPat((id,srt),b) ->
      let (srt,minfo) = p2mSort(spc,srt,minfo) in
      (VarPat((id,srt),b),minfo)
    | RecordPat(fields,b) ->
      let (fields,minfo) = foldl (fn((id,pat),(fields,minfo)) ->
				  let (pat,minfo) = p2mPattern(spc,pat,minfo) in
				  (concat(fields,[(id,pat)]),minfo))
                                  ([],minfo) fields
      in
      (RecordPat(fields,b),minfo)
    | RelaxPat(pat,t,b) ->
      let (pat,minfo) = p2mPattern(spc,pat,minfo) in
      let (t,minfo) = p2mTerm(spc,t,minfo) in
      (RelaxPat(pat,t,b),minfo)
    | QuotientPat(pat,t,b) ->
      let (pat,minfo) = p2mPattern(spc,pat,minfo) in
      let (t,minfo) = p2mTerm(spc,t,minfo) in
      (QuotientPat(pat,t,b),minfo)
    | SortedPat(pat,s,b) ->
      let (pat,minfo) = p2mPattern(spc,pat,minfo) in
      let (s,minfo) = p2mSort(spc,s,minfo) in
      (SortedPat(pat,s,b),minfo)
    | _ -> (pat,minfo)

op p2mFun: Spec * Fun * MS.Sort * SortOpInfos -> Fun * MS.Sort * SortOpInfos
def p2mFun(spc,fun,srt,minfo) =
  let (srt1,minfo) = p2mSort(spc,srt,minfo) in
  case fun of
    | Embed(id,b?) ->
      %let _ = writeLine("constructor "^id^" found.") in
      let cpsrt = (case srt of
		     | Arrow(_,srt,_) -> srt
		     | _ -> srt
		  )
      in
      (case cpsrt of
	| Base(sqid,insttv as _::_,_) ->
	  if exists (fn(TyVar _) -> true | s -> false) insttv then (fun,srt1,minfo) else
	  let id = id^(getSortNameSuffix insttv) in
	  let fun = Embed(id,b?) in
	  (fun,srt1,minfo)
	| _ -> (fun,srt1,minfo)
	)
    | Op(qid as Qualified(q,id),fix) ->
      (case findTheOp(spc,qid) of
	| None -> (fun,srt1,minfo)
	| Some (names,fixi,(mtv,asrt),x as ((tv as (_::_),term)::terms)) -> 
	  %let _ = writeLine("polymorphic op found: "^printQualifiedId(qid)) in
	  let tvsubst0 = sortMatch(asrt,srt,spc) in
	  let tvsubst = filter (fn(id,TyVar _) -> false | _ -> true) tvsubst0 in
	  let ntv = map (fn(id,_) -> id) (filter (fn(id,TyVar _) -> true | _ -> false) tvsubst0) in
	  if tvsubst = [] then (fun,srt1,minfo) else
	  let nqid = Qualified(q,id^getSortNameFromTyVarSubst(tvsubst)) in
	  let names = cons(nqid,(filter (fn(qid0) -> ~(qid0 = qid)) names)) in
	  %let _ = writeLine("  New op name:"^(printQualifiedId nqid)) in
	  %let _ = writeLine("  "^(printTyVarSubst tvsubst)) in
	  let nfun = Op(nqid,fix) in
	  let minfo = if monoInfosContainOp?(nqid,minfo) then minfo
		      else
			% construct the new opinfo
			let term = applyTyVarSubst2Term(term,tvsubst) in
			%let _ = writeLine("substituted op term[1]: "^printTerm(term)) in
			let tmp_opinfo = (names,fixi,(mtv,srt1),x) in
			let tmp_minfo = addOpInfo2SortOpInfos(nqid,tmp_opinfo,minfo) in
			let (term,minfo) = p2mTerm(spc,term,tmp_minfo) in
			%let _ = writeLine("substituted op term[2]: "^printTerm(term)) in
			let nopinfo = (names,fixi,(ntv,srt1),[(ntv,term)]) in
			%let _ = writeLine("adding new opinfo for "^id^" with "^natToString(length(ntv))^" tyvars...") in
			let minfo = exchangeOpInfoInSortOpInfos(nqid,nopinfo,minfo) in
			%let _ = writeLine(printSortOpInfos minfo) in
			minfo
	  in
	  (nfun,srt1,minfo)
	| _ -> (fun,srt1,minfo)
	 )
    | _ -> (fun,srt1,minfo)



op printTyVarSubst: TyVarSubst -> String
def printTyVarSubst(tvsubst) =
  case tvsubst of
    | [] -> ""
    | [(id,srt)] -> id^" -> "^printSort(srt)
    | (id,srt)::tvsubst ->
      id^" -> "^printSort(srt) ^ ", "^printTyVarSubst(tvsubst)

op printSortOpInfos : SortOpInfos -> String
def printSortOpInfos minfo =
  let s1 = foldl (fn(((Qualified(_,id))::_,_,_,_),s) -> s^" "^id) "" minfo.ops in
  let s2 = foldl (fn(((Qualified(_,id))::_,_,_),s) -> s^" "^id) "" minfo.sorts in
  "ops: "^s1^newline^"sorts: "^s2
  

op getSortNameFromTyVarSubst: TyVarSubst -> String
def getSortNameFromTyVarSubst(subst) =
  getSortNameSuffix (map (fn(_,srt) -> srt) subst)

op getSortNameSuffix: List Sort -> String
def getSortNameSuffix(instlist) =
  case instlist of
    | [] -> ""
    | srt::instlist -> "_" ^ (sortId srt)^(getSortNameSuffix instlist)

op addOpInfo2SortOpInfos: QualifiedId * OpInfo * SortOpInfos -> SortOpInfos
def addOpInfo2SortOpInfos(nqid,opinfo,minfo) =
  let ops = minfo.ops in
  case find (fn(names,_,_,_) -> member(nqid,names)) ops of
    | Some _ -> minfo
    | None -> {ops = cons(opinfo,ops), sorts = minfo.sorts}

op exchangeOpInfoInSortOpInfos: QualifiedId * OpInfo * SortOpInfos -> SortOpInfos
def exchangeOpInfoInSortOpInfos(nqid,opinfo,minfo) =
  let ops = minfo.ops in
  let ops = filter (fn(names,_,_,_) -> ~(member(nqid,names))) ops in
  {ops = cons(opinfo,ops), sorts = minfo.sorts}

op monoInfosContainOp?: QualifiedId * SortOpInfos -> Boolean
def monoInfosContainOp?(nqid,minfo) =
  let ops = minfo.ops in
  case find (fn(names,_,_,_) -> member(nqid,names)) ops of
    | Some _ -> true
    | None -> false

op monoInfosContainSort?: QualifiedId * SortOpInfos -> Boolean
def monoInfosContainSort?(nqid,minfo) =
  let srts = minfo.sorts in
  case find (fn(names,_,_) -> member(nqid,names)) srts of
    | Some _ -> true
    | None -> false

op addSortInfo2SortOpInfos: QualifiedId * SortInfo * SortOpInfos -> SortOpInfos
def addSortInfo2SortOpInfos(nqid,sinfo,minfo) =
  if monoInfosContainSort?(nqid,minfo) then minfo else
    {ops = minfo.ops, sorts = cons(sinfo,minfo.sorts)}

op exchangeSortInfoInSortOpInfos: QualifiedId * SortInfo * SortOpInfos -> SortOpInfos
def exchangeSortInfoInSortOpInfos(nqid,sinfo,minfo) =
  let sorts = minfo.sorts in
  let sorts = filter (fn(names,_,_) -> ~(member(nqid,names))) sorts in
  {ops = minfo.ops, sorts = cons(sinfo,sorts)}

op applyTyVarSubst2Term: MS.Term * TyVarSubst -> MS.Term
def applyTyVarSubst2Term(trm,subst) =
  let def inst(srt) = instantiateTyVars(srt,subst) in
  mapTerm (id,inst,id) trm

op applyTyVarSubst2Sort: MS.Sort * TyVarSubst -> MS.Sort
def applyTyVarSubst2Sort(srt,subst) =
  let def inst(srt) = instantiateTyVars(srt,subst) in
  mapSort (id,inst,id) srt

op addSortSuffixToConstructors: MS.Sort * String -> MS.Sort
def addSortSuffixToConstructors(srt,suffix) =
  case srt of
    | CoProduct(fields,b) ->
      let fields = map (fn(id,optsrt) -> (id^suffix,optsrt)) fields in
      CoProduct(fields,b)
    | _ -> srt

op isEmptySortOpInfos?: SortOpInfos -> Boolean
def isEmptySortOpInfos?(minfo) =
  minfo.ops = [] & minfo.sorts = []

% --------------------------------------------------------------------------------

(**
 * add the ops and sort definitions that are defined in the bspc and used in the
 * spc to the spc, so that the resultung spec is self-contained.
 * ignore is a function that can be used to exclude certain qid's from being added
 * if ignore(qid) evaluates to true, the sort/op will be ignored, i.e. it will *not* be added.
 *)
op addMissingFromBase: Spec * Spec * (QualifiedId -> Boolean) -> Spec
def addMissingFromBase(bspc,spc,ignore) =
  let srts = spc.sorts in
  let ops = spc.ops in
  let minfo =
    foldriAQualifierMap
    (fn(qu,i,(names,tyvars,defs),minfo) ->
     foldl (fn(def0 as (tv,srt),minfo) ->
	    let minfo = addMissingFromSort(bspc,spc,ignore,srt,minfo) in
	    minfo) minfo defs
     ) emptyMonoInfo srts
  in
  let minfo =
    foldriAQualifierMap
    (fn(qu,i,(names,fix,(mtv,srt),defs),minfo) ->
     let minfo =
       foldl (fn((_,trm),minfo) ->
	      addMissingFromTerm(bspc,spc,ignore,trm,minfo))
	      minfo defs
     in
     let minfo = addMissingFromSort(bspc,spc,ignore,srt,minfo) in
     minfo
     ) minfo ops
  in
  if isEmptySortOpInfos?(minfo) then spc else
  %let _ = writeLine("added sorts: "^newline^printSortOpInfos(minfo)) in
  let srts = foldr (fn(sinfo as ((Qualified(q,id))::_,_,_),map) -> insertAQualifierMap(map,q,id,sinfo))
            srts minfo.sorts
  in
  let ops = foldr (fn(opinfo as ((Qualified(q,id))::_,_,_,_),map) -> insertAQualifierMap(map,q,id,opinfo))
            ops minfo.ops
  in
  let spc = setSorts(spc,srts) in
  let spc = setOps(spc,ops) in
  addMissingFromBase(bspc,spc,ignore)


op addMissingFromSort: Spec * Spec * (QualifiedId -> Boolean) * MS.Sort * SortOpInfos -> SortOpInfos
def addMissingFromSort(bspc,spc,ignore,srt,minfo) =
  case srt of
    | Arrow(srt1,srt2,_) ->
      let minfo = addMissingFromSort(bspc,spc,ignore,srt1,minfo) in
      addMissingFromSort(bspc,spc,ignore,srt2,minfo)
    | Product(fields,_) -> foldl (fn((_,srt),minfo) -> addMissingFromSort(bspc,spc,ignore,srt,minfo)) minfo fields
    | CoProduct(fields,_) -> foldl (fn((_,Some srt),minfo) -> addMissingFromSort(bspc,spc,ignore,srt,minfo)|_ -> minfo) minfo fields
    | Quotient(srt,term,_) -> addMissingFromTerm(bspc,spc,ignore,term,addMissingFromSort(bspc,spc,ignore,srt,minfo))
    | Subsort(srt,term,_) -> addMissingFromTerm(bspc,spc,ignore,term,addMissingFromSort(bspc,spc,ignore,srt,minfo))
    | Base(qid,srts,_) ->
      if ignore(qid) then minfo else
      let minfo = foldl (fn(srt,minfo) -> addMissingFromSort(bspc,spc,ignore,srt,minfo)) minfo srts in
      (case findTheSort(spc,qid) of
	 | Some _ -> minfo
	 | None -> (case findTheSort(bspc,qid) of
		      | None -> fail("can't happen: couldn't find sort definition for "^printQualifiedId(qid))
		      | Some sinfo ->
		        %let _ = writeLine("adding sort "^printQualifiedId(qid)^" from base spec.") in
		        addSortInfo2SortOpInfos(qid,sinfo,minfo)
		   )
	)
    | _ -> minfo


op addMissingFromTerm: Spec * Spec * (QualifiedId -> Boolean) * MS.Term * SortOpInfos -> SortOpInfos
def addMissingFromTerm(bspc,spc,ignore,term,minfo) =
  let def amt(t,minfo) = addMissingFromTerm(bspc,spc,ignore,t,minfo) in
  let def ams(s,minfo) = addMissingFromSort(bspc,spc,ignore,s,minfo) in
  let def amp(p,minfo) = addMissingFromPattern(bspc,spc,ignore,p,minfo) in
  case term of
    | Apply(t1,t2,_) -> amt(t2,amt(t1,minfo))
    | Record(fields,_) -> foldl (fn((_,t),minfo) -> amt(t,minfo)) minfo fields
    | Bind(_,vlist,t,_) ->
      let minfo = foldl (fn((_,srt),minfo) -> ams(srt,minfo)) minfo vlist in
      amt(t,minfo)
    | Let(ptlist,t,_) ->
      let minfo = foldl (fn((p,t),minfo) -> amp(p,amt(t,minfo))) minfo ptlist in
      amt(t,minfo)
    | LetRec(vtlist,t,_) ->
      let minfo = foldl (fn(((id,srt),t),minfo) -> ams(srt,amt(t,minfo))) minfo vtlist in
      amt(t,minfo)
    | Var((id,srt),_) -> ams(srt,minfo)
    | Lambda(match,_) -> foldl (fn((p,t1,t2),minfo) -> amt(t2,amt(t1,amp(p,minfo)))) minfo match
    | IfThenElse(t1,t2,t3,_) -> amt(t3,amt(t2,amt(t1,minfo)))
    | Seq(tl,_) -> foldl (fn(t,minfo) -> amt(t,minfo)) minfo tl
    | SortedTerm(t,s,_) -> ams(s,amt(t,minfo))
    | Fun(fun,srt,_) ->
      let minfo = ams(srt,minfo) in
      (case fun of
	 | Op(qid,_) ->
	   if ignore(qid) then minfo else
	   (case findTheOp(spc,qid) of
	      | Some _ -> minfo
	      | None -> (case findTheOp(bspc,qid) of
			   | None -> fail("can't happen: couldn't find op \""^printQualifiedId(qid)^"\"")
			   | Some opinfo ->
			     %let _ = writeLine("adding op "^printQualifiedId(qid)^" from base spec.") in
			     addOpInfo2SortOpInfos(qid,opinfo,minfo)
			    ))
	 | _ -> minfo
	)
    | _ -> minfo


op addMissingFromPattern: Spec * Spec * (QualifiedId -> Boolean) * MS.Pattern * SortOpInfos -> SortOpInfos
def addMissingFromPattern(bspc,spc,ignore,pat,minfo) =
  let def amt(t,minfo) = addMissingFromTerm(bspc,spc,ignore,t,minfo) in
  let def ams(s,minfo) = addMissingFromSort(bspc,spc,ignore,s,minfo) in
  let def amp(p,minfo) = addMissingFromPattern(bspc,spc,ignore,p,minfo) in
  case pat of
    | AliasPat(p1,p2,_) -> amp(p2,amp(p1,minfo))
    | VarPat((_,srt),_) -> ams(srt,minfo)
    | EmbedPat(_,Some p,s,_) -> amp(p,ams(s,minfo))
    | EmbedPat(_,None,s,_) -> ams(s,minfo)
    | RecordPat(fields,_) -> foldl (fn((_,p),minfo) -> amp(p,minfo)) minfo fields
    | WildPat(s,_) -> ams(s,minfo)
    | RelaxPat(p,t,_) -> amp(p,amt(t,minfo))
    | QuotientPat(p,t,_) -> amp(p,amt(t,minfo))
    | SortedPat(p,s,_) -> amp(p,ams(s,minfo))
    | _ -> minfo

%--------------------------------------------------------------------------------




endspec
