% derived from SW4/Languages/MetaSlang/ADT/Specs/Environment.sl v1.4
% Some names have had to be introduced qualified with SpecEnvironment
% to avoid clashes with others qualified with MetaSlang

(*
 * SpecEnvironment builds an association map of sort identifiers 
 * to their definitional unfolding. 
 *) 
 
SpecEnvironment qualifying
spec
 import Utilities
 import Printer
 import /Library/Legacy/DataStructures/ListPair
 %% importing TypecChecker is overkill
 %import Elaborate/TypeChecker

 type SpecEnvironment = StringMap Spec
 % sort Env             = SpecName * SpecEnvironment

 op makeEnv     : List Spec              -> SpecEnvironment
 op empty       : ()                     -> SpecEnvironment
 op add         : SpecEnvironment * Spec -> SpecEnvironment 
 op add_rev     : Spec * SpecEnvironment -> SpecEnvironment 

% %% makeSpecReportError is called only from ui::loadFile
% %%  (and from some mysterious GlueFront routines)
% def makeSpecReportError (specs, spc, env, fileName) = 
%  %% env will be ignored!
%  makeSpecReportError_ (specs, spc, env, true, fileName)

% def makeSpecNoMergeImportsReportError (specs, spc, env, fileName) =
%  %% env will be ignored!
%  makeSpecReportError_ (specs, spc, env, false, fileName)

% def makeSpecReportError_ (specs, spc, env, _(* mergeImports? *), fileName) =
%  let specs2 = StringMap.listItems (empty ()) in
%  %% env will be ignored!
%  case elaborateSpecReportError(specs2 ++ specs,spc,env,fileName) 
%    of Error msg -> Error msg
%     | Ok spc -> 
%       let spc = convertPosSpecToSpec spc in
%       let spc = addImportedSpecsEnv(spc,makeEnv specs2)
%       in Ok spc


 op unfoldBeforeCoProduct: Spec * Sort -> Sort
 def unfoldBeforeCoProduct(sp, srt) =
   case srt of
     | Base (qid, srts, a) ->
      (case findTheSort (sp, qid) of
	 | None -> srt
	 | Some info ->
	   if definedSortInfo? info then
	     let (tvs, fsrt) = unpackFirstSortDef info in
	     case fsrt of
	       | CoProduct _ -> srt
	       | _ -> 
	       let ssrt = substSort (zip (tvs, srts), fsrt) in
		 unfoldBeforeCoProduct (sp, ssrt)
	   else
	     srt)
    | _ -> srt

 %% This is dangerous as there may be recursion (I have removed calls to it -- sjw)
 op unfoldStripSort : Spec * Sort * Boolean -> Sort
 def unfoldStripSort (spc, srt, verbose) =
  unfoldStripSort1 (spc, srt, [], verbose)

 op unfoldStripSort1 : Spec * Sort * List(Sort) * Boolean -> Sort
 def unfoldStripSort1 (sp, srt, vsrts, verbose) =
  if typeIn?(srt, vsrts) then
    srt
  else
    case srt of
       | Arrow(srt1,srt2,a) -> 
         Arrow(unfoldStripSort1(sp,srt1,vsrts,verbose),
               unfoldStripSort1(sp,srt2,vsrts,verbose),
               a)
       | Product(srtlist, a) -> 
         Product(List.map (fn(id,s) -> (id,unfoldStripSort1(sp,s,vsrts,verbose))) srtlist,
                  a)
       | CoProduct (srtlist, a) -> 
         CoProduct (List.map (fn 
                              | (id, None)   -> (id, None)
                              | (id, Some s) -> (id, Some (unfoldStripSort1 (sp,
                                                                             s, 
                                                                             vsrts,
                                                                             verbose))))
                             srtlist,
                     a)
       | Quotient (srt, _,    _) -> unfoldStripSort1 (sp, srt, vsrts, verbose)
       | Subsort  (srt, t,    _) -> unfoldStripSort1 (sp, srt, vsrts, verbose)
       | Base     (qid, srts, a) ->
         let srts = List.map (fn(s) -> unfoldStripSort1 (sp, s, vsrts, verbose)) srts in
         let srt0 = Base (qid, srts, a) in
         let srt = unfoldBaseV (sp, srt0, verbose) in
         if srt = srt0 then
             srt
         else
          unfoldStripSort1 (sp, srt, List.cons(srt0,vsrts), verbose)
       | Boolean _ -> srt
       | TyVar (tv, a) -> srt
     

op stripRangeSubsorts(sp: Spec, srt: Sort, dontUnfoldQIds: List QualifiedId): Sort =
   case srt of
     | Base(qid, _, _) | qid in? dontUnfoldQIds -> srt
     | Subsort (s_srt, _, _) -> stripRangeSubsorts (sp, s_srt, dontUnfoldQIds)
     | Arrow (d_srt, r_srt, a)-> Arrow(d_srt, stripRangeSubsorts (sp, r_srt, dontUnfoldQIds), a)
     | Base _ ->
       let uf_srt = unfoldBase (sp, srt) in
       if equalType?(uf_srt, srt) || embed? CoProduct srt || embed? Quotient srt
         then srt
         else stripRangeSubsorts (sp, uf_srt, dontUnfoldQIds)
     | _ -> srt
   
 op booleanType?(spc: Spec, ty: Sort): Boolean =
   case ty of
     | Boolean _ -> true
     | Base _ ->
       (case tryUnfoldBase spc ty of
          | Some uf_ty -> booleanType?(spc, uf_ty)
          | None -> false)
     | _ -> false

 op arrow : Spec * Sort -> Sort * Sort

 def arrow (sp : Spec, srt : Sort) = 
   case stripSubsorts (sp, srt) of
     | Arrow (dom, rng, _) -> (dom, rng)
     | mystery ->
       % let _ = writeLine(printSpecFlat sp) in
       System.fail ("Could not extract arrow sort: " ^ (printSort srt) ^ " yielded " ^ (printSort mystery))
     
 def product (sp : Spec, srt : Sort) = 
   let srt = unfoldBase(sp,srt) in
   case stripSubsorts (sp, srt) of
     | Product (fields, _) -> fields
     | mystery -> System.fail ("Could not extract product sort: " ^ (printSort srt) ^ " yielded " ^ (printSort mystery))
      
 op  productSorts: Spec * Sort -> List Sort
 def productSorts (sp, srt1) =
   let srt = unfoldBase(sp,srt1) in
   case stripSubsorts (sp, srt)
    of Product (fields, _) ->
       if tupleFields? fields
	 then map (fn (_,x) -> x) fields
	 else [srt1]
     | _ -> [srt1]

 def coproduct (sp : Spec, srt : Sort) = 
  case stripSubsorts (sp, srt) of
    | CoProduct (fields, _) -> fields
    | mystery -> System.fail ("Could not extract co-product sort: " ^ (printSort srt) ^ " yielded " ^ (printSort mystery))
  
 def domain (sp, srt) = 
  let (dom, _) = arrow (sp, srt) in dom
 
 def range (sp, srt) = 
  let (_, rng) = arrow (sp, srt) in rng

 op  arrow?     : Spec * Sort -> Boolean
 def arrow? (sp, srt) =
   case stripSubsorts (sp, srt)
    of Arrow _ -> true
     | _ -> false

 %- def arrowOpt(sp:Spec,srt:Sort) = 
 %-   let res = arrowOpt_(sp,srt) in
 %-   let _ = writeLine("arrowOpt("^printSort(srt)^")="^
 %-                       (case res
 %-                          of None -> "None"
 %-                           | Some(dom,rng) -> printSort(Arrow(dom,rng)))) in
 %-   res


% def SpecEnvironment.stringSort  : Sort = Base (Qualified ("String",  "String"),  [], noPos)
% def booleanSort : Sort = Boolean noPos
% def SpecEnvironment.charSort    : Sort = Base (Qualified ("Char",    "Char"),    [], noPos)
% def integerSort : Sort = Base (Qualified ("Integer", "Integer"), [], noPos)

%% This is no different than MetaSlang.patternSort 
% op SpecEnvironment.patternSort : Pattern -> Sort
% def SpecEnvironment.patternSort = fn
%   | AliasPat   (pat1, _,       _) -> SpecEnvironment.patternSort pat1
%   | VarPat     ((_,srt),       _) -> srt
%   | EmbedPat   (_,_,srt,       _) -> srt
%   | RecordPat  (idpatternlist, _) -> let fields = List.map (fn (id, pat) -> 
%                                                             (id, SpecEnvironment.patternSort pat)) 
%                                                            idpatternlist in
%                                      Product (fields, noPos)
%   | WildPat     (srt,          _) -> srt
%   | StringPat   _                 -> SpecEnvironment.stringSort
%   | BoolPat     _                 -> booleanSort
%   | CharPat     _                 -> SpecEnvironment.charSort
%   | NatPat      _                 -> integerSort
%   | QuotientPat (pat, _,       _) -> SpecEnvironment.patternSort pat


 op mkRestrict    : Spec * {pred : MS.Term, term : MS.Term} -> MS.Term
 op mkProjectTerm : Spec * Id * MS.Term                  -> MS.Term
 op mkSelectTerm  : Spec * Id * MS.Term                  -> MS.Term

 def mkRestrict (sp, {pred, term}) = 
  let srt = inferType (sp, term) in
  let srt = mkArrow (srt, mkSubsort (srt, pred)) in
  mkApply ((Fun (Restrict, srt, noPos)), 
           term)
 
 def mkProjectTerm (sp, id, term) = 
  let srt = inferType (sp, term) in
  let fields = product (sp, srt) in
    (case List.find (fn (id2, s)-> id = id2) fields
       of Some (_, s) -> 
          mkApply(Fun (Project id, mkArrow(srt,s), noPos),
                  term)
        | _ -> System.fail "Projection index not found in product")

 def mkSelectTerm (sp, id, term) = 
  let srt    = inferType (sp, term) in
  let fields = coproduct (sp, srt)  in
  case List.find (fn (id2, s)-> id = id2) fields
    of Some (_,Some s) -> mkApply (Fun (Select id, mkArrow (srt, s), noPos),
                                   term)
     | _ -> System.fail "Selection index not found in product"

 
 % Assuming that op names are unambiguous in a spec
 % one can obtain the sort of ops given the name and spec only.

%%  ### unused
%%  op  getSortOfOp : Spec * String * String -> TyVars * Sort
%%  def getSortOfOp (spc, qid, opName) =
%%   % sjw: (4/02) Not sure if should check imports
%%   case findAQualifierMap (spc.ops, qid, opName)
%%     of None -> (printSpecToTerminal spc;
%%                 System.fail ("Operator "^qid^"."^opName^" has not been declared"
%%                              ))
%%      | Some (op_names, fixity, (tyVars, srt), opt_def) -> (tyVars, srt)
%% 

 %- ----------------------------------------------------------------
 %- get dependencies transitively
 %- ----------------------------------------------------------------

% op getDependenciesSpecTrans : SpecEnvironment * Spec -> List Spec
% def getDependenciesSpecTrans (env, spc) =
%  let
%   def getDependenciesSpecTrans0 (env, spclist : List Spec, spcsfinished : List Spec) =
%    case spclist
%      of [] -> spcsfinished
%       | spc :: spclist ->
%         let spcname = spc.name in
%         if member(spcname, List.map (fn(spc) -> spc.name) spcsfinished) then 
%          %- spec is already in the list of processed specs
%          getDependenciesSpecTrans0 (env, spclist, spcsfinished)
%         else
%          let specdepslist = StringSet.toList(getDependenciesSpec(spc)) in
%          let spcsfinished = cons(spc,spcsfinished) in
%          let spclist = List.foldl
%                        (fn (spclist, spcn) ->
%                         let spcnl = List.map (fn(spc) -> spc.name) spclist in
%                         if member (spcn, spcnl) then 
%                           spclist
%                         else
%                           case lookupSpec(env,spcn)
%                             of Some spc -> cons(spc,spclist)
%                              | None     ->
%                                (writeLine("*** WARNING: spec "^spcn^" not found ***");
%                                 spclist))
%                        spclist specdepslist
%          in
%            getDependenciesSpecTrans0(env,spclist,spcsfinished)
%  in
%  %- allspecs contain all specs that are used by specs + the spec itself
%  let allspecs = getDependenciesSpecTrans0(env,[spc],[]) in
%  let allspecs = foldl (fn (spcs,spcname) ->
%                        let spcnames = List.map (fn (spc : Spec) -> spc.name) spcs in
%                        if member (spcname, spcnames) then 
%                         spcs
%                        else
%                         case lookupSpec (env, spcname)
%                           of None     -> spcs
%                            | Some spc -> cons (spc, spcs))
%                         allspecs 
%                       primitiveSpecNames
%  in
%  let usedspecs = filter (fn(s) -> ~(s.name = spc.name)) allspecs in
%  usedspecs

 %- ---------------------------------------------------------------------------------
 %- calculate the minimal SpecEnvironment for a spec in that sense that the resulting
 %- SpecEnvironment contains only those specs that the input spec uses
 %- ---------------------------------------------------------------------------------

% op getMinimalSpecEnvironment : SpecEnvironment * Spec -> SpecEnvironment
% def getMinimalSpecEnvironment (env, spc) =
%  let usedspecs = getDependenciesSpecTrans (env, spc) in
%  StringMap.fromList (List.map (fn(spc) -> (spc.name, spc)) usedspecs)

 %- --------------------------------------------------------------------------
 %- search for a spec with a given name

(* ### unused
 op lookupSpec : SpecEnvironment * String -> Option Spec
 def lookupSpec (env, spcname) =
  StringMap.foldli (fn (_,     _,   Some spc) -> Some spc
                     | (sname, spc, None)     -> if sname = spcname 
                                                 then Some spc
                                                 else None)
                   None 
                   (env : StringMap Spec)
*)

 %- --------------------------------------------------------------------------------
 (**
  unfold to an arrow sort; if it doesn't unfold to an arrow, leave it unchanged.
  *)

(* ### unused #NO! **)
 op unfoldToArrow: Spec * Sort -> Sort
 def unfoldToArrow (sp, srt) =
  let 
    def unfoldRec srt = 
     let usrt = unfoldBase (sp, srt) in
     if usrt = srt then srt else unfoldRec usrt
  in
  let usrt = unfoldRec srt in
  case usrt of
    | Arrow _ -> usrt
    | _       -> srt

 %- --------------------------------------------------------------------------------
 (**
   determine the sort of a term including unfolding of base sorts.
  *)

 op termSortEnv : Spec * MS.Term -> Sort
 def termSortEnv(sp,term) = 
  let res =
   case term 
     of Apply      (t1, t2,               _) -> 
        (case stripSubsorts(sp,termSortEnv (sp, t1)) of
           | Arrow (dom, rng, _)            -> rng
	   | _ -> System.fail ("Cannot extract sort of application "^ printTerm term))
      | Bind       _                         -> boolSort
      | Record     (fields,               _) -> Product(map (fn (id, t)-> 
                                                             (id, termSortEnv (sp, t)))
                                                            fields,
                                                        noPos)
      | Let        (_, t,                 _) -> termSortEnv   (sp, t)
      | LetRec     (_, t,                 _) -> termSortEnv   (sp, t)
      | Var        ((_, srt),             _) -> unfoldToArrow (sp, srt)
      | Fun        (fun, srt,             _) -> unfoldToArrow (sp, srt)
      | Lambda     (Cons((pat,_,body),_), _) -> mkArrow (patternSort pat,
                                                         termSortEnv (sp, body))
      | Lambda     ([],                   _) -> System.fail "Ill formed lambda abstraction"
      | The        ((_,srt),_,            _) -> unfoldToArrow (sp, srt)
      | IfThenElse (_, t2, t3,            _) -> termSortEnv   (sp, t2)
      | Seq        _                         -> mkProduct     []
      | SortedTerm (_, s,                 _) -> s
      | Pi         (_, t,                 _) -> termSortEnv   (sp, t)
      | mystery                              ->
	System.fail ("In termSortEnv, unrecognized term: " ^ printTerm mystery)
  in
  %let _ = writeLine("termSortEnv: "^printTerm(term)^"="^printSort(res)) in
  res

  op  maybeIntroduceVarsForTerms: MS.Term * List MS.Term * Spec -> MS.Term
  def maybeIntroduceVarsForTerms(mainTerm,vterms,spc) =
  %% Introduces variables for vterms if they occur in mainTerm and they are non-trivial
    case filter(fn t -> ~(simpleTerm t) && (existsSubTerm (fn st -> st = t) mainTerm)) vterms of
      | [] -> mainTerm
      | rvterms ->
	let (_,vbinds) =
	      foldl (fn ((i,result),t) -> (i+1,result ++ [(t,"tv--"^toString i,inferType(spc,t))]))
	        (0,[]) rvterms
	in
	mkLet(map (fn (tm,v,s) -> (mkVarPat (v,s),tm)) vbinds,
	      mapTerm ((fn t -> case find (fn (tm,_,_) -> t = tm) vbinds of
				| Some(_,v,s) -> mkVar(v,s)
				| None -> t),
			id,id)
		 mainTerm)

  op  fieldAcessTerm: MS.Term * String * Spec -> MS.Term
  def fieldAcessTerm(t,field,spc) =
    case t of
      | Record(fields,_) ->
	(case getField(fields,field) of
	  | Some fld -> fld
	  | _ -> mkProjection(field,t,spc))	% Shouldn't happen
      | _ -> mkProjection(field,t,spc)

  op  mkProjection  : Id * MS.Term * Spec -> MS.Term
  def mkProjection (id, term, spc) = 
    let super_sort = termSort(term) in
    case productOpt(spc,super_sort) of
     | Some (fields) -> 
       (case find (fn (id2, _) -> id = id2) fields of
	 | Some (_,sub_sort) -> 
	   mkApply (mkProject (id, super_sort, sub_sort),term)
	 | _ -> System.fail ("Projection index "^id^" not found in product with fields "
                             ^(foldl (fn (res,(id2, _)) -> res^id2^" ") "" fields)
                             ^"at "^print(termAnn term)))
     | _ -> System.fail("Product sort expected for mkProjectTerm: "^printTermWithSorts term)


 op productLength(sp: Spec, srt:Sort): Nat = 
   case productOpt(sp,srt)
     of Some fields -> length fields
      | None -> 1

 op sortArity : Spec * Sort            -> Option(Sort * Nat)
 def sortArity(sp,srt) =
     case arrowOpt(sp,srt)
       of Some(dom,rng) -> 
          let len = productLength(sp,dom) in 
          if ~(len = 1)
             then Some (dom,len)
          else None
        | _ -> None

 def polymorphicDomainOp? (spc, idf) =
   case findTheOp (spc, idf) of
     | Some info -> 
       let srt = firstOpDefInnerSort info in
       polymorphicDomain? (spc, srt)
     | None -> false

 def polymorphicDomain? (sp, srt) =
   case arrowOpt (sp, srt) of
     | Some (TyVar _, _) -> true
     | _                -> false

 op mkCondEqualityFromLambdaDef(spc: Spec, lhs_tm: MS.Term, rhs_tm: MS.Term): MS.Term * List MS.Term =
   case rhs_tm of
     | Lambda ([(pat, _, body)], _) ->
       (case patternToTermPlusConds(pat) of
          | (Some arg_tm, conds) ->
            let (eql, r_conds) = mkCondEqualityFromLambdaDef(spc, mkApply(lhs_tm, arg_tm), body) in
            (eql, conds ++ r_conds)
          | (None, conds) -> (mkEquality (inferType(spc, lhs_tm), lhs_tm, rhs_tm), conds))
     | _ -> (mkEquality (inferType(spc, lhs_tm), lhs_tm, rhs_tm), [])

 op defToTheorem(spc: Spec, ty: Sort, name: QualifiedId, term: MS.Term): MS.Term =
    let (new_equality, conds) = mkCondEqualityFromLambdaDef (spc, mkOp(name, ty), term) in
    % let _ = writeLine("new_eq: "^printTerm new_equality) in
    let cond_equality = mkSimpImplies(mkSimpConj conds, new_equality) in
    let faVars       = freeVars cond_equality in
    let cond_equality = mkBind (Forall, faVars, cond_equality) in
    let eqltyWithPos = withAnnT (cond_equality, termAnn term) in
    eqltyWithPos

(*
 * Freshvar generates a unique suffix with the inserted name.
 *)

 type UsedNames = StringSet.Set

 op freshName: String * UsedNames -> String * UsedNames 
 def freshName(name0,names) = 
     let name1 = StringUtilities.freshName(name0,names) in
     (name1,StringSet.add(names,name1))

 def freshNames(name0,xs,names) =
     let (nameList,names) =  
             foldr (fn (_,(nameList,names)) -> 
                let (name1,names) = freshName(name0,names) in
                (cons(name1,nameList),names))
                ([],names) xs
     in
     (nameList,names)


 op normalizeLambda(term: MS.Term, usedNames: StringSet.Set, spc: Spec): MS.Term =
   case term of
     | Lambda((pat1,_,_)::(_::_),_) ->
       (let dom = patternSort pat1 in
        case productOpt(spc, dom) of
          | None ->
            let (name,_) = freshName("xx",usedNames) in
            let x = (name, dom) in
            mkLambda(mkVarPat x, mkApply(term, mkVar x))
          | Some fields ->
            let (names,_) = freshNames("xx",fields,usedNames) in
            let vars = map (fn (name,(label,srt)) -> (label,(name,srt))) (names,fields) in
            mkLambda(mkRecordPat(map (fn (l,v) -> (l, mkVarPat v)) vars),
                     mkApply(term, mkRecord(map (fn (l,v) -> (l, mkVar v)) vars))))
      | Lambda([(pat, cnd, bod)], pos) ->
        let usedNames = foldl (fn (usedNames, (vn,_)) ->
                                 StringSet.add(usedNames, vn))
                          usedNames (patVars pat)
        in
        Lambda([(pat, cnd, normalizeLambda(bod, usedNames, spc))], pos)
      | _ -> term

 op normalizeTopLevelLambdas(spc: Spec): Spec =
   setOps (spc, 
           mapOpInfos (fn info -> 
                         let pos = termAnn info.dfn in
                         let (old_decls, old_defs) = opInfoDeclsAndDefs info in
                         let new_defs =
                             map (fn dfn ->
                                    let pos = termAnn dfn in
                                    let (tvs, srt, term) = unpackTerm dfn in
                                    let tm = normalizeLambda(term, empty, spc) in
                                    maybePiTerm (tvs, SortedTerm (tm, srt, pos)))
                               old_defs
                         in
                           let new_dfn = maybeAndTerm (old_decls ++ new_defs, pos) in
                           info << {dfn = new_dfn})
           spc.ops)

endspec
