% derived from SW4/Languages/MetaSlang/ADT/Specs/Environment.sl v1.4
% Some names have had to be introduced qualified with SpecEnvironment
% to avoid clashes with others qualified with MetaSlang

(*
 * SpecEnvironment builds an association map of sort identifiers 
 * to their definitional unfolding. 
 *) 
 
SpecEnvironment qualifying
spec {
 import StandardSpec
 import Printer
 import /Library/Legacy/DataStructures/ListPair
 %% importing TypecChecker is overkill
 %import Elaborate/TypeChecker

 sort SpecEnvironment = StringMap Spec
 % sort Env             = SpecName * SpecEnvironment

 op makeEnv     : List Spec              -> SpecEnvironment
 op empty       : ()                     -> SpecEnvironment
 op add         : SpecEnvironment * Spec -> SpecEnvironment 
 op add_        : Spec * SpecEnvironment -> SpecEnvironment 
 op unfoldBase  : Spec * Sort -> Sort 
 op unfoldBaseV : Spec * Sort * Boolean -> Sort 
 op inferType   : Spec * MS.Term -> Sort

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

 op substSort : fa(a) List (Id * ASort a) * ASort a -> ASort a
 def substSort (S, srt) =
  let def find (name, S, a) =  
       case S 
         of []            -> TyVar(name,a)
          | (id, srt) ::S -> if name = id then srt else find (name, S, a) 
  in 
  let def substRec srt =  
       case srt of
          | Base (id,                   srts, a) ->  
            Base (id, List.map substRec srts, a) 

          | Arrow (         s1,          s2,  a) ->  
            Arrow (substRec s1, substRec s2,  a) 

          | Product (                                      fields, a) ->  
            Product (List.map (fn(id,s)-> (id,substRec s)) fields, a) 

          | CoProduct (fields, a) ->  
            CoProduct (List.map (fn (id, sopt)->
                                 (id,
                                  case sopt
                                    of None   -> None
                                     | Some s -> Some(substRec s))) 
                                fields,
                       a) 

          | Quotient (         srt, term, a) -> % No substitution for quotientsorts
            Quotient (substRec srt, term, a) 

          | Subsort  (         srt, term, a) -> % No substitution for subsorts
            Subsort  (substRec srt, term, a) 

          | TyVar (name, a) -> find (name, S, a)
  in 
  substRec srt 
 
 def unfoldBase (sp, srt) =
   unfoldBaseV (sp, srt, true)

 def unfoldBaseV (sp:Spec, srt, verbose) = 
  case srt
    of Base (qid, srts, a) ->
       (case findTheSort(sp,qid)
          of None -> srt
           | Some(_, _, [])      -> srt
           | Some(_, _, (type_vars, srt2)::_) ->
             let ssrt = substSort(zip(type_vars,srts), srt2) in
             unfoldBaseV (sp, ssrt, verbose))
     | _ -> srt

 op unfoldStripSort : Spec * Sort * Boolean -> Sort
 def unfoldStripSort (spc, srt, verbose) =
  unfoldStripSort1 (spc, srt, [], verbose)

 op unfoldStripSort1 : Spec * Sort * List(Sort) * Boolean -> Sort
 def unfoldStripSort1 (sp, srt, vsrts, verbose) =
  if List.member(srt,vsrts) then
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
       | TyVar (tv, a) -> srt
     

 op stripSubsorts : Spec * Sort -> Sort
 def stripSubsorts (sp, srt) = 
  case unfoldBase (sp, srt)
    of Subsort (srt, _, _) -> stripSubsorts (sp, srt)
     | srt -> srt

 op arrow : Spec * Sort -> Sort * Sort

 def arrow (sp : Spec, srt : Sort) = 
  case stripSubsorts (sp, srt)
    of Arrow (dom, rng, _) -> (dom, rng)
     | _ -> System.fail "Could not get function space sort"
     
 
 def product (sp : Spec, srt : Sort) = 
  case stripSubsorts (sp, srt)
    of Product (fields, _) -> fields
     | _ -> System.fail ("Could not extract product sort "^printSort srt)

 def coproduct (sp : Spec, srt : Sort) = 
  case stripSubsorts (sp, srt)
    of CoProduct (fields, _) -> fields
     | _ -> System.fail "Could not extract co-product sort"
  
 def domain (sp, srt) = 
  let (dom, _) = arrow (sp, srt) in dom
 
 def range (sp, srt) = 
  let (_, rng) = arrow (sp, srt) in rng

 op  arrowOpt     : Spec * Sort -> Option (Sort * Sort)
 op  rangeOpt     : Spec * Sort -> Option (Sort)
 op  productOpt   : Spec * Sort -> Option (List (Id * Sort))
 op  coproductOpt : Spec * Sort -> Option (List (Id * Option Sort))


 %- def arrowOpt(sp:Spec,srt:Sort) = 
 %-   let res = arrowOpt_(sp,srt) in
 %-   let _ = writeLine("arrowOpt("^printSort(srt)^")="^
 %-                       (case res
 %-                          of None -> "None"
 %-                           | Some(dom,rng) -> printSort(Arrow(dom,rng)))) in
 %-   res

 def arrowOpt (sp : Spec, srt : Sort) = 
  case stripSubsorts (sp, srt)
    of Arrow (dom, rng, _) -> Some (dom, rng)
     | _ -> None

 def rangeOpt (sp, srt) = 
  case arrowOpt (sp, srt)
    of None -> None
     | Some (_, rng) -> Some rng

 def productOpt (sp : Spec, srt : Sort) = 
  case stripSubsorts (sp, srt)
    of Product (fields, _) -> Some fields
     | _ -> None

 def coproductOpt (sp : Spec, srt : Sort) = 
  case stripSubsorts (sp, srt)
    of CoProduct (fields, _) -> Some fields
     | _ -> None

 def inferType (sp, tm : MS.Term) = 
  case tm
    of Apply      (t1, t2,               _) -> (case rangeOpt(sp,inferType(sp,t1))
                                                  of Some rng -> rng
                                                   | None -> 
                                                     System.fail 
                                                     ("Could not extract type for "^
                                                      printTermWithSorts tm))
     | Bind       _                         -> boolSort
     | Record     (fields,               a) -> Product(map (fn (id, t) -> 
							    (id, inferType (sp, t)))
						         fields,
                                                       a)
     | Let        (_, term,              _) -> inferType (sp, term)
     | LetRec     (_, term,              _) -> inferType (sp, term)
     | Var        ((_,srt),              _) -> srt
     | Fun        (_, srt,               _) -> srt
     | Lambda     (Cons((pat,_,body),_), _) -> mkArrow(patternSort pat,
                                                       inferType (sp, body))
     | Lambda     ([],                   _) -> System.fail 
                                                "inferType: Ill formed lambda abstraction"
     | IfThenElse (_, t2, t3,            _) -> inferType (sp, t2)
     | Seq        ([],                   _) -> Product ([], noPos)
     | Seq        ([M],                  _) -> inferType (sp, M)
     | Seq        (M::Ms,                _) -> inferType (sp, Seq(Ms, noPos))
     | _ -> System.fail "inferType: Non-exhaustive match"

% def SpecEnvironment.stringSort  : Sort = Base (Qualified ("String",  "String"),  [], noPos)
% def booleanSort : Sort = Base (Qualified ("Boolean", "Boolean"), [], noPos)
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
%   | RelaxPat    (pat, _,       _) -> SpecEnvironment.patternSort pat
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

(* ### unused
 op  getSortOfOp : Spec * String * String -> TyVars * Sort
 def getSortOfOp (spc, qid, opName) =
  % sjw: (4/02) Not sure if should check imports
  case findAQualifierMap (spc.ops, qid, opName)
    of None -> (printSpecToTerminal spc;
                System.fail ("Operator "^qid^"."^opName^" has not been declared"
                             ))
     | Some (op_names, fixity, (tyVars, srt), opt_def) -> (tyVars, srt)
*)

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
%                        (fn (spcn, spclist) ->
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
%  let allspecs = foldl (fn (spcname, spcs) ->
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
  case usrt
    of Arrow _ -> usrt
     | _       -> srt
(* *)


 %- --------------------------------------------------------------------------------
 (**
   determine the sort of a term including unfolding of base sorts.
  *)

(* ### unused
 op termSortEnv : Spec * MS.Term -> Sort
 def termSortEnv(sp,term) = 
  let res =
   case term 
     of Apply      (t1, t2,               _) -> 
        (case termSortEnv (sp, t1)
           of Arrow (dom, rng, _)            -> rng
            | _ -> System.fail ("Cannot extract sort of application "^
                                System.toString term))
      | Bind       _                         -> boolSort
      | Record     (fields,               _) -> Product(map (fn (id, t)-> 
                                                             (id, termSortEnv (sp, t)))
                                                            fields,
                                                        noPos)
      | Let        (_, term,              _) -> termSortEnv   (sp, term)
      | LetRec     (_, term,              _) -> termSortEnv   (sp, term)
      | Var        ((id, srt),            _) -> unfoldToArrow (sp, srt)
      | Fun        (fun, srt,             _) -> unfoldToArrow (sp, srt)
      | Lambda     (Cons((pat,_,body),_), _) -> mkArrow (patternSort pat,
                                                         termSortEnv (sp, body))
      | Lambda     ([],                   _) -> System.fail "Ill formed lambda abstraction"
      | IfThenElse (_, t2, t3,            _) -> termSortEnv   (sp, t2)
      | Seq        _                         -> mkProduct     []
      | _                                    -> System.fail "Non-exhaustive match"
  in
  %let _ = writeLine("termSortEnv: "^printTerm(term)^"="^printSort(res)) in
  res
*)
}
