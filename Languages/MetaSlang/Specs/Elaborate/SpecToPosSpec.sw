SpecToPosSpec qualifying spec {
 %%  convert standard terms to pos terms

 import ../StandardSpec
 % import ../PosSpec

 op convertSpecToPosSpec       : Spec      -> Spec
 def convertSpecToPosSpec spc = spc

(* ### unused
 op convertSortInfoToPSortInfo : SortInfo  -> MS.SortInfo
 op convertOpInfoToPOpInfo     : OpInfo    -> MS.OpInfo

 op convertTermToPTerm         : MS.Term      -> MS.Term
 op convertVarToPVar           : Var       -> MS.Var
 op convertVarsToPVars         : List Var  -> List MS.Var
 op convertPatternToPPattern   : Pattern   -> MS.Pattern
 op convertSortToPSort         : Sort      -> MS.Sort
 op convertFunToPFun           : Fun       -> MS.Fun
*)

(* ### unused
 * Remainder of the file is not longer used

 %% Half-baked conversion from StandardSpec to PosSpec
% def convertSpecToPosSpec {importInfo, sorts, ops, properties = _} =
%  {importInfo   = importInfo,
%   sorts        = mapAQualifierMap convertSortInfoToPSortInfo sorts,
%   ops          = mapAQualifierMap convertOpInfoToPOpInfo     ops,
%   properties   = emptyAProperties
%  } 

def convertSortInfoToPSortInfo info = info

% def convertSortInfoToPSortInfo (sort_names, tvs, opt_def : Option Sort) = 
%  let new_opt_pdef : Option PSort =
%      (case opt_def of
%        | None     -> None
%        | Some srt -> Some (convertSortToPSort srt))
%  in
%    (sort_names, tvs, new_opt_pdef)

def convertOpInfoToPOpInfo info = info

% def convertOpInfoToPOpInfo (op_names, fixity, (tvs, srt), opt_def : Option Term) =
%  let new_psrt = convertSortToPSort srt in
%  let new_opt_pdef : Option PTerm =
%      (case opt_def of
%        | None     -> None
%        | Some trm -> Some (convertTermToPTerm trm)) 
%  in
%    (op_names, fixity, (tvs, new_psrt), new_opt_pdef)

% def convertSortInfoToPSortInfo (sort_names, tvs, opt_def : Option Sort) = 
%  let new_opt_pdef : Option PSort =
%      (case opt_def of
%        | None     -> None
%        | Some srt -> Some (convertSortToPSort srt))
%  in
%    (sort_names, tvs, new_opt_pdef)

% def convertOpInfoToPOpInfo (op_names, fixity, (tvs, srt), opt_def : Option Term) =
%  let new_psrt = convertSortToPSort srt in
%  let new_opt_pdef : Option PTerm =
%      (case opt_def of
%        | None     -> None
%        | Some trm -> Some (convertTermToPTerm trm)) 
%  in
%    (op_names, fixity, (tvs, new_psrt), new_opt_pdef)


 %sort TVContext = StringMap TyVar
 %op tvToAst   : TyVar -> TyVar
 %op tvsToAst  : Nat * TyVars -> Nat * TVContext * TyVars
 %op qIdToAst  : QualifiedId -> IdInfo

 def convertTermToPTerm (term) =
   let pos = Internal "converted from linked term" in
   case term of
        | Apply(t1,t2,_) -> 
          ApplyN([convertTermToPTerm t1,convertTermToPTerm t2], pos)
        | Record(fields,_) -> 
          Record(map(fn(f,t)-> (f,convertTermToPTerm t)) fields,pos)
        | Bind(b,vars,term,_) -> 
          Bind(b,convertVarsToPVars vars,convertTermToPTerm term,pos)
        | Let(decls,term,_) -> 
          Let(map (fn(pat,t)-> (convertPatternToPPattern pat,convertTermToPTerm t)) decls,convertTermToPTerm term,pos)
        | LetRec(defs,term,_) -> 
          LetRec(map (fn(v,t)-> (convertVarToPVar v,convertTermToPTerm t)) defs,convertTermToPTerm term,pos)
        | Var((n,s),_) -> Var((n,convertSortToPSort s),pos)
        | Fun(f,s,_) -> 
          let srt = convertSortToPSort s in
          Fun(convertFunToPFun (f),srt,pos)
        | Lambda(match,_) -> 
          Lambda(map 
                 (fn(pat,t1,t2)-> (convertPatternToPPattern pat,convertTermToPTerm t1,convertTermToPTerm t2))
                 match,pos)
        | IfThenElse(t1,t2,t3,_) -> 
          IfThenElse(convertTermToPTerm t1,convertTermToPTerm t2,convertTermToPTerm t3,pos)
        | Seq(terms,_) -> Seq(map convertTermToPTerm terms,pos)

 def convertVarToPVar (n,s) =
   (n,convertSortToPSort s)

 def convertVarsToPVars vars =
   map convertVarToPVar vars

 def convertPatternToPPattern p = 
  let pos = Internal "converted from linked pattern" in
  case p of
   | StringPat   (s,          _) -> StringPat   (s,                    pos)
   | BoolPat     (b,          _) -> BoolPat     (b,                    pos)
   | CharPat     (c,          _) -> CharPat     (c,                    pos)
   | NatPat      (n,          _) -> NatPat      (n,                    pos)
   | VarPat      (v,          _) -> VarPat      (convertVarToPVar   v, pos)
   | WildPat     (s,          _) -> WildPat     (convertSortToPSort s, pos)

   | AliasPat    (p1, p2,     _) -> AliasPat    (convertPatternToPPattern p1, 
                                                 convertPatternToPPattern p2, 
                                                 pos)
   | RelaxPat    (p,  t,      _) -> RelaxPat    (convertPatternToPPattern p,  
                                                 convertTermToPTerm t,        
                                                 pos)
   | QuotientPat (p,  t,      _) -> QuotientPat (convertPatternToPPattern p,  
                                                 convertTermToPTerm t,        
                                                 pos)
   | RecordPat   (fields,     _) -> RecordPat   (List.map (fn (f, s) -> (f, convertPatternToPPattern s)) fields, 
                                                 pos)
   | EmbedPat    (n, pat, s,  _) -> EmbedPat    (n, 
                                                 case pat of
                                                  | None -> None
                                                  | Some p -> Some (convertPatternToPPattern p),
                                                 convertSortToPSort s,
                                                 pos)

 def convertSortToPSort s = 
  let pos = Internal "converted from linked sort" in
  case s of
   | Arrow     (s1, s2,    _) -> Arrow     (convertSortToPSort s1, 
                                            convertSortToPSort s2,
                                            pos)
   | Product   (fields,    _) -> Product   (List.map (fn (f,s) -> (f,convertSortToPSort s)) fields,
                                            pos)
   | CoProduct (fields,    _) -> CoProduct (List.map (fn (f,s) -> (f, case s of
                                                                         | None -> None
                                                                       | Some s -> Some (convertSortToPSort s)))
                                                      fields,
                                            pos)
   | Quotient (s, t,       _) -> Quotient  (convertSortToPSort s, 
                                            convertTermToPTerm t, 
                                            pos)
   | Subsort  (s, t,       _) -> Subsort   (convertSortToPSort s, 
                                            convertTermToPTerm t, 
                                            pos)
   | Base     (qid, sorts, _) -> Base      (qid, 
                                            List.map convertSortToPSort sorts,
                                            pos)
   | TyVar    (tv,         _) -> TyVar     (tv, pos)

 def convertFunToPFun (f) =
  case f of
   | Equals                -> Equals
   | Op       (qId, fixty) -> Op       (qId, fixty)
   | Project  x            -> Project  x
   | Embed    x            -> Embed    x
   | Embedded id           -> Embedded id
   | Nat      n            -> Nat      n
   | Char     c            -> Char     c
   | String   s            -> String   s
   | Bool     b            -> Bool     b
   | Quotient              -> Quotient 
   | Choose                -> Choose
   | Restrict              -> Restrict
   | Relax                 -> Relax
   | OneName  x            -> OneName  x
   | TwoNames x            -> TwoNames x
*)
}
