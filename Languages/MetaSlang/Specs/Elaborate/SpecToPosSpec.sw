spec {
 %%  convert standard terms to pos terms

 import ../StandardSpec
 import ../PosSpec

 op convertSpecToPosSpec       : Spec      -> PosSpec
 op convertSortInfoToPSortInfo : SortInfo  -> PSortInfo
 op convertOpInfoToPOpInfo     : OpInfo    -> POpInfo

 op convertTermToPTerm         : Term      -> PTerm
 op convertVarToPVar           : Var       -> PVar
 op convertVarsToPVars         : List Var  -> List PVar
 op convertPatternToPPattern   : Pattern   -> PPattern
 op convertSortToPSort         : Sort      -> PSort
 op convertFunToPFun           : Fun       -> PFun


 %% Half-baked conversion from StandardSpec to PosSpec
 def convertSpecToPosSpec {imports, importedSpec, sorts, ops, properties = _} =
  {imports      = imports,
   importedSpec = importedSpec,
   sorts        = mapAQualifierMap convertSortInfoToPSortInfo sorts,
   ops          = mapAQualifierMap convertOpInfoToPOpInfo     ops,
   properties   = emptyAProperties
  } 

 def convertSortInfoToPSortInfo (sort_names, tvs, opt_def : Option Sort) = 
  let new_opt_pdef : Option PSort =
      (case opt_def of
        | None     -> None
        | Some srt -> Some (convertSortToPSort srt))
  in
    (sort_names, tvs, new_opt_pdef)

 def convertOpInfoToPOpInfo (op_names, fixity, (tvs, srt), opt_def : Option Term) =
  let new_psrt = convertSortToPSort srt in
  let new_opt_pdef : Option PTerm =
      (case opt_def of
        | None     -> None
        | Some trm -> Some (convertTermToPTerm trm)) 
  in
    (op_names, fixity, (tvs, new_psrt), new_opt_pdef)


 %sort TVContext = StringMap TyVar
 %op tvToAst   : TyVar -> TyVar
 %op tvsToAst  : Nat * TyVars -> Nat * TVContext * TyVars
 %op qIdToAst  : QualifiedId -> IdInfo

 def convertTermToPTerm (term) =
     case term of
        | Apply(t1,t2,_) -> 
          ApplyN([convertTermToPTerm t1,convertTermToPTerm t2],pos0)
        | Record(fields,_) -> 
          Record(map(fn(f,t)-> (f,convertTermToPTerm t)) fields,pos0)
        | Bind(b,vars,term,_) -> 
          Bind(b,convertVarsToPVars vars,convertTermToPTerm term,pos0)
        | Let(decls,term,_) -> 
          Let(map (fn(pat,t)-> (convertPatternToPPattern pat,convertTermToPTerm t)) decls,convertTermToPTerm term,pos0)
        | LetRec(defs,term,_) -> 
          LetRec(map (fn(v,t)-> (convertVarToPVar v,convertTermToPTerm t)) defs,convertTermToPTerm term,pos0)
        | Var((n,s),_) -> Var((n,convertSortToPSort s),pos0)
        | Fun(f,s,_) -> 
          let srt = convertSortToPSort s in
          Fun(convertFunToPFun (f),srt,pos0)
        | Lambda(match,_) -> 
          Lambda(map 
                 (fn(pat,t1,t2)-> (convertPatternToPPattern pat,convertTermToPTerm t1,convertTermToPTerm t2))
                 match,pos0)
        | IfThenElse(t1,t2,t3,_) -> 
          IfThenElse(convertTermToPTerm t1,convertTermToPTerm t2,convertTermToPTerm t3,pos0)
        | Seq(terms,_) -> Seq(map convertTermToPTerm terms,pos0)

 def convertVarToPVar (n,s) =
   (n,convertSortToPSort s)

 def convertVarsToPVars vars =
   map convertVarToPVar vars

 def convertPatternToPPattern p = 
  case p of
   | StringPat   (s,          _) -> StringPat   (s,                    pos0)
   | BoolPat     (b,          _) -> BoolPat     (b,                    pos0)
   | CharPat     (c,          _) -> CharPat     (c,                    pos0)
   | NatPat      (n,          _) -> NatPat      (n,                    pos0)
   | VarPat      (v,          _) -> VarPat      (convertVarToPVar   v, pos0)
   | WildPat     (s,          _) -> WildPat     (convertSortToPSort s, pos0)

   | AliasPat    (p1, p2,     _) -> AliasPat    (convertPatternToPPattern p1, 
                                                 convertPatternToPPattern p2, 
                                                 pos0)
   | RelaxPat    (p,  t,      _) -> RelaxPat    (convertPatternToPPattern p,  
                                                 convertTermToPTerm t,        
                                                 pos0)
   | QuotientPat (p,  t,      _) -> QuotientPat (convertPatternToPPattern p,  
                                                 convertTermToPTerm t,        
                                                 pos0)
   | RecordPat   (fields,     _) -> RecordPat   (List.map (fn (f, s) -> (f, convertPatternToPPattern s)) fields, 
                                                 pos0)
   | EmbedPat    (n, pat, s,  _) -> EmbedPat    (n, 
                                                 case pat of
                                                  | None -> None
                                                  | Some p -> Some (convertPatternToPPattern p),
                                                 convertSortToPSort s,
                                                 pos0)

 def convertSortToPSort s = 
  case s of
   | Arrow     (s1, s2,    _) -> Arrow     (convertSortToPSort s1, 
                                            convertSortToPSort s2,
                                            pos0)
   | Product   (fields,    _) -> Product   (List.map (fn (f,s) -> (f,convertSortToPSort s)) fields,
                                            pos0)
   | CoProduct (fields,    _) -> CoProduct (List.map (fn (f,s) -> (f, case s of
                                                                         | None -> None
                                                                       | Some s -> Some (convertSortToPSort s)))
                                                      fields,
                                            pos0)
   | Quotient (s, t,       _) -> Quotient  (convertSortToPSort s, 
                                            convertTermToPTerm t, 
                                            pos0)
   | Subsort  (s, t,       _) -> Subsort   (convertSortToPSort s, 
                                            convertTermToPTerm t, 
                                            pos0)
   | Base     (qid, sorts, _) -> PBase     (qid, 
                                            List.map convertSortToPSort sorts,
                                            pos0)
   | TyVar    (tv,         _) -> TyVar     (tv, pos0)

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
}
