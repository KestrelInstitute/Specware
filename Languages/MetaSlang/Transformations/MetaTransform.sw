MetaTransform qualifying
spec
import CurryUtils, ../AbstractSyntax/PathTerm

type MetaTransform.TypedFun =
   | TFn (AnnTypeValue -> TypedFun)
   | TVal AnnTypeValue

type MTypeInfo = | Spec
                 | Term
                 | PathTerm
                 | Arrows (List MTypeInfo * MTypeInfo)
                 | Str
                 | Num
                 | Bool
                 | OpName
                 | Rule
                 | RefinementProof
                 | TransformHistory
                 | Opt MTypeInfo
                 | List MTypeInfo
                 | Tuple(List MTypeInfo)
                 | Rec List(String * MTypeInfo)
                 | Monad MTypeInfo

op existsMTypeInfo? (p: MTypeInfo -> Bool) (mti: MTypeInfo): Bool =
  p mti ||
    (case mti of
       | Arrows(mtis, rng) -> exists? (existsMTypeInfo? p) (rng::mtis)
       | Opt o_mti -> existsMTypeInfo? p o_mti
       | List l_mti -> existsMTypeInfo? p l_mti
       | Tuple mtis -> exists? (existsMTypeInfo? p) mtis
       | Rec tagged_mtis -> exists? (fn (_, mtii) -> existsMTypeInfo? p mtii) tagged_mtis
       | Monad mti1 -> existsMTypeInfo? p mti1
       | _ -> false)

op defaultAnnTypeValue(mty: MTypeInfo): Option AnnTypeValue =
  case mty of
    | Spec -> Some(SpecV emptySpec)
    | Term -> Some(TermV(Any noPos))
    | PathTerm -> Some(PathTermV(toPathTerm(Any noPos)))
    | Bool -> Some(BoolV false)
    | Opt _ -> Some(OptV None)
    | List _ -> Some(ListV [])
    | Num -> Some(NumV 0)
    | Str -> Some(StrV "")
    | Rec prs ->
      let new_prs = mapPartial (fn (id, val) -> mapOption (fn new_val -> (id, new_val))
                                                  (defaultAnnTypeValue val))
                      prs in
      if length new_prs = length prs
        then Some(RecV new_prs)
        else None
    | Tuple flds ->
      let fld_vals = mapPartial defaultAnnTypeValue flds in
      if length fld_vals = length flds
        then Some(TupleV fld_vals)
        else None
    | _ -> None

%% The next two give up on MonadV
op mapAnnTypeValue (f: AnnTypeValue -> AnnTypeValue) (atv: AnnTypeValue): AnnTypeValue =
  let n_atv = f atv in
  case n_atv of
    | ArrowsV atvs -> ArrowsV(map (mapAnnTypeValue f) atvs)
    | OptV o_atv -> OptV(mapOption f o_atv)
    | ListV atvs -> ListV(map (mapAnnTypeValue f) atvs)
    | TupleV atvs -> TupleV(map (mapAnnTypeValue f) atvs)
    | RecV tagged_atvs -> RecV(map (fn (tgi, atvi) -> (tgi, mapAnnTypeValue f atvi)) tagged_atvs)
    | _ -> n_atv

op existsAnnTypeValue? (p: AnnTypeValue -> Bool) (atv: AnnTypeValue): Bool =
  p atv ||
    (case atv of
       | ArrowsV atvs -> exists? (existsAnnTypeValue? p) atvs
       | OptV (Some o_atv) -> existsAnnTypeValue? p o_atv
       | ListV atvs -> exists? (existsAnnTypeValue? p) atvs
       | TupleV atvs -> exists? (existsAnnTypeValue? p) atvs
       | RecV tagged_atvs -> exists? (fn (_, atvi) -> existsAnnTypeValue? p atvi) tagged_atvs
       | _ -> false)

op replaceSpecArg(atv: AnnTypeValue, spc: Spec): AnnTypeValue =
  mapAnnTypeValue (fn atvi ->
                     case atvi of
                       | SpecV _ -> SpecV spc
                       | _ -> atvi)
    atv

op replaceTermArg(atv: AnnTypeValue, tm: MSTerm): AnnTypeValue =
   mapAnnTypeValue (fn atvi ->
                     case atvi of
                       | TermV(Any _) -> TermV tm
                       | _ -> atvi)
     atv

op replaceSpecTermArgs(atv: AnnTypeValue, spc: Spec, tm: MSTerm): AnnTypeValue =
   mapAnnTypeValue (fn atvi ->
                     case atvi of
                       | SpecV _ -> SpecV spc
                       | TermV(Any _) -> TermV tm
                       | _ -> atvi)
     atv

op replaceATVArgs(atv: AnnTypeValue, spc: Spec, path_tm: PathTerm, op_qid: QualifiedId): AnnTypeValue =
   mapAnnTypeValue (fn atvi ->
                     case atvi of
                       | SpecV _ -> SpecV spc
                       | TermV(Any _) -> TermV(fromPathTerm path_tm)
                       | PathTermV _ -> PathTermV path_tm
                       | OpNameV qid | qid = dummyQualifiedId -> OpNameV op_qid
                       | _ -> atvi)
     atv

 op extractMSTerm(tf: TypedFun): Option MSTerm =
   let def findTerm atv =
         case atv of
           | TermV tm -> Some tm
           | OptV(Some o_atv) -> findTerm o_atv
           | TupleV(atvs) ->
             (case mapPartial findTerm atvs of
                | tm :: _ -> Some tm
                | _ -> None)
           | _ -> None
   in
   case tf of
     | TVal atv -> findTerm atv
     | _ -> None

op extractProof(tf: TypedFun): Option RefinementProof =
   let def findTerm atv =
         case atv of
           | ProofV prf -> Some prf
           | OptV(Some o_atv) -> findTerm o_atv
           | TupleV(atvs) ->
             (case mapPartial findTerm atvs of
                | tm :: _ -> Some tm
                | _ -> None)
           | _ -> None
   in
   case tf of
     | TVal atv -> findTerm atv
     | _ -> None


op annTypeValueType: MSType = mkBase(Qualified("MetaTransform", "AnnTypeValue"), [])
op typedFunType: MSType = mkBase(Qualified("MetaTransform", "TypedFun"), [])
op specType: MSType = mkBase(Qualified("AnnSpec", "Spec"), [])
op msTermType: MSType = mkBase(Qualified("MS", "MSTerm"), [])
op pathTermType: MSType = mkBase(Qualified("PathTerm", "PathTerm"), [])
op refinementProofType: MSType = mkBase(Qualified("AnnSpec", "RefinementProof"), [])
op transformHistoryType: MSType = mkBase(Qualified("AnnSpec", "TransformHistory"), [])
op optionMsTermType: MSType = mkBase(Qualified("Option", "Option"), [msTermType])
op qualifiedIdType: MSType = mkBase(Qualified("MetaSlang", "QualifiedId"), [])
op ruleSpecType: MSType = mkBase(Qualified("AnnSpec", "RuleSpec"), [])
op monadAnnTypeValueType: MSType = mkBase(Qualified("SpecCalc", "Env"), [annTypeValueType])
op optionAnnTypeValueType: MSType = mkBase(Qualified("Option", "Option"), [annTypeValueType])

op TFnTerm: MSTerm = mkEmbed1("TFn", mkArrow(mkArrow(annTypeValueType, typedFunType), typedFunType))
op TValTerm: MSTerm = mkEmbed1("TVal", mkArrow(annTypeValueType, typedFunType))
op monadVTerm: MSTerm = mkEmbed1("MonadV", mkArrow(monadAnnTypeValueType, annTypeValueType))
op optVTerm: MSTerm = mkEmbed1("OptV", mkArrow(optionAnnTypeValueType, annTypeValueType))
op returnTerm: MSTerm = mkOp(Qualified("SpecCalc", "return"), mkArrow(annTypeValueType, monadAnnTypeValueType))
op monadBindTerm: MSTerm = mkOp(Qualified("SpecCalc", "monadBind"),
                                mkArrow(mkProduct[mkBase(Qualified("SpecCalc", "Env"), [specType]),
                                                  mkArrow(specType, monadAnnTypeValueType)],
                                        mkArrow(annTypeValueType, monadAnnTypeValueType)))
op mapOptionTerm: MSTerm =  mkOp(Qualified("Option", "mapOption"), mkArrow(annTypeValueType, optionAnnTypeValueType))

op mtiToMSType(mti: MTypeInfo): MSType =
  case mti of
    | Spec -> specType
    | Term -> msTermType
    | PathTerm -> pathTermType
    | Arrows (dom_mtis, r_mti) ->
      foldr (fn (mtii, ty) -> mkArrow(mtiToMSType mtii, ty)) (mtiToMSType r_mti) dom_mtis
    | Str -> stringType
    | Num -> intType
    | Bool -> boolType
    | OpName -> qualifiedIdType
    | Rule -> ruleSpecType   % ?
    | RefinementProof -> refinementProofType
    | TransformHistory -> transformHistoryType
    | Opt o_mti -> mkBase(Qualified("Option", "Option"), [mtiToMSType o_mti])
    | List l_mti -> mkBase(Qualified("List", "List"), [mtiToMSType l_mti])
    | Tuple mtis -> mkProduct(map mtiToMSType mtis)
    | Rec mtiprs -> mkRecordType(map (fn (id, mtii) -> (id, mtiToMSType mtii)) mtiprs)
    | Monad m_mti -> mkBase(Qualified("SpecCalc", "Env"), [mtiToMSType m_mti])

op mkAnnTypeValueFun(ty_i: MTypeInfo): MSTerm =
  case ty_i of
    | Spec -> mkEmbed1("SpecV", mkArrow(specType, annTypeValueType))
    | Term -> mkEmbed1("TermV", mkArrow(msTermType, annTypeValueType))
    | RefinementProof -> mkEmbed1("ProofV", mkArrow(refinementProofType, annTypeValueType))
    | TransformHistory -> mkEmbed1("TransformHistoryV", mkArrow(transformHistoryType, annTypeValueType))
    | Opt o_ty ->
      let arg_ty = mtiToMSType o_ty in
      let arg_v = ("o_result", arg_ty) in
      mkLambda(mkVarPat arg_v,
               mkApply(optVTerm,
                       mkApply(mkApply(mkOp(Qualified("Option", "mapOption"),
                                            mkArrow(mkArrow(arg_ty, annTypeValueType),
                                                    mkArrow(mtiToMSType ty_i, optionAnnTypeValueType))),
                                       mkAnnTypeValueFun o_ty),
                               mkVar arg_v)))
    | Monad _ -> mkEmbed1("MonadV", mkArrow(monadAnnTypeValueType, annTypeValueType))
%    | Monad Spec -> mkEmbed1("MonadV", mkArrow(specType, annTypeValueType))
    | Tuple tis ->
      let tp_vs = tabulate(length tis, fn i -> ("x"^show i, mtiToMSType(tis@i))) in
      let tv = ("tp_result", mkProduct(map (fn _ -> annTypeValueType) tis)) in
      mkLambda(mkVarPat tv,
               mkLet([(mkVarsPat tp_vs, mkVar tv)],
                     mkApply(mkEmbed1("TupleV", mkArrow(mkListType(annTypeValueType), annTypeValueType)),
                             mkList(map (fn (tii, v) -> mkApply(mkAnnTypeValueFun tii, mkVar v)) (zip(tis, tp_vs)),
                                    noPos, annTypeValueType))))
%    | Monad Term ->  mkEmbed1("TermV", mkArrow(msTermType, annTypeValueType))
    | _ -> fail ("Can only return Specs, MSTerms and RefinementProofs not "^show ty_i)

op varForMTypeInfo(ty_i: MTypeInfo): MSVar =
  case ty_i of
    | Spec -> ("spc__0", specType)
    | Term -> ("tm__0", msTermType)
    | RefinementProof -> ("prf__0", refinementProofType)
    | _ -> fail ("Can only return Specs, MSTerms or Proofs")


op apply(f as TFn tf: TypedFun, arg: AnnTypeValue): TypedFun =
  case arg of
    | ArrowsV args -> applyN(f, args)
    | _ ->  tf arg

op applyN(tf: TypedFun, args: List AnnTypeValue): TypedFun =
  case args of
    | [] -> tf
    | arg :: r_args -> applyN(apply(tf, arg), r_args)

%op applyM(f as TFn tf: TypedFun, arg: AnnTypeValue): Env TypedFun%  =
  % case arg of
  %   | ArrowsV args -> applyNM(f, args)
  %   | _ -> tf arg

%op applyNM(tf: TypedFun, args: List AnnTypeValue): Env TypedFun % =
  % case args of
  %   | [] -> tf
  %   | arg :: r_args -> applyNM(apply(tf, arg), r_args)



op Script.ppRuleSpec(rl: RuleSpec): WLPretty

op ppAnnTypeValue(atv: AnnTypeValue): Doc =
  case atv of
    | SpecV _ -> ppString "spec"
    | TermV _ -> ppString "term"
    | ArrowsV atvs -> ppSep (ppString " ") (map ppAnnTypeValue atvs)
    | StrV str -> ppString str
    | NumV n -> ppString(show n)
    | BoolV b -> ppString(show b)
    | OpNameV qid -> ppString(show qid)
    | RuleV rs -> ppRuleSpec rs
    | ProofV prf -> ppString(showRefinementProof prf)
    | OptV None -> ppString "None"
    | OptV (Some atv1) -> ppConcat[ppString "Some ", ppAnnTypeValue atv1]
    | ListV atvs -> ppConcat[ppString "[", ppSep (ppString ", ") (map ppAnnTypeValue atvs), ppString "]"]
    | TupleV atvs -> ppConcat[ppString "(", ppSep (ppString ", ") (map ppAnnTypeValue atvs), ppString ")"]
    | RecV id_atv_prs  -> ppConcat[ppString "{",
                                   ppSep (ppString ", ")
                                     (map (fn (id, atvi) ->
                                             ppConcat[ppString id, ppString ": ", ppAnnTypeValue atvi])
                                        id_atv_prs),
                                   ppString "}"]
    | MonadV atv1 -> ppConcat[ppString "Monad"]

op ppAbbrAnnTypeValue(atv: AnnTypeValue): Doc =
  let def ppOpt(atv: AnnTypeValue): Option Doc =
       case atv of
         | SpecV _ -> None
         | TermV _ -> None
         | PathTermV _ -> None
         | ArrowsV atvs -> Some(ppSep (ppString " ") (mapPartial ppOpt atvs))
         | StrV str -> Some(ppString str)
         | NumV n -> Some(ppString(show n))
         | BoolV b -> Some(ppString(show b))
         | OpNameV qid ->
           if qid = dummyQualifiedId then None else Some(ppString(show qid))
         | RuleV rs -> Some(ppRuleSpec rs)
         | ProofV prf -> None
         | OptV (Some atv1) -> ppOpt atv1
         | ListV atvs -> Some(ppConcat[ppString "[", ppSep (ppString ", ") (map ppSome atvs), ppString "]"])
         | TupleV atvs -> Some(ppConcat[ppString "(", ppSep (ppString ", ") (map ppSome atvs), ppString ")"])
         | RecV id_atv_prs  ->
           let flds = mapPartial (fn (id, atvi) ->
                                    case ppIfNotDefault atvi of
                                      | None -> None
                                      | Some doci -> 
                                        Some(ppConcat[ppString id, ppString " = ", doci]))
                        id_atv_prs
           in
           if flds = [] then None
             else Some(ppConcat[ppString "{", ppSep (ppString ", ") flds, ppString "}"])
         | MonadV atv1 -> None
     def ppIfNotDefault(atv: AnnTypeValue): Option Doc =
       case atv of
         | BoolV false -> None
         | NumV 0 -> None
         | StrV "" -> None
         | OptV None -> None
         | ListV [] -> None
         | _ -> ppOpt atv
     def ppSome(atv: AnnTypeValue): Doc =
       case ppOpt atv of
         | Some d -> d
         | None -> ppString ""
  in
  ppSome atv


op AnnTypeValue.show(atv: AnnTypeValue): String =
  let pp = ppNest 2 (ppAnnTypeValue atv) in
  ppFormat(pp)

op MTypeInfo.show(ty_info: MTypeInfo): String =
  case ty_info of
    | Spec -> "Spec"
    | Term -> "Term"
    | PathTerm -> "PathTerm"
    | Arrows(doms, ran) -> "("^(foldr (fn (d, result) -> show d^" -> "^result) (show ran^")") doms)^")"
    | Str  -> "Str"
    | Num  -> "Num"
    | Bool -> "Bool"
    | OpName -> "OpName"
    | Rule -> "Rule"
    | RefinementProof -> "RefinementProof"
    | TransformHistory -> "TransformHistory"
    | Opt i -> "Opt "^show i
    | List l -> "List "^show l
    | Tuple (l) -> "Tuple"^show l
    | Rec ((fld,i)::l) -> "Rec("^fld^": "^show i
                                     ^(foldr (fn ((fld, i), result) -> ", "^fld^": "^show i^result) ")" l)
    | Monad m -> "Monad "^show m

op MTypeInfos.show(ty_infos: List MTypeInfo): String =
  case ty_infos of
    | [] -> "()"
    | i::l -> "("^show i^foldr (fn (i, result) -> ", "^show i^result) ")" l

op transformResultType?(ti: MTypeInfo): Bool =
  case ti of
    | Spec -> true
    | Term -> true
    | Opt sti -> transformResultType? sti
    | RefinementProof -> true
    | Monad Spec -> true
    | Tuple tis -> exists? transformResultType? tis
    | Arrows(tis, ran) -> transformResultType? ran
    | _ -> false

op argInfoFromType(ty: MSType, spc: Spec): Option MTypeInfo =
  % let _ = writeLine("argInfoFromType: "^printType ty) in
  let result =
      case ty of
        | Boolean _ -> Some Bool
        | Base(Qualified("Bool", "Bool"), [], _)  -> Some Bool % otherwise fails below
        | Base(Qualified("AnnSpec", "Spec"), [], _)  -> Some Spec
        | Base(Qualified("Integer", "Nat"), [], _)   -> Some Num
        | Base(Qualified("Integer", "Int"), [], _)   -> Some Num
        | Base(Qualified("String", "String"), [], _) -> Some Str
        | Base(Qualified("MetaSlang", "QualifiedId"), [], _) -> Some OpName
        %| Base(Qualified("MetaSlang", "MSTerm"), [], _) -> Some Term
        | Base(Qualified("MS", "MSTerm"), [], _) -> Some Term
        | Base(Qualified("PathTerm", "PathTerm"), [], _) -> Some PathTerm
        | Base(Qualified("AnnSpec", "RuleSpec"), [], _) -> Some Rule
        | Base(Qualified("AnnSpec", "RefinementProof"), [], _) -> Some RefinementProof
        | Base(Qualified("AnnSpec", "TransformHistory"), [], _) -> Some TransformHistory
        | Base(Qualified("SpecCalc", "Env"), [m_ty], _) ->  mapOption (fn el_info -> Monad el_info) (argInfoFromType(m_ty, spc))
        | Base(Qualified("List", "List"), [el_ty], _) -> mapOption (fn el_info -> List el_info) (argInfoFromType(el_ty, spc))
        | Base(Qualified("Option", "Option"), [op_ty], _) -> mapOption (fn op_info -> Opt op_info) (argInfoFromType(op_ty, spc))
        | Base _ -> let uf_ty = unfoldBase0 spc ty in
                    if equalType?(ty, uf_ty) then None % Bool.Bool = Boolean, so Bool.Bool would fail here
                      else argInfoFromType(uf_ty, spc)
        | Arrow(dom, rng, _) ->
          (case (argInfoFromType(dom, spc), argInfoFromType(rng, spc)) of
             | (Some dom_info, Some ran_info) | transformResultType? ran_info ->
               let (r_doms, ran_info) = case ran_info of
                                          | Arrows (doms, ran_info) -> (doms, ran_info)
                                          | _ -> ([], ran_info)
               in
               Some(Arrows(dom_info :: r_doms, ran_info))
             | _ -> None)
        | Product(prs as ("1",_)::_, _) | tupleFields? prs->
          mapOption Tuple
            (foldr (fn ((_, fld_ty), o_flds) ->
                      case o_flds of
                        | None -> None
                        | Some flds ->
                      case argInfoFromType(fld_ty, spc) of
                        | None -> None
                        | Some fld_info -> Some(fld_info :: flds))
               (Some []) prs)
        | Product(prs, _) ->
          mapOption Rec
            (foldr (fn ((fld, fld_ty), o_flds) ->
                      case o_flds of
                        | None -> None
                        | Some flds ->
                      case argInfoFromType(fld_ty, spc) of
                        | None -> None
                        | Some fld_info -> Some((fld, fld_info) :: flds))
               (Some []) prs)
        | Subtype(s_ty, _, _) -> argInfoFromType(s_ty, spc)
        | _ -> None
  in
  % let _ = writeLine(" = "^(case result of
  %                            | None -> "None"
  %                            | Some i -> "Some "^show i))
  % in
  result

op mkExtractFn(tyi: MTypeInfo): MSTerm =
  case tyi of
    | Spec -> mkOp(Qualified("MetaTransform", "extractSpec"), mkArrow(annTypeValueType, specType))
    | Term -> mkOp(Qualified("MetaTransform", "extractTerm"), mkArrow(annTypeValueType, msTermType))
    | PathTerm -> mkOp(Qualified("MetaTransform", "extractPathTerm"), mkArrow(annTypeValueType, msTermType))
    % | Arrow(doms, ran) ->
    | Str  -> mkOp(Qualified("MetaTransform", "extractStr"), mkArrow(annTypeValueType, stringType))
    | Num  -> mkOp(Qualified("MetaTransform", "extractNum"), mkArrow(annTypeValueType, intType))
    | Bool -> mkOp(Qualified("MetaTransform", "extractBool"), mkArrow(annTypeValueType, boolType))
    | OpName -> mkOp(Qualified("MetaTransform", "extractOpName"), mkArrow(annTypeValueType, qualifiedIdType))
    | Rule -> mkOp(Qualified("MetaTransform", "extractRule"), mkArrow(annTypeValueType, ruleSpecType))
    | RefinementProof -> mkOp(Qualified("MetaTransform", "extractRefinementProof"), mkArrow(annTypeValueType, refinementProofType))
    | Opt i ->
      let el_tm = mkExtractFn i in
      let el_tm_ty as Arrow(_, el_ran_ty, _) = termType el_tm in
      mkApply(mkOp(Qualified("MetaTransform", "extractOpt"),
                   mkArrow(el_tm_ty, mkArrow(annTypeValueType, mkOptionType el_ran_ty))),
              el_tm)
    | List l ->
      let el_tm = mkExtractFn l in
      let el_tm_ty as Arrow(_, el_ran_ty, _) = termType el_tm in
      mkApply(mkOp(Qualified("MetaTransform", "extractList"),
                   mkArrow(el_tm_ty, mkArrow(annTypeValueType, mkListType el_ran_ty))),
              el_tm)
    | Tuple el_tyis ->
      let el_extr_fns = map mkExtractFn el_tyis in
      let el_tys = map (fn extr_fn -> let Arrow(_, ran, _) = termType extr_fn in ran) el_extr_fns in
      let el_vs = tabulate(length el_tys, fn i -> ("x_"^show i, el_tys@i)) in
      mkLambda(mkEmbedPat("TupleV", Some(mkListPat(map mkVarPat el_vs)), annTypeValueType),
               mkTuple(map (fn (v, extr_fn) -> mkApply(extr_fn, mkVar v)) (zip(el_vs, el_extr_fns))))
      
    | Rec (flds) ->
      let extr_fns = map (fn (id, el) -> (id, mkExtractFn el)) flds in
      let el_tys = map (fn (id, extr_fn) -> let Arrow(_, ran, _) = termType extr_fn in ran) extr_fns in
      let el_vs = tabulate(length el_tys, fn i -> ("x_"^show i, el_tys@i)) in
      mkLambda(mkEmbedPat("RecV", Some(mkListPat(map (fn el_v -> mkTuplePat[mkWildPat stringType, mkVarPat el_v]) el_vs)),
                          annTypeValueType),
               mkRecord(map (fn (v, (id, extr_fn)) -> (id, mkApply(extr_fn, mkVar v))) (zip(el_vs, extr_fns))))
    % | Monad m -> "Monad "^show m


type TransformInfo = MTypeInfo * TypedFun
type TransformInfoMap = AQualifierMap(TransformInfo)

op transformInfoMap: TransformInfoMap = emptyAQualifierMap

op annFunTerm(Arrows(dom_tyis, ran_tyi): MTypeInfo, qid: QualifiedId, op_ty: MSType, spc: Spec): MSTerm =
  let params = tabulate(length dom_tyis, fn i -> ("x_"^show i, annTypeValueType)) in
  let main_comp = mkCurriedApply(mkOp(qid, op_ty),
                                 map (fn (v, tyi) -> mkApply(mkExtractFn tyi, mkVar v)) (zip(params, dom_tyis))) in
  let val_tm = case ran_tyi of
                 | Monad m_ty ->
                   let val_v = varForMTypeInfo m_ty in
                   let return_tm = mkApply(returnTerm, mkApply(mkAnnTypeValueFun m_ty, mkVar val_v)) in
                   let return_lam = mkLambda(mkVarPat val_v, return_tm) in
                   let bind_tm = mkAppl(monadBindTerm, [main_comp, return_lam]) in
                   mkApply(monadVTerm, bind_tm)
                 % | Opt o_ty ->
                 %   let val_fn = mkAnnTypeValueFun o_ty in
                 %   let map_option_tm = mkCurriedApply(mapOptionTerm, [val_fn, main_comp]) in
                 %   mkApply(mkAnnTypeValueFun(ran_tyi), map_option_tm)
                 | _ ->  mkApply(mkAnnTypeValueFun(ran_tyi), main_comp)
  in
  let body = mkApply(TValTerm, val_tm) in
  let lam = foldr (fn (v, bod) -> mkApply(TFnTerm, mkLambda(mkVarPat v, bod)))
              body params in
  % let _ = writeLine(printTerm lam) in
  lam

op specTransformQualifier: String = "SpecTransform"
op msTermTransformQualifier: String = "MSTermTransform"
op msRuleQualifier: String = "MSRule"
op transformQualifiers: Ids = [specTransformQualifier, msTermTransformQualifier, msRuleQualifier]

op addTransformInfo(q: Id, nm: Id, ty_info: MTypeInfo, tr_fn: TypedFun): TransformInfoMap =
  insertAQualifierMap(transformInfoMap, q, nm, (ty_info, tr_fn))

op lookupTransformInfo(q: Id, nm: Id): Option TransformInfo =
  findAQualifierMap(transformInfoMap, q, nm)

op lookupSpecTransformInfo(nm: Id): Option TransformInfo =
  lookupTransformInfo(specTransformQualifier, nm)

op lookupMSTermTransformInfo(nm: Id): Option TransformInfo =
  lookupTransformInfo(msTermTransformQualifier, nm)

op lookupMSRuleInfo(nm: Id): Option TransformInfo =
  lookupTransformInfo(msRuleQualifier, nm)

op generateAddTransformUpdates(spc: Spec): List(QualifiedId * (MTypeInfo * MSTerm)) =
  foldriAQualifierMap
     (fn (q, id, info, result)->
        if q in? transformQualifiers
          then
            let (_, op_ty, _) = unpackFirstOpDef info in
            case argInfoFromType(op_ty, spc) of
              | Some(ty_info as Arrows _) ->
                (Qualified(q, id), (ty_info, annFunTerm(ty_info, Qualified(q, id), op_ty, spc))) :: result
              | _ -> result
        else result)
     []
     spc.ops

op transformInfoCommand?(nm: String): Bool =
  exists? (fn q -> some?(lookupTransformInfo(q, nm))) transformQualifiers

end-spec
