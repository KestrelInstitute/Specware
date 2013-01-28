MetaTransform qualifying
spec
import CurryUtils

type MetaTransform.TypedFun =
   | TFn (AnnTypeValue -> TypedFun)
   | TVal AnnTypeValue

type MTypeInfo = | Spec
                 | Term
                 | Arrows (List MTypeInfo * MTypeInfo)
                 | Str
                 | Num
                 | Bool
                 | OpName
                 | Rule
                 | Opt MTypeInfo
                 | List MTypeInfo
                 | Tuple(List MTypeInfo)
                 | Rec List(String * MTypeInfo)
                 | Monad MTypeInfo


op defaultAnnTypeValue(mty: MTypeInfo): Option AnnTypeValue =
  case mty of
    | Bool -> Some(BoolV false)
    | Opt _ -> Some(OptV None)
    | List _ -> Some(ListV [])
    | _ -> None

op mapAnnTypeValue (f: AnnTypeValue -> AnnTypeValue) (atv: AnnTypeValue): AnnTypeValue =
  let n_atv = f atv in
  case n_atv of
    | ArrowsV atvs -> ArrowsV(map (mapAnnTypeValue f) atvs)
    | OptV o_atv -> OptV(mapOption f o_atv)
    | ListV atvs -> ListV(map (mapAnnTypeValue f) atvs)
    | TupleV atvs -> TupleV(map (mapAnnTypeValue f) atvs)
    | RecV tagged_atvs -> RecV(map (fn (tgi, atvi) -> (tgi, mapAnnTypeValue f atvi)) tagged_atvs)
    | _ -> n_atv

op replaceSpecArg(atv: AnnTypeValue, spc: Spec): AnnTypeValue =
  mapAnnTypeValue (fn atvi ->
                     case atvi of
                       | SpecV _ -> SpecV spc
                       | _ -> atvi)
    atv

op annTypeValueType: MSType = mkBase(Qualified("MetaTransform", "AnnTypeValue"), [])
op typedFunType: MSType = mkBase(Qualified("MetaTransform", "TypedFun"), [])
op specType: MSType = mkBase(Qualified("AnnSpec", "Spec"), [])
op msTermType: MSType = mkBase(Qualified("MetaSlang", "MSTerm"), [])
op qualifiedIdType: MSType = mkBase(Qualified("MetaSlang", "QualifiedId"), [])
op ruleSpecType: MSType = mkBase(Qualified("AnnSpec", "RuleSpec"), [])
op monadAnnTypeValueType: MSType = mkBase(Qualified("SpecCalc", "Env"), [annTypeValueType])

op TFnTerm: MSTerm = mkEmbed1("TFn", mkArrow(mkArrow(annTypeValueType, typedFunType), typedFunType))
op TValTerm: MSTerm = mkEmbed1("TVal", mkArrow(annTypeValueType, typedFunType))
op monadVTerm: MSTerm = mkEmbed1("MonadV", mkArrow(monadAnnTypeValueType, annTypeValueType))
op returnTerm: MSTerm = mkOp(Qualified("SpecCalc", "return"), mkArrow(annTypeValueType, monadAnnTypeValueType))
op monadBindTerm: MSTerm = mkOp(Qualified("SpecCalc", "monadBind"),
                                mkArrow(mkProduct[mkBase(Qualified("SpecCalc", "Env"), [specType]),
                                                  mkArrow(specType, monadAnnTypeValueType)],
                                        mkArrow(annTypeValueType, monadAnnTypeValueType)))

op mkAnnTypeValueFun(ty_i: MTypeInfo): MSTerm =
  case ty_i of
    | Spec -> mkEmbed1("SpecV", mkArrow(specType, annTypeValueType))
    | Term -> mkEmbed1("TermV", mkArrow(msTermType, annTypeValueType))
    | Monad _ -> mkEmbed1("MonadV", mkArrow(monadAnnTypeValueType, annTypeValueType))
%    | Monad Spec -> mkEmbed1("MonadV", mkArrow(specType, annTypeValueType))
%    | Monad Term ->  mkEmbed1("TermV", mkArrow(msTermType, annTypeValueType))
    | _ -> fail ("Can only return Specs or MSTerms")

op varForMTypeInfo(ty_i: MTypeInfo): Var =
  case ty_i of
    | Spec -> ("spc__0", specType)
    | Term -> ("tm__0", msTermType)
    | _ -> fail ("Can only return Specs or MSTerms")


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
    | ArrowsV atvs -> ppSep (ppString " -> ") (map ppAnnTypeValue atvs)
    | StrV str -> ppString str
    | NumV n -> ppString(show n)
    | BoolV b -> ppString(show b)
    | OpNameV qid -> ppString(show qid)
    | RuleV rs -> ppRuleSpec rs
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

op AnnTypeValue.show(atv: AnnTypeValue): String =
  let pp = ppNest 2 (ppAnnTypeValue atv) in
  ppFormat(pp)

op MTypeInfo.show(ty_info: MTypeInfo): String =
  case ty_info of
    | Spec -> "Spec"
    | Term -> "Term"
    | Arrows(doms, ran) -> "("^(foldr (fn (d, result) -> show d^" -> "^result) (show ran^")") doms)^")"
    | Str  -> "Str"
    | Num  -> "Num"
    | Bool -> "Bool"
    | OpName -> "OpName"
    | Rule -> "Rule"
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
    | Monad Spec -> true
    | Arrows(tis, ran) -> transformResultType? ran
    | _ -> false

op argInfoFromType(ty: MSType, spc: Spec): Option MTypeInfo =
  % let _ = writeLine("argInfoFromType: "^printType ty) in
  let result =
      case ty of
        | Boolean _ -> Some Bool
        | Base(Qualified("AnnSpec", "Spec"), [], _)  -> Some Spec
        | Base(Qualified("Integer", "Nat"), [], _)   -> Some Num
        | Base(Qualified("Integer", "Int"), [], _)   -> Some Num
        | Base(Qualified("String", "String"), [], _) -> Some Str
        | Base(Qualified("MetaSlang", "QualifiedId"), [], _) -> Some OpName
        | Base(Qualified("MetaSlang", "MSTerm"), [], _) -> Some Term
        | Base(Qualified("MS", "MSTerm"), [], _) -> Some Term
        | Base(Qualified("AnnSpec", "RuleSpec"), [], _) -> Some Rule
        | Base(Qualified("SpecCalc", "Env"), [m_ty], _) ->  mapOption (fn el_info -> Monad el_info) (argInfoFromType(m_ty, spc))
        | Base(Qualified("List", "List"), [el_ty], _) -> mapOption (fn el_info -> List el_info) (argInfoFromType(el_ty, spc))
        | Base(Qualified("Option", "Option"), [op_ty], _) -> mapOption (fn op_info -> Opt op_info) (argInfoFromType(op_ty, spc))
        | Base _ -> let uf_ty = unfoldBase0 spc ty in
                    if equalType?(ty, uf_ty) then None
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
    % | Arrow(doms, ran) ->
    | Str  -> mkOp(Qualified("MetaTransform", "extractStr"), mkArrow(annTypeValueType, stringType))
    | Num  -> mkOp(Qualified("MetaTransform", "extractNum"), mkArrow(annTypeValueType, intType))
    | Bool -> mkOp(Qualified("MetaTransform", "extractBool"), mkArrow(annTypeValueType, boolType))
    | OpName -> mkOp(Qualified("MetaTransform", "extractOpName"), mkArrow(annTypeValueType, qualifiedIdType))
    | Rule -> mkOp(Qualified("MetaTransform", "extractRule"), mkArrow(annTypeValueType, ruleSpecType))
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
                 | _ ->  mkApply(mkAnnTypeValueFun(ran_tyi), main_comp)
  in
  let body = mkApply(TValTerm, val_tm) in
  let lam = foldr (fn (v, bod) -> mkApply(TFnTerm, mkLambda(mkVarPat v, bod)))
              body params in
  % let _ = writeLine(printTerm lam) in
  lam

op transformQualifier: Id = "SpecTransform"

op addTransformInfo(nm: Id, ty_info: MTypeInfo, tr_fn: TypedFun): TransformInfoMap =
  insertAQualifierMap(transformInfoMap, transformQualifier, nm, (ty_info, tr_fn))

op lookupTransformInfo(nm: Id): Option TransformInfo =
  findAQualifierMap(transformInfoMap, transformQualifier, nm)

op generateAddTransformUpdates(spc: Spec): List(QualifiedId * (MTypeInfo * MSTerm)) =
  foldriAQualifierMap
     (fn (q, id, info, result)->
        if q = transformQualifier
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
  case lookupTransformInfo nm of
    | None -> false
    | Some(ty_info, _) ->
      true

end-spec
