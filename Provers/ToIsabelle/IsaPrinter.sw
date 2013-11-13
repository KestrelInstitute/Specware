IsaTermPrinter qualifying spec

 %import /Languages/SpecCalculus/Semantics/Bootstrap
 import /Languages/MetaSlang/Transformations/TheoryMorphism
 import /Languages/MetaSlang/Transformations/NormalizeTypes
 %import /Languages/MetaSlang/Specs/Utilities
 %import /Library/PrettyPrinter/WadlerLindig
 import /Library/PrettyPrinter/BjornerEspinosa
 import /Library/Legacy/DataStructures/ListUtilities
 import /Languages/SpecCalculus/AbstractSyntax/Types                % including SCTerm
 import /Languages/SpecCalculus/Semantics/Value
 import /Languages/MetaSlang/Transformations/SubtypeElimination
 import /Languages/MetaSlang/Transformations/EmptyTypesToSubtypes
 import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities
 import /Languages/MetaSlang/Specs/TypeObligations
 import /Languages/MetaSlang/Specs/Environment
 import /Languages/MetaSlang/Transformations/Coercions
 import /Languages/MetaSlang/Transformations/LambdaLift
% import /Languages/MetaSlang/Transformations/InstantiateHOFns
 import /Languages/MetaSlang/AbstractSyntax/PathTerm
 import /Languages/MetaSlang/Transformations/RewriteRules
% import /Languages/MetaSlang/Transformations/ArityNormalize
 import /Languages/MetaSlang/Transformations/NormalizeTopLevelLambdas

 op addObligations?: Bool = true
 op lambdaLift?: Bool     = true
%% op simplify?: Bool       = false  %% now passed in and threaded through
 op usePosInfoForDefAnalysis?: Bool = true
 op printQuantifiersWithType?: Bool = true
 op autoProof: String = "by auto"
 op addExplicitTyping?: Bool = true
 op targetFunctionDefs?: Bool = true
 op unfoldMonadBinds?: Bool = true

 type Pretty = PrettyPrint.Pretty

 type Context = {printTypes?: Bool,
		 recursive?: Bool,
                 thy_name: String,
                 anon_thy_count: Ref Nat,
		 spec?: Option Spec,
                 currentUID: Option UnitId,
		 trans_table: TransInfo,
                 coercions: TypeCoercionTable,
                 overloadedConstructors: List String,
                 defaultProof: String,
                 newVarCount: Ref Nat,
                 source_of_thy_morphism?: Bool,
                 typeNameInfo: List(QualifiedId * TyVars * MSType),
                 simplify? : Bool}


 def getNewVar (c : Context) : Nat =
   let cnt = c.newVarCount in
   let _ = (cnt := !cnt + 1) in
   !cnt

 op  specialOpInfo: Context -> QualifiedId -> Option OpTransInfo
 def specialOpInfo c qid = apply(c.trans_table.op_map, qid)

 op  specialTypeInfo: Context -> QualifiedId -> Option TypeTransInfo
 def specialTypeInfo c qid = apply(c.trans_table.type_map, qid)

 op getSpec (c: Context): Spec = let Some spc = c.spec? in spc

 op getCurrentUID (c: Context): UnitId = let Some uid = c.currentUID in uid


 type ParentTerm = | Top | Nonfix | Infix Associativity * Nat
 type ParentType = | Top | ArrowLeft | ArrowRight | Product | CoProduct
                   | Quotient | Subtype | Apply

 % def prGrConcat x = prGroup (prConcat x)
 op prSymString(s: String): Pretty =
   if testSubseqEqual?("\\<", s, 0, 0)
     then lengthString(1, s)
     else prString(infixId s)

  %% --------------------------------------------------------------------------------
  %% Give the signature of utilities so we don't have to import them

  type GlobalContext
  %op  MonadicStateInternal.readGlobalVar : [a] String -> Option a
  op  Specware.evaluateUnitId: String -> Option Value
  %op  SpecCalc.findUnitIdForUnit: Value * GlobalContext -> Option UnitId
  %op  SpecCalc.uidToFullPath : UnitId -> String
  op  Specware.cleanEnv : SpecCalc.Env ()
  op  Specware.runSpecCommand : [a] SpecCalc.Env a -> a


  op  uidToIsaName : UnitId -> String
  def uidToIsaName {path, hashSuffix=_} =
   let device? = deviceString? (head path) in
   let main_name = last path in
   let path_dir = butLast path in 
   let mainPath = flatten (foldr (fn (elem, result) -> "/"::elem::result)
			        ["/Isa/", thyName main_name]
				(if device? then tail path_dir else path_dir))
   in if device?
	then (head path) ^ mainPath
	else mainPath


  op  printUIDtoThyFile: String * Bool * Bool -> String
  def printUIDtoThyFile (uid_str, recursive?, simplify?) =
    case Specware.evaluateUnitId uid_str of
      | Some val ->
        (case uidNamesForValue val of
	   | None -> "Error: Can't get UID string from value"
	   | Some (thy_nm, uidstr, uid) ->
	     let fil_nm = uidstr ^ ".thy" in
	     let _ = ensureDirectoriesExist fil_nm in
	     let _ = toFile(fil_nm, showValue(val, recursive?, Some uid, Some thy_nm, simplify?)) in
	     fil_nm)
      | _ -> "Error: Unknown UID " ^ uid_str

  op  deleteThyFilesForUID: String -> ()
  def deleteThyFilesForUID uidstr =
    case evaluateUnitId uidstr of
      | Some val ->
        deleteThyFilesForVal val
      | _ -> ()

  op  deleteThyFilesForVal: Value -> ()
  def deleteThyFilesForVal val =
    case uidNamesForValue val of
      | None -> ()
      | Some (_, uidstr, uid) ->
        if val = Spec(getBaseSpec())
          then ()
        else
        let fil_nm = uidstr ^ ".thy" in
	let _ = ensureFileDeleted fil_nm in
	case val of
	  | Spec spc ->
	    app (fn elem -> case elem of
		              | Import(sc_tm, im_sp, _, _) ->
		                deleteThyFilesForVal (Spec im_sp)
			      | _ -> ())
	      spc.elements
          | Morph morph -> deleteThyFilesForVal (Spec morph.dom)

  op  ensureFileDeleted: String -> ()
  def ensureFileDeleted fil_nm =
    if fileExists? fil_nm
      then deleteFile fil_nm
      else ()

  op  ensureValuePrinted: Context -> Value -> String
  def ensureValuePrinted c val =
    case uidStringPairForValue val of
      | None -> "Unknown"
      | Some ((thy_nm, fil_nm, hash_ext),uid) ->
        printValueIfNeeded(c, val, thy_nm, fil_nm, hash_ext, uid)

  op printValueIfNeeded
       (c: Context, val: Value, thy_nm: String, fil_nm: String, hash_ext: String, uid: UnitId): String =
    let full_thy_nm = if fil_nm = hash_ext then fil_nm else fil_nm ^ hash_ext in
    let thy_fil_nm = full_thy_nm ^ ".thy" in
    let sw_fil_nm = fil_nm ^ ".sw" in
    let _ = if fileOlder?(sw_fil_nm, thy_fil_nm)
              then ()
            else toFile(thy_fil_nm,
                        showValue(val, c.recursive?, Some uid, Some (full_thy_nm), c.simplify?))
    in thy_nm

  op  uidNamesForValue: Value -> Option (String * String * UnitId)
  def uidNamesForValue val =
    case uidStringPairForValue val of
      | None -> None
      | Some((thynm, filnm, hash), uid) ->
        Some(if thynm = hash then (thynm, filnm, uid)
             else (thynm ^ hash, filnm ^ hash, uid))

  op  uidStringPairForValue: Value -> Option ((String * String * String) * UnitId)
  def uidStringPairForValue val =
    case MonadicStateInternal.readGlobalVar "GlobalContext" of
      | None -> None
      | Some global_context ->
    case findUnitIdForUnit(val, global_context) of
      | None -> None
      | Some uid -> Some (unitIdToIsaString uid, uid)

  op unitIdToIsaString(uid: UnitId): (String * String * String) =
    case uid.hashSuffix of
      | Some loc_nm | loc_nm ~= last uid.path -> (last uid.path, uidToIsaName uid, "_" ^ loc_nm)
      | _ ->           (last uid.path, uidToIsaName uid, "")

  op isaLibrarySpecNames: List String = ["list", "integer", "nat", "set", "map", "fun",
                                         "option", "string",
                                         "lattices", "orderings", "sat", "relation", "record",
                                         "gcd", "datatype", "recdef", "hilbert_choice"]
  op thyName(spname: String): String =
    if (map toLowerCase spname) in? isaLibrarySpecNames
      then "SW_"^spname
      else spname

  op uidStringPairForValueOrTerm
       (c: Context, val: Value, sc_tm: SCTerm)
       : Option((String * String * String) * Value * UnitId) =
    case uidStringPairForValue val of
      | None ->
        (case uidStringPairForTerm(c, sc_tm) of
           | None -> None
           | Some((thynm, sw_file, thy_file), uid) ->
         case evaluateTermWrtUnitId(sc_tm, getCurrentUID c) of
           | None -> None
           | Some real_val ->
             Some((thyName thynm, sw_file, thyName thy_file ^ ".thy"),
                  val, uid))
      | Some((thynm, filnm, hash), uid) ->
        Some(if thynm = hash
               then (thyName(thynm),
                     uidToFullPath uid ^ ".sw",
                     thyName(filnm) ^ ".thy")
               else (thyName(thynm ^ hash),
                     uidToFullPath uid ^ ".sw",
                     thyName(filnm ^ hash) ^ ".thy"),
             val, uid)

  op strFromRenaming(renamings: RenamingRules, _: Position): String =
    case renamings of
      | [] -> "empty"
      | (Ambiguous(_, t_qid, _), _) :: _ -> show t_qid
      | (Type(_, t_qid, _), _) :: _ -> show t_qid
      | (Op(_, (t_qid, _), _), _) :: _ -> show t_qid
      | _ -> "unknown"

  op uidStringPairForTerm(c: Context, sc_tm: SCTerm): Option((String * String * String) * UnitId) =
    case sc_tm of
      | (Subst(spc_tm, morph_tm, _), pos) ->
        (case uidStringPairForTerm(c, spc_tm) of
           | None -> None
           | Some((thynm, sw_file, thy_file), uid) ->
             let sb_id = "_sb_" ^ scTermShortName morph_tm in
             Some((thynm^sb_id, sw_file, thy_file^sb_id),
                  uid))
      | (Translate(spc_tm, renaming), pos) ->
        (case uidStringPairForTerm(c, spc_tm) of
           | None -> None
           | Some((thynm, sw_file, thy_file), uid) ->
             let sb_id = "_tr_" ^ strFromRenaming renaming in
             Some((thynm^sb_id, sw_file, thy_file^sb_id),
                  uid))
      | (Qualify(spc_tm, qual), pos) ->
        (case uidStringPairForTerm(c, spc_tm) of
           | None -> None
           | Some((thynm, sw_file, thy_file), uid) ->
             let sb_id = "_qual_" ^ qual in
             Some((thynm^sb_id, sw_file, thy_file^sb_id),
                  uid))
      | (UnitId relId, pos) ->
        (case evaluateRelUIDWrtUnitId(relId, pos, getCurrentUID c) of
          | None -> None
          | Some(val, uid) ->
            let (thynm, filnm, hash) = unitIdToIsaString uid in
            Some(if thynm = hash
                   then (thynm,
                         uidToFullPath uid ^ ".sw",
                         filnm)
                   else (thynm ^ hash,
                         uidToFullPath uid ^ ".sw",
                         filnm ^ hash),
                 uid))
      | _ -> None

  op scTermShortName(sc_tm: SCTerm): String =
    case sc_tm of
      | (UnitId relId, _) -> relativeIdShortName relId
      | _ -> "tm"

  op relativeIdShortName(relId: RelativeUID): String =
    case relId of
      | UnitId_Relative uid -> unitIdShortName uid
      | SpecPath_Relative uid -> unitIdShortName uid
    
  op unitIdShortName(uid: UnitId): String =
    case uid of
      | {path, hashSuffix = Some nm} -> nm
      | {path, hashSuffix} -> last path

  op  evaluateRelUIDWrtUnitId(rel_uid: RelativeUID, pos: Position, currentUID: UnitId): Option (Value * UnitId) = 
    let
      %% Ignore exceptions
      def handler _ (* except *) =
        return None
    in
    let prog = {cleanEnv;
		setCurrentUID currentUID;
		((val, _, _), uid)  <- evaluateReturnUID pos rel_uid false;
		return (Some(val, uid))} 
    in
      runSpecCommand (catch prog handler)


  op  evaluateTermWrtUnitId(sc_tm: SCTerm, currentUID: UnitId): Option Value = 
    let
      %% Ignore exceptions
      def handler _ (* except *) =
        return None
    in
    let prog = {cleanEnv;
		setCurrentUID currentUID;
		val  <- evaluateTerm sc_tm;
		return (Some val)} 
    in
      runSpecCommand (catch prog handler)

  op  SpecCalc.findUnitIdForUnitInCache: Value -> Option UnitId
  def findUnitIdForUnitInCache val =
    case readGlobalVar "GlobalContext" of
      | None -> None
      | Some global_context ->
        findUnitIdForUnit(val, global_context)

  %% Seems to be dead code?:  
  op  printUID : String * Bool * Bool -> ()
  def printUID (uid, recursive?, simplify?) =
    case evaluateUnitId uid of
      | Some val -> toTerminal(showValue (val, recursive?, findUnitIdForUnitInCache val, None, simplify?))
      | _ -> toScreen "<Unknown UID>"

  op  showValue : Value * Bool * Option UnitId * Option String * Bool -> Text
  def showValue (value, recursive?, uid, opt_nm, simplify?) =
    let (thy_nm, val_uid) = case uidStringPairForValue value of
                             | Some ((thy_nm, _, hash_nm), uid) ->
                               (if thy_nm = hash_nm then thy_nm else thy_nm ^ hash_nm, Some uid)
                             | _ -> ("", None)
    in
    let main_pp_val = ppValue {printTypes? = false,
			       recursive? = recursive?,
			       thy_name = case opt_nm of
                                            | Some nm -> nm
                                            | None -> thy_nm,
			       anon_thy_count = Ref 0,
                               spec? = None,
                               currentUID = case uid of
                                              | None -> val_uid
                                              | _ -> uid,
			       trans_table = emptyTranslationTable,
                               coercions = [],
                               overloadedConstructors = [],
                               defaultProof = autoProof,
                               newVarCount = Ref 0,
                               source_of_thy_morphism? = false,
                               typeNameInfo = [],
                               simplify? = simplify?}
			value
    in
    format(110, main_pp_val)


  op SpecCalc.morphismObligations: Morphism * SpecCalc.GlobalContext * Position -> Spec
  %% --------------------------------------------------------------------------------

  op  ppValue : Context -> Value -> Pretty
  def ppValue c value =
    case value of
      | Spec spc -> ppSpec c spc
      | Morph morph ->
        let Some glob_ctxt = MonadicStateInternal.readGlobalVar "GlobalContext" in
        let oblig_spec = morphismObligations(morph, glob_ctxt, noPos) in
        ppSpec c oblig_spec
      | _ -> prString "<Not a spec>"
 
  %% --------------------------------------------------------------------------------
  %% Specs
  %% --------------------------------------------------------------------------------


  %% Convert definitions of ops mapped by thy morphism to theorems
  op thyMorphismDefsToTheorems (c: Context) (spc: Spec): Spec =
    let def maybeAddTheoremForDef(qid, el) =
          case specialOpInfo c qid of
            | Some(_,_,_,_,true) ->
              (case findTheOp(spc, qid) of
                 | Some {names=_, fixity=_, dfn, fullyQualified?=_} ->
                   let (tvs, ty, term) = unpackFirstTerm dfn in
                   let Qualified(q, nm) = qid in
                   % let _ = writeLine("def_tm: "^printTerm term) in
                   let initialFmla = defToTheorem(getSpec c, ty, qid, term) in
                   let liftedFmlas = removePatternTop(getSpec c, initialFmla) in
                   % let _ = app (fn fmla -> writeLine("def_thm1: "^printTerm fmla)) liftedFmlas in
                   let liftedFmlas = map (convertApplyToIn? spc) liftedFmlas in
                   let (_,thms) = foldl (fn((i, result), fmla) ->
                                           (i + 1,
                                            result ++ [mkConjecture(Qualified (q, nm^"__def"^(if i = 0 then ""
                                                                                              else show i)),
                                                                    tvs, fmla)]))
                                    (0, []) liftedFmlas
                   in
                   el::thms
                 | _ -> [el])
            | _ -> [el]
    in
    let newelements = foldr (fn (el, elts) ->
                              case el of
                                | Op(qid, true, _)    -> maybeAddTheoremForDef(qid, el) ++ elts
                                | OpDef(qid, 0, _, _) -> maybeAddTheoremForDef(qid, el) ++ elts
                                | _ -> el::elts)
                        [] spc.elements
    in
    spc << {elements = newelements}

  op renameRefinedDef(names: List QualifiedId, dfn: MSTerm, refine_num: Nat)
     : List QualifiedId * MSTerm =
    (map (refinedQID refine_num) names,
     mapTerm (fn t -> case t of
                       | Fun(Op(qid, inf), ty, a) | qid in? names ->
                         Fun(Op(refinedQID refine_num qid, inf), ty, a)
                       | _ -> t,
              id, id)
       dfn)

  op getArgVarsAndConstraints(spc: Spec, ty: MSType, o_dfn_tm: Option MSTerm, v_name: Id): MSTerm * MSTerms * Option MSTerm =
    case o_dfn_tm of
      | Some(Lambda([(pat, _, bod)], _)) ->
        let (pat_tm, conds, _) = patternToTermPlusExConds pat in
        (pat_tm, conds, Some bod)
      | _ ->
    case ty of
      | Subtype(s_ty, Lambda ([(pat, _, pred)], _), _) ->
        let (tm, conds, _) = patternToTermPlusExConds pat in
        (tm, conds ++ getConjuncts pred, None)
      | Subtype(s_ty, pred, _) ->
        let (tm, preds, _) = getArgVarsAndConstraints(spc, s_ty, None, v_name) in
        (tm, mkApply(pred, tm) :: preds, None)
      | _ ->
        let arg_tys = productTypes(spc, ty) in
        let vs = tabulate(length arg_tys, fn i -> mkVar(v_name^show i, arg_tys@i)) in
        (mkTuple vs, [], None)

  op mkFnEquality(ty: MSType, t1: MSTerm, t2: MSTerm, dfn: MSTerm, spc: Spec): MSTerm =
    let def mk_equality(o_dfn_tm, ty, t1, t2, preds, v_names) =
          % let _ = writeLine("mk_equality: "^printType ty^"\n"^printTerm t1^" = "^printTerm t2^"\n"^printTerm dfn) in
          case arrowOpt(spc, ty) of
            | Some(dom, rng) | v_names ~= [] && none?(subtypeOf(ty, Qualified("Set", "Set"), spc)) ->
              let v_name :: v_names = v_names in
              let (vs, new_preds, o_dfn_tm) = getArgVarsAndConstraints(spc, dom, o_dfn_tm, v_name) in
              % let arg_tys = productTypes(spc, dom) in
              % let vs = tabulate(length arg_tys, fn i -> mkVar(v_name^show i, arg_tys@i)) in
              mk_equality(o_dfn_tm, rng, mkApply(t1, vs), mkApply(t2, vs), preds ++ new_preds, v_names)
            | _ -> mkSimpImplies(mkSimpConj preds, mkEquality(ty, t1, t2))
    in
    let equality = mk_equality(Some dfn, ty, t1, t2, [], ["x", "y", "z"]) in
    case freeVars equality of
      | [] -> equality
      | fvs -> mkBind(Forall, fvs, equality)
  
  op equalityArgs(eq_tm: MSTerm): MSTerm * MSTerm =
    case eq_tm of
      | Apply(Fun(Implies, _, _), Record([("1", lhs), ("2", rhs)], _), _) -> equalityArgs rhs
      | Bind(_, _, bod, _) -> equalityArgs bod
      | Apply(_, Record([("1", lhs), ("2", rhs)], _), _) -> (lhs, rhs)
      | _ -> (eq_tm, trueTerm) 

  op makeTheorem(qid: QualifiedId, fml: MSTerm): SpecElement =
    let uvs = freeVars fml in
    let fml = mkSimpBind(Forall, uvs, fml) in
    Property(Theorem, qid, tyVarsInTerm fml, fml, termAnn fml)

  op makeNonTrivTheorem(q: Id, nm: Id, fml: MSTerm, spc: Spec): Option SpecElement =
    let s_fml = simplify spc fml in
    if equalTerm?(fml, trueTerm) then None
      else Some(makeTheorem(Qualified(q, nm), fml))

  op getResultExptAndPostCondn(ty: MSType, spc: Spec): Option(MSTerm * MSTerms) =
    case range_*(spc, ty, false) of
      | Subtype(result_ty, Lambda([(pat, _, condn)], _), _) ->
        let (result_tm, pat_conds, ign_vs) = patternToTermPlusExConds pat in
        Some(result_tm, pat_conds ++ getConjuncts condn)
      | _ -> None

 op extractLambdaVars(tm: MSTerm, f_tm: MSTerm): MSTerm * MSTerms =
   case tm of
     | Lambda([(pat, _, bod)], _) ->
       let (pat_tm, pat_conds, ign_vs) = patternToTermPlusExConds pat in
       let (res_tm, conds) = extractLambdaVars(bod, mkApply(f_tm, pat_tm)) in
       (res_tm, pat_conds ++ conds)
     | _ -> (f_tm, [])

 op mkObligTerm(qid: QualifiedId, new_ty: MSType, new_dfn: MSTerm, prev_ty: MSType, prev_dfn: MSTerm, spc: Spec)
      : MSTerm * MSTerm * MSTerm * MSTerm =
   % let _ = writeLine("Obligation for:\n"^printTerm (mkTypedTerm(new_dfn, new_ty))^"\n given\n"^printTerm(mkTypedTerm(prev_dfn, prev_ty))) in
   case (getResultExptAndPostCondn(new_ty, spc), getResultExptAndPostCondn(prev_ty, spc)) of
     | (Some(new_result_tm, new_post_condns), Some(old_result_tm, old_post_condns)) ->
       let f_tm = mkOp(qid, new_ty) in
       let (val_tm, param_conds) = extractLambdaVars(new_dfn, f_tm) in
       let rhs = mkConj(old_post_condns) in
       let condn = mkConj(param_conds ++ new_post_condns) in
       (mkSimpImplies(condn, rhs), mkConj new_post_condns, rhs, condn)
     | _ -> (trueTerm, trueTerm, trueTerm, trueTerm)

  op addRefineObligations (c: Context) (spc: Spec): Spec =
    %% Add equality or implication obligations for refined ops
    let (newelements, ops) =
        foldr (fn (el, (elts, ops)) ->
                 case el of
                   | OpDef(qid as Qualified(q,id), refine_num, _, _) | refine_num > 0 ->
                     let Some opinfo = findTheOp(spc, qid) in
                     let mainId = head opinfo.names in
                     let refId as Qualified(q,nm)  = refinedQID refine_num mainId in
                     let trps = unpackTypedTerms (opinfo.dfn) in
                     let (tvs, ty, dfn) = nthRefinement(trps, refine_num) in
                     % let _ = writeLine("addRefineObligations: "^show mainId^" "^show refine_num^": "^printType ty^"\n"^printTerm dfn
                     %                     ^"\n"^printTerm opinfo.dfn^"\n") in
                     let (_, prev_ty, prev_dfn) = nthRefinement(trps, refine_num - 1) in
                     let ops =
                         if anyTerm? dfn || anyTerm? prev_dfn then ops
                           else
                             let (new_names, new_dfn) = renameRefinedDef(opinfo.names, dfn, refine_num) in
                             let new_dfn = maybePiAndTypedTerm(replaceNthRefinement(trps, refine_num, (tvs, ty, new_dfn))) in
                             let new_opinfo = opinfo << {%names = new_names,
                                                           dfn   = new_dfn}
                             in
                             insertAQualifierMap (ops, q, id, new_opinfo)
                     in
                     %% Make refinement obligation obligations
                     let thm_name = (if anyTerm? dfn then id else nm)^"__"^"obligation_refine_def"^show refine_num in
                     if anyTerm? dfn
                       then
                         if anyTerm? prev_dfn
                           then    % Post-condition refinement
                             let thm_name = (if anyTerm? dfn then id else nm)^"__"^"obligation_refine_def"^show refine_num in
                             let (oblig, lhs, rhs, condn) = mkObligTerm(qid, ty, dfn, prev_ty, prev_dfn, spc) in
                             % let _ = writeLine("oblig: "^printTerm oblig) in
                             case makeNonTrivTheorem(q, thm_name, oblig, spc) of
                               | None -> (el::elts, ops)
                               | Some new_el ->
                                 (el::new_el::elts, ops)
                           else (el::elts, ops)   % Not sure if this is meaningful
                       else
                         if anyTerm? prev_dfn
                           then (el::elts, ops)    % !!! place holder
                           else
                             let thm_name = (if anyTerm? dfn then id else nm)^"__"^"obligation_refine_def" in
                             let eq_tm = mkFnEquality(ty, mkOpFromDef(mainId, ty, spc), mkInfixOp(refId, opinfo.fixity, ty),
                                                      prev_dfn, spc) in
                             let eq_oblig = mkConjecture(Qualified(q, thm_name), tvs, eq_tm) in
                             (el::eq_oblig::elts, ops)
                   | _ -> (el::elts, ops))
           ([], spc.ops) spc.elements
    in
    spc << {elements = newelements,
            ops      = ops}

  op addRefinementProofs (c: Context) (spc: Spec): Spec =
    let newelements =
        foldr (fn (el, elts) ->
                 case el of
                   | OpDef(qid as Qualified(q,id1), refine_num, Some (hist, pf), _) | refine_num > 0 && (hist ~= [] || pf ~= None) ->
                     let Some opinfo = findTheOp(spc, qid) in
                     let mainId = head opinfo.names in
                     let refId as Qualified(q,nm)  = refinedQID refine_num mainId in
                     let tsp = (relativizeQuantifiers spc, id, id) in
                     let hist = map (fn (tm, rl) -> (mapTerm tsp tm, rl)) hist in
                     let pf = mapRefinementProofOpt (mapTerm tsp) pf in
                     let trps = unpackTypedTerms (mapTerm tsp opinfo.dfn) in
                     let (tvs, ty, dfn) = nthRefinement(trps, refine_num) in
                     let (_, prev_ty, prev_dfn) = nthRefinement(trps, refine_num - 1) in

                     %% Make refinement obligation proof
                     let thm_name = (if anyTerm? dfn then id1 else nm)^"__"^"obligation_refine_def"^show refine_num in
                     % let _ = writeLine("arp: "^thm_name^" "^show(embed? Property (head elts))) in
                     % let _ = writeLine(printTerm dfn^"\n"^printTerm prev_dfn) in 
                     if anyTerm? dfn
                        then
                          if anyTerm? prev_dfn
                            then    % Post-condition refinement
                              let thm_name = (if anyTerm? dfn then id1 else nm)^"__"^"obligation_refine_def"^show refine_num in
                              let (oblig, lhs, rhs, condn) = mkObligTerm(qid, ty, dfn, prev_ty, prev_dfn, spc) in
                              if equalTerm?(oblig, trueTerm) then el::elts
                              else
                              % let _ = writeLine("oblig: "^printTerm oblig) in
                              % let _ = writeLine("Generating proof for "^thm_name) in
                              let prf_str =
                                case pf of
                                    % if we have an implication proof, convert it to Isabelle
                                  | Some (RefineStrengthen impl_pf) ->
                                    generateImplicationProof (c, condn, rhs, impl_pf)
                                  | Some (RefineEq eq_pf) ->
                                    generateImplicationProof (c, condn, rhs, ImplEq eq_pf)
                                    % otherwise, fall back on old method based on TransformHistory
                                  | _ -> generateProofForRefinedPostConditionObligation(c, lhs, rhs, condn, hist)
                              in
                              let prf_el = Pragma("proof", " Isa "^thm_name^"\n"^prf_str, "end-proof", noPos) in
                              % let _ = writeLine("Proof string:\n"^prf_str) in
                              el::prf_el::elts
                            else el::elts   % Not sure if this is meaningful
                        else
                          if anyTerm? prev_dfn
                            then el::elts    % !!! place holder
                            else
                              let thm_name = (if anyTerm? dfn then id1 else nm)^"__"^"obligation_refine_def" in
                              let eq_tm = mkFnEquality(ty, mkOpFromDef(mainId, ty, spc), mkInfixOp(refId, opinfo.fixity, ty),
                                                       prev_dfn, spc) in
                              let prf_str =
                                case pf of
                                    % if we have an equality proof, convert it to Isabelle
                                  | Some (RefineEq eq_pf) ->
                                    generateEqualityProof (c, eq_tm, prev_dfn, eq_pf)
                                    % otherwise, fall back on old method based on TransformHistory
                                  | _ -> generateProofForRefineObligation(c, eq_tm, prev_dfn, hist, spc)
                              in
                              let prf_el = Pragma("proof", " Isa "^thm_name^"\n"^prf_str, "end-proof", noPos) in
                              % let _ = writeLine("Proof string:\n"^prf_str) in
                              el::prf_el::elts

                   | _ -> el::elts)
           [] spc.elements
    in
    spc << {elements = newelements}


%%%
%%% generating Isabelle proofs from TransformHistories (old approach)
%%%

  op fnQidOfTerm(tm: MSTerm): QualifiedId =
    case tm of
      | Fun(Op(qid, _), _, _) -> qid
      | Apply(f, _, _) -> fnQidOfTerm f

  op isaDefString(tm: MSTerm): String =
    let fn_qid = fnQidOfTerm tm in
    qidToIsaString fn_qid ^ "_def"

  op foldFn(tm: MSTerm): String =
    let def_str = isaDefString tm in
    "fold "^def_str^", rule HOL.refl"

  op unfoldFn(tm: MSTerm): String =
    let def_str = isaDefString tm in
    "unfold "^def_str^", rule HOL.refl"

  op pathWithinDef(lhs: MSTerm): PathTerm.Path =
    case lhs of
      | Apply(f, _, _) -> 0 :: pathWithinDef f
      | _ -> []

 op cleanupCommand(qid: QualifiedId, spc: Spec): String =
   case findTheOp(spc, qid) of
     | None -> ", rule HOL.refl"
     | Some opinfo ->
   let (_, _, tm) = unpackFirstTerm opinfo.dfn in
   case tm of
     | Lambda((pat, _, _)::_, _) | tuplePattern? pat ->
       ", rule split_conv"  %", rule Product_Type.prod.cases"       
     | _ -> ", rule HOL.refl"

 op ruleToIsaRule (c: Context) (rl_spc: RuleSpec): String =
   case rl_spc of
     | Unfold  qid -> "unfold "^qidToIsaString qid^"_def"^cleanupCommand(qid, getSpec c)
     | Fold    qid -> "fold "^qidToIsaString qid^"_def, rule HOL.refl"
     | Rewrite qid -> "unfold "^qidToIsaString qid^"_def"^cleanupCommand(qid, getSpec c)
     | LeftToRight qid -> "rule "^qidToIsaString qid
     | RightToLeft qid -> "rule "^qidToIsaString qid^"[symmetric]"
     | _ -> "auto"
     % | RLeibniz    qid -> 
     % | Strengthen  qid -> "strengthen " ^ show qid
     % | Weaken      qid -> "weaken " ^ show qid
     % | SimpStandard -> "simplify"
     % | AbstractCommonExpressions -> "abstractCommonExpressions"
     % | Eval -> "eval"
     % | Context -> "context"
     % | AllDefs -> "alldefs"

 op anyType: MSType = Any noPos

 op schemaFrom(tm: MSTerm, path: PathTerm.Path): MSTerm * Bool =
   let arg_cong_v = ("xxx", anyType) in
   let def pick(i: Nat, tm_lvs: List(MSTerm * MSVars), r_path: PathTerm.Path, j: Nat): MSTerms =
         %% new_vars are vars bound over the scope of the last element of tms (for let and letrec cases)
         let len = length tm_lvs in
         tabulate(len, fn k -> let (tm, local_vars) = tm_lvs@i in
                               if i = k
                                then schematize(tm, r_path, j+len, local_vars)
                                else
                                  makeApplyTerm(mkVar("?z_"^show(j+k), pat_var_type(tm, local_vars)), local_vars))
       def pat_var_type(tm: MSTerm, local_vars: MSVars): MSType =
         let tm_ty = case maybeTermType tm of
                       | None -> anyType
                       | Some ty -> ty
         in
         foldr (fn ((_,v_ty), ty) -> mkArrow(v_ty, ty)) tm_ty local_vars
       def schematize(tm, path, j, local_vars) =
         case path of
           | [] -> makeApplyTerm(mkVar(arg_cong_v.1, pat_var_type(tm, local_vars)), local_vars)
           | i :: r_path ->
         % let _ = writeLine("schemaFrom: "^anyToString path^"\n"^printVars local_vars^"\n"^printTerm tm) in
         case tm of
          | Apply(ft as Fun(f, _, _), Record([("1", x), ("2", y)], a1), a2) | infixFn? f ->
            let [x, y] = pick(i, [(x, local_vars), (y, local_vars)], r_path, j) in
            Apply(ft, Record([("1", x), ("2", y)], a1), a2)
          | Apply _ | i = 0 && r_path = [] ->    % Avoid functional variable as leads to non-det match
            makeApplyTerm(mkVar(arg_cong_v.1, pat_var_type(tm, local_vars)), local_vars)
          | Apply(x, y, a) ->
            if embed? Lambda x
              then let [y, x] = pick(i, [(y, local_vars), (x, local_vars)], r_path, j) in
                   Apply(x, y, a)
            else let [x, y] = pick(i, [(x, local_vars), (y, local_vars)], r_path, j) in
                 Apply(x, y, a)
          | Record(l, a) ->
            let new_tms = pick(i, map (fn (_, t) -> (t, local_vars)) l, r_path, j) in
            Record(tabulate(length l, fn k -> let (id, _) = l@k in (id, new_tms@k)), a)
          | Bind(bdr, vs, x, a) -> Bind(bdr, vs, schematize(x, r_path, j, local_vars ++ vs), a)
          | The(v, x, a) -> The(v, schematize(x, r_path, j, local_vars ++ [v]), a)
          | Let (l, b, a) ->
            let new_tms = pick(i, (map (fn (_, t) -> (t, local_vars)) l) ++ [(b, local_vars ++ boundVars tm)], r_path, j) in
            Let (tabulate(length l, fn k -> let (pat, _) = l@k in (pat, new_tms@k)),
                 last new_tms, a)
          | LetRec (l, b, a) ->
            let local_vars = local_vars ++ boundVars tm in
            let new_tms = pick(i, (map (fn (_, t) -> (t, local_vars)) l) ++ [(b, local_vars)], r_path, j) in
            LetRec (tabulate(length l, fn k -> let (v, _) = l@k in (v, new_tms@k)),
                    last new_tms, a)
          | Lambda (l, a) ->
            let new_tms = pick(i, map (fn (pat, _, t) -> (t, local_vars ++ patternVars pat)) l, r_path, j) in
            Lambda(tabulate(length l, fn k -> let (pat, condn, _) = l@k in (pat, condn, new_tms@k)), a)
          | IfThenElse(x, y, z, a) ->
            let [x, y, z] = pick(i, [(x, local_vars), (y, local_vars), (z, local_vars)], r_path, j) in
            IfThenElse(x, y, z, a)
          | Seq(l, a) -> Seq(pick(i, map (fn tm -> (tm, local_vars)) l, r_path, j), a)
          | TypedTerm(x, ty, a) ->
            (case postCondn? ty of
               | None -> TypedTerm(schematize(x, r_path, j, local_vars), ty, a)
               | Some post -> let [x,post] = pick(i, [(x, local_vars), (post, local_vars)], r_path, j) in
                              %% Need to incorporate updated post
                              TypedTerm(x, ty, a))
          | And(l, a) -> And(pick(i, map (fn tm -> (tm, local_vars)) l, r_path, j), a)
          | _ -> tm
      def makeApplyTerm(main_tm: MSTerm, local_vars: MSVars): MSTerm =
        foldl (fn (result, v) -> mkApply(result, mkVar v)) main_tm local_vars
   in
   let schema_tm = schematize(tm, reverse path, 0, []) in
   % let _ = writeLine("schemaFrom"^anyToString path^"\n"^printTerm schema_tm) in
   % Simpler to do existsSubTerm search than thread result through schematize
   let has_local_vars? = existsSubTerm (fn stm ->
                                          case stm of
                                            | Apply(Var(fv, _), Var _, _) | fv = arg_cong_v -> true
                                            | _ -> false)
                           schema_tm
   in
   (mkLambda(mkVarPat arg_cong_v, schema_tm), has_local_vars?)

 op ppTermStrFix (c: Context) (parentTerm: ParentTerm) (term: MSTerm) (indent: Int): String =
   replaceString(ppTermStrIndent c parentTerm term indent, "e_pz", "?z")

 op equalityContext: ParentTerm = Infix (Left, 50)

 op argCongTerm(c: Context, tm: MSTerm, path: PathTerm.Path, indent: Int): String =
   let (schema_term, has_local_vars?) = schemaFrom(tm, path) in
   let schema_str = ppTermStrFix c Top schema_term (indent + 14) in
   "rule_tac f = \""^schema_str^"\" in arg_cong"
      %% If there are local variables then terms are wrapped in lambdas: use rule ext to lift
      ^(if has_local_vars? then ", (rule ext)+" else "")

 op ruleProof(c: Context, before: MSTerm, after: MSTerm, rl_spc: RuleSpec, indent: Int): String =
   let (_, path) = changedPathTerm(before, after) in
   % let _ = writeLine("changed term:\n"^printTerm(fromPathTerm(before, path))) in
   let rule_str = ruleToIsaRule c rl_spc in
   spaces indent^"by ("
     ^(if path = [] then ""
       else let arg_cong_str = argCongTerm(c, before, path, indent + 4) in
            arg_cong_str^(if length arg_cong_str + length rule_str > 90 then ",\n"^(blanks(indent + 4)) else ", "))
     ^rule_str^")\n"

 op transformedTermPlusProof(c: Context, before: MSTerm, after: MSTerm, rl_spc: RuleSpec, indent: Int): String =
   ppTermStrIndent c equalityContext after indent^"\"\n"
    ^ ruleProof(c, before, after, rl_spc, indent - 14)

  op chainedEqualityProof(c: Context, init_tm: MSTerm, f_path: PathTerm.Path,
                          hist: TransformHistory, init_str: String, indent: Int)
       : String =
    let _ = printTransformHistory hist in
    flatten(tabulate(length hist,
                     fn i ->
                       let (tr_tm, rl_spc) = hist@i in
                       let tr_tm = fromPathTerm(tr_tm, f_path) in
                       (if i = 0 then init_str
                        else spaces indent^"also have \"... = ")
                       ^ transformedTermPlusProof(c, if i = 0 then init_tm
                                                     else fromPathTerm((hist@(i-1)).1, f_path),
                                                  tr_tm, rl_spc, indent + 16)))

  % This is invoked with the 'refine def' changes the *body* of
  % the op, but not if it defines a previously uninterpreted op.
  op generateProofForRefineObligation(c: Context, eq_tm: MSTerm, init_dfn: MSTerm, hist: TransformHistory, spc: Spec): String =
    let (lhs, rhs) = equalityArgs eq_tm in
    let path = pathWithinDef lhs in
    let init_dfn = fromPathTerm(init_dfn, path) in
    let f_path = 0 :: path in
      "proof -\n"
    ^ "  have \"           "^(ppTermStrIndent c equalityContext lhs 19)^"\n"
    ^ "                 = " ^(ppTermStrIndent c equalityContext init_dfn 19)^"\"\n"
    ^ "    by ("^unfoldFn lhs^")\n"
    ^ chainedEqualityProof(c, init_dfn, f_path, hist, "  also have \"... = ", 2)
    ^ "  also have \"... = "^(ppTermStr c equalityContext rhs)^"\"\n"
    ^ "    by ("^unfoldFn rhs^")\n"
    ^ "  finally show ?thesis by assumption\n"
    ^ "qed\n"

  % This is invoked when the 'refine def' simply changes the *type* of
  % the op, and does not change (or define) the definition of the op.
  op generateProofForRefinedPostConditionObligation
       (c: Context, new_pcond: MSTerm, prev_pcond: MSTerm, conds: MSTerm, hist: TransformHistory): String =

    % We handle transform-specific transforms special.
    case hist of
      | [(tr_tm, MergeRulesTransform t)] ->
        let _ = writeLine "Generating MergeRules Proof" in
        let def isabelleTerm tm =
              let out = (ppTermStrIndent c Top tm 7) in        
              let tm' = mapTerm (relativizeQuantifiers (getSpec c),id,id) tm in
              let out' = (ppTermStrIndent c Top tm' 7) in
              % let _ = writeLine ("Relativize:\n" ^ out ^ "\nto\n" ^ out') in
              out'
        in
        let def simpleIsabelleTerm tm = ppTermStrIndent c Top tm 7
        in
        printMergeRulesProof (getSpec c) isabelleTerm t

      | _  -> 
       
    % let _ = writeLine("gpc: \n"^printTerm new_pcond^"\n  =>\n"^printTerm prev_pcond^"\n"^anyToPrettyString hist) in
    %if true then "" else
    %let path = pathWithinDef lhs in
    %let init_dfn = fromPathTerm(init_dfn, path) in
    let (_, f_path) = changedPathTerm(prev_pcond, new_pcond) in %path in
    let prev_changed_subtm = fromPathTerm(prev_pcond, f_path) in
    % let _ = writeLine("genProof f_path: "^anyToString f_path^"\n"^printTerm prev_changed_subtm) in
    let arg_cong_str =  argCongTerm(c, prev_pcond, f_path, 43) in
      "proof -\n"
    ^ "  have \""^(ppTermStrIndent c equalityContext prev_pcond 7)^"\n"
    ^ "      = " ^(ppTermStrIndent c equalityContext new_pcond 7)^"\"\n"
    ^ (case hist of
         | [hist1] ->
           let (tr_tm, rl_spc) = hist1 in
           ruleProof(c, prev_pcond, new_pcond, rl_spc, 4)
         | _ ->
       "  proof -\n"
      ^ "    have \"           "^(ppTermStrIndent c equalityContext prev_changed_subtm 20)^"\n"
      ^ chainedEqualityProof(c, prev_pcond, 1 :: f_path, hist, "                   = ", 4)
      ^ "    finally show ?thesis by ("^arg_cong_str^")\n"
      ^ "    qed\n")
    ^ "  moreover\n"
    ^ (case getConjuncts new_pcond of
       | [_] -> "  assume \""^(ppTermStrIndent c Top new_pcond 10)^"\"\n"
              ^ "  ultimately show ?thesis ..\n"
       | cjs -> "  assume "^(foldr (fn (cj, str) -> "\""^(ppTermStrIndent c Top cj 10)^"\" "^str) "\n" cjs)
             ^ "  ultimately show ?thesis by auto\n")
    ^ "qed\n"


%%%
%%% Helper functions for building Isabelle proofs
%%%

 % An Isabelle proof is just a pretty-printed string, except that we
 % also track the current Isabelle mode in the type, to keep users
 % from using commands in the wrong mode
 type IsaProof m = | IsaProof Pretty

 % dummy types to represent the different Isabelle proof modes
 % NOTE: each of these represents a *complete* proof in that mode,
 % either ending with "qed" or "done" for ProveMode, or with "show"
 % for StateMode
 type ProveMode = | ProveMode
 type StateMode = | StateMode

 % dummy type for to represent a proof tactic, which is not really an
 % Isabelle mode but we treat it as such
 type ProofTacticMode = | ProofTacticMode

 % print out a complete ProveMode proof
 op isaProofToString (IsaProof pretty : IsaProof ProveMode) : String =
   toString (format (0, pretty))

 %% building tactics

 % build a tactic using Isabelle's "rule" tactic, applied to a string
 op ruleTactic (rule : String) : IsaProof ProofTacticMode =
 IsaProof (string ("(rule " ^ rule ^ ")"))

 % same as above, but use a Pretty to format the rule
 op ruleTacticPP (rule : Pretty) : IsaProof ProofTacticMode =
 IsaProof (blockFill (0, [(0, string "(rule "), (3, rule), (0, string ")")]))

 % use a non-rule tactic, just given as a string
 op otherTactic (tactic : String) : IsaProof ProofTacticMode =
 IsaProof (string (tactic^" "))

 %% building ProveMode proofs

 % apply a proof tactic, which is prepended to the rest of the proof
 op applyTactic (tactic : IsaProof ProofTacticMode, pf : IsaProof ProveMode) : IsaProof ProveMode =
   applyTactics ([tactic], pf)

 % same as above, but with multiple tactics
 op applyTactics (tactics : List (IsaProof ProofTacticMode),
                  IsaProof pf : IsaProof ProveMode) : IsaProof ProveMode =
 let lines = map (fn (IsaProof tactic) ->
                    prConcat [string "apply ", tactic]) tactics in
 IsaProof (prLines 0 (lines ++ [pf]))

 % build an empty proof, i.e., just the keyword "done"
 op emptyProof : IsaProof ProveMode = IsaProof (string "done ")

 % build a proof using a single tactic using the keyword "by"
 op singleTacticProof (IsaProof tactic : IsaProof ProofTacticMode) : IsaProof ProveMode =
   IsaProof (prConcat [string "by ", tactic])

 % generate a "proof -" / "qed" Isabelle proof block, given a body for
 % that block; technically, the body is in "state" mode, and the proof
 % block then works in "prove" mode
 % NOTE: body must end with at least one whitespace
 op forwardProofBlock (IsaProof body : IsaProof StateMode) : IsaProof ProveMode =
   IsaProof (blockLinear (0, [(0, string "proof - "), (2, body), (0, string "qed ")]))

 %% building StateMode (forward-reasoning) proofs

 % Add an Isabelle assumption with a unique name, generated from a
 % prefix (which should not end with a number) passed by the caller;
 % the name gets passed to the remainder of the proof; the proposition
 % being assumed should be a term that has already been pretty-printed
 op addForwardAssumption (c : Context, prefix: String, prop: Pretty, rest: String -> IsaProof StateMode) : IsaProof StateMode =
 let assum_name = prefix ^ show (getNewVar c) in
 let rest_pretty = case rest assum_name of IsaProof p -> p in
 IsaProof
 (prLines 0
    [blockFill
       (0,
        [(0, string "assume "),
         (2, string (assum_name ^ ": ")),
         (4, prConcat [string "\"", prop, string "\""])]),
     rest_pretty])

 % add a named, intermediate goal in a forward-reasoning proof, using
 % a "have" in Isabelle; the proof is bound to a uniquely-generated
 % name, which is passed to the rest of the proof
 op addForwardStep (c: Context, prefix: String, prop: Pretty, pf: IsaProof ProveMode, rest: String -> IsaProof StateMode) : IsaProof StateMode =
 let assum_name = prefix ^ show (getNewVar c) in
 let pf_pretty = case pf of IsaProof p -> p in
 let rest_pretty = case rest assum_name of IsaProof p -> p in
 IsaProof
 (prLines 0
    [blockFill
       (0,
        [(0, string "have "),
         (4, string (assum_name ^ ": ")),
         (6, prConcat [string "\"", prop, string "\""]),
         (2, pf_pretty)]),
     rest_pretty])

 % finish a forward-reasoning proof block by showing the final result
 op showFinalResult (prop: Pretty, pf : IsaProof ProveMode) : IsaProof StateMode =
 let pf_pretty = case pf of IsaProof p -> p in
 IsaProof (blockFill (0,
                      [(0, string "show "),
                       (4, doubleQuote prop),
                       (2, pf_pretty)]))

 % chain a sequence of proof steps together into a combined proof of a
 % transitive closure; e.g., "x = y" and "y = z" --> "x = z"
 op showFinalChainedResult (final_prop: Pretty, steps : List (Pretty * IsaProof ProveMode)) : IsaProof StateMode =
 let haves_pp =
   map (fn (prop, IsaProof pf) ->
     blockFill
          (0,
           [(0, string "have "),
            (4, doubleQuote prop),
            (2, pf)])) steps in
   IsaProof
   (prLines 0
      (intersperse (string "also") haves_pp
         ++
         [string "finally",
          blockFill
            (0,
             [(0, string "show "),
              (4, doubleQuote final_prop),
              (0, string ".")])]))

 %% misc helper functions

 % pretty-print an equality proposition / constraint
 op ppEquality (c: Context, lhs: MSTerm, rhs: MSTerm) : Pretty =
 ppTerm c Top (mkEquality(Any noPos,lhs,rhs))

 % pretty-print an implication
 op ppImplication (c: Context, lhs: MSTerm, rhs: MSTerm) : Pretty =
 ppTerm c Top (mkImplies(lhs, rhs))

 % pretty-print an Isabelle fat arrow "==>" implication
 op ppBigImplication (c: Context, lhs: MSTerm, rhs: MSTerm) : Pretty =
 prBreak 0 [ppTerm c Top lhs, string " \\<Longrightarrow> ", ppTerm c Top rhs]

 % add double quotes around a Pretty
 op doubleQuote (p : Pretty) : Pretty = prConcat [string "\"", p, string "\""]

 % pretty-print N forall-eliminations
% FIXME: put in the actual arg, as a double-check for Isabelle
 op ppForallElims (args : List Pretty, body : Pretty) : Pretty =
 case args of
   | [] -> body
   | arg :: args' ->
     blockFill
     (0,
      [(0, string "allE[OF "),
       (2, ppForallElims (args', body)),
       (0, string "]")])
   


%%%
%%% Generation of Isabelle proofs from RefinementProofs
%%%

  % generate an Isabelle proof of equality "lhs = rhs"
  op generateEqualityProof(c: Context, lhs: MSTerm, rhs: MSTerm, pf:EqProof): String =
  isaProofToString (forwardProofBlock (ppEqualityProof (c, lhs, rhs, pf)))

  op ppEqualityProof(c: Context, lhs: MSTerm, rhs: MSTerm, pf:AnnSpec.EqProof): IsaProof StateMode =
  case pf of
   | EqProofSubterm (path, sub_pf) ->
     (*
        have subeq:"lhs_sub = rhs_sub" (sub_pf)
        show "lhs = rhs" by (rule arg_cong[OF subeq]) *)
     let lhs_sub = fromPathTerm (lhs, path) in
     let rhs_sub = fromPathTerm (rhs, path) in
     let sub_eq_pp = ppEquality (c, lhs_sub, rhs_sub) in
     addForwardStep
     (c, "subeq", sub_eq_pp,
      forwardProofBlock (ppEqualityProof (c, lhs_sub, rhs_sub, sub_pf)),
      (fn pf_name ->
         showFinalResult (ppEquality (c, lhs, rhs),
                          singleTacticProof
                            (ruleTactic ("arg_cong[OF "^ pf_name ^"]")))))
   | EqProofSym sub_pf ->
     (* have subeq:"rhs = lhs" (sub_pf) show "lhs=rhs" by (rule subeq[symmetric]) *)
     let sub_eq_pp = ppEquality (c, rhs, lhs) in
     addForwardStep
     (c, "subeq", sub_eq_pp,
      forwardProofBlock (ppEqualityProof (c, rhs, lhs, sub_pf)),
      (fn pf_name ->
         showFinalResult (sub_eq_pp,
                          singleTacticProof
                            (ruleTactic (pf_name ^ "[symmetric]")))))
   | EqProofTrans (pf1, middle, pf2) ->
     (*
        have "lhs=middle" (pf1)
        also
        have "middle=rhs" (pf2)
        finally
        show "lhs=rhs" .
        *)
     showFinalChainedResult
     (ppEquality (c, lhs, rhs),
      [(ppEquality (c, lhs, middle),
        forwardProofBlock (ppEqualityProof (c, lhs, middle, pf1))),
       (ppEquality (c, middle, rhs),
        forwardProofBlock (ppEqualityProof (c, middle, rhs, pf2)))])
   | EqProofTheorem (qid, args) ->
     (* show "lhs=rhs" by (rule qid[of tm1 ... tmn]) *)
     showFinalResult
     (ppEquality (c, lhs, rhs),
      singleTacticProof
        (ruleTacticPP
           %(ppForallElims (map (ppTerm c Top) args, ppQualifiedId qid))
           (prLinear 2
              [ppQualifiedId qid, string "[of ",
               prLinear 0 (map (ppTerm c Top) args),
               string "]"])
           ))
   | EqProofUnfoldDef qid ->
     % FIXME: if qid is functional, use the extensionality rule
     (* show "f=rhs" by (rule f_def) *)
     showFinalResult
     (ppEquality (c, lhs, rhs),
      singleTacticProof (ruleTacticPP (prConcat [ppQualifiedId qid, string "_def"])))
   | EqProofTactic tactic ->
     (* by tactic *)
     showFinalResult (ppEquality (c, lhs, rhs), singleTacticProof (ruleTactic tactic))

  % generate an Isabelle proof of an implication "lhs -> rhs"
  op generateImplicationProof (c: Context, lhs: MSTerm, rhs: MSTerm, pf:AnnSpec.ImplProof): String =
  isaProofToString (forwardProofBlock (ppImplicationProof (c, lhs, rhs, pf)))

  op ppImplicationProof (c: Context, lhs: MSTerm, rhs: MSTerm, pf:AnnSpec.ImplProof): IsaProof StateMode =
  case pf of
  | ImplTrans (pf1, middle, pf2) ->
    (*
       have impl_trans1: "A --> B" (pf1)
       have impl_trans2: "B --> C" (pf2)
       have impl_trans_big:"A ==> C"
         proof -
           assume impl_lhs:A
           show C by (rule impE[OF impl_trans2,OF impE[OF impl_trans1,OF impl_lhs]])
         qed
       show "A --> C" by (rule impI[OF impl_trans_big]) *)
    addForwardStep
    (c, "impl_trans1_", ppImplication (c, lhs, middle),
     forwardProofBlock (ppImplicationProof (c, lhs, middle, pf1)),
     (fn pf1_name ->
        addForwardStep
        (c, "impl_trans2_", ppImplication (c, middle, rhs),
         forwardProofBlock (ppImplicationProof (c, middle, rhs, pf2)),
         (fn pf2_name ->
          addForwardStep
            (c, "impl_trans_big", ppBigImplication (c, lhs, rhs),
             forwardProofBlock
               (addForwardAssumption
                  (c, "impl_lhs", ppTerm c Top lhs,
                   fn lhs_name ->
                   showFinalResult
                     (ppTerm c Top rhs,
                      singleTacticProof
                        (ruleTactic
                           ("impE[OF " ^pf2_name
                              ^ ", OF impE[OF "^pf1_name^", OF "^lhs_name^"]]"))))),
             (fn big_impl_name ->
              showFinalResult
                (ppImplication (c, lhs, rhs),
                 singleTacticProof (ruleTactic ("impI[OF "^big_impl_name^"]")))))))))
  | ImplTheorem (qid, args) ->
     (* show "lhs --> rhs" by (rule allE[OF allE[OF ... [OF qid] ... ]]) *)
     showFinalResult
     (ppEquality (c, lhs, rhs),
      singleTacticProof
        (ruleTacticPP
           %(ppForallElims (map (ppTerm c Top) args, ppQualifiedId qid))
           (prLinear 2
              [ppQualifiedId qid, string "[of ",
               prLinear 0 (map (ppTerm c Top) args),
               string "]"])
           ))
  | ImplEq eq_pf ->
    (*
       have eq_pf: "A = B" (eq_pf)
       have eq_impl: "A ==> B"
       proof -
         assume lhs:A
         show B by (rule subst[OF eq_pf, of "lambda z . z", OF lhs])
       qed
       show "A --> B" by (rule impI[OF eq_impl]) *)
    addForwardStep
    (c, "eq_pf", ppEquality (c, lhs, rhs),
     forwardProofBlock (ppEqualityProof (c, lhs, rhs, eq_pf)),
     (fn eq_pf_name ->
      addForwardStep
      (c, "eq_impl", ppBigImplication (c, lhs, rhs),
       forwardProofBlock
         (addForwardAssumption
            (c, "lhs", ppTerm c Top lhs,
             (fn lhs_name ->
              showFinalResult
                (ppTerm c Top rhs,
                 singleTacticProof (ruleTactic ("subst[OF "^eq_pf_name^", of \"\\<lambda>z . z\", OF "^lhs_name^"]")))))),
       (fn eq_impl_name ->
        showFinalResult
          (ppImplication (c, lhs, rhs),
           singleTacticProof (ruleTactic ("impI[OF "^eq_impl_name^"]")))))))
  | ImplProofTactic tactic ->
    (* by tactic *)
     showFinalResult (ppImplication (c, lhs, rhs), singleTacticProof (ruleTactic tactic))
  | MergeRulesProof tree ->
        let def isabelleTerm tm =
              let out = (ppTermStrIndent c Top tm 7) in        
              let tm' = mapTerm (relativizeQuantifiers (getSpec c),id,id) tm in
              let out' = (ppTermStrIndent c Top tm' 7) in
              % let _ = writeLine ("Relativize:\n" ^ out ^ "\nto\n" ^ out') in
              out'
        in
        let def simpleIsabelleTerm tm = ppTermStrIndent c Top tm 7
        in
        IsaProof (string (printMergeRulesProof (getSpec c) isabelleTerm tree))
    % fail "ppImplicationProof: need to add support for MergeRules!"


%%%
%%% End of Generation of Isabelle proofs from RefinementProofs
%%%

  op makeSubstFromRecPats(pats: List(Id * MSPattern), rec_tm: MSTerm, spc: Spec): List (MSPattern * MSTerm) =
    mapPartial (fn (fld, pat) -> if embed? WildPat pat then None
                                  else Some(pat, mkProjectTerm(spc, fld, rec_tm)))
      pats

  op expandRecPatterns (spc: Spec) (pat: MSPattern, condn: MSTerm, body: MSTerm): MSPattern * MSTerm * MSTerm =
    case pat of
      | RecordPat(pats as (id1,_)::_,_) | id1 ~= "1" && varOrRecordPattern? pat ->
        let rec_v = ("record__v", patternType pat) in
        let binds = makeSubstFromRecPats(pats, mkVar rec_v, spc) in
        let let_bod = foldr (fn (bnd, bod) -> maybeExpandRecordPattern spc (MS.mkLet([bnd], bod))) body binds in
        (mkVarPat rec_v, condn, let_bod)
      | RecordPat(pats, a) ->
        let (newpats, condn, new_body)
           = foldl (fn ((newpats, condn, body), (id, p)) ->
                    let (new_p, condn, new_body) = expandRecPatterns spc (p, condn, body) in
                    (newpats ++ [(id, new_p)], condn, new_body))
              ([], condn, body) pats
        in
        (RecordPat(newpats, a), condn, new_body)
      | AliasPat(p1, p2, a) ->
        let (new_p2, condn, new_body) = expandRecPatterns spc (p2, condn, body) in
        (AliasPat(p1, new_p2, a), condn, new_body)
      | EmbedPat(id, Some p2, ty, a) ->
        let (new_p2, condn, new_body) = expandRecPatterns spc (p2, condn, body) in
        (EmbedPat(id, Some new_p2, ty, a), condn, new_body)
      | _ -> (pat, condn, body)

  op maybeExpandRecordPattern(spc: Spec) (t: MSTerm): MSTerm =
    case t of
      | Let([(pat as RecordPat(pats as (id1,_)::_,_), rec_tm)], body, _)
          | id1 ~= "1" && varOrRecordPattern? pat ->
        let binds = makeSubstFromRecPats(pats, rec_tm, spc) in
        foldr (fn (bnd, bod) -> maybeExpandRecordPattern spc (MS.mkLet([bnd], bod))) body binds
      | Lambda (pats, a) ->
        Lambda(map (expandRecPatterns spc) pats, a)
      | _ -> t

  op expandRecordPatterns(spc: Spec): Spec =
    mapSpec (maybeExpandRecordPattern spc, id, id)
      spc

  op generateAllSubtypeConstrs?(spc: Spec): Bool =
    let (initial_make_subtype_constr_pragma?, _) =
        foldl (fn (r as (initial_make_subtype_constr_pragma?, done?), el) ->
               if done? then r
               else
               case el of
                 | Pragma("proof", prag_str, "end-proof", _) ->
                   (case controlPragmaString prag_str of
                      | Some strs ->
                        if makeSubtypeConstrTheoremsString in? strs
                          then (true, false)
                          else if noMakeSubtypeConstrTheoremsString in? strs
                          then (false, true)
                          else r
                      | None -> r)
                 | Op _ -> (initial_make_subtype_constr_pragma?, true)
                 | _ -> r)
          (false, false)
          spc.elements
    in
    initial_make_subtype_constr_pragma?

  op generateObligsForSTPFuns?(spc: Spec): Bool =
    let (initial_make_stp_obligs_pragma?, _) =
        foldl (fn (r as (initial_make_stp_obligs_pragma?, done?), el) ->
               if done? then r
               else
               case el of
                 | Pragma("proof", prag_str, "end-proof", _) ->
                   (case controlPragmaString prag_str of
                      | Some strs ->
                        if subtypePredicateOpsObligationsString in? strs
                          then (true, false)
                          else if noSubtypePredicateOpsObligationsString in? strs
                          then (false, true)
                          else r
                      | None -> r)
                 | Op _ -> (initial_make_stp_obligs_pragma?, true)
                 | _ -> r)
          (false, false)
          spc.elements
    in
    initial_make_stp_obligs_pragma?

  op STPFunName?(qual: String, nm: String): Bool =
    endsIn?(nm, "__stp")

(* ppSpec - key dependencies wrt subtype handling
addSubtypePredicateLifters doesn't depend on anything (?)
addCoercions & raiseNamedTypes before makeTypeCheckObligationSpec
addCoercions before raiseNamedTypes
removeSubTypes can introduce subtype conditions that require addCoercions
*)

  op  ppSpec (c: Context) (spc: Spec): Pretty =
    % let _ = writeLine("0:\n"^printSpec spc) in
    let rel_elements = filter isaElement? spc.elements in
    let spc = spc << {elements = normalizeSpecElements(rel_elements)} in
    let spc = adjustElementOrder spc in
    let source_of_thy_morphism? = exists? (fn el ->
                                            case el of
                                              | Pragma("proof", prag_str, "end-proof", pos)
                                                  | some?(thyMorphismPragma prag_str "Isa" pos)
                                                  -> true
                                              | _ -> false)
                                     spc.elements
    in
    let trans_table = thyMorphismMaps spc "Isa" convertPrecNum in
    let c = c << {spec? = Some spc,
                  trans_table = trans_table,
                  source_of_thy_morphism? = source_of_thy_morphism?}
    in
    let spc = addSubtypePredicateLifters spc in
    let spc = normalizeTopLevelLambdas spc in
    let spc = if lambdaLift?
               then lambdaLiftInternal(spc, false, false) % ignore imports, don't simulate closures
	       else spc
    in
    let spc = if unfoldMonadBinds? then unfoldMonadBinds spc else spc in
    let spc = if c.simplify? && some?(AnnSpec.findTheType(spc, Qualified("Nat", "Nat")))
                then simplifyTopSpec spc
                else spc
    in
    let morphism_coercions = makeCoercionTable(trans_table, spc) in   % before removeSubTypes!
    let typedef_coercions = coercionsFromTypeDefPragmas spc in
    let coercions = coerceLiteralsInCoercions spc (typedef_coercions ++ morphism_coercions) in
    let c = c << {coercions = coercions,
                  overloadedConstructors = overloadedConstructors spc}
    in
    % let _ = printSpecWithTypesToTerminal spc in
    %% ? let spc = addRefineObligations c spc in
    let spc = normalizeNewTypes(spc, false) in
    let c = c << {typeNameInfo = topLevelTypes spc, spec? = Some spc} in
    let spc = addRefineObligations c spc in
    % let _ = writeLine("1:\n"^printSpec spc) in
    let spc = addCoercions coercions spc in
    let (spc, opaque_type_map) = removeDefsOfOpaqueTypes coercions spc in
    let spc = raiseNamedTypes spc in
    % let _ = writeLine("2:\n"^printSpec spc) in
    let (spc, stp_tbl) = addSubtypePredicateParams spc coercions in
    % let _ = writeLine("4:\n"^printSpec spc) in
    % let _ = printSpecWithTypesToTerminal spc in
    let spc = exploitOverloading coercions false spc in
    % let _ = writeLine("5:\n"^printSpec spc) in
    let spc = if addObligations?
               then makeTypeCheckObligationSpec(spc, generateAllSubtypeConstrs? spc,
                                                if generateObligsForSTPFuns? spc
                                                  then FALSE
                                                  else STPFunName?,
                                                c.thy_name)
	       else spc
    in
    let spc = exploitOverloading coercions true spc in   % nat(int x - int y)  -->  x - y now we have obligation
    let spc = thyMorphismDefsToTheorems c spc in    % After makeTypeCheckObligationSpec to avoid redundancy
    let spc = emptyTypesToSubtypes spc in
    let spc = addRefinementProofs c spc in
    % let _ = writeLine("9:\n"^printSpec spc) in
    let spc = removeSubTypes spc coercions stp_tbl in
    % let _ = writeLine("10:\n"^printSpec spc) in
    let spc = addCoercions coercions spc in
    let spc = exploitOverloading coercions true spc in
    %% Second round of simplification could be avoided with smarter construction
    let spc = expandRecordPatterns spc in
    let spc = normalizeNewTypes(spc, true) in
    let spc = if c.simplify? && some?(AnnSpec.findTheType(spc, Qualified("Nat", "Nat")))
                then simplifyTopSpec(simplifyTopSpec spc) % double simplify temporary?
                else spc
    in
    let spc = addTypeDefs spc opaque_type_map in
    let c = c << {typeNameInfo = topLevelTypes spc, spec? = Some spc} in
    % let _ = writeLine("n:\n"^printSpec spc) in
    prLinesCat 0 ([[prString "theory ", prString (thyName c.thy_name)],
                   [prString "imports ", ppImports c spc.elements],
                   [prString "begin"]]
                  ++
                  (if specHasSorryProof? spc then [[], [prString "ML {* quick_and_dirty := true; *}"], []] else [])
                  ++
		  [[ppSpecElements c spc (filter elementFilter spc.elements)],
		  [ prString "end"]])

  op specHasSorryProof?(spc: Spec): Bool =
    exists? (fn elt ->
               case elt of
                 | Pragma("proof", prag_str, "end-proof", _) | isaPragma? prag_str ->
                   %% Ignores that "sorry" might be in a comment
                   some?(search("sorry", prag_str))
                 |  _ -> false)
      spc.elements

  op  isaElement?: SpecElement -> Bool
  def isaElement? elt =
    case elt of
      | Pragma("proof", prag_str, "end-proof", _) | isaPragma? prag_str -> true
      | Pragma _ -> false
      | Comment _ -> false
      | _ -> true

  op  elementFilter: SpecElement -> Bool
  def elementFilter elt =
    case elt of
      %| Import _ -> false
      | Pragma("proof", prag_str, "end-proof", pos) | isaPragma? prag_str
                                                && thyMorphismPragma prag_str "Isa" pos = None ->
        true
      | Pragma _ -> false
      | _ -> true

  %% Originally was just supertype but generalized to also be a named type
  op getSuperType(ty: MSType): MSType =
    case ty of
      | Subtype(sup,_,_) -> sup
      | _ -> ty

  op makeCoercionTable(trans_info: TransInfo, spc: Spec): TypeCoercionTable =
   foldi (fn (subty_qid, (super_id, opt_coerc, overloadedOps, no_def?), val) ->
           case opt_coerc of
             | None -> val
             | Some(toSuper, toSub) ->
           let (tvs, ty_def) = typeDef (subty_qid, spc) in
           let subty = mkBase(subty_qid, map mkTyVar tvs) in
           let superty = getSuperType ty_def in
           Cons({subtype = subty_qid,
                 supertype = superty,
                 coerceToSuper = mkOp(Qualified(toIsaQual, toSuper),
                                      mkArrow(subty, ty_def)),
                 coerceToSub   = mkOp(Qualified(toIsaQual, toSub),
                                      mkArrow(ty_def, subty)),
                 overloadedOps = overloadedOps},
                val))
      [] trans_info.type_map

  def baseSpecName = "Empty"

  op  ppImports: Context -> SpecElements -> Pretty
  def ppImports c elems =
    let imports_from_thy_morphism = thyMorphismImports c in
    let explicit_imports =
        mapPartial (fn el ->
		     case el of
		       | Import(imp_sc_tm, im_sp, _, _) -> Some (ppImport c imp_sc_tm im_sp)
		       | _ -> None)
           elems
    in case explicit_imports ++ imports_from_thy_morphism of
      | [] -> prString baseSpecName
      | imports -> prPostSep 0 blockFill prSpace imports

  op thyMorphismImports (c:Context): List Pretty =
    map prString c.trans_table.thy_imports

  op firstTypeDef (elems:SpecElements): Option QualifiedId =
    case elems of
      | [] -> None
      | (Type (type_id, _)) :: _ -> Some type_id
      | (TypeDef (type_id, _)) :: _ -> Some type_id
      | _ :: r -> firstTypeDef r

  op Specware.Specware4: String

  op normIsaPath(p: List String): List String =
    let specware4 = splitStringAt(Specware4, "/") in
    let sw4_len = length specware4 in
    let red_p = if length p >= sw4_len && subFromTo(p, 0, sw4_len) = specware4
                  then  let rem_p = subFromTo(p, sw4_len, length p) in
                       %               | "Library" :: _ ->
                       %                 ["Library"]
                       %               | rem_p -> rem_p
                       % in
                       "$SPECWARE4" :: rem_p
                  else abbreviatedPath p
    in
    red_p ++ ["Isa"]

  op tryRelativize(p: List String, rel_p: List String): List String =
    let def aux(pi, rel_pi) =
          %let _ = writeLine("tryRelativize:\n"^anyToString pi^"\n"^anyToString rel_pi) in
          case (pi, rel_pi) of
            | ([], []) -> []
            | ([], rel_pi) -> ["/"]
            | (pi, []) -> pi
            | (x :: r_p, y :: r_rel_p) | x = y ->
              aux(r_p, r_rel_p)
            | _ -> if length rel_pi > 3 then p
                    else tabulate(length rel_pi, fn _ -> "..") ++ pi
    in
    aux(p, rel_p)

  op importName(c:Context) (thy_nm: Id) (thy_fil_nm: Id): String =
    let cur_uid = getCurrentUID c in
    let ctxt_comps = normIsaPath(butLast(splitStringAt(uidToFullPath cur_uid, "/"))) in
    let thy_comps  = normIsaPath(removeSuffix(splitStringAt(thy_fil_nm, "/"), 2)) in
    if thy_comps = ctxt_comps
      then thy_nm
    else
      let rel_path = tryRelativize(thy_comps, ctxt_comps) in
      let nm = foldr (fn (compi, result) -> compi^"/"^result) thy_nm rel_path in
      (%writeLine("imports "^nm);
       if exists? (fn c -> c = #/) nm
         then "\""^nm^"\"" else nm)

  %% Should add "/Isa"
  op convertToIsaDir(filnm: String): String = filnm

  op  ppImport: Context -> SCTerm -> Spec -> Pretty
  def ppImport c sc_tm spc =
    case uidStringPairForValueOrTerm(c, Spec spc, sc_tm) of
      | None ->
        let thy_ext = show(!c.anon_thy_count) in
        let thy_nm = c.thy_name ^ thy_ext in
        let thy_fil_nm = convertToIsaDir(uidToFullPath(getCurrentUID c)) ^ thy_ext ^ ".thy" in
        (%writeLine("ppI0: "^thy_nm^" in "^thy_fil_nm);
         c.anon_thy_count := !c.anon_thy_count + 1;
         if c.recursive?
           then toFile(thy_fil_nm,
                       showValue(Spec spc, c.recursive?, c.currentUID, Some thy_nm, c.simplify?))
           else ();
         prString thy_nm)
      | Some ((thy_nm, sw_fil_nm, thy_fil_nm), val, uid) ->
        (%writeLine("ppI: "^thy_nm^" "^sw_fil_nm^" "^thy_fil_nm);
         if c.recursive?
           then
             if fileOlder?(sw_fil_nm, thy_fil_nm) %|| spc = getBaseSpec()
               then ()
             else toFile(thy_fil_nm,
                         showValue(val, c.recursive?, Some uid, Some thy_nm, c.simplify?))
           else ();
	 prString (importName c thy_nm thy_fil_nm))

  op  ppSpecElements: Context -> Spec -> SpecElements -> Pretty
  def ppSpecElements c spc elems =
    let
      %op  ppSpecElementsAux: Context -> Spec -> SpecElements -> Prettys
      def aux c spc r_elems =
        let prettys =
            (case r_elems of
               | [] -> []
               | (Comment (c_str,_)) :: (Property prop) :: (Pragma prag) :: rst | unnamedPragma? prag ->
                 Cons(ppProperty c prop c_str elems (Some prag),
                      aux c spc rst)
                 %	  | (Pragma(_, c_str, _, _)) :: (Property prop) :: (Pragma prag) :: rst ->
                 %	    Cons(ppProperty c prop c_str (Some prag),
                 %		 aux c spc rst)
                 %	  | (Property prop) :: (Pragma prag) :: rst ->
                 %	    Cons(ppProperty c prop "" (Some prag),
                 %		 aux c spc rst)
          
               | (el as Op(qid, true, _)) :: rst | defHasForwardRef?(qid, rst, spc) ->
                 let (op_qids, pre_els, mrec_els, m_rst) = findMutuallyRecursiveElts(qid, rst, spc) in
                 if pre_els = []
                   then ppMutuallyRecursiveOpElts c op_qids (el :: mrec_els) elems
                     :: (aux c spc m_rst)
                 else  %% After printing pre_els, this will redo analysis, but this is cheap
                   aux c spc (pre_els ++ (el :: mrec_els) ++ m_rst)
               | (el as Property(_, _, _, term, _)) :: rst | hasForwardRef?(term, rst) ->
                 let new_els = moveAfterOp(el, rst) in
                 aux c spc new_els
               | (el as TypeDef (qid,_)) :: rst | hasForwardCoProductTypeRef?(qid, rst, spc) ->
                 let (mrec_els, m_rst) = findMutuallyRecursiveCoProductElts(qid, rst, spc) in
                 ppMutuallyRecursiveCoProductElts c (el :: mrec_els)
                 ++ aux c spc m_rst
               | el :: (rst as (Pragma prag) :: _) | unnamedPragma? prag ->
                 let pretty1 = ppSpecElement c spc el (Some prag) elems in
                 let prettyr = aux c spc rst in
                 if pretty1 = prEmpty
                   then prettyr
                 else pretty1::prettyr
               | (Pragma prag) :: rst | defaultProofPragma? prag ->
                 let prf_str = prfFromPragma prag in
                 let c = c << {defaultProof = prf_str} in
                 aux c spc rst
               | el :: rst ->
                 let pretty1 = ppSpecElement c spc el None elems in
                 let prettyr = aux c spc rst in
                 if pretty1 = prEmpty
                   then prettyr
                 else pretty1::prettyr)
          in
          case prettys of
            | pr :: _ | pr = prEmpty -> prettys
            | _ -> prEmpty :: prettys
    in
    prLines 0 (aux c spc elems)

  op hasOpDef?(qids: QualifiedIds, els: SpecElements) : Bool =
    if qids = [] then false
    else
    exists? (fn el -> case el of
                        | Op(qid, true, _) -> qid in? qids
                        | _ -> false)
      els

  op defHasForwardRef?(qid: QualifiedId, els: SpecElements, spc: Spec) : Bool =
    hasOpDef?(opsInOpDefFor(qid, spc), els)

  op hasForwardRef?(tm: MSTerm, els: SpecElements): Bool =
    hasOpDef?(opsInTerm tm, els)

  op moveAfterOp(move_el: SpecElement, els: SpecElements): SpecElements =
    case els of
      | [] -> [move_el]                      % Shouldn't happen!
      | (op_el as Op _):: r_els -> op_el :: move_el :: r_els
      | el :: r_els -> el :: moveAfterOp(move_el, r_els)


  op findMutuallyRecursiveElts(qid0: QualifiedId, els: SpecElements, spc: Spec)
       : QualifiedIds * SpecElements * SpecElements * SpecElements =
    let op_refs = qid0 :: opsInOpDefFor(qid0, spc) in
    let _ = writeLine(show qid0^" has ops (0)\n"^anyToString(map show (opsInOpDefFor(qid0, spc)))) in
    let def findMutuallyRecursiveOps(els, op_refs, mr_els, pending_prag_els) =
          case els of
            | [] -> orderElts(mr_els, pending_prag_els)
            | el :: r_els ->
          case el of
            | Op(qid, true, _) ->
              if qid in? op_refs
                then
                  let new_op_refs = opsInOpDefFor(qid, spc) ++ op_refs in
                  % let _ = writeLine(show qid^" has ops\n"^anyToString(map show (opsInOpDefFor(qid, spc)))) in
                  findMutuallyRecursiveOps(r_els, new_op_refs,
                                           mr_els ++ pending_prag_els ++ [el], [])
                else
                  findMutuallyRecursiveOps(r_els, op_refs,
                                           mr_els, pending_prag_els ++ [el])
            | _ ->
          if (case el of
                | Pragma _ -> true
                | Property _ -> true
                | Comment _ -> true
                | _ -> false)
            then findMutuallyRecursiveOps(r_els, op_refs, mr_els,
                                          pending_prag_els ++ [el])
            else orderElts(mr_els, pending_prag_els ++ els)
        def orderElts(mr_els, els) =
          let (mr_els, els) = case els of
                                | (el as (Pragma prag)) :: rm_rst | unnamedPragma? prag ->
                                  (mr_els ++ [el], rm_rst)
                                | _ -> (mr_els, els)
          in
          let op_qids = mapPartial (fn el -> case el of
                                   | Op(qid, _, _) -> Some qid
                                   | _ -> None)
                mr_els
          in
          extractProperties(mr_els, qid0 :: op_qids, [], [], els)
        def extractProperties(els, op_qids, pre_els, mr_els, post_els) =
          %% Split properties and assoc pragmas with els into
          case els of
            | [] -> (op_qids, pre_els, mr_els, post_els)
            | (el as Property(_, _, _, term, _)) :: r_els ->
              let (unnamedPragEls, r_els) =
                  case r_els of
                    | (prag_el as Pragma prag) :: rr_els | unnamedPragma? prag ->
                      ([prag_el], rr_els)
                    | _ -> ([], r_els)
              in
              if exists? (fn qid -> qid in? op_qids) (opsInTerm term)
                then extractProperties(r_els, op_qids, pre_els, mr_els, el :: unnamedPragEls ++ post_els)
                else extractProperties(r_els, op_qids, pre_els ++ (el :: unnamedPragEls), mr_els, post_els)
           | el :: r_els ->
             extractProperties(r_els, op_qids, pre_els, mr_els ++ [el], post_els)
    in
    findMutuallyRecursiveOps(els, op_refs, [], [])

  op ppMutuallyRecursiveOpElts (c: Context) (op_qids: QualifiedIds) (els: SpecElements) (all_els: SpecElements)
       : Pretty =
    let spc = getSpec c in
    let c = c << {newVarCount = Ref 0} in
    let op_qid_infos = map (fn op_qid ->
                              let Some{names=_, fixity, dfn, fullyQualified?=_} = findTheOp(spc, op_qid) in
                              let (_, ty, term) = unpackNthTerm(dfn, 0) in
                              case specialOpInfo c op_qid of
                                | Some (isa_id, infix?, _, _, no_def?) ->
                                  (mkUnQualifiedId(isa_id), ty, term,
                                   case infix? of
                                     | Some pr -> Infix pr
                                     | None -> fixity)
                                | _ -> (op_qid, ty, term, convertFixity fixity))
                         op_qids
    in
    let opt_prag_el = findLeftmost (fn el -> case el of
                                          | Pragma prag -> unnamedPragma? prag
                                          | _ -> false)
                        els
    in
    let opt_prag = case opt_prag_el of
                   | Some(Pragma prag) -> Some prag
                   | _ -> None
    in
    let opt_prag = findPragmaNamed(all_els, head op_qids, opt_prag) in
    let opt_prag = foldl (fn (opt_prag, op_qid) ->
                            case opt_prag of
                              | None -> findPragmaNamed(all_els, op_qid, opt_prag)
                              | _ -> opt_prag)
                     opt_prag (tail op_qids)
    in
    let pp_cases =
        flatten (map (fn (op_qid, ty, dfn, fixity) ->
                        let op_tm = mkFun (Op (op_qid, fixity), ty) in
                        let cases = defToFunCases c op_tm dfn in
                        map (fn (lhs, rhs) ->
                               let (lhs,rhs) = addExplicitTyping2(c,lhs,rhs) in
                               prConcat[prString "\"",
                                        ppTerm c Top (mkEquality(Any noPos,lhs,rhs)),
                                        prString "\""])
                          cases)
                  op_qid_infos)
    in
    let def fn_decl_pp_lines (prefix, op_qid_infos) =
          case op_qid_infos of
            | [] -> []
            | (op_qid, ty, dfn, fixity) :: rst ->
              let this_def =
                    [prString prefix,
                     ppIdInfo [op_qid],
                     prString " :: \"",
                     (case fixity of
                        | Infix(assoc,prec) -> ppInfixType c ty   % Infix operators are curried in Isa
                        | _ -> ppType c Top true ty),
                     prString "\""]
                     ++ (case fixity of
                           | Infix(assoc,prec) ->
                             [prString "\t(",
                              case assoc of
                                | Left  -> prString "infixl \""
                                | Right -> prString "infixr \"",
                              ppInfixDefId (op_qid),
                              prString "\" ",
                              prString (show prec),
                              prString ")"]
                           | _ -> [])
              in
              this_def :: fn_decl_pp_lines("and ", rst)
    in
    case findParenAnnotation opt_prag of
      | None ->
        prLinesCat 0 (fn_decl_pp_lines ("fun ", op_qid_infos)
                      ++
                      [[prString "where"],
                       [prString "   ", prSep (-2) blockAll (prString "| ") pp_cases]])
      | Some patt_control_str ->
        let (prf_pp, includes_prf_terminator?) = processOptPrag opt_prag in
        prLinesCat 0 (fn_decl_pp_lines ("function ", op_qid_infos)
                      ++
                      [[prString "where"],
                       [prString "   ", prSep (-2) blockAll (prString "| ") pp_cases]]
                    ++ prf_pp
                    ++ (if prf_pp = []
                         then [[prString defaultFunctionProof]]
                             ++ (if prfEndsWithTerminator? defaultFunctionProof then []
                                   else [[prString "done", prEmpty]])
                         else (if includes_prf_terminator?
                                 then []
                                 else [[prString "done", prEmpty]])))


  op hasForwardCoProductTypeRef?(qid: QualifiedId, els: SpecElements, spc: Spec) : Bool =
    let type_refs = typesInTypeDefFor(qid, spc) in
    if type_refs = [] then false
    else
    exists? (fn el -> case el of
                        | TypeDef(qid, _) -> qid in? type_refs
                        | _ -> false)
      els
        
  op findMutuallyRecursiveCoProductElts(qid0: QualifiedId, els: SpecElements, spc: Spec)
       : SpecElements * SpecElements =
    let type_refs = typesInTypeDefFor(qid0, spc) in
    let def findMutuallyRecursiveTypes(els, type_refs, mr_els, pending_prag_els) =
          case els of
            | [] -> (mr_els, pending_prag_els)
            | el :: r_els ->
          case el of
            | TypeDef(qid, _) ->
              if qid in? type_refs
                then let new_type_refs = typesInTypeDefFor(qid, spc) in
                     findMutuallyRecursiveTypes(r_els, type_refs ++ new_type_refs,
                                                mr_els ++ [el], pending_prag_els)
                else (mr_els, pending_prag_els ++ [el] ++ r_els)
            | _ -> findMutuallyRecursiveTypes(r_els, type_refs, mr_els,
                                              pending_prag_els ++ [el])
    in
    findMutuallyRecursiveTypes(els, type_refs, [], [])

  op ppMutuallyRecursiveCoProductElts (c: Context) (els: SpecElements): Prettys =
    let spc = getSpec c in
    let def ppMRC (els, header) =
          case els of
          | [] -> []
          | (TypeDef(mainId, _)) :: r_els ->
          case specialTypeInfo c mainId of
          | Some _ -> []
          | None ->
          let Some {names, dfn} = AnnSpec.findTheType(spc, mainId) in
          let (tvs, ty) = unpackType dfn in
          (case ty of
            | CoProduct(taggedTypes,_) ->
             (let def ppTaggedType (id,optTy) =
                    case optTy of
                      | None -> ppConstructor(c, id, mainId)
                      | Some ty ->
                        prConcat [ppConstructor(c, id, mainId), prSpace,
                                  case ty of
                                    | Product(fields as ("1",_)::_,_) ->	% Treat as curried
                                      prConcat(addSeparator prSpace
                                                 (map (fn (_,c_ty) -> ppType c CoProduct false c_ty) fields))
                                    | _ -> ppType c CoProduct false ty]
              in
              prBreakCat 2
                [[prString header,
                  ppTyVars tvs,
                  ppIdInfo [mainId]],
                 [prString " = ", prSep (-2) blockAll (prString "| ") (map ppTaggedType taggedTypes)]])
            | _ -> (warn("Recursive type "^printQualifiedId mainId^" not a coproduct:\n"^printType ty);
                    prEmpty))
            :: ppMRC(r_els, "and ")
     in
     ppMRC(els, "datatype ")
          

  op normalizeSpecElements (elts: SpecElements): SpecElements =
    case elts of
      | [] -> []
      | (Op (qid1, false, a)) :: (OpDef (qid2, 0, _, _)) :: rst | qid1 = qid2 ->
        Cons(Op(qid1, true, a), normalizeSpecElements rst)
      | x::rst -> x :: normalizeSpecElements rst

  op abstractionFn (qid: QualifiedId): QualifiedId =
    mkUnQualifiedId("Abs_"^qidToIsaString qid)

  op reprFn (qid: QualifiedId): QualifiedId =
    mkUnQualifiedId("Rep_"^qidToIsaString qid)

  op mkTypeCoercionEntryForTypeDef (spc: Spec) (type_qid: QualifiedId) (tct: TypeCoercionTable): TypeCoercionTable =
    case AnnSpec.findTheType(spc, type_qid) of
      | Some info ->
        let (ty_vars, ty) = unpackType info.dfn in
        (case ty of
           | Subtype(superty, pred, _) ->
             let subty = mkBase(type_qid, map mkTyVar ty_vars) in
             let abstr_qid =  abstractionFn type_qid in
             let repr_qid =  reprFn type_qid in
             let coerce_info = {subtype = type_qid,
                                supertype = superty,
                                coerceToSuper = mkOp(repr_qid, mkArrow(subty, ty)),
                                coerceToSub   = mkOp(abstr_qid, mkArrow(ty, subty)),
                                overloadedOps = []}
             in
             coerce_info :: tct
           | _ -> (warn("typedef pragma ignored for non-subtype type: "^printQualifiedId type_qid);
                   tct))
      | None -> (warn("typedef pragma ignored for undefined type: "^printQualifiedId type_qid);
                 tct)

  op coercionsFromTypeDefPragmas (spc: Spec): TypeCoercionTable =
    let dummy_qid = mkUnQualifiedId "__dummy__" in
    (foldlSpecElements (fn ((tct, type_qid), el) ->
                         case el of
                           | Pragma("proof", prag_str, "end-proof", _) ->
                             (let line1 = case search("\n", prag_str) of
                                | None -> prag_str
                                | Some n -> subFromTo(prag_str, 0, n)
                              in
                              case removeEmpty(splitStringAt(line1, " ")) of
                                | [pragma_kind, "-typedef"]
                                    | (pragma_kind = "Isa" || pragma_kind = "isa") ->
                                  if type_qid = dummy_qid
                                    then (warn("Can't find type for typedef pragma.");
                                          (tct, type_qid))
                                    else (mkTypeCoercionEntryForTypeDef spc type_qid tct, dummy_qid)
                                | pragma_kind :: nm :: rst | validName? nm && "-typedef" in? rst ->
                                  let type_qid = case parseQualifiedId nm of
                                                   | Qualified(UnQualified, nm) ->
                                                     let Qualified(q, _) = type_qid in
                                                     Qualified(q, nm)
                                                   | qid -> qid                                                     
                                  in
                                  (mkTypeCoercionEntryForTypeDef spc type_qid tct, dummy_qid)
                                | _ -> (tct, type_qid))
                           | TypeDef(qid, _) -> (tct, qid)
                           | _ -> (tct, type_qid))
        ([], dummy_qid) spc.elements).1

  op removeDefsOfOpaqueTypes (coercions: TypeCoercionTable) (spc: Spec): Spec * List(QualifiedId * MSType) =
    let opaque_type_map = foldTypeInfos
                                 (fn (info, opt_map) ->
                                  let qid = primaryTypeName info in
                                  % let _ = writeLine("rdo: "^printQualifiedId qid^" = "^printType(unpackFirstTypeDef info).2
                                  %                   ^"\n"^printType(unpackFirstTypeDef info).2) in
                                  if opaqueTypeQId? coercions qid && embed? Subtype (unpackFirstTypeDef info).2
                                   then (qid, info.dfn) :: opt_map
                                   else opt_map)
                                [] spc.types
    in
    let spc = spc << {types = mapTypeInfos
                                (fn info ->
                                 let qid = primaryTypeName info in
                                 if opaqueTypeQId? coercions qid && embed? Subtype (unpackFirstTypeDef info).2
                                   then info << {dfn = And([],noPos)}
                                   else info)
                                spc.types}
    in
    (spc, opaque_type_map)

  op addTypeDefs (spc: Spec) (opaque_type_map: List(QualifiedId * MSType)): Spec =
   let spc  = spc << {types = mapTypeInfos
                                (fn info ->
                                 let qid = primaryTypeName info in
                                 case findLeftmost (fn (opaque_qid, _) -> opaque_qid = qid) opaque_type_map of
                                   |  Some(_, opaque_dfn) -> info << {dfn = opaque_dfn}
                                   | _ -> info)
                                spc.types}
   in
   spc

  op  ppSpecElement: Context -> Spec -> SpecElement -> Option Pragma
                    -> SpecElements -> Pretty
  def ppSpecElement c spc elem opt_prag elems =
    case elem of
      | Import (_, im_sp, im_elements, _) -> prEmpty
      | Op (qid as Qualified(_, nm), def?, _) ->
	(case findTheOp(spc, qid) of
	   | Some {names, fixity, dfn, fullyQualified?=_} ->
	     ppOpInfo c true def? elems opt_prag
               names fixity 0 dfn  % TODO: change  op_with_def?  to  def? -- no one looks at it??
	   | _ -> 
	     let _  = toScreen("\nInternal error: Missing op: "
				 ^ printQualifiedId qid ^ "\n") in
	     prString "<Undefined Op>")
      | OpDef(qid as Qualified(_,nm), refine_num, hist, _) ->
	(case findTheOp(spc, qid) of
	   | Some {names, fixity, dfn, fullyQualified?=_} ->
             let names = map (refinedQID refine_num) names in
	     ppOpInfo c (refine_num > 0) true elems opt_prag names fixity refine_num dfn
	   | _ -> 
	     let _  = toScreen("\nInternal error: Missing op: "
				 ^ printQualifiedId qid ^ "\n") in
	     prString "<Undefined Op>")
      | Type (qid,_) ->
	(case AnnSpec.findTheType(spc, qid) of
	   | Some {names, dfn} -> ppTypeInfo c false (names, dfn) opt_prag elems
	   | _ -> 
	     let _  = toScreen("\nInternal error: Missing type: "
				 ^ printQualifiedId qid ^ "\n") in
	     prString "<Undefined Type>")
      | TypeDef (qid, pos) ->
        if existsSpecElement? (fn el ->
                                 case el of
                                   | Type (qid1,_) -> qid1 = qid
                                     %| TypeDef (qid1, pos1) -> qid1 = qid && pos ~= pos1
                                   | _ -> false)
             elems
          then (warn("Redefinition of type "^printQualifiedId qid^" at "^printAll pos);
                prString("<Illegal type redefinition of "^printQualifiedId qid^">"))
        else 
	(case AnnSpec.findTheType(spc, qid) of
	   | Some {names, dfn} -> ppTypeInfo c true (names, dfn) opt_prag elems
	   | _ -> 
	     let _  = toScreen("\nInternal error: Missing type: "
				 ^ printQualifiedId qid ^ "\n") in
	     prString "<Undefined Type>")
      | Property prop -> ppProperty c prop "" elems opt_prag
      | Pragma("proof", mid_str, "end-proof", pos) | verbatimPragma? mid_str ->
        let verbatim_str = case search("\n", mid_str) of
                             | None -> ""
                             | Some n -> specwareToIsaString(subFromTo(mid_str, n, length mid_str))
        in
        prLines 0 [prString verbatim_str]
	   
      | Pragma("proof", mid_str, "end-proof", pos) | hookPragma? mid_str ->
        (case controlPragmaString mid_str of
          | Some(_ :: hook_name :: _) ->
            (case findPragmaNamed1(elems, hook_name) of
              | Some("proof", mid_str, "end-proof", pos) ->
                let verbatim_str = case search("\n", mid_str) of
                                     | None -> ""
                                     | Some n -> specwareToIsaString(subFromTo(mid_str, n, length mid_str))
                in
                prLines 0 [prString verbatim_str]
              | None -> (warn("Hook "^hook_name^" not found!");
                         prEmpty))
          | _ -> (warn("Unnamed hook!");
                  prEmpty))

      | Comment (str,_) ->
	prConcat [prString "(*",
		  prString str,
		  prString "*)"]
      | _ -> prEmpty

 op xSymbolWords: List String = ["and", "or", "And", "Or", "lbrakk", "rbrakk", "inter", "union",
                                 "in", "notin", "lambda", "bar", "Colon",
                                 "Rightarrow", "Longrightarrow", "noteq",
                                 "forall", "exists", "equiv", "ge", "le", "times", "plus", "minus",
                                 "Inter", "Sqinter", "Union", "Squnion", "Prod", "not", "Sum"]
 op findXSymbolWord(s: String, start: Nat): Option Nat =
   let def find1 words =
         case words of
           | [] -> None
           | w::r ->
             let end_pos = start + length w - 1 in
             if testSubseqEqual?(w, s, 0, start)
               then Some (end_pos)
               else find1 r
   in
   find1 xSymbolWords
            

 op specwareToIsaString(s: String): String =
   case search("\\_", s) of
     | None -> s
     | Some i ->
   let len = length s in
   let def loop j =
         if j >= len then j-1
         else if isAlphaNum(s@j)
                 then loop(j+1)
                 else j-1
   in
   let j = case findXSymbolWord(s, i+2) of
             | Some j -> j
             | None -> loop(i+2)
   in
   subFromTo(s, 0, i+1) ^ "<" ^ subFromTo(s, i+2, j+1) ^ ">" ^ specwareToIsaString(subFromTo(s, j+1, len))
         

 op findPragmaNamed(elts: SpecElements, qid as (Qualified(q, nm)): QualifiedId, opt_prag: Option Pragma)
     : Option Pragma =
   % let _ = writeLine("findPragmaNamed: "^printQualifiedId qid^" opt_prag: "^anyToString opt_prag) in
   case findPragmaNamed1(elts, q^"__"^nm) of
     | Some p -> Some p
     | None ->
   case findPragmaNamed1(elts, qidToIsaString qid) of   % Allow Isabelle name
     | Some p -> Some p
     | None ->
   case findPragmaNamed1(elts, printQualifiedId qid) of   % Allow Specware qualified name
     | Some p -> Some p
     | None ->   %% Try without qualifier
   case findPragmaNamed1(elts, nm) of
     | Some p -> Some p
     | None ->                          % Allow Isabelle name
   case findPragmaNamed1(elts, ppIdStr nm) of
     | Some p -> Some p
     | None -> opt_prag

 op  findPragmaNamed1: SpecElements * String -> Option Pragma
 def findPragmaNamed1(elts, nm) =
   %% Finds last pragma named
   % let _ = writeLine("findPragmaNamed1: "^nm) in
   let result =
         case elts of
          | [] -> None
          | el::rst ->
            (case el of
               | Pragma(p_bod as ("proof", prag_str, "end-proof", _)) ->
                 (case findPragmaNamed1(rst, nm) of
                    | None ->
                      (let line1 = case search("\n", prag_str) of
                                    | None -> prag_str
                                    | Some n -> subFromTo(prag_str, 0, n)
                       in
                       case removeEmpty(splitStringAt(line1, " ")) of
                         | pragma_kind::thm_nm::r | (pragma_kind = "Isa" || pragma_kind = "isa") && thm_nm = nm ->
                           Some p_bod
                         | _ -> None)
                    | rec_result -> rec_result)
               | _ -> findPragmaNamed1(rst, nm))
   in
   % let _ = writeLine("returned: "^anyToString result) in
   result

 op isabelleReservedWords: List String = ["value", "defs", "theory", "imports", "begin", "end", "axioms",
                                          "axiomatization",
                                          "recdef", "primrec", "consts", "class", "primitive",
                                          "next", "instance", "and", "open", "extract"]
 op disallowedVarNames: List String =          % \_dots Don't know how to get all of them
   ["hd", "tl", "comp", "fold", "map", "o", "size", "mod", "exp", "snd", "O", "OO", "True",
    "False", "Not", "sub", "sup", "Sigma", "map", "dom", "field", "fields", "acc", "id",
    "max", "mem"]

 op directConstructorTypes: List QualifiedId =
   [Qualified("Option", "Option"),
    Qualified("List", "List"),
    Qualified("Compare", "Comparison")]

op constructorTranslation(c_nm: String, c: Context): Option String =
   case specialOpInfo c (mkUnQualifiedId c_nm) of
     | Some(tr_nm, None, false, false, true) ->
       Some tr_nm
     | _ -> None


 op ppConstructor(c: Context, c_nm: String, qid: QualifiedId): Pretty =
   case constructorTranslation(c_nm, c) of
     | Some tr_c_nm -> prString tr_c_nm
     | None -> 
   prString(if qid in? directConstructorTypes then ppIdStr c_nm
              else qidToIsaString qid^"__"^ppIdStr c_nm)

 op ppConstructorTyped(c: Context, c_nm: String, ty: MSType, spc: Spec): Pretty =
   case unfoldToBaseNamedType(spc, ty) of
     | Base(qid, _, _) -> ppConstructor(c, c_nm, qid)
     | _ -> fail("Couldn't find coproduct type of constructor "^c_nm)

 op  ppIdInfo : List QualifiedId -> Pretty
 def ppIdInfo qids =
   let qid = head qids in
   case qid of
     | Qualified(qual, nm) | qual = UnQualified && nm in? isabelleReservedWords ->
       prConcat [prString "\"", ppQualifiedId qid, prString "\""]
     | _ ->  ppQualifiedId qid

 op mkFieldName(nm: String): String = ppIdStr nm ^ "__fld"
 op mkNamedRecordFieldName (c: Context)(qid: QualifiedId, nm: String): String =
   (typeQualifiedIdStr c qid)^"__"^ppIdStr nm

 op ppToplevelName(nm: String): Pretty =
   if nm in? isabelleReservedWords
     then prConcat [prString "\"", prString nm, prString "\""]
     else prString nm

 op quoteIf(quote?: Bool, nm: String, pr: Pretty): Pretty =
   if quote? && nm in? isabelleReservedWords then prConcat [prString "\"", pr, prString "\""]
   else pr

   
 op  ppTypeInfo : Context -> Bool -> List QualifiedId * MSType -> Option Pragma -> SpecElements -> Pretty
 def ppTypeInfo c full? (aliases, dfn) opt_prag elems =
   let mainId = head aliases in
   let opt_prag = findPragmaNamed(elems, mainId, opt_prag) in
   let (mainId, no_def?) =
       case specialTypeInfo c mainId of
         | Some(isa_id, _, _, no_def?) -> (stringToQId isa_id, no_def?)
         | None -> (mainId, false)
   in
   if no_def? then prEmpty
   else
   let aliases = [mainId] in
   let (tvs, ty) = unpackType dfn in
   % let _ = writeLine("type "^printQualifiedId mainId^" = "^printType ty^"\n"^anyToString opt_prag) in
   if full? && ~(embed? Any ty)
     then case ty of
	   | CoProduct(taggedTypes,_) ->
             (let def ppTaggedType (id,optTy) =
                case optTy of
                  | None -> ppConstructor(c, id, mainId)
                  | Some ty ->
                    prConcat [ppConstructor(c, id, mainId), prSpace,
                              case ty of
                                | Product(fields as ("1",_)::_,_) ->	% Treat as curried
                                  prConcat(addSeparator prSpace
                                             (map (fn (_,c_ty) -> ppType c CoProduct false c_ty) fields))
                                | _ -> ppType c CoProduct false ty]
              in
              prBreakCat 2
                [[prString "datatype ",
                  ppTyVars tvs,
                  ppIdInfo aliases],
                 [prString " = ", prSep (-2) blockAll (prString "| ") (map ppTaggedType taggedTypes)]])
	   | Product (fields,_) | length fields > 0 && (head fields).1 ~= "1" ->
	     prLinesCat 2
	       ([[prString "record ",
		  ppTyVars tvs,
		  ppIdInfo aliases,
		  prString " = "]] ++
		(map (fn (fldname, fldty) ->
		      [ppToplevelName (mkNamedRecordFieldName c (mainId, fldname)),
                       prString " :: ", ppType c Top false fldty])
		 fields))
           | Subtype(superty, pred, _) | some? opt_prag ->
             let  (prf_pp,includes_prf_terminator?) = processOptPrag opt_prag in
             prLinesCat 2 ([[prString "typedef ", ppTyVars tvs, ppIdInfo aliases, prString " = \"",
                             %if tvs = [] then ppTerm c Top pred
                             %  else
                                 let spc = getSpec c in
                                 let pred_dom_ty = domain(spc, inferType(spc, pred)) in
                                 let (v_pp, pred) =
                                     case pred of
                                       | Lambda([(VarPat((x1,_),_), _, Apply(pred1, Var((x2, _), _), _))], _) | x1 = x2 ->
                                         (prString x1, pred1)
                                       | _ -> (prString "x", pred)
                                 in
                                 prConcat [prString "{", v_pp, prString ":: ", ppType c Top true pred_dom_ty,
                                           prString ". ", ppTerm c Nonfix pred, prString " ", v_pp, prString "}"],
                             prString "\""]]
                           ++ prf_pp
                           ++ (if prf_pp = []
                                 then [[prString c.defaultProof]]
                                   ++ (if prfEndsWithTerminator? c.defaultProof then []
                                       else [[prString "done",prEmpty]])
                               else (if includes_prf_terminator?
                                       then []
                                     else [[prString "done",prEmpty]])))
	   | _ ->
	     prBreakCat 2
	       [[prString "type_synonym ",
		 ppTyVars tvs,
		 ppIdInfo aliases,
		 prString " = "],
		[prString "\"", ppType c Top true ty, prString "\""]]
     else prBreakCat 2
	    [[prString "typedecl ",
	      ppTyVars tvs,
	      ppIdInfo aliases]]

 op  ppTyVars : TyVars -> Pretty
 def ppTyVars tvs =
   case tvs of
     | [] -> prEmpty
     | [tv] -> prConcat [prString "'", prString tv, prSpace]
     | _ -> prConcat [prString " (",
		      prPostSep 0 blockFill (prString ",")
		        (map (fn tv -> prConcat[prString "'", prString tv]) tvs),
		      prString ")"]

 op convertPrecNum(sw_prec_num: Nat): Nat =
   sw_prec_num + 40                     % Right for +


 op convertFixity(fx: Fixity): Fixity =
   case fx of
     | Infix(assoc, prec) -> Infix(assoc, convertPrecNum prec)
     | _ -> fx

 op expandNatToSucc(tm: MSTerm): MSTerm =
   case tm of
     | Fun(Nat i, _, _) | i ~= 0 && i < 10 ->
       let def expandNat i =
            if i = 0 then mkNat 0
              else mkApply(mkOp(Qualified("Nat", "succ"), mkArrow(natType, natType)),
                           expandNat(i - 1))
       in
       expandNat i              
     | _ -> tm

 op  defToFunCases: Context -> MSTerm -> MSTerm -> List (MSTerm * MSTerm)
 def defToFunCases c op_tm bod =
   let spc = getSpec c in
   let
     def aux(hd, bod) =
       % let _ = writeLine("dtfc: "^printTerm hd^" = "^printTerm bod) in
       case bod of
         | Lambda ([(VarPat (v as (nm,ty),_), _, term)], a) ->
           aux(Apply(hd, mkVar v, a), term)
         | Lambda ([(pattern, _, term)], a) ->
           (case patToTerm (pattern, "",  c) of
              | Some pat_tm ->
                aux (Apply(hd, pat_tm, a), term)
              | _ -> [(hd, bod)])
         | Apply(Lambda(match,  _), arg, _) | charMatch? match ->
           aux(hd, caseToIf(c, match, arg))
         | Apply (Lambda (pats,_), Var(v,_), _) ->
           if exists? (fn v1 -> v = v1) (freeVars hd)
            then foldl (fn (cases, (pati, _, bodi)) ->
                        case patToTerm(pati, "",  c) of
                          | Some pati_tm ->
                            let pati_tm = mapTerm (expandNatToSucc, id, id) pati_tm in
                            let sbst = [(v, pati_tm)] in
                            let s_bodi = if hasVarNameConflict?(pati_tm, [v]) then bodi
                                          else substitute(bodi, sbst)
                            in
                            let new_cases = aux_case(substitute(hd, sbst), s_bodi) in
                            (cases ++ new_cases)
                          | _ ->
                            let new_cases = aux_case(hd, bodi) in
                            (cases ++ new_cases))
                   [] pats
            else [(hd, bod)]
         | Apply (Lambda (pats,_), arg as Record(var_tms,_), _)
             | tupleFields? var_tms    % ??
               &&  forall? (fn (_,t) -> embed? Var t) var_tms
%                && (case hd of
%                      | Apply(_,param,_) -> equalTerm?(param,arg)
%                      | _ -> false)
           ->
           let def matchPat (p: MSPattern, cnd, bod: MSTerm): Option (MSTerm * MSTerm) =
                 case p of
                   | RecordPat(rpats,_) ->
                     let sbst = mapPartial (fn ((_, v_tm as Var(v, _)), (_, p1)) ->
                                              case p1 of
                                                | WildPat _ -> Some(v, v_tm)  % id
                                                | _ ->
                                              case patToTerm (p1, "", c) of
                                                | Some p_tm -> Some(v, p_tm)
                                                | None -> None)
                                 (zip (var_tms, rpats))
                     in
                     if length sbst ~= length rpats then None
                     else
                     let bod_sbst = filter (fn (v,tm) -> ~(hasVarNameConflict?(tm, [v]))) sbst in
                     Some(substitute(hd, sbst), substitute(bod, bod_sbst))
                   | VarPat(v, _) -> Some(hd, substitute(bod, [(v, arg)]))
                   | WildPat _ -> Some(hd, bod)
                   | AliasPat(VarPat(v, _), p2, _) -> matchPat(p2, cnd, substitute(bod, [(v, arg)]))
                   | RestrictedPat(rp,_,_) -> matchPat(rp, cnd, bod)
                   | _ -> None
           in
           let cases = mapPartial matchPat pats in
           if length cases = length pats
             then foldl (fn (cases, (lhs,rhs)) -> cases ++ aux(lhs,rhs)) [] cases
             else [(hd, bod)]
         | Let([(pat, Var(v,_))], bod, a) | v in? freeVars hd ->
           (case patToTerm(pat, "",  c) of
              | Some pat_tm ->
                let s_bod = if hasVarNameConflict?(pat_tm, [v]) then bod
                            else substitute(bod,[(v,pat_tm)])
                in
                aux(substitute(hd, [(v,pat_tm)]), s_bod)
              | None -> [(hd, bod)])
         | IfThenElse(Apply(Fun(Equals, _,_),
                            Record([("1", vr as Var(v as (vn,s),_)),
                                    ("2",zro as Fun(Nat 0,_,_))],_),
                            _),
                      then_cl, else_cl, _)
             | natType? s && inVars?(v, freeVars hd) ->
           let cases1 = aux(substitute(hd, [(v,zro)]), substitute(then_cl, [(v,zro)])) in
           let cases2 = aux(substitute(hd, [(v,mkApply(mkOp(Qualified("Nat","succ"),
                                                            mkArrow(natType, natType)),
                                                       vr))]),
                            simpSubstitute(spc, else_cl,
                                           [(v,mkApply(mkOp(Qualified("Integer","+"),
                                                            mkArrow(mkProduct [natType, natType],
                                                                    natType)),
                                                       mkTuple[vr,mkNat 1]))]))
           in
           cases1 ++ cases2
         | _ -> [(hd,bod)]
     def aux_case(hd,bod: MSTerm) =
       aux(hd,bod) 
     def fix_vars(hd,bod) =
       case hd of
         | Fun(_, ty, _) ->
           (case arrowOpt(spc, ty) of
              | Some(dom,_) ->
                let new_v = mkVar("x__a", dom) in
                (mkApply(hd, new_v), mkApply(bod, new_v))
              %% Shouldn't happen?
              | None -> (hd,bod))
         | _ ->
       let fvs = freeVars hd ++ freeVars bod in
       let rename_fvs = filter (fn (nm,_) -> nm in? disallowedVarNames) fvs in
       if rename_fvs = [] then (hd,bod)
         else let sb = map (fn (v as (nm,ty)) -> (v,mkVar(nm^"_v",ty))) rename_fvs in
              let bod_sb = filter (fn (v,tm) -> ~(hasVarNameConflict?(tm, [v]))) sb in
              (substitute(hd,sb), substitute(bod,bod_sb))
   in
   case bod of
     | Lambda ([(RestrictedPat(rpat,_,_),condn,tm)], a) ->
       defToFunCases c op_tm (Lambda ([(rpat, condn, tm)], a))
     | _ ->
   let cases =
         case bod of
           | Lambda ([(recd as (RecordPat (prs as (("1",_)::_),_)), _, tm)],a)
               | varOrTuplePattern? recd ->
             let Some arg = patToTerm(recd,"", c) in
             let cases = aux(Apply(op_tm, arg, a), tm) in
             cases
           | _ -> aux(op_tm, bod)
   in
   let def normalize_args cases =
         %% Make sure all cases have the same number of args
         let (max_args, min_args) = foldl (fn ((mx,mn), (x,_)) ->
                                             let nc_args = numCurryArgs x in
                                             (max(mx, nc_args), min(mn, nc_args)))
                                      (0, 100) cases
         in
         if max_args = min_args then cases
           else normalize_args(map (fn (x,y) ->
                                      let num_args = numCurryArgs x in
                                      if num_args = max_args then (x,y)
                                      else
                                        let v = mkVar("xx__"^show num_args, range(spc, inferType(spc, x))) in
                                        (mkApply(x, v), mkApply(y, v)))
                                 cases)
   in
   let cases = normalize_args cases in
   % let _ = app (fn (x,y) -> writeLine(printTerm x^" -> "^printTerm y)) cases in
   % let _ = writeLine(" = "^show (length cases)^", "^show tuple?) in
   (map fix_vars cases)

 op prfFromPragma ((_,mid_str,_,_): Pragma): String =
   let len = length mid_str in
   case search("\n",mid_str) of
     | None -> (case removeEmpty(splitStringAt(mid_str, " ")) of
                  | _ :: _ :: p1 :: rst -> foldl (fn (result, w) -> result ^ " " ^ w) p1 rst
                  | _ -> autoProof)
     | Some n -> stripExcessWhiteSpace(subFromTo(mid_str,n+1,len))

 op processOptPrag(opt_prag: Option Pragma): List (List Pretty) * Bool =
   case opt_prag of
     | Some(beg_str,mid_str,end_str,pos) ->
       let len = length mid_str in
       (case search("\n",mid_str) of
          | None -> ([], false)
          | Some n ->
            let prf_str = stripExcessWhiteSpace(subFromTo(mid_str,n+1,len)) in
            ([[prString(specwareToIsaString prf_str)]],
             prfEndsWithTerminator? prf_str))
     | _ -> ([], false)

op defaultFunctionProof: String =
   "by pat_completeness auto\ntermination by lexicographic_order"

op ppFunctionDef (c: Context) (aliases: Aliases) (dfn: MSTerm) (ty: MSType) (opt_prag: Option Pragma) (fixity: Fixity)
    : Pretty =
  let mainId = head aliases in
  let op_tm = mkFun (Op (mainId, fixity), ty) in
  let cases = defToFunCases c op_tm dfn in
  let pp_cases = map (fn (lhs, rhs) ->
                        let (lhs,rhs) = addExplicitTyping2(c,lhs,rhs) in
                        prConcat[prString "\"",
                                 ppTerm c Top (mkEquality(Any noPos,lhs,rhs)),
                                 prString "\""])
                   cases
  in
  case findParenAnnotation opt_prag of
    | None ->
      prLinesCat 0 ([[prString "fun ", ppIdInfo aliases,
                     prString " :: \"",
                     (case fixity of
                        | Infix(assoc,prec) -> ppInfixType c ty   % Infix operators are curried in Isa
                        | _ -> ppType c Top true ty),
                     prString "\""]
                     ++ (case fixity of
                           | Infix(assoc,prec) ->
                             [prString "\t(",
                              case assoc of
                                | Left  -> prString "infixl \""
                                | Right -> prString "infixr \"",
                              ppInfixDefId (mainId),
                              prString "\" ",
                              prString (show prec),
                              prString ")"]
                           | _ -> []),
                     [prString "where"],
                     [prString "   ", prSep (-2) blockAll (prString "| ") pp_cases]])
    | Some patt_control_str ->
      let (prf_pp,includes_prf_terminator?) = processOptPrag opt_prag in
      prLinesCat 0 ([[prString "function ",
                      (if patt_control_str = "()" then prString ""
                         else prConcat [prString patt_control_str, prSpace]),
                      ppIdInfo aliases,
                      prString " :: \"",
                      (case fixity of
                        | Infix(assoc,prec) -> ppInfixType c ty   % Infix operators are curried in Isa
                        | _ -> ppType c Top true ty),
                      prString "\""]
                     ++ (case fixity of
                           | Infix(assoc,prec) ->
                             [prString "\t(",
                              case assoc of
                                | Left  -> prString "infixl \""
                                | Right -> prString "infixr \"",
                              ppInfixDefId (mainId),
                              prString "\" ",
                              prString (show prec),
                              prString ")"]
                           | _ -> []),
                     [prString "where"],
                     [prString "   ", prSep (-2) blockAll (prString "| ") pp_cases]]
                  ++ prf_pp
                  ++ (if prf_pp = []
                       then [[prString defaultFunctionProof]]
                           ++ (if prfEndsWithTerminator? defaultFunctionProof then []
                                 else [[prString "done", prEmpty]])
                       else (if includes_prf_terminator?
                               then []
                               else [[prString "done",prEmpty]])))

op  ppOpInfo :  Context -> Bool -> Bool -> SpecElements -> Option Pragma
                  -> Aliases -> Fixity -> Nat -> MSTerm
                  -> Pretty
def ppOpInfo c decl? def? elems opt_prag aliases fixity refine_num dfn =
  %% Doesn't handle multi aliases correctly
  let c = c << {newVarCount = Ref 0} in
  let mainId = head aliases in
  % let _ = writeLine("Processing "^printQualifiedId mainId) in
  let opt_prag = findPragmaNamed(elems, mainId, opt_prag) in
  let (no_def?, mainId, fixity) =
      case specialOpInfo c mainId of
        | Some (isa_id, infix?, _, _, no_def?) ->
          (no_def?, mkUnQualifiedId(isa_id),
           case infix? of
             | Some pr -> Infix pr
             | None -> fixity)
        | _ -> (refine_num > 0 && anyTerm?(unpackNthTerm(dfn, refine_num)).3,
                mainId, convertFixity fixity)
  in
  if no_def?
    then prEmpty
  else
  let (tvs, ty, term) = if def? then unpackNthTerm(dfn, refine_num)
                         else unpackTerm(dfn)
  in
  let aliases = [mainId] in
  if decl? && def? && targetFunctionDefs?
      %% The following conditions are temporary!!
      %% Don't want f(x,y) = ... to be a fun because this would be added as a rewrite
      && (some?(findParenAnnotation opt_prag)
           || % none?(findMeasureAnnotation opt_prag)
               %&&
               (case defToFunCases c (mkFun (Op (mainId, fixity), ty)) term of
                     | [(lhs, rhs)] ->
                       %let _ = writeLine("defToFunCases: "^printTerm lhs^"\n = "^printTerm rhs) in
                       (case lhs of
                        | Apply(Apply _, _, _) -> containsRefToOp?(rhs, mainId) % recursive
                        | Apply _ | exists? (fn arg ->
                                               case arg of
                                                 | Apply(Fun(Embed _, _, _), _, _) -> true
                                                 | Fun(Embed _, _, _) -> true
                                                 | Fun(Nat _, _, _) -> true
                                                 | Fun(Char _, _, _) -> true
                                                 | Fun(String _, _, _) -> true
                                                 | Fun(Bool _, _, _) -> true
                                                 | _ -> false)
                                      (getArgs lhs) ->
                          true
                        | _ ->
                        case fixity of
                        | Infix _ ->
                          (foldSubTerms (fn (tm, count) ->
                                           case tm of
                                             | Var _ -> count
                                             | Apply _ -> count
                                             | Record _ -> count
                                             | _ -> %let _ = writeLine (printTerm tm) in
                                                    count + 1)
                             0 lhs)
                           > 1
                        | _ -> containsRefToOp?(rhs, mainId) )
                     | _ -> true)
              )

    then
      ppFunctionDef c aliases term ty opt_prag fixity
  else
  let decl_list = 
        if decl?
          then [[prString "consts ",
                %ppTyVars tvs,
                ppIdInfo aliases,
                prString " :: \"",
                (case fixity of
                  | Infix(assoc, prec) -> ppInfixType c ty   % Infix operators are curried in Isa
                  | _ -> ppType c Top true ty),
                prString "\""]
             ++ (case fixity of
                   | Infix(assoc,prec) ->
                     [prString "\t(",
                      case assoc of
                        | Left  -> prString "infixl \""
                        | Right -> prString "infixr \"",
                      ppInfixDefId (mainId),
                      prString "\" ",
                      prString (show prec),
                      prString ")"]
                   | _ -> [])]
           else []
  in
  let infix? = case fixity of Infix _ -> true | _ -> false in
  let def_list = if def? then [[ppDef c mainId ty opt_prag term fixity]] else []
  in prLinesCat 0 (decl_list ++ def_list)

 op ensureNotCurried(lhs: MSTerm, rhs: MSTerm): MSTerm * MSTerm =
   case lhs of
     | Apply(h as Apply _, Var(v, _), _) ->
       ensureNotCurried(h, mkLambda(mkVarPat v, rhs))
     | _ -> (lhs, rhs)

 op  ppDef: Context -> QualifiedId -> MSType -> Option Pragma -> MSTerm -> Fixity -> Pretty
 def ppDef c op_nm ty opt_prag body fixity =
   let recursive? = containsRefToOp?(body, op_nm) in
   let op_tm = mkFun (Op (op_nm, fixity), ty) in
   let infix? = case fixity of Infix _ -> true | _ -> false in
   case defToCases c op_tm body infix? of
     | ([(lhs,rhs)], tuple?) ->
       % let _ = writeLine(printTerm lhs^"\n= "^printTerm rhs) in
       let (lhs,rhs) = addExplicitTyping2(c,lhs,rhs) in
       if ~tuple? && existsSubTerm constructorTerm? lhs
         then prBreak 2 [prString "primrec ",
                          prString "\"",
                          ppTerm c Top (mkEquality(Any noPos,lhs,rhs)),
                          prString "\""]
         else if recursive? % || tuple? % && ~(simpleHead? lhs))
             then
               let (lhs, rhs) = ensureNotCurried(lhs, rhs) in
               prLinesCat 2 [[prString "recdef ", ppQualifiedId op_nm, prSpace,
                              case findMeasureAnnotation opt_prag of
                                | Some anot -> prConcat[prString (specwareToIsaString anot)]
                                | None -> prConcat [prString (if recursive?
                                                                then "\"measure size\""
                                                              else "\"{}\"")]],
                             [prBreakCat 2 [[prString "\"",
                                             ppTerm c (Infix(Left,200)) lhs],
                                            [prString " = ",
                                             %% Note sure what precedence number it should be
                                             ppTerm c (Infix(Left,200)) rhs,
                                             prString "\""]]]]
         else
           let (lhs,rhs) = if tuple? then addExplicitTyping2(c,op_tm,body)
                            else (lhs,rhs)
           in
           prBreakCat 2 [[prString "defs ", ppQualifiedId op_nm, prString "_def",
                          case findBracketAnnotation opt_prag of
                            | Some anot -> prConcat[prSpace,prString(specwareToIsaString anot)]
                            | None -> prEmpty,
                          prString ": "],
                         [prBreakCat 2 [[prString "\"",
                                         ppTerm c (Infix(Left,200)) lhs],
                                        [lengthString(3," \\<equiv> "),
                                         ppTerm c (Infix(Right,200)) rhs,
                                         prString "\""]]]]
     | (cases,false) ->
       prBreak 2 [prString "primrec ",
                  prLinesCat 0 (map (fn(lhs,rhs) ->
                                     let (lhs,rhs) = addExplicitTyping2(c,lhs,rhs) in
                                      [prString "\"",
                                       ppTerm c Top (mkEquality(Any noPos,lhs,rhs)),
                                       prString "\""])
                                       cases)]
     | (cases,true) ->
       prLinesCat 2 [[prString "recdef ", ppQualifiedId op_nm, prSpace,
                      case findMeasureAnnotation opt_prag of
                        | Some anot -> prConcat[prString (specwareToIsaString anot)]
                        | None -> prConcat [prString (if recursive?
                                                        then "\"measure size\""
                                                        else "\"{}\"")]],
                     [prLinesCat 0 (map (fn(lhs,rhs) ->
                                         let (lhs, rhs) = ensureNotCurried(lhs, rhs) in
                                         let (lhs, rhs) = addExplicitTyping2(c, lhs, rhs) in
                                          [prString "\"",
                                           ppTerm c Top (mkEquality(Any noPos, lhs, rhs)),
                                           prString "\""])
                                       cases)]]

 %op  Utilities.patternToTerm : MSPattern -> Option MSTerm
 %op  Utilities.substitute    : MSTerm * MSVarSubst -> MSTerm
 %op  Utilities.freeVars      : MSTerm -> MSVars

op patToTerm(pat: MSPattern, ext: String, c: Context): Option MSTerm = 
    case pat
      of EmbedPat(con,None,ty,a) -> 
         Some(Fun(Embed(con,false),ty,a))
       | EmbedPat(con,Some p,ty,a) -> 
         (case p of
            | WildPat(pty,a) | multiArgConstructor?(con,ty,getSpec c) ->
              let tys = productTypes(getSpec c, pty) in
              let args = (foldr (fn (ty,(result,i)) ->
                                   let cnt = c.newVarCount in
                                   let _ = (cnt := !cnt + 1) in
                                   let v = (if true then "zzz" else "zzz_"^ext)^show (!cnt) in
                                   (Cons(Var((v,ty), a),result),i-1))
                            ([], length tys) tys).1
              in
              Some (Apply(Fun(Embed(con,true),Arrow(pty,ty,a),a),mkTuple args,a))
            | _ ->
          case patToTerm(p, ext, c)
            of None -> None
             | Some (trm) -> 
               let ty1 = patternType p in
               Some (Apply(Fun(Embed(con,true),Arrow(ty1,ty,a),a),trm,a)))
       | RecordPat(fields,a) -> 
         let
            def loop(new,old,i) = 
                case new
                  of [] -> Some(Record(reverse old,a))
                   | (l,p)::new -> 
                case patToTerm(p, ext^(show i), c)
                  of None -> None
                   | Some(trm) -> 
                     loop(new, Cons((l,trm),old), i+1)
         in
         loop(fields,[], 0)
       | NatPat(i, _) -> Some(mkNat i)
       | BoolPat(b, _) -> Some(mkBool b)
       | StringPat(s, _) -> Some(mkString s)
       | CharPat(c, _) -> Some(mkChar c)
       | VarPat((v,ty), a) -> Some(Var((v,ty), a))
       | WildPat(ty,a) ->
         let cnt = c.newVarCount in
         let _ = (cnt := !cnt + 1) in
         let v = "zzz_"^show (!cnt) in
         Some(Var((v,ty), a))
       | QuotientPat(pat,cond,_,_)  -> None %% Not implemented
       | RestrictedPat(pat,cond,_)  ->
         patToTerm(pat,ext, c)		% cond ??
       | AliasPat(p1,p2,_) -> 
         (case patToTerm(p2, ext, c) 
            of None -> patToTerm(p1, ext, c)
             | Some(trm) -> Some trm)

 op constructorTerm?(tm: MSTerm): Bool =
   case tm of
     | Fun(Embed _, _, _) -> true
     | _ -> false

 op primitiveArg?(tm: MSTerm): Bool =
   case tm of
     | Apply(Fun(Embed _, _, _), arg, _) ->
       forall? (embed? Var) (MS.termToList arg)
     | Fun(Embed _, _, _) -> true
     | Var _ -> true
     | _ -> false

 op sameHead?(tm1: MSTerm, tm2: MSTerm): Bool =
   equalTerm?(tm1, tm2)
     || (case (tm1, tm2) of
           | (Apply(x1,_,_), Apply(x2,_,_)) -> sameHead?(x1,x2)
           | _ -> false)

 op nonPrimitiveArg?(tm1: MSTerm, tm2: MSTerm): Bool =
   case tm1 of
     | Apply(Fun(Embed _, _, _), arg, _) ->
       ~(termIn?(tm2, MS.termToList arg))
     | _ -> false

 op hasNonPrimitiveArg?(tm1: MSTerm, tm2: MSTerm): Bool =
   case (tm1, tm2) of
     | (Apply(x1,y1,_), Apply(x2,y2,_)) ->
       nonPrimitiveArg?(y1,y2) || hasNonPrimitiveArg?(x1,x2)
     | _ -> false

 op nonPrimitiveCall? (hd: MSTerm) (tm: MSTerm): Bool =
   sameHead?(hd,tm) && hasNonPrimitiveArg?(hd,tm)

 %% Only concerned with curried calls
 op recursiveCallsNotPrimitive?(hd: MSTerm, bod: MSTerm): Bool =
   existsSubTerm (nonPrimitiveCall? hd) bod

 op patternLambda?(v_pos: Position, lam_pos: Position): Bool =
   %% an explicit lambda will have beginning of variable close to beginning of lambda expr
   usePosInfoForDefAnalysis?
     => (case (v_pos, lam_pos) of
           | (File(_,(_,_,v_byte),_), File(_,(_,_,lam_byte),_)) ->
             v_byte - lam_byte > 4
           | _ -> true)

 op  defToCases: Context -> MSTerm -> MSTerm -> Bool -> List(MSTerm * MSTerm) * Bool
 def defToCases c op_tm bod infix? =
   let
     def aux(hd, bod, tuple?) =
       % let _ = writeLine("aux("^printTerm bod^", "^show tuple?^")") in
       case bod of
         | Lambda ([(VarPat (v as (nm,ty),v_pos),_,term)],a) | ~ tuple? ->
           if patternLambda?(v_pos,a)
             then aux(Apply(hd,mkVar v,a), term, tuple?)
             else ([(hd,bod)], recursiveCallsNotPrimitive?(hd,bod))
         | Lambda ([(pattern,_,term)],a) | ~ tuple? ->
           (case patToTerm (pattern,"", c) of
              | Some pat_tm | primitiveArg? pat_tm ->
                aux (Apply(hd,pat_tm,a), term, tuple? || embed? Record pat_tm)
              | _ -> ([(hd,bod)], tuple? || recursiveCallsNotPrimitive?(hd,bod)))
         | Apply(Lambda(match, _),arg,_) | ~targetFunctionDefs? && nonCaseMatch? match ->
           aux(hd, caseToIf(c, match, arg), tuple?)
         | Apply (Lambda (pats,_), Var(v,_), _) ->
           if exists? (fn v1 -> v = v1) (freeVars hd)
            then foldl (fn ((cases,not_prim), (pati,_,bodi)) ->
                        case patToTerm(pati,"", c) of
                          | Some pati_tm ->
                            let (new_cases,n_p) = aux_case(substitute(hd,[(v,pati_tm)]), bodi, tuple?) in
                            (cases ++ new_cases, not_prim || n_p || ~(primitiveArg? pati_tm))
                          | _ ->
                            let (new_cases,n_p) = aux_case(hd,bodi,tuple?) in
                            (cases ++ new_cases, not_prim || n_p))
                   ([],tuple?) pats
            else ([(hd,bod)], tuple? || recursiveCallsNotPrimitive?(hd,bod))
         | Apply (Lambda (pats,_), arg as Record(var_tms,_), _)
             | tuple? && tupleFields? var_tms
               && forall? (fn (_,t) -> embed? Var t) var_tms
               && (case hd of
                     | Apply(_,param,_) -> equalTerm?(param,arg)
                     | _ -> false)
           ->
           let def matchPat (p,c,bod) =
                 case p of
                   | RecordPat(rpats,_) ->
                     let sbst = mapPartial (fn ((_,v_tm as Var(v,_)),(_,p)) ->
                                              case p of
                                                | WildPat _ -> Some(v,v_tm)  % id
                                                | _ ->
                                              case patternToTerm p of
                                                | Some p_tm -> Some(v,p_tm)
                                                | None -> None)
                                 (zip (var_tms, rpats))
                     in
                     if length sbst ~= length rpats then None
                     else
                     let pat_tms = map (fn (_,p_tm) -> p_tm) sbst in
                     let Apply(hd_hd,_,a) = hd in
                     let bod_sbst = filter (fn (v,tm) -> ~(hasVarNameConflict?(tm, [v]))) sbst in
                     Some(Apply(hd_hd,mkTuple pat_tms,a), substitute(bod,bod_sbst))
                   | VarPat(v,_) -> Some(hd,substitute(bod,[(v,arg)]))
                   | WildPat _ -> Some(hd,bod)
                   | AliasPat(VarPat(v,_),p2,_) -> matchPat(p2,c,substitute(bod,[(v,arg)]))
                   | RestrictedPat(rp,_,_) -> matchPat(rp,c,bod)
                   | _ -> None
           in
           let cases = mapPartial matchPat pats in
           if length cases = length pats
             then (cases, true)
             else ([(hd,bod)], true)
         | Let([(pat,Var(v,_))],bod,a) | tuple? && v in? freeVars hd ->
           (case patToTerm(pat,"", c) of
              | Some pat_tm ->
                let s_bod = if hasVarNameConflict?(pat_tm, [v]) then bod
                            else substitute(bod,[(v,pat_tm)])
                in
                aux(substitute(hd, [(v,pat_tm)]),
                    s_bod,
                    tuple? || ~(primitiveArg? pat_tm))
              | None -> ([(hd,bod)], tuple? || recursiveCallsNotPrimitive?(hd,bod)))
         | IfThenElse(Apply(Fun(Equals, _,_),
                            Record([("1", vr as Var(v as (vn,s),_)),
                                    ("2",zro as Fun(Nat 0,_,_))],_),
                            _),
                      then_cl, else_cl, _)
             | natType? s && inVars?(v, freeVars hd) ->
           let (cases1,n_p1) = aux(substitute(hd, [(v,zro)]), substitute(then_cl, [(v,zro)]), tuple?) in
           let (cases2,n_p2) = aux(substitute(hd, [(v,mkApply(mkOp(Qualified("Nat","succ"),
                                                                   mkArrow(natType, natType)),
                                                              vr))]),
                                   simpSubstitute(getSpec c, else_cl,
                                                  [(v,mkApply(mkOp(Qualified("Integer","+"),
                                                                   mkArrow(mkProduct [natType, natType],
                                                                           natType)),
                                                              mkTuple[vr,mkNat 1]))]),
                                   tuple?)
           in
           (cases1 ++ cases2, n_p1 || n_p2)
         | _ -> ([(hd,bod)], tuple? || recursiveCallsNotPrimitive?(hd,bod))
     def aux_case(hd,bod: MSTerm,tuple?) =
       if tuple? then aux(hd,bod,tuple?) else ([(hd,bod)], tuple? || recursiveCallsNotPrimitive?(hd,bod))
     def fix_vars(hd,bod) =
       let fvs = freeVars hd ++ freeVars bod in
       let rename_fvs = filter (fn (nm,_) -> nm in? disallowedVarNames) fvs in
       if rename_fvs = [] then (hd,bod)
         else let sb = map (fn (v as (nm,ty)) -> (v,mkVar(nm^"_v",ty))) rename_fvs in
              let bod_sb = filter (fn (v,tm) -> ~(hasVarNameConflict?(tm, [v]))) sb in
              (substitute(hd,sb), substitute(bod,bod_sb))
   in
   case bod of
     | Lambda ([(RestrictedPat(rpat,_,_),condn,tm)], a) ->
       defToCases c op_tm (Lambda ([(rpat, condn, tm)], a)) infix?
     | _ ->
   let (cases, tuple?) =
         case bod of
           | Lambda ([(recd as (RecordPat (prs as (("1",_)::_),_)), _, tm)],a)
               | varOrTuplePattern? recd ->
             let Some arg = patToTerm(recd,"", c) in
             let (cases,n_p) = aux(Apply(op_tm, arg, a), tm, true) in
             (cases, n_p && ~ infix?)
           | _ -> aux(op_tm, bod, false) in
   %let _ = writeLine(" = "^show (length cases)^", "^show tuple?) in
   (map fix_vars cases, tuple?)

 op addExplicitTyping2(c: Context, lhs: MSTerm, rhs: MSTerm): MSTerm * MSTerm =
   if addExplicitTyping? then
     let fvs = freeVars lhs ++ freeVars rhs in
     %let _ = toScreen("d fvs: "^anyToString (map (fn (x,_) -> x) fvs)^"\n") in
     let vs = filterConstrainedVars(c, lhs, fvs) in
     %let _ = toScreen("d inter vs: "^anyToString (map (fn (x,_) -> x) vs)^"\n") in
     let vs = filterConstrainedVars(c, rhs, vs) in
     %let _ = toScreen("d remaining vs: "^anyToString (map (fn (x,_) -> x) vs)^"\n\n") in
     let (lhs, vs) = addExplicitTypingForVars(lhs, vs) in
     let (rhs, vs) = addExplicitTypingForVars(rhs, vs) in
     (lhs, rhs)
   else (lhs, rhs)

 op addExplicitTyping(t: MSTerm): MSTerm =
   if addExplicitTyping? then
     (addExplicitTypingForVars(t, freeVars t)).1
   else t

 op addExplicitTyping_n1(c: Context, lhs: MSTerms, rhs: MSTerm): MSTerms * MSTerm =
   if addExplicitTyping? then
     let fvs = removeDuplicateVars(foldl (fn (vs,t) -> freeVars t ++ vs)
                                     (freeVars rhs) lhs)
     in
     % let _ = toScreen("fvs: "^anyToString (map (fn (x,_) -> x) fvs)^"\n\n") in
     let vs = foldl (fn (vs,t) -> filterConstrainedVars(c,t,vs)) fvs lhs in
     % let _ = toScreen("inter vs: "^anyToString (map (fn (x,_) -> x) vs)^"\n\n") in
     let vs = filterConstrainedVars(c,rhs,vs) in
     % let _ = toScreen("remaining vs: "^anyToString (map (fn (x,_) -> x) vs)^"\n\n\n") in

     let (lhs,vs) = foldl (fn ((lhs,vs),st) ->
                            let (st,vs) = addExplicitTypingForVars(st,vs) in
                            (lhs ++ [st], vs))
                       ([],vs) lhs
     in
     let (rhs,vs) = addExplicitTypingForVars(rhs,vs) in
     (lhs,rhs)
   else (lhs,rhs)

 %% Ops that are not polymorphic in Specware but are mapped to polymorphic ops in Isabelle
 op isabelleOverloadedOps: List String = ["**", "modF", "divF"]

 op filterConstrainedVars(c: Context, t: MSTerm, vs: MSVars): MSVars =
   let def removeArgs(vs: MSVars, args: MSTerms, bound_vars: MSVars): MSVars =
         % let _ = writeLine("removeArgs: "^anyToString (map (fn (x,_) -> x) bound_vars)) in
         % let _ = app (fn t -> writeLine (printTerm t)) args in
         let v_args = mapPartial (fn t ->
                                    case t of
                                      | Var (v,_) | inVars?(v, vs)
                                                   && ~(hasVarNameConflict?(t, bound_vars)) ->
                                        Some v
                                      | _ -> None)
                         args
         in deleteVars(v_args, vs)
       def filterKnown(vs: MSVars, id: String, f: MSTerm, args: MSTerms, bound_vs: MSVars): MSVars =
         % let _ = writeLine("fk "^id^": "^ anyToString (map (fn (x,_) -> x) vs)) in
         if id = "natural?" || id in? isabelleOverloadedOps 
            || exists? (fn ci -> id in? ci.overloadedOps)
                c.coercions
          then vs
         else
         if (termFixity f = Nonfix && ~ (overloadedIsabelleOp? c f))
            || (length(wildFindUnQualified((getSpec c).ops, id)) = 1
                  %% The following is only necessary for base specs
                  && length(wildFindUnQualified((getBaseSpec()).ops, id)) <= 1)
           then removeArgs(vs,args,bound_vs)
           else vs
%         case wildFindUnQualified((getSpec c).ops, id) of
%              | [opinfo] ->
%                (case unpackFirstOpDef opinfo of
%                   | (tvs, _, _) ->     % Could polymorphic operator sometimes be a problem??
%                     removeArgs(vs,args,bound_vs)
%                   | _ -> vs)
%              | _ -> vs
      def fCV(st, vs: MSVars, bound_vs: MSVars): MSVars =
        % let _ = writeLine("fCV: "^printTerm st^"\n"^anyToString (map (fn (x,_) -> x) vs)) in
        let vs = case st of
                   | Apply(f as Fun(Op(qid as Qualified(q,id),_),_,_),arg,_) % !!!| ~(polymorphic? (getSpec c) qid)
                     ->
                     filterKnown(vs, id, f, termList arg, bound_vs)
                   | Apply(Fun(Embed(id,_),_,_),arg,_) ->
                     if id in? c.overloadedConstructors
                       then vs
                       else removeArgs(vs, termList arg, bound_vs)
                   | Apply(Var(v,_), arg, _) | ~(inVars?(v, vs)) ->
                     removeArgs(vs, termList arg, bound_vs)
                   | _ ->
                 case CurryUtils.getCurryArgs st of
                   | Some(f as Fun(Op(qid as Qualified(q,id),_),_,_),args) % !!!!| ~(polymorphic? (getSpec c) qid)
                     ->
                     filterKnown(vs, id, f, args, bound_vs)
                   | _ -> vs
        in
        % let _ = writeLine("fCV 1: "^anyToString (map (fn (x,_) -> x) vs)) in
        let def fCVBV(vs: MSVars, st: MSTerm): MSVars = fCV(st, vs, bound_vs)
            def fCVsBV(vs: MSVars, tms: MSTerms): MSVars = foldl fCVBV vs tms
        in
        case st of
          | Apply     (M, N, _)     -> fCVBV(fCVBV(vs, M), N)
          | Record    (fields, _)   -> foldl (fn (vs,(_,M)) -> fCVBV(vs, M)) vs fields
          | Bind      (_,vars,M, _) -> fCV(M, vs, insertVars(vars, bound_vs))
          | The       (var,M, _)    -> fCV(M, vs, insertVar(var, bound_vs))
          | Let       (decls, N, _) -> let vs = foldl (fn (vs,(_,M)) -> fCVBV(vs, M)) vs decls in
                                       let bound_vs = foldl (fn (bound_vs,(pat,_)) ->
                                                               insertVars(patVars pat, bound_vs))
                                                          bound_vs decls
                                       in
                                       fCV(N, vs, bound_vs)
          | LetRec    (decls, N, _) -> let vs = foldl (fn (vs,(_,M)) -> fCVBV(vs, M)) vs decls in
                                       let bound_vs = foldl (fn (bound_vs, (var,_)) ->
                                                               insertVar(var, bound_vs))
                                                          bound_vs decls
                                       in
                                       fCV(N, vs, bound_vs)
          | Lambda    (rules,    _) -> foldl (fn (vs,(p, _, M)) ->
                                              fCV(M, vs, insertVars(patVars p, bound_vs)))
                                         vs rules
          | IfThenElse(P, M, N,  _) -> fCVBV(fCVBV(fCVBV(vs, P), M), N)
          | Seq       (Ms,       _) -> fCVsBV(vs, Ms)
          | TypedTerm (M,   _,   _) -> fCVBV(vs, M)
          | Pi        (_,   M,   _) -> fCVBV(vs, M)
          | And       (tms, _)      -> fCVsBV(vs, tms)
          | _ -> vs
   in
   fCV(t, vs, [])

 %% Adds explicit typing for first reference of variable
 op addExplicitTypingForVars(t: MSTerm, vs: MSVars): MSTerm * MSVars =
   let def addExpl(t: MSTerm, vs: MSVars, bound_vs: MSVars): MSTerm * MSVars =
         case t of
           | Var(v1 as (_,ty),pos) | inVars?(v1, vs) && ~(hasVarNameConflict?(t, bound_vs)) ->
             (TypedTerm(t,ty,pos), filter (fn v2 -> ~ (equalVar?(v1, v2))) vs)
           | Apply(t1,t2,a) ->
             let (t1,vs) = addExpl(t1,vs,bound_vs) in
             let (t2,vs) = addExpl(t2,vs,bound_vs) in
             (Apply(t1,t2,a),vs)
           | Record(prs,a) ->
             let (prs,vs) = foldl (fn ((prs,vs),(id,st)) ->
                                  let (st,vs) = addExpl(st,vs,bound_vs) in
                                  (Cons((id,st),prs), vs))
                             ([],vs) prs
             in
             (Record(reverse prs,a),vs)
           | Bind(bdr,lvs,st,a) ->
             let (st,vs) = addExpl(st,vs,insertVars(lvs, bound_vs)) in
             (Bind(bdr,lvs,st,a),vs)
           | The(v,st,a) ->
             let (st,vs) = addExpl(st,vs,insertVar(v, bound_vs)) in
             (The(v,st,a),vs)
           | Let(bds,st,a) ->                % Should really look in bds
             let bound_vs = foldl (fn (bound_vs,(pat,_)) ->
                                     insertVars(patVars pat, bound_vs))
                              bound_vs bds
             in
             let (st,vs) = addExpl(st,vs,bound_vs) in
             (Let(bds,st,a),vs)
           | LetRec(bds,st,a) ->
             let bound_vs = foldl (fn (bound_vs, (var,_)) ->
                                     insertVar(var, bound_vs))
                              bound_vs bds
             in
             let (st,vs) = addExpl(st,vs,bound_vs) in
             (LetRec(bds,st,a),vs)
           | IfThenElse(t1,t2,t3,a) ->
             let (t1,vs) = addExpl(t1,vs,bound_vs) in
             let (t2,vs) = addExpl(t2,vs,bound_vs) in
             let (t3,vs) = addExpl(t3,vs,bound_vs) in
             (IfThenElse(t1,t2,t3,a),vs)
           | Lambda(cases,a) ->
             let (cases,vs) = foldl (fn ((result,vs),(p,c,t)) ->
                                       let (t,vs) = addExpl(t,vs,insertVars(patVars p, bound_vs)) in
                                       (result ++ [(p,c,t)], vs))
                                ([],vs) cases
             in
             (Lambda(cases,a), vs)
            %% Probably should put other cases
           | _ -> (t,vs)
    in
    addExpl(t, vs, [])

 %op addExplicitTypingForNumbers(tm: MSTerm): MSTerm =


 op  ppProperty : Context -> Property -> String -> SpecElements -> Option Pragma -> Pretty
 def ppProperty c (propType, name, tyVars, term, _) comm elems opt_prag =
   % let _ = writeLine ((MetaSlang.printQualifiedId name) ^ ": " ^ comm ^ "\n"^ printTerm term) in
   %% Axioms are mapped to theorems in theory morphisms
   let opt_prag = findPragmaNamed(elems, name, opt_prag) in
   let propType = if propType = Axiom && c.source_of_thy_morphism?
                    then Theorem
                    else propType
   in
   let annotation =
       case findBracketAnnotation(opt_prag) of
         | Some str -> prConcat [prSpace, prString (specwareToIsaString str)]
         | _ ->
           let comm = stripOuterSpaces comm in
           let len = length comm in
           if len > 13 && subFromTo(comm,0,14) = "Simplification"
             then prString " [simp]"
             else prEmpty
   in
   let (prf_pp,includes_prf_terminator?) = processOptPrag opt_prag in
   prLinesCat 2
     ([[ppPropertyType propType,
        prSpace,
        ppQualifiedId name,
        annotation,
        prString ": "],
        %ppTyVars tyVars,
        [prString "\"",
         ppPropertyTerm c (explicitUniversals opt_prag) term,
         prString "\""]]
       ++ prf_pp
       ++ (case propType of
             | Axiom -> []
             | _ -> (if prf_pp = []
                       then [[prString c.defaultProof]]
                           ++ (if prfEndsWithTerminator? c.defaultProof then []
                                 else [[prString "done",prEmpty]])
                       else (if includes_prf_terminator?
                               then []
                               else [[prString "done",prEmpty]]))))

 op backwardsSExpr(s: String, pos: Nat): Option Nat =
   if pos >= length s then None
   else
   let def skip_back(i, paren_depth, non_ws?) =
         if i < 0 then None
         else
         let chr = s@i in
         if chr = #) then skip_back(i-1, paren_depth+1, true)
          else if chr = #(
            then if paren_depth = 1 then Some i
                   else skip_back(i-1, paren_depth-1, true)
          else if paren_depth = 0 && whiteSpaceChar? chr
            then if non_ws? then Some(i+1)
                  else skip_back(i-1, paren_depth, false)
          else skip_back(i-1, paren_depth, true)
   in
   skip_back(pos, 0, false)

 op lastLineEnds(prf: String): Bool =
   let len_prf = length prf in
   case backwardsSExpr(prf, len_prf-1) of
     | None -> false
     | Some end_char ->
   let beg_last_line = case findLastBefore("\n", prf, end_char) of
                         | Some i -> i+1
                         | None -> 0
   in
  % let real_beg_last_line = skipWhiteSpace(prf, beg_last_line) in
   %% Should be more sophisticated
   case searchBetween("by", prf, beg_last_line, end_char) of
     | None -> false
     | Some n -> (n = 0 || whiteSpaceChar?(prf@(n-1)))
                && length prf > n+3
                && (whiteSpaceChar?(prf@(n+2))
                      || prf@(n+2) = #()

 op prfEndsWithTerminator?(prf: String): Bool =
   let len = length prf in
   endsIn?(prf,"done")
  || endsIn?(prf,"sorry")
  || endsIn?(prf,"oops")
  || endsIn?(prf,"qed")
  || lastLineEnds prf

 op  stripExcessWhiteSpace: String -> String
 def stripExcessWhiteSpace s =
   let len = length s in
   if len > 0 && s@(len-1) in? [#\s,#\n]
     then stripExcessWhiteSpace(subFromTo(s,0,len-1))
     else if len > 2 && s@0 = #\s && s@1 = #\s
           then subFromTo(s,2,len)
           else s

 op  explicitUniversals: Option Pragma -> List String
 def explicitUniversals prf =
   case prf of
     | None -> []
     | Some (_,prag_str,_,_) ->
   let end_pos = case search("\n",prag_str) of
                   | Some n -> n
                   | None -> length prag_str
   in
   let end_fa_pos = case search(" fa ",prag_str) of
                      | Some n -> n+4
                      | None ->
                    case search(" \\<forall>",prag_str) of
                      | Some n -> n+9
                      | None -> 
                    case search(" \\_forall",prag_str) of
                      | Some n -> n+9
                      | None -> length prag_str
   in
   let end_vars_pos = case search(".",prag_str) of
                      | Some n -> n
                      | None -> 0
   in
   if end_fa_pos >= end_pos || end_vars_pos <= end_fa_pos then []
     else removeEmpty(splitStringAt(subFromTo(prag_str,end_fa_pos,end_vars_pos)," "))

 op endOfFirstLine(s: String): Nat =
   case search("\n",s) of
     | Some n -> n
     | None -> length s

 op  findBracketAnnotation: Option Pragma -> Option String
 def findBracketAnnotation prf =
   case prf of
     | None -> None
     | Some (_,prag_str,_,_) ->
   let end_pos =  endOfFirstLine prag_str in
   findStringBetween(prag_str, "[", "]", 0, endOfFirstLine prag_str)

 op findParenAnnotation(prf: Option Pragma): Option String =
   case prf of
     | None -> None
     | Some (_,prag_str,_,_) ->
   let end_pos =  endOfFirstLine prag_str in
   if some?(searchBetween("\"", prag_str, 0, end_pos))
     then None
   else findStringBetween(prag_str, "(", ")", 0, end_pos)


 op  findMeasureAnnotation: Option Pragma -> Option String
 def findMeasureAnnotation prf =
   case prf of
     | None -> None
     | Some (_,prag_str,_,_) ->
   let end_pos = endOfFirstLine prag_str in
   case findStringBetween(prag_str, "\"", "\"", 0, end_pos) of
     | Some str -> Some(replaceString(str, "\fn", "\\<lambda>"))
     | None -> None


 op  ppPropertyType : PropertyType -> Pretty
 def ppPropertyType propType =
   case propType of
     | Axiom -> prString "axiomatization where"
     | Theorem -> prString "theorem"
     | Conjecture -> prString "theorem"
     | any -> fail ("No match in ppPropertyType with: '"
                      ^ (anyToString any)
                      ^ "'")

 %% --------------------------------------------------------------------------------
 %% Terms
 %% --------------------------------------------------------------------------------

 op infixFun? (c: Context) (f: MSFun): Option String =
   % let _ = writeLine("infixFun? of "^anyToString f) in
   let result =
         case f of
           | Op(qid,fx?) ->
             (let spc = getSpec c in
               case specialOpInfo c qid of
                | Some(isa_id, infix?, _, _, _) ->
                  (case infix? of
                     | Some fx -> Some isa_id
                     | None -> None)
                | _ ->
               if embed? Infix fx?
                 then Some(mainId qid)
               else
               case findTheOp(spc,qid) of
                 | Some{names=_,fixity = Infix fx, dfn=_,fullyQualified?=_} ->
                   Some(mainId qid)
                 | _ -> None)
           | And       -> Some "\\<and>"
           | Or        -> Some "\\<or>"
           | Implies   -> Some "\\<longrightarrow>"
           | Iff       -> Some "="
           | Equals    -> Some "="
           | NotEquals -> Some "\\<noteq>"
           | _ -> None
   in
   % let _ = writeLine("is "^anyToString result) in
   result

 op infixOp? (c: Context) (t: MSTerm): Option String =
   case t of
     | Fun(f,_,_) -> infixFun? c f
     | _ -> None

 op nonCaseMatch?(match: MSMatch): Bool =
   case match of
     | (NatPat _,_,_)::_ -> true
     | (CharPat _,_,_)::_ -> true
     | _ -> false

 op charMatch?(match: MSMatch): Bool =
   case match of
     | (CharPat _,_,_)::_ -> true
     | _ -> false


 %% Should also handle tuples?
 op caseToIf(c: Context, match: MSMatch, c_tm: MSTerm): MSTerm =
   let arg_ty = inferType(getSpec c, c_tm) in
   let arg = if simpleTerm c_tm then c_tm else mkVar("case__v", arg_ty) in
   let (_,_,result1)::_ = match in
   let result_ty = inferType(getSpec c, result1) in

   let def aux match =
         case match of
           | [] -> mkArbitrary result_ty
           | (WildPat _,_,tm)::_ -> tm
           | (p,_,tm)::r_match ->
             let Some pat_tm = patToTerm(p,"",c) in
             MS.mkIfThenElse(mkEquality(arg_ty,arg,pat_tm), tm, aux r_match)
   in
   let if_tm = aux match in
   if arg = c_tm then if_tm
     else MS.mkLet([(mkVarPat("case__v", arg_ty), c_tm)], if_tm)

 op mkCoproductPat(ty: MSType, id: String, spc: Spec): MSPattern =
   let Some(_,opt_ty) = findLeftmost (fn (id1,_) -> id = id1) (coproduct(spc, ty)) in
   mkEmbedPat(id,mapOption mkWildPat opt_ty,ty)

 op  ppTerm : Context -> ParentTerm -> MSTerm -> Pretty
 def ppTerm c parentTerm term =
   %let _ = writeLine(printTerm term^": "^anyToString parentTerm) in
   case (isFiniteList term) of
     | Some terms ->
       prConcat [prString "[",
                 prPostSep 0 blockFill (prString ", ") (map (ppTerm c Top) terms),
                 prString "]"]
     | None ->
   let def prApply(term1, term2) =
      case (term1, term2) of
        | (Apply(Fun(Op(qid, _), _, _), t1, _), _) | reversedNonfixOp? c qid ->
          %% Reversed curried op, not infix
          let Some(isa_id,_,_,reversed,_) = specialOpInfo c qid in
          enclose?(parentTerm ~= Top,
                   prBreak 2 [prSymString isa_id,
                              prSpace,
                              ppTermEncloseComplex? c Nonfix term2,
                              prSpace,
                              ppTermEncloseComplex? c Nonfix t1])
        | (Fun(Embed(constr_id,_), ty, _), Record (("1",_)::_,_)) ->
          let spc = getSpec c in
          let constr_ty = range(spc,ty) in
          if multiArgConstructor?(constr_id,constr_ty,spc) then
          %% Treat as curried
             prBreak 2 [ppConstructorTyped(c, constr_id, constr_ty, spc),
                        prSpace,
                        prPostSep 2 blockFill prSpace
                          (map (ppTermEncloseComplex? c Nonfix)
                             (MS.termToList term2))]
          else prConcat [ppConstructorTyped(c, constr_id, constr_ty, spc),
                         prSpace,
                         ppTerm c Nonfix term2]
        | (Lambda (match, _),_) ->
          if nonCaseMatch? match
            then ppTerm c parentTerm (caseToIf(c, match, term2))
            else enclose?(parentTerm ~= Top,
                          prBreakCat 0 [[prString "case ",
                                         ppTerm c Top term2],
                                        [prString " of ",
                                         ppMatch c match]])
        | (Fun (Project p, ty1, _), _) ->
          let pid = projectorFun(c,p,ty1,getSpec c) in
          prConcat [prString pid,
                    prConcat [prSpace, ppTermEncloseComplex? c Nonfix term2]]
%         | (Fun (Op (Qualified("Nat","natural?"),_), _,a),_) ->  % natural? e \_longrightarrow 0 <= e
%           let term2 = case term2 of
%                         | Apply(Fun(Op(Qualified(q,"int"),_),_,_),x,_) | q = toIsaQual ->
%                           %% In this case it is known true, but leave it in for now for transparency
%                           x
%                         | _ -> term2
%           in
%           ppTerm c parentTerm (mkAppl(Fun(Op (Qualified("Integer","<="),Infix(Left,20)),Any a,a),
%                                       [mkNat 0, term2]))
        %% Set Collect(fn x -> p x) --> {x. p x}
        | (Fun(Op(Qualified("Set","collect"), _), _, _), Lambda([(pattern, _, bod)], _)) ->
          prBreakCat 2 [[prString "{",
                         let c = c << {printTypes? = true} in
                         ppPattern c pattern (Some "") false,
                         prString ". "],
                        [ppTerm c Top bod],
                        [prString "}"]]
        | (Fun(Op(qid,Infix _),f_ty,a), term2) ->
          let spc = getSpec c in
          ppTerm c parentTerm
            (case productTypes(spc, inferType (spc, term2)) of
               | [t1,t2] ->
                 MS.mkLet([(MS.mkTuplePat[MS.mkVarPat("x",t1), MS.mkVarPat("y",t2)], term2)],
                          mkAppl(term1, [mkVar("x",t1), mkVar("y",t2)]))
               | _ -> (warn("Can't get argument types of infix operator: "^ printTerm term);
                       mkApply(Fun(Op(qid,Nonfix),f_ty,a), term2)))
        %%  embed? foo x  -->  case x of foo _ -> true | _ -> false
        | (Fun(Embedded id,ty,a), term2) ->
          let spc = getSpec c in
          let term2_ty = inferType(spc, term2) in
          let lam_tm = Lambda([(mkCoproductPat(term2_ty,id,spc),trueTerm,trueTerm),
                               (mkWildPat term2_ty,trueTerm,falseTerm)], a)
          in
          prApply(lam_tm, term2)
        | _ ->
          (case infixOp? c term1 of    % Infix ops are translated uniformly to curried ops
             | Some infix_str ->
               enclose?(parentTerm ~= Top,
                        prLinearCat 0 [[prString "let (x,y) = ",
                                        ppTerm c Top term2,
                                        prSpace],
                                       [prString "in x ",
                                        prSymString infix_str,
                                        prString " y"]])
%                let spc = getSpec c in
%                ppTerm c parentTerm
%                  (case productTypes(spc, inferType (spc, term2)) of
%                     | [t1,t2] ->
%                       MS.mkLet([(MS.mkTuplePat[MS.mkVarPat("x",t1), MS.mkVarPat("y",t2)], term2)],
%                                mkAppl(term1, [mkVar("x",t1), mkVar("y",t2)]))
%                     | _ -> fail("Can't get argument types of infix operator: "^ printTerm term))
             | _ ->
           (case termFixity c term1 of
              | (Some pp_id,_,true,reversed) ->  % op translated to curried
                let terms2 = MS.termToList term2 in
                let terms2 = if reversed then reverse terms2 else terms2 in
                if length terms2 = 1
                  then
                    (let spc = getSpec c in
                     case productOpt(spc, inferType(spc, term2)) of
                       | Some fields ->
                         let (rec_pat, rec_tm) = patTermVarsForProduct fields in
                         ppTerm c parentTerm (MS.mkLet([(rec_pat, term2)], mkApply(term1, rec_tm)))
                       | None ->
                     case arrowOpt(spc, inferType(spc, term)) of
                       | Some(dom, _) ->
                         let new_v = ("cv", dom) in
                         ppTerm c parentTerm (mkLambda (mkVarPat new_v, mkApply(term, mkVar new_v)))
                       | None -> fail("Can't reverse term: "^printTerm term))
                else
                prBreak 2 [pp_id,
                           prSpace,
                           prPostSep 2 blockFill prSpace
                             (map (ppTermEncloseComplex? c Nonfix) terms2)]
              | (Some pp_id,_,false,true) ->
                (let spc = getSpec c in
                 case arrowOpt(spc, inferType(spc, term)) of
                   | Some(dom, _) ->
                     let new_v = ("cv", dom) in
                     ppTerm c parentTerm (mkLambda (mkVarPat new_v, mkApply(term, mkVar new_v)))
                   | None -> fail("Can't reverse term: "^printTerm term))
          | _ ->                 
            prBreak 2 [ppTerm c (Infix(Left,1000)) term1,
                       case term2 of
                         | Record _ -> ppTerm c Top term2
                         | _ -> prConcat [prSpace, ppTermEncloseComplex? c Nonfix term2]]))

   in
   case term of
     | Apply(Fun(Op(Qualified("Function", "id"),_), Arrow(dom, ran, _),_), x, _) | ~(equalType?(dom, ran)) ->
       %% Remnants of adding exploitOverloading
       ppTerm c parentTerm x       
     | Apply (trm1, trm2 as (Record ([("1", t1), ("2", t2)], a)), _) ->
       (case (trm1, t2) of
        | (Fun(RecordMerge, ty, _), Record (fields,_)) ->
          let spc = getSpec c in
          let recd_ty = range(spc, ty) in
          let recd_ty = normalizeType (spc, c.typeNameInfo, false, true, true) recd_ty in
          let recd_ty = unfoldToBaseNamedType(spc, recd_ty) in
          enclose?(parentTerm ~= Top,
                   prBreak 2 [ppTerm c (Infix(Left,1000)) t1,
                              let def ppField (x,y) =
                                     prConcat [prString (case recd_ty of
                                                           | Base(qid, _, _) -> mkNamedRecordFieldName c (qid,x)
                                                           | _ -> mkFieldName x),
                                               prString " := ",
                                               ppTerm c Top y]
                              in
                              prConcat [lengthString(1, "\\<lparr>"),
                                        prPostSep 0 blockLinear (prString ", ") (map ppField fields),
                                        lengthString(1, "\\<rparr>")]])
        | _ ->
        let def prInfix (f1, f2, encl?, same?, t1, oper, t2) =
              enclose?(encl?,
                       prLinearCat (if same? then -2 else 2)    % -2 is mainly for conjunction
                         [[ppTerm c f1 t1, prSpace],
                          [oper, prSpace, ppTerm c f2 t2]])
        in
        let fx = termFixity c trm1 in
        % let _ = writeLine("parentTerm: "^anyToString parentTerm) in
        % let _ = writeLine(printTerm trm1 ^ " " ^printTerm trm2 ^ "\n" ^ anyToString fx) in
        let (t1,t2) = if fx.4 then (t2,t1) else (t1,t2) in   % Reverse args
        (case (parentTerm, fx) of
           | (_, (None, Nonfix, false, _)) ->
             prApply (trm1, mkTuple[t1,t2])
           | (_, (Some pr_op, Nonfix, curried?, _)) ->
             if ~curried?
               then enclose?(parentTerm ~= Top,
                             prConcat[pr_op,
                                      enclose?(true, prLinearCat 0 [[ppTerm c Top t1, prString ", "],
                                                                    [ppTerm c Top t2]])])
             else
             enclose?(parentTerm ~= Top,
                      prLinearCat 2 [[pr_op,prSpace],
                                     [ppTermEncloseComplex? c Nonfix t1, prSpace,
                                      ppTermEncloseComplex? c Nonfix t2]])
           | (Nonfix, (Some pr_op, Infix (a, p), _, _)) ->
             prInfix (Infix (Left, p), Infix (Right, p), true, false, t1, pr_op, t2)
           | (Top,    (Some pr_op, Infix (a, p), _, _)) ->
             prInfix (Infix (Left, p), Infix (Right, p), false, false, t1, pr_op, t2) 
           | (Infix (a1, p1), (Some pr_op, Infix (a2, p2), _, _)) ->
             if p1 = p2
               then prInfix (Infix (Left, p2), Infix (Right, p2),
                             p1 ~= 35, % not And % true,  % be conservative a1 ~= a2
                             a1 = Right && a2 = Right, t1, pr_op, t2)
               else prInfix (Infix (Left, p2), Infix (Right, p2), p1 > p2, false, t1, pr_op, t2)))
     | Apply(term1 as Fun (Not, _, _),term2,_) ->
       enclose?(case parentTerm of
                  | Infix(_,prec) -> prec > 40
                  | _ -> false,
                prApply (term1,term2))
     | Apply (term1,term2,_) -> prApply (term1,term2)
     | ApplyN ([t1, t2], _) -> prApply (t1, t2)
     | ApplyN (t1 :: t2 :: ts, a) -> prApply (ApplyN ([t1, t2], a), ApplyN (ts, a))
     | Record (fields,_) ->
       (case fields of
          | [] -> prString "()"
          | ("1",_) :: _ ->
            let def ppField (_,y) = ppTerm c Top y in
            prConcat [prString "(",
                      prPostSep 0 blockFill (prString ", ") (map ppField fields),
                      prString ")"]
          | _ ->
            let spc = getSpec c in
            let recd_ty = inferType(spc, term) in
            let recd_ty = normalizeType (spc, c.typeNameInfo, false, true, true) recd_ty in
            let recd_ty = unfoldToBaseNamedType(spc, recd_ty) in
            let def ppField (x,y) =
                  prConcat [prString (case recd_ty of
                                      | Base(qid, _, _) -> mkNamedRecordFieldName c (qid,x)
                                      | _ -> mkFieldName x),
                            prString " = ",
                            ppTerm c Top y]
            in
              prConcat [lengthString(1, "\\<lparr>"),
                        prPostSep 0 blockLinear (prString ", ") (map ppField fields),
                        lengthString(1, "\\<rparr>")])
     | The (var,term,_) ->
       prBreak 0 [prString "(THE ",
                  ppVarWithType c false var,
                  prString ". ",
                  ppTerm c Top term,
                  prString ")"]
     | Bind (binder,vars,term,_) ->
       enclose?(case parentTerm of
                  | Infix(_,prec) -> true  % prec > 18
                  | _ -> false,
                prBreakCat 2 [[ppBinder binder,
                               prBreak 2 (addSeparator prSpace (map (ppVarWithType c (length vars > 1)) vars)),
                               prString ". "],
                              [ppTerm c Top term]])
     | Let ([(p,t)], bod, a) | existsPattern? (embed? EmbedPat) p ->
       prApply(Lambda([(p, trueTerm ,bod)], a), t)
     | Let (decls,term,_) ->
       let def ppDecl (pattern,term) =
             prBreakCat 2 [[ppPattern c pattern (Some "") false,
                            prSpace],
                           [prString "= ",
                            ppTerm c Top term]]
       in
       enclose?(infix? parentTerm,
                prLinear 0 [prLinear 0
                              [prConcat[prString "let ",
                                        prLinear 0 (addSeparator (prString "; ")
                                                      (map ppDecl decls)),
                                        prSpace],
                               prString "in "],
                            %% For some reason Isabelle always wants a lambda in a let to be parenthesized
                            %% in all cases. This is conservative, but not too bad.
                            ppTerm c (if parentTerm = Top then Nonfix else parentTerm) term])
     | LetRec (decls,term,_) ->
       let def ppDecl (v,term) =
             prBreak 0 [%prString "def ",
                        ppVarWithoutType v,
                        prString " = ",
                        ppTerm c Top term]
       in
       enclose?(infix? parentTerm,
                prLinear 0 [prLinear 0
                              [prString "let",
                               prConcat[prLinear 0 (map ppDecl decls), prSpace],
                               prString "in "],
                            ppTerm c (if infix? parentTerm then Top else parentTerm) term])
     | Var (v,_) -> ppVarWithoutType v
     | Fun (fun,ty,_) -> ppFun c parentTerm fun ty
%      | Lambda ([(_, Fun (Bool true,  _, _), Fun (Bool true,  _, _))], _) ->
%        prString "TRUE"                 % fnx. True
     | Lambda ([(pattern,_,term)],_) ->
       enclose?(parentTerm ~= Top,
                prBreakCat 2 [[lengthString(2, "\\<lambda> "),
                               let c = c << {printTypes? = true} in
                                 ppPattern c pattern (Some "") true,
                               prString ". "],
                              [ppTerm c Top term]])
     | Lambda (match,_) ->
       let spc = getSpec c in
       let lam_ty = inferType(spc, term) in
       let eta_var = ("xx", domain(spc, lam_ty)) in
       let eta_tm = mkLambda(mkVarPat eta_var, mkApply(term, mkVar eta_var)) in
       ppTerm c parentTerm eta_tm
     | IfThenElse (pred,term1,term2,_) -> 
       enclose?(infix? parentTerm,
                blockLinear (0,[(0,prConcat [prString "if ",
                                             ppTerm c Top pred,
                                             prString " then "]),
                                (2,ppTerm c Top term1),
                                (-1,prString " else "),
                                (2,ppTerm c Top term2)]))
     | Seq (terms,_) ->
       %prPostSep 0 blockLinear (prString "; ") (map (ppTerm c Top) terms)
       ppTerm c parentTerm (last terms)
     | TypedTerm (tm, ty, _) ->
       enclose?(true, prBreakCat 0 [[ppTerm c parentTerm tm, prString "::"], [ppType c Top true ty]])
     | mystery -> fail ("No match in ppTerm with: '" ^ (anyToString mystery) ^ "'")

 op ppTermStr (c: Context) (parentTerm: ParentTerm) (term: MSTerm): String =
   toString(format(110, ppTerm c parentTerm term))

 % ppTermStrIndent
 %  c: Isabelle Translation Context
 %  parentTerm: Information about the parent, used soley for parentheization
 %  term: the term to print
 %  indent: minimal starting column if term does not print on one line.
 op ppTermStrIndent(c: Context) (parentTerm: ParentTerm) (term: MSTerm) (indent: Int): String =
   let indentPP = PrettyPrint.blanks indent in
   let termPP   = ppTerm c parentTerm term in
   let termPP   = PrettyPrint.prettysNone [PrettyPrint.string indentPP, termPP] in
   let str      = PrettyPrint.toString(format(120,termPP)) in
   subFromTo(str, indent, length str)

 op unfoldToBaseNamedType(spc: Spec, ty: MSType): MSType =
   % let _ = writeLine("ufnp: "^printType ty) in
   case ty of
     | Base _ ->
       (case tryUnfoldBase spc ty of
        | Some (uf_ty as Base _) -> unfoldToBaseNamedType(spc, uf_ty)
        | Some (Subtype(sup_ty, _, _)) -> unfoldToBaseNamedType(spc, sup_ty)
        | _ -> ty)
     | _ -> ty

 op  projectorFun: Context * String * MSType * Spec -> String
 def projectorFun (c, p, s, spc) =
   let (prod_ty, arity) = case typeArity(spc, s) of
                            | None -> (s,1)
                            | Some pr -> pr
   in
   case p of
     | "1" -> "fst"
     | "2" -> (if arity = 2 then "snd" else "second")
     | "3" -> (if arity = 3 then "thirdl" else "third")
     | "4" -> (if arity = 4 then "fourthl" else "fourth")
     | "5" -> (if arity = 5 then "fifthl" else "fifth")
     | "6" -> (if arity = 6 then "sixthl" else "sixth")
     | "7" -> (if arity = 7 then "seventhl" else "seventh")
     | "8" -> (if arity = 8 then "eighthl" else "eighth")
     | "9" -> (if arity = 9 then "ninethl" else "nineth")
     | _ ->
   case unfoldToBaseNamedType(spc, prod_ty) of
     | Base(qid, _, _) -> mkNamedRecordFieldName c (qid,p)
     | _ -> mkFieldName p

 op  ppBinder : Binder -> Pretty
 def ppBinder binder =
   case binder of
     | Forall -> lengthString(1, "\\<forall>")
     | Exists -> lengthString(1, "\\<exists>")
     | Exists1 -> lengthString(2, "\\<exists>!")

 op ppVarStr(nm: String): Pretty =
   if nm in? disallowedVarNames then prString(nm^"__v")
     else prString (ppIdStr nm)

 op  ppVarWithoutType : MSVar -> Pretty
 def ppVarWithoutType (id, _(* ty *)) =
   ppVarStr id

 op ppVarWithType (c: Context) (parens?: Bool) ((id, ty): MSVar): Pretty =
   if printQuantifiersWithType? then
     enclose?(parens?, prConcat [ppVarStr id, prString "::", ppType c Top true ty])
   else ppVarStr id

 op  ppVar : Context -> MSVar -> Pretty
 def ppVar c (id, ty) =
   prConcat [ppVarStr id,
             prString ":",
             ppType c Top true ty]

 %%% Top-level theorems use implicit quantification meta-level -> and lhs &&
 op  ppPropertyTerm : Context -> List String -> MSTerm -> Pretty
 def ppPropertyTerm c explicit_universals term =
   let (assmpts, concl) = parsePropertyTerm c explicit_universals term in
   let (assmpts, concl) = addExplicitTyping_n1(c, assmpts, concl) in
   if assmpts = [] then ppTerm c Top concl
     else prLinear 0 [prConcat [lengthString(1, "\\<lbrakk>"),
                                prPostSep 0 blockLinear (prString "; ")
                                  (map (ppTerm c Top) assmpts),
                                lengthString(2, "\\<rbrakk>"),
                               lengthString(5, " \\<Longrightarrow> ")],
                      ppTerm c Top concl]

 op  parsePropertyTerm: Context -> List String -> MSTerm -> MSTerms * MSTerm
 def parsePropertyTerm c explicit_universals term =
   case term of
     | Bind (Forall, vars, bod, a) ->
       let expl_vars = filter (fn (vn,_) -> vn in? explicit_universals) vars in
       let renameImplicits = filter (fn (vn,_) -> vn nin? explicit_universals
                                                 && vn in? disallowedVarNames)
                               vars
       in
       let bod = if renameImplicits = [] then bod
                  else substitute(bod, map (fn (v as (s, ty)) -> (v, mkVar(s^"__v", ty)))
                                        renameImplicits)
       in
       if expl_vars = []
         then parsePropertyTerm c explicit_universals bod
         else ([], Bind (Forall, expl_vars, bod, a))
     | Apply(Fun(Implies, _, _),
             Record([("1", lhs), ("2", rhs)], _),_) ->
       let lhj_cjs = getConjuncts lhs in
       let (rec_cjs, bod) = parsePropertyTerm c explicit_universals rhs in
       (lhj_cjs ++ rec_cjs, bod)
     | _ -> ([], term)

 op  ppMatch : Context -> MSMatch -> Pretty
 def ppMatch c cases =
   let def ppCase (pattern, _, term) =
         prBreakCat 0 [[ppPattern c pattern None true,
                        lengthString(3, " \\<Rightarrow> ")],
                       [ppTerm c Top term]]
   in
     (prSep (-3) blockAll (prString " | ") (map ppCase cases))

 op ppPattern (c: Context) (pattern: MSPattern) (wildstr: Option String) (parens?: Bool): Pretty = 
   case pattern of
     | AliasPat (pat1, pat2, _) -> 
       prBreak 0 [ppPattern c pat1 wildstr true,
                  prString " as ",
                  ppPattern c pat2 wildstr true]
     | VarPat (v, _) -> if c.printTypes? && ~(embed? Any v.2) then ppVarWithType c parens? v
                        else ppVarWithoutType v
     | EmbedPat (constr, pat, ty, _) ->
       prBreak 0 [ppConstructorTyped(c, constr, ty, getSpec c),
                  case pat of
                    | None -> prEmpty
                    | Some pat ->
                  case pat of
                    %% Print constructors with tuple args curried, unless polymorphic
                    | RecordPat(("1",_)::_,_) | multiArgConstructor?(constr, ty, getSpec c) ->
                      prBreak 2 [prSpace,
                                 prPostSep 2 blockFill prSpace
                                   (map (fn p -> enclose?(case p of
                                                            | EmbedPat(_, Some _, _, _)-> true
                                                            | AliasPat _ -> true
                                                            | _ -> false,
                                                          ppPattern c p wildstr true))
                                    (patternToList pat))]
                    | WildPat (pty,_) | multiArgConstructor?(constr, ty, getSpec c) ->
                      let tys = productTypes(getSpec c, pty) in
                      prConcat [prSpace,
                                prPostSep 0 blockFill prSpace
                                  (map (fn ty -> ppPattern c (mkWildPat ty) wildstr true) tys)]
                    | _ -> prConcat [prSpace, enclose?(embed? EmbedPat pat,
                                                       ppPattern c pat wildstr true)]]
     | RecordPat (fields,_) ->
       (case fields of
         | [] -> prString "()"
         | ("1",_)::_ ->
           let def ppField (idstr,pat) = ppPattern c pat (extendWild wildstr idstr) false in
           prConcat [prString "(",
                     prPostSep 0 blockFill (prString ", ") (map ppField fields),
                     prString ")"]
         | _ ->
           let def ppField (x,pat) =
                 prConcat [prString (mkFieldName x),
                           prString "=",
                           ppPattern c pat (extendWild wildstr x) true]
           in
           prConcat [prString "{",
                     prPostSep 0 blockLinear (prString ", ") (map ppField fields),
                     prString "}"])
     | WildPat (ty,_) ->
       (case wildstr of
          | Some str -> prString("ignore"^str)
          | None -> prString "_")
     | StringPat (str,_) -> prString ("''" ^ str ^ "''")
     | BoolPat (b,_) -> ppBool b
     | CharPat (chr,_) -> prString (Char.show chr)
     | NatPat (int,_) -> prString (Nat.show int)      
     | QuotientPat (pat,qid,_,_) -> 
       prBreak 0 [prString ("(quotient[" ^ show qid ^ "] "),
                  ppPattern c pat wildstr false,
                  prString ")"]
     | RestrictedPat (pat,term,_) -> 
%        (case pat of
%	   | RecordPat (fields,_) ->
%	     (case fields of
%	       | [] -> prBreak 0 [prString "() | ",ppTerm c term]
%	       | ("1",_)::_ ->
%		   let def ppField (_,pat) = ppPattern c pat wildstr in
%		   prConcat [
%		     prString "(",
%		     prSep (prString ",") (map ppField fields),
%		     prString " | ",
%		     ppTerm c term,
%		     prString ")"
%		   ]
%	       | _ ->
%		   let def ppField (x,pat) =
%		     prConcat [
%		       prString x,
%		       prString "=",
%		       ppPattern c pat
%		     ] in
%		   prConcat [
%		     prString "{",
%		     prSep (prString ",") (map ppField fields),
%		     prString " | ",
%		     ppTerm c term,
%		     prString "}"
%		   ])
%	       | _ ->
           prBreak 0 [ppPattern c pat wildstr parens?
%% Ignore restricted patterns for now (certainly for lambdas)
%                       prString " | ",
%                       ppTerm c Top term
                      ] %)
     | TypedPat (pat,ty,_) -> ppPattern c pat wildstr parens?
     | mystery -> fail ("No match in ppPattern with: '" ^ (anyToString mystery) ^ "'")

 op  multiArgConstructor?: Id * MSType * Spec -> Bool
 def multiArgConstructor?(constrId,ty,spc) =
   case ty of
     | Base(qid,_,_) ->
       (let (_, base_ty) = typeDef(qid,spc) in
        case coproductOpt(spc,base_ty) of
          | None -> false
          | Some fields ->
            exists? (fn (id,opt_arg_ty) ->
                       case opt_arg_ty of
                         | Some(Product(("1",_)::_, _)) -> id = constrId
                         | _ -> false)
              fields)
     | _ -> false

 op  extendWild (wildstr: Option String) (str: String): Option String =
    case wildstr of
      | Some s -> Some (s^str)
      | None -> None

 op typeDef(qid: QualifiedId, spc: Spec): TyVars * MSType =
   let Some info = AnnSpec.findTheType(spc,qid) in
   unpackFirstTypeDef info

 op  ppBool : Bool -> Pretty
 def ppBool b =
   case b of
     | true -> prString "True"
     | false -> prString "False"

 op etaRuleProduct(tm: MSTerm, fields: List(Id * MSType)): MSTerm =
   let (pat,arg) = patTermVarsForProduct fields in
   mkLambda(pat, mkApply(tm, arg))

 op  ppFun : Context -> ParentTerm -> MSFun -> MSType -> Pretty
 def ppFun c parentTerm fun ty =
   case fun of
     | Not       -> lengthString(1, "\\<not>")
     | And       -> lengthString(1, "\\<and>")
     | Or        -> lengthString(1, "\\<or>")
     | Implies   -> lengthString(3, "\\<longrightarrow>")
     | Iff       -> prString "="
     | Equals    -> prString "="
     | NotEquals -> lengthString(1, "\\<noteq>")
     | Quotient  _ -> prString "quotient"
     | PQuotient _ -> prString "quotient"
     | Choose    _ -> prString "choose"
     | PChoose   _ -> prString "choose"
     | Restrict -> prString "restrict"
     | Relax -> prString "relax"
     %| Op (qid,Nonfix) -> ppOpQualifiedId c qid
     %| Op (qid,Unspecified) -> ppOpQualifiedId c qid
     | Op (qid as Qualified(_,opstr),_) ->
       (case infixFun? c fun of
          | Some infix_str ->
            enclose?(parentTerm ~= Top,
                     prConcat [lengthString(11, "\\<lambda> (x,y). x "),
                               prSymString infix_str,
                               prString " y"])
          | None ->
        if (qid = Qualified("IntegerAux","-") || qid = Qualified("Integer","~"))
          && parentTerm ~= Infix(Left,1000)   % Only true if an application
          then let vt = ("i",intType) in
               ppTerm c parentTerm (mkLambda(mkVarPat vt, mkApply(mkFun(fun,ty), mkVar vt)))
        else
        case specialOpInfo c qid of
          | Some(isa_id, _, curry?, reversed?, _) ->
            if curry? || reversed?
              then (let spc = getSpec c in
                    case productOpt(spc,domain(spc,ty)) of
                      | Some fields -> ppTerm c parentTerm (etaRuleProduct(mkFun(fun,ty), fields))
                      | None ->
                    case arrowOpt(spc, ty) of
                      | Some(dom, _) ->
                        let new_v = ("cv0", dom) in
                        ppTerm c parentTerm (mkLambda (mkVarPat new_v, mkApply(mkFun(fun,ty), mkVar new_v)))
                      | _ -> prSymString isa_id)
              else prString isa_id
          | _ -> ppOpQualifiedId c qid)
     | Project id ->
       let (dom, _) = arrow(getSpec c, ty) in
       ppTerm c parentTerm (mkLambda(mkVarPat("tp",dom), mkApply(mkFun(fun,ty), mkVar("tp",dom))))
     | RecordMerge -> prString "<<"
     | Embed (id,b) ->
       (let spc = getSpec c in
        case arrowOpt(spc,ty) of
          | Some(dom,rng) ->
            (if multiArgConstructor?(id,rng,spc)
               then
                 case productOpt(spc,dom) of
                 | Some fields -> ppTerm c parentTerm (etaRuleProduct(mkFun(fun,ty), fields))
                 | None -> ppConstructorTyped(c, id, rng, getSpec c)
               else ppConstructorTyped(c, id, rng, getSpec c))
          | None -> ppConstructorTyped(c, id, ty, getSpec c))
     | Embedded id ->
       let (dom, _) = arrow(getSpec c, ty) in
       ppTerm c parentTerm (mkLambda(mkVarPat("cp",dom), mkApply(mkFun(fun,ty), mkVar("cp",dom))))
     | Select id -> prConcat [prString "select ", prString id] % obsolete?
     | Nat n -> prString (Nat.show n)
     | Char chr -> prConcat [prString "CHR ''",
                             prString (Char.show chr),
                             prString "''"]
     | String str -> prString ("''" ^ str ^ "''")
     | Bool b -> ppBool b
     | OneName (id,fxty) -> prString id
     | TwoNames (id1,id2,fxty) -> ppOpQualifiedId c (Qualified (id1,id2))
     | mystery -> fail ("No match in ppFun with: '" ^ (anyToString mystery) ^ "'")

 def omittedQualifiers = [toIsaQual]  % "IntegerAux" "Option" ...?

 op qidToIsaString(Qualified (qualifier,id): QualifiedId): String =
   if qualifier = UnQualified || qualifier in? omittedQualifiers then
     if id in? disallowedVarNames then id ^ "__c"
       else ppIdStr id
   else
     ppIdStr qualifier ^ "__" ^ ppIdStr id

 op ppQualifiedId (qid: QualifiedId): Pretty =
   prString(qidToIsaString qid)

 op  ppOpQualifiedId : Context -> QualifiedId -> Pretty
 def ppOpQualifiedId c qid =
   case specialOpInfo c qid of
     | Some(s,_,_,_,_) -> prSymString s
     | None -> ppQualifiedId qid

 %% May only need ops that can be unary
 op overloadedIsabelleOps: List String = ["+","-","^","abs","min","max"]

 op overloadedIsabelleOp? (c: Context) (f: MSTerm) : Bool =
   case f of
     | Fun(Op(qid,_),_,_) ->
       (case specialOpInfo c qid of
          | Some(s,_,_,_,_) -> s in? overloadedIsabelleOps
          | None -> false)
     | _ -> false

op typeQualifiedIdStr (c: Context) (qid: QualifiedId): String =
   case specialTypeInfo c qid of
     | Some(s, _, _, _) -> s
     | None -> qidToIsaString qid

 op  ppTypeQualifiedId : Context -> QualifiedId -> Pretty
 def ppTypeQualifiedId c qid =
   case specialTypeInfo c qid of
     | Some(s,_,_,_) -> prString s
     | None -> ppQualifiedId qid

 op  ppFixity : Fixity -> Pretty
 def ppFixity fix =
   case fix of
     | Infix (Left,  n) -> prConcat [prString "infixl ",
                                     prString (show n)]
     | Infix (Right, n) -> prConcat [prString "infixr ",
                                     prString (show n)]
     | Nonfix           -> prEmpty % prString "Nonfix"
     | Unspecified      -> prEmpty % prString "Unspecified"
     | Error fixities   -> prConcat [prString "conflicting fixities: [",
                                     prPostSep 0 blockFill (prString ",")
                                       (map ppFixity fixities),
                                     prString "]"]
     | mystery -> fail ("No match in ppFixity with: '" ^ (anyToString mystery) ^ "'")

 op  isSimpleType? : MSType -> Bool
 def isSimpleType? ty =
   case ty of
     | Base    _ -> true
     | Boolean _ -> true
     | _ -> false

 op  ppInfixType : Context -> MSType -> Pretty
 def ppInfixType c ty =
   case arrowOpt(getSpec c,ty) of
     | Some(dom, rng) ->
       (case productTypes(getSpec c,dom) of
         | [arg1_ty,arg2_ty] ->
           ppType c Top true (mkArrow(arg1_ty, mkArrow(arg2_ty,rng)))
         | _ -> ppType c Top true ty)
     | _ -> ppType c Top true ty

 op  ppType : Context -> ParentType -> Bool -> MSType -> Pretty
 def ppType c parent in_quotes? ty =
   case ty of
     | Base (qid,[],_) -> ppTypeQualifiedId c qid
      %% CoProduct only at top level
%     | CoProduct (taggedTypes,_) -> 
%       let def ppTaggedType (id,optTy) =
%       case optTy of
%         | None -> quoteIf(~in_quotes?, id, ppConstructor id)
%         | Some ty ->
%           prConcat [quoteIf(~in_quotes?, id, ppConstructor id), prSpace,
%                     case ty of
%                       | Product(fields as ("1",_)::_,_) ->	% Treat as curried
%                         prConcat(addSeparator prSpace
%                                    (map (fn (_,c_ty) -> ppType c CoProduct in_quotes? c_ty) fields))
%                       | _ -> ppType c CoProduct in_quotes? ty]
%       in
%         enclose?(case parent of
%                    | Product -> true
%                    | CoProduct -> true
%                    | Subtype -> true
%                    | _ -> false,
%                  prSep (-2) blockAll (prString "| ") (map ppTaggedType taggedTypes))
     | Boolean _ -> prString "bool"  
     | TyVar (tyVar,_) -> prConcat[prString "'",prString tyVar]
     | MetaTyVar (tyVar,_) -> 
       let ({link, uniqueId, name}) = ! tyVar in
       prString (name ^ (Nat.show uniqueId))

     | _ | ~in_quotes? ->
       prConcat [prString "\"", ppType c Top true ty, prString "\""]

     | Base (qid,[ty],_) ->
       prBreak 0 [ppType c Apply in_quotes? ty,
                  prSpace,
                  ppTypeQualifiedId c qid]
     | Base (qid,tys,_) ->
       prBreak 0 [prString " (",
                  prPostSep 0 blockFill (prString ", ") (map (ppType c Top in_quotes?) tys),
                  prString ")",
                  ppTypeQualifiedId c qid]      | Arrow (ty1,ty2,_) ->
       enclose?(case parent of
                  | Product -> true
                  | ArrowLeft -> true
                  | Subtype -> true
                  | Apply -> true
                  | _ -> false,
                prBreak 0[ppType c ArrowLeft in_quotes? ty1,
                          lengthString(4, " \\<Rightarrow> "),
                          ppType c ArrowRight in_quotes? ty2])
     | Product (fields,_) ->
       (case fields of
          | [] -> prString "unit"
          | ("1",_)::_ ->
            let def ppField (_,y) = ppType c Product in_quotes? y in
            enclose?(case parent of
                       | Product -> true
                       | Subtype -> true
                       | Apply -> true
                       | _ -> false,
                     prSep 2 blockFill (lengthString(3, " \\<times> "))
                       (map ppField fields))
          | _ ->
            let def ppField (x,y) =
            prLinearCat 2 [[prString (mkFieldName x),
                            prString " :: "],
                           [ppType c Top in_quotes? y]]
            in
              prBreak 2 [lengthString(1, "\\<lparr>"),
                         prPostSep 0 blockLinear(prString ", ") (map ppField fields),
                         lengthString(1, "\\<rparr>")])
     | Quotient (ty,term,_) ->
         prBreak 0 [prString "(",
                    ppType c Top in_quotes? ty,
                    prString " \\ ",
                    ppTerm c Top term,
                    prString ")"]
     | Subtype (ty,term,_) ->
         prBreak 0 [prString "(",
                    ppType c Top in_quotes? ty,
                    prString " | ",
                    ppTerm c Top term,
                    prString ")"]

     | mystery -> fail ("No match in ppType with: '" ^ (anyToString mystery) ^ "'")

op  ppLitString: String -> Pretty
def ppLitString id = prString(IO.formatString1("~S",id))

op  infix?: ParentTerm -> Bool
def infix? parentTerm =
  case parentTerm of
    | Infix _ -> true
    | _ -> false

op termFixity (c: Context) (term: MSTerm): Option Pretty * Fixity * Bool * Bool = 
  case term of
    | Fun (termOp, _, _) -> 
      (case termOp of
         | Op (id, fixity) ->
           (case specialOpInfo c id of
              | Some(isa_id,fix,curried,reversed,_) ->
                (case fix of
                   | Some f -> (Some(prSymString isa_id), Infix f, curried, reversed)
                   | None ->   (Some(prSymString isa_id), Nonfix, curried, reversed))
              | None ->
                case fixity of
                  | Unspecified -> (None, Nonfix, false, false)
                  | Nonfix -> (None, Nonfix, false, false)
                  | Infix(assoc, precnum) -> (Some(ppInfixId id), Infix(assoc, convertPrecNum precnum),
                                              true, false))
         | And            -> (Some(lengthString(1, "\\<and>")),Infix (Right, 35), true, false)
         | Or             -> (Some(lengthString(1, "\\<or>")), Infix (Right, 30), true, false)
         | Implies        -> (Some(lengthString(3, "\\<longrightarrow>")), Infix (Right, 25), true, false) 
         | Iff            -> (Some(prString "="), Infix (Left, 50), true, false)
         | Not            -> (Some(lengthString(1, "\\<not>")), Infix (Left, 40), false, false) % ?
         | Equals         -> (Some(prString "="), Infix (Left, 50), true, false) % was 10 ??
         | NotEquals      -> (Some(lengthString(1, "\\<noteq>")), Infix (Left, 50), true, false)
         | RecordMerge    -> (Some(prString "<<"), Infix (Left, 65), true, false)
         | _              -> (None, Nonfix, false, false))
    | _ -> (None, Nonfix, false, false)

op reversedNonfixOp? (c: Context) (qid: QualifiedId): Bool =
  case specialOpInfo c qid of
    | Some(_ ,None,_,true,_) -> true
    | _ -> false

op  enclose?: Bool * Pretty -> Pretty
def enclose?(encl? ,pp) =
  if encl? then prConcat [prString "(", pp, prString ")"]
    else pp

op ppTermEncloseComplex? (c: Context) (parentTerm: ParentTerm) (term: MSTerm): Pretty =
  let encl? = ~(isSimpleTerm? term) in
  enclose?(encl?, ppTerm c (if encl? then Top else parentTerm) term)

def prSpace = prString " "

op  ppInfixId: QualifiedId -> Pretty
def ppInfixId(Qualified(_,main_id)) = prString (infixId main_id)

op infixId(id: String): String =
  let idarray = explode(id) in
  let id = foldr (fn(#\\,id) -> "\\\\"^id   % backslashes must be escaped
                  | (c,id) -> show(c)^id) "" idarray
  in id

op  ppInfixDefId: QualifiedId -> Pretty
def ppInfixDefId(Qualified(_,main_id)) = prString (infixDefId main_id)

op infixDefId(id: String): String =
  let idarray = explode(id) in
  let id = foldr (fn(#\\,id) -> "\\\\"^id   % backslashes must be escaped
                  | (#/,id) -> "'/"^id
                  | (#(,id) -> "'("^id
                  | (#),id) -> "')"^id
                  | (#_,id) -> "'_"^id
                  | (c,id) -> show(c)^id) "" idarray
  in id

op  ppIdStr: String -> String
def ppIdStr id =
  let idarray = explode(id) in
  let def att(id, s) =
        (if id = "" then "e" else id) ^ s
  in
  let id = foldl (fn(id,#?) -> att(id, "_p")
                  | (id,#=) -> att(id, "_eq")
                  | (id,#<) -> att(id, "_lt")
                  | (id,#>) -> att(id, "_gt")
                  | (id,#~) -> att(id, "_tld")
                  | (id,#/) -> att(id, "_fsl")
                  | (id,#\\ ) -> att(id, "_bsl")
                  | (id,#-) -> att(id, "_dsh")
                  | (id,#*) -> att(id, "_ast")
                  | (id,#+) -> att(id, "_pls")
                  | (id,#|) -> att(id, "_bar")
                  | (id,#!) -> att(id, "_excl")
                  | (id,#@) -> att(id, "_at")
                  | (id,##) -> att(id, "_hsh")
                  | (id,#$) -> att(id, "_dolr")
                  | (id,#^) -> att(id, "_crt")
                  | (id,#&) -> att(id, "_amp")
                  | (id,#') -> att(id, "_cqt")
                  | (id,#`) -> att(id, "_oqt")
                  | (id,#:) -> att(id, "_cl")
                  | (id,c) -> id ^ show c) "" idarray
  in id

op  isSimpleTerm? : MSTerm -> Bool
def isSimpleTerm? trm =
  case trm of
    | TypedTerm(t,_,_) -> isSimpleTerm? t
    | Var _ -> true
    | Fun _ -> true
    | _ -> false

op  isSimplePattern? : MSPattern -> Bool
def isSimplePattern? trm =
  case trm of
    | VarPat _ -> true
    | WildPat _ -> true
    | EmbedPat(_,None,_,_) -> true
    | StringPat _ -> true
    | BoolPat _ -> true
    | CharPat _ -> true
    | NatPat _ -> true
    | _ -> false

 op  varOrTuplePattern?: MSPattern -> Bool
 def varOrTuplePattern? p =
   case p of
     | VarPat _ -> true
     | RecordPat(prs,_) | tupleFields? prs ->
       forall? (fn (_,p) -> varOrTuplePattern? p) prs
     | RestrictedPat(pat,cond,_) -> varOrTuplePattern? pat
     | WildPat _ -> true
     | _ -> false

 op  varOrRecordPattern?: MSPattern -> Bool
 def varOrRecordPattern? p =
   case p of
     | VarPat _ -> true
     | RecordPat(prs,_) ->
       forall? (fn (_,p) -> varOrRecordPattern? p) prs
     | RestrictedPat(pat,cond,_) -> varOrRecordPattern? pat
     | WildPat _ -> true
     | _ -> false

 op  simpleHead?: MSTerm -> Bool
 def simpleHead? t =
   case t of
     | Apply(_,arg,_) -> varOrTupleTerm? arg
     | _ -> false

 op  varOrTupleTerm?: MSTerm -> Bool
 def varOrTupleTerm? p =
   case p of
     | Var _ -> true
     | Record(prs as (("1",_)::_),_) ->
       forall? (fn (_,p) -> varOrTupleTerm? p) prs
     | _ -> false

 op overloadedConstructors(spc: Spec): List String =
   (foldTypeInfos
      (fn (info, result as (found,overloaded)) ->
         case typeInnerType(info.dfn) of
           | CoProduct(prs,_) ->
             foldl (fn ((found,overloaded),(id,_)) ->
                      if id in? found
                        then (  found, id::overloaded)
                      else (id::found,     overloaded))
               result prs
           | _ -> result)
     ([],[])
     spc.types).2

op unfoldMonadBinds(spc: Spec): Spec = 
  let def unfold tm =
        case tm of
          | Apply(Fun(Op(Qualified(_, "monadBind"), _), _, _) , x, _) ->
            (case tryUnfold(spc, tm) of
               | Some new_tm ->
                 % let _ = writeLine("monadBind to "^printTerm new_tm) in
                 unfold new_tm
               | None -> tm)
          | Apply(Lambda(rules, _), t2, _) | length rules > 1 && ~(embed? Var t2)->
            (let uf_t2 = case tryUnfold(spc, t2) of
                           | None -> t2
                           | Some uf_tm -> uf_tm
             in
             % let _ = writeLine("ufmb: "^printTerm t2^"\n"^printTerm uf_t2) in
             case uf_t2 of
               | IfThenElse(p, t_tm, f_tm, a) ->
                 (case (patternMatchRulesToLet(rules, t_tm, spc), patternMatchRulesToLet(rules, f_tm, spc)) of
                    | (Some exp_t_tm, Some exp_f_tm) -> IfThenElse(p, exp_t_tm, exp_f_tm, a)
                    | _ -> tm)
               | _ ->
             case patternMatchRulesToLet(rules, uf_t2, spc) of
               | Some exp_tm ->
                 % let _ = writeLine("case to "^printTerm exp_tm) in
                 exp_tm
               | None -> tm)
          | _ -> simplifyUnfoldCase spc tm
  in
  mapSpecLocalOps (unfold, id, id) spc
end-spec


