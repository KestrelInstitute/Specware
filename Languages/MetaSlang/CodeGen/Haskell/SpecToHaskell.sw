(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Haskell qualifying spec

 import /Languages/MetaSlang/CodeGen/Generic/CodeGenTransforms

 import /Languages/SpecCalculus/Semantics/Evaluate/Signature             % SCTerm
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements  % adjustElementOrder

 % import /Languages/MetaSlang/CodeGen/SubstBaseSpecs                    % substBaseSpecs1, also gets hack for evaluateUnitId

 import /Languages/MetaSlang/Transformations/TheoryMorphism
 import /Languages/MetaSlang/Transformations/NormalizeTypes
 import /Library/PrettyPrinter/BjornerEspinosa
 import /Library/Legacy/DataStructures/ListUtilities
 import /Languages/SpecCalculus/AbstractSyntax/Types
 import /Languages/SpecCalculus/Semantics/Value
 import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities
 import /Languages/MetaSlang/Specs/Environment
 import /Languages/MetaSlang/Transformations/Coercions
 import /Languages/MetaSlang/Transformations/CurryUtils
 import /Languages/MetaSlang/Transformations/RenameBound

 import /Languages/MetaSlang/CodeGen/Haskell/SliceForHaskell

 op useQualifiedNames?: Bool = false
 op simplify?: Bool = false

 type Pretty = PrettyPrint.Pretty
 type Pragma = String * String * String * Position

 type TypeClassInfo = {type_qid: QualifiedId,
                       class_id: String,
                       instance_ops: List(QualifiedId * String)}

 type Context = {recursive?: Bool,
                 generateStrict?: Bool,
                 top_spec?: Bool,
                 top_spec: Spec,
                 top_uid: UnitId,
                 slicing?: Bool,
                 needed_ops: QualifierSet,
                 needed_types: QualifierSet,
                 spec_name: String,
		 spec?: Option Spec,
                 qualifier?: Option String,
                 currentUID: UnitId,
		 trans_table: TransInfo,
                 coercions: TypeCoercionTable,
                 overloadedConstructors: List String,
                 newVarCount: Ref Nat,
                 source_of_haskell_morphism?: Bool,
                 typeNameInfo: List(QualifiedId * TyVars * MSType),
                 polyEqualityFunInfo: AQualifierMap TyVars}

 op specialOpInfo (c: Context) (qid: QualifiedId): Option OpTransInfo =
   apply(c.trans_table.op_map, qid)

 op specialTypeInfo (c: Context) (qid: QualifiedId): Option TypeTransInfo =
   apply(c.trans_table.type_map, qid)

 op mappedType?(c: Context) (qid: QualifiedId): Bool =
   case specialTypeInfo c qid of
     | Some(_,_,_,no_def?) -> no_def?
     | None -> false

 op getSpec(c: Context): Spec =
   let Some spc = c.spec? in spc

 op getCurrentUID(c: Context): UnitId = c.currentUID

 op neededOp? (c: Context) (qid: QualifiedId): Bool =
   c.slicing? => qid in? c.needed_ops

 op neededType? (c: Context) (qid: QualifiedId): Bool =
   c.slicing? => qid in? c.needed_types


 type ParentTerm = | Term.Top | Nonfix | Infix Associativity * Nat
 type ParentType = | Type.Top | ArrowLeft | ArrowRight | Product | CoProduct | Quotient | Subtype | Apply

  %% --------------------------------------------------------------------------------
  %% Give the signature of utilities so we don't have to import them

  type GlobalContext
  %op  MonadicStateInternal.readGlobalVar : [a] String -> Option a
  %op  Specware.evaluateUnitId: String -> Option Value
  %op  SpecCalc.findUnitIdForUnit: Value * GlobalContext -> Option UnitId
  %op  SpecCalc.uidToFullPath : UnitId -> String
  op  Specware.cleanEnv : SpecCalc.Env ()
  op  Specware.runSpecCommand : [a] SpecCalc.Env a -> a

  op uidToHaskellNames ({path, hashSuffix=_}: UnitId, slicing?: Bool,
                       {path=top_path, hashSuffix=_}: UnitId): String * String =
   let device? = deviceString? (if slicing? then head top_path else head path) in
   let main_name = last path in
   let path_dir = butLast path in 
   let (full_name, main_path) =
       if slicing?
         then let top_path_dir = butLast top_path in 
              let common_par = longestCommonPrefix(path_dir, top_path_dir) in
              let unique_path_dir = removePrefix(path_dir, length common_par) in
              let top_haskell_dir =
                  foldr (fn (elem, result) -> "/"::elem::result)
                    ["/Haskell/"]
                    (if device? then tail top_path_dir else top_path_dir)
              in
              let par_num = length top_path_dir - length common_par in
              let par_dir = "Par__"^show(par_num) in
              let up_to_unique_dir = top_haskell_dir ++ (if par_num = 0 then [] else [par_dir^"/"]) in
              (flatten((if par_num = 0 then [] else[par_dir^"."])
                         ++ foldr (fn (elem, result) -> elem::"."::result)
                              [haskellName main_name] unique_path_dir),
               flatten (up_to_unique_dir
                         ++ foldr (fn (elem, result) -> elem::"/"::result)
                              [haskellName main_name] unique_path_dir))
         else (main_name,
               flatten (foldr (fn (elem, result) -> "/"::elem::result)
                         ["/Haskell/", haskellName main_name]
                         (if device? then tail path_dir else path_dir)))
   in
   (full_name,
    if device?
      then (if slicing? then head top_path else head path) ^ main_path
    else main_path)

 op unitIdToHaskellString(uid: UnitId, slicing?: Bool, top_uid: UnitId)
       : (String * String * String * String) =
    let (import_name, file_name) = uidToHaskellNames(uid, slicing?, top_uid) in
    % let _ = writeLine("uiths import: "^import_name^" file_name: "^file_name) in
    case uid.hashSuffix of
      | Some loc_nm -> (last uid.path, import_name, file_name, "_" ^ loc_nm)
      | _ ->           (last uid.path, import_name, file_name, "")

  op  printUIDtoHaskellFile: String * Bool * Bool -> String
  def printUIDtoHaskellFile (uid_str, slicing?, recursive?) =
    case Specware.evaluateUnitId uid_str of
      | Some(val as Spec spc) ->
        (case uidNamesForValue(val, slicing?) of
	   | None -> "Error: Can't get UID string from value"
	   | Some (haskell_nm, haskell_module_name, uidstr, uid) ->
             % let _ = writeLine("pruid hmn: "^haskell_module_name^" uidstr: "^uidstr) in
             %let top_dirs = rootDirectoriesForSpec(spc, uid) in
             %let _ = writeLine "Directories:" in
             %let _ = app (fn dir -> writeLine(anyToString dir)) top_dirs in
             let _ = if slicing? then deleteHaskellFilesForSpec(spc, slicing?, uid) else () in
	     let fil_nm = uidstr ^ ".hs" in
	     let _ = ensureDirectoriesExist fil_nm in
	     let _ = toFile(fil_nm, showValue(val, true, spc, uid, slicing?, emptySet, emptySet,
                                              recursive?, uid, Some haskell_module_name)) in
	     fil_nm)
      | _ -> "Error: Unknown UID " ^ uid_str

  type Directory = List String

  op subDirectory?(d1: Directory) (d2: Directory): Bool =
    length d2 <= length d1
      && d2 = subFromTo(d1, 0, length d2)

  op uidDirectory(uid: UnitId): Directory =
    subFromTo(uid.path, 0, length uid.path - 1)

(*
  op rootDirectoriesForSpec(spc: Spec, uid: UnitId): List Directory =
    let base_spec = getBaseSpec() in
    let def addUIDfor(spc: Spec, sc_tm: MSTerm, currentUID: UnitId, red_els: SpecElements, dirs: List Directory): List Directory =
          if spc = base_spec then dirs
          else
          case uidForValueOrTerm(currentUID, Spec spc, sc_tm) of
            | None -> dirs
            | Some(uid, _) -> findDirsInImports(red_els, uid, addDir(uid, dirs))
        def findDirsInImports(els: SpecElements, currentUID: UnitId, dirs: List Directory): List Directory =
          List.foldl (fn (dirs, el) ->
                 case el of
                 | Import(imp_sc_tm, im_sp, red_els, _) ->
                   addUIDfor(im_sp, imp_sc_tm, currentUID, red_els, dirs)
                 | _ -> dirs)
            dirs els
        def addDir(uid, dirs) =
          let uid_dir = uidDirectory uid in
          if exists? (subDirectory? uid_dir) dirs
            then dirs
            else uid_dir :: dirs           
    in
    case uidStringPairTermForValue(Spec spc) of
      | None -> []
      | Some(_, uid, _) ->
        findDirsInImports(spc.elements, uid, [uidDirectory uid])
*)

  op deleteHaskellFilesForSpec (spc: Spec, slicing?: Bool, top_uid: UnitId): () =
    let base_spec = getBaseSpec() in
    let def delUIDfor(spc: Spec, sc_tm: SCTerm, currentUID: UnitId, red_els: SpecElements): () =
          if spc = base_spec then ()
          else
          case uidForValueOrTerm(currentUID, Spec spc, sc_tm, slicing?, top_uid) of
            | None -> ()
            | Some(uid, filnm) -> delHaskellFilesFromImports(red_els, filnm, uid)
        def delHaskellFilesFromImports(els: SpecElements, fil_nm, currentUID: UnitId): () =
          %let _ = if fileExists? fil_nm then writeLine("Deleting "^fil_nm) else () in
          let _ = ensureFileDeleted(fil_nm) in
          List.app (fn el ->
                      case el of
                        | Import(imp_sc_tm, im_sp, red_els, _) ->
                          delUIDfor(im_sp, imp_sc_tm, currentUID, red_els)
                        | _ -> ())
            els
    in
    case uidStringPairTermForValue(Spec spc, slicing?, Some top_uid) of
      | None -> ()
      | Some((_, _, filnm, hash), uid, _) ->
        delHaskellFilesFromImports(spc.elements, filnm ^ hash ^ ".hs", uid)

  op  ensureFileDeleted: String -> ()
  def ensureFileDeleted fil_nm =
    if fileExists? fil_nm
      then deleteFile fil_nm
      else ()

  def uidNamesForValue (val: Value, slicing?: Bool): Option (String * String * String * UnitId) =
    case uidStringPairTermForValue(val, slicing?, None) of
      | None -> None
      | Some((haskellnm, haskell_module_name, filnm, hash), uid, _) ->
        % let _ = writeLine("unfrv haskellnm: "^haskellnm^" filnm: "^filnm^" mn: "^haskell_module_name) in
        Some(haskellnm ^ hash, haskell_module_name ^ hash, filnm ^ hash, uid)

  op uidStringPairTermForValue (val: Value, slicing?: Bool, top_uid?: Option UnitId)
       : Option ((String * String * String * String) * UnitId * SCTerm) =
    case MonadicStateInternal.readGlobalVar "GlobalContext" of
      | None -> None
      | Some global_context ->
    case findUnitIdTermForUnit(val, global_context) of
      | None -> None
      | Some (uid, sc_tm) -> Some (unitIdToHaskellString(uid, slicing?, case top_uid? of
                                                                        | Some top_uid -> top_uid
                                                                        | None -> uid),
                                   uid, sc_tm)

  op haskellLibrarySpecNames: List String = ["List", "Char", "Prelude",  "Ratio", "Complex", "Numeric",
                                             "Ix", "Array", "Maybe", "Monad", "Locale", "Time", "IO",
                                             "Integer", "Ring", "String", "System", "Base"]
  op haskellName(spname: String): String =
    if spname in? haskellLibrarySpecNames
      then "SW_"^spname
    else if spname = "Character"
      then "SW_Char"
      else spname

  op uidForValueOrTerm(currentUID: UnitId, val: Value, sc_tm: SCTerm, slicing?: Bool, top_uid: UnitId) : Option(UnitId * String) =
    case uidStringPairTermForValue (val, slicing?, Some top_uid) of
      | None ->
        (case uidStringPairForTerm(currentUID, sc_tm, slicing?, top_uid) of
           | None -> None
           | Some((_, _, _, haskell_file), uid) -> Some(uid, haskell_file ^ ".hs"))
      | Some((_, _, filnm, hash), uid, _) -> Some(uid, haskellName(filnm ^ hash) ^ ".hs")

  op uidStringPairForValueOrTerm
       (currentUID: UnitId, val: Value, sc_tm: SCTerm, slicing?: Bool, top_uid: UnitId)
       : Option((String * String * String * String) * Value * UnitId) =
    case uidStringPairTermForValue(val, slicing?, Some top_uid) of
      | None ->
        (case uidStringPairForTerm(currentUID, sc_tm, slicing?, top_uid) of
           | None -> None
           | Some((haskellnm, sw_file, haskell_module_name, haskell_file), uid) ->
         % let _ = writeLine("uidStringPairForValueOrTerm0: "^haskellnm^" "^haskell_module_name) in
         case evaluateTermWrtUnitId(sc_tm, currentUID) of
           | None ->
             (writeLine("sc_tm not evaluated:\n"^anyToString sc_tm);
              None)
           | Some real_val ->
             Some((haskellnm, sw_file, haskell_module_name, haskellName haskell_file ^ ".hs"),
                  real_val, uid))
      | Some((haskellnm, haskell_module_name, filnm, hash), uid, _) ->
        % let _ = writeLine("uidStringPairForValueOrTerm1: "^haskellnm^" "^haskell_module_name) in
        Some((haskellnm ^ hash,
              uidToFullPath uid ^ ".sw",
              haskell_module_name ^ hash,
              haskellName(filnm ^ hash) ^ ".hs"),
             val, uid)

  op uidStringPairForTerm(currentUID: UnitId, sc_tm: SCTerm, slicing?: Bool, top_uid: UnitId)
       : Option((String * String * String * String) * UnitId) =
    % let _ = writeLine("Evaluating sc_tm:\n"^anyToString sc_tm) in
    case sc_tm of
      | (Subst(spc_tm, morph_tm, pragmas), pos) ->
        (case uidStringPairForTerm(currentUID, spc_tm, slicing?, top_uid) of
           | None -> (writeLine("subst sc_tm not evaluated:\n"^anyToString spc_tm);
                      None)
           | Some((haskellnm, sw_file, haskell_module_name, haskell_file), uid) ->
             let sb_id = "_sb_" ^ scTermShortName morph_tm in
             Some((haskellnm^sb_id, sw_file, haskell_module_name^sb_id, haskell_file^sb_id),
                  uid))
      | (UnitId relId, pos) ->
        (case evaluateRelUIDWrtUnitId(relId, pos, currentUID) of
          | None ->
            (writeLine("reluid not found:\n"^anyToString sc_tm);
             None)
          | Some(val, uid) ->
            % let _ = writeLine("Found RelUID:\n"^anyToString uid) in
            let (haskellnm, haskell_module_name, filnm, hash) = unitIdToHaskellString(uid, slicing?, top_uid) in
            Some((haskellnm ^ hash,
                  uidToFullPath uid ^ ".sw",
                  haskell_module_name ^ hash,
                  filnm ^ hash),
                 uid))
      | (Qualify(spc_tm, qual), pos) ->
        (case uidStringPairForTerm(currentUID, spc_tm, slicing?, top_uid) of
           | None -> None
           | Some((haskellnm, sw_file, haskell_module_name, haskell_file), uid) ->
             Some((haskellnm^"_"^qual, sw_file, haskell_module_name^"_"^qual, haskell_file^"_"^qual),
                  uid))
      | (Translate(spc_tm, _), pos) ->
        (case uidStringPairForTerm(currentUID, spc_tm, slicing?, top_uid) of
           | None -> None
           | Some((thynm, sw_file, haskell_module_name, thy_file), uid) ->
             Some((thynm^"_translated", sw_file, haskell_module_name^"_translated", thy_file^"_translated"),
                  uid))
      | _ ->
        (writeLine("sc_tm not handled:\n"^anyToString sc_tm);
         None)

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
    % let _ = writeLine("Evaluating RelUID:\n"^anyToString rel_uid) in
    let
      %% Ignore exceptions
      def handler except =
        let _ = writeLine("Evaluation failed:\n"^anyToString except) in
        return None
    in
    let prog = {cleanEnv;
		setCurrentUID currentUID;
                % print("evalRelUID: "^anyToString currentUID^"\n");
		((val, _, _), uid)  <- evaluateReturnUID pos rel_uid false;
		return (Some(val, uid))} 
    in
      runSpecCommand (catch prog handler)

  op  evaluateTermWrtUnitId(sc_tm: SCTerm, currentUID: UnitId): Option Value = 
    % let _ = writeLine("Evaluating term wrt UID:\n"^anyToString sc_tm) in
    let
      %% Ignore exceptions except for warning message
      def handler except =
        let _ = writeLine("Evaluation failed:\n"^anyToString except) in
        return None
    in
    % let _ = writeLine("evaluateTermWrtUnitId") in
    let prog = {cleanEnv;
		setCurrentUID currentUID;
		val  <- evaluateTerm sc_tm;
                % print ("evalTerm:\n"^(case val of Spec spc -> printSpecFlat (subtractSpec spc (getBaseSpec())) | _ -> "")^"\n" );
		return (Some val)} 
    in
      runSpecCommand (catch prog handler)

  op  SpecCalc.findUnitIdForUnitInCache: Value -> Option UnitId
  def findUnitIdForUnitInCache val =
    case readGlobalVar "GlobalContext" of
      | None -> None
      | Some global_context ->
        findUnitIdForUnit(val, global_context)
  
  op findSpecQualifier(sc_tm: SCTerm): Option String =
    case sc_tm of
      | (Qualify(_, qual), _) -> Some (haskellName qual)
      | _ -> None

  op dummySpecCalcTerm: SCTerm = (Spec [], noPos)

  op  showValue : Value * Bool * Spec * UnitId * Bool * QualifierSet * QualifierSet * Bool * UnitId
                    * Option String -> Text
  def showValue (value, top_spec?, top_spec, top_uid, slicing?, needed_ops, needed_types,
                 recursive?, uid, opt_nm) =
    let (haskell_nm, qualifier?) =
        case uidStringPairTermForValue(value, slicing?, Some top_uid) of
          | None -> (case opt_nm of
                     | Some haskell_module_name -> (haskell_module_name, None)
                     | None -> ("<Unknown spec>", None))
          | Some ((_, haskell_module_name, _, hash_nm), val_uid, sc_tm) ->
            (haskell_module_name, findSpecQualifier sc_tm)
    in
    let main_pp_val = ppValue {recursive? = recursive?,
                               generateStrict? = false,
                               top_spec? = top_spec?,
                               top_spec = top_spec,
                               top_uid = top_uid,
                               slicing? = slicing?,
                               needed_ops = needed_ops,
                               needed_types = needed_types,
			       spec_name = case opt_nm of
                                            | Some nm -> nm
                                            | None -> haskell_nm,
			       spec? = None,
                               qualifier? = qualifier?,
                               currentUID = uid,
			       trans_table = emptyTranslationTable,
                               coercions = [],
                               overloadedConstructors = [],
                               newVarCount = Ref 0,
                               source_of_haskell_morphism? = false,
                               typeNameInfo = [],
                               polyEqualityFunInfo = emptyAQualifierMap}
			value
    in
    format(120, main_pp_val)

  %% --------------------------------------------------------------------------------

  op  ppValue : Context -> Value -> Pretty
  def ppValue c value =
    case value of
      | Spec spc -> % let _ = writeLine(printSpec spc) in
        ppSpec c spc
      | _ -> prString "<Not a spec>"
 
(*
  op mergeRealImports(full_els: SpecElements, reduced_els: SpecElements): List SpecElement =
    %% Spec elaboration removes duplicate imports in the import tree. We need them for Haskell generation
    %% so that sub-module can be compiled
    (writeLine("Reduced imports:");
     app (fn el -> case el of
                    | Import(sp_tm, _, _, _) -> writeLine(anyToString sp_tm) | _ -> ()) reduced_els;
     writeLine("full importt:");
     app (fn el -> case el of
                    | Import(sp_tm, _, _, _) -> writeLine(anyToString sp_tm) | _ -> ()) full_els;

    let imports_to_restore =
        filter (fn f_el ->
                case f_el of
                  | Import(f_sc_tm, im_sp, _, _) ->
                    ~(exists? (fn r_el ->
                               case r_el of
                                 | Import(r_sc_tm, im_sp, _, _) -> f_sc_tm = r_sc_tm
                                 | _ -> false)
                        reduced_els)
                 %% Shouldn't be removing pragmas that need to be added back
                 % | Pragma("#translate", prag_str, "#end", _) -> haskellPragma? prag_str
                 | _ -> false)
          full_els
    in
    imports_to_restore ++ reduced_els)
 *)                                 

  %% --------------------------------------------------------------------------------
  %% Specs
  %% --------------------------------------------------------------------------------

  op makeSubstFromRecPats(pats: List(Id * MSPattern), rec_tm: MSTerm, spc: Spec): List(MSPattern * MSTerm) =
    mapPartial (fn (fld, pat) -> if embed? WildPat pat then None
                                  else Some(pat, mkProjectTerm(spc, fld, rec_tm)))
      pats

  op expandRecPatterns (spc: Spec) (pat: MSPattern, condn: MSTerm, body: MSTerm): MSPattern * MSTerm * MSTerm =
    case pat of
      | RecordPat(pats as (id1, _)::_, _) | id1 ~= "1" && varOrRecordPattern? pat ->
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
      | Let([(pat as RecordPat(pats as (id1, _)::_, _), rec_tm)], body, _)
          | id1 ~= "1" && varOrRecordPattern? pat ->
        let binds = makeSubstFromRecPats(pats, rec_tm, spc) in
        foldr (fn (bnd, bod) -> maybeExpandRecordPattern spc (MS.mkLet([bnd], bod))) body binds
      | Lambda (pats, a) ->
        Lambda(map (expandRecPatterns spc) pats, a)
      | _ -> t

  op expandRecordPatterns(spc: Spec): Spec =
    mapSpec (maybeExpandRecordPattern spc, id, id)
      spc

  op nonExecBaseSpecs: List String = ["List", "String", "Integer"]
  op addExecutableDefs (spc: Spec, spec_name: String): Spec =
    if spec_name in? nonExecBaseSpecs
      then substBaseSpecs1(spc, ["/Library/Base/"^spec_name^"_Executable"])
      else spc

  op ppSpec (c: Context) (spc: Spec): Pretty =
    % let _ = writeLine("0:\n"^printSpec spc) in
    %% Get rid of non-haskell pragmas
    %% let _ = writeLine(c.spec_name) in
    let spc = explicateEmbeds spc in
    let spc = removeImplicitConstructorOps spc in
    let spc = addExecutableDefs(spc, c.spec_name) in
    let trans_table = thyMorphismMaps spc "Haskell" convertPrecNum in
    % let _ = writeLine("0a:\n"^printSpecFlat( spc)^"\n") in
    let c = if c.slicing? && c.top_spec? then
              %% don't recur into subtype predicates, don't chase through theorems
              let (needed_ops, needed_types) = 
                  sliceSpecInfoForCode (spc, topLevelOpNames spc, topLevelTypeNames spc)
              in
              c << {needed_ops   = needed_ops,
                    needed_types = needed_types}
            else 
              c
    in
    let rel_elements = filter haskellElement? spc.elements in
    let spc = spc << {elements = normalizeSpecElements(rel_elements)} in
    let spc = adjustElementOrder spc in
    let source_of_haskell_morphism? = exists? (fn el ->
                                            case el of
                                              | Pragma("#translate", prag_str, "#end", _)
                                                  -> true
                                              | _ -> false)
                                     spc.elements
    in
    let c = c << {spec? = Some spc,
                  top_spec = if c.top_spec? then spc else c.top_spec,
                  trans_table = trans_table,
                  source_of_haskell_morphism? = source_of_haskell_morphism?,
                  polyEqualityFunInfo = polyEqualityAnalyze spc}
    in
    let spc = normalizeTopLevelLambdas spc in
    let spc = if simplify? && some?(AnnSpec.findTheType(spc, Qualified("Nat", "Nat")))
                then simplifyTopSpec spc
                else spc
    in
    let spc = normalizeNewTypes(spc, false) in
    let morphism_coercions = makeCoercionTable(trans_table, spc) in   % before removeSubTypes!
    let (typeclass_coercions, c) = coercionsFromTypeClassPragmas c spc in
    let coercions = typeclass_coercions ++ morphism_coercions in
    let c = c << {coercions = coercions,
                  overloadedConstructors = overloadedConstructors spc}
    in
    % let _ = printSpecWithTypesToTerminal spc in
    % let _ = writeLine("1:\n"^printSpec spc) in
% ?    let spc = removeSubTypes spc coercions stp_tbl in
    %% Second round of simplification could be avoided with smarter construction
% ?    let spc = expandRecordPatterns spc in
% ?    let spc = normalizeNewTypes spc in
    let spc = addCoercions coercions spc in
    let spc = if simplify? && some?(AnnSpec.findTheType(spc, Qualified("Nat", "Nat")))
                then simplifyTopSpec(simplifyTopSpec spc) % double simplify temporary?
                else spc
    in
    let c = c << {typeNameInfo = topLevelTypeNameInfo spc,
                  spec? = Some spc}
    in
    % let _ = writeLine("n:\n"^printSpec spc) in
    let (pp_imports, pp_exports) = ppImports c spc.elements in
    let pr_haskellname = prString(haskellName c.spec_name) in
    prLinesCat 0 (ppHeaderPragmas spc.elements
                  ++ [[prString "module ", pr_haskellname,
                       prString " ( ",
                       prSep 0 blockFill (prString ", ")
                         (if c.slicing? && ~(c.top_spec?) && pp_exports ~= [] then pp_exports
                            else prConcat [prString "module ", pr_haskellname] :: pp_exports),
                       prString " )",
                       prString " where"]]
                  ++ pp_imports
		  ++ [[ppSpecElements c spc (filter elementFilter spc.elements)]])

  op  elementFilter: SpecElement -> Bool
  def elementFilter elt =
    case elt of
      | Import _ -> false
      | Pragma("#translate", prag_str, "#end", _) | haskellPragma? prag_str
                                                && haskellMorphismPragma prag_str = None ->
        true
      | Pragma _ -> false
      | _ -> true

  %% Originally was just supertype but generalized to also be a named type
  %% For internal use. Choose unparseable name
  def toHaskellQual = "ToHaskell-Internal"

 %% Originally was just supertype but generalized to also be a named type
  op getSuperType(ty: MSType): MSType =
    case ty of
      | Subtype(sup,_,_) \_rightarrow sup
      | _ \_rightarrow ty

  op  makeCoercionTable: TransInfo * Spec -> TypeCoercionTable
  def makeCoercionTable(trans_info, spc) =
    foldi (fn (subty, (super_id, opt_coerc, overloadedOps, no_def?), val) ->
           case opt_coerc of
             | None -> val
             | Some(toSuper, toSub) ->
           let srtDef = typeDef(subty, spc) in
           let superty = getSuperType srtDef in
           Cons({subtype = subty,
                 supertype = superty,
                 coerceToSuper = mkOp(Qualified(toHaskellQual, toSuper),
                                      mkArrow(mkBase(subty, []), superty)),
                 coerceToSub   = mkOp(Qualified(toHaskellQual, toSub),
                                      mkArrow(superty, mkBase(subty, []))),
                 overloadedOps = overloadedOps},
                val))
      [] trans_info.type_map

  op exportedOps (c: Context) (spc: Spec): QualifiedIds =
    % let _ = writeLine("Export from\n"^printSpec spc) in
    let top_spec = c.top_spec in
    let op_tbl = spc.ops in
    let base_op_tbl = (getBaseSpec()).ops in
    %% Map through all ops in top spec that aren't in spc, and collect ops used
    %% that are in spc
    if spc = top_spec then []
    else
    let needed_ops =
        foldriAQualifierMap  (fn (q, id, info, needed_ops) ->
                                if primaryOpName? (q, id, info)
                                     && none?(findAQualifierMap (op_tbl, q, id))
                                     && Qualified(q, id) in? c.needed_ops
                                  then
                                    % let _ = writeLine("Checking def of "^id) in
                                    foldSubTerms (fn (tm, needed_ops) ->
                                                  case tm of
                                                    | Fun(Op(qid as Qualified(q, id), _), _, _)
                                                        | qid in? c.needed_ops
                                                            && none?(findAQualifierMap (base_op_tbl, q, id))
                                                            && some?(findAQualifierMap (op_tbl, q, id))
                                                            && numRefinedDefs spc qid = numRefinedDefs top_spec qid
                                                            && qid nin? needed_ops ->
                                                      qid :: needed_ops
                                                    | _ -> needed_ops)
                                      needed_ops info.dfn
                                else needed_ops)
          [] top_spec.ops
    in
    % let _ = writeLine(anyToString needed_ops) in
    needed_ops

  op exportableType? (c: Context) (qid as Qualified(q, id): QualifiedId) (o_defn: Option TypeInfo): Bool =
    let def exportable? ty =
          case ty of
            | Base _ -> false
            | Pi(_, ty1, _)      -> exportable? ty1
            | Subtype(ty1, _, _) -> exportable? ty1
            | _ -> true
    in
    case o_defn of
      | None -> false
      | Some ty_info ->
    ~(mappedType? c qid) && exportable? ty_info.dfn

  op exportedTypes (c: Context) (spc: Spec): QualifiedIds =
    let top_spec = c.top_spec in
    let op_tbl = spc.ops in
    let type_tbl = spc.types in
    let base_type_tbl = (getBaseSpec()).types in
    %% Map through all ops in top spec that aren't in spc, and collect types used
    %% that are in spc
    if spc = top_spec then []
    else
    let def collectExportable(needed_types, ty) =
          case ty of
            | Base(qid as Qualified(q, id), _, _)
                | none?(findAQualifierMap (base_type_tbl, q, id))
                 && (let o_ty_def = findAQualifierMap (type_tbl, q, id) in
                       exportableType? c qid o_ty_def)
                 && qid nin? needed_types ->
              qid :: needed_types
            | _ -> needed_types
    in
    let needed_types = foldriAQualifierMap (fn  (q, id, info, needed_types) ->
                                              if primaryOpName? (q, id, info)
                                                && none?(findAQualifierMap (op_tbl, q, id))
                                                && Qualified(q, id) in? c.needed_ops
                                               then foldTypesInTerm collectExportable needed_types info.dfn
                                               else needed_types)
                           [] top_spec.ops
    in
    let needed_types = foldriAQualifierMap (fn  (q, id, info, needed_types) ->
                                              if primaryTypeName? (q, id, info)
                                                && none?(findAQualifierMap (type_tbl, q, id))
                                                && Qualified(q, id) in? c.needed_types
                                               then foldTypesInType collectExportable needed_types info.dfn
                                               else needed_types)
                           needed_types top_spec.types
    in
    % let _ = writeLine(anyToString needed_types) in
    needed_types

  op realElement?(c: Context) (el: SpecElement): Bool =
    %% Used to avoid printing empty modules
    %% Can ignore translated ops and types and non-verbatim pragmas
    case el of
      | Op (qid, _, _) ->
        (case specialOpInfo c qid of
           | Some (_, _, _, _, no_def?) -> ~no_def?
           | _ -> neededOp? c qid)
      | OpDef (qid, _, _, _) ->
        (case specialOpInfo c qid of
           | Some (_, _, _, _, no_def?) -> ~no_def?
           | _ -> neededOp? c qid)
      | Import(imp_sc_tm, im_sp, _, _) ->
         % let _ = writeLine("real?: "^show (im_sp ~= (getBaseSpec()))^" "^anyToString imp_sc_tm) in
        im_sp ~= (getBaseSpec()) && exists? (realElement? c) im_sp.elements
      | Pragma("#translate", mid_str, "#end", pos) -> verbatimPragma? mid_str
      | Pragma _ -> false
      | Type _ -> false
      | TypeDef (qid, _) -> ~(mappedType? c qid) && neededType? c qid
      | Property _ -> false
      | _ -> true

  op numSpecElts (spc: Spec): Nat =
    foldlSpecElements (fn (sum, _) -> sum + 1)  0  spc.elements

  op specInBase? (spc: Spec): Bool =
    let base_size? = numSpecElts(getBaseSpec()) in
    ~(exists? (fn el -> case el of
                        | Import(_, im_spc, _, _) -> numSpecElts im_spc >= base_size?
                        | _ -> false)
        spc.elements)

  op ppImports (c: Context) (elems: SpecElements): List(List Pretty) * List Pretty =
    let imports_from_haskell_morphism = haskellMorphismImports c in
    let explicit_imports =
        mapPartial (fn el ->
		     case el of
		       | Import(imp_sc_tm, im_sp, _, _) | ~c.slicing? || exists? (realElement? c) im_sp.elements ->
                         % let _ = writeLine("imports: "^anyToString imp_sc_tm) in
                         ppImport c imp_sc_tm im_sp
		       | _ -> None)
           elems
    in
    let (explicit_imports1, explicit_imports_names) = unzip explicit_imports in
    let ppImports = map (fn im -> [prConcat [prString "import ", im]])
                      (explicit_imports1 ++ imports_from_haskell_morphism ++ (if "SW_Base" in? explicit_imports_names
                                                                                   || specInBase?(getSpec c)
                                                                              then []
                                                                              else [prString "SW_Base"]))
    in
    let ppExports =
        if c.slicing? && ~(c.top_spec?)
          then mapPartial (fn qid ->
                             let str = opQualifiedIdString c qid in
                             if exists? whiteSpaceChar? str
                               then None
                             else Some(prConcat [ppOpQualifiedId c qid, prSpace]))
                 (exportedOps c (getSpec c))
             ++ mapPartial (fn qid ->
                             let str = opQualifiedIdString c qid in
                             if exists? whiteSpaceChar? str
                               then None
                             else Some(prConcat [ppTyQualifiedId c qid, prString "(..) "]))
                 (exportedTypes c (getSpec c))

          else map (fn im -> prConcat [prString "module ", im])
                 (map prString explicit_imports_names ++ imports_from_haskell_morphism)
    in
    (ppImports, ppExports)

  op haskellMorphismImports (c: Context): List Pretty =
    map prString c.trans_table.thy_imports

  op firstTypeDef (elems:SpecElements): Option QualifiedId =
    case elems of
      | [] -> None
      | (Type    (type_id, _)) :: _ -> Some type_id
      | (TypeDef (type_id, _)) :: _ -> Some type_id
      | _ :: r -> firstTypeDef r

  op  ppImport: Context -> SCTerm -> Spec -> Option (Pretty * String)
  def ppImport c sc_tm spc =
    case uidStringPairForValueOrTerm(getCurrentUID c, Spec spc, sc_tm, c.slicing?, c.top_uid) of
      | None ->
        let _ = writeLine("Unknown:\n"^anyToString sc_tm) in
        Some(prString "<UnknownSpec>", "<UnknownSpec>")
      | Some ((spc_nm, sw_fil_nm, haskell_module_name, haskell_fil_nm), val, uid) ->
        % let _ = writeLine("ppI spc_nm: "^spc_nm^" hmn: "^haskell_module_name) in
        % let _ = case val of Spec spc -> writeLine(printSpecFlat (subtractSpec spc (getBaseSpec()))) | _ -> () in
        case spc_nm of
          | "IsabelleExtensions" -> None
          | _ ->
        let _ = if c.recursive?
	          then
		    if fileOlder?(sw_fil_nm, haskell_fil_nm) || spc = getBaseSpec()
		      then ()
		    else
                      toFile(haskell_fil_nm,
                             showValue(val, false, c.top_spec, c.top_uid, c.slicing?, c.needed_ops, c.needed_types,
                                       c.recursive?, uid, Some haskell_module_name))
		  else ()
	in
        case spc_nm of
          | "Base" -> Some(prString "SW_Base", "SW_Base")
          | _ ->
        let haskell_nm = haskellName haskell_module_name in
        case uidStringPairTermForValue(val, c.slicing?, Some c.top_uid) of
          | Some (_, _, sc_tm) | useQualifiedNames? && some?(findSpecQualifier sc_tm) ->  % ???
            let Some qualifier = findSpecQualifier sc_tm in
            Some(prConcat ([prString "qualified ", prString haskell_nm]
                             ++ (if qualifier = haskell_nm then []
                                 else [prString " as ", prString qualifier])),
                 qualifier)
          | _ -> Some(prString haskell_nm, haskell_nm)

  op  ppSpecElements: Context -> Spec -> SpecElements -> Pretty
  def ppSpecElements c spc elems =
    let
      %op  ppSpecElementsAux: Context -> Spec -> SpecElements -> List Pretty
      def aux c spc r_elems =
	case r_elems of
	  | [] -> []
	  | el :: (rst as (Pragma prag) :: _) | unnamedPragma? prag ->
	    let pretty1 = ppSpecElement c spc el (Some prag) elems in
	    let prettyr = aux c spc rst in
	    if pretty1 = prEmpty
	      then prettyr
	      else pretty1::prettyr
	  | el :: rst ->
	    let pretty1 = ppSpecElement c spc el None elems in
	    let prettyr = aux c spc rst in
	    if pretty1 = prEmpty
	      then prettyr
	      else pretty1::prettyr
    in
    prLines 0 (aux c spc elems)

  op  normalizeSpecElements: SpecElements -> SpecElements
  def normalizeSpecElements elts =
    case elts of
      | [] -> []
      | (Op (qid1, false, a)) :: (OpDef (qid2, 0, _, _)) :: rst | qid1 = qid2 ->
        Cons(Op(qid1, true, a), normalizeSpecElements rst)
      | x::rst -> x :: normalizeSpecElements rst

 def findPragmaInstance(qid_str: String, elts: SpecElements): Option String =
   let result =
         case elts of
          | [] -> None
          | el::rst ->
            (case el of
               | Pragma("#translate", prag_str, "#end", _) ->
                 (let line1 = case search("\n", prag_str) of
                                | None -> prag_str
                                | Some n -> subFromTo(prag_str, 0, n)
                  in
                  case removeEmpty(splitStringAt(line1, " ")) of
                    | pragma_kind :: "-instance" :: _ :: type_str :: _
                      | (pragma_kind = "Haskell" \_or pragma_kind = "haskell") && type_str = qid_str ->
                      Some prag_str
                    | _ -> findPragmaInstance(qid_str, rst))
               | _ -> findPragmaInstance(qid_str, rst))
   in
   % let _ = writeLine("returned: "^anyToString result) in
   result

  op newtypeConstructorName (c: Context) (qid: QualifiedId): String =
    "Make"^qidToHaskellString c qid true

 op extractTypeClassIn(prag): Option TypeClassInfo =
    case search("\n",prag) of
      | None -> None
      | Some n ->
    let line1 = subFromTo(prag,0,n) in
    let def_lines = splitStringAt(subFromTo(prag,n,length prag), "\n") in
    case removeEmpty(splitStringAt(line1," ")) of
      | _ :: _ :: class_nm :: qid_str :: _ ->
        let instance_prs = mapPartial (fn line ->
                                       case splitStringAt(removeWhiteSpace line, "->") of
                                         | sw_str :: haskell_str :: _ ->
                                           Some(case splitStringAt(sw_str, ".") of
                                                  | [q,id] -> Qualified(q,id)
                                                  | _ -> mkUnQualifiedId sw_str,
                                                haskell_str)
                                         | _ -> None)
                             def_lines
        in
        Some {type_qid = parseQualifiedId qid_str,
              class_id = class_nm,
              instance_ops = instance_prs}
      | _ -> None

  op coercionsFromTypeClassPragmas (c: Context) (spc: Spec): TypeCoercionTable * Context =
    foldlSpecElements (fn ((tct, c), el) ->
                         case el of
                           | Pragma("#translate", prag_str, "#end", _) ->
                             (let line1 = case search("\n", prag_str) of
                                | None -> prag_str
                                | Some n -> subFromTo(prag_str, 0, n)
                              in
                              case removeEmpty(splitStringAt(line1, " ")) of
                                | pragma_kind :: "-instance" :: _ :: _ :: _
                                    | (pragma_kind = "Haskell" \_or pragma_kind = "haskell") ->
                                  (case extractTypeClassIn prag_str of
                                   | Some {type_qid,
                                           class_id,
                                           instance_ops} ->
                                     (case AnnSpec.findTheType(spc, type_qid) of
                                        | Some info ->
                                          let (ty_vars, superty) = unpackType info.dfn in
                                          let subty = mkBase(type_qid, map mkTyVar ty_vars) in
                                          let constructor_nm = newtypeConstructorName c type_qid in
                                          let c = addConstructorTranslation(c, mkUnQualifiedId constructor_nm, constructor_nm) in
                                          let coerce_info = {subtype = type_qid,
                                                             supertype = superty,
                                                             coerceToSuper =
                                                               let x = ("x", superty) in
                                                               mkLambda(mkEmbedPat(mkUnQualifiedId constructor_nm,
                                                                                   Some(mkVarPat x), subty), mkVar x),
                                                             coerceToSub   = mkEmbed1(mkUnQualifiedId constructor_nm,
                                                                                      mkArrow(superty, subty)),
                                                             overloadedOps = []}
                                          in
                                          (coerce_info :: tct, c)
                                        | None -> (warn("Instance pragma ignored for undefined type: "^printQualifiedId type_qid);
                                                   (tct, c)))
                                   | None -> (tct, c))
                                | _ -> (tct, c))
                           | _ -> (tct, c))
      ([], c) spc.elements


  op findTypeClassInfo (qid: QualifiedId) (elems: SpecElements): Option TypeClassInfo =
    case findPragmaInstance(printQualifiedId qid, elems) of
      | None -> None
      | Some prag -> extractTypeClassIn prag
 
  op addCoercionsForNewtype(dfn: MSTerm, type_qid_constrs: List(QualifiedId * String), spc: Spec): MSTerm =
    let def addCoercion(tm, d_ty) =
          let u_ty = inferType(spc, tm) in
          % let _ = writeLine(printTerm tm^":\n"^printType u_ty ^"\n-> " ^ printType d_ty^"\n\n") in
          let new_tm =
              case tm of
                | Apply (t1, t2, pos) ->
                  let fn_ty = inferType(spc, t1) in
                  % let _ = writeLine("acfn dom: "^printType fn_ty) in
                  (case arrowOpt(spc, fn_ty) of
                   | None -> tm
                   | Some(dom, _) ->
                     Apply(addCoercion(t1, mkArrow(dom, d_ty)), addCoercion(t2, dom), pos))
                | Record (row, pos) ->
                  let srts = map (project 2) (product (spc, d_ty)) in
                  Record(map (fn (f_ty, (id, tmi)) -> (id, addCoercion(tmi, f_ty)))
                           (zip(srts, row)), pos)
                | Bind (bdr, vs, bod, pos) -> Bind (bdr, vs, addCoercion(bod, boolType), pos)
                | The  (var,  bod, pos) -> The  (var, addCoercion(bod, boolType), pos)
                | Let (decls, bdy, pos) ->
                  Let (map (fn (pat, trm) -> (pat, addCoercion(trm, patternType pat))) decls,
                       addCoercion(bdy, d_ty),
                       pos) 
                | LetRec (decls, bdy, pos) ->
                  LetRec (map (fn ((pat, lr_ty), trm) -> ((pat, lr_ty), addCoercion(trm, lr_ty))) decls,
                          addCoercion(bdy, d_ty),
                          pos)
                | Lambda (match, pos) ->
                  let ran = range(spc, d_ty) in
                  Lambda (map (fn (pat, condn, bod) ->
                                 (pat, addCoercion(condn, boolType), addCoercion(bod, ran)))
                            match, pos)
                | IfThenElse (t1, t2, t3, pos) ->
                  IfThenElse(addCoercion(t1, boolType), addCoercion(t2, d_ty), addCoercion(t3, d_ty), pos)
                | Seq (terms, pos) ->
                  let pre_trms = butLast terms in
                  let lst_trm  =    last terms in
                  Seq (map (fn trm -> addCoercion(trm, mkProduct [])) pre_trms ++ [addCoercion(lst_trm, d_ty)], pos) 
                | TypedTerm (trm, srt, pos) -> TypedTerm(addCoercion(trm, srt), srt, pos)
                | _ -> tm
          in
          case (d_ty, u_ty) of
            | (Base(d_qid, _, _), _) | exists? (fn (qid, _) -> qid = d_qid) type_qid_constrs && ~(embed? Base u_ty) ->
              let Some(_, newtypeConstructorNmID) = findLeftmost (fn (qid, _) -> qid = d_qid) type_qid_constrs in
              mkApply(mkEmbed1(mkUnQualifiedId newtypeConstructorNmID, mkArrow(u_ty, d_ty)), new_tm)
            | (_, Base(u_qid, _, _)) | exists? (fn (qid, _) -> qid = u_qid) type_qid_constrs && ~(embed? Base d_ty) ->
              let Some(_, newtypeConstructorNmID) = findLeftmost (fn (qid, _) -> qid = u_qid) type_qid_constrs in
              let x = ("x", d_ty) in
              MS.mkLet([(mkEmbedPat(mkUnQualifiedId newtypeConstructorNmID, Some(mkVarPat x), u_ty), new_tm)], mkVar x)
            | _ -> new_tm
    in
    let (tvs, ty, term) = unpackFirstTerm(dfn) in
    let new_term = addCoercion(term, ty) in
    maybePiTerm(tvs, TypedTerm(new_term, ty, noPos))
    
  op  ppSpecElement: Context -> Spec -> SpecElement -> Option Pragma
                    -> SpecElements -> Pretty
  def ppSpecElement c spc elem opt_prag elems =
    case elem of
      | Import (_, im_sp, im_elements, _) -> prEmpty
      | Op (qid as Qualified(_, nm), def?, _) | neededOp? c qid ->
	(case AnnSpec.findTheOp(spc, qid) of
	   | Some {names, fixity, dfn, fullyQualified?=_} ->
	     ppOpInfo c true def? elems opt_prag
               names fixity 0 dfn  % TODO: change  op_with_def?  to  def? -- no one looks at it??
	   | _ -> 
	     let _  = toScreen("\nInternal error: Missing op: "
				 ^ printQualifiedId qid ^ "\n") in
	     prString "<Undefined Op>")
      | OpDef(qid as Qualified(_, nm), refine_num, _, _) | neededOp? c qid ->
	(case AnnSpec.findTheOp(spc, qid) of
	   | Some {names, fixity, dfn, fullyQualified?=_} ->
	     ppOpInfo c (refine_num > 0) true elems opt_prag names fixity refine_num dfn
	   | _ -> 
	     let _  = toScreen("\nInternal error: Missing op: "
				 ^ printQualifiedId qid ^ "\n") in
	     prString "<Undefined Op>")
      | Type (qid, _) | neededType? c qid ->
	(case AnnSpec.findTheType(spc, qid) of
	   | Some {names, dfn} -> ppTypeInfo c false elems opt_prag (names, dfn) None
	   | _ -> 
	     let _  = toScreen("\nInternal error: Missing type: "
				 ^ printQualifiedId qid ^ "\n") in
	     prString "<Undefined Type>")
      | TypeDef (qid, _) | neededType? c qid ->
	(case AnnSpec.findTheType(spc, qid) of
	   | Some {names, dfn} -> ppTypeInfo c true elems opt_prag (names, dfn) (findTypeClassInfo qid elems)
	   | _ -> 
	     let _  = toScreen("\nInternal error: Missing type: "
				 ^ printQualifiedId qid ^ "\n") in
	     prString "<Undefined Type>")
      | Pragma("#translate", mid_str, "#end", pos) | verbatimPragma? mid_str ->
        let verbatim_str = case search("\n", mid_str) of
                             | None -> ""
                             | Some n -> specwareToHaskellString(subFromTo(mid_str, n, length mid_str))
        in
        prLines 0 [prString verbatim_str]
	   
      | Comment (str, _) ->
	prConcat [prString "{-",
		  prString str,
		  prString "-}"]
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
            

 op specwareToHaskellString(s: String): String =
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
   subFromTo(s, 0, i+1) ^ "<" ^ subFromTo(s, i+2, j+1) ^ ">" ^ specwareToHaskellString(subFromTo(s, j+1, len))

  op controlPragmaString(s: String): Option(List String) =
    let line1 = case search("\n", s) of
                  | None -> s
                  | Some n -> subFromTo(s, 0, n)
    in
    case removeEmpty(splitStringAt(line1, " ")) of
     | "Haskell"::str::rst | length str > 1 && str@0 = #- && str@1 ~= #> && str ~= strictIdString ->
       Some(str::rst)
     | _ -> None

 op controlPragma?(s: String): Bool =
   embed? Some (controlPragmaString s)

 op namedPragma?(p: Pragma): Bool =
   let (_, s, _, _) = p in
   let line1 = case search("\n", s) of
                 | None -> s
                 | Some n -> subFromTo(s, 0, n)
   in
   case removeEmpty(splitStringAt(line1, " ")) of
    | pragma_kind::name?::r | pragma_kind = "Haskell" \_or pragma_kind = "haskell" ->
      ~(name? = "fa"
          \_or name?@0 in? [#(, #[, #\\, #", #-])  % #" #]
    | _ -> false

 op unnamedPragma?(p: Pragma): Bool =
   ~(namedPragma? p || controlPragma? p.2)

 op verbatimIdString: String = "-verbatim"

 op verbatimPragma?(s: String): Bool =
   case controlPragmaString s of
     | Some(str::_) -> str = verbatimIdString
     | _ -> false

 op strictIdString: String = "-strict"

 op strictPragma?(p?: Option Pragma): Bool =
   case p? of
     | None -> false
     | Some(_, s, _, _) -> strictIdString in? splitStringAt(s, " ")

 op headerIdString: String = "-header"

 op headerPragma?(s: String): Bool =
   case controlPragmaString s of
     | Some(str::_) -> str = headerIdString
     | _ -> false

 op ppHeaderPragmas (els: SpecElements): List Prettys =
   mapPartial (fn el ->
               case el of
                 | Pragma("#translate", prag_str, "#end", _) | headerPragma? prag_str ->
                   let header_str =
                       case search("\n", prag_str) of
                         | None -> ""
                         | Some n -> specwareToHaskellString(subFromTo(prag_str, n+1, length prag_str))
                   in
                   Some [prString header_str]
                 | _ -> None)
     els
                              
 op  haskellMorphismPragma: String -> Option(String * List String)
 def haskellMorphismPragma prag =
   case search("\n", prag) of
     | None -> None
     | Some n ->
   let line1 = subFromTo(prag, 0, n) in
   case removeEmpty(splitStringAt(line1, " ")) of
     | "Haskell"::haskellMorphStr::r | haskellMorphStr in?
				      ["ThyMorphism", "Thy_Morphism",  "-morphism",
				       "TheoryMorphism", "Theory_Morphism"] ->
       Some(subFromTo(prag, n, length prag), r)
     | _ -> None


 op findPragmaNamed
      (elts: SpecElements, qid as (Qualified(q, nm)): QualifiedId, opt_prag: Option Pragma, c: Context)
     : Option Pragma =
   % let _ = writeLine("findPragmaNamed: "^printQualifiedId qid^" opt_prag: "^anyToString opt_prag) in
   case findPragmaNamed1(elts, q^"__"^nm) of
     | Some p -> Some p
     | None ->
   case findPragmaNamed1(elts, qidToHaskellString c qid false) of   % Allow Haskell name
     | Some p -> Some p
     | None ->
   %% Try without qualifier
   case findPragmaNamed1(elts, nm) of
     | Some p -> Some p
     | None ->                          % Allow Haskell name
   case findPragmaNamed1(elts, ppIdStr nm false) of
     | Some p -> Some p
     | None -> opt_prag                  

 op  findPragmaNamed1: SpecElements * String -> Option Pragma
 def findPragmaNamed1(elts, nm) =
   % let _ = writeLine("findPragmaNamed1: "^nm) in
   let result =
         case elts of
          | [] -> None
          | el::rst ->
            (case el of
               | Pragma(p_bod as ("#translate", prag_str, "#end", _)) ->
                 (let line1 = case search("\n", prag_str) of
                                | None -> prag_str
                                | Some n -> subFromTo(prag_str, 0, n)
                  in
                  case removeEmpty(splitStringAt(line1, " ")) of
                    | pragma_kind::thm_nm::r
                      | (pragma_kind = "Haskell" \_or pragma_kind = "haskell") && thm_nm = nm ->
                      Some p_bod
                    | _ -> findPragmaNamed1(rst, nm))
               | _ -> findPragmaNamed1(rst, nm))
   in
   % let _ = writeLine("returned: "^anyToString result) in
   result

 op haskellReservedWords: List String = ["class", "data", "default", "deriving", "do", "import",
                                         "infix", "infixr", "infixl",
                                         "instance", "module", "newtype", "type", "where"]
 op disallowedVarNames: List String = ["sum", "**", "map", "filter", "concat", "concatMap", "head", "last", "tail",
                                       "init", "null", "length", "!!", "foldl", "foldl1", "scanl", "scanl1", "foldr", "foldr1",
                                       "scanr", "scanr1", "iterate", "repeat", "replicate", "cycle", "take", "drop", "splitAt",
                                       "takeWhile", "dropWhile", "span", "break", "lines", "words", "unlines", "unwords", "reverse",
                                       "and", "or", "any", "all", "elem", "notElem", "lookup", "sum", "product",
                                       "maximum", "minimum", "zip", "zip3", "zipWith", "zipWith3", "unzip", "unzip3",
                                       "False", "True", "Nothing", "Just", "Left", "Right", "LT", "EQ", "GT", "atanh", "encodeFloat",
                                       "exponent", "significand", "scaleFloat", "isNaN", "isInfinite", "isDenormalized",
                                       "isIEEE", "isNegativeZero", "atan2", ">>=", ">>", "return", "fail", "fmap", "mapM",
                                       "mapM_", "sequence", "sequence_", "=<<", "maybe", "either", "&&", "||", "not",
                                       "otherwise", "subtract", "even", "odd", "gcd", "lcm", "fromIntegral",
                                       "realToFrac", "fst", "snd", "curry", "uncurry", "id", "const", ".", "flip", "$", "until",
                                       "asTypeOf", "error", "undefined", "seq"]

 op directConstructorTypes: List QualifiedId =
   [Qualified("Option", "Option"),
    Qualified("List", "List"),
    Qualified("Compare", "Comparison")]

 op constructorTranslation(c_nm: QualifiedId, c: Context): Option String =
   case specialOpInfo c c_nm of
     | Some(tr_nm, None, false, false, true) | ~(isLowerCase(tr_nm@0)) ->
       Some tr_nm
     | _ -> None

 op addConstructorTranslation(c: Context, c_qid: QualifiedId, c_tg: String): Context =
   let tbl = c.trans_table in
   c << {trans_table = tbl << {op_map = update(tbl.op_map, c_qid,
                                               (c_tg, None, false, false, true))}}

 op ppConstructor(c_qid as Qualified(_, c_nm): QualifiedId, qid: QualifiedId, c: Context): Pretty =
   case constructorTranslation(c_qid, c) of
     | Some tr_c_nm -> prString tr_c_nm
     | None -> prString(if qid in? directConstructorTypes then ppIdStr c_nm true
                         else (typeQualifiedIdStr c qid true) ^ "__" ^ (ppIdStr c_nm (isUpperCase (c_nm@0))))

 op ppConstructorTyped(c_nm: QualifiedId, ty: MSType, c: Context): Pretty =
   case unfoldToBaseNamedType(getSpec c, ty) of
     | Base(qid, _, _) -> ppConstructor(c_nm, qid, c)
     | _ -> fail("Couldn't find coproduct type of constructor "^show c_nm^": \n"^printType ty)

 op ppIdInfo (c: Context) (qids: List QualifiedId): Pretty =
   let qid = head qids in
   ppOpQualifiedId c qid

op ppTypeIdInfo (c: Context) (qids: List QualifiedId): Pretty =
  let qid = head qids in
   ppTyQualifiedId c qid

op ppOpIdInfo (c: Context) (qids: List QualifiedId): Pretty =
  let qid = head qids in
  ppOpQualifiedId c qid

 op upCase1(nm: String): String =
   if nm = "" then ""
     else show(toUpperCase(nm@0)) ^ subFromTo(nm, 1, length nm)

 op downCase1(nm: String): String =
   if nm = "" then ""
     else show(toLowerCase(nm@0)) ^ subFromTo(nm, 1, length nm)

 op  ensureCase(s: String) (up_case?: Bool): String =
    if up_case? then upCase1 s else downCase1 s

% op printTypeQid (c: Context) (qid: QualifiedId): Pretty =
%   prString(qidToHaskellString c qid true)

 op mkFieldName(nm: String): String = ppIdStr nm false ^ "__fld"
 op mkNamedRecordFieldName (c: Context) (qid: QualifiedId, nm: String): String =
   (typeQualifiedIdStr c qid false)^"__"^(ppIdStr nm (isUpperCase (nm@0)))

 op derivingString: String = " deriving (Eq, Show)"

 op ppTypeInfo (c: Context) (full?: Bool) (elems: SpecElements) (opt_prag: Option Pragma) (aliases: QualifiedIds, dfn: MSType)
      (tc_info: Option TypeClassInfo): Pretty =
   let mainId = head aliases in
   let opt_prag = findPragmaNamed(elems, mainId, opt_prag, c) in
   let (mainId, no_def?) =
       case specialTypeInfo c mainId of
         | Some(haskell_id, _, _, no_def?) -> (stringToQId haskell_id, no_def?)
         | None -> (mainId, false)
   in
   if no_def? then prEmpty
   else
   let (tvs, ty) = unpackType dfn in
   if unfoldSubtypes? && embed? Base (stripSubtypes(getSpec c, ty))
     then prEmpty
   else
   let aliases = [mainId] in
   if full? \_and (case ty of Any _ -> false | _ -> true)
     then let def ppTyDef ty =
              case ty of
                | CoProduct(taggedTypes, _) ->
                  (let strict? = strictPragma? opt_prag in
                   let def ppTaggedType (qid, optTy) =
                     case optTy of
                       | None -> ppConstructor(qid, mainId, c)
                       | Some ty ->
                         prConcat [ppConstructor(qid, mainId, c), prSpace,
                                   case ty of
                                     | Product(fields as ("1", _)::_, _) ->	% Treat as curried
                                       prConcat(addSeparator prSpace
                                                  (map (fn (_, c_ty) -> ppField c_ty)
                                                     fields))
                                     | _ -> ppField ty]
                      def ppField ty =
                        if strict?
                          then prConcat[prString "!",
                                        enclose? (case ty of
                                                    | Base(_, [], _) -> false
                                                    | TyVar _ -> false
                                                    | _ -> true,
                                                  ppType c CoProduct ty)]
                        else ppType c CoProduct ty
                   in
                   prLinearCat 2
                     [[prString "data ",
                       ppTypeIdInfo c aliases,
                       ppTyVars tvs],
                      [prString " = ", prSep (-2) blockAll (prString "| ") (map ppTaggedType taggedTypes)],
                      [prString derivingString]])
                | Product (("1", _)::_, _) ->
                  prConcat [prString "type ",
                            ppTyVars tvs,
                            ppTypeIdInfo c aliases,
                            prString " = ",
                            ppType c Top ty]
                | Product (fields, _) | length fields > 0 ->
                  prLinearCat 2
                    [[prString "data ",
                     ppTyVars tvs,
                     ppTypeIdInfo c aliases,
                     prString " = ",
                     ppTypeIdInfo c aliases,
                     prString " {",
                     prPostSep 0 blockLinear (prString ", ")
                       (map (fn (fldname, fldty) ->
                               prConcat [prString (mkNamedRecordFieldName c (mainId, fldname)),
                                         prString " :: ",
                                         ppType c Top fldty])
                          fields),
                     prString "}"],
                     [prString derivingString]]
                | Quotient(qty, equiv_rel, _) ->
                  let pp_name = ppTyQualifiedId c mainId in
                  let pp_tyvars = ppTyVars tvs in
                  let pp_constr = prConcat [prString "Make", pp_name] in
                  prLinesCat 0 [[],
                                [prString "newtype ", pp_name, pp_tyvars, prString " = ", pp_constr, prSpace, ppType c Top qty,
                                 prString derivingString],
                                [],
                                [prString "instance "]
                                  ++ (if tvs = [] then [] else [prString "Eq", pp_tyvars, prString " => "])
                                  ++ [prString "Eq (", pp_name, pp_tyvars, prString ") where"],
                                [prString "  ", pp_constr, prString " x == ", pp_constr, prString " y = ",
                                 ppTerm c Top equiv_rel, prString"(x, y)"]]
                | Subtype(s_ty, _, _) -> ppTyDef s_ty
                | Arrow _ -> prBreak 2 [prString "type ", ppTyQualifiedId c mainId, ppTyVars tvs, prString " = ", ppType c Top ty]
                | _ ->
              case tc_info of
                | Some{type_qid, class_id, instance_ops} ->
                  let constructor_nm = newtypeConstructorName c mainId in
                  prLinearCat 2 [[prString "newtype ", ppTyQualifiedId c mainId, ppTyVars tvs, prString " = "],
                                [prString constructor_nm, prSpace, ppType c Apply ty],
                                [prString derivingString]]
                | None -> prEmpty  % prBreak 2 [prString "type ", ppTyQualifiedId c mainId, ppTyVars tvs, prString " = ", ppType c Top ty]
          in
          let pp_def = ppTyDef ty in
          case tc_info of
            | Some{type_qid, class_id, instance_ops} ->
              let constructor_nm = newtypeConstructorName c type_qid in
              prLinesCat 0 ([[],
                             [pp_def],
                             [],
                             [prString "instance ", prString class_id, prSpace, ppTyQualifiedId c type_qid],
                             [prLines 4 (prString "  where"
                                           :: map (fn (qid, _) ->
                                                     case AnnSpec.findTheOp(getSpec c, qid) of
                                                       | None -> 
                                                         let _  = toScreen("\nInternal error: Missing op: "
                                                                             ^ printQualifiedId qid ^ "\n") in
                                                         prString "<Undefined Op>"
                                                       | Some {names, fixity, dfn, fullyQualified?=_} ->
                                                         let c = c << {newVarCount = Ref 0} in
                                                         let (tvs, ty, term) = unpackFirstTerm(dfn) in
                                                         let term = renameTerm (emptyContext()) term in
                                                         ppFunctionDef c  [qid] term ty None fixity false)
                                                instance_ops)]])
                               
            | None -> pp_def
	    % prBreakCat 2
%	       [[prString "type ",
%		 ppTyVars tvs,
%		 ppTypeIdInfo c aliases,
%		 prString " = "],
%		[ppType c Top ty]]
     else prBreakCat 2                  % ??? Error (not executable)
	    [[prString "type",
	      ppTyVars tvs, prSpace,
	      ppTypeIdInfo c aliases]]

 op  ppTyVars : TyVars -> Pretty
 def ppTyVars tvs =
   case tvs of
     | [] -> prEmpty
     | [tv] -> prConcat [prSpace, prString tv]
     | _ -> prConcat [prSpace,
                      prPostSep 0 blockFill prSpace
		        (map prString tvs)]

 %%% Steps for ops       =>  ||  &&   =  ::   +   *  **, ? apply
 op precNumSteps: List Nat = [13, 14, 15, 20, 23, 25, 27, 30, 35, 1000]
 op convertPrecNum(sw_prec_num: Nat): Nat =
   case leftmostPositionSuchThat (precNumSteps, fn step -> sw_prec_num < step) of
     | Some i -> i 
     | None -> 10

 op convertFixity(fx: Fixity): Fixity =
   case fx of
     | Infix(assoc, prec) -> Infix(assoc, convertPrecNum prec)
     | _ -> fx

 op mkIncTerm(t: MSTerm): MSTerm =
   mkApply(mkInfixOp(Qualified("Integer", "+"),
                     Infix(Left, 25),
                     mkArrow(mkProduct [natType, natType], natType)),
           mkTuple[t, mkNat 1])

 op  defToFunCases: Context -> MSTerm -> MSTerm -> List(MSTerm * Option MSTerm * MSTerm)
 def defToFunCases c op_tm bod =
   let
     def aux(hd, bod) =
       % let _ = writeLine("dtfc: "^printTerm hd^" = "^printTerm bod) in
       case bod of
         | Lambda ([(VarPat (v as (nm, ty), _), _, term)], a) ->
           aux(Apply(hd, mkVar v, a), term)
         | Lambda ([(pattern, _, term)], a) ->
           (case patToTerm (pattern, "",  c) of
              | Some pat_tm ->
                aux (Apply(hd, pat_tm, a), term)
              | _ -> [(hd, None, bod)])
         | Apply (Lambda (pats, _), Var(v, _), _) ->
           if exists? (fn v1 -> v = v1) (freeVars hd)
            then let cases =
                     foldl (fn (cases, (pati, _, bodi)) ->
                            let (pati, condn?) = case pati of
                                                   | RestrictedPat(p, condn, _) -> (p, Some condn)
                                                   | _ -> (pati, None)
                            in
                            case patToTerm(pati, "",  c) of
                              | Some pati_tm ->
                                let sbst = [(v, pati_tm)] in
                                let (s_bodi, condn?) =
                                    if hasVarNameConflict?(pati_tm, [v]) then (bodi, condn?)
                                    else (substitute(bodi, sbst),
                                          mapOption (fn condn -> substitute(condn, sbst)) condn?)
                                in
                                let new_cases = aux_case(substitute(hd, sbst), condn?, s_bodi) in
                                (cases ++ new_cases)
                              | _ ->
                                let new_cases = aux_case(hd, condn?, bodi) in
                                (cases ++ new_cases))
                       [] pats
                 in
                 if exists? (fn (_, _, bodi) ->
                               existsSubTerm unkownPatternVar? bodi)
                     cases
                   then [(hd, None, bod)]
                   else cases
            else [(hd, None, bod)]
         | Apply (Lambda (pats, _), arg as Record(var_tms, _), _)
             | tupleFields? var_tms    % ??
               &&  forall? (fn (_, t) -> embed? Var t) var_tms
%                && (case hd of
%                      | Apply(_, param, _) -> equalTerm?(param, arg)
%                      | _ -> false)
           ->
           let def matchPat (p: MSPattern, cnd, bod: MSTerm): Option(MSTerm * MSTerm) =
                 case p of
                   | RecordPat(rpats, _) ->
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
                     let bod_sbst = filter (fn (v, tm) -> ~(hasVarNameConflict?(tm, [v]))) sbst in
                     Some(substitute(hd, sbst), substitute(bod, bod_sbst))
                   | VarPat(v, _) -> Some(hd, substitute(bod, [(v, arg)]))
                   | WildPat _ -> Some(hd, bod)
                   | AliasPat(VarPat(v, _), p2, _) -> matchPat(p2, cnd, substitute(bod, [(v, arg)]))
                   | RestrictedPat(rp, _, _) -> matchPat(rp, cnd, bod)
                   | _ -> None
           in
           let cases = mapPartial matchPat pats in
           if length cases = length pats
             then foldl (fn (cases, (lhs, rhs)) -> cases ++ aux(lhs, rhs)) [] cases
             else [(hd, None, bod)]
         | Let([(pat, Var(v, _))], bod, a) | v in? freeVars hd ->
           (case patToTerm(pat, "",  c) of
              | Some pat_tm ->
                let s_bod = if hasVarNameConflict?(pat_tm, [v]) then bod
                            else substitute(bod, [(v, pat_tm)])
                in
                aux(substitute(hd, [(v, pat_tm)]), s_bod)
              | None -> [(hd, None, bod)])
         | IfThenElse(Apply(Fun(Equals, _, _),
                            Record([("1", vr as Var(v as (vn, s), _)),
                                    ("2", zro as Fun(Nat 0, _, _))], _),
                            _),
                      then_cl, else_cl, _)
             | natType? s \_and inVars?(v, freeVars hd) ->
           let cases1 = aux(substitute(hd, [(v, zro)]), substitute(then_cl, [(v, zro)])) in
           let cases2 = aux(substitute(hd, [(v, mkIncTerm vr)]),
                            simpSubstitute(getSpec c, else_cl, [(v, mkIncTerm vr)]))
           in
           cases1 ++ cases2
         | Apply(Apply(Fun(Choose qid, ty, _),
                       Lambda ([(pat, _, bod)], _), _),
                 Var(v, _), _) | v in? freeVars hd ->
           (case patToTerm(pat, "",  c) of
              | Some pat_tm ->
                let s_bod = if hasVarNameConflict?(pat_tm, [v]) then bod
                            else substitute(bod, [(v, pat_tm)])
                in
                aux(substitute(hd, [(v, mkQuotient(pat_tm, qid, natType))]), s_bod)    % !!! Nattype is wrong but no one cares(?)
              | None -> [(hd, None, bod)])           
         | _ -> [(hd, None, bod)]
     def aux_case(hd, condn?, bod: MSTerm) =
       case condn? of
         | None -> aux(hd, bod)
         | Some _ -> [(hd, condn?, bod)]
     def fix_vars(hd, condn?, bod) =
       case hd of
         | Fun(_, ty, _) ->
           (case arrowOpt(getSpec c, ty) of
              | Some(dom, _) ->
                let new_v = mkVar("x__a", dom) in
                (mkApply(hd, new_v), condn?, mkApply(bod, new_v))
              %% Shouldn't happen?
              | None -> (hd, condn?, bod))
         | _ ->
       let fvs = freeVars hd ++ freeVars bod in
       let rename_fvs = filter (fn (nm, _) -> nm in? disallowedVarNames) fvs in
       if rename_fvs = [] then (hd, condn?, bod)
         else let sb = map (fn (v as (nm, ty)) -> (v, mkVar(nm^"_v", ty))) rename_fvs in
              let bod_sb = filter (fn (v, tm) -> ~(hasVarNameConflict?(tm, [v]))) sb in
              (substitute(hd, sb), mapOption (fn condn -> substitute(condn, sb)) condn?,
               substitute(bod, bod_sb))
   in
   case bod of
     | Lambda ([(RestrictedPat(rpat, _, _), condn, tm)], a) ->
       defToFunCases c op_tm (Lambda ([(rpat, condn, tm)], a))
     | _ ->
   let cases =
         case bod of
           | Lambda ([(recd as (RecordPat (prs as (("1", _)::_), _)), _, tm)], a)
               | varOrTuplePattern? recd ->
             let Some arg = patToTerm(recd, "", c) in
             let cases = aux(Apply(op_tm, arg, a), tm) in
             cases
           | _ -> aux(op_tm, bod)
   in
   % let _ = app (fn (x, y) -> writeLine(printTerm x^" -> "^printTerm y)) cases in
   %let _ = writeLine(" = "^show (length cases)^", "^show tuple?) in
   (map fix_vars cases)

 op processOptPrag(opt_prag: Option Pragma): List (List Pretty) * Bool =
   case opt_prag of
     | Some(beg_str, mid_str, end_str, pos) ->
       let len = length mid_str in
       (case search("\n", mid_str) of
          | None -> ([], false)
          | Some n ->
            let prf_str = stripExcessWhiteSpace(subFromTo(mid_str, n+1, len)) in
            ([[prString(specwareToHaskellString prf_str)]],
             proofEndsWithTerminator? prf_str))
     | _ -> ([], false)

op ppLambdaDef (c: Context) (strict?: Bool) (hd: MSTerm) (dfn: MSTerm): Pretty =
  let cases = defToFunCases c hd dfn in
  let pp_cases = map (fn (lhs, condn?, rhs) ->
                        case condn? of
                        | None ->
                          % let _ = writeLine(printTerm lhs^" = "^printTerm rhs) in
                          prBreakCat 2 [[ppTerm c Top lhs, string " = "], [ppTerm (c << {generateStrict? = strict?}) Top rhs]]
                        | Some condn ->
                          prBreak 2 [prConcat[ppTerm c Top lhs, prSpace],
                                     let c = c << {generateStrict? = strict?} in
                                     prBreakCat 1 [[prString "| ", ppTerm c Top condn], [prString " = ", ppTerm c Top rhs]]])
  
                   cases
  in
  prLines (0) pp_cases


op ppFunctionDef (c: Context) (aliases: Aliases) (dfn: MSTerm) (ty: MSType) (opt_prag: Option Pragma) (fixity: Fixity) (strict?: Bool)
    : Pretty =
  let mainId = head aliases in
  let op_tm = mkFun (Op (mainId, fixity), ty) in
  ppLambdaDef c strict? op_tm dfn
 
op  ppOpInfo :  Context -> Bool -> Bool -> SpecElements -> Option Pragma
                  -> Aliases -> Fixity -> Nat -> MSTerm
                  -> Pretty
def ppOpInfo c decl? def? elems opt_prag aliases sw_fixity refine_num dfn =
  %% Doesn't handle multi aliases correctly
  let c = c << {newVarCount = Ref 0} in
  let mainId0 = head aliases in
  % let _ = writeLine("Processing "^printQualifiedId mainId) in
  let opt_prag = findPragmaNamed(elems, mainId0, opt_prag, c) in
  let strict? = strictPragma? opt_prag in
  let (specialOpInfo?, no_def?, mainId, fixity) =
      case specialOpInfo c mainId0 of
        | Some (haskell_id, infix?, _, _, no_def?) ->
          (true, no_def?, stringToQId(haskell_id),
           case infix? of
             | Some pr -> Infix pr
             | None -> convertFixity sw_fixity)
        | _ -> (false, false, mainId0, convertFixity sw_fixity)
  in
  if no_def?
    then prEmpty
  else
  let (tvs, ty, term) = unpackFirstTerm(dfn) in
  let term = renameTerm (emptyContext()) term in
  let aliases = [mainId] in
  let decl_list = 
        if decl?
          then [[ppOpIdInfo c aliases,
                 prString " :: ",
                 (case getEqualityTyVars c mainId0 of
                    | [] -> prEmpty
                    | eq_tvs as (tv1 :: tvr) ->
                      prConcat[if tvr = []
                                 then prConcat [prString "Eq ", prString tv1]
                                 else enclose?(true,
                                               prSep 0 blockNone (prString ", ")
                                                 (map (fn tv -> prConcat [prString "Eq ", prString tv])
                                                    eq_tvs)),
                               prString " => "]),
                 (case fixity of
                    | Infix(assoc, prec) -> ppInfixType c ty   % Infix operators are curried in Haskell
                    | _ -> ppType c Top ty)]]
             ++ (case fixity of
                   | Infix(assoc, prec) ->
                     [[case assoc of
                        | Left     -> prString "infixl "
                        | Right    -> prString "infixr "
                        | NotAssoc -> prString "infix ",
                       prString (show prec),
                       prSpace,
                       ppInfixId c mainId]]
                   | _ -> [])
           else []
  in
  % let infix? = case fixity of Infix _ -> true | _ -> false in
  let def_list = if def? then [[ppFunctionDef c aliases term ty opt_prag sw_fixity strict?]] else []
  in prLinesCat 0 ([[]] ++ decl_list ++ def_list)

 op ensureNotCurried(lhs: MSTerm, rhs: MSTerm): MSTerm * MSTerm =
   case lhs of
     | Apply(h as Apply _, Var(v, _), _) ->
       ensureNotCurried(h, mkLambda(mkVarPat v, rhs))
     | _ -> (lhs, rhs)

 %op  Utilities.patternToTerm : MSPattern -> Option MSTerm
 %op  Utilities.substitute    : MSTerm * List (Var * MSTerm) -> MSTerm
 %op  Utilities.freeVars      : MSTerm -> List Var

op patToTerm(pat: MSPattern, ext: String, c: Context): Option MSTerm = 
    case pat
      of EmbedPat(con, None, ty, a) -> 
         Some(Fun(Embed(con, false), ty, a))
       | EmbedPat(con, Some p, ty, a) -> 
         (case patToTerm(p, ext, c)
            of None -> None
             | Some (trm) -> 
               let ty1 = patternType p in
               Some (Apply(Fun(Embed(con, true), Arrow(ty1, ty, a), a), trm, a)))
       | RecordPat(fields, a) -> 
         let
            def loop(new, old, i) = 
                case new
                  of [] -> Some(Record(reverse old, a))
                   | (l, p)::new -> 
                case patToTerm(p, ext^(show i), c)
                  of None -> None
                   | Some(trm) -> 
                     loop(new, Cons((l, trm), old), i+1)
         in
         loop(fields, [], 0)
       | NatPat(i, _) -> Some(mkNat i)
       | BoolPat(b, _) -> Some(mkBool b)
       | StringPat(s, _) -> Some(mkString s)
       | CharPat(c, _) -> Some(mkChar c)
       | VarPat((v, ty), a) -> Some(Var((v, ty), a))
         %% Not valid Specware but seems to work for our purposes here except we need to check this doesn't end up
         %% on rhs of a definition
       | WildPat(ty, a) -> Some(Var(("_", ty), a))   
       | QuotientPat(qpat, qid, tys, pos)  ->
         (case patToTerm(qpat, ext, c) of
            | None -> None
            | Some tm -> Some(mkQuotient(tm, qid, mkBase(qid, tys))))
       | RestrictedPat(pat, cond, _)  ->
         patToTerm(pat, ext, c)		% cond ??
       | AliasPat(p1, p2, _) -> 
         (case patToTerm(p2, ext, c) 
            of None -> patToTerm(p1, ext, c)
             | Some(trm2) ->
          case patToTerm(p1, ext, c) of
             | None -> Some trm2
             | Some trm1 ->
               let ty = inferType(getSpec c, trm1) in
               Some(mkApply(mkInfixOp(mkUnQualifiedId "@", Infix(Left, 50),
                                      mkArrow(mkProduct[ty, ty], ty)),
                            mkTuple[trm1, trm2])))

 op unkownPatternVar?(t: MSTerm): Bool =
   case t of
     | Var(("_", _), _) -> true
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
           | (Apply(x1, _, _), Apply(x2, _, _)) -> sameHead?(x1, x2)
           | _ -> false)

 op nonPrimitiveArg?(tm1: MSTerm, tm2: MSTerm): Bool =
   case tm1 of
     | Apply(Fun(Embed _, _, _), arg, _) ->
       ~(termIn?(tm2, MS.termToList arg))
     | _ -> false

 op hasNonPrimitiveArg?(tm1: MSTerm, tm2: MSTerm): Bool =
   case (tm1, tm2) of
     | (Apply(x1, y1, _), Apply(x2, y2, _)) ->
       nonPrimitiveArg?(y1, y2) || hasNonPrimitiveArg?(x1, x2)
     | _ -> false

 op nonPrimitiveCall? (hd: MSTerm) (tm: MSTerm): Bool =
   sameHead?(hd, tm) && hasNonPrimitiveArg?(hd, tm)

 %% Only concerned with curried calls
 op recursiveCallsNotPrimitive?(hd: MSTerm, bod: MSTerm): Bool =
   existsSubTerm (nonPrimitiveCall? hd) bod

 op patternLambda?(v_pos: Position, lam_pos: Position): Bool =
   %% an explicit lambda will have beginning of variable close to beginning of lambda expr
   false   %usePosInfoForDefAnalysis?
     => (case (v_pos, lam_pos) of
           | (File(_, (_, _, v_byte), _), File(_, (_, _, lam_byte), _)) ->
             v_byte - lam_byte > 4
           | _ -> true)

 %% Ops that are not polymorphic in Specware but are mapped to polymorphic ops in Haskell
 op haskellOverloadedOps: List String = ["**", "modF", "divF"]

 op filterConstrainedVars(c: Context, t: MSTerm, vs: MSVars): MSVars =
   let def removeArgs(vs: MSVars, args: MSTerms, bound_vars: MSVars): MSVars =
         % let _ = writeLine("removeArgs: "^anyToString (map (fn (x, _) -> x) bound_vars)) in
         % let _ = app (fn t -> writeLine (printTerm t)) args in
         let v_args = mapPartial (fn t ->
                                    case t of
                                      | Var (v, _) | inVars?(v, vs)
                                                   && ~(hasVarNameConflict?(t, bound_vars)) ->
                                        Some v
                                      | _ -> None)
                         args
         in deleteVars(v_args, vs)
       def filterKnown(vs: MSVars, id: String, f: MSTerm, args: MSTerms, bound_vs: MSVars): MSVars =
         % let _ = writeLine("fk "^id^": "^ anyToString (map (fn (x, _) -> x) vs)) in
         if id = "natural?" \_or id in? haskellOverloadedOps 
            \_or exists? (fn ci -> id in? ci.overloadedOps)
                c.coercions
          then vs
         else
         if (termFixity f = Nonfix \_and \_not (overloadedHaskellOp? c f))
            \_or (length(wildFindUnQualified((getSpec c).ops, id)) = 1
                  %% The following is only necessary for base specs
                  && length(wildFindUnQualified((getBaseSpec()).ops, id)) <= 1)
           then removeArgs(vs, args, bound_vs)
           else vs
%         case wildFindUnQualified((getSpec c).ops, id) of
%              | [opinfo] ->
%                (case unpackFirstOpDef opinfo of
%                   | (tvs, _, _) ->     % Could polymorphic operator sometimes be a problem??
%                     removeArgs(vs, args, bound_vs)
%                   | _ -> vs)
%              | _ -> vs
      def fCV(st, vs: MSVars, bound_vs: MSVars): MSVars =
        % let _ = writeLine("fCV: "^printTerm st^"\n"^anyToString (map (fn (x, _) -> x) vs)) in
        let vs = case st of
                   | Apply(f as Fun(Op(Qualified(q, id), _), _, _), arg, _) ->
                     filterKnown(vs, id, f, termList arg, bound_vs)
                   | Apply(Fun(Embed(Qualified(_,id), _), _, _), arg, _) ->
                     if id in? c.overloadedConstructors
                       then vs
                       else removeArgs(vs, termList arg, bound_vs)
                   | Apply(Var(v, _), arg, _) | ~(inVars?(v, vs)) ->
                     removeArgs(vs, termList arg, bound_vs)
                   | _ ->
                 case CurryUtils.getCurryArgs st of
                   | Some(f as Fun(Op(Qualified(q, id), _), _, _), args) ->
                     filterKnown(vs, id, f, args, bound_vs)
                   | _ -> vs
        in
        % let _ = writeLine("fCV 1: "^anyToString (map (fn (x, _) -> x) vs)) in
        let def fCVBV(vs: MSVars, st: MSTerm): MSVars = fCV(st, vs, bound_vs)
            def fCVsBV(vs: MSVars, tms: MSTerms): MSVars = foldl fCVBV vs tms
        in
        case st of
          | Apply     (M, N, _)     -> fCVBV(fCVBV(vs, M), N)
          | Record    (fields, _)   -> foldl (fn (vs, (_, M)) -> fCVBV(vs, M)) vs fields
          | Bind      (_, vars, M, _) -> fCV(M, vs, insertVars(vars, bound_vs))
          | The       (var, M, _)    -> fCV(M, vs, insertVar(var, bound_vs))
          | Let       (decls, N, _) -> let vs = foldl (fn (vs, (_, M)) -> fCVBV(vs, M)) vs decls in
                                       let bound_vs = foldl (fn (bound_vs, (pat, _)) ->
                                                               insertVars(patVars pat, bound_vs))
                                                          bound_vs decls
                                       in
                                       fCV(N, vs, bound_vs)
          | LetRec    (decls, N, _) -> let vs = foldl (fn (vs, (_, M)) -> fCVBV(vs, M)) vs decls in
                                       let bound_vs = foldl (fn (bound_vs, (var, _)) ->
                                                               insertVar(var, bound_vs))
                                                          bound_vs decls
                                       in
                                       fCV(N, vs, bound_vs)
          | Lambda    (rules,    _) -> foldl (fn (vs, (p, _, M)) ->
                                              fCV(M, vs, insertVars(patVars p, bound_vs)))
                                         vs rules
          | IfThenElse(P, M, N,  _) -> fCVBV(fCVBV(fCVBV(vs, P), M), N)
          | Seq       (Ms,       _) -> fCVsBV(vs, Ms)
          | TypedTerm(M,   _,   _) -> fCVBV(vs, M)
          | Pi        (_,   M,   _) -> fCVBV(vs, M)
          | And       (tms, _)      -> fCVsBV(vs, tms)
          | _ -> vs
   in
   fCV(t, vs, [])

 %% Adds explicit typing for first reference of variable
 op addExplicitTypingForVars(t: MSTerm, vs: MSVars): MSTerm * MSVars =
   let def addExpl(t: MSTerm, vs: MSVars, bound_vs: MSVars): MSTerm * MSVars =
         case t of
           | Var(v1 as (_, ty), pos) | inVars?(v1, vs) && ~(hasVarNameConflict?(t, bound_vs)) ->
             (TypedTerm(t, ty, pos), filter (fn v2 -> \_not (equalVar?(v1, v2))) vs)
           | Apply(t1, t2, a) ->
             let (t1, vs) = addExpl(t1, vs, bound_vs) in
             let (t2, vs) = addExpl(t2, vs, bound_vs) in
             (Apply(t1, t2, a), vs)
           | Record(prs, a) ->
             let (prs, vs) = foldl (fn ((prs, vs), (id, st)) ->
                                  let (st, vs) = addExpl(st, vs, bound_vs) in
                                  (Cons((id, st), prs), vs))
                             ([], vs) prs
             in
             (Record(reverse prs, a), vs)
           | Bind(bdr, lvs, st, a) ->
             let (st, vs) = addExpl(st, vs, insertVars(lvs, bound_vs)) in
             (Bind(bdr, lvs, st, a), vs)
           | The(v, st, a) ->
             let (st, vs) = addExpl(st, vs, insertVar(v, bound_vs)) in
             (The(v, st, a), vs)
           | Let(bds, st, a) ->                % Should really look in bds
             let bound_vs = foldl (fn (bound_vs, (pat, _)) ->
                                     insertVars(patVars pat, bound_vs))
                              bound_vs bds
             in
             let (st, vs) = addExpl(st, vs, bound_vs) in
             (Let(bds, st, a), vs)
           | LetRec(bds, st, a) ->
             let bound_vs = foldl (fn (bound_vs, (var, _)) ->
                                     insertVar(var, bound_vs))
                              bound_vs bds
             in
             let (st, vs) = addExpl(st, vs, bound_vs) in
             (LetRec(bds, st, a), vs)
           | IfThenElse(t1, t2, t3, a) ->
             let (t1, vs) = addExpl(t1, vs, bound_vs) in
             let (t2, vs) = addExpl(t2, vs, bound_vs) in
             let (t3, vs) = addExpl(t3, vs, bound_vs) in
             (IfThenElse(t1, t2, t3, a), vs)
           | Lambda(cases, a) ->
             let (cases, vs) = foldl (fn ((result, vs), (p, c, t)) ->
                                       let (t, vs) = addExpl(t, vs, insertVars(patVars p, bound_vs)) in
                                       (result ++ [(p, c, t)], vs))
                                ([], vs) cases
             in
             (Lambda(cases, a), vs)
            %% Probably should put other cases
           | _ -> (t, vs)
    in
    addExpl(t, vs, [])

 %op addExplicitTypingForNumbers(tm: MSTerm): MSTerm =

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

 op proofEndsWithTerminator?(prf: String): Bool =
   let len = length prf in
   testSubseqEqual?("done", prf, 0, len-4)
  \_or testSubseqEqual?("sorry", prf, 0, len-5)
  \_or testSubseqEqual?("qed", prf, 0, len-3)
  \_or lastLineEnds prf

 op  stripExcessWhiteSpace: String -> String
 def stripExcessWhiteSpace s =
   let len = length s in
   if len > 0 \_and s@(len-1) in? [#\s, #\n]
     then stripExcessWhiteSpace(subFromTo(s, 0, len-1))
     else if len > 2 && s@0 = #\s && s@1 = #\s
           then subFromTo(s, 2, len)
           else s

 op endOfFirstLine(s: String): Nat =
   case search("\n", s) of
     | Some n -> n
     | None -> length s


 %% --------------------------------------------------------------------------------
 %% Terms
 %% --------------------------------------------------------------------------------

 op infixFun? (c: Context) (f: MSFun): Option String =
   % let _ = writeLine("infixFun? of "^anyToString f) in
   let result =
         case f of
           | Op(qid, fx?) ->
             (let spc = getSpec c in
               case specialOpInfo c qid of
                | Some(haskell_id, infix?, _, _, _) ->
                  (case infix? of
                     | Some fx -> Some(makeOpName haskell_id)
                     | None -> None)
                | _ ->
               if embed? Infix fx?
                 then Some(makeOperator c qid)
               else
               case AnnSpec.findTheOp(spc, qid) of
                 | Some{names=_, fixity = Infix fx, dfn=_, fullyQualified?=_} ->
                   let main_id = mainId qid in
                   Some(makeOperator c qid)
                 | _ -> None)
           | And       -> Some "&&"
           | Or        -> Some "||"
%%           | Implies   -> Some "=>"
           | Iff       -> Some "=="
           | Equals    -> Some "=="
           | NotEquals -> Some "/="
           | _ -> None
   in
   % let _ = writeLine("is "^anyToString result) in
   result

 op makeOpName(nm: String): String =
   if identifier? nm
     then "`"^downCase1 nm^"`"
     else nm

 op makeOperator (c:Context) (qid as Qualified(_, id): QualifiedId): String =
   let nm = qidToHaskellString c qid false in
   if identifier? nm
     then "`"^nm^"`"
     else nm

 op identifier?(s: String): Bool =
   s ~= "" && isAlpha(s@0)

 op infixOp? (c: Context) (t: MSTerm): Option String =
   case t of
     | Fun(f, _, _) -> infixFun? c f
     | _ -> None

 op nonCaseMatch?(match: MSMatch): Bool =
   case match of
     | (NatPat _, _, _)::_ -> true
     | (CharPat _, _, _)::_ -> true
     | _ -> false

 op charMatch?(match: MSMatch): Bool =
   case match of
     | (CharPat _, _, _)::_ -> true
     | _ -> false

 op mkCoproductPat(ty: MSType, qid: QualifiedId, spc: Spec): MSPattern =
   let Some(_, opt_ty) = findLeftmost (fn (qid1, _) -> qid = qid1) (coproduct(spc, ty)) in
   mkEmbedPat(qid, mapOption mkWildPat opt_ty, ty)

 op strictFuns: List String = ["$!", "monadBind", "monadSeq"]

 op strictFun?(tm: MSTerm): Bool =
   case tm of
     | Fun(Op(Qualified(q, id), _), _, _) -> id in? strictFuns
     | _ -> false

 op [a] hConstantTerm? (t: ATerm a): Bool =
   case t of
     | Lambda _ -> true
     | Fun _    -> true
     | _        -> false

 def ppTerm (c: Context) (parentTerm: ParentTerm) (term: MSTerm): Pretty =
   %let _ = writeLine(printTerm term^": "^anyToString parentTerm) in
   case (isFiniteList term) of
     | Some terms ->
       prConcat [prString "[",
                 prPostSep 0 blockFill (prString ", ") (map (ppTerm c Top) terms),
                 prString "]"]
     | None ->
   let spc = getSpec c in
   let def prApply(term1, term2) =
      case (term1, term2) of
        | (Apply(Fun(Op(qid, _), _, _), t1, _), _) | reversedNonfixOp? c qid ->
          %% Reversed curried op, not infix
          let Some(haskell_id, _, _, reversed, _) = specialOpInfo c qid in
          enclose?(parentTerm ~= Top,
                   prBreak 2 [prString(makeIdentifier haskell_id),
                              prSpace,
                              ppTermEncloseComplex? c Nonfix term2,
                              prSpace,
                              ppTermEncloseComplex? c Nonfix t1])
        | (Apply(Fun(Choose qid, _, _), Lambda ([(p, _, bod)], _), _), _) ->
          enclose?(infix? parentTerm,
                   prLinear 0 [prLinear 0
                                 [prConcat[prString "let ",
                                           prLinear 0 [prConcat [prString "Make", ppTyQualifiedId c qid, prSpace,
                                                                 ppPattern c p,
                                                                 prString " = "],
                                                       ppTerm c Nonfix term2],
                                           prSpace],
                                  prString "in "],
                               ppTerm c parentTerm bod])
        | (Fun(Embed(constr_qid, _), ty, _), Record (("1", _)::_, _)) ->
          let constr_ty = range(spc, ty) in
          if multiArgConstructor?(constr_qid, constr_ty, spc) then
          %% Treat as curried
             prBreak 2 [ppConstructorTyped(constr_qid, constr_ty, c),
                        prSpace,
                        prPostSep 2 blockFill prSpace
                          (map (ppTermEncloseComplex? c Nonfix)
                             (MS.termToList term2))]
          else prConcat [ppConstructorTyped(constr_qid, constr_ty, c),
                         prSpace,
                         ppTerm c Nonfix term2]
        | (Lambda (match, _), _) ->
          enclose?(parentTerm \_noteq Top,
                   prLines 2 [prConcat[prString "case ",
                                       ppTerm c Top term2,
                                       prString " of "],
                              ppMatch c match])
        | (Fun (Project p, ty1, _), _) ->
          ppProjection(p, ty1, term2, parentTerm, c)

%         | (Fun (Op (Qualified("Nat", "natural?"), _), _, a), _) ->  % natural? e \_longrightarrow 0 <= e
%           let term2 = case term2 of
%                         | Apply(Fun(Op(Qualified(q, "int"), _), _, _), x, _) | q = toHaskellQual ->
%                           %% In this case it is known true, but leave it in for now for transparency
%                           x
%                         | _ -> term2
%           in
%           ppTerm c parentTerm (mkAppl(Fun(Op (Qualified("Integer", "<="), Infix(Left, 20)), Any a, a),
%                                       [mkNat 0, term2]))
        | (Fun(Op(qid, Infix _), _, a), term2) | ~(embed? Record term2) ->
          let spc = getSpec c in
          ppTerm c parentTerm
            (case productTypes(spc, inferType (spc, term2)) of
               | [t1, t2] ->
                 MS.mkLet([(MS.mkTuplePat[MS.mkVarPat("x", t1), MS.mkVarPat("y", t2)], term2)],
                          mkAppl(term1, [mkVar("x", t1), mkVar("y", t2)]))
               | _ -> fail("Can't get argument types of infix operator: "^ printTerm term))
        | (Fun(Implies, _, a), term2) ->
          let spc = getSpec c in
          ppTerm c parentTerm
            (case productTypes(spc, inferType (spc, term2)) of
               | [t1, t2] ->
                 MS.mkLet([(MS.mkTuplePat[MS.mkVarPat("x", t1), MS.mkVarPat("y", t2)], term2)],
                          mkAppl(term1, [mkVar("x", t1), mkVar("y", t2)]))
               | _ -> fail("Can't get argument types of infix operator: "^ printTerm term))
        %%  embed? foo x  -->  case x of foo _ -> true | _ -> false
        | (Fun(Embedded id, ty, a), term2) ->
          let spc = getSpec c in
          let term2_ty = inferType(spc, term2) in
          let lam_tm = Lambda([(mkCoproductPat(term2_ty, id, spc), trueTerm, trueTerm),
                               (mkWildPat term2_ty, trueTerm, falseTerm)], a)
          in
          prApply(lam_tm, term2)
        | _ ->
          (case infixOp? c term1 of    % Infix ops are translated uniformly to curried ops
             | Some infix_str ->
               % let _ = writeLine("letize:\n"^printTerm term) in
               enclose?(parentTerm ~= Top,
                        prLinearCat 0 [[prString "let (x, y) = ",
                                        ppTerm c Top term2,
                                        prSpace],
                                       [prString "in x ",
                                        prString infix_str,
                                        prString " y"]])
%                let spc = getSpec c in
%                ppTerm c parentTerm
%                  (case productTypes(spc, inferType (spc, term2)) of
%                     | [t1, t2] ->
%                       MS.mkLet([(MS.mkTuplePat[MS.mkVarPat("x", t1), MS.mkVarPat("y", t2)], term2)],
%                                mkAppl(term1, [mkVar("x", t1), mkVar("y", t2)]))
%                     | _ -> fail("Can't get argument types of infix operator: "^ printTerm term))
             | _ ->
           (case termFixity c term1 of
              | (Some pp_id, _, true, reversed) ->  % op translated to curried
                let terms2 = MS.termToList term2 in
                let terms2 = if reversed then reverse terms2 else terms2 in
                if length terms2 = 1
                  then
                    (let spc = getSpec c in
                     case productOpt(spc, inferType(spc, term2)) of
                       | Some fields ->      % op is not curried
                         let (rec_pat, rec_tm) = patTermVarsForProduct fields in
                         ppTerm c parentTerm (MS.mkLet([(rec_pat, term2)], mkApply(term1, rec_tm)))
                       | None ->
                     case arrowOpt(spc, inferType(spc, term)) of
                       | Some(dom, _) ->     % op is curried
                         % let _ = break("c->c: "^printTerm term) in
                         let new_v = ("cv1", dom) in
                         ppTerm c parentTerm (mkLambda (mkVarPat new_v, mkApply(term, mkVar new_v)))
                       | None -> fail("Can't reverse term: "^printTerm term))
                else
                prBreak 2 [pp_id,
                           prSpace,
                           prPostSep 2 blockFill prSpace
                             (map (ppTermEncloseComplex? c Nonfix) terms2)]
              | (Some pp_id, _, false, true) ->
                (let spc = getSpec c in
                 case arrowOpt(spc, inferType(spc, term)) of
                   | Some(dom, _) ->
                     let new_v = ("cv2", dom) in
                     ppTerm c parentTerm (mkLambda (mkVarPat new_v, mkApply(term, mkVar new_v)))
                   | None -> fail("Can't reverse term: "^printTerm term))
              | _ ->                 
                prBreak 2 [ppTerm c (Infix(Left, 10)) term1,
                           case term2 of
                             | Record (("1", _)::_, _) -> ppTerm c Top term2
                             | _ -> prConcat [prSpace, ppTermEncloseComplex? c Nonfix term2]]))

   in
   % let term = if embed? Let term then renameTerm (empty(), emptyEnv()) term else term in
   case term of
     | Apply(t1, t2, _) | c.generateStrict? && ~(strictFun? t1) && ~(hConstantTerm? t2)->
       let t1_ty = inferType(spc, t1) in
       let t2_ty = inferType(spc, t2) in
       let strict_appl_fn = mkInfixOp(Qualified(toHaskellQual, "$!"),
                                      Infix(Right, 1),
                                      mkArrow(mkProduct[t1_ty, t2_ty], t2_ty))
       in
       let strict_appl = mkAppl(strict_appl_fn, [t1, t2]) in
       % let _ = writeLine("strict: "^printTerm strict_appl) in
       % let c = c << {generateStrict? = false} in
       ppTerm c parentTerm strict_appl
     | Apply (trm1, trm2 as (Record ([("1", t1), ("2", t2)], a)), _) ->
       (case (trm1, t2) of
        | (Fun(Op(qid, _), ty, _), Lambda _) | monadBindQid? c qid ->
          printMonadBind c t1 t2
        | (Fun(RecordMerge, ty, _), Record (fields, _)) ->
          let spc = getSpec c in
          let recd_ty = range(spc, ty) in
          let recd_ty = normalizeType (spc, c.typeNameInfo, false, true, true) recd_ty in
          let recd_ty = unfoldToBaseNamedType(spc, recd_ty) in
          enclose?(parentTerm ~= Top,
                   prBreak 2 [ppTerm c (Infix(Left, 10)) t1,
                              let def ppField (x, y) =
                                     prConcat [prString (case recd_ty of
                                                           | Base(qid, _, _) -> mkNamedRecordFieldName c (qid, x)
                                                           | _ -> mkFieldName x),
                                               prString " = ",
                                               ppTerm c Top y]
                              in
                              prConcat [prString "{",
                                        prPostSep 0 blockLinear (prString ", ") (map ppField fields),
                                        prString "}"]])
        | (Fun(Implies, _, _), _) ->
          ppTerm c parentTerm (MS.mkOr(MS.mkNot t1, t2))
        | _ ->
        let def prInfix (f1, f2, encl?, same?, t1, oper, t2) =
              enclose?(encl?,
                       prLinearCat (if same? then -2 else 2)
                         [[ppTerm c f1 t1, prSpace],
                          [oper, prSpace, ppTerm c f2 t2]])
        in
        let fx = termFixity c trm1 in
        % let _ = writeLine("parentTerm: "^anyToString parentTerm) in
        % let _ = writeLine(printTerm trm1 ^ " " ^printTerm trm2 ^ "\n" ^ anyToString fx^"\n") in
        let (t1, t2) = if fx.4 then (t2, t1) else (t1, t2) in   % Reverse args
        (case (parentTerm, fx) of
           | (_, (None, Nonfix, false, _)) ->
             prApply (trm1, mkTuple[t1, t2])
           | (_, (Some pr_op, Nonfix, curried?, _)) ->
             if ~curried?
               then enclose?(parentTerm ~= Top,
                             prConcat[pr_op,
                                      enclose?(true, prLinearCat 0 [[ppTerm c Top t1, prString ", "],
                                                                    [ppTerm c Top t2]])])
             else
             enclose?(parentTerm ~= Top,
                      prLinearCat 2 [[pr_op, prSpace],
                                     [ppTermEncloseComplex? c Nonfix t1, prSpace,
                                      ppTermEncloseComplex? c Nonfix t2]])
           | (Nonfix, (Some pr_op, Infix (a, p), _, _)) ->
             prInfix (Infix (Left, p), Infix (Right, p), true, false, t1, pr_op, t2)
           | (Top,    (Some pr_op, Infix (a, p), _, _)) ->
             prInfix (Infix (Left, p), Infix (Right, p), false, false, t1, pr_op, t2) 
           | (Infix (a1, p1), (Some pr_op, Infix (a2, p2), _, _)) ->
             if p1 = p2
               then prInfix (Infix (Left, p2), Infix (Right, p2),
                             a1 ~= a2 || a1 = NotAssoc,
                             a1 = a2 && a1 ~= NotAssoc, t1, pr_op, t2)
               else prInfix (Infix (Left, p2), Infix (Right, p2), p1 > p2, false, t1, pr_op, t2)))
     | Apply(term1 as Fun (Not, _, _), term2, _) ->
       enclose?(case parentTerm of
                  | Infix(_, prec) -> prec > 18
                  | _ -> false,
                prApply (term1, term2))
     | Apply (term1, term2, _) -> prApply (term1, term2)
     | ApplyN ([t1, t2], _) -> prApply (t1, t2)
     | ApplyN (t1 :: t2 :: ts, a) -> prApply (ApplyN ([t1, t2], a), ApplyN (ts, a))
     | Record (fields, _) ->
       (case fields of
          | [] -> prString "()"
          | ("1", _) :: _ ->
            let def ppField (_, y) = ppTerm c Top y in
            prConcat [prString "(",
                      prPostSep 0 blockFill (prString ", ") (map ppField fields),
                      prString ")"]
          | _ ->
            let spc = getSpec c in
            let recd_ty = inferType(spc, term) in
            let recd_ty = normalizeType (spc, c.typeNameInfo, false, true, true) recd_ty in
            let recd_ty = unfoldToBaseNamedType(spc, recd_ty) in
            let record_type_qid = case recd_ty of
                                  | Base(qid, _, _) -> Some qid
                                  | _ -> None
            in
            let def ppField (x, y) =
                  prConcat [prString (case record_type_qid of
                                      | Some(qid) -> mkNamedRecordFieldName c (qid, x)
                                      | None -> mkFieldName x),
                            prString " = ",
                            ppTerm c Top y]
            in
            case record_type_qid of
            | Some qid ->
              prConcat [ppTypeQualifiedId c qid,
                        prString " {",
                        prPostSep 0 blockLinear (prString ", ") (map ppField fields),
                        prString "}"]
            | None ->
              let _ = writeLine("ppTerm can't determine name of record:\n"^printType recd_ty) in
              prString "{Can't determine name of record!}")
     | The (var, term, pos) ->    %% Not exec!!
       let _ = warn("Translating a non-executable expression at "^printAll pos) in
       prString("error \"Trying to evaluate a \\\"the\\\" expression.\"")
     | Bind (binder, vars, term, pos) ->  %% Not exec!!
       let _ = warn("Translating a non-executable expression at "^printAll pos) in
       enclose?(case parentTerm of
                  | Infix(_, prec) -> true  % prec > 18
                  | _ -> false,
                prString("error \"Trying to evaluate a"
                           ^ (case binder of
                              | Forall -> " univeral quanitification."
                              | Exists -> "n existential quanitification."
                              | Exists1 -> "n exist1 quanitification.")
                           ^ "\""))
     | Let ([(p, t)], bod, a) | existsPattern? (embed? EmbedPat) p ->
       prApply(Lambda([(p, trueTerm , bod)], a), t)
     | Let (decls, body_term, _) ->
       let def ppDecl (pattern, term) =
             prBreakCat 2 [[ppPattern c pattern, prSpace],
                           [prString "= ", ppTerm c Top term]]
       in
       enclose?(infix? parentTerm,
                prLinear 0 [prLinear 0
                              [prConcat[prString "let ",
                                        prLinear 0 (addSeparator (prString "; ")
                                                      (map ppDecl decls)),
                                        prSpace],
                               prString "in "],
                            ppTerm c parentTerm body_term])
     | LetRec (decls, term, _) ->
       let def ppDecl (v, term) =
             let v_ref = mkVar v in
             % let _ = writeLine("letrec: "^printTerm v_ref^" =\n"^printTerm term) in
             ppLambdaDef c c.generateStrict? v_ref term
%             prBreak 2 [ppVarWithoutType v,
%                        prString " = ",
%                        ppTerm c Top term]
       in
       enclose?(infix? parentTerm,
                prLines 0 [prLines 2
                              [prString "let",
                               prConcat[prLinear 0 (map ppDecl decls), prSpace]],
                           prString "in ",
                           ppTerm c (if infix? parentTerm then Top else parentTerm) term])
     | Var (v, _) -> ppVarWithoutType v
     | Fun (fun, ty, _) -> ppFun c parentTerm fun ty
%      | Lambda ([(_, Fun (Bool true,  _, _), Fun (Bool true,  _, _))], _) ->
%        prString "TRUE"                 % fnx. True
     | Lambda ([(pattern, _, term)], _) ->
       enclose?(parentTerm \_noteq Top,
                prBreakCat 2 [[prString "\\", enclose?(complexPattern? pattern, ppPattern c pattern),
                               prString " -> "],
                              [ppTerm c Top term]])
     | Lambda (match, _) ->
       let dom_ty = patternType (head match).1 in
       let x_v = ("x", dom_ty) in
       ppTerm c parentTerm (mkLambda(mkVarPat x_v, mkApply(term, mkVar x_v)))
     | IfThenElse (pred, term1, term2, _) -> 
       enclose?(infix? parentTerm,
                block (if monadBindTerm? term1 then All else Linear,
                       0, [(0, prLinearCat 0 [[prString "if ", ppTerm c Top pred],
                                                    [prString " then "]]),
                                 (2, ppTerm c Top term1),
                                 (0, prString " else "),
                                 (2, ppTerm c Top term2)]))
     | Seq (terms, _) ->
       %prPostSep 0 blockLinear (prString "; ") (map (ppTerm c Top) terms)
       ppTerm c parentTerm (last terms)
     | TypedTerm (tm, ty, _) ->
       enclose?(true, prBreakCat 0 [[ppTerm c parentTerm tm, prString "::"], [ppType c Top ty]])
     | mystery -> fail ("No match in ppTerm with: '" ^ (anyToString mystery) ^ "'")

 op printMonadBind (c: Context) (f: MSTerm) (cf: MSTerm): Pretty =
   let def extractMonadSteps(f, cf): Prettys =
         case cf of
           | Lambda([(WildPat _, _, term)], _) ->
             ppTerm c Top f :: extractMonadBind(term)
           | Lambda([(pat, _, term)], _) ->
             prBreak 2 [ppPattern c pat, prString " <- ", ppTerm c Top f]
                :: extractMonadBind(term)
           | _ -> []               % shouldn't happen?
       def extractMonadBind(mon_ex) =
         case mon_ex of
           | Apply (Fun(Op(qid, _), ty, _), Record ([("1", t1), ("2", t2)], _), _) | monadBindQid? c qid ->
             extractMonadSteps(t1, t2)
           | _ -> [ppTerm c Top mon_ex]
   in
   let stats = extractMonadSteps(f, cf) in
   prLines 2 ((prString "do") :: stats)

 op monadBindQid? (c: Context) (qid: QualifiedId): Bool =
   case specialOpInfo c qid of
     | Some(s, _, _, _, _) -> s = ">>="
     | None -> false

 op monadBindTerm?(t: MSTerm): Bool =
   case t of
     | Apply (Fun(Op(Qualified(qual, "monadBind"), _), ty, _), _, _)  -> true
     | _ -> false

 op unfoldToBaseNamedType(spc: Spec, ty: MSType): MSType =
   % let _ = writeLine("ufnp: "^printType ty) in
   case ty of
     | Base _ ->
       (case tryUnfoldBase spc ty of
        | Some (uf_ty as Base _) -> unfoldToBaseNamedType(spc, uf_ty)
        | Some (Subtype(sup_ty, _, _)) -> unfoldToBaseNamedType(spc, sup_ty)
        | _ -> ty)
     | Subtype(sup_ty, _, _) -> unfoldToBaseNamedType(spc, sup_ty)
     | _ -> ty

 %op projectorNames: List String = ["fst", "snd", "third", "fourth", "fifth", "sixth", "seventh",
 %                                  "eighth", "ninth", "tenth"]

 op ppProjection (p: String, s: MSType, t2: MSTerm, parentTerm: ParentTerm, c: Context): Pretty =
   let spc = getSpec c in
   case arrowOpt(spc, s) of
     | Some(dom, _) ->
   if isAlpha(p@0)
     then let recd_ty = unfoldToBaseNamedType(spc, dom) in
          prConcat[prString(case recd_ty of
                              | Base(qid, _, _) -> mkNamedRecordFieldName c (qid, p)
                              | _ -> mkFieldName p),
                   prSpace,
                   ppTermEncloseComplex? c Nonfix t2]
   else
   case productOpt(spc, dom) of
     | Some fields ->
   if length fields = 2 && (p = "1" || p = "2")
     then prConcat[prString(if p ="1" then "fst " else "snd "),
                   ppTermEncloseComplex? c Nonfix t2]
   else
   let Some (_, field_ty) = findLeftmost (fn (fld_name, _) -> fld_name = p) fields in
   let result_var = ("px", field_ty) in
   let rec_pats = map (fn (fld_name, fld_ty) ->
                         (fld_name, if fld_name = p then mkVarPat result_var
                                      else mkWildPat fld_ty))
                    fields
   in
   let pat_match_project = MS.mkLet([(mkRecordPat rec_pats, t2)], mkVar result_var) in
   ppTerm c parentTerm pat_match_project
%    if length p > 1 && p ~= "10"
%      then (warn("Can't dereference tuples longer than size 10: use pattern matching (or records");
%            "tooLargeTupleDereferencer")
%    else
%    let projectorNum = stringToNat p - 1 in
%    projectorNames@projectorNum^"_of_"^show arity

 op  ppBinder : Binder -> Pretty
 def ppBinder binder =
   case binder of
     | Forall -> prString "fa"
     | Exists -> prString "ex"
     | Exists1 -> prString "ex1"

 op ppVarStr(nm: String): Pretty =
   if nm in? disallowedVarNames then prString(nm^"__v")
     else prString (ppIdStr nm false)

 op  ppVarWithoutType : MSVar -> Pretty
 def ppVarWithoutType (id, _(* ty *)) =
   ppVarStr id

 op  ppVar : Context -> MSVar -> Pretty
 def ppVar c (id, ty) =
   ppVarStr id
%   prConcat [ppVarStr id,
%             prString ":",
%             ppType c Top ty]

 op  ppMatch : Context -> MSMatch -> Pretty
 def ppMatch c cases =
   let def ppCase (pattern, _, term): Pretty =
         prBreakCat 4 [[ppPattern c pattern, prString " -> "],
                       [ppTerm c Top term]]
   in
   prLines 0 (map ppCase cases)

 op  ppPattern : Context -> MSPattern -> Pretty
 def ppPattern c pattern = 
   case pattern of
     | AliasPat (pat1, pat2, _) -> 
       prBreak 0 [ppPattern c pat1,
                  prString "@",
                  enclose?(true, ppPattern c pat2)]
     | VarPat (v, _) -> ppVarWithoutType v
     | EmbedPat (Qualified(_,"Cons"), Some(RecordPat ([("1", hd), ("2", tl)], _)), _, _) ->
       prBreak 2 [ppPattern c hd, prSpace, prConcat[prString ": ", ppPattern c tl]]
     | EmbedPat (constr, pat, ty, _) ->
       prBreak 0 [ppConstructorTyped (constr, ty, c),
                  case pat of
                    | None -> prEmpty
                    | Some pat ->
                  case pat of
                    %% Print constructors with tuple args curried, unless polymorphic
                    | RecordPat(("1", _)::_, _) | multiArgConstructor?(constr, ty, getSpec c) ->
                      prBreak 2 [prSpace,
                                 prPostSep 2 blockFill prSpace
                                   (map (fn p -> enclose?(case p of
                                                        | EmbedPat(_, Some _, _, _)-> true
                                                        | AliasPat _ -> true
                                                        | _ -> false,
                                                        ppPattern c p))
                                    (patternToList pat))]
                    | _ -> prConcat [prSpace, enclose?(embed? EmbedPat pat,
                                                       ppPattern c pat)]]
     | RecordPat (fields, _) ->
       (case fields of
         | [] -> prString "()"
         | ("1", _)::_ ->
           let def ppField (idstr, pat) = ppPattern c pat in
           prConcat [prString "(",
                     prPostSep 0 blockFill (prString ", ") (map ppField fields),
                     prString ")"]
         | _ ->
           let spc = getSpec c in
           let recd_ty = patternType pattern in
           let recd_ty = normalizeType (spc, c.typeNameInfo, false, true, true) recd_ty in
           let recd_ty = unfoldToBaseNamedType(spc, recd_ty) in
           let record_type_qid = case recd_ty of
                                 | Base(qid, _, _) -> Some qid
                                 | _ -> None
           in
           let def ppField (x, pat) =
                 prConcat [prString (case record_type_qid of
                                      | Some(qid) -> mkNamedRecordFieldName c (qid, x)
                                      | None -> mkFieldName x),
                           prString "=",
                           ppPattern c pat]
           in
           case record_type_qid of
            | Some qid ->
              prConcat [ppTypeQualifiedId c qid,
                        prString " {",
                        prPostSep 0 blockLinear (prString ", ") (map ppField fields),
                        prString "}"]
            | None -> prString "{Only handle top-level records!}")
     | WildPat (ty, _) -> prString "_"
     | StringPat (str, _) -> prString ("\"" ^ normString str ^ "\"")
     | BoolPat (b, _) -> ppBool b
     | CharPat (chr, _) -> prString ("'"^(cShow chr)^"'")
     | NatPat (int, _) -> prString (Nat.show int)      
     | QuotientPat (pat, qid, _, _) -> 
       prBreak 0 [prConcat [prString "Make", ppTyQualifiedId c qid, prSpace],
                  ppPattern c pat]
     | RestrictedPat (pat, term, _) -> 
       prLines 2 [ppPattern c pat,
                  prConcat[prString "| ", ppTerm c Top term]] 
     | TypedPat (pat, ty, _) -> ppPattern c pat
     | mystery -> fail ("No match in ppPattern with: '" ^ (anyToString mystery) ^ "'")

 %% Need parens around them
 op complexPattern?(p: MSPattern): Bool =
   case p of
     | QuotientPat _ -> true
     | EmbedPat(_, Some _, _, _) -> true
     | AliasPat _ -> true
     | RecordPat((fld1, _)::_, _) -> fld1 ~= "1"
     | _ -> false

 op  multiArgConstructor?: QualifiedId * MSType * Spec -> Bool
 def multiArgConstructor?(constrId, ty, spc) =
   case ty of
     | Base(qid, _, _) ->
       (let base_ty = typeDef(qid, spc) in
        case coproductOpt(spc, base_ty) of
          | None -> false
          | Some fields ->
            exists? (fn (id, opt_arg_ty) ->
                       case opt_arg_ty of
                         | Some(Product(("1", _)::_, _)) -> id = constrId
                         | _ -> false)
              fields)
     | _ -> false

 op  typeDef: QualifiedId * Spec -> MSType
 def typeDef(qid, spc) =
   let Some info = AnnSpec.findTheType(spc, qid) in
   firstTypeDefInnerType info

 op  ppBool : Bool -> Pretty
 def ppBool b =
   case b of
     | true -> prString "True"
     | false -> prString "False"

 op etaRuleProduct(tm: MSTerm, fields: List(Id * MSType)): MSTerm =
   let (pat, arg) = patTermVarsForProduct fields in
   mkLambda(pat, mkApply(tm, arg))

 op  ppFun : Context -> ParentTerm -> MSFun -> MSType -> Pretty
 def ppFun c parentTerm fun ty =
   case fun of
     | Not       -> prString "not"
     | And       -> prString "&&"
     | Or        -> prString "||"
     | Implies   -> prString "==>"
     | Iff       -> prString "=="
     | Equals    -> prString "=="
     | NotEquals -> prString "/="
     | Quotient  qid -> prConcat [prString "Make", ppTyQualifiedId c qid]
     | PQuotient _ -> prString "quotient"
     | Choose    _ -> prString "choose"
     | PChoose   _ -> prString "choose"
     | Restrict -> prString "restrict"
     | Relax -> prString "relax"
     %| Op (qid, Nonfix) -> ppOpQualifiedId c qid
     %| Op (qid, Unspecified) -> ppOpQualifiedId c qid
     | Op (qid as Qualified(_, opstr), _) ->
       (case infixFun? c fun of
          | Some infix_str ->
            enclose?(parentTerm ~= Top,
                     prConcat [lengthString(11, "\\(x, y) -> x "),
                               prString infix_str,
                               prString " y"])
          | None ->
        if (qid = Qualified("IntegerAux", "-") || qid = Qualified("Integer", "~"))
          && parentTerm ~= Infix(Left, 10)   % Only true if an application
          then let vt = ("i", intType) in
               ppTerm c parentTerm (mkLambda(mkVarPat vt, mkApply(mkFun(fun, ty), mkVar vt)))
        else
        case specialOpInfo c qid of
          | Some(haskell_id, _, curry?, reversed?, _) ->
            if curry? || reversed?
              then (let spc = getSpec c in
                    case productOpt(spc, domain(spc, ty)) of
                      | Some fields -> ppTerm c parentTerm (etaRuleProduct(mkFun(fun, ty), fields))
                      | None ->
                    case arrowOpt(spc, ty) of
                      | Some(dom, _) ->
                        let new_v = ("cv0", dom) in
                        ppTerm c parentTerm (mkLambda (mkVarPat new_v, mkApply(mkFun(fun, ty), mkVar new_v)))
                      | _ -> prString(makeIdentifier haskell_id))
              else ppOpHaskellId c haskell_id
          | _ -> ppOpQualifiedId c qid)
     | Project id ->
       let (dom, _) = arrow(getSpec c, ty) in
       ppTerm c parentTerm (mkLambda(mkVarPat("tp", dom), mkApply(mkFun(fun, ty), mkVar("tp", dom))))
     | RecordMerge -> prString "<<"
     | Embed (Qualified(_,"Nil"), false) -> prString "[]"
     | Embed (id, b) ->
       (let spc = getSpec c in
        case arrowOpt(spc, ty) of
          | Some(dom, rng) ->
            (if multiArgConstructor?(id, rng, spc)
               then
                 case productOpt(spc, dom) of
                 | Some fields -> ppTerm c parentTerm (etaRuleProduct(mkFun(fun, ty), fields))
                 | None -> ppConstructorTyped(id, rng, c)
               else ppConstructorTyped(id, rng, c))
          | None -> ppConstructorTyped(id, ty, c))
     | Embedded id ->
       let (dom, _) = arrow(getSpec c, ty) in
       ppTerm c parentTerm (mkLambda(mkVarPat("cp", dom), mkApply(mkFun(fun, ty), mkVar("cp", dom))))
     | Select (Qualified(_,id)) -> prConcat [prString "select ", prString id] % obsolete?
     | Nat n -> prString (Nat.show n)
     | Char chr -> prConcat [prString "'",
                             prString (cShow chr),
                             prString "'"]
     | String str -> prString ("\"" ^ normString str ^ "\"")
     | Bool b -> ppBool b
     | OneName (id, fxty) -> prString id
     | TwoNames (id1, id2, fxty) -> ppOpQualifiedId c (Qualified (id1, id2))
     | mystery -> fail ("No match in ppFun with: '" ^ (anyToString mystery) ^ "'")

 op cShow(chr: Char): String =
   case chr of
      | #\n -> "\\n"
      | #\t -> "\\t"
      | _ -> show chr

 op normString(s: String): String =
   %% eols have to be symbolic
   replaceString(s, "\n", "\\n")

 def omittedQualifiers = [toHaskellQual]  % "IntegerAux" "Option" ...?

 op qidToHaskellString (c: Context) (Qualified (qualifier, id): QualifiedId) (upper?: Bool): String =
   let qualifier = if useQualifiedNames? then haskellName qualifier else qualifier in
   if qualifier = UnQualified \_or qualifier in? omittedQualifiers
        \_or (if useQualifiedNames?
              then Some qualifier = c.qualifier?
              else ~(identifier? id))
     then if id in? disallowedVarNames then id ^ (if identifier? id  then "__c" else "!!*")
          else ppIdStr id upper?
   else
     if useQualifiedNames?
       then ppIdStr qualifier true ^ "." ^ ppIdStr id upper?
       else ppIdStr (qualifier ^ "__" ^ id) upper?

 op ppTyQualifiedId (c: Context) (qid as Qualified(_, id): QualifiedId): Pretty =
   let nm = qidToHaskellString c qid true in
   prString(nm)

 op makeIdentifier(nm: String): String =
   if identifier? nm || nm@0 = #(
     then nm
   else "("^nm^")"

 op opQualifiedId0String(c: Context) (qid: QualifiedId): String =
   makeIdentifier(qidToHaskellString c qid false)

 op ppOpQualifiedId0 (c: Context) (qid as Qualified(_, id): QualifiedId): Pretty =
   prString(opQualifiedId0String c qid)

 op qualifiedBy?(s: String, q: String): Bool =
   let len = length q in
   testSubseqEqual?(q^".", s, 0, 0)

 op opQualifiedIdString(c: Context) (qid: QualifiedId): String =
   case specialOpInfo c qid of
     | Some(s, _, _, _, _) ->
       % let _ = writeLine(" -> "^s) in
       (case splitStringAt(s, ".") of
          | [s]    ->  s
          | [q,id] -> opQualifiedId0String c (mkQualifiedId(q,id)))
     | None -> opQualifiedId0String c qid

 op ppOpHaskellId (c: Context) (s: String): Pretty =
   case splitStringAt(s, ".") of
     | [s]    ->  prString s
     | [q,id] -> ppOpQualifiedId c (mkQualifiedId(q,id))

 op ppOpQualifiedId (c: Context) (qid: QualifiedId): Pretty =
   prString(opQualifiedIdString c qid)

 %% May only need ops that can be unary
 op overloadedHaskellOps: List String = ["+", "-", "^", "abs", "min", "max"]

 op overloadedHaskellOp? (c: Context) (f: MSTerm) : Bool =
   case f of
     | Fun(Op(qid, _), _, _) ->
       (case specialOpInfo c qid of
          | Some(s, _, _, _, _) -> s in? overloadedHaskellOps
          | None -> false)
     | _ -> false

 op typeQualifiedIdStr (c: Context) (qid: QualifiedId) (up_case?: Bool): String =
   case specialTypeInfo c qid of
     | Some(s, _, _, _) -> ensureCase s up_case?
     | None -> qidToHaskellString c qid up_case?

 op  ppTypeQualifiedId : Context -> QualifiedId -> Pretty
 def ppTypeQualifiedId c qid =
   case specialTypeInfo c qid of
     | Some(s, _, _, _) -> prString s
     | None -> ppTyQualifiedId c qid

 op  isSimpleType? : MSType -> Bool
 def isSimpleType? ty =
   case ty of
     | Base _ -> true
     | Boolean _ -> true
     | _ -> false

 op  ppInfixType : Context -> MSType -> Pretty
 def ppInfixType c ty =
   case arrowOpt(getSpec c, ty) of
     | Some(dom, rng) ->
       (case productTypes(getSpec c, dom) of
         | [arg1_ty, arg2_ty] ->
           ppType c Top (mkArrow(arg1_ty, mkArrow(arg2_ty, rng)))
         | _ -> ppType c Top ty)
     | _ -> ppType c Top ty

 op unfoldSubtypes?: Bool = true

 op  ppType : Context -> ParentType -> MSType -> Pretty
 def ppType c parent ty =
   % let _ = writeLine("ppType: "^printType ty^" --> "^printType(unfoldToBaseNamedType(getSpec c, ty))) in
   case ty of
     | Base(qid, _, _) | unfoldSubtypes? && ~(mappedType? c qid) && unfoldToBaseNamedType(getSpec c, ty) ~= ty ->
       ppType c parent (unfoldToBaseNamedType(getSpec c, ty))
     | Base (qid, [], _) -> ppTypeQualifiedId c qid
      %% CoProduct only at top level
%     | CoProduct (taggedTypes, _) -> 
%       let def ppTaggedType (id, optTy) =
%       case optTy of
%         | None -> quoteIf(~in_quotes?, id, ppConstructor id)
%         | Some ty ->
%           prConcat [quoteIf(~in_quotes?, id, ppConstructor id), prSpace,
%                     case ty of
%                       | Product(fields as ("1", _)::_, _) ->	% Treat as curried
%                         prConcat(addSeparator prSpace
%                                    (map (fn (_, c_ty) -> ppType c CoProduct in_quotes? c_ty) fields))
%                       | _ -> ppType c CoProduct in_quotes? ty]
%       in
%         enclose?(case parent of
%                    | Product -> true
%                    | CoProduct -> true
%                    | Subtype -> true
%                    | _ -> false,
%                  prSep (-2) blockAll (prString "| ") (map ppTaggedType taggedTypes))
     | Boolean _ -> prString "Bool"  
     | TyVar (tyVar, _) -> prString tyVar
     | MetaTyVar (tyVar, _) -> 
       let ({link, uniqueId, name}) = ! tyVar in
       prString (name ^ (Nat.show uniqueId))

     | Base (Qualified("List", "List"), [ty], _) ->
       prConcat [prString "[",
                 ppType c Top ty,
                 prString "]"]

     | Base (qid, [ty], _) ->
       prBreak 0 [ppTypeQualifiedId c qid,
                  prSpace,
                  ppType c Apply ty]
     | Base (qid, tys, _) ->
       prBreak 0 [ppTypeQualifiedId c qid,
                  prSpace,
                  prPostSep 0 blockFill (prString " ") (map (ppType c Top) tys)]
     | Arrow (ty1, ty2, _) ->
       enclose?(case parent of
                  | Product -> true
                  | ArrowLeft -> true
                  | Subtype -> true
                  | Apply -> true
                  | _ -> false,
                prBreak 0[ppType c ArrowLeft ty1,
                          prString " -> ",
                          ppType c ArrowRight ty2])
     | Product (fields, _) ->
       (case fields of
          | [] -> prString "()"
          | ("1", _)::_ ->
            let def ppField (_, y) = ppType c Product y in
            enclose?(true,
                     prSep 2 blockFill (prString ", ")
                       (map ppField fields))
          | _ ->
            let def ppField (x, y) =
            prLinearCat 2 [[prString (mkFieldName x),
                            prString " :: "],
                           [ppType c Top  y]]
            in
              prBreak 2 [prString "{",
                         prPostSep 0 blockLinear(prString ", ") (map ppField fields),
                         prString "}"])
     | Quotient (ty, term, _) ->
         prBreak 0 [prString "(",
                    ppType c Top ty,
                    prString " \\ ",
                    ppTerm c Top term,
                    prString ")"]
     | Subtype (ty, _, _) -> ppType c parent ty

     | mystery -> fail ("No match in ppType with: '" ^ (anyToString mystery) ^ "'")

op  ppLitString: String -> Pretty
def ppLitString id = prString(IO.formatString1("~S", id))

op  infix?: ParentTerm -> Bool
def infix? parentTerm =
  case parentTerm of
    | Infix _ -> true
    | _ -> false

op  termFixity: Context -> MSTerm -> Option Pretty * Fixity * Bool * Bool
def termFixity c term = 
  case term of
    | Fun (termOp, _, _) -> 
      (case termOp of
         | Op (id, fixity) ->
           (case specialOpInfo c id of
              | Some(haskell_id, fix, curried, reversed, _) ->
                (case fix of
                   | Some f -> (Some(prString(makeOpName haskell_id)), Infix f, curried, reversed)
                   | None ->   (Some(prString(makeIdentifier haskell_id)), Nonfix, curried, reversed))
              | None ->
                case fixity of
                  | Unspecified  -> (None, Nonfix, false, false)
                  | Constructor0 -> (None, Nonfix, false, false)
                  | Constructor1 -> (None, Nonfix, false, false)
                  | Nonfix       -> (None, Nonfix, false, false)
                  | Infix(assoc, precnum) -> (Some(ppInfixId c id), Infix(assoc, convertPrecNum precnum), true, false))
         | And            -> (Some(prString "&&"), Infix (Right, 3), true, false)
         | Or             -> (Some(prString "||"), Infix (Right, 2), true, false)
%%         | Implies        -> (Some(prString "==>"), Infix (Right, 1), true, false) 
         | Iff            -> (Some(prString "=="), Infix (NotAssoc, 4), true, false)
         | Not            -> (Some(prString "~"), Nonfix, false, false) % ???
         | Equals         -> (Some(prString "=="), Infix (NotAssoc, 4), true, false) % was 10 ??
         | NotEquals      -> (Some(prString "/="), Infix (NotAssoc, 4), true, false) % ???
         | Embed(Qualified(_,"Cons"), true) -> (Some(prString ":"), Infix (Right, 5), true, false)
         % | RecordMerge    -> (None, Infix (Left, 25), true, false)  % ???
         | _              -> (None, Nonfix, false, false))
    | _ -> (None, Nonfix, false, false)

op reversedNonfixOp? (c: Context) (qid: QualifiedId): Bool =
  case specialOpInfo c qid of
    | Some(_ , None, _, true, _) -> true
    | _ -> false

op  enclose?: Bool * Pretty -> Pretty
def enclose?(encl? , pp) =
  if encl? then prConcat [prString "(", pp, prString ")"]
    else pp

op ppTermEncloseComplex? (c: Context) (parentTerm: ParentTerm) (term: MSTerm): Pretty =
  let encl? = \_not(isSimpleTerm? term || embed? Record term) in
  enclose?(encl?, ppTerm c (if encl? then Top else parentTerm) term)

def prSpace = prString " "

def ppInfixId (c: Context)(qid: QualifiedId): Pretty = prString (makeOperator c qid)

op infixId(id: String): String =
  let idarray = explode(id) in
  let id = foldr (fn(#\\, id) -> "\\\\"^id   % backslashes must be escaped
                  | (c, id) -> show(c)^id) "" idarray
  in id

op  ppInfixDefId: QualifiedId -> Pretty
def ppInfixDefId(Qualified(_, main_id)) = prString (infixDefId main_id)

op infixDefId(id: String): String =
  let idarray = explode(id) in
  let id = foldr (fn(#\\, id) -> "\\\\"^id   % backslashes must be escaped
                  | (#/, id) -> "'/"^id
                  | (#(, id) -> "'("^id
                  | (#), id) -> "')"^id
                  | (#_, id) -> "'_"^id
                  | (c, id) -> show(c)^id) "" idarray
  in id

op ppIdStr (id: String) (up?: Bool): String =
  let id = replaceString(id, "--", "-^-^") in
  case explode(id) of
    | [] -> "e"
    | [#@] -> ppIdStr "at__1" up?
    | c0 :: r_chars ->
      if c0 = #( then id
      else
      let chars = (if up? then toUpperCase c0 else toLowerCase c0) :: r_chars in
      let chars = if mixedIdStr?(r_chars, c0) then alphaize chars else chars in
      let def att(id, s) = (if id = "" then "e" else id) ^ s
      in
      let id = foldl (fn(id, #?) -> att(id, "_p")
                      | (id, c) -> id ^ show c) "" chars
      in id

op haskellIdChar0?(c: Char): Bool = isAlphaNum c || c = #_
op haskellIdChar? (c: Char): Bool = isAlphaNum c || c = #_ || c = #'

op mixedIdStr?(chrs: List Char, ch1: Char): Bool =
  if haskellIdChar0? ch1
    then ~(forall? haskellIdChar? chrs)
    else exists? haskellIdChar? chrs

op alphaize(chrs: List Char): List Char =
  let def att(id, s) =
        (if id = [] then [#e] else id) ++ explode s
  in
  foldl (fn (id,#?) -> att(id, "_p")
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
          | (id,#`) -> att(id, "_oqt")
          | (id,#:) -> att(id, "_cl")
          | (id,c) -> id ++ [c]) 
    [] chrs

op  isSimpleTerm? : MSTerm -> Bool
def isSimpleTerm? trm =
  case trm of
    | TypedTerm(t, _, _) -> isSimpleTerm? t
    | Var _ -> true
    | Fun _ -> true
    | _ -> false

op  isSimplePattern? : MSPattern -> Bool
def isSimplePattern? trm =
  case trm of
    | VarPat _ -> true
    | WildPat _ -> true
    | EmbedPat(_, None, _, _) -> true
    | StringPat _ -> true
    | BoolPat _ -> true
    | CharPat _ -> true
    | NatPat _ -> true
    | _ -> false

 op  varOrTuplePattern?: MSPattern -> Bool
 def varOrTuplePattern? p =
   case p of
     | VarPat _ -> true
     | RecordPat(prs, _) | tupleFields? prs ->
       forall? (fn (_, p) -> varOrTuplePattern? p) prs
     | RestrictedPat(pat, cond, _) -> varOrTuplePattern? pat
     | WildPat _ -> true
     | _ -> false

 op  varOrRecordPattern?: MSPattern -> Bool
 def varOrRecordPattern? p =
   case p of
     | VarPat _ -> true
     | RecordPat(prs, _) ->
       forall? (fn (_, p) -> varOrRecordPattern? p) prs
     | RestrictedPat(pat, cond, _) -> varOrRecordPattern? pat
     | WildPat _ -> true
     | _ -> false

 op  simpleHead?: MSTerm -> Bool
 def simpleHead? t =
   case t of
     | Apply(_, arg, _) -> varOrTupleTerm? arg
     | _ -> false

 op  varOrTupleTerm?: MSTerm -> Bool
 def varOrTupleTerm? p =
   case p of
     | Var _ -> true
     | Record(prs as (("1", _)::_), _) ->
       forall? (fn (_, p) -> varOrTupleTerm? p) prs
     | _ -> false

 op overloadedConstructors(spc: Spec): List String =
   (foldTypeInfos
      (fn (info, result as (found, overloaded)) ->
         case typeInnerType(info.dfn) of
           | CoProduct(prs, _) ->
             foldl (fn ((found, overloaded), (Qualified(_,id), _)) ->
                      if id in? found
                        then (  found, id::overloaded)
                      else (id::found,     overloaded))
               result prs
           | _ -> result)
     ([], [])
     spc.types).2

op notReallyEqualityOps: QualifiedIds = [Qualified("Option", "some?"), Qualified("Option", "none?")]

op polyEqualityAnalyze(spc: Spec): AQualifierMap TyVars =
  let def foundOp?(qmap, qid) =
        let Qualified(q, id) = qid in
        some?(findAQualifierMap(qmap, q, id))  
      def iterate1(qmap,initial?) =
        foldOpInfos
          (fn (info, qmap) ->
             let qid as Qualified(q, id) = primaryOpName info in
             if foundOp?(qmap, qid) || qid in? notReallyEqualityOps then qmap
             else
             let (tvs,_,defn) = unpackFirstOpDef info in
             if tvs = []
               then qmap   % not polymorphic
             else 
             foldSubTerms (fn (t, qmap) ->
                           case t of
                             | Fun(f, f_ty, _) ->
                               let tvs = freeTyVars f_ty in
                               if tvs ~= []
                                  && (initial? && (f = Equals || f = NotEquals))
                                      || (case f of
                                            | Op(qid, _) -> foundOp?(qmap, qid)
                                            | _ -> false)
                               then 
                                let old_val = case findAQualifierMap(qmap, q, id) of
                                                | Some val -> val
                                                | _ -> []
                                in
                                insertAQualifierMap(qmap, q, id, removeDuplicates(tvs ++ old_val))
                              else qmap
                           | _ -> qmap)
                qmap defn)
          qmap spc.ops
      def iterateUntilNoChange qmap =
        let new_qmap = iterate1(qmap, false) in
        if new_qmap = qmap then qmap
          else iterateUntilNoChange new_qmap
  in
  iterateUntilNoChange(iterate1(emptyAQualifierMap, true))

op getEqualityTyVars (c: Context) (qid: QualifiedId): TyVars =
  let Qualified(q, id) = qid in
  case findAQualifierMap(c.polyEqualityFunInfo, q, id) of
    | None -> []
    | Some tvs -> tvs

endspec
