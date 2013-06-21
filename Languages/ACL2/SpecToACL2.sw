ACL2 qualifying spec

import /Languages/SpecCalculus/AbstractSyntax/Types
import /Languages/MetaSlang/AbstractSyntax/AnnTerm
import /Library/PrettyPrinter/WadlerLindig
% import /Languages/MetaSlang/Specs/Printer
import /Languages/SpecCalculus/Semantics/Value
import /Languages/SpecCalculus/Semantics/Environment
 %import /Languages/SpecCalculus/Semantics/Monad
import /Languages/SpecCalculus/AbstractSyntax/ShowUtils
import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements

type Context = {printTypes?: Bool,
                printPositionInfo?: Bool,
                fileName: String,
                %currentUID: UnitId,
                %uidsSeen: List UnitId,	% Used to avoid infinite recursion because of circularity
                recursive?: Bool,
                showImportedSpecs? : Bool  %Can cause exponential blowup.  Recommend importing /Library/Base/Empty into the spec being shown if you set this to true
                }

op fileNameOfValue (value:Value) : Option String =
  case value of
    | Spec        spc           -> fileNameOfSpec spc
%      | Morph       spec_morphism -> ppMorphism c  spec_morphism
%      | SpecPrism   spec_prism    -> ppPrism     spec_prism     % tentative
%      | SpecInterp  spec_interp   -> ppInterp    spec_interp    % tentative
%      | Diag        spec_diagram  -> ppDiagram  c  spec_diagram
%      | Colimit     spec_colimit  -> ppColimit  c  spec_colimit
%      | Other       other_value   -> ppOtherValue other_value
%      | InProcess                 -> ppString "InProcess"
%      | UnEvaluated _             -> ppString "some unevaluated term"
    | _                         -> None

op fileNameOfSpec (spc:Spec) : Option String =
  case findLeftmost (fn el -> some?(fileNameOfSpecElement(el,spc))) spc.elements of
    | Some el -> fileNameOfSpecElement (el,spc)
    | None -> None

op fileNameOfSpecElement (el : SpecElement, spc : Spec) : Option String =
  case el of
    | Op       (qid, _,       _) -> fileNameOfOpId   (qid, spc)
    | OpDef    (qid, _, _,    _) -> fileNameOfOpId   (qid, spc)
    | Type     (qid,          _) -> fileNameOfTypeId (qid, spc)
    | TypeDef  (qid,          _) -> fileNameOfTypeId (qid, spc)
    | Property (_, _, _, trm, _) -> fileNameOfTerm   trm
    | _ -> None

op fileNameOfOpId(qid:QualifiedId, spc:Spec) : Option String =
  case findTheOp(spc,qid) of
    | Some {names=_,fixity=_,dfn,fullyQualified?=_} -> fileNameOfTerm dfn
    | _ -> None

op fileNameOfTypeId(qid:QualifiedId,spc:Spec) : Option String =
  case findTheType(spc,qid) of
    | Some {names=_,dfn} -> fileNameOfType dfn
    | _ -> None

op fileNameOfTerm (tm:MSTerm) : Option String =
  foldSubTerms (fn (t,val) ->
		  case val of
		    | Some _ -> val
		    | None ->
                      case termAnn t of
                        | File(nm,_,_) -> Some nm
                        | _ -> None)
  None tm

op fileNameOfType (s:MSType) : Option String =
  case typeAnn s of
    | File(nm,_,_) -> Some nm
    | _ -> None

op ppGrConcat (x:List WLPretty) : WLPretty = ppNest 0 (ppConcat x) % ppGroup (ppConcat x)
op ppGr1Concat (x:List WLPretty) : WLPretty = ppNest 1 (ppConcat x)
op ppGr2Concat (x:List WLPretty) : WLPretty = ppNest 2 (ppConcat x)
op ppNum (n:Integer) : WLPretty = ppString(show n)
op ppSpace : WLPretty = ppString " "
op ppSpaceBreak : WLPretty = ppConcat[ppSpace, ppBreak]


op ppType (elem:SpecElement) (spc:Spec) : WLPretty =
  case elem of
    | Type (qid, pos) -> 
      let Qualified (q, id) = qid in
      ppConcat [ppString "((", ppString id, ppString " *) => *)"]

op ppTypeLocalDef (elem:SpecElement) (spc:Spec) : WLPretty =
  case elem of
    | Type (qid, pos) -> 
      let Qualified (q, id) = qid in
      ppConcat [ppString "(local (defun ", ppString id, ppString " (x) (declare (ignore x)) nil))"]

op ppConstrainedFunctions (types:SpecElements) (spc:Spec) : WLPretty =
  ppConcat [ppString "(encapsulate", ppNewline,
            ppString " ;; Constrained function declarations", ppNewline,
            ppString " (",
            ppGr1Concat [ppConcat [ppString " ;; types", ppNewline], ppSep ppNewline (map (fn t -> ppType t spc) types)], ppString ")", ppNewline, ppNewline,
            
            ppGr1Concat [ppConcat [ppString " ;; Local Definitions", ppNewline], ppSep ppNewline (map (fn t -> ppTypeLocalDef t spc) types)],
            ppString ")"]

op ppTypeDef (elem:SpecElement) (spc:Spec) : WLPretty =
  case elem of
    | TypeDef (qid, pos) ->
      let Qualified (q, id) = qid in
      let Some typeDef = findTheType (spc, qid) in
      let name = typeDef.names @ 0 in
      let dfn = typeDef.dfn in
      case dfn of
        | Base (Qualified (_, pid) , _, _) ->
          ppConcat [ppString "(defun ", ppString id, ppString "(x)", ppNewline,
                    ppString "  (", ppString pid, ppString " x))"]

op ppFunctions (typeDefs:SpecElements) (spc:Spec) : WLPretty =
  ppGrConcat [ppConcat [ppString ";; typeDefs", ppNewline], 
               ppSep ppNewline (map (fn t -> ppTypeDef t spc) typeDefs)]

op filterType (elems:SpecElements) : SpecElements =
  case elems of
    | [] -> []
    | el :: rst ->
      case el of
        | Type x -> (Type x) :: filterType rst
        | _      -> filterType rst

op filterTypeDef (elems:SpecElements) : SpecElements =
  case elems of
    | [] -> []
    | el :: rst ->
      case el of
        | TypeDef x -> (TypeDef x) :: filterTypeDef rst
        | _         -> filterTypeDef rst

(* 
op ppSpecElementsAux (c:Context) (elems:SpecElements) (spc:Spec) : List WLPretty =
  case elems of
    | [] -> []
    | el :: rst ->
      Cons (ppSpecElement c el spc,
            ppSpecElementsAux c rst spc)
*)

op ppSpecElements (c:Context) (spc:Spec) : WLPretty = 
  ppConcat [ppConstrainedFunctions (filterType spc.elements) spc,
            ppNewline, ppNewline,
            ppFunctions (filterTypeDef spc.elements) spc]
%  ppNest 1 (ppConcat [(ppSep ppNewline
%                         (filter (fn pp -> pp ~= ppNil)  %% why the filter?
%                            (ppSpecElementsAux c spc.elements spc)))])

op ppSpec (c: Context) (spc:Spec) : WLPretty =
  ppGr2Concat [ppString "(in-package \"ACL2\")",
               ppNewline,
               ppNewline,
               ppSpecElements c (adjustElementOrder spc)]
                          
(*               case spc.qualifier of | Some qual -> ppString qual | None -> ppString "<no-qualifier>",
               ppNewline,
               ppSpecElements c spc.elements,
               ppNewline,
               ppAOpMap(c, spc.ops),
               ppNewline,
               ppATypeMap(c, spc.types),
               ppString ")"
               ]
*)

op ppValue (c: Context) (value:Value) : WLPretty =
  case value of
    | Spec        spc           -> ppSpec c spc %opt_val_tm
%      | Morph       spec_morphism -> ppMorphism c  spec_morphism
%      | SpecPrism   spec_prism    -> ppPrism     spec_prism     % tentative
%      | SpecInterp  spec_interp   -> ppInterp    spec_interp    % tentative
%      | Diag        spec_diagram  -> ppDiagram  c  spec_diagram
%      | Colimit     spec_colimit  -> ppColimit  c  spec_colimit
%      | Other       other_value   -> ppOtherValue other_value
%      | InProcess                 -> ppString "InProcess"
%      | UnEvaluated _             -> ppString "some unevaluated term"
    | _                         -> ppString "ERROR: <unrecognized value>"


op printValue (c:Context) (value:Value) : String =
  let file_nm = case fileNameOfValue value of
                  | Some str -> str
                  | _ -> ""
  in
  let main_pp_val = ppValue (c << {fileName = file_nm}) value in
  ppFormat main_pp_val


op printValueTop (value : Value, uid : UnitId, showImportedSpecs? : Bool) : String =
  printValue {printTypes? = true,
              printPositionInfo? = false,
              fileName = "", %FIXME the caller already has the file name? ah, this is used to print position information?
              %currentUID = uid,
              %uidsSeen = [uid],
              recursive? = true,
              showImportedSpecs? = showImportedSpecs?}
             value

op genACL2Core (val : Value, showImportedSpecs? : Bool) : Bool =
  case uidForValue val of
    | None -> let _ = writeLine "Error: Can't get UID string from value" in false
    | Some uid -> 
      let uidstr = fileNameInSubDir(uid, "acl2") in
      let filename = uidstr ^ "-acl2.lisp" in
      let _ = ensureDirectoriesExist filename in
      let _ = writeLine("Writing ACL2 to: " ^ filename ^ "\n") in
      let _ = writeStringToFile(printValueTop(val,uid,showImportedSpecs?),filename) in
        true

op evaluateGenACL2Helper (optional_argstring : Option String, lastUnitIdLoaded : Option String, homedir : String, showImportedSpecs? : Bool) : Option String = 
  case UIDStringFromArgString(optional_argstring, lastUnitIdLoaded, homedir) of
    | None -> None
    | Some uid_str -> 
      let success? = (case evaluateUnitId uid_str of
                        | None -> let _ = writeLine("Error: Unknown UID " ^ uid_str) in false
                        | Some val -> genACL2Core(val, showImportedSpecs?)) in
      if success? then Some uid_str else None

op evaluateGenACL2 (optional_argstring : Option String, lastUnitIdLoaded : Option String, homedir : String) : Option String =
  evaluateGenACL2Helper (optional_argstring, lastUnitIdLoaded, homedir, false)

end-spec