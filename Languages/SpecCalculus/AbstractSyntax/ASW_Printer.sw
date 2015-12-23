(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

 %%% Top level function printUIDtoFile 

ASWPrinter qualifying spec 

 import Types
 import /Languages/MetaSlang/AbstractSyntax/AnnTerm
 import /Languages/MetaSlang/Transformations/NormalizeTypes
 % op  NormTypes.normalizeTypes: Spec -> Spec
 import /Library/PrettyPrinter/WadlerLindig
  import /Languages/MetaSlang/Specs/Printer
 import /Languages/SpecCalculus/Semantics/Value
 import /Languages/SpecCalculus/Semantics/Monad
  % type SpecCalc.Exception
  % type SpecCalc.Result a =
  %   | Ok a
  %   | Exception Exception
  % type SpecCalc.State = {exceptions : List Exception} % for deferred processing
  % type SpecCalc.Env a = State -> (Result a) * State
  % op SpecCalc.run : fa (a) Env a -> a
  % op SpecCalc.catch : fa (a) Env a -> (Exception -> Env a) -> Env a
  % op SpecCalc.return : fa (a) a -> SpecCalc.Env a
  % op SpecCalc.monadBind : fa (a,b) (SpecCalc.Env a) * (a -> SpecCalc.Env b) -> SpecCalc.Env b
  % op MonadicStateInternal.readGlobalVar : fa (a) String -> Option a
  % op IO.writeStringToFile : String *  Filename -> ()

 type Context = {printTypes?: Bool,
                 printPositionInfo?: Bool,
                 fileName: String,
                 currentUID: UnitId,
                 uidsSeen: List UnitId, % Used to avoid infinite recursion because of circularity
                 recursive?: Bool}
 %type SpecTerm = SpecCalc.SpecTerm
 %type Term = SCTerm
 type SpecElem = SpecElemTerm
 %type Decl = SCDecl

 % def ppGrConcat x = ppGroup (ppConcat x)

 op ppGrConcat (x:List WLPretty) : WLPretty  = ppConcatGN 0 x
 op ppGr2Concat (x:List WLPretty) : WLPretty = ppConcatGN 2 x
 op  ppNum: Int -> WLPretty
 def ppNum n = ppString(show n)


% op  showTerm : SCTerm -> String
% def showTerm term = ppFormat (ppSCTerm {printTypes? = true,
%                                        printPositionInfo? = false,
%                                        fileName = "",
%                                        currentUID = ,
%                                        recursive? = false}
%                                term)

 op  ppLitString: String -> WLPretty
 def ppLitString id = ppString(IO.formatString1("~S",id))

 %%% Identifiers have string quotes around them
 op  ppID: String -> WLPretty
 def ppID id = ppLitString id

 op  ppUID : UnitId -> WLPretty
 def ppUID unitId =
   let ppLocal = ppUIDlocal unitId in
   case unitId of
     | {path=h::_,hashSuffix=_} ->
       if deviceString? h
         then ppLocal
         else ppAppend (ppString "/") ppLocal
     | _ -> ppLocal                     % Shouldn't happen

 op  ppUIDlocal : UnitId -> WLPretty
 def ppUIDlocal {path, hashSuffix} =
   case hashSuffix of
     | None -> ppSep (ppString "/") (map ppID path)
     | Some suffix ->
       let def pp path =
             case path of
               | [] -> []
               | [x] -> [ppID(x ^ "#" ^ suffix)]  %  "
               | x::rp -> Cons(ppID x, pp rp)
       in
       ppSep (ppString "/") (pp path)

 op  ppRelativeUID : RelativeUID -> WLPretty
 def ppRelativeUID relUID =
   case relUID of
     | SpecPath_Relative unitId -> ppAppend (ppString "/") (ppUIDlocal unitId)
     | UnitId_Relative   unitId -> ppUIDlocal unitId


 op  ppSCTerm : Context -> SCTerm -> WLPretty
 def ppSCTerm c (term, pos) =
   case term of
     | Print t ->
       ppConcat [ppString "print ",
                 ppSCTerm c t]

     | UnitId unitId -> 
       ppConcat [ppString "unit ", ppRelativeUID unitId]

     | Spec specElems -> 
       ppConcat [ppString "spec",
                 ppNewline,
                 ppString "  ",
                 ppNest 2 (ppSpecElems c specElems),
                 ppNewline,
                 ppString "end spec"]

      | Qualify (term, qualifier) ->
        ppConcat [ppString "qualifying ",
                  ppID qualifier,
                  ppString " in ",
                  ppNewline,
                  ppSCTerm c term]

      | Translate (term, renaming) ->
        ppConcat [ppString "translate ",
                  ppSCTerm c term,
                  ppString " by ",
                  ppRenaming renaming]

      | Let (decls, term) ->
        ppConcat [ppString "let",
                  ppNewline,
                  ppString "  ",
                  ppNest 2 (ppDecls c decls),
                  ppNewline,
                  ppString "in",
                  ppNewline,
                  ppNest 2 (ppSCTerm c term)]

      | Where (decls, term) ->
        ppConcat [ppString "where",
                  ppNewline,
                  ppString "  ",
                  ppNest 2 (ppDecls c decls),
                  ppNewline,
                  ppString "in",
                  ppNewline,
                  ppNest 2 (ppSCTerm c term)]

      | Diag elems ->
        ppConcat [ppString "diag {",    % with apologies to stephen
                  ppNewline,
                  ppString "  ",
                  ppNest 2 (ppSep ppNewline (map (ppDiagElem c) elems)),
                  ppNewline,
                  ppString "}"]

      | Colimit term ->
        ppConcat [ppString "colim ",
                  ppSCTerm c term]

      | Subst (specTerm,morphTerm,pragmas) ->
        ppConcat [ppSCTerm c specTerm,
                  ppString " [",
                  ppSCTerm c morphTerm,
                  ppString "]",
                  ppBreak,
                  ppString " proof [",
                  ppSep (ppAppend (ppString ", ") ppBreak)
                    (map (fn ((p1,p2,p3),pos) -> ppConcat [ppLitString p1,
                                                           ppLitString p2,
                                                           ppLitString p3])
                       pragmas),
                  ppString "]"]

      | SpecMorph (dom, cod, elems, pragmas) ->
        let 
          def ppSpecMorphRule (rule, _(* position *)) = 
            case rule of          
              | Type (left_qid, right_qid) ->
                ppConcat [ppString " type ",
                          ppQualifiedId left_qid,
                          ppString " +-> ",
                          ppQualifiedId right_qid]
               
              | Op ((left_qid, _), (right_qid, _)) ->
                ppConcat [ppString " op ",
                          ppQualifiedId left_qid,
                          ppString " +-> ",
                          ppQualifiedId right_qid]

              | Ambiguous (left_qid, right_qid) ->
                ppConcat [ppQualifiedId left_qid,
                          ppString " +-> ",
                          ppQualifiedId right_qid]
        in
          ppConcat [ppString "morphism ",
                    ppSCTerm c dom,
                    ppString " -> ",
                    ppSCTerm c cod,
                    ppNewline,
                    ppString "  {",
                    ppIndent (ppSep ppNewline (map ppSpecMorphRule elems)),
                    ppNewline,
                    ppString "} : "]

      | Hide (nameExprs, term) ->
        let 
          def ppNameExpr expr = 
            case expr of          
              | Type qid ->
                ppConcat [ppString "type ",
                          ppQualifiedId qid]

              | Op (qid, optType) ->
                ppConcat [ppString "op ",
                          ppQualifiedId qid]

              | Axiom qid ->
                ppConcat [ppString "axiom ",
                          ppQualifiedId qid]

              | Theorem qid ->
                ppConcat [ppString "theorem ",
                          ppQualifiedId qid]

              | Conjecture qid ->
                ppConcat [ppString "conjecture ",
                          ppQualifiedId qid]

              | Ambiguous qid ->
                ppQualifiedId qid
        in
          ppConcat [ppString "hide {",
                    ppSep (ppString ", ") (map ppNameExpr nameExprs),
                    ppString "} in",
                    ppSCTerm c term]
    % | Export (nameExpr, term) ->
    %   ppConcat [ppString "export {",
    %             ppSep (ppString ",") (map ppIdInfo nameExpr),
    %             ppString "} from",
    %             ppSCTerm term]

      | Generate (target, term, optFileNm) ->
        ppConcat [ppString ("generate " ^ target ^ " "),
                  ppSCTerm c term,
                  (case optFileNm of
                     | Some filNm -> ppString (" in " ^ filNm)
                     | _ -> ppNil)]

      | Reduce (msTerm, scTerm) ->
        ppConcat [ppString "reduce ",
                  ppTerm c msTerm,
                  ppString " in ",
                  ppSCTerm c scTerm]

      | Prove (claimName, term, proverName, assertions, proverOptions, proverBaseOptions, answer_var) ->
          ppConcat [
            ppString ("prove " ^ printQualifiedId(claimName) ^ " in "),
            ppSCTerm c term,
            (case assertions of
               | All -> ppNil
               | Explicit ([]) -> ppNil
               | Explicit (assertions) -> ppConcat [
                                            ppString " using ",
                                            ppSep (ppString ", ") (map ppQualifiedId assertions)]),
            (case proverOptions of
               | OptionString ([option]) -> 
                                          if option = string("") then ppNil else
                                          ppConcat [
                                           ppString " options ",
                                           ppString (uncell (option)) ]
               | OptionName (prover_option_name) -> ppConcat [
                                                    ppString " options ",
                                                    ppString (printQualifiedId(prover_option_name)) ])
                    ]

      | Expand term ->
        ppConcat [ppString "expand ",
                  ppSCTerm c term]

      | Obligations term ->
        ppConcat [ppString "obligations ",
                  ppSCTerm c term]

      | Quote (value,_,_) -> 
        ppValue c value None

      | Other other_term -> ppString "<<Other>>"
        %ppOtherTerm other_term

 op  ppQualifiedId : QualifiedId -> WLPretty
 def ppQualifiedId (Qualified (q, id))  =
   if q = UnQualified then 
     ppID id
   else 
     ppConcat [ppID q, ppString ".", ppID id]


  op  ppDiagElem :  Context -> DiagElem -> WLPretty
  def ppDiagElem c (elem, _ (* position *)) =
    case elem of
      | Node (nodeId, term) ->
          ppConcat [
            ppString nodeId,
            ppString " |-> ",
            ppSCTerm c term
          ]
      | Edge (edgeId, dom, cod, term) ->
          ppConcat [
            ppString edgeId,
            ppString " : ",
            ppString dom,
            ppString " -> ",
            ppString cod,
            ppString " |-> ",
            ppSCTerm c term
          ]

 op  ppDecls : Context -> List (SCDecl) -> WLPretty
 def ppDecls c decls =
   let 
     def ppDecl (name, term) =
       ppConcat [ppID name,
                 ppString " = ",
                 ppSCTerm c term]
   in
     ppSep ppNewline (map ppDecl decls)

 op  ppSpecElems : Context -> List (SpecElem) -> WLPretty
 def ppSpecElems c elems = ppSep ppNewline (map (ppSpecElem c) elems)

 op  ppSpecElem : Context -> SpecElem -> WLPretty
 def ppSpecElem c (elem, pos) = 
   case elem of
     | Import  terms                  -> ppConcat [ppString "import [",
                                                   ppSep (ppString ", ") (map (ppSCTerm c) terms),
                                                   ppString "]"]
     | Type    (aliases, dfn)         -> ppTypeInfo c true (aliases, dfn) pos
     | Op      (aliases, fixity, def?, dfn) -> ppOpInfo c true true (aliases, fixity, dfn) pos  % !!!
     | Claim   (propType, name, tyVars, term) -> ppProperty c (propType, name, tyVars, term, pos)
     | Comment str                    -> if exists? (fn char -> char = #\n) str then
                                           ppConcat [ppString " (* ",
                                                     ppString str,
                                                     ppString " *) "]
                                         else
                                           ppString (" %% " ^ str)

 op  ppIdInfo : List QualifiedId -> WLPretty
 def ppIdInfo qids = ppSep (ppString ", ") (map ppQualifiedId qids)
   
 op  ppTypeInfo : Context -> Bool -> List QualifiedId * MSType -> Position -> WLPretty
 def ppTypeInfo c full? (aliases, dfn) pos =
   let (tvs, srt) = unpackType dfn in
   ppGr2Concat
     ((if c.printPositionInfo?
        then [ppPosition c pos]
        else [])
      ++
      (if full? && (case srt of Any _ -> false | _ -> true)
        then [ppString "type ",
              ppIdInfo aliases,
              ppBrTyVars tvs,
              ppString " = ",
              ppBreak,
              ppIndent(ppType c srt)]
        else [ppString "type decl ",
              ppIdInfo aliases,
              ppBrTyVars tvs]))

 op  ppBrTyVars : TyVars -> WLPretty
 def ppBrTyVars tvs =
   if tvs = [] then ppString " "
     else ppConcat [ppString " [",
                    ppTyVars tvs,
                    ppString "] "]

 op  ppTyVars : TyVars -> WLPretty
 def ppTyVars tvs =
   case tvs of
     | [] -> ppNil
     | _  -> ppSep (ppString ", ") (map ppID tvs)

 op  ppOpInfo :  Context -> Bool -> Bool -> Aliases * Fixity * MSTerm -> Position -> WLPretty
 def ppOpInfo c decl? def? (aliases, fixity, dfn) pos =
   let (tvs, srt, term) = unpackTerm dfn in
   ppGr2Concat
     ((if c.printPositionInfo?
        then [ppPosition c pos]
        else [])
      ++
      (if decl?
         then (if def? \_and (case term of
                             | Any _ -> false
                             | _ -> true)
                 then
                  [ppString "op",
                   ppBrTyVars tvs,
                   ppIdInfo aliases,
                   ppString " ",
                   ppFixity fixity,
                   ppString ": ",
                   ppType c srt,
                   ppString " = ",
                   ppNewline,
                   ppIndent(ppTerm c term)]
                 else
                  [ppString "op decl",
                   ppBrTyVars tvs,
                   ppIdInfo aliases,
                   ppString " ",
                   ppFixity fixity,
                   ppString ": ",
                   ppType c srt])
         else [ppString "op def",
               ppBrTyVars tvs,
               ppIdInfo aliases,
               ppString " = ",
               ppNewline,
               ppIndent(ppTerm c term)]))
  op  ppProperty : Context -> Property -> WLPretty
    def ppProperty c (propType, name, tyVars, term, pos) =
      ppGr2Concat [if c.printPositionInfo?
                    then ppPosition c pos
                    else ppNil,
                   ppString "claim ",
                   ppPropertyType propType,
                   ppString " ",
                   ppQualifiedId name,
                   ppBrTyVars tyVars,
                   ppString " is ",
                   ppBreak,
                   ppTerm c term]
 
  op  ppPropertyType : PropertyType -> WLPretty
   def ppPropertyType propType =
     case propType of
       | Axiom -> ppString "axiom"
       | Theorem -> ppString "theorem"
       | Conjecture -> ppString "conjecture"
       | any ->
            fail ("No match in ppPropertyType with: '"
               ^ (anyToString any)
               ^ "'")

 op   ppRenaming : Renaming -> WLPretty
  def ppRenaming (rules, _) =
    let 
      def ppRenamingRule (rule, _(* position *)) = 
        case rule of          
          | Type (left_qid, right_qid, aliases) ->
            ppConcat [ppString " type ",
                      ppQualifiedId left_qid,
                      ppString " +-> ", % ??
                      ppString (printAliases aliases)] % ppQualifiedId right_qid
            
          | Op ((left_qid,_), (right_qid, _), aliases) ->
            ppConcat [ppString " op ",
                      ppQualifiedId left_qid,
                      ppString " +-> ",
                      ppQualifiedId right_qid]

          | Ambiguous (left_qid, right_qid, aliases) ->
            ppConcat [ppString " ambiguous ",
                      ppQualifiedId left_qid,
                      ppString " +-> ",
                      ppQualifiedId right_qid]
          | Other other_rule -> ppString "<<Other>>"
            %ppOtherRenamingRule other_rule
    in
      ppConcat [ppString "[",
                ppSep (ppString ", ") (map ppRenamingRule rules),
                ppString "]"]

 op  ppOtherTerm         : OtherTerm Position -> WLPretty % Used for extensions to Specware
 op  ppOtherRenamingRule : OtherRenamingRule  -> WLPretty % Used for extensions to Specware

  %% --------------------------------------------------------------------------------
  %% Give the signature of utilities so we don't have to import them

  %type SpecCalc.GlobalContext
  %op  MonadicStateInternal.readGlobalVar : [a] String -> Option a
  op  Specware.evaluateUnitId: String -> Option Value
  op  SpecCalc.findUnitIdForUnit: Value * GlobalContext -> Option UnitId
  op  SpecCalc.findDefiningTermForUnit: Value * GlobalContext -> Option SCTerm
  %op  SpecCalc.uidToFullPath: UnitId -> String
  op  SpecCalc.evaluateTermInfo: SCTerm -> SpecCalc.Env ValueInfo
  %op  SpecCalc.setCurrentUID : UnitId -> SpecCalc.Env ()

  op  uidToAswName : UnitId -> String
  def uidToAswName {path,hashSuffix=_} =
   let device? = deviceString? (head path) in
   let main_name = last path in
   let path_dir = butLast path in 
   let mainPath = flatten (List.foldr (fn (elem,result) -> Cons("/",Cons(elem,result)))
                             ["/asw/",main_name]
                             (if device? then tail path_dir else path_dir))
   in if device?
        then (head path) ^ mainPath
        else mainPath


  %type SpecCalc.State
  %type SpecCalc.Env a = State -> (Result a) * State
  %op  SpecCalc.run : fa (a) Env a -> a
  %type SpecCalc.Exception
  %op  SpecCalc.catch : fa (a) Env a -> (Exception -> Env a) -> Env a

  op  evalSCTerm: Context -> SCTerm -> Option Value
  def evalSCTerm c term =
    let def handler _ = return None in
    let prog = {setCurrentUID(c.currentUID);
                (val,_,_) <- evaluateTermInfo term;
                return (Some val)}
    in
    run (catch prog handler)

  op  printUIDtoFile: String * Bool * Bool -> String
  def printUIDtoFile (uid_str, printPositionInfo?, recursive?) =
    case evaluateUnitId uid_str of
      | Some val ->
        (case uidStringForValue val of
          | None -> "Error: Can't get UID string from value"
          | Some (uid,uidstr) ->
            let fil_nm = uidstr ^ ".asw" in
            let _ = ensureDirectoriesExist fil_nm in
            let _ = writeStringToFile(printValueTop(val,uid,printPositionInfo?,recursive?),fil_nm) in
            fil_nm)
      | _ -> "Error: Unknown UID " ^ uid_str

  op  deleteASWFilesForUID: String -> ()
  def deleteASWFilesForUID uidstr =
    case evaluateUnitId uidstr of
      | Some val ->
        deleteASWFilesForVal val
      | _ -> ()

  op  deleteASWFilesForVal: Value -> ()
  def deleteASWFilesForVal val =
    case uidStringForValue val of
      | None -> ()
      | Some (_,uidstr) ->
        let fil_nm = uidstr ^ ".asw" in
        let _ = ensureFileDeleted fil_nm in
        case val of
          | Spec spc ->
            app (fn elem -> case elem of
                              | Import(_,im_sp,_,_) ->
                                deleteASWFilesForVal (Spec im_sp)
                              | _ -> ())
              spc.elements
          | _ -> ()

  op  ensureFileDeleted: String -> ()
  def ensureFileDeleted fil_nm =
    if fileExists? fil_nm
      then deleteFile fil_nm
      else ()

  op  ensureValuePrinted: Context -> Value -> ()
  def ensureValuePrinted c val =
    case uidStringPairForValue val of
      | None -> ()
      | Some (uid,fil_nm, hash_ext) ->
        let asw_fil_nm = fil_nm ^ hash_ext ^ ".asw" in
        let sw_fil_nm = fil_nm ^ ".sw" in
        if fileOlder?(sw_fil_nm,asw_fil_nm)
          then ()
          else let c = c << {currentUID = uid} in
               writeStringToFile(printValue c val,asw_fil_nm)

  op  uidStringForValue: Value -> Option (UnitId * String)
  def uidStringForValue val =
    case uidStringPairForValue val of
      | None -> None
      | Some(uid,filnm,hash) -> Some(uid,filnm ^ hash)

  op  uidStringPairForValue: Value -> Option (UnitId * String * String)
  def uidStringPairForValue val =
    case MonadicStateInternal.readGlobalVar "GlobalContext" of
      | None -> None
      | Some global_context ->
    case findUnitIdForUnit(val,global_context) of
      | None -> None
      | Some uid ->
        Some (uid,
              uidToAswName uid,
              case uid.hashSuffix of
                | Some loc_nm -> "#" ^ loc_nm   % "
                | _ -> "")

  op  SpecCalc.findUnitIdforUnitInCache: Value -> Option UnitId
  def findUnitIdforUnitInCache val =
    case readGlobalVar "GlobalContext" of
      | None -> None
      | Some global_context ->
        findUnitIdForUnit(val,global_context)

  op  SpecCalc.findTermForUnitInCache: Value -> Option SCTerm
  def findTermForUnitInCache val =
    case readGlobalVar "GlobalContext" of
      | None -> None
      | Some global_context ->
        findDefiningTermForUnit(val,global_context)
    
%  op  printUID : String * Bool * Bool -> ()
%  def printUID (uid, printPositionInfo?, recursive?) =
%    toScreen
%      (case evaluateUnitId uid of
%       | Some val -> printValue (val,printPositionInfo?,recursive?)
%       | _ -> "<Unknown UID>")

  op  printValueTop : Value * UnitId * Bool * Bool -> String
  def printValueTop (value,uid,printPositionInfo?,recursive?) =
    printValue {printTypes? = true,
                printPositionInfo? = printPositionInfo?,
                fileName = "",
                currentUID = uid,
                uidsSeen = [uid],
                recursive? = recursive?}
      value

  op  printValue : Context -> Value -> String
  def printValue c value =
    let file_nm = case fileNameOfValue value of
                    | Some str -> str
                    | _ -> ""
    in
    let main_pp_val = ppValue (c << {fileName = file_nm}) value None in
    let pp_val = if c.printPositionInfo?
                  then ppConcat [ppString "infile ", ppID file_nm, ppNewline, main_pp_val]
                  else main_pp_val
    in
    ppFormat pp_val

  op  fileNameOfValue: Value -> Option String
  def fileNameOfValue value =
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

  op  fileNameOfSpec: Spec -> Option String
  def fileNameOfSpec spc =
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

  op  fileNameOfOpId: QualifiedId * Spec -> Option String
  def fileNameOfOpId(qid,spc) =
    case findTheOp(spc,qid) of
      | Some {names=_,fixity=_,dfn,fullyQualified?=_} -> fileNameOfTerm dfn
      | _ -> None

  op  fileNameOfTypeId: QualifiedId * Spec -> Option String
  def fileNameOfTypeId(qid,spc) =
    case findTheType(spc,qid) of
      | Some {names=_,dfn} -> fileNameOfType dfn
      | _ -> None

  op  fileNameOfTerm: MSTerm -> Option String
  def fileNameOfTerm tm =
    foldSubTerms (fn (t,val) ->
                  case val of
                    | Some _ -> val
                    | None ->
                  case termAnn t of
                    | File(nm,_,_) -> Some nm
                    | _ -> None)
      None tm

  op  fileNameOfType: MSType -> Option String
  def fileNameOfType s =
    case typeAnn s of
      | File(nm,_,_) -> Some nm
      | _ -> None


  %% --------------------------------------------------------------------------------

  op  ppValue : Context -> Value -> Option SCTerm -> WLPretty
% ???
  def ppValue c value opt_val_tm =
    case value of
      | Spec        spc           -> ppSpec c spc opt_val_tm
      | Morph       spec_morphism -> ppMorphism c  spec_morphism
      | SpecPrism   spec_prism    -> ppPrism     spec_prism     % tentative
      | SpecInterp  spec_interp   -> ppInterp    spec_interp    % tentative
%      | Diag        spec_diagram  -> ppDiagram  c  spec_diagram
%      | Colimit     spec_colimit  -> ppColimit  c  spec_colimit
%      | Other       other_value   -> ppOtherValue other_value
%      | InProcess                 -> ppString "InProcess"
%      | UnEvaluated _             -> ppString "some unevaluated term"
      | _                         -> ppString "<unrecognized value>"


  (* tentative *)
  def ppPrism {dom=_, sms=_, pmode=_, tm=_} =
    ppString "<some prism>"

  (* tentative *)
  def ppInterp {dom=_, med=_, cod=_, d2m=_, c2m=_} =
    ppString "<some interp>"

  %% --------------------------------------------------------------------------------
  %% Specs
  %% --------------------------------------------------------------------------------
  
%  op  printSpec: Spec -> ()
%  def printSpec spc = toScreen(ppFormat (ppSpec {printTypes? = true,
%                                                printPositionInfo? = false,
%                                                fileName = "",
%                                                recursive? = false}
%                                          spc))

  op  ppSpec: Context -> Spec -> Option SCTerm -> WLPretty
  def ppSpec c spc optTm =
    let norm_spc =  normalizeTypes(spc, false) in
    ppGr2Concat [ppString "spec ",
                 ppNewline,
                 case optTm of
                   | Some def_tm -> ppSpecOrigin c def_tm
                   | None ->
                 case findTermForUnitInCache(Spec spc) of
                   | None -> ppString "elements"
                   | Some def_tm -> ppSpecOrigin c def_tm,
                 ppNewline,
                 ppSpecElements c norm_spc norm_spc.elements,
                 ppNewline,
                 ppString "end spec"]

  op  ppSpecOrigin: Context -> SCTerm -> WLPretty
  def ppSpecOrigin c (def_tm,_) =
    case def_tm of
      | Subst(spec_tm,morph_tm,pragmas) ->
        ppGr2Concat [ppString "substitution ",
                     ppSCTermVal c spec_tm "name ",
                     ppNewline,
                     ppString "[",
                     ppSCTermVal c morph_tm " name morphism ",
                     ppString "]"]
        
      | Translate(spec_tm,renaming) ->
        ppGr2Concat[ppString "translate ",
                    ppSCTermVal c spec_tm "name ",
                    ppString " by ",
                    ppRenaming renaming]
      | Qualify(spec_tm,nm) ->
        if baseUnitId?(c.currentUID)
          then ppGrConcat [ppString "qualify base ",
                           ppID nm]
        else
        ppGr2Concat[ppString "qualify ",
                    ppID nm,
                    ppString " ",
                    ppSCTermVal c spec_tm "name "]
      | Obligations spec_or_morph_tm ->
        let oblig_keywords = if morphismTerm? c spec_or_morph_tm
                               then "morphism obligations "
                               else "obligations "
        in
        ppGr2Concat[ppString oblig_keywords,
                    ppSCTermVal c spec_or_morph_tm "name "]
         
      | _ -> ppString "elements"

  op  morphismTerm?: Context -> SCTerm -> Bool
  def morphismTerm? c tm =
    case tm of
      | (SpecMorph _,_) -> true
      | (UnitId _,_) ->
        (case evalSCTerm c tm of
          | Some (Morph _) -> true
          | _ -> false)
      | _ -> false

  op  baseUnitId?: UnitId -> Bool
  def baseUnitId? uid =
    let len = length uid.path in
    case subFromTo(uid.path,len-3,len-1) of
      | ["Library","Base"] -> true
      | _ -> false

  op  ppSCTermVal: Context -> SCTerm -> String -> WLPretty
  def ppSCTermVal c tm name_str=
    case tm of
      | (UnitId _,_) ->
        (case evalSCTerm c tm of
          | Some val -> ppUIDorFull c val (Some tm) name_str
          | _ -> ppString "<<Shouldn't happen!>>")
      | _ ->
        case evalSCTerm c tm of
          | Some val -> ppValue c val (Some tm)
          | _ -> ppString "<<Shouldn't happen!>>"
         
  op  ppUIDorFull: Context -> Value -> Option SCTerm -> String -> WLPretty
  def ppUIDorFull c val opt_val_tm name_str =
    case findUnitIdforUnitInCache val of
      | Some uid ->
        let _ = if c.recursive? && uid nin? c.uidsSeen
                  then ensureValuePrinted (c << {uidsSeen = Cons(uid,c.uidsSeen)}) val
                else ()
        in
          ppConcat [ppString name_str, ppUID uid]
      | None -> ppValue c val opt_val_tm

  op  ppSpecElements: Context -> Spec -> SpecElements -> WLPretty
  def ppSpecElements c spc elems = ppSep (ppConcat [ppString ";",ppNewline])
                                     (filter (fn pp -> pp ~= ppNil)
                                        (ppSpecElementsAux c spc elems))

  op  ppSpecElementsAux: Context -> Spec -> SpecElements -> List WLPretty
  def ppSpecElementsAux c spc elems =
    case elems of
      | [] -> []
      | (Op (qid1,false,pos)) :: (OpDef (qid2,0,hist,_)) :: rst | qid1 = qid2 ->
        Cons(ppSpecElement c spc (Op (qid1,true,pos)) true,
             ppSpecElementsAux c spc rst)
      | el :: rst ->
        Cons(ppSpecElement c spc el false,
             ppSpecElementsAux c spc rst)

%  op  normalizeSpecElements: SpecElements -> SpecElements
%  def normalizeSpecElements elts =
%    case elts of
%      | [] -> []
%      | (Op qid1) :: (OpDef qid2) :: rst | qid1 = qid2 ->
%        Cons(Op qid1, normalizeSpecElements rst)
%      | x::rst -> Cons(x,normalizeSpecElements rst)

  op  ppSpecElement: Context -> Spec -> SpecElement -> Bool -> WLPretty
  def ppSpecElement c spc elem op_with_def? =
    case elem of
      | Import (im_sc_tm,im_sp,im_elements,pos) ->
        ppConcat [if c.printPositionInfo?
                    then ppPosition c pos
                  else ppNil,
                  ppString "import ",
                  ppUIDorFull c (Spec im_sp) (Some im_sc_tm) "name "]
      | Op (qid,d?,pos) ->
        (case findTheOp(spc,qid) of
           | Some {names,fixity,dfn,fullyQualified?=_} ->
             ppOpInfo c true (d? \_or op_with_def?) (names,fixity,dfn) pos
           | _ -> 
             let _  = toScreen("\nInternal error: Missing op: " ^ printQualifiedId qid ^ "\n") in
             ppString "<Undefined Op>")
      | OpDef (qid,refine_num,hist,pos) ->    % !!!
        (case findTheOp(spc,qid) of
           | Some {names,fixity,dfn,fullyQualified?=_} -> ppOpInfo c false true (names,fixity,dfn) pos
           | _ -> 
             let _  = toScreen("\nInternal error: Missing op: " ^ printQualifiedId qid ^ "\n") in
             ppString "<Undefined Op>")
      | Type (qid,pos) ->
        (case findTheType(spc,qid) of
           | Some {names,dfn} -> ppTypeInfo c false (names,dfn) pos
           | _ -> 
             let _  = toScreen("\nInternal error: Missing type: " ^ printQualifiedId qid ^ "\n") in
             ppString "<Undefined Type>")
      | TypeDef (qid,pos) ->
        (case findTheType(spc,qid) of
           | Some {names,dfn} -> ppTypeInfo c true (names,dfn) pos
           | _ -> 
             let _  = toScreen("\nInternal error: Missing type: " ^ printQualifiedId qid ^ "\n") in
             ppString "<Undefined Type>")
      | Property prop -> ppProperty c prop
      | Pragma(beg_str,mid_str,end_str,pos) ->
        ppConcat [if c.printPositionInfo?
                    then ppPosition c pos
                  else ppNil,
                  ppString "proof ",
                  ppLitString beg_str,
                  ppString " ",
                  ppLitString mid_str,
                  ppString " ",
                  ppLitString end_str]
           
      | Comment (str,pos) ->
        ppConcat [if c.printPositionInfo?
                    then ppPosition c pos
                  else ppNil,
                  ppString " (* ",
                  ppString str,
                  ppString " *) "]

  op  ppPosition : Context -> Position -> WLPretty
  def ppPosition c pos =
    case pos of
      | File(fil_nm,(x1,x2,x3),(y1,y2,y3)) ->
        ppConcat ([ppString "at "]
                    ++ (if fil_nm = c.fileName
                          then []
                        else [ppID fil_nm])
                    ++ [ppString "[",
                        ppSep (ppString ", ") [ppNum x1, ppNum x2, ppNum x3,
                                               ppNum y1, ppNum y2, ppNum y3],
                        ppString "] ",
                        ppBreak])
      | _ -> ppString "@ "

  %% --------------------------------------------------------------------------------
  %% The term language
  %% --------------------------------------------------------------------------------

  op  ppTerm : Context -> MSTerm -> WLPretty
  def ppTerm c term =
    if c.printPositionInfo?
      then ppConcat [ppPosition c (termAnn term),
                     ppBreak,
                     ppTerm1 c term]
      else ppTerm1 c term

  op  ppTerm1 : Context -> MSTerm -> WLPretty
  def ppTerm1 c term =
    case term of
      | Apply (term1, term2, _)
         ->
         ppGrConcat [ppString "apply ",
                     ppTerm c term1,
                     ppBreak,
                     ppIndent(ppString "to "),
                     ppTerm c term2]
      | Record (fields,_) ->      
        (case fields of
          | [] -> ppString "tuple()"
          | ("1",_) :: _ ->
            let def ppField (_,y) = ppTerm c y in
            ppConcat [ppString "tuple(",
                      ppGrConcat[ppSep (ppAppend (ppString ", ") ppBreak) (map ppField fields),
                                 ppString ")"]]
          | _ ->
            let def ppField (x,y) =
                      ppConcat [ppID x,
                                ppString ":",
                                ppTerm c y
                               ] in
            ppGrConcat [ppString "record",
                        ppString "{",
                        ppSep (ppString ", ") (map ppField fields),
                        ppString "}"])
      | The (var,term,_) ->
        ppGrConcat [ppString "the ",
                    ppVar c var,
                    ppString " . ",
                    ppBreak,
                    ppTerm c term]
      | Bind (binder,vars,term,_) ->
        ppGr2Concat [ppString "bind ",
                     ppBinder binder,
                     ppString " ",
                     ppSep (ppString ", ") (map (ppVar c) vars),
                     ppString ". ",
                     ppBreak,
                     ppTerm c term]
      | Let (decls,term,_) ->
          let def ppDecl (pattern: MSPattern, term: MSTerm) =
                ppConcat [ppPattern c pattern,
                          ppString " = ",
                          ppTerm c term]
          in
          ppGrConcat [ppString "let ",
                      ppIndent (ppSep ppNewline (map ppDecl decls)),
                      ppString "in",
                      ppNewline,
                      ppIndent (ppTerm c term)
                     ]
      | LetRec (decls,term,_) ->
          let def ppDecl (v,term) =
                ppGr2Concat [
                             %ppString "def ",
                             ppVar c v,
                             ppString " = ",
                             ppBreak,
                             ppTerm c term]
          in
          ppGr2Concat [ppString "letrec",
                       ppString "  ",
                       ppIndent (ppSep ppNewline (map ppDecl decls)),
                       ppNewline,
                       ppString "in",
                       ppNewline,
                       ppTerm c term
                      ]
      | Var (v,_) -> ppVar c v
      | Fun (fun,ty,_) ->
        if c.printTypes?
          then ppFunWithType c fun ty
          else ppFun fun
%      | Lambda ([(pattern,_,term)],_) ->
%         ppGrConcat [
%           ppString "lambda ",
%           ppPattern c pattern,
%           ppGroup (ppIndent (ppConcat [
%             ppString " ->",
%             ppBreak,
%             ppAppend (ppTerm c term) (ppString ")")
%           ]))
%         ]
      | Lambda (match,_) ->
          ppIndent(ppGr2Concat [ppString "lambda ",
                                ppBreak,
                                ppString "[",
                                ppGrConcat [ppMatch c match,
                                            ppString "]"]])
      | IfThenElse (pred,term1,term2,_) -> 
          ppGrConcat [
            ppString "if ",
            ppTerm c pred,
            ppString " then",
            ppBreak,
            ppString "  ",
            ppIndent (ppTerm c term1),
            ppBreak,
            ppString "else",
            ppBreak,
            ppString "  ",
            ppIndent (ppTerm c term2)
          ]
      | Seq (terms,_) ->
          ppGrConcat [ppString "seq [",
                      ppSep (ppAppend (ppString ", ") ppBreak) (map (ppTerm c) terms),
                      ppString "]"]
      | Pi(tvs,term1,_) ->
        if tvs = [] then ppTerm c term1
          else ppGr2Concat [ppString "pi ",
                            ppTyVars tvs,
                            ppString " . ",
                            ppBreak,
                            ppTerm c term1]
      | And(terms,_) ->
        ppGrConcat [ppString "and ",
                    ppString "[",
                    ppSep (ppString ", ") (map (ppTerm c) terms),
                    ppString "]"]
      | Any(_) -> ppString "any"

      | TypedTerm (tm,srt,_) ->
          ppGr2Concat [ppString "sorted ",ppBreak,ppTerm c tm, ppString ": ",ppBreak,ppType c srt]
      | mystery -> fail ("No match in ppTerm with: '" ^ (anyToString mystery) ^ "'")

  op  ppBinder : Binder -> WLPretty
  def ppBinder binder =
    case binder of
      | Forall -> ppString "forall"
      | Exists -> ppString "exists"
      | Exists1 -> ppString "exists1"

  op  ppVar : Context -> MSVar -> WLPretty
  def ppVar c (id,srt) =
    if c.printTypes?
      then ppConcat [ppString "var(",
                     ppID id,
                     ppString ": ",
                     ppType c srt,
                     ppString ")"]
      else ppConcat [ppString "var(",
                     ppID id,
                     ppString ")"]

  op  ppMatch : Context -> MSMatch -> WLPretty
  def ppMatch c cases =
    let def ppCase (pattern,guard,term) =
          ppGrConcat [ppPattern c pattern,
                      ppString " | ",
                      ppTerm c guard,   % wrong?
                      ppBreak,
                      ppString " -> ",
                      ppTerm c term]
    in
      ppGroup (ppSep (ppAppend (ppString ", ") ppBreak) (map ppCase cases))

 %% Placeholder for patAnn which was missing a case
 op  patAnn1: [a] APattern a -> a
 def patAnn1 pat =
   case pat of
     | AliasPat     (_,_,   a) -> a
     | VarPat       (_,     a) -> a
     | EmbedPat     (_,_,_, a) -> a
     | RecordPat    (_,     a) -> a
     | WildPat      (_,     a) -> a
     | BoolPat      (_,     a) -> a
     | NatPat       (_,     a) -> a
     | StringPat    (_,     a) -> a
     | CharPat      (_,     a) -> a
     %| RelaxPat     (_,_,   a) -> a
     | QuotientPat  (_,_,_, a) -> a
     | RestrictedPat(_,_,   a) -> a
     | TypedPat     (_,_,   a) -> a

  op  ppPattern : Context -> MSPattern -> WLPretty
  def ppPattern c pattern =
     if c.printPositionInfo?
      then case patAnn1 pattern of
             | File(fil_nm,(x1,x2,x3),(y1,y2,y3)) ->
               ppGrConcat ([ppString "at "]
                           ++ (if fil_nm = c.fileName
                                then []
                                else [ppID fil_nm])
                           ++ [ppString "[",
                               ppSep (ppString ", ") [ppNum x1, ppNum x2, ppNum x3,
                                                      ppNum y1, ppNum y2, ppNum y3],
                               ppString "] ",
                               ppBreak,
                               ppPattern1 c pattern])
             | _ -> ppConcat [ppString "@ ", ppPattern1 c pattern]
      else ppPattern1 c pattern

  op  ppPattern1 : Context -> MSPattern -> WLPretty
  def ppPattern1 c pattern = 
    case pattern of
      | AliasPat (pat1,pat2,_) -> 
          ppGrConcat [ppString "alias ",
                      ppPattern c pat1,
                      ppString " with ",
                      ppPattern c pat2
                     ]
      | VarPat (v,_) -> ppVar c v
      | EmbedPat (constr,pat,srt,_) ->
        ppGrConcat ([ppString "embed ",
                    ppQualifiedId constr,
                    case pat of
                      | None -> ppNil
                      | Some pat -> ppAppend (ppString " ") (ppPattern c pat)]
                ++ (if c.printTypes?
                     then [ppString " in ",
                           ppType c srt]
                     else []))

      | RecordPat (fields,_) ->
        (case fields of
          | [] -> ppString "tuple()"
          | ("1",_)::_ ->
            let def ppField (_,pat) = ppPattern c pat in
            ppConcat [ppString "tuple(",
                      ppGrConcat[ppSep (ppString ", ") (map ppField fields),
                                 ppString ")"]]
          | _ ->
            let def ppField (x,pat) =
                  ppConcat [ppID x,
                            ppString ": ",    %% " = "  ?? 
                            ppPattern c pat]
            in
            ppConcat [ppString "record{",
                      ppSep (ppString ", ") (map ppField fields),
                      ppString "}"])
      | WildPat (srt,_) -> ppConcat[ppString "wild ",
                                    ppType c srt]
      | StringPat (str,_) -> ppString ("\"" ^ str ^ "\"")
      | BoolPat (b,_) -> ppBool b
      | CharPat (chr,_) -> ppConcat[ppString "#", ppString (show chr)]  % "
      | NatPat (int,_) -> ppString (show int)      
%      | RelaxPat (pat,term,_) ->   
%        ppGrConcat [ppString "relax ",
%                   ppPattern c pat,
%                   ppString ", ",
%                   ppTerm c term]
      | QuotientPat (pat,typename,tys,_) ->
        %% This requires update to interchange grammar
        ppGrConcat [ppString "quotient[",
                    ppType c (mkBase(typename, tys)),
                    ppString "] ",
                    ppPattern c pat]
      | RestrictedPat (pat,term,_) -> 
%        (case pat of
%          | RecordPat (fields,_) ->
%            (case fields of
%              | [] -> ppGrConcat [ppString "() | ",ppTerm c term]
%              | ("1",_)::_ ->
%                  let def ppField (_,pat) = ppPattern c pat in
%                  ppConcat [
%                    ppString "(",
%                    ppSep (ppString ",") (map ppField fields),
%                    ppString " | ",
%                    ppTerm c term,
%                    ppString ")"
%                  ]
%              | _ ->
%                  let def ppField (x,pat) =
%                    ppConcat [
%                      ppString x,
%                      ppString "=",
%                      ppPattern c pat
%                    ] in
%                  ppConcat [
%                    ppString "{",
%                    ppSep (ppString ",") (map ppField fields),
%                    ppString " | ",
%                    ppTerm c term,
%                    ppString "}"
%                  ])
%              | _ ->
            ppGrConcat [ppString "restrict ",
                        ppPattern c pat,
                        ppString " | ",
                        ppTerm c term]
      | TypedPat (pat,srt,_) ->
          ppGrConcat [ppString "sorted ",
                      ppPattern c pat,
                      ppString ": ",
                      ppType c srt]
      | mystery -> fail ("No match in ppPattern with: '" ^ (anyToString mystery) ^ "'")


  op  ppBool : Bool -> WLPretty
  def ppBool b =
    case b of
      | true -> ppString "true"
      | false -> ppString "false"

  op  ppFunWithType: Context -> MSFun -> MSType -> WLPretty
  def ppFunWithType c fun ty =
    ppGrConcat [ppFun fun, ppString ": ", ppType c ty]

  op  ppFun : MSFun -> WLPretty
  def ppFun fun =
    case fun of
      | Not       -> ppString "not"
      | And       -> ppString "and"
      | Or        -> ppString "or"
      | Implies   -> ppString "implies"
      | Iff       -> ppString "iff"
      | Equals    -> ppString "equals"
      | NotEquals -> ppString "notequals"
      | Quotient _  -> ppString "quotient"
      | PQuotient _ -> ppString "quotient"
      | Choose _ -> ppString "choose"
      | PChoose _ -> ppString "choose"
      | Restrict -> ppString "restrict"
      %| PRestrict _ -> ppString "restrict"
      | Relax -> ppString "relax"
      %| PRelax _ -> ppString "relax"
      | Op (qid,fix) -> ppConcat[ppString "op ", ppQualifiedId qid, ppString " ", ppFixity fix]
      | Project id ->
          ppConcat [ppString "project ", ppID id]
      | RecordMerge -> ppString "merge"
      | Embed (id,b) -> ppConcat [ppString "embed ", ppQualifiedId id, ppString " ", ppBool b]
      | Embedded id  -> ppConcat [ppString "embedded ", ppQualifiedId id]
      | Select id -> ppConcat [ppString "select ", ppQualifiedId id]
      | Nat n -> ppString (show n)
      | Char chr -> ppConcat[ppString "#", ppString (show chr)]  % "
      | String str -> ppString ("\"" ^ str ^ "\"")
      | Bool b -> ppBool b
      | OneName (id,fxty) -> ppString id
      | TwoNames (id1,id2,fxty) -> ppQualifiedId (Qualified (id1,id2))
      | mystery -> fail ("No match in ppFun with: '" ^ (anyToString mystery) ^ "'")


  op  ppFixity : Fixity -> WLPretty
  def ppFixity fix =
    case fix of
      | Infix (assoc,  n) -> ppConcat [ppString "infix ",
                                       case assoc of
                                         | Left  -> ppString "left "
                                         | Right -> ppString "right ",
                                       ppString (show n)]
      | Nonfix           -> ppString "nonfix"
      | Constructor0     -> ppString "nonfix"
      | Constructor1     -> ppString "nonfix"
      | Unspecified      -> ppString "unspecified"
      | Error fixities   -> ppConcat [
                                      ppString "error [",
                                      ppSep (ppString ", ") (map ppFixity fixities),
                                      ppString "]"
                                     ]
      | mystery -> fail ("No match in ppFixity with: '" ^ (anyToString mystery) ^ "'")

  op  isSimpleType? : MSType -> Bool
  def isSimpleType? srt =
    case srt of
      | Base _ -> true
      | Boolean _ -> true
      | _ -> false

  op  ppType : Context -> MSType -> WLPretty
  def ppType c ty =
    if c.printPositionInfo?
      then case typeAnn ty of
             | File(fil_nm,(x1,x2,x3),(y1,y2,y3)) ->
               ppGrConcat ([ppString "at "]
                           ++ (if fil_nm = c.fileName
                                then []
                                else [ppID fil_nm])
                           ++ [ppString "[",
                               ppSep (ppString ", ") [ppNum x1, ppNum x2, ppNum x3,
                                                      ppNum y1, ppNum y2, ppNum y3],
                               ppString "] ",
                               ppBreak,
                               ppType1 c ty])
             | _ -> ppConcat [ppString "@ ", ppType1 c ty]
      else ppType1 c ty

  op  ppType1 : Context -> MSType -> WLPretty
  def ppType1 c ty =
    case ty of
      | Arrow (ty1,ty2,_) ->
        ppGrConcat [ppString "arrow ",
                    ppType c ty1,
                    ppString " -> ",
                    ppType c ty2]
      | Product (fields,_) ->
        (case fields of
            [] -> ppString "tuple()"
          | ("1",_)::_ ->
            let def ppField (_,y) = ppType c y in
            ppGrConcat [
              ppString "tuple(",
              ppSep (ppString ", ") (map ppField fields),
              ppString ")"
            ]
          | _ ->
            let def ppField (x,y) =
              ppGrConcat [
                ppID x,
                ppString " : ",
                ppType c y
              ] in
            ppIndent (ppGrConcat [
              ppString "record{",
              ppSep (ppAppend (ppString ", ") ppBreak) (map ppField fields),
              ppString "}"
            ]))
      | CoProduct (taggedTypes,_) -> 
        let def ppTaggedType (id,optTy) =
          case optTy of
            | None -> ppQualifiedId id
            | Some ty ->
                ppConcat [ppQualifiedId (id),
                          ppString ": ",
                          ppType c ty]
        in ppGrConcat [
          ppString "sum(",
          ppGrConcat [
            ppSep (ppAppend (ppString ", ") ppBreak) (map ppTaggedType taggedTypes)
          ],
          ppString ")"
        ]
      | Quotient (ty,term,_) ->
        ppGrConcat [
          ppString "quotient ",
          ppType c ty,
          ppString " / ",
          ppTerm c term
        ]
      | Subtype (ty,term,_) ->
        ppConcat [
          ppString "restrict ",
          ppType c ty,
          ppString " | ",
          ppTerm c term
        ]
      | Base (qid,[],_) -> ppQualifiedId qid
      | Base (qid,tys,_) ->
         ppGrConcat [
           ppQualifiedId qid,
           ppString "[",
           ppSep (ppString ", ") (map (ppType c) tys),
           ppString "]"
         ]
      | Boolean _ -> ppString "bool"  
      | TyVar (tyVar,_) -> ppConcat [ppString "tyvar ",ppID tyVar]
      | Pi(tvs,ty,_) ->
        if tvs = [] then ppType c ty
          else ppGrConcat [ppString "pi ",
                           ppTyVars tvs,
                           ppString " . ",
                           ppType c ty]
      | And(types,_) ->
        ppGrConcat[ppString "and ",
                   ppString "[",
                   ppSep (ppString ", ") (map (ppType c) types),
                   ppString "]"]
      | Any(_) -> ppString "any"
      | mystery -> fail ("No match in ppType with: '" ^ (anyToString mystery) ^ "'")

  op  ppMorphism: Context -> Morphism -> WLPretty
  def ppMorphism c {dom,cod,typeMap,opMap,pragmas,sm_tm} =
    ppGrConcat [ppString "morphism ",
                ppUIDorFull c (Spec dom) None "name ",
                ppBreak,
                ppString " to ",
                ppUIDorFull c (Spec cod) None "name ",
                ppBreak,
                ppString " types ",
                ppIdMap typeMap,
                ppNewline,
                ppString " ops ",
                ppIdMap opMap,
                ppBreak,
                ppString " proof [",
                ppSep (ppAppend (ppString ", ") ppBreak)
                  (map (fn ((p1,p2,p3),pos) -> ppConcat [ppLitString p1,
                                                         ppLitString p2,
                                                         ppLitString p3])
                   pragmas),
                ppString "]",
                ppBreak,
                ppString "end morphism"]

 %op  PolyMap.mapToList : QualifiedIdMap -> List (QualifiedId * QualifiedId)

 op  ppIdMap: QualifiedIdMap -> WLPretty
 def ppIdMap idMap =
   ppNest 0
     (ppSep (ppAppend (ppString ", ") ppBreak)
        (map (fn (d,r) -> ppConcat [ppQualifiedId d, ppString " -> ",ppQualifiedId r])
           (mapToList idMap)))

endspec
