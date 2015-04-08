%%% Top level function printUIDtoFile 

MMT = MMT qualifying spec

import /Languages/MetaSlang/Specs/Position
 
op mkString : List String -> String -> String
def mkString l sep =
   case l of
    | Nil -> ""
    | Cons(x, Nil) -> x
    | Cons(hd,tl) -> hd ^ sep ^ (mkString tl sep)
 
 op Elem(tag: String, atts: List String, children: List String, pos: Position): String =
   "<" ^ tag ^ " " ^ (flatten atts) ^ ">" ^ (mkString children "\n") ^ "</" ^ tag ^ ">" 

 op Att(k: String, v: String) : String =
   " " ^ k ^ "=\"" ^ v ^ "\""

 op Document (file: String, spc: String) : String =
   Elem("omdoc", [Att("file", file)], [spc], noPos)

 op Theory (name: String, decls: List String, pos: Position) : String =
   Elem("theory", [Att("name", name)], decls, pos)
   
 op ConstDec (name: String, role: String, tyvar: List String, tp: Option String, df: Option String, not: Option String, pos: Position) : String =
   let tpS = case tp of | None -> Nil | Some t -> [Elem("type", [], [t], noPos)] in
   let dfS = case df of | None -> Nil | Some d -> [Elem("definition", [], [d], noPos)] in
   let notS = case not of | None -> Nil | Some n -> [Elem("notations", [], [n], noPos)] in
   Elem("constant", [Att("name", name), Att("role", role)], tpS ++ dfS ++ notS, pos)
   
 op Assignment(name: String, df: String): String = 
   ConstDec(name, "assignment", Nil, None, Some df, None, noPos)

 op InclDec (frm: String, pos: Position) : String =
   Elem("import", [], [Elem("from", [], [frm], noPos)], pos)
 
 op MInfix(assoc: String, prec: String): String =
   let atts = [Att("fixity", "infix"^assoc), Att("precedence", prec), Att("arguments", "0 2")] in
   Elem("notation", atts, [], noPos)
   
 op MConst (mod: Option String, name: String, pos: Position): String =
   let modAtt = case mod of | None -> Nil | Some m -> [Att("module", m)] in
   Elem("OMS", modAtt ++ [Att("name",name)], [], pos)
   
 op MVar (name: String, pos: Position): String =
   Elem("OMV", [Att("name", name)], [], pos)
   
 op MLit (tp: String, l: String, pos: Position): String =
   Elem("OMLIT", [Att("type", tp), Att("value", l)], [], pos)
   
 op MApp (fun: String, args: List String, pos: Position): String =
   Elem("OMA", [], fun :: args, pos)
   
 op MBindN (bindername: String, vars: List String, body: List String, pos: Position): String =
   Elem("OMBIND", [], [SW(bindername), flatten vars] ++ body, pos)
 op MBind (bindername: String, vars: List String, body: String, pos: Position): String =
   MBindN(bindername, vars, [body], pos)
 
 op MRecord(fields: List (String * String), types: Bool, pos: Position): String =
   let tag = if types then "type" else "definition" in
   Elem("Subst", [],
        map (fn (key, value) -> Elem("OMV", [Att("name", key)], [Elem(tag,[], [value], noPos)], noPos)) fields, pos)
 op MProjection(field: String, pos: Position): String =
   MUConst(field, pos)
 
 op MVarDef(name: String, tpOpt: Option String, dfOpt: Option String, pos: Position): String =
   let tp = case tpOpt of | None -> Nil | Some t -> [Elem("type", [], [t], noPos)] in
   let df = case dfOpt of | None -> Nil | Some d -> [Elem("definition", [], [d], noPos)] in
   Elem("OMV", [Att("name", name)], tp ++ df, pos)

 op MVarDec(name: String, tp: Option String, pos: Position): String =
   MVarDef(name, tp, None, pos)
 
 op MProof(text: String, pos: Position): String = ""
 op MComment(text: String, pos: Position): String = ""
 
  
 op SWP(name: String, pos: Position): String =
   MConst(Some "Specware", name, pos)
 op SW(name: String): String =
   MConst(Some "Specware", name, noPos)
 op SApp(name: String, args: List String, pos: Position): String =
   MApp(SW(name), args, pos)
 op MUConst (name: String, pos: Position): String =
   MConst(None, name, pos)

end-spec

XMLPrinter = XMLPrinter qualifying spec 

%% imports

 import Types
 import /Languages/MetaSlang/AbstractSyntax/AnnTerm
 import /Languages/MetaSlang/Transformations/NormalizeTypes
 import /Languages/MetaSlang/Specs/Printer
 import /Languages/SpecCalculus/Semantics/Value
 import /Languages/SpecCalculus/Semantics/Monad

 %% Give the signature of utilities so we don't have to import them
 op  Specware.evaluateUnitId: String -> Option Value
 op  SpecCalc.findUnitIdForUnit: Value * GlobalContext -> Option UnitId
 op  SpecCalc.findDefiningTermForUnit: Value * GlobalContext -> Option SCTerm
 % op  SpecCalc.evaluateTermInfo: SCTerm -> SpecCalc.Env ValueInfo
 type SpecElem = SpecElemTerm
 
 import MMT

%% printing context

 type Context = {printTypes?: Bool,
                 printPositionInfo?: Bool,
                 fileName: String,
                 currentUID: UnitId,
                 uidsSeen: List UnitId, % Used to avoid infinite recursion because of circularity
                 recursive?: Bool}

%% printing identifiers

 %%% Identifiers have string quotes around them
 op  ppLitString: String -> String
 def ppLitString id = IO.formatString1("~S",id)

 op  ppID: String -> String
 def ppID id = id

 op  ppUID : UnitId -> String
 def ppUID unitId =
   let ppLocal = ppUIDlocal unitId in
   case unitId of
     | {path=h::_,hashSuffix=_} ->
       if deviceString? h
         then ppLocal
         else "/" ^ ppLocal
     | _ -> ppLocal                     % Shouldn't happen

 op  ppUIDlocal : UnitId -> String
 def ppUIDlocal {path, hashSuffix} =
   case hashSuffix of
     | None -> mkString(map ppID path) "/"
     | Some suffix ->
       let def pp path =
             case path of
               | [] -> ""
               | [x] -> ppID(x ^ "#" ^ suffix)
               | x::rp -> (ppID x) ^ "/" ^ (pp rp)
       in
       pp path

 op  ppQualifiedId : QualifiedId -> String
 def ppQualifiedId (Qualified (q, id))  =
   if q = UnQualified then 
     ppID id
   else 
     (ppID q) ^ "." ^ (ppID id)

%% toplevel functions
 (* main function, if recursive, also call on all imported Specs *)
 op  printUIDtoFile: String * Bool * Bool -> String
 def printUIDtoFile (uid_str, printPositionInfo?, recursive?) =
    case evaluateUnitId uid_str of
      | Some val ->
        (case uidStringForValue val of
          | None -> "Error: Can't get UID string from value"
          | Some (uid,uidstr) ->
            let fil_nm = uidstr ^ ".omdoc" in
            let _ = ensureDirectoriesExist fil_nm in
            let _ = writeStringToFile(printValueTop(val,uid,printPositionInfo?,recursive?),fil_nm) in
            fil_nm)
      | _ -> "Error: Unknown UID " ^ uid_str

 op  uidToAswName : UnitId -> String
 def uidToAswName {path,hashSuffix=_} =
   let device? = deviceString? (head path) in
   let main_name = last path in
   let path_dir = butLast path in 
   let mainPath = flatten (List.foldr (fn (elem,result) -> Cons("/",Cons(elem,result)))
                             ["/omdoc/",main_name]
                             (if device? then tail path_dir else path_dir))
   in if device?
        then (head path) ^ mainPath
        else mainPath

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
                | Some loc_nm -> "#" ^ loc_nm
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
    
 (* initialize context *)
 op  printValueTop : Value * UnitId * Bool * Bool -> String
 def printValueTop (value,uid,printPositionInfo?,recursive?) =
    printValue {printTypes? = true,
                printPositionInfo? = printPositionInfo?,
                fileName = "",
                currentUID = uid,
                uidsSeen = [uid],
                recursive? = recursive?}
      value

 (* print file *)
 op  printValue : Context -> Value -> String
 def printValue c value =
    let file_nm = case fileNameOfValue value of
                    | Some str -> str
                    | _ -> ""
    in
    let main_pp_val = ppValue (c << {fileName = file_nm}) value None in
    Document(ppID file_nm, main_pp_val)

 op  fileNameOfValue: Value -> Option String
 def fileNameOfValue value =
    case value of
      | Spec        spc           -> fileNameOfSpec spc
      %      | Morph       spec_morphism -> ppMorphism c  spec_morphism
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


%% printing modules

 op  ppValue : Context -> Value -> Option SCTerm -> String
 def ppValue c value opt_val_tm =
    case value of
      | Spec        spc           -> ppSpec c spc opt_val_tm
      | Morph       spec_morphism -> ppMorphism c  spec_morphism
      % | SpecPrism   spec_prism    -> ppPrism     spec_prism     % tentative
      % | SpecInterp  spec_interp   -> ppInterp    spec_interp    % tentative
      % | Diag        spec_diagram  -> ppDiagram  c  spec_diagram
      % | Colimit     spec_colimit  -> ppColimit  c  spec_colimit
      % | Other       other_value   -> ppOtherValue other_value
      | _                           -> "<unrecognized value>"


%% printing specs

 op  ppSpec: Context -> Spec -> Option SCTerm -> String
 def ppSpec c spc optTm =
    let norm_spc =  normalizeTypes(spc, false) in
    let name = ppUID c.currentUID in
     (* get the SCTerm that this Spec is derived from, not necessarily useful *)
    let specOrigin =
                 case optTm of
                   | Some def_tm -> ppSpecOrigin c def_tm
                   | None ->
                 case findTermForUnitInCache(Spec spc) of
                   | None -> "elements"
                   | Some def_tm -> ppSpecOrigin c def_tm
    in Theory("", ppSpecElements c norm_spc norm_spc.elements, noPos) (* Spec Uids are derived theories are unnamed for now *)

 op  ppSpecOrigin: Context -> SCTerm -> String
 def ppSpecOrigin c (def_tm,_) =
    case def_tm of
      | Subst(spec_tm,morph_tm,pragmas) -> ""
          (* spec_tm with morph_tm; morph_tm maps name->name; pragmas may discharge proof obligations if target has definiens
             ppSCTermVal c spec_tm
             ppSCTermVal c morph_tm
          *)
      | Translate(spec_tm,renaming) -> ""
          (* spec_tm with renaming
             ppSCTermVal c spec_tm
             ppRenaming renaming
          *)
      | Qualify(spec_tm,nm) -> ""
          (* spec_tm with all names renamed by prefixing nm ??? what if they have a prefix alreday?
             occurs frequently at beginning of spec to introduce canonical qualifier
             ppSCTermVal c spec_tm
             ppRenaming renaming
             if baseUnitId?(c.currentUID) then "qualify base " ^ (ppID nm)
             else "qualify " ^ (ppID nm) ^ ppSCTermVal c spec_tm
          *)
      | Obligations spec_or_morph_tm -> ""
        (* rare *)
      | _ -> "elements"

 (*
 op  morphismTerm?: Context -> SCTerm -> Bool
 def morphismTerm? c tm =
    case tm of
      | (SpecMorph _,_) -> true
      | (UnitId _,_) ->
        (case evalSCTerm c tm of
          | Some (Morph _) -> true
          | _ -> false)
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
 *)

 op  baseUnitId?: UnitId -> Bool
 def baseUnitId? uid =
    let len = length uid.path in
    case subFromTo(uid.path,len-3,len-1) of
      | ["Library","Base"] -> true
      | _ -> false

 (* tries to turn a value into a unit: if so, export it recursively and print the UID; otherwise, print the value *) 
 op  ppUIDorFull: Context -> Value -> Option SCTerm -> String -> String
 def ppUIDorFull c val opt_val_tm name_str =
    case findUnitIdforUnitInCache val of
      | Some uid ->
        let _ = if c.recursive? && uid nin? c.uidsSeen
                  then ensureValuePrinted (c << {uidsSeen = Cons(uid,c.uidsSeen)}) val
                else ()
        in
          name_str ^ (ppUID uid)
      | None -> ppValue c val opt_val_tm

 op  ppSpecElements: Context -> Spec -> SpecElements -> List String
 def ppSpecElements c spc elems =
    case elems of
      | [] -> []
      | (Op (qid1,false,pos)) :: (OpDef (qid2,0,hist,_)) :: rst | qid1 = qid2 ->
        Cons(ppSpecElement c spc (Op (qid1,true,pos)) true,
             ppSpecElements c spc rst)
      | el :: rst ->
        Cons(ppSpecElement c spc el false,
             ppSpecElements c spc rst)

%% printing symbols
 op  ppSpecElement: Context -> Spec -> SpecElement -> Bool -> String
 def ppSpecElement c spc elem op_with_def? =
    case elem of
      | Import (im_sc_tm,im_sp,im_elements,pos) ->
        InclDec(ppUIDorFull c (Spec im_sp) (Some im_sc_tm) "name ", pos)
      | Op (qid,d?,pos) ->
        (case findTheOp(spc,qid) of
           | Some {names,fixity,dfn,fullyQualified?=_} ->
             ppOpInfo c true (d? \_or op_with_def?) (names,fixity,dfn) pos
           | _ -> 
             let _  = toScreen("\nInternal error: Missing op: " ^ printQualifiedId qid ^ "\n") in
             "<Undefined Op>")
      | OpDef (qid,refine_num,hist,pos) ->
        (case findTheOp(spc,qid) of
           | Some {names,fixity,dfn,fullyQualified?=_} ->
             ppOpInfo c false true (names,fixity,dfn) pos
           | _ ->
             let _  = toScreen("\nInternal error: Missing op: " ^ printQualifiedId qid ^ "\n") in
             "<Undefined Op>")
      | Type (qid,pos) ->
        (case findTheType(spc,qid) of
           | Some {names,dfn} ->
             ppTypeInfo c false (names,dfn) pos
           | _ -> 
             let _  = toScreen("\nInternal error: Missing type: " ^ printQualifiedId qid ^ "\n") in
             "<Undefined Type>")
      | TypeDef (qid,pos) ->
        (case findTheType(spc,qid) of
           | Some {names,dfn} ->
             ppTypeInfo c true (names,dfn) pos
           | _ -> 
             let _  = toScreen("\nInternal error: Missing type: " ^ printQualifiedId qid ^ "\n") in
             "<Undefined Type>")
      | Property prop -> ppProperty c prop
      | Pragma(beg_str,mid_str,end_str,pos) ->
        MProof(mkString [beg_str, mid_str, end_str] " ", pos)
      | Comment (str,pos) ->
        MComment(str, pos)

 op  ppOpInfo :  Context -> Bool -> Bool -> Aliases * Fixity * MSTerm -> Position -> String
 def ppOpInfo c decl? def? (aliases, fixity, dfn) pos =
   let (tvs, srt, term) = unpackTerm dfn in
   let name = ppQualifiedId (head aliases) in  (* taking only the first name; aliases are mainly created by colimits that have to identify symbols *)
   let tvsS = map ppID tvs in
   let tpOpt = if decl? then Some (ppType c srt) else None in
   let defOpt = if decl? \_and def? \_and (case term of | Any _ -> false | _ -> true)
      then Some (ppTerm c term) else None in
   let notOpt = if decl? then ppFixity fixity else None in
       ConstDec(name, "op", tvsS, tpOpt, defOpt, notOpt, pos)

 op  ppTypeInfo : Context -> Bool -> List QualifiedId * MSType -> Position -> String
 def ppTypeInfo c full? (aliases, dfn) pos =
   let (tvs, srt) = unpackType dfn in
   let name = ppQualifiedId (head aliases) in
   let tvsS = map ppID tvs in
   let defOpt = if full? && (case srt of Any _ -> false | _ -> true)
                then Some (ppType c srt) else None
   in ConstDec(name, "type", tvsS, Some (SW("type")), defOpt, None, pos)

 op  ppProperty : Context -> Property -> String
 def ppProperty c (propType, name, tvs, term, pos) =
     ConstDec("", ppPropertyType propType, map ppID tvs, Some (ppTerm c term), None, None, pos)
 
 op  ppPropertyType : PropertyType -> String
 def ppPropertyType propType =
     case propType of
       | Axiom -> "axiom"
       | Theorem -> "theorem"
       | Conjecture -> "conjecture"
       | any ->
            fail ("No match in ppPropertyType with: '"
               ^ (anyToString any)
               ^ "'")
(*
 op  ppRenaming : Renaming -> WLPretty
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
*)

%% printing terms

 op  ppTerm : Context -> MSTerm -> String
 def ppTerm c term =
   let pos = termAnn term in
    case term of
      | Apply (term1, term2, _) -> SApp("apply", [ppTerm c term1, ppTerm c term2], pos)
      | ApplyN (terms, _) -> SApp("apply", map (ppTerm c) terms, pos)
      | Record (fields,_) -> ( 
        case fields of
          | [] -> SApp("tuple", [], pos)
          | ("1",_) :: _ ->
            let def ppField (_,y) = ppTerm c y in
            SApp("tuple", map ppField fields, pos)
          | _ ->
            let def ppField (x,y) = (ppID x, ppTerm c y) in
            MRecord(map ppField fields, false, pos)
      )
      | The (var,term,_) -> MBind("the", [ppVar c var], ppTerm c term, pos)
      (* quantifiers *)
      | Bind (binder,vars,term,_) -> MBind(SW(ppBinder binder), map (ppVar c) vars, ppTerm c term, pos)
      (* let (pattern = term)* in term, must be uncurried into "let pattern = term in ... in term"  *)
      | Let (patTerms,term,_) ->
          let def folder ((pattern: MSPattern, df: MSTerm), sofar: String): String =
            let pVarsS = map (ppVar c) (patternVars pattern) in
            let patternS = ppPattern c pattern in
            let dfS = ppTerm c df in
            MBindN("let", pVarsS, [patternS, dfS, sofar], pos)
          in foldr folder (ppTerm c term) patTerms
      (* letrec f = ... f ... in term *)
      | LetRec (decls,term,_) -> 
          let def ppDecl ((v,tp),df) = MVarDef(ppID v, Some (ppType c tp), Some (ppTerm c df), pos)
          in MBind(SW("letrec"), map ppDecl decls, ppTerm c term, pos)
      | Var ((v,_),_) -> MVar(ppID v, pos)
      (* constants, see ppFun *)
      | Fun (fun,ty,_) ->
        if c.printTypes? (* ??? *)
          then ppFunWithType c fun ty pos
          else ppFun fun pos
      (* Lambda takes list of pattern-guard-case tuples *)
      | Lambda (match,_) -> SApp("lambda", ppMatch c match, pos)
      | IfThenElse (pred,term1,term2,_) -> SApp("if", [ppTerm c pred, ppTerm c term1, ppTerm c term2], pos)
      | Seq (terms,_) -> SApp("sep", map (ppTerm c) terms, pos)
      | Pi(tvs,term1,_) -> if tvs = [] then ppTerm c term1
          else MBind(SW("pi"), map (fn tv -> MVarDec(tv, Some (SW("type")), noPos)) tvs, ppTerm c term1, pos)
      | And(terms,_) -> SApp("colimit_and", map (ppTerm c) terms, pos)
      | Any(_) -> SWP("any", pos)
      | TypedTerm (tm,srt,_) ->
          SApp("sorted", [ppTerm c tm, ppType c srt], pos)
      | Transform(tr, _) -> fail ("no case for Transform")
      | mystery -> fail ("No match in ppTerm with: '" ^ (anyToString mystery) ^ "'")

 op  ppBinder : Binder -> String
 def ppBinder binder =
    case binder of
      | Forall -> "forall"
      | Exists -> "exists"
      | Exists1 -> "exists1"

 (* variable declarations ??? can we check if the type was infered? *)
 op  ppVar : Context -> MSVar -> String
 def ppVar c (id,srt) =
    if c.printTypes?
      then MVarDec(ppID id, Some (ppType c srt), noPos)
      else MVarDec(ppID id, None, noPos)

 (* free variables of a patterns ??? remove duplicates? *)
 op  patternVars: MSPattern -> List MSVar
 def patternVars pat =
   case pat of
     | AliasPat     (p1,p2,   _) -> (patternVars p1) ++ (patternVars p2)
     | VarPat       (v,       _) -> [v]
     | EmbedPat     (_,pO,_,  _) -> (case pO of | None -> Nil | Some p -> patternVars p)
     | RecordPat    (fields,  _) -> flatten (map (fn (_,p) -> patternVars p) fields)
     | WildPat      (tp,      _) -> [("", tp)] 
     | BoolPat      _            -> []
     | NatPat       _            -> []
     | CharPat      _            -> []
     | StringPat    _            -> []
     | QuotientPat  (p, _, _, _) -> patternVars p
     | RestrictedPat(p, _,    _) -> patternVars p
     | TypedPat     (p, _,    _) -> patternVars p

 op  ppPattern : Context -> MSPattern -> String
 def ppPattern c pattern =
     case patAnn pattern of
          | File(fil_nm,(x1,x2,x3),(y1,y2,y3)) -> ""
            (* ???
            (if fil_nm = c.fileName then [] else [ppID fil_nm])
                ppNum x1, ppNum x2, ppNum x3, ppNum y1, ppNum y2, ppNum y3
                ppPattern1 c pattern
                *)
          | _ -> ppPattern1 c pattern

 (* where possible, patterns are transformed into a term, which is then printed
    other cases are copy-pasted and adapted from ppTerm *)
 op  ppPattern1 : Context -> MSPattern -> String
 def ppPattern1 c pattern =
   let pos = patAnn pattern in
   case pattern of
      | WildPat (srt,_) -> MVar("", pos)
      | AliasPat (p1,p2,_) -> SApp("alias", [ppPattern c p1, ppPattern c p2], pos) 
      | VarPat v -> ppTerm c (Var v)
      | StringPat (str,_) -> ppFun (String str) pos
      | BoolPat (b,_) -> ppFun (Bool b) pos
      | CharPat (chr,_) -> ppFun (Char chr) pos
      | NatPat (int,_) -> ppFun (Nat int) pos
      | EmbedPat (constr,patO,srt,b) ->
         (case patO of
           | None     -> ppTerm c (Fun (Embed (constr,false), srt, b))
           | Some pat ->
              let opS =  ppTerm c (Fun(Embed (constr, true), srt, noPos)) in
              SApp("apply", [opS, ppPattern c pat], b)
         )
      | RecordPat (fields,_) -> (
        case fields of
          | [] -> SApp("tuple", [], pos)
          | ("1",_) :: _ ->
            let def ppField (_,y) = ppPattern c y in
            SApp("tuple", map ppField fields, pos)
          | _ ->
            let def ppField (x,y) = (ppID x, ppPattern c y) in
            MRecord(map ppField fields, false, pos)
      )
      | QuotientPat (pat,typename,tys,_) -> "" % ???
      | RestrictedPat (pat,term,_) -> "" % ???
      | TypedPat (pat,srt,_) -> SApp("sorted ", [ppPattern c pat, ppType c srt], pos)
      | mystery -> fail ("No match in ppPattern with: '" ^ (anyToString mystery) ^ "'")

 op  ppMatch : Context -> MSMatch -> List String
 def ppMatch c cases =
    let def ppCase (pattern,guard,term) =
        MBindN("case", map (ppVar c) (patternVars pattern), [ppPattern c pattern, ppTerm c guard, ppTerm c term], noPos)
    in
      map ppCase cases

 op  ppFunWithType: Context -> MSFun -> MSType -> Position -> String
 def ppFunWithType c fun ty pos = SApp("sorted", [ppFun fun pos, ppType c ty], pos)

 op  ppFun : MSFun -> Position -> String
 def ppFun fun pos = case fun of
      | Not       -> SWP("not", pos)
      | And       -> SWP("and", pos)
      | Or        -> SWP("or", pos)
      | Implies   -> SWP("implies", pos)
      | Iff       -> SWP("iff", pos)
      | Equals    -> SWP("equals", pos)
      | NotEquals -> SWP("notequals", pos)
      | Quotient qid  -> ppFunQid "quotient" qid pos
      | PQuotient qid -> ppFunQid "pquotient" qid pos
      | Choose qid -> ppFunQid "choose" qid pos
      | PChoose qid -> ppFunQid "choose" qid pos
      | Restrict -> SWP("restrict", pos)
      | Relax -> SWP("relax", pos)
      | Op (qid,_) -> MUConst(ppQualifiedId qid, pos)
      | Project id -> MProjection(ppID id, pos)
      | RecordMerge -> SWP("merge", pos)
      | Embed (qid,_) -> MUConst(ppQualifiedId qid, pos) %% legacy ADT constructor; should now be special case of Op 
      | Embedded qid  -> MUConst(ppQualifiedId qid ^ "?", pos) %% legacy test of whether constructed qid; ?-convention is not official 
      | Select id -> fail ("no case for Select") %% should be impossible
      | Nat n -> MLit("Nat", show n, pos)
      | Char chr -> MLit("Char", show chr, pos)
      | String str -> MLit("String", str, pos)
      | Bool b -> MLit("Bool", ppBool b, pos)
      | OneName (id,fxty) -> MUConst(ppID id, pos)                                       %% should be impossible
      | TwoNames (id1,id2,fxty) -> MUConst(ppQualifiedId (Qualified (id1,id2)), pos)     %% should be impossible
      | mystery -> fail ("No match in ppFun with: '" ^ (anyToString mystery) ^ "'")

 op  ppFunQid : String -> QualifiedId -> Position -> String
 def ppFunQid funName qid pos = SApp(funName, [MUConst(ppQualifiedId qid, noPos)], pos)
      
 op  ppBool : Bool -> String
 def ppBool b =
    case b of
      | true -> "true"
      | false -> "false"

%% printing types

 op  ppType : Context -> MSType -> String
 def ppType c ty =
    let pos = typeAnn ty in
    case ty of
      | Arrow (ty1,ty2,_) -> SApp("arrow", [ppType c ty1, ppType c ty2], pos)
      | Product (fields,_) -> ( 
        case fields of
            [] -> SApp("Tuple", [], pos)
          | ("1",_)::_ ->
            let def ppField (_,y) = ppType c y in
            SApp("Tuple", map ppField fields, pos)
          | _ ->
            let def ppField (x,y) = (ppID x, ppType c y) in
            MRecord(map ppField fields, true, pos)
      )
      (* ADTs (constructors are nullary, unary, or unary taking a tuple; by convention, ADTs are not anonymous *)
      | CoProduct (constructors,_) ->
        let def ppConstructor (qid,optTy) =
          case optTy of
            | None -> (ppQualifiedId qid, SApp("Tuple", [], noPos))
            | Some ty -> (ppQualifiedId qid, ppType c ty)
        in SApp("inductive", [MRecord(map ppConstructor constructors, true, noPos)], pos)
      | Quotient (ty,term,_) -> SApp("quotient", [ppType c ty, ppTerm c term], pos)
      | Subtype (ty,term,_) -> SApp("restrict", [ppType c ty, ppTerm c term], pos)
      | Base (qid,[],_) -> MUConst(ppQualifiedId qid, pos)
      | Base (qid,tys,_) -> SApp("apply", MUConst(ppQualifiedId qid, noPos) :: map (ppType c) tys, pos)
      | Boolean _ -> SWP("bool", pos)
      | TyVar (tyVar,_) -> MVar(ppID tyVar, pos)
      | Pi(tvs,ty,_) -> if tvs = [] then ppType c ty
          else MBind(SW("pi"), map (fn tv -> MVarDec(tv, Some (SW("type")), noPos)) tvs, ppType c ty, pos)
      | And(types,_) -> SApp("colimit_and", map (ppType c) types, pos)
      | Any(_) -> SWP("any", pos)
      | MetaTyVar (mtyVar, _) -> fail("no case for metatyvar")
      | mystery -> fail ("No match in ppType with: '" ^ (anyToString mystery) ^ "'")

%% printing morphisms

 op  ppMorphism: Context -> Morphism -> String
 def ppMorphism c {dom,cod,typeMap,opMap,pragmas,sm_tm} =
    let dom = ppUIDorFull c (Spec dom) None "name " in
    let codom = ppUIDorFull c (Spec cod) None "name " in
    let typeAssignments = ppIdMap typeMap in
    let opAssignments = ppIdMap opMap in
    let axiomAssignments = (map (fn ((p1,p2,p3),pos) -> p1 ^ p2 ^ p3) pragmas) in
    ""

 op  ppIdMap: QualifiedIdMap -> List String
 def ppIdMap idMap = map (fn (d,r) -> Assignment(ppQualifiedId d, MUConst(ppQualifiedId r, noPos))) (mapToList idMap)

%% printing notations

 op  ppFixity : Fixity -> Option String
 def ppFixity fix =
    case fix of
      | Infix (assoc, n) ->
        Some (MInfix(case assoc of | Left  -> "-left" | Right -> "-right"| NotAssoc -> "", show n))
      | _  -> None

%% ungrouped
 (*
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
     | Import  term                   -> ppConcat [ppString "import [",
                                                   ppSep (ppString ", ") (map (ppSCTerm c) term),
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


 op  ppIdInfo : List QualifiedId -> String
 def ppIdInfo qids = mkString (map ppQualifiedId qids) ", "

 op  evalSCTerm: Context -> SCTerm -> Option Value
 def evalSCTerm c term =
    let def handler _ = return None in
    let prog = {setCurrentUID(c.currentUID);
                (val,_,_) <- evaluateTermInfo term;
                return (Some val)}
    in
    run (catch prog handler)
*)
endspec
