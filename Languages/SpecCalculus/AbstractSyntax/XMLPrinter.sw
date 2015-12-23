(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% This spec defines inductive functions to print out the abstract syntax in XML format.
% The specific XML format used is the MMT dialect of the OMDoc language.                    
%
% The generated files can be read in by MMT for further processing.
% See
% - git@gl.mathhub.info:Specware/Library.git
%   for an MMT repository of the (public parts of the) Specware library
% - https://svn.kwarc.info/repos/MMT
%   for documentation, source, and binaries of MMT
% 
% The top level function of the induction is printUIDtoFile.
% It can be called from the command line using the script specware-xmlprint
% (currently only Windows but easily adaptible to Unix).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


XMLPrinter qualifying spec 

 import Types
 import /Languages/MetaSlang/AbstractSyntax/AnnTerm
 import /Languages/MetaSlang/Transformations/NormalizeTypes
 import /Languages/MetaSlang/Specs/Printer
 % import /Languages/MetaSlang/Specs/Position
 import /Languages/SpecCalculus/Semantics/Value
 import /Languages/SpecCalculus/Semantics/Monad
 
 %% Give the signature of utilities so we don't have to import them
 op  Specware.evaluateUnitIdWithErrors : String -> Option Value * List(String * Position)
 op  SpecCalc.findUnitIdForUnit: Value * GlobalContext -> Option UnitId
 op  SpecCalc.findDefiningTermForUnit: Value * GlobalContext -> Option SCTerm
 op  SpecCalc.pathStringToCanonicalUID : String * Bool -> UnitId
 % op  SpecCalc.evaluateTermInfo: SCTerm -> SpecCalc.Env ValueInfo
 type SpecElem = SpecElemTerm


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% abbreviations for conveniently creating XML and MMT
 %% These look like constructors but actually return strings

  (* concatenates a list of strings inserting a separator *)
  op  mkString : List String -> String -> String
  def mkString l sep =
    case l of
     | Nil -> ""
     | Cons(x, Nil) -> x
     | Cons(hd,tl) -> hd ^ sep ^ (mkString tl sep)

  (* true if s starts with prefix *)
  op  startsWith(s: String, prefix: String) : Boolean =
    sublistAt?(explode prefix, 0, explode s)
  
  (* <tag atts><metadata>...pos...</metadata> *)
  op ElemOpen(tag: String, atts: List String, pos: Position): String =
    let posS = SRef(pos) in
    let posElem = if pos = noPos then "" else Elem("metadata", [], [SRefLink(posS)], noPos) in
    let openTag = "<" ^ tag ^ (flatten atts) in
    openTag ^ ">" ^ posElem 
  (* </tag> *)
  op ElemClose(tag:String): String  = "</" ^ tag ^ ">"
  (* <tag atts><metadata>...pos...</metadata>children</tag> *)
  op Elem(tag: String, atts: List String, children: List String, pos: Position): String =
    let posS = SRef(pos) in
    let posElem = if pos = noPos then [] else [Elem("metadata", [], [SRefLink(posS)], noPos)] in
    let openTag = "<" ^ tag ^ (flatten atts) in
    let body = mkString (posElem ++ children) "\n" in
    if body = "" then openTag ^ "/>" else openTag ^ ">" ^ body ^ ElemClose(tag) 
    
  op xmlEncode(s: String): String =
   translate (fn c -> case c | #& -> "&amp;" | #" -> "&quot;" | #< -> "&lt;" | c -> show c) s
 
  (* k="v" *)
  op Att(k: String, v: String) : String =
    " " ^ k ^ "=\"" ^ (xmlEncode v) ^ "\""
 
  op Document (file: String, spc: String) : String =
    Elem("omdoc", [Att("base", file)], [spc], noPos)
  op DocumentOpen(file: String) : String =
    ElemOpen("omdoc", [Att("base", file)], noPos)
  op DocumentClose:String = ElemClose("omdoc")
 
  op Theory (ns: String, name: String, decls: List String, pos: Position) : String =
    Elem("theory", [Att("base", ns), Att("name", name), Att("meta","/Specware?Specware")], decls, pos)
  op TheoryOpen(ns: String, name: String, pos: Position) : String =
    ElemOpen("theory", [Att("base", ns), Att("name", name), Att("meta","/Specware?Specware")], pos)
  op TheoryClose: String = ElemClose("theory")
    
  op ConstDec (name: String, role: String, tyvar: List String, tp: Option String, df: Option String, not: Option String, pos: Position) : String =
    let def wrapTyvars comp binder termOpt = case termOpt
      | None -> Nil
      | Some term ->
        let tyvarS = map (fn v -> MVarDec(v, Some (SW("tp")), noPos)) tyvar in
        let tyvarTerm = if tyvar = Nil then term else MBind(LF(binder), tyvarS, [term], noPos) in
        [Elem(comp, [], [tyvarTerm], noPos)] in
    let tpS = wrapTyvars "type" "Pi" tp in
    let dfS = wrapTyvars "definition" "lambda" df in
    let notS = case not of | None -> Nil | Some n -> [Elem("notations", [], [n], noPos)] in
    Elem("constant", [Att("name", name), Att("role", role)], tpS ++ dfS ++ notS, pos)
    
  op Assignment(name: String, df: String): String = 
    ConstDec(name, "assignment", Nil, None, Some df, None, noPos)
 
  op InclDec (frm: String, pos: Position) : String =
    Elem("import", [Att("from", frm)], [], pos)
  
  op MInfix(assoc: String, prec: String): String =
    let atts = [Att("fixity", "infix"^assoc), Att("precedence", prec), Att("arguments", "0 2")] in
    Elem("notation", atts, [], noPos)
    
  op MConst (nsmod: Option (String * String), name: String, pos: Position): String =
    let modAtt = case nsmod
        | None -> Nil
        | Some (ns,mod) -> [Att("base", ns), Att("module", mod)] in
    Elem("OMS", modAtt ++ [Att("name",name)], [], pos)
    
  op MVar (name: String, pos: Position): String =
    Elem("OMV", [Att("name", name)], [], pos)
    
  op MLit (tp: String, l: String, pos: Position): String =
    Elem("OMLIT", [Att("type", SWURI(tp)), Att("value", l)], [], pos)
    
  op MApp (fun: String, args: List String, pos: Position): String =
    Elem("OMA", [], fun :: args, pos)
    
  op MBind (binder: String, vars: List String, body: List String, pos: Position): String =
    Elem("OMBIND", [], [binder, MContext(vars)] ++ body, pos)
  
  op MRecord(fields: List (String * String), types: Bool, pos: Position): String =
    let (sym,tag) = if types then ("Record","type") else ("record","definition") in
    let fieldsS = map (fn (key, value) -> Elem("OML", [Att("name", key)], [Elem(tag,[], [value], noPos)], noPos)) fields in
    SApp(SW(sym), fieldsS, pos)
  op MProjection(field: String, pos: Position): String =
    Elem("OML", [Att("name", field)], [], pos)
 
  (* <OMBVAR>...</OMBVAR> *)
  op MContext(vds: List String): String =
    Elem("OMBVAR", [], vds, noPos)
  (* <OMV name=name><type>...</type><definition>...</definition></OMV> *)
  op MVarDef(name: String, tpOpt: Option String, dfOpt: Option String, pos: Position): String =
    let tp = case tpOpt of | None -> Nil | Some t -> [Elem("type", [], [t], noPos)] in
    let df = case dfOpt of | None -> Nil | Some d -> [Elem("definition", [], [d], noPos)] in
    Elem("OMV", [Att("name", name)], tp ++ df, pos)
 
  (* <OMV name=name><type>...</type></OMV> *)
  op MVarDec(name: String, tp: Option String, pos: Position): String =
    MVarDef(name, tp, None, pos)
 
  op MProof(text: String, pos: Position): String = ""
  op MComment(text: String, pos: Position): String = ""
 
  (* Specware symbol OMS *)
  op SWP(name: String, pos: Position): String =
    MConst(Some ("/Specware","Specware"), name, pos)
  op SW(name: String): String = SWP(name, noPos)
  (* LF symbol OMS *)
  op LF(name: String): String =
    MConst(Some ("ur:","LF"), name, noPos)
  (* Specware symbol URI *)
  op SWURI(name: String): String = "/Specware?Specware?" ^ name
  (* application of a Specware symbol *)
  op SApp(name: String, args: List String, pos: Position): String =
    MApp(SW(name), args, pos)
  (* application of a Specware binder *)
  op SBindN (bindername: String, vars: List String, body: List String, pos: Position): String =
    MBind(SW(bindername), vars, body, pos)
  op SBind(bindername: String, vars: List String, body: String, pos: Position): String =
    SBindN(bindername, vars, [body], pos)
  (* user-defined constant; currently the module is not known *)
  op MUConst (name: String, pos: Position): String =
    MConst(None, name, pos)
 
  (* <errors>...</errors/> *)
  op Errors(errs: List String): String =
    Elem("errors", [], errs, noPos)
 
  (* <error .../> *)
  op Error(msg: String, pos: Position): String =
    let posS = SRef(pos) in
    Elem("error", [Att("target", "specware-omdoc"),
        Att("type", "info.kwarc.mmt.api.SourceError"), 
        Att("shortMsg", msg), Att("level", "1"), Att("sref", posS)], [], noPos)
 
  (* file:/PATH/TO/FILE#BEGIN-END *)
  op SRef(pos: Position): String = case pos
    | File (file, beg, ed) ->
      let slashOpt = if startsWith(file, "/") then "" else "/" in
      "file:" ^ slashOpt ^ file ^ "#" ^ Pos(beg) ^ ":" ^ Pos(ed)
    | _ -> if pos = noPos then "" else "#-1.0.0:-1.0.0" (* other positions are not useful, this case includes noPos *)
 
  (* byte.line.end, all starting at 0 *)
  op Pos(line: Nat, col: Nat, byte: Nat): String =
    mkString (map show [byte-1, line-1, col]) "."
 
  (* <link rel="..." resource="res"/> *)
  op SRefLink(res: String): String =
    Elem("link", [Att("rel", "http://cds.omdoc.org/mmt?metadata?sourceRef"), Att("resource", res)], [], noPos)
 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% The XMLPrinter is a big induction over the elaborated data structures, mostly AnnTerm and Spec
 
 %% the context of the induction
  type Context = {printTypes?: Bool,
                  fileName: String,
                  physLogMap: List (String * String), (* (physical,logical) URI pairs *)
                  currentUID: UnitId,
                  uidsSeen: List UnitId, % Used to avoid infinite recursion because of circularity
                  outStream: IO.Stream,
                  recursive?: Bool}

 (* replace the phyiscal prefix with the corresponding logical one *)
 op  physicalToLogicalPath : Context -> String -> String
 def physicalToLogicalPath c p =
     case findLeftmost (fn (phys,log) -> startsWith(p, phys)) c.physLogMap
        | None -> p
        | Some (phys,log) -> log ^ subFromTo(p, length phys, length p)
                  
 %% toplevel functions
  (* main function, if recursive, also call on all imported Specs
     arguments: phyiscal root, logical root, absolute path to UID, flag for recursive printing *)
  op  printUIDtoFile: String * String * String * Bool -> String
  def printUIDtoFile (phys, log, uid_str_ext, recursive?) =
     let uid_str = case (reverse (explode uid_str_ext)) of
      | #w :: #s :: #. :: rest -> implode (reverse rest)
      | _ -> uid_str_ext
     in
     let (valOpt, errs) = evaluateUnitIdWithErrors uid_str in
     let physLogMap = [(phys,log)] in
     let uid = pathStringToCanonicalUID(uid_str, false) in
     let outFile = uidToOutFileName uid in
     let xmlFile = outFile ^ ".omdoc" in
     let errFile = outFile ^ ".sw.err" in
     let _ = ensureDirectoriesExist xmlFile in
     let _ = writeStringToFile(ppErrors errs, errFile) in
     case valOpt of
       | Some val ->
          (printValueTop(val,physLogMap,uid,[],uid_str,recursive?,xmlFile); "OK")
       | None -> "no value for uid found"

  (* returns the UnitId and the string to use as its file name (without extension, possibly ending in #name) *)
  op  uidStringForValue: Value -> Option (UnitId * String)
  def uidStringForValue val =
     case uidStringPairForValue val of
       | None -> None
       | Some(uid,filnm,hash) -> Some(uid,filnm ^ hash)
 
  (* there can be named specs inside a file; in that case #suffixes are used to form UnitIds *)
  (* returns the UnitId, the file name string (without extension), and #name if the unit is named *) 
  op  uidStringPairForValue: Value -> Option (UnitId * String * String)
  def uidStringPairForValue val =
     case MonadicStateInternal.readGlobalVar "GlobalContext" of
       | None -> None
       | Some global_context ->
     case findUnitIdForUnit(val,global_context) of
       | None -> None
       | Some uid ->
           Some (uid, uidToOutFileName uid, case uid.hashSuffix | Some loc_nm -> "#" ^ loc_nm | _ -> "")
 
  (* path/omdoc/name[#suffix] *)
  op  uidToOutFileName : UnitId -> String
  def uidToOutFileName uid =
    (* path: path of the file defining the unit (with device, without extension) *) 
    (* device?: true if path begins with Windows device name, i.e., ends in : *)
    let suffix = case uid.hashSuffix | None -> "" | Some s -> "#" ^ s in
    let path = uid.path in
    let (device_dir, name) = (butLast path, last path) in
    let (device, dir) = if deviceString? (head path) then
       (head device_dir, tail device_dir) else ("", device_dir)
    in (mkString ([device] ++ dir ++ ["omdoc", name]) "/") ^ suffix
 
  op  deleteASWFilesForUID: String -> ()
  def deleteASWFilesForUID uidstr =
     case evaluateUnitIdWithErrors uidstr of
       | (Some val, _) ->
         deleteASWFilesForVal val
       | _ -> ()
 
  op  deleteASWFilesForVal: Value -> ()
  def deleteASWFilesForVal val =
     case uidStringForValue val of
       | None -> ()
       | Some (_,uidstr) ->
         let fil_nm = uidstr ^ ".omdoc" in
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

  (* called for recursively printing a value, if 'recursive' is set *)
  op  ensureValuePrinted: Context -> Value -> String
  def ensureValuePrinted c val =
     case uidStringForValue val of
       | None -> "skipped"
       | Some (uid,fil_nm) ->
         let omdoc_fil_nm = fil_nm ^ ".omdoc" in
         printValueTop(val, c.physLogMap, uid, c.uidsSeen, fil_nm, c.recursive?, omdoc_fil_nm)
 
  (* called for printing the top value that was provided by the main call *)
  op  printValueTop : Value * List (String * String) * UnitId * List UnitId * String * Bool * String -> String
  def printValueTop (value, pLMap,uid,seen, fN,recursive?, outFile) =
   let def writer stream =
     printValue {printTypes? = true,
                 physLogMap = pLMap,
                 currentUID = uid,
                 fileName = fN,
                 outStream = stream,
                 uidsSeen = uid :: seen,
                 recursive? = recursive?}
       value
   in IO.withOpenFileForWrite(outFile, writer)
 
  (* prepare the context and print a value (toplevel or recursive) *)
  op  printValue : Context -> Value -> String
  def printValue c value =
     let _ = streamWriter(c.outStream, DocumentOpen(physicalToLogicalPath c ("file:" ^ c.fileName))) in
     let _ = streamWriter(c.outStream, ppValue c value None) in
     let _ = streamWriter(c.outStream, DocumentClose)
     in "streamed document\n"

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
     let (ns,name) = UIDtoMMTURI c c.currentUID in
      (* get the SCTerm that this Spec is derived from, not necessarily useful *)
     let specOrigin =
                  case optTm of
                    | Some def_tm -> ppSpecOrigin c def_tm
                    | None ->
                  case findTermForUnitInCache(Spec spc) of
                    | None -> "elements"
                    | Some def_tm -> ppSpecOrigin c def_tm
     in
     (streamWriter(c.outStream, TheoryOpen(ns, name, noPos));
      ppSpecElements c norm_spc norm_spc.elements;
      streamWriter(c.outStream, TheoryClose);
      "streamed theory\n"
     )
 
  op  SpecCalc.findTermForUnitInCache: Value -> Option SCTerm
  def findTermForUnitInCache val =
     case readGlobalVar "GlobalContext" of
       | None -> None
       | Some global_context ->
         findDefiningTermForUnit(val,global_context)
     
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
           | Some val -> ppUIDorFull c val (Some tm)
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
 
  (* returns the URI of a value if it is a named value. Also makes sure that spec is printed if recursive. *) 
  op  ppUIDorFull: Context -> Value -> Option SCTerm -> String
  def ppUIDorFull c val opt_val_tm =
     case findUnitIdforUnitInCache val of
       | Some uid ->
         let _ = if c.recursive? && uid nin? c.uidsSeen
           then ensureValuePrinted c val 
           else ""
         in
           (ppUID c uid)
       | None -> "?UnknownValueOmitted" (* happes, e.g., for "Q qualifying S" *)
 
  op  SpecCalc.findUnitIdforUnitInCache: Value -> Option UnitId
  def findUnitIdforUnitInCache val =
     case readGlobalVar "GlobalContext" of
       | None -> None
       | Some global_context ->
         findUnitIdForUnit(val,global_context)
 
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
     let elemS = case elem of
       | Import (im_sc_tm,im_sp,im_elements,pos) ->
         InclDec(ppUIDorFull c (Spec im_sp) (Some im_sc_tm), pos)
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
     in
       (streamWriter(c.outStream, elemS); "streamed element\n")
 
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
    in ConstDec(name, "type", tvsS, Some (SW("tp")), defOpt, None, pos)
 
  op  ppProperty : Context -> Property -> String
  def ppProperty c (propType, name, tvs, term, pos) =
      ConstDec(ppQualifiedId name, ppPropertyType propType, map ppID tvs, Some (SApp("property", [ppTerm c term], noPos)), None, None, pos)
  
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
 (* old code
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
       | The (var,term,_) -> SBind("the", [ppVar c var], ppTerm c term, pos)
       (* quantifiers *)
       | Bind (binder,vars,term,_) -> SBind(ppBinder binder, map (ppVar c) vars, ppTerm c term, pos)
       (* let (pattern = term)* in term, must be uncurried into "let pattern = term in ... in term"  *)
       | Let (patTerms,term,_) ->
           let def folder ((pattern: MSPattern, df: MSTerm), sofar: String): String =
             let pVarsS = map (ppVar c) (patternVars pattern) in
             let patternS = ppPattern c pattern in
             let dfS = ppTerm c df in
             SBindN("let", pVarsS, [patternS, dfS, sofar], pos)
           in foldr folder (ppTerm c term) patTerms
       (* letrec f = ... f ... in term *)
       | LetRec (decls,term,_) -> 
           let def ppDecl ((v,tp),df) = MVarDef(ppID v, Some (ppType c tp), Some (ppTerm c df), pos)
           in SBind("letrec", map ppDecl decls, ppTerm c term, pos)
       | Var ((v,_),_) -> MVar(ppID v, pos)
       (* constants, see ppFun *)
       | Fun (fun,ty,_) ->
         if c.printTypes? (* ??? *)
           then ppFunWithType c fun ty pos
           else ppFun fun pos
       (* Lambda takes list of pattern-guard-case tuples *)
       | Lambda (match,_) -> SApp("lambda", ppMatch c match, pos)
       | IfThenElse (pred,term1,term2,_) -> SApp("if", [ppTerm c pred, ppTerm c term1, ppTerm c term2], pos)
       | Seq (terms,_) -> SApp("seq", map (ppTerm c) terms, pos)
       | Pi(tvs,term1,_) -> if tvs = [] then ppTerm c term1
           else MBind(LF("lambda"), map (fn tv -> MVarDec(tv, Some (SW("tp")), noPos)) tvs, [ppTerm c term1], pos)
       | And(terms,_) -> SApp("colimit_and", map (ppTerm c) terms, pos)
       | Any(_) -> SWP("any", pos) %% internal placeholder, should not come up ideally 
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
         let vars = (patternVars pattern) in
         let args = [ppPattern c pattern, ppTerm c guard, ppTerm c term] in
         if vars = Nil then
           SApp("case", args, noPos)
         else
           SBindN("case", map (ppVar c) vars, args, noPos)
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
       | PQuotient qid -> ppFunQid "quotient" qid pos
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
       | Nat n -> MLit("nat", show n, pos)
       | Char chr -> MLit("char", show chr, pos)
       | String str -> MLit("string", str, pos)
       | Bool b -> MLit("bool", ppBool b, pos)
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
           else MBind(LF("Pi"), map (fn tv -> MVarDec(tv, Some (SW("tp")), noPos)) tvs, [ppType c ty], pos)
       | And(types,_) -> SApp("colimit_and", map (ppType c) types, pos)
       | Any(_) -> SWP("any", pos)
       | MetaTyVar (mtyVar, _) -> fail("no case for metatyvar")
       | mystery -> fail ("No match in ppType with: '" ^ (anyToString mystery) ^ "'")
 
 %% printing morphisms
 
  op  ppMorphism: Context -> Morphism -> String
  def ppMorphism c {dom,cod,typeMap,opMap,pragmas,sm_tm} =
     let dom = ppUIDorFull c (Spec dom) None in
     let codom = ppUIDorFull c (Spec cod) None in
     let typeAssignments = ppIdMap typeMap in
     let opAssignments = ppIdMap opMap in
     let axiomAssignments = (map (fn ((p1,p2,p3),pos) -> p1 ^ p2 ^ p3) pragmas) in
     ""
 
  op  ppIdMap: QualifiedIdMap -> List String
  def ppIdMap idMap = map (fn (d,r) -> Assignment(ppQualifiedId d, MUConst(ppQualifiedId r, noPos))) (mapToList idMap)
 
 %% printing identifiers
 
  (* currently trivial, can be used for encoding names *)
  op  ppID: String -> String
  def ppID id = id
 
  (* module references *)
  op  ppUID : Context -> UnitId -> String
  def ppUID c uid =
    let (ns, name) = UIDtoMMTURI c uid in
    ns ^ "?" ^ (ppID name)
 
  (* DIR/FILE -> file:DIR?FILE; DIR/FILE#SPEC -> file/DIR?FILE#SPEC *)
  op  UIDtoMMTURI: Context -> UnitId -> String * String
  def UIDtoMMTURI c uid =
     let ns = physicalToLogicalPath c ("file:/" ^ (mkString (butLast uid.path) "/")) in
     case uid.hashSuffix
       | Some h -> (ns, last uid.path ^ "#" ^ h)
       | None -> (ns, last uid.path)

  (* names of Specware symbols are either name or name.name;
     the qualifier can be chosen freely and is unrelated to the name of the theory *)
  op  ppQualifiedId : QualifiedId -> String
  def ppQualifiedId (Qualified (q, id))  =
    if q = UnQualified then 
      ppID id
    else 
      (ppID q) ^ "." ^ (ppID id)
 
 %% printing notations
 
  op  ppFixity : Fixity -> Option String
  def ppFixity fix =
     case fix of
       | Infix (assoc, n) ->
         Some (MInfix(case assoc of | Left  -> "-left" | Right -> "-right"| NotAssoc -> "", show n))
       | _  -> None

 %% printing errors 
  op  ppErrors : List (String * Position) -> String
  def ppErrors errs = Errors (map ppError errs)

  op  ppError : String * Position -> String
  def ppError (msg, pos) = Error(msg, pos)

endspec

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
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
 
  (*
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
 *)
 
