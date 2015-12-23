(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%% This is a pretty-printer for specs that produces output in a Lisp-like
%% s-expression-based format.  Having sub-terms printed within balanced
%% parentheses makes it easy to navigate around the printed representation of a
%% spec (e.g., using Emacs keys to skip over large 
%% expressions between balanced parentheses).

%% This file is a modification of ASW_Printer.sw, and it is not yet finished.  I
%% am changing the printing of constructs to use s-expressions on an as-needed
%% basis. -EWS

%% The top level function to call is evaluateShowData.

%% TODO: Print to the screen instead of a file?
%% TODO: Print things like this: /\ with vertical bars (or in some other way that doesn't confuse emacs)
%% TODO: strings that include quotes (single or double?) seem to interfere with the
%% ability to jump over complete S-expressions in the output of this
%% tool.  Perhaps PPString should escape such characters or something?

ShowData qualifying spec 

import Types
import /Languages/MetaSlang/AbstractSyntax/AnnTerm
import /Languages/MetaSlang/Specs/Proof
import /Library/PrettyPrinter/WadlerLindig
% import /Languages/MetaSlang/Specs/Printer
import /Languages/SpecCalculus/Semantics/Value
import /Languages/SpecCalculus/Semantics/Environment
 %import /Languages/SpecCalculus/Semantics/Monad
import ShowUtils

%% --------------------------------------------------------------------------------
%% Give the signature of utilities so we don't have to import them

%type GlobalContext
%op  MonadicStateInternal.readGlobalVar : [a] String -> Option a
%  op  Specware.evaluateUnitId: String -> Option Value
%  op  SpecCalc.findDefiningTermForUnit: Value * GlobalContext -> Option SCTerm
  %op  SpecCalc.uidToFullPath: UnitId -> String
%  op  SpecCalc.evaluateTermInfo: SCTerm -> SpecCalc.Env ValueInfo
  %op  SpecCalc.setCurrentUID : UnitId -> SpecCalc.Env ()

%Additional pretty-printer routines:
op ppGrConcat (x:List WLPretty) : WLPretty  = ppConcatGN 0 x
op ppGr1Concat (x:List WLPretty) : WLPretty = ppConcatGN 1 x
op ppGr2Concat (x:List WLPretty) : WLPretty = ppConcatGN 2 x
op ppNum (n:Int) : WLPretty = ppString(show n)
op ppSpace : WLPretty = ppString " "
op ppSpaceBreak : WLPretty = ppConcat[ppSpace, ppBreak]

%TODO: use this more
op ppWrapParens (pp : WLPretty) : WLPretty =
  ppConcat [ppString "(",
            pp,
            ppString ")"]

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
                %currentUID: UnitId,
                %uidsSeen: List UnitId,	% Used to avoid infinite recursion because of circularity
                recursive?: Bool,
                showImportedSpecs? : Bool  %Can cause exponential blowup.  Recommend importing /Library/Base/Empty into the spec being shown if you set this to true
                }

% op  showTerm : SCTerm -> String
% def showTerm term = ppFormat (ppSCTerm {printTypes? = true,
%					 printPositionInfo? = false,
%					 fileName = "",
%					 currentUID = ,
%					 recursive? = false}
%			         term)

op ppBool (b: Bool) : WLPretty =
  case b of
    | true -> ppString "true"
    | false -> ppString "false"

op ppLitString (id:String) : WLPretty = ppString(IO.formatString1("~A",id))  %%formatString1("~S",id)

%%% Identifiers have string quotes around them
op ppID (id: String) : WLPretty = ppLitString id

op ppUID (unitId:UnitId) : WLPretty =
  let ppLocal = ppUIDlocal unitId in
  case unitId of
    | {path=h::_,hashSuffix=_} ->
      if deviceString? h
        then ppLocal
      else ppAppend (ppString "/") ppLocal
    | _ -> ppLocal			% Shouldn't happen

op ppUIDlocal ({path, hashSuffix}: UnitId) : WLPretty =
  case hashSuffix of
    | None -> ppSep (ppString "/") (map ppID path)
    | Some suffix ->
      let def pp path =
      case path of
        | [] -> []
        | [x] -> [ppID(x ^ numberSignString ^ suffix)]
        | x::rp -> Cons(ppID x, pp rp)
      in
      ppSep (ppString "/") (pp path)
       
% %TODO wrap in parens
op ppStrings (strs : List String) : WLPretty =
  case strs of
    | [] -> ppString ""
    | hd::tl -> ppConcat ((ppString hd)::[(ppStrings tl)])

op ppUnitId (UID : UnitId) : WLPretty =
  ppConcat[ppString "((path ", 
           %ppStrings UID.path,  %TODO separate with spaces.
           ppSep ppSpace (map (ppString) UID.path),
           ppString ") (hashSuffix ", 
           (case UID.hashSuffix of None -> ppString "None" | Some str -> ppConcat [ppString "Some ", ppString str]),
           ppString "))"]
 
op ppRelativeUID (relUID : RelativeUID) : WLPretty =
  case relUID of
    | SpecPath_Relative unitId -> ppConcat [ppString "(SpecPath_Relative ", ppUnitId unitId, ppString")"] %ppAppend (ppString "/") (ppUIDlocal unitId)
    | UnitId_Relative   unitId -> ppConcat [ppString "(UnitId_Relative "   , ppUnitId unitId, ppString")"] %ppUIDlocal unitId
              
op ppSCTerm (c:Context) ((term, pos):SCTerm) : WLPretty =
  case term of
    | Print t ->
      ppConcat [ppString "print ",
                ppSCTerm c t]
    | UnitId unitId ->
      ppConcat [ppString "(UnitId ", ppRelativeUID unitId, ppString ")"]
    | Spec specElems -> 
      ppConcat [ppString "(SCspec",
                ppNewline,
                ppNest 2 (ppSpecElemTerms c specElems),
                ppNewline,
                ppString "endSCspec)"]
    | Qualify (term, qualifier) ->
      ppConcat [ppString "(Qualify ",
                ppSCTerm c term,
                ppString " ",
                ppBreak,
                ppID qualifier,
                ppString ")",
                ppBreak]
    | Translate (term, renaming) ->
      ppConcat [ppString "(Translate ",
                ppSCTerm c term,
                ppRenaming renaming,
                ppString ")"]
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
    | Subst (specTerm, morphTerm, pragmas) ->
      ppConcat [ppString "(Subst ",
                ppSCTerm c specTerm,
                ppString " ",
                ppBreak,
                ppSCTerm c morphTerm,
                ppString " ",
                ppBreak,
                ppString "(",
                ppSep (ppAppend (ppString " ") ppBreak)
                  (map (fn ((p1,p2,p3),pos) -> ppConcat [ppLitString p1,
                                                         ppLitString p2,
                                                         ppLitString p3])
                     pragmas),
                ppString ")",
                ppString " endSubst)"]
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
                let def ppNameExpr expr = 
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
                    ppValue c value
                  | Other other_term -> ppString "<<Other>>"
                    %ppOtherTerm other_term
                    
op ppQualifiedId (Qualified (q, id) : QualifiedId) : WLPretty =
  if q = UnQualified then 
    ppID id
  else 
    ppConcat [ppID q, ppString ".", ppID id]
    
op ppDiagElem (c:Context) ((elem, _ (* position *)) : DiagElem) : WLPretty =
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
      
op ppDecls (c:Context) (decls: List SCDecl) : WLPretty =
  let def ppDecl (name, term) =
    ppConcat [ppID name,
              ppString " = ",
              ppSCTerm c term]
  in
  ppSep ppNewline (map ppDecl decls)
  
op ppSpecElemTerms (c: Context) (elems : List SpecElemTerm) : WLPretty =
  ppSep ppNewline (map (ppSpecElemTerm c) elems)

op ppSpecElemTerm (c:Context) ((elem, pos):SpecElemTerm) : WLPretty = 
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
                                          
op ppIdInfo (qids: List QualifiedId) : WLPretty = ppSep (ppString ", ") (map ppQualifiedId qids)
   
op ppTypeInfo (c:Context) (full?:Bool) (aliases: List QualifiedId, dfn: MSType) (pos:Position) : WLPretty =
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
  
op ppBrTyVars (tvs:TyVars) : WLPretty =
  if tvs = [] then ppString " "
  else ppConcat [ppString " [",
                 ppTyVars tvs,
                 ppString "] "]
    
op ppTyVars (tvs: TyVars) : WLPretty =
  case tvs of
    | [] -> ppNil
    | _  -> ppSep (ppString " ") (map ppID tvs)

op ppOpInfo (c:Context) (decl?:Bool) (def?:Bool) (aliases:Aliases, fixity:Fixity, dfn:MSTerm) (pos:Position) : WLPretty =
  let (tvs, srt, term) = unpackTerm dfn in %TODO think about this
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
                   %                   ppFixity fixity,
                   ppString ": ",
                   ppBreak,
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
            ppBreak,
            ppIndent(ppTerm c term)]))
  
op ppProperty (c:Context) ((propType, name, tyVars, term, pos):Property) : WLPretty =
  ppGr2Concat [if c.printPositionInfo?
                 then ppPosition c pos
               else ppNil,
               ppString "(Property ",
               ppPropertyType propType,
               ppString " ",
               ppQualifiedId name,
               ppString " (", %TODO Have ppTyVars print the parens?
               ppTyVars tyVars,
               ppString ") ",
               ppBreak,
               ppTerm c term,
               ppString ")"]
 
op ppPropertyType (propType:PropertyType) : WLPretty =
  case propType of
    | Axiom -> ppString "Axiom"
    | Theorem -> ppString "Theorem"
    | Conjecture -> ppString "Conjecture"
    | any ->
      fail ("ERROR: No match in ppPropertyType with: "
              ^ (anyToString any))
      
op ppRenaming ((rules, _): Renaming) : WLPretty =
  let def ppRenamingRule (rule, _(* position *)) = 
  case rule of          
    | Type (left_qid, right_qid, aliases) ->
      ppConcat [ppString " type ",
                ppQualifiedId left_qid,
                ppString " +-> ",	% ??
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
  
% op  ppOtherTerm         : OtherTerm Position -> WLPretty % Used for extensions to Specware
% op  ppOtherRenamingRule : OtherRenamingRule  -> WLPretty % Used for extensions to Specware

 % %TODO remove mentions of "asw" here and elsewhere
 %  op uidToAswName ({path,hashSuffix=_} : UnitId) : String =
 %   let device? = deviceString? (head path) in
 %   let main_name = last path in
 %   let path_dir = butLast path in 
 %   let mainPath = flatten (List.foldr (fn (elem,result) -> Cons("/",Cons(elem,result)))
 %                             ["/data/",main_name]
 %                             (if device? then tail path_dir else path_dir))
 %   in if device?
 %        then (head path) ^ mainPath
 %        else mainPath
    

  %type SpecCalc.State
  %type SpecCalc.Env a = State -> (Result a) * State
  %op  SpecCalc.run : fa (a) Env a -> a
  %type SpecCalc.Exception
  %op  SpecCalc.catch : fa (a) Env a -> (Exception -> Env a) -> Env a

  %% op evalSCTerm (c:Context) (term:SCTerm) : Option Value =
  %%   let def handler _ = return None in
  %%   let prog = {setCurrentUID(c.currentUID);
  %%       	(val,_,_) <- evaluateTermInfo term;
  %%       	return (Some val)}
  %%   in
  %%   run (catch prog handler)
      
  %% op  deleteASWFilesForUID: String -> ()
  %% def deleteASWFilesForUID uidstr =
  %%   case evaluateUnitId uidstr of
  %%     | Some val ->
  %%       deleteASWFilesForVal val
  %%     | _ -> ()

  %% op  deleteASWFilesForVal: Value -> ()
  %% def deleteASWFilesForVal val =
  %%   case uidStringForValue val of
  %%     | None -> ()
  %%     | Some (_,uidstr) ->
  %%       let fil_nm = uidstr ^ ".asw" in
  %%       let _ = ensureFileDeleted fil_nm in
  %%       case val of
  %%         | Spec spc ->
  %%           app (fn elem -> case elem of
  %%       	              | Import(_,im_sp,_,_) ->
  %%       	                deleteASWFilesForVal (Spec im_sp)
  %%       		      | _ -> ())
  %%             spc.elements
  %%         | _ -> ()

  %% op  ensureFileDeleted: String -> ()
  %% def ensureFileDeleted fil_nm =
  %%   if fileExists? fil_nm
  %%     then deleteFile fil_nm
  %%     else ()

  % op  ensureValuePrinted: Context -> Value -> ()
  % def ensureValuePrinted c val =
  %   case uidStringPairForValue val of
  %     | None -> ()
  %     | Some (uid,fil_nm, hash_ext) ->
  %       let asw_fil_nm = fil_nm ^ hash_ext ^ ".asw" in
  %       let sw_fil_nm = fil_nm ^ ".sw" in
  %       if fileOlder?(sw_fil_nm,asw_fil_nm)
  %         then ()
  %         else let c = c << {currentUID = uid} in
  %              writeStringToFile(printValue c val,asw_fil_nm)

  % op uidStringForValue (val:Value) : Option (UnitId * String) =
  %   case uidStringPairForValue val of
  %     | None -> None
  %     | Some(uid,filnm,hash) -> Some(uid,filnm ^ hash)

  % op  SpecCalc.findUnitIdforUnitInCache: Value -> Option UnitId
  % def findUnitIdforUnitInCache val =
  %   case readGlobalVar "GlobalContext" of
  %     | None -> None
  %     | Some global_context ->
  %       findUnitIdForUnit(val,global_context)

  % op  SpecCalc.findTermForUnitInCache: Value -> Option SCTerm
  % def findTermForUnitInCache val =
  %   case readGlobalVar "GlobalContext" of
  %     | None -> None
  %     | Some global_context ->
  %       findDefiningTermForUnit(val,global_context)
    
%  op  printUID : String * Bool * Bool -> ()
%  def printUID (uid, printPositionInfo?, recursive?) =
%    toScreen
%      (case evaluateUnitId uid of
%	| Some val -> printValue (val,printPositionInfo?,recursive?)
%	| _ -> "<Unknown UID>")

op printValue (c:Context) (value:Value) : String =
  let file_nm = case fileNameOfValue value of
                  | Some str -> str
                  | _ -> ""
  in
  let main_pp_val = ppValue (c << {fileName = file_nm}) value in
  let pp_val = if c.printPositionInfo?
                 then ppConcat [ppString "infile ", ppID file_nm, ppNewline, main_pp_val]
               else main_pp_val
  in
  ppFormat pp_val
  
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
      

  %% --------------------------------------------------------------------------------

% ???
op ppValue (c: Context) (value:Value) : WLPretty =
  case value of
    | Spec        spc           -> ppSpec c spc %opt_val_tm
    | Morph       spec_morphism -> ppMorphism c  spec_morphism
    | SpecPrism   spec_prism    -> ppPrism     spec_prism     % tentative
    | SpecInterp  spec_interp   -> ppInterp    spec_interp    % tentative
%      | Diag        spec_diagram  -> ppDiagram  c  spec_diagram
%      | Colimit     spec_colimit  -> ppColimit  c  spec_colimit
%      | Other       other_value   -> ppOtherValue other_value
%      | InProcess                 -> ppString "InProcess"
%      | UnEvaluated _             -> ppString "some unevaluated term"
    | _                         -> ppString "ERROR: <unrecognized value>"


  (* tentative *)
op ppPrism ({dom=_, sms=_, pmode=_, tm=_}:SpecPrism) : WLPretty =
  ppString "<some prism>"

  (* tentative *)
op ppInterp ({dom=_, med=_, cod=_, d2m=_, c2m=_}:SpecInterp) : WLPretty =
  ppString "<some interp>"

  %% --------------------------------------------------------------------------------
  %% Specs
  %% --------------------------------------------------------------------------------
  
%  op  printSpec: Spec -> ()
%  def printSpec spc = toScreen(ppFormat (ppSpec {printTypes? = true,
%						 printPositionInfo? = false,
%						 fileName = "",
%						 recursive? = false}
%					   spc))
             
           

op ppAOpInfo (c : Context, aopinfo : AOpInfo StandardAnnotation) : WLPretty = 
  let {names, fixity, dfn, fullyQualified?} = aopinfo in
  ppGr2Concat [ppString "(AOpInfo ",
               ppBreak,
               ppWrapParens (ppSep (ppString " ") (map ppQualifiedId names)), %%when can there be more than one name?
               ppString " ",
               ppBreak,
               ppFixity fixity,
               %ppString " ",
               ppNewline, %ppBreak,
               ppTerm c dfn,
               ppString " ",
               ppBreak,
               if fullyQualified? then ppString "IsFullyQualified" else ppString "NotFullyQualified",
               ppString ")"]

% TODO use ppSep to put in the newlines?
op ppMapLMapFromStringsToAOpInfos (c : Context) (m:MapL.Map(String, (AOpInfo StandardAnnotation))) : List WLPretty =
  foldi
  (fn (key, val, prettys) -> 
     ((ppConcat [ppString "(",
                 ppString key, %% the qualifier
                 ppNewline,
                 ppAOpInfo (c, val),
                 ppString ")",
                 ppNewline
                 ])
        ::prettys))
  []
  m
   
%% Each val in the map is itself a map.
op ppAOpMapEntry (c : Context) (key : String, val : (MapL.Map(String, (AOpInfo StandardAnnotation))), pps: List WLPretty) : List WLPretty =
  (ppGr2Concat [ppString "(",
                ppString key, %% the op name (without the qualifier)
                ppNewline,
                ppGr2Concat [ppString "(",
                             ppSep (ppConcat [ppNewline, ppString " "]) (ppMapLMapFromStringsToAOpInfos c val),
                             ppString ")"],
                ppString ")"])::
  pps
  
  %% This is a map from op names to (maps from qualifiers to opinfos).
op ppAOpMap (c : Context, m:(AOpMap StandardAnnotation)) : WLPretty =
  if (m = emptyAQualifierMap) then
    ppString "(ops)"
  else
    ppGr2Concat [ppString "(ops ",
                 ppNewline,
                 ppSep ppNewline (MapSTHashtable.STH_foldi (ppAOpMapEntry c, [], m)),
                 ppString ")",
                 ppNewline]
    
op ppATypeInfo (c : Context, atypeinfo : ATypeInfo StandardAnnotation) : WLPretty = 
  let {names, dfn} = atypeinfo in
  ppGr2Concat [ppString "(ATypeInfo ",
               ppBreak,
               ppWrapParens (ppSep (ppString " ") (map ppQualifiedId names)), %%when can there be more than one name?
               ppString " ",
               ppNewline, %ppBreak,
               ppType c dfn,
               ppString ")",
               ppNewline]

op ppMapLMapFromStringsToATypeInfos (c : Context) (m:MapL.Map(String, (ATypeInfo StandardAnnotation))) : List WLPretty =
  foldi
  (fn (key, val, prettys) -> 
     ((ppConcat [ppString "(",
                 ppString key,
                 ppNewline,
                 ppATypeInfo (c, val),
                 ppString ")",
                 ppBreak
                 ])
        ::prettys))
  []
  m


%% Each val in the map is itself a map.
op ppATypeMapEntry (c : Context) (key : String, val : (MapL.Map(String, (ATypeInfo StandardAnnotation))), pps: List WLPretty) : List WLPretty =
  (ppGr2Concat [ppString "(",
                ppString key,
                ppString " ",
                ppBreak,
                ppGr2Concat [ppString "(",
                             ppSep (ppConcat [ppNewline, ppString " "]) (ppMapLMapFromStringsToATypeInfos c val),
                             ppString ")"],
                ppString ")"])::
  pps

%% This is a map from type names to (maps from qualifiers to typeinfos).
op ppATypeMap (c : Context, m:(ATypeMap StandardAnnotation)) : WLPretty =
  if (m = emptyAQualifierMap) then
    ppString "(types)"
  else
    ppGr2Concat [ppString "(types ",
                 ppNewline,
                 ppSep ppNewline (MapSTHashtable.STH_foldi (ppATypeMapEntry c, [], m)),
                 ppString ")"
                 ]
    
op ppSpec (c: Context) (spc:Spec) : WLPretty =
  ppGr2Concat [ppString "(Spec ",
               ppNewline,
               case spc.qualifier of | Some qual -> ppString qual | None -> ppString "<no-qualifier>",
               ppNewline,
               ppSpecElements c spc.elements,
               ppNewline,
               ppAOpMap(c, spc.ops),
               ppNewline,
               ppATypeMap(c, spc.types),
               ppString ")"
               ]
    
  %% op  ppSpecOrigin: Context -> SCTerm -> WLPretty
  %% def ppSpecOrigin c (def_tm,_) =
  %%   case def_tm of
  %%     | Subst(spec_tm,morph_tm) ->
  %%       ppGr2Concat [ppString "substitution ",
  %%       	     ppSCTermVal c spec_tm "name ",
  %%       	     ppNewline,
  %%       	     ppString "[",
  %%       	     ppSCTermVal c morph_tm " name morphism ",
  %%       	     ppString "]"]
  %%     | Translate(spec_tm,renaming) ->
  %%       ppGr2Concat[ppString "translate ",
  %%       	    ppSCTermVal c spec_tm "name ",
  %%       	    ppString " by ",
  %%       	    ppRenaming renaming]
  %%     | Qualify(spec_tm,nm) ->
  %%       if baseUnitId?(c.currentUID)
  %%         then ppGrConcat [ppString "qualify base ",
  %%       		   ppID nm]
  %%       else
  %%       ppGr2Concat[ppString "qualify ",
  %%       	    ppID nm,
  %%       	    ppString " ",
  %%       	    ppSCTermVal c spec_tm "name "]
  %%     | Obligations spec_or_morph_tm ->
  %%       let oblig_keywords = if morphismTerm? c spec_or_morph_tm
  %%       		       then "morphism obligations "
  %%       		       else "obligations "
  %%       in
  %%       ppGr2Concat[ppString oblig_keywords,
  %%       	    ppSCTermVal c spec_or_morph_tm "name "]
  %%     | _ -> ppString "elements"

  %% op  morphismTerm?: Context -> SCTerm -> Bool
  %% def morphismTerm? c tm =
  %%   case tm of
  %%     | (SpecMorph _,_) -> true
  %%     | (UnitId _,_) ->
  %%       (case evalSCTerm c tm of
  %%         | Some (Morph _) -> true
  %%         | _ -> false)
  %%     | _ -> false

  %% op  baseUnitId?: UnitId -> Bool
  %% def baseUnitId? uid =
  %%   let len = length uid.path in
  %%   case subFromTo(uid.path,len-3,len-1) of
  %%     | ["Library","Base"] -> true
  %%     | _ -> false

  %% op  ppSCTermVal: Context -> SCTerm -> String -> WLPretty
  %% def ppSCTermVal c tm name_str=
  %%   case tm of
  %%     | (UnitId _,_) ->
  %%       (case evalSCTerm c tm of
  %%         | Some val -> ppUIDorFull c val (Some tm) name_str
  %%         | _ -> ppString "<<Shouldn't happen!>>")
  %%     | _ ->
  %%       case evalSCTerm c tm of
  %%         | Some val -> ppValue c val (Some tm)
  %%         | _ -> ppString "<<Shouldn't happen!>>"
	 
  % op ppUIDorFull (c:Context) (val:Value) (opt_val_tm: Option SCTerm) (name_str: String) : WLPretty =
  %   case findUnitIdforUnitInCache val of
  %     | Some uid ->
  %       let _ = if c.recursive? && uid nin? c.uidsSeen
  %       	  then ensureValuePrinted (c << {uidsSeen = Cons(uid,c.uidsSeen)}) val
  %       	else ()
  %       in
  %         ppConcat [ppString name_str, ppUID uid]
  %     | None -> ppValue c val opt_val_tm

%  op  normalizeSpecElements: SpecElements -> SpecElements
%  def normalizeSpecElements elts =
%    case elts of
%      | [] -> []
%      | (Op qid1) :: (OpDef qid2) :: rst | qid1 = qid2 ->
%        Cons(Op qid1, normalizeSpecElements rst)
%      | x::rst -> Cons(x,normalizeSpecElements rst)

op ppSpecElements (c:Context) (elems:SpecElements) : WLPretty = 
  ppNest 1 (ppConcat [ppString "(elements",
                      ppNewline,
                      (ppSep ppNewline
                         (filter (fn pp -> pp ~= ppNil)  %% why the filter?
                            (ppSpecElementsAux c elems))),
                      ppString ")"])
    
op ppSpecElementsAux (c:Context) (elems:SpecElements) : List WLPretty =
  case elems of
    | [] -> []
      % | (Op (qid1,false,pos)) :: (OpDef (qid2,0,hist,_)) :: rst | qid1 = qid2 ->
      %   Cons(ppSpecElement c spc (Op (qid1,true,pos)) true,
      %        ppSpecElementsAux c spc rst)
    | el :: rst ->
      Cons(ppSpecElement c el,
           ppSpecElementsAux c rst)

% FIXME: use pretty-printing features to print proofs
op ppProof (c:Context) (pf:Proof) : WLPretty =
  ppString (printProof pf)

op ElidePragmas? : Bool = true
  
op ppSpecElement (c:Context) (elem:SpecElement) : WLPretty  =
  case elem of
    | Import (im_sc_tm, im_sp, im_elements, pos) ->
      ppConcat [if c.printPositionInfo?
                  then ppPosition c pos
                else ppNil,
                ppGr1Concat[ppString "(Import ",
                            ppSCTerm c im_sc_tm,
                            ppNewline,
                            %%ppUIDorFull c (Spec im_sp) (Some im_sc_tm) "name ",
                            if c.showImportedSpecs? 
                              then ppSpec c im_sp
                            else ppString "(...imported spec elided...)",
                            ppNewline,
                            %%ppString "(...imported elements elided...)",
                            ppSpecElements c im_elements,
                            ppString ")"]
                ]
    | Op (qid,d?,pos) ->
      ppConcat[ppString "(OpDecl ",
               ppQualifiedId qid,
               ppString " ",
               if d? then ppString "defined-when-declared" else ppString "not-defined-when-declared",
               ppString ")"]
      %% Note that most of the information for the op is not here but rather in the Spec's op map.
    | OpDef (qid,refine_num,opt_pf,pos) ->    % !!!
      ppConcat[ppString "(OpDef ",
               ppQualifiedId qid,
               ppString " ",
               ppString (show refine_num),
               ppString " (",
               (case opt_pf of
                  | None -> ppString "None"
                  | Some pf -> ppProof c pf),
               ppString "))"]
    | Type (qid,pos) ->
      ppConcat[ppString "(TypeDecl ",
               ppQualifiedId qid,
               ppString ")"]
      %% Note that most of the information for the type is not here but rather in the Spec's type map.
    | TypeDef (qid,pos) ->
      ppConcat[ppString "(TypeDef ",
               ppQualifiedId qid,
               ppString ")"]
    | Property prop -> ppProperty c prop
    | Pragma(beg_str,mid_str,end_str,pos) ->
      ppConcat [if c.printPositionInfo?
                  then ppPosition c pos
                else ppNil,
                ppString "(Pragma ",
                ppLitString (enquote beg_str),
                ppString " ",
                ppLitString (enquote (if ElidePragmas? then "(...middle string elided...)" else mid_str)), %%ppLitString mid_str,
                ppString " ",
                ppLitString (enquote end_str),
                ppString ")"]
    | Comment (str,pos) ->
      ppConcat [if c.printPositionInfo?
                  then ppPosition c pos
                else ppNil,
                ppString "(Comment ",
                ppString str,
                ppString " ) "]
      
op ppPosition (c:Context) (pos:Position) : WLPretty =
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

op ppTerm (c:Context) (term:MSTerm) : WLPretty =
  if c.printPositionInfo?
    then ppConcat [ppPosition c (termAnn term),
                   ppBreak,
                   ppTerm1 c term]
  else ppTerm1 c term

op ppTerm1 (c:Context) (term:MSTerm) : WLPretty =
  case term of
    | Apply (term1, term2, _)
      ->
      ppGr2Concat [ppString "(Apply ",
                   ppBreak,
                   ppTerm c term1,
                   ppSpaceBreak,
                   ppTerm c term2,
                   ppString ")"]
    | ApplyN (terms, _)
      ->
      ppGr2Concat [ppString "(ApplyN ",
                   ppBreak,
                   ppSep (ppAppend (ppString " ") ppBreak) (map (ppTerm c) terms),
                   ppSpaceBreak,
                   ppString ")"]

    | Record (fields,_) ->      
	% (case fields of
	%   | [] -> ppString "(tuple)"
	%   | ("1",_) :: _ ->
	%     let def ppField (_,y) = ppTerm c y in
	%     ppGr1Concat [ppString "(tuple ",
        %                  ppSep (ppAppend (ppString " ") ppBreak) (map ppField fields),
        %                  ppString ")"]
	%   | _ ->
        let def ppField (x,y) =
        ppWrapParens (ppConcat [ppID x,
                                ppString " ",
                                ppTerm c y
                                ]) in
        ppGr2Concat [ppString "(Record ",
                     ppBreak,
                     ppSep ppSpaceBreak (map ppField fields),
                     ppString ")"]
    | Bind (binder,vars,term,_) ->
      ppGr2Concat [ppString "(Bind ",
                   ppBinder binder,
                   ppString " (",
                   ppNest 0 (ppSep (ppConcat [(ppString " "), (ppBreak)]) (map (ppVar c) vars)),
                   ppString ") ",
                   ppBreak,
                   ppTerm c term,
                   ppString ")"
                   ]
    | The (var,term,_) ->
      ppGrConcat [ppString "(The ",
                  ppVar c var,
                  ppString " ",
                  ppTerm c term,
                  ppString ")"]
    | Let (decls,term,_) ->
      let def ppDecl (pattern: MSPattern, term: MSTerm) =
      ppConcat [ppString "(",
                ppGr1Concat [ppPattern c pattern,
                             ppString " ",
                             ppBreak,
                             ppTerm c term],
                ppString ")"]
      in
      ppGr2Concat [ppString "(Let (",
                   ppSep ppBreak (map ppDecl decls) ,
                   ppString ") ",
                   ppBreak,
                   ppTerm c term,
                   ppString ")"]
    | LetRec (decls,term,_) ->
      let def ppDecl (v: MSVar,term: MSTerm) =
      ppGr2Concat [ppString "(",
                   ppVar c v,
                   ppString " ",
                   ppBreak,
                   ppTerm c term,
                   ppString ")"]
      in
      ppGr2Concat [ppString "(LetRec (",
                   ppIndent (ppSep ppBreak (map ppDecl decls)),
                   ppString ") ",
                   ppBreak,
                   ppTerm c term,
                   ppString ")"]
    | Var (v,_) -> ppVar c v
    | Fun (fun,ty,_) ->
      if c.printTypes?
        then ppGr2Concat [ppString "(Fun ",
                          ppFun fun,
                          ppString " ", 
                          ppBreak,
                          ppType c ty,
                          ppString ")"]
      else ppGrConcat [ppString "(Fun ",
                       ppFun fun,
                       ppString "),",
                       ppBreak]
%      | Lambda ([(pattern,_,term)],_) ->
%	  ppGrConcat [
%	    ppString "lambda ",
%	    ppPattern c pattern,
%	    ppGroup (ppIndent (ppConcat [
%	      ppString " ->",
%	      ppBreak,
%	      ppAppend (ppTerm c term) (ppString ")")
%	    ]))
%	  ]
      | Lambda (match,_) ->
        ppIndent(ppGr2Concat [ppString "(lambda ",
                              ppBreak,
                              ppNest 1 (ppGrConcat [ppString "(",
                                                    ppMatch c match,
                                                    ppString ")"]),
                              ppString ")"
                              ])
      | IfThenElse (pred,term1,term2,_) -> 
        ppGrConcat [
                    ppString "(if ",
                    ppTerm c pred,
                    %	    ppString " then",
                    ppBreak,
                    ppString "  ",
                    ppIndent (ppTerm c term1),
                    ppBreak,
                    %	    ppString "else",
                    %	    ppBreak,
                    ppString "  ",
                    ppIndent (ppTerm c term2),
                    ppString ")"
                    ]
      | Seq (terms,_) ->
        ppGrConcat [ppString "(seq ",
                    ppSep (ppAppend (ppString " ") ppBreak) (map (ppTerm c) terms),
                    ppString ")"]
      | Pi(tvs,term1,_) ->
	% if tvs = [] then ppTerm c term1
	%   else 
        ppGr2Concat [ppString "(Pi (",
		     ppTyVars tvs,
                     ppString ")",
		     ppString " ",
		     ppBreak,
		     ppTerm c term1,
                     ppString ")"]
      | And(terms,_) ->
	ppGrConcat [ppString "(and ",
%		    ppString "[",
%		    ppSep (ppString ", ") (map (ppTerm c) terms),
		    ppSep ppBreak (map (ppTerm c) terms),
%		    ppString "]"
		    ppString ")"
                    ]
      | Any(_) -> ppString "AnyTerm"
      | TypedTerm (tm,ty,_) ->
        ppGr2Concat [ppString "(TypedTerm ",
                     ppBreak,
                     ppTerm c tm,
                     ppString " ", %% ppString ": ",
                     ppBreak,
                     ppType c ty, 
                     ppString ")"]
      | mystery -> fail ("No match in ppTerm with: '" ^ (anyToString mystery) ^ "'")
        
op ppBinder (binder:Binder) : WLPretty =
  case binder of
    | Forall -> ppString "forall"
    | Exists -> ppString "exists"
    | Exists1 -> ppString "exists1"

op ppVar (c:Context) ((id,ty):MSVar) : WLPretty =
  if c.printTypes?
    then ppConcat [ppString "(var ",
                   ppID id,
                   ppString " ",
                   ppType c ty,
                   ppString ")"]
  else ppConcat [ppString "(var ",
                 ppID id,
                 ppString ")"]
    
op ppMatch (c:Context) (cases:MSMatch) : WLPretty =
  let def ppCase (pattern,guard,term) =
  ppNest 1 (ppGrConcat [ppString "(",
                        ppPattern c pattern,
                        %%		      ppString " | ",
                        ppString " ",
                        ppBreak,
                        ppTerm c guard,	% wrong?
                        ppString " ",
                        ppBreak,
                        ppTerm c term,
                        ppString ")"])
  in
  (ppSep 
     (ppAppend (ppString " ") ppBreak)
     (map ppCase cases))
  
 %% Placeholder for patAnn which was missing a case
op [a] patAnn1 (pat: APattern a) : a =
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
    | TypedPat    (_,_,   a) -> a

op ppPattern (c:Context) (pattern:MSPattern) : WLPretty =
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

op ppPattern1 (c:Context) (pattern:MSPattern) : WLPretty = 
  case pattern of
    | AliasPat (pat1,pat2,_) -> 
      ppGrConcat [ppString "alias ",
                  ppPattern c pat1,
                  ppString " with ",
                  ppPattern c pat2
                  ]
    | VarPat (v,_) -> ppConcat [ppString "(VarPat ", ppVar c v, ppString ")"]
    | EmbedPat (constr,pat,ty,_) ->
      ppGrConcat ([ppString "(EmbedPat ",
                   ppQualifiedId constr,
                   ppString " ",
                   case pat of
                     | None -> ppString "None" %ppNil
                     | Some pat -> (ppPattern c pat),
                   ppBreak]
                    ++ (if c.printTypes?
                          then [ppType c ty]
                        else [])
                    ++ [ppString ")"])
    | RecordPat (fields,_) ->
      % (case fields of
      %   | [] -> ppString "(RecordPat)"
      %     %% If a record has 1 as its first field name, it's really a tuple
      %     %% ("1" is not a legal record field name because it starts with a
      %     %% number).
      %   | ("1",_)::_ ->
      %     let def ppField (_,pat) = ppPattern c pat in
      %     ppNest 1 (ppConcat [ppString "(record-pat-for-tuple ",
      %                         (ppGrConcat [ppSep (ppAppend (ppString " ") ppBreak) %(ppString ", ")
      %                                        (map ppField fields),
      %                                      ppString ")"])])
      %   | _ ->
      let def ppField (x,pat) =
      ppConcat [ppString "(",
                ppID x,
                ppString " ",
                ppPattern c pat,
                ppString ")"]
      in
      ppGr2Concat [ppString "(RecordPat ",
                   ppBreak,
                   ppSep ppSpaceBreak (map ppField fields),
                   ppString ")"] %)
    | WildPat (ty,_) -> ppConcat[ppString "(Wild ",
                                 ppType c ty,
                                 ppString ")"]
    | StringPat (str,_) -> ppString (enquote str)
    | BoolPat (b,_) -> ppBool b
    | CharPat (chr,_) -> ppConcat[ppString numberSignString, ppString (show chr)]
    | NatPat (int,_) -> ppString (show int)      
      %      | RelaxPat (pat,term,_) ->   
      %        ppGrConcat [ppString "relax ",
      %		    ppPattern c pat,
      %		    ppString ", ",
      %		    ppTerm c term]
    | QuotientPat (pat,typename,tys,_) ->
      %% This requires update to interchange grammar
      ppGrConcat [ppString "(QuotientPat ",
                  ppPattern c pat,
                  ppString " ",
                  ppQualifiedId typename,
                  ppString " (",
                  ppSep (ppString " ") (map (ppType c) tys),
                  ppString "))"
                  ]
    | RestrictedPat (pat,term,_) -> 
%        (case pat of
%	   | RecordPat (fields,_) ->
%	     (case fields of
%	       | [] -> ppGrConcat [ppString "() | ",ppTerm c term]
%	       | ("1",_)::_ ->
%		   let def ppField (_,pat) = ppPattern c pat in
%		   ppConcat [
%		     ppString "(",
%		     ppSep (ppString ",") (map ppField fields),
%		     ppString " | ",
%		     ppTerm c term,
%		     ppString ")"
%		   ]
%	       | _ ->
%		   let def ppField (x,pat) =
%		     ppConcat [
%		       ppString x,
%		       ppString "=",
%		       ppPattern c pat
%		     ] in
%		   ppConcat [
%		     ppString "{",
%		     ppSep (ppString ",") (map ppField fields),
%		     ppString " | ",
%		     ppTerm c term,
%		     ppString "}"
%		   ])
%	       | _ ->
      ppGrConcat [ppString "(restrict ",
                  ppPattern c pat,
                  %%			ppString " | ",
                  ppString " ",
                  ppBreak,
                  ppTerm c term,
                  ppString ")"]
    | TypedPat (pat,srt,_) ->
      ppGrConcat [ppString "(TypedPat ",
                  ppPattern c pat,
                  ppString " ",
                  ppType c srt,
                  ppString ")"]
    | mystery -> fail ("No match in ppPattern with: '" ^ (anyToString mystery) ^ "'")
  
op ppFun (fun:MSFun) : WLPretty =
  case fun of
    | Not       -> ppString "Not"
    | And       -> ppString "And"
    | Or        -> ppString "Or"
    | Implies   -> ppString "Implies"
    | Iff       -> ppString "Iff"
    | Equals    -> ppString "Equals"
    | NotEquals -> ppString "NotEquals"
    | Quotient typename  -> ppGr2Concat [ppString "(Quotient",
                                         ppString " ", 
                                         ppBreak,
                                         ppQualifiedId typename,
                                         ppString ")",
                                         ppBreak]
    | PQuotient typename  -> ppGr2Concat [ppString "(PQuotient",
                                          ppString " ", 
                                          ppBreak,
                                          ppQualifiedId typename,
                                          ppString ")",
                                          ppBreak]
    | Choose typename  -> ppGr2Concat [ppString "(Choose",
                                       ppString " ", 
                                       ppBreak,
                                       ppQualifiedId typename,
                                       ppString ")",
                                       ppBreak]
    | PChoose typename  -> ppGr2Concat [ppString "(PChoose",
                                        ppString " ", 
                                        ppBreak,
                                        ppQualifiedId typename,
                                        ppString ")",
                                        ppBreak]
    | Restrict -> ppString "Restrict"
    | Relax -> ppString "Relax"
    | Op (qid,fix) -> ppConcat[ppString "(Op ", ppQualifiedId qid,  ppString " ", ppFixity fix, 
                               ppString ")"]
    | Project id ->
      ppConcat [ppString "(Project ", ppID id, ppString ")"]
    | RecordMerge -> ppString "RecordMerge"
    | Embed (id,b) -> ppConcat [ppString "(embed ", ppQualifiedId id, ppString " ", ppBool b, ppString ")"]
    | Embedded id  -> ppConcat [ppString "(embedded ", ppQualifiedId id, ppString ")"]
    | Select id -> ppGr2Concat [ppString "(Select ", ppBreak, ppQualifiedId id, ppString ") ", ppBreak]
    | Nat n -> ppConcat[ ppString "(Nat ", ppString (show n), ppString ")"]
    | Char chr -> ppConcat[ppString numberSignString, ppString (show chr)]
    | String str -> ppConcat[ppString "(String ", ppString (enquote str), ppString ")"]  %TODO escape any quotes in the string with backslash
    | Bool b -> ppConcat [ppString "(bool ", ppBool b, ppString ")"]
    | OneName (id,fxty) -> ppString id
    | TwoNames (id1,id2,fxty) -> ppQualifiedId (Qualified (id1,id2))
    | mystery -> fail ("ERROR: No match in ppFun with: " ^ (anyToString mystery))
      
op ppFixity (fix: Fixity) : WLPretty =
  case fix of
    | Infix (assoc,  n) -> ppConcat [ppString "(Infix ",
                                     case assoc of
                                       | Left  -> ppString "Left "
                                       | Right -> ppString "Right ",
                                     ppString (show n),
                                     ppString ")"]
    | Nonfix           -> ppString "Nonfix"
    | Constructor0     -> ppString "Constructor0"
    | Constructor1     -> ppString "Constructor1"
    | Unspecified      -> ppString "Unspecified-fixity"
    | Error fixities   -> ppConcat [
                                    ppString "(ErrorFixity [",
                                    ppSep (ppString ", ") (map ppFixity fixities),
                                    ppString "])"
                                    ]
    | mystery -> fail ("ERROR: No match in ppFixity with: '" ^ (anyToString mystery) ^ "'")
      
      % op isSimpleType? (ty:MSType) : Bool =
      %   case ty of
      %     | Base _ -> true
      %     | Bool _ -> true
      %     | _ -> false

op ppOptionType (c: Context) (ty:Option MSType) : WLPretty =
  case ty of
  | None -> ppString "None"
  | Some ty -> ppType c ty

op ppType (c: Context) (ty:MSType) : WLPretty =
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

op ppMetaTyVar (c: Context) (x: AMetaTyVar StandardAnnotation) : WLPretty =
  let Ref rc = x in
      ppGrConcat [ppString "((link ",
                  ppOptionType c rc.link,
                  ppString ") (uniqueId ",
                  ppString (show rc.uniqueId),
                  ppString ") (name ",
                  ppString rc.name,
                  ppString "))"]
  
    
op ppType1 (c:Context) (ty:MSType) : WLPretty =
  case ty of
    | Arrow (ty1,ty2,_) ->
      ppGrConcat [ppString "(arrow ",
                  ppType c ty1,
                  %%		    ppString " -> ",
                  ppBreak,
                  ppString " ",
                  ppType c ty2,
                  ppString ")"]
      %% TODO remove special printing for records here?
    | Product (fields,_) ->
      (case fields of
         [] -> ppString "(product-type)"
       | ("1",_)::_ ->
         let def ppField (_,y) = ppType c y in
         ppGr2Concat [ppString "(product-type ",
                      ppSep (ppAppend (ppString " ") ppBreak) %(ppString ", ")
                        (map ppField fields),
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
                               ppString "(Product-for-record ",
                               ppSep (ppAppend (ppString " ") ppBreak) (map ppField fields),
                               ppString ")"
                               ]))
    | CoProduct (taggedTypes,_) -> 
      let def ppTaggedType (id,optTy) =
      case optTy of %TODO combine these two cases:
        | None -> ppConcat [ppString "(",
                            ppQualifiedId (id),
                            ppString " ",
                            ppString "None",
                            ppString ")"]
        | Some ty ->
          ppConcat [ppString "(",
                    ppQualifiedId id,
                    ppString " ",
                    ppType c ty,
                    ppString ")"]
      in ppGrConcat [
                     ppString "(CoProduct (",
                     ppGrConcat [
                                 ppSep (ppAppend (ppString " ") ppBreak) (map ppTaggedType taggedTypes)
                                 ],
                     ppString "))"
                     ]
    | Quotient (ty,term,_) ->
      ppGrConcat [
                  ppString "(Quotient ",
                  ppType c ty,
                  ppString " ",
                  ppNewline,
                  ppTerm c term,
                  ppString ")"
                  ]
    | Subtype (ty,term,_) ->
      ppGr1Concat [
                   ppString "(Subtype ",
                   ppType c ty,
                   ppString " ",
                   ppNewline,
                   ppTerm c term,
                   ppString ")"
                   ]
      %      | Base (qid,[],_) -> ppGrConcat [ppString "(Base ", ppQualifiedId qid, ppString ")"]
    | Base (qid,tys,_) ->
      ppGrConcat [ppString "(BaseType ",
                  ppQualifiedId qid,
                  %% what are these types?  They are the instantiations of the polymorphic type vars of the type whose name is qid.
                  ppString " (",
                  ppSep (ppString " ") (map (ppType c) tys),
                  ppString "))"
                  ]
    | Boolean _ -> ppString "BoolType"  
    | TyVar (tyVar,_) -> ppConcat [ppString "(TyVar ",
                                   ppID tyVar,
                                   ppString ")"]
    | MetaTyVar (metaTyVar,_) -> ppConcat [ppString "(MetaTyVar ",
                                           ppMetaTyVar c metaTyVar,
                                           ppString ")"]
    | Pi(tvs,ty,_) ->
      % if tvs = [] then ppType c ty
      %   else 
      ppGrConcat [ppString "(PiType (",
                  ppTyVars tvs,
                  ppString ") ",
                  %%ppString " . ",
                  ppType c ty,
                  ppString ")"
                  ]
    | And(types,_) ->
      ppGrConcat[ppString "(AndType (",
                 ppSep (ppAppend (ppString " ") ppBreak)
                   (map (ppType c) types),
                 ppString "))"]
    | Any(_) -> ppString "AnyType"
    | mystery -> fail ("No match in ppType with: '" ^ (anyToString mystery) ^ "'")

op ppMorphism (c:Context) ({dom,cod,typeMap,opMap,pragmas,sm_tm}:Morphism) : WLPretty =
  ppGrConcat [ppString "(Morphism ",
              ppString "(",
              ppString "...domain spec elided...",  %ppUIDorFull c (Spec dom) None "name ",
              ppString ")",
              ppBreak,
              ppString " to ",
              ppString "(",
              ppString "...codomain spec elided...",  %ppUIDorFull c (Spec cod) None "name ",
              ppString ")",
              ppBreak,
              ppString " types ",
              ppIdMap typeMap,
              ppBreak,
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
              ppString "endMorphism)"]
  
op ppIdMap (idMap:QualifiedIdMap) : WLPretty =
  ppNest 0
  (ppSep (ppAppend (ppString ", ") ppBreak)
     (map (fn (d,r) -> ppConcat [ppQualifiedId d, ppString " -> ",ppQualifiedId r])
        (mapToList idMap)))

op printValueTop (value : Value, uid : UnitId, showImportedSpecs? : Bool) : String =
  printValue {printTypes? = true,
              printPositionInfo? = false,
              fileName = "", %FIXME the caller already has the file name? ah, this is used to print position information?
              %currentUID = uid,
              %uidsSeen = [uid],
              recursive? = true,
              showImportedSpecs? = showImportedSpecs?}
             value

%% Returns a success Bool flag.
op showDataCore (val : Value, showImportedSpecs? : Bool) : Bool =
%TODO Awkward to extract the UID here and the uid string below?; just do whatever evaluateUnitId does to turn it into an absolute path?
  case uidForValue val of 
    | None -> let _ = writeLine "Error: Can't get UID string from value" in false
    | Some uid ->
      let uidstr = fileNameInSubDir(uid, "data") in
      let filename = uidstr ^ ".data" in
      let _ = ensureDirectoriesExist filename in
      let _ = writeLine("Writing data to: "^filename^"\n") in
      let _ = writeStringToFile(printValueTop(val,uid,showImportedSpecs?),filename) in
        true

% TODO abstract out this pattern for use in other commands?
% returns an optional string to store in *last-unit-Id-_loaded*
op evaluateShowDataHelper (optional_argstring : Option String, lastUnitIdLoaded : Option String, homedir : String, showImportedSpecs? : Bool) : Option String = 
%  let _ = writeLine "Calling evaluateShowData." in
%  let _ = writeLine ("The user's home directory: "^homedir) in
%  let _ = writeLine ("arg string: "^(case optional_argstring of Some str -> enquote str | None -> "No arg string supplied.")) in
%  let _ = writeLine ("Last unit ID: "^(case lastUnitIdLoaded of | Some str -> str | None ->  "No last uid processed.")) in
  case UIDStringFromArgString(optional_argstring, lastUnitIdLoaded, homedir) of
    | None -> None % fail and don't change *last-unit-Id-_loaded*
    | Some uid_str ->
      % let _ = writeLine "Printing spec to file." in
      % let _ = writeLine ("uid_str:"^uid_str) in
      %% Evaluate the given unit
      let success? = (case evaluateUnitId uid_str of
                        | None -> let _ = writeLine("Error: Unknown UID " ^ uid_str) in false
                          %%  Print the unit's data structures to a file:
                        | Some val -> showDataCore(val, showImportedSpecs?)) in
      %% Return a new value for *last-unit-Id-_loaded* if the operation succeeded:
      if success? then Some uid_str else None

% This is the top-level function for the showdata Specware shell command.
% returns an optional string to store in *last-unit-Id-_loaded*
op evaluateShowData (optional_argstring : Option String, lastUnitIdLoaded : Option String, homedir : String) : Option String =
  evaluateShowDataHelper (optional_argstring, lastUnitIdLoaded, homedir, false)

% This is the top-level function for the showdatav (verbose) Specware shell command.
% returns an optional string to store in *last-unit-Id-_loaded*
op evaluateShowDataV (optional_argstring : Option String, lastUnitIdLoaded : Option String, homedir : String) : Option String = 
  evaluateShowDataHelper (optional_argstring, lastUnitIdLoaded, homedir, true)        

end-spec

