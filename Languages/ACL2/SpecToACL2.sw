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

type PPError a = 
  | Good a
  | Bad WLPretty

op [a,b,c] zipWith (f:(a * b -> c), l1:List a, l2:List b) : List c =
  case (l1,l2) of
    | ([],_)  -> []
    | (_,[])  -> []
    | (x::xs,y::ys) -> f (x, y) :: zipWith (f,xs,ys)

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

op ppType (elem:SpecElement) (spc:Spec) : PPError WLPretty =
  case elem of
    | Type (qid, pos) -> 
      let Qualified (q, id) = qid in
      Good (ppConcat [ppString "((", ppString id, ppString " *) => *)"])
    | _ -> Bad (ppString "Bad argument to ppType")

op ppTypeLocalDef (elem:SpecElement) (spc:Spec) : PPError WLPretty =
  case elem of
    | Type (qid, pos) -> 
      let Qualified (q, id) = qid in
      Good (ppConcat [ppString "(local (defun ", ppString id, ppString " (x) (declare (ignore x)) t))"])
    | _ -> Bad (ppString "Bad argument to ppTypeLocalDef")

op ppTypeName (t:MSType) : PPError WLPretty = 
  case t of
    | Base (Qualified (_, pid),_,_) -> Good (ppString pid)
    | Boolean _ -> Good (ppString "booleanp")
    | _ -> Bad (ppString "Can't handle t in typeName")

op ppTypeDef (elem:SpecElement) (spc:Spec) : PPError WLPretty =
  case elem of
    | TypeDef (qid, pos) ->
      let Qualified (q, id) = qid in
      let Some typeDefInfo = findTheType (spc, qid) in
      let name = typeDefInfo.names @ 0 in
      let dfn = typeDefInfo.dfn in
      (case ppTypeName dfn of
         | Good tn ->
           Good (ppConcat [ppString "(defun ", ppString id, ppString " (x)", ppNewline,
                           ppString "  (", tn, ppString " x))"])
         | _ -> Bad (ppConcat [ppString "Can't handle type of ", ppString id]))
    | _ -> Bad (ppString "Bad argument to ppTypeDef")

op ppVarListHelper (l : MSMatch) : WLPretty =
  case l of
    | [] -> ppString ""
    | ((VarPat ((v,_),_), _, trm)::[]) -> ppString v
    | ((RecordPat ((_,VarPat ((v,_),_))::[],_), _, trm)::[]) -> ppString v
    | ((RecordPat ((_,VarPat ((v,_),_))::xs,x), y, trm)::[]) -> 
      ppConcat [ppString v, ppString " ", 
                ppVarListHelper ((RecordPat (xs,x), y, trm)::[])]

op ppVarList (trm : MSTerm) (tpe : MSType) : PPError WLPretty =
  case trm of
    | Fun _ -> Good (ppString "()")
    | Lambda (l, _) -> Good (ppConcat [ppString "(", ppVarListHelper l, ppString ")"])
    | IfThenElse _ -> Good (ppString "()")
    | Apply _ -> Good (ppString "()")
    | _ -> Bad (ppString "Can't handle term in ppVarList")

op varListHelper (l : MSMatch) : List WLPretty =
  case l of
    | [] -> []
    | ((VarPat ((v,_),_), _, trm)::[]) -> [ppString v]
    | ((RecordPat ((_,VarPat ((v,_),_))::[],_), _, trm)::[]) -> [ppString v]
    | ((RecordPat ((_,VarPat ((v,_),_))::xs,x), y, trm)::[]) -> 
      ppString v :: (varListHelper ((RecordPat (xs,x), y, trm)::[]))

op varList (trm : MSTerm) (tpe : MSType) : PPError (List WLPretty) =
  case trm of
    | Fun _ -> Good []
    | Lambda (l, _) -> Good (varListHelper l)
    | IfThenElse _ -> Good []
    | Apply _ -> Good []
    | _ -> Bad (ppString "Can't handle trm in varList")

op ppFun (f : MSFun) : PPError WLPretty =
  case f of
    | Bool x -> 
      (case x of | false -> Good (ppString "nil") | _ -> Good (ppString "t"))
    | Not -> Good (ppString "not")
    | And -> Good (ppString "and")
    | Or -> Good (ppString "or")
    | Implies -> Good (ppString "implies")
    | Iff -> Good (ppString "iff")
    | Equals -> Good (ppString "equal")
    | Op (Qualified (q,id),_) -> Good (ppString id)
    | _ -> Bad (ppString "Can't handle f in ppFun")

op ppTerm (trm : MSTerm) : PPError WLPretty =
  case trm of
    | Fun (f, _, _) -> ppFun f
    | Var ((v,_),_) -> Good (ppString v)
    | Lambda ((_,_,trm)::ms,_) -> ppTerm trm
%    | Lambda _ -> Bad (ppString "Can't handle lambda in ppTerm")
    | IfThenElse (t1,t2,t3,_) ->
      (case (ppTerm t1, ppTerm t2, ppTerm t3) of
         | (Good st1, Good st2, Good st3) -> 
           Good (ppConcat [ppString "(if ", st1, ppNewline,
                           ppString "    ", st2, ppNewline,
                           ppString "  ", st3, ppString ")"])
         | (Bad s,_,_) -> Bad s
         | (_,Bad s,_) -> Bad s
         | (_,_,Bad s) -> Bad s)
    | Apply (t1,t2,_) ->
      (case (ppTerm t1, ppTerm t2) of
         | (Good st1, Good st2) ->
           Good (ppConcat [ppString "(", st1, ppString " ", st2, ppString ")"])
         | (Bad s,_) -> Bad s
         | (_,Bad s) -> Bad s)
    | _ -> Bad (ppString "Can't handle trm in ppTerm")
    
op ppOpDef (elem:SpecElement) (spc:Spec) : PPError WLPretty =
  case elem of
    | Op (qid, defd, pos) ->
      let Qualified (q, id) = qid in
      let Some opDefInfo = findTheOp (spc, qid) in
      let name = opDefInfo.names @ 0 in
      let dfn = opDefInfo.dfn in
      (case dfn of
        | TypedTerm (trm,tpe,pos) -> 
          (case (ppTerm trm, ppVarList trm tpe, varList trm tpe) of
             | (Good strm, Good svarlist, Good varlist) ->
               Good (ppConcat [ppString "(defun ", ppString id, ppString " ", svarlist, ppNewline,
                               ppString "  (declare (ignorable ", ppSep (ppString " ") varlist, ppString "))", ppNewline,
                               ppString "  ", strm, ppString ")"])
             | (Bad s,_,_) -> Bad s
             | (_,Bad s,_) -> Bad s
             | (_,_,Bad s) -> Bad s)
        | _ -> Bad (ppString "Can't handle dfn in ppOpDef"))
    | _ -> Bad (ppString "Bad argument to ppOpDef")

op ppTypeThm (elem:SpecElement) (spc:Spec) : PPError WLPretty =
  case elem of
    | Op (qid, defd, pos) ->
      let Qualified (q, id) = qid in
      let Some opDefInfo = findTheOp (spc, qid) in
      let name = opDefInfo.names @ 0 in
      let dfn = opDefInfo.dfn in
      (case dfn of
         | TypedTerm (trm,tpe,_) ->
           (case tpe of
              | Boolean _ ->
                Good (ppConcat [ppString "(defthm ", ppString id, ppString "-type-constraint", ppNewline,
                                ppString "  (booleanp (", ppString id, ppString ")))"])
              | Arrow (Boolean _,codomain,_) ->
                (case ppTypeName codomain of
                   | Good cdtn ->
                     Good (ppConcat [ppString "(defthm ", ppString id, ppString "-type-constraint", ppNewline,
                                     ppString "  (implies (booleanp x)", ppNewline,
                                     ppString "           (", cdtn, ppString " (", ppString id, ppString " x))))"])
                   | Bad s -> Bad s)
              | Arrow (Base (Qualified (type_q, type_id),_,_), codomain,_) ->
                (case ppTypeName codomain of
                   | Good cdtn ->
                     Good (ppConcat [ppString "(defthm ", ppString id, ppString "-type-constraint", ppNewline,
                                     ppString "  (implies (", ppString type_id, ppString " x)", ppNewline,
                                     ppString "           (", cdtn, ppString " (", ppString id, ppString " x))))"])
                   | Bad s -> Bad s)
              | Arrow (Product (types,_), codomain,_) ->
                % WARNING: Potential error here
                (case ppTypeName codomain of
                   | Good cdtn ->
                     % Get the list of variables
                     let Good vlist = varList trm tpe in
                     % Get the list of types
                     let types = map (fn (_,t) -> t) types in
                     % Zip the two up
                     let typeRestrictions = zipWith ((fn (v, t) -> 
                                                        let Good tn = ppTypeName t in
                                                        ppConcat [ppString "(",tn,ppString " ",v,ppString ")"]),
                                                     vlist, types) in
                     Good (ppConcat [ppString "(defthm ", ppString id, ppString "-type-constraint", ppNewline,
                                     ppString "  (implies (and ",
                                     ppNest 1 (ppSep ppNewline typeRestrictions),
                                     ppString ")", ppNewline, 
                                     ppString "           (", cdtn, ppString " (",
                                     ppString id, ppString " ", ppSep (ppString " ") vlist, ppString "))))"])
                   | Bad s -> Bad s)
              | _ -> Bad (ppString "Can't handle tpe in ppTypeThm"))
         | _ -> Bad (ppString "Bad argument to ppTypeThm"))
    | _ -> Bad (ppString "Bad argument to ppTypeThm")

op [a, b] ppErrorMap : (a -> PPError b) -> List a -> PPError (List b)
def ppErrorMap f l =
  case l of
    | [] -> Good []
    | (x :: xs) -> 
      case (f x, ppErrorMap f xs) of
        | (Good y, Good ys) -> Good (y::ys)
        | (Bad s, _) -> Bad s
        | (_, Bad s) -> Bad s

op ppSpecElements (types:SpecElements) (typeDefs:SpecElements) (opDefs:SpecElements) (spc:Spec) : PPError WLPretty =
  case (ppErrorMap (fn t -> ppType t spc) types,
        ppErrorMap (fn t -> ppTypeLocalDef t spc) types,
        ppErrorMap (fn t -> ppTypeDef t spc) typeDefs,
        ppErrorMap (fn t -> ppOpDef t spc) opDefs,
%        Good "") of
        ppErrorMap (fn t -> ppTypeThm t spc) opDefs) of
    | (Good typeString, Good localTypeDefString, Good typeDefString, Good opDefString, Good typeThmString) ->
      Good (ppConcat [ppString "(encapsulate", ppNewline,
                      ppString " ;; Constrained function declarations", ppNewline,
                      ppString " (",
                      ppGr1Concat [ppConcat [ppString " ;; types", ppNewline], 
                                   ppSep ppNewline typeString], ppString ")", ppNewline, ppNewline,
                      ppGr1Concat [ppConcat [ppString " ;; Local Definitions", ppNewline], 
                                   ppSep ppNewline localTypeDefString], ppNewline, ppNewline,
                      ppGr1Concat [ppConcat [ppString " ;; typeDefs", ppNewline],
                                   ppSep ppNewline typeDefString], ppNewline, ppNewline,
                      ppGr1Concat [ppConcat [ppString " ;; opDefs", ppNewline],
                                   ppSep ppNewline opDefString],
                      ppString ")", ppNewline, ppNewline,
                      ppGr1Concat [ppConcat [ppString ";; type constraints", ppNewline],
                                   ppSep ppNewline typeThmString],
                      ppNewline])
    | (Bad s,_,_,_,_) -> Bad s
    | (_,Bad s,_,_,_) -> Bad s
    | (_,_,Bad s,_,_) -> Bad s
    | (_,_,_,Bad s,_) -> Bad s
    | (_,_,_,_,Bad s) -> Bad s

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

op filterOp (elems:SpecElements) : SpecElements =
  case elems of
    | [] -> []
    | el :: rst ->
      case el of
        | Op (qid, defd,  pos) ->
          (Op (qid, defd, pos)) :: filterOp rst
        | _ -> filterOp rst

op ppSpec (c: Context) (spc:Spec) : PPError WLPretty =
  let spc = adjustElementOrder spc in
  case ppSpecElements (filterType spc.elements) (filterTypeDef spc.elements) (filterOp spc.elements) spc of
    | Good s -> 
      Good (ppGr2Concat [ppString "(in-package \"ACL2\")",
                         ppNewline,
                         ppNewline,
                         s])
    | Bad s -> Bad s
      
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
    | Spec spc -> 
      (case ppSpec c spc of
         | Good s -> s
         | Bad s -> s)
    | _ -> ppString "Can't handle value in ppValue"

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