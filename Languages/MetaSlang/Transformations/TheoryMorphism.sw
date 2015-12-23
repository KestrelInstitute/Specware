(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%%% Utilities for handling simple logic morphisms to Isabelle

IsaTermPrinter qualifying spec
import Pragma
import /Languages/SpecCalculus/Semantics/Value
import /Library/Unvetted/StringUtilities
import /Library/Structures/Data/Maps/SimpleAsAlist
                (* op       infix info                    curried   reversed  include_def? *)
type OpTransInfo = String * Option(Associativity * Nat) * Bool * Bool * Bool
                  (* type     coercion fns              Overloaded ops *)
type TypeTransInfo = String * Option(String * String) * List String * Bool

type OpMap   = MapL.Map (QualifiedId, OpTransInfo)
type TypeMap = MapL.Map (QualifiedId, TypeTransInfo)

type TransInfo =
  {op_map:   OpMap,
   type_map: TypeMap,
   thy_imports: List String}
type TranslationMap = PolyMap.Map (UnitId, TransInfo)

op  emptyTranslationTable: TransInfo
def emptyTranslationTable = {op_map=[], type_map=[], thy_imports=[]}

op translatePragmaBrackets?(begp: String, endp: String): Bool =
  (begp = "proof" && endp = "end-proof")
 || (begp = "#translate" && endp = "#end")

op qidMatch?(prag_nm: String, Qualified(q, id): QualifiedId): Bool =
  prag_nm = id
    || (q ~= UnQualified
          && (prag_nm = q^"."^id
                || prag_nm = q^"__"^id))

op findQIDForName(prag_nm: String, elts: SpecElements): Option(QualifiedId * Bool) =
  % let _ = writeLine("QID for: "^prag_nm) in
  let result =
      foldl (fn (result, el) ->
               if some? result then result
               else
               case el of
                 | OpDef (qid, _, _, _) | qidMatch?(prag_nm, qid) -> Some(qid, false)
                 | Op    (qid, _, _)    | qidMatch?(prag_nm, qid) -> Some(qid, false)
                 | TypeDef (qid, _)     | qidMatch?(prag_nm, qid) -> Some(qid, true)
                 | Type (qid, _)        | qidMatch?(prag_nm, qid) -> Some(qid, true)
                 | _ -> None)
        None elts
  in
  % let _ = writeLine("findQID: "^anyToString result) in
  result

op thyMorphismMaps (spc: Spec) (kind: String) (convertPrecNum: Int -> Int): TransInfo =
  let def foldElts accum elts =
       foldl (fn (accum as (result, prev_id), el) ->
                case el of
                  | Import(s_tm, i_sp, im_elts, _) ->
                    foldElts accum im_elts
                  | Pragma(prag as (begp, prag_str, endp, pos)) | isPragmaKind(prag_str, kind)
                                                                 && translatePragmaBrackets?(begp, endp) ->
                    (case thyMorphismPragma prag_str kind pos of
                       | None ->
                         let def addRenaming(qid, type?, trans_id, fix, curried?, reversed?) =
                         if type? then (result << {type_map = update(result.type_map, qid, (trans_id, None, [], false))},
                                        None)
                         else
                           let (fix, curried?) =
                           if some? fix then (fix, true)
                           else
                             let Some {names=_, fixity, dfn=_, fullyQualified?=_} = findTheOp(spc,qid) in
                             case fixity of
                               | Infix (assoc, precnum) -> (Some(assoc, convertPrecNum precnum), true)
                               | _ -> (None, false)
                           in
                             (result << {op_map = update(result.op_map,qid,(trans_id,fix,curried?,reversed?,false))},
                              None)
                         in
                           (case splitNameFromPragmaStr prag_str of
                              | Some(prag_nm, r_prag_str) ->
                                (case (findQIDForName(prag_nm, elts), findRenaming r_prag_str kind pos) of
                                   | (Some(qid, type?), Some (trans_id, fix, curried?, reversed?)) ->
                                     addRenaming(qid, type?, trans_id, fix, curried?, reversed?)
                                   | _ -> (result, None))
                              | None ->
                                (case (prev_id, findRenaming prag_str kind pos) of
                                   | (Some(qid, type?), Some (trans_id, fix, curried?, reversed?)) ->
                                     addRenaming(qid, type?, trans_id, fix, curried?, reversed?)
                                   | _ -> (result, None)))
                               | Some (trans_string, import_strings) ->
                                 %% Only use import_strings from top-level specs as others will be imported
                                 let import_strings = if el in? spc.elements then import_strings else [] in
                                 let result = result << {thy_imports = removeDuplicates(import_strings ++ result.thy_imports)} in
                                 (parseMorphMap(trans_string, result, kind, pos), None))
                  | OpDef (qid,_,_,_) -> (result,Some(qid, false))
                  | Op    (qid,_,_)   -> (result,Some(qid, false))
                  | TypeDef(qid,_)    -> (result,Some(qid, true))
                  | Type  (qid,_)     -> (result,Some(qid, true))
                  | _                 -> (result,None))
       accum
       elts
   in
   (foldElts (emptyTranslationTable, None) spc.elements).1

 op thyMorphismPragma (prag: String) (kind: String) (pos: Position): Option(String * List String) =
  case search("\n",prag) of
    | None -> None
    | Some n ->
  let line1 = subFromTo(prag,0,n) in
  case removeEmpty(splitStringAt(line1," ")) of
    | hd::thyMorphStr::r | hd = kind && thyMorphStr in?
                                          ["ThyMorphism","Thy_Morphism", "-morphism",
                                           "TheoryMorphism","Theory_Morphism",
                                           "-instance"] ->
      Some(subFromTo(prag,n,length prag), if thyMorphStr = "-instance" then [] else r)
    | _ -> None

op toPrecNum(precnum_str: String, kind: String, pos: Position): Nat =
  if natConvertible precnum_str
    then let precnum = stringToInt precnum_str in
         if precnum >= 0
              && (if kind = "Haskell"
                  then precnum <= 10
                  else true)
         then precnum
         else (warn(precnum_str^": Illegal precedence number for "^kind);
               precnum)
    else (warn(precnum_str^": Not a number!");
          -999)

op processRhsOp (rhs: String) (kind: String) (pos: Position): String * Option(Associativity * Nat) * Bool * Bool =
  let def joinParens(strs, par_str, i) =
        case strs of
          | []       -> if par_str = "" then [] else [par_str]
          | "%" :: _ -> if par_str = "" then [] else [par_str]
          | "(" :: r_strs -> joinParens(r_strs, par_str^"(", i+1)
          | ")" :: r_strs ->
            if i = 1 then par_str^")" :: joinParens(r_strs, "", i-1)
              else joinParens(r_strs, par_str^")", i-1)
          | s :: r_strs ->
            if par_str = "" then s :: joinParens(r_strs, par_str, i)
              else joinParens(r_strs, par_str^s, i)
  in
  let rhs_strs = joinParens(splitStringAtChars(rhs, [# , #(, #), #%]), "", 0) in
  let rhs_strs = filter (fn s -> s ~= "" && s ~= " ") rhs_strs in
  case rhs_strs of
    | [] -> (" ", None, false, false)
    | [isaSym] -> (isaSym, None, false, false)
    | isaSym :: r ->
      (case r of
         | "curried"::rst -> (isaSym, None, true, "reversed" in? rst)
         | "reversed"::rst -> (isaSym, None, "curried" in? rst, true)
         | "Left"::ns::rst -> (isaSym, Some(Left, toPrecNum(ns, kind, pos)),
                               true, "reversed" in? rst)
         | "Right"::ns::rst -> (isaSym, Some(Right, toPrecNum(ns, kind, pos)),
                                true, "reversed" in? rst)
         | "Infix"::ns::rst -> (isaSym, Some(NotAssoc, toPrecNum(ns, kind, pos)),
                                true, "reversed" in? rst)
         | _ -> (isaSym, None, false, false))

 op findRenaming(prag_str: String) (kind: String) (pos: Position)
    : Option (String * Option(Associativity * Nat) * Bool * Bool) =
   let end_pos = case searchPredFirstAfter(prag_str, fn c -> c in? [ #\n, #", #[ ], 0) of   % #]
                   | Some n -> n
                   | None -> length prag_str
   in
   case searchBetween("->", prag_str, 0, end_pos) of
     | Some n -> Some(processRhsOp (subFromTo(prag_str, n+2, end_pos)) kind pos)
     | _ -> None

op parseQualifiedId(s: String): QualifiedId =
  case splitStringAt(s,".") of
    | [qual,id] -> Qualified(qual,id)
    | _ -> Qualified(UnQualified, s)

%%% Basic string parsing function
op parseMorphMap (morph_str: String, result: TransInfo, kind: String, pos: Position): TransInfo =
  let lines = splitStringAt(morph_str,"\n") in
  let def parseLine (result,s) =
        case splitAtStr(s, "\\_rightarrow") of
          | Some (lhs, rhs) -> processLine(lhs, rhs, result)
          | None ->
        case splitAtStr(s, "->") of
          | Some (lhs, rhs)  -> processLine(lhs, rhs, result)
          | None -> result
      def processLhs lhs =
        let lhs = removeInitialWhiteSpace lhs in
        let type? = length lhs > 5 && subFromTo(lhs,0,5) in? ["type ","Type "] in
        let lhs = if type? then subFromTo(lhs,5,length lhs) else lhs in
        let lhs = removeWhiteSpace lhs in
        (type?, parseQualifiedId lhs)
      def processRhsType rhs =
        let rhs = removeWhiteSpace rhs in
        case search("(",rhs) of
          | None -> (rhs, None, [])
          | Some lpos ->
        case search(",",rhs) of
          | None -> let _ = warn("Comma expected after left paren") in
                    (rhs, None, [])
          | Some commapos ->
        case search(")",rhs) of
          | None -> let _ = warn("Missing right parenthesis.") in
                    (rhs, None, [])
          | Some rpos ->
            (subFromTo(rhs,0,lpos),
             Some(subFromTo(rhs,lpos+1,commapos),
                  subFromTo(rhs,commapos+1,rpos)),
             parseOverloadedOps(rhs))
      def processLine(lhs,rhs,result) =
        let (type?,qid) = processLhs lhs in
        if type?
          then let (isaSym,coercions,overloadedOps) = processRhsType rhs in
               result << {type_map = update(result.type_map,qid,(isaSym,coercions,overloadedOps, true))}
          else let (isaSym,fixity,curried,reversed) = processRhsOp rhs kind pos in
               result << {op_map = update(result.op_map,qid,(isaSym,fixity,curried,reversed,true))}
  in	     
  foldl parseLine result lines

 op parseOverloadedOps(str: String): List String =
   case search("[",str) of
     | None -> []
     | Some lpos ->
   case search("]",str) of
     | None -> let _ = warn("Missing right bracket.") in  [] 
     | Some rpos ->
   if rpos < lpos then []
   else
   splitStringAt(removeWhiteSpace(subFromTo(str,lpos+1,rpos)), ",")

op stringToQId(s: String): QualifiedId =
  case search(".", s) of
    | Some i -> mkQualifiedId(subFromTo(s, 0, i), subFromTo(s, i+1, length s))
    | None   -> mkUnQualifiedId s

endspec
