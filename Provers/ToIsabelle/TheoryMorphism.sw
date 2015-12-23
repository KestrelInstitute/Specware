(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%%% Utilities for handling simple logic morphisms to Isabelle

IsaTermPrinter qualifying spec
 import /Languages/SpecCalculus/Semantics/Value
 import /Library/Unvetted/StringUtilities
 import /Library/Structures/Data/Maps/SimpleAsAlist
                 (* op       infix info                    curried   reversed  include_def? *)
 type OpTransInfo = String * Option(Associativity * Nat) * Bool * Bool * Bool
                   (* type     coercion fns              Overloaded ops *)
 type TypeTransInfo = String * Option(String * String) * List String * Bool

 type OpMap   = Map.Map (QualifiedId, OpTransInfo)
 type TypeMap = Map.Map (QualifiedId, TypeTransInfo)

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

 def thyMorphismMaps (spc: Spec) (kind: String) (convertPrecNum: Int -> Int): TransInfo =
   (foldlSpecElements
     (fn ((result, prev_id),el) \_rightarrow
      case el of
       | Pragma(begp, prag_str, endp, pos) |  translatePragmaBrackets?(begp, endp) \_rightarrow
         (case thyMorphismPragma prag_str kind pos of
	    | None \_rightarrow 
              (case (prev_id, findRenaming prag_str kind pos) of
                 | (Some(qid, type?), Some (trans_id, fix, curried?, reversed?)) \_rightarrow
                   if type? then (result << {type_map = update(result.type_map, qid, (trans_id, None, [], false))},
                                  None)
                   else
                   let (fix, curried?) =
                       if some? fix then (fix, true)
                       else
                         let Some {names=_, fixity, dfn=_, fullyQualified?=_} = findTheOp(spc,qid) in
                         case fixity of
                           | Infix (assoc, precnum) \_rightarrow (Some(assoc, convertPrecNum precnum), true)
                           | _ \_rightarrow (None, false)
                   in
                   (result << {op_map = update(result.op_map,qid,(trans_id,fix,curried?,reversed?,false))},
                    None)
                 | _ \_rightarrow (result, None))
	    | Some (trans_string, import_strings) \_rightarrow
              %% Only use import_strings from top-level specs as others will be imported
              let import_strings = if el in? spc.elements then import_strings else [] in
	      let result = result << {thy_imports = removeDuplicates(import_strings ++ result.thy_imports)} in
	      (parseMorphMap(trans_string, result, kind, pos), None))
       | OpDef (qid,_,_) \_rightarrow (result,Some(qid, false))
       | Op    (qid,_,_) \_rightarrow (result,Some(qid, false))
       | TypeDef(qid,_)  \_rightarrow (result,Some(qid, true))
       | Type  (qid,_)   \_rightarrow (result,Some(qid, true))
       | _               \_rightarrow (result,None))
     (emptyTranslationTable, None)
     spc.elements).1

  op thyMorphismPragma (prag: String) (kind: String) (pos: Position): Option(String * List String) =
   case search("\n",prag) of
     | None \_rightarrow None
     | Some n \_rightarrow
   let line1 = subFromTo(prag,0,n) in
   case removeEmpty(splitStringAt(line1," ")) of
     | hd::thyMorphStr::r | hd = kind && thyMorphStr in?
				           ["ThyMorphism","Thy_Morphism", "-morphism",
                                            "TheoryMorphism","Theory_Morphism",
                                            "-instance"] \_rightarrow
       Some(subFromTo(prag,n,length prag), if thyMorphStr = "-instance" then [] else r)
     | _ \_rightarrow None

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
     | [] \_rightarrow (" ", None, false, false)
     | [isaSym] \_rightarrow (isaSym, None, false, false)
     | isaSym :: r \_rightarrow
       (case r of
          | "curried"::rst \_rightarrow (isaSym, None, true, "reversed" in? rst)
          | "reversed"::rst \_rightarrow (isaSym, None, "curried" in? rst, true)
          | "Left"::ns::rst \_rightarrow (isaSym, Some(Left, toPrecNum(ns, kind, pos)),
                                true, "reversed" in? rst)
          | "Right"::ns::rst \_rightarrow (isaSym, Some(Right, toPrecNum(ns, kind, pos)),
                                 true, "reversed" in? rst)
          | "Infix"::ns::rst \_rightarrow (isaSym, Some(NotAssoc, toPrecNum(ns, kind, pos)),
                                 true, "reversed" in? rst))

  op findRenaming(prag_str: String) (kind: String) (pos: Position)
     : Option (String * Option(Associativity * Nat) * Bool * Bool) =
    let end_pos = case searchPred(prag_str, fn c -> c in? [#\n, #", #[]) of   % #]
		    | Some n \_rightarrow n
		    | None \_rightarrow length prag_str
    in
    case searchBetween("->", prag_str, 0, end_pos) of
      | Some n \_rightarrow Some(processRhsOp (subFromTo(prag_str, n+2,end_pos)) kind pos)
      | _ \_rightarrow None

 op splitAtStr(s: String, pat: String): Option(String * String) =
  case search(pat, s) of
    | Some i \_rightarrow Some(subFromTo(s,0,i),subFromTo(s,i + length pat, length s))
    | None \_rightarrow None

 op parseQualifiedId(s: String): QualifiedId =
   case splitStringAt(s,".") of
     | [qual,id] \_rightarrow Qualified(qual,id)
     | _ \_rightarrow Qualified(UnQualified, s)

 %%% Basic string parsing function
 op parseMorphMap (morph_str: String, result: TransInfo, kind: String, pos: Position): TransInfo =
   let lines = splitStringAt(morph_str,"\n") in
   let def parseLine (result,s) =
         case splitAtStr(s, "\\_rightarrow") of
	   | Some (lhs, rhs) \_rightarrow processLine(lhs, rhs, result)
	   | None \_rightarrow
         case splitAtStr(s, "->") of
           | Some (lhs, rhs)  \_rightarrow processLine(lhs, rhs, result)
           | None \_rightarrow result
       def processLhs lhs =
	 let lhs = removeInitialWhiteSpace lhs in
	 let type? = length lhs > 5 && subFromTo(lhs,0,5) in? ["type ","Type "] in
	 let lhs = if type? then subFromTo(lhs,5,length lhs) else lhs in
         let lhs = removeWhiteSpace lhs in
	 (type?, parseQualifiedId lhs)
       def processRhsType rhs =
	 let rhs = removeWhiteSpace rhs in
	 case search("(",rhs) of
	   | None \_rightarrow (rhs, None, [])
	   | Some lpos \_rightarrow
	 case search(",",rhs) of
	   | None \_rightarrow let _ = warn("Comma expected after left paren") in
	             (rhs, None, [])
	   | Some commapos \_rightarrow
	 case search(")",rhs) of
	   | None \_rightarrow let _ = warn("Missing right parenthesis.") in
	             (rhs, None, [])
	   | Some rpos \_rightarrow
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
      | None \_rightarrow []
      | Some lpos \_rightarrow
    case search("]",str) of
      | None \_rightarrow let _ = warn("Missing right bracket.") in  [] 
      | Some rpos \_rightarrow
    if rpos < lpos then []
    else
    splitStringAt(removeWhiteSpace(subFromTo(str,lpos+1,rpos)), ",")
   
 op stringToQId(s: String): QualifiedId =
   case search(".", s) of
     | Some i -> mkQualifiedId(subFromTo(s, 0, i), subFromTo(s, i+1, length s))
     | None   -> mkUnQualifiedId s

endspec
