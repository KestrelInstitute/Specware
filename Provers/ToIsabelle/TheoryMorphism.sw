%%% Utilities for handling simple logic morphisms to Isabelle

IsaTermPrinter qualifying spec
 import /Languages/SpecCalculus/Semantics/Value
 import /Library/Unvetted/StringUtilities
 import /Library/Structures/Data/Maps/SimpleAsAlist
                 (* op       infix info                    curried   reversed *)
 type OpTransInfo = String * Option(Associativity * Nat) * Boolean * Boolean
                   (* type     coercion fns              Overloaded ops *)
 type TypeTransInfo = String * Option(String * String) * List String

 type OpMap   = Map.Map (QualifiedId, OpTransInfo)
 type TypeMap = Map.Map (QualifiedId, TypeTransInfo)

 type TransInfo =
   {op_map:   OpMap,
    type_map: TypeMap,
    thy_imports: List String}
 type TranslationMap = PolyMap.Map (UnitId, TransInfo)

 op  emptyTranslationTable: TransInfo
 def emptyTranslationTable = {op_map=[], type_map=[], thy_imports=[]}

 op  thyMorphismMaps: Spec \_rightarrow TransInfo
 def thyMorphismMaps spc =
   foldlSpecElements
     (fn (el,result) \_rightarrow
      case el of
       | Pragma("proof",prag_str,"end-proof",_) \_rightarrow
         (case isaThyMorphismPragma prag_str of
	    | None \_rightarrow result
	    | Some (trans_string, import_strings) \_rightarrow
              %% Only use import_strings from top-level specs as others will be imported
              let import_strings = if member(el,spc.elements) then import_strings else [] in
	      let result = result << {thy_imports = removeDuplicates(import_strings ++ result.thy_imports)} in
	      parseMorphMap(trans_string,result))
       | _ \_rightarrow result)
     emptyTranslationTable
     spc.elements

 op  isaThyMorphismPragma: String \_rightarrow Option(String * List String)
 def isaThyMorphismPragma prag =
   case search("\n",prag) of
     | None \_rightarrow None
     | Some n \_rightarrow
   let line1 = substring(prag,0,n) in
   case removeEmpty(splitStringAt(line1," ")) of
     | "Isa"::thyMorphStr::r | member(thyMorphStr,
				      ["ThyMorphism","Thy_Morphism",
				       "TheoryMorphism","Theory_Morphism"]) \_rightarrow
       Some(substring(prag,n,length prag), r)
     | _ \_rightarrow None

 %%% Basic string parsing function
 op  parseMorphMap: String * TransInfo \_rightarrow TransInfo
 def parseMorphMap (morph_str,result) =
   let lines = splitStringAt(morph_str,"\n") in
   let def parseLine (s,result) =
         case splitStringAt(s,"\\_rightarrow") of
	   | [lhs,rhs] \_rightarrow
	     processLine(lhs,rhs,result)
	   | [_] \_rightarrow
	     (case splitStringAt(s,"->") of
	       | [lhs,rhs] \_rightarrow processLine(lhs,rhs,result)
	       | _ \_rightarrow result)
	   | _ \_rightarrow result
       def processLhs lhs =
	 let lhs = removeInitialWhiteSpace lhs in
	 let type? = length lhs > 5 && member(substring(lhs,0,5), ["type ","Type "]) in
	 let lhs = if type? then substring(lhs,5,length lhs) else lhs in
         let lhs = removeWhiteSpace lhs in
	 (type?,
	  case splitStringAt(lhs,".") of
	    | [qual,id] \_rightarrow Qualified(qual,id)
	    | _ \_rightarrow Qualified(UnQualified,lhs))
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
	     (substring(rhs,0,lpos),
	      Some(substring(rhs,lpos+1,commapos),
		   substring(rhs,commapos+1,rpos)),
              parseOverloadedOps(rhs))
       def processRhsOp rhs =
	 case removeEmpty(splitStringAt(rhs," ")) of
	   | [] \_rightarrow (" ", None, false, false)
	   | [isaSym] \_rightarrow (isaSym, None, false, false)
	   | isaSym :: r \_rightarrow
	     (case r of
	       | "curried"::rst \_rightarrow (isaSym, None, true, member("reversed",rst))
	       | "reversed"::rst \_rightarrow (isaSym, None, member("curried",rst), true)
	       | "Left"::ns::rst \_rightarrow (isaSym, Some(Left,stringToNat ns),
                                    true, member("reversed",rst))
	       | "Right"::ns::rst \_rightarrow (isaSym, Some(Right,stringToNat ns),
                                      true, member("reversed",rst)))
       def processLine(lhs,rhs,result) =
	 let (type?,qid) = processLhs lhs in
	 if type?
	   then let (isaSym,coercions,overloadedOps) = processRhsType rhs in
	        result << {type_map = update(result.type_map,qid,(isaSym,coercions,overloadedOps))}
	   else let (isaSym,fixity,curried,reversed) = processRhsOp rhs in
	        result << {op_map = update(result.op_map,qid,(isaSym,fixity,curried,reversed))}
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
    splitStringAt(removeWhiteSpace(substring(str,lpos+1,rpos)), ",")
   
  op  removeEmpty: List String \_rightarrow List String
  def removeEmpty l =
    filter (fn s \_rightarrow s ~= "") l

endspec