SpecCalc qualifying spec 
 import ../../Environment
% --------------------------------------------------------------------------------

(**
 * the following "abuses" a spec as an attribute store; it looks for op-defs of the form
 *      def attrname = attrvalue
 * where attrvalue is a String.
 * This is used, for instance, to use a spec to define options for code 
 * generation (e.g. the Java package name etc.)
 *)
op getStringAttributesFromSpec: Spec -> StringMap.Map String
def getStringAttributesFromSpec spc =
  let ops = opsAsList spc in
  foldl (fn ((_ , id, info), map) ->
	 let defs = opInfoDefs info in
	 case defs of
	   | term :: _ ->
	     (let (_, _, tm) = unpackTerm term in
	      case tm of
		| Fun (String val,_,_) -> StringMap.insert (map, id, val)
		| _ -> map)
	   | _ -> map)
	StringMap.empty
	ops


 sort AttrValue = | String String | Nat Nat | StringList (List String) | Bool Boolean | Null

 (**
  * reads an "option" spec and returns the value of the given operator using the AttrValue sort
  * as result type.
  *)
 op getAttributeFromSpec: Spec * String -> AttrValue
 def getAttributeFromSpec (spc, aname) =
   let
     def extractList (t, list) =
       case t of
	 | Apply(Fun(Embed(Cons,_),_,_),Record([(_,Fun(String elem,_,_)),(_,t)],_),_) ->
	   extractList (t, concat (list, [elem]))
	 | _ -> list
   in
   let
     def getAttrFromOps ops =
       case ops of
	 | [] -> Null
	 | (_, id, info)::ops ->
           if (id = aname) then
	     let defs = opInfoDefs info in
	     case defs of
	       | term :: _ ->
	         (let (_, _, tm) = unpackTerm term in
		  case tm of
		    | Fun   (String val,      _, _) -> String val
		    | Fun   (Nat    val,      _, _) -> Nat    val
		    | Fun   (Bool   val,      _, _) -> Bool   val
		    | Fun   (Embed  (Nil, _), _, _) -> StringList []
		    | Apply (Fun (Embed (Cons,_), _, _),
			     Record([(_, Fun (String elem,_,_)), (_,t)],_),
			     _) ->
		      StringList (extractList (t, [elem]))
		    | _ -> getAttrFromOps ops)
	       | _ -> getAttrFromOps ops
	  else
	    getAttrFromOps ops
  in
    getAttrFromOps (opsAsList spc)

 (**
  * returns whether or not id is declared without a definition
  * as sort in spc
  *)
  op sortIsDefinedInSpec?: Spec * Sort -> Boolean
 def sortIsDefinedInSpec? (spc, srt) =
  case srt of
    | Base (Qualified (_,id),_,_) -> sortIdIsDefinedInSpec? (spc, id)
    | Boolean _ -> true
    | _ -> false

  op sortIdIsDefinedInSpec?: Spec * Id -> Boolean
 def sortIdIsDefinedInSpec? (spc, id) =
   %%TODO: fix this -- hideously inefficient, and dubious semantics
   let srts = sortsAsList spc in
   case find (fn (_, id0, _) -> id0 = id) srts of
     | Some (_,_,info) -> definedSortInfo? info
     | _ -> false 

 op opIdIsDefinedInSpec?: Spec * Id -> Boolean
 def opIdIsDefinedInSpec?(spc,id) =
   %%TODO: fix this -- hideously inefficient, and dubious semantics
   let ops = opsAsList spc in
   case find (fn (_, id0, _) -> id0 = id) ops of
     | Some (_,_,info) -> definedOpInfo? info
     | _ -> false

 op  definedOp? : Spec * QualifiedId -> Boolean
 def definedOp? (spc,qid) =
   case findTheOp (spc, qid) of
     | Some info -> definedOpInfo? info
     | _ -> false

 op  declaredOp? : Spec * QualifiedId -> Boolean
 def declaredOp? (spc,qid) =
   case findTheOp (spc, qid) of
     | Some _ -> true
     | _ -> false

% --------------------------------------------------------------------------------
(**
 * returns the list of qualified id's that are declared in the spec (sorts and ops)
 *)

 op getDeclaredQualifiedIds: Spec -> List QualifiedId
 def getDeclaredQualifiedIds spc =
   let qids = foldriAQualifierMap
                (fn (q, id, _, qids) -> cons (Qualified (q, id), qids))
	        [] 
	        spc.sorts
   in
   let qids = foldriAQualifierMap
                (fn (q, id, _, qids) -> cons (Qualified (q, id), qids))
		qids 
		spc.ops
   in
     qids

% --------------------------------------------------------------------------------

   op basicQualifier?   : Qualifier   -> Boolean
   op basicQualifiedId? : QualifiedId -> Boolean
   op basicSortName?    : QualifiedId -> Boolean
   op basicOpName?      : QualifiedId -> Boolean

  def basicQualifiers = [
			 "Boolean",    % can appear in raw translation rules
			 "Char", 
			 "Compare",
			 "Functions",  % TODO: add Relations ?
			 "Integer", 
			 "Integer_",   % special hack for unary minus -- deprecated
			 "IntegerAux", % special hack for unary minus
			 "List",
			 "Nat",
			 "Option",
			 "String",
		%	 "WFO",        % TODO: basic ??
			 "System"      % TODO: basic ??
			]

  def basicQualifier? q = member (q, basicQualifiers)
  (* def basicQualifiedId? (Qualified(q,_)) = member (q, basicQualifiers) *)

  def basicQualifiedId? qid =
    let (basic_sort_names, basic_op_names) = getBaseNames() in
    member (qid, basic_sort_names) || 
    member (qid, basic_op_names)

  def basicSortName? qid =
    let (basic_sort_names, _) = getBaseNames () in
    member (qid, basic_sort_names)

  def basicOpName? qid =
    let (_, basic_op_names) = getBaseNames () in
    member (qid, basic_op_names)

endspec
