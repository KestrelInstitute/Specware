(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

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
  foldl (fn (map, (_ , id, info)) ->
	 let defs = opInfoDefs info in
	 case defs of
	   | term :: _ ->
	     (let (_, _, tm) = unpackFirstTerm term in
	      case tm of
		| Fun (String val,_,_) -> StringMap.insert (map, id, val)
		| _ -> map)
	   | _ -> map)
	StringMap.empty
	ops


 type AttrValue = | String String | Nat Nat | StringList (List String) | Bool Bool | Null

 (**
  * reads an "option" spec and returns the value of the given operator using the AttrValue type
  * as result type.
  *)
 op getAttributeFromSpec: Spec * String -> AttrValue
 def getAttributeFromSpec (spc, aname) =
   let
     def extractList (t, list) =
       case t of
	 | Apply(Fun(Embed(Cons,_),_,_),Record([(_,Fun(String elem,_,_)),(_,t)],_),_) ->
	   extractList (t, list ++ [elem])
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
	         (let (_, _, tm) = unpackFirstTerm term in
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
  * as type in spc
  *)
  op typeIsDefinedInSpec?: Spec * MSType -> Bool
 def typeIsDefinedInSpec? (spc, srt) =
  case srt of
    | Base (Qualified (_,id),_,_) -> typeIdIsDefinedInSpec? (spc, id)
    | Boolean _ -> true
    | _ -> false

  op typeIdIsDefinedInSpec?: Spec * Id -> Bool
 def typeIdIsDefinedInSpec? (spc, id) =
   %%TODO: fix this -- hideously inefficient, and dubious semantics
   let srts = typesAsList spc in
   case findLeftmost (fn (_, id0, _) -> id0 = id) srts of
     | Some (_,_,info) -> definedTypeInfo? info
     | _ -> false 

 op opIdIsDefinedInSpec?: Spec * Id -> Bool
 def opIdIsDefinedInSpec?(spc,id) =
   %%TODO: fix this -- hideously inefficient, and dubious semantics
   let ops = opsAsList spc in
   case findLeftmost (fn (_, id0, _) -> id0 = id) ops of
     | Some (_,_,info) -> definedOpInfo? info
     | _ -> false

 op  definedOp? : Spec * QualifiedId -> Bool
 def definedOp? (spc,qid) =
   case findTheOp (spc, qid) of
     | Some info -> definedOpInfo? info
     | _ -> false

 op  declaredOp? : Spec * QualifiedId -> Bool
 def declaredOp? (spc,qid) =
   case findTheOp (spc, qid) of
     | Some _ -> true
     | _ -> false

% --------------------------------------------------------------------------------
(**
 * returns the list of qualified id's that are declared in the spec (types and ops)
 *)

 op getDeclaredQualifiedIds: Spec -> List QualifiedId
 def getDeclaredQualifiedIds spc =
   let qids = foldriAQualifierMap
                (fn (q, id, _, qids) -> Cons (Qualified (q, id), qids))
	        [] 
	        spc.types
   in
   let qids = foldriAQualifierMap
                (fn (q, id, _, qids) -> Cons (Qualified (q, id), qids))
		qids 
		spc.ops
   in
     qids

% --------------------------------------------------------------------------------

   op basicQualifier?   : Qualifier   -> Bool
   op basicQualifiedId? : QualifiedId -> Bool
   op basicTypeName?    : QualifiedId -> Bool
   op basicOpName?      : QualifiedId -> Bool

  def basicQualifiers = [
			 "Bool",       % can appear in raw translation rules
			 "Char", 
			 "Compare",
			 "Function",   % TODO: add Relations ?
			 "Integer", 
			 "IntegerAux", % special hack for unary minus
			 "List",
			 "Nat",
			 "Option",
			 "String",
		%	 "WFO",        % TODO: basic ??
			 "System"      % TODO: basic ??
			]

  def basicQualifier? q = q in? basicQualifiers
  (* def basicQualifiedId? (Qualified(q,_)) = member (q, basicQualifiers) *)

  def basicQualifiedId? qid =
    let (basic_type_names, basic_op_names) = getBaseNames() in
    qid in? basic_type_names || 
    qid in? basic_op_names

  def basicTypeName? qid =
    let (basic_type_names, _) = getBaseNames () in
    qid in? basic_type_names

  def basicOpName? qid =
    let (_, basic_op_names) = getBaseNames () in
    qid in? basic_op_names

endspec
