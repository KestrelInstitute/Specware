(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SpecCalc qualifying spec 

 import ../../Environment                        % monad
 import /Languages/MetaSlang/Specs/Equivalences  % equivType?

 op  complainIfAmbiguous : Spec -> Position -> Env Spec
 def complainIfAmbiguous spc pos =
   case auxComplainIfAmbiguous spc of
     | (Some spc, _) -> return spc
     | (_, Some msg) -> raise (SpecError (pos,msg))

 op  auxComplainIfAmbiguous : Spec -> (Option Spec) * (Option String)
 def auxComplainIfAmbiguous spc =
   let def check_op(spc, qid, result) =
         case findTheOp(spc, qid) of
           | None -> result
           | Some info ->
         let fixity_err? = embed? Error info.fixity in
         let ambiguous? = check_op_ambiguity(spc, info) in
         if ~fixity_err? && ~ambiguous? then result
         else
         let (ambiguous_types, bad_fixity_ops, ambiguous_ops) = result in
         (ambiguous_types,
          if fixity_err? then ListUtilities.insert (info, bad_fixity_ops) else bad_fixity_ops,
          if ambiguous? then ListUtilities.insert (info, ambiguous_ops) else ambiguous_ops)
       def check_op_ambiguity(spc, info) =
         let (decls, defs) = opInfoDeclsAndDefs info in
         case (decls, defs) of
           | ([],  [])  -> false
           | ([],  [_]) -> false
           | ([_], [])  -> false
           | ([x], [y]) -> 
             let xtype = termType x in
             let ytype = termType y in
             ~(equivType? spc (xtype, ytype))
           | _ -> true
   in
   let (ambiguous_types, bad_fixity_ops, ambiguous_ops) =
       foldl (fn (result, el) ->
              case el of
                | TypeDef(qid, _) ->
                  (case findTheType(spc, qid) of
                     | None -> result
                     | Some info ->
                       let (decls, defs) = typeInfoDeclsAndDefs info in
                       if length decls <= 1 && length defs <= 1 then result
                       else let (ambiguous_types, bad_fixity_ops, ambiguous_ops) = result in
                            (ListUtilities.insert (info, ambiguous_types),
                             bad_fixity_ops, ambiguous_ops))
                | Op(qid, _, _) -> check_op(spc, qid, result)
                | OpDef(qid, _, _, _) -> check_op(spc, qid, result)
                | _ -> result)
         ([], [], [])
         spc.elements
   in
   if ambiguous_types = [] && bad_fixity_ops = []  % && ambiguous_ops = []
     then (Some spc, None)
   else
     let type_msg = 
         case ambiguous_types of
	   | [] -> ""
	   | _ ->
	     (foldl (fn (msg, type_info) ->
		     msg ^ (ppFormat (ppATypeInfo type_info)))
	            "\nAmbiguous types:\n"
		    ambiguous_types)
	     ^ "\n"
     in
     let fixity_msg = 
         case bad_fixity_ops of
	   | [] -> ""
	   | _ ->
	     (foldl (fn (msg, opinfo) ->
		     msg ^ (printAliases opinfo.names) ^ " : " ^ (ppFormat (ppFixity opinfo.fixity)))
	            "\nOps with multiple fixities:\n"
		    bad_fixity_ops)
     in
     let op_msg = 
         case ambiguous_ops of
	   | [] -> ""
	   | _ ->
	     (foldl (fn (msg, opinfo) ->
		     msg ^ (ppFormat (ppAOpInfo opinfo)))
	            "\nAmbiguous ops:\n"
		    ambiguous_ops)
     in
       (None, Some ("\n" ^ type_msg ^ fixity_msg ^ op_msg ^ "\n"))

endspec
