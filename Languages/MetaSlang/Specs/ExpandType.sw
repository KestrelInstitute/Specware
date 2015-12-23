(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

% Synchronized with version 1.8 of  SW4/Languages/MetaSlang/TypeChecker/TypeCheckUtilities.sl 

Utilities qualifying spec
 import Printer                                         % error messages
 import /Library/Legacy/DataStructures/MergeSort        % combining error messages
 import /Library/Legacy/DataStructures/ListPair         % misc utility
 import /Library/Unvetted/StringUtilities               % search
 import /Languages/MetaSlang/AbstractSyntax/Equalities  % equalType?
 import Elaborate/Utilities                             % freshMetaTyVar

 %% Similar to unfoldType, but obeys new rules for Quotient and Coproduct.
 %% Replace a base type by its instantiated definition, unless it is 
 %% defined as a Quotient or CoProduct,

 op  expandType : LocalEnv * MSType -> MSType
 def expandType (env, typ) = 
   let 
     def compare_qid (Qualified (q1, id1), Qualified (q2, id2)) =
       case String.compare (q1, q2) of
         | Equal  -> String.compare (id1, id2)
         | result -> result
   in
     expandTypeRec (env, typ, SplaySet.empty compare_qid)
   
 def expandTypeRec (env, typ, qids) : MSType = 
   let 
     def expansion_error (env, msg, pos) =
       let errors = env.errors in
       errors := Cons ((msg, pos), ! errors)

     def unlink_type t =
       case t of
         | MetaTyVar (mtv, _) -> 
           (case (! mtv).link of
              | Some t -> unlink_type t
              | _ -> t)
         | _ -> t

     def instantiate_type_scheme (env, pos, type_args, typ) = 
       let (tvs, unpacked_type) = unpackType typ in
       if ~(length type_args = length tvs) then
         (expansion_error (env, 
                           "\nInstantiation list (" ^ 
                             (foldl (fn (s,arg) -> s ^ " " ^ (printType arg)) "" type_args) ^
                             " ) does not match argument list (" ^ 
                             (foldl (fn (s,tv) -> s ^ " " ^ tv) "" tvs) ^
                             " )",
                           pos);
          unpacked_type)
       else
         let (new_mtvs, new_type) = metafy_type typ in
         (ListPair.app (fn (typ, mtv) -> 
                          let cell = ! mtv in
                          mtv := cell << {link = Some typ})
            (type_args, new_mtvs);
          new_type)

     def metafy_type typ =
       let (tvs, typ) = unpackType typ in
       if empty? tvs then
         ([],typ)
       else
         let mtvar_position = Internal "metafyType" in
         let tv_map = List.map (fn tv -> (tv, freshMetaTyVar ("metafy", mtvar_position))) tvs in
         let
           def mapTyVar (tv, tvs, pos) : MSType = 
             case tvs of
               | [] -> TyVar (tv, pos)
               | (tv1, s) :: tvs -> 
                 if tv = tv1 then s else mapTyVar (tv, tvs, pos)
                   
           def cp (typ : MSType) = 
             case typ of
               | TyVar (tv, pos) -> mapTyVar (tv, tv_map, pos)
               | typ -> typ
         in
           let typ  = mapType (id, cp, id) typ in
           let mtvs = List.map (fn (_, (MetaTyVar (y, _))) -> y) tv_map in
           (mtvs, typ)

   in
   let unlinked_type = unlink_type typ in
   case unlinked_type of
    | Base (qid, type_args, pos) -> 
      if SplaySet.member (qids, qid) then
	(expansion_error (env,
                          "The type " ^ (printQualifiedId qid) ^ " is recursively defined using itself",
                          pos);
	 unlinked_type)
      else
        (case findTheType (env.internal, qid) of   % was findAllTypes which is just wrong
          | Some info ->
	    (if ~ (definedTypeInfo? info) then
	       let tvs = firstTypeDefTyVars info in
	       let l1 = length tvs in
	       let l2 = length type_args in
	       ((if l1 ~= l2 then
		   expansion_error (env,
                                    "\nInstantiation list (" ^ 
                                      (foldl (fn (s,arg) -> s ^ " " ^ (printType arg)) "" type_args) ^
                                      " ) does not match argument list (" ^ 
                                      (foldl (fn (s,tv) -> s ^ " " ^ tv) "" tvs) ^
                                      " )",
                                    pos)
		 else 
		   ());
		%% Use the primary name, even if the reference was via some alias.
                %% This normalizes all references to be via the same name.
		Base (primaryTypeName info, type_args, pos))
	     else
	       let defs = typeInfoDefs info in
	       let true_defs = filter (fn typ ->
				       case typeInnerType typ of
					 | Quotient  _ -> false
					 | CoProduct _ -> false
					 | _  -> true)
	                              defs
	       in
               if empty? true_defs then
                 unlinked_type
               else
                 let base_defs = filter (fn typ ->
                                           let (tvs, typ) = unpackType typ in
                                           case typ of
                                             | Base _ -> true
                                             | _      -> false)
                                        true_defs
                 in
                   case base_defs of
                     | [] ->
                       let dfn = maybeAndType (true_defs, typeAnn info.dfn) in
                       instantiate_type_scheme (env, pos, type_args, dfn)
                     | _ ->
                       %% A base type can be defined in terms of other base types
                       %% So we unfold recursively here.
                       let dfn = maybeAndType (base_defs, typeAnn info.dfn) in
                       instantiate_type_scheme (env, pos, type_args, dfn)
                       % expandTypeRec (env,
                       %                instantiate_type_scheme (env, pos, type_args, dfn),
                       %                %% Watch for self-references, even via aliases: 
                       %                foldl (fn (qids,qid) -> SplaySet.add (qids, qid))
                       %                      qids
                       %                      info.names)
                       )
          | None -> 
	    (expansion_error (env, "Could not find type "^ printQualifiedId qid, pos);
	     unlinked_type))
   %| Boolean is the same as default case
    | s -> s 

endspec
