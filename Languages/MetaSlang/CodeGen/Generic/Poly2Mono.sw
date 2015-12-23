(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Poly2Mono qualifying spec

 import /Languages/MetaSlang/Specs/StandardSpec
 import /Languages/MetaSlang/Specs/Environment
 import /Languages/MetaSlang/CodeGen/Generic/TypeOpInfos
 
 op InstantiateHO.typeMatch (t1 : MSType, t2 : MSType, spc : Spec) : TyVarSubst 
 op Java.typeId: MSType -> Id
 
  (**
  * transform a polymorphic spec into a monomorphic by instantiating polymorphic types
  * and op definitions. For each instantiation of a polymorphic type/term a corresponding type/op
  * definition is introduced for the specific instantiation and the constructor/op name is changed
  * by appending the typeid of the instantiation.
  * e.g. List Nat
  * generated: type ListNat = | ConsNat Nat * ListNat | NilNat
  * uses of the constructors are renamed accordingly.
  * The fullspc is the spc + the base spec; the full spec is need in order to generate the monomorphic
  * types/ops for builtin entities (e.g., Lists, Option, etc)
  * @param keepPolyMorphic? controls whether the polymorphic types and ops should be included in the
  * resulting spec or not. If keepPolyMorphic? is false, the resulting spec will be free of polymorphic
  * entities.
  *)

 op SpecTransform.poly2monoAndDropPoly (spc : Spec) : Spec =
  poly2mono (spc, false)
 
 op poly2mono (spc : Spec, keepPolyMorphic? : Bool) : Spec =
  poly2monoInternal (spc, keepPolyMorphic?, false) 
 
 op poly2monoForSnark (spc : Spec, keepPolyMorphic? : Bool) : Spec =
  poly2monoInternal (spc, keepPolyMorphic?, true) 
 
 op poly2monoInternal (spc                 : Spec, 
                       keepPolyMorphic?    : Bool, 
                       modifyConstructors? : Bool) 
  : Spec =
  let 
    def processTypeinfo (Qualified (q, id), info, typemap, minfo) =
      let pos                   = typeAnn info.dfn          in
      let (old_decls, old_defs) = typeInfoDeclsAndDefs info in
      let (new_defs, minfo) =
          foldl (fn ((defs, minfo), def0) ->
 		   let (tvs, typ)   = unpackType def0                                in
 		   let (typ, minfo) = p2mType (spc, modifyConstructors?, typ, minfo) in
 		   let ndef         = maybePiType (tvs, typ)                         in
 		   let defs         = defs ++ [ndef]                                 in
 		   (defs, minfo)) 
 		([], minfo) 
 		old_defs
      in
      let dfn  = maybeAndType (old_decls ++ new_defs, pos)  in
      let info = info << {dfn = dfn}                        in
      let tmap = insertAQualifierMap (typemap, q, id, info) in
      (tmap, minfo)
 
    def processOpinfo (Qualified (q, id), info, opmap, minfo) =
      let pos                   = termAnn info.dfn        in
      let (tvs, typ, _)         = unpackFirstOpDef info   in
      let (old_decls, old_defs) = opInfoDeclsAndDefs info in
      let (new_decls_and_defs, minfo) =
          foldl (fn ((defs, minfo), def0) ->
 		   let (tvs, old_typ, old_trm) = unpackFirstTerm def0                                          in
 		   let (new_typ, minfo)        = p2mType (spc, modifyConstructors?, old_typ, minfo)            in
 		   let (new_trm, minfo)        = p2mTerm (spc, modifyConstructors?, old_trm, minfo)            in
 		   let ndef                    = maybePiTerm (tvs, TypedTerm (new_trm, new_typ, termAnn def0)) in
 		   let defs                    = defs ++ [ndef]                                                in
                   (defs, minfo)) 
 		([], minfo) 
 		(old_decls ++ old_defs)
      in
      let dfn  = maybeAndTerm (new_decls_and_defs, pos)   in
      let info = info << {dfn = dfn}                      in
      let omap = insertAQualifierMap (opmap, q, id, info) in
      (omap, minfo)

    def modElts (elts, minfo, ops, types) =
      foldl (fn ((rev_elts, minfo, ops, types), el) ->
               case el of
 		 | Type (qid, _) ->
                   (case findTheType (spc, qid) of
                      | Some typeinfo ->
                        let (types, new_minfo) = processTypeinfo (qid, typeinfo, types, minfo) in
                        let el_s               = if keepPolyMorphic? || firstTypeDefTyVars typeinfo = [] then 
                                                   [el] 
                                                 else 
                                                   [] 
                        in
                        incorporateMinfo (rev_elts, el_s, new_minfo, minfo, ops, types)
                      | _ ->
                        (rev_elts, minfo, ops, types))
 		 | TypeDef (qid, _) ->
                   (case findTheType (spc, qid) of
                      | Some typeinfo ->
                        let (types, new_minfo) = processTypeinfo (qid, typeinfo, types, minfo) in
                        let el_s               = if keepPolyMorphic? || firstTypeDefTyVars typeinfo = [] then 
                                                   [el] 
                                                 else 
                                                   [] 
                        in
                        incorporateMinfo (rev_elts, el_s, new_minfo, minfo, ops, types)
                      | _ ->
                        (rev_elts, minfo, ops, types))
 
 		 | Op (qid, def?, _) ->
 		   (case findTheOp (spc, qid) of
                      | Some opinfo ->
                        let (ops, new_minfo) = processOpinfo (qid, opinfo, ops, minfo) in
                        let el_s             = if keepPolyMorphic? || firstOpDefTyVars opinfo = [] then 
                                                 [el] 
                                               else 
                                                 [] 
                        in
                        incorporateMinfo (rev_elts, el_s, new_minfo, minfo, ops, types)
                      | _ ->
                        (rev_elts, minfo, ops, types))
 		 | OpDef (qid, _, _, _) ->
                   (case findTheOp(spc, qid) of
                      | Some opinfo ->
                        let (ops, new_minfo) = processOpinfo (qid, opinfo, ops, minfo) in
                        let el_s             = if keepPolyMorphic? || firstOpDefTyVars opinfo = [] then
                                                 [el] 
                                               else 
                                                 []
                        in
                        incorporateMinfo (rev_elts, el_s, new_minfo, minfo, ops, types)
                      | _ ->
                        (rev_elts, minfo, ops, types))

 		 | Property (ptype, pname, tv, t, pos) ->
 		   let (trm, new_minfo) = p2mTerm (spc, modifyConstructors?, t, minfo) in
 		   let nprop            = Property (ptype, pname, tv, trm, pos)        in
 		   incorporateMinfo (rev_elts, [nprop], new_minfo, minfo, ops, types)

 		 | Import (s_tm, i_sp, elts, pos) ->
 		   let (rev_imported_elts, minfo, ops, types) = modElts (elts, minfo, ops, types)                   in
                   let new_elt                                = Import (s_tm, i_sp, reverse rev_imported_elts, pos) in
                   let new_elts                               = new_elt :: rev_elts                                 in
 		   (new_elts, minfo, ops, types)

 		 | _ -> 
                   (el :: rev_elts, minfo, ops, types))

            ([], minfo, ops, types) 
            elts
  in
  let (rev_elts, minfo, ops, types) = modElts (spc.elements, emptyMonoInfo, spc.ops, spc.types) in
  let elts  = reverse rev_elts in
  let types = foldl (fn (map, info) -> 
                       let Qualified (q, id) = primaryTypeName info in
                       insertAQualifierMap (map, q, id, info))
                    types 
                    minfo.types
  in
  let ops   = foldl (fn (map, info) -> 
                       let Qualified (q, id) = primaryOpName info in
                       insertAQualifierMap (map, q, id, info))
                    ops 
                    minfo.ops
  in

  % remove polymorphic type/op defs (disabled)
  let types = 
      if keepPolyMorphic? then 
        types 
      else 
        foldriAQualifierMap (fn (q, id, info, map) ->
                               if q = "Accord" && id = "Update" then
                                 insertAQualifierMap (map, q, id, info)
                               else
                                 case firstTypeDefTyVars info of
                                   | [] -> insertAQualifierMap (map, q, id, info)
                                   | _ -> map)
                            emptyATypeMap 
                            types
  in
  let ops = 
      if keepPolyMorphic? then 
        ops 
      else
        foldriAQualifierMap (fn (q, id, info, map) ->
                               case firstOpDefTyVars info of
                                 | [] -> insertAQualifierMap (map, q, id, info)
                                 | _ -> map)
                            emptyAOpMap 
                            ops
  in
  let spc = setTypes    (spc, types) in
  let spc = setOps      (spc, ops)   in
  let spc = setElements (spc, elts)  in
  spc
 
 op p2mType (spc                 : Spec, 
             modifyConstructors? : Bool, 
             typ                 : MSType, 
             minfo               : TypeOpInfos) 
  : MSType * TypeOpInfos =
  case typ of
    | Base (qid0 as Qualified (q, id), insttv as _::_, pos) ->
      % We are trying to simplify instances of polymorphic types where
      % all the type vars have been instantitated.
      if q = "Accord" && (id = "ProcType" || id = "Update") then 
 	% Process the args to ProcType or Update, but leave the
 	% main type as ProcType or Update.  These types control
 	% later Accord processing and are eliminated by Accord
 	% once their usefulness is over.
 	let (new_args, minfo) = 
            foldl (fn ((new_args, minfo), typ) -> 
                     let (typ, minfo) = p2mType (spc, modifyConstructors?, typ, minfo) in
                     (new_args ++ [typ], minfo))
 	          ([], minfo)
 		  insttv
 	in
 	let new_typ =  Base (qid0, new_args, pos) in
 	(new_typ, minfo) 
      else
        if exists? (fn (TyVar _) -> true | s -> false) insttv then (typ, minfo) else
          let suffix = getTypeNameSuffix insttv in
          let qid    = Qualified (q, id^suffix) in
          % let _    = writeLine ("instantiated Type: "^printQualifiedId qid) in
          let minfo = 
              if monoInfosContainType? (qid, minfo) then 
                minfo
              else
                case findTheType (spc, qid0) of
                  | Some info ->
                    let names         = info.names              in
                    let (tvs, typdef) = unpackFirstTypeDef info in
                    (case (tvs, typdef) of
                       | (_::_, Any _) ->
                         % DAC:  Added this case for uninterpreted types.  After looking at the
                         % code below for the interpreted case I am not sure this is the right
                         % thing to do for code-generation, because in the above code, care is
                         % to exchange the typ definition types for the original types.
                         % However, this case is needed for the Snark translator and to ensure
                         % that the resulting spec is a valid metaslang spec.
                         if modifyConstructors? then % using modifyConstructors? as synonym for "for snark, but not for codeGen"
                           let tvsubst = zip (tvs, insttv) in
                           let names   = qid :: filter (fn qid1 -> qid1 ~= qid0) names in 
                           let sinfo   = {names = names, 
                                          dfn   = Any noPos} 
                           in
                           let minfo   = addTypeInfo2TypeOpInfos (qid, sinfo, minfo) in
                           minfo
                         else 
                           minfo
                       | (_::_, _) ->
                         let tvsubst         = zip (tvs, insttv)                                 in
                         let names           = qid :: filter (fn qid1 -> qid1 ~= qid0) names     in 
                         let typdef          = applyTyVarSubst2Type (typdef, tvsubst)            in
                         let typdef          = if modifyConstructors? then
                                                 addTypeSuffixToConstructors (typdef, suffix)
                                               else 
                                                 typdef
                         in
                         % add it first to prevent infinite loop:
                         let tmp_sinfo       = {names = names, dfn = typdef}                     in
                         let minfo           = addTypeInfo2TypeOpInfos (qid, tmp_sinfo, minfo)   in
                         let (typdef, minfo) = p2mType (spc, modifyConstructors?, typdef, minfo) in
                         let sinfo           = {names = names, dfn = typdef}                     in
                         let minfo           = exchangeTypeInfoInTypeOpInfos (qid, sinfo, minfo) in
                         minfo
                       | _ -> minfo)
                  | _ -> minfo
         in
 	 (Base (qid, [], pos), minfo)

    | Boolean _ -> (typ, minfo) 

    | Arrow (typ1, typ2, pos) ->
      let (typ1, minfo) = p2mType (spc, modifyConstructors?, typ1, minfo) in
      let (typ2, minfo) = p2mType (spc, modifyConstructors?, typ2, minfo) in
      (Arrow (typ1, typ2, pos), minfo)

    | Product (fields, pos) ->
      let (fields, minfo) = foldl (fn ((fields, minfo), (id, typ)) ->
                                     let (typ, minfo) = p2mType (spc, modifyConstructors?, typ, minfo) in
                                     (fields ++ [(id, typ)], minfo))
                                  ([], minfo) 
                                  fields
      in
      (Product (fields, pos), minfo)

    | CoProduct (fields, pos) ->
      let (fields, minfo) = 
          foldl (fn ((fields, minfo), (id, opttyp)) ->
                   let (opttyp, minfo) = 
                   case opttyp of
                     | None -> (None, minfo)
                     | Some typ ->
                       let (typ, minfo) = p2mType (spc, modifyConstructors?, typ, minfo) in
                       (Some typ, minfo)
                   in
                   (fields ++ [(id, opttyp)], minfo))
                ([], minfo) 
                fields
      in
      (CoProduct (fields, pos), minfo)

    | Quotient (typ, t, pos) ->
      let (typ, minfo) = p2mType (spc, modifyConstructors?, typ, minfo) in
      let (t,   minfo) = p2mTerm (spc, modifyConstructors?, t,   minfo) in
      (Quotient (typ, t, pos), minfo)

    | Subtype (typ, t, pos) ->
      let (typ, minfo) = p2mType (spc, modifyConstructors?, typ, minfo) in
      let (t,   minfo) = p2mTerm (spc, modifyConstructors?, t,   minfo) in
      (Subtype (typ, t, pos), minfo)

    | _ -> (typ, minfo)
 
 op p2mTerm (spc                 : Spec,
             modifyConstructors? : Bool, 
             term                : MSTerm, 
             minfo               : TypeOpInfos)
  : MSTerm * TypeOpInfos =
  case term of

    | Apply (t1, t2, pos) ->
      let (t1, minfo) = p2mTerm (spc, modifyConstructors?, t1, minfo) in
      let (t2, minfo) = p2mTerm (spc, modifyConstructors?, t2, minfo) in
      (Apply (t1, t2, pos), minfo)

    | Bind (binder, varlist, body, pos) ->
      let (varlist, minfo) = 
          foldl (fn ((varlist, minfo), (id, typ)) ->
                   let (typ, minfo) = p2mType (spc, modifyConstructors?, typ, minfo) in
                   (varlist ++ [(id, typ)], minfo))
                ([], minfo) 
                varlist
      in
      let (body, minfo) = p2mTerm (spc, modifyConstructors?, body, minfo) in
      (Bind (binder, varlist, body, pos), minfo)

    | Record (fields, pos) ->
      let (fields, minfo) = 
          foldl (fn ((fields, minfo), (id, trm)) ->
                   let (trm, minfo) = p2mTerm (spc, modifyConstructors?, trm, minfo) in
                   (fields ++ [(id, trm)], minfo))
                ([], minfo) 
                fields
      in
      (Record (fields, pos), minfo)

    | Let (patTerms, body, pos) ->
      let (patTerms, minfo) = 
          foldl (fn ((patTerms, minfo), (pat, trm)) ->
                   let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
                   let (trm, minfo) = p2mTerm    (spc, modifyConstructors?, trm, minfo) in
                   (patTerms ++ [(pat, trm)], minfo))
                ([], minfo) 
                patTerms
      in
      let (body, minfo) = p2mTerm (spc, modifyConstructors?, body, minfo) in
      (Let (patTerms, body, pos), minfo)

    | LetRec (varTerms, body, pos) ->
      let (varTerms, minfo) = 
          foldl (fn ((varTerms, minfo), ((id, typ), trm)) ->
                   let (typ, minfo) = p2mType (spc, modifyConstructors?, typ, minfo) in
                   let (trm, minfo) = p2mTerm (spc, modifyConstructors?, trm, minfo) in
                   (varTerms ++ [((id, typ), trm)], minfo))
                ([], minfo) 
                varTerms
      in
      let (body, minfo) = p2mTerm (spc, modifyConstructors?, body, minfo) in
      (LetRec (varTerms, body, pos), minfo)

    | Var ((id, typ), pos) ->
      let (typ, minfo) = p2mType (spc, modifyConstructors?, typ, minfo) in
      (Var ((id, typ), pos), minfo)

    | Fun (fun, typ, pos) -> 
      let (fun, typ, minfo) = p2mFun (spc, modifyConstructors?, fun, typ, minfo) in
      (Fun (fun, typ, pos), minfo)

    | Lambda (match, pos) ->
      let (match, minfo) = 
          foldl (fn ((match, minfo), (pat, t1, t2)) ->
                   let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
                   let (t1,  minfo) = p2mTerm    (spc, modifyConstructors?, t1,  minfo) in
                   let (t2,  minfo) = p2mTerm    (spc, modifyConstructors?, t2,  minfo) in
                   (match ++ [(pat, t1, t2)], minfo))
                ([], minfo) 
                match
      in
      (Lambda (match, pos), minfo)

    | IfThenElse (t1, t2, t3, pos) ->
      let (t1, minfo) = p2mTerm (spc, modifyConstructors?, t1, minfo) in
      let (t2, minfo) = p2mTerm (spc, modifyConstructors?, t2, minfo) in
      let (t3, minfo) = p2mTerm (spc, modifyConstructors?, t3, minfo) in
      (IfThenElse (t1, t2, t3, pos), minfo)

    | Seq (terms, pos) ->
      let (terms, minfo) = 
          foldl (fn ((terms, minfo), tm) ->
                   let (tm, minfo) = p2mTerm (spc, modifyConstructors?, tm, minfo) in
                   (terms ++ [tm], minfo))
                ([], minfo) 
                terms
      in
      (Seq (terms, pos), minfo)

    | TypedTerm (trm, typ, pos) ->
      let (trm, minfo) = p2mTerm (spc, modifyConstructors?, trm, minfo) in
      let (typ, minfo) = p2mType (spc, modifyConstructors?, typ, minfo) in
      (TypedTerm (trm, typ, pos), minfo)

    | _ -> (term, minfo)
 
 op p2mPattern (spc                 : Spec,
                modifyConstructors? : Bool, 
                pat                 : MSPattern, 
                minfo               : TypeOpInfos)
  : MSPattern * TypeOpInfos =
  case pat of

    | EmbedPat (Qualified(q,id), opt_pat, typ, pos) ->
      % Given "| Foo List (Nat)", we might convert to "| Foo_Nat List_Nat"
      let id = 
          case typ of
            | Base (_, insttv as _::_, _) ->
              if ~ modifyConstructors? || (exists? (fn (TyVar _) -> true | s -> false) insttv) then 
                id
              else 
                id ^ (getTypeNameSuffix insttv)
            % Boolean is same as default 
            | _ -> id
      in
      let (opt_pat, minfo) = 
          case opt_pat of
            | Some pat ->
              let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
              (Some pat, minfo)
            | _ -> 
              (None, minfo)
      in
      let (typ, minfo) = p2mType (spc, modifyConstructors?, typ, minfo) in
      (EmbedPat (Qualified(q,id), opt_pat, typ, pos), minfo)

    | AliasPat (pat1, pat2, pos) ->
      let (pat1, minfo) = p2mPattern (spc, modifyConstructors?, pat1, minfo) in
      let (pat2, minfo) = p2mPattern (spc, modifyConstructors?, pat2, minfo) in
      (AliasPat (pat1, pat2, pos), minfo)

    | VarPat ((id, typ), pos) ->
      let (typ, minfo) = p2mType (spc, modifyConstructors?, typ, minfo) in
      (VarPat ((id, typ), pos), minfo)

    | WildPat (typ, pos) ->
      let (typ, minfo) = p2mType (spc, modifyConstructors?, typ, minfo) in
      (WildPat (typ, pos), minfo)

    | RecordPat (fields, pos) ->
      let (fields, minfo) = 
          foldl (fn ((fields, minfo), (id, pat)) ->
                   let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
                   (fields ++ [(id, pat)], minfo))
 	        ([], minfo) 
 		fields
      in
      (RecordPat (fields, pos), minfo)

    | QuotientPat (pat, qid, tys, pos) ->
      let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
      (QuotientPat (pat, qid, tys, pos), minfo)

    | RestrictedPat (pat, typ, pos) ->
      let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
      let (typ, minfo) = p2mTerm    (spc, modifyConstructors?, typ, minfo) in
      (RestrictedPat (pat, typ, pos), minfo)

    | TypedPat (pat, typ, pos) ->
      let (pat, minfo) = p2mPattern (spc, modifyConstructors?, pat, minfo) in
      let (typ, minfo) = p2mType    (spc, modifyConstructors?, typ, minfo) in
      (TypedPat (pat, typ, pos), minfo)

    | _ -> (pat, minfo)
 
 op p2mFun (spc                 : Spec, 
            modifyConstructors? : Bool, 
            fun                 : MSFun, 
            typ                 : MSType, 
            minfo               : TypeOpInfos)
  : MSFun * MSType * TypeOpInfos =
  let (typ1, minfo) = p2mType (spc, modifyConstructors?, typ, minfo) in
  case fun of

    | Embed (Qualified(q,id), b?) ->
      let cptyp = case typ of
                    | Arrow (_, typ, _) -> typ
                    | _ -> typ
      in
      let cptyp = unfoldBeforeCoProduct (spc, cptyp) in
      (case cptyp of
         | Base (sqid, insttv as _::_, _) ->
           let fun = 
               if ~modifyConstructors? || (exists? (fn (TyVar _) -> true | s -> false) insttv) then 
                 fun
               else
                 % constructor Cons could become Cons_Nat for List (Nat), etc.
                 Embed (Qualified(q,id ^ (getTypeNameSuffix insttv)), b?)
           in
           (fun, typ1, minfo)
         % Boolean is same as default
         | _ -> (fun, typ1, minfo))
 
    | Embedded (Qualified(q,id)) ->
      let cptyp = case typ of
                    | Arrow (typ, _, _) -> typ
                    | _ -> typ
      in
      let cptyp = unfoldBeforeCoProduct (spc, cptyp) in
      (case cptyp of
         | Base (sqid, insttv as _::_, _) ->
           let fun = 
               if ~modifyConstructors? || (exists? (fn (TyVar _) -> true | s -> false) insttv) then 
                 fun
               else
                 % constructor Cons could become Cons_Nat for List (Nat), etc.
                 Embedded (Qualified(q,id ^ (getTypeNameSuffix insttv)))
           in
           (fun, typ1, minfo)
         % Boolean is same as default
         | _ -> (fun, typ1, minfo))
 
    | Op (qid as Qualified (q, id), fix) ->
      (case AnnSpec.findTheOp (spc, qid) of
 	 | None -> (fun, typ1, minfo)
 	 | Some info ->
 	   let (mtvs, atyp, term) = unpackFirstOpDef info in
 	   if definedOpInfo? info then
             let tvsubst0 = typeMatch (atyp, typ, spc)                              in
             let tvsubst  = filter (fn (id, TyVar _) -> false | _ -> true) tvsubst0 in
             if tvsubst = [] then 
               (fun, typ1, minfo) 
             else
               let ntvs  = map (fn (id, _) -> id) 
                               (filter (fn (id, TyVar _) -> true | _ -> false) 
                                       tvsubst0) 
               in
               let nqid  = Qualified (q, id ^ getTypeNameFromTyVarSubst tvsubst) in
               let names = nqid :: filter (fn qid0 -> qid0 ~= qid) info.names    in
               let nfun  = Op (nqid, fix)                                        in
               let minfo = 
                   if monoInfosContainOp? (nqid, minfo) then 
                     minfo
                   else
                     % construct the new opinfo
                     let term          = applyTyVarSubst2Term (term, tvsubst)                     in
                     let dfn           = maybePiTerm (mtvs, TypedTerm (Any noPos, typ1, noPos))   in
                     let tmp_opinfo    = info << {names = names, dfn = dfn}                       in
                     let tmp_minfo     = addOpInfo2TypeOpInfos (nqid, tmp_opinfo, minfo)          in
                     let (term, minfo) = p2mTerm (spc, modifyConstructors?, term, tmp_minfo)      in
                     let dfn           = maybePiTerm (ntvs, TypedTerm (term, typ1, termAnn term)) in
                     let nopinfo       = info << {names = names, dfn = dfn}                       in
                     let minfo         = exchangeOpInfoInTypeOpInfos (nqid, nopinfo, minfo)       in
                     minfo
               in
               (nfun, typ1, minfo)
           else if modifyConstructors? then % using modifyConstructors? as synonym for "for snark, but not for codeGen"
             let tvsubst0 = typeMatch (atyp, typ, spc)                              in
             let tvsubst  = filter (fn (id, TyVar _) -> false | _ -> true) tvsubst0 in
             if tvsubst = [] then 
               (fun, typ1, minfo)
             else
               let ntvs  = map (fn (id, _) -> id) (filter (fn (id, TyVar _) -> true | _ -> false) tvsubst0) in
               let nqid  = Qualified (q, id ^ getTypeNameFromTyVarSubst tvsubst)                            in
               let names = nqid :: filter (fn qid0 -> qid0 ~= qid) info.names                               in
               let nfun  = Op (nqid, fix)                                                                   in
               let minfo = 
                   if monoInfosContainOp? (nqid, minfo) then 
                     minfo
                   else
                     % construct the new opinfo
                     let dfn        = maybePiTerm (mtvs, TypedTerm (Any noPos, typ1, noPos)) in
                     let tmp_opinfo = info << {names = names, dfn = dfn}                     in
                     let minfo      = addOpInfo2TypeOpInfos (nqid, tmp_opinfo, minfo)        in
                     % let nopinfo = info << {typ = (ntvs, typ1)} in
                     % let _ = if id = "empty_seq" then writeLine ("adding new opinfo for "^id^" with "^natToString (length (ntvs))^" tyvars...") else () in
                     % let _ = if id = "empty_seq" then writeLine (printTypeOpInfos minfo) else () in
                     minfo
               in
               (nfun, typ1, minfo)
           else 
             (fun, typ1, minfo))

    % Not/And/Or/Implies/Equals/NotEquals are all same as default

    | _ -> (fun, typ1, minfo)
 
 op incorporateMinfo (elts                                            : SpecElements, 
                      el_s                                            : SpecElements, 
                      new_minfo as {ops = new_ops, types = new_types} : TypeOpInfos, 
                      old_minfo as {ops = old_ops, types = old_types} : TypeOpInfos, 
                      ops                                             : OpMap, 
                      types                                           : TypeMap)
  : SpecElements * TypeOpInfos * OpMap * TypeMap =
  % Add newly added ops and types to elts before el (note elts are in reverse of their final order)
  let 

    def newTypes new_types =
      if new_types = old_types then 
        []
      else 
        let typinfo :: r_types = new_types               in
        let qid                = primaryTypeName typinfo in
        let new_elt            = TypeDef (qid, noPos)    in
        new_elt :: newTypes r_types

    def newOps new_ops =
      if new_ops = old_ops then 
        []
      else 
        let opinfo :: r_ops = new_ops                   in
        let qid             = primaryOpName opinfo      in
        let new_elt1        = OpDef (qid, 0, None, noPos) in
        let new_elt2        = Op    (qid, false, noPos) in
        % false means don't print def as part of decl
        new_elt1 :: new_elt2 :: newOps r_ops
  in
  let new_elts = el_s ++ (newOps new_ops) ++ (newTypes new_types) ++ elts in
  (new_elts, new_minfo, ops, types)
   
 op getTypeNameFromTyVarSubst (subst : TyVarSubst) : String =
  getTypeNameSuffix (map (fn (_, typ) -> typ) subst)
 
 op getTypeNameSuffix (instlist : MSTypes) : String =
  case instlist of
    | [] -> ""
    | typ :: instlist -> 
      "_" ^ (typeId typ) ^ getTypeNameSuffix instlist
 
 op applyTyVarSubst2Term (trm : MSTerm, subst : TyVarSubst) : MSTerm =
  let 
    def inst typ = 
      instantiateTyVars (typ, subst)
  in
  mapTerm (id, inst, id) trm
 
 op applyTyVarSubst2Type (typ : MSType, subst : TyVarSubst) : MSType =
  let 
    def inst typ = 
      instantiateTyVars (typ, subst)
  in
  mapType (id, inst, id) typ
 
 op addTypeSuffixToConstructors (typ : MSType, suffix : String) : MSType =
  case typ of
    | CoProduct (fields, pos) ->
      let fields = map (fn (Qualified(q,id), opttyp) -> (Qualified(q,id ^ suffix), opttyp)) fields in
      CoProduct (fields, pos)
    | _ -> typ
 
end-spec
 
