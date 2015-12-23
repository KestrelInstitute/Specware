(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

ConformOpDecls qualifying spec 

 import /Languages/MetaSlang/CodeGen/CodeGenUtilities

 (*
  * conformOpDecls checks whether we have an opdef of the form
  *
  * type P = A * B
  * op foo: P -> Q
  * def foo (a, b) = ...
  *
  * i.e. the declaration contains the user type name, but the arguments refer to its definition term.
  * ops are transformed to something like
  * 
  * def foo (arg) = 
  *   let a = arg^1 in
  *   let b - arg^2 in
  *   ...
  *)

 op SpecTransform.conformOpDecls (spc : Spec) : Spec =
  %let _ = writeLine ("lambdaToInner...") in
  let ops = foldriAQualifierMap
             (fn (q, id, info, newops) ->
                let (old_decls, old_defs) = opInfoDeclsAndDefs info in
                let new_defs = 
                    List.map (fn dfn ->
                                let (tvs, srt, term) = unpackFirstTerm dfn in
                                let new_tm = conformOpDeclsTerm (spc, srt, term, id) in
                                maybePiTerm (tvs, TypedTerm (new_tm, srt, termAnn term)))
                             old_defs
                in
                let new_dfn = maybeAndTerm (old_decls ++ new_defs, termAnn info.dfn) in
                let new_info = info << {dfn = new_dfn} in
                insertAQualifierMap (newops, q, id, new_info))
             emptyAQualifierMap 
             spc.ops
  in
  setOps (spc, ops)

 op conformOpDeclsTerm (spc : Spec, typ : MSType, term : MSTerm, _ : Id) : MSTerm =
  let typ = unfoldToArrow (spc, typ) in
  case typ of
    | Arrow (domain as (Base _), _, _) ->
      let domain = unfoldToProduct (spc, domain) in
      (case domain of
         | Product (fields, _) ->
           let termtype = inferType (spc, term) in
           (case termtype of
              | Arrow (Product (fields0, _), _, _) ->
                if productfieldsAreNumbered (fields0) then
                  case term of
                    | Lambda ([(pat, _, bodyterm)], b) ->
                      let optplist =
                          (case pat of
                             | VarPat ((id, _), _) -> Some[id]
                             | RecordPat (plist, _) -> 
                               if forall? (fn | (_, VarPat _) -> true | (_, _) -> false) plist then
                                 Some (List.map (fn (_, VarPat ((id, _), _)) -> id) plist)
                               else
                                 None
                             | _ -> None)
                      in
                      (case optplist of
                         | None -> term
                         | Some plist -> 
                           if length (fields0) = length (plist) then
                             %let _ = writeLine ("checking "^id^"...")   in
                             let argname    = "_arg"                     in
                             let pnamestyps = zip (plist, fields0)       in
                             let bodyterm   = foldr (fn ((variable, (id, ftyp)), bodyterm) ->
                                                       let proj = Fun (Project (id), Arrow (typ, ftyp, b), b) in
                                                       let pterm = Apply (proj, Var ((argname, typ), b), b) in
                                                       Let ([(VarPat ((variable, ftyp), b), pterm)], bodyterm, b))
                                                    bodyterm 
                                                    pnamestyps
                             in
                             let cond       = mkTrue ()                  in
                             let newpat     = VarPat ((argname, typ), b) in
                             Lambda ([(newpat, cond, bodyterm)], b)
                           else
                             term)
                    | _ ->term
                else term
              | _ -> term)
         | _ -> term)
    | _ -> term
       


end-spec
