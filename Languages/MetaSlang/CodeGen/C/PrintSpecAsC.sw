PrintAsC qualifying spec 

 import PrintAsCUtils
 import PrintTypeAsC
 import PrintTermAsC

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% Code to find slice of elements that are both at-or-below top-level spec 
 %%% and also above CTarget.sw
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op findCSliceFrom (spc : Spec) : SpecElements =
  let
    def aux (all_elements, current_elements) =
      foldl (fn (all_elements, element) ->
               case element of
                 | Type    _ -> all_elements ++ [element]
                 | TypeDef _ -> all_elements ++ [element]
                 | Op      _ -> all_elements ++ [element]
                 | OpDef   _ -> all_elements ++ [element]
                 | Import (term, spc, imported_elements, _) -> 
                   %% TODO: the choice of specs whose elements should be included needs some thought
                   if refersToCTarget? term then  
                     all_elements                          % ignore CTarget itself
                   else if importsCTarget? spc then
                     aux (all_elements, imported_elements) % include specs that (recursively) import CTarget 
                   else
                     all_elements                          % ignore specs that don't (this includes the base specs)
                 | _ -> all_elements)
            all_elements            
            current_elements
  in
  aux ([], spc.elements)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op ppTypeInfoToH (status: CGenStatus, qid : QualifiedId, opt_info : Option TypeInfo)
  : Option (Prettys * CGenStatus) =
  case opt_info of
    | Some info -> 
      (case printTypeAsC_split (status, info.dfn) of
         | Some (pretty_base_type, index_lines, status) ->
           (case addNewType (qid, status) of
              | Some (c_type_name, status) ->
                Some ([string (case info.dfn of
                                 | Product _ -> "typedef struct "
                                 | _         -> "typedef "),
                       pretty_base_type,
                       string " ",
                       string c_type_name,
                       blockNone (0, index_lines)],
                      status)
              | - ->
                None)
         | _ ->
           None)
    | _ -> 
      let _ = writeLine ("Error in ppTypeInfoToH: no definition for type " ^ show qid) in
      None

 op ppOpInfoSig (status          : CGenStatus, 
                 qid             : QualifiedId, 
                 c_function_name : Id, 
                 opt_info        : Option OpInfo) 
  : Option (Prettys * CGenStatus) =
  case opt_info of
    | Some info -> 
      (case termType info.dfn of
         | Arrow (dom, rng, _) -> 
           (case printTypeAsC (status, rng) of
              | Some (pretty_rng, status) ->
                let opt_pat = 
                case info.dfn of
                  | Lambda ([(pat,_,_)], _) -> Some pat
                  | TypedTerm (Lambda ([(pat,_,_)], _), _, _) -> Some pat
                  | _ -> 
                    let _ = writeLine ("Error in ppOpInfoSig: definition not a lambda: " ^ printTerm info.dfn) in
                    None
                in
                let opt_args = 
                case opt_pat of
                  | Some (VarPat ((id, typ), _)) -> 
                    if legal_C_Id? id then
                      Some [(id, typ)]
                    else
                      let _ = writeLine ("Error in ppTypeInfoToH: illegal var name: " ^ id) in
                      None
                  | Some (RecordPat ([],        _)) -> Some []
                  | Some (pat as (RecordPat (id_pats,   _))) -> 
                    (case id_pats of
                       | ("1", _) :: _ ->
                         foldl (fn (opt_x, (_, pat)) ->
                                  case pat of
                                    | VarPat ((id, typ), _) ->
                                      (case opt_x of
                                         | Some pairs -> Some (pairs ++ [(id, typ)])
                                         | _ -> None)
                                    | _ ->
                                      let _ = writeLine ("Error in ppOpInfoSig: arg not a var: " ^ printPattern pat) in
                                      None)
                         (Some [])
                         id_pats
                                    | _ ->
                                      let _ = writeLine ("Error in ppOpInfoSig: args not a tuple: " ^ printPattern pat) in
                                      None)
                  | _ ->
                    None
                in
                let opt_blocks = 
                case opt_args of
                  | Some args ->
                    foldl (fn (opt_blocks, (id, typ)) -> 
                             case opt_blocks of
                               | Some blocks ->
                                 (case printTypeAsC (status, typ) of
                                    | Some (pretty, status) ->
                                      Some (blocks ++ [blockNone (0, [(0, pretty),
                                                                      (0, string " "),
                                                                      (0, string id)])])
                                    | _ ->
                                      None)
                               | _ ->
                                 None)
                    (Some [])
                    args
                               | _ ->
                                 None
                in
                case opt_blocks of
                  | Some blocks ->
                    let pretty_args =
                    AnnTermPrinter.ppList (fn block -> block)
                    (string "(", string ", ", string ")")
                    blocks
                    in
                    Some ([pretty_rng, string " ", string c_function_name, string " ", pretty_args],
                          status)
                  | _ ->
                    None)
         | _ ->
           let _ = writeLine ("Error in ppOpInfoSig: " ^ printQualifiedId qid ^ " does not have an arrow type") in
           None)
    | _ ->
      let _ = writeLine ("Error in ppOpInfoSig: no definition for op " ^ printQualifiedId qid) in
      None

 op ppOpInfoToH (status : CGenStatus, qid : QualifiedId, opt_info : Option OpInfo) 
  : Option (Prettys * CGenStatus) =
  case addNewOp (qid, status) of
    | Some (c_function_name, status) ->
      ppOpInfoSig (status, qid, c_function_name, opt_info)
    | _ ->
      None

 op ppInfoToH (status : CGenStatus, info : CInfo) : Option (Prettys * CGenStatus) =
  let opt_prettys_and_status =
      case info of
        | Type (qid, opt_info) -> ppTypeInfoToH (status, qid, opt_info)
        | Op   (qid, opt_info) -> ppOpInfoToH   (status, qid, opt_info)
  in
  case opt_prettys_and_status of
    | Some (prettys, status) -> Some (prettys ++ [string ";"], status)
    | _ -> None

 op ppInfosToH (status : CGenStatus, basename : FileName, infos : CInfos) 
  : Option (Prettys * CGenStatus) =
  let opt_prettys_and_status =
      foldl (fn (opt_prettys_and_status, info) -> 
               case opt_prettys_and_status of
                 | Some (prettys, status) ->
                   (case ppInfoToH (status, info) of
                      | Some (new_prettys, status) ->
                        Some (prettys  ++ [blockFill (0, map (fn pretty : Pretty -> (0, pretty)) new_prettys)],
                              status)
                      | _ ->
                        None)
                 | _ ->
                   None)
            (Some ([], status))
            infos
  in
  case opt_prettys_and_status of
    | Some( prettys, status) ->
      let header_pretty = string ("/* " ^ basename ^ ".h by " ^ userName() ^ " at " ^ currentTimeAndDate() ^ " */") in
      Some ([header_pretty] ++ prettys, status)
    | _ ->
      None

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op ppTypeInfoToC (status : CGenStatus, qid : QualifiedId, opt_info : Option TypeInfo)
  : Option (Prettys * CGenStatus) =
  Some ([], status)

 op ppOpInfoToC (status : CGenStatus, qid : QualifiedId, opt_info : Option OpInfo) 
  : Option (Prettys * CGenStatus) =
  case (opt_info, getCFunctionName qid status) of
    | (Some info, Some c_function_name) -> 
      (case ppOpInfoSig (status, qid, c_function_name, opt_info) of
         | Some (decl_prettys, status) ->
           let decl_lines   = map (fn pretty : Pretty -> (0, pretty)) decl_prettys in
           let 
             def bodyOf tm =
               case tm of
                 | Lambda ([(_,_,body)], _) -> body
                 | TypedTerm (t1, _, _) -> bodyOf t1
                 | _ -> fail("ppOpInfoToC: definition of " ^ printQualifiedId qid ^ " is not a lambda term" 
                               ^ printTerm tm)
           in
           (case printTermAsC (status, bodyOf info.dfn) of
              | Some pretty_body ->
                Some ([blockAll (0,
                                 [(0, blockFill (0, decl_lines ++ [(0, string " {")])),
                                  (0, blockFill (0, [(0, string "  return "),
                                                     (0, pretty_body),
                                                     (0, string ";")])),
                                  (0, blockFill (0, [(0, string "}")]))])],
                      status)
              | _ ->
                None)
         | _ ->
           None)
    | _ -> 
      let _ = writeLine ("Error in ppOpInfoToC: No definition for " ^ printQualifiedId qid) in
      None

 op ppInfoToC (status : CGenStatus, info : CInfo) : Option (Prettys * CGenStatus) =
  case info of
    | Type (qid, opt_info) -> ppTypeInfoToC (status, qid, opt_info)
    | Op   (qid, opt_info) -> ppOpInfoToC   (status, qid, opt_info)

 op ppInfosToC (status : CGenStatus, basename : FileName, infos : CInfos) 
  : Option (Prettys * CGenStatus) =
  let opt_prettys_and_status =
      foldl (fn (opt_prettys_and_status, info) -> 
               case opt_prettys_and_status of
                 | Some (prettys, status) ->
                   (case ppInfoToC (status, info) of
                      | Some (new_prettys, status) ->
                        (case new_prettys of
                           | [] -> opt_prettys_and_status
                           | _ -> Some (prettys ++ [blockFill (0, map (fn pretty : Pretty -> (0, pretty)) 
                                                                 new_prettys)],
                                        status))
                      | _ ->
                        None)
                 | _ ->
                   None)
            (Some ([], status))
            infos
  in
  case opt_prettys_and_status of
    | Some (prettys, status) -> 
      let header_pretty  = string ("/* " ^ basename ^ ".c by " ^ userName() ^ " at " ^ currentTimeAndDate() ^ " */") in
      let include_pretty = string ("#include \"" ^ basename ^ ".h\"") in
      Some ([header_pretty, include_pretty, string ""] ++ prettys,
            status)
    | _ ->
      None

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op printSpecAsCToFile (filename : FileName, spc : Spec) : () = 

  let basename =
      case reverse (explode filename) of
        | #c :: #. :: tail -> implode (reverse tail)
        | _ -> filename
  in
  let h_file = "C/" ^ basename ^ ".h" in
  let c_file = "C/" ^ basename ^ ".c" in

  case init_cgen_status spc of  % options and status
    | Some status ->
      let elements = findCSliceFrom spc in
      let elements = topSortElements (spc, elements) in

      let infos = reverse (foldl (fn (infos, element) ->
                                    case element of
                                      | Type    (qid,    _) -> [Type (qid, findTheType (spc, qid))] ++ infos
                                      | TypeDef (qid,    _) -> [Type (qid, findTheType (spc, qid))] ++ infos
                                      | Op      (qid, _, _) -> [Op   (qid, findTheOp   (spc, qid))] ++ infos
                                      | OpDef   (qid, _, _) -> [Op   (qid, findTheOp   (spc, qid))] ++ infos
                                      | _ -> infos)
                                 []
                                 elements)
      in
      (case ppInfosToH (status, basename, infos) of
         | Some (h_prettys, status) ->
           (case ppInfosToC (status, basename, infos) of
              | Some (c_prettys, status) ->
                let h_lines   = map (fn (pretty : Pretty) -> (0, pretty)) h_prettys in
                let c_lines   = map (fn (pretty : Pretty) -> (0, pretty)) c_prettys in
                let h_text    = format (80, blockAll (0, h_lines)) in
                let c_text    = format (80, blockAll (0, c_lines)) in
                let _ = writeLine("Writing " ^ h_file) in
                let _ = toFile (h_file, h_text) in
                let _ = writeLine("Writing " ^ c_file) in
                let _ = toFile (c_file, c_text) in
                ()
              | _ ->
                let _ = writeLine("Due to errors above, not printing .c (or .h) file : " ^ c_file) in
                ())
         | _ ->
           let _ = writeLine("Due to errors above, not printing .c (or .h) file : " ^ c_file) in
           ())
     | _ ->
      let _ = writeLine("Due to errors above, not printing .c (or .h) file : " ^ c_file) in
      ()

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

endspec
