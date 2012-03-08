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

 op getPattern (status : CGenStatus, qid : QualifiedId, tm : MSTerm) : Option MSPattern * CGenStatus =
  let
    def aux tm1 =
      case tm1 of
        | Lambda ([(pat,_,_)], _) -> (Some pat, status)
        | TypedTerm (tm2, _,   _) -> aux tm2
        | _ -> 
          (None,
           reportError ("definition for " ^ show qid ^ " is not a lambda: " ^ printTerm tm, 
                        status))
  in
  aux tm


 op getVars (status : CGenStatus, opt_pat : Option MSPattern) : Option Vars * CGenStatus =
  case opt_pat of
    | Some pat -> 
      (case pat of
         | VarPat ((id, typ), _) -> 
           if legal_C_Id? id then
             (Some [(id, typ)], status)
           else
             (None, reportError ("illegal C variable name: " ^ id, status))
         | RecordPat ([],        _) -> (Some [], status)
         | RecordPat (id_pats,   _) -> 
           (case id_pats of
              | ("1", _) :: _ ->
                foldl (fn ((opt_x, status), (_, pat)) ->
                         case pat of
                           | VarPat ((id, typ), _) ->
                             (case opt_x of
                                | Some pairs -> (Some (pairs ++ [(id, typ)]), status)
                                | _ -> (None, status))
                           | _ ->
                             (None,
                              reportError ("parameter is not a variable: " ^ printPattern pat, status)))
                      (Some [], status)
                      id_pats
              | _ ->
                (None, reportError ("parameters are not a tuple: " ^ printPattern pat, status)))
         | _ -> (None, reportError ("unrecognized parameter pattern: " ^ printPattern pat, status)))
    | _ -> (None, status)

 op ppOpInfoSig (status          : CGenStatus, 
                 qid             : QualifiedId, 
                 c_function_name : Id, 
                 opt_info        : Option OpInfo,
                 to_h_file?      : Bool)
  : CGenStatus =
  case opt_info of
    | Some info -> 
      (case termType info.dfn of
         | Arrow (dom, rng, _) -> 
           let (pretty_rng, status) = printTypeAsC (status, rng)           in
           let (opt_pat,    status) = getPattern   (status, qid, info.dfn) in
           let (opt_vars,   status) = getVars      (status, opt_pat)       in
           let opt_blocks = 
               case opt_vars of
                  | Some vars ->
                    foldl (fn (opt_blocks, (id, typ)) -> 
                             case opt_blocks of
                               | Some blocks ->
                                 let (pretty, status) = printTypeAsC (status, typ) in
                                 Some (blocks ++ [blockNone (0, [(0, pretty),
                                                                 (0, string " "),
                                                                 (0, string id)])])
                               | _ ->
                                 None)
                    (Some [])
                    vars
           in
           (case opt_blocks of
             | Some blocks ->
               let pretty_args =
                   AnnTermPrinter.ppList (fn block -> block)
                                         (string "(", string ", ", string ")")
                                         blocks
               in
               addPretty (status,
                          blockNone (0, [(0, pretty_rng), 
                                         (0, string " "), 
                                         (0, string c_function_name), 
                                         (0, string " "), 
                                         (0, pretty_args)]
                                        ++
                                        (if to_h_file? then [(0, string ";")] else [])),
                          to_h_file?)
             | _ ->
               status)
         | _ ->
           reportError (printQualifiedId qid ^ " does not have an arrow type", status))
    | _ ->
      reportError ("no definition at all for " ^ printQualifiedId qid, status)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op ppTypeInfoToH (status: CGenStatus, qid : QualifiedId, opt_info : Option TypeInfo) : CGenStatus =
  case opt_info of
    | Some info -> 
      let (pretty_base_type, index_lines, status) = getPartsForCType (status, info.dfn) in
      let (c_type_name,                   status) = addNewType       (status, qid)      in
      let p : Pretty =
                blockFill (0, 
                             [(0, string (case info.dfn of
                                        | Product _ -> "typedef struct "
                                        | _         -> "typedef ")),
                              (0, pretty_base_type),
                              (0, string " "),
                              (0, string c_type_name),
                              (0, blockNone (0, index_lines)),
                              (0, string ";")])
      in
      addHPretty (status, p)
    | _ ->
      reportError ("no definition for type " ^ show qid, status)

 op ppOpInfoToH (status : CGenStatus, qid : QualifiedId, opt_info : Option OpInfo) : CGenStatus =
  let (c_function_name, status) = addNewOp (status, qid) in
  ppOpInfoSig (status, qid, c_function_name, opt_info, true)
  
 op ppInfoToH (status : CGenStatus, info : CInfo) : CGenStatus =
  case info of
    | Type (qid, opt_info) -> ppTypeInfoToH (status, qid, opt_info)
    | Op   (qid, opt_info) -> ppOpInfoToH   (status, qid, opt_info)

 op ppInfosToH (status : CGenStatus, basename : FileName, infos : CInfos) : CGenStatus =
  let hdr = "/* " ^ basename ^ ".h by " ^ userName() ^ " at " ^ currentTimeAndDate() ^ " */" in
  let status = addHPretty (status, string hdr) in
  foldl ppInfoToH status infos

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op ppTypeInfoToC (status : CGenStatus, qid : QualifiedId, opt_info : Option TypeInfo) 
  : CGenStatus =
  status

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op ppOpInfoToC (status : CGenStatus, qid : QualifiedId, opt_info : Option OpInfo) 
  : CGenStatus =
  case opt_info of
    | Some info ->
      (case getCFunctionName (qid, status) of
        | Some c_function_name ->
          let status = addCPretty  (status, string "") in
          let status = ppOpInfoSig (status, qid, c_function_name, opt_info, false) in
          let 
            def bodyOf tm =
              case tm of
                | Lambda ([(_,_,body)], _) -> body
                | TypedTerm (t1, _, _) -> bodyOf t1
                | _ -> fail("ppOpInfoToC: definition of " ^ printQualifiedId qid ^ " is not a lambda term" 
                              ^ printTerm tm)
          in
          let (pretty_body, has_return?, status) = printTermAsC (status, bodyOf info.dfn, Statement) in
          let pretty_body = if has_return? then pretty_body else wrapReturn pretty_body in
          let pretty_body = blockLinear (0, [(0, string " {"), (2, pretty_body), (1, string "}")]) in
          addCPretty (status, pretty_body)
        | _ -> 
          reportError ("?? No declaration for " ^ printQualifiedId qid, status))
    | _ -> 
      reportWarning ("No definition for " ^ printQualifiedId qid, status)

 op ppInfoToC (status : CGenStatus, info : CInfo) : CGenStatus =
  case info of
    | Type (qid, opt_info) -> ppTypeInfoToC (status, qid, opt_info)
    | Op   (qid, opt_info) -> ppOpInfoToC   (status, qid, opt_info)

 op ppInfosToC (status : CGenStatus, basename : FileName, infos : CInfos) : CGenStatus =
  let hdr_msg     = "/* " ^ basename ^ ".c by " ^ userName() ^ " at " ^ currentTimeAndDate() ^ " */" in
  let include_msg = "#include \"" ^ basename ^ ".h\"" in
  let status = addCPretty (status, string hdr_msg) in
  let status = addCPretty (status, string include_msg) in
  foldl ppInfoToC status infos

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
      let status = ppInfosToH (status, basename, infos) in
      let status = ppInfosToC (status, basename, infos) in
      (case status.error_msgs of
         | [] ->
           let _ = app (fn msg -> writeLine ("CGen warning: " ^ msg)) status.warning_msgs in
           let h_lines = map (fn (pretty : Pretty) -> (0, pretty)) status.h_prettys in
           let c_lines = map (fn (pretty : Pretty) -> (0, pretty)) status.c_prettys in
           let h_lines = h_lines ++ [(0, string "")] in
           let c_lines = c_lines ++ [(0, string "")] in
           let h_text  = format (80, blockAll (0, h_lines)) in
           let c_text  = format (80, blockAll (0, c_lines)) in
           let _ = writeLine("Writing " ^ h_file) in
           let _ = toFile (h_file, h_text) in
           let _ = writeLine("Writing " ^ c_file) in
           let _ = toFile (c_file, c_text) in
           ()
         | msgs ->
           let _ = app (fn msg -> writeLine ("CGen error: " ^ msg)) status.error_msgs in
           let _ = app (fn msg -> writeLine ("CGen warning: " ^ msg)) status.warning_msgs in
           let _ = writeLine("Due to errors above, not printing .c (or .h) file : " ^ c_file) in
           ())
    | _ ->
      let _ = writeLine("Due to errors above, not printing .c (or .h) file : " ^ c_file) in
      ()

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

endspec
