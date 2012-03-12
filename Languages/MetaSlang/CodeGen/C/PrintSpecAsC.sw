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
         | _ -> 
           (None, reportError ("unrecognized parameter pattern: " ^ printPattern pat, status)))
    | _ -> 
      (None, status)

 op ppOpInfoSig (status : CGenStatus, qid : QualifiedId, c_name : Id, info : OpInfo)
  : Bool * Lines * CGenStatus =
  let
    def defined? tm =
      case tm of
        | TypedTerm (t1, _,        _) -> defined? t1
        | Pi        (_, t1,        _) -> defined? t1 
        | And       (t1 :: _,      _) -> defined? t1
        | Lambda    ([(_,_,body)], _) -> defined? body
        | Any       _                 -> false
        | _ -> true
  in
  let (function?, lines, status) =
      case termType info.dfn of
        | Arrow (dom, rng, _) -> 
          let (pretty_rng, status) = printTypeAsC (status, rng)           in
          let (opt_pat,    status) = getPattern   (status, qid, info.dfn) in
          let (opt_vars,   status) = getVars      (status, opt_pat)       in
          let (arg_lines, _, status) = 
              case opt_vars of
                | Some vars ->
                  foldl (fn ((lines, first?, status), (id, typ)) -> 
                           let (pretty_type, status) = printTypeAsC (status, typ) in
                           let pretty_parameter =
                           blockNone (0,
                                      if first? then
                                        [(0, pretty_type), L0_space, (0, string id)]
                                      else
                                        [L0_comma_space, (0, pretty_type), L0_space, (0, string id)])
                           in
                           (lines ++ [(0, pretty_parameter)], false, status))
                        ([], true, status)
                        vars
                | _ -> 
                  ([], true, status)
          in
          let pretty_args =
              case arg_lines of
                | [] -> string "(void)"
                | _ -> blockNone (0, [L0_lparen, (0, blockLinear (0, arg_lines)), L0_rparen])
          in
          (true, 
           [(0, pretty_rng), L0_space, (0, string c_name), L0_space, (0, pretty_args)],
           status)
        | typ ->
          let (pretty_type, status) = printTypeAsC (status, typ) in
          (false, [(0, pretty_type), L0_space, (0, string c_name)], status)
  in
  (function?,
   if defined? info.dfn then lines else [(0, string "extern ")] ++ lines,
   status)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op ppTypeInfoToH (status: CGenStatus, qid : QualifiedId, info : TypeInfo) : CGenStatus =
  let (pretty_base_type, index_lines, status) = getPartsForCType (status, info.dfn) in
  let (c_type_name,                   status) = addNewType       (status, qid)      in
  let lines = 
      [(0, string (case info.dfn of
                     | Product _ -> "typedef struct "
                     | _         -> "typedef ")),
       (0, pretty_base_type),
       L0_space,
       (0, string c_type_name),
       (0, blockNone (0, index_lines)),
       L0_semicolon]
  in
  ppToH (status, blockFill (0, lines))

 op ppOpInfoToH (status : CGenStatus, qid : QualifiedId, info : OpInfo) : CGenStatus =
  let (c_name, status) = addNewOp (status, qid) in
  %% C prototype
  let (_, lines, status) = ppOpInfoSig (status, qid, c_name, info) in
  let pretty = blockNone (0, lines ++ [L0_semicolon]) in
  ppToH (status, pretty)   % prototype
  
 op ppInfoToH (status : CGenStatus, info : CInfo) : CGenStatus =
  case info of
    | Type (qid, info) -> ppTypeInfoToH (status, qid, info)
    | Op   (qid, info) -> ppOpInfoToH   (status, qid, info)

 op ppInfosToH (status : CGenStatus, basename : FileName, infos : CInfos) : CGenStatus =
  let hdr = "/* " ^ basename ^ ".h by " ^ userName() ^ " at " ^ currentTimeAndDate() ^ " */" in
  let status = ppToH (status, string hdr) in
  let status = ppToH (status, string "") in
  foldl ppInfoToH status infos

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op ppTypeInfoToC (status : CGenStatus, qid : QualifiedId, info : TypeInfo) 
  : CGenStatus =
  status

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op ppOpInfoToC (status : CGenStatus, qid : QualifiedId, info : OpInfo) 
  : CGenStatus =
  let 
    def inner tm =
      case tm of
        %% strip away type information
        | TypedTerm (t1, _,        _) -> inner t1
        | Pi        (_, t1,        _) -> inner t1 
        | And       (t1 :: _,      _) -> inner t1
        | Any       _                 -> None
        | _ -> Some tm  % TODO: could this be a lambda not typed as a function?

    def lambdaBodyOf tm =
      case tm of
        %% strip away type information, and proceed to body of lambda
        | Lambda    ([(_,_,body)], _) -> Some body
        | TypedTerm (t1, _,        _) -> lambdaBodyOf t1
        | Pi        (_, t1,        _) -> lambdaBodyOf t1 
        | And       (t1 :: _,      _) -> lambdaBodyOf t1
        | _ -> None
  in
  case getCOpName (qid, status) of
    | Some c_name ->
      let status = ppToC (status, string "") in
      let (typed_as_function?, sig_lines, status) = ppOpInfoSig (status, qid, c_name, info) in
      let sig_pretty = blockNone (0, sig_lines) in
      if typed_as_function? then
        case lambdaBodyOf info.dfn of
          | Some body ->
            (case inner body of
               | Some body ->
                 let (pretty_body, inner_level, status) = printTermAsC (status, body, CPrecedence_NO_PARENS, Statement) in
                 let pretty_body = if inner_level = Expression then wrapReturn pretty_body else pretty_body in
                 let lines = [(0, sig_pretty), (0, string " { "), (2, pretty_body), (1, string "}")] in
                 ppToC (status, blockLinear (0, lines))
               | _ ->
                 status)
          | _->
            reportConfusion ("Non-lambda definition for function?: " ^ show qid, status)
      else 
        (case inner info.dfn of
           | Some tm ->
             let (pretty_value, _, status) = printTermAsC (status, tm, CPrecedence_NO_PARENS, Statement) in
             let lines = [(0, sig_pretty), L0_space_equal_space, (0, pretty_value), L0_semicolon] in
             ppToC (status, blockNone (0, lines))
           | _ ->
             status)
    | _ -> 
      %% this should not be possible
      reportConfusion ("No prototype for " ^ printQualifiedId qid, status)

 op ppInfoToC (status : CGenStatus, info : CInfo) : CGenStatus =
  case info of
    | Type (qid, info) -> ppTypeInfoToC (status, qid, info)
    | Op   (qid, info) -> ppOpInfoToC   (status, qid, info)

 op ppInfosToC (status : CGenStatus, basename : FileName, infos : CInfos) : CGenStatus =
  let hdr_msg     = "/* " ^ basename ^ ".c by " ^ userName() ^ " at " ^ currentTimeAndDate() ^ " */" in
  let include_msg = "#include \"" ^ basename ^ ".h\"" in
  let status = ppToC (status, string hdr_msg) in
  let status = ppToC (status, string include_msg) in
  foldl ppInfoToC status infos

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op collectCInfos (status : CGenStatus, spc : Spec) : CInfos * CGenStatus =
  %% TODO: what about Type followed by TypeDef ?                
  %% TODO: what about Op followed by opDef ?                
  %% TODO: what about multiple opDefs (refinements) ?                
  let elements = findCSliceFrom spc in
  let elements = topSortElements (spc, elements) in
  foldl (fn ((infos, status), element) ->
           case element of
             | Type    (qid,    _) -> 
               (case findTheType (spc, qid) of
                  | Some info ->
                    (infos ++ [Type (qid, info)], status)
                  | _ ->
                    %% Something is messed up with spec...
                    (infos, reportConfusion ("No type info for " ^ show qid, status)))
             | TypeDef (qid,    _) -> 
               (case findTheType (spc, qid) of
                  | Some info ->
                    (infos ++ [Type (qid, info)], status)
                  | _ ->
                    %% Something is messed up with spec...
                    (infos, reportConfusion ("No type info for " ^ show qid, status)))
             | Op      (qid, _, _) -> 
               (case findTheOp (spc, qid) of
                  | Some info ->
                    (infos ++ [Op (qid, info)], status)
                  | _ ->
                    %% Something is messed up with spec...
                    (infos, reportConfusion ("No op info for " ^ show qid, status)))
             | OpDef   (qid, _, _) -> 
               (case findTheOp (spc, qid) of
                  | Some info ->
                    (infos ++ [Op (qid, info)], status)
                  | _ ->
                    %% Something is messed up with spec...
                    (infos, reportConfusion ("No op info for " ^ show qid, status)))
             | _ -> (infos, status))
        ([], status)
        elements
  
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
      let (cinfos, status) = collectCInfos (status, spc) in
      %% TODO: Is this the right decision?
      %% Do all of the H prototypes first, to make all of them available when printing terms for the C file.
      %% (As opposed to printing the H and C forms in parallel for each info.)
      let status = ppInfosToH (status, basename, cinfos) in  
      let status = ppInfosToC (status, basename, cinfos) in
      (case status.error_msgs of
         | [] ->
           let _ = app (fn msg -> writeLine ("CGen warning: " ^ msg)) status.warning_msgs in
           let h_lines = map (fn (pretty : Pretty) -> (0, pretty)) status.h_prettys in
           let c_lines = map (fn (pretty : Pretty) -> (0, pretty)) status.c_prettys in
           let h_lines = h_lines ++ [L0_null] in
           let c_lines = c_lines ++ [L0_null] in
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
