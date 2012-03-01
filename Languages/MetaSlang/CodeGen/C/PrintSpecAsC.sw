PrintTermAsC qualifying spec 
 import /Languages/SpecCalculus/AbstractSyntax/SCTerm  % SCTerm
 import /Languages/MetaSlang/AbstractSyntax/Printer
 import /Languages/MetaSlang/Specs/MSTerm
 import /Languages/MetaSlang/Specs/AnnSpec
 import /Languages/SpecCalculus/Semantics/Environment
 import PrintTypeAsC
 import PrintTermAsC
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements % topSortElements

 %% type NatStrings = List (Nat * String)     % List (Length * String)
 %% type Text  = List (Nat * NatStrings)      % List (Indent * NatStrings)
 %% type Pretty = Nat * (Nat * Text -> Text)
 %% type Line  = Nat * Pretty
 %% type Lines = List (Line)
 %% type Prettys = List (Pretty)

 type FileName = String
 type Indent   = Nat

 type Info = 
   | Type QualifiedId * Option TypeInfo
   | Op   QualifiedId * Option OpInfo

 type Infos = List Info

 op refersToCTarget? (term : SCTerm) : Bool =
  case term.1 of
    | UnitId (SpecPath_Relative {hashSuffix = _, path = ["Library", "CGen", "CTarget"]}) -> true
    | _ -> false

 op refersToBase? (term : SCTerm) : Bool =
  case term.1 of
    | UnitId (SpecPath_Relative {hashSuffix = _, path = ["Library", "Base"]}) -> true
    | _ -> false

 op importsCTarget? (spc : Spec) : Bool =
  let 
    def aux elements =
      case elements of 
        | (Import (term, spc, _, _)) :: tail ->
          (refersToCTarget? term) || (aux tail)
        | _ -> false
  in
  aux spc.elements

 op findCSliceFrom (spc : Spec) : SpecElements =
  let
    def aux all_elements current_elements =
      foldl (fn (all_elements, element) ->
               case element of
                 | Type    _ -> all_elements ++ [element]
                 | TypeDef _ -> all_elements ++ [element]
                 | Op      _ -> all_elements ++ [element]
                 | OpDef   _ -> all_elements ++ [element]
                 | Import (term, spc, imported_elements, _) -> 
                   %% TODO: the choice of specs whose elements should be included needs some thought
                   if refersToCTarget? term || refersToBase? term then
                     %% ignore CTarget and base specs
                     all_elements
                   else if importsCTarget? spc then
                     %% include specs that (recursively) import CTarget 
                     aux all_elements imported_elements
                   else
                     %% ignore specs that don't import CTarget 
                     all_elements
                 | _ -> all_elements)
            all_elements            
            current_elements
  in
  aux [] spc.elements 

 op printSpecAsCToFile (filename : FileName, spc : Spec) : () = 

  let basename =
      case reverse (explode filename) of
        | #c :: #. :: tail -> implode (reverse tail)
        | _ -> filename
  in
  let h_file = basename ^ ".h" in
  let c_file = basename ^ ".c" in

  let elements = findCSliceFrom spc in
  let elements = topSortElements (spc, elements) in

  let cgen_options = init_cgen_options spc in

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
  case (ppInfosToH cgen_options basename infos, 
        ppInfosToC cgen_options basename infos) 
    of
    | (Some h_prettys, Some c_prettys) ->
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
      ()

 op ppInfosToH (cgen_options : CGenOptions) (basename : FileName) (infos : Infos) : Option Prettys =
  let opt_prettys =
      foldl (fn (all_prettys, info) -> 
               case (all_prettys, ppInfoToH cgen_options info) of
                 | (Some all_prettys, Some new_prettys) ->
                   Some (all_prettys  ++ [blockFill (0, map (fn pretty : Pretty -> (0, pretty)) new_prettys)])
                 | _ ->
                   None)
            (Some [])
            infos
  in
  case opt_prettys of
    | Some prettys ->
      let header_pretty = string ("/* " ^ basename ^ ".h by " ^ userName() ^ " at " ^ currentTimeAndDate() ^ " */") in
      Some ([header_pretty] ++ prettys)
    | _ ->
      None

 op ppInfosToC (cgen_options : CGenOptions) (basename : FileName) (infos : Infos) : Option Prettys =
  let opt_prettys =
      foldl (fn (opt_all_prettys, info) -> 
               case (opt_all_prettys, ppInfoToC cgen_options info) of
                 | (Some all_prettys, Some new_prettys) ->
                   (case new_prettys of
                      | [] -> opt_all_prettys
                      | _ -> Some (all_prettys ++ [blockFill (0, map (fn pretty : Pretty -> (0, pretty)) new_prettys)]))
                 | _ ->
                   None)
            (Some [])
            infos
  in
  case opt_prettys of
    | Some prettys -> 
      let header_pretty  = string ("/* " ^ basename ^ ".c by " ^ userName() ^ " at " ^ currentTimeAndDate() ^ " */") in
      let include_pretty = string ("#include \"" ^ basename ^ ".h\"") in
      Some ([header_pretty, include_pretty, string ""] ++ prettys)
    | _ ->
      None

 op ppInfoToH (cgen_options : CGenOptions) (info : Info) : Option Prettys =
  let opt_prettys =
      case info of
        | Type (qid, opt_info) -> ppTypeInfoToH cgen_options (qid, opt_info)
        | Op   (qid, opt_info) -> ppOpInfoToH   cgen_options (qid, opt_info)
  in
  case opt_prettys of
    | Some prettys -> Some (prettys ++ [string ";"])
    | _ -> None

 op ppInfoToC (cgen_options : CGenOptions) (info : Info) : Option Prettys =
  case info of
    | Type (qid, opt_info) -> ppTypeInfoToC cgen_options (qid, opt_info)
    | Op   (qid, opt_info) -> ppOpInfoToC   cgen_options (qid, opt_info)

 op ppTypeInfoToH (cgen_options : CGenOptions) (qid as Qualified (q,id) : QualifiedId, opt_info : Option TypeInfo) 
  : Option Prettys =
  case opt_info of
    | Some info -> 
      (case printTypeAsC_split cgen_options info.dfn of
         | Some (pretty_base_type, index_lines) ->
           if legal_C_Id? id then
             Some [string (case info.dfn of
                             | Product _ -> "typedef struct "
                             | _         -> "typedef "),
                   pretty_base_type,
                   string " ",
                   string (if q in? [UnQualified, "C"] then id else id), %% q ^ "_" ^ id
                   blockNone (0, index_lines)]
           else
             let _ = writeLine ("Error in ppTypeInfoToH: illegal name for type: " ^ show qid) in
             None
         | _ ->
           None)
    | _ -> 
      let _ = writeLine ("Error in ppTypeInfoToH: no definition for type " ^ show qid) in
      None

 op ppTypeInfoToC (cgen_options : CGenOptions) (qid : QualifiedId, opt_info : Option TypeInfo) : Option Prettys =
  Some []

 op ppOpInfoToH (cgen_options : CGenOptions) (qid as Qualified (q,op_id) : QualifiedId, opt_info : Option OpInfo) 
  : Option Prettys =
  if legal_C_Id? op_id then
    case opt_info of
      | Some info -> 
        (case termType info.dfn of
           | Arrow (dom, rng, _) -> 
             (case printTypeAsC cgen_options rng of
                | Some pretty_rng ->
                  let opt_pat = case info.dfn of
                                  | Lambda ([(pat,_,_)], _) -> Some pat
                                  | TypedTerm (Lambda ([(pat,_,_)], _), _, _) -> Some pat
                                  | _ -> 
                                    let _ = writeLine ("Error in ppOpInfoToH: definition not a lambda: " ^ printTerm info.dfn) in
                                    None
                  in
                  let opt_args = case opt_pat of
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
                                                       let _ = writeLine ("Error in ppOpInfoToH: arg not a var: " ^ printPattern pat) in
                                                       None)
                                                (Some [])
                                                id_pats
                                        | _ ->
                                          let _ = writeLine ("Error in ppOpInfoToH: args not a tuple: " ^ printPattern pat) in
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
                                       (case printTypeAsC cgen_options typ of
                                          | Some pretty ->
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
                      Some [pretty_rng,
                            string " ",
                            string op_id,
                            string " ",
                            pretty_args]
                    | _ ->
                      None)
           | _ ->
             let _ = writeLine ("Error in ppOpInfoToH: " ^ printQualifiedId qid ^ " does not have an arrow type") in
             None)
      | _ ->
        let _ = writeLine ("Error in ppOpInfoToH: no definition for op " ^ printQualifiedId qid) in
        None
  else
    let _ = writeLine ("Error in ppOpInfoToH: name of op is illegal for C: " ^ op_id) in
    None

 op ppOpInfoToC (cgen_options : CGenOptions) (qid : QualifiedId, opt_info : Option OpInfo) : Option Prettys =
  case opt_info of
    | Some info -> 
      (case ppOpInfoToH cgen_options (qid, opt_info) of
         | Some decl_prettys ->
           let decl_lines   = map (fn pretty : Pretty -> (0, pretty)) decl_prettys in
           let 
             def bodyOf tm =
               case tm of
                 | Lambda ([(_,_,body)], _) -> body
                 | TypedTerm (t1, _, _) -> bodyOf t1
                 | _ -> fail("ppOpInfoToC: definition of " ^ printQualifiedId qid ^ " is not a lambda term" ^ printTerm tm)
           in
           (case printTermAsC cgen_options (bodyOf info.dfn) of
              | Some pretty_body ->
                Some ([blockAll (0,
                                 [(0, blockFill (0, decl_lines ++ [(0, string " {")])),
                                  (0, blockFill (0, [(0, string "  return "),
                                                     (0, pretty_body),
                                                     (0, string ";")])),
                                  (0, blockFill (0, [(0, string "}")]))])])
              | _ ->
                None)
         | _ ->
           None)
    | _ -> 
      let _ = writeLine ("Error in ppOpInfoToC: No definition for " ^ printQualifiedId qid) in
      None

endspec
