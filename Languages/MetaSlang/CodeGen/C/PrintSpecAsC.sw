CPrinter qualifying spec 
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
    | UnitId (SpecPath_Relative {hashSuffix = None, path = ["Library", "C", "CTarget"]}) -> 
      let _ = writeLine("spec refers to CTarget") in
      true
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
  let root_elements = spc.elements in
  root_elements

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
  let h_prettys = ppInfosToH infos in
  let c_prettys = [blockAll (0, [(0, string ("#import \"" ^ h_file ^ "\";")), (0, string "")])]
                  ++
                  ppInfosToC infos 
  in
  let h_lines   = map (fn (pretty : Pretty) -> (0, pretty)) h_prettys in
  let c_lines   = map (fn (pretty : Pretty) -> (0, pretty)) c_prettys in
  let h_text    = format (80, blockAll (0, h_lines)) in
  let c_text    = format (80, blockAll (0, c_lines)) in
  let _ = toFile (h_file, h_text) in
  let _ = toFile (c_file, c_text) in
  ()

 op ppInfosToH (infos : Infos) : Prettys =
  foldl (fn (all_prettys, info) -> 
           case ppInfoToH info of
             | [] -> all_prettys
             | prettys -> all_prettys ++ [blockFill (0, map (fn pretty : Pretty -> (0, pretty)) prettys)])
        []
        infos

 op ppInfosToC (infos : Infos) : Prettys =
  foldl (fn (all_prettys, info) -> 
           case ppInfoToC info of
             | [] -> all_prettys
             | prettys -> all_prettys ++ [blockFill (0, map (fn pretty : Pretty -> (0, pretty)) prettys)])
        []
        infos

 op ppInfoToH (info : Info) : Prettys =
  (case info of
     | Type (qid, opt_info) -> ppTypeInfoToH (qid, opt_info)
     | Op   (qid, opt_info) -> ppOpInfoToH   (qid, opt_info))
  ++ 
  [string ";"] 

 op ppInfoToC (info : Info) : Prettys =
  case info of
    | Type (qid, opt_info) -> ppTypeInfoToC (qid, opt_info)
    | Op   (qid, opt_info) -> ppOpInfoToC   (qid, opt_info)

 op ppTypeInfoToH (qid as Qualified (q,id) : QualifiedId, opt_info : Option TypeInfo) : Prettys =
   case opt_info of
     | Some info -> 
       let pretty_type = printTypeAsC info.dfn in
       (case info.dfn of
          | Product _ ->
            [string "struct ",
             string id,
             string " ",
             pretty_type]
          | _ ->
            [string "typedef ",
             pretty_type,
             string " ",
             string id])
     | _ -> [string "<missing>"]

 op ppTypeInfoToC (qid : QualifiedId, opt_info : Option TypeInfo) : Prettys =
  []

 op ppOpInfoToH (qid as Qualified (q,id) : QualifiedId, opt_info : Option OpInfo) : Prettys =
  case opt_info of
    | Some info -> 
      (case termType info.dfn of
         | Arrow (dom, rng, _) -> 
           let pretty_rng = printTypeAsC rng in
           let pat = case info.dfn of
                       | Lambda ([(pat,_,_)], _) -> pat
                       | TypedTerm (Lambda ([(pat,_,_)], _), _, _) -> pat
                       | _ -> fail("op not a lambda")
           in
           let args = case pat of
                        | VarPat    ((id, typ), _) -> [(id, typ)]
                        | RecordPat ([],        _) -> []
                        | RecordPat (id_pats,   _) -> 
                          case id_pats of
                            | ("1", _) :: _ ->
                              map (fn (_, VarPat ((id, typ), _)) -> (id, typ)) id_pats
                            | _ ->
                              fail ("id_pats = " ^ anyToString id_pats)
           in
           let pretty_args =
               AnnTermPrinter.ppListPath []
                                         (fn (path, (id, typ)) -> 
                                            blockFill (0, [(0, printTypeAsC typ),
                                                           (0, string " "),
                                                           (0, string id)]))
                                         (string "(", string ", ", string ")")
                                         args
           in
           [pretty_rng,
            string " ",
            string id,
            string " ",
            pretty_args]
         | _ ->
           [string ("<" ^ printQualifiedId qid ^ " does not have an arrow type>")])
    | _ ->
      [string ("<missing definition for " ^ printQualifiedId qid ^ ">")]

 op ppOpInfoToC (qid : QualifiedId, opt_info : Option OpInfo) : Prettys =
  case opt_info of
    | Some info -> 
      let decl_prettys = ppOpInfoToH (qid, opt_info) in
      let decl_lines   = map (fn pretty : Pretty -> (0, pretty)) decl_prettys in
      [blockAll (0,
                 [(0, blockFill (0, decl_lines ++ [(0, string " {")]))]
                 ++
                 [(0, printTermAsC info.dfn)]
                 ++
                 [(0, blockFill (0, [(0, string "}")]))])]
    | _ -> 
      [string ("<missing definition for " ^ printQualifiedId qid ^ ">")]


endspec
