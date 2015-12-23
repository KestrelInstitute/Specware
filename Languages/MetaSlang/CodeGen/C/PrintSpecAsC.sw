(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

PrintAsC qualifying spec

 import PrintAsCUtils
 import PrintTypeAsC
 import PrintTermAsC
 import /Languages/MetaSlang/Transformations/OldSlice  % TOOD: deprecated
%import /Languages/MetaSlang/Transformations/SliceSpec % replace with this
 import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% Code to find slice of elements that are both at-or-below top-level spec 
 %%% and also above CTarget.sw
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% %TODO deprecate?
%  op findCSliceFrom (spc : Spec) : SpecElements =
%   let
%     def aux (all_elements, current_elements) =
%       foldl (fn (all_elements, element) ->
%                case element of
%                  | Type    _ -> all_elements ++ [element]
%                  | TypeDef _ -> all_elements ++ [element]
%                  | Op      _ -> all_elements ++ [element]
%                  | OpDef   _ -> all_elements ++ [element]
%                  | Import (term, spc, imported_elements, _) -> 
%                    %% TODO: the choice of specs whose elements should be included needs some thought
%                    if refersToCTarget? term then  
%                      all_elements                          % ignore CTarget itself
%                    else if importsCTarget? spc then
%                      aux (all_elements, imported_elements) % include specs that (recursively) import CTarget 
%                    else
%                      all_elements                          % ignore specs that don't (this includes the base specs)
%                  | _ -> all_elements)
%             all_elements            
%             current_elements
%   in
%   aux ([], spc.elements)



op filterSpecElementsaux (elements : SpecElements, p : SpecElement -> Bool, acc : SpecElements) : SpecElements =
  case elements of
    | [] -> acc
    | element::rest -> let acc = (case element of
                                    | Import (_, _, imported_elements, _) -> filterSpecElementsaux(imported_elements, p, acc)
                                    | _ -> if (p element) then element |> acc else acc)
                       in filterSpecElementsaux(rest, p, acc)
                       
%Keeps the elements which satisfy the predicate p, except that imports are handled specially (we look inside them, rather than running p on them).
op filterSpecElements (elements : SpecElements, p : SpecElement -> Bool) : SpecElements = filterSpecElementsaux (elements, p, [])

  % Get all the op names and type names in the spec that don't come in via importing
  % CTarget.  Usually this will bring in things that we can't generate C for,
  % but this works well for small examples.
  % TODO what about the base libraries?  Are they explicitly imported?
  % TODO what about things that are declared but not defined?
  % The first return value is the op names; the second is the type names.
  op nonCTargetOpsAndTypes (opnames : List QualifiedId, typenames : List QualifiedId, elements : SpecElements) : (List QualifiedId) * (List QualifiedId)  =
  case elements of
    | [] -> (opnames, typenames)
    | element::rest ->
      let (opnames, typenames) =
      (case element of
         | Type    (qid,_) -> (opnames, qid |> typenames)
         | TypeDef (qid,_) -> (opnames, qid |> typenames)
         | Op      (qid,_,_) -> (qid |> opnames, typenames)
         | OpDef   (qid,_,_,_) -> (qid |> opnames, typenames)
         | Import (term, spc, imported_elements, _) -> 
           %% TODO: the choice of specs whose elements should be processed needs some thought
           if refersToCTarget? term then  
             (opnames, typenames)                          % ignore CTarget itself
           else if importsCTarget? spc then
             nonCTargetOpsAndTypes (opnames, typenames, imported_elements) % include specs that (recursively) import CTarget 
           else
             (opnames, typenames)                          % ignore specs that don't (this includes the base specs)
         | _ -> (opnames, typenames)) in
      nonCTargetOpsAndTypes(opnames, typenames, rest)
      

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op getPattern (status : CGenStatus, qid : QualifiedId, tm : MSTerm) : Option MSPattern * CGenStatus =
  let
    def aux tm1 =
      case tm1 of
        | Lambda ([(pat,_,_)], _) -> (Some pat, status)
        | TypedTerm (tm2, _,   _) -> aux tm2
        | And (tm::rest, _) -> aux tm
        | _ -> 
          (None,
           reportError ("definition for " ^ show qid ^ " is not a lambda: " ^ printTerm tm, 
                        status))
  in
  aux tm


 op getVars (status : CGenStatus, opt_pat : Option MSPattern) : Option MSVars * CGenStatus =
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
  let hdr = "/* " ^ basename ^ ".h by " ^ userName() ^ " */" %% ^ " at " ^ currentTimeAndDate() ^ " */"  %%Removing this to prevent spurious diffs in the regression suite. -EWS
in
  let status = ppToH (status, string hdr) in
  let status = ppToH (status, string "") in
  foldl ppInfoToH status infos

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op ppTypeInfoToC (status : CGenStatus, qid : QualifiedId, info : TypeInfo) 
  : CGenStatus =
  status

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op ppLocalVarInfoToC (info: LocalVarInfo) : List (Nat * Pretty) =
  case info of
  | [] -> []
  | (varid, typeid)::tl -> 
    [(2, string (typeid ^ " " ^ varid ^ ";"))] ++ ppLocalVarInfoToC(tl)

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
                 let (pretty_body, compoundflag, status, localvarinfo) = printTermAsCStatement (status, body) in
		 %%TODO check conditions on the local vars (e.g., distinct from each other and from all params)
                 let localvarlines = ppLocalVarInfoToC localvarinfo in
                 let pretty_body = if compoundflag then wrapBraces pretty_body else pretty_body in
                 let lines = [(0, sig_pretty), (0, string " { ")] ++ localvarlines ++ [(2, pretty_body), (1, string "}")] in
                 ppToC (status, blockLinear (0, lines))
               | _ ->
                 status)
          | _->
            reportConfusion ("Non-lambda definition for function?: " ^ show qid, status)
      else 
        (case inner info.dfn of
           | Some tm ->
             let (pretty_value, status) = printTermAsCExpression (status, tm, CPrecedence_NO_PARENS) in  %%TODO consider when tm contains a Let or refers to another "constant"
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
  let hdr_msg     = "/* " ^ basename ^ ".c by " ^ userName() ^ " */"     %% ^ " at " ^ currentTimeAndDate() %%Removing this to prevent spurious diffs in the regression suite. -EWS
  in
  let include_msg = "#include \"" ^ basename ^ ".h\"" in
  let status = ppToC (status, string hdr_msg) in
  let status = ppToC (status, string include_msg) in
  foldl ppInfoToC status infos



%  % We translate all the elements in spc whose names are in the corresponding set (op_set or type_set).
%  op collectCInfos (op_set : QualifierSet,
%                    type_set : QualifierSet,
%                    status : CGenStatus, 
%                    spc : Spec
%                    ) : CInfos * CGenStatus =
%   %% TODO: what about Type followed by TypeDef ?                
%   %% TODO: what about Op followed by opDef ?                
%   %% TODO: what about multiple opDefs (refinements) ?                
% %  let elements = findCSliceFrom spc in
%   let allelements = spc.elements in
%   % let _ = writeLine(anyToString op_set) in
%   let elements_to_translate = filterSpecElements (allelements, (fn el -> case el of
%                                                                            | Type    (qid,_) -> qid in? type_set
%                                                                            | TypeDef (qid,_) -> qid in? type_set
%                                                                            | Op      (qid,_,_) -> qid in? op_set
%                                                                            | OpDef   (qid,_,_,_) -> qid in? op_set
%                                                                            | _ -> false)) in
%   %why doesn't the topological sort work?
%   %let elements_to_translate = topSortElements (spc, elements_to_translate) in  %What if there is no sorted order (because of mutual recursion)?
%   let elements_to_translate = reverse elements_to_translate in
%   let _ = writeLine("sorted elements to translate:"^flatten(intersperse(" ", map showQ elements_to_translate))) in
%   foldl (fn ((infos, status), element) ->
%            case element of
%              | Type    (qid,    _) -> 
%                (case findTheType (spc, qid) of
%                   | Some info ->
%                     (infos ++ [Type (qid, info)], status)
%                   | _ ->
%                     %% Something is messed up with spec...
%                     (infos, reportConfusion ("ERROR: No type info for " ^ show qid, status)))
%              | TypeDef (qid,    _) -> 
%                (case findTheType (spc, qid) of
%                   | Some info ->
%                     (infos ++ [Type (qid, info)], status)
%                   | _ ->
%                     %% Something is messed up with spec...
%                     (infos, reportConfusion ("ERROR: No type info for " ^ show qid, status)))
%              | Op      (qid, _, _) -> 
%                (case findTheOp (spc, qid) of
%                   | Some info ->
%                     (infos ++ [Op (qid, info)], status)
%                   | _ ->
%                     %% Something is messed up with spec...
%                     (infos, reportConfusion ("ERROR: No op info for " ^ show qid, status)))
%              | OpDef   (qid, _, _, _) -> 
%                (case findTheOp (spc, qid) of
%                   | Some info ->
%                     (infos ++ [Op (qid, info)], status)
%                   | _ ->
%                     %% Something is messed up with spec...
%                     (infos, reportConfusion ("ERROR: No op info for " ^ show qid, status)))
%              | _ -> (infos, status))
%         ([], status)
%         elements_to_translate

% Checks whether item depends on anything in items
op [a] dependsOnAny?(item : a, items : List a, dependsOn? : a * a -> Bool) : Bool =
  case items of 
    | Nil -> false
    | hd::tl -> 
      if dependsOn?(item, hd) then
        true
      else dependsOnAny?(item, tl, dependsOn?)

% Look for an items that doesn't depend on any other items (it can go first).
op [a] findNextItem (items : List a, dependsOn? : a * a -> Bool) : Option a =
 let def findNextItem_aux (items : List a, allItems : List a) =
    case items of
      | Nil -> None
      | hd::tl -> 
        if dependsOnAny?(hd, allItems, dependsOn?) then
          findNextItem_aux (tl, allItems)
        else % hd depends on nothing and so can go first
          Some hd
 in findNextItem_aux(items, items)

%TODO: Pull this out into a library somewhere?
%not very efficient!
%example call: topSort([1,3,2,4], fn (x,y) -> x > y)
op [a] topSort (items : List a, dependsOn? : a * a -> Bool) : List a =
  case items of
    | Nil -> Nil
    | _ -> 
      % find an item that does not depend directly on any item in the set.
      case findNextItem(items, dependsOn?) of
        | Some item -> Cons(item, topSort(delete item items, dependsOn?))
        | None -> let _ = writeLine "Error: No topological sort is possible (because of a cycle?)." in Nil

op [b] stripTypes (pairs : List (Id * AType b)) : List (AType b) =
  map (fn x -> x.2) pairs

op [b] stripTypesOptionVersion (pairs : List (QualifiedId * Option (AType b))) : List (AType b) =
  case pairs of
    | [] -> []
    | hd::tl ->
      case hd of 
        | (_, Some ty) -> ty::stripTypesOptionVersion(tl)
        | _ -> stripTypesOptionVersion(tl)

op anyTypeMentions? (x : List (AType StandardAnnotation), y : QualifiedId) : Bool = 
  case x of
    | Nil -> false
    | hd::tl -> typeMentions?(hd, y) || anyTypeMentions?(tl, y)

% Check whether type x mentions y
 op typeMentions? (x : AType StandardAnnotation, y : QualifiedId) : Bool = 
   case x of
     | Arrow(ty1, ty2,_) -> typeMentions?(ty1, y) || typeMentions?(ty2, y)
     | Product(pairs, _) -> anyTypeMentions?(stripTypes(pairs), y)
     | CoProduct(pairs, _) -> anyTypeMentions?(stripTypesOptionVersion(pairs), y)
     | Quotient(ty,tm, _) -> typeMentions?(ty, y) %TODO use tm?
     | Subtype(ty,tm, _) -> typeMentions?(ty, y) %TODO use tm?
     | Base(qid,tys, _) -> qid = y || anyTypeMentions?(tys, y)
     | Boolean _ -> false
     | TyVar(_, _) -> false
%     | (MetaTyVar _, _) -> false   % Before elaborateSpec
     | Pi(vars,ty, _) -> typeMentions?(ty, y)
     | And(tys, _) -> anyTypeMentions?(tys, y)
     | Any _ -> false

% The CInfos should be TypeInfos
op typeInfoDependsOnTypeInfo? (Type(qidx, infox) : CInfo, Type(qidy, infoy) : CInfo) : Bool = 
  typeMentions?(infox.dfn, qidy) %TODO what about the names field in the typeinfo?

op printSpecAsCToFile (op_set : QualifierSet,
                       type_set : QualifierSet,
                       c_file : FileName, % an absolute path
                       h_file : FileName, % an absolute path
                       basename : FileName, %the base name of the two files (no directories, no extension)
                       spc : Spec) : () = 
  case init_cgen_status spc of  % options and status
    | Some status ->
      %let (cinfos, status) = collectCInfos (op_set, type_set, status, spc) in
      let infosfortypes = foldriAQualifierMap (fn (qualifier,id,info,list:CInfos) -> if (mkQualifiedId(qualifier,id) in? type_set) then (Type(mkQualifiedId(qualifier,id),info))::list else list) [] spc.types in
      let infosforops = foldriAQualifierMap (fn (qualifier,id,info,list:CInfos) -> if (mkQualifiedId(qualifier,id) in? op_set) then (Op(mkQualifiedId(qualifier,id), info))::list else list) [] spc.ops  in
      % types must appear in sorted order in the .h file:
      let infosfortypes = topSort(infosfortypes, typeInfoDependsOnTypeInfo?) in
      let _ = writeLine("Sorted types:" ^ (showQIDs (map (fn x -> case x of | Type(qid, _) -> qid | Op(qid, _) -> qid) infosfortypes))) in
      % TODO Add a topological sort on infos?  Or should the sorting be done by the user, as a transformation?
      let cinfos = infosfortypes++infosforops in

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

type QIDorAll = 
  | QID QualifiedId
  | All

%TODO make a general purpose remove suffix routine.
% %this is a duplicate                                              
%   op  removeSWsuffix : String -> String
%   def removeSWsuffix path =
%     case (reverse (explode path)) of
%       | #w :: #s :: #. :: rest -> implode (reverse rest)
%       | _ -> path

  % Given the value (e.g., a spec wrapped in the 'Spec' constructor), get its UnitID (absolute pathname and hash suffix)
  op uidForValue (val : Value) : Option UnitId =
    case MonadicStateInternal.readGlobalVar "GlobalContext" of
      | None -> None %% means something is really messed up, so print a warning?
      | Some global_context -> findUnitIdForUnit(val, global_context)

%% TODO move these lists to CTarget.sw:
        
  op CTargetOpNames : List String = 
  ["test",
% UCHAR_MAX
% SCHAR_MIN
% SCHAR_MAX
% CHAR_MIN
% CHAR_MAX
% USHORT_MAX
%   UINT_MAX
%  ULONG_MAX
% ULLONG_MAX
% SSHORT_MIN
%   SINT_MIN
%  SLONG_MIN
% SLLONG_MIN
% SSHORT_MAX
%   SINT_MAX
%  SLONG_MAX
% SLLONG_MAX
   "sintConstant",
   "slongConstant",
   "sllongConstant",

   "uintConstant",
   "ulongConstant",
   "ullongConstant",

   "ucharOfUshort",
   "ucharOfUint",
   "ucharOfUlong",
   "ucharOfUllong",
   "ucharOfSchar",
   "ucharOfSshort",
   "ucharOfSint",
   "ucharOfSlong",
   "ucharOfSllong",
   "ucharOfChar",

   "ushortOfUchar",
   "ushortOfUint",
   "ushortOfUlong",
   "ushortOfUllong",
   "ushortOfSchar",
   "ushortOfSshort",
   "ushortOfSint",
   "ushortOfSlong",
   "ushortOfSllong",
   "ushortOfChar",

   "uintOfUchar",
   "uintOfUshort",
   "uintOfUlong",
   "uintOfUllong",
   "uintOfSchar",
   "uintOfSshort",
   "uintOfSint",
   "uintOfSlong",
   "uintOfSllong",
   "uintOfChar",

   "ulongOfUchar",
   "ulongOfUshort",
   "ulongOfUint",
   "ulongOfUllong",
   "ulongOfSchar",
   "ulongOfSshort",
   "ulongOfSint",
   "ulongOfSlong",
   "ulongOfSllong",
   "ulongOfChar",

   "ullongOfUchar",
   "ullongOfUshort",
   "ullongOfUint",
   "ullongOfUlong",
   "ullongOfSchar",
   "ullongOfSshort",
   "ullongOfSint",
   "ullongOfSlong",
   "ullongOfSllong",
   "ullongOfChar",

   "scharOfUchar",
   "scharOfUshort",
   "scharOfUint",
   "scharOfUlong",
   "scharOfUllong",
   "scharOfSshort",
   "scharOfSint",
   "scharOfSlong",
   "scharOfSllong",
   "scharOfChar",

   "sshortOfUchar",
   "sshortOfUshort",
   "sshortOfUint",
   "sshortOfUlong",
   "sshortOfUllong",
   "sshortOfSchar",
   "sshortOfSint",
   "sshortOfSlong",
   "sshortOfSllong",
   "sshortOfChar",

   "sintOfUchar",
   "sintOfUshort",
   "sintOfUint",
   "sintOfUlong",
   "sintOfUllong",
   "sintOfSchar",
   "sintOfSshort",
   "sintOfSlong",
   "sintOfSllong",
   "sintOfChar",

   "slongOfUchar",
   "slongOfUshort",
   "slongOfUint",
   "slongOfUlong",
   "slongOfUllong",
   "slongOfSchar",
   "slongOfSshort",
   "slongOfSint",
   "slongOfSllong",
   "slongOfChar",

   "sllongOfUchar",
   "sllongOfUshort",
   "sllongOfUint",
   "sllongOfUlong",
   "sllongOfUllong",
   "sllongOfSchar",
   "sllongOfSshort",
   "sllongOfSint",
   "sllongOfSlong",
   "sllongOfChar",

   "charOfUchar",
   "charOfUshort",
   "charOfUint",
   "charOfUlong",
   "charOfUllong",
   "charOfSchar",
   "charOfSshort",
   "charOfSint",
   "charOfSlong",
   "charOfSllong",

   "+_1_sint",
   "+_1_slong",
   "+_1_sllong",
   "+_1_uint",
   "+_1_ulong",
   "+_1_ullong",

   "-_1_sint",
   "-_1_slong",
   "-_1_sllong",
   "-_1_uint",
   "-_1_ulong",
   "-_1_ullong",

   "~_sint",
   "~_slong",
   "~_sllong",
   "~_uint",
   "~_ulong",
   "~_ullong",

   "!_char",
   "!_schar",
   "!_uchar",
   "!_sshort",
   "!_ushort",
   "!_sint",
   "!_uint",
   "!_slong",
   "!_ulong",
   "!_sllong",
   "!_ullong",

   "*_sint",
   "*_slong",
   "*_sllong",
   "*_uint",
   "*_ulong",
   "*_ullong",

   "/_sint",
   "/_slong",
   "/_sllong",
   "/_uint",
   "/_ulong",
   "/_ullong",

   "//_sint",
   "//_slong",
   "//_sllong",
   "//_uint",
   "//_ulong",
   "//_ullong",

   "+_sint",
   "+_slong",
   "+_sllong",
   "+_uint",
   "+_ulong",
   "+_ullong",

   "-_sint",
   "-_slong",
   "-_sllong",
   "-_uint",
   "-_ulong",
   "-_ullong",

   "<<_sint_sint",
   "<<_sint_slong",
   "<<_sint_sllong",
   "<<_sint_uint",
   "<<_sint_ulong",
   "<<_sint_ullong",
   "<<_slong_sint",
   "<<_slong_slong",
   "<<_slong_sllong",
   "<<_slong_uint",
   "<<_slong_ulong",
   "<<_slong_ullong",
   "<<_sllong_sint",
   "<<_sllong_slong",
   "<<_sllong_sllong",
   "<<_sllong_uint",
   "<<_sllong_ulong",
   "<<_sllong_ullong",
   "<<_uint_sint",
   "<<_uint_slong",
   "<<_uint_sllong",
   "<<_uint_uint",
   "<<_uint_ulong",
   "<<_uint_ullong",
   "<<_ulong_sint",
   "<<_ulong_slong",
   "<<_ulong_sllong",
   "<<_ulong_uint",
   "<<_ulong_ulong",
   "<<_ulong_ullong",
   "<<_ullong_sint",
   "<<_ullong_slong",
   "<<_ullong_sllong",
   "<<_ullong_uint",
   "<<_ullong_ulong",
   "<<_ullong_ullong",

   ">>_sint_sint",
   ">>_sint_slong",
   ">>_sint_sllong",
   ">>_sint_uint",
   ">>_sint_ulong",
   ">>_sint_ullong",
   ">>_slong_sint",
   ">>_slong_slong",
   ">>_slong_sllong",
   ">>_slong_uint",
   ">>_slong_ulong",
   ">>_slong_ullong",
   ">>_sllong_sint",
   ">>_sllong_slong",
   ">>_sllong_sllong",
   ">>_sllong_uint",
   ">>_sllong_ulong",
   ">>_sllong_ullong",
   ">>_uint_sint",
   ">>_uint_slong",
   ">>_uint_sllong",
   ">>_uint_uint",
   ">>_uint_ulong",
   ">>_uint_ullong",
   ">>_ulong_sint",
   ">>_ulong_slong",
   ">>_ulong_sllong",
   ">>_ulong_uint",
   ">>_ulong_ulong",
   ">>_ulong_ullong",
   ">>_ullong_sint",
   ">>_ullong_slong",
   ">>_ullong_sllong",
   ">>_ullong_uint",
   ">>_ullong_ulong",
   ">>_ullong_ullong",

   "&_sint",
   "&_slong",
   "&_sllong",
   "&_uint",
   "&_ulong",
   "&_ullong",

   "^_sint",
   "^_slong",
   "^_sllong",
   "^_uint",
   "^_ulong",
   "^_ullong",

   "|_sint",
   "|_slong",
   "|_sllong",
   "|_uint",
   "|_ulong",
   "|_ullong",

   "@_char",
   "@_schar",
   "@_uchar",
   "@_sshort",
   "@_ushort",
   "@_sint",
   "@_uint",
   "@_slong",
   "@_ulong",
   "@_sllong",
   "@_ullong",

   "<_sint",
   "<_slong",
   "<_sllong",
   "<_uint",
   "<_ulong",
   "<_ullong",
   
   ">_sint",
   ">_slong",
   ">_sllong",
   ">_uint",
   ">_ulong",
   ">_ullong",
   
   "<=_sint",
   "<=_slong",
   "<=_sllong",
   "<=_uint",
   "<=_ulong",
   "<=_ullong",
   
   ">=_sint",
   ">=_slong",
   ">=_sllong",
   ">=_uint",
   ">=_ulong",
   ">=_ullong",
   
   "==_sint",
   "==_slong",
   "==_sllong",
   "==_uint",
   "==_ulong",
   "==_ullong",
   
   "!=_sint",
   "!=_slong",
   "!=_sllong",
   "!=_uint",
   "!=_ulong",
   "!=_ullong"]

  op CTargetOpQIDs : List QualifiedId = map (fn x -> mkQualifiedId("C",x)) CTargetOpNames 

  op CTargetTypeNames : List String = 
  ["Char",
   "Uchar",
   "Ushort",
   "Uint",
   "Ulong",
   "Ullong",
   "Schar",
   "Sshort",
   "Sint",
   "Slong",
   "Sllong",
   "Array"]

 %% TODO add all the CTarget types
  op CTargetTypeQIDs : List QualifiedId =
  map (fn x -> mkQualifiedId("C",x)) CTargetTypeNames  ++
  [
   %% These are included to get around the fact that sliceSpecInfo doesn't do exactly what I want.  It includes the types of the 'CTarget' cut ops (which include subtype predicates).
   mkQualifiedId("Integer", "Int"),
   mkQualifiedId("Nat", "Nat"), %why did this print as just Nat?
   mkQualifiedId("Set", "Set"),
   mkQualifiedId("Bool", "Bool"),
   mkQualifiedId("Function", "Bijection"),
   mkQualifiedId("Set", "FiniteSet"),
   mkQualifiedId("C", "IntConstBase"),
   mkQualifiedId("C", "IntUint")
   ]

  op [a] intersperse (separator : a, vals : List a) : List a =
    (head vals)::(foldr (fn (elem, result) -> separator::elem::result) [] (tail vals))

  op [a] insertBeforeAll (separator : a, vals : List a) : List a =
    foldr (fn (elem, result) -> separator::elem::result) [] vals

  op slash : Char = #/
  op backslash : Char = #\\
  op pathSeparator : Char = (if msWindowsSystem? then backslash else slash)
  op String.pathSeparator : String = Char.show pathSeparator

  op showStrings (strings : List String) : String = (flatten (intersperse(" ", strings)))
  op showQIDs (qids : List QualifiedId) : String = showStrings (map printQualifiedId qids)

  % better way to do this?
  op [b] getRecordTypes (pairs : List (Id * AType b)) : List (AType b) =
    case pairs of
      | [] -> []
      | (id,ty)::tl -> ty::getRecordTypes tl

  op [b] getRecordTerms (pairs : List (Id * ATerm b)) : List (ATerm b) =
    case pairs of
      | [] -> []
      | (id,ty)::tl -> ty::getRecordTerms tl

  op [b] getLetTerms (pairs : List (APattern b * ATerm b)) : List (ATerm b) =
    case pairs of
      | [] -> []
      | (pat,ty)::tl -> ty::getLetTerms tl


  % May extend the set types_in_slice.
  % Not many things are legal here yet.  Examples:
  %   Array Point3D | ofLength? 10
  %   {startp:Point2D, endp:Point2D}
  op typesToTranslateFromType (ty : MSType) : List QualifiedId = 
    case ty of
      %% If it's a subtype, recur on the core type:
      | Subtype(ty, term, _) -> typesToTranslateFromType (ty) %term will often be the "ofLength? ..."
      %% If it's an array, recur on the element type:        
      | Base(Qualified("C","Array"),[elemtype],_) -> typesToTranslateFromType (elemtype)
      %% If it's just the name of a type, include it for translation if it's not a CTarget type
      | Base(qid,[],_) -> if (qid in? CTargetTypeQIDs) then [] else [qid]
      | Product(pairs, _) -> typesToTranslateFromTypes (getRecordTypes pairs)
        % TODO: any other cases to consider?
      | _ -> []

  op typesToTranslateFromTypes (tys : MSTypes) : List QualifiedId =
    case tys of
      | [] -> []
      | ty::rest -> (typesToTranslateFromType ty)++(typesToTranslateFromTypes rest)
 
  % May extend the set types_in_slice
  op typesToTranslateFromTypeWrapper (ty_qid : QualifiedId, spc : Spec) : List QualifiedId =
    case findTheType (spc, ty_qid) of
      | None -> [] % TODO signal an error
      | Some typeinfo -> typesToTranslateFromType(typeinfo.dfn)


%maybe this should handle the outer lambda as well?
  % Deals with And and TypedTerm and Pi (not sure which will be inside of which, although we are moving toward a standard way of doing things):  
  op getCoreTerm (tm : MSTerm) : MSTerm =
    case tm of 
      | And(tm::tms, _) -> getCoreTerm tm  %the first definition is the most recent
      | TypedTerm(tm, ty, _) -> getCoreTerm tm
      | Pi(tyvars, tm, _) -> getCoreTerm tm % included for completeness (should appear for gen-c-thin)
      | _ -> % let _ = writeLine ("core term"^anyToString tm) in 
        tm

%maybe this should handle the outer lambda as well?
  % Deals with And and TypedTerm and Pi (not sure which will be inside of which, although we are moving toward a standard way of doing things):
  op getTypeAndCoreTerm (tm : MSTerm) : MSTerm * MSType =
    case tm of 
      | And(tms, _) -> getTypeAndCoreTerm (head tms) %the first definition is the most recent
      | TypedTerm(tm, ty, _) -> (getCoreTerm tm, ty) %we found the type, now keep looking for the core term
      | Pi(tyvars, tm, _) -> getTypeAndCoreTerm tm % included for completeness (should appear for gen-c-thin)
      | _ -> (tm, Any noPos) %%TODO this should be an error

  % We've already dealt with TypedTerm, And, and Pi
  op opsToTranslateFromTerm (tm : MSTerm) : (List QualifiedId) =
  case tm of
    | Apply(fun, arg, _) -> (opsToTranslateFromTerm fun)++(opsToTranslateFromTerm arg)
    | Record(pairs, _) -> opsToTranslateFromTerms (getRecordTerms pairs)
    | Let(pairs, body, _) ->  (opsToTranslateFromTerms (getLetTerms pairs))++(opsToTranslateFromTerm body)
    | Fun(Op(qid, _), ty, _) -> if (qid in? CTargetOpQIDs) then [] else [qid]
    | Lambda([(_,_,tm)],_) -> (opsToTranslateFromTerm tm) %this should only be near the top level
    | IfThenElse(cond, thenbranch, elsebranch, _) -> (opsToTranslateFromTerm cond)++(opsToTranslateFromTerm thenbranch)++(opsToTranslateFromTerm elsebranch)
    %% TODO should we allow seq?  could get rid of seqs with a transformation
    | _ -> [] %TODO anything missing?
                   
  op opsToTranslateFromTerms (tms : MSTerms) : (List QualifiedId) =
    case tms of
      | [] -> []
      | tm::rest -> (opsToTranslateFromTerm tm)++(opsToTranslateFromTerms rest)        

  op opsAndTypesToTranslateFromOp (op_qid : QualifiedId, spc : Spec)
                                            : (List QualifiedId) * (List QualifiedId) =
    case findTheOp (spc, op_qid) of
      | None -> ([],[]) % TODO signal an error
      | Some opinfo -> let body = opinfo.dfn in 
                       let (corebody, ty) = getTypeAndCoreTerm body in
                       %% We mine the type of this op for types to translate:
                       let types_to_add = typesToTranslateFromType ty in
                       %% We mine the body of this op for ops to translate:
                       %% I think there is no need to mine the body for types, since the type of any called, non-CTarget op will be included when that op is processed recursively (by this opsAndTypesToTranslateFromOp function).
                       let ops_to_add = opsToTranslateFromTerm(corebody) in
                       %% We add all the non-C-Target ops called by this op, and we add the type of this op:
                       (ops_to_add, types_to_add)


  % There are some differences between this and what we would get from calling
  % sliceSpecInfo.  I tried using sliceSpecInfo but found a couple of issues.
  % First, when cutting at a CTarget op, sliceSpecInfo would still include its
  % type in the slice.  Unfortunately, the type of a CTarget op is not always
  % representable in C (e.g., for ops such as -_1_sint that are only defined on
  % certain inputs).  Second, sliceSpecInfo doesn't completely exclude extra
  % definitions for ops (introduced via refine def or transformations and
  % manifested in "And" terms), e.g., when calling foldTerm to process *all*
  % subterms of a term.  So I wrote this custom function.  Improvements/changing
  % to sliceSpecInfo might allow us to call that here instead.
  %% Returns the stuff to be translated to C: set of ops and a set of types.
  op getOpsAndTypesToTranslate (op_worklist    : QualifiedIds, % should not include any CTarget ops
                                type_worklist  : QualifiedIds, % should not include any CTarget types
                                ops_in_slice   : QualifierSet,
                                types_in_slice : QualifierSet,
                                done_ops       : QualifierSet,
                                done_types     : QualifierSet,
                                spc            : Spec) 
                               : QualifierSet * QualifierSet =
    case op_worklist of
      | [] ->
        (case type_worklist of
           | [] -> (ops_in_slice, types_in_slice) % Nothing left to process
           | tyQID::rest -> (if (tyQID in? done_types) then
                               % skip this type (already done):
                               getOpsAndTypesToTranslate (op_worklist, rest, ops_in_slice, types_in_slice, done_ops, done_types, spc)
                             else
                               % process tyQID (for thin C generation, we don't extract any ops from types - type can just be arrays, structs, or aliases of other types):
                               let types_to_add = typesToTranslateFromTypeWrapper(tyQID, spc) in
                               % Add the newly discovered types to the result we are building up and also to the worklist to be processed recursively.  Also add the current type to the result and mark it as done:
                               getOpsAndTypesToTranslate (op_worklist, types_to_add++rest, ops_in_slice, addList(types_in_slice, types_to_add) <| tyQID, done_ops, done_types <| tyQID, spc)))
      | opQID::rest ->  (if (opQID in? done_ops) then
                               % skip this op (already done):
                               getOpsAndTypesToTranslate (rest, type_worklist, ops_in_slice, types_in_slice, done_ops, done_types, spc)
                             else
                               % process opQID (for thin C generation, we don't extract any ops from types - type can just be arrays, structs, or aliases of other types):
                               let (ops_to_add, types_to_add) = opsAndTypesToTranslateFromOp(opQID, spc) in
                               % Add the newly discovered types and ops to the results we are building up and also to their respective worklists to be processed recursively.  Also add the current op to the result and mark it as done:
                               getOpsAndTypesToTranslate (rest++ops_to_add, type_worklist++types_to_add, addList(ops_in_slice, ops_to_add) <| opQID, addList(types_in_slice, types_to_add), done_ops <| opQID, done_types, spc))


 %% The return value indicates success or failure (true or false, respectively).
 % TODO check that opqid is a valid op in the spec?
 % TODO we could have the user do the slicing before calling gen-c-thin...
 op evaluateGenCThinHelper (opqid : QIDorAll, uid_str : String, spc : Spec) : Bool = 
    %% let _ = writeLine("Calling evaluateGenCThinHelper.") in
    %% let _ = writeLine("Op: "^anyToString(opqid)) in
    %% Find out the absolute unit id of the spec (the user-supplied unit ID may have been resolved with respect to SWPATH, etc.):
    let uid = uidForValue(Spec spc) in
    case uid of
    | None -> let _ = writeLine("ERROR: Processing the given unit seems to have failed.") in false
    | Some uid ->
      %% let _ = writeLine ("uid.path:"^anyToString(uid.path)) in
      let spc = explicateEmbeds spc in
      let spc = removeImplicitConstructorOps spc in
      let path = uid.path in
      let hashSuffix = uid.hashSuffix in
      let dirs = butLast path in
      let basename = last path ^ (case hashSuffix of | None -> "" | Some str -> "_"^str) in
      let dirString = insertBeforeAll(pathSeparator, dirs) in  %%TODO handle Windows drive letters.  Are they part of the path stored in the unitID?  Don't put a slash in front of the drive letter!
      %% Everything goes in the C/ subdirectory:
      let pathForFilesNoExtention = flatten (dirString ++ [pathSeparator] ++ ["C"] ++ [pathSeparator] ++ [basename]) in
      let CFileName = pathForFilesNoExtention^".c" in
      let HFileName = pathForFilesNoExtention^".h" in
      % let _ = writeLine("Writing to files:") in
      % let _ = writeLine(pathForCFile^".c") in
      % let _ = writeLine(pathForCFile^".h") in
      %% TODO allow a type to be passed in explicitly (actually, a list of ops and types -- but how to tell which is which?), instead of just an op.
      let (root_ops, root_types) = (case opqid of
                                      | QID opqid -> ([opqid],[])
                                      | All -> nonCTargetOpsAndTypes([],[],spc.elements)) in
      let _ = writeLine("Root ops: "^showQIDs root_ops) in
      let _ = writeLine("Root types: "^showQIDs root_types) in
      %% Slice to find everything on which the root_ops and root_type depend (stopping when we hit anything in CTarget).
      %% All of the resulting ops and types will be translated to C.
      let (op_set, type_set) = getOpsAndTypesToTranslate(root_ops, root_types, emptySet, emptySet, emptySet, emptySet, spc)
                                             % root_ops,
                                             % root_types,
                                             % %% ops at which to stop slicing:
                                             % fn x -> x in? CTargetOpQIDs, 
                                             % %% types at which to stop slicing:
                                             % fn x -> x in? CTargetTypeQIDs,
                                             % false, %chase_terms_in_types?
                                             % false, %chase_theorems?
                                             % true % firstDefsOnly?
                                               in
      let op_names = foldriAQualifierMap (fn (q, i, boolval, lst) -> if boolval then Qualified(q,i) |> lst else lst) [] op_set in
      let type_names = foldriAQualifierMap (fn (q, i, boolval, lst) -> if boolval then Qualified(q,i) |> lst else lst) [] type_set in
      % TODO print the qualifiers:
      let _ = writeLine("ops to generate C code for: "^showQIDs op_names) in
      % let _ = MapSTHashtable.STH_mapi ((fn (key %(qualifier,basename)
      %                                         ,bool) -> writeLine %(qualifier^"."^basename)
      %                                     key
      %                                     ), op_set) in 
      % TODO print the qualifiers:
      let _ = writeLine("types to generate C code for: "^showQIDs type_names) in
      % let _ = MapSTHashtable.STH_mapi ((fn (key %(qualifier,basename)
      %                                         ,bool) -> writeLine %(qualifier^"."^basename)
      %                                     key
      %                                     ), type_set) in 
      let _ = printSpecAsCToFile(op_set, type_set, CFileName, HFileName, basename, spc) in
      true
    
end-spec
