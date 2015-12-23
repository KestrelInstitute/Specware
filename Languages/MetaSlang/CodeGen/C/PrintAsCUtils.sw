(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

PrintAsC qualifying spec

 import /Languages/SpecCalculus/AbstractSyntax/SCTerm                   % SCTerm
 import /Languages/MetaSlang/Specs/MSTerm                               % MSTerm
 import /Languages/MetaSlang/Specs/AnnSpec                              % Spec
 import /Languages/SpecCalculus/Semantics/Environment                   % ??
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements % topSortElements
 import /Languages/MetaSlang/AbstractSyntax/Printer                     % Pretty, format, etc.

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% useful things that probably should be in AnnSpec, etc.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type FileName = String
 type Indent   = Nat
 type MSFun    = AFun Position

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Misc printer stuff
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% crib notes for Printer:

 %%  type NatStrings = List (Nat * String)         % List (Length * String)
 %%  type Text       = List (Nat * NatStrings)     % List (Indent * NatStrings)

 %%  type Pretty     = Nat * (Nat * Text -> Text)  % ??
 %%  type Prettys    = List Pretty

 %%  type Line       = Nat * Pretty                % ??
 %%  type Lines      = List Line

 op L0_null        : Line = (0, string "")

 op L0_lparen      : Line = (0, string "(")  
 op L0_rparen      : Line = (0, string ")")
 op L0_lsquare     : Line = (0, string "[")
 op L0_rsquare     : Line = (0, string "]")
 op L0_lbracket    : Line = (0, string "{")
 op L0_rbracket    : Line = (0, string "}")
 op L0_space       : Line = (0, string " ")
 op L0_semicolon   : Line = (0, string ";")

 op L0_comma_space : Line = (0, string ", ")
 op L0_if          : Line = (0, string "if ")
 op L0_else        : Line = (0, string "else ")
 op L0_expr_then   : Line = (0, string " ? ")
 op L0_expr_else   : Line = (0, string " : ")

 op L0_space_equal_space : Line = (0, string " = ")  

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Local structures for C generation
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type CFunCall = {f : MSTerm, args : MSTerms}

 type CInfo = 
   | Type QualifiedId * TypeInfo
   | Op   QualifiedId * OpInfo

 type CInfos = List CInfo

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Predicates for C generation
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op legal_C_Id? (id : String) : Bool =
  let 
    def legal_C_char? char =
      isAlphaNum char || char = #_
  in
  case explode id of
    | hd :: tail -> (isAlpha hd || hd = #_) && (forall? legal_C_char? tail)
    | _ -> false

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Options and Status for C generation
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type CGenStatus = {plainCharsAreSigned? : Bool,        % Option
                    printPragmas?        : Bool,        % Option
                    defined_types        : List Id,     % Status % QualifieId ?
                    defined_ops          : List Id,     % Status % QualifieId ?
                    h_prettys            : Prettys,
                    c_prettys            : Prettys,
                    warning_msgs         : List String,
                    error_msgs           : List String}

 op init_cgen_status (spc : Spec) : Option CGenStatus = 
  let plain_chars_are_signed? =
      case findTheOp (spc, Qualified ("C", "plainCharsAreSigned")) of
        | Some opinfo ->
          let 
            def true? tm =
              case tm of
                | Fun (Bool b, _, _) -> b
                | TypedTerm (tm, _, _) -> true? tm
                | _ -> 
                  let _ = writeLine ("plainCharsAreSigned has unrecognized definition: " ^ printTerm tm 
                                       ^ ", defaulting to false") 
                  in
                  false
          in
          let signed? = true? opinfo.dfn in
          signed?
        | _ ->
          let _ = writeLine ("could not find plainCharsAreSigned, defaulting to false") in
          false
  in

  let _ = writeLine ("printPragmas? is hardwired to false for now") in
  let print_pragmas? = false in

  let _ = writeLine ("plainCharsAreSigned? = " ^ show plain_chars_are_signed?) in
  let _ = writeLine ("printPragmas?        = " ^ show print_pragmas?)          in
  let _ = writeLine ("") in

  case findCTarget spc of
    | Some (ctarget_spec, ctarget_elements) ->
      let defined_types = [] in
      let defined_ops   = [] in
      Some {plainCharsAreSigned? = plain_chars_are_signed?,
            printPragmas?        = print_pragmas?,
            defined_types        = ["char", "short", "int", "long"], % "unsigned char" can't possibly be a user type
            defined_ops          = [],
            h_prettys            = [],
            c_prettys            = [],
            warning_msgs         = [],
            error_msgs           = []}
    | _ ->
      let _ = writeLine ("Confusion in C generation:  CTarget suddenly no longer imported?") in
      None

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op reportWarning (msg : String, status : CGenStatus) : CGenStatus =
  % let _ = writeLine warning_msg in
  status << {warning_msgs = status.warning_msgs ++ [msg]}

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op reportError (msg : String, status : CGenStatus) : CGenStatus =
  % let _ = writeLine error_msg in
  status << {error_msgs = status.error_msgs ++ [msg]}

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op reportConfusion (msg : String, status : CGenStatus) : CGenStatus =
  % let _ = writeLine error_msg in
  status << {error_msgs = status.error_msgs ++ ["?? Internal confusion: " ^ msg]}

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op addNewType (status : CGenStatus, qid as Qualified(_,id) : QualifiedId) : Id * CGenStatus =
  let defined_types = status.defined_types in
  if id in? defined_types then
    (id, reportError ("attempting to redefine: " ^ id, status))
  else if legal_C_Id? id then
    (id, status << {defined_types = id :: defined_types})
  else
    (id, reportError ("illegal C type name: " ^ id, status))

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op getCTypeName (qid as Qualified (q,id) : QualifiedId, status : CGenStatus) : Option Id =
  if q = "C" then
     case id of
       | "Uchar"  -> Some "unsigned char"
       | "Schar"  -> Some "signed char"
       | "Char"   -> Some "char"
       | "Ushort" -> Some "unsigned short"
       | "Uint"   -> Some "unsigned int"
       | "Ulong"  -> Some "unsigned long"
       | "Ullong" -> Some "unsigned long long"
       | "Sshort" -> Some "short"
       | "Sint"   -> Some "int"
       | "Slong"  -> Some "long"
       | "Sllong" -> Some "long long"
       | _        -> None
   else if id in? status.defined_types then
     Some id
   else 
     None

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op addNewOp (status : CGenStatus, qid as Qualified (_,id) : QualifiedId) : Id * CGenStatus =
  let defined_ops = status.defined_ops in
  if id in? defined_ops then
    (id, reportError ("attempting to redefine: " ^ id, status))
  else if legal_C_Id? id then
    (id, status << {defined_ops = id :: defined_ops})
  else
    (id, reportError ("illegal C function name: " ^ id, status))

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op getCOpName (qid as Qualified (_,id) : QualifiedId, status : CGenStatus) : Option Id =
  let defined_ops = status.defined_ops in
  if id in? defined_ops then
    Some id
  else 
    None

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Utilities related to CTarget.sw
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op refersToCTarget? (term : SCTerm) : Bool =
  %% TODO: Perhaps determine that this is the CTarget in the base library,
  %%       as opposed to a CTarget.sw in some random directory.
  case term.1 of
    | UnitId (SpecPath_Relative {hashSuffix = _, path = ["Library", "CGen", "Shallow", "CTarget"]}) -> 
      true

    | UnitId (UnitId_Relative unit_id) ->
      (case reverse unit_id.path of
         | "CTarget" :: _ -> true
         | _ -> false)

    | _ -> false

 op importsCTarget? (spc : Spec) : Bool =
  let 
    def aux elements =
      case elements of 
        | (Import (term, spc, imported_elements, _)) :: tail ->
          (refersToCTarget? term) || 
          (aux imported_elements) ||
          (aux tail)
        | _ -> false
  in
  aux spc.elements

 op findCTarget (spc : Spec) : Option (Spec * SpecElements) =
  let 
    def aux elements =
      case elements of 
        | (Import (scterm, spc, imported_elements, _)) :: tail ->
          if refersToCTarget? scterm then
            Some (spc, imported_elements)
          else 
            (case aux imported_elements of  % search recursively
               | Some pair -> Some pair     % stopping if we found it
               | _ -> aux tail)             % else continue search at this level
        | _ -> None
  in
  aux spc.elements

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Status of C generation
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(*
 op ppForC (status : CGenStatus, pretty : Pretty, to_h_file? : Bool) : CGenStatus =
  if to_h_file? then
    ppToHFile (status, pretty)
  else
    ppToCFile (status, pretty)
*)
 op ppToH (status : CGenStatus, pretty : Pretty) : CGenStatus =
  status << {h_prettys = status.h_prettys ++ [pretty]} 

 op ppToC (status : CGenStatus, pretty : Pretty) : CGenStatus =
  status << {c_prettys = status.c_prettys ++ [pretty]} 

end-spec
