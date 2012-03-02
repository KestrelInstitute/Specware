PrintAsC qualifying spec

 import /Languages/SpecCalculus/AbstractSyntax/SCTerm                   % SCTerm
 import /Languages/MetaSlang/Specs/MSTerm                               % MSTerm
 import /Languages/MetaSlang/Specs/AnnSpec                              % Spec
 import /Languages/SpecCalculus/Semantics/Environment                   % ??
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements % topSortElements
 import /Languages/MetaSlang/AbstractSyntax/Printer                     % Pretty, format, etc.

 %% crib notes for Printer:

 %%  type NatStrings = List (Nat * String)         % List (Length * String)
 %%  type Text       = List (Nat * NatStrings)     % List (Indent * NatStrings)

 %%  type Pretty     = Nat * (Nat * Text -> Text)  % ??
 %%  type Prettys    = List Pretty

 %%  type Line       = Nat * Pretty                % ??
 %%  type Lines      = List Line

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% useful things that probably should be in AnnSpec, etc.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type FileName = String
 type Indent   = Nat
 type MSFun    = AFun Position

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Local structures for C generation
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type CFunCall = {f : MSTerm, args : MSTerms}

 type CInfo = 
   | Type QualifiedId * Option TypeInfo
   | Op   QualifiedId * Option OpInfo

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

 type CGenStatus = {plainCharsAreSigned? : Bool,    % Option
                    printPragmas?        : Bool,    % Option
                    defined_types        : List Id, % Status % QualifieId ?
                    defined_ops          : List Id} % Status % QualifieId ?

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
            defined_types        = [],
            defined_ops          = []}
    | _ ->
      let _ = writeLine ("?? huh?:  CTarget no longer imported?") in
      None

  op addNewType (qid as Qualified(_,id) : QualifiedId) (status : CGenStatus) 
   : Option (Id * CGenStatus) =
   let defined_types = status.defined_types in
   if id in? defined_types then
     let _ = writeLine("Error: addNewType: attempting to redefine: " ^ id) in
     None
   else if legal_C_Id? id then
     Some (id, status << {defined_types = id :: defined_types})
   else
     let _ = writeLine("Error: addNewType: id is not legal C type name: " ^ id) in
     None

  op addNewOp (qid as Qualified (_,id) : QualifiedId) (status : CGenStatus) 
   : Option (Id * CGenStatus) =
   let defined_ops = status.defined_ops in
   if id in? defined_ops then
     let _ = writeLine("Error: addNewOp: attempting to redefine: " ^ id) in
     None
   else if legal_C_Id? id then
     Some (id, status << {defined_ops = id :: defined_ops})
   else
     let _ = writeLine("Error: addNewOp: id is not legal C function name: " ^ id) in
     None

  op getCFunctionName (qid as Qualified (_,id) : QualifiedId) (status : CGenStatus) 
   : Option Id =
   let defined_ops = status.defined_ops in
   if id in? defined_ops then
     Some id
   else 
     None

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Utilities related to CTarget.sw
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op refersToCTarget? (term : SCTerm) : Bool =
  case term.1 of
    | UnitId (SpecPath_Relative {hashSuffix = _, path = ["Library", "CGen", "CTarget"]}) -> true
    | _ -> false

 % superfluous
 % op refersToBase? (term : SCTerm) : Bool =
 %  case term.1 of
 %    | UnitId (SpecPath_Relative {hashSuffix = _, path = ["Library", "Base"]}) -> true
 %    | _ -> false

 op importsCTarget? (spc : Spec) : Bool =
  let 
    def aux elements =
      case elements of 
        | (Import (term, spc, _, _)) :: tail ->
          (refersToCTarget? term) || (aux tail)
        | _ -> false
  in
  aux spc.elements

 op findCTarget (spc : Spec) : Option (Spec * SpecElements) =
  let 
    def aux elements =
      case elements of 
        | (Import (term, spc, imported_elements, _)) :: tail ->
          if refersToCTarget? term then
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


end-spec
