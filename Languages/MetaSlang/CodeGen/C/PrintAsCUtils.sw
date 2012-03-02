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
  %% TODO: look for name clashes
  let 
    def legal_C_char? char =
      isAlphaNum char || char = #_
  in
  case explode id of
    | hd :: tail -> (isAlpha hd || hd = #_) && (forall? legal_C_char? tail)
    | _ -> false

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Options for C generation
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type CGenOptions = {plainCharsAreSigned? : Bool,
                     printPragmas?        : Bool}

 op init_cgen_options (spc : Spec) : CGenOptions = 
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
  {plainCharsAreSigned? = plain_chars_are_signed?,
   printPragmas?        = print_pragmas?}

end-spec
