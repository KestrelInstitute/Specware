CG qualifying spec
{
 import /Languages/MetaSlang/Transformations/PatternMatch
 import /Languages/MetaSlang/Transformations/SliceSpec

 import /Languages/MetaSlang/CodeGen/AddMissingFromBase
 import /Languages/MetaSlang/CodeGen/Poly2Mono
 import /Languages/MetaSlang/CodeGen/LetWildPatToSeq
 import /Languages/MetaSlang/CodeGen/AddEqOpsToSpec
 import /Languages/MetaSlang/CodeGen/AddTypeConstructorsToSpec
 import /Languages/MetaSlang/CodeGen/ConformOpDecls
 import /Languages/MetaSlang/CodeGen/AdjustAppl
 import /Languages/MetaSlang/CodeGen/SubstBaseSpecs
 
 import /Languages/MetaSlang/Transformations/RemoveCurrying
 import /Languages/MetaSlang/Transformations/LambdaLift
 import /Languages/MetaSlang/Transformations/InstantiateHOFns
 import /Languages/MetaSlang/Transformations/RecordMerge
 import /Languages/MetaSlang/Transformations/TheoryMorphism
 
 import /Languages/MetaSlang/CodeGen/I2L/SpecsToI2L  % MetaSlang =codegen=> I2L
 import /Languages/I2L/CodeGen/C/I2LToC              % I2L       =codegen=> C

 import /Languages/MetaSlang/CodeGen/C/PrintSpecAsC

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% Debugging support...

 op verbosity : Nat = 0

 op showInternals (spc : Spec) : () =
  appSpec ((fn tm  -> writeLine (printTermWithTypes tm)), 
           (fn typ -> writeLine (printType          typ)),
           (fn pat -> writeLine (printPattern       pat)))
          spc

 op showSpc (msg : String) (spc : Spec) : () =
  % let n = internalRunTime() in
  % let _ = writeLine("CG: " ^ show n ^ " " ^ msg) in
  if verbosity > 0 then 
    let _ = writeLine "--------------------" in
    let _ = writeLine ("### " ^ msg)         in
    let _ = writeLine (printSpec spc)        in
    let _ = writeLine "----"                 in
    let _ = if (verbosity > 1) then showInternals spc else () in
    let _ = writeLine "--------------------" in
    ()
  else
    ()

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% If these predicates are true, don't include the indicated op or type when 
 %% slicing, and don't recur through their definitions.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op builtinCType? (Qualified (q, id) : QualifiedId) : Bool =
  case q of
    | "Boolean"    -> id in? ["Bool"]
    | "Integer"    -> id in? ["Int", "Int0"]
    | "Nat"        -> id in? ["Nat"]
    | "Char"       -> id in? ["Char"]
    | "String"     -> id in? ["String"]
    | _ -> false
      
 op builtinCOp? (Qualified (q, id) : QualifiedId) : Bool =
  case q of
    | "Boolean"    -> id in? ["show", "toString"]
    | "Integer"    -> id in? ["+", "-", "*", "div", "mod", "<=", "<", "~", ">", ">=", "**", "isucc", "ipred", "toString"]
    | "IntegerAux" -> id in? ["-"]  % unary minus
    | "Nat"        -> id in? ["show", "toString"]
    | "Char"       -> id in? ["chr", "ord", "compare", "show"] 
    | "String"     -> id in? ["compare", "append", "++", "^", "<", "newline", "length", "implode"]
    | "System"     -> id in? ["writeLine", "toScreen"]
    | "Handcoded"  -> true
    | _ -> false

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Remove subtype predicates, etc. that would not appear in final code.
 %% Keep subtypes of Nat, later used to choose among char, short, int, long, etc.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op stripNonNatSubtypesAndBaseDefs (spc : Spec) (typ : MSType) : MSType =
  let 
    def strip typ =
      case typ of
        %% new case to preserve subtypes of Nat:
        | Subtype (Base (Qualified ("Nat", "Nat"), [], _),
                   %% {x : Nat -> x < n} where n is a Nat
                   Lambda ([(VarPat ((X,_), _),
                             Fun (Bool true, _, _),
                             Apply (Fun (Op (Qualified (_, pred), _), _, _),
                                    Record ([(_, Var((X0,_), _)),
                                             (_, Fun (Nat n, _, _))],
                                            _),
                                    _)
                             )],
                           _),
                   _)
           | X = X0 && pred in? ["<=", "<"] 
          -> 
          typ

        | Subtype (typ, _, _) -> strip typ

        | Base (qid, typs, a) ->
          (case findTheType (spc, qid) of
             | Some info ->
               if definedTypeInfo? info then
                 let (tvs, tdef) = unpackFirstTypeDef info in
                 let recur? = (length tvs = length typs)
                              &&
                              (case tdef of
                                 | Subtype _ -> true
                                 | Base    _ -> true
                                 | _ -> false)
                 in
                 if recur? then 
                   strip (substType (zip (tvs, typs), tdef))
                 else
                   typ
               else
                 typ
             | _ -> typ)
        | _ -> typ
  in
  strip typ

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Transform MetaSlang spec in preparation for C code generation. 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op transformSpecForCodeGen (spc : Spec) : Spec =
  let _ = if verbosity > 0 then 
            let _ = showSpc "Starting" spc                                                  in
            let _ = writeLine ";;; generating C code..."                                    in
            let _ = writeLine "-----------------------------------------------------------" in
            let _ = writeLine "transforming spec for C code generation..."                  in
            let _ = writeLine "-----------------------------------------------------------" in
            ()
          else
            ()
  in

  let 

   def removeUnusedOps top_ops top_types spc =
     sliceSpecForCode (spc, top_ops, top_types, builtinCOp?, builtinCType?)

   def specStripNonNatSubtypesAndBaseDefs spc =
     let stripper = stripNonNatSubtypesAndBaseDefs spc in
     mapSpec (fn t -> t, stripper, fn p -> p) spc

  in

  let (top_ops, top_types) = topLevelOpsAndTypesExcludingBaseSubsts spc in % fetch early, to avoid including anything accidentally added at toplevel by transforms
  let _ = writeLine "----" in
  let _ = writeLine (anyToString top_ops) in
  let _ = writeLine "----" in

  let _ = showSpc "Original"                      spc in %  (0)
  
  let spc = substBaseSpecs                        spc in %  (1) adds misc ops (possibly unused) from List_Executable.sw, String_Executable.sw, etc.
  let _ = showSpc "substBaseSpecs"                spc in
  
  let spc = removeUnusedOps top_ops top_types     spc in %  (2) do this early to minimize wasted motion (and again later to filter incidental cruft)
  let _ = showSpc "sliceSpec[1]"                  spc in 
  
  let spc = removeCurrying                        spc in %  (3) op f: A -> B -> C  ==>  op f_1_1: A * B -> C, etc.
  let _ = showSpc "removeCurrying"                spc in
  
  let spc = normalizeTopLevelLambdas              spc in %  (4) convert patterned lambdas into case expressions
  let _ = showSpc "normalizeTopLevelLambdas"      spc in
  
  let spc = instantiateHOFns                      spc in %  (5) calls normalizeCurriedDefinitions and simplifySpec -- should precede lambdaLift, poly2mono
  let _ = showSpc "instantiateHOFns"              spc in
  
  let spc = lambdaLiftWithImports                 spc in %  (6) as good a time as any
  let _ = showSpc "lambdaLift"                    spc in
  
  let spc = translateMatch                        spc in %  (7) Wadler's pattern matching compiler -- may add calls to polymorphic fns, so must precede poly2mono
  let _ = showSpc "translateMatch"                spc in
  
  let spc = letWildPatToSeq                       spc in %  (8) transforms "let _ = t1 in t2" into "(t1;t2)"
  let _ = showSpc "letWildPatToSeq"               spc in
  
  let spc = specStripNonNatSubtypesAndBaseDefs    spc in %  (9) should preceed poly2mono, to avoid introducing spurious names such as List_List1_Nat__Cons
  let _ = showSpc "strip subtypes"                spc in
  
  let spc = poly2monoAndDropPoly                  spc in % (10) After this is called, we can no longer reason about polymorphic types such as List(a)
  let _ = showSpc "poly2mono"                     spc in
  
  let spc = translateRecordMergeInSpec            spc in % (11) rewrite forms such as foo << {y = y} to {x = foo.x, y = y, z = foo.z}
  let _ = showSpc "translateRecordMergeInSpec"    spc in
  
  let spc = simplifySpec                          spc in % (12) generic optimizations -- inlining, remove dead code, etc. % TODO: move to end?
  let _ = showSpc "simplifySpec"                  spc in
  
  let spc = addEqOpsToSpec                        spc in % (13) add equality ops for sums, products, etc. -- TODO: adds far too many (but removeUnusedOps removes them)
  let _ = showSpc "addEqOpsToSpec"                spc in
  
  let spc = removeUnusedOps top_ops top_types     spc in % (14) remove newly introduced but unused ops (mainly eq ops) 
  let _ = showSpc "sliceSpec[2]"                  spc in 
  
  let (spc,constrOps) = addTypeConstructorsToSpec spc in % (15) these ops won't survive slicing, so this must follow removeUnusedOps
  let _ = showSpc "addTypeConstructorsToSpec"     spc in
  
  let spc = conformOpDecls                        spc in % (16) change def with multiple args to decompose single arg when decl has one (product) arg
  let _ = showSpc "conformOpDecls"                spc in
  
  let spc = adjustAppl                            spc in % (17) change call with multiple args to compose single arg when decl has one (product) arg
  let _ = showSpc "adjustAppl"                    spc in
  
  spc

 op topLevelOpsAndTypesExcludingBaseSubsts (spc : Spec) : QualifiedIds * QualifiedIds =
  let (base_subst_ops, base_subst_types) = substBaseSpecOpsAndTypes () in
  let ops   = filter (fn qid -> ~ (qid in? base_subst_ops)) (topLevelOps   spc) in
  let types = filter (fn qid -> ~ (qid in? base_subst_ops)) (topLevelTypes spc) in
  (ops, types)
  
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Generate the C_Spec for the given spec. 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op generateCSpec (app_name : String) (spc : Spec) : C_Spec =
  let spc  = transformSpecForCodeGen spc in
  generateCSpecFromTransformedSpec app_name spc 

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Generate a C_Spec from an already transformed MetaSlang spec.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op generateCSpecFromTransformedSpec (app_name : String) (spc : Spec) : C_Spec =
  generateCSpecFromTransformedSpecIncr app_name spc (emptyCSpec "") 

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% As above, but incremental -- the provided C_Spec is used to lookup already 
 %% existing definitions.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op generateCSpecFromTransformedSpecIncr (app_name : String) 
                                         (spc      : Spec) 
                                         (xcspc    : C_Spec)
  : C_Spec =
  let filter = (fn _ -> true) in
  generateCSpecFromTransformedSpecIncrFilter app_name spc xcspc filter

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Generate a C_Spec from an already transformed MetaSlang spec.
 %% The filter function is used to selectively generate code only for those ops 
 %% and types x for which filter(x) is true.
 %% The C_Spec parameter is used for incremental code generation.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op generateCSpecFromTransformedSpecIncrFilter (app_name : String) 
                                               (spc      : Spec) 
                                               (xcspc    : C_Spec)
                                               (filter   : QualifiedId -> Bool) 
  : C_Spec =
  let constrOps   = []                                                              in
  let useRefTypes = true                                                            in
  let impunit     = generateI2LCodeSpecFilter (spc, useRefTypes, constrOps, filter) in
  let cspec       = generateC4ImpUnit         (impunit, xcspc, useRefTypes)         in
  cspec

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Split the C spec into .c and .h portions and print those two files.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op printToFile (app_name     : String,
                 c_spec       : C_Spec,
                 opt_filename : Option String)
  : () =
  let filename =
      case opt_filename of
        | None          -> "cgenout.c"
        | Some filename -> filename
  in
  let len = length filename in
  let basename = if subFromTo (filename, len-2, len) = ".c" then
                   subFromTo (filename, 0, len-2)
                 else
                   filename
  in
  let _ = writeLine (";; writing generated code to " ^ basename ^ ".[ch]...") in

  let c_filename       = basename ^ ".c"    in
  let h_filename       = basename ^ ".h"    in
  let (h_spec, c_spec) = splitCSpec c_spec  in  

  let id_dfn           = ("Patched_PrismId", C_String, C_Const (C_Str basename)) in

  let c_spec           = addConstDefn (c_spec, id_dfn)   in  
  let c_spec           = addHeader  (c_spec, app_name)   in
  let c_spec           = addTrailer (c_spec, app_name)   in
  let h_spec           = addHeader  (h_spec, app_name)   in
  let h_spec           = addTrailer (h_spec, app_name)   in
  let c_spec           = addInclude (c_spec, h_filename) in

  let _ = printCSpecToFile (h_spec, h_filename) in
  let _ = printCSpecToFile (c_spec, c_filename) in
  ()

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% Generate C code for the given spec and write it into the given file.
 %% If the filename is None, "cgenout.c" is taken.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op generateCCode (app_name     : String,
                   spc          : Spec, 
                   opt_filename : Option String)
  : () =
  if importsCTarget? spc then
    let filename = case opt_filename of 
                     | Some filename -> filename 
                     | _ -> "testing" 
    in
    printSpecAsCToFile (filename, spc)
  else
    let cspec = generateCSpec app_name spc in 
    printToFile (app_name, cspec, opt_filename)
}
