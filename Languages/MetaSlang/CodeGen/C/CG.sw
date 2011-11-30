(**
 * interface to the MetaSlang C code generator
 *)

CG qualifying
spec
%  import /Languages/MetaSlang/CodeGen/CodeGenTransforms

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

  import /Languages/MetaSlang/Specs/SubtractSpec

  import /Languages/MetaSlang/CodeGen/I2L/SpecsToI2L             % MetaSlang =codegen=> I2L
  import /Languages/I2L/CodeGen/C/I2LToC                         % I2L       =codegen=> C

% --------------------------------------------------------------------------------
% interface
% --------------------------------------------------------------------------------

  (**
   * performs the neccessary transformations on the MetaSlang spec spc as preparation
   * for the C code generation. The basespec is used to add the neccessary types and op
   * the base spec to the resulting spec.
   * op transformSpecForCodeGen: (*basespec:*)AnnSpec.Spec -> (*spc:*)AnnSpec.Spec -> AnnSpec.Spec 
   *)

  (**
   * same as transformSpecForCodeGen, only that the transformation step "addMissingFromBase"
   * is omitted, i.e. no ops and types are added from the base spec
   * op transformSpecForCodeGenNoAdd: AnnSpec.Spec -> AnnSpec.Spec
   *)

  (**
   * generates C code for the given spec and writes it into the given file.
   * If the filename is None, "cgenout.c" is taken.
   * The basespec is used to add the neccessary types and op
   * the base spec to the resulting spec.
   * The third argument is ignored (todo: eliminate 3rd parameter in calls to this op)
   * op generateCCode: (*basespec:*)AnnSpec.Spec * (*spc:*)AnnSpec.Spec * AnnSpec.Spec * Option String -> ()
   *)

  (**
   * generates the C_Spec for the given spec. The basespec is used to add the neccessary
   * types and op the base spec to the resulting cspec.
   * op generateCSpec: (*basespec:*)AnnSpec.Spec -> (*spc:*)AnnSpec.Spec -> C_Spec
   *)


  (**
   * generate a C_Spec from an already transformed MetaSlang spec
   * op generateCSpecFromTransformedSpec: AnnSpec.Spec -> C_Spec
   *)
  

  (**
   * generate a C_Spec from an already transformed MetaSlang spec,
   * the filter function is used to selectively generate code only
   * for those ops and types x for which filter(x) is true.
   * The C_Spec parameter is used for incremental code generation.
   * op generateCSpecFromTransformedSpecIncrFilter: C_Spec -> AnnSpec.Spec -> (QualifiedId -> Bool) -> C_Spec
   *)

  (**
   * same as generateCSpecFromTransformedSpec, only that the additional C_Spec
   * is used to lookup already existing definitions in the C_Spec
   * op generateCSpecFromTransformedSpecIncr: C_Spec -> AnnSpec.Spec -> C_Spec
   * op generateCSpecFromTransformedSpecEnv: AnnSpec.Spec -> Env C_Spec
   *)


  (**
   * print the given cspec to a .h and .c file. The filename is used as
   * base name for the generated file, if omitted it defaults to "cgenout"
   * op printToFile: C_Spec * Option String -> ()
   * op postProcessCSpec: C_Spec -> C_Spec
   *)


  (**
   * monadic version of printToFile
   * op printToFileEnv: C_Spec * Option String -> Env ()
   *)

  (**
   * transforms a MetaSlang type to a C type
   * op typeToCType: C_Spec -> AnnSpec.Spec -> Type -> (C_Spec * C_Type)
   *)

  (**
   * transforms a MetaSlang term to a C expression
   * op termToCExp: C_Spec -> AnnSpec.Spec -> MSTerm -> (C_Spec * C_Block * C_Exp)
   *)

  (**
   * returns the string representation of the qualified id
   * as it appears in the resulting cspec
   * op showQualifiedId: QualifiedId -> String
   *)


% --------------------------------------------------------------------------------

  op transformSpecForCodeGen  (base : Spec) (spc : Spec) : Spec =
    transformSpecForCodeGenAux base spc true

  op transformSpecForCodeGenNoAdd (spc : Spec) : Spec =  % never called?
    transformSpecForCodeGenAux emptySpec spc false  % initialSpecInCat ??

  op c_precNumSteps: List Nat = [13, 14, 15, 20, 23, 25, 27, 30, 35, 1000]
  op c_convertPrecNum (sw_prec_num : Nat) : Nat =
    case leftmostPositionSuchThat (c_precNumSteps, fn step -> sw_prec_num < step) of
     | Some i -> i 
     | None -> 10

  op jjj : Nat = 0

  op showInternals (spc : Spec) : () =
   appSpec ((fn tm  -> writeLine (printTermWithTypes tm)), 
            (fn typ -> writeLine (printType          typ)),
            (fn pat -> writeLine (printPattern       pat)))
           spc

  op showSpc (msg : String) (spc : Spec) : () =
    % let n = internalRunTime() in
    % let _ = writeLine("CG: " ^ show n ^ " " ^ msg) in
    if jjj > 0 then 
      let _ = writeLine "--------------------" in
      let _ = writeLine ("### " ^ msg)         in
      let _ = writeLine (printSpec spc)        in
      let _ = writeLine "----"                 in
      let _ = if (jjj > 1) then showInternals spc else () in
      let _ = writeLine "--------------------" in
      ()
    else
      ()

  op builtinCType? (Qualified (q, id) : QualifiedId) : Bool =
    %% If true, don't include these (and don't recur through their definitions) when slicing for code generation.
    case q of
      | "Boolean"    -> id in? ["Bool"]
      | "Integer"    -> id in? ["Int", "Int0"]
      | "Nat"        -> id in? ["Nat"]
      | "Char"       -> id in? ["Char"]
      | "String"     -> id in? ["String"]
      | _ -> false

  op builtinCOp? (Qualified (q, id) : QualifiedId) : Bool =
    %% If true, don't include these (and don't recur through their definitions) when slicing for code generation.
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

  %% TODO: deprecated...
  op C_BuiltinTypeOp? (Qualified (q, id) : QualifiedId) : Bool =
    case q of
      | "Boolean"    -> id in? ["Bool", "show", "toString"]
      | "Integer"    -> id in? ["Int", "Int0", "+", "-", "*", "div", "rem", "<=", "<", "~", ">", ">=", "**", "isucc", "ipred", "toString"]
      | "IntegerAux" -> id in? ["-"]  % unary minus
      | "Nat"        -> id in? ["Nat", "show", "toString"]
      | "Char"       -> id in? ["Char", "chr", "ord", "compare", "show"] 
      | "String"     -> id in? ["String", "compare", "append", "++", "^", "<", "newline", "length", "implode"]
      | "System"     -> id in? ["writeLine", "toScreen"]
      | "Handcoded"  -> true
      | _ -> false

  op subtract? : Bool = false  % TODO: Would like to deprecate use of subtractSpec, 
                               % setting subtract? to false still causes problems

  op removeUnusedOps (top_ops : QualifiedIds) (top_types : QualifiedIds) (spc : Spec) : Spec =
   sliceSpecForCode (spc, top_ops, top_types, builtinCOp?, builtinCType?)

  op transformSpecForCodeGenAux (basespc             : Spec)
                                (spc                 : Spec) 
                                (addmissingfrombase? : Bool)  % true in all actual calls
    : Spec =
    % let trans_table = thyMorphismMaps spc "C" c_convertPrecNum in
    let _ = if jjj > 0 then 
              % let _ = writeLine(";;; thyMorphismMaps = " ^ anyToString trans_table) in
              let _ = showSpc "Starting" spc in
              let _ = writeLine(";;; generating C code...") in
              let _ = writeLine("-----------------------------------------------------------\n\n\n") in
              let _ = writeLine("transforming spec for C code generation...") in
              let _ = writeLine("\n\n\n-----------------------------------------------------------") in
              ()
            else
              ()
    in
    let _ = showSpc "Original"                      spc in

    let (top_ops, top_types) = topLevelOpsAndTypesExcludingBaseSubsts spc in

    let spc = substBaseSpecs                        spc in %  (1) adds misc ops (possibly unused) from List_Executable.sw, String_Executable.sw, etc.
    let _ = showSpc "substBaseSpecs"                spc in

    let spc = removeUnusedOps top_ops top_types     spc in %  (2) do this early to minimize wasted motion 
    let _ = showSpc "sliceSpec[1]"                  spc in 

    let spc = 
        % note: addmissingfrombase? is true in all actual calls here
        if subtract? && addmissingfrombase? then                        
          %% TODO: deprecated...
          let spc = 
              addMissingFromBase (basespc, spc,
                                  C_BuiltinTypeOp?)     in %  (3) may add HO fns, etc., so do this before removeCurrying, etc.
          let _ = showSpc "addMissingFromBase" spc in
          spc
        else
          spc
    in  

    let spc = removeCurrying                        spc in %  (4) op f: A -> B -> C  ==>  op f_1_1: A * B -> C, etc.
    let _ = showSpc "removeCurrying"                spc in

    let spc = normalizeTopLevelLambdas              spc in %  (5) convert patterned lambdas into case expressions
    let _ = showSpc "normalizeTopLevelLambdas"      spc in

    let spc = instantiateHOFns                      spc in %  (6) calls normalizeCurriedDefinitions and simplifySpec -- should precede lambdaLift, poly2mono
    let _ = showSpc "instantiateHOFns"              spc in

   %let spc = lambdaToInner                         spc in %  ??
   %let _ = showSpc("lambdaToInner"                 spc in

    let spc = lambdaLift                     (spc,true) in %  (7) as good a time as any
    let _ = showSpc "lambdaLift"                    spc in

    let spc = translateMatch                        spc in %  (8) Wadler's pattern matching compiler -- may add calls to polymorphic fns, so must precede poly2mono
    let _ = showSpc "translateMatch"                spc in

    let spc = letWildPatToSeq                       spc in %  (9) transforms "let _ = t1 in t2" into "(t1;t2)"
    let _ = showSpc "letWildPatToSeq"               spc in
 
    let spc = specStripNonNatSubtypesAndBaseDefs    spc in % (10) should preceed poly2mono, to avoid introducing spurious names such as List_List1_Nat__Cons
    let _ = showSpc "strip subtypes"                spc in

    let spc = poly2mono                     (spc,false) in % (11) After this is called, we can no longer reason about polymorphic types such as List(a)
    let _ = showSpc "poly2mono"                     spc in
 
    let spc = translateRecordMergeInSpec            spc in % (12) rewrite forms such as foo << {y = y} to {x = foo.x, y = y, z = foo.z}
    let _ = showSpc "translateRecordMergeInSpec"    spc in

    let spc = simplifySpec                          spc in % (13) generic optimizations -- inlining, remove dead code, etc. % TODO: move to end?
    let _ = showSpc "simplifySpec"                  spc in

    let (top_ops, top_types) = topLevelOpsAndTypesExcludingBaseSubsts spc in % prior to adding eq ops, so we can later flush eq ops not reachable from these

    let spc = addEqOpsToSpec                        spc in % (14) add equality ops for sums, products, etc. -- TODO: currently adds far too many (but spliceSpec removes them)
    let _ = showSpc "addEqOpsToSpec"                spc in

    let spc = removeUnusedOps top_ops top_types     spc in % (15) remove unused ops (mainly eq ops) -- ignore subtypes, do not slice base types/ops
    let _ = showSpc "sliceSpec[2]"                  spc in 

    let (spc,constrOps) = addTypeConstructorsToSpec spc in % (16) these ops won't survive slicing, so this must follow sliceSpec
    let _ = showSpc "addTypeConstructorsToSpec"     spc in

    let spc = conformOpDecls                        spc in % (17) change def with multiple args to decompose single arg when decl has one (product) arg
    let _ = showSpc "conformOpDecls"                spc in

    let spc = adjustAppl                            spc in % (18) change call with multiple args to compose single arg when decl has one (product) arg
    let _ = showSpc "adjustAppl"                    spc in

    spc

  op topLevelOpsAndTypesExcludingBaseSubsts (spc : Spec) : QualifiedIds * QualifiedIds =
   let (base_subst_ops, base_subst_types) = substBaseSpecOpsAndTypes () in
   let ops   = filter (fn qid -> ~ (qid in? base_subst_ops)) (topLevelOps   spc) in
   let types = filter (fn qid -> ~ (qid in? base_subst_ops)) (topLevelTypes spc) in
   (ops, types)

  op generateCSpec (app_name : String) (base : Spec) (spc : Spec) : C_Spec =
    let base = substBaseSpecs base              in
    let spc  = transformSpecForCodeGen base spc in
    generateCSpecFromTransformedSpec app_name spc 

  op generateCSpecFromTransformedSpec (app_name : String) (spc : Spec) : C_Spec =
    let xcspc = emptyCSpec "" in
    generateCSpecFromTransformedSpecIncr app_name xcspc spc

  op generateCSpecFromTransformedSpecIncr (app_name : String) (xcspc : C_Spec) (spc : Spec) : C_Spec =
    let filter = (fn _ -> true) in
    generateCSpecFromTransformedSpecIncrFilter app_name xcspc spc filter

  op generateCSpecFromTransformedSpecIncrFilter (app_name : String) (xcspc : C_Spec) (spc : Spec) (filter : QualifiedId -> Bool) 
    : C_Spec =
    let useRefTypes = true                                                        in
    let constrOps   = []                                                          in
    let impunit     = generateI2LCodeSpecFilter(spc,useRefTypes,constrOps,filter) in
    let cspec       = generateC4ImpUnit(impunit, xcspc, useRefTypes)              in
    cspec

  op generateCSpecFromTransformedSpecEnv (app_name : String) (spc : Spec) : Env C_Spec =
    return (generateCSpecFromTransformedSpec app_name spc)

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
    let c_filename = basename ^ ".c" in
    let h_filename = basename ^ ".h" in
    let (h_spec, c_spec) = splitCSpec c_spec  in
    let id_dfn = ("Patched_PrismId", C_String, C_Const (C_Str basename)) in
    let c_spec = addConstDefn (c_spec, id_dfn) in  
    let c_spec = addHeader  (c_spec, app_name) in
    let c_spec = addTrailer (c_spec, app_name) in
    let h_spec = addHeader  (h_spec, app_name) in
    let h_spec = addTrailer (h_spec, app_name) in
    let c_spec = addInclude (c_spec, h_filename) in
    let _ = printCSpecToFile (h_spec, h_filename) in
    let _ = printCSpecToFile (c_spec, c_filename) in
    ()

  op printToFileEnv (app_name     : String,
                     c_spec       : C_Spec, 
                     opt_filename : Option String)
   : Env () =
   return (printToFile (app_name, c_spec, opt_filename))

  op generateCCode (app_name     : String,
                    base         : Spec, 
                    spc          : Spec, 
                    opt_filename : Option String)
    : () =
    let spc = if subtract? then subtractSpec spc base else spc in % TODO: Would like to deprecate use of subtractSpec
    let cspec = generateCSpec app_name base spc in 
    printToFile (app_name, cspec, opt_filename)

  op typeToCType (cspc : C_Spec) (spc : Spec) (typ : MSType) : C_Spec * C_Type =
    %% note: these two defaultCgContext's are very different from each other:
    let ctxt1   = default_S2I_Context                  in 
    let ctxt2   = default_I2C_Context                  in
    let tyvars  = []                                   in
    let i2lType = type2itype (tyvars, typ, ctxt1, spc) in
    c4Type(ctxt2,cspc,i2lType)

  op termToCExp (cspc : C_Spec) (spc : Spec) (tm : MSTerm) 
    : C_Spec * C_Block * C_Exp =
    let block = ([],[]) in
    termToCExpB cspc spc block tm

  op termToCExpB (cspc : C_Spec) (spc : Spec) (block : C_Block) (tm : MSTerm) 
    : C_Spec * C_Block * C_Exp =
    let ctxt1  = default_S2I_Context              in
    let ctxt2  = default_I2C_Context              in
    let i2lExp = term2expression (tm, ctxt1, spc) in
    c4Expression (ctxt2, cspc, block, i2lExp)

  def showQualifiedId (qid as Qualified (q, id) : QualifiedId) : String =
    qname2id (q, id)

  op postProcessCSpec (cspc : C_Spec) : C_Spec =
    I2LToC.postProcessCSpec cspc

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
            % let _ = writeLine ("preserving subtype of Nat: " ^ printType typ) in
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

  op specStripNonNatSubtypesAndBaseDefs (spc : Spec) : Spec =
    let stripper = stripNonNatSubtypesAndBaseDefs spc in
    mapSpec (fn t -> t, stripper, fn p -> p) spc

end-spec
