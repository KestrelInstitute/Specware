% Synchronized with version 1.11 of /SW4/Languages/MetaSlang/TypeChecker/TypeChecker.sl

(* This structure adds type checking and 
   inference to the abstract syntax tree.
      - It infers sorts of each subterm.
      - Resolves record projection from structure accessing.
 *)

(*
   TODO:

   Syntactic well-formedness checks:
        - duplicate variables in patterns
        - distinguish recursive calls.
        - capture free variables.
        - no free variables in quotient, subsorts.
        
*)

TypeChecker qualifying
spec { 
  %% The TypeChecker function is elaboratePosSpec 

  import /Library/Base
  import /Library/Legacy/DataStructures/ErrorMonad
  import Infix
  import Utilities
  import PosSpecToSpec       % for convertPSortSchemeToSortScheme

  %% ========================================================================

  sort Filename = String
  sort Message  = String

  %% ========================================================================

  % op elaboratePosSpecMaybeFail   : List Spec     * PosSpec                        -> PosSpec
  % op elaboratePosSpecReportError : List Spec     * PosSpec * Environment * String -> ErrorMonad.Result PosSpec

  op elaboratePosSpec           : PosSpec * Filename * Boolean  -> ErrorMonad.Result PosSpec

  op unlinkRec                  : PSort -> PSort
  op undeterminedSort?          : PSort -> Boolean

  op checkSort                  : LocalEnv * PSort                    -> PSort
  op elaborateSort              : LocalEnv * PSort    * PSort         -> PSort
  op elaborateCheckSortForTerm  : LocalEnv * PTerm    * PSort * PSort -> PSort 
  op elaborateSortForTerm       : LocalEnv * PTerm    * PSort * PSort -> PSort
  op elaborateTerm              : LocalEnv * PTerm    * PSort         -> PTerm
  op elaboratePattern           : LocalEnv * PPattern * PSort         -> PPattern * LocalEnv

  op mkEmbed0                   : LocalEnv * PSort         * Id            -> Option Id
  op mkEmbed1                   : LocalEnv * PSort * PTerm * Id * Position -> Option PTerm
  op lookupEmbedId              : LocalEnv * Id * PSort                    -> Option (Option PSort)
  op isCoproduct                : LocalEnv * PSort                         -> Option (List (Id * Option PSort))
  op mkProject                  : LocalEnv * Id * PSort * Position         -> Option PTerm

  op undeclared                 : LocalEnv * PTerm      * Id * PSort * Position -> PTerm
  op undeclaredResolving        : LocalEnv * PTerm      * Id * PSort * Position -> PTerm
  op undeclared2                : LocalEnv * PTerm * Id * Id * PSort * Position -> PTerm

  op pass2Error                 : LocalEnv * PSort * Message * Position         -> ()

  %% ========================================================================

  def type_nat    = natPSort
  def type_bool   = boolPSort
  def type_char   = charPSort
  def type_string = stringPSort

  % ========================================================================
  %% The TypeChecker function is elaboratePosSpec 
  %%
  %% Here is where all the various load paths from the following high-level
  %% routines converge:
  %%
  %%    ui.sl                            : SpecwareUI.loadFile  
  %%     [ui does some peculiar stuff with environment]
  %%    meta-slang-parser-semantics.lisp : parser::make-spec-as-term 
  %%    compile-all.sl                   : CompileAll.compileSpec
  %%    EvalSpec.sl                      : lEvalSpec.evaluateSpec
  %%    ...

  def elaboratePosSpec (given_spec, filename, verbose) = 
   let _ = if verbose then writeLine (";;; Elaborating spec (" ^ filename ^ ")") else () in
   let _ = initializeMetaTyVar () in
 
   %% ======================================================================
   %%                           PASS ZERO  [ 0 => 1 ]
   %% ======================================================================
 
   %% ---------- INITIALIZE SPEC (see ast-environment.sl) ----------
   %%   AstEnvironment.init adds default imports, etc.
   %%
   let env_1 = initialEnv ("??spec_name??", given_spec, filename) in
   let {importInfo = importInfo as {imports = _, importedSpec = _, localOps, localSorts},
        sorts      = sorts_0, 
        ops        = ops_0, 
        properties = props_0 
       } = given_spec
   in
 
   %% ---------- SORTS : PASS 0 ----------
   %let _ = String.writeLine "Elaborating sorts" in
   let def elaborate_sort_0
             (qualifier,sortName,
              sortInfo as (sort_names, type_vars_0, opt_def_0)) = 
        %% Sanity check on sort
        if ~(memberQualifiedId(qualifier,sortName,localSorts))
          then sortInfo
          else (sort_names, 
                type_vars_0,          
                case opt_def_0 of
                  | None       -> None
                  | Some srt_0 -> Some (checkSort (env_1, srt_0)))
   in
   %% sorts is a map to a map to sort_info
   let sorts_1 = mapiAQualifierMap elaborate_sort_0 sorts_0 in
 
   %% ---------- OPS : PASS 0 ----------
%% Identity!
%   let def elaborate_op_0 (op_name, op_info_0 : POpInfo) =
%        (case op_info_0 of
%          | (given_op_names, Nonfix, ([], (op_sort_0 as MetaTyVar _)), opt_def_0) ->
%             (if undeterminedSort? op_sort_0 then op_info_0
%             else op_info_0)
%                 %% (case lookupImportedOp (env_1.importMap, op_name) of
%                     %% | [(found_op_names, fixity, (ftvs, fsrt), _)] -> 
%                 %% TODO:  Determine appropriate use of found_op_names vs. given_op_names
%                 %%   (found_op_names, fixity, (ftvs, convertSortToPSort fsrt), opt_def_0)
%                 %% | _ -> op_info_0)
%          | _ -> op_info_0)
%   in
%   let ops_1 = map (fn m -> StringMap.mapi elaborate_op_0 m) ops_0 in                
   let ops_1 = ops_0 in

   %% ---------- PROPERTIES : PASS 0 ----------
   let props_1 = props_0 in
 
   %% ---------- SPEC AFTER PASS 0  ----------
   let spec_1 = {importInfo   = importInfo,   
                 sorts        = sorts_1, 
                 ops          = ops_1, 
                 properties   = props_1} 
   in
 
   %% ======================================================================
   %%                           PASS ONE  [ 1 => 2 ]
   %% ======================================================================
 
   %% ---------- ADD MAP FOR CONSTRUCTORS ----------
   let env_2 = addConstrsEnv (env_1, spec_1) in
 
   %% ---------- SORTS : PASS 1 ----------
   let sorts_2 = sorts_1 in
 
   %% ---------- OPS   : PASS 1 ----------
   let def elaborate_op_1 poly?
             (qualifier, op_name,
              opinfo as (op_names, fixity, (type_vars_1, srt_1), opt_def_1)) = 
        if ~(memberQualifiedId(qualifier,op_name,localOps))
          then opinfo
        else
        let srt_2 = checkSort (env_2, srt_1) in
        (op_names, 
         fixity, 
         (type_vars_1, srt_2), 
         case opt_def_1 of
           None ->  None
           | Some term_1 -> 
            % let _ = System.print term_1 in
            let term_2 = if poly? = ~(type_vars_1 = Nil)
                          then elaborateTerm (env_2, term_1, srt_2)
                         else term_1 
            in
             % TODO: Check that op sort is an instance of def sort
             Some term_2)
   in
   %% Do polymorphic definitions first
   let ops_2_a = mapiAQualifierMap (elaborate_op_1 true)  ops_1   in
   let ops_2_b = mapiAQualifierMap (elaborate_op_1 false) ops_2_a in
   let ops_2_c = mapiAQualifierMap (elaborate_op_1 true)  ops_2_b in
   let ops_2   = mapiAQualifierMap (elaborate_op_1 false) ops_2_c in
 
   %% ---------- PROPERTIES : PASS 1. ---------- 
   let def elaborate_fm_1 (prop_type, name, type_vars_1, fm_1) = 
        let type_vars_2 = type_vars_1 in
        let fm_2 = elaborateTerm (env_2, fm_1, type_bool) in
        (prop_type, name, type_vars_2, fm_2)
   in
   let props_2 = map elaborate_fm_1 props_1 in
 
   %% ---------- SPEC AFTER PASS 1  ----------
   %%  (don't need spec_2)
 
   %% ======================================================================
   %%                           PASS TWO  [ 2 => 3 ]
   %% ======================================================================
 
   %% sjw: 7/17/01 Added a second pass so that order is not so important
   let env_3 = secondPass env_2 in
 
   %% ---------- SORTS : PASS 2 ---------- 
   % let _ = String.writeLine "Elaborating sorts" in
   let def elaborate_sort_2 (qualifier, sortName,
                             sortInfo as (sort_names, type_vars_2, opt_def_2)) = 
        (sort_names, 
         type_vars_2, 
         case opt_def_2 of
          | None       -> None
          | Some srt_2 -> Some (checkSort (env_3, srt_2)))
   in
   let sorts_3 = mapiAQualifierMap elaborate_sort_2 sorts_2 
   in
 
   %% ---------- OPS : PASS 2 ---------- 
   let def elaborate_op_2 (qualifier, op_name,
                           opinfo as (op_names, fixity, (type_vars_2, srt_2), opt_def_2)) =
        if ~(memberQualifiedId(qualifier,op_name,localOps))
          then opinfo
        else
        let type_vars_3 = type_vars_2 in
        let srt_3 = checkSort (env_3, srt_2) in
        %let _ (* pos *) = sortAnn srt in
        (op_names, 
         fixity, 
         (type_vars_3, srt_3), 
         case opt_def_2 of
         | None -> None
          | Some term_2 -> 
            let pos    = termAnn term_2 in
            let term_3 = elaborateTerm (env_3, term_2, srt_3)  in
            let all_different? = checkDifferent (type_vars_3, StringSet.empty)  in
            %%  ---
            let tvpe_vars_used  =
                (let tv_cell = Ref [] : Ref TyVars in
                 let def insert tv = tv_cell := ListUtilities.insert (tv, ! tv_cell) in
                 let def record_type_vars_used (aSrt : PSort) = 
                      case aSrt of
                       | MetaTyVar (mtv,     _) -> 
                         (let {name = _, uniqueId, link} = ! mtv in
                          case link of
                           | Some s -> record_type_vars_used s
                           | None   -> error (env_3, 
                                              "Incomplete sort for op "^op_name^":"^newline
                                              ^(printSort srt_3), 
                                              pos))
                       | TyVar     (tv,      _) -> insert tv
                       | Product   (fields,  _) -> app (fn (_, s)      -> record_type_vars_used s)           fields
                       | CoProduct (fields,  _) -> app (fn (_, Some s) -> record_type_vars_used s | _ -> ()) fields
                       | Subsort   (s, _,    _) -> record_type_vars_used s
                       | Quotient  (s, _,    _) -> record_type_vars_used s
                       | Arrow     (s1, s2,  _) -> (record_type_vars_used s1; record_type_vars_used s2)
                       | PBase     (_, srts, _) -> app record_type_vars_used srts
                 in                        
                 let _ = record_type_vars_used srt_3 in
                 ! tv_cell)
            in
            let type_vars_3_b = if null type_vars_3 then
                                 tvpe_vars_used % Function was polymorphic, but not declared so.
                                else if length tvpe_vars_used = length type_vars_3 then
                                 tvpe_vars_used (* Probably correct ;-*)
                                else 
                                 let scheme = convertPSortSchemeToSortScheme (type_vars_3, srt_3)   in
                                 let scheme = printSortScheme (scheme) in
                                 (error (env_3, 
                                         "mismatch between bound and free variables "^scheme, 
                                         pos);
                                  type_vars_3)
            in                                 
            ((if all_different? then
                ()
              else 
                let scheme = convertPSortSchemeToSortScheme (type_vars_3_b, srt_3)   in
                let scheme = printSortScheme(scheme) in
                error(env_3, "Repeated sort variables contained in "^scheme, pos));
             Some term_3))
   in
   let ops_3 = mapiAQualifierMap elaborate_op_2 ops_2 
   in
 
   %% ---------- AXIOMS : PASS 2 ----------
   let def elaborate_fm_2 (prop_type, name, type_vars_2, fm_2) = 
        (let type_vars_3 = type_vars_2 in
         let fm_3 = elaborateTerm (env_3, fm_2, type_bool) in
         %String.writeLine "Elaborating formula";
         %let context = initializeTyVars() in
         %let term1 = termToMetaSlang context term in
         %let tyVars1 = deleteTyVars context tyVars in
         %let tyVars  = map unlinkTyVar tyVars in
         %let tyVars2 = deleteTyVars context tyVars in
         %let term3 = termToMetaSlang context term_3 in
         (%String.writeLine (MetaSlangPrint.printTermWithSorts term1);
          %app String.writeLine tyVars1;
          %String.writeLine (MetaSlangPrint.printTermWithSorts term3);
          %app String.writeLine tyVars2;
          (prop_type, name, type_vars_3, fm_3)))
   in
   let props_3 = map elaborate_fm_2 props_2 in
 
   %% ---------- SPEC AFTER PASS 2 ----------
   let spec_3 = {importInfo   = importInfo,   
                 sorts        = sorts_3, 
                 ops          = ops_3, 
                 properties   = props_3}
   in
   case checkErrors (env_3) of
    | None     -> Ok spec_3 : ErrorMonad.Result PosSpec
    | Some msg -> Error msg
 
 
  % ========================================================================
  %% ---- called inside SORTS : PASS 0  -----
  % ========================================================================
 
  def checkSort (env, srt) = 
 %% checkSort calls elaborateTerm, which calls checkSort
    case srt
      of TyVar _ -> srt

       | MetaTyVar (v, _) ->
         (case ! v
            of {link = Some other_sort, uniqueId, name} -> checkSort(env,other_sort)
             | _ -> srt)

       | PBase (given_sort_qid, instance_sorts, pos) ->
         (case findAllSorts (env.internal, given_sort_qid) of
           | sort_info::r -> 
             %% TODO: complain if ambiguous
             (case sort_info of (main_name::_, found_ty_vars, _) -> 
               ((if ~(length found_ty_vars = length instance_sorts) then
                   let given_sort_str =
                        (printQualifiedId main_name)
                       ^ (case instance_sorts of
                            | Nil    -> ""    
                            | hd::tl -> "("^ "??" ^ (foldl (fn (instance_sort, str) ->
                                                            str^", "^ "??")
                                                     ""
                                                     tl) 
                                        ^ ")")
                   in
                   let found_sort_str =
                        (printQualifiedId main_name)
                       ^ (case found_ty_vars of
                            | Nil    -> ""    
                            | hd::tl -> "("^ hd ^ (foldl (fn (ty_var, str) ->
                                                          str^", "^ ty_var) 
                                                   ""
                                                   tl) 
                                       ^ ")")
                   in                                
                   error (env, 
                          "Sort reference "^given_sort_str^" does not match declared sort "
                          ^found_sort_str, 
                          pos)
                 else ()); 
                PBase (main_name,
                       map (fn instance_sort -> checkSort (env, instance_sort))
                           instance_sorts, 
                       pos)))
           | [] -> 
             (let given_sort_str =
                   (printQualifiedId given_sort_qid)
                  ^(case instance_sorts of
                      | Nil    -> ""    
                      | hd::tl -> "("^ "??" ^ (foldl (fn (instance_sort, str) ->
                                                      str^", "^ "??")
                                               ""
                                               tl) 
                                 ^ ")")
                   in
              error (env, 
                     "Sort identifier in "^given_sort_str^" has not been declared", 
                     pos);
              PBase (given_sort_qid, instance_sorts, pos)))

      | CoProduct (fields, pos) ->  
        CoProduct (map (fn (id, None)   -> (id, None) 
                         | (id, Some s) -> (id, Some (checkSort (env, s))))
                       fields, 
                   pos)

      | Product (fields, pos) ->
        Product (map (fn (id, s)-> (id, checkSort (env, s))) fields,
                 pos)

      | Quotient (given_base_sort, given_relation, pos) ->
        let new_base_sort = checkSort (env, given_base_sort) in
        let new_rel_sort = Arrow (Product ([("1", new_base_sort), 
                                            ("2", new_base_sort)], 
                                           pos), 
                                  type_bool, 
                                  pos) in
        let new_relation = elaborateTerm (env, given_relation, new_rel_sort) in
        Quotient (new_base_sort, new_relation, pos)

      | Subsort (given_super_sort, given_predicate, pos) -> 
        let new_super_sort = checkSort (env, given_super_sort) in
        let new_pred_sort  = Arrow (new_super_sort, type_bool, pos) in
        let new_predicate  = elaborateTerm (env, given_predicate, new_pred_sort) in
        Subsort (new_super_sort, new_predicate, pos)

      | Arrow (t1, t2, pos) ->
        Arrow (checkSort (env, t1), checkSort (env, t2), pos)


  % ========================================================================
  %% ---- called inside OPS : PASS 0  -----
  % ========================================================================

  def undeterminedSort? srt =
   case unlinkPSort srt of
    | MetaTyVar _ -> true
    | _           -> false

  % ========================================================================
  %% ---- called inside OPS        : PASS 1 -----
  %% ---- called inside PROPERTIES : PASS 1 -----
  %% ---- called inside OPS        : PASS 2 -----
  %% ---- called inside AXIOMS     : PASS 2 -----
  %% ---- called inside CheckSort 
  % ========================================================================

  %% elaborateTerm calls aux_elaborateTerm, 
  %% which calls elaborateCheckSortForTerm, 
  %% which calls elaborateSortForTerm, 
  %% which calls unifySorts, 
  %%  which side-effects links for metaTyVar's via 

  def elaborateTerm (env, trm, term_sort : PSort) = aux_elaborateTerm (env, trm, term_sort)

  def aux_elaborateTerm (env, trm, term_sort : PSort) = 
   case trm of

    | Fun (OneName (idXXX, fixity), srt, pos) -> % ### Changed id to idXXX to avoid name conflict
      let _ = elaborateCheckSortForTerm (env, trm, srt, term_sort) in 
      (* resolve sort from environment *)
      (case findVarOrOps (env, idXXX, pos) of
        | terms as _::_ ->
          %% selectTermWithConsistentSort calls consistentSortOp?, which calls unifySorts 
          (case selectTermWithConsistentSort (env, idXXX, pos, terms, term_sort) of
            | None -> trm
            | Some term ->
              let srt = termSort term in
              let srt = elaborateCheckSortForTerm (env, term, srt, term_sort) in
              (case term of
                | Var ((idXXX, _),         pos) -> Var ((idXXX, srt),         pos)
                | Fun (OneName qidf, _, pos) -> Fun (OneName qidf, srt, pos)
                | Fun (TwoNames xx,  _, pos) -> Fun (TwoNames xx,  srt, pos)
                | _ -> System.fail "Variable or constant expected"))
        | [] -> 
          (* resolve identifier declaration from sort information *)
          (case mkEmbed0 (env, srt, idXXX) of
           | Some idXXX -> Fun (Embed (idXXX, false), checkSort (env, srt), pos)
           | None -> 
              (case mkEmbed1 (env, srt, trm, idXXX, pos) of
               | Some term -> term
               | None ->
                  (case uniqueConstr (env, trm, idXXX, pos) of
                   | Some term -> term
                   | _ -> undeclared  (env, trm, idXXX, term_sort, pos)))))


    | Fun (TwoNames (id1, id2, fixity), srt, pos) -> 
      let _ = elaborateCheckSortForTerm (env, trm, srt, term_sort) in 
      %% Either Qualified (id1, id2) or field selection
      (case findTheOp2 (env, id1, id2) of
        %% First see if Qualified (id1, id2) refers to an op
        | Some ((Qualified(qualifier,id)):: aliases, fixity, (tyvars,srt), _) ->
          %% It does. Use the canonical name for that op.
          let (_,srt) = copySort(tyvars,srt) in
          let term = Fun (TwoNames (qualifier, id, fixity), srt, pos) in
          let srt = elaborateCheckSortForTerm (env, term, srt, term_sort) in
          (case term of
            | Fun (TwoNames xx, _, pos) -> Fun (TwoNames xx, srt, pos)
            | _ -> System.fail ("Op expected for elaboration of "^id1^"."^id2^" as resolved to "^qualifier^"."^id))
        %% If that fails, check for field selection
        | None -> 
          (case findVarOrOps (env, id1, pos) of
            | [big_term] ->
              %% unqualified id1 refers to big_term
              let big_sort = termSort big_term in
              let big_sort = checkSort (env, big_sort) in
              let 
               def projectRow (big_term, big_sort, row, id2) =
                 %% See if id2 is one of the field selectors for the big sort.
                 (case row of
                  | [] -> undeclared2 (env, trm, id1, id2, term_sort, pos)
                  | (field_id, field_sort) :: row -> 
                    if id2 = field_id then
                      let field_sort = checkSort (env, field_sort) in
                      let projector : PTerm = Fun (Project id2, Arrow (big_sort, field_sort, pos), pos) in
                      let projection = (ApplyN ([projector, big_term], pos)) : PTerm in
                      let _ = elaborateSortForTerm (env, projection, field_sort, term_sort) in
                      projection
                    else
                      projectRow (big_term, big_sort, row, id2))
               def getProduct srt : Option (List (String * PSort)) = 
                 (case unfoldPSort (env, srt) of
                  | Product (row,       _) -> Some row
                  | Subsort (srt, pred, _) -> getProduct srt
                  | _ -> None)
              in          
              %% See if big_term is a product or a subsort of a product
              (case getProduct big_sort of
                | Some row -> projectRow (big_term, big_sort, row, id2)
                | None     -> undeclared2 (env, trm, id1, id2, term_sort, pos)
                | _        -> undeclared2 (env, trm, id1, id2, term_sort, pos))
            | _ -> 
              %% Both id1.id2 and id1 fail to refer to anything
              undeclared2 (env, trm, id1, id2, term_sort, pos)
             )
        | _ -> 
          %% id1.id2 is ambiguous??  That shouldn't be possible.
          undeclared2 (env, trm, id1, id2, term_sort, pos)
         )

    | Fun (Embed (id, _), srt, pos) -> 
         let _  (* srt *) = elaborateCheckSortForTerm (env, trm, srt, term_sort) in
         (case mkEmbed0 (env, term_sort, id)
            of Some id -> Fun (Embed (id,false),checkSort (env, term_sort),pos)
             | None -> 
          (case mkEmbed1 (env,term_sort,trm,id,pos)
            of Some term -> term
             | None -> undeclared (env,trm,id,term_sort,pos)))

    | Fun (Project id,srt,pos) -> 
         let srt = elaborateCheckSortForTerm (env, trm, srt, term_sort) in
         (case mkProject (env,id,srt,pos)
            of Some term -> term
             | None -> undeclaredResolving (env,trm,id,term_sort,pos))

    % | Fun (Select id,srt,pos) -> Fun (Select id,srt,pos)      (*** Not checked ***)

    | Fun (Embedded id, srt, pos) -> 
         let srt = elaborateCheckSortForTerm (env, trm, srt, term_sort) in
         ((case unfoldPSort (env, srt)
             of Arrow (dom, _, _) -> 
                 (case isCoproduct (env, dom)
                   of Some fields -> 
                      if exists (fn (id2, _) -> id = id2) fields
                            then ()
                         else
                         error
                           (env, "Name "^id^" is not among the constructors of "^
                                 printSort dom, pos)
                    | None -> 
                        pass2Error
                          (env, dom, newLines ["Sum sort with constructor "^id^" expected", 
                                             "found instead "^printSort dom], pos))
              | _ -> pass2Error (env, srt, "Function sort expected ", pos));
          Fun (Embedded id, srt, pos))

    | Fun (PChoose equiv, srt, pos) ->  (* Has sort (a -> b) -> Quotient(a, equiv) -> b *)
         let a = freshMetaTyVar pos in
         let b = freshMetaTyVar pos in
         let ty1 : PSort = Arrow (Product ([("1", a), ("2", a)], pos), type_bool, pos) in
         let equiv = elaborateTerm (env, equiv, ty1)                   in 
         let ty2 : PSort = Arrow (Quotient (a, equiv, pos), b, pos) in
         let ty3 : PSort = Arrow (a, b, pos) in
         let ty4 : PSort = Arrow (ty3, ty2, pos) in
         (elaborateSortForTerm (env, trm, ty4, term_sort);
          elaborateSortForTerm (env, trm, srt, ty4);
          Fun (PChoose equiv, srt, pos))

    | Fun (PQuotient equiv, srt, pos) ->  % Has sort a -> Quotient(a, equiv)
         let a = freshMetaTyVar pos in
         let ty1:PSort = Arrow (Product ([("1", a), ("2", a)], pos), type_bool, pos) in
         let equiv = elaborateTerm (env, equiv, ty1) in 
         let ty2: PSort = Arrow (a, Quotient (a, equiv, pos), pos) in
         (elaborateSortForTerm (env, trm, ty2, term_sort);
          elaborateSortForTerm (env, trm, srt, ty2);
          Fun (PQuotient equiv, srt, pos))  

    | Fun (Equals, srt, pos) -> 
         let a = freshMetaTyVar pos in
         let ty:PSort = Arrow (Product ([("1", a), ("2", a)], pos), type_bool, pos) in
         (elaborateSortForTerm (env, trm, ty, term_sort);
          elaborateSortForTerm (env, trm, srt, ty);
          Fun (Equals, srt, pos))

    | Fun (Bool b, srt, pos) -> 
         (elaborateSortForTerm (env, trm, type_bool, term_sort) ; 
          elaborateCheckSortForTerm (env, trm, srt, type_bool);
          Fun (Bool b, srt, pos))

    | Fun (Nat n, srt, pos) ->  
         (elaborateSortForTerm (env, trm, type_nat, term_sort);
          elaborateCheckSortForTerm (env, trm, srt, type_nat);
          Fun (Nat n, srt, pos))

    | Fun (String s, srt, pos) -> 
         (elaborateSortForTerm (env, trm, type_string, term_sort);
          elaborateCheckSortForTerm (env, trm, srt, type_string);
          Fun (String s, srt, pos))

    | Fun (Char ch, srt, pos) -> 
         (elaborateSortForTerm (env, trm, type_char, term_sort);
          elaborateCheckSortForTerm (env, trm, srt, type_char);
          Fun (Char ch, srt, pos))


    | Fun (PRelax pred, srt, pos) -> % Has sort Subsort(a, pred) -> a
         let a = freshMetaTyVar pos in
         let ty1 : PSort = Arrow (a, type_bool, pos) in
         let pred = elaborateTerm (env, pred, ty1) in
         let ty2 : PSort = Arrow (Subsort (a, pred, pos), a, pos) in
         (elaborateSortForTerm (env, trm, ty2, term_sort);
          elaborateSortForTerm (env, trm, srt, ty2);
          Fun (PRelax pred, srt, pos))
    %% FINISH THIS
    %% 
    %%          let _ = elaborateSortForTerm (env, trm, srt, term_sort) in
    %%          (Fun (PRelax, srt), pos)

    | Fun (PRestrict pred, srt, pos) -> % Has sort a -> Subsort(a, pred)
         let a = freshMetaTyVar pos in
         let ty1 : PSort = Arrow (a, type_bool, pos) in
         let pred = elaborateTerm (env, pred, ty1) in
         let ty2 : PSort = Arrow (a, Subsort (a, pred, pos), pos) in
         (elaborateSortForTerm (env, trm, ty2, term_sort);
          elaborateSortForTerm (env, trm, srt, ty2);
          Fun (PRestrict pred, srt, pos))
    %% FINISH THIS
    %%
    %        | Fun (Spec _ (* spc *), _ (* srt *), _) -> trm

    | Var ((id, srt), pos) -> 
         let srt = elaborateCheckSortForTerm (env, trm, srt, term_sort) in
         Var ((id, srt), pos)

    | LetRec (decls, body, pos) -> 
         let def declareFun (((id, srt), bdy), env) = 
              addVariable (env, id, srt)
 in
         let  def elaborateDecl env ((id, srt), bdy) = 
                    let terms = findVarOrOps (env, id, pos) in
                let srt = termSort (hd terms) in
                let bdy = elaborateTerm (env, bdy, srt) in
                ((id, srt), bdy)
 in
         let env = foldr declareFun env decls in
         let decls = map (elaborateDecl env) decls         in 
         let bdy = elaborateTerm (env, body, term_sort)                 in 
         LetRec (decls, bdy, pos)

    | Let (decls, body, pos) -> 
         let env0 = env in
         let def doDeclaration ((pat, bdy), (decls, env)) = 
               let alpha = freshMetaTyVar pos in
               (* In case the pattern is has a sort constraint, move
                  this to the body such that the sort constraint is 
                  attatched to alpha.
                  *)
               let (pat, bdy) = case pat:PPattern
                                 of SortedPat (pat, srt, pos) -> 
                                   (pat, (SortedTerm (bdy, srt, pos)):PTerm)
                                  | _ -> (pat, bdy)
               in             
               let bdy = elaborateTerm (env0, bdy, alpha) in
               let (pat, env) = elaboratePattern (env, pat, alpha) in
               (cons ((pat, bdy), decls), env)
         in         
         let (decls, env) = foldr doDeclaration ([], env) decls in
         let body = elaborateTerm (env, body, term_sort) in 
         Let (decls, body, pos)

    | IfThenElse (test, thenTrm, elseTrm, pos) -> 
          let test = elaborateTerm (env, test, type_bool) in
          let thenTrm = elaborateTerm (env, thenTrm, term_sort) in 
          let elseTrm = elaborateTerm (env, elseTrm, term_sort) in
          IfThenElse (test, thenTrm, elseTrm, pos)          


    | Record (row, pos) -> 
         let def unfoldConstraint (srt) = 
               (case unfoldPSort (env, srt)
                 of Product (rows, _) -> 
                    (if ~(length (row) = length (rows)) then
                       error (env, 
                             newLines [printTerm trm, "is incompatible with constraint", printSort term_sort], 
                             pos)
                     else 
                       ();
                     rows)
                  | MetaTyVar (mtv, _) ->
                    let row = map (fn (id, _)-> (id, freshMetaTyVar pos)) row 
 in
                      (linkMetaTyVar mtv ((Product (row, pos)):PSort);
                       row)
                        
                  | Subsort (srt, term, _) -> 
                      unfoldConstraint (srt)        

                  | sv : PSort -> 
                      (pass2Error (env, 
                                  sv, 
                                  printTerm trm^" is constrained to be of an incompatible sort "^newline^ printSort term_sort, 
                                  pos);
                       map (fn (id, _)-> (id, freshMetaTyVar pos)) row))
 in
         let tyrows = unfoldConstraint (term_sort) in
         let trow = ListPair.zip (row, tyrows) in
         let row = map (fn ((id, t), (id_, ty))->
                            if id = id_ 
                                then (id, elaborateTerm (env, t, ty))
                            else 
                            (error (env, "Field-name "^id^
            " is not the one imposed by sort constraint.  Expected field-name is: "^
                           id_, pos);
             (id, t))) trow
 in
         Record (row, pos)

    | Lambda (rules, pos) -> 
         let alpha = freshMetaTyVar pos in
          let beta  = freshMetaTyVar pos in
          let ty    = (Arrow (alpha, beta, pos)):PSort in
          let _     = elaborateSort (env, ty, term_sort) in 
          Lambda 
           (map 
             (fn (pat, cond, term)->
                 let (pat, env) = elaboratePattern (env, pat, alpha) in
                 let term = elaborateTerm (env, term, beta) in
                 let cond = elaborateTerm (env, cond, type_bool) in
                 (pat, cond, term)) 
             rules,    pos)
          

    | Bind (bind, vars, term, pos) ->
          let _ = elaborateSort (env, term_sort, type_bool) in
          let (vars, env) = 
              foldl (fn ((id, srt), (vars, env))->
                              let srt = checkSort (env, srt) in
                         (cons ((id, srt), vars), 
                          addVariable (env, id, srt)))
                          ([], env) vars 
 in
          let vars = rev vars in
             Bind (bind, vars, elaborateTerm (env, term, term_sort), 
              pos)        

    | SortedTerm (term, srt, _) ->
          let srt  = elaborateSort (env, srt, term_sort) in
          let term = elaborateTerm (env, term, srt) in
          term

    | Seq (terms, pos) -> 
          let
              def elab ts = 
                  (case ts
                    of [] -> []
                     | [t] -> [elaborateTerm (env, t, term_sort)]
                     | (t::ts) -> 
                      let alpha = freshMetaTyVar pos in
                      let t = elaborateTerm (env, t, alpha) in
                      cons (t, elab ts))
 in
              Seq (elab terms, pos) 

    | ApplyN ([t1 as Fun (Embedded _, _, _), t2], pos) -> 
          let alpha = freshMetaTyVar pos in
          let ty    = Arrow (alpha, term_sort, pos) in
          let t2    = elaborateTerm (env, t2, alpha) in
          let t1    = elaborateTerm (env, t1, ty) in
          ApplyN ([t1, t2], pos)

    | ApplyN ([t1 as Fun (Project _, _, _), t2], pos) -> 
          let alpha = freshMetaTyVar pos in
          let ty    = Arrow (alpha, term_sort, pos) in
          let t2    = elaborateTerm (env, t2, alpha) in
          let t1    = elaborateTerm (env, t1, ty) in
          ApplyN ([t1, t2], pos)

    | ApplyN ([t1 as Fun (f1, s1, _), t2], pos) -> 
          let alpha = freshMetaTyVar pos in
          let ty    = Arrow (alpha, term_sort, pos) in
          let t1    = elaborateTerm (env, t1, ty) in
          let t2    = elaborateTerm (env, t2, alpha) in
          let t1    = (if ~(env.firstPass?) & f1 = Equals
                         then adjustEqualitySort (env, s1, t1, t2)
                       else t1) in
          ApplyN ([t1, t2], pos)

    | ApplyN ([t1, t2], pos) ->
          let alpha = freshMetaTyVar pos in
          let ty    = Arrow (alpha, term_sort, pos) in
          let t2    = elaborateTerm (env, t2, alpha) in
          let t1    = elaborateTerm (env, t1, ty) in
         ApplyN ([t1, t2], pos)

    | ApplyN (terms, pos) ->
          (let def tagTermWithInfixInfo (term : PTerm) : FixatedPTerm = 
                 case term of
                  | Fun (OneName (_ ,  Infix p), _, pos) -> Infix (term, p)
                  | Fun (OneName (id, _),        _, pos) ->
                      (case consistentTag (findVarOrOps (env, id, pos)) of
                        | (true, (Some p) : (Option (Associativity * Nat))) -> Infix (term, p) % ### Why the Type?
                        | (true, _)      -> Nonfix term
                        | _ ->
                       (error (env, "Inconsistent infix information for overloaded op: " ^ id,
                              pos);
                        Nonfix term))
                  | Fun (TwoNames (_ , _, Infix p), _, pos) -> Infix (term, p)
                  | Fun (TwoNames (id1, id2, _),    _, pos) ->
                      %% If, due to union semantics, findOps always returns 0 or 1 hits for Q.Id, 
                      %% then consistentTag will necessarily return (true, priority).
                      (case findTheOp2 (env, id1, id2) of
                        | Some (_,Infix p,_,_) -> Infix  (term, p)
                        | _                    -> Nonfix term)
                  | Fun (Equals, _, _) -> Infix (term, (Left, 20))
                  | _ -> Nonfix term
           in 
           let term = resolveInfixes (tagTermWithInfixInfo, pos, terms) in
           elaborateTerm (env, term, term_sort))

    | term -> (%System.print term;
               term)

  % ========================================================================

  def selectTermWithConsistentSort (env, id, pos, terms, srt) =
   %% calls consistentSortOp?, which calls unifySorts 
   case terms of
    | [term] -> (Some term) : (Option PosSpec.PTerm)
    | _ ->
       (case unlinkPSort srt of
         | MetaTyVar _ -> None
         | rsort ->
             let srtPos = sortAnn srt in
             (case filter (consistentSortOp? (env, withAnnS (rsort, srtPos))) terms of
                | [] -> (error (env,
                          "No matches for op "^id^" of sort "^ printSort srt,
                           pos);
                             None)
                | [term]        -> Some term
                | tms ->
                   if env.firstPass? then
                     None
                   else %% If there is a valid unqualified term then prefer that because you
                        %% cannot explicitly
                     let def findUnqualified tms =
                        case tms of
                          | [] -> None
                          | tm::rtms ->
                              (case tm of
                                 |Fun (OneName  (     _,_), _, _) -> Some tm
                                 | Fun (TwoNames (id1, _,_), _, _) ->
                                    if id1 = UnQualified then
                                      Some tm
                                    else
                                      findUnqualified rtms
                                 | _ -> findUnqualified rtms)
                     in
                       (case findUnqualified tms of
                         | Some term -> Some term
                         | None ->
                             (error (env,
                                    "Several matches for overloaded op "
                                    ^ id
                                    ^ " of sort "
                                    ^ printSort srt
                                    ^ (foldl (fn (tm, str) -> str ^
                                         (case tm of
                                            | Fun (OneName  (     id2, _), _, _) -> " "^id2
                                            | Fun (TwoNames (id1, id2, _), _, _) -> " "^id1^"."^id2))
                                          " : "
                                          terms),
                              pos); None))))

  def consistentSortOp? (env, srt1) (Fun (_, srt2, _)) =
   %% calls unifySorts, but then resets metatyvar links to None...
   consistentSorts? (env, srt1, srt2)

  % ========================================================================

  def elaborateCheckSortForTerm (env, term, givenSort, expectedSort) = 
   elaborateSortForTerm (env, term, (checkSort (env, givenSort)), expectedSort)

  def elaborateSortForTerm (env, term, givenSort, expectedSort) = 
   %% unifySorts has side effect of modifying metaTyVar links
   let (success, msg) = unifySorts env givenSort expectedSort in
   ((if success then
       ()
     else
       let pos        = termAnn   term in
       let termString = printTerm term in
       let tsLength   = length termString in
       let fillerA    = blankString ((Integer.fromNat 10) - (Integer.fromNat tsLength)) in  % ### why the qualifier? why the coercion?
       let fillerB    = blankString ((Integer.fromNat tsLength) - (Integer.fromNat 10)) in
       error (env, 
             newLines [" Could not match sort constraint", 
                       fillerA ^ termString ^ " of sort " ^ printSort givenSort, 
                       fillerB ^ "with expected sort " ^ printSort expectedSort], 
             pos));
    givenSort)

   % If f : A -> B, and x : C, then for f(x) we want to see
   % an error message like:
   %
   % Could not match sort constraint
   %       x of sort C
   %       with expected sort A
   %
   % Most of the time, givenSort is C (the sort of the argument)
   % while expectedSort is A (the domain sort of the function).
   %
   % ---
   %
   % Apparently the sense of givenSort and expectedSort used to be 
   %  reversed for some obscure reason, but they seem ok now here.
   %  If there are problems, fix them elsewhere, and don't mangle 
   %  this code!
   %
   % Obsolete comment:
   %   Here, most of the time, expectedSort is C (the sort of the argument)
   %   while givenSort is A (the domain sort of the function); rather
   %   ill-chosen names.

  def elaborateSort (env, s1, s2) = 
   let s1Checked = checkSort (env, s1) in
   %% unifySorts has side effect of modifying metatyvar links
   let (success, msg) = unifySorts env s1Checked s2 in
   ((if success then
       ()
     else             
       error (env, 
              newLines ["Could not match sort " ^ printSort s1, 
                        "                with " ^ printSort s2], 
              chooseNonZeroPos (sortAnn s1, sortAnn s2)));
    s1Checked)

  def chooseNonZeroPos (p1: Position, p2: Position) : Position =
   case p1 of
    | ((0, 0), (0, 0)) -> p2
    | _                -> p1

  % ========================================================================
  %% Called inside elaborateTerm 

  def mkEmbed0 (env, srt, id) =
   case lookupEmbedId (env, id, srt) of
    | Some None -> Some id
    | _   -> None
        
  def lookupEmbedId (env, id, srt) = 
   case unfoldPSort (env, srt) of
    | CoProduct(row, _) -> 
     let def lookup row =
          case row of
           | [] -> None : Option (Option PSort)
           | (found_id, entry) :: row ->  
             if id = found_id then
               Some (case entry of
                      | None   -> None
                      | Some s -> Some (checkSort (env, s)))
             else 
               lookup row
 in
       lookup row
    | Subsort (srt, pred, _) -> lookupEmbedId (env, id, srt)
    | _ -> None

  def mkEmbed1 (env, srt, trm, id, pos) = 
   case isArrowCoProduct (env, srt) of
    | Some (sum_sort, row) ->
      let 
       %% This checks that a sum-sort constructor is given the proper sort
       def findId ls = 
        case ls of
         | [] -> Some (undeclared (env, trm, id, srt, pos))
         | (constructor_id, (Some constructor_dom_sort) : Option PSort) :: row -> 
           if id = constructor_id then
             %%  let _ = String.writeLine ("coprod: "^printSort (Arrow (s, CoProduct (row, pos0)), pos0)) in
             %%  let _ = String.writeLine ("srt:  "^printSort srt) in
             %%  let _ = String.writeLine ("srt1: "^printSort found_sort) in
             %%  let _ = String.writeLine ("dom:  "^printSort (sum_sort, pos)) in
             let constructor_dom_sort = checkSort (env, constructor_dom_sort) in
             let _ (* dom *) = elaborateSort (env, withAnnS (sum_sort, pos), constructor_dom_sort) in
             Some (Fun (Embed (id, true), checkSort (env, srt), pos))
           else 
             findId row
         | _ :: row -> findId row
 in
       findId row
    | _ -> None

  def isArrowCoProduct (env, srt) : Option (PSort * List (Id * Option PSort)) =
   case unfoldPSort (env, srt) of
    | Arrow (dom, rng, _) -> 
      (case isCoproduct (env, rng) of
        | Some row -> Some (dom, row)
        | None -> None)
    | _ -> None

  def isCoproduct (env, srt)  = 
   case unfoldPSort (env, srt) of
    | CoProduct (row, _)    -> Some row
    | Subsort   (srt, _, _) -> isCoproduct (env, srt)
    | _ -> None

  %% If id is the unique name of a constructor, use that constructor
  def uniqueConstr (env, trm, id, pos) =
   case StringMap.find (env.constrs, id) of
    | Some [srt_info] ->
      let (_, c_srt) = copySort srt_info in
      let id_srt = case c_srt of
                    | CoProduct (fields, pos) ->
                      (case find (fn (id2, _) -> id = id2) fields of
                        | Some (_, Some dom_srt) -> Arrow (dom_srt, c_srt, pos)
                        | _ -> c_srt)
                    | _ -> c_srt
 in
      (case mkEmbed0 (env, id_srt, id) of
        | Some id -> Some (Fun (Embed (id, false), checkSort (env, id_srt), pos))
        | None    -> mkEmbed1 (env, id_srt, trm, id, pos))
    | _ -> None

  def mkProject (env, id, srt, pos) = 
   case unfoldPSort (env, srt) of
    | Arrow (dom, rng, _) -> 
      (let def analyzeDom dom =
            case unfoldPSort (env, dom) of
             | Product (row, _) -> 
               (let def findId ls = 
                     case ls of
                      | [] -> None : Option PTerm
                      | (selector_id, selector_rng_srt) :: ids -> 
                          if id = selector_id then
                          (elaborateSort (env, withAnnS (rng, pos), selector_rng_srt);
                           Some (Fun (Project id, srt, pos)))
                        else 
                          findId ids
 in
                  findId row)
             | Subsort (ssrt, _, _) -> analyzeDom ssrt
             | _ -> None
       in analyzeDom dom)
    | Subsort (ssrt, _, _) -> mkProject (env, id, ssrt, pos)
    | _ -> None
      

  def consistentTag competing_pterms =
   %% If all the alternatives (found by findVarOrOps) have the same optional infix priority, 
   %% return (true, priority), otherwise return (false, None).
   %% In other words, we will complain if F or Foo.F is ambigous among terms that
   %% have differing infix priorities.
   %% Note: due to union semantics, findVarOrOps should always returns 0 or 1 hits for Q.Id, 
   %%       in which case this routine will necessarily return (true, priority).
   case competing_pterms of
    | (Fun (OneName  (_,    Infix priority), _, pos))::r -> consistentInfixPTerms (r, Some priority)
    | (Fun (TwoNames (_, _, Infix priority), _, pos))::r -> consistentInfixPTerms (r, Some priority) % r must be []
    | _::r                                               -> consistentInfixPTerms (r, None)
    | _                                                  -> (true, None)

  def consistentInfixPTerms (competing_pterms, optional_priority) = 
   case competing_pterms of
    | [] -> (true, optional_priority)
    | (Fun (OneName (_, Infix element_priority), _, pos))::tail ->
      (case optional_priority of
        | None -> (false, None)
        | Some priority -> if element_priority = priority
                            then consistentInfixPTerms (tail, optional_priority)
                            else (false, None))
    | (Fun (TwoNames (_, _, Infix element_priority), _, pos))::tail ->
      %% Union semantics should preclude multiple alternatives for Q.Id,
      %% so we should never get here.
      (case optional_priority of
        | None -> (false, None)
        | Some priority -> if element_priority = priority
                            then consistentInfixPTerms (tail, optional_priority)
                            else (false, None))
    | _::tail -> (case optional_priority of
                  | None -> consistentInfixPTerms (tail, optional_priority)
                  | _    -> (false, None))
       

  def adjustEqualitySort (env, srt, t1, eq_args) =
   case (eq_args, unlinkPSort srt) of
    | (Record ([("1", e1), ("2", e2)], _), 
       Arrow (Product ([("1", elSrt1), ("2", _)], _), _, _)) -> 
      t1
      %% This code is correct except that termSort doesn't take account of defined sorts and gives an error
         %       let
         %         def subsort? (srt1_, srt2_) = 
         %           srt1_ = srt2_
         %           or (case srt1_
         %                of Subsort ((s1_, _), _) -> subsort? (s1_, srt2_)
         %                 | _ -> false)
         %         def commonAnc (s1_, s2_) =
         %           if subsort? (s1_, s2_) then s2_ else
         %           if subsort? (s2_, s1_) then s1_ else
         %           case s1_
         %             of Subsort ((ss1_, _), _) -> commonAnc (ss1_, s2_)
         %              | _ -> s2_                        % Shouldn't happen
         %             
         % in
         %       let (s1_, s2_) = (unfold (env, termSort e1), unfold (env, termSort e2)) in
         %       let expElSrt_ = unfold (env, elSrt1) in
         %       let elSrt = if subsort? (s1_, expElSrt_) & subsort? (s2_, expElSrt_)
         %                    then elSrt1 else (commonAnc (s1_, s2_), pos) in
         %       (Fun (Equals, (Arrow ((Product [("1", elSrt), ("2", elSrt)], pos), type_bool), pos)), pos)
    | _ -> (error (env, 
                   "Illegal Equality" ^ printTerm eq_args, 
                   sortAnn srt);
            t1)


  def undeclared (env, fun, id, srt, pos) =
  if env.firstPass? then %& undeterminedSort? s 
    fun
  else
    (error (env, "Name "^id^" has not been declared", pos);
     % raise (TypeCheck (pos, "Name "^id^" has not been declared"));
     Fun (OneName (id, Nonfix), srt, pos))

  def undeclared2 (env, fun, id1, id2, srt, pos) =
  if env.firstPass? then %& undeterminedSort? s 
    fun
  else
    (error (env, id1^"."^id2^" has not been declared as a qualified name or as a field selection", pos);
     % raise (TypeCheck (pos, id1^"."^id2^" has not been declared as a qualified name or as a field selection"));
     Fun (TwoNames (id1, id2, Nonfix), srt, pos))

  def undeclaredResolving (env, fun, id, srt, pos) = 
  if env.firstPass? then %& undeterminedSort? s
    fun
  else
    (error (env, "Name "^id^" has not been declared."^" Resolving with "^printSort srt, pos);
     % raise (TypeCheck (pos, "Name "^id^" has not been declared."^" Resolving with "^printSort srt));
     (Fun (OneName (id, Nonfix), srt, pos)) : PTerm)


  % ========================================================================
  %% Called inside elaborateTerm 
  % ========================================================================

  def elaboratePattern (env, p, sort1) = 
  let sort1 = checkSort (env, sort1) in
  let def elab (p:PPattern):PPattern * LocalEnv =
    case p of
      | WildPat (s, pos) -> (WildPat (elaborateSort (env, s, sort1), pos), env)
      | BoolPat _ -> (elaborateSort (env, sort1, type_bool); (p, env))
      | NatPat _ ->  (elaborateSort (env, sort1, type_nat); (p, env))
      | StringPat _ ->  (elaborateSort (env, sort1, type_string);  (p, env))
      | CharPat _ ->  (elaborateSort (env, sort1, type_char); (p, env))
      | VarPat ((id, srt), pos) -> 
         let srt = elaborateSort (env, srt, sort1)  in 
           (case lookupEmbedId (env, id, srt) of
              | Some None -> (EmbedPat (id, None, srt, pos), env)
              | Some _ -> 
                     (error (env, "Constructor "^id^" expects an argument, but was given none", pos);
                      % raise (TypeCheck (pos, "Constructor "^id^" expects an argument, but was given none"));
                      (VarPat ((id, srt), pos), env))
              | None ->
                 if undeterminedSort? srt then
                   (case StringMap.find (env.constrs, id) of
                     | None ->
                          (VarPat ((id, srt), pos), addVariable (env, id, srt))
                     | Some [srt_info] ->
                                 let (_, c_srt) = copySort srt_info in
                                 (VarPat ((id, c_srt), pos), env)
                     | Some _ -> (VarPat ((id, srt), pos), env))
                 else
                   (VarPat ((id, srt), pos), addVariable (env, id, srt)))
              | SortedPat (pat, srt, _) -> 
                let srt = elaborateSort (env, srt, sort1) in
                let (p, env) = elaboratePattern (env, pat, srt) in
                (p, env)
              | AliasPat (pat1, pat2, pos) ->
                let (pat1, env) = elaboratePattern (env, pat1, sort1) in
                let (pat2, env) = elaboratePattern (env, pat2, sort1) in
                (AliasPat (pat1, pat2, pos), env)
              | EmbedPat (embedId, pattern, sort0, pos) ->
                let sort0 = elaborateSort (env, sort0, sort1) in
                let sort0 =
                  if undeterminedSort? sort0 then
                    % See if there is only one constructor with this name
                    (case StringMap.find (env.constrs, embedId) of
                      | Some [srt_info] ->
                          let (_, c_srt) = copySort srt_info in
                          elaborateSort (env, c_srt, sort1)
                      | _ -> sort0)
                  else
                   sort0
                 in
                   if env.firstPass? & undeterminedSort? sort0 then
                    (EmbedPat (embedId, pattern, sort0, pos), env)
                   else
                    let srt = lookupEmbedId (env, embedId, sort0) in
                    let (env, pat):LocalEnv * Option (PPattern) = 
                      (case (srt, pattern) of
                        | (Some (Some srt), Some pat) -> 
                           let (pat, env) = elaboratePattern (env, pat, srt) in
                             (env, Some pat)
                         
                        | (Some None, None) -> (env, None)
                        | (None, None) -> 
                            (error (env, "Sort for constructor "
                                     ^ embedId
                                     ^ " not found. Resolving with sort "
                                     ^ printSort sort1, pos);
                              (env, None))
                        | (None, Some pat) -> 
                          let alpha = freshMetaTyVar pos in
                          let (pat, env) = elaboratePattern (env, pat, alpha)
 in
                              (error (env, "Sort for constructor "
                                      ^ embedId
                                      ^ " not found. Resolving with sort "
                                      ^ printSort sort1, pos);
                               (env, None))
                         | (Some None, Some pat) -> 
                              (error (env, newLines ["Constructor "
                                      ^ embedId
                                      ^ " takes no argument", 
                                        "but was given "
                                      ^ printPattern pat], pos);
                              (env, Some pat))
                         | (Some (Some _), None) -> 
                              (error (env, "Argument expected for constructor "
                                        ^ embedId, pos);
                               (env, None)))
                     in
                       (EmbedPat (embedId, pat, sort1, pos), env)
          | RecordPat (row, pos) ->
            let r = map (fn (id, srt)-> (id, freshMetaTyVar pos)) row in
            let _ = elaborateSort (env, (Product (r, pos)):PSort, sort1) in
            let r = ListPair.zip (r, row) in
            let (r, env) = 
                   foldr (fn (((id, srt), (_, p)), (row, env))->
                           let (p, env) = elaboratePattern (env, p, srt) in
                           (cons ((id, p), row), env)) ([], env) r
 in
                (RecordPat (r, pos), env)
          | RelaxPat (pat, term, pos) -> 
            let term = elaborateTerm (env, term, 
                                     Arrow (sort1, type_bool, pos)) in
            let sort2 = (Subsort (sort1, term, pos)):PSort in
            let (pat, env) = elaboratePattern (env, pat, sort2) in
            (RelaxPat (pat, term, pos), env)
          | QuotientPat (pat, term, pos) ->
            let v = freshMetaTyVar pos in
            let sort2 = (Quotient (v, term, pos)):PSort in
            let _ = elaborateSort (env, sort2, sort1) in
            let term = elaborateTerm (env, term, 
                                     Arrow (Product ([("1", v), ("2", v)], pos), 
                                           type_bool, pos)) in
            let (pat, env) = elaboratePattern (env, pat, v) in
            (QuotientPat (pat, term, pos), env)
          | p -> (System.print p; System.fail "Nonexhaustive")
            
 in
  let (p, env) = elab p in
  (p, env)

  % ========================================================================

  def pass2Error (env, _(* s *), msg, pos) =
  if env.firstPass? %& undeterminedSort? s
    then ()
    else error (env, msg, pos)

  def blankString (n:Integer) =
   if n <= (Integer.fromNat 0) then 
     "" 
   else
   let oneHundredSpaces = "                                                                                                    " in
   if n < (Integer.fromNat 100) then
     substring (oneHundredSpaces, 0, (Nat.toNat n))
   else
     oneHundredSpaces ^ blankString (n - (Integer.fromNat 100))

  def newLines lines = 
   case lines of
    | [] -> ""
    | [line] -> line
    | line :: lines -> 
      line ^ Char.toString (Char.chr 10) ^ "          " ^ (newLines lines)
     
  %% ---- called inside OPS : PASS 2  -----

  def checkDifferent (tvs : TyVars, setOfUniqueIds) =
   case tvs of
    | []      -> true
    | id::tvs ->  
        if StringSet.member(setOfUniqueIds, id) then
          false
        else 
          checkDifferent (tvs, StringSet.add (setOfUniqueIds, id))
}
