SpecToLisp qualifying spec

import /Languages/MetaSlang/CodeGen/DebuggingSupport

import /Languages/MetaSlang/Transformations/MetaTransform

import /Languages/MetaSlang/CodeGen/Generic/CodeGenTransforms
import /Languages/MetaSlang/CodeGen/Generic/PatternMatch
import /Languages/MetaSlang/CodeGen/Generic/InstantiateHOFns
import /Languages/MetaSlang/CodeGen/Generic/LambdaLift
import /Languages/MetaSlang/CodeGen/Generic/RemoveCurrying
import /Languages/MetaSlang/CodeGen/Generic/DeconflictUpdates
import /Languages/MetaSlang/CodeGen/Generic/LiftSequences

import /Languages/MetaSlang/CodeGen/Stateful/StatefulUpdates
import /Languages/MetaSlang/CodeGen/Stateful/IntroduceSetfs
import /Languages/MetaSlang/CodeGen/Stateful/Globalize

import /Languages/MetaSlang/CodeGen/Lisp/SliceForLisp

import /Languages/Lisp/Lisp

import /Library/Structures/Data/Maps/SimpleAsSTHarray

type FileName     = String
type PackageName  = String
type PackageNames = List PackageName
type Arity        = Option (MSType * Nat)

op slPos : Position = Internal "SpecToLisp"

op generateCaseSensitiveLisp? : Bool = true
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op lispPackages : PackageNames = 
 ["LISP", "COMMON-LISP", 
  %% Added because of Xanalys packages, but prudent anyway
  "SYSTEM", "SI", "IO", "BOOTSTRAP",
  %% Added for cmulisp compatibility
  "ALIST", "BYTES", "HASH", "HASHTABLE", "SEQ"]

op lispStrings : StringSet =
 foldr add 
       emptyMap 
       (["NIL", "T", "CONS", "NULL", "CAR", "CDR", "LIST", "LISP", 
         "APPEND", "REVAPPEND", "REVERSE", "COMPILE", "REDUCE", 
         "SUBSTITUTE", "COUNT", "ENCLOSE", "EVAL", "ERROR", "FIRST", "LAST", 
         "SECOND", "THIRD", "FOURTH", "FIFTH", "SIXTH", 
         "SEVENTH", "EIGHTH", "NINTH", "TENTH", 
         "UNION", "INTERSECTION", "SET", "SETQ", "SETF", "SOME", 
         "ARRAY", "POP", "PUSH", "TOP", "REMOVE", "GET", 
         "REPLACE", "PI", "DELETE", "IDENTITY", "REM", 
         "NTH", "EQ", "EQL", "EQUAL", "ZEROP", "ODDP", "EVENP", 
         "SEARCH", "COMPILE", "MERGE", "RETURN", 
         "VECTOR", "SVREF", "FORALL", "EXISTS", "SETF", "LOOP", 
         "OR", "AND", "NOT", "LENGTH", "MAP", "MEMBER", "TIME", 
         "CHAR", "STRING", "SYMBOL", "NAT", "MAKE-STRING", 
         "CONST", "IF", "APPLY", "QUOTE", "MIN", "GO", 
         "PRINT", "READ", "WRITE", "LOAD", "..", 
         "BLOCK", "FORMAT", "BREAK", "SUBST", "FIND", "CLASS", 
         "+", "++", "**", "-", "*", ">", "<", "<=", ">= ", "\\=", 
         "BOOLEAN", "INTEGER", "SHADOW", "TRACE", "WHEN"]
          ++ lispPackages)

op notReallyLispStrings : Strings =
 ["C", "D", "I", "M", "N", "P", "S", "V", "X", "Y", "Z", "KEY", "NAME", "VALUE", "PATTERN"]

op lispString? (id : Id) : Bool = 
 member? (id, lispStrings)
 ||
 %% The above is only necessary for packages. They should be done differently in next release.
 (uncell (findSymbol (id, "CL"))
  && 
  id nin? notReallyLispStrings)

op lispPackage? (id : Id) : Bool =
 let pkg = apply (symbol ("CL", "FIND-PACKAGE"), [string id]) in
 uncell pkg
 && 
 uncell (apply (symbol ("CL", "PACKAGE-NAME"), [pkg])) in? lispPackages

op [a] ith (n : Nat, id : String, ids : List (String * a)) : Nat =
 case ids of
   | [] -> fail ("No such index " ^ id)
   | (id2, _) :: ids -> 
     if id = id2 then
       n 
     else 
       ith (n + 1, id, ids)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  StringSet maps var names to Bool
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type StringSet = STHMap.Map (String, Bool)

op member? (s : String, sset : StringSet) : Bool =
 case apply (sset, s) of
   | Some b -> b
   | _  -> false

op add (s : String, sset : StringSet) : StringSet =
 update (sset, s, true)

op addList (strings : Strings, sset : StringSet) : StringSet =
 foldr add sset strings

%% op difference (S1: StringSet, S2: StringSet) : StringSet =
%%  foldi (fn (x, y, S) -> if y then remove (S, x) else S) S1 S2

%% Domain is qualification. First set is strings as given, second is upper case version
op userStringMap : Ref (STHMap.Map (String, (Ref StringSet) * (Ref StringSet))) =
 Ref emptyMap

op initializeSpecId () : () =
 (userStringMap := emptyMap)
       
op lookupSpecId (id : String, ID : String, pkg : String) : String =
 case apply (! userStringMap, pkg) of

   | Some (userStrings, userUpper) ->
     if member? (ID, ! userUpper) then
       if member? (id, ! userStrings) then
         id
       else 
         "|!" ^ id ^ "|"
     else 
       (userUpper   := add (ID, ! userUpper);
        userStrings := add (id, ! userStrings);
        id)

   | _ -> 
     (userStringMap := update (! userStringMap, pkg, 
                               (Ref (add (id, emptyMap)), 
                                Ref (add (ID, emptyMap))));
      id)

op specId (id : String, pkg : String) : String = 
 let id =
     if forall? (fn #|  -> false
                  | #`  -> false
                  | #'  -> false
                  | #\\ -> false
                  | _   -> true)
                id
       then 
         id                        % Test is redundant, but translate is expensive even if identity
     else 
       translate (fn #|  -> "\\|" 
                   | #`  -> "\\`"
                   | #'  -> "\\'"
                   | #\\ -> "\\\\" 
                   | ch  -> show ch)
                 id
 in
 let upper_ID = map toUpperCase id                                  in
 let ID       = if generateCaseSensitiveLisp? then id else upper_ID in
 if lispString? upper_ID || id@0 = #! then
   "|!" ^ id ^ "|"
 else if exists? (fn ch -> ch = #:) id then
   "|"  ^ id ^ "|"
 else 
   lookupSpecId (id, upper_ID, pkg)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op projectionIndex (sp : Spec, id : Id, ty : MSType) : Nat = 
 let (dom, _) = arrow   (sp, ty)  in
 let row      = product (sp, dom) in
 ith (0, id, row)

op optSpecialProjection (sp : Spec, ty : MSType, id : Id) : Option String = 
 case stripSubtypes (sp, ty) of
   | Arrow (dom, _, _) -> 
     (case stripSubtypes (sp, dom) of

        | Product ([(id1, _), (id2, _)], _) -> 
          Some (if id1 = id then "car" else "cdr")

        | Product ([(id1, _)], _) ->	% Unary record
          Some "functions::id"

        | _ -> None)

   | _ -> None

op optConsDataType (sp : Spec, ty : MSType) : Option (Id * Id) =
 let
   def isTwoTuple (ty : MSType) = 
     case stripSubtypes (sp, ty) of
       | Product ([_, _], _) -> true 
       | _ -> false
 in
 case stripSubtypes (sp, ty) of
   | CoProduct ([(Qualified(_,"None"), None), (Qualified(_,"Some"), Some _)], _) -> None 
     
   % Options never get to be cons types.
   % This is required to make boot strapping work
   % as hash-quote-spec prints options without optimization.
     
   | CoProduct ([(Qualified(_,i1), None  ), (Qualified(_,i2), Some s)], _) -> if isTwoTuple s then Some (i1, i2) else None
   | CoProduct ([(Qualified(_,i2), Some s), (Qualified(_,i1), None  )], _) -> if isTwoTuple s then Some (i1, i2) else None
   | _ -> None
    

op hasConsEmbed? (sp : Spec, ty : MSType) : Bool = 
 case stripSubtypes (sp, ty) of
   | Arrow (_, rng, _) -> 
     (case optConsDataType (sp, rng) of
        | Some _ -> true
        | _      -> false)
   | _ -> false

op optConsIdentifier (sp : Spec, id : Id, ty : MSType) : Option String = 
 case optConsDataType (sp, ty) of
   | Some (i1, i2) -> Some (if id = i1 then "null" else "consp")
   | _  -> None

op optConsDomain (sp : Spec, id : Id, ty : MSType) : Option String = 
 case stripSubtypes (sp, ty) of
   | Arrow (dom, _, _) -> 
     (case optConsDataType (sp, dom) of
        | Some (i1, i2) -> Some (if id = i1 then "null" else "consp")
        | _ -> None)
   | _ -> None

op listTerm (tm : MSTerm, sp : Spec) : Option MSTerms =
 case tm of
   | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkTuple"), _), _, _),
            Record ([(_, x), 
                     (_, y)], 
                    _), 
            _) 
     ->
     (case y of

        | Fun (Embed (id, false), ty, _) | some? (optConsDataType (sp, ty)) ->
          Some [x]

        | Apply (Fun (Embed (id, true), ty, _), cdr_arg, _) | some? (optConsDataType (sp, range (sp, ty))) ->
          (case listTerm(cdr_arg, sp) of
             | Some r_list_args -> Some(x :: r_list_args)
             | _ -> None)

        | _ -> None)       
   | _ -> None


op patternName (pattern : MSPattern) : Id = 
 case pattern of
   | VarPat        ((id, _), _) -> id
   | RestrictedPat (p, _,    _) -> patternName p
   | _ -> 
     fail ("SpecToLisp.patternName " ^ printPattern pattern)

op patternNames (pattern : MSPattern) : List1 Id = 
 case pattern of
   | VarPat    ((id, _), _) -> [id] 
   | RecordPat (fields,  _) -> map (fn (_, p) -> patternName p) fields
  %| RestrictedPat(p,_,_) -> patternNames p
   | _ -> 
     fail ("SpecToLisp.patternNames " ^ printPattern pattern)

op defaultSpecwarePackage : String = 
 if generateCaseSensitiveLisp? then
   "SW-User"
 else 
   "SW-USER"

op mkLPackageId (id : String) : PackageName = 
 if id = UnQualified then 
   defaultSpecwarePackage
 else
   let upper_id = map Char.toUpperCase id                             in
   let id       = if generateCaseSensitiveLisp? then id else upper_id in
   if lispString? upper_id || lispPackage? upper_id then
     id ^ (if generateCaseSensitiveLisp? then "-Spec" else "-SPEC")
   else 
     id
      
% see Suppress.sw
op printPackageId (name as Qualified (pack, id) : QualifiedId, 
                   default_package_name         : String) 
 : String = 
 case (pack, id) of
   | ("System", "time") -> "TIME"
   | _ ->
     let pkg = mkLPackageId pack in
     if pkg = default_package_name then
       specId (id, "") % !!!
     else
       (pkg ^ "::" ^ specId (id, pkg))
      
op opArity (sp : Spec, op_name : OpName, ty : MSType) : Arity =
 case typeArity (sp, ty) of
   | None -> None
   | arity ->
     if polymorphicDomainOp? (sp, op_name) then
       None
     else 
       arity

op compareSymbols : LispTerm = mkLOp "eq"

op mkLispTuple (valTms : LispTerms) : LispTerm =
 case valTms of
   | []     -> mkLBool false         % Nil
   % Named tuples can be unary
   | [x]    -> x
   | [_, _] -> mkLApply (mkLOp "cons",   valTms)
   | _      -> mkLApply (mkLOp "vector", valTms)
     
op unaryName (name : String) : String = name  % ^ "-1"

op naryName (Qualified (q, id)    : QualifiedId, 
             arity                : Nat,
             default_package_name : PackageName)
 : String =
 let new_id = id ^ "-" ^ show arity in
 printPackageId (Qualified (q, new_id), default_package_name)

op mkLUnaryFnRef (id     : String, 
                  arity  : Arity,
                  varset : StringSet) 
 : LispTerm =
 if member? (id, varset) then 
   mkLVar id
 else 
   case arity of
     | Some _ -> mkLOp (unaryName id)
     | _      -> mkLOp id

op mkLApplyArity (id                   : QualifiedId, 
                  default_package_name : PackageName, 
                  arity                : Arity, 
                  varset               : StringSet, 
                  args                 : LispTerms) 
 : LispTerm =
 let pid = printPackageId (id, default_package_name) in
 let rator = if member? (pid, varset) then 
               mkLVar pid
             else 
               case arity of
                 | Some _ ->
                   let n = length args in
                   if n = 1 then
                     mkLOp (unaryName pid)
                   else
                     mkLOp (naryName (id, n, default_package_name))
                 | _ -> mkLOp pid
 in 
 mkLApply (rator, args)

%
% Ad hoc optimization of the equality operation.
%
op mkLEqualityOp (sp : Spec, ty : MSType) : String = 
 case stripSubtypes (sp, ty) of
   | Arrow (dom, _, _) -> 
     (case stripSubtypes (sp, dom) of
        | Product ([(_, s), _], _) -> 
          if natType? s then         % intType? s
            "="
          else
            (case stripSubtypes (sp, s) of
               | Boolean _                                    -> "eq"
               | Base (Qualified ("Nat",     "Nat"),    _, _) -> "="
               | Base (Qualified ("Integer", "Int"),    _, _) -> "="
               | Base (Qualified ("String",  "String"), _, _) -> "string="
               | Base (Qualified ("Char",    "Char"),   _, _) -> "eq"
               | _ -> "Slang-Built-In::slang-term-equals-2")
        | _ -> "Slang-Built-In::slang-term-equals-2")
   | _ -> "Slang-Built-In::slang-term-equals-2"

%
% Ad hoc optimization of the inequality operation.
%
op mkLInEqualityOp (sp  : Spec, ty : MSType) : String = 
 case stripSubtypes (sp, ty) of  
   | Arrow (dom, _, _) -> 
     (case stripSubtypes (sp, dom) of
        | Product ([(_, s), _], _) -> 
          if natType? s then     % intType?(s)
            "/="
          else
            (case stripSubtypes (sp, s) of
               | Boolean _                                    -> "Slang-Built-In:boolean-term-not-equals-2"
               | Base (Qualified ("Nat",     "Nat"),    _, _) -> "/="
               | Base (Qualified ("Integer", "Int"),    _, _) -> "/="
               | Base (Qualified ("String",  "String"), _, _) -> "Slang-Built-In:string-term-not-equals-2"  % careful! string/= won't work
               | Base (Qualified ("Char",    "Char"),   _, _) -> "char/="
               | _ -> "Slang-Built-In::slang-term-not-equals-2")
        | _ -> "Slang-Built-In::slang-term-not-equals-2")
   | _ -> "Slang-Built-In::slang-term-not-equals-2"

op [a] mkLTermOp (sp                   : Spec,
                  default_package_name : PackageName,
                  varset               : StringSet,
                  term_op              : MSFun * MSType * a,
                  optArgs              : Option MSTerm)
 : LispTerm =
 let
   def mk_lisp_term varset tm =
     mkLTerm (sp, default_package_name, varset, tm)
 in
 case term_op of

   | (Project id, ty, _) -> 
     (case (optSpecialProjection (sp, ty, id), optArgs) of

        | (Some proj, None) -> 
          mkLLambda (["!x"], [], 
                     mkLApply (mkLOp proj, 
                               [mkLVar "!x"]))

        | (Some proj, Some trm) ->
          let lTrm = mk_lisp_term varset trm in
          if proj = "functions::id" then
            lTrm
          else 
            mkLApply (mkLOp proj, 
                      [lTrm])

        | (None, Some trm) -> 
          let id = projectionIndex (sp, id, ty)  in
          mkLApply (mkLOp "svref", 
                    [mk_lisp_term varset trm, 
                     mkLNat id])

        | (None, None) -> 
          let id = projectionIndex (sp, id, ty) in
          mkLLambda (["!x"], [], 
                     mkLApply (mkLOp "svref", 
                               [mkLVar "!x", 
                                mkLNat id]))
          )

   | (Not, ty, _ ) ->
     let oper = mkLOp "cl:not" in
     (case optArgs of
        %| None -> oper  
        | Some arg -> mkLApply (oper, mkLTermList (sp, default_package_name, varset, arg)))
     
   | (And, ty, _ ) ->
     % Note: And ("&&") is non-strict -- it might not evalute the second arg.
     %       This means it is not commutative wrt termination.
     let oper = mkLOp ("cl:and") in  % lisp AND is also non-strict
     (case optArgs of
        %| None -> oper  % TODO: is this situation possible? Given note above, should it be allowed?
        | Some arg -> mkLApply (oper, mkLTermList (sp, default_package_name, varset, arg)))
     
   | (Or, ty, _ ) ->
     % Note: Or ("||") is non-strict -- it might not evalute the second arg
     %       This means it is not commutative wrt termination.
     let oper = mkLOp ("cl:or") in  % lisp OR is also non-strict
     (case optArgs of
        %| None -> oper  % TODO: is this situation possible? Given note above, should it be allowed?
        | Some arg -> mkLApply (oper, mkLTermList (sp, default_package_name, varset, arg)))
     
   | (Implies, ty, _ ) ->
     % Note: Implies ("=>") is non-strict -- it might not evalute the second arg.
     %       This means it is not commutative (to the contrapositive) wrt termination.
     (case optArgs of
        | Some (Record ([(_, x), (_, y)], _)) ->
          % "x => y" = "if x then y else true" = "or (~ x, y)"
          mkLApply (mkLOp ("cl:or"),         
                    [mkLApply (mkLOp "cl:not", 
                               [mk_lisp_term varset x]), 
                     mk_lisp_term varset y])
        %| None -> mkLOp ("Slang-Built-In:implies-2") % TODO: is this situation possible? Given note above, should it be allowed?
        )

   | (Iff, ty, _ ) ->
     % Note: Iff ("<=>") is strict, becasue the second arg must be evaluated, no matter what the value of the first arg is.
     %       This means it is commmuative wrt termination.
     (case optArgs of
        %| None -> mkLOp ("cl:eq") % presumably boolean-valued args each evaluate to T or NIL, so this should be ok.
        | Some (Record ([(_, x), (_, y)], _)) ->
          % "x => y" = "if x then y else ~ y"
          mkLIf (mk_lisp_term varset x, 
                 mk_lisp_term varset y, 
                 mkLApply (mkLOp "cl:not", 
                           [mk_lisp_term varset y])))

   | (Equals, ty, _) ->
     let oper = mkLOp (mkLEqualityOp (sp, ty)) in
     (case optArgs of
        %| None -> oper
        | Some arg -> mkLApply (oper, 
                                mkLTermList (sp, default_package_name, varset, arg)))
     
   | (NotEquals, ty, _) ->
     (case optArgs of
        %| None -> mkLOp (mkLInEqualityOp (sp, ty))
        | Some arg -> 
          %% for efficiency, open-code the call to not
          %% let ineq_op = mkLOp (mkLInEqualityOp (sp, ty)) in
          %% mkLApply (ineq_op, mkLTermList (sp, default_package_name, varset, arg)))
          let eq_oper = mkLOp (mkLEqualityOp (sp, ty)) in
          mkLApply (mkLOp "cl:not", 
                    [mkLApply (eq_oper, 
                               mkLTermList (sp, default_package_name, varset, arg))]))
     
   | (Select (Qualified(_,id)), ty, _) -> 
     (case (optConsDomain (sp, id, ty), optArgs) of
        | (Some queryOp, None)      -> mkLLambda (["!x"], [], mkLVar "!x")
          
        | (Some queryOp, Some term) -> mkLTerm (sp, default_package_name, varset, term)
          
        | (None,         None)      -> mkLOp "cdr"
          
        | (None,         Some term) -> mkLApply (mkLOp "cdr", 
                                                 [mkLTerm (sp, default_package_name, varset, term)]))
     
   | (Embedded (Qualified(_,id)), ty, _) -> 
     let dom = domain (sp, ty) in
     (case (optConsIdentifier (sp, id, dom), optArgs) of
        | (Some queryOp, None)      -> mkLLambda (["!x"], [], 
                                                  mkLApply (mkLOp queryOp, 
                                                            [mkLVar "!x"]))
          
        | (Some queryOp, Some term) -> mkLApply (mkLOp queryOp, 
                                                 [mkLTerm (sp, default_package_name, varset, term)])
          
        | (None,         None)      -> mkLLambda (["!x"], 
                                                  [], 
                                                  mkLApply (compareSymbols, 
                                                            [mkLApply (mkLOp "car", 
                                                                       [mkLVar "!x"]), 
                                                             mkLIntern id]))
        | (None,         Some term) -> mkLApply (compareSymbols, 
                                                 [mkLApply (mkLOp "car", 
                                                            [mkLTerm (sp, default_package_name, varset, term)]), 
                                                  mkLIntern id])
          )
     
   | (Nat    n, ty, _) -> mkLInt    n
   | (String s, ty, _) -> mkLString s
   | (Bool   b, ty, _) -> mkLBool   b
   | (Char   c, ty, _) -> mkLChar   c
     
   | (f as Op (qid, _), ty, a) ->
     (case qid of
        | Qualified ("TranslationBuiltIn", "mkFail") ->
          mkLApply(mkLOp "error",case optArgs of Some term -> mkLTermList(sp, default_package_name, varset, term))
        | _ ->
      case constructorFun?(f, ty, sp) of
        | Some cf -> mkLTermOp(sp, default_package_name, varset, (cf, ty, a), optArgs)
        | None -> 
          let arity = opArity (sp, qid, ty) in
          (case optArgs of
             | None ->
               let pid = printPackageId (qid, default_package_name) in
               if functionType? (sp, ty) then
                 mkLUnaryFnRef (pid, arity, varset)
               else 
                 Const (Parameter pid)
             | Some term ->
               mkLApplyArity (qid, default_package_name, arity, varset, 
                              mkLTermList (sp, default_package_name, varset, term))))
     
   | (Embed (Qualified(_,id), true), ty, _) ->
     let rng = range (sp, ty) in
     (case optConsDataType (sp, rng) of
        | Some _ ->
          (case optArgs of
             | None -> mkLLambda (["!x"], [], mkLVar "!x")
             | Some term -> 
               case listTerm(term, sp) of
                 | Some list_args ->
                   let l_list_args = map (fn t -> mkLTerm (sp, default_package_name, varset, t)) list_args in
                   mkLApply(mkLOp "list", l_list_args)
                 | _ -> mkLTerm (sp, default_package_name, varset, term))
        | _ -> 
          let id = mkLIntern id in
          (case optArgs of
             | None -> mkLLambda (["!x"], [], 
                                  mkLApply (mkLOp "cons", 
					    [id, mkLVar "!x"]))
             | Some term -> 
               mkLApply (mkLOp "cons", [id, mkLTerm (sp, default_package_name, varset, term)])))
     
   | (Embed (Qualified(_,id), false), ty, _) -> 
     (case optConsDataType (sp, ty) of
        | Some _ -> mkLBool false
        | _      -> mkLApply (mkLOp "list", [mkLIntern id]))
     
   | (Quotient qid, ty, _) -> 
     (case findAllTypes (sp, qid) of
        | [info] ->
          (case unpackFirstTypeDef info of
             | (tvs, Quotient (_, equiv, _)) ->
               let equiv = mkLTerm (sp, default_package_name, varset, equiv) in
               (case optArgs of
                  | Some term -> 
                    mkLApply (mkLOp "Slang-Built-In::quotient-1-1", 
                              [equiv, mkLTerm (sp, default_package_name, varset, term)])
                  | _ -> 
                    mkLApply (mkLOp "Slang-Built-In::quotient", 
                              [equiv]))
             | x -> 
               fail ("Internal confusion in mkLTermOp: expected quotient " ^ show qid ^ " to name a quotient type, saw: " ^ anyToString x))
        | x -> 
          fail ("Internal confusion in mkLTermOp: expected quotient " ^ show qid ^ " to name one quotient type, but saw: " ^ anyToString x))
     
   | (Choose qid, ty, _) ->  
     (case findAllTypes (sp, qid) of
        | [info] ->
          (case unpackFirstTypeDef info of
             | (tvs, Quotient _) ->
               %% Don't need the equivalence relation when doing a choose
               (case optArgs of
                  | None      -> mkLApply (mkLOp "Slang-Built-In::choose", 
                                           [])
                  | Some term -> mkLApply (mkLOp "Slang-Built-In::choose-1", 
                                           [mkLTerm (sp, default_package_name, varset, term)]))
             | x -> 
               fail ("Internal confusion in mkLTermOp: expected choose " ^ show qid ^ " to name a quotient type, saw: " ^ anyToString x))
        | x -> 
          fail ("Internal confusion in mkLTermOp: expected choose " ^ show qid ^ " to name one quotient type, but saw: " ^ anyToString x))

   % Restrict and relax are implemented as identities
      
   | (Restrict, ty, _) -> 
     (case optArgs of
        | Some term -> mkLTerm (sp, default_package_name, varset, term)
        | _ -> mkLLambda (["!x"], [], mkLVar "!x"))
     
   | (Relax, ty, _) -> 
     (case optArgs of
        | None -> mkLLambda (["!x"], [], mkLVar "!x")
        | Some term -> mkLTerm (sp, default_package_name, varset, term))

   | mystery -> fail ("In mkLTermOp, unexpected termOp: " ^ (anyToString mystery))

op typeOfOp (sp : Spec, name : QualifiedId) : MSType =
 case findTheOp (sp, name) of
   | Some info -> 
     firstOpDefInnerType info
   | _ -> fail ("Undefined op: " ^ show name)

op fullCurriedApplication (sp                   : Spec,
                           default_package_name : String, 
                           varset               : StringSet, 
                           term                 : MSTerm)
 : Option LispTerm =
 let 

   def aux (term, i, args) =
     case term of

       | Fun (Op (id, _), ty, _) ->
         %% Note that we use typeOfOp(sp, id) instead of ty because may be polymorphic with instantiation to a fn type
         if i > 1 && i = curryShapeNum (sp, typeOfOp(sp, id)) 
           then
             Some (mkLApply (mkLOp (unCurryName (id, i, default_package_name)), 
                             map (fn t -> 
                                    mkLTerm (sp, default_package_name, varset, t)) 
                                 args))
         else 
           None
           
       | Fun (Choose _, _, _) ->
         if i = 2 then
           case args of
             | [f, val] ->
               if identityFn? f then
                 Some (mkLApply (mkLOp "Slang-Built-In::quotient-element", 
                                 [mkLTerm (sp, default_package_name, varset, val)]))
               else 
                 Some (mkLApply (mkLOp "Slang-Built-In::choose-1-1", 
                                 [mkLTerm (sp, default_package_name, varset, f), 
                                  mkLTerm (sp, default_package_name, varset, val)]))
             | _ -> None % shouldn't happen
         else 
           None
           
       | Apply (t1, t2, _) -> aux (t1, i+1, t2::args)
               
       | _ -> None

 in 
 aux (term, 0, [])


op mkLTermList (sp                   : Spec, 
                default_package_name : String, 
                varset               : StringSet, 
                term                 : MSTerm) 
 : LispTerms = 
 case term of
   | Record (fields, _) -> 
     map (fn (_, tm) -> 
            mkLTerm (sp, default_package_name, varset, tm)) 
         fields
   | _ -> 
     [mkLTerm (sp, default_package_name, varset, term)]

%% Make a special op for the message format to ensure that terms built by mkLTerm 
%% can be recognized by warn_about_non_constructive_defs
op non_constructive_format_msg : LispTerm =
  mkLString "Non-constructive Term: ~A~%       where ~{~A = ~S~^, ~}"

op mkLTerm (sp                   : Spec, 
            default_package_name : PackageName, 
            varset               : StringSet, 
            term                 : MSTerm) 
 : LispTerm = 
 let
   def mk_lisp_term varset tm =
     mkLTerm (sp, default_package_name, varset, tm)

   def mk_lisp_terms varset tms =
     map (mk_lisp_term varset) tms

 in
 case fullCurriedApplication (sp, default_package_name, varset, term) of
   | Some lTerm -> lTerm
   | _ ->
     case term of
       
       | Fun termOp -> mkLTermOp (sp, default_package_name, varset, termOp, None)
         
       | Var ((id, ty), _) -> 
         let id = specId (id, "") in
         if member? (id, varset) then
           Var id 
         else
           Op id
           
       | Let (decls, body, _) ->
         let (pats, terms) = unzip decls                          in
         let names         = map patternName                pats  in
         let names         = map (fn id -> specId (id, "")) names in
         mkLLet (names, 
                 mk_lisp_terms varset                    terms, 
                 mk_lisp_term  (addList (names, varset)) body)
         
       | LetRec (decls, term, _) ->
         let
           def unfold (decls, names, terms) = 
             case decls of
               | [] -> (names, terms)
               | (name, term) :: decls -> 
                 unfold (decls,name::names, term::terms)
                    
         in
         let (names, terms) = unfold (decls, [], [])                    in
         let names          = map (fn (id, _) -> specId (id, "")) names in
         let varset         = foldl remove varset names                 in
         % let varset = StringSet.difference (varset, StringSet.fromList names) in
         
         %% Letrec bound names are to be treated as op-refs and not var-refs 
         
         mkLLetRec (names, 
                    mk_lisp_terms varset terms, 
                    mk_lisp_term  varset term)
         
       | Apply (t1, Apply (Fun (Restrict, _, _), t2, _), a) ->
         mk_lisp_term varset (Apply (t1, t2, a))
         
       | Apply (t1, Apply (Fun (Relax, _, _), t2, _), a) ->
         mk_lisp_term varset (Apply (t1, t2, a))
         
       %% Forced tuples are translated to tuples by translating the argument to mkLTuple recursively
       
       | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkTuple"), _), _, _), 
                term, 
                _) 
         -> 
         mk_lisp_term varset term

       %% Functions of arity different from 1 are wrapped in an apply when given only 1 argument

       | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkApply"), _), _, _), 
                Record ([(_, t1), (_, t2)], _),
                _) 
         -> 
         mkLApply (mkLOp "apply", 
                   [mk_lisp_term varset t1, 
                    mk_lisp_term varset t2])
         
       | Apply (term, term2 as Record (fields, _), _) ->
         (case term of
            | Fun termOp -> 
              mkLTermOp (sp, default_package_name, varset, termOp, Some term2)
            | _ -> 
              let terms = map (fn (_, tm) -> mk_lisp_term varset tm) fields in
              mkLApply (mk_lisp_term varset term, 
                        terms))         
         
       | Apply (t1, t2, _) ->
         (case t1 of
            
            | Fun termOp -> 
              mkLTermOp (sp, default_package_name, varset, termOp, Some t2)
              
            | Var ((id, ty), _) ->
              let id = specId (id, "") in
              if member? (id, varset) then
                mkLApply (mk_lisp_term varset t1, 
                          [mk_lisp_term varset t2])
              else 
                mkLApply (mkLOp id, 
                          [mk_lisp_term varset t2])
                
            | _ -> 
              mkLApply (mk_lisp_term varset t1,
                        [mk_lisp_term varset t2]))
         
       | Record (fields, _) ->
         mkLispTuple (map (fn (_, tm) -> mk_lisp_term varset tm) fields)
         
       | IfThenElse (t1, t2, t3, _) -> 
         mkLIf (mk_lisp_term varset t1, 
                mk_lisp_term varset t2,
                mk_lisp_term varset t3)
         
       | Lambda ([(pat, cond, body)], _) ->
         let names = patternNames pat                     in 
         let names = map (fn id -> specId (id, "")) names in
         mkLLambda (names, 
                    [], 
                    mk_lisp_term (addList (names, varset)) body)
         
       | Seq (terms, _) ->
         mkLSeq (mk_lisp_terms varset terms)
         
       | TypedTerm (tm, _, _) ->
         mk_lisp_term varset tm 

       | _ -> 
         let pos    = termAnn term             in
         let tm_str = printTerm_OnOneLine term in
         (%% System.warn ("Non-constructive term " ^ (printIfExternal pos) ^ ": " ^ tm_str);
          %%
          %% The overall effect of the code constructed here
	  %% is to produce something like this at runtime:
	  %%
	  %%   In the following, n = 33, f = "testing"
	  %%   Error: Non-constructive Term: fa(i : Nat) i < n => embed?(Some)(f i)
	  %%
	  %% A nice side effect is that the free varset in this term will appear as
	  %% used lisp varset (the even positions in the name/value list), so the 
	  %% lisp compiler will not spuriously warn about them being unused.
	  %%
	  let free_varset = map (fn (id,_) -> specId (id, "")) (freeVars term) in
	  mkLApply (mkLOp "cl:error",
                    [%% The following lisp format string says to successively 
                     %% take two things from the argument list and then:
                     %%  print the first (a string) using ~A (so no surrounding quotes),
		     %%  print the second (a value) using ~S (so use quotes, etc.),
		     non_constructive_format_msg,       % cf. warn_about_non_constructive_defs
		     mkLString tm_str,
		     %% The following will produce a form something like 
		     %% (list "aa" aa "foo" foo" xyz "xyz")
		     %% At lisp runtime, that creates a (heterogenous!) list with 
		     %% the name of each var followed by the value it is bound to.
		     mkLApply (mkLOp "list",
                               foldl (fn (args, id) ->
                                        args ++ [mkLString id, Var id])
                                     []
                                     free_varset)]))

op printTerm_OnOneLine (term : MSTerm) : String = 
 let s = toString (format (8000, 
                           ppTerm (initialize (asciiPrinter, false))
                                  ([], Top) 
                                  term))
 in
 let 

   def whitespace? char = 
     char = #\s || char = #\n || char = #\t

   def compress (chars, have_whitespace?) =
     %% avoid deep recursions...
     let (chars, _) = 
         foldl (fn ((chars, have_whitespace?), char) ->
                  if whitespace? char then
                    if have_whitespace? then
                      (chars, have_whitespace?)
                    else
                      ([#\s] ++ chars, true)
                  else
                    ([char] ++ chars, false))
               ([], true)
               chars
     in
     reverse chars
 in
 implode (compress (explode s, true))

	 
%% Poor man's optimizer. 
%%  Takes care of unnecessary redexes generated by compiler.

%
% Count occurrences up to at most 2
%
op countOccurrence2 (x : String, count : Nat, terms : LispTerms) : Nat = 
 case terms of
   | [] -> count 
   | term :: terms -> 
     case term of
       | Apply (t1, terms1) -> 
         countOccurrence2 (x, count, Cons (t1, terms1 ++ terms))
         
       | Lambda (vars, _, body) -> 
         %% Was: 2 (* give up *) 
         %% Never do a real subsitution within a lambda body, but if there are no 
         %% occurences, return count of 0 to trigger vacuous
         %% subsitution that allows us to drop unused arg.
         if x in? vars || countOccurrence2 (x, 0, [body]) = 0 then
           countOccurrence2 (x, count, terms)		% Captured
         else 
           2 (* give up because may be called more than once *)
           
       | Letrec (vars, terms1, body) -> 
         %% Was: 2 (* give up *)
         %% Similar to Lambda case
         if x in? vars || countOccurrence2 (x, 0, [body]) = 0 then
           countOccurrence2 (x, count, body::terms1 ++ terms)
         else 
           2
           
       | Let (vars, terms1, body) -> 
         countOccurrence2 (x, count, body::terms1 ++ terms)
         
       | If     (t1, t2, t3) -> countOccurrence2 (x, count, [t1, t2, t3] ++ terms)
       | IfThen (t1, t2)     -> countOccurrence2 (x, count, [t1, t2]     ++ terms)
       | Seq    terms1       -> countOccurrence2 (x, count, terms1       ++ terms)
         
       | Var y -> 
         if x = y then 
           if count > 0 then 
             2 
           else
             countOccurrence2 (x, count + 1, terms)
         else countOccurrence2 (x, count, terms)
           
       | _ -> countOccurrence2 (x, count, terms)
      
op getNames (term : LispTerm) : Strings =
 case term of
   | Apply   (t1, terms)         -> foldr (fn (t, names) -> getNames t ++ names) (getNames t1) terms
   | Lambda  (vars, _, t)        -> vars ++ (getNames t)
   | Op      r                   -> [r]
   | Var     r                   -> [r] 
   | Const   _                   -> []
   | If      (t1, t2, t3)        -> (getNames t1) ++ (getNames t2) ++ (getNames t3)
   | IfThen  (t1, t2)            -> (getNames t1) ++ (getNames t2)
   | Let     (vars, terms, body) -> vars ++ (flatten (map getNames terms)) ++ (getNames body)
   | Letrec  (vars, terms, body) -> vars ++ (flatten (map getNames terms)) ++ (getNames body)
   | Seq     terms               -> flatten (map getNames terms)
   | _ -> System.fail "Unexpected term in getNames"
      
op rename (old : String, 
           (vars  : Strings, 
            names : Strings, 
            body  : LispTerm)) 
 : Strings * Strings * LispTerm =
 if exists? (fn name -> name = old) names then
   let new  = newName (old, names) in
   let body = substitute (old, mkLVar new) body in
   (new :: vars, 
    new :: names, 
    body)
 else 
   (old :: vars, names, body)

op rename2 (old : String,
            (vars  : Strings, 
             terms : List (LispTerm), 
             names : Strings, 
             body  : LispTerm))
 : Strings * List (LispTerm) * Strings * LispTerm =
 if exists? (fn name -> name = old) names then
   let new   = newName (old, names)                in 
   let lvar  = mkLVar new                          in
   let body  = substitute (old, lvar) body         in 
   let terms = map (substitute (old, lvar)) terms  in
   (new::vars, terms, new::names, body)
 else 
   (old::vars, terms,      names, body)

op substitute (x : String, arg : LispTerm) (body : LispTerm) : LispTerm =
 let 
   def subst_in_decls decls =
     case arg of
       | Var new_var ->
         map (fn decl ->
                case decl of
                  | Ignore ignored_varset -> 
                    Ignore (map (fn ignored_var -> 
                                   if ignored_var = x then 
                                     new_var
                                   else 
                                     ignored_var)
                                ignored_varset))
             decls
       | _ -> decls
 in
 case body of
   
   | Apply (term, terms) -> 
     Apply (substitute (x, arg) term, 
            map (substitute (x, arg)) terms)
     
   | Lambda (vars, decls, body) -> 
     if exists? (fn v -> x = v) vars then
       mkLLambda (vars, decls, body) 
     else
       let names               = getNames arg                        in
       let (vars, names, body) = foldr rename ([], names, body) vars in
       mkLLambda (vars, 
                  %% we might be renaming a var, in which case
                  %% any decls referring to it must be updated
                  subst_in_decls decls, 
                  substitute (x, arg) body)
       
   | Var y -> if x = y then arg else mkLVar y
     
   | Let (vars, terms, body) -> 
     if exists? (fn v -> x = v) vars then
       mkLLet (vars, 
               map (substitute (x, arg)) terms, 
               body)
     else 
       let terms               = map (substitute (x, arg)) terms     in
       let names               = getNames arg                        in
       let (vars, names, body) = foldr rename ([], names, body) vars in
       mkLLet (vars, 
               terms, 
               substitute (x, arg) body)
       
   | Letrec (vars, terms, body) -> 
     if exists? (fn v -> x = v) vars then
       mkLLetRec (vars, terms, body)
     else 
       let names = getNames arg                    in
       let terms = map (substitute (x, arg)) terms in
       let (vars, terms, names, body) = 
           foldr rename2 
                 ([], terms, names, body) 
                 vars
       in
       mkLLetRec (vars, 
                  terms, 
                  substitute (x, arg) body)
       
   | If (t1, t2, t3) -> 
     mkLIf (substitute (x, arg) t1, 
            substitute (x, arg) t2, 
            substitute (x, arg) t3)
     
   | IfThen (t1, t2) -> 
     IfThen (substitute (x, arg) t1, 
             substitute (x, arg) t2)
     
   | Seq ts -> 
     mkLSeq (map (substitute (x, arg)) ts)
     
   | _ -> body
     

op simpleTerm? (term : LispTerm) : Bool = 
 case term of
   | Var   _              -> true
   | Const (Parameter nm) -> ~(testSubseqEqual?("Global::", nm, 0, 0))
   | Const _              -> true
   | Op    _              -> true
   | _                    -> false
      

op pure? (term : LispTerm) : Bool = 
 case term of
   | Var    _                   -> true
   | Const (Parameter nm)       -> ~(testSubseqEqual?("Global::", nm, 0, 0))
   | Const  _                   -> true
   | Op     _                   -> true
   | Lambda _                   -> true
   | Apply (Op "cdr",    terms) -> forall? pure? terms % Selector from data type constructors.
   | Apply (Op "car",    terms) -> forall? pure? terms % Selector from tuple.
   | Apply (Op "svref",  terms) -> forall? pure? terms % Projection from record
   | Apply (Op "vector", terms) -> forall? pure? terms % Tuple formation
   | Apply (Op "cons",   terms) -> forall? pure? terms % Tuple formation
   | _                          -> false
      
  
op pV? (var_name : String) : Bool =
 case explode var_name of
   |       #p :: #V :: digits -> forall? isNum digits % lexer gets upset if no space between "::#"
   | #a :: #p :: #V :: digits -> forall? isNum digits
   | _ -> false

op reduceTerm (term : LispTerm) : LispTerm = 
 case term of

   | Apply (Lambda (xs, _, body), args) -> reduceTerm (Let (xs, args, body))
     
   | Apply (term, terms) -> 
     let term  = reduceTerm term      in
     let terms = map reduceTerm terms in
     %% DELETED 6/7/00 nsb to make choose and quotient compile correctly.
     %% Where is this relevant?
     %% let (* Ops need an argument *)
     %%   def etaExpandOp (term : LispTerm) = 
     %%    case term of
     %%      | Op _ -> mkLLambda (["!x"], [], mkLApply (term, [mkLVar "!x"]))
     %%      | _ -> term
     %% in 
     %  let terms = map etaExpandOp terms in
     mkLApply (term, terms)
           
   | Lambda (vars, decls, body) -> 
     let reduced_body = reduceTerm body in
     let unused_and_unignored_pv_vars = 
         foldr (fn (var_name, unused_vars) ->
                  if (%% internally generated?
                        %% For user-defined varset, we do NOT want add an ignore decl, 
                        %% as that would hide useful debugging information.
                        (pV? var_name)
                        &&
                        %% unused?
                        (countOccurrence2 (var_name, 0, [reduced_body]) = 0) 
                        &&
                        %% not already in an ignore declaration?
                        %% (can happen if there are multiple passes through reduceTerm)
                        ~(exists? (fn decl ->
                                     case decl of
                                       | Ignore ignored_names ->
                                         exists? (fn ignored_name -> var_name = ignored_name) 
                                         ignored_names
                                       | _ -> false)
                            decls) 
                        &&
                        %% duplications among the varset probably shouldn't happen, 
                        %% but it doesn't hurt to double-check
                        var_name nin? unused_vars)
                    then 
                      var_name :: unused_vars
                  else 
                    unused_vars)
               []      
               vars
     in
     let augmented_decls = 
         case unused_and_unignored_pv_vars of
           | [] -> decls
           | _  -> Ignore unused_and_unignored_pv_vars :: decls
     in
     mkLLambda (vars, augmented_decls, reduced_body)

   %
   % Optimized by deleting pure arguments that do not
   % occur in the body at all.
   %
   | Let (xs, args, body) -> 
     let body  = reduceTerm body     in
     let args  = map reduceTerm args in
     let xArgs = zip (xs, args)      in
     %
     % Count along multiplicity of a variable in the let bound arguments.
     % This prevents capture in sequential substitution.
     % ?? Example please...
     %
     let terms = body::args in
     let xNumArgs = 
         map (fn (x, arg) ->
                if simpleTerm? arg then
                  %% If arg is a constant, why do we not substitute if
                  %%  there are 2 or more occurrences of the var among 
                  %%  the args (ignoring the body)?
                  %% Why not always substitute? (I.e. return count of 0 or 1)
                  %% Is this related to the capture issue above?
                  (x, countOccurrence2 (x, 0, args),  false, arg)
                  
                else if pure? arg then
                  (x, countOccurrence2 (x, 0, terms), false, arg)
                  
                else if countOccurrence2 (x, 0, terms) > 0 then
                  %% arg has possible side effects, and var is used, 
                  %% so leave it in place and don't substitute into body
                  (x, 2, false, arg)
                  
		     else
		       %% arg has possible side effects, 
		       %% but var is never used, so convert to sequence
		       (x, 2, true, arg)) 
             xArgs                              
     in
     let (xs, args, body)  = 
         foldr (fn ((x, num, convert_to_seq?, arg), (xs, args, body)) -> 
		  %% If num = 0, then x and arg will vanish from result.
		  %% This happens only if arg is pure or simpleTerm.
		  if num < 2 then
		    (xs, 
		     args, 
		     substitute (x, arg) body)
		  else if convert_to_seq? then
		    %% "let _ = xxx in yyy" => "(xxx ; yyy)"
		    (xs, 
		     args, 
		     mkLSeq [arg, body])
                  else
                    (x::xs, 
                     arg::args, 
                     body)) 
               ([], [], body) 
               xNumArgs
     in
     mkLLet (reverse xs, reverse args, body)

   | Letrec (vars, terms, body) -> 
     mkLLetRec (vars, map reduceTerm terms, reduceTerm body)

   | If (t1, t2, t3) -> 
     mkLIf (reduceTerm t1, reduceTerm t2, reduceTerm t3)

   | IfThen (t1, t2) -> 
     IfThen (reduceTerm t1, reduceTerm t2)

   | Seq (terms) -> mkLSeq (map reduceTerm terms)

   | l -> l
                          
op lispTerm (sp                   : Spec,
             default_package_name : PackageName,
             term                 : MSTerm) 
 : LispTerm = 
 reduceTerm (mkLTerm (sp, default_package_name, emptyMap, term))

op functionType? (sp : Spec, ty : MSType) : Bool = 
 case unfoldBase (sp, ty) of
   | Arrow   _         -> true
   | Subtype (s, _, _) -> functionType? (sp, s)
   | _                 -> false

op genNNames (n : Nat) : Strings = 
 tabulate (n, fn i -> "x" ^ show i)

op nTupleDerefs (n : Nat, vr : LispTerm) : LispTerms = 
 if n = 2 then 
   [mkLApply (mkLOp "car", [vr]), 
    mkLApply (mkLOp "cdr", [vr])]
 else 
   tabulate (n, 
             fn i -> 
               mkLApply (mkLOp "svref", 
                         [vr, mkLNat i]))

op duplicateString (n : Nat, s : String) : String =
 case n of
   | 0 -> ""
   | _ -> s ^ duplicateString (n - 1, s)

op unCurryName (Qualified (q, id) : QualifiedId,
                n                 : Nat,
                default_package_name : PackageName)
 : String =
 let new_id = id ^ duplicateString (n, "-1") in
 printPackageId (Qualified (q, new_id),
                 default_package_name)

%% fn x -> fn (y1, y2) -> fn z -> bod --> fn (x, y, z) let (y1, y2) = y in bod
op unCurryDef (term : LispTerm, n : Nat) : Option LispTerm =
 let 
   def auxUnCurryDef (term, i, params, let_binds) =
     if i > n then 
       Some (reduceTerm (mkLLambda (params, 
                                    [], 
                                    foldl (fn (bod, (vars, vals)) ->
                                             mkLLet (vars, vals, bod))
                                          term 
                                          let_binds)))
     else
       case term of
         | Lambda (formals, _, body) ->
           (case formals of
              
              | [_] -> 
                auxUnCurryDef (body, 
                               i+1, 
                               params ++ formals, 
                               let_binds)
              | _ -> 
                let newParam = "!x" ^ (Nat.show i) in
                auxUnCurryDef (body, 
                               i+1, 
                               params ++ [newParam], 
                               [(formals, 
                                 nTupleDerefs (length formals, 
                                               mkLVar newParam))]
				 ++ 
				 let_binds))
           
	   %% Lets are effectively pushed inwards
         | Let (vars, terms, body) ->
           auxUnCurryDef (body, 
                          i, 
                          params, 
                          [(vars, terms)] ++ let_binds)
           
         | _ -> None        
 in 
 auxUnCurryDef (term, 1, [], [])

% fn (x, y, z) -> f-1 (tuple (x, y, z))
op defNaryByUnary (name : String, n : Nat) : LispTerm =
 let vnames = genNNames n in
 reduceTerm (mkLLambda (vnames, 
                        [], 
                        mkLApply (mkLOp (name), 
                                  [mkLispTuple (map mkLVar vnames)])))

% fn (x, y, z) -> f-1 (tuple (x, y, z))
op defAliasFn (name : String, n : Nat) : LispTerm =
 let vnames = genNNames n in
 reduceTerm (mkLLambda (vnames, 
                        [], 
                        mkLApply (mkLOp (name), 
                                  map mkLVar vnames)))

% fn x -> f (x.1, x.2, x.3)
op defUnaryByNary (name : String, n : Nat) : LispTerm =
 reduceTerm (mkLLambda ([if n = 0 then "ignore" else "x"], 
                        if n = 0 then [Ignore ["ignore"]] else [], 
                        mkLApply (mkLOp name, 
                                  nTupleDerefs (n, mkLVar "x"))))

% fn x1 -> fn ... -> fn xn -> name (x1, ..., xn)
op defCurryByUncurry (name : String, n : Nat) : LispTerm =
 let 
   def auxRec (i, args) =
     if i > n then 
       mkLApply (mkLOp name, args)
     else 
       let vn = "x" ^ (Nat.show i) in
       reduceTerm (mkLLambda ([vn], 
                              [], 
                              auxRec (i+1, args ++ [mkLVar vn])))
 in 
 auxRec (1, [])

% fn (x1, ..., xn) -> f x1 ... xn
op defUncurryByUnary (name : String, n : Nat) : LispTerm =
 let 
   def auxRec (i, args, bod) =
     if i > n then 
       reduceTerm (mkLLambda (args, [], bod))
     else 
       let vn = "x" ^ (Nat.show i) in
       auxRec (i + 1, 
               args ++ [vn], 
               mkLApply (bod, [mkLVar vn]))
 in 
 auxRec (1, [], mkLOp name)

op renameDef? (term : LispTerm) : Option String =
 case term of
   | Lambda ([v], _, Apply (Op fnName, [Var vr])) ->
     if v = vr then 
       Some fnName 
     else 
       None
   | _ -> None

op indexTransforms? : Bool = true

op extract_getter_setters (spc : Spec) : List (String * String) =
 %% TODO: The relevant axioms and theorems are get sliced away before this point,
 %%       so setf_entries is empty.  (Sigh)

 let 
   def uncurried_name (Qualified (q, id), arg_counts) =
     let new_id = foldl (fn (id, n) -> id ^ "-" ^ show n) id arg_counts in
     printPackageId (Qualified (q, new_id), defaultSpecwarePackage)
 in

 let setf_entries   = findSetfEntries spc in
 let getter_setters = map (fn entry ->
                             (uncurried_name (entry.accesser_name, entry.accesser_arg_counts),
                              uncurried_name (entry.updater_name,  entry.updater_arg_counts)))
                          setf_entries
 in
 % let _ = writeLine ("==to lisp==") in
 % let _ = writeLine ("setf_entries   = " ^ anyToString setf_entries) in
 % let _ = writeLine ("getter_setters = " ^ anyToString getter_setters) in
 % let _ = writeLine ("====") in
 getter_setters

op extract_forms (spc: Spec) : LispTerms =
 if ~indexTransforms? || none?(findTheType(spc, Qualified("MetaTransform", "AnnTypeValue"))) then 
   []
 else
   let tr_infos = generateAddTransformUpdates spc in
   map (fn (Qualified(q, nm), (ty_info, fn_tm)) ->
        let q_ty_info = Const (Cell (cell ty_info))                         in
        let name      = mkQualifiedId ("MetaTransform", "addTransformInfo") in
        let fn_tm     = translateMatchInTerm spc name fn_tm                 in
        let fn_ltm    = lispTerm (spc, defaultSpecwarePackage, fn_tm)       in  
        Set ("MetaTransform::transformInfoMap",
             mkLApply(mkLOp "MetaTransform::addTransformInfo-4", 
                      [mkLString q, mkLString nm, q_ty_info, fn_ltm])))
       tr_infos

op lisp (slice : Slice) : LispSpec =

 %% For now, we ignore everything about the slice execpt the spec itself.

 %let _ = describeSlice ("lisp gen", slice) in
 let spc = slice.ms_spec in
 %let _ = printSpecToTerminal spc in
 
 let _        = initializeSpecId ()                   in
 let packages = map mkLPackageId (qualifiers spc.ops) in
 
 %% Make defaultSpecwarePackage be the standard package name rather than some random package
 
 let (defPkgName, extraPackages) = (defaultSpecwarePackage, packages) in
 
 let
   def mkLOpDef (q, id, info, defs) = 
     let op_name = Qualified (q, id) in
     foldl (fn (defs, dfn) -> 
              let (tvs, ty, term) = unpackFirstTerm dfn in
              if anyTerm? term then 
                defs     % Maybe should give a warning
              else
                % let _ = writeLine("lopdef: "^id^"\n"^printTerm term^"\n"^printTerm dfn) in
                let term  = lispTerm  (spc, defPkgName, term)            in
                let uName = unaryName (printPackageId (op_name, defPkgName)) in
                let new_defs =
                    if functionType? (spc, ty) then
                      (case (curryShapeNum (spc, ty), typeArity (spc, ty)) of

                         | (1, None) ->
                           (case term of
                              | Lambda (formals, _, _) -> 
                                [(uName, term)]
                              | _ -> 
                                [(uName, mkLLambda (["!x"], [], 
                                                    mkLApply (term, [mkLVar "!x"])))])

                         | (1, Some (_, arity)) ->
                           let nName = naryName (op_name, arity, defPkgName) in
                           (case term of
                              | Lambda (formals, _, _) ->
                                let n = length formals in
                                [(nName, if n = arity then 
                                           term
                                         else 
                                           defNaryByUnary (uName, arity)),                 % fn (x, y, z) -> f-1 (tuple (x, y, z))
                                 (uName, if n = arity then
                                           defUnaryByNary (nName, n)                       % fn x -> f (x.1, x.2, x.3)
                                         else 
                                           term)]
                              | _ ->  
                                %% Not sure that arity normalization hasn't precluded this case
                                [(nName, defNaryByUnary (uName, arity)),            % fn (x, y, z) -> f-1 (tuple (x, y, z))
                                 (uName, mkLLambda (["!x"], [], 
                                                    mkLApply (term, [mkLVar "!x"])))])

                         | (curryN, None) ->
                           let ucName = unCurryName (op_name, curryN, defPkgName) in
                           (case unCurryDef (term, curryN) of
                              | Some uCDef ->                                       % fn x -> fn y -> fn z -> f-1-1-1 (x, y, z)
                                [(uName,  defCurryByUncurry (ucName, curryN)), 
                                 (ucName, uCDef)]
                              | _ ->
                                [(uName,  term), 
                                 (ucName, case renameDef? term of
                                            | Some equivFn ->                               % fn (x, y, z) -> equivFn-1-1-1 ( x, y, z)
                                              %% Questionable call to unCurryName
                                              defAliasFn (unCurryName (Qualified (defPkgName, equivFn), 
                                                                       curryN, 
                                                                       defPkgName), 
                                                          curryN)
                                            | _ ->                                          % fn (x, y, z) -> f x y z
                                              defUncurryByUnary (uName, curryN))])
                           
                         | (curryN, Some (_, arity)) ->
                           let ucName = unCurryName (op_name, curryN, defPkgName) in
                           let nName  = naryName    (op_name, arity,  defPkgName) in
                           (case unCurryDef (term, curryN) of
                              | Some uCDef ->
                                [(nName,  defNaryByUnary    (uName,  arity)),        % fn (x, y, z) -> f-1 (tuple (x, y, z))
                                 (uName,  defCurryByUncurry (ucName, curryN)),       % fn x -> fn y -> fn z -> f-1-1-1 (x, y, z)
                                 (ucName, uCDef)]
                              | _ ->
                                (case term : LispTerm of
                                   | Lambda (formals, _, _) ->
                                     let n = length formals in
                                     [(nName,  if n = arity then 
                                                 term
                                               else 
                                                 defNaryByUnary (uName, arity)),            % fn (x, y, z) -> f-1 (tuple (x, y, z))
                                      (uName,  if n = arity then
                                                  defUnaryByNary (nName, n)                  % fn x -> f (x.1, x.2, x.3)
                                                else 
                                                  term), 
                                       (ucName, defUncurryByUnary (uName, curryN))]  % fn (x, y, z) -> f-1 x y z
                                    | _ ->
                                      [(nName,  defNaryByUnary (uName, arity)),       % fn (x, y, z) -> f-1 (tuple (x, y, z))
                                       (uName,  mkLLambda (["!x"], [], 
                                                           mkLApply (term, [mkLVar "!x"]))), 
                                       (ucName, defUncurryByUnary (uName, curryN))])))
                     else 
                       [(uName, term)]
                 in
                 new_defs ++ defs)
            defs
            (case opInfoDefs info of
               | main_def :: _ -> [main_def]
               | _ -> 
                 if q = "Global" then
                   [Record ([], slPos)]  % to get (defvar Global.xxx nil)
                 else
                   [])
 in
 let opnames = 
     case filter (fn op_qid -> definedOp?(spc, op_qid)) (opsInImplementation slice) of
       | [] -> 
         let _ = writeLine("No defined ops found in implementation slice, so using all ops") in
         foldriAQualifierMap (fn (q, id, info, opnames) ->
                                mkQualifiedId (q, id) :: opnames)
                             []
                             spc.ops
       | opnames_in_slice -> 
         opnames_in_slice 
 in
 let defs = foldl (fn (defs, opname as Qualified(q,id)) ->
                     case findTheOp (spc, opname) of
                       | Some op_info -> mkLOpDef (q, id, op_info, defs) 
                       | _ -> 
                         if q = "TranslationBuiltIn" then 
                           defs
                         else 
                           let _ = writeLine("Could not find op " ^ show opname) in 
                           defs)
                  []
                  opnames
 in

 let _ = warn_about_non_constructive_defs defs in

 %% this section is identical to code in generateC4ImpUnit in I2LtoC.sw:
 let lm_data        = slice.lm_data                in
 let includes       = extractImports   lm_data.lms in
 let include_strs   = map printImport  includes    in
 let verbatims      = extractVerbatims lm_data.lms in
 let type_defines   = foldl (fn (defines, trans) ->
                               case trans.target of 
                                 | Name _ -> defines
                                 | term -> 
                                   defines ++ [(printName trans.source,
                                                printTerm term)])
                            []
                            lm_data.type_translations
 in
 let op_defines     = foldl (fn (defines, trans) ->
                               case trans.target of 
                                 | Name _ -> defines
                                 | term -> 
                                   defines ++ [(printName trans.source,
                                                        printTerm term)])
                            []
                            lm_data.op_translations
 in
 let defines        = type_defines ++ op_defines in

 %% this section is unique to lisp generation:
 let getter_setters = extract_getter_setters spc in
 let forms          = extract_forms          spc in

 {name           = defPkgName, 
  extraPackages  = extraPackages, 
  includes       = include_strs,
  verbatims      = verbatims,
  getter_setters = getter_setters,
  ops            = map (fn (n, _) -> n) defs, 
  axioms         = [], 
  opDefns        = defs,
  forms          = forms
  } 
      
op warn_about_non_constructive_defs (defs : List(String * LispTerm)) : () = 
 %% mkLTerm incorporates non_constructive_format_msg into certain calls to error
 app (fn (uname, tm) ->
	if calls_specific_error? tm non_constructive_format_msg 
           && 
           uname nin? SuppressGeneratedDefuns
          then 
            warn ("Non-constructive def for " ^ uname)
	else
	  ())
     defs

op calls_specific_error? (term : LispTerm) (format_str : LispTerm) : Bool =
 let 
   def aux tm =
     case tm of
       | Apply  (Op "cl:error", msg :: _) -> msg = format_str
       | Apply  (tm, tms)                 -> aux tm || exists? aux tms
       | Lambda (_,   _,   tm)            -> aux tm
       | If     (t1, t2, t3)              -> aux t1 || aux t2 || aux t3
       | IfThen (t1, t2)                  -> aux t1 || aux t2
       | Let    (_, tms, tm)              -> exists? aux tms || aux tm
       | Letrec (_, tms, tm)              -> exists? aux tms || aux tm
       | Seq    tms                       -> exists? aux tms
       | _                                -> false
 in
 aux term

 
%% ==========================================================================================
%%  (1) refine (possibly unused) ops using List_Executable.sw, String_Executable.sw, etc.
%% ==========================================================================================

op maybeSubstBaseSpecs (substBaseSpecs? : Bool) (spc : Spec) : Spec =
 if substBaseSpecs? then 
   SpecTransform.substBaseSpecs spc
 else 
   spc 

op transformSpecForLispGen (substBaseSpecs? : Bool) (slice? : Bool) (spc : Spec) : Spec =

 let _ = showIfVerbose ["---------------------------------------------",
                        "transforming spec for Lisp code generation...",
                        "---------------------------------------------"]
 in
 let _ = showSpecIfVerbose "Original"                              spc in

 %% ==========================================================================================
 %% fetch toplevel types and op early, to avoid including anything incidentally added later
 %% ==========================================================================================

 let (top_ops, top_types) = topLevelOpsAndTypesExcludingBaseSubsts spc in 
 let _ = showIfVerbose ["toplevel ops: ", 
                        anyToString top_ops, 
                        "------------------------------------------"]
 in

 %% Phase 1: Add stuff

 %% ==========================================================================================
 %%  (1) Substitute Base Specs, to intoduce executable definitions
 %%      Refine (possibly unused) ops using List_Executable.sw, String_Executable.sw, etc.
 %% ==========================================================================================

 %% substBaseSpecs should preceed other transforms, so those other transforms can apply to 
 %% the substituted definitions

 %% substBaseSpecs? will be true for gen-lisp, false for lgen-lisp

 let spc = maybeSubstBaseSpecs substBaseSpecs?                     spc in
 let _   = maybeShowSpecIfVerbose substBaseSpecs? "substBaseSpecs" spc in

 let spc = explicateEmbeds spc in       % Shouldn't really be necessary?

 %% Phase 2: Spec to Spec transforms

 %% ==========================================================================================
 %%  (2) Normalize Top Level Lambdas
 %%      Convert patterned lambdas into case expressions.
 %% ==========================================================================================

 let spc = SpecTransform.normalizeTopLevelLambdas                  spc in 
 let _   = showSpecIfVerbose "normalizeTopLevelLambdas"            spc in

 %% ==========================================================================================
 %%  (3) Instantiate Higher Order Functions
 %%      Calls normalizeCurriedDefinitions and simplifySpec.
 %%
 %%      Should precede removeCurrying, which eliminates higher order.
 %%      Should precede lambdaLift, which would remove inlineable local functions.
 %%      Should precede poly2mono, since higher order functions are usually polymorphic.
 %% ==========================================================================================

 let spc = SpecTransform.instantiateHOFns                          spc in 
 let _   = showSpecIfVerbose "instantiateHOFns"                    spc in

 %% ==========================================================================================
 %%  (4) Remove Currying
 %% ==========================================================================================
  
 %% ==========================================================================================
 %%  (5) Lift Unsupported Patterns
 %% ==========================================================================================

 %% ==========================================================================================
 %%  (6) Pattern Match Compiler, to remove case expressions.
 %%      Variant of Wadler's pattern matching compiler.
 %%
 %%      Currently introduces Select's and parallel Let bindings, which may confuse other
 %%      transforms.  
 %%
 %%      This may add calls to polymorphic fns, so must precede poly2mono. [TODO: verify this]
 %%      This may add local defs, so should preceed lambda lift.
 %% ==========================================================================================

 let spc = SpecTransform.translateMatch                            (spc, false) in 
 let _   = showSpecIfVerbose "translateMatch"                      spc in

 %% ==========================================================================================
 %%  (7) Lambda Lift
 %% ==========================================================================================

 %% ==========================================================================================
 %%  (8) Expand Record Merges
 %%      Make record constructions explicit.
 %%      'foo << {y = y}'   =>  '{x = foo.x, y = y, z = foo.z}'
 %%
 %%     This might be reversed later by introduceRecordMerges if we choose to produce Setf 
 %%     forms to revise mutable structures, but for now we stay within normal MetaSlang.
 %% ==========================================================================================

 let spc = SpecTransform.expandRecordMerges                        spc in 
 let _   = showSpecIfVerbose "translateRecordMergeInSpec"          spc in
  
 %% ==========================================================================================
 %%  (9) Convert Lets of Wild Patterns to Seq's
 %% ==========================================================================================

 %% ==========================================================================================
 %% (10) Eta Expansion
 %% ==========================================================================================

 %% TODO: Verity conjecture that matchCon in translateMatch has already done eta expansion,
 %%       making this redundant.  If so, we can remove this.

 let spc = SpecTransform.etaExpandDefs                             spc in  
 let _   = showSpecIfVerbose "etaExpandDefs"                       spc in

 %% ==========================================================================================
 %% (11) arityNormalize
 %% ==========================================================================================

 %% For exmaple, revise
 %%
 %%  op f1 (x: Nat) (y: Nat, z: Nat) : Nat = x + y + z
 %%   =>
 %%  op f1 (x: Nat) (apV: Nat * Nat) : Nat = let x0 = apV in case (x0.1, x0.2) of (y, z) -> x + y + z
 %%
 %%  op g1 (x: Nat, y: Nat, z: Nat) : Nat = f1 x (y, z)
 %%   =>
 %%  op g1 (x: Nat, y: Nat, z: Nat) : Nat = f1 x (TranslationBuiltIn.mkTuple(y, z))'

 let spc = SpecTransform.arityNormalize                            spc in
 let _   = showSpecIfVerbose "arityNormalize"                      spc in

 %% PHASE 3: Slicing, trimming

 %% ==========================================================================================
 %% (12) Conform Op Decls
 %% ==========================================================================================

 %% ==========================================================================================
 %% (13) Encapsulate Product Args
 %% ==========================================================================================

 %% ==========================================================================================
 %% (14) Introduce Record Merges
 %% ==========================================================================================

 %% ==========================================================================================
 %% (15) Expand Type Defs
 %% ==========================================================================================

 %% ==========================================================================================
 %% (16) Revise Types for Code Generation
 %% ==========================================================================================

 %% ==========================================================================================
 %% (17) add equality ops for sums, products, etc. -- TODO: adds far too many (but removeUnusedOps removes them)
 %% ==========================================================================================

 spc

op toLispSpec (substBaseSpecs? : Bool) (slice? : Bool) (ms_spec : Spec) 
  : LispSpec =
  %% top level ops are not very useful basis for slicing
  let (top_ops, top_types) = ([], []) in  % topLevelOpsAndTypesExcludingBaseSubsts ms_spec in 
  let slice?               = case (top_ops, top_types) of
                               | ([], []) -> 
                                 if slice? then
                                   let _ = writeLine (";;; No toplevel ops or types in spec, so not slicing.") in
                                   false
                                 else
                                   false
                               | _ -> 
                                 slice?
  in
  toLispSpecOps substBaseSpecs? slice? ms_spec top_ops top_types 

op toLispSpecOps (substBaseSpecs? : Bool)
                 (slice?          : Bool)
                 (ms_spec         : Spec) 
                 (top_ops         : OpNames)
                 (top_types       : TypeNames)
 : LispSpec =
 let slice?    = case top_ops of 
                   | [] -> 
                     if slice? then
                       let _ = writeLine("No toplevel ops in spec, so not slicing.") in
                       false
                     else
                       false
                   | _ -> 
                     true
 in
 let ms_spec   = transformSpecForLispGen substBaseSpecs? slice? ms_spec in
 let slice     = sliceForLispGen         ms_spec top_ops top_types      in
 let lisp_spec = lisp slice in
 lisp_spec               

op lispFilePreamble() : String =
 ";; THIS FILE IS GENERATED FROM SPECWARE SOURCE. DO NOT HAND-EDIT THIS FILE.\n" ^    
 "(eval-when (:compile-toplevel :load-toplevel :execute)\n" ^
 " (require \"SpecwareRuntime\" \""
 ^(case getEnv "SPECWARE4" of
     | Some path -> translate (fn ch ->	  % \ to / for windows
                                 case ch of
                                   | #\\ -> "/"
                                   | _ -> show ch)
       path
                                   | None -> "")
 ^"/Library/SpecwareRuntime.lisp\"))\n\n"
                          
                          
op SpecTransform.genLisp (original_ms_spec    : Spec,
                          root_op_names       : OpNames, 
                          % root_op_names_b     : OpNames, 
                          % stateful_type_names : TypeNames,
                          % global_type_name    : TypeName,
                          % opt_global_var_id   : Option Id,
                          % opt_ginit           : Option OpName,
                          filename            : String,
                          tracing?            : Bool)
 : () =
 let preamble  = lispFilePreamble()                                        in
 let lisp_spec = toLispSpecOps true true original_ms_spec root_op_names [] in
 let filename  = if (length filename < 5) || (implode (suffix (explode filename, 5)) ~= ".lisp") then
                   filename ^ ".lisp"
                 else
                   filename
 in
 ppSpecToFile (lisp_spec, filename, preamble)

op toLispFile (spc             : Spec, 
               file            : String, 
               preamble        : String, 
               substBaseSpecs? : Bool, 
               slice?          : Bool) 
 : () =  
 let lisp_spec = toLispSpec substBaseSpecs? slice? spc in
 ppSpecToFile (lisp_spec, file, preamble)

op toLispText (spc : Spec) : Text =
 let lisp_spec = toLispSpec true false spc in
 let pretty    = ppSpec lisp_spec          in
 let text      = format (120, pretty)      in
 text

%% Just generates code for the local defs
op localDefsToLispFile (spc : Spec, file : String, preamble : String) : () =
 %let localOps = spc.importInfo.localOps in
 let spc = setOps (spc, 
                   mapiAQualifierMap
                     (fn (q, id, info) ->
                        if localOp? (Qualified(q, id), spc) then
                          info
                        else 
                          let (tvs, ty, _) = unpackFirstOpDef info in
                          info << {dfn = maybePiTerm (tvs, TypedTerm (Any slPos, ty, slPos))})
                     spc.ops)
 in
 let spc = setElements (spc,mapPartialSpecElements 
                          (fn el ->
                             case el of
                               | Op    (_, true, _) -> Some el
                               | OpDef _            -> Some el
                               | _ -> None)
                          spc.elements)
 in 
 toLispFile (spc, file, preamble, false, false)  % don't substitue base spec, don't slice
     

(*
This is the same as MetaSlang.toLispFile only with an extra argument
giving the name of lisp package to be used in the generated lisp
file. This is intended to be used to generate code for "anonymous"
specs. These are specs defines by "def S = spec .. end" rather than
"spec S is .. end".  The latter sets the name field in the spec whereas
the former doesn't. Since the name of the package is computed from the
internal specname, we just create a new spec with the given name. The
proper way to do this would be to extend the parameters to the function
lisp (...) There are no references to that function from outside that
file.  This can come later once we come up with a coherent naming scheme.
In the meantime the following does the job.
*)

%   op toLispFileAsPackage : Spec * String * SpecName -> ()
  
%   def toLispFileAsPackage (spc, file, package) =
%    let renamedSpec = {
%      imports = spc.imports, 
%      types = spc.types, 
%      ops = spc.ops, 
%      properties = spc.properties
%    } : Spec in
%      toLispFile (renamedSpec, file, [])
endspec
