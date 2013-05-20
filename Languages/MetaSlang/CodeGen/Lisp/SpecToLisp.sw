(* Synchronized with version 1.3 of SW4/Languages/MetaSlang/ToLisp/SpecToLisp.sl *)

SpecToLisp qualifying spec
 import /Languages/MetaSlang/Transformations/PatternMatch
 import /Languages/MetaSlang/Transformations/InstantiateHOFns
 import /Languages/MetaSlang/Transformations/LambdaLift
 import /Languages/MetaSlang/Transformations/RemoveCurrying
% import /Languages/MetaSlang/Transformations/RecordMerge
 import /Languages/MetaSlang/Transformations/SliceSpec
 import /Languages/MetaSlang/Transformations/Globalize
 import /Languages/MetaSlang/Transformations/MetaTransform
%import /Languages/MetaSlang/CodeGen/CodeGenTransforms
 import /Languages/MetaSlang/CodeGen/SubstBaseSpecs
 import /Languages/MetaSlang/CodeGen/DebuggingSupport
 import /Languages/Lisp/Lisp
 import /Library/Structures/Data/Maps/SimpleAsSTHarray

 op generateCaseSensitiveLisp?: Bool = true
 
 op lispPackages: Strings = ["LISP", "COMMON-LISP", 
                             %% Added because of Xanalys packages, but prudent anyway
                             "SYSTEM", "SI", "IO", "BOOTSTRAP",
                             %% Added for cmulisp compatibility
                             "ALIST", "BYTES", "HASH", "HASHTABLE", "SEQ"]

 op lispStrings: StringSet =
    foldl add emptyMap 
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

 op notReallyLispStrings: Strings =
   ["C", "D", "I", "M", "N", "P", "S", "V", "X", "Y", "Z", "KEY", "NAME", "VALUE", "PATTERN"]

 op isLispString(id: Id): Bool = 
   member (lispStrings, id) 
   ||
   %% The above is only necessary for packages. They should be done differently in next release.
   (Lisp.uncell (Lisp.findSymbol(id, "CL"))
    && 
    id nin? notReallyLispStrings)

 op lispPackage?(id: Id): Bool =
   let pkg = Lisp.apply (Lisp.symbol ("CL", "FIND-PACKAGE"), [Lisp.string id]) in
   Lisp.uncell pkg
   && 
    Lisp.uncell (Lisp.apply (Lisp.symbol ("CL", "PACKAGE-NAME"), [pkg])) 
      in? lispPackages

 op  ith : [a] Nat * String * List (String * a) -> Nat
 def ith (n, id, ids) = 
   case ids of
     | [] -> System.fail ("No such index " ^ id)
     | (id2, _) :: ids -> 
       if id = id2 then
	 n 
       else 
	 ith (n + 1, id, ids)

 op projectionIndex (sp: Spec, id: Id, ty: MSType): Nat = 
   let (dom, _) = arrow (sp, ty) in
   let row = product (sp, dom) in
   ith (0, id, row)

 op isSpecialProjection (sp: Spec, ty: MSType, id: Id) : Option String = 
   case stripSubtypes (sp, ty) of
     | Arrow (dom, _, _) -> 
       (case stripSubtypes (sp, dom) of
	  | Product ([(id1, _), (id2, _)], _) -> 
	    Some (if id1 = id then "car" else "cdr")
	  | Product ([(id1, _)], _) ->	% Unary record
	    Some "functions::id"
	  | _ -> None)
     | _ -> None

 op  isConsDataType : Spec * MSType -> Option (Id * Id)
 def isConsDataType (sp, ty) : Option (Id * Id) = 
   let
     def isTwoTuple (ty : MSType) = 
       case stripSubtypes (sp, ty) of
	 | Product ([_, _], _) -> true 
	 | _ -> false
   in
     case stripSubtypes (sp, ty) of
       | CoProduct ([("None", None), ("Some", Some _)], _) -> None 

       % Options never get to be cons types.
       % This is required to make boot strapping work
       % as hash-quote-spec prints options without optimization.
       
       | CoProduct ([(i1, None  ), (i2, Some s)], _) -> if isTwoTuple s then Some (i1, i2) else None
       | CoProduct ([(i2, Some s), (i1, None  )], _) -> if isTwoTuple s then Some (i1, i2) else None
       | _ -> None
    

 op hasConsEmbed (sp: Spec, ty: MSType): Bool = 
   case stripSubtypes (sp, ty) of
     | Arrow (_, rng, _) -> 
       (case isConsDataType (sp, rng) of
	  | Some _ -> true
	  | None   -> false)
     | _ -> false

 op isConsIdentifier (sp: Spec, id: Id, ty: MSType) : Option String = 
   case isConsDataType (sp, ty) of
     | Some (i1, i2) -> Some (if id = i1 then "null" else "consp")
     | None -> None

 op hasConsDomain (sp: Spec, id: Id, ty: MSType) : Option String = 
   case stripSubtypes (sp, ty) of
     | Arrow (dom, _, _) -> 
       (case isConsDataType (sp, dom) of
	  | Some (i1, i2) -> Some (if id = i1 then "null" else "consp")
	  | None -> None)
     | _ -> None

 op listTerm(tm: MSTerm, sp: Spec): Option(List MSTerm) =
   case tm of
     | Apply(Fun(Op(Qualified("TranslationBuiltIn", "mkTuple"), _), _, _),
             Record([(_, x), (_, y)], _), _) ->
       (case y of
          | Fun(Embed (id, false), ty, _) | some?(isConsDataType(sp, ty)) ->
            Some [x]
          | Apply(Fun(Embed (id, true), ty, _), cdr_arg, _) | some?(isConsDataType(sp, range (sp, ty))) ->
            (case listTerm(cdr_arg, sp) of
               | Some r_list_args -> Some(x :: r_list_args)
               | None -> None)
          | _ -> None)       
     | _ -> None


 op patternName (pattern : MSPattern): Id = 
   case pattern of
     | VarPat ((id, _), _) -> id
     | RestrictedPat(p, _, _) -> patternName p
     | _ -> 
       System.fail ("SpecToLisp.patternName " ^ printPattern pattern)

 op patternNames (pattern : MSPattern): List1 Id = 
   case pattern of
     | VarPat    ((id, _), _) -> [id] 
     | RecordPat (fields,  _) -> List.map (fn (_, p) -> patternName p) fields
     %| RestrictedPat(p,_,_) -> patternNames p
     | _ -> 
       System.fail ("SpecToLisp.patternNames " ^ printPattern pattern)

 % type StringSet = StringSet.Set
 type StringSet = STHMap.Map(String, Bool)
 op member(S: StringSet, x: String): Bool =
   case apply(S, x) of
     | Some b -> b
     | None -> false

 op add( S: StringSet, x: String): StringSet =
   update(S, x, true)

 %op delete( S: StringSet, x: String): StringSet =
%   remove(S, x, false)

op addList(S: StringSet, l: List String): StringSet =
  foldl add S l

%op difference(S1: StringSet, S2: StringSet): StringSet =
%  foldi (fn (x, y, S) -> if y then remove(S, x) else S) S1 S2

 %% Domain is qualification. First set is strings as given, second is upper case version
 op  userStringMap : Ref (STHMap.Map (String, (Ref StringSet) * (Ref StringSet)))
 def userStringMap = Ref (emptyMap)
 def initializeSpecId () =
   (userStringMap := emptyMap)
       
 op  lookupSpecId : String * String * String -> String
 def lookupSpecId (id, ID, pkg) =
   case apply (! userStringMap, pkg) of
     | Some (userStrings, userUpper) ->
       if member (! userUpper, ID) then
         if member (! userStrings, id) then
	   id
	 else 
	   "|!" ^ id ^ "|"
       else 
         (userUpper   := add (! userUpper,   ID);
          userStrings := add (! userStrings, id);
          id)
     | None -> 
       (userStringMap := update (! userStringMap, pkg, 
                                 (Ref (add (emptyMap, id)), 
                                  Ref (add (emptyMap, ID))));
	id)

 def specId (id, pkg) = 
   let id =
       if forall? (fn #|  -> false
                    | #`  -> false
                    | #'  -> false
                    | #\\ -> false
                    | _ -> true)
           id
         then id                        % Test is redundant, but translate is expensive even if identity
         else translate (fn #|  -> "\\|" 
                          | #`  -> "\\`"
                          | #'  -> "\\'"
		          | #\\ -> "\\\\" 
			  | ch  -> Char.show ch)
                id
   in
   let upper_ID = String.map toUpperCase id in
   let ID = if generateCaseSensitiveLisp? then id else upper_ID in
   if isLispString upper_ID || id@0 = #! then
       "|!" ^ id ^ "|"
     else if exists? (fn ch -> ch = #:) id then
       "|"  ^ id ^ "|"
     else 
       lookupSpecId (id, upper_ID, pkg)

 def defaultSpecwarePackage = 
   if generateCaseSensitiveLisp? then
     "SW-User"
   else 
     "SW-USER"

 def mkLPackageId id = 
   if id = UnQualified then 
     defaultSpecwarePackage
   else
     let upper_id = String.map Char.toUpperCase id in
     let id = (if generateCaseSensitiveLisp? then id else upper_id) in
     if isLispString upper_id || lispPackage? upper_id then
         id ^ (if generateCaseSensitiveLisp? then "-Spec" else "-SPEC")
     else 
	 id
      
 %op printPackageId : QualifiedId * String -> String % see Suppress.sw
 def SpecToLisp.printPackageId (id, defPkgNm) = 
   case id of
     | Qualified ("System", "time") -> "TIME"
     | Qualified (pack, id) ->
       let pkg = mkLPackageId pack in
       if pkg = defPkgNm then
	 specId (id, "") % !!!
       else
	 (pkg ^ "::" ^ specId (id, pkg))
      
 def opArity (sp, idf, ty) =
   case typeArity (sp, ty) of
     | None -> None
     | arity ->
       if polymorphicDomainOp? (sp, idf) then
	 None
       else 
	 arity

 def compareSymbols = (mkLOp "eq") : LispTerm

 def mkLispTuple valTms =
   case valTms of
     | []     -> mkLBool false         % Nil
     % Named tuples can be unary
     | [x]    -> x
     | [_, _] -> mkLApply (mkLOp "cons",   valTms)
     | _      -> mkLApply (mkLOp "vector", valTms)
     
 op  unaryName : String -> String
 def unaryName (nm : String) : String = nm  % ^ "-1"

 op  naryName : QualifiedId * Nat * String -> String
 def naryName (Qualified (q, id), n, dpn) =
   printPackageId (Qualified (q, id ^ "-" ^ (Nat.show n)), 
		   dpn)

 def mkLUnaryFnRef (id : String, arity, vars) =
   if member (vars, id) then 
     mkLVar id
   else 
     case arity of
       | Some _ -> mkLOp (unaryName id)
       | _      -> mkLOp id

 %op mkLApplyArity : String * Option Nat *
 def mkLApplyArity (id : QualifiedId, defPkgNm : String, arity, vars, args) =
   let pid = printPackageId (id, defPkgNm) in
   let rator = (if member (vars, pid) then 
		  mkLVar pid
		else 
		  case arity of
		    | Some _ ->
		      if length args = 1 then
			mkLOp (unaryName pid)
		      else
			mkLOp (naryName (id, length args, defPkgNm))
		    | _ -> mkLOp pid)
   in 
     mkLApply (rator, args)

 %
 % Ad hoc optimization of the equality operation.
 %
 def mkLEqualityOp (sp, ty) = 
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
 def mkLInEqualityOp (sp, ty) = 
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

 op  mkLTermOp : [a] Spec * String * StringSet * (Fun * MSType * a) * Option (MSTerm) -> LispTerm
 def mkLTermOp (sp, dpn, vars, termOp, optArgs) =
   case termOp of
     | (Project id, ty, _) -> 
       (case (isSpecialProjection (sp, ty, id), optArgs) of
	  | (Some proj, None) -> 
	    mkLLambda (["!x"], [], 
		       mkLApply (mkLOp proj, 
				 [mkLVar "!x"]))

	  | (Some proj, Some trm) ->
	    let lTrm = mkLTerm (sp, dpn, vars, trm) in
	    if proj = "functions::id" then
	      lTrm
	    else 
	      mkLApply (mkLOp proj, 
			[lTrm])

	  | (None, Some trm) -> 
	    let id = projectionIndex (sp, id, ty)  in
	    mkLApply (mkLOp "svref", 
		      [mkLTerm (sp, dpn, vars, trm), 
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
	  | Some arg -> mkLApply (oper, mkLTermList (sp, dpn, vars, arg)))

     | (And, ty, _ ) ->
       % Note: And ("&&") is non-strict -- it might not evalute the second arg.
       %       This means it is not commutative wrt termination.
       let oper = mkLOp ("cl:and") in  % lisp AND is also non-strict
       (case optArgs of
         %| None -> oper  % TODO: is this situation possible? Given note above, should it be allowed?
	  | Some arg -> mkLApply (oper, mkLTermList (sp, dpn, vars, arg)))

     | (Or, ty, _ ) ->
       % Note: Or ("||") is non-strict -- it might not evalute the second arg
       %       This means it is not commutative wrt termination.
       let oper = mkLOp ("cl:or") in  % lisp OR is also non-strict
       (case optArgs of
         %| None -> oper  % TODO: is this situation possible? Given note above, should it be allowed?
	  | Some arg -> mkLApply (oper, mkLTermList (sp, dpn, vars, arg)))

     | (Implies, ty, _ ) ->
       % Note: Implies ("=>") is non-strict -- it might not evalute the second arg.
       %       This means it is not commutative (to the contrapositive) wrt termination.
       (case optArgs of
         %| None -> mkLOp ("Slang-Built-In:implies-2") % TODO: is this situation possible? Given note above, should it be allowed?
	  | Some (Record ([(_, x), (_, y)], _)) ->
	    % "x => y" = "if x then y else true" = "or (~ x, y)"
	    mkLApply (mkLOp ("cl:or"),         
		      [mkLApply (mkLOp "cl:not", 
				[mkLTerm (sp, dpn, vars, x)]), 
		       mkLTerm (sp, dpn, vars, y)]))

     | (Iff, ty, _ ) ->
       % Note: Iff ("<=>") is strict, becasue the second arg must be evaluated, no matter what the value of the first arg is.
       %       This means it is commmuative wrt termination.
       (case optArgs of
	 %| None -> mkLOp ("cl:eq") % presumably boolean-valued args each evaluate to T or NIL, so this should be ok.
          | Some (Record ([(_, x), (_, y)], _)) ->
	    % "x => y" = "if x then y else ~ y"
	    mkLIf (mkLTerm (sp, dpn, vars, x), 
		   mkLTerm (sp, dpn, vars, y), 		   
		   mkLApply (mkLOp "cl:not", 
			     [mkLTerm (sp, dpn, vars, y)])))

     | (Equals, ty, _) ->
       let oper = mkLOp (mkLEqualityOp (sp, ty)) in
       (case optArgs of
	 %| None -> oper
	  | Some arg -> mkLApply (oper, 
				  mkLTermList (sp, dpn, vars, arg)))

     | (NotEquals, ty, _) ->
       (case optArgs of
	 %| None -> mkLOp (mkLInEqualityOp (sp, ty))
          | Some arg -> 
	    %% for efficiency, open-code the call to not
	    %% let ineq_op = mkLOp (mkLInEqualityOp (sp, ty)) in
            %% mkLApply (ineq_op, mkLTermList (sp, dpn, vars, arg)))
	    let eq_oper = mkLOp (mkLEqualityOp (sp, ty)) in
	    mkLApply (mkLOp "cl:not", 
		     [mkLApply (eq_oper, 
				mkLTermList (sp, dpn, vars, arg))]))

     | (Select id, ty, _) -> 
       (case (hasConsDomain (sp, id, ty), optArgs) of
	  | (Some queryOp, None)      -> mkLLambda (["!x"], [], mkLVar "!x")

	  | (Some queryOp, Some term) -> mkLTerm (sp, dpn, vars, term)

	  | (None,         None)      -> mkLOp "cdr"

	  | (None,         Some term) -> mkLApply (mkLOp "cdr", 
						   [mkLTerm (sp, dpn, vars, term)]))

     | (Embedded id, ty, _) -> 
       let dom = domain (sp, ty) in
       (case (isConsIdentifier (sp, id, dom), optArgs) of
	  | (Some queryOp, None)      -> mkLLambda (["!x"], [], 
						    mkLApply (mkLOp queryOp, 
							      [mkLVar "!x"]))

	  | (Some queryOp, Some term) -> mkLApply (mkLOp queryOp, 
						   [mkLTerm (sp, dpn, vars, term)])

	  | (None,         None)      -> mkLLambda (["!x"], 
						    [], 
						    mkLApply (compareSymbols, 
							      [mkLApply (mkLOp "car", 
									 [mkLVar "!x"]), 
							       mkLIntern id]))
	  | (None,         Some term) -> mkLApply (compareSymbols, 
						   [mkLApply (mkLOp "car", 
							      [mkLTerm (sp, dpn, vars, term)]), 
						    mkLIntern id])
	   )
     | (Nat    n, ty, _) -> mkLInt    n
     | (String s, ty, _) -> mkLString s
     | (Bool   b, ty, _) -> mkLBool   b
     | (Char   c, ty, _) -> mkLChar   c

     | (Op (id, _), ty, _) ->
       (case id of
	  | Qualified ("TranslationBuiltIn", "mkFail") ->
	    mkLApply(mkLOp "error",case optArgs of Some term -> mkLTermList(sp, dpn, vars, term))
	  | _ ->
	let arity = opArity (sp, id, ty) in
	(case optArgs of
	   | None ->
	     let pid = printPackageId (id, dpn) in
	     if functionType? (sp, ty) then
	       mkLUnaryFnRef (pid, arity, vars)
	     else 
	       Const (Parameter pid)
	   | Some term ->
	     mkLApplyArity (id, dpn, arity, vars, 
			    mkLTermList (sp, dpn, vars, term))))

     | (Embed (id, true), ty, _) ->
       let rng = range (sp, ty) in
       (case isConsDataType (sp, rng) of
	  | Some _ ->
	    (case optArgs of
	       | None -> mkLLambda (["!x"], [], mkLVar "!x")
	       | Some term -> 
             case listTerm(term, sp) of
               | Some list_args ->
                 let l_list_args = map (fn t -> mkLTerm (sp, dpn, vars, t)) list_args in
                 mkLApply(mkLOp "list", l_list_args)
               | None -> mkLTerm (sp, dpn, vars, term))
	  | None -> 
	    let id = mkLIntern id in
	    (case optArgs of
	       | None -> mkLLambda (["!x"], [], 
				   mkLApply (mkLOp "cons", 
					    [id, mkLVar "!x"]))
	       | Some term -> 
	         mkLApply (mkLOp "cons", [id, mkLTerm (sp, dpn, vars, term)])))

     | (Embed (id, false), ty, _) -> 
       (case isConsDataType (sp, ty) of
	  | Some _ -> mkLBool false
	  | None   -> mkLApply (mkLOp "list", [mkLIntern id]))

     | (Quotient qid, ty, pos) -> 
       % let _ = toScreen("\nQuotient qid     = " ^  anyToString qid     ^ "\n") in
       % let _ = toScreen("\nQuotient ty     = " ^  anyToString ty     ^ "\n") in
       % let _ = toScreen("\nQuotient vars    = " ^  anyToString vars    ^ "\n") in
       % let _ = toScreen("\nQuotient termOp  = " ^  anyToString termOp  ^ "\n") in
       % let _ = toScreen("\nQuotient optArgs = " ^  anyToString optArgs ^ "\n") in
       (case findAllTypes (sp, qid) of
          | [info] ->
            % let _ = toScreen("\nQuotient info    = " ^  anyToString info  ^ "\n") in
            (case unpackFirstTypeDef info of
                | (tvs, Quotient (_, equiv, _)) ->
                  let equiv = mkLTerm (sp, dpn, vars, equiv) in
                  % let _ = toScreen("\nQuotient tvs     = " ^  anyToString tvs   ^ "\n") in
                  % let _ = toScreen("\nQuotient equiv   = " ^  anyToString equiv ^ "\n") in
                  (case optArgs of
                     | None      -> mkLApply (mkLOp "Slang-Built-In::quotient", 
                                              [equiv])
                     | Some term -> mkLApply (mkLOp "Slang-Built-In::quotient-1-1", 
                                              [equiv, mkLTerm (sp, dpn, vars, term)]))
                | x -> fail("Internal confusion in mkLTermOp: expected quotient " ^ show qid ^ " to name a quotient type, saw: " ^ anyToString x))
          | x -> fail("Internal confusion in mkLTermOp: expected quotient " ^ show qid ^ " to name one quotient type, but saw: " ^ anyToString x))
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
                                              [mkLTerm (sp, dpn, vars, term)]))
                | x -> fail("Internal confusion in mkLTermOp: expected choose " ^ show qid ^ " to name a quotient type, saw: " ^ anyToString x))
          | x -> fail("Internal confusion in mkLTermOp: expected choose " ^ show qid ^ " to name one quotient type, but saw: " ^ anyToString x))
     (*
      *  Restrict and relax are implemented as identities
      *)

     | (Restrict, ty, _) -> 
       (case optArgs of
	  | None -> mkLLambda (["!x"], [], mkLVar "!x")
	  | Some term -> mkLTerm (sp, dpn, vars, term))

     | (Relax, ty, _) -> 
       (case optArgs of
	  | None -> mkLLambda (["!x"], [], mkLVar "!x")
	  | Some term -> mkLTerm (sp, dpn, vars, term))

     | mystery -> System.fail ("In mkLTermOp, unexpected termOp: " ^ (anyToString mystery))

 op  flattenFailWith : MSTerm -> MSTerms
 def flattenFailWith term =
   case term of
     | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "failWith"), _), _, _), 
	      Record ([(_, t1), (_, t2)], _), _)
       -> 
       flattenFailWith t1 ++ flattenFailWith t2
     | _ -> [term]


 def lispBlock (sp, dpn, vars, term : MSTerm) : LispTerm = 
   let terms = flattenFailWith term in
   let terms = List.map (fn term -> blockAtom (sp, dpn, vars, term)) terms in
   mkLSeq terms        

 def blockAtom (sp, dpn, vars, term : MSTerm) : LispTerm = 
   case term of

     | IfThenElse (t1, t2, Fun (Op (Qualified ("TranslationBuiltIn", "mkBreak"), _), _, _), _) ->
       IfThen (mkLTerm   (sp, dpn, vars, t1), 
	       blockAtom (sp, dpn, vars, t2))

     | IfThenElse (t1, t2, t3, _) -> 
       If (mkLTerm  (sp, dpn, vars, t1), 
	   blockAtom (sp, dpn, vars, t2), 
	   blockAtom (sp, dpn, vars, t3))

     | Let (decls, body, _) -> 
       let (pats, terms) = unzip decls in
       let  names = List.map patternName pats  in
       let  names = List.map (fn id -> specId (id, "")) names      in
       mkLLet (names, 
	      List.map (fn t -> mkLTerm (sp, dpn, vars, t)) terms, 
	      blockAtom (sp, dpn, addList (vars, names), body))   

     | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkSuccess"), _), _, _), 
	      term, _)
       -> 
       mkLApply (mkLOp "return", [mkLTerm (sp, dpn, vars, term)])

     | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkFail"), _), _, _), 
	      Fun (String msg, _, _), _) 
       -> 
       mkLApply (mkLOp "error", [mkLString msg])
        
     | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "failWith"), _), _, _), _, _) -> 
       lispBlock (sp, dpn, vars, term)

     | _ -> 
       System.fail ("Unexpected atom " ^ printTerm term)

 % DIE HARD if the above cases are not exhaustive

 op  typeOfOp : Spec * QualifiedId -> MSType
 def typeOfOp (sp, qid) =
   case AnnSpec.findTheOp (sp, qid) of
     | Some info -> 
       firstOpDefInnerType info
     | None -> System.fail("Undefined op: "^show qid)

 op  fullCurriedApplication : AnnSpec.Spec * String * StringSet * MSTerm -> Option LispTerm
 def fullCurriedApplication (sp, dpn, vars, term) =
   let 

     def aux (term, i, args) =
       case term of

	 | Fun (Op (id, _), ty, _) ->
           %% Note that we use typeOfOp(sp, id) instead of ty because may be polymorphic with instantiation to a fn type
	   if i > 1 && i = curryShapeNum (sp, typeOfOp(sp, id)) 
             then
	     Some (mkLApply (mkLOp (unCurryName (id, i, dpn)), 
			     List.map (fn t -> mkLTerm (sp, dpn, vars, t)) args))
	   else 
	     None

	 | Fun (Choose _, _, _) ->
	   if i = 2 then
	     case args of
	       | [f, val] ->
		 if identityFn? f then
		   Some (mkLApply (mkLOp "Slang-Built-In::quotient-element", 
				   [mkLTerm (sp, dpn, vars, val)]))
		 else 
		   Some (mkLApply (mkLOp "Slang-Built-In::choose-1-1", 
				   [mkLTerm (sp, dpn, vars, f), 
				    mkLTerm (sp, dpn, vars, val)]))
	       | _ -> None % shouldn't happen
	   else 
	     None

	 | Apply (t1, t2, _) -> aux (t1, i+1, t2::args)

	 | _ -> None

  in 
    aux (term, 0, [])


 def mkLTermList (sp, dpn, vars, term : MSTerm) = 
   case term of
     | Record (fields, _) -> List.map (fn (_, t) -> mkLTerm (sp, dpn, vars, t)) fields
     | _ -> [mkLTerm (sp, dpn, vars, term)]

 %% Make a special op for the message format to ensure that terms built by mkLTerm 
 %% can be recognized by warn_about_non_constructive_defs
 op  non_constructive_format_msg : LispTerm
 def non_constructive_format_msg = mkLString "Non-constructive Term: ~A~%       where ~{~A = ~S~^, ~}"

 def mkLTerm (sp, dpn, vars, term : MSTerm) = 
   case fullCurriedApplication (sp, dpn, vars, term) of
     | Some lTerm -> lTerm
     | _ ->
       case term of

	 | Fun termOp -> mkLTermOp (sp, dpn, vars, termOp, None)

	 | Var ((id, ty), _) -> 
	   let id = specId (id, "") in
	   if member (vars, id) then
	     Var id 
	   else
	     Op id

	 | Let (decls, body, _) ->
	   let (pats, terms) = unzip decls in
	   let  names = List.map patternName pats  in
	   let  names = List.map (fn id -> specId (id, "")) names in
	   mkLLet (names, 
		  List.map (fn t -> mkLTerm (sp, dpn, vars, t)) terms, 
		  mkLTerm (sp, dpn, addList (vars, names), body))   

	 | LetRec (decls, term, _) ->
	   let
             def unfold (decls, names, terms) = 
	       case decls of
		 | [] -> (names, terms)
		 | (name, term) :: decls -> 
		   unfold (decls,name::names, term::terms)
                    
	   in
	   let (names, terms) = unfold (decls, [], []) in
	   let names = List.map (fn (id, _) -> specId (id, "")) names in
           let vars  = foldl remove vars names in
	   % let vars  = StringSet.difference (vars, StringSet.fromList names) in

	   %% Letrec bound names are to be treated as op-refs and not var-refs 

	   mkLLetRec (names, 
		     List.map (fn t -> mkLTerm (sp, dpn, vars, t)) terms, 
		     mkLTerm (sp, dpn, vars, term))

	 | Apply (t1, Apply (Fun (Restrict, _, _), t2, _), a) ->
	   mkLTerm (sp, dpn, vars, Apply (t1, t2, a))

	 | Apply (t1, Apply (Fun (Relax, _, _), t2, _), a) ->
	   mkLTerm (sp, dpn, vars, Apply (t1, t2, a))

	 (*
	  * Here we translate the pattern matching monads that are inserted 
	  * by the pattern matching translator.
	  * They are translated to block constructs.
	  *)
	   
	 | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "block"), _), _, _), t, _) ->
	   %% let _ = writeLine ("Block " ^ printTerm term) in 
	   let terms = flattenFailWith t in
	   let terms = List.map (fn term -> blockAtom (sp, dpn, vars, term)) terms in
	   mkLApply (mkLOp "block", Cons (Const (Boolean false), terms))

	 %% Forced tuples are translated to tuples by translating the argument to mkLTuple recursively

	 | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkTuple"), _), _, _), 
		 term, _) 
	   -> 
	   mkLTerm (sp, dpn, vars, term)

	 %% Functions of arity different from 1 are wrapped in an apply when given only 1 argument

	 | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkApply"), _), _, _), 
		  Record ([(_, t1), (_, t2)], _), _) 
	   -> 
	   mkLApply (mkLOp "apply", [mkLTerm (sp, dpn, vars, t1), mkLTerm (sp, dpn, vars, t2)])

	 | Apply (term, term2 as Record (fields, _), _) ->
	   (case term of
	      | Fun termOp -> 
	        mkLTermOp (sp, dpn, vars, termOp, Some term2)
	      | _ -> 
		let terms = List.map (fn (_, t) -> mkLTerm (sp, dpn, vars, t)) fields in
		mkLApply (mkLTerm (sp, dpn, vars, term), terms))         

	 | Apply (term1, term2, _) -> 
	   (case term1 of

	      | Fun termOp -> 
	        mkLTermOp (sp, dpn, vars, termOp, Some term2)

	      | Var ((id, ty), _) ->
		let id = specId (id, "") in
		if member (vars, id) then
		  mkLApply (mkLTerm (sp, dpn, vars, term1), 
			    [mkLTerm (sp, dpn, vars, term2)])
		else 
		  mkLApply (mkLOp id, 
			    [mkLTerm (sp, dpn, vars, term2)])

	      | _ -> 
		mkLApply (mkLTerm (sp, dpn, vars, term1), 
			  [mkLTerm (sp, dpn, vars, term2)]))

	 | Record (row, _) ->
	   mkLispTuple (List.map (fn (_, t) -> mkLTerm (sp, dpn, vars, t)) row)

	 | IfThenElse (t1, t2, t3, _) -> 
	   mkLIf (mkLTerm (sp, dpn, vars, t1), 
		  mkLTerm (sp, dpn, vars, t2), 
		  mkLTerm (sp, dpn, vars, t3))

	 | Lambda ([(pat, cond, trm)], _) ->
           let names = patternNames pat in 
           let names = List.map (fn id -> specId (id, "")) names in
	   mkLLambda (names, 
		     [], 
		     mkLTerm (sp, dpn, addList (vars, names), trm))
            
	 | Seq (terms, _) ->
           mkLSeq (List.map (fn t -> mkLTerm (sp, dpn, vars, t)) terms)

	 | _ -> 
	   let pos = (termAnn term) in
	   let tm_str = printTerm_OnOneLine term in
	   (%% System.warn ("Non-constructive term " ^ (printIfExternal pos) ^ ": " ^ tm_str);
	    %%
	    %% The overall effect of the code constructed here
	    %% is to produce something like this at runtime:
	    %%
	    %%   In the following, n = 33, f = "testing"
	    %%   Error: Non-constructive Term: fa(i : Nat) i < n => embed?(Some)(f i)
	    %%
	    %% A nice side effect is that the free vars in this term will appear as
	    %% used lisp vars (the even positions in the name/value list), so the 
	    %% lisp compiler will not spuriously warn about them being unused.
	    %%
	    let free_vars = List.map (fn (id,_) -> specId (id, "")) (freeVars term) in
	    mkLApply(mkLOp "cl:error",
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
				      free_vars)]))

 def SpecToLisp.printTerm_OnOneLine term = 
   let s = PrettyPrint.toString (format (8000, ppTerm (initialize (asciiPrinter, false))
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
 def countOccurrence2 (x, count, terms : List LispTerm) = 
   case terms of
     | [] -> count 
     | Cons (term, terms) -> 
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
      
 def getNames (term : LispTerm) =
   case term of
     | Apply   (t1, terms)         -> foldr (fn (t, names) -> getNames t ++ names) (getNames t1) terms
     | Lambda  (vars, _, t)        -> vars ++ (getNames t)
     | Op      r                   -> [r]
     | Var     r                   -> [r] 
     | Const   _                   -> []
     | If      (t1, t2, t3)        -> (getNames t1) ++ (getNames t2) ++ (getNames t3)
     | IfThen  (t1, t2)            -> (getNames t1) ++ (getNames t2)
     | Let     (vars, terms, body) -> vars ++ (flatten (List.map getNames terms)) ++ (getNames body)
     | Letrec  (vars, terms, body) -> vars ++ (flatten (List.map getNames terms)) ++ (getNames body)
     | Seq     terms               -> flatten (List.map getNames terms)
     | _ -> System.fail "Unexpected term in getNames"
      
 op  rename  : String * (Strings *                   Strings * LispTerm) -> Strings *                   Strings * LispTerm
 op  rename2 : String * (Strings * List (LispTerm) * Strings * LispTerm) -> Strings * List (LispTerm) * Strings * LispTerm

 def rename (v, (vars, names, body)) = 
   if exists? (fn n -> n = v) names then
     let n = newName (v, names) in
     let body = substitute (v, mkLVar n) body in
     (n::vars, 
      n::names, 
      body)
   else 
     (v::vars, names, body)

 def rename2 (v, (vars, terms, names, body)) = 
   if exists? (fn n -> n = v) names then
     let n = newName (v, names) in 
     let body  = substitute (v, (mkLVar n) : LispTerm) body  in 
     let terms = List.map (substitute (v, mkLVar n)) terms  in
     (n::vars, terms, n::names, body)
   else 
     (v::vars, terms,    names, body)

 op  substitute : (String * LispTerm) -> LispTerm -> LispTerm
 def substitute (x, arg) body = 
   let 
     def subst_in_decls decls =
       case arg of
	 | Var new_var ->
           (List.map (fn decl ->
		      case decl of
			| Ignore ignored_vars -> 
			  Ignore (List.map (fn ignored_var -> 
					    if ignored_var = x then 
					      new_var
					    else 
					      ignored_var)
				           ignored_vars))
	             decls)
	 | _ -> decls
   in
     case body of

       | Apply (term, terms) -> 
         Apply (substitute (x, arg) term, 
		List.map (substitute (x, arg)) terms)

       | Lambda (vars, decls, body) -> 
	 if exists? (fn v -> x = v) vars then
	   mkLLambda (vars, decls, body) 
	 else
           let names = getNames arg in
           let (vars, names, body) = foldr rename ([], names, body) vars
           in
	     mkLLambda (vars, 
		       %% we might be renaming a var, in which case
		       %% any decls referring to it must be updated
		       subst_in_decls decls, 
		       substitute (x, arg) body)
           
       | Var y -> if x = y then arg else mkLVar y

       | Let (vars, terms, body) -> 
	 if exists? (fn v -> x = v) vars then
	   mkLLet (vars, 
		   List.map (substitute (x, arg)) terms, 
		   body)
	 else 
           let terms = List.map (substitute (x, arg)) terms in
           let names = getNames (arg) in
           let (vars, names, body) = foldr rename ([], names, body) vars
           in
	     mkLLet (vars, 
		     terms, 
		     substitute (x, arg) body)
           
       | Letrec (vars, terms, body) -> 
	 if exists? (fn v -> x = v) vars then
	   mkLLetRec (vars, terms, body)
	 else 
           let names = getNames (arg) in
           let terms = List.map (substitute (x, arg)) terms in
           let (vars, terms, names, body) = 
	       foldr rename2 ([], terms, names, body) vars  
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
	 mkLSeq (List.map (substitute (x, arg)) ts)

       | _ -> body
     

 def simpleTerm (term : LispTerm) = 
   case term of
     | Var   _ -> true
     | Const (Parameter nm) -> ~(testSubseqEqual?("Global::", nm, 0, 0))
     | Const _ -> true
     | Op    _ -> true
     | _ -> false
      

 def pure (term : LispTerm) = 
   case term of
     | Var    _ -> true
     | Const (Parameter nm) -> ~(testSubseqEqual?("Global::", nm, 0, 0))
     | Const  _ -> true
     | Op     _ -> true
     | Lambda _ -> true
     | Apply (Op "cdr",    terms) -> forall? pure terms % Selector from data type constructors.
     | Apply (Op "car",    terms) -> forall? pure terms % Selector from tuple.
     | Apply (Op "svref",  terms) -> forall? pure terms % Projection from record
     | Apply (Op "vector", terms) -> forall? pure terms % Tuple formation
     | Apply (Op "cons",   terms) -> forall? pure terms % Tuple formation
     | _ -> false
      
  
 def pV? var_name =
   case explode var_name of
     | #p :: #V :: digits -> forall? isNum digits % lexer gets upset if no space between "::#"
     | #a :: #p :: #V :: digits -> forall? isNum digits
     | _ -> false

 def reduceTerm (term : LispTerm) = 
   case term of

     | Apply (Lambda (xs, _, body), args) -> reduceTerm (Let (xs, args, body))

     | Apply (term, terms) -> 
       let term  = reduceTerm term   in
       let terms = List.map reduceTerm terms in
       %% DELETED 6/7/00 nsb to make choose and quotient compile correctly.
       %% Where is this relevant?
       %% let (* Ops need an argument *)
       %%   def etaExpandOp (term : LispTerm) = 
       %%    case term of
       %%      | Op _ -> mkLLambda (["!x"], [], mkLApply (term, [mkLVar "!x"]))
       %%      | _ -> term
       %% in 
       %  let terms = List.map etaExpandOp terms in
       mkLApply (term, terms)
           
     | Lambda (vars, decls, body) -> 
       let reduced_body = reduceTerm body in
       let unused_and_unignored_pv_vars = 
           List.foldr (fn (var_name, unused_vars) ->
		       if (%% internally generated?
			   %% For user-defined vars, we do NOT want add an ignore decl, 
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
			   %% duplications among the vars probably shouldn't happen, 
			   %% but it doesn't hurt to double-check
			   var_name nin? unused_vars)
		       then 
			  var_name::unused_vars
		       else 
			 unused_vars)
	              []      
		      vars
       in
       let augmented_decls = 
           (case unused_and_unignored_pv_vars of
	      | [] -> decls
	      | _  -> Ignore unused_and_unignored_pv_vars :: decls)
       in
	 mkLLambda (vars, augmented_decls, reduced_body)

     %
     % Optimized by deleting pure arguments that do not
     % occur in the body at all.
     %
     | Let (xs, args, body) -> 
       let body  = reduceTerm body          in
       let args  = List.map reduceTerm args in
       let xArgs = zip (xs, args)  in
       %
       % Count along multiplicity of a variable in the let bound arguments.
       % This prevents capture in sequential substitution.
       % ?? Example please...
       %
       let terms = body::args in
       let xNumArgs = 
           List.map (fn (x, arg) ->
		     if simpleTerm arg then
		       %% If arg is a constant, why do we not substitute if
		       %%  there are 2 or more occurrences of the var among 
		       %%  the args (ignoring the body)?
		       %% Why not always substitute? (I.e. return count of 0 or 1)
		       %% Is this related to the capture issue above?
		       (x, countOccurrence2 (x, 0, args),  false, arg)

		     else if pure arg then
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
       mkLLetRec (vars, List.map reduceTerm terms, reduceTerm body)

     | If (t1, t2, t3) -> 
       mkLIf (reduceTerm t1, reduceTerm t2, reduceTerm t3)

     | IfThen (t1, t2) -> 
       IfThen (reduceTerm t1, reduceTerm t2)

     | Seq (terms) -> mkLSeq (List.map reduceTerm terms)

     | l -> l
                          
 def lispTerm (sp, dpn, term) = 
   reduceTerm (mkLTerm (sp, dpn, emptyMap, term))

 def functionType? (sp, ty) = 
   case unfoldBase (sp, ty) of
     | Arrow _ -> true
     | Subtype (s, _, _) -> functionType? (sp, s)
     | _ -> false

 def genNNames n = 
   tabulate (n, fn i -> "x" ^ (Nat.show i))

 def nTupleDerefs (n, vr) = 
   if n = 2 then 
     [mkLApply (mkLOp "car", [vr]), 
      mkLApply (mkLOp "cdr", [vr])]
   else 
     tabulate (n, fn i -> 
	          mkLApply (mkLOp "svref", 
			    [vr, mkLNat i]))

 def duplicateString (n, s) =
   case n of
     | 0 -> ""
     | _ -> s ^ duplicateString (n - 1, s)

 op  unCurryName : QualifiedId * Nat * String -> String
 def unCurryName (Qualified (q, id), n, dpn) =
   printPackageId (Qualified (q, id ^ duplicateString (n, "-1")), dpn)

 %% fn x -> fn (y1, y2) -> fn z -> bod --> fn (x, y, z) let (y1, y2) = y in bod
 def unCurryDef (term, n) =
   let 
     def auxUnCurryDef (term, i, params, let_binds) =
       if i > n then 
	 (Some (reduceTerm (mkLLambda (params, 
				       [], 
				       foldl (fn (bod, (vars, vals)) ->
					      mkLLet (vars, vals, bod))
				             term 
					     let_binds)))) 
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
 def defNaryByUnary (name, n) =
   let vnames = genNNames n in
   reduceTerm (mkLLambda (vnames, 
			  [], 
			  mkLApply (mkLOp (name), 
				    [mkLispTuple (List.map mkLVar vnames)])))

 % fn (x, y, z) -> f-1 (tuple (x, y, z))
 def defAliasFn (name, n) =
   let vnames = genNNames n in
   reduceTerm (mkLLambda (vnames, 
			  [], 
			  mkLApply (mkLOp (name), 
				    List.map mkLVar vnames)))

 % fn x -> f (x.1, x.2, x.3)
 def defUnaryByNary (name, n) =
   reduceTerm (mkLLambda ([if n = 0 then "ignore" else "x"], 
			  if n = 0 then [Ignore ["ignore"]] else [], 
			  mkLApply (mkLOp name, 
				    nTupleDerefs (n, mkLVar "x"))))

 % fn x1 -> fn ... -> fn xn -> name (x1, ..., xn)
 def defCurryByUncurry (name, n) =
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
 def defUncurryByUnary (name, n) =
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

 op  renameDef? : ListADT.LispTerm -> Option String
 def renameDef? term =
   case term of
     | Lambda ([v], _, Apply (Op fnName, [Var vr])) ->
       if v = vr then 
	 Some fnName 
       else 
	 None
     | _ -> None

 op indexTransforms?: Bool = true

 op formsFromSpec(spc: Spec): LispTerms =
   if ~indexTransforms? || none?(findTheType(spc, Qualified("MetaTransform", "AnnTypeValue"))) then []
   else
   let tr_infos = generateAddTransformUpdates spc in
   map (fn (Qualified(_, nm), (ty_info, fn_tm)) ->
        let q_ty_info = Const (Cell (cell ty_info))                         in
        let name      = mkQualifiedId ("MetaTransform", "addTransformInfo") in
        let fn_tm     = translateMatchInTerm spc name fn_tm                 in
        let fn_ltm    = lispTerm (spc, defaultSpecwarePackage, fn_tm)       in  
        Set("MetaTransform::transformInfoMap",
            mkLApply(mkLOp "MetaTransform::addTransformInfo-3", [mkLString nm, q_ty_info, fn_ltm])))
     tr_infos

 op lisp(spc: Spec): LispSpec =
  %let _ = printSpecToTerminal spc in
   let _ = initializeSpecId () in
   let packages = map mkLPackageId (qualifiers spc.ops) in
   let (defPkgName, extraPackages) = (defaultSpecwarePackage, packages) in
   %% Make defaultSpecwarePackage be the standard package name rather than some random package
   %        case packages
   %          of x :: r -> (x, r)
   %           | [] -> (defaultSpecwarePackage, [])
   let
     def mkLOpDef (q, id, info, defs) = 
       foldl (fn (defs, dfn) -> 
	      let (tvs, ty, term) = unpackFirstTerm dfn in
              if anyTerm? term then defs     % Maybe should give a warning
              else
              % let _ = writeLine("lopdef: "^id^"\n"^printTerm term^"\n"^printTerm dfn) in
	      let term = lispTerm (spc, defPkgName, term) in
	      let qid = Qualified (q, id) in
	      let uName = unaryName (printPackageId (qid, defPkgName)) in
	      let new_defs =
	          if functionType? (spc, ty) then
		     (case (curryShapeNum (spc, ty), typeArity (spc, ty)) of
			| (1, None) ->
			  (case term of
			     | Lambda (formals, _, _) -> [(uName, term)]
			     | _ -> [(uName, mkLLambda (["!x"], [], 
							mkLApply (term, [mkLVar "!x"])))])
			| (1, Some (_, arity)) ->
			  let nName = naryName (qid, arity, defPkgName) in
			  (case term of
			     | Lambda (formals, _, _) ->
			       let n = length formals in
			       [(nName, 
				 if n = arity then 
				   term
				 else 
				   defNaryByUnary (uName, arity)),                 % fn (x, y, z) -> f-1 (tuple (x, y, z))
				(uName, 
				 if n = arity then
				   defUnaryByNary (nName, n)                       % fn x -> f (x.1, x.2, x.3)
				 else 
				   term)]
			     | _ ->  
			       %% Not sure that arity normalization hasn't precluded this case
			       [(nName, defNaryByUnary (uName, arity)),            % fn (x, y, z) -> f-1 (tuple (x, y, z))
				(uName, mkLLambda (["!x"], [], 
						   mkLApply (term, [mkLVar "!x"])))])
			| (curryN, None) ->
			  let ucName = unCurryName (qid, curryN, defPkgName) in
			  (case unCurryDef (term, curryN) of
			     | Some uCDef ->                                       % fn x -> fn y -> fn z -> f-1-1-1 (x, y, z)
			       [(uName, defCurryByUncurry (ucName, curryN)), 
				(ucName, uCDef)]
			     | _ ->
			       [(uName, term), 
				(ucName, 
				 case renameDef? term of
				   | Some equivFn ->                               % fn (x, y, z) -> equivFn-1-1-1 ( x, y, z)
				   %% Questionable call to unCurryName
				   defAliasFn (unCurryName (Qualified (defPkgName, equivFn), 
							    curryN, 
							    defPkgName), 
					       curryN)
				   | _ ->                                          % fn (x, y, z) -> f x y z
				   defUncurryByUnary (uName, curryN))])
			 
			| (curryN, Some (_, arity)) ->
			  let ucName = unCurryName (qid, curryN, defPkgName) in
			  let nName = naryName (qid, arity, defPkgName) in
			  (case unCurryDef (term, curryN) of
			     | Some uCDef ->
			       [(nName, defNaryByUnary    (uName,  arity)),        % fn (x, y, z) -> f-1 (tuple (x, y, z))
				(uName, defCurryByUncurry (ucName, curryN)),       % fn x -> fn y -> fn z -> f-1-1-1 (x, y, z)
				(ucName, uCDef)]
			     | _ ->
			       (case term : LispTerm of
				  | Lambda (formals, _, _) ->
				    let n = length formals in
				    [(nName, 
				      if n = arity then 
					term
				      else 
					defNaryByUnary (uName, arity)),            % fn (x, y, z) -> f-1 (tuple (x, y, z))
				     (uName, 
				      if n = arity then
					defUnaryByNary (nName, n)                  % fn x -> f (x.1, x.2, x.3)
				      else 
					term), 
				     (ucName, defUncurryByUnary (uName, curryN))]  % fn (x, y, z) -> f-1 x y z
				   | _ ->
				    [(nName, defNaryByUnary (uName, arity)),       % fn (x, y, z) -> f-1 (tuple (x, y, z))
				     (uName, mkLLambda (["!x"], [], 
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
                    [Record([],noPos)]  % to get (defvar Global.xxx nil)
                  else
                    [])
   in
     let defs = reverse(foldriAQualifierMap mkLOpDef [] spc.ops) in
     let _    = warn_about_non_constructive_defs defs   in
     let 
       def uncurried_name (Qualified (q, id), arg_counts) =
         let new_id = foldl (fn (id, n) -> id ^ "-" ^ show n) id arg_counts in
         printPackageId (Qualified (q, new_id), defPkgName)
     in
     %% TODO: The relevant axioms and theorems are get sliced away before this point,
     %%       so setf_entries is empty.  (Sigh)
     let setf_entries = findSetfEntries spc in
     let getter_setters = 
         map (fn entry ->
                (uncurried_name (entry.accesser_name, entry.accesser_arg_counts),
                 uncurried_name (entry.updater_name,  entry.accesser_arg_counts)))
             setf_entries
     in
     % let _ = writeLine ("====") in
     % let _ = writeLine ("setf_entries   = " ^ anyToString setf_entries) in
     % let _ = writeLine ("getter_setters = " ^ anyToString getter_setters) in
     % let _ = writeLine ("====") in
     let forms = formsFromSpec spc in
     {name           = defPkgName, 
      extraPackages  = extraPackages, 
      getter_setters = getter_setters,
      ops            = List.map (fn (n, _) -> n) defs, 
      axioms         = [], 
      opDefns        = defs,
      forms          = forms
     } : LispSpec
      
 op  warn_about_non_constructive_defs : List(String * ListADT.LispTerm) -> ()
 def warn_about_non_constructive_defs defs =
   %% mkLTerm incorporates non_constructive_format_msg into certain calls to error
   app (fn (uname, tm) ->
	if calls_specific_error? tm non_constructive_format_msg
            && uname nin? SuppressGeneratedDefuns
          then System.warn ("Non-constructive def for " ^ uname)
	else
	  ())
       defs

 op  calls_specific_error? : LispTerm -> LispTerm -> Bool
 def calls_specific_error? tm format_str =
   let 
      def aux tm =
	case tm of
	  | Apply  (Op "cl:error", msg :: _) -> msg = format_str
	  | Apply  (tm, tms)       -> aux tm || exists? aux tms
	  | Lambda (_,   _,   tm)  -> aux tm
	  | If     (tm1, tm2, tm3) -> aux tm1 || aux tm2 || aux tm3
	  | IfThen (tm1, tm2)      -> aux tm1 || aux tm2
	  | Let    (_, tms, tm)    -> exists? aux tms || aux tm
	  | Letrec (_, tms, tm)    -> exists? aux tms || aux tm
	  | Seq    tms             -> exists? aux tms
	  | _                      -> false
   in
     aux tm

 op removeTheorems (spc : Spec) : Spec = 
  %% theorems are irrelevant for code generation
  let
    def filter el =
      case el of
        | Property _ -> None
        | _ -> Some el
  in
  setElements (spc, mapPartialSpecElements filter spc.elements)

 op builtInLispType? (qid : QualifiedId) : Bool = false
 op builtInLispOp?   (qid : QualifiedId) : Bool = false

 op maybeRemoveUnusedOps (slice? : Bool) (spc : Spec) : Spec =
  if slice? then 
    sliceSpecForCode (spc, 
                      topLevelOps   spc, 
                      topLevelTypes spc, 
                      builtInLispOp?, 
                      builtInLispType?)
  else 
    spc 

 op maybeSubstBaseSpecs (substBaseSpecs? : Bool) (spc : Spec) : Spec =
  if substBaseSpecs? then 
    substBaseSpecs spc
  else 
    spc 

 op removeCurrying? : Bool = false

 op maybeRemoveCurrying (spc : Spec) : Spec =
  if removeCurrying? then  % false by default
    removeCurrying spc 
  else
    spc

 op instantiateHOFns? : Bool = true

 op maybeInstantiateHOFns (spc : Spec) : Spec =
  if instantiateHOFns? then % true by default
    instantiateHOFns spc
  else 
    spc

 op lambdaLift? : Bool = false
 op LambdaLift.simulateClosures? : Bool = false % If false just use lambdas with free vars (deprecated as global option)

 op maybeLambdaLift (spc : Spec) : Spec =
  if lambdaLift? then          % false by default
    if simulateClosures? then
      lambdaLiftWithImportsSimulatingClosures spc
    else
      lambdaLiftWithImports spc
  else 
    spc

 op transformSpecForLispGen (substBaseSpecs? : Bool) (slice? : Bool) (spc : Spec) : Spec =
   let _ = showIfVerbose ["------------------------------------------",
                          "transforming spec for Lisp code generation...",
                          "------------------------------------------"]
   in
   let _   = showSpecIfVerbose "Original"                   spc in %  (0)

   let spc = maybeSubstBaseSpecs substBaseSpecs?            spc in %  (1) via gen-lisp, substBaseSpecs? is true 
   let _   = showSpecIfVerbose "substBaseSpecs"             spc in

   let spc = removeTheorems                                 spc in %  (2)
   let _   = showSpecIfVerbose "removeTheorems"             spc in

   let spc = maybeRemoveUnusedOps slice?                    spc in %  (3) via gen-lisp, slice? is false
   let _   = showSpecIfVerbose "maybeRemoveUnusedOps"       spc in

   let spc = maybeRemoveCurrying                            spc in %  (4) no-op by default
   let _   = showSpecIfVerbose "removeCurrying"             spc in

   let spc = normalizeTopLevelLambdas                       spc in %  (5)
   let _   = showSpecIfVerbose "normalizeTopLevelLambdas"   spc in

   let spc = maybeInstantiateHOFns                          spc in %  (6)
   let _   = showSpecIfVerbose "instantiateHOFns"           spc in

   let spc = maybeLambdaLift                                spc in %  (7) no-op by default
   let _   = showSpecIfVerbose "maybeLambdaLift"            spc in

   %% Currently, translateMatch introduces Select's and parallel Let bindings,
   %% which would confuse other transforms.  So until that is changed, 
   %% translateMatch should be done late in the transformation sequence.
   %%
   %% We also might wish to convert matches to case or typecase expressions,
   %% in which case not all matches would be transformed to if statements.

   let spc = translateMatch                                 spc in %  (8)
   let _   = showSpecIfVerbose "translateMatch"             spc in

   let spc = expandRecordMerges                             spc in %  (9)
   let _   = showSpecIfVerbose "expandRecordMerges"         spc in

   let spc = arityNormalize                                 spc in % (10)
   let _   = showSpecIfVerbose "arityNormalize"             spc in

   spc

 op toLispSpec (substBaseSpecs? : Bool) (slice? : Bool) (spc : Spec) 
  : LispSpec =
  let spc       = transformSpecForLispGen substBaseSpecs? slice? spc in
  let lisp_spec = lisp spc in
  lisp_spec               

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
 def localDefsToLispFile (spc, file, preamble) =
   %let localOps = spc.importInfo.localOps in
   let spc = setOps (spc, 
		     mapiAQualifierMap
		       (fn (q, id, info) ->
			if localOp? (Qualified(q, id), spc) then
			  info
			else 
			  let pos = termAnn info.dfn in
			  let (tvs, ty, _) = unpackFirstOpDef info in
			  info << {dfn = maybePiTerm (tvs, TypedTerm (Any pos, ty, pos))})
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
