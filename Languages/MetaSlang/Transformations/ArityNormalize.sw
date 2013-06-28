% Synchronized with version 1.3 of SW4/Languages/MetaSlang/Transformations/ArityNormalize.sl

(* 
 *  normalizeArity(specName,nameSupply,term) 
 *
 *  normalizes the arities of function applications and tuple formations in term
 *  such that tuples only appear as arguments to functions that are declared as
 *  n-ary or to the polymorphic constructor TranslationBuiltIn.mkTuple
 *  (whose semantics is to be the identity function, but it is translated into
 *   the adequate constructors that form tuples).
 * 
 *  We assume that nested patterns have been be eliminated using the pattern 
 *  matching algorithm and that all identifiers are unique (resolveTerm has been
 *  invoked).
 * 
 *  Let f : fn x -> fn (y,z) -> (+ x y z) 
 *  then f 1 (2,3)
 *  translates into: (funcall (f 1) 2 3)
 * 
 *  Let f : fn x -> fn y -> (+ x (car y) (cdr y))
 *  then f 1 (2,3)
 *  translates into: (funcall (f 1) (mkTuple 2 3))
 * 
 *  Let f : fn (x,y) -> (+ x y)
 *  then f z
 *  translates into: (mkApply f z)        
 * 
 *  def foo(x,y) = x + y
 * 
 *  (fn f -> f(1,2)) foo
 *  translates into: funcall #' (lambda (f) (funcall f 1 2)) #'foo
 *)

ArityNormalize qualifying spec

import /Languages/MetaSlang/Specs/Environment

(*
 *  The arity of a match is some n >= 0,
 *  when all patterns in the match are records of arity n,
 *  otherwise it is 1.
 *)

op matchArity (match : MSMatch) : Nat =
 let
   def aux (match, num) = 
     case match of
       | [] -> num
       | (RecordPat (pats, _),_,_) :: match ->
         if num = length pats then
           aux (match, num)
         else 
           1
       | (WildPat _, _, _) :: match -> 
         aux (match, num)
       | _ -> 1
 in
 case match of
   | [] -> 0
   | (RecordPat     (pats, _),                    _, _) :: match -> aux (match, length pats)
   | (RestrictedPat (RecordPat (pats, _) , _, _), _, _) :: match -> aux (match, length pats)
   | _ -> 1
        
% The arity map stores the ops having a domain type consisting of
% a record (possibly subsetted)

type Gamma = List (String * Option (MSType * Nat))

(*
 Arities are associated with term identifiers according to 
 arities in type definitions or arities of top-level pattern.
 The top-level pattern gets precedence such that the pattern 
 matching algorithm can always generate the pattern with 
 as many arguments as possible.
 *)
  
op termArity (spc   : Spec, 
              gamma : Gamma, 
              term  : MSTerm) 
 : Option (MSType * Nat) =
 case term of
   | Apply _ -> None

   | Var ((id, _),_ ) -> 
     (case findLeftmost (fn (id2, r) -> id = id2) gamma of
        | Some (w, r) -> r
        | _ -> None)

   | Fun (Not,              typ, _) -> typeArity (spc, typ)
   | Fun (And,              typ, _) -> typeArity (spc, typ)
   | Fun (Or,               typ, _) -> typeArity (spc, typ)
   | Fun (Implies,          typ, _) -> typeArity (spc, typ)
   | Fun (Iff,              typ, _) -> typeArity (spc, typ)
   | Fun (Equals,           typ, _) -> typeArity (spc, typ)
   | Fun (NotEquals,        typ, _) -> typeArity (spc, typ)
   | Fun (RecordMerge,      typ, _) -> typeArity (spc, typ)
   | Fun (Embed (id, true), typ, _) -> None  % typeArity(spc,typ)
   | Fun        _ -> None
   | Let        _ -> None
   | LetRec     _ -> None
   | Bind       _ -> None
   | The        _ -> None
   | IfThenElse _ -> None
   | Record     _ -> None
   | Seq        _ -> None
   | Lambda (match, _) -> 
     let mArity = matchArity match in
     if mArity = 1 then
       None
     else 
       Some (case match of
               | (pat, _, _) :: _ -> patternType pat
               | _ -> System.fail "Unexpected empty match",mArity)
   | _ -> System.fail "Unmatched term"
    
op mkArityApply (spc        : Spec,
                 dom       : MSType,
                 t1        : MSTerm,
                 t2        : MSTerm,
                 used_names : UsedNames) 
 : MSTerm =
 let
  def unfoldArgument (dom : MSType, t2) = 
    case unfoldBase (spc, dom) of
      | Subtype(s,t,_) -> 
        %
        % First relax the argument, then restrict the result.
        %
        let relaxOp = mkRelax(s,t) in
        let t2 = mkApply(relaxOp,t2) in
        let (t2,decls) = unfoldArgument(s,t2) in
        let t2 = mkRestriction(t,t2) in
        (t2,decls)
      | Product(fields,_) -> 
        let (names, used_names) = 
            foldr (fn ((fieldName, typ), (names, used_names)) ->
                     let (newName,used_names) = freshName("v"^fieldName,used_names) in
                     let names = (newName, fieldName, typ) :: names in
                     (names, used_names))
                  ([], used_names) 
                  fields
        in
        let (x, used_names) = freshName("x",used_names) in
        let decl           = (mkVarPat(x,dom),t2) in
        let v              = mkVar(x,dom) in
        let fields = 
            map (fn (name, label, typ)->
                   let trm = mkApply ((Fun (Project label, 
                                            mkArrow (dom, typ), 
                                            noPos)),
                                      v) 
                   in
                   (label, trm))
                names
        in
        (mkRecord fields, [decl])
      | _ -> 
        (toScreen "Unexpected non-record argument to function ";
         toScreen (printTerm t2^" :  " );
         writeLine (printType dom);
         (t2,[])) 
        %% This should not happen (?) 
        %% because we only apply it to terms expecting
        %% a record of arguments.
 in
 let (t2, decls) = unfoldArgument (dom, t2) in
 mkLet (decls, mkApply (t1, t2))

op mkArityTuple (spc : Spec, term : MSTerm) : MSTerm = 
 let typ = inferType (spc, term) in
 mkApply (mkOp (Qualified ("TranslationBuiltIn", "mkTuple"),
                mkArrow (typ, typ)),
         term)

op insertPattern (pat : MSPattern, 
                  result as (used_names : UsedNames,
                             gamma      : Gamma)) 
 : UsedNames * Gamma =
 case pat of

   | VarPat ((v as (id, typ)), _) -> 
     (StringSet.add (used_names, id), 
      (id, None) :: gamma)

   | RecordPat (fields, _) -> 
     foldr (fn ((_, p), result) -> 
              insertPattern (p, result)) 
           result 
           fields

   | RestrictedPat (p, _, _) ->
     insertPattern (p, result)
 (*
  * (* These cases should not appear after pattern match compilation, 
  *    but are listed for independence of possible pattern matching *)
  * | AliasPat    (p1, p2)       -> insertPattern (p1, insertPattern (p2, result))
  * | EmbedPat    (_, Some p, _) -> insertPattern (p, result)
  * | QuotientPat (p, t)         -> insertPattern (p, result)
  * | _ -> result
  *)

op insertVars (vars       : MSVars,
               used_names : UsedNames, 
               gamma      : Gamma) 
 : UsedNames * Gamma =
 foldr (fn (v as (id, typ), (used_names, gamma)) -> 
          let used_names = StringSet.add (used_names, id) in
          let gamma      = (id,None) :: gamma             in
          (used_names, gamma))
       (used_names, gamma) 
       vars

op addLocalVars (term : MSTerm, used_names : UsedNames) : UsedNames =
 let used = Ref used_names in
 let _ = mapTerm (id, 
                  id, 
                  fn pat ->
                    case pat of
                      | VarPat ((qid, _), _) ->
                        (used := StringSet.add (!used, qid); pat)
                      | _ -> pat)
                 term
 in 
 !used

op etaExpand (spc        : Spec, 
              used_names : UsedNames, 
              typ        : MSType, 
              term       : MSTerm)
 : MSTerm =
 case arrowOpt (spc, typ) of
   | None -> term
   | Some (dom, _) -> 
     case productOpt (spc, dom) of
       | None -> (case term of
                    | Lambda _ -> term
                    | _ -> 
                      let (name,_) = freshName ("x", used_names) in
                      let x = (name, dom) in
                      mkLambda (mkVarPat x, mkApply (term, mkVar x)))
       | Some fields ->
         if case term of
              | Lambda (rules, _) -> simpleAbstraction? rules
              | _ -> false
           then 
             term
         else
           let (vnames, _)  = freshNames ("x", fields, used_names) in
           let labeled_vars = map (fn (vname, (label, typ)) -> 
                                     (label, (vname, typ))) 
                                  (vnames, fields) 
           in
           let vpats        = map (fn (label, var) -> (label, mkVarPat var)) labeled_vars in
           let vrefs        = map (fn (label, var) -> (label, mkVar    var)) labeled_vars in
           let pat          = mkRecordPat vpats in
           let body         = mkApply (term, mkRecord vrefs) in
           mkLambda (pat, body)

op SpecTransform.etaExpandDefs (spc: Spec) : Spec =
 setOps (spc, 
         mapOpInfos (fn info -> 
                       let (old_decls, old_defs) = opInfoDeclsAndDefs info in
                       let new_defs =
                           map (fn dfn ->
                                  let (tvs, typ, term) = unpackFirstTerm dfn        in
                                  let used_names       = addLocalVars (term, empty) in
                                  let term = etaExpand (spc, used_names, typ, term) in
                                  maybePiTerm (tvs, TypedTerm (term, typ, noPos)))
                               old_defs
                       in
                       let new_dfn = maybeAndTerm (old_decls ++ new_defs, noPos) in
                       info << {dfn = new_dfn})
                    spc.ops)

op simplePattern? (pattern : MSPattern) : Bool = 
 case pattern of
   | VarPat _ -> true
   | RestrictedPat (p, _, _) -> simplePattern? p
   | _ -> false
 
op simpleAbstraction? (rules : MSMatch) : Bool = 
 case rules of

   | [(pat, Fun (Bool true, _, _), _)] ->
     (case pat of
        | RecordPat (fields, _) ->
          forall? (fn (_, p) -> simplePattern? p) fields

        | RestrictedPat (RecordPat (fields, _), _, _) ->
          forall? (fn (_, p) -> simplePattern? p) fields

        | _ ->
          simplePattern? pat)

   | _ -> false

op normalizeArityTopLevel (spc        : Spec,
                           gamma      : Gamma,
                           used_names : UsedNames,
                           term       : MSTerm)
 :MSTerm =
 if anyTerm? term then 
   term 
 else
   case term of
     | Lambda (rules, _) -> 
       Lambda (map (fn (pat, cond, body)->
                      let (used_names, gamma) = insertPattern (pat, (used_names, gamma)) in
                      (pat,
                       normalizeArity (spc, gamma, used_names, cond),
                       normalizeArity (spc, gamma, used_names, body)))
                   rules,
               noPos)
     | _ -> normalizeArity (spc, gamma, used_names, term)

op normalizeArity (spc        : Spec, 
                   gamma      : Gamma, 
                   used_names : UsedNames, 
                   term       : MSTerm)
 : MSTerm = 
 let

  def normalizeRecordArguments (trm : MSTerm) : MSTerm * Bool = 
    case trm of

      | Record (fields, _) -> 
        let fields = map (fn (id, tm) -> 
                            let tm = normalizeArity (spc, gamma, used_names, tm) in
                            (id, tm))
                         fields 
        in
        (mkRecord fields, true)

      | Apply (t1 as (Fun (Restrict, _, _)), t2, _) -> 
        let (t2, isRecord?) = normalizeRecordArguments t2 in
        (Apply (t1, t2, noPos), isRecord?)

      | _ -> 
        let trm = normalizeArity (spc, gamma, used_names, trm) in
        (trm, false)

  def nonPolymorphicFun? trm =
    case trm of
      | Fun (Op (qid, _), _, _) -> ~(polymorphicDomainOp? (spc, qid))
      | _ -> false
 in
 case term of
   | Apply (t1, t2, _) ->
     (if nonPolymorphicFun? t1 then
        let (t2, _) = normalizeRecordArguments t2 in
        mkApply (t1, t2)        % Multiple entry points if necessary
      else
        case termArity (spc, gamma, t1) of
          | None -> 
            (mkApply (normalizeArity (spc, gamma, used_names, t1),
                      normalizeArity (spc, gamma, used_names, t2)))
          | Some (dom, num) -> 
            let (t2, isRecord?) = normalizeRecordArguments t2 in
            let t1 = case t1 of
                       | Var _ -> t1
                       | Fun _ -> t1
                       | _ -> normalizeArityTopLevel (spc, gamma, used_names, t1) 
            in
            if isRecord? then
              mkApply (t1, t2)
            else 
              mkArityApply (spc, dom, t1, t2, used_names))

   | Record (fields, _) -> 
     let fields = map (fn (id, tm) -> 
                         let tm = normalizeArity (spc, gamma, used_names, tm) in
                         (id, tm))
                      fields 
     in
     mkArityTuple (spc, mkRecord fields)

   | Bind (binder, vars, body, _) -> 
     let (used_names, gamma) = insertVars (vars, used_names, gamma)          in
     let body                = normalizeArity (spc, gamma, used_names, body) in
     mkBind (binder, vars, body)

   | The (var, body, _) -> 
     let (used_names, gamma) = insertVars ([var], used_names, gamma)         in
     let body                = normalizeArity (spc, gamma, used_names, body) in
     mkThe (var, body)

   | Let (decls, body, _) -> 
     let (decls, used_names, gamma) = 
         foldr (fn ((pat, t1), (decls, used_names, gamma)) ->
                  let t2                  = normalizeArity (spc, gamma, used_names, t1) in
                  let decls               = (pat, t2) :: decls                          in
                  let (used_names, gamma) = insertPattern (pat, (used_names, gamma))    in
                  (decls, used_names,  gamma))
               ([], used_names, gamma)
               decls 
     in
     let body = normalizeArity (spc, gamma, used_names, body) in
     mkLet (decls, body)

   | LetRec (decls, term, _) ->
     let (used_names, gamma) = 
     foldr (fn ((v, term), (used_names, gamma)) ->
              let (id, _)    = v                                       in
              let used_names = StringSet.add (used_names, id)          in
              let gamma      = (id,termArity(spc,gamma,term)) :: gamma in
              (used_names, gamma))
           (used_names, gamma)
           decls
     in
     let decls = 
         map (fn (v, trm) -> 
                let trm = normalizeArityTopLevel (spc, gamma, used_names, trm) in
                (v, trm))
             decls 
     in
     let term =  normalizeArity(spc,gamma,used_names,term) in
     mkLetRec(decls,term)

   | IfThenElse (t1, t2, t3, _) -> 
     IfThenElse (normalizeArity (spc, gamma, used_names, t1),
                 normalizeArity (spc, gamma, used_names, t2),
                 normalizeArity (spc, gamma, used_names, t3),
                 noPos)

   | Seq (terms, _) -> 
     Seq (map (fn trm -> 
                 normalizeArity (spc, gamma, used_names, trm)) 
              terms, 
          noPos)

   | Lambda _ -> 
     let term = normalizeArityTopLevel (spc, gamma, used_names, term) in
     convertToArity1 (spc, gamma, used_names, term)

   | Var _ -> convertToArity1 (spc, gamma, used_names, term)

   | Fun _ -> convertToArity1 (spc, gamma, used_names, term)

   | And (tm :: r_tms, _) ->
     let tm = normalizeArity (spc, gamma, used_names, tm) in
     And (tm :: r_tms, noPos)

   | tm -> tm

op convertToArity1 (spc        : Spec, 
                    gamma      : Gamma,
                    used_names : UsedNames,
                    term       : MSTerm)
 : MSTerm = 
 case termArity (spc, gamma, term) of
   | None -> term
   | Some (dom, num) ->
     %% by using "pV" as the prefix, 
     %% we pass the pV? test in reduceTerm,
     %% which allows use to include an ignore decl
     %% if the var is not used in the body
     let (name,used_names) = freshName("apV",used_names) in
     let x = (name, dom) in
     (Lambda ([(VarPat (x, noPos), 
                mkTrue (),
                mkArityApply (spc, dom, term, mkVar x, used_names))],
              noPos))

%
% This one ignores arity normalization in types, axioms and theorems.
%     

op SpecTransform.arityNormalize (spc : Spec) : Spec =
 let used_names = StringSet.fromList (qualifierIds spc.ops) in
 setOps (spc, 
         mapOpInfos (fn info -> 
                       let pos                   = termAnn info.dfn        in
                       let (old_decls, old_defs) = opInfoDeclsAndDefs info in
                       let new_defs =
                           map (fn dfn ->
                                  let pos = termAnn dfn in
                                  let (tvs, typ, term) = unpackFirstTerm dfn                    in
                                  let used_names       = addLocalVars (term, used_names)        in
                                  let term             = etaExpand (spc, used_names, typ, term) in
                                  let term             = normalizeArityTopLevel (spc, 
                                                                                 [],  % gamma
                                                                                 used_names,
                                                                                 term)
                                  in
                                  maybePiTerm (tvs, TypedTerm (term, typ, pos)))
                               old_defs
                       in
                       let new_dfn = maybeAndTerm (old_decls ++ new_defs, pos) in
                       info << {dfn = new_dfn})
                    spc.ops)

endspec
