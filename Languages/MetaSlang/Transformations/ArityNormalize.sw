ArityNormalize qualifying spec

import /Languages/MetaSlang/Specs/Environment

(* 
 *  normalizeArity normalizes the arities of function applications and tuple formations 
 *  so that tuples appear as arguments only to functions declared to be n-ary or to the 
 *  polymorphic constructor TranslationBuiltIn.mkTuple.
 *  
 *  The semantics of mkTuple is the identity function, but for purposes of code generation 
 *  it is translated into appropriate constructors to form tuples.
 * 
 *  We assume that nested patterns have been be eliminated using the pattern matching 
 *  algorithm and that all identifiers are unique (resolveTerm has been invoked).
 * 
 *  ----------------------------------------
 * 
 *  Given:  
 *   op f (x : Nat) (y : Nat, z : Nat) : Nat
 *
 *  f 1 (2, 3)
 *   produces
 *  (funcall (f 1) 2 3)
 * 
 *  ----------------------------------------
 * 
 *  Given:  
 *   op f (x : Nat) (y : Nat * Nat) : Nat 
 *
 *  f 1 (2, 3)
 *   produces
 *  (funcall (f 1) (mkTuple 2 3))
 * 
 *  ----------------------------------------
 * 
 *  Given:  
 *   op f (x : Nat: y : Nat) : Nat
 *   op z : Nat * Nat
 *
 *  f z
 *   produces
 *  (mkApply f z)        
 * 
 *  ----------------------------------------
 * 
 *  Given
 *   op foo (x : Nat,y : Nat) : Nat
 * 
 *  (fn f -> f (1, 2)) foo
 *   produces
 *  (funcall #'(lambda (f) (funcall f 1 2)) #'foo)
 *
 *
 *  When all patterns in the match are records of the same arity n >= 0, 
 *  the arity of a match is n, otherwise it is 1.
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
        
% The arity map stores the ops having a domain type consisting of a record (possibly subsetted)

type Gamma = List (String * Option (MSType * Nat))

(*
 * Arities are associated with term identifiers according to arities in type definitions 
 * or arities of top-level pattern.  
 *
 * The top-level pattern gets precedence such that the pattern matching algorithm can 
 * always generate the pattern with as many arguments as possible.
 *)
  
op termArity (spc : Spec, gamma : Gamma, term  : MSTerm) : Option (MSType * Nat) =
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
   | Fun (Embed (id, true), typ, _) -> None  

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
                 dom        : MSType,
                 t1         : MSTerm,
                 t2         : MSTerm,
                 used_names : UsedNames) 
 : MSTerm =
 let

  def unfoldArgument (dom, arg) = 
    case unfoldBase (spc, dom) of

      | Subtype (typ, pred, _) -> 
        %
        % Relax the argument, then restrict the result.
        %
        let relaxOp      = mkRelax (typ, pred)       in
        let arg          = mkApply (relaxOp, arg)    in
        let (arg, decls) = unfoldArgument (typ, arg) in
        let arg          = mkRestriction (pred, arg) in
        (arg, decls)

      | Product (product_fields, _) -> 
        let (vname, used_names) = freshName ("x", used_names) in
        let vpat                = mkVarPat (vname, dom)       in
        let vref                = mkVar    (vname, dom)       in
        let record_fields = 
            map (fn (label, typ) ->
                   let arg = mkApply ((Fun (Project label, 
                                            mkArrow (dom, typ), 
                                            noPos)),
                                      vref) 
                   in
                   (label, arg))
                product_fields
        in
        (mkRecord record_fields, [(vpat, arg)])

      | _ -> 
        %% This should not happen (?) because we only apply it to terms 
        %% expecting a record of arguments.
        let _ = writeLine "Unexpected non-record argument to function " in
        let _ = writeLine (printTerm arg ^ " : " )                      in
        let _ = writeLine (printType dom)                               in
        (arg, []) 
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
 let (_, used_names) =
     mapAccumTerm (fn used_names -> fn tm  -> (tm,  used_names),
                   fn used_names -> fn typ -> (typ, used_names),
                   fn used_names -> fn pat ->
                     (pat, 
                      case pat of
                        | VarPat ((qid, _), _) ->
                          StringSet.add (used_names, qid)
                        | _ -> 
                         used_names))
                  used_names
                  term
 in
 used_names

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
                      let var      = (name, dom)                 in
                      mkLambda (mkVarPat var, 
                                mkApply (term, mkVar var)))
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

op SpecTransform.etaExpandDefs (spc : Spec) : Spec =
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
 : MSTerm =
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

  def normalizeRecordArguments trm =
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
     let (name, used_names) = freshName ("apV", used_names) in
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
