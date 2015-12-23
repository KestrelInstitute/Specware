(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

ArityNormalize qualifying spec

import /Languages/MetaSlang/Specs/Environment

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Normalize Arity
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(* 
 *  normalizeArity normalizes the arities of function applications and tuple formations 
 *  so that tuples appear as arguments only to functions declared to be n-ary or to the 
 *  polymorphic constructor TranslationBuiltIn.mkTuple.
 *  
 *  The semantics of mkTuple is the identity function, but for purposes of code generation 
 *  it is translated into appropriate constructors to form tuples.
 * 
 *  We assume that nested patterns have been eliminated using the pattern matching 
 *  algorithm and that all identifiers are unique (resolveTerm has been invoked).
 * 
 *  Some examples of the effect of this transformation, and the eventual lisp code that
 *  is produced:
 *  ----------------------------------------------------------------------------------------------------
 *
 *   op f1 (x: Nat) (y: Nat, z: Nat) : Nat = x + y + z
 *     =>
 *   op f1 (x: Nat) (apV: Nat * Nat) : Nat = let x0 = apV in case (x0.1, x0.2) of (y, z) -> x + y + z
 *
 *   op g1 (x: Nat, y: Nat, z: Nat) : Nat = f1 x (y, z)
 *     =>
 *   op g1 (x: Nat, y: Nat, z: Nat) : Nat = f1 x (TranslationBuiltIn.mkTuple(y, z))
 *   
 *   to lisp:
 *
 *     (defun f1-1-1 (x apV) (Nat-Spec::+-2 (Nat-Spec::+-2 x (car apV)) (cdr apV)))
 *     (defun g1-3 (x y z) (f1-1-1 x (cons y z)))
 *
 *     (defun f1 (x1) #'(lambda (x2) (f1-1-1 x1 x2)))
 *     (defun g1 (x) (g1-3 (svref x 0) (svref x 1) (svref x 2)))
 *
 *  ----------------------------------------------------------------------------------------------------
 *
 *   op f2 (x: Nat) (y: Nat * Nat) : Nat = x + y.1 + y.2
 *    =>
 *   op f2 (x: Nat) (y: Nat * Nat) : Nat = x + y.1 + y.2
 *
 *   op g2 (x: Nat, y: Nat, z: Nat) = f2 x (y, z)
 *    =>
 *   op g2 (x: Nat, y: Nat, z: Nat) = f2 x (TranslationBuiltIn.mkTuple(y, z))
 *
 *   to lisp:
 * 
 *     (defun f2-1-1 (x y) (Nat-Spec::+-2 (Nat-Spec::+-2 x (car y)) (cdr y)))
 *     (defun g2-3 (x y z) (f2-1-1 x (cons y z)))
 *     
 *     (defun f2 (x1) #'(lambda (x2) (f2-1-1 x1 x2)))
 *     (defun g2 (x) (g2-3 (svref x 0) (svref x 1) (svref x 2)))
 *
 *  ----------------------------------------------------------------------------------------------------
 *
 *   op f3 (x: Nat, y: Nat) : Nat  = x + y
 *    =>
 *   op f3 (x: Nat, y: Nat) : Nat  = x + y
 *   
 *   op z3 : Nat * Nat = (4,5)
 *    =>
 *   op z3 : Nat * Nat = TranslationBuiltIn.mkTuple(4, 5)
 *
 *   op g3 (x: Nat, y: Nat) : Nat = f3 (x, y)
 *    =>
 *   op g3 (x: Nat, y: Nat) : Nat = f3 (x, y)
 * 
 *   op h3 (x: Nat, y: Nat) : Nat = f3 z3
 *    =>
 *   op h3 (x: Nat, y: Nat) : Nat = f3 z3
 *
 *   to lisp:
 *
 *     (defun f3-2 (x y) (Nat-Spec::+-2 x y))
 *     (defparameter z3 (cons 4 5))
 *     (defun g3-2 (x y) (f3-2 x y))
 *     (defun h3-2 (x y) (f3 z3))                ; note
 *
 *     (defun f3 (x) (f3-2 (car x) (cdr x)))
 *     (defun g3 (x) (g3-2 (car x) (cdr x)))
 *     (defun h3 (x) (h3-2 (car x) (cdr x))) 
 *
 *  ----------------------------------------------------------------------------------------------------
 *
 *   op f4 (x: Nat, y: Nat) : Nat  = x + y
 *    =>
 *   op f4 (x: Nat, y: Nat) : Nat  = x + y
 * 
 *   op g4 (x: Nat, y: Nat) : Nat = (fn f -> f (x, y)) f4
 *    =>
 *   op g4 (x: Nat, y: Nat) : Nat = (fn f -> f (x, y)) f4
 *  
 *   to lisp:
 *
 *     (defun f4-2 (x y) (Nat-Spec::+-2 x y))
 *     (defun g4-2 (x y) (f4-2 x y))
 *     
 *     (defun f4 (x) (f4-2 (car x) (cdr x)))
 *     (defun g4 (x) (g4-2 (car x) (cdr x)))
 *
 *  ----------------------------------------------------------------------------------------------------
 *)

%% The arity map stores the ops having a domain type consisting of a record (possibly subsetted)

type Gamma = List (String * Option (MSType * Nat))


op matchArity (match : MSMatch) : Nat =
 %%  When all patterns in the match are records of the same arity n >= 0, 
 %%  the arity of a match is n, otherwise it is 1.
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

 %%  t1 (t2)
 %%   =>
 %%  let x = t2 in t1 (x.1, ..., x.n)
 %%   -or-
 %%  let x = t2 in t1 {a = x.a, ..., z = x.z}

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

op convertToArity1 (spc        : Spec, 
                    gamma      : Gamma,
                    used_names : UsedNames,
                    term       : MSTerm)
 : MSTerm = 

 case termArity (spc, gamma, term) of
   | Some (dom, num) ->

     %%  eta expansion:
     %%
     %%  fn (y: Nat, z: Nat) -> x + y + z
     %%   =>
     %%  fn (apV: Nat * Nat) -> 
     %%    let x0 = apV in 
     %%    case (x0.1, x0.2) of (y, z) -> x + y + z

     %% by using "pV" as the prefix we pass the pV? test in reduceTerm, which
     %% allows use to include an ignore decl if the var is not used in the body

     let (name, used_names) = freshName ("apV", used_names) in
     let var  = (name, dom) in
     let vpat = VarPat (var, noPos)  in
     let vref = Var    (var, noPos)  in
     Lambda ([(vpat, 
               mkTrue (),
               mkArityApply (spc, dom, term, vref, used_names))],
              noPos)
   | _ -> term

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
     let t1 = normalizeArityTopLevel (spc, gamma, used_names, term) in
     let t2 = convertToArity1        (spc, gamma, used_names, t1)   in
     t2

   | Var _ -> convertToArity1 (spc, gamma, used_names, term)

   | Fun _ -> convertToArity1 (spc, gamma, used_names, term)

   | And (tm :: r_tms, _) ->
     let tm = normalizeArity (spc, gamma, used_names, tm) in
     And (tm :: r_tms, noPos)

   | tm -> tm

op SpecTransform.arityNormalize (spc : Spec) : Spec =
 let used_names = StringSet.fromList (qualifierIds spc.ops) in
 let 
   def revise dfn =
     let (tvs, typ, term) = unpackFirstTerm dfn                    in
     let used_names       = addLocalVars (term, used_names)        in
     let term1            = normalizeArityTopLevel (spc, 
                                                    [],  % gamma
                                                    used_names,
                                                    term)
     in
     maybePiTerm (tvs, TypedTerm (term1, typ, noPos))
 in
 let new_ops = 
     mapOpInfos (fn info -> 
                   let (old_decls, old_defs) = opInfoDeclsAndDefs info                     in
                   let new_defs              = map revise old_defs                         in
                   let new_dfn               = maybeAndTerm (old_decls ++ new_defs, noPos) in
                   info << {dfn = new_dfn})
                spc.ops
 in

 %% --------------------------------------------------------
 %% ignore arity normalization in types, axioms and theorems
 %% --------------------------------------------------------

 setOps (spc, new_ops)

endspec
