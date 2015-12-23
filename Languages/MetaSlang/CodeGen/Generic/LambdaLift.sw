(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(**
 Lambda lifting.
 ------------------------------------------------------------------------

 Perform lambda lifting in order to generation function definitions that
 work where only non-nested definitions are allowed.

 The lambda lifter is essentially a Johnson style lifter.
 See: Peyton Jones and Lester: Implementing functional languages, a tutorial.
 
 Assumption here is that all variables have unique names.
 **)

LambdaLift qualifying spec
 import /Languages/MetaSlang/Transformations/Simplify
 import /Languages/MetaSlang/CodeGen/Generic/ArityNormalize
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements

 type LiftInfo = {ident    : String,     % Name of original identifier for lambda lifted term.
		  name     : String,     % Name of lambda-lifted function.
		  freeVars : FreeVars,   % Free variables in body (excluding those in pattern).
		  closure  : MSTerm,     % Expression corresponding to name(freeVars)
		  pattern  : MSPattern,  % Pattern.
                  domain   : MSType,     % Type of pattern (including subtype)
                  range    : MSType,     % Type of op (including subtype)
		  body     : MSTerm      % Body of lambda lifted expression.
		 }
 %
 % The purpose of LiftInfo is to capture the situation where:
 % 
 % In the context where freeVars are declared we have:
 %
 %      ident = pattern -> body
 %
 % This is replaced by the context where no free variables are declared, and     
 %
 %    name = freeVars -> patterm -> body
 % 
 % and ident is replaced by name(freeVars) throughout the use of ident.
 % 
 % To target code where currying is not admitted, instead of the above we write: 
 %
 % name = (v,pattern) -> let freeVars = project(v) in body
 % 
 % and replace ident by 
 %
 %    closure: TranslationBuiltIn.makeClosure(name, freeVars)
 % 		   

(**
sjw: I made simulateClosures? an option so that the transformation could be used as a
MetaSlang -> MetaSlang transformation that makes free variables into explicit parameters
where possible and lifts local functions to global functions. The latter could be
made optional as well. It seems the allegro compiler handles global functions more 
efficiently, but cmulisp may do better with local functions.
**)
%% op simulateClosures? : Bool = false	% If false just use lambdas with free vars -- moved to SpecToLisp.sw and deprecated

 type Ops   = MapL.Map (String, LiftInfo)
 type LLEnv = {spc 	         : Spec, 
	       opers             : Ops, 
	       opName            : String, 
	       qName             : String, 
	       counter	         : Ref Nat, 
	       usedNames         : Ref StringSet.Set,
               simulateClosures? : Bool}

 type FreeVars = MSVars


(* 
 * MSTerm decorated with free variables in each sub-expression.
 *)

 type VarTerm = VarTermBody * FreeVars * Position
 type VarTermBody = 
  | Apply        VarTerm * VarTerm
  | Record       List (Id * VarTerm)
  | Bind         Binder * MSVars * VarTerm
  | The          MSVar * VarTerm
  | Let	         List (MSPattern * VarTerm) * VarTerm
  | LetRec       List (MSVar     * VarTerm) * VarTerm
  | Var          MSVar
  | Fun          MSFun * MSType
  | Lambda       VarMatch
  | IfThenElse   VarTerm * VarTerm * VarTerm
  | Seq          List VarTerm

 type VarMatch = List (MSPattern * MSTerm * VarTerm)
 op makeVarTerm: MSTerm -> VarTerm

 %% for debugging purposes...
 op undoVarTerm (vt : VarTerm) : MSTerm =
  let 
    def undo (body, _, pos) =
      case body of
        | Apply        (     vt1,      vt2) -> 
          Apply        (undo vt1, undo vt2, pos)

        | Record       pairs ->
          Record       (map (fn (id, vt) -> (id, undo vt)) pairs, pos)

        | Bind         (binder, vars,      vt) ->
          Bind         (binder, vars, undo vt, pos)

        | The          (var,      vt) ->
          The          (var, undo vt, pos)

        | Let	       (bindings, vt) ->
          Let	       (map (fn (pat, vt) -> (pat, undo vt)) bindings, undo vt, pos)

        | LetRec       (bindings, vt) ->
          LetRec       (map (fn (var, vt) -> (var, undo vt)) bindings, undo vt, pos)

        | Var          var ->
          Var          (var, pos)

        | Fun          (fun, typ) ->
          Fun          (fun, typ, pos)

        | Lambda       vmatch ->
          Lambda       (map (fn (pat, tm, vt) -> (pat, tm, undo vt)) vmatch, pos)

        | IfThenElse   (     vt1,      vt2,      vt3) ->
          IfThenElse   (undo vt1, undo vt2, undo vt3, pos)

        | Seq          vts ->
          Seq          (map undo vts, pos)
  in
  undo vt

 %% for debugging purposes...
 op printVarTerm (vt : VarTerm) : String = 
  printTerm (undoVarTerm vt)

(**
 op applyClosure : (A, B) Closure(A, B) * A -> B
 
 **)
(*
 * Free variables relative to environment supplying additional free variables associated
 * with variables that are to be bound to other terms with free variables.

 * Assumptions: 
	- All variables occur uniquely bound (fresh names have been generated).
	- Pattern matching compilation has been performed.
 *)

 (* Already defined in Utilities
def patternVars (pat:MSPattern): MSVars = 
   case pat of
     | VarPat       (v,              _) -> [v]
     | RecordPat    (fields,         _) -> foldr (fn ((_, p), vs)-> patternVars p ++ vs) [] fields
     | WildPat      _                   -> []
     | EmbedPat     (_, Some pat, _, _) -> patternVars pat
     | EmbedPat     (_, None, _,     _) -> []
     | AliasPat     (pat1, pat2,     _) -> concat (patternVars pat1, patternVars pat2)
     | QuotientPat  (pat, _,         _) -> patternVars pat
     | RestrictedPat(pat, _,         _) -> patternVars pat
     | TypedPat     (pat, _,         _) -> patternVars pat
     | StringPat    _                   -> []
     | BoolPat      _                   -> []
     | CharPat      _                   -> []
     | NatPat       _                   -> []
     | _ -> System.fail("Unexpected pattern in match normalized expression: "^printPattern pat)
*)

 op makeVarTerm (term : MSTerm) : VarTerm = 
   %let _ = String.writeLine("{") in
   %let _ = String.writeLine("makeVarTerm("^MetaSlangPrint.printTerm term^")...") in
   %let res =
   case term of

     | Let (decls, body, a) -> 
       let decls = List.map (fn (pat, term) -> (pat, makeVarTerm term)) decls in
       let vars  = flatten (List.map (fn (_, (_, vars, _)) -> vars) decls) in
       let letVars = flatten (List.map (fn (pat, _) -> patternVars pat) decls) in
       let body as (_, bodyVars, _) = makeVarTerm body in
       let vars = removeDuplicates (vars ++ diffVs (bodyVars, letVars)) in
       (Let (decls, body), vars, a) 

     | LetRec (decls, body, a) -> 
       let decls = List.map (fn (v, term) -> (v, makeVarTerm term)) decls in
       let vars  = flatten (List.map (fn (_, (_, vars, _)) -> vars) decls) in
       let letVars = List.map (fn (v, _) -> v) decls in
       let body as (_, bodyVars, _) = makeVarTerm body in
       let vars = removeDuplicates (vars ++ bodyVars) in
       let diffVars = diffVs (vars, letVars) in
       (LetRec (decls, body), diffVars, a)

     | Lambda (match, a) -> 
       % let (pat, _, _)::_ = match in
       %let _ = String.writeLine ("  lambda-term, pattern: "^MetaSlangPrint.printPattern pat) in
       let match = map (fn (pat, cond, term) -> (pat, cond, makeVarTerm term)) match in
       let vars  = flatten (map (fn (_, _, (_, vars, _)) -> vars) match) in
       let boundVars = flatten (map (fn (pat, _, _) -> patternVars pat) match) in
       let vars = diffVs (vars, boundVars) in
       (Lambda (match), vars, a)
       
     | Var (v, a) -> (Var v, [v], a)

     | Fun (f, s, a) -> (Fun (f, s), [], a)

     | IfThenElse (t1, t2, t3, a) -> 
       let t1 as (_, vs1, _) = makeVarTerm t1 in
       let t2 as (_, vs2, _) = makeVarTerm t2 in
       let t3 as (_, vs3, _) = makeVarTerm t3 in
       (IfThenElse (t1, t2, t3), removeDuplicates (vs1 ++ vs2 ++ vs3), a)
       
     | Seq (terms, a) -> 
       let terms = List.map makeVarTerm terms in
       let vars  = flatten (List.map (fn (_, vs, _) -> vs) terms) in
       let vars  = removeDuplicates (vars) in
       (Seq terms, vars, a)

     | Apply (t1, t2, a) -> 
       let t1 as (_, vs1, _) = makeVarTerm t1 in
       let t2 as (_, vs2, _) = makeVarTerm t2 in
       (Apply (t1, t2), removeDuplicates (vs1 ++ vs2), a)

     | Record (fields, a) -> 
       let fields = List.map (fn (id, t) -> (id, makeVarTerm t)) fields in
       let vars   = flatten (List.map (fn (_, (_, vs, _)) -> vs) fields) in
       let vars   = removeDuplicates vars in
       (Record fields, vars, a)

     | Bind (binder, bound, body, a) -> 
       let body as (_, vs, _) = makeVarTerm body in
       let vars = diffVs (vs, bound) in
       (Bind (binder, bound, body), vars, a)

     | The (var, body, a) -> 
       let body as (_, vs, _) = makeVarTerm body in
       let vars = diffVs (vs, [var]) in
       (The (var, body), vars, a)

     | TypedTerm (t, srt, a) ->
       let (t, vars, _) = makeVarTerm t in
       (t, vars, a)

     | _ -> System.fail("makeVarTerm can't handle "^printTerm term)

   %in
   %let (_, vars) = res in
   %let _ = String.writeLine("vars: "^varsToString(vars)) in
   %let _ = String.writeLine("}") in
   %res

 op diffVs (l1 : MSVars, l2 : MSVars) : MSVars =
  case l1 of
    | [] -> []
    | hd :: tl -> 
      if memberPred (hd, l2, fn ((id1, _), (id2, _)) -> id1 = id2) then
        diffVs (tl, l2) 
      else 
        hd :: diffVs (tl, l2)

 op [a] memberPred (x : a, l : List a, p : a * a -> Bool) : Bool =
  case l of
    | []     -> false
    | hd::tl -> if p (x, hd) then true else memberPred (x, tl, p)

 % Build:
 %
 %    closure: TranslationBuiltIn.makeClosure (name, freeVars)
 % 		   

 op makeClosureOp () : MSTerm = 
   let alpha = mkTyVar "alpha" in
   let beta  = mkTyVar "beta" in
   let gamma = mkTyVar "gamma" in
   let srt1  = mkArrow (mkProduct [alpha, beta], gamma) in
   let srt2  = mkArrow (mkProduct [srt1, alpha], mkArrow (beta, gamma)) in
   %           ((a * b) -> c) * a  ->  (b -> c)     
   %
   % Later change this to:
   % mkArrow (mkProduct [srt1, alpha], 
   %          (Base (Qualified ("TranslationBuiltIn", "Closure"), [beta, gamma]))) 
   %
   %
   mkOp (Qualified ("TranslationBuiltIn", "makeClosure"), srt2)


 op makeUnitClosureOp () : MSTerm = 
   let alpha = mkTyVar "alpha" in
   let beta  = mkTyVar "beta"  in
   mkOp (Qualified ("TranslationBuiltIn", "makeUnitClosure"), 
	 mkArrow (mkArrow (alpha, beta), 
		  (Base (Qualified ("TranslationBuiltIn", "Closure"), 
			 [alpha, beta], noPos))))

 %
 % (dom type should be a list of dom types corresponding to record/tuple patterns in functions)
 %
 op makeClosureApplication (env      : LLEnv, 
                            name     : String, 
                            freeVars : FreeVars,
                            pat      : MSPattern, 
                            dom      : MSType, 
                            rng      : MSType) 
  : MSTerm = 
  let qualname = Qualified (env.qName, name) in
  %let dom = patternType pat in
  if freeVars = [] then  
    mkOp (qualname, mkArrow (dom, rng))
  else if ~env.simulateClosures? then
    let pats  = patternToList pat in
    let oVars = foldl (fn (result, p) ->
                         let newV = case p of
                                      | VarPat (v, _) -> v
                                      | _ -> ("Xv-"^ (Nat.show (length result)), 
                                              patternType p)
                         in 
                         result ++ [newV])
                      []
                      pats
    in
    mkLambda (mkTuplePat (map mkVarPat oVars), 
              mkAppl (mkOp (qualname, 
                            mkArrow (mkProduct (productTypes (getSpecEnv env, dom)
                                                  ++ 
                                                  map (fn (_, varSrt) -> varSrt) freeVars), 
                                     rng)), 
                      map mkVar (oVars ++ freeVars)))
  else
    let farg =
        case freeVars of
          | [fv] -> mkVar fv 
          | _ -> ArityNormalize.mkArityTuple (getSpecEnv env, 
                                              mkTuple (map mkVar freeVars))
    in
    let ftype = inferType (getSpecEnv env, farg) in
    let oper  = mkOp (qualname, mkArrow (mkProduct [ftype, dom], rng)) in
    mkApply (makeClosureOp (), 
             mkTuple[oper, farg])
    

 op makeLiftInfo (env  : LLEnv, 
                  id   : String, 
                  name : String, 
                  pat  : MSPattern, 
                  body : MSTerm,
                  dom  : MSType, 
                  rng  : MSType, 
                  vars : FreeVars)
  : LiftInfo = 
  {ident    = id, 
   name     = name, 
   freeVars = vars, 
   closure  = makeClosureApplication (env, name, vars, pat, dom, rng), 
   pattern  = pat, 
   domain   = dom,
   range    = rng,
   body     = body}

 op insertOper (liftInfo : LiftInfo, env : LLEnv) : LLEnv =
   env << {opers = update (env.opers, liftInfo.ident, liftInfo)}

 op freshName (name : Id, env : LLEnv) : Id =
  let uniqueName = StringUtilities.freshName (name, !env.usedNames) in
  let _ = 
      env.usedNames := StringSet.add (!env.usedNames, uniqueName) 
  in
  uniqueName

 op actualFreeVars (env : LLEnv, vars : FreeVars) : FreeVars =
  let
     def lookup (v as (id, _)) = 
       case apply (env.opers, id) of
	 | None -> [v]
	 | Some info -> info.freeVars
   in 
     removeDuplicates (flatten (List.map lookup vars))

 op removeBound (variableList : FreeVars, boundVars : List (Id * MSType)) 
  : FreeVars = 
  case boundVars of
    | [] -> variableList 
    | (id, _) :: bvs -> 
      let
        def removeOne vars = 
          case vars of
            | [] -> []
            | (v as (id2, _)) :: vs -> 
              if id2 = id then 
                removeOne vs 
              else 
                v :: removeOne vs
      in
      removeBound (removeOne variableList, bvs)

 % ensure that the term is a closure
 op ensureClosure (env : LLEnv, term : MSTerm) : MSTerm =
   if ~ env.simulateClosures? then 
     term
   else
     let closureOp     = makeClosureOp     () in
     let unitClosureOp = makeUnitClosureOp () in
     case term of
       | Apply (t1, t2, _) ->
         if (t1 = closureOp) || (t1 = unitClosureOp) then 
	   term
	 else 
	   mkApply (makeUnitClosureOp (), term)
       | _  -> 
	   mkApply (makeUnitClosureOp (), term)

(*

  Lambda lifting inserts ops with the following types:

   op clos : ('a * 'b -> 'c) * 'a -> ('b -> 'c)

 *)

 op lambdaLiftApply (env    : LLEnv, 
                     vars   : FreeVars, 
                     vterm1 : VarTerm, 
                     vterm2 : VarTerm,
                     pos    : Position)
  : List LiftInfo * MSTerm =
  case vterm1 of
    | (Lambda (match as _::_), vars1, lpos) ->
      let (infos1, match) =
          foldl (fn ((infos, match), (p, t1, trm2 as (t2, vars, _))) -> 
                   %let (infos1, t1) = lambdaLiftTerm (env, (t1, [])) in
                   let (infos2, t2) = lambdaLiftTerm (env, trm2) in
                   let match = match ++ [(p, t1, t2)] in
                   let infos = infos ++ infos2        in
                   (infos, match))
                ([], []) 
                match
      in
      let (infos2, t2) = lambdaLiftTerm (env, vterm2) in
      (infos1 ++ infos2, 
       simplifiedApply (Lambda (match, lpos), t2, getSpecEnv env))

    | (Lambda [(pat, Fun (Bool true, _, _), body)], vars1, _) ->
      lambdaLiftTerm (env, 
                      (Let ([(pat, vterm2)], body), 
                       vars ++ vars1, pos))

    % Distinguish between pure function application and
    % application of closure.

    | _ ->
      let (opers1, nt1) = 
          case vterm1 of
            | (Fun (f, s), _, fpos) -> ([], Fun (f, s, fpos))
            | _ -> lambdaLiftTerm (env, vterm1)
      in
      let (opers2, nt2) = lambdaLiftTerm (env, vterm2) in
      let opers = opers1 ++ opers2 in
      let tm = 
          case nt1 of
            | Fun f ->
              if ~env.simulateClosures? then
                (case vterm1 of
                   | (Var (id, srt), _, _) ->
                     (case apply (env.opers, id) of
                        | Some {ident, name, freeVars, closure, pattern, domain, range, body} ->
                          let oldArgs = termToList nt2 in
                          let newArgs = map mkVar freeVars in
                          simplifiedApply (nt1, mkTuple (oldArgs ++ newArgs), getSpecEnv env)
                        | _ -> 
                          mkApply (nt1, nt2))
                   | _ -> 
                     mkApply (nt1, nt2))
              else 
                mkApply (nt1, nt2)

            | _ ->
              if ~env.simulateClosures? then
                simplifiedApply (nt1, nt2, getSpecEnv env)
              else 
                %% closure has type ('a * 'b -> 'c) * 'a -> ('b -> 'c)
                %% so we need (('a * 'b -> 'c) * 'a -> ('b -> 'c)) * a -> (b -> c)
                let argument = mkTuple [nt1, nt2] in
                let alpha    = mkTyVar "alpha" in
                let beta     = mkTyVar "beta" in
                let gamma    = mkTyVar "gamma" in
                let srt      = mkArrow (mkProduct [mkArrow (mkProduct [mkArrow (mkProduct [alpha, beta],
                                                                                gamma),
                                                                       alpha],
                                                            mkArrow (beta, gamma)),
                                                   alpha], 
                                        mkArrow (beta, gamma))
                in
                let fnOp     = mkOp (Qualified ("TranslationBuiltIn", "applyClosure"), srt) in
                mkApply (fnOp, argument)
      in
      (opers, tm)

 op lambdaLiftLambda (env   : LLEnv,
                      vars  : FreeVars, 
                      match : List (MSPattern * MSTerm * VarTerm),
                      pos   : Position)
  : List LiftInfo * MSTerm =
  case match of
    | [(pat, cond, body)] -> 
       let (opers, body) = lambdaLiftTerm (env, body) in
       if ~env.simulateClosures? then
	 (opers, 
	  Lambda ([(pat, cond, body)], pos))
       else
	 let num = !(env.counter) in
	 let _ = env.counter := num + 1 in
	 let name = env.opName ^ "__internal_" ^ (Nat.show num) in

	 %let _ = String.writeLine ("  new oper: "^name) in

	 let ident = name ^ "__closure" in
	 let vars = actualFreeVars (env, vars) in

	 let liftInfo = makeLiftInfo (env, ident, name, pat, body,
                                      patternType pat,
                                      inferType (getSpecEnv env, body),
                                      vars)
         in

	 % MA: make sure that liftInfo.closure is really a closure
	 let liftInfoClosure = ensureClosure (env, liftInfo.closure) in
	 (liftInfo::opers, 
	  liftInfoClosure)

    | (pat, cond, body) :: _ ->
      let argTypes = productTypes (getSpecEnv env, patternType pat) in
      let newVs = makeNewVars argTypes in
      lambdaLiftTerm (env, 
                      (Lambda [(mkTuplePat (map mkVarPat newVs), 
                                mkTrue (), 
                                (Apply ((Lambda match, vars, pos), 
                                        mkVarTermTuple (map (fn x -> (Var x, [], pos)) newVs)), 
                                 vars, pos))], 
                       vars, 
                       pos))
       
 op lambdaLiftLet (env   : LLEnv,
                   vars  : FreeVars, 
                   decls : List (MSPattern * VarTerm),
                   body  : VarTerm,
                   pos   : Position)
  : List LiftInfo * MSTerm =
  (*
   * Given Let definition:
   * 
   * let a = body_1(x, y)  and b = body_2(y, z) in body(a, b)
   * 
   * Since names are unique after the renaming 
   * one can treat the let-declaration sequentially.
   * 
   * After pattern matching we can assume that the patterns 
   * a and b are always of the form (VarPat v).
   * 
   * Given let definition:
   *      let a = fn pat -> body_a (x, y) in body
   *  1. Get free variables from body_a to get the form
   * 
   *      let a = (fn (x, y) -> fn pat -> body_a (x, y)) (x, y) in body
   * 
   *  2. Lambda lift body_a
   * 
   *      let a = (fn (x, y) -> fn pat -> body_a_lifted (x, y)) (x, y) in body
   * 
   *  3. Insert association:
   *      [ a |-> (a_op, (x, y), fn pat -> body_a_lifted (x, y), typeOf_a) ]
   *     in env.
   * 
   *  4. Recursively lambda lift body (a)
   * 
   *  5. Return with other ops, also (a_op, (x, y), fn pat -> body_a_lifted (x, y), typeOf_a).
   * 
   * Given let definition:
   *      let a = body_a (x, y) in body
   *   1. Lambda lift body_a
   *   2. Recursively lambda lift body
   *   3. Return let a = body_a_lifted (x, y) in body_lifted
   * 
   *)

   let opName = env.opName in
   let
     def liftDecl ((pat, term as (trm, vars, _)), (opers, env, decls)) =
       case (pat, trm) of
         | (VarPat ((id, srt), _), Lambda ([(pat2, cond, body)])) -> 
           let (opers2, body) = lambdaLiftTerm (env, body) in
           let name = freshName (opName ^ "__" ^ id, env) in
           let vars = actualFreeVars (env, vars) in
           let oper = makeLiftInfo (env, id, name, pat2, body,
                                    domain (getSpecEnv env, srt),
                                    range (getSpecEnv env, srt),
                                    vars)
           in
           let env  = insertOper (oper, env) in
           (oper::opers ++ opers2, env, decls)
         | _ ->
           let (opers2, term) = lambdaLiftTerm (env, term) in
           (opers ++ opers2, 
            env, 
            (pat, term) :: decls)
   in
   let (opers1, env, decls) = foldr liftDecl ([], env, []) decls in
   let (opers2, body) = lambdaLiftTerm (env, body) in
   (opers1 ++ opers2, 
    case decls of
      | [] -> body
      | _  -> Let (decls, body, pos))


 op lambdaLiftLetRec (env   : LLEnv,
                      vars  : FreeVars, 
                      decls : List (MSVar * VarTerm),
                      body  : VarTerm,
                      pos   : Position)
  : List LiftInfo * MSTerm =
  (*
   * Given Let-rec definition:
   * 
   * let
   *      def f = fn pat_1 -> body_1 (f, g, x, y)
   *      def g = fn pat_2 -> body_2 (f, g, y, z)
   * in
   *      body (f, g)
   * 
   * 1. Get free variables from body_1 and body_2 to get the form:
   * 
   *   let
   *      def f = fn  (x, y, z) -> fn pat_1 -> body_1 (f, g, x, y)
   *      def g = fn (x, y, z) -> fn pat_2 -> body_2 (f, g, y, z)
   *   in
   *      body (f, g)
   * 
   * 2. Generate associations:
   * 
   *      opers:
   *      [
   *       f |-> (f_op, (x, y, z), pat_1, body_1 (f, g, x, y)), 
   *       g |-> (g_op, (x, y, z), pat_2, body_2 (f, g, y, z))
   *      ]
   * 
   *    update the environment with these associations    
   * 
   * 3. Lambda lift body_1 and body_2.
   * 
   *   let
   *      def f = fn (x, y, z) -> fn pat_1 -> body_1_lifted (f_op (x, y, z), g_op (x, y, z), x, y)
   *      def g = fn (x, y, z) -> fn pat_2 -> body_2_lifted (f_op (x, y, z), g_op (x, y, z), y, z)
   *   in
   *      body (f, g)
   * 
   * 4. Recursively lambda lift body (f, g)
   * 
   * 5. Return updated assocations:
   * 
   *      opers:
   *      [
   *       f |-> (f_op, (x, y, z), fn pat_1 -> body_1_lifted (f_op (x, y, z), g_op (x, y, z), x, y), typeOf_f_op), 
   *       g |-> (g_op, (x, y, z), fn pat_2 -> body_2_lifted (f_op (x, y, z), g_op (x, y, z), y, z), typeOf_g_op)
   *      ]
   * 
   *    update the environment with these associations.    
   *)

   % Step 1.
   let opName = env.opName in
   let (free, bound) = 
       foldr (fn ((v, (_, vars, _)), (free, bound)) ->
                (vars ++ free, v::bound))
             ([], []) 
             decls 
   in
   let vars = removeBound (free, bound) in
   let vars = actualFreeVars (env, vars) in

   % Step 2.
   let tmpOpers =
       map (fn (v as (id, srt), (Lambda ([(pat, _, body)]), _, _)) ->
              let name = freshName (opName ^ "__" ^ id, env) in
              let dom = domain(getSpecEnv env, srt) in
              (body, 
               makeLiftInfo (env, id, name, pat, mkTrue () (* Dummy body *),
                             dom, range (getSpecEnv env, srt), 
                             vars))
             | _ -> System.fail "liftDecl Non-lambda abstracted term")
           decls
   in
   let env1 = foldl (fn (env, (_, oper)) -> insertOper (oper, env)) env tmpOpers in

   % Step 3.
   let
     def liftDecl ((realBody, {ident, name, pattern, domain, range, closure, body, freeVars}), opers) = 
       let (opers2, body) = lambdaLiftTerm (env1, realBody) in
       let oper = makeLiftInfo (env, ident, name, pattern, body, domain, range, freeVars) in
       oper::opers ++ opers2
   in
   let opers1 = foldr liftDecl [] tmpOpers in

   % Step 4.
   let (opers2, body) = lambdaLiftTerm (env1, body) in
   (opers1 ++ opers2, body) 

 op lambdaLiftVar (env  : LLEnv, 
                   vars : FreeVars, 
                   id   : Id, 
                   typ  : MSType,
                   pos  : Position)
  : List LiftInfo * MSTerm =
  case apply (env.opers, id) of
    | Some liftInfo -> 
      let liftInfoClosure = ensureClosure (env, liftInfo.closure) in
      ([], liftInfoClosure)
      %of Some (liftInfo:LiftInfo) -> ([], mkApply (makeUnitClosureOp (), liftInfo.closure))
    | _ ->
      ([], (Var ((id, typ), pos)))

 op lambdaLiftFun (env  : LLEnv, 
                   vars : FreeVars, 
                   f    : MSFun,
                   typ  : MSType,
                   pos  : Position)
  : List LiftInfo * MSTerm =
  % If returning a function not taking arguments, then 
  % return a closure version of it.
  let tm = mkFun (f, typ) in
  let tm =
      if ~env.simulateClosures? then 
        tm
      else
        let typ = unfoldToArrow (getSpecEnv env, typ) in
        case typ of
          | (Arrow _) -> mkApply (makeUnitClosureOp (), tm)
          | (TyVar _) -> mkApply (makeUnitClosureOp (), tm)
          | _ -> tm
  in
  ([], tm)

 op lambdaLiftIf (env  : LLEnv, 
                  vars : FreeVars, 
                  t1   : VarTerm,
                  t2   : VarTerm,
                  t3   : VarTerm,
                  pos  : Position)
  : List LiftInfo * MSTerm =
  let (opers1, t1) = lambdaLiftTerm (env, t1) in
  let (opers2, t2) = lambdaLiftTerm (env, t2) in
  let (opers3, t3) = lambdaLiftTerm (env, t3) in
  (opers1 ++ opers2 ++ opers3, 
   IfThenElse (t1, t2, t3, pos))

 op lambdaLiftSeq (env   : LLEnv, 
                   vars  : FreeVars, 
                   terms : List VarTerm,
                   pos   : Position)
  : List LiftInfo * MSTerm =
  let
    def liftRec (t, (opers, terms)) = 
      let (opers2, t) = lambdaLiftTerm (env, t) in
      (opers ++ opers2, t :: terms)
  in
  let (opers, terms) = foldr liftRec ([], []) terms in
  (opers, Seq (terms, pos))

 op lambdaLiftRecord (env    : LLEnv, 
                      vars   : FreeVars, 
                      fields : List (Id * VarTerm),
                      pos    : Position)
  : List LiftInfo * MSTerm =
  let
    def liftRec ((id, t), (opers, fields)) = 
      let (opers2, t) = lambdaLiftTerm (env, t) in
      (opers ++ opers2, 
       (id, t) :: fields)
  in
  let (opers, fields) = foldr liftRec ([], []) fields in
  (opers, (Record (fields, pos)))

 op lambdaLiftTerm (env                      : LLEnv, 
                    term as (trm, vars, pos) : VarTerm)
  : List LiftInfo * MSTerm =
  case trm of
    | Apply      (vt1, vt2)    -> lambdaLiftApply  (env, vars, vt1, vt2,    pos)
    | Lambda     matches       -> lambdaLiftLambda (env, vars, matches,     pos)
    | Let        (decls, body) -> lambdaLiftLet    (env, vars, decls, body, pos)
    | LetRec     (decls, body) -> lambdaLiftLetRec (env, vars, decls, body, pos)
    | Var        (id, typ)     -> lambdaLiftVar    (env, vars, id, typ,     pos)
    | Fun        (f,  typ)     -> lambdaLiftFun    (env, vars, f,  typ,     pos)
    | IfThenElse (t1, t2, t3)  -> lambdaLiftIf     (env, vars, t1, t2, t3,  pos)
    | Seq        terms         -> lambdaLiftSeq    (env, vars, terms,       pos)
    | Record     fields        -> lambdaLiftRecord (env, vars, fields,      pos)

    | Bind       (binder, bound, body) -> 
      let (opers, liftBody) = lambdaLiftTerm (env, body) in
      (opers, mkBind (binder, bound, liftBody))

    | The (var, body) -> 
      let (opers, liftBody) = lambdaLiftTerm (env, body) in
      (opers, mkThe (var, liftBody))

    | _ -> System.fail "Unexpected term"

 op makeNewVars (types : MSTypes) : MSVars =
  foldl (fn (vars, typ) ->
           let var = ("llp-" ^ Nat.show (length vars), typ) in
            var :: vars)
         [] 
         types

 op mkVarTermTuple (vts : List VarTerm) : VarTerm =
  case vts of
    | [vt] -> vt
    | _ -> (Record (tagTuple vts), [], noPos)

 op abstractName (env         : LLEnv,
                  names       : QualifiedIds,
                  name        : String,
                  freeVars    : FreeVars,
                  pattern     : MSPattern,
                  domain      : MSType,
                  range       : MSType,
                  body        : MSTerm,
                  extra_conds : MSTerms)
  : OpInfo =
  if ~env.simulateClosures? then
    let oldPatLst  = patternToList pattern in
    let newPattern = mkTuplePat (oldPatLst ++ map mkVarPat freeVars) in
    let domType    = addSubtypeInfo(newPattern,pattern,domain,extra_conds,getSpecEnv env) in
    let new_type   = mkArrow (domType, range) in
    let pos        = termAnn(body) in
    let new_term   = withAnnT(mkLambda (newPattern, body), pos) in
    let tvs        = freeTyVars new_type in
    {names           = names,
     fixity          = Nonfix, 
     dfn             = maybePiTerm(tvs, TypedTerm (new_term, new_type, termAnn body)),
     fullyQualified? = false}
  else
    let varType       = mkProduct (List.map (fn (_, srt) -> srt) freeVars) in
    let closureVar    = ("closure-var", varType) in
    let closureArg    = mkVar    closureVar in
    let closureVarPat = mkVarPat closureVar in
    let newPattern =
        if empty? freeVars then
          pattern
        else 
          RecordPat ([("1", closureVarPat), ("2", pattern)], noPos)
    in	
    let 
      def mkProject ((id, srt), n) = 
        (mkVarPat ((id, srt)), 
         mkApply ((Fun (Project (Nat.show n), mkArrow (varType, srt), noPos)), 
                  closureArg))
    in
    let newBody = 
        case freeVars of
          | [] -> body
          | [v] -> mkLet ([(mkVarPat v, closureArg)], body)
          | _ -> 
            let (decls, n) = 
                foldl (fn ((decls, n), v) ->
                         (mkProject (v, n) :: decls, 
                          n + 1))
                      ([], 1) 
                      freeVars
            in
            mkLet (decls, body)
    in
    let new_type = mkArrow (patternType newPattern, range) in
    let new_term = withAnnT(mkLambda (newPattern, newBody), termAnn body) in
    {names           = names,
     fixity          = Nonfix, 
     dfn             = TypedTerm (new_term, new_type, termAnn body),
     fullyQualified? = false}

 op addSubtypeInfo (new_pat     : MSPattern, 
                    old_pat     : MSPattern, 
                    orig_ty     : MSType, 
                    extra_conds : MSTerms, 
                    spc         : Spec)
  : MSType =
  let ty            = patternType new_pat in
  let new_vars      = patternVars new_pat in
  let condns_to_add = filter (fn tm -> forall? (fn v -> inVars?(v, new_vars)) (freeVars tm)) extra_conds in
  case orig_ty of
    | Subtype (_, pred, a) ->
      (case patternToTerm old_pat of

         | Some old_var_tm ->
           let condns_to_add = mkApply(pred, old_var_tm) :: condns_to_add in
           let conds = mkSimpConj condns_to_add in
           Subtype(ty, simplify spc (mkLambda (new_pat, conds)), a)

         | None | condns_to_add ~= [] -> 
           let conds = mkSimpConj condns_to_add in
           Subtype(ty, simplify spc (mkLambda (new_pat, conds)), a)

         | _ -> ty)

    | _ | condns_to_add ~= [] -> 
      let conds = mkSimpConj condns_to_add in
      Subtype(ty, simplify spc (mkLambda (new_pat, conds)), typeAnn ty)

    | _ -> ty

 op getSpecEnv (env : LLEnv) : Spec =
  env.spc			% Better be defined

 op varsToString (vars : MSVars) : String =
  (foldl (fn (s, v as (id, srt)) ->
            s ^ (if s = "[" then "" else " ")
            ^ id ^ ":" ^ printType srt)
         "[" 
         vars)
  ^ "]"

 op SpecTransform.lambdaLift (spc : Spec) (simulateClosures? : Bool) : Spec =
  lambdaLiftInternal (spc, true, simulateClosures?, [])

 op lambdaLiftInternal (spc               : Spec, 
                        imports?          : Bool, 
                        simulateClosures? : Bool,
                        just_these        : List (OpName * Ids))
  : Spec =
  let counter = Ref 1 : Ref Nat in
  %% The 'just_these' argument was added to allow deconflictUpdates to lambda-lift just 
  %% those ops containing local defs with stateful accesses and/or updates, even when 
  %% lambda-lifting would normally not be done (as for lisp generation).
  let process_all_ops? =
      case just_these of
        | [] -> true
        | _ -> false
  in
  let 
    def mkEnv (qname, name) =
      {opName            = name, 
       qName             = qname, 
       spc               = spc, 
       counter           = counter, 
       opers             = emptyMap, 
       usedNames         = Ref empty,
       simulateClosures? = simulateClosures?} 

    def insertOpers (opers, q, result, extra_conds) =
      case opers of
	 | [] -> (result)
	 | {name = id, ident, pattern, domain, range, freeVars, body, closure}::m_opers -> 
           let names  = [Qualified (q, id)] in	 
	   let info   = abstractName (mkEnv (q, id), names, id, freeVars, pattern, domain, range, body, extra_conds) in
	   let result = addNewOpAux (info, result, true, 0, None, noPos) in
	   insertOpers (m_opers, q, result, extra_conds)

     def doOp (q, id, opinfo, result, decl?, refine_num, info, a) = 
       % let _ = writeLine ("lambdaLift \""^id^"\"...") in
       if ~ (definedOpInfo? opinfo) then
         let opinfo = opinfo << {names = [Qualified (q, id)]} in
         addNewOpAux (opinfo, result, decl?, refine_num, info, a)
       else
         let trps            = unpackTypedTerms (opinfo.dfn) in
         let (tvs, ty, term) = nthRefinement(trps, refine_num) in
         if anyTerm? term then
           let opinfo = opinfo << {names = [Qualified (q, id)]} in
           addNewOpAux (opinfo, result, decl?, refine_num, info, a)
         else
         let new_id          = if refine_num = 0 then id else id ^ "__" ^ show refine_num in
         let env             = mkEnv (q, new_id)                                          in
	 case term of 
	   | Lambda ([(pat, cond, body)], a) ->
	     let body                = makeVarTerm body                                            in
	     let (opers, body)       = lambdaLiftTerm (env, body)                                  in
	     let term                = Lambda ([(pat, cond, body)], a)                             in
	     let new_dfn             = maybePiAndTypedTerm(replaceNthRefinement(trps, refine_num, (tvs, ty, term))) in
             let new_opinfo            = opinfo << {names = [Qualified (q, id)], dfn   = new_dfn}      in
	     let result              = addNewOpAux (new_opinfo, result, decl?, refine_num, info, a)  in
             let (_, extra_conds, _) = patternToTermPlusExConds pat                                in % restrictions
             insertOpers (reverse opers, q, result, extra_conds)

	   | _ ->
	     let term          = makeVarTerm term                                             in
	     let (opers, term) = lambdaLiftTerm (env, term)                                   in
	     let new_dfn       = maybePiAndTypedTerm(replaceNthRefinement(trps, refine_num, (tvs, ty, term))) in
             let new_opinfo    = opinfo << {names = [Qualified (q, id)], dfn   = new_dfn}     in
	     let result        = addNewOpAux (new_opinfo, result, decl?, refine_num, info, a) in
             insertOpers (reverse opers, q, result, [])

     def doProp ((pt, pn as Qualified (qname, name), tvs, fmla, pos), (r_elts, r_ops)) =
       let env           = mkEnv (qname, name)                in
       let pos           = termAnn fmla                       in
       let fmla          = withAnnT (termInnerTerm fmla, pos) in
       let term          = makeVarTerm fmla                   in
       let (opers, term) = lambdaLiftTerm (env, term)         in
       let newProp       = (pt, pn, tvs, term, noPos)         in
       let new_elts      = (Property newProp) :: r_elts       in
       let result        = (new_elts, r_ops)                  in
       %% Could get extra_conds from context
       insertOpers (reverse opers, qname, result, [])

     def process_op? name =
       process_all_ops? || (exists? (fn (op_name, _) -> name = op_name) just_these)

     def liftElts (elts, result) =
       foldr (fn (el, result as (r_elts, r_ops)) ->
                case el of
                  | Import (s_tm,i_sp,s_elts,a) | imports? ->
                    let (new_elts, new_ops) = liftElts (s_elts, ([], r_ops)) in
                    let new_elt  = Import (s_tm, i_sp, new_elts, a) in
                    let new_elts = new_elt :: r_elts in
                    (new_elts, new_ops)

                  | Op (name as Qualified(q,id), true, a) | process_op? name -> % true means decl includes def
                    (case findAQualifierMap(r_ops,q,id) of
                       | Some opinfo -> doOp (q, id, opinfo, result, true, 0, None, a)
                       | _ ->
                         let _ = writeLine ("LambdaLift saw Op element not in qmap : " ^ q ^ "." ^ id) in
                         let new_elts = el :: r_elts in
                         (new_elts, r_ops))

                  | OpDef (name as Qualified(q,id), refine_num, opt_info, a) | process_op? name ->
                    (case findAQualifierMap (r_ops, q, id) of
                       | Some opinfo -> doOp (q, id, opinfo, result, false, refine_num, opt_info, a)
                       | _ ->
                         let _ = writeLine ("LambdaLift saw OpDef element not in qmap : " ^ 
                                              q ^ "." ^ id ^ 
                                              " [refinement number " ^ anyToString refine_num ^ "]") 
                         in
                         let new_elts = el :: r_elts in
                         (new_elts, r_ops))

                  | Property p | process_all_ops? -> doProp (p, result)

                  | _ -> 
                    let new_elts = el :: r_elts in
                    (new_elts, r_ops))
             result
             elts
   in 
   let (newElts,newOps) = liftElts(spc.elements, ([],spc.ops)) in
   let new_spc = spc << {ops        = newOps, 
                         elements   = newElts}
   in
   new_spc

 % op  addNewOp : [a] QualifiedId * Fixity * ATerm a * ASpec a -> ASpec a
 % def addNewOp (name as Qualified (q, id), fixity, dfn, spc) =
 %   let info = {names = [name],
 %	       fixity = fixity, 
 %	       dfn    = dfn,
 %	       fullyQualified? = false}
 %   in
 %     addNewOpAux (info, spc)

 op addNewOpAux (info       : OpInfo, 
                 (elts : SpecElements, 
                  ops  : OpMap), 
                 decl?      : Bool, 
                 refine_num : Nat, 
                 pf_opt       : Option Proof, 
                 pos        : Position) 
  : SpecElements * OpMap =
  let name as Qualified (q, id) = primaryOpName info in
  let new_elt = if decl? then 
                  Op (name, true, pos) 
                else 
                  OpDef (name, refine_num, pf_opt, pos)
  in
  let new_elts = new_elt :: elts in
  let new_ops  = insertAQualifierMap (ops, q, id, info) in
  (new_elts, new_ops)

endspec

