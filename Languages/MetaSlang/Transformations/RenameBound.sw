
%% Rename bound variables so they're all unique.
RenameBound qualifying
spec
  import /Library/Legacy/DataStructures/ListPair
  import NameSupply
  import ../Specs/StandardSpec

  %% Environment

  sort Environment = Ref (StringMap(String))
  sort Term = MS.Term

  op emptyEnv : () -> Environment
  op insertEnv : Environment -> (String * String) -> ()
  op lookupEnv : Environment -> String -> Option (String)
  op savingEnv : fa(a) Environment -> (() -> a) -> a

  def emptyEnv () =
    Ref (StringMap.empty)

  def insertEnv env (n1, n2) =
    env := StringMap.insert(! env,n1, n2)

  def lookupEnv env n =
    StringMap.find(! env, n)

  def savingEnv env f =
    let e = ! env in
    let a = f () in
    let _ = env := e in
    a

  %% Contexts
  sort Context = NameSupply.NameSupply * Environment

  op emptyContext : () -> Context
  op fresh  : Context -> String -> String
  op lookup : Context -> String -> Option (String)
  op emptyEnvContext : Context -> Context
  op savingEnvContext : fa(a) Context -> (() -> a) -> a

  def emptyContext () =
    (NameSupply.empty (), emptyEnv ())
    
  def fresh (ns, env) old =
    let new = NameSupply.fresh ns old in
    (insertEnv env (old, new);
     new)

  def lookup (_, env) id =
    lookupEnv env id

  def emptyEnvContext (ns, _) =
    (ns, emptyEnv ())

  def savingEnvContext (_, env) f =
    savingEnv env f

  %% Renaming
  op renameInSpec   : Spec -> Spec
  op renameOp       : Context -> OpInfo -> OpInfo
  op renameFormula  : Context -> Property -> Property

  op renameTerm     : Context -> Term -> Term
  op renamePattern  : Context -> Pattern -> Pattern

  op renameTerms    : Context -> Terms -> Terms
  op renamePatterns : Context -> Patterns -> Patterns

  sort Terms    = List Term
  sort Patterns = List Pattern

  def renameTerms c terms =
    List.map (renameTerm c) terms

  def renamePatterns c pats =
    List.map (renamePattern c) pats

  def renameInSpec s =
    let c = emptyContext () in
    let {importInfo, sorts, ops, properties} = s in
    let ops      = mapAQualifierMap (renameOp c) ops in
    let properties   = map (renameFormula c) properties in
    {importInfo = importInfo,
     sorts    = sorts,
     ops      = ops,
     properties = properties}

  def renameFormula c (pt,name, tyvars, term) =
    (pt,name, tyvars, renameTerm c term)

  def renameOp c (op_names, fixity, sortScheme, termSchemes) =
    (op_names, 
     fixity,
     sortScheme,
     map (fn (tvs,term) -> (tvs,renameTerm c term)) termSchemes)

  def renameClosedTerm c term =
    savingEnvContext c (fn () ->
      renameTerm (emptyEnvContext c) term)

  def renameTerm c term =
    case term

      of Apply (t1, t2, a) ->
         Apply (renameTerm c t1, renameTerm c t2, a)

       | Record (fields,a) ->
         Record (List.map (fn (id, t) -> (id, renameTerm c t)) fields, a)

       | Bind (b, idSrts, term, a) ->
         savingEnvContext c (fn () ->
         let (ids, srts) = ListPair.unzip idSrts in
         let ids = List.map (fresh c) ids in
         let idSrts = ListPair.zip (ids, srts) in
         let term = renameTerm c term in
         Bind (b, idSrts, term, a))

       | Let (decls, term, a) ->
         savingEnvContext c (fn () ->
         let (pats, terms) = ListPair.unzip decls in
         let terms = renameTerms c terms in
         let pats = renamePatterns c pats in
         let decls = ListPair.zip (pats, terms) in
         let term = renameTerm c term in
         Let (decls, term, a))

       | LetRec (decls, term, a) ->
         savingEnvContext c (fn () ->
         let (idSrts, terms) = ListPair.unzip decls in
         let (ids, srts) = ListPair.unzip idSrts in
         let ids = List.map (fresh c) ids in
         let terms = renameTerms c terms in
         let idSrts = ListPair.zip (ids, srts) in
         let decls = ListPair.zip (idSrts, terms) in
         let term = renameTerm c term in
         LetRec (decls, term, a))

       | Var((id, srt), a) ->
         (case lookup c id
            of Some id -> Var((id, srt), a)
             | None    -> System.fail ("renameTerm: Found free variable " ^ id))

       | Fun (f, srt,_) -> term

       | Lambda (pcts, a) ->
         Lambda
         (List.map
          (fn (pat, cond, term) ->
           savingEnvContext c (fn () ->
           let pat  = renamePattern c pat in
           let cond = renameTerm c cond in
           let term = renameTerm c term in
           (pat, cond, term)))
          pcts, a)

       | IfThenElse (t1, t2, t3, a) ->
         IfThenElse (renameTerm c t1, renameTerm c t2, renameTerm c t3, a)

       | Seq (terms, a) ->
         Seq (renameTerms c terms, a)

  def renamePattern c p =
    case p

      of AliasPat (p1, p2, a) ->
         AliasPat (renamePattern c p1, renamePattern c p2, a)

       | VarPat((id, srt), a) ->
         VarPat((fresh c id, srt), a)

       | EmbedPat (id, Some p, srt, a) ->
         EmbedPat (id, Some (renamePattern c p), srt, a)

       | EmbedPat (id, None, srt, a) -> p

       | RecordPat (idPats, a) ->
	 let (ids, pats) = ListPair.unzip idPats in
	 let pats = renamePatterns c pats in
	 let idPats = ListPair.zip (ids, pats) in
	 RecordPat (idPats, a)

       | RelaxPat (p,t, a) ->
	 RelaxPat (renamePattern c p, renameClosedTerm c t, a)

       | QuotientPat (p, t, a) ->
	 QuotientPat (renamePattern c p, renameClosedTerm c t, a)

       | _ -> p

endspec

