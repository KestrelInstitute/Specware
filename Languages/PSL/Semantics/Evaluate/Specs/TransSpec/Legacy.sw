\section{Implementation of transition specs}

\begin{spec}
TransSpec qualifying spec
  import ../TransSpec
  import ../Op/Legacy
  import ../Subst/AsOpInfo
  import ../ModeSpec/AsRecord

  % sort TransSpec.TransSpec = SpecMorph.Morphism * ModeSpec.ModeSpec * SpecMorph.Morphism

  % op forwMorph : TransSpec -> SpecMorph.Morphism
  % op backMorph : TransSpec -> SpecMorph.Morphism
  % op modeSpec : TransSpec -> ModeSpec.ModeSpec

  def TransSpec.modeSpec (forwMorph,modeSpec,backMorph) = modeSpec
  def TransSpec.backMorph (forwMorph,modeSpec,backMorph) = backMorph
  def TransSpec.forwMorph (forwMorph,modeSpec,backMorph) = forwMorph

  % op make : ModeSpec -> OpRefSet.Set -> TranSpec
  def TransSpec.make modeSpec changedVars = ({changedVars=empty},modeSpec,{changedVars=changedVars})

  op withModeSpec infixl 17 : TransSpec * ModeSpec -> TransSpec
  def withModeSpec ((forwMorph,oldModeSpec,backMorph), newModeSpec) = (forwMorph,newModeSpec,backMorph)

  % op applySubst : TransSpec * Subst -> Env TransSpec
  def TransSpec.applySubst (transSpec,subst) = {
        modeSpec <- foldM (fn modeSpec -> fn opInfo -> {
          ms <- ModeSpec.addOp modeSpec opInfo noPos; 
          let Qualified (qual,id) = idOf opInfo in
          let newRules = defRule (context modeSpec,qual,id,opInfo) in
          let newRules = addUnconditionalRules(newRules,rewriteRules modeSpec) in
          return (ms withRewriteRules newRules)
      }) (modeSpec transSpec) subst;
      return (transSpec withModeSpec modeSpec)
    }
    
  (* We normalize because simplifying against the rules for procedures may introduce conjuncts *)
  % op simplifyVariants : ModeSpec -> TransSpec -> Env TransSpec
  def TransSpec.simplifyVariants ms transSpec = {
      modeSpc <- simplifyInvariants ms (modeSpec transSpec);
      normalize (transSpec withModeSpec modeSpc)
    }

  % op TransSpec.elaborate : TransSpec -> Env TranSpec
  def TransSpec.elaborate transSpec = {
      % print "trans spec elaborate";
      elabSpec <- Spec.elaborate (specOf (modeSpec transSpec));
      % elabSpec <- catch (Spec.elaborate (specOf modeSpec))
      %      (fn except -> {
      %          print (printException except);
      %          print (show modeSpec);
      %          raise (SpecError (noPos, ""))
      %       });
      % newModeSpec <- return (setElaborated (modeSpec withSpec elabSpec));
      % norm <- normalize newModeSpec;
      % ctxt <- return (makeContext (specOf newModeSpec));
      % rules <- return (demodRules (specRules ctxt (specOf newModeSpec)));
      ms <- return {
        spc = {
            importInfo = {
              imports = elabSpec.importInfo.imports,
              importedSpec = elabSpec.importInfo.importedSpec,
              localOps = [],
              localSorts = []
            },
            sorts = elabSpec.sorts,
            ops = elabSpec.ops,
            properties = elabSpec.properties
          },
        variables = variables (modeSpec transSpec),
        hidden = hidden (modeSpec transSpec),
        invariants = invariants (modeSpec transSpec),
        context = context (modeSpec transSpec),
        rewriteRules = rewriteRules (modeSpec transSpec),
        localSorts = empty,
        localOps = empty,
        localClaims = empty
      };
      newTransSpec <- return (transSpec withModeSpec ms);
      normalize newTransSpec
    }

  % op TransSpec.addVariable : TransSpec -> Op.OpInfo -> Position -> Env TransSpec
  def TransSpec.addVariable transSpec varInfo position = {
      newModeSpec <- addVariable (modeSpec transSpec) varInfo position;
      return (transSpec withModeSpec newModeSpec)
    }

  % This is completely out to lunch if a ref is anything other than an id.
  % op projectPostSubst : TransSpec -> Env Subst
  def TransSpec.projectPostSubst transSpec =
    let def projectVar ops opInfo =
%%       opInfo <-
%%         if member? (changedVars (backMorph transSpec),idOf opInfo) then
%%            findTheVariable (modeSpec transSpec) (makePrimedId (idOf opInfo))
%%         else
%%            findTheVariable (modeSpec transSpec) (idOf opInfo);
      case term opInfo of
        | Some trm ->
           if ~(isPrimedName? (Op.idOf opInfo)) & member? (changedVars (backMorph transSpec),idOf opInfo) then
             return ops
           else
             if groundTerm? trm then
               % print ("projectPostSubst: is ground: " ++ (show trm) ++ "\n");
               return (cons (opInfo withId (removePrime (Op.idOf opInfo)), ops))
             else
               % print ("projectPostSubst: not ground: " ++ (show trm) ++ "\n");
               return ops
        | None -> return ops
    in {
      preSub <- foldVariables projectVar [] (modeSpec transSpec);
      return (order preSub)
    }

  (*
   This is odd. After rewriting, it should be sufficient just to check for non-op Fun
   constructs. Not true. May have constructors and residual applications.
   *)
  op groundTerm? : MSlang.Term -> Boolean
  def groundTerm? term =
    case term of
      | Apply (t1,t2,_) -> (groundTerm? t1) & (groundTerm? t2)
      | ApplyN (terms,_) -> all groundTerm? terms
      | Record (pairs,_) -> all (fn (id,trm) -> groundTerm? trm) pairs
      | Bind (binder,vars,term,_) -> groundTerm? term % this is probably wrong
      | Let (decls,term,_) ->
          (all (fn(pat,term) -> groundTerm? term) decls) & (groundTerm? term)
      | LetRec (decls,term,_) ->
          (all (fn(var,term) -> groundTerm? term) decls) & (groundTerm? term)
      | Var _ -> false
      | Fun (Op (name,fxty), srt,_) -> false
      | Fun (_,srt,_) -> true
      | Lambda (match,_) -> all (fn (pat,cond,term) -> groundTerm? term) match
      | IfThenElse (t1,t2,t3,_) ->
         (groundTerm? t1) & (groundTerm? t2) & (groundTerm? t3)
      | Seq (terms,_) -> all groundTerm? terms
      | SortedTerm (term,_,_) -> groundTerm? term

  def TransSpec.makePrimedId (Qualified (qual,id)) = Qualified (qual,id ^ "'")

  def TransSpec.removePrime (qualId as (Qualified (qual,id))) =
    let chars = rev (explode id) in
    case chars of
      | #'::rest -> Qualified (qual, implode (rev rest))
      | _ -> qualId

  % op hideVariables : TransSpec -> Subst -> Subst -> Env TransSpec
  def TransSpec.hideVariables transSpec preSubst postSubst = {
      newModeSpec <- hideVariables (modeSpec transSpec) preSubst;
      primedPostSubst <-
        return (map
          (fn varInfo ->
             if member? (changedVars (backMorph transSpec),refOf varInfo) then
               (varInfo withId (makePrimedId (idOf varInfo)))
             else
               varInfo) postSubst);
      newModeSpec <- hideVariables newModeSpec primedPostSubst;
      newChangedVars <-
         foldM (fn vars -> fn varInfo ->
            return (delete (vars, refOf varInfo))) (changedVars (backMorph transSpec)) postSubst;
      return (make newModeSpec newChangedVars)
    }

 def TransSpec.withClaim (transSpec,newClaim) =
   let ms = modeSpec transSpec in
   let {importInfo,sorts,ops,properties} = specOf ms in
   let newSpec = {importInfo=importInfo,sorts=sorts,ops=ops,properties=[newClaim]} in
     transSpec withModeSpec (ms withSpec newSpec)
\end{spec}

This detects if a spec is false. This is, of course, only approximate
since, in general, it is undecidable. This is naive. We assume that
rewriting has been applied and we are left with one or more trivial
axioms that are either true or false. If we find a false one then
the spec is false. 

### The next is wrong. We really want to just check the invariants.
Now we do that .. but now the test on the non-invariants doesn't make
sense.

It is unfortunate that this depends on the representation of
the collection of properties as a list. There should be a
more abstract way of doing this. The dependency comes
because we want a lazy version of exists and this is available
for lists.

\begin{spec}
  def TransSpec.provablyInconsistent? transSpec =
    let def falseProp? prop =
      case prop of
        | (Axiom,name,tyVars, Fun (Bool false,_,_)) ->
             if member? (invariants (modeSpec transSpec), name) then
               true
             else
               false  % does this make sense?
        | _ -> false in
    exists falseProp? (specOf (modeSpec transSpec)).properties


  (* Normalizing a transition spec does two things to its claims. First,
  it performs trivial boolean reduction (true & x = x etc).  More
  important however, is that it descends conjuncts and terms equations
  of the form x' = t into a definition for x', It is from definitions
  that later we extract the post condition of the transition. *)

  op normalize : TransSpec -> Env TransSpec
  def normalize transSpec =
    let
      def normalizeClaims modeSpec claims invars =
        case claims of
          | [] -> return (modeSpec,claims,invars)
          | claim::claims -> {
              (newModeSpec,newClaims,newInvars) <- normalizeClaims modeSpec claims invars;
              ref <- refOf claim;
              if member? (invariants modeSpec, ref) then
                case claimType claim of
                  | Conjecture -> return (newModeSpec,Cons(claim,newClaims), insert(newInvars,ref))
                  | _ -> {
                       % print ("normalize: claim = " ^ (show (term claim)) ^ "\n");
                       (newModeSpec,newFormula) <- visitConjunct newModeSpec (term claim);
                       % print ("normalize: after = " ^ (show newFormula) ^ "\n");
                       case newFormula of
                         | Fun (Bool b,_,_) ->
                            if b then
                              return (newModeSpec,newClaims,newInvars)
                            else
                              return (newModeSpec, Cons (claim withTerm newFormula,newClaims),insert(newInvars,ref))
                         | _ -> return (newModeSpec, Cons (claim withTerm newFormula,newClaims),insert(newInvars,ref))
                     }
              else
                return (newModeSpec, Cons (claim,newClaims),newInvars)
            }
      def visitConjunct modeSpec formula =
        (case formula of
          | Apply (Fun (Op (Qualified ("Boolean","&"),fxty),srt,funPos),
                   Record([(M_fld,M),(N_fld,N)], recPos),applPos) -> {
                     % print ("normalize: conjunction = " ^ (show formula) ^ "\n"); % " (" ^ (anyToString formula) ^ ")\n");
                     (newModeSpec,newM) <- visitConjunct modeSpec M;
                     (newModeSpec,newN) <- visitConjunct newModeSpec N;
                     newTerm <-
                       return (case (newM,newN) of
                         | (Fun (Bool b1,srt,pos), Fun (Bool b2,_,_)) -> Fun (Bool (b1 & b2),srt,pos)
                         | (Fun (Bool b,_,_), _) -> if b then newN else newM
                         | (_, Fun (Bool b,_,_)) -> if b then newM else newN
                         | _ ->
                             Apply (Fun (Op (Qualified("Boolean","&"),fxty),srt,funPos),
                                    Record([(M_fld,newM),(M_fld,newN)],
                                    recPos),applPos));
                     return (newModeSpec,newTerm)
                   }
          | Apply (Fun (Equals,_,_), Record ([(_,M),(_,N)], _),pos) ->
              (case M of
                | (Fun (Op(qid,fxty),_,_)) ->
                      if isPrimedName? qid then {
                        varInfo <- findTheVariable modeSpec qid;
                        newModeSpec <- addVariable modeSpec (varInfo withTerm N) pos;
                        return (newModeSpec, Fun (Bool true,boolSort,pos))
                      } else
                        return (modeSpec,formula)
                % | Apply (Fun (Op(qid,fxty),_,_), arg,pos) -> {
                %       varInfo <- findTheVariable modeSpec qid;
                %       newTuple <- return (mkTuple [mkOp (makeId "update))
                %       newTerm <- return mkApply;
                %       newModeSpec <- addVariable modeSpec (varInfo withTerm N) pos;
                %       return (newModeSpec, Fun (Bool true,boolSort,pos))
                %    }
                | _ -> return (modeSpec,formula))
          | _ -> return (modeSpec,formula))
    in {
      (newModeSpec,newClaims,newInvars) <-
         normalizeClaims (modeSpec transSpec) (specOf (modeSpec transSpec)).properties ClaimRefSet.empty;
      let newSpec:Spec.Spec = {
          sorts = (specOf newModeSpec).sorts,
          ops = (specOf newModeSpec).ops,
          properties = newClaims,
          importInfo = (specOf newModeSpec).importInfo
        }
      in
        return (transSpec withModeSpec ((((newModeSpec : ModeSpec)
                          withSpec newSpec)
                          withInvariants newInvars)))
    }

  op isPrimedName? : QualifiedId -> Boolean
  def isPrimedName? (qualId as (Qualified (qual,id))) = hd (rev (explode id)) = #'
endspec
\end{spec}

So we want to fold a boolean operation over a collection of axioms. So the binding operation
should be lazy.

Need two such functions analogous to the exists and all functions on lists.
But think about lazyness .. more generally.
for example is the size of some collection more than 10. Don't need to visit
everything in the collection.

But there should be no difference in the specification. Only in the refinement.
One is strict whereas the short cut version of all or exists may not be. So there
is a refinement, only when all functions have a finite normal form.
