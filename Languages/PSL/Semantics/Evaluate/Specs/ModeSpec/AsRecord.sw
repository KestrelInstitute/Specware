\section{Spec of labelling the BSpec states (modes) and transitions.}

\begin{spec}
ModeSpec qualifying spec
  import ../ModeSpec
  import ../ClaimSets
  import ../Subst/AsOpInfo
  import ../Spec/Legacy
  import /Languages/MetaSlang/Transformations/Rewriter
  import /Languages/SpecCalculus/Semantics/Evaluate/Spec

  sort ModeSpec.ModeSpec = {
      spc : Spec.Spec,
      variables : OpRefSet.Set,
      hidden : OpRefSet.Set,
      invariants : ClaimRefSet.Set,
      context : HigherOrderMatching.Context,
      rewriteRules : DemodRewriteRules,
      localSorts : SortRefSet.Set,
      localOps : OpRefSet.Set,
      localClaims : ClaimRefSet.Set
    }

  % op specOf : ModeSpec -> Spec.Spec
  def ModeSpec.specOf modeSpec = modeSpec.spc

  % op variables : ModeSpec -> OpRefSet.Set
  def ModeSpec.variables modeSpec = modeSpec.variables

  % op hidden : ModeSpec -> OpRefSet.Set
  def ModeSpec.hidden modeSpec = modeSpec.hidden

  % op invariants : ModeSpec -> ClaimRefSet.Set
  def ModeSpec.invariants modeSpec = modeSpec.invariants

  % op empty : ModeSpec
  def ModeSpec.empty = make Spec.empty OpRefSet.empty ClaimRefSet.empty

  % The next three operators should be hidden
  op ModeSpec.context : ModeSpec -> HigherOrderMatching.Context
  def ModeSpec.context modeSpec = modeSpec.context

  op ModeSpec.rewriteRules : ModeSpec -> DemodRewriteRules
  def ModeSpec.rewriteRules modeSpec = modeSpec.rewriteRules

  op ModeSpec.localSorts : ModeSpec -> SortRefSet.Set
  def ModeSpec.localSorts modeSpec = modeSpec.localSorts

  op ModeSpec.localOps : ModeSpec -> OpRefSet.Set
  def ModeSpec.localOps modeSpec = modeSpec.localOps

  op ModeSpec.localClaims : ModeSpec -> ClaimRefSet.Set
  def ModeSpec.localClaims modeSpec = modeSpec.localClaims

  % op make : Spec.Spec -> OpRefSet.Set -> ClaimRefSet.Set -> ModeSpec
  def ModeSpec.make spc variables invariants = {
      spc = spc,
      variables = variables,
      hidden = empty,
      invariants = invariants,
      context = makeContext emptySpec,
      rewriteRules = {unconditional=empty,conditional=empty},
      localSorts = empty,
      localOps = empty,
      localClaims = empty
    }

  op ModeSpec.withVariables infixl 18 : ModeSpec * OpRefSet.Set -> ModeSpec
  def ModeSpec.withVariables (modeSpec,variables) = {
      spc = specOf modeSpec,
      variables = variables,
      hidden = hidden modeSpec,
      invariants = invariants modeSpec,
      context = context modeSpec,
      rewriteRules = rewriteRules modeSpec,
      localSorts = localSorts modeSpec,
      localOps = localOps modeSpec,
      localClaims = localClaims modeSpec
    }

  def ModeSpec.hideVariable modeSpec varRef =
    return {
      spc = specOf modeSpec,
      variables = variables modeSpec,
      hidden = insert (hidden modeSpec,varRef),
      invariants = invariants modeSpec,
      context = context modeSpec,
      rewriteRules = rewriteRules modeSpec,
      localSorts = localSorts modeSpec,
      localOps = localOps modeSpec,
      localClaims = localClaims modeSpec
    }

  def ModeSpec.hideVariables modeSpec subst =
      let def rem ops (Qualified (qual,id)) = removeAQualifierMap (ops, qual,id) in {
      (localOps,newVars) <- 
        foldM (fn (ops,vars) -> fn varInfo -> return (rem ops (Op.refOf varInfo), delete (vars, Op.refOf varInfo)))
             ((specOf modeSpec).ops, variables modeSpec) subst;
      let spc = specOf modeSpec in
      let newSpec:Spec.Spec = {
        sorts = spc.sorts,
        ops = localOps,
        properties = spc.properties,
        importInfo = spc.importInfo
      } in
        return ((modeSpec withSpec newSpec)
                          withVariables newVars)
    }

  % op ModeSpec.withSpec infixl 18 : ModeSpec.ModeSpec * Spec.Spec -> ModeSpec.ModeSpec
  def ModeSpec.withSpec (modeSpec,spc) = {
      spc = spc,
      variables = variables modeSpec,
      hidden = hidden modeSpec,
      invariants = invariants modeSpec,
      context = context modeSpec,
      rewriteRules = rewriteRules modeSpec,
      localSorts = localSorts modeSpec,
      localOps = localOps modeSpec,
      localClaims = localClaims modeSpec
    }

  op withContext infixl 18 : ModeSpec * HigherOrderMatching.Context -> ModeSpec
  def withContext (modeSpec,ctxt) = {
      spc = specOf modeSpec,
      variables = variables modeSpec,
      hidden = hidden modeSpec,
      invariants = invariants modeSpec,
      context = ctxt,
      rewriteRules = rewriteRules modeSpec,
      localSorts = localSorts modeSpec,
      localOps = localOps modeSpec,
      localClaims = localClaims modeSpec
    }

  op withRewriteRules infixl 18 : ModeSpec * DemodRewriteRules -> ModeSpec
  def withRewriteRules (modeSpec,rules) = {
      spc = specOf modeSpec,
      variables = variables modeSpec,
      hidden = hidden modeSpec,
      invariants = invariants modeSpec,
      context = context modeSpec,
      rewriteRules = rules,
      localSorts = localSorts modeSpec,
      localOps = localOps modeSpec,
      localClaims = localClaims modeSpec
    }

  % op withInvariants infixl 18 : ModeSpec * ClaimRefSet.Set -> ModeSpec
  def ModeSpec.withInvariants (modeSpec,invariants) = {
      spc = specOf modeSpec,
      variables = variables modeSpec,
      hidden = hidden modeSpec,
      invariants = invariants,
      context = context modeSpec,
      rewriteRules = rewriteRules modeSpec,
      localSorts = localSorts modeSpec,
      localOps = localOps modeSpec,
      localClaims = localClaims modeSpec
    }

  op ModeSpec.addLocalOp : ModeSpec -> Op.Ref -> ModeSpec
  def ModeSpec.addLocalOp modeSpec ref = {
      spc = specOf modeSpec,
      variables = variables modeSpec,
      hidden = hidden modeSpec,
      invariants = invariants modeSpec,
      context = context modeSpec,
      rewriteRules = rewriteRules modeSpec,
      localSorts = localSorts modeSpec,
      localOps = insert (localOps modeSpec, ref),
      localClaims = localClaims modeSpec
    }

  op ModeSpec.addLocalClaim : ModeSpec -> Claim.Ref -> ModeSpec
  def ModeSpec.addLocalClaim modeSpec ref = {
      spc = specOf modeSpec,
      variables = variables modeSpec,
      hidden = hidden modeSpec,
      invariants = invariants modeSpec,
      context = context modeSpec,
      rewriteRules = rewriteRules modeSpec,
      localSorts = localSorts modeSpec,
      localOps = localOps modeSpec,
      localClaims = insert (localClaims modeSpec, ref)
    }

  op ModeSpec.addLocalSort : ModeSpec -> Sort.Ref -> ModeSpec
  def ModeSpec.addLocalSort modeSpec ref = {
      spc = specOf modeSpec,
      variables = variables modeSpec,
      hidden = hidden modeSpec,
      invariants = invariants modeSpec,
      context = context modeSpec,
      rewriteRules = rewriteRules modeSpec,
      localSorts = insert (localSorts modeSpec, ref),
      localOps = localOps modeSpec,
      localClaims = localClaims modeSpec
    }

  % op addOp : ModeSpec -> Op.OpInfo -> Position -> Env ModeSpec
  def ModeSpec.addOp modeSpec opInfo position = {
      newSpec <- SpecEnv.addOp (specOf modeSpec) opInfo position;
      return (addLocalOp (modeSpec withSpec newSpec) (refOf opInfo))
    }

        % let Qualified (qual,id) = idOf opInfo in
        % let rules = defRule (context modeSpec,qual,id,opInfo) in
        % let rules = addUnconditionalRules(rules,rewriteRules modeSpec) in
        % return ((modeSpec withSpec newSpec)
                          % withRewriteRules rules)
      % else
        % return (modeSpec withSpec newSpec)

  % op addSort : ModeSpec -> Sort.SortInfo -> Position -> Env ModeSpec
  def ModeSpec.addSort modeSpec sortInfo position = {
      newSpec <- SpecEnv.addSort (specOf modeSpec) sortInfo position;
      return (addLocalSort (modeSpec withSpec newSpec) (refOf sortInfo))
    }

  % op addVariable : ModeSpec -> Op.OpInfo -> Position -> Env ModeSpec
  def ModeSpec.addVariable modeSpec opInfo position = {
      newSpec <- SpecEnv.addOp (specOf modeSpec) opInfo position;
      return ((addLocalOp (modeSpec withSpec newSpec) (refOf opInfo))
                         withVariables (insert (variables modeSpec, refOf opInfo)))
    }
%       ref <- refOf opInfo;
%       if elaborated? modeSpec then
%         let Qualified (qual,id) = idOf opInfo in
%         let rules = defRule (context modeSpec,qual,id,opInfo) in
%         let rules = addUnconditionalRules(rules,rewriteRules modeSpec) in
%         return (((modeSpec withSpec newSpec)
%                          withRewriteRules rules)
%                          withVariables (insert (variables modeSpec, ref)))
%       else
%         return ((modeSpec withSpec newSpec)
%                          withVariables (insert (variables modeSpec, ref)))
%     }

  % op findTheOp : ModeSpec -> Id.Id -> Env Op.OpInfo
  def ModeSpec.findTheOp modeSpec id = findTheOp (specOf modeSpec) id

  % op findTheVariable : ModeSpec -> Id.Id -> Env Op.OpInfo
  def ModeSpec.findTheVariable modeSpec id = {
      opInfo <- findTheOp (specOf modeSpec) id;
      ref <- refOf opInfo;
      if member? (variables modeSpec, ref) then
        return opInfo
      else
        specError ("Id is an op but not a variable: " ^ (Id.show id))
    }

  % op ModeSpecEnv.foldOps : fa(a) (a -> Op.OpInfo -> Env a) -> a -> ModeSpec -> Env a
  def ModeSpecEnv.foldOps f unit modeSpec = SpecEnv.foldOps f unit (specOf modeSpec)

  % op ModeSpec.foldVariables : fa (a) (a -> Op.OpInfo -> a) -> a -> ModeSpec -> a
  def ModeSpec.foldVariables f unit modeSpec = Spec.foldOps
    (fn x -> fn opInfo ->
        if OpRefSet.member? (variables modeSpec, refOf  opInfo) then
          f x opInfo
        else
          x) unit (specOf modeSpec)
 
  % op ModeSpecEnv.foldVariables : fa (a) (a -> Op.OpInfo -> Env a) -> a -> ModeSpec -> Env a
  def ModeSpecEnv.foldVariables f unit modeSpec = SpecEnv.foldOps
    (fn x -> fn opInfo -> {
        ref <- refOf opInfo;
        if member? (variables modeSpec, ref) then
          f x opInfo
        else
          return x
      }) unit (specOf modeSpec)

  % op ModeSpecEnv.mapVariables : ModeSpec -> (Op.OpInfo -> Env Op.OpInfo) -> ModeSpec
  % op ModeSpecEnv.mapClaim : ModeSpec -> (Claim.Claim -> Env Claim.Claim) -> ModeSpec

  % op ModeSpecEnv.foldVariants : fa (a) (a -> Claim -> Env a) -> a -> ModeSpec -> Env a
  def ModeSpecEnv.foldVariants f unit modeSpec =
    foldM (fn x -> fn claim -> {
        ref <- refOf claim;
        if member? (invariants modeSpec, ref) then
          f x claim
        else
          return x
      }) unit (specOf modeSpec).properties

  % op ModeSpecEnv.printRules : ModeSpec -> Env ()
  def ModeSpecEnv.printRules modeSpec =
    let {unconditional,conditional} = rewriteRules modeSpec in
    let _ = map printRule (listRules unconditional) in
    let _ = map printRule (listRules conditional) in
    return ()

  % op addClaim : ModeSpec -> Claim.Claim -> Position -> Env ModeSpec
  def ModeSpec.addClaim modeSpec property position = {
      newSpec <- addClaim (specOf modeSpec) property position;
      return (addLocalClaim (modeSpec withSpec newSpec) (refOf property))
%       if elaborated? modeSpec then
%         let newRules = axiomRules (context modeSpec) property in
%         let rules = addUnconditionalRules(newRules,rewriteRules modeSpec) in
%         return ((modeSpec withSpec newSpec)
%                          withRewriteRules rules)
%       else
%         return (modeSpec withSpec newSpec)
    }

  % op addInvariant : ModeSpec -> Claim.Claim -> Position -> Env ModeSpec
  def ModeSpec.addInvariant modeSpec property position = {
      newSpec <- SpecEnv.addClaim (specOf modeSpec) property position;
      ref <- refOf property;
      return (addLocalClaim ((modeSpec withSpec newSpec)
                           withInvariants (insert (invariants modeSpec, ref))) ref)
    }

  % op elaborate : ModeSpec -> Env ModeSpec
  def ModeSpec.elaborate modeSpec = {
      % print "mode spec elaborate";
      elabSpec <- Spec.elaborate (specOf modeSpec);
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
      modeSpec <- foldM (fn modeSpec -> fn claim ->
        if member? (localClaims modeSpec, refOf claim) then 
          let newRules = axiomRules (context modeSpec) claim in
          let rules = addUnconditionalRules (newRules,rewriteRules modeSpec) in
            return (modeSpec withRewriteRules rules)
        else
          return modeSpec
        ) (modeSpec withSpec elabSpec) elabSpec.properties;
      modeSpec <- fold (fn modeSpec -> fn ref -> {
          opInfo <- findTheOp modeSpec ref;
          let Qualified (qual,id) = idOf opInfo in
          let rules = defRule (context modeSpec,qual,id,opInfo) in
          let rules = addUnconditionalRules (rules,rewriteRules modeSpec) in
          return (modeSpec withRewriteRules rules)
        }) modeSpec (localOps modeSpec);
      return {
        spc = {
            importInfo = {
              imports = modeSpec.spc.importInfo.imports,
              importedSpec = modeSpec.spc.importInfo.importedSpec,
              localOps = [],
              localSorts = []
            },
            sorts = modeSpec.spc.sorts,
            ops = modeSpec.spc.ops,
            properties = modeSpec.spc.properties
          },
        variables = variables modeSpec,
        hidden = hidden modeSpec,
        invariants = invariants modeSpec,
        context = context modeSpec,
        rewriteRules = rewriteRules modeSpec,
        localSorts = empty,
        localOps = empty,
        localClaims = empty
      }
    }

  % op subtract : ModeSpec -> ModeSpec -> ModeSpec
  def ModeSpec.subtract m1 m2 =
     make (subtract (specOf m1) (specOf m2))
          (difference (variables m1, variables m2))
          (difference (invariants m1, invariants m2))
    
  % op union : ModeSpec -> ModeSpec -> Env ModeSpec
  def ModeSpec.union ms1 ms2 = {
      spc <- union (specOf ms1) (specOf ms2);
      return ((ms1 withSpec spc)
                   withVariables (union (variables ms1, variables ms2)))
    }

  def ModeSpec.simplifyInvariants ruleModeSpec modeSpec =
    % let rules = mergeDemodRules [rewriteRules ruleModeSpec, rewriteRules modeSpec] in
    let rules = rewriteRules ruleModeSpec in
    let
      def doTerm count trm =
        let lazy = rewriteRecursivePre ((context ruleModeSpec) withSpec (specOf ruleModeSpec),[],rules,trm) in
        case lazy of
          | Nil -> trm
          | Cons([],tl) -> trm
          | Cons((rule,trm,subst)::_,tl) ->
              if (count > 0) then 
                doTerm (count - 1) trm
              else
                trm
 
      def doOp (opInfo as (names,fixity,sortSchemes,termSchemes)) =
        let ref = Op.refOf opInfo in
        if member? (variables modeSpec, ref) then
          case termSchemes of
            | [] -> opInfo    % fail "empty term schemes"
            | [(typeVars,term)] ->
               (names,fixity,sortSchemes,[(typeVars, doTerm 20 term)])
            | _ -> fail "multiple term schemes"
        else
          opInfo

      def doClaim claim =
        let ref = refOf claim in
        if member? (invariants modeSpec, ref) then
          case claim of
            | (Axiom,name,typeVars,term) -> (Axiom,name,typeVars,doTerm 20 term) 
            | claim -> claim
        else
          claim in
    let spc = specOf modeSpec in
    let newSpec:Spec.Spec = {
        sorts = spc.sorts,
        ops = mapAQualifierMap doOp spc.ops,
        properties = map doClaim spc.properties,
        importInfo = spc.importInfo
      } in
    return (modeSpec withSpec newSpec)

  % op simplifyVariable : ModeSpec * Op.Ref -> Env ModeSpec
  def ModeSpec.simplifyVariable (modeSpec,opRef) =
    if member? (variables modeSpec, opRef) then {
      spc <- simplifyOp (specOf modeSpec) opRef;
      return (modeSpec withSpec spc)
    } else
      specError ("simplifyVariable: id '" ^ (OpRef.show opRef) ^ "' is not a variable")

  % op simplifyInvariant : ModeSpec * Claim.Ref -> Env ModeSpec
  def ModeSpec.simplifyInvariant (modeSpec,claimRef) =
    let
      def doTerm count trm =
        let lazy = rewriteRecursivePre ((context modeSpec) withSpec (specOf modeSpec),[],rewriteRules modeSpec,trm) in
        case lazy of
          | Nil ->
              % let _ = writeLine "appToSpec: Nil no change" in
              trm
          | Cons([],tl) -> 
              % let _ = writeLine "appToSpec: Cons Nil no change" in
              trm
          | Cons((rule,trm,subst)::_,tl) ->
              if (count > 0) then 
                doTerm (count - 1) trm
              else
                trm
 
      def doClaim claim =
        let ref = refOf claim in
          if member? (invariants modeSpec, ref) then
            case claim of
              | (Axiom,name,typeVars,term) -> (Axiom,name,typeVars,doTerm 20 term) 
              | claim -> claim
          else
            claim in
    let spc = specOf modeSpec in
    let newSpec:Spec.Spec = {
        sorts = spc.sorts,
        ops = spc.ops,
        properties = map doClaim spc.properties,
        importInfo = spc.importInfo
      } in
      return (modeSpec withSpec newSpec)

  % op show : ModeSpec -> String
  def ModeSpec.show modeSpec = ppFormat (pp modeSpec)

  % op applySubst : ModeSpec * Subst -> Env ModeSpec
  def ModeSpec.applySubst (modeSpec,subst) =
    foldM (fn spc -> fn opInfo -> addOp spc opInfo noPos) modeSpec subst

  % op join : ModeSpec -> ModeSpec -> Env ModeSpec
  def ModeSpec.join term ms1 ms2 position = {
    newSpc <- mergeImport term (specOf ms1) (specOf ms2) position;
    return {
        spc = newSpc,
        variables = union (variables ms1, variables ms2),
        hidden = union (hidden ms1, hidden ms2),
        invariants = union (invariants ms1, invariants ms2),
        context = context ms1,
        rewriteRules = mergeDemodRules [rewriteRules ms1, rewriteRules ms2],
        localOps = union (localOps ms1,localOps ms2),
        localSorts = union (localSorts ms1,localSorts ms2),
        localClaims = union (localClaims ms1,localClaims ms2)
      }
  }

  % op pp : ModeSpec -> Doc
  def ModeSpec.pp modeSpec =
    ppIndent (ppConcat [
      String.pp "spec=",
      pp (specOf modeSpec),
      ppNewline,
      String.pp "variables=",
      pp (variables modeSpec),
      ppNewline,
      String.pp "invariants=",
      pp (invariants modeSpec),
      ppNewline,
      String.pp "hidden=",
      pp (hidden  modeSpec)
    ])
endspec
\end{spec}
