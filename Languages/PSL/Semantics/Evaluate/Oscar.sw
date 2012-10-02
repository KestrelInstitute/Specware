\subsection{Evalution of an Oscar Spec}

\begin{spec}
let S = spec
  import Specs/Compiler
  import Specs/Oscar
endspec in
SpecCalc qualifying spec {
  import translate S by {Monad._ +-> Env._}
  import translate Refinement by {Monad._ +-> Env._}
  import Specs/Spec/Legacy
  import /Languages/SpecCalculus/Semantics/Evaluate/Signature
  import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities
  import /Languages/SpecCalculus/Semantics/Evaluate/Spec
  import /Library/Legacy/DataStructures/ListUtilities
  import ../../AbstractSyntax/SimplePrinter
\end{spec}

\begin{spec}
  type SpecCalc.OtherValue = Oscar.Spec
\end{spec}

To evaluate a spec we deposit the declarations in a new spec
(evaluating any import terms along the way), elaborate the spec
and then qualify the resulting spec if the spec was given a name.

So we have a problem. This does not fit withing the paradigm
so far. Does the global context map names to things representing procedures,
or names to spec like things that include procedures. I think the latter.
They are procedures in context.

\begin{spec}
  op renameElems : List (OscarSpecElem Position) -> List (OscarSpecElem Position)

  op SpecCalc.evaluateOscar : List (OscarSpecElem Position) -> SpecCalc.Env ValueInfo
  def SpecCalc.evaluateOscar oscarSpecElems = {
     unitId <- getCurrentUID;
     print (";;; Processing oscar spec at " ^ (uidToString unitId) ^ "\n");
     base <- baseOscarSpec;
     (oscarSpec,timeStamp,depUnitIds) <- evaluateOscarSpecElems base (renameElems oscarSpecElems);
     newOscarSpec <- elaborate oscarSpec;
     return (Other newOscarSpec,timeStamp,depUnitIds)
   }
\end{spec}

\begin{spec}
  op evaluateOscarSpecElems :
           Oscar.Spec
        -> List (OscarSpecElem Position)
        -> SpecCalc.Env (Oscar.Spec * TimeStamp * UnitId_Dependency)

  def SpecCalc.evaluateOscarSpecElems initialOscarSpec oscarSpecElems = {
      (oscarSpecWithImports,timeStamp,depUnitIds)
          <- foldM evaluateOscarSpecImportElems (initialOscarSpec,0,[]) oscarSpecElems;
      oscarSpec <- evaluateOscarSpecContextElems oscarSpecWithImports oscarSpecElems;
      oscarSpec <- foldM evaluateProcElemPassOne oscarSpec oscarSpecElems;
      oscarSpec <- foldM evaluateProcElemPassTwo oscarSpec oscarSpecElems;
      oscarSpec <- foldM evaluateProcElemPassThree oscarSpec oscarSpecElems;
      return (oscarSpec,timeStamp,depUnitIds)
    }
  
  op evaluateOscarSpecContextElems : Oscar.Spec -> List (OscarSpecElem Position) -> SpecCalc.Env Oscar.Spec
  def evaluateOscarSpecContextElems oscarSpec oscarSpecElems = {
      oscarSpec <- foldM evaluateOscarSpecContextElem oscarSpec oscarSpecElems;
      elab <- elaborate oscarSpec;
      % print "before procedure elements\nRules = \n";
      % printRules (modeSpec elab);
      % print "ModeSpec";
      % print (ppFormat (ModeSpec.pp (modeSpec elab)));
      % print (ppFormat (ppLess elab (modeSpec elab)));
      % print "\n";
      return elab
   }

  op evaluateOscarSpecImportElems :
           (Oscar.Spec * TimeStamp * UnitId_Dependency)
        -> OscarSpecElem Position
        -> SpecCalc.Env (Oscar.Spec * TimeStamp * UnitId_Dependency)
  def evaluateOscarSpecImportElems info (elem,position) =
    case elem of
      | Import terms -> foldM evaluateOscarSpecImportElem info terms
      | _ -> return info

  op evaluateOscarSpecImportElem :
           (Oscar.Spec * TimeStamp * UnitId_Dependency)
        -> SpecCalc.Term Position
        -> SpecCalc.Env (Oscar.Spec * TimeStamp * UnitId_Dependency)
  def evaluateOscarSpecImportElem (val as (oscarSpec,currentTimeStamp,currentDeps)) term = {
     (value,importTimeStamp,depUnitIds) <- evaluateTermInfo term;
     newOscarSpec <-
       case value of
         | Other impOscarSpec -> join term oscarSpec impOscarSpec (positionOf term)
         | Spec impSpec -> {
               newSpec <- mergeImport term impSpec (specOf (modeSpec oscarSpec));
               let newRules = specRules (context (modeSpec oscarSpec)) newSpec in
               let allRules = mergeDemodRules [demodRules newRules, rewriteRules (modeSpec oscarSpec)] in
               return (oscarSpec withModeSpec (((modeSpec oscarSpec) withSpec newSpec) withRewriteRules allRules))
             }
         | _ -> raise (Fail ("Import not a spec"));
     return (newOscarSpec, max (currentTimeStamp,importTimeStamp), listUnion (currentDeps, depUnitIds))
    }

  op evaluateOscarSpecContextElem : Oscar.Spec -> OscarSpecElem Position -> SpecCalc.Env Oscar.Spec
  def evaluateOscarSpecContextElem oscarSpec (elem, position) =
    case elem of
      | Type ([id],(tyVars,[])) -> {
            typeInfo <- makeType id;
            addType oscarSpec typeInfo position
          }
      | Type ([id],(tyVars,[si_type])) -> {
            typeInfo <- makeType id si_type;
            addType oscarSpec typeInfo position
          }
      | Def ([id],(fxty,oi_type,[(_,term)])) -> {
            opInfo <- makeOp (id,fxty,term,oi_type);
            addOp oscarSpec opInfo position
          }
      | Var ([id],(fxty,oi_type,[])) -> {
            opInfo <- makeOp (id,fxty,oi_type);
            addVariable oscarSpec opInfo position
          }
      | Op ([id],(fxty,oi_type,[])) -> {
            opInfo <- makeOp (id,fxty,oi_type);
            addOp oscarSpec opInfo position
          }
      | Claim (Axiom, name, tyVars, term) -> {
            axm <- makeAxiom name tyVars term;
            % print ("adding axiom: " ^ name ^ "\n");
            addClaim oscarSpec axm position
          }
      | Claim (Invariant, name, tyVars, term) -> {
            axm <- makeAxiom name tyVars term;
            % print ("adding invariant: " ^ name ^ "\n");
            addInvariant oscarSpec axm position
          }
      | Claim (Theorem, name, tyVars, term) -> {
            thm <- makeTheorem name tyVars term;
            addClaim oscarSpec thm position
          }
      | Claim (Conjecture, name, tyVars, term) -> {
            conj <- makeConjecture name tyVars term;
            addClaim oscarSpec conj position
          }
      | Claim _ -> error "evaluateSpecElem: unsupported claim type"
      | _ -> return oscarSpec
\end{spec}

So how do we reconcile these things?  We construct a Spec with position,
and then we start construction the diagram for the body of some
procedure. Don't we want to elaborate as we go along?

begin{spec}
  op PosSpec.mkTyVar : String -> AType Position
  def PosSpec.mkTyVar name = TyVar (name, internalPosition)

  op staticBase : SpecCalc.Env Spec
  def staticBase = {
      baseURI <- pathToRelativeURI "/Library/PSL/Base";
      (Spec baseSpec,_,_) <- SpecCalc.evaluateURI (Internal "PSL base") baseURI;
      return baseSpec
    }

  op baseSpec : SpecCalc.Env Spec
  def baseSpec = {
      baseURI <- pathToRelativeURI "/Library/Base";
      (Spec baseSpec,_,_) <- SpecCalc.evaluateURI (Internal "Specware base") baseURI;
      return baseSpec
    }

  def baseOscarSpec = {
    base <- staticBase;
    uri <- pathToRelativeURI "/Library/PSL/Base";
    dynamicSpec <- mergeImport (URI uri,internalPosition) base emptySpec;
    % dynamicSpec <- return (setImportedSpec(dynamicSpec,base));
    return {
        staticSpec = base,
        dynamicSpec = dynamicSpec,
        procedures = PolyMap.emptyMap
      }
  }

\begin{spec}
  op baseOscarSpec : SpecCalc.Env Oscar.Spec
  def baseOscarSpec = {
      baseUnitId <- pathToRelativeUID "/Library/PSL/Base";
      (Spec baseSpec,_,_) <- SpecCalc.evaluateUID (Internal "PSL base") baseUnitId;
      return (Oscar.make (ModeSpec.make baseSpec OpRefSet.empty ClaimRefSet.empty) ProcMap.empty)
    }
}
\end{spec}

      op addConstantType : OscarSpec -> QualifiedId -> TyVars ATypeScheme Position -> Position -> SpecCalc.Env OscarSpec
      def addConstantType pSpec name tyVars optType)) position = {
            static <- staticSpec pSpec;
            static <- addType names tyVars [optType] static position;
            setStaticSpec pSpec static
          }
A constant must be added to both the static and dynamic spec. We do this
by adding it to the static spec and then copy the opInfo to the dynamic
spec. In the dynamic spec, the operators remain distinguishable from the
variables since the variables are considered "local" to the spec. This
mechanism is a design descision and perhaps a poor one. There should
be a more abstract way of doing this. For instance, to label each state
with both the static and dynamic specs. Needs thought.

      op addConstant : OscarSpec -> QualifiedId -> Fixity -> ATypeScheme Position -> Position -> SpecCalc.Env OscarSpec
      def addConstant pSpec qualId fxty srtScheme position = {
            static <- staticSpec pSpec;
            static <- addOp [qualId] fxty srtScheme [] static position;
            pSpec <- setStaticSpec pSpec static;
            case findAQualifierMap (static, qualId) of
              | None -> fail "addConstant: inserted op not found" 
              | Some info -> {
                    dynamic <- dynamicSpec pSpec;
                    dynamic <- addNonLocalOpInfo dynamic qualId info;
                    setDynamicSpec pSpec dynamic
                 }
          }

      op addVariable : OscarSpec -> QualifiedId -> Fixity -> ATypeScheme Position -> Position -> SpecCalc.Env OscarSpec
      def addVariable pSpec qualId fxty srtScheme optTerm = {
            dynamic <- dynamicSpec pSpec;
            dynamic <- addOp [qualId] fxty srtScheme [] dynamic position;
            setDynamicSpec pSpec dynamic
          }

