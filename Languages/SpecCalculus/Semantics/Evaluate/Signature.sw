\section{Evalution of a term in the Spec Calculus}

\begin{spec}
SpecCalc qualifying spec {
  import ../../AbstractSyntax/Types
  import ../Environment

  %% Generic mechanism:

  op evaluateTerm        : SCTerm                                                                   -> SpecCalc.Env Value
  op evaluateLet         : List (Decl Position) -> SCTerm                                           -> SpecCalc.Env ValueInfo

  %% Specific kinds of terms:

  op evaluateReturnUID   : Position -> RelativeUnitId -> Env (ValueInfo * UnitId)
  op evaluateUID         : Position -> RelativeUnitId                                               -> SpecCalc.Env ValueInfo
  op evaluateSpec        : List (SpecElem Position)                                     -> Position -> SpecCalc.Env ValueInfo
  op evaluateSpecMorph   : SCTerm * SCTerm * (List (SpecMorphRule Position))                        -> SpecCalc.Env ValueInfo
  op evaluateSpecPrism   : SCTerm * List SCTerm * PrismModeTerm Position                -> Position -> SpecCalc.Env ValueInfo  % tentative
  op evaluateSpecInterp  : SCTerm * SCTerm * (SpecInterpRules Position)                 -> Position -> SpecCalc.Env ValueInfo  % tentative
  op evaluateExtendMorph : SCTerm                                                                   -> SpecCalc.Env ValueInfo
  op evaluateLispCompile : ValueInfo * SCTerm * Option String                                       -> SpecCalc.Env ValueInfo
  op evaluateLispCompileLocal: ValueInfo * SCTerm * Option String                                   -> SpecCalc.Env ValueInfo
  op evaluateJavaGen     : ValueInfo * (SpecCalc.Term Position) * Option String                     -> SpecCalc.Env ValueInfo
  op evaluateDiag        : List (DiagElem Position)                                                 -> SpecCalc.Env ValueInfo
  op evaluateDiagMorph   : SCTerm * SCTerm * (List (DiagMorphRule Position))                        -> SpecCalc.Env ValueInfo
  op evaluateColimit     : SCTerm                                                                   -> SpecCalc.Env ValueInfo
  op evaluateTermInfo    : SCTerm                                                                   -> SpecCalc.Env ValueInfo
  op evaluatePrint       : SCTerm                                                                   -> SpecCalc.Env ValueInfo
  op evaluateQualify     : SCTerm -> Qualifier                                                      -> SpecCalc.Env ValueInfo
  op evaluateTranslate   : SCTerm -> TranslateExpr Position                                         -> SpecCalc.Env ValueInfo
  op evaluateSubstitute  : SCTerm * SCTerm                                              -> Position -> SpecCalc.Env ValueInfo
  op evaluateProve       : ClaimName * SCTerm * ProverName * Assertions * ProverOptions * ProverBaseOptions * AnswerVar -> Position -> SpecCalc.Env ValueInfo
  op evaluateObligations : SCTerm                                                                   -> SpecCalc.Env ValueInfo
  op evaluateExpand      : SCTerm                                                       -> Position -> SpecCalc.Env ValueInfo
  op evaluateGenerate    : String * SCTerm * Option String                              -> Position -> SpecCalc.Env ValueInfo

  op setBaseToPath : String -> Env ()
  op reloadBase : Env ()

  %% Hook for extensions to specware
  op evaluateOther       : OtherTerm Position -> Position -> SpecCalc.Env ValueInfo
  op evaluateOtherSpecMorph :
       ValueInfo
    -> ValueInfo
    -> List (SpecMorphRule Position)
    -> Position
    -> SpecCalc.Env ValueInfo

  op SpecCalc.evaluateOtherSubstitute :
       SCTerm -> ValueInfo
    -> SCTerm -> ValueInfo
    -> Position
    -> SpecCalc.Env ValueInfo

  op evaluateOtherPrint : OtherValue -> Position -> SpecCalc.Env ()

  op evaluateOtherGenerate :
       String * SCTerm * Option String
    -> OtherValue * TimeStamp * UnitId_Dependency
    -> Position
    -> SpecCalc.Env ValueInfo

  op evaluateOtherQualify : SCTerm -> ValueInfo -> Qualifier -> Position -> SpecCalc.Env ValueInfo

  op evaluateOtherProofGen      : OtherValue * SCTerm * Option String * Boolean -> Position -> SpecCalc.Env ()
  op evaluateOtherProofGenLocal : OtherValue * SCTerm * Option String * Boolean -> Position -> SpecCalc.Env ()
  op evaluateOtherObligations   : OtherValue                                    -> Position -> SpecCalc.Env ValueInfo
  op evaluateOtherProve         : ClaimName * OtherValue * Option String * ProverName * Assertions * ProverOptions * ProverBaseOptions * AnswerVar -> Position -> SpecCalc.Env Value

  %% Lower-level support routines:

  op getUnitId : SCTerm -> SpecCalc.Env UnitId
  op coerceToSpec : Value -> Value

  op Specware.toplevelHandler : Exception -> SpecCalc.Env Boolean
  op Specware.getOptSpec: Option String -> Option Spec
}
\end{spec}



%%
%% $Id$
%%
%% $Log$
%% Revision 1.39  2005/02/10 09:53:05  mcdonald
%% added hook for other obligations
%%
%% still unclear what to do for obligations of complex things
%% that contain many specs, morphisms, etc. -- hard to make it
%% a single spec
%%
%% Revision 1.38  2004/12/21 13:38:47  mcdonald
%% misc tweaks for Prism
%%
%% Revision 1.37  2004/12/14 11:22:55  mcdonald
%% hooks for tentative new prism code -- should be transparent to others
%%
%% Revision 1.36  2004/11/12 23:02:25  cyrluk
%% Added other for ProofGen.
%%
%% Revision 1.35  2004/11/12 19:04:53  becker
%% Added the signature and default implementations to
%% evaluateProofGenOther  and evaluateProofGenLocalOther
%% to dispatch the generation of proof obligations to functions
%% outside Specware.
%%
%%
%%
