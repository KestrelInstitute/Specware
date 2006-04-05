\section{Evalution of a term in the Spec Calculus}

\begin{spec}
SpecCalc qualifying spec {
  import ../../AbstractSyntax/Types
  import ../Environment

  %% Generic mechanism:

  op evaluateTerm             : SCTerm                                                           -> SpecCalc.Env Value
  op evaluateLet              : List (Decl Position) -> SCTerm                                   -> SpecCalc.Env ValueInfo

  %% Specific kinds of terms:

  op evaluateReturnUID        : Position -> RelativeUID                                          -> SpecCalc.Env (ValueInfo * UnitId)
  op evaluateUID              : Position -> RelativeUID                                          -> SpecCalc.Env ValueInfo
  op evaluateSpec             : List (SpecElem Position)                             -> Position -> SpecCalc.Env ValueInfo
  op evaluateSpecMorph        : SCTerm * SCTerm * (List (SpecMorphRule Position))                -> SpecCalc.Env ValueInfo
  op evaluateSpecPrism        : SCTerm * List SCTerm * PrismModeTerm Position        -> Position -> SpecCalc.Env ValueInfo  % tentative
  op evaluateSpecInterp       : SCTerm * SCTerm * (SpecInterpRules Position)         -> Position -> SpecCalc.Env ValueInfo  % tentative
  op evaluateExtendMorph      : SCTerm                                                           -> SpecCalc.Env ValueInfo
  op evaluateLispCompile      : ValueInfo * SCTerm * Option String                               -> SpecCalc.Env ValueInfo
  op evaluateLispCompileLocal : ValueInfo * SCTerm * Option String                               -> SpecCalc.Env ValueInfo
  op evaluateJavaGen          : ValueInfo * (SpecCalc.Term Position) * Option String             -> SpecCalc.Env ValueInfo
  op evaluateDiag             : List (DiagElem Position)                                         -> SpecCalc.Env ValueInfo
  op evaluateDiagMorph        : SCTerm * SCTerm * (List (DiagMorphRule Position))                -> SpecCalc.Env ValueInfo
  op evaluateColimit          : SCTerm                                                           -> SpecCalc.Env ValueInfo
  op evaluateTermInfo         : SCTerm                                                           -> SpecCalc.Env ValueInfo
  op evaluatePrint            : SCTerm                                                           -> SpecCalc.Env ValueInfo
  op evaluateQualify          : SCTerm -> Qualifier                                              -> SpecCalc.Env ValueInfo
  op evaluateTranslate        : SCTerm -> Renaming                                   -> Position -> SpecCalc.Env ValueInfo
  op evaluateSubstitute       : SCTerm * SCTerm                                      -> Position -> SpecCalc.Env ValueInfo
  op evaluateOpRefine         : SCTerm * (List (SpecElem Position))                  -> Position -> SpecCalc.Env ValueInfo
  op evaluateObligations      : SCTerm                                                           -> SpecCalc.Env ValueInfo
  op evaluateExpand           : SCTerm                                               -> Position -> SpecCalc.Env ValueInfo
  op evaluateGenerate         : String * SCTerm * Option String                      -> Position -> SpecCalc.Env ValueInfo
  op evaluateProve            : ClaimName * SCTerm * ProverName * Assertions * ProverOptions * ProverBaseOptions * AnswerVar ->
                                                                                        Position -> SpecCalc.Env ValueInfo
  %% Hooks for extensions to specware:

  op evaluateOther              : OtherTerm Position                                 -> Position -> SpecCalc.Env ValueInfo
  op evaluateOtherQualify       : SCTerm -> ValueInfo -> Qualifier                   -> Position -> SpecCalc.Env ValueInfo
  op evaluateOtherTranslate     : SCTerm -> ValueInfo -> Renaming                    -> Position -> SpecCalc.Env ValueInfo
  op evaluateOtherObligations   : OtherValue                                         -> Position -> SpecCalc.Env ValueInfo
  op evaluateOtherPrint         : OtherValue                                         -> Position -> SpecCalc.Env ()
  op evaluateOtherProofGen      : OtherValue * SCTerm * Option String * Boolean      -> Position -> SpecCalc.Env ()
  op evaluateOtherProofGenLocal : OtherValue * SCTerm * Option String * Boolean      -> Position -> SpecCalc.Env ()

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


  op evaluateOtherGenerate :
       String * SCTerm * Option String
    -> OtherValue * TimeStamp * UnitId_Dependency
    -> Position
    -> SpecCalc.Env ValueInfo

  op evaluateOtherProve :
       ClaimName * OtherValue * Option String * ProverName * Assertions * ProverOptions * ProverBaseOptions * AnswerVar 
    -> Position 
    -> SpecCalc.Env Value

  op evaluateOtherProofCheck :
       PCClaimName * OtherValue * Option String * ProverName * Assertions * ProverOptions * ProverBaseOptions 
    -> Position 
    -> SpecCalc.Env Value

  %% Lower-level support routines:

  op setBaseToPath : String -> Env ()
  op reloadBase    : Env ()

  op getUnitId    : SCTerm -> SpecCalc.Env UnitId
  op coerceToSpec : Value -> Value

  op Specware.toplevelHandler       : Exception -> SpecCalc.Env Boolean
  op Specware.toplevelHandlerOption : [a] Exception -> SpecCalc.Env (Option a)

  op Specware.getOptSpec      : Option String -> Option Spec

  op SpecCalc.otherSameSCTerm? : [a] SpecCalc.Term a * SpecCalc.Term a -> Boolean

}

\end{spec}

%%
%% $Id$
%%
%% $Log$
%% Revision 1.48  2005/09/13 22:31:25  cyrluk
%% Changes to add a ProofCheck SpecCalc unit, some changes to the proof
%% generator, and added reporting of Snark timing.
%%
%% Revision 1.47  2005/08/18 13:32:51  mcdonald
%% prep for improved test comparing scterms
%%
%% Revision 1.46  2005/06/19 05:50:06  mcdonald
%% move op for toplevelHandlerOption from Specware.sw to Signature.sw
%%
%% Revision 1.45  2005/06/16 01:45:07  mcdonald
%% deprecated RelativeUnitId replaced by RelativeUID
%%
%% Revision 1.44  2005/06/11 00:05:36  mcdonald
%% added evaluateOtherTranslate
%%
%% Revision 1.43  2005/06/10 20:51:45  mcdonald
%% revised renaming/translate stuff yet again
%% Renaming     => Translators (and localized to Translator.sw)
%% RenamingExpr => Renaming
%%
%% moved things among Types.sw, Printer.sw, Value.sw to fix
%% a perennial headache with things being badly placed
%%
%% Revision 1.42  2005/06/08 04:18:01  mcdonald
%% TranslationMaps  => Renamings
%% TranslationMap   => Renamings
%% translation_maps => renamings
%% translation_map  => renaming
%% op_id_map        => op_renaming
%% sort_id_map      => sort_renaming
%% etc.
%%
%% Revision 1.41  2005/06/07 06:34:12  mcdonald
%% cosmetic spacing (prep for things to come)
%%
%% Revision 1.40  2005/04/01 21:43:24  gilham
%% Changed evaluateProve to support OtherValues in addition to Specs.
%% Fixed a problem with invalid file names for proof files.
%% Fixed some bugs in the definition of unionProofDecls
%%
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
