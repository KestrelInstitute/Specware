(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* Evalution of a term in the Spec Calculus *)

SpecCalc qualifying spec
  import /Languages/SpecCalculus/AbstractSyntax/Types  % including SCTerm
  import /Languages/SpecCalculus/Semantics/Environment
  import /Languages/SpecCalculus/AbstractSyntax/Printer % showValue, ppDecls, ppRenaming, etc.

  %% Generic mechanism:

  op evaluateTerm             : SCTerm                                                           -> SpecCalc.Env Value
  op evaluateLet              : SCDecls -> SCTerm                                                -> SpecCalc.Env ValueInfo

  %% Specific kinds of terms:

  op evaluateReturnUID        : Position -> RelativeUID -> Bool                                  -> SpecCalc.Env (ValueInfo * UnitId)
  op evaluateUID              : Position -> RelativeUID                                          -> SpecCalc.Env ValueInfo
  op evaluateSpec             : ExplicitSpecTerm -> Id                               -> Position -> SpecCalc.Env ValueInfo
  op evaluateSpecMorph        : SpecMorphismTerm                                     -> Position -> SpecCalc.Env ValueInfo
  op evaluateSpecPrism        : SpecPrismTerm                                        -> Position -> SpecCalc.Env ValueInfo  % tentative
  op evaluateSpecInterp       : SpecInterpTerm                                       -> Position -> SpecCalc.Env ValueInfo  % tentative
%%  op evaluateExtendMorph      : ExtendMorphismTerm                                               -> SpecCalc.Env ValueInfo
  op evaluateLispCompile      : ValueInfo * SCTerm * Option String * Bool                        -> SpecCalc.Env ValueInfo
  op evaluateLispCompileLocal : ValueInfo * SCTerm * Option String                               -> SpecCalc.Env ValueInfo
  op evaluateJavaGen          : ValueInfo * SCTerm * Option String                               -> SpecCalc.Env ValueInfo
  op evaluateDiag             : DiagramTerm                                          -> Position -> SpecCalc.Env ValueInfo
  op evaluateDiagMorph        : DiagramMorphismTerm                                              -> SpecCalc.Env ValueInfo
  op evaluateColimit          : ColimitTerm                                          -> Position -> SpecCalc.Env ValueInfo
  op evaluateTermInfo         : SCTerm                                                           -> SpecCalc.Env ValueInfo
  op evaluatePrint            : PrintTerm * Bool                                                 -> SpecCalc.Env ValueInfo
  op evaluateQualify          : SCTerm -> Qualifier                                              -> SpecCalc.Env ValueInfo
  op evaluateTranslate        : SCTerm -> Renaming                                   -> Position -> SpecCalc.Env ValueInfo
  op evaluateSubstitute       : SubstTerm                                            -> Position -> SpecCalc.Env ValueInfo
  op evaluateOpRefine         : OpRefineTerm                                         -> Position -> SpecCalc.Env ValueInfo
  op evaluateTransform        : TransformTerm                                        -> Position -> SpecCalc.Env ValueInfo
  op evaluateObligations      : ObligationsTerm                                                  -> SpecCalc.Env ValueInfo
  op evaluateExpand           : ExpandTerm                                           -> Position -> SpecCalc.Env ValueInfo
  op evaluateGenerate         : GenerateTerm                                         -> Position -> SpecCalc.Env ValueInfo
  op evaluateProve            : ProveTerm                                            -> Position -> SpecCalc.Env ValueInfo

  %% Hooks for extensions to specware:

  op evaluateOther              : OtherTerm Position                                 -> Position -> SpecCalc.Env ValueInfo
  op evaluateOtherQualify       : SCTerm -> ValueInfo -> Qualifier                   -> Position -> SpecCalc.Env ValueInfo
  op evaluateOtherTranslate     : SCTerm -> ValueInfo -> Renaming                    -> Position -> SpecCalc.Env ValueInfo
  op evaluateOtherObligations   : OtherValue                                         -> Position -> SpecCalc.Env ValueInfo
  op evaluateOtherPrint         : OtherValue                                         -> Position -> SpecCalc.Env ()
  op evaluateOtherProofGen      : OtherValue * SCTerm * Option String * Bool         -> Position -> SpecCalc.Env ()
  op evaluateOtherProofGenLocal : OtherValue * SCTerm * Option String * Bool         -> Position -> SpecCalc.Env ()
  op evaluateOtherSubstitute    : SCTerm -> ValueInfo -> SCTerm -> ValueInfo         -> Position -> SpecCalc.Env ValueInfo

  op evaluateOtherSpecMorph     : ValueInfo -> ValueInfo -> SpecMorphRules -> SM_Pragmas                        -> Position -> SpecCalc.Env ValueInfo
  op evaluateOtherGenerate      : String * SCTerm * Option String -> OtherValue * TimeStamp * UnitId_Dependency -> Position -> SpecCalc.Env ValueInfo

  op evaluateOtherProve         : ClaimName   * OtherValue * Option String * ProverName * Assertions * ProverOptions * ProverBaseOptions * AnswerVar -> Position -> SpecCalc.Env Value
  op evaluateOtherProofCheck    : PCClaimName * OtherValue * Option String * ProverName * Assertions * ProverOptions * ProverBaseOptions             -> Position  -> SpecCalc.Env Value

  %% Lower-level support routines:

  op setBaseToPath : String -> Env ()
  op reloadBase    : Env ()

  op getUnitId    : SCTerm -> SpecCalc.Env UnitId
  op coerceToSpec : Value -> Value

  op Specware.toplevelHandler       : Exception -> SpecCalc.Env Bool
  op Specware.toplevelHandlerOption : [a] Exception -> SpecCalc.Env (Option a)

  op Specware.getOptSpec      : Option String -> Option Spec

  op SpecCalc.otherSameSCTerm? : SCTerm * SCTerm -> Bool

  op SMPragmaToElement(((prefix, body, postfix), pos): SM_Pragma): SpecElement =
    Pragma(prefix, body, postfix, pos)
end-spec


%%
%% $Id$
%%
%% $Log$
%% Revision 1.56  2011/10/14 10:53:38  mcdonald
%% pervasive internal cleanup affecting about 350 files
%%
%% Among other things:
%%
%% 'sort' should now be fully removed in favor of 'type'
%% (but 'sort' is still accepted for the time being)
%% As a side effect, some files that had "Sort" in their names
%% have been renamed to use "Type", to avoid confusion.
%%
%% The type 'Boolean' should now be fully removed in favor of 'Bool'
%% (but 'Boolean' is still defined as 'Bool' for now)
%%
%% The internal types for structures in the Metaslang abstract syntax
%% are now universally referenced as 'MSType', 'MSTerm', and 'MSPattern',
%% to make it easier to avoid conflicts with descriptions of types, terms,
%% and patterns in other langauges such as SpecCalculus, Lisp, Java, C,
%% Haskell, Isabelle, etc.
%%
%% Some imports have been restructured to more cleanly share declarations.
%%
%% And probably some other minor changes as well...
%%
%% Revision 1.55  2011/10/11 07:37:55  mcdonald
%% internal revisions to simplify specs:
%%
%% pervasive change to eliminate polymorphism in SpecCalculus terms
%%
%% also misc changes to simplify imports
%%
%% also misc changes to clarify some names of some types
%%
%% Revision 1.54  2010/11/25 05:06:34  westfold
%% Summary: Add interface for producing lisp code for sliced specs
%%
%% Revision 1.53  2008/05/21 11:52:31  mcdonald
%% pass position argument down a level in some calls, to make things more regular
%% and to simplify adding debugging messages
%%
%% Revision 1.52  2007/07/11 20:41:27  westfold
%% Initial version of syntax for transform statement.
%%
%% Revision 1.51  2006/05/27 00:21:55  westfold
%% Add support for x-symbol
%%
%% Revision 1.50  2006/05/02 02:53:57  mcdonald
%% new pragmas slot for spec morphisms
%%
%% Revision 1.49  2006/04/05 22:41:23  gilham
%% Support refinement of individual spec ops.
%%
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
%% type_id_map      => type_renaming
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
