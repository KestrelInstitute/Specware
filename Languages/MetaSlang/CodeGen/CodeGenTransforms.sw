spec

import /Languages/MetaSlang/CodeGen/DebuggingSupport

%% SpecTransforms used for code generation

import /Languages/MetaSlang/CodeGen/SubstBaseSpecs                      %  (1) Lisp C Java  subtBaseSpecs
import /Languages/MetaSlang/Transformations/NormalizeTopLevelLambdas    %  (2) Lisp C Java  normalizeTopLevelLambdas
import /Languages/MetaSlang/Transformations/InstantiateHOFns            %  (3) Lisp C Java  instantiateHOFns
import /Languages/MetaSlang/Transformations/RemoveCurrying              %  (4)      C Java  removeCurrying
import /Languages/MetaSlang/Transformations/LiftUnsupportedPatterns     %  (5)      C Java  liftUnsupportedPatterns [expand type restrictions into cases]
import /Languages/MetaSlang/Transformations/PatternMatch                %  (6) Lisp C Java  translateMatch
import /Languages/MetaSlang/Transformations/LambdaLift                  %  (7)      C Java  lambdaLiftWithImportsSimulatingClosures, lambdaLift
import /Languages/MetaSlang/Transformations/RecordMerge                 %  (8) Lisp C Java  expandRecordMerges
import /Languages/MetaSlang/Transformations/LetWildPatToSeq             %  (9)      C Java  letWildPatToSeq

%% TODO: Clarify these four.  They are currently rather confusing.
import /Languages/MetaSlang/Transformations/EtaExpansion                % (10) Lisp   Java  etaExpandDefs
import /Languages/MetaSlang/Transformations/ArityNormalize              % (11) Lisp   Java  arityNormalize
import /Languages/MetaSlang/CodeGen/ConformOpDecls                      % (12)      C Java  conformOpDecls
import /Languages/MetaSlang/CodeGen/EncapsulateProductArgs              % (13)      C Java  encapsulateProductArgs

                                                                        % (14)      C Java  introduceRecordMerges  -- RecordMerge alredy imported

import /Languages/MetaSlang/Transformations/TypeAllTerms                %                   typeAllTerms [work in progress]
import /Languages/MetaSlang/Transformations/ExpandTypeDefs              % (15)      C Java  expandTypeDefs
import /Languages/MetaSlang/Transformations/NarrowTypes                 %           C Java  narrowTypes                         [Nat  => Nat16, etc.]
import /Languages/MetaSlang/CodeGen/ReviseTypesForCodeGen               % (16)      C Java  reviseTypesForC, reviseTypesForJava [Nat7 => (Nat8 | fits_in_7_bits?), etc.]
import /Languages/MetaSlang/Transformations/AddEqOps                    % (17)      C Java  addEqOps
import /Languages/MetaSlang/Transformations/AddTypeConstructors         % (18)      C Java  addTypeConstructors

import /Languages/MetaSlang/Transformations/SliceSpec                   % (19) Lisp C Java  sliceSpecForLisp, sliceSpecForC, sliceSpecForJava

import /Languages/MetaSlang/CodeGen/RemoveGeneratedSuffixes             % (20) Lisp C Java  removeGeneratedSuffixes

end-spec
