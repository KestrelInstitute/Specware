(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec

import /Languages/MetaSlang/CodeGen/DebuggingSupport

%% SpecTransforms used for code generation

import /Languages/MetaSlang/CodeGen/Generic/SubstBaseSpecs              %  (1) Lisp C Java  subtBaseSpecs
import /Languages/MetaSlang/CodeGen/Generic/NormalizeTopLevelLambdas    %  (2) Lisp C Java  normalizeTopLevelLambdas
import /Languages/MetaSlang/CodeGen/Generic/InstantiateHOFns            %  (3) Lisp C Java  instantiateHOFns
import /Languages/MetaSlang/CodeGen/Generic/RemoveCurrying              %  (4)      C Java  removeCurrying
import /Languages/MetaSlang/CodeGen/Generic/LiftUnsupportedPatterns     %  (5)      C Java  liftUnsupportedPatterns [expand type restrictions into cases]
import /Languages/MetaSlang/CodeGen/Generic/PatternMatch                %  (6) Lisp C Java  translateMatch
import /Languages/MetaSlang/CodeGen/Generic/LambdaLift                  %  (7)      C Java  lambdaLiftWithImportsSimulatingClosures, lambdaLift
import /Languages/MetaSlang/CodeGen/Generic/RecordMerge                 %  (8) Lisp C Java  expandRecordMerges
import /Languages/MetaSlang/CodeGen/Generic/LetWildPatToSeq             %  (9)      C Java  letWildPatToSeq

%% TODO: Clarify these four.  They are currently rather confusing.
import /Languages/MetaSlang/CodeGen/Generic/EtaExpansion                % (10) Lisp   Java  etaExpandDefs
import /Languages/MetaSlang/CodeGen/Generic/ArityNormalize              % (11) Lisp   Java  arityNormalize
import /Languages/MetaSlang/CodeGen/Generic/ConformOpDecls              % (12)      C Java  conformOpDecls
import /Languages/MetaSlang/CodeGen/Generic/EncapsulateProductArgs      % (13)      C Java  encapsulateProductArgs

                                                                        % (14)      C Java  introduceRecordMerges  -- RecordMerge alredy imported

import /Languages/MetaSlang/CodeGen/Generic/TypeAllTerms                %                   typeAllTerms [work in progress]
import /Languages/MetaSlang/CodeGen/Generic/ExpandTypeDefs              % (15)      C Java  expandTypeDefs
import /Languages/MetaSlang/CodeGen/Generic/NarrowTypes                 %           C Java  narrowTypes                         [Nat  => Nat16, etc.]
import /Languages/MetaSlang/CodeGen/Generic/ReviseTypesForCodeGen       % (16)      C Java  reviseTypesForC, reviseTypesForJava [Nat7 => (Nat8 | fits_in_7_bits?), etc.]
import /Languages/MetaSlang/CodeGen/Generic/AddEqOps                    % (17)      C Java  addEqOps
import /Languages/MetaSlang/CodeGen/Generic/AddTypeConstructors         % (18)      C Java  addTypeConstructors

import /Languages/MetaSlang/CodeGen/Generic/SliceSpec                   % (19) Lisp C Java  sliceSpecForLisp, sliceSpecForC, sliceSpecForJava

import /Languages/MetaSlang/CodeGen/Generic/RemoveGeneratedSuffixes     % (20) Lisp C Java  removeGeneratedSuffixes

end-spec
