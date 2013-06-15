spec

import /Languages/MetaSlang/CodeGen/DebuggingSupport

%% SpecTransforms used for code generation

import /Languages/MetaSlang/CodeGen/SubstBaseSpecs                      %  (1) Lisp C Java  subtBaseSpecs
import /Languages/MetaSlang/Transformations/RemoveTheorems              %  (2) Lisp C Java  removeTheorems
import /Languages/MetaSlang/Transformations/SliceSpec                   %  (3) Lisp C Java  sliceSpecForLisp, sliceSpecForC, sliceSpecForJava
import /Languages/MetaSlang/Transformations/RemoveCurrying              %  (4)      C Java  removeCurrying
import /Languages/MetaSlang/Transformations/NormalizeTopLevelLambdas    %  (5) Lisp C Java  normalizeTopLevelLambdas
import /Languages/MetaSlang/Transformations/InstantiateHOFns            %  (6) Lisp C Java  instantiateHOFns
import /Languages/MetaSlang/Transformations/LambdaLift                  %  (7)      C Java  lambdaLiftWithImportsSimulatingClosures, lambdaLift
import /Languages/MetaSlang/Transformations/PatternMatch                %  (8) Lisp C Java  translateMatch
import /Languages/MetaSlang/Transformations/RecordMerge                 %  (9) Lisp C Java  expandRecordMerges
import /Languages/MetaSlang/Transformations/LetWildPatToSeq             % (10)      C Java  letWildPatToSeq
import /Languages/MetaSlang/CodeGen/UnfoldTypeAliases                   % (11)        Java  unfoldTypeAliases
import /Languages/MetaSlang/Transformations/ExpandTypeDefs              % (12)      C Java  expandTypeDefs
import /Languages/MetaSlang/CodeGen/RemoveSubtypes                      % (13)      C Java  removeNonNatSubtypes
import /Languages/MetaSlang/Transformations/LiftUnsupportedPatterns     % (14)      C Java  liftUnsupportedPatterns
import /Languages/MetaSlang/CodeGen/Poly2Mono                           % (15)      C Java  poly2monoAndDropPoly
import /Languages/MetaSlang/Transformations/Simplify                    % (16)      C Java  simplifySpec
import /Languages/MetaSlang/Transformations/AddEqOps                    % (16)      C Java  addEqOps
                                                                        % (18)      C Java  sliceSpecForLisp, sliceSpecForC, sliceSpecForJava  [see 3]
import /Languages/MetaSlang/Transformations/AddTypeConstructors         % (19)      C Java  addTypeConstructors
import /Languages/MetaSlang/CodeGen/ConformOpDecls                      % (20)      C Java  conformOpDecls
import /Languages/MetaSlang/Transformations/ArityNormalize              % (21) Lisp   Java  arityNormalize, etaExpandDefs
import /Languages/MetaSlang/CodeGen/AdjustAppl                          % (22)      C Java  adjustAppl
                                                                        % (23)      C Java  lambdaLiftWithImports  [see 7]
                                                                        % (24)      C Java  translateMatch         [see 8]
import /Languages/MetaSlang/Transformations/DistinctVariable            % (25)        Java  distinctVariable

end-spec
