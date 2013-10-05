% ======================================================================
% Specs
% ======================================================================

A = spec
  type T
  op f : T -> T
end-spec

B = spec
  import A
  op g : T -> Bool
end-spec

M = morphism A -> B {}

% ======================================================================
% spec transform 'makeImportingSpec':
%   op SpecTransform.makeImportingSpec (spc : Spec) : Spec
% ======================================================================

TF_Good_1 = transform A by {makeImportingSpec;
                            showSpec ""}

% transforming a morphism means transforming its codomain
TF_Good_2 = transform M by {makeImportingSpec;
                            showSpec ""}

