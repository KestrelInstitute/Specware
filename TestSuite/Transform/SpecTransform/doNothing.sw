% ======================================================================
% Specs
% ======================================================================

A = spec
  type T
  op f : T -> T
end-spec

% ======================================================================
% spec transform 'doNothing':
%   op SpecTransform.doNothing(spc: Spec): Spec
% ======================================================================

% ERROR: Unknown unit A0
TF_Bad_1 = transform A0 by {doNothing}
TF_Bad_2 = A0 {doNothing}

TF_Good_1 = transform A by {doNothing}
TF_Good_2 = A {doNothing}

