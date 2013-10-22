% ======================================================================
% Specs
% ======================================================================

A = spec
  type T
  op f : T -> T
end-spec

% ======================================================================
% unknown spec transform
% ======================================================================

% ERROR: in transform: Unrecognized transform: nonExistentSpecTransform 
TF_Bad_1 = transform A by {nonExistentSpecTransform}
TF_Bad_2 = A {nonExistentSpecTransform}

