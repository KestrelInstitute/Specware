% ======================================================================
% Specs
% ======================================================================

A = spec
  type T
  op f : T -> T
end-spec

% ======================================================================
% spec transform 'copySpec'
%   op SpecTransform.copySpec (spc : Spec) : Spec
% ======================================================================

% ERROR: in transform: Too many arguments to transform (at "copy of A")
TF_Bad_1 = transform A by {copySpec "copy of A"}
TF_Bad_2 = A {copySpec "copy of A"}

TF_Good_1 = transform A by {copySpec;
                            showSpec "copy of A"}
TF_Good_2 = A {copySpec;
               showSpec "copy of A"}

