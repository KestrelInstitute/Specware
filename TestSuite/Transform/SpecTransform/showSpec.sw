% ======================================================================
% Specs
% ======================================================================

A = spec
  type T
  op f : T -> T
end-spec

% ======================================================================
% spec transform 'showSpec':
%   op SpecTransform.showSpec (spc : Spec) (msg : String) : Spec
% ======================================================================

% Empty String Now OK
TF_WasBad_1 = transform A by {showSpec}
TF_WasBad_2 = A {showSpec}

% string argument does not need string quotes if it is an identifier
TF_Good_1 = transform A by {showSpec abc}
TF_Good_2 = A {showSpec abc}

