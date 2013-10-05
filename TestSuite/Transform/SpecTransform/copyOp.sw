% ======================================================================
% Specs
% ======================================================================

A = spec
  type T
  op f : T -> T
end-spec

% ======================================================================
% spec transform 'copyOp'
%   op SpecTransform.copyOp (qid : QualifiedId, spc : Spec) : Spec 
% ======================================================================

% ERROR: in transform: Expected argument: OpName (at "f")
TF_Bad_1 = transform A by {copyOp "f";
                           showSpec "A with copy of op 'f'"}
TF_Bad_2 = A {copyOp "f";
              showSpec "A with copy of op 'f'"}

TF_Good_1 = transform A by {copyOp f;
                            showSpec "A with copy of op 'f'"}
TF_Good_2 = A {copyOp f;
               showSpec "A with copy of op 'f'"}

