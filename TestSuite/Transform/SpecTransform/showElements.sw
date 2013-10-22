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

% ======================================================================
% spec transform 'showElements':
%    op SpecTransform.showElements (spc : Spec) (msg : String) (depth : Nat) (verbose? : Bool) : Spec
% ======================================================================

% ERROR: in transform: Expected argument: Num (at 'true')
TF_Bad_1 = transform B by {showElements "" true t}
TF_Bad_2 = B {showElements "" true t}

% ERROR: in transform: Expected argument: Bool (at 't')
TF_Bad_3 = transform B by {showElements "" 2 t}

% ERROR: in transform: Unexpected argument type (at '("", 2, true)')
% arguments need to be curried
TF_Bad_4 = transform B by {showElements("", 2, true)}

%ERROR: in transform: Too many arguments to transform
%FIXME: incorrect error message
TF_Bad_5 = transform B by {showElements "" -1 true}

TF_Good_1 = transform B by {showElements "elems" 2 true}
TF_Good_2 = B {showElements "elems" 2 true}

