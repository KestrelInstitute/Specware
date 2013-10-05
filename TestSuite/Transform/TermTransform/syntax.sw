% ======================================================================
% Specs
% ======================================================================

A = spec
  type T
  op f : T -> T
end-spec

% ======================================================================
% Term Transform 'at' spec ops
% ======================================================================

% syntactic error (at {f})
% parentheses and brackets can be used in 'at' locations, but not braces
TF_Bad_1 = transform A by {at {f} simpIf}

% syntactic error (at [simplIf], (simpIf))
% braces are used for transformation rules, not parentheses or brackets
TF_Bad_2 = transform A by {at f [simpIf]}
TF_Bad_3 = transform A by {at f (simpIf)}

% syntactic error (at ,)
% delimiter for transformation rules is ';'
TF_Bad_4 = transform A by {at f {simpIf, structureEx}

% syntactic error (at "f")
% locations at need to be (qualified) id for spec ops
TF_Bad_5 = transform A by {at "f" simpIf}

