% ======================================================================
% Specs
% ======================================================================

A = spec
  op g1(n: Int): (Int * Option Int)
  op g2(n: Int): Bool
  op f(n: Int): {r: Int | if ex (m, w) (m, Some w) = g1 n && r = m ** w && m > 2 then g2 r else true}
end-spec

B = spec 
  import A 
end-spec

% ======================================================================
% term transform 'simpIf'
%   op MSRule.simpIf(spc: Spec) (tm: TransTerm): Option MSTerm
% ======================================================================

% WARNING: In transform, At referenced unknown op: f1
% return the same spec if the 'at' location (op name) cannot be resolved
TF_Bad_1 = transform B by {at f1 simpIf}
TF_Bad_2 = B {at f1 simpIf}

TF_Good_1 = transform B by {at [f] {simpIf};
                            showSpec simpIf}

TF_Good_2 = transform B by {at [f, g1] {simpIf}}

TF_Good_3 = transform B by {at [f] simpIf}

TF_Good_4 = transform B by {at f {simpIf}}

TF_Good_5 = transform B by {at f simpIf}
TF_Good_6 = B {at f simpIf}



