% ======================================================================
% Specs
% ======================================================================

A = A qualifying spec
  op g1(n: Int): (Int * Option Int)
  op g2(n: Int): Bool
  op f(n: Int): {r: Int | if ex (m, w) (m, Some w) = g1 n && r = m ** w && m > 2 then g2 r else true}
end-spec

% ======================================================================
% Term Transform 'at' spec ops
% ======================================================================

% Warning: In transform, At referenced unknown op: f
TF_Bad_1 = transform A by {at f simpIf}

TF_Good_1 = transform A by {at A.f simpIf}

