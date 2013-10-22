% ======================================================================
% Specs
% ======================================================================

A = spec
  op g1(n: Int): Option(Option Int)
  op f1a(n: Int): {r: Int | ex (m: Int, y) Some(y) = g1 n && Some m = y && r = m ** 2}

  theorem ex_some is [a,b] fa(e, p) (ex(x:a,y:b) Some y = e && p(x,y)) = (case e of Some y -> ex(x) p(x,y) | _ -> false)
end-spec

% ======================================================================
% unknown term transforms / rules
% ======================================================================

% ERROR: in transform: Unrecognized transform: ex_some
TF_Bad_1 = transform A by {at f1a ex_some}

% ERROR: in transform: Unrecognized rule reference
TF_Bad_2 = transform A by {at f1a simplify [ex_some]}
