% ======================================================================
% Specs
% ======================================================================

A1 = spec
  op g1(n: Int): Option(Option Int)
  op f1a(n: Int): {r: Int | ex (m: Int, y) Some(y) = g1 n && Some m = y && r = m ** 2}
end-spec

A = spec
  theorem ex_List_in? is [a] fa (l: List a, p) (ex(x: a) x in? l && p x) = (exists? p l)

  op g1(n: Int): Option(Option Int)
  op f1(n: Int): {r: Int | ex (m: Int) Some(Some m) = g1 n && r = m ** 2}  % && r > 2}
  op f1a(n: Int): {r: Int | ex (m: Int, y) Some(y) = g1 n && Some m = y && r = m ** 2}

  op f(n: Int): {r: Int | ex (m: Int) m = n ** 2 && r = m ** 2 && r > 2}

  op g2(n: Int): Option (Int * Int)
  op f2(n: Int): {r: Int | ex (m, w) Some (m, w) = g2 n && r = m ** w && r > 2}

  op g3(n: Int): List Int
  op f3(n: Int): {r: Int | ex (m: Int, z) m in? g3 n && z = m ** 2 && z > 2 && r > 3}

  op g4(n: Int): (Int * Int)
  op f4(n: Int): {r: Int | ex (m, w) (m, w) = g4 n && r = m ** w && r > 2}

  op g5(n: Int): List (Int * Int)
  op f5(n: Int): {r: Int | ex (m, w) (m, w) in? g5 n && r = m ** w && r > 2}

  op g6(n: Int): (Int * Option Int)
  op f6(n: Int): {r: Int | ex (m, w) (m, Some w) = g6 n && r = m ** w && r > 2}

  op g7(n: Int): List (Int * Option Int)
  op f7(n: Int): {r: Int | ex (m, w) (m, Some w) in? g7 n && r = m ** w && r > 2}

  op g8(n: Int): Bool
  op f8(n: Int): {r: Int | if ex (m, w) (m, Some w) = g6 n && r = m ** w && m > 2 then g8 r else true}

  op g9(n: Int): List(Option(Option Int))
  op f9(n: Int): {r: Int | ex (m: Int) Some(Some m) in? g9 n && r = m ** 2 && r > 2}

end-spec

B = spec 
  import A 
end-spec

% ======================================================================
% term transform 'structureEx'
%   op MSTermTransform.simpIf(spc: Spec) (tm: MSTerm): Option MSTerm
% ======================================================================

TF_Good_1 = transform A1 by {at f1a structureEx;
                             showSpec tf}

TF_Good_2 = transform A by {at (f, f1, f2, f3, f4, f5, f6, f7) apply structureEx;
                            showSpec tf}

TF_Good_3 = transform B by {at f1 structureEx;
                            showSpec tf}

TF_Good_4 = transform B by {at [f, f1, f1a, f2, f3, f4, f5, f6, f7, f8, f9] structureEx;
                            showSpec tf}

TF_Good_5 = transform B by {at [f, f1, f1a, f2, f3, f4, f5, f6, f7, f8, f9]
                              {structureEx;
                               lr ex_List_in?};
                            showSpec tf}

TF_Good_6 = transform B by {at [f, f1, f1a, f2, f3, f4, f5, f6, f7, f8, f9]
                              {apply structureEx;
                               lr ex_List_in?};
                            showSpec tf}
