(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%% A simple morphism example.

A = spec
  op double (x:Nat) : Nat = x + x
end-spec

B = spec
  op double (x:Nat) : Nat = 2 * x
end-spec

M = morphism A -> B {}


proof isa double_def
  by(auto simp add: double_def)
end-proof

