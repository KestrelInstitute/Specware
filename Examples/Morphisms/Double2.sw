(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%% This version shows how the morphism mechanism allows different
%% qualifiers when the meaning is unambiguous.

A = spec
  op foo.double (x:Nat) : Nat = x + x
end-spec

%% Note that foo.double is not explicitly mapped to anything.
%% Specware infers that it should be mapped to bar.double:

B = foo qualifying spec
  op bar.double (x:Nat) : Nat = 2 * x
end-spec

M = morphism A -> B {}


proof isa foo__double_def
  by(auto simp add: bar__double_def)
end-proof

