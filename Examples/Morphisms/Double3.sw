(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%% Note that there are two ops in spec A with the simple name "double"
%% but different qualifiers.  The morphism will map both of them to
%% "bar.double".

A = spec
  op foo.double (x:Nat) : Nat = x + x
  op foo2.double (x:Nat) : Nat = x + x + 0
end-spec

B = foo qualifying spec
  op bar.double (x:Nat) : Nat = 2 * x
end-spec

M = morphism A -> B {}

proof isa foo__double_def
  by(auto simp add: bar__double_def)
end-proof
proof isa foo2__double_def
  by(auto simp add: bar__double_def)
end-proof

