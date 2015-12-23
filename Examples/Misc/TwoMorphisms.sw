(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

A = spec
    type A
    op A.op1 : A * A -> Bool
    op A.op2 : A * A -> Bool
    axiom a1 is fa(x:A) op1(x,x) % op1 is reflexive
    axiom a2 is fa(x:A,y:A) op2(x,y) = op2(y,x) % op2 is symmetric
end-spec

B = spec
    type B = Nat
    op B.op1(x:B, y:B) : Bool = (x <= y)
    op B.op2(x:B, y:B) : Bool = ((x mod 3) = (y mod 3))
end-spec

CheckRqmtsB = morphism A -> B {A+-> B, A.op1 +-> B.op1,A.op2 +->B.op2}
proof Isa a1
  apply(simp add: B__op1_def)
end-proof
proof Isa a2
  apply(auto simp add: B__op2_def)
end-proof
    
C = spec
    import B
    type C = | Wrapper B
    %% helper op:
    op unwrap(x:C) : B = let Wrapper x0 = x in x0
    op C.op1 (x:C,y:C) : Bool = B.op1(unwrap x,unwrap y)
    op C.op2 (x:C,y:C) : Bool = B.op2(unwrap x,unwrap y)
end-spec

CheckRqmtsC = morphism A -> C {A+-> C, A.op1 +-> C.op1,A.op2 +->C.op2}

%% These proofs use the proofs from CheckRqmtsB:
proof Isa a1
  apply(simp add: C__op1_def TwoMorphisms_CheckRqmtsB.a1)
end-proof
proof Isa a2
  apply(simp add: C__op2_def TwoMorphisms_CheckRqmtsB.a2)
end-proof

%% The magic command to import the proofs from CheckRqmtsB:
proof Isa Thy_Morphism TwoMorphisms_CheckRqmtsB
end-proof
