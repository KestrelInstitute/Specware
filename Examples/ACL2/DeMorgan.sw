(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

DeMorgan = spec

  op bnot (x:Bool) : Bool = if x then false else true
  op bor (x:Bool,y:Bool) : Bool = if x then true else y
  op band (x:Bool,y:Bool) : Bool = if x then y else false

  theorem demorgan1 is
    fa (x:Bool, y:Bool) bnot (band (x,y)) = bor (bnot x, bnot y)

  theorem demorgan2 is
    fa (x:Bool, y:Bool) bnot (bor (x,y)) = band (bnot x, bnot y)

%%% The proofs:

  proof ACL2 demorgan1
    :hints (("Goal" :in-theory (enable band bor not)))
  end-proof

  proof ACL2 demorgan2
    :hints (("Goal" :in-theory (enable band bor not)))
  end-proof

end-spec
