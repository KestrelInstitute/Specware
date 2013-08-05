DeMorgan = spec

  op bnot (x:Boolean) : Boolean = if x then false else true
  op bor (x:Boolean,y:Boolean) : Boolean = if x then true else y
  op band (x:Boolean,y:Boolean) : Boolean = if x then y else false

  theorem demorgan1 is
    fa (x:Boolean, y:Boolean) bnot (band (x,y)) = bor (bnot x, bnot y)

  theorem demorgan2 is
    fa (x:Boolean, y:Boolean) bnot (bor (x,y)) = band (bnot x, bnot y)

%%% The proofs:

  proof ACL2 demorgan1
    :hints (("Goal" :in-theory (enable band bor not)))
  end-proof

  proof ACL2 demorgan2
    :hints (("Goal" :in-theory (enable band bor not)))
  end-proof

end-spec