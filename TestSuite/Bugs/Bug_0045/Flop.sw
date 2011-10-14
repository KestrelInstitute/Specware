Flip =
  spec
     type Flip
     op flip : Flip -> Flip
  endspec

Flop =
  spec
     type A
     type B
     op A.flop : A -> A
     op B.flop : B -> B
  endspec

FlipFlopImplementation =
  morphism Flip -> Flop {Flip +-> A, flip +-> flop}
