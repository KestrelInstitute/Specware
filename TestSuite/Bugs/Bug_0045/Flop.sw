Flip =
  spec
     sort Flip
     op flip : Flip -> Flip
  endspec

Flop =
  spec
     sort A
     sort B
     op A.flop : A -> A
     op B.flop : B -> B
  endspec

FlipFlopImplementation =
  morphism Flip -> Flop {Flip +-> A, flip +-> flop}
