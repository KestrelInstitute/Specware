Flipflop =
  spec
     sort Flip
     op flop : Flip -> Flip
     axiom change is
        fa(x) ~(flop x = x)
  endspec

FlipFlopImplementation =
  morphism Flipflop -> spec endspec {Flip +-> Boolean, flop +-> Boolean.~}

Correct =
  prove change in obligations FlipFlopImplementation
