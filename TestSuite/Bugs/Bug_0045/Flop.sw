Flipflop =
  spec
     sort Flip
     op flop : Flip -> Flip
  endspec

FlipFlopImplementation =
  morphism Flipflop -> spec endspec {Flip +-> Boolean, flop +-> ~}
