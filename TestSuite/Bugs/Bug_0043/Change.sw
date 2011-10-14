Flipflop =
  spec
     type Flip
     op flop : Flip -> Flip
     axiom change is
        fa(x) ~(flop x = x)
  endspec

GiveNameToTilde = % since ~ can't appear directly in morphisms
 spec
    op negation : Bool -> Bool
   def negation = (~)
 endspec

FlipFlopImplementation =
  morphism Flipflop -> GiveNameToTilde {Flip +-> Bool, flop +-> negation}

ShouldBeProvable =
  prove change in obligations FlipFlopImplementation
