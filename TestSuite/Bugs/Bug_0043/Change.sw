Flipflop =
  spec
     sort Flip
     op flop : Flip -> Flip
     axiom change is
        fa(x) ~(flop x = x)
  endspec

GiveNameToTilde = % since ~ can't appear directly in morphisms
 spec
     op negation : Boolean -> Boolean
   def negation = (~)
 endspec

FlipFlopImplementation =
  morphism Flipflop -> GiveNameToTilde {Flip +-> Boolean, flop +-> negation}

Correct =
  prove change in obligations FlipFlopImplementation
