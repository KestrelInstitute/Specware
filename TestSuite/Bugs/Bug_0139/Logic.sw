Logic = Logic qualifying spec

  type Predicate a = a -> Bool

  op <= infixl 20 : [a] Predicate a * Predicate a -> Bool
  def [a] <= (p1,p2) =
    (fa(x:a) p1 x => p2 x)

  type PredicateProperty a = Predicate (Predicate a)

  op minimallySatisfies? : [a] Predicate a * PredicateProperty a -> Bool
  def minimallySatisfies?(pred,prop) =
    prop pred &&
    (fa(pred1) prop pred1 => pred <= pred1)

  conjecture TRUE is true

endspec 

Prove = prove TRUE in Logic
