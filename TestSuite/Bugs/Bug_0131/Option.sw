O = PFunctions qualifying spec

  import /Provers/ProofChecker/Libs

  (* Functions are always total in Metaslang. Partial functions can be modeled
  using Option:
  - (f x = Some y) means that f maps x to y, while
  - (f x = None) means that f is not defined on x.
  *)

  type PFunction(a,b) = a -> Option b

  op liftToPartial : [a,b] (a -> b) -> PFunction(a,b)
  def liftToPartial f x = Some (f x)

  op o infixl 24 : [a,b,c] PFunction(b,c) * PFunction(a,b) -> PFunction(a,c)
  def o (f,g) x = case g x of Some y -> f y
                            | None   -> None

  op definedAt? : [a,b] PFunction(a,b) * a -> Boolean
  def definedAt?(f,x) = embed? Some (f x)

  op undefinedAt? : [a,b] PFunction(a,b) * a -> Boolean
  def undefinedAt?(f,x) = embed? None (f x)

  op finite? : [a,b] PFunction(a,b) -> Boolean
  def [a,b] finite? f =
    Set.finite? (fn(x:a) -> definedAt?(f,x))

  type FFunction(a,b) = (PFunction(a,b) | finite?)

endspec

P = prove o_Obligation_exhaustive in obligations O