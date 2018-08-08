LinearOrder = spec

  import PartialOrder

  axiom comparability is
    fa(a:A, b:A) a <= b || b <= a

end-spec
