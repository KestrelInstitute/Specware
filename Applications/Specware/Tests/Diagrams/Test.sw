let
  a = spec {
     sort X
     op x : X
    }
  b = spec {
     sort Y
     op y : Y
    }
  c = spec {
     sort Z
     op z : Z
    }
  m = morphism a -> b {X +-> Y, x +-> y}
  n = morphism a -> c {X +-> Z, x +-> z}
  d = diagram {
      u : v -> w +-> m
      x : y -> z +-> n
    }
in
  colimit d
