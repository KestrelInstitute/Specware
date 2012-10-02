let
  a = spec {
     type X
     op x : X
    }
  b = spec {
     type Y
     op y : Y
    }
  c = spec {
     type Z
     op z : Z
    }
  m = morphism a -> b {X +-> Y, x +-> y}
  n = morphism a -> c {X +-> Z, x +-> z}
  p = morphism b -> c {Y +-> Z, y +-> z}
  d = diagram {
      u : v -> w +-> m,
      x : v -> z +-> n
    }
in
  colimit d
