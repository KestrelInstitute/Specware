
A = spec type A endspec

E = spec
      import C
      type E
    endspec

D = spec
      import C
      type D
    endspec

F = spec
      import E
      type F
    endspec

C = spec
      import B
      type C
    endspec

G = spec
      import A
      type G
    endspec

B = spec
      import A
      type B
    endspec

H = spec
      import B
      type H
    endspec
   