
A = spec type A endspec

D = spec
      import C
      type D
    endspec

C = spec
      import B
      type C
    endspec

B = spec
      import A
      type B
    endspec

   