T1 = translate (spec endspec) by {Integer +-> Char}

T2 = translate (spec endspec) by {Integer +-> X}

S = spec
  import T2
  op c : Integer
  op d : X
endspec
