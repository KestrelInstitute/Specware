A = spec op fff : Nat -> Nat def fff = fn iii -> iii+1 endspec
B = spec op fff : Nat -> Nat def fff = fn jjj -> jjj+2 endspec
C = spec import A import B def ggg = fff endspec
