psl {
  op even : Nat -> Boolean

  proc expon(x : Nat, y : Nat) : Nat {
  let
  var z : Nat
  in {
    z := 1;
    do {
        ~(y = 0) ->
            do {
                even y ->
                  x := x * 2;
                  y := y div 2
            };
            y := y - 1;
            z := z * x
     };
     return_expon := z
  }}
}

