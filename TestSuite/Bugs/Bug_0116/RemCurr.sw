S = spec

 sort A
 sort S
 sort R
 op h: E * (A -> E) * S -> R * S
 sort E = S -> R * S

 op bind: E * (A -> E) -> E
 def bind(f, g) s =
    h(f, g, s)

 op seq: E * E -> E
 def seq(f, g) = bind(f, (fn _ -> g))

conjecture TRUE is true

(*
Here is what the removeCurrying produces:

 op  bind-1-1 : E * (A * S -> R * S) * S -> R * S
 def bind-1-1 (f, g, s) = h(f, g, s)

 op  seq-1-1 : E * E * S -> R * S
 def seq-1-1 (f, g, x) = bind-1-1((f, (fn x -> g x)), x)
                                  ^^^^^^^^^^^^^^^^^^^^^
The above seems wrong, shouldn't it be:
 def seq-1-1 (f, g, x) = bind-1-1(f, (fn x -> g x), x)


Here is the original MetaSlang that inspired this example:

 op  SpecCalc.monadSeq :
  [a, b] SpecCalc.Env(a) * SpecCalc.Env(b) -> SpecCalc.Env(b)
 def SpecCalc.monadSeq (f, g) = SpecCalc.monadBind(f, (fn _ -> g))

 op  SpecCalc.monadBind :
  [a, b] SpecCalc.Env(a) * (a -> SpecCalc.Env(b)) -> SpecCalc.Env(b)
 def SpecCalc.monadBind (f, g) state = 
   (case f state
      of (Ok y, newState) -> g y newState
       | (Exception except, newState) -> (Exception except, newState))

*)

endspec

P = prove TRUE in S