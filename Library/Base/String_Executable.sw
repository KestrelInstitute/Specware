spec
 import String

 refine def natConvertible (s:String) : Bool =
   let cs = explode s in
   (exists? isNum cs) && (forall? isNum cs)

 refine def intConvertible (s:String) : Bool =
   let cs = explode s in
   (exists? isNum cs) &&
   ((forall? isNum cs) || (head cs = #- && forall? isNum (tail cs)))

 op explodedStringToNat(l: List Char): Nat =
   foldl (fn (result, dig) -> result * 10 + ord dig - 48) 0 l

 refine def stringToInt (s:String | intConvertible s) : Int =
   let e_s = explode s in
   let firstchar::r_s = e_s in
   if firstchar = #- then - (explodedStringToNat r_s)
                     else    explodedStringToNat e_s

 refine def stringToNat (s:String | natConvertible s) : Nat =
   explodedStringToNat(explode s)

 refine def explode (s:String) : List Char =
   tabulate (length s, fn i -> s@i)

 refine def implode(char_list: List Char): String =
   foldl (fn (s, c) -> s ^ show c) "" char_list      % Hopefully code generators will provide a more efficient version


proof isa Nat__natConvertible__1__obligation_refine_def
sorry
end-proof

proof isa Integer__intConvertible__1__obligation_refine_def
sorry
end-proof

proof isa explodedStringToNat_Obligation_subtype
sorry
end-proof

proof isa Integer__stringToInt__1__obligation_refine_def
sorry
end-proof

proof isa Nat__stringToNat__1__obligation_refine_def
sorry
end-proof

proof isa String__explode__1_Obligation_subtype
sorry
end-proof

proof isa String__explode__1__obligation_refine_def
sorry
end-proof

proof isa String__implode__1__obligation_refine_def
sorry
end-proof

proof isa Integer__stringToInt__1_Obligation_exhaustive
sorry
end-proof

proof isa Nat__stringToNat__1_Obligation_exhaustive
sorry
end-proof

endspec
