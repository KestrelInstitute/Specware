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

 refine def stringToNat (s:String | natConvertible s) : Int =
   explodedStringToNat(explode s)

 refine def explode (s:String) : List Char =
   tabulate (length s, fn i -> s@i)

 refine def implode(char_list) =
   foldl (fn (s, c) -> s ^ show c) "" char_list      % Hopefully code generators will provide a more efficient version
endspec
