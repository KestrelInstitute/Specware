refine /Library/Base/String by {

 op Nat.natConvertible (s:String) : Bool =
   let cs = explode s in
   (exists? isNum cs) && (forall? isNum cs)

 op Integer.intConvertible (s:String) : Bool =
   let cs = explode s in
   (exists? isNum cs) &&
   ((forall? isNum cs) || (hd cs = #- && forall? isNum (tl cs)))

 op Integer.stringToInt (s:String | Integer.intConvertible s) : Integer =
   let firstchar::_ = explode s in
   if firstchar = #- then - (stringToNat (substring (s,1,length s)))
                     else    stringToNat s

}
