
XML qualifying spec
  %% Stuff to augment Base library

  % TODO: add Nat.toHex for specware

  op toHex : Nat -> String

  def toHex (n : Nat) : String =
    let
       def aux (n, digits) =
	 let digit = rem (n, 16) in
	 let n = div(n, 16) in
	 if n = 0 then
	   implode (map (fn digit -> 
			 chr (if digit <= 9 then
				48 + digit
			      else
				%% 55 + 10 = 65 = A
				55 + digit))
		        digits)
	 else
	   aux (n, cons (digit, digits))
    in
      aux (n, [])

  sort NE_List a = (List a | non_null?)

  def fa (a) non_null? (xx : List a) = ~ (List.null xx)

  op sublist? : fa (a) List a * List a -> Boolean

endspec