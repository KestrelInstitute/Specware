(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)


XML qualifying spec
  %% Stuff to augment Base library

  % TODO: add Nat.toHex for specware

  op toHex (n : Nat) : String =
    let
       def aux (n, digits) =
	 let digit = n modT 16 in
	 let n = n div 16 in
	 if n = 0 then
	   implode (map (fn digit ->
			 chr (if digit <= 9 then
				48 + digit
			      else
				%% 55 + 10 = 65 = A
				55 + digit))
		        digits)
	 else
	   aux (n,  digit::digits)
    in
      aux (n, [])

  type NE_List a = (List a | non_null?)

  op [a] non_null? (xx : List a): Bool = ~ (empty? xx)

  op sublist? : [a] List a * List a -> Bool 
  def sublist? (aa, bb) =
    case leftmostPositionOfSublistAndFollowing (aa, bb) of 
      | None -> false
      | _    -> true

endspec
