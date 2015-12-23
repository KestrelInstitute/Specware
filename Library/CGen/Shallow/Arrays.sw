(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

% ------------------------------------------------------------------------------
% Experiments with array operations
% ------------------------------------------------------------------------------

Array = spec 

import CTarget

op [a] @ (array elems : Array a, i:Nat | i < length elems) infixl 30 : a =
  elems @ i

op [a] update (array elems : Array a, i:Nat, x:a | i < length elems) : Array a =
  array (update (elems, i, x))

theorem update_length is [a]
  fa (arr: Array a, i:Nat, x:a)        
   i < length arr => length (update (arr, i, x) )  = length arr

theorem update_at_same is [a]
  fa (arr: Array a, i:Nat, x:a)        
   i < length arr => update (arr, i, x) @ i = x

theorem update_at_neq is [a]
  fa (arr: Array a,i:Nat, j:Nat, x:a)  
   i < length arr && j < length arr && j ~= i => update (arr, i, x) @ j = arr @ j

% ------------------------------------------------------------------------------
% Some standard specs, not algorithmic
% ------------------------------------------------------------------------------

op Array.+ (x: Array Int, y: Array Int | length x = length y) infixl 25
            : Array Int
   = the (z: Array Int)  length z = length x &&
             (fa (i:Nat) i < length x => z @ i = x @ i + y @ i)

op Array.- (x: Array Int, y: Array Int | length x = length y) infixl 25
            : Array Int
   = the (z: Array Int)  length z = length x &&
             (fa (i:Nat) i < length x => z @ i = x @ i - y @ i)

op Array.* (x: Array Int, y: Array Int | length x = length y) infixl 27
            : Array Int
   = the (z: Array Int)  length z = length x &&
             (fa (i:Nat) i < length x => z @ i = x @ i * y @ i)

op array_sum (array elems : Array Int) : Int =  foldl (+) (0:Int) elems

op mult (x: Array Int, y: Array Int | length x = length y) infixl 27
            : Int
   = array_sum (x * y)

%% Currently, the translation of this is rejected by Isabelle.
% op [a] sortt (ord:LinearOrder a) (array elems : Array a) : Array a 
%     = array (List.sortt ord elems)

proof isa update_length
  apply(case_tac arr)
  apply(auto)
end-proof

proof isa update_at_same_Obligation_subtype0 
  apply(case_tac arr)
  apply(auto)
end-proof

proof isa update_at_same
  apply(case_tac arr)
  apply(auto)
end-proof

proof isa update_at_neq_Obligation_subtype0
  apply(case_tac arr)
  apply(auto)
end-proof

proof isa update_at_neq
  apply(case_tac arr)
  apply(auto)
end-proof

proof isa Array__e_pls_Obligation_the
  sorry
end-proof

proof isa Array__e_dsh_Obligation_the
  sorry
end-proof

proof isa Array__e_ast_Obligation_the
  sorry
end-proof

%% I moved this to the Array spec to prevent name clashes. (It
%% appeared in Array1 and also in Array1a, which is generated from
%% Array1.  So I couldn't legally include both Array1 and Array1a in
%% All.sw.) --Eric

op abs_add (arr: Array Int) (n:Nat, r: Int | n < length arr) : Int 
   =  r + arr @ n

end-spec

% ------------------------------------------------------------------------------
% A coarse refinement
% ------------------------------------------------------------------------------

Array1 = spec 
  import Array

refine def array_sum (arr : Array Int) : Int  
 = let def aux (n:Nat | n <= length arr): Int
            = if n = 0 then 0 else aux (n-1) + arr @ (n-1)
   in aux (length arr)

% Keep in mind that array indices go from 0 to length arr - 1

theorem isucc_inv_ipred is   isucc = inverse ipred

theorem isucc_is_add_1 is    fa (x:Int) isucc x = x + 1

theorem ipred_is_sub_1 is    fa (x:Int) ipred x = x - 1

end-spec

% ------------------------------------------------------------------------------
% And a transformation into the imperative form
% ------------------------------------------------------------------------------

Array1a = transform Array1 by
  { at (array_sum)
       {simplify (rl ipred_is_sub_1)
        ; fold abs_add}
  }

% ------------------------------------------------------------------------------
% The same again, more specific
% ------------------------------------------------------------------------------

Array2 = spec 
  import Array1
  import Imp

% theorem higher_order_decompose_test is
%    fa (arr : Array Int, x:Int, aux: Int -> Int)
%       (fn (n,r) -> r +  arr @ (n-1)) (x,aux (ipred x))
%         = aux (ipred x) + arr @ (x - 1)
%    
% refine def array_sum (arr : Array Int) : Int  
%  = let def aux (n:Int | n < length arr): Int
%             = if n = 0 then 0 
%                        else (fn (n,r) -> r + arr @ (n-1)) (n, aux (ipred n))
%    in aux (length arr)

   
% this should be a simple "fold frec_aux" but even with the commented hints above
% this doesn't work yet

refine def array_sum (arr : Array Int) : Int  
  = frec_aux (0, 0,  fn (n,r) -> r + arr @ (n-1), ipred, length arr)

end-spec

% ------------------------------------------------------------------------------
% Transformation into the imperative form
% ------------------------------------------------------------------------------

Array2a = transform Array2 by
  {at (array_sum)
      {simplify (lr rec_aux_to_loop)
      ;unfold floop
      ;simplify (rl isucc_inv_ipred)
      ;simplify (lr isucc_is_add_1)
      % ; unfold abs_add 
      }}

(******************************************************************************
RESULT:

refine def array_sum(arr: C.Array(Int)): Int
  = '
      ({x <- backtick 0;
        r <- backtick 0;
        while(x ~= C.length arr) ({x <- backtick(x + 1);
                                   r <- backtick(r + arr @ (x-1));
                                   -});
        return r})
end-spec

*******************************************************************************)
