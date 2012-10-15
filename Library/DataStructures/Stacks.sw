%Stacks qualifying 
spec

(* currently we can't refine a sum type to a product, so these constructors
   must become ops, and we must use destructors instead of inductive/cases defs.
*)

  type Stack a         % = | empty_stack | push (a*Stack a)
  op [a] empty_stack : Stack a
  op [a] push (elt:a, stk:Stack a) : Stack a

  op [a] empty_stack? : Stack a -> Boolean

  op [a] pop (stk:Stack a | stk ~= empty_stack):  Stack a 
%     = case stk of | push (_,stk) -> stk

  op [a] top (stk:Stack a | stk ~= empty_stack):  a 
%      = case stk of | push (elt,_) -> elt

% This pushes a list onto the stack (in reserver order)
  op [a] pushl (lst:List a, stk:Stack a): Stack a = 
      push_aux(reverse(lst),stk)

%    case lst of
%      | nil -> stk
%      | elt::y -> push(elt, pushl(y,stk))

  op [a] push_aux (lst:List a, stk:Stack a): Stack a =
    case lst of
      | [] -> stk
      | elt::y -> % push(elt, push_aux(y,stk))
                  push_aux(y, push(elt, stk))
end-spec