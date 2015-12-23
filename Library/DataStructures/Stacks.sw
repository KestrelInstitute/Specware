(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%% A specification for (finite) stacks.  For refinements of this spec,
%% see BasicStacks.sw and StacksAsLists.sw and StacksAsVectors.sw.

Stack qualifying spec

%% Old comment: currently we can't refine a sum type to a product
%% (TODO what about isomorphic type refinement?), so these
%% constructors must become ops, and we must use destructors instead
%% of inductive/cases defs.

type Stack a

%% We give semantics to stacks by making them isomorphic to lists.
%% The declaration of stackToList gives rise to an implicit axiom that
%% Stacks and Lists are isomorphic.  Then we define the Stack
%% operations below in terms of their corresponding list operations.

op [a] stackToList : Bijection(Stack a, List a)

%% Unlike stackToList, we can give this one a definition:

op [a] listToStack : Bijection(List a, Stack a) = inverse stackToList

%% ListToStack is injective (TODO Other ways to state injectivity?):

theorem listToStack_equal_listToStack is [a]
  fa(stk1 : List a, stk2 : List a) (listToStack stk1 = listToStack stk2) = (stk1 = stk2)

%% The empty Stack corresponds to the empty list:

op [a] empty_stack : Stack a = listToStack []

op [a] empty_stack? (s:Stack a) : Bool = (s = empty_stack)

type NE_Stack a = {s: Stack a | ~(empty_stack? s)}

theorem empty_stack?_empty? is [a]
  fa(l:List a) empty_stack?(listToStack l) = empty? l

theorem empty?_empty_stack? is [a]
  fa(s:Stack a) empty?(stackToList s) = empty_stack? s

%% TODO Add op to test for non-emptiness (and a type for non-empty
%% stacks, which we could use below)?  Also add an op for the length
%% of a stack?  I guess such new ops would have to be given
%% refinements in the morphisms..

%% The push operation on Stacks corresponds to Cons on lists:

op [a] push (elt:a, stk:Stack a) : NE_Stack a = listToStack (Cons(elt, stackToList stk))

%% The pop operation on Stacks corresponds to tail on lists:

op [a] pop (stk:NE_Stack a): Stack a = listToStack (tail (stackToList stk))

%% The top operation on Stacks corresponds to head on lists:

op [a] top (stk:NE_Stack a): a = head (stackToList stk)

theorem push_not_empty is [a]
  fa(elt:a, stk: Stack a) (push(elt, stk) = empty_stack) = false

theorem top_push is [a]
  fa(elt:a, stk: Stack a) top(push(elt, stk)) = elt

theorem pop_push is [a]
  fa(elt:a, stk: Stack a) pop(push(elt, stk)) = stk

%% Push the elements of lst onto stk (earlier elements of lst go deeper in the stack).
%% Note that this function is tail-recursive.
%% TODO rename to pushl_aux?

op [a] push_aux (lst:List a, stk:Stack a): Stack a =
  case lst of
    | [] -> stk
    | elt::y -> push_aux(y, push(elt, stk))

%% TODO add analogous theorem about pushl:

theorem push_aux_append is [a]
  fa(x:List a,y:List a,stk:Stack a) push_aux(x ++ y, stk) = push_aux(y, push_aux(x, stk))

%% Push the elements of lst onto stk (earlier elements of lst go shallower in the stack):

op [a] pushl (lst:List a, stk:Stack a): Stack a = 
%  push_aux(reverse(lst),stk)
      case lst of
        | Nil -> stk
        | x::lst1 -> push(x, pushl(lst1,stk))

theorem pushl_alt_def is [a]
  fa(lst: List a, stk: Stack a)
  pushl (lst, stk) = push_aux(reverse(lst),stk)

theorem stackToList_of_pop is [a]
  fa(stk: NE_Stack a)
     stackToList (pop stk) = tail (stackToList stk)

theorem length_of_stackToList_non_zero is [a]
  fa(stk: NE_Stack a)
    ~(length (stackToList stk) = 0)

theorem equal_stackToList_empty is [a]
  fa(stk: Stack a)
    (stackToList stk = []) = (stk = empty_stack)

%% TODO This is what I want to do for pushl but cannot, due to an Isabelle translator bug (JIRA issue SPEC-41):
%% %% Push the elements of lst onto stk (earlier elements of lst go shallower in the stack):
%% %% This op is not tail-recursive but is refined to a tail-recursive op below.

%%   op [a] pushl (lst:List a, stk:Stack a): Stack a = 
%%     case lst of
%%     | [] -> stk
%%     | elt::y -> push(elt, pushl(y,stk))
                  
%% %% Tail-recursive refinement of pushl:

%%   refine def [a] pushl (lst:List a, stk:Stack a): Stack a = 
%%     push_aux(reverse(lst),stk)


theorem stack_cases is [a]
  fa(stk:Stack a) (stk = empty_stack) || (ex(elem:a, stkb : Stack a) stk = push(elem,stkb))

theorem stack_induction_helper is [a]
  fa(p: Stack a -> Bool)
    ((p empty_stack) && 
     (fa(stk : Stack a, elem : a) (p stk => p (push(elem,stk))))) =>
     (fa(lst : List a) p (listToStack lst))


theorem stack_induction is [a]
  fa(p: Stack a -> Bool)
    ((p empty_stack) && 
     (fa(stk : Stack a, elem : a) (p stk => p (push(elem,stk))))) =>
     (fa(stk : Stack a) p stk)


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Proofs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

proof Isa push_aux_append
  apply(induct "x" arbitrary: stk)
  apply(simp)
  apply(simp)
end-proof

proof Isa pop_Obligation_subtype
  by (metis List__nonEmpty_p_def Stack__empty_p_empty_stack_p null_rec(2))
end-proof

proof Isa top_Obligation_subtype
  by (rule Stack__pop_Obligation_subtype)
end-proof

proof Isa listToStack_equal_listToStack
  by (metis Function__f_inverse_apply Stack__listToStack_def Stack__stackToList_subtype_constr)
end-proof

proof Isa empty_stack?_empty?
  by (simp add: List__empty_p__def Stack__empty_stack_def Stack__empty_stack_p_def Stack__listToStack_equal_listToStack)
end-proof

proof Isa empty?_empty_stack?
  by (metis Function__inverse_f_apply Stack__empty_stack_p_empty_p Stack__listToStack_def Stack__stackToList_subtype_constr)
end-proof

proof Isa push_Obligation_subtype
  by (simp add: Stack__empty_stack_p_empty_p)
end-proof

proof Isa push_not_empty
  apply(simp add: Stack__push_def Stack__empty_stack_def Stack__listToStack_equal_listToStack)
end-proof

proof Isa top_push
  apply(simp add: Stack__top_def Stack__push_def Stack__listToStack_def)
  by (metis Function__f_inverse_apply list.sel(1) Stack__stackToList_subtype_constr)
end-proof

proof Isa pop_push
  apply(simp add: Stack__push_def Stack__pop_def)
  by (metis Function__f_inverse_apply Function__inverse_f_apply Stack__listToStack_def Stack__stackToList_subtype_constr list.sel(3))
end-proof

proof Isa stackToList_of_pop_Obligation_subtype
  by (rule Stack__top_Obligation_subtype)
end-proof

proof Isa stackToList_of_pop
  apply(simp add: Stack__pop_def)
  apply( metis Function__f_inverse_apply Stack__listToStack_def Stack__stackToList_subtype_constr)
end-proof

proof Isa length_of_stackToList_non_zero
  apply(metis List__nonEmpty_p_def Stack__stackToList_of_pop_Obligation_subtype length_0_conv)
end-proof

proof Isa stack_cases
  apply(case_tac "Stack__stackToList stk")
  apply (metis Stack__equal_stackToList_empty)
  apply(simp add: Stack__push_def Stack__listToStack_def)
  by (metis Function__inverse_f_apply Stack__empty_p_empty_stack_p Stack__stackToList_of_pop 
            Stack__stackToList_subtype_constr list.sel(3) null_rec(1))
end-proof

proof Isa stack_induction_helper
  apply(induct lst)
  apply(simp add: Stack__empty_stack_def)
  apply(auto simp add: Stack__push_def)
  apply(metis Function__f_inverse_apply Stack__listToStack_def Stack__stackToList_subtype_constr)
end-proof

proof Isa stack_induction
  apply(cut_tac p=p and lst="Stack__stackToList stk" in Stack__stack_induction_helper)
  apply(simp)
  apply(simp)
  apply(auto simp add: Stack__listToStack_def)
  apply(metis Function__inverse_f_apply Stack__stackToList_subtype_constr)
end-proof

proof Isa equal_stackToList_empty
  by (simp add: Stack__empty_stack_p_def[symmetric] null_def[symmetric] Stack__empty_p_empty_stack_p)
end-proof

proof Isa pushl_alt_def
  apply(induct lst)
  apply (metis Stack__push_aux.simps(1) Stack__pushl.simps(1) rev.simps(1))
  apply (metis Stack__push_aux.simps(1) Stack__push_aux.simps(2) Stack__push_aux_append Stack__pushl.simps(2) rev.simps(2))
end-proof

end-spec
