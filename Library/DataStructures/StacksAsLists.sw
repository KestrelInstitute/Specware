%% TODO This spec is incompatible with Stacks.sw (name clashes, e.g., for push), but Specware allows both to be imported!
%% TODO Try this (maybe after we give a qualifier to Stacks):
%% StacksAsLists = StacksAsLists qualifying spec
StacksAsLists = spec

%% This spec is a simple refinement of stacks as lists.  Note that the
%% Stacks spec constrains stacks to be isomorphic to lists.  Here we
%% define them as actually equal to lists.  As usual, because this
%% spec will be a refinement of the Stacks spec, we must define here
%% each of the ops in that Spec.

%% Unlike in the spec Stacks, this has a definition here:
type Stack a = List a

op [a] empty_stack : Stack a = []

%% Identical to the version in Stacks:

op [a] empty_stack? (s:Stack a) : Bool = (s = empty_stack)

op [a] push (elt:a, stk:Stack a) : Stack a = Cons(elt, stk)

%% No case needed for [] because the type forbids it:

op [a] pop (stk:Stack a | stk ~= empty_stack): Stack a =
  case stk of | Cons (_,stk) -> stk

%% No case needed for [] because the type forbids it:

op [a] top (stk:Stack a | stk ~= empty_stack): a =
  case stk of | Cons (elt,_) -> elt

%% Unlike in Stacks, this one has a definition:

op [a] stackToList : Bijection(Stack a, List a) =
  fn stk -> stk

theorem stackToList_equal_empty is [a]
 fa(stk:Stack a) ([] = stackToList stk) = (empty_stack = stk)

theorem stackToList_injective is [a]
  fa(stk1 : Stack a, stk2 : Stack a) (stackToList stk1 = stackToList stk2) => (stk1 = stk2)

theorem stackToList_injective2 is [a]
  injective? (stackToList:(Stack a -> List a))

theorem stackToList_surjective is [a]
  fa(y:List a) ex(x:Stack a) stackToList x = y

theorem stackToList_surjective2 is [a]
  surjective? (stackToList:(Stack a -> List a))

theorem stackToList_bijective is [a]
  bijective? (stackToList:(Stack a -> List a))

%% Identical to the version in Stacks:

op [a] listToStack : Bijection(List a, Stack a) = inverse stackToList

theorem stackToList_listToStack is [a]
  fa(lst : List a) (stackToList (listToStack lst)) = lst



%% Push the elements of lst onto stk (earlier elements of lst go deeper in the stack):
%% Identical to the version in Stacks:

op [a] push_aux (lst:List a, stk:Stack a): Stack a =
  case lst of
  | [] -> stk
  | elt::y -> push_aux(y, push(elt, stk))

%% Push the elements of lst onto stk (earlier elements of lst go shallower in the stack):                  
%% Identical to the version in Stacks:
%% TODO refine this to be a no-op?  or just run the conversion?  what should this be over in the stacks as co-products spec?
op [a] pushl (lst:List a, stk:Stack a): Stack a = 
  push_aux(reverse(lst),stk)


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Proofs for StacksAsLists
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



proof isa stackToList_Obligation_subtype
   by (metis bij_betw_cong bij_id id_def)
end-proof

proof isa stackToList_equal_empty
  apply(simp add: stackToList_def empty_stack_def)
end-proof

proof isa stackToList_injective
  apply(simp add: stackToList_def)
end-proof

proof isa stackToList_injective2
  apply(simp add: stackToList_def)
end-proof

proof isa stackToList_surjective
  apply(simp add: stackToList_def)
end-proof

proof isa stackToList_surjective2
  apply(simp add: stackToList_def)
end-proof

proof isa stackToList_bijective
  apply(simp add: stackToList_def Fun.bij_def)
end-proof

proof isa stackToList_listToStack
  apply(simp add: listToStack_def)
  apply(rule Function__f_inverse_apply)
  by (rule stackToList_bijective)
end-proof


end-spec



%% TODO: Try this once Stacks gets a qualifier:
%% M = morphism Stacks -> StacksAsLists {Stack +-> StacksAsLists.Stack}
M = morphism Stacks -> StacksAsLists {}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Proofs for morphism M
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

proof isa pushl_def
  by(simp add: pushl_def)
end-proof

proof isa push_aux_def
  apply(rule ext)
  apply(auto simp add: push_aux.simps)
  apply(case_tac "a")
  apply(simp)
  apply(simp)
end-proof

proof isa top_def_Obligation_subtype
  apply(auto simp add: stackToList_def empty_stack_def)
end-proof

proof isa top_def
  apply(rule ext)  
  apply(case_tac stk)  
  apply(auto simp add: empty_stack_def stackToList_def)
end-proof

proof isa pop_def_Obligation_subtype
  apply(auto simp add: stackToList_def empty_stack_def)
end-proof

proof isa pop_def
  apply(auto)
  apply(rule ext)
  apply(auto simp add: empty_stack_def)
  apply(case_tac "x")
  apply(auto simp add: listToStack_def)
  apply(cut_tac f="\<lambda> x . stackToList x" and x="Stack" in Function__inverse_f_apply)
  apply(auto simp add: stackToList_bijective)
  apply(auto simp add: stackToList_def)
  by (metis inj_on_id2 inv_f_eq)
end-proof

proof isa push_def
  apply(rule ext)
  apply(case_tac "x", auto)
  apply(rule stackToList_injective)
  apply(auto simp add: push_def stackToList_listToStack stackToList_def listToStack_def)
  by (metis inj_on_id2 inv_f_eq)
end-proof

proof isa empty_stack_def
  apply(auto simp add: empty_stack_def listToStack_def stackToList_def)
  by (metis inj_on_id2 inv_f_eq)
end-proof

%% TODO Why is this obligation not being generated?  Maybe because the definition of listToStack is identical in Stacks and StacksAsLists.
%% proof isa listToStack_def
%%   apply(rule ext)
%%   apply(simp add: listToStack_def)
%% end-proof
