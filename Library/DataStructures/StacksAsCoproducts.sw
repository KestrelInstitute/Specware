%% TODO This spec is incompatible with Stacks.sw (name clashes, e.g., for push), but Specware allows both to be imported!
%% TODO Try this (maybe after we give a qualifier to Stacks):
%% StacksAsCoproducts = StacksAsCoproducts qualifying spec
StacksAsCoproducts = spec

%% This spec is a simple refinement of stacks as a sum type.  Because
%% this spec will be a refinement of the Stacks spec, we must define
%% here each of the ops in that Spec.

type Stack a = | Empty_stack | Push(a * Stack a)

%% Just a wrapper around the constructor:

op [a] empty_stack : Stack a = Empty_stack

%% Identical to the version in Stacks:

op [a] empty_stack? (s:Stack a) : Bool = (s = empty_stack)

type NE_Stack a = {s: Stack a | ~(empty_stack? s)}

%% Just a wrapper around the constructor:

op [a] push (elt:a, stk:Stack a) : NE_Stack a = Push(elt, stk)

%% No case needed for Empty_stack because the type forbids it:

op [a] pop (stk:NE_Stack a): Stack a =
  case stk of | Push (_,stk) -> stk

%% No case needed for Empty_stack because the type forbids it:

op [a] top (stk:NE_Stack a): a =
  case stk of | Push (elt,_) -> elt

%% Unlike in Stacks, this one has a definition:

op [a] stackToList : Bijection(Stack a, List a) =
  fn stk -> (case stk of | Empty_stack -> [] | Push(elt, stk) -> Cons(elt, stackToList stk))

% TODO: I would like to handle this better: I want the lemmas defined
% below under helperhook to appear before the subtype obligations for
% stackToList (to help prove the subtype obligations).  This use of
% -hook seems to put them in the right place.  However, a hook can
% only contain Isabelle lemmas, and I really want them all to be
% Specware lemmas.  So for now, I just duplicate the Isabelle lemmas
% as Specware lemmas further below (the Isabelle lemmas have _lemma
% after their names) and then use the Isabelle lemmas to prove the
% Specware lemmas directly.  It's awkward because the Specware lemmas
% about stackToList can't go before stackToList is defined, and there
% is no nice way (that I know of) to sneak their proofs in between the
% definition of stackToList and its subtype obligations.

proof Isa -hook helperhook end-proof

theorem stackToList_equal_empty is [a]
 fa(stk:Stack a) ([] = stackToList stk) = (Empty_stack = stk)

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

op [a] pushl (lst:List a, stk:Stack a): Stack a = 
%  push_aux(reverse(lst),stk)
      case lst of
        | Nil -> stk
        | x::lst1 -> push(x, pushl(lst1,stk))


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Proofs for StacksAsCoproducts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

proof Isa push_Obligation_subtype
   by (simp add: empty_stack_def empty_stack_p_def)
end-proof

proof isa helperhook

  theorem stackToList_equal_empty_lemma: 
    "([] = stackToList stk) = (Empty_stack = stk)"
    apply(cases stk)
    apply(auto)
    done

  theorem stackToList_injective_lemma: 
    "stackToList x = stackToList y \<Longrightarrow> x = y"
    apply(induct x arbitrary: y)
    apply(simp add: stackToList_equal_empty_lemma)
    by (metis Stack.exhaust list.inject stackToList.simps(2) stackToList_equal_empty_lemma)

  theorem stackToList_injective2_lemma: 
    "inj stackToList"
    apply(auto simp add: Function__injective_p__def)
    by(rule stackToList_injective_lemma)

  theorem stackToList_surjective_lemma: 
    " \<exists>x. stackToList x = y"
    apply(induct y)
    apply (metis stackToList.simps(1))
   by (metis stackToList.simps(2))

  theorem stackToList_surjective2_lemma: 
    "surj stackToList"
    apply(auto simp add: Function__surjective_p__def)
    by(rule stackToList_surjective_lemma)

  theorem stackToList_bijective_lemma: 
    "bij stackToList"
    by(simp add: Fun.bij_def stackToList_surjective2_lemma stackToList_injective2_lemma)

end-proof  %end of helperhook


proof isa stackToList_Obligation_subtype
  apply(cut_tac stackToList_bijective_lemma)
  apply(subgoal_tac "stackToList = (\<lambda> (stk::'a Stack). 
          case stk
           of Empty_stack \<Rightarrow> []
            | Push elt stk0 \<Rightarrow> Cons elt (stackToList stk0))")
  apply(simp)
  apply(thin_tac "bij stackToList")
  apply(rule ext)
  by (metis Stack.exhaust Stack.simps(4) Stack.simps(5) stackToList.simps(1) stackToList.simps(2))
end-proof

proof isa stackToList_equal_empty
  by(rule stackToList_equal_empty_lemma)
end-proof

proof isa stackToList_injective
  by(rule stackToList_injective_lemma)
end-proof

proof isa stackToList_injective2
  by(rule stackToList_injective2_lemma)
end-proof

proof isa stackToList_surjective
  by(rule stackToList_surjective_lemma)
end-proof

proof isa stackToList_surjective2
  by(rule stackToList_surjective2_lemma)
end-proof

proof isa stackToList_bijective
  by(rule stackToList_bijective_lemma)
end-proof

proof isa stackToList_listToStack
  apply(simp add: listToStack_def)
  apply(rule Function__f_inverse_apply)
  by (rule stackToList_bijective)
end-proof


end-spec



%% TODO: Try this once Stacks gets a qualifier:
%% M = morphism Stacks -> StacksAsCoproducts {Stack +-> StacksAsCoproducts.Stack}
M = morphism Stacks -> StacksAsCoproducts {}

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

proof Isa top_def_Obligation_subtype
  apply(cases "stk")
  apply(auto simp add: empty_stack_def empty_stack_p_def)
end-proof

proof Isa top_def
  apply(auto)
  apply(rule ext)
  apply(auto simp add: empty_stack_def empty_stack_p_def)
  apply(case_tac "x")
  apply(auto)
end-proof

proof isa pop_def_Obligation_subtype
  apply(case_tac "stk", auto simp add: empty_stack_def empty_stack_p_def)
end-proof

proof isa pop_def
  apply(auto)
  apply(rule ext)
  apply(auto simp add: empty_stack_def empty_stack_p_def)
  apply(case_tac "x")
  apply(auto simp add: listToStack_def)
  apply(cut_tac f="\<lambda> x . stackToList x" and x="Stack" in Function__inverse_f_apply)
  defer
  apply (simp add: stackToList_injective2_lemma)
  by (rule stackToList_bijective)
end-proof

proof isa push_def
  apply(rule ext)
  apply(case_tac "x", auto)
  apply(rule stackToList_injective)
  apply(auto simp add: push_def stackToList_listToStack)
end-proof

proof isa empty_stack_p_def
  apply(rule ext)
  apply(simp only: empty_stack_p_def)
end-proof

proof isa empty_stack_def
  apply(rule stackToList_injective)
  apply(auto simp add: empty_stack_def stackToList_listToStack)
end-proof

proof isa listToStack_def
  apply(rule ext)
  apply(simp add: listToStack_def)
end-proof

proof Isa push_def_Obligation_subtype
  apply(metis empty_stack_def empty_stack_p_def list.distinct(1) stackToList.simps(1) stackToList_listToStack)
end-proof