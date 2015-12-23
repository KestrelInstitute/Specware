(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* Q: Does the code for the MapVec functions come from
      Specware/Library/Structures/Data/Maps/Handwritten/Lisp/MapAsVector.lisp?
   A: Yes

   Q: What does implementing stacks as vectors have to do with maps?
   A: Stacks are implemented as a pair (Vector,index-of-top + 1) with
       destructive push/pop.  MapVec provides maps->vectors with
       destructive update for use in single-threaded contexts.  
*)

StacksAsVectors =
StacksAsVectors qualifying
spec
  import /Library/Structures/Data/Maps/MapVec

% Stacks are implemented as a pair (Vector,index-of-top + 1)
  type VStack a = Map(Nat,a) * Nat 

  op [a] empty_stack : VStack a = 
          (MapVec.V_empty_map, 0)

  op [a] empty_stack? (stk:VStack a) : Bool = 
          (stk.2 = 0)

 type NE_VStack a = {s: VStack a | ~(empty_stack? s)}

(* Note: push destructively assigns a to the next free position in the vector
         and bumps up the index.  *)
  op [a] push (elt:a, stk:VStack a): NE_VStack a =
    (MapVec.V_update(stk.1, stk.2, elt), stk.2 + 1)

(*  precondition: the stack is non-empty *)
  op [a] top (stk:NE_VStack a): a =
     MapVec.V_eval(stk.1, (stk.2 - 1):Nat) %TODO, without the Nat here, Specware assumes Int, which seems wrong and leads to an Isabelle error

(* Note: pop does not remove the element from the map.  It just adjusts the stack
   height so that the top element becomes invalid.  *)
  op [a] pop (stk:NE_VStack a): VStack a = (stk.1, (stk.2) - 1)

  op [a] pushl (lst:List a, stk:VStack a): VStack a = 
     push_aux(lst,stk)       % first arg was reverse(lst)

  op [a] push_aux (lst:List a, stk:VStack a): VStack a =
    case lst of
      | [] -> stk
      | elt::y -> push_aux(y, push(elt, stk))

(*  Q: Is this true, since an empty_stack is not the only stack whose
       second component is 0, unless we add an invariant to that effect.
    A: It is bisimilar to the empty stack; i.e. we have observable equality;
       but then the question is the nature of the Isabelle proof... 
*)

  theorem empty_stack is [a]
    fa(stk:VStack a)((stk = empty_stack) = (stk.2 = 0))

%% TODO add a definition:
  op [a] stackToList : Bijection(VStack a, List a)

  op [a] listToStack : Bijection(List a, VStack a) = inverse stackToList

end-spec


%% This morphism was previously called "S"
M = morphism Stacks -> StacksAsVectors {Stack +-> VStack, NE_Stack +-> NE_VStack}
