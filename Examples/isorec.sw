(*
 * An example of applying an isomorphic type refinement to a type
 * that is part of a mutually recursive set of types.
 *)


% The original spec.
TreeSpec = spec

% Children and Tree are mutually recursive.
  type Children = {left:Tree, right:Tree}

  type Tree =
    | Leaf Nat
    | Branch Children

% An example op on Tree.
  op total (t:Tree) : Nat =
    case t of
    | Leaf x -> x
    | Branch b -> total(b.left) + total(b.right)

end-spec


% The spec giving the isomorphism.
isos = spec
  import TreeSpec

% We are creating a new type, Children', that is the essentially the same as Children,
% but with the fields renamed.
% We need to also transform the Tree type, giving Tree', since we need a type that
% refers to Children' rather than to Children; likewise, Children' refers to
% Tree' rather than to Tree.

% We define Children' manually, since that is were the desired change is.
  type Children' = {first:Tree', second:Tree'}

% The Tree' type is fully implied by isomorphism between Children and Children'.
% We declare it here manually because it is referenced in the definition of Children',
% but we do not need to define it - the definition will be created automatically.
  type Tree'

% Likewise, we manually define the isomorphism ops for Children/Children',
% because they capture our intention. The isomorphims ops of Tree/Tree' are
% fully implied and will be automatically defined.
  op isoChildren(therec:Children): Children' =
    {first=isoTree(therec.left), second=isoTree(therec.right)}
  op osiChildren(therec:Children'): Children =
    {left=osiTree(therec.first), right=osiTree(therec.second)}

% We declare to isomorhpism ops for Tree/Tree' because we need to reference them in
% the isomorphism ops for Children/Children', but we do not need to define them -
% their definitions will be created automatically.
  op isoTree: Tree -> Tree'
  op osiTree: Tree' -> Tree

end-spec

% Apply the isomorphism. Note that we give both pairs of iso/osi ops.
TreeSpec2 = isos{isomorphism((isoChildren,osiChildren), (isoTree,osiTree))
                [unfold osiChildren, unfold osiTree]}


% The following, commented-out spec is the result.
% The definitions for Tree', isoTree and osiTree have been generated.
% The total' op is equivalent to the total op, but operates directly
% with Tree' and Children' rather than Tree.
(*
  spec  
  import TreeSpec
 
  type Tree' =  | Branch Children' | Leaf Nat
 
  type Children' = {first: Tree', second: Tree'}
  op isoTree: Tree -> Tree'
  op isoChildren (therec: Children): Children'
    = {first = isoTree(therec.left), second = isoTree(therec.right)}
  op osiTree: Tree' -> Tree
  op osiChildren (therec: Children'): Children
    = {left = osiTree(therec.first), right = osiTree(therec.second)}
  def isoTree (x: Tree): Tree'
    = case x
       of Branch y -> Branch(isoChildren y)
        | Leaf y -> Leaf y
  def osiTree (x: Tree'): Tree
    = case x
       of Branch y -> Branch(osiChildren y)
        | Leaf y -> Leaf y
 
  theorem generated.inverse_iso_is_osi is Function.inverse isoChildren = osiChildren
 
  theorem generated.inverse_osi_is_iso is Function.inverse osiChildren = isoChildren
 
  theorem generated.iso__osi is fa(x': Children') isoChildren(osiChildren x') = x'
 
  theorem generated.osi__iso is fa(x: Children) osiChildren(isoChildren x) = x
 
  theorem generated.inverse_iso_is_osi is Function.inverse isoTree = osiTree
 
  theorem generated.inverse_osi_is_iso is Function.inverse osiTree = isoTree
 
  theorem generated.iso__osi is fa(x': Tree') isoTree(osiTree x') = x'
 
  theorem generated.osi__iso is fa(x: Tree) osiTree(isoTree x) = x

  op total' (t: Tree'): Nat
    = case t
       of Branch y -> (total'(y.first) + total'(y.second))
        | Leaf y -> y
  end-spec
*)
