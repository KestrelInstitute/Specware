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

% An example op that accesses a Tree.
op total (t:Tree): Nat =
  case t of
  | Leaf x -> x
  | Branch b -> total(b.left) + total(b.right)

% An example op that creates a Tree (having nodes m to n, inc.)
op between(m:Nat, n:Nat | m <= n): Tree =
  if m = n
  then Leaf m
  else let mid = (m + n) divF 2 in
       Branch {left=between(m, mid), right=between(mid + 1, n)}

% An example op that transforms a Tree.
op double(t:Tree): Tree =
  case t of
  | Leaf x -> Leaf (2 * x)
  | Branch {left=L, right=R} -> Branch {left=double(L), right=double(R)}
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
TreeSpec2 = isos{isomorphism((isoChildren,osiChildren), (isoTree,osiTree))}

TreeSpec3 = TreeSpec2
            {at total' {unfold osiTree;
                        unfold osiChildren;
                        simplify (lr *.iso__osi)
                        }
             }
            {at between' {unfold isoTree;
                          simplify (lr *.iso__osi);
                          unfold isoChildren;
                          simplify (lr *.iso__osi)
                          }
             }
            {at double' {unfold osiTree;
                         simplify (lr *.iso__osi);
                         simplify (lr *.iso__osi, unfold osiChildren);
                         simplify (lr *.iso__osi, unfold isoTree);
                         simplify (lr *.iso__osi, unfold isoChildren)
                         }
             }

% The following, commented-out spec is the result.
% The definitions for Tree', isoTree and osiTree have been generated.
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
op double' (t: Tree'): Tree'
  = isoTree
      (case osiTree t
        of Leaf x -> Leaf(2 * x)
         | Branch {left = L, right = R} -> 
           Branch{left = osiTree(double'(isoTree L)), right = osiTree(double'(isoTree R))})
op between' (m: Nat, n: Nat | m <= n): Tree'
  = isoTree
      (if m = n
        then Leaf m 
       else 
       let mid = (m + n) divF 2 in 
       Branch
         {left = let (m0, n0 | m0 <= n0) = (m, mid) in 
                 osiTree(between'(m0, n0)), 
          right = let (m0, n0 | m0 <= n0) = (mid + 1, n) in 
                  osiTree(between'(m0, n0))})
op total' (t: Tree'): Nat
  = case osiTree t
     of Leaf x -> x
      | Branch b -> (total'(isoTree(b.left)) + total'(isoTree(b.right)))
refine def total' (t: Tree'): Nat
  = case t
     of Branch y -> (total'(y.first) + total'(y.second))
      | Leaf y -> y
refine def between' (m: Nat, n: Nat | m <= n): Tree'
  = if m = n
     then Leaf m 
    else 
    let mid = (m + n) divF 2 in 
    Branch
      {first = let (m0, n0 | m0 <= n0) = (m, mid) in 
               between'(m0, n0), 
       second = let (m0, n0 | m0 <= n0) = (mid + 1, n) in 
                between'(m0, n0)}
refine def double' (t: Tree'): Tree'
  = case t
     of Branch y -> Branch{first = double'(y.first), second = double'(y.second)}
      | Leaf y -> Leaf(2 * y)
end-spec
*)

