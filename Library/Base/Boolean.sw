Bool qualifying spec

(* Make sure that the extensions to standard Isabelle are loaded (this is done
solely for verification purposes). *)

import IsabelleExtensions

(* Specware has a built-in type Boolean, which will be renamed to Bool at some
point in the future. Meanwhile, we introduce Bool as a synonym for Boolean, in
order to enable the use of Bool immediately and to facilitate the migration from
Boolean to Bool in existing specs. When we change Boolean to Bool in the
Specware implementation, the following type definition will be removed. *)

type Bool = Boolean

% lifting of negation, conjunction, disjunction, and truth to predicates:

op [a] ~~~ (p: a -> Bool) : a -> Bool = fn x:a -> ~(p x)

op [a] &&& (p1: a -> Bool, p2: a -> Bool) infixr 25 : a -> Bool =
  fn x:a -> p1 x && p2 x

op [a] ||| (p1: a -> Bool, p2: a -> Bool) infixr 24 : a -> Bool =
  fn x:a -> p1 x || p2 x

op [a] TRUE: a -> Bool = fn _:a -> true

op [a] FALSE: a -> Bool = fn _:a -> false



% Some simple theorems (these were in Library/DataStructures/StructuredTypes.sw):
% Are any of these built in to the Specware rewriter itself?

theorem conditional_true is [a]
  fa(p:a,q:a) ((if true then p else q) = p)

theorem conditional_false is [a]
  fa(p:a,q:a) ((if false then p else q) = q)

theorem conditional_noop is [a]
  fa(p:Boolean,e:a) ((if p then e else e) = e)


% Isabelle pragmas

proof Isa ~~~ [simp] end-proof
proof Isa &&& [simp] end-proof
proof Isa ||| [simp] end-proof
proof Isa TRUE__def [simp] end-proof
proof Isa FALSE [simp] end-proof

% Isabelle mapping:

proof Isa ThyMorphism
  type Bool.Bool -> bool
  Bool.TRUE -> TRUE
end-proof

% Haskell mapping:

#translate Haskell -morphism
  type Bool.Bool -> Bool
#end

endspec
