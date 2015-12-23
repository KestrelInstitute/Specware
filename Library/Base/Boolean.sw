(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Bool qualifying spec

(* Make sure that the extensions to standard Isabelle are loaded (this is done
solely for verification purposes). *)

import IsabelleExtensions

(* "Bool" and "Bool.Bool" are parsed as the Specware built-in Boolean type. *)

type Boolean = Bool  % "Boolean" is a deprecated name for Bool 

type Prop = Bool

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
  fa(p:Bool,e:a) ((if p then e else e) = e)

% This can be used to prove an equality of booleans by proving the
% forward and backward implications separately.
theorem bool_equal_split is fa(a:Bool, b:Bool) ((a => b) && (b => a)) => (a = b)


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
