% Status: I changed some things in this file to get it to proc.  Note
% sure if it is correct or needed.  -Eric, 10/11/12

%---- Functions missing from existing library datatypes ---------
spec
import Maps
%----- set stuff ------
op [a] list2set (lst : List a) : Set a = foldl (fn (set, elem) -> set_insert(elem, set)) empty_set lst

% Cons is now a constructor.
% %NOTE: cons doesn't satisfy the axioms for using set_fold
% def [a] set2list: Set a -> List a = set_fold [] Cons

%completely crap implementation of size
%op size : [a] Set a -> Nat 
%def size(s) = length (set2list s)

(*
  why do you need it to be 1-1?
  op [a,b] set_map : ((a -> b) | 1-1?) -> Set a -> Set b
  op [a,b] 1-1? : (a -> b) -> Boolean

  axiom set_map is
        (fa(f,x,s) x in? s => (ex(y) (y in? set_map(f,s) && y = f(x)))) &&
        (fa(f,y,s) y in? set_map(f,s) => (ex(x) (x in? s && y = f(x))))
*)

% This was a conflict.  -Eric
% %Another awful hack
% op [a,b] Set.map : (a->b) -> Set a -> Set b
% def [a,b] Set.map f s =
%     list2set (map f (set2list s))
    
op [a] Set.forallIn : Set a -> (a -> Boolean) -> Boolean
  axiom Set.forAllIn is fa(x,s,p) Set.forallIn s p <=> (x in? s => p(x))
  
def Set.forallIn s p =
    set_fold true (&&) (Set.map p s)

op flatten : [a] Set (Set a) -> Set a
def flatten = set_fold empty_set (Set.\/)

op SoL.flatten : [a] Set (List a) -> List a
def SoL.flatten = set_fold [] (++)


op fm2fn : [a,b] Map(a,b) -> (a -> b)
def fm2fn(fm) = (fn(x) -> TMApply(fm, x))

op numRange : Nat * Nat -> List Nat
def numRange(a:Nat, b:Nat) =
    if (a>=b) then [a] else Cons(a, numRange(a+1, b))
%

op List.forallIn : [a] List a -> (a -> Boolean) -> Boolean
def List.forallIn l p =
    foldl (&&) true (map p l)
%
op List.forallIn_do : [a,b] List a -> (a->b) -> List b
def [a,b] List.forallIn_do l f =
    map f l
%
%some occurrence of x1 in the list is followed by some occurrence of x2
op List.prec? : [a] List a -> a -> a -> Boolean
def [a] List.prec? xs x1 x2  =
    case xs of
    | [] -> false
    | (x1::rest) -> in? %member
                     (x2, rest)
    | (x::rest) -> (List.prec? rest x1 x2)

endspec
