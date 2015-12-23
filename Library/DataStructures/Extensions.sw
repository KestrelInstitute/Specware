(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

% Status: I changed some things in this file to get it to proc.  Not
% sure if it is correct or needed.  -Eric, 10/11/12

%TODO combine some ops and defs in this file into ops.

%---- Functions missing from existing library datatypes ---------
Map qualifying
spec
import Maps


%----- set stuff ------
op [a] list2set (lst : List a) : Set a = foldl (fn (set, elem) -> set_insert(elem, set)) empty_set lst

% Cons is now a constructor.

% %NOTE: cons doesn't satisfy the axioms for using set_fold.  It seems that it
% doesn't make sense to just convert a set to a list, because the result is not
% unique (we'd like to maybe return a sorted list, but the type of the set
% elements may not support an ordering).
% def [a] set2list: Set a -> List a = set_fold [] Cons

%completely bad implementation of size
%op size : [a] Set a -> Nat 
%def size(s) = length (set2list s)

%TODO do we still need this?
(*
  why do you need it to be 1-1?
  op [a,b] set_map : ((a -> b) | 1-1?) -> Set a -> Set b
  op [a,b] 1-1? : (a -> b) -> Bool

  axiom set_map is
        (fa(f,x,s) x in? s => (ex(y) (y in? set_map(f,s) && y = f(x)))) &&
        (fa(f,y,s) y in? set_map(f,s) => (ex(x) (x in? s && y = f(x))))
*)

% This was a conflict.  -Eric
% %Another awful hack
% op [a,b] Set.map : (a->b) -> Set a -> Set b
% def [a,b] Set.map f s =
%     list2set (map f (set2list s))
    
op flatten : [a] Set (Set a) -> Set a
%TODO interesting that there are no formals given here.  Maybe this is a use case for using def insted of op?  Or can we do the same with op?
def flatten = set_fold empty_set (Set.\/)

%% %TODO does not seem well-defined; in what order do the lists get appended?  See the restrictions on set_fold. 
%% op SoL.flatten : [a] Set (List a) -> List a
%% def SoL.flatten = set_fold [] (++)

%% %Convert a finite map to a function.
%% %TODO Not sure this is well-defined; what should it do on keys that are not given values by the map?
%% %We could instead have this return a function from a to Option b.
%% op fm2fn : [a,b] Map(a,b) -> (a -> b)
%% def fm2fn(fm) = (fn(x) -> TMApply(fm, x))

%% %TODO Perhaps when a>b, this should return the empty list?
%% %TODO compare to upto in StructuredTypes.sw.
%% op numRange : Nat * Nat -> List Nat
%% def numRange(a:Nat, b:Nat) =
%%     if (a>=b) then [a] else Cons(a, numRange(a+1, b))

%% %TODO see op forall? in Library/Base/List
%% op List.forallIn : [a] List a -> (a -> Bool) -> Bool
%% def List.forallIn l p =
%%     foldl (&&) true (map p l)

%% %TODO just use map and deprecate this?
%% op List.forallIn_do : [a,b] List a -> (a->b) -> List b
%% def [a,b] List.forallIn_do l f =
%%     map f l

%some occurrence of x1 in the list is followed by some occurrence of x2
op [a] List.prec? (xs:List a) (x1:a) (x2:a) : Bool =
    case xs of
    | [] -> false
    | (hd::rest) -> (if hd = x1 then
                       in? (x2, rest)
                     else
                       List.prec? rest x1 x2)

proof Isa flatten_Obligation_subtype
  by (metis Set__e_bsl_bsl_fsl_fsl_Obligation_subtype)
end-proof

%% proof Isa SoL__flatten_Obligation_subtype
%%   sorry
%% end-proof

%% proof Isa fm2fn_Obligation_subtype
%%   sorry
%% end-proof

end-spec
