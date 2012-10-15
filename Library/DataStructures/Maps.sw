% TODO can we replace this with something in Library/Structures/Data/Maps?  Maybe Simple.sw?

(*
                    Specification of Finite Maps

    empty_map and update could be constructors,
    but we want implementations that do destructive update
    to keep the size linear in the domain.
*)

Maps = Map qualifying spec
  import Sets
  type Map(a,b)

  % a map from a to b yields, when applied to an element of type a,
  % an element of type b if defined on it, otherwise no element:
  % this is modeled by means of the Option polymorphic type

  % if two maps return the same result on each element of type a,
  % they are the same map

  op [a,b] apply : Map(a,b) -> a -> Option b
  axiom map_equality is [a,b]
        fa(m1: Map(a,b),m2) (fa(x) apply m1 x = apply m2 x) => m1 = m2

  % the empty map is undefined over all elements of type a

  op [a,b] empty_map :  Map(a,b)
  axiom empty_map is [a,b]
        fa(x) apply (empty_map: Map(a,b)) x = None

 % TODO map_apply is not a good name for this (maybe apply_present or apply_default?)
 % TODO just make this a definition?
  op [a,b] map_apply (m: Map(a,b))(null_elt:b)(x: a): b
  axiom map_apply_def is [a,b]
    fa(m: Map(a,b),x:a,null_elt:b, y:b,z:b)
      (map_apply m null_elt x = z
       =>
       (case apply m x of
           | Some y -> z=y
           | None   -> z=null_elt))


  % update is used to define the map to return a certain element of
  % type b when applied over a certain element of type a; if the map
  % was undefined on that element of type a, now it is defined; if
  % instead it was already defined, the previous element of type b
  % is "overwritten"

  op [a,b] update : Map(a,b) -> a -> b -> Map(a,b)
  axiom update is
        fa(m,x,y,z) apply (update m x y) z =
                    (if z = x then Some y else apply m z)

%  who added this? %TODO add axiom for this
  op remove : [a,b] Map (a,b) -> a -> Map (a,b)

%TODO why not use the def?
  op [a,b] singletonMap : a -> b -> Map(a,b)
%  def [a,b] singletonMap x y = (update (empty_map) x y)
  axiom def_of_singletonMap is
        fa(x,y) (singletonMap x y) = (update empty_map x y)

  % this induction axiom constrains maps to be finite: any finite map can be
  % obtained by suitable successive applications of update to empty_map

  axiom map_induction is [a,b]
        fa (p : Map(a,b) -> Boolean)
           p empty_map &
           (fa(m,x,y) p m => p (update m x y)) =>
           (fa(m) p m)

 %TODO delete this comment?
  % we could define several other operations on maps (e.g., "undefinition"
  % of elements (TODO done above as remove), homomorphic application of a function) but the above
  % operations are sufficient for this example

% TODO could use a definedOn? helper predicate
  op [a,b] domain: Map(a,b) -> Set a
  axiom map_domain is
     [a,b] fa(m:Map(a,b), x:a)( (x in? domain(m)) = (ex(z:b)(apply m x = Some z)))

  op [a,b] range : Map(a,b) -> Set b
  axiom map_range is
     [a,b] fa(m:Map(a,b), z:b)( z in? range(m) = (ex(x:a)(apply m x = Some z)))

% TODO could use a definedOn? helper predicate
  op [a,b] total? (s:Set(a), m:Map(a,b)):Boolean =
    fa(x:a) (x in? s => (ex(z:b) apply m x = Some z))

%TODO I guess we don't say how the elements in the list are sorted.
%just call domain and a generic setToList function?
  op [a,b] domainToList: Map(a,b) -> List a
  axiom map_domainToList is
     [a,b] fa(m:Map(a,b)) size(domain m) = length(domainToList m)
                     && (fa(x) (x in? domain(m)) = (x in? domainToList m))

%TODO constrain the length of rangeToList?  otherwise, this allows duplicates
  op [a,b] rangeToList: Map(a,b) -> List b
  axiom map_rangeToList is
     [a,b] fa(m:Map(a,b), z:b) (z in? range(m)) = (z in? rangeToList m)

% who added this?
  op [a,b] size: Map(a,b) -> Nat
  axiom map_size is
     [a,b] fa(m:Map(a,b)) size m = size(domain m)

%  type TotalMap(a, b) = (Set(a) * Map(a,b) | total?)

  % Strips off the Some constructor.  Only works if the key is known to be in the domain of the map.
  op [a,b] TMApply(m:Map(a,b),x:a | x in? domain(m)): b =
    the(z:b)( apply m x = Some z)

 %TODO doesn't seem to type check (what if x is not in the domain of m1 and/or m2?)
  axiom totalmap_equality is [a,b]
        fa(m1: Map(a,b),m2) (fa(x) TMApply(m1,x) = TMApply(m2,x)) => m1 = m2

 %TODO doesn't seem to type check in the else branch
  theorem TMApply_over_update is [a,b]
    fa(m: Map(a,b), x: a, y: b, z: a)
    TMApply(update m x y, z) = (if x = z then y else TMApply(m, z))

%TODO these next theorems don't have much to do with the Map data structure:

 %TODO needs to assert that f is a bijection
 theorem map_map_inv is [a,b]
   fa(f: a -> b, f': b -> a, l: List b)
   inverse f = f' => map f (map f' l) = l
 
  theorem map_doubleton is [a,b]
    fa(f: a -> b,x:a,y:a) map f [x,y] = [f x,f y]

  theorem map_empty is [a,b]
    fa(f: a -> b) map f [] = []

 %TODO could also phrase in terms of insert and then prove that insert is either a no-op or insert_new
  theorem domain_update is [a,key]
    fa(m: Map(key,a), x: key, y: a)
      domain(update m x y) 
       = (if x in? domain m 
            then domain m 
          else set_insert_new(x, domain m))

% who added this?
%TODO This may need commutativity and idempotence restrictions, like those for set_fold?
  op foldi : [Dom,Cod,a] (Dom * Cod * a -> a) -> a -> Map (Dom,Cod) -> a


(******************************** The Proofs ********************************)

proof isa Map__TMApply_Obligation_the
  sorry
end-proof

proof isa Map__totalmap_equality_Obligation_subtype
  sorry
end-proof

proof isa Map__totalmap_equality_Obligation_subtype0
  sorry
end-proof

proof isa Map__TMApply_over_update_Obligation_subtype
  sorry
end-proof

proof isa Map__TMApply_over_update_Obligation_subtype0
  sorry
end-proof

proof isa Map__TMApply_over_update
  sorry
end-proof

proof isa Map__map_map_inv_Obligation_subtype
  sorry
end-proof

proof isa Map__map_map_inv
  sorry
end-proof

proof isa Map__domain_update
  sorry
end-proof


end-spec






Maps_extended = spec
  import Maps

  %% for some reason the version of this in Maps is not seen by Globalize
  theorem TMApply_over_update_2 is [a,b]
    fa(m: Map(a,b), x: a, y: b, z: a)
    %% theorems with this form induce setf generation in Globalize
    TMApply(update m x y, z) = (if x = z then y else TMApply(m, z))

  op [a,b] mapFrom(s: Set a, f: a -> b): Map(a,b) =
    set_fold empty_map (fn (m, x) -> update m x (f x)) s

%% This causes a name clash with the Isabelle translation of the definition of mapFrom.
%% %% not quite right
%%   axiom mapFrom_def is [a,b]
%%     fa(x:a, y: b, s: Set a, f: a -> b) 
%%       y = TMApply(mapFrom(s,f), x) <=> x in? s && y = f x

  %% Really needs a totality condition: x in s
  theorem mapFrom_TMApply is [a,b]
    fa(x:a, y: b, s: Set a, f: a -> b)
      TMApply(mapFrom(s,f), x) = f x

  theorem mapFrom_if_shadow is [a,b]
    fa(x:a, y: b, s: Set a, p: a -> Boolean, f: a -> b, g: a -> b)
      mapFrom(s,fn x:a -> if p x then f x else g x)
        = mapUpdateSet(mapFrom(s,g), filter p s, f)

  theorem mapFrom_identity is [a,b]
   fa(m: Map(a,b),dom: Set a) 
     domain(m) = dom => mapFrom(dom, (fn x -> TMApply(m,x))) = m

  theorem domain_of_mapFrom is [a,b]
   fa(dom: Set a, g: a -> b) 
     domain(mapFrom(dom, g)) = dom

  op [a,b,c] update_map_prepend(m:Map(a*b,c),lst:Set a,bval:b, f:a*b->c):Map(a*b,c) =
     set_fold m (fn (m1, aval) -> update m1 (aval,bval) (f(aval,bval))) lst

  op [a,b,c] map2DFrom(lst1: Set a, lst2: Set b, f: a*b -> c): Map(a*b,c) =
    set_fold empty_map (fn (m, bval) -> update_map_prepend(m,lst1,bval,f)) lst2
  
  op [a,b] mapUpdateSet(m: Map(a,b), s: Set a, f: a -> b): Map(a,b) =
     set_fold m (fn  (m, x) -> update m x (f x)) s

(*--------  Special ops and axioms for isomorphism between Map(a,b)* Map(a,c) and Map(a,b*c) ---*)

  def [A,B,C] map_compose(m1:Map(A,B), m2:Map(A,C)| domain(m1)=domain(m2)): Map(A,B*C) =
    mapFrom( domain(m1), (fn(domelt:A)-> (TMApply(m1,domelt),TMApply(m2,domelt))))

  def [A,B,C] map_project1(m:Map(A,B*C)): Map(A,B) =
    mapFrom( domain(m), fn(domelt:A)-> (TMApply(m,domelt)).1)

  def [A,B,C] map_project2(m:Map(A,B*C)): Map(A,C) =
    mapFrom( (domain m), fn(domelt:A)-> (TMApply(m,domelt)).2)

  theorem TMApply_map_project1 is [A,B,C]
     fa(m:Map(A,B*C),a:A)( TMApply(map_project1(m),a) = (TMApply(m,a)).1 )

  theorem TMApply_map_project2 is [A,B,C]
     fa(m:Map(A,B*C),a:A)( TMApply(map_project2(m),a) = (TMApply(m,a)).2 )

  theorem update_map_project1 is [A,B,C]
     fa(m:Map(A,B*C),a:A,b:B)
       (  map_compose((update (map_project1 m) a b),
                      (map_project2 m))
        = (update m a (b,(TMApply(m,a)).2)) )

  theorem update_map_project2 is [A,B,C]
     fa(m:Map(A,B*C),a:A,c:C)
       (  map_compose((map_project1 m),
                      (update (map_project2 m) a c))
        = (update m a ((TMApply(m,a)).1,c)) )

  theorem combine_map_project1_map_project2 is [A,B,C]
     fa(m:Map(A,B*C),m1:Map(A,B),m2:Map(A,C))
       (  ((map_project1 m) = m1 && (map_project2 m) = m2)
        = (m = map_compose(m1,m2))
       )

  theorem combine_map_project1_map_project2_cond is [A,B,C]
     fa(m:Map(A,B*C),m1:Map(A,B),m2:Map(A,C))
       (  ((map_project1 m) = m1) =>
          (((map_project2 m) = m2) = (m = map_compose(m1,m2)))
       )

  theorem combine_map_project1_map_project2_simplify is [A,B,C]
     fa(m:Map(A,B*C),m1:Map(A,B),m2:Map(A,C))
       (m = map_compose(m1,m2)) => ((map_project1 m) = m1) = true


  theorem combine_of_map_projections is [A,B,C]
     fa(m:Map(A,B*C)) map_compose((map_project1 m), (map_project2 m)) = m 

%----------------- 3-tuple version -----------------------------------------

  def [A,B,C,D] map_compose3(m1:Map(A,B), m2:Map(A,C), m3:Map(A,D)
                             | domain(m1)=domain(m2) && domain(m1)=domain(m3)): Map(A,B*C*D) =
    mapFrom( domain(m1), (fn(domelt:A)-> (TMApply(m1,domelt),TMApply(m2,domelt),TMApply(m3,domelt))))

  def [A,B,C,D] map_project31(m:Map(A,B*C*D)): Map(A,B) =
    mapFrom( domain(m), fn(domelt:A)-> (TMApply(m,domelt)).1)

  def [A,B,C,D] map_project32(m:Map(A,B*C*D)): Map(A,C) =
    mapFrom( (domain m), fn(domelt:A)-> (TMApply(m,domelt)).2)

  def [A,B,C,D] map_project33(m:Map(A,B*C*D)): Map(A,D) =
    mapFrom( (domain m), fn(domelt:A)-> (TMApply(m,domelt)).3)

  theorem TMApply_map_project31 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A)( TMApply(map_project31(m),a) = (TMApply(m,a)).1 )

  theorem TMApply_map_project32 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A)( TMApply(map_project32(m),a) = (TMApply(m,a)).2 )

  theorem TMApply_map_project33 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A)( TMApply(map_project33(m),a) = (TMApply(m,a)).3 )

% this forms a triple unnecessarily - how to update a triple in the range of a map?
  theorem update_map_project31 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A,b:B)
       (  map_compose3((update (map_project31 m) a b),
                      (map_project32 m),(map_project33 m))
        = (update m a (b,(TMApply(m,a)).2,(TMApply(m,a)).3)) )

  theorem update_map_project32 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A,c:C)
       (  map_compose3((map_project31 m),
                       (update (map_project32 m) a c),
                       (map_project33 m))
        = (update m a ((TMApply(m,a)).1,c,(TMApply(m,a)).3)) )

  theorem update_map_project33 is [A,B,C,D]
     fa(m:Map(A,B*C*D),a:A,d:D)
       (  map_compose3((map_project31 m),
                       (map_project32 m),
                       (update (map_project33 m) a d))
        = (update m a ((TMApply(m,a)).1,(TMApply(m,a)).2,d)) )

%  theorem combine_map_project3 is [A,B,C,D]
%     fa(m:Map(A,B*C*D),m1:Map(A,B),m2:Map(A,C),m3:Map(A,D))
%       (  ((map_project31 m) = m1 
%             && (map_project32 m) = m2
%             && (map_project33 m) = m3)
%        = (m = map_compose3(m1,m2,m3))
%       )

  theorem combine_map_project3 is [A,B,C,D]
     fa(m:Map(A,B*C*D),m1:Map(A,B),m2:Map(A,C),m3:Map(A,D))
       map_compose3((map_project31 m),(map_project32 m),(map_project33 m)) = m 

%  theorem combine_map_project31_map_project32_cond is [A,B,C,D]
%     fa(m:Map(A,B*C*D),m1:Map(A,B),m2:Map(A,C),m3:Map(A,D))
%       (  ((map_project31 m) = m1) =>
%          (((map_project32 m) = m2) = (m = map_compose(m1,m2)))
%       )

  theorem map_compose3_project31_simplify is [A,B,C,D]
     fa(m:Map(A,B*C*D),m1:Map(A,B),m2:Map(A,C),m3:Map(A,D))
       (m = map_compose3(m1,m2,m3)) => ((map_project31 m) = m1) = true
  theorem map_compose3_project32_simplify is [A,B,C,D]
     fa(m:Map(A,B*C*D),m1:Map(A,B),m2:Map(A,C),m3:Map(A,D))
       (m = map_compose3(m1,m2,m3)) => ((map_project32 m) = m2) = true
  theorem map_compose3_project33_simplify is [A,B,C,D]
     fa(m:Map(A,B*C*D),m1:Map(A,B),m2:Map(A,C),m3:Map(A,D))
       (m = map_compose3(m1,m2,m3)) => ((map_project33 m) = m3) = true

  theorem combine_of_map_projections3 is [A,B,C,D]
     fa(m:Map(A,B*C*D)) map_compose3((map_project31 m), (map_project32 m),(map_project33 m)) = m 


(******************************** The Proofs ********************************)

proof isa mapFrom_Obligation_subtype
  sorry
end-proof

proof isa mapFrom_TMApply_Obligation_subtype
  sorry
end-proof

proof isa mapFrom_TMApply
  sorry
end-proof

proof isa mapUpdateSet_Obligation_subtype
  sorry
end-proof

proof isa mapFrom_if_shadow
  sorry
end-proof

proof isa mapFrom_identity_Obligation_subtype
  sorry
end-proof

proof isa mapFrom_identity
  sorry
end-proof

proof isa domain_of_mapFrom
  sorry
end-proof

proof isa update_map_prepend_Obligation_subtype
  sorry
end-proof

proof isa map2DFrom_Obligation_subtype
  sorry
end-proof

proof isa map_compose_Obligation_subtype
  sorry
end-proof

proof isa map_compose_Obligation_subtype0
  sorry
end-proof

proof isa map_project1_Obligation_subtype
  sorry
end-proof

proof isa map_project2_Obligation_subtype
  sorry
end-proof

proof isa TMApply_map_project1_Obligation_subtype
  sorry
end-proof

proof isa TMApply_map_project1_Obligation_subtype0
  sorry
end-proof

proof isa TMApply_map_project1
  sorry
end-proof

proof isa TMApply_map_project2_Obligation_subtype
  sorry
end-proof

proof isa TMApply_map_project2_Obligation_subtype0
  sorry
end-proof

proof isa TMApply_map_project2
  sorry
end-proof

proof isa update_map_project1_Obligation_subtype
  sorry
end-proof

proof isa update_map_project1_Obligation_subtype0
  sorry
end-proof

proof isa update_map_project1
  sorry
end-proof

proof isa update_map_project2_Obligation_subtype
  sorry
end-proof

proof isa update_map_project2_Obligation_subtype0
  sorry
end-proof

proof isa update_map_project2
  sorry
end-proof

proof isa combine_map_project1_map_project2_Obligation_subtype
  sorry
end-proof

proof isa combine_map_project1_map_project2
  sorry
end-proof

proof isa combine_map_project1_map_project2_cond_Obligation_subtype
  sorry
end-proof

proof isa combine_map_project1_map_project2_cond
  sorry
end-proof

proof isa combine_map_project1_map_project2_simplify_Obligation_subtype
  sorry
end-proof

proof isa combine_map_project1_map_project2_simplify
  sorry
end-proof

proof isa combine_of_map_projections_Obligation_subtype
  sorry
end-proof

proof isa combine_of_map_projections
  sorry
end-proof


proof isa map_compose3_Obligation_subtype
  sorry
end-proof

proof isa map_compose3_Obligation_subtype0
  sorry
end-proof

proof isa map_compose3_Obligation_subtype1
  sorry
end-proof

proof isa map_project31_Obligation_subtype
  sorry
end-proof

proof isa map_project32_Obligation_subtype
  sorry
end-proof

proof isa map_project33_Obligation_subtype
  sorry
end-proof

proof isa TMApply_map_project31_Obligation_subtype
  sorry
end-proof

proof isa TMApply_map_project31_Obligation_subtype0
  sorry
end-proof

proof isa TMApply_map_project31
  sorry
end-proof

proof isa TMApply_map_project32_Obligation_subtype
  sorry
end-proof

proof isa TMApply_map_project32_Obligation_subtype0
  sorry
end-proof

proof isa TMApply_map_project32
  sorry
end-proof

proof isa TMApply_map_project33_Obligation_subtype
  sorry
end-proof

proof isa TMApply_map_project33_Obligation_subtype0
  sorry
end-proof

proof isa TMApply_map_project33
  sorry
end-proof

proof isa update_map_project31_Obligation_subtype
  sorry
end-proof

proof isa update_map_project31_Obligation_subtype0
  sorry
end-proof

proof isa update_map_project31_Obligation_subtype1
  sorry
end-proof

proof isa update_map_project31
  sorry
end-proof

proof isa update_map_project32_Obligation_subtype
  sorry
end-proof

proof isa update_map_project32_Obligation_subtype0
  sorry
end-proof

proof isa update_map_project32_Obligation_subtype1
  sorry
end-proof

proof isa update_map_project32
  sorry
end-proof

proof isa update_map_project33_Obligation_subtype
  sorry
end-proof

proof isa update_map_project33_Obligation_subtype0
  sorry
end-proof

proof isa update_map_project33_Obligation_subtype1
  sorry
end-proof

proof isa update_map_project33
  sorry
end-proof

proof isa combine_map_project3_Obligation_subtype
  sorry
end-proof

proof isa combine_map_project3
  sorry
end-proof

proof isa map_compose3_project31_simplify_Obligation_subtype
  sorry
end-proof

proof isa map_compose3_project31_simplify
  sorry
end-proof

proof isa map_compose3_project32_simplify_Obligation_subtype
  sorry
end-proof

proof isa map_compose3_project32_simplify
  sorry
end-proof

proof isa map_compose3_project33_simplify_Obligation_subtype
  sorry
end-proof

proof isa map_compose3_project33_simplify
  sorry
end-proof

proof isa combine_of_map_projections3_Obligation_subtype
  sorry
end-proof

proof isa combine_of_map_projections3
  sorry
end-proof

proof isa TMApply_over_update_2_Obligation_subtype
  apply(cut_tac Map__TMApply_over_update_Obligation_subtype)
  apply(auto)
end-proof

proof isa TMApply_over_update_2_Obligation_subtype0
  apply(cut_tac Map__TMApply_over_update_Obligation_subtype0)
  apply(auto)
end-proof

proof isa TMApply_over_update_2
  apply(cut_tac Map__TMApply_over_update)
  apply(auto)
end-proof




end-spec
