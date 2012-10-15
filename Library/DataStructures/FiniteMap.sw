(*
                    Specification of Finite Maps

    empty_map and update could be constructors,
    but we want implementations that do destructive update
    to keep the size linear in the domain.
*)

spec
  import Sets
  type Map(a,b)

  % a map from a to b yields, when applied to an element of type a,
  % an element of type b if defined on it, otherwise no element:
  % this is modeled by means of the Option polymorphic type

  % if two maps return the same result on each element of type a,
  % they are the same map

  op [a,b] apply : Map(a,b) -> a -> Option b
  axiom map_equality is [a,b]
        fa(m1: Map(a,b), m2: Map(a,b)) (fa(x) apply m1 x = apply m2 x) => m1 = m2

  % the empty map is undefined over all elements of type a

  op [a,b] empty_map :  Map(a,b)
  axiom empty_map is [a, b]
        fa(x: a) apply empty_map x = (None: Option b)

  % update is used to define the map to return a certain element of
  % type b when applied over a certain element of type a; if the map
  % was undefined on that element of type a, now it is defined; if
  % instead it was already defined, the previous element of type b
  % is "overwritten"

  op [a,b] update : Map(a,b) -> a -> b -> Map(a,b)
  axiom update is
        fa(m,x,y,z) apply (update m x y) z =
                    (if z = x then Some y else apply m z)

  % this induction axiom constrains maps to be finite: any finite map can be
  % obtained by suitable successive applications of update to empty_map

  axiom map_induction is [a,b]
        fa (p : Map(a,b) -> Boolean)
           p empty_map &
           (fa(m,x,y) p m => p (update m x y)) =>
           (fa(m) p m)

  % we could define several other operations on maps (e.g., "undefinition"
  % of elements, homomorphic application of a function) but the above
  % operations are sufficient for this example

  op [a,b] domain: Map(a,b) -> Set a
  axiom map_domain is
     [a,b] fa(m:Map(a,b), x:a)( (x in? domain(m)) = (ex(z:b)(apply m x = Some z)))

  op [a,b] range : Map(a,b) -> Set b
  axiom map_range is
     [a,b] fa(m:Map(a,b), z:b)( z in? range(m) = (ex(x:a)(apply m x = Some z)))

  def [a,b] total? (s:Set(a), m:Map(a,b)):Boolean =
    fa(x:a) (x in? s => (ex(z:b) apply m x = Some z))

%  type TotalMap(a, b) = (Set(a) * Map(a,b) | total?)

  def [a,b] TMApply(m:Map(a,b),x:a | x in? domain(m)): b =
    the(z:b)( apply m x = Some z)

  axiom totalmap_equality is [a,b]
        fa(m1:Map(a,b),m2:Map(a,b)) (fa(x) TMApply(m1,x) = TMApply(m2,x)) => m1 = m2

end-spec
