Relation qualifying spec

import Set

% relations as sets of pairs:

type Relation(a,b) = Set (a * b)

% domain and range:

op [a,b] domain (r: Relation(a,b)) : Set a = fn x:a -> (ex(y:b) r(x,y))

proof Isa domain__def
  by (simp add: Domain_def)
end-proof

op [a,b] range (r: Relation(a,b)) : Set b = fn y:b -> (ex(x:a) r(x,y))

proof Isa range__def
  by (simp add: Range_def Domain_def converse_def)
end-proof

% range/domain values related to domain/range value (set):

op [a,b] apply (r: Relation(a,b)) (x:a) : Set b = fn y:b -> r(x,y)

op [a,b] applyi (r: Relation(a,b)) (y:b) : Set a = fn x:a -> r(x,y)

op [a,b] applys (r: Relation(a,b)) (xS: Set a) : Set b =
  fn y:b -> (ex(x:a) x in? xS && r(x,y))

proof Isa applys__def
  by (simp add: Image_def Bex_def)
end-proof

op [a,b] applyis (r: Relation(a,b)) (yS: Set b) : Set a =
  fn x:a -> (ex(y:b) y in? yS && r(x,y))

% forward and backward composition:

op [a,b,c] :> (r1: Relation(a,b), r2: Relation(b,c)) infixl 24
              : Relation(a,c) = fn (x:a,z:c) -> (ex(y:b) r1(x,y) && r2(y,z))

op [a,b,c] o (r1: Relation(b,c), r2: Relation(a,b)) infixl 24
             : Relation(a,c) = r2 :> r1
proof Isa -> o_R end-proof
% proof Isa [simp] end-proof

% inverse:

op [a,b] inverse (r: Relation(a,b)) : Relation(b,a) = fn (y,x) -> r(x,y)

proof Isa inverse__def
  by (simp add: converse_def)
end-proof

% remove pairs whose domain/range value is not in argument set:

op [a,b] restrictDomain (r: Relation(a,b), xS: Set a) infixl 25
                        : Relation(a,b) = fn (x,y) -> r(x,y) && x in? xS

op [a,b] restrictRange (r: Relation(a,b), yS: Set b) infixl 25
                       : Relation(a,b) = fn (x,y) -> r(x,y) && y in? yS

% some range value for every domain value:

op [a,b] total? (r: Relation(a,b)) : Bool = (domain r = full)

type TotalRelation(a,b) = (Relation(a,b) | total?)

% some domain value for every range value:

op [a,b] surjective? (r: Relation(a,b)) : Bool = (range r = full)

type SurjectiveRelation(a,b) = (Relation(a,b) | surjective?)

% at most one range value for every domain value:

op [a,b] functional? (r: Relation(a,b)) : Bool =
  fa(x) (single? \/ empty?) (apply r x)

type Map(a,b) = (Relation(a,b) | functional?)

% at most one domain value for every range value:

op [a,b] injective? (r: Relation(a,b)) : Bool =
  fa(y) (single? \/ empty?) (applyi r y)

type InjectiveRelation(a,b) = (Relation(a,b) | injective?)

% exactly one range/domain value for each domain/range value:

op [a,b] bijective? : Relation(a,b) -> Bool =
  total? /\ surjective? /\ functional? /\ injective?

type BijectiveRelation(a,b) = (Relation(a,b) | bijective?)

% relative totality, surjectivity, and bijectivity:

op [a,b] totalOn? (s:Set a) (r:Relation(a,b)) : Bool =
  domain r = s

op [a,b] surjectiveOn? (s:Set b) (r:Relation(a,b)) : Bool =
  range r = s

op [a,b] bijectiveOn? (s:Set a) (s':Set b) : Relation(a,b) -> Bool =
  totalOn? s /\ surjectiveOn? s' /\ functional? /\ injective?

% cardinalities:

type      FiniteRelation(a,b) = (Relation(a,b) | finite?)
type    InfiniteRelation(a,b) = (Relation(a,b) | infinite?)
type   CountableRelation(a,b) = (Relation(a,b) | countable?)
type UncountableRelation(a,b) = (Relation(a,b) | uncountable?)

proof Isa Thy_Morphism 
  Relation.domain -> Domain 
  Relation.range  -> Range
  Relation.applys -> Image
  Relation.:> -> O Left 24
  Relation.inverse -> converse
%%  Relation.apply -> 
%%  Relation.applyi -> 
%%  Relation.applyis -> 
%%  Relation.o ->  
%%  Relation.restrictDomain -> 
%%  Relation.restrictRange -> 
%%  Relation.total? -> 
%%  Relation.surjective? -> 
%%  Relation.functional? -> 
%%  Relation.injective? -> 
%%  Relation.bijective? -> 
%%  Relation.totalOn? -> 
%%  Relation.surjectiveOn? -> 
%%  Relation.bijectiveOn? -> 
end-proof

endspec
