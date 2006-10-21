% This file contains an axiomatic semantics for the OWL (Full)
% Semantic Web Ontology Language, with test cases that serve to validate
% the axioms.  All the theorems have been proved. (as of 10/11/2006).


% The OWL theory is written in Kestrel's Specware language.  In Specware,
% theories are called "specs".  Conjectures are translated into the language
% of SRI's SNARK theorem prover and then are proved by SNARK.  Each
% conjecture is proved in the subtheory consisting of previous axioms and
% (proved or unproved) conjectures.

% changes made to use specware/snark interface 1/19/2005
% the new translation uses predicate symbols rather than snark sorts to 
% represent specware types.

% Type "prwb nil" before running Specware


% The theory is composed of nested subtheories.  The most central
% primitive subtheory is owl_core.  

owl_core = spec

  sort Individual 

%  The relation Class? characterizes those individuals that are 
%  classes.

  op Class? : Individual -> Boolean

% Classes provide an abstraction mechanism for grouping resources with
% similar characteristics. Like RDF classes, every OWL class is
% associated with a set of individuals, called the class extension. The
% individuals in the class extension are called the instances of the
% class.

%  The sort Class consists of those individuals that are classes.
%  Hence all classes are individuals, an Owl Full assumption.

  sort Class = {x : Individual | Class? x}

%  We introduce relations for Type and SubClass: 

  op Type : Individual * Class -> Boolean

% The rdfs:subClassOf construct is defined as part of RDF Schema [RDF
% Schema]. Its meaning in OWL is exactly the same: if the class
% description C1 is defined as a subclass of class description C2, than
% the set of individuals in the class extension of C1 should be a subset
% of the set of individuals in the class extension of C2. A class is by
% definition a subclass of itself (as the subset may be the complete
% set).

  op SubClass : Class * Class -> Boolean

% In Owl, every relation corresponds to a Property.

  op Property? : Individual -> Boolean

% The Specware sort Property corresponds to the OWL Class Property.
  
  sort Property = {x : Individual | Property? x}

  op Property : Class

  axiom Sort_Properties_are_Properties is
   fa(P : Property)Type(P, Property)

% The properties corresponding to Type and SubClass are
% typeOf and subClassOf respectively.

  op typeOf : Property

  op subClassOf : Property


% The relationship between a relation and its 
% corresponding property is defined in terms of the Holds relation.

  op Holds : Property * Individual * Individual -> Boolean

  axiom SubClass_relation_vs_property is
    fa(c1 : Class, c2 : Class)
     SubClass(c1, c2) <=> Holds(subClassOf, c1, c2)

  axiom definition_SubClass_implies is
    fa(c1 : Class, c2 : Class)
     SubClass(c1, c2) =>
     (fa(x : Individual)
      Type(x, c1) => Type(x, c2))

  axiom reflexivity_of_SubClass is
    fa(c : Class)
     SubClass(c, c)

% Two OWL class identifiers are predefined, namely the classes owl:Thing
% and owl:Nothing. The class extension of owl:Thing is the set of all
% individuals. The class extension of owl:Nothing is the empty
% set. Consequently, every OWL class is a subclass of owl:Thing and
% owl:Nothing is a subclass of every class (for the meaning of the
% subclass relation, see the section on rdfs:subClassOf).  

% <These are not actually consequences but are included as axioms.
% Presumably the extensions of two classes can be subsets even though
% the classes are not subclasses.--RW>

  op Thing : Class

  axiom Type_of_Thing is
    fa(x : Individual)
      Type(x, Thing)

  axiom SubClass_of_Thing is
    fa(c : Class)
      SubClass(c, Thing)    

  op Nothing : Class 

  axiom Nothing_is_a_Class is
    Class?(Nothing)

  axiom Type_of_Nothing is
    fa(x : Individual)
      ~(Type(x, Nothing))

  axiom Nothing_is_SubClass is
    fa(C : Class)
      SubClass(Nothing, C)    


% The built-in OWL property owl:sameAs links an individual to an
% individual. Such an owl:sameAs statement indicates that two URI
% references actually refer to the same thing: the individuals have the
% same "identity".

op sameAs : Individual * Individual -> Boolean 

   axiom definition_sameAs is
    fa(x : Individual, y : Individual)
     sameAs(x, y) <=> x=y

   conjecture theorem_reflexivity_of_sameAs is
    fa(x : Individual)
     sameAs(x, x)
    
  
% The built-in OWL owl:differentFrom property links an individual to an
% individual. An owl:differentFrom statement indicates that two URI
% references refer to different individuals.


op differentFrom : Individual * Individual -> Boolean 
  
   axiom definition_differentFrom is
    fa(x : Individual, y : Individual)
     differentFrom(x, y) <=> ~(x=y)

% 5.2.3 owl:AllDifferent

% For ontologies in which the unique-names assumption holds, the use of
% owl:differentFrom is likely to lead to a large number of statements,
% as all individuals have to be declared pairwise disjoint. For such
% situations OWL provides a special idiom in the form of the construct
% owl:AllDifferent. owl:AllDifferent is a special built-in OWL class,
% for which the property owl:distinctMembers is defined, which links an
% instance of owl:AllDifferent to a list of individuals. The intended
% meaning of such a statement is that all individuals in the list are
% all different from each other.

% Because Specware does not allow functions of variable arity, we
% introduce AllDifferent on Lists of Individuals

sort List

op nil : List

op cons : Individual * List -> List

op first : List -> Individual

op rest : List -> List

axiom first_of_cons is
   fa(x : Individual, l : List)
    first(cons(x, l)) = x

axiom rest_of_cons is
   fa(x : Individual, l : List)
    rest(cons(x, l)) = l

op AllDifferent2 : Individual * List -> Boolean
% AllDifferent2(x, t) means x is distinct from the elements of t.

axiom AllDifferent2_nil is
   fa(x : Individual)
    AllDifferent2(x, nil)

axiom AllDifferent2_cons is
   fa(x : Individual, y: Individual, l : List)
    AllDifferent2(x, cons(y, l)) <=>
    ~(x = y) & AllDifferent2(x, l)

op AllDifferent : List -> Boolean

% AllDifferent(t) means the elements of t are distinct

axiom AllDifferent_nil is
  AllDifferent(nil)

axiom AllDifferent_cons is
   fa(x : Individual, l : List)
     AllDifferent(cons(x, l)) <=>
     AllDifferent2(x, l) & AllDifferent(l)

%  Suggested by SNARK 7/04
conjecture theorem_not_AllDifferent_cons_xx is
   fa(x : Individual, l : List)
    ~(AllDifferent(cons(x, cons(x, l))))

op addOne : Individual * Class -> Class

   axiom addOne_of_type is
    fa(x : Individual, y : Individual, C : Class) 
     Type(x, addOne(y, C)) <=> 
     (sameAs(x, y) or Type(x, C))

   conjecture theorem_type_identity is
    fa(x : Individual, C : Class)
     Type(x, addOne(x, C))


   conjecture theorem_singleton is
    fa(x : Individual, y : Individual)
     Type(x, addOne(y, Nothing)) => sameAs(x, y)
     
% A class axiom may contain (multiple) owl:equivalentClass
% statements. owl:equivalentClass is a built-in property that links a
% class description to another class description. The meaning of such a
% class axiom is that the two class descriptions involved have the same
% class extension (i.e., both class extensions contain exactly the same
% set of individuals).

  op equivalentClass :  Class * Class -> Boolean

  axiom definition_equivalentClass is 
  fa(C1 : Class, C2 : Class)
   equivalentClass(C1, C2) <=> 
   (fa(x1 : Individual)(Type(x1, C1) <=> Type(x1, C2)))

  conjecture theorem_reflexivity_of_equivalentClass is
  fa(C : Class)equivalentClass(C, C)

  axiom replacement_of_equivalentClass is
  fa(C1: Class, C2 : Class, x : Individual)
   equivalentClass(C1, C2) =>
   equivalentClass(addOne(x, C1), addOne(x, C2))

% Prove options are settings for the theorem prover (in this case,
% SNARK).  Different conjectures require different settings, but
% owl_prove_options is most common.  Hyperresolution, set of support
% strategy, no automatic numerical processing.  The orderings are symbol
% orderings for controlling paramdolation and the resolution rules.
% Smaller symbols are preferred.

%% use hyperresolution
def owl_prove_options = "(use-resolution nil) (use-hyperresolution t)
(use-negative-hyperresolution nil) (use-paramodulation)
(use-factoring) (use-literal-ordering-with-hyperresolution
'literal-ordering-p)(use-literal-ordering-with-negative-hyperresolution
'literal-ordering-p)(use-literal-ordering-with-resolution
'literal-ordering-a)(use-literal-ordering-with-paramodulation
'literal-ordering-p) (use-ac-connectives) (run-time-limit
10)(assert-supported nil) (use-code-for-numbers nil)
(print-symbol-ordering) (print-final-rows) 
(declare-ordering-greaterp 'snark::|Holds| 'snark::|Class?|) 
(declare-ordering-greaterp 'snark::|Type| 'snark::|Holds|) 
(declare-ordering-greaterp 'snark::|SubClass| 'snark::|Holds|) 
(declare-ordering-greaterp 'snark::|Type| 'snark::|sameAs|)
(declare-ordering-greaterp 'snark::|sameAs| 'snark::=)"    

%% use both hyperresolution and negative hyperresolution
def owl_hyper_prove_options = "(use-resolution nil) (use-hyperresolution t)
(use-negative-hyperresolution t) (use-paramodulation)
(use-factoring) (use-literal-ordering-with-hyperresolution
'literal-ordering-p)(use-literal-ordering-with-negative-hyperresolution
'literal-ordering-p)(use-literal-ordering-with-resolution
'literal-ordering-a)(use-literal-ordering-with-paramodulation
'literal-ordering-p) (use-ac-connectives) (run-time-limit
10)(assert-supported nil) (use-code-for-numbers nil)
(print-symbol-ordering) (print-final-rows) 
(declare-ordering-greaterp 'snark::|Holds| 'snark::|Class?|) 
(declare-ordering-greaterp 'snark::|Type| 'snark::|Holds|) 
(declare-ordering-greaterp 'snark::|SubClass| 'snark::|Holds|) 
(declare-ordering-greaterp 'snark::|Type| 'snark::|sameAs|)
(declare-ordering-greaterp 'snark::|sameAs| 'snark::=)"    

% The following proof option uses negative hyperesolution, procedural
% attachment for numerical operations, and set of support.

def owl_number_hyper_options = "(use-resolution nil) (use-hyperresolution nil)
(use-negative-hyperresolution t) (use-paramodulation)
(use-factoring) (use-literal-ordering-with-hyperresolution
'literal-ordering-p)(use-literal-ordering-with-negative-hyperresolution
'literal-ordering-n)(use-literal-ordering-with-resolution
'literal-ordering-a)(use-literal-ordering-with-paramodulation
'literal-ordering-a) (use-ac-connectives) (run-time-limit
10)(assert-supported nil) (use-code-for-numbers t)
(USE-REPLACEMENT-RESOLUTION-WITH-X=X)
(print-symbol-ordering) (print-final-rows) 
(declare-ordering-greaterp 'snark::|Holds| 'snark::|Class?|) 
(declare-ordering-greaterp 'snark::|Type| 'snark::|Holds|) 
(declare-ordering-greaterp 'snark::= 'snark::|Type|) 
(declare-ordering-greaterp  'snark::|sameAs| 'snark::|Type|)
(declare-ordering-greaterp 'snark::|SubClass| 'snark::|Holds|)
(declare-ordering-greaterp 'snark::|sameAs| 'snark::=)
(declare-ordering-greaterp 'snark::|card| 'snark::+)
(declare-ordering-greaterp  'snark::|card| 'snark::+)
(declare-ordering-greaterp 'snark::|AllDifferent| 'snark::=)
(declare-ordering-greaterp 'snark::|AllDifferent| 'snark::|Type|)
(declare-ordering-greaterp  'snark::= 'snark::|equivalentClass|)
"

% The following proof option uses binary resolution (rather than
% hyperresolution), procedural attachment for numbers, and set of
% support.


def owl_number_resolution_options = "(use-resolution t) 
(use-hyperresolution nil)(use-negative-hyperresolution nil) 
(use-paramodulation)(use-factoring) (use-literal-ordering-with-hyperresolution
'literal-ordering-p)(use-literal-ordering-with-negative-hyperresolution
'literal-ordering-p)(use-literal-ordering-with-resolution
nil)(use-literal-ordering-with-paramodulation
'literal-ordering-a) (use-ac-connectives) (run-time-limit
10)(assert-supported nil) (use-code-for-numbers t)
(USE-REPLACEMENT-RESOLUTION-WITH-X=X t)
(print-symbol-ordering) (print-final-rows) 
(declare-ordering-greaterp 'snark::|Holds| 'snark::|Class?|) 
(declare-ordering-greaterp 'snark::|Type| 'snark::|Holds|) 
(declare-ordering-greaterp 'snark::= 'snark::|Type|) 
(declare-ordering-greaterp  'snark::|sameAs| 'snark::|Type|)
(declare-ordering-greaterp 'snark::|SubClass| 'snark::|Holds|)
(declare-ordering-greaterp 'snark::|sameAs| 'snark::=)
(declare-ordering-greaterp 'snark::|AllDifferent| 'snark::=)
(declare-ordering-greaterp 'snark::|AllDifferent| 'snark::|Type|)
(declare-ordering-greaterp  'snark::= 'snark::|equivalentClass|)
"

% The following proof option uses binary resolution and numerical
% procedural attachments, but not set of support.

def owl_early_prove_options = "(use-resolution t)
(use-hyperresolution nil) (use-negative-hyperresolution nil)
(use-paramodulation) (use-factoring)
(use-literal-ordering-with-hyperresolution
'literal-ordering-p)(use-literal-ordering-with-negative-hyperresolution
'literal-ordering-p)(use-literal-ordering-with-resolution
nil)(use-literal-ordering-with-paramodulation
'literal-ordering-a) (use-ac-connectives) 
(run-time-limit
10)(assert-supported t) (use-code-for-numbers t)
(USE-REPLACEMENT-RESOLUTION-WITH-X=X)
(print-symbol-ordering) (print-final-rows) (declare-ordering-greaterp
'snark::|Holds| 'snark::|Class?|) (declare-ordering-greaterp
'snark::|Type| 'snark::|Holds|) 
(declare-ordering-greaterp 'snark::|SubClass| 'snark::|Holds|)
(declare-ordering-greaterp 'snark::|SubClass| 'snark::|Type|)  
(declare-ordering-greaterp 'snark::|Type| 'snark::|sameAs|)
(declare-ordering-greaterp 'snark::|sameAs| 'snark::=)
(declare-ordering-greaterp 'snark::|AllDifferent| 'snark::=)
(declare-ordering-greaterp 'snark::|AllDifferent| 'snark::|Type|)"

% The following option is similar to number_prove_options; it uses binary
% resolution, numerical processing, and set of support.  It differs in the
% ordering on some of the symbols.  Some theorems can be proved with one
% ordering but not the other, and vice versa.

def owl_resolution_prove_options = "(use-resolution t)
(use-hyperresolution nil) (use-negative-hyperresolution nil)
(use-paramodulation) (use-factoring)
(use-literal-ordering-with-hyperresolution
'literal-ordering-p)(use-literal-ordering-with-negative-hyperresolution
'literal-ordering-p)(use-literal-ordering-with-resolution
'literal-ordering-a)(use-literal-ordering-with-paramodulation
'literal-ordering-a) (use-ac-connectives) (run-time-limit
10)(assert-supported nil) (use-code-for-numbers t)
(USE-REPLACEMENT-RESOLUTION-WITH-X=X)
(print-symbol-ordering) (print-final-rows) 
(declare-ordering-greaterp 'snark::|Holds| 'snark::|Class?|) 
(declare-ordering-greaterp 'snark::|Type| 'snark::|Holds|) 
(declare-ordering-greaterp 'snark::|SubClass| 'snark::|Holds|)
(declare-ordering-greaterp 'snark::|SubClass| 'snark::|Type|)  
(declare-ordering-greaterp 'snark::|Type| 'snark::|sameAs|)
(declare-ordering-greaterp 'snark::|sameAs| 'snark::=)
(declare-ordering-greaterp 'snark::|AllDifferent| 'snark::=)
(declare-ordering-greaterp 'snark::|AllDifferent| 'snark::|Type|)"


endspec

owl_core_test = spec

import owl_core

% "Testcase" conjectures come from OWL testcase files.  

conjecture testcase_AllDifferent_Manifest_test is
   fa(Fred : Individual, Wilma : Individual,
      Barney : Individual, Betty : Individual)
       AllDifferent(cons(Fred, cons(Wilma, cons(Barney, cons(Betty, nil)))))
        =>
       differentFrom(Barney, Fred)
endspec

owl_class_ops = spec

import owl_core


% 3.1.1 Enumeration

% A class description of the "enumeration" kind is defined with the
% owl:oneOf property. The value of this built-in OWL property must be a
% list of individuals that are the instances of the class. This enables
% a class to be described by exhaustively enumerating its instances. The
% class extension of a class described with owl:oneOf contains exactly
% the enumerated individuals, no more, no less.

% Because Specware does not allow functions with multiple arities, we
% define oneOf for only two arguments.  Composition gives the multiple
% arity function.


op oneOf :  Individual * Individual -> Class

  axiom oneOf_definition is
   fa(x : Individual, y : Individual, z : Individual)
     Type(z, oneOf(x, y)) <=>
     (z = x or z = y)

  conjecture lemma_oneOf_vs_addOne is
   fa(x : Individual, y : Individual, z : Individual)
    Type(z, oneOf(x, y)) <=>  Type(z, addOne(x, addOne(y, Nothing)))

  conjecture theorem_oneOf_vs_addOne is
   fa(x : Individual, y : Individual)
    equivalentClass(oneOf(x, y), addOne(x, addOne(y, Nothing)))


% 3.1.3.1 owl:intersectionOf

% The owl:intersectionOf property links a class to a list of class
% descriptions. An owl:intersectionOf statement describes a class for
% which the class extension contains precisely those individuals that
% are members of the class extension of all class descriptions in the
% list.
 
op intersectionOf : Class * Class -> Class

  axiom intersectionOf_definition is
  fa(C1 : Class, C2 : Class, x : Individual)
    Type(x, intersectionOf(C1, C2)) <=>
    (Type(x, C1) & Type(x, C2))

  conjecture theorem_intersectionOf_Nothing is
  fa(C : Class)equivalentClass(intersectionOf(C, Nothing), Nothing)

  conjecture theorem_intersectionOf_Thing is
  fa(C : Class)equivalentClass(intersectionOf(C, Thing), C)

% 3.1.3.2 owl:unionOf

% The owl:unionOf property links a class to a list of class
% descriptions. An owl:unionOf statement describes an anonymous class
% for which the class extension contains those individuals that occur in
% at least one of the class extensions of the class descriptions in the
% list.


op unionOf : Class * Class -> Class

  axiom unionOf_definition is
  fa(C1 : Class, C2 : Class, x : Individual)
    Type(x, unionOf(C1, C2)) <=>
    (Type(x, C1) or Type(x, C2))

  conjecture theorem_unionOf_Nothing is
  fa(C : Class)equivalentClass(unionOf(C, Nothing), C)


  conjecture theorem_unionOf_Thing is
  fa(C : Class)equivalentClass(unionOf(C, Thing), Thing)

% 3.1.3.3 owl:complementOf

% An owl:complementOf property links a class to precisely one class
% description. An owl:complementOf statement describes a class for which
% the class extension contains exactly those individuals that do not
% belong to the class extension of the class description that is the
% object of the statement. owl:complementOf is analogous to logical
% negation: the class extension consists of those individuals that are
% NOT members of the class extension of the complement class.

op complementOf : Class -> Class

  axiom complementOf_definition is
  fa(C : Class, x : Individual)
    Type(x, complementOf(C)) <=> ~(Type(x, C))

  conjecture theorem_complementOf_Nothing is
  fa(C : Class)equivalentClass(complementOf(Nothing), Thing)

  conjecture theorem_complementOf_Thing is
  fa(C : Class)equivalentClass(complementOf(Thing), Nothing)

% A class axiom may also contain (multiple) owl:disjointWith
% statements. owl:disjointWith is a built-in OWL property with a class
% description as domain and range. Each owl:disjointWith statement
% asserts that the class extensions of the two class descriptions
% involved have no individuals in common. Like axioms with
% rdfs:subClassOf, declaring two classes to be disjoint is a partial
% definition: it imposes a necessary but not sufficient condition on the
% class.

op disjointWith : Class * Class -> Boolean

  axiom disjoint_implies_no_common_element is
   fa(C1 : Class, C2 : Class, x : Individual)
    disjointWith(C1, C2) =>
    ~(Type(x, C1) & Type(x, C2))

  
% common(C1, C2) is a common element of C1 and C2, if one exists.

op common : Class * Class -> Individual

  axiom disjoint_if_no_common_element is
   fa(C1 : Class, C2 : Class)
    ~(Type(common(C1, C2), C1) & Type(common(C1, C2), C2)) =>
    disjointWith(C1, C2)

  conjecture theorem_complements_are_disjoint is
   fa(C : Class)disjointWith(C, complementOf(C))


endspec

owl_class_ops_test = spec

import owl_class_ops


  conjecture test_complementOf_001 is
   fa(C : Class)
    equivalentClass(C, complementOf(complementOf(C)))


endspec

property_restriction = spec

import owl_core


% The value constraint owl:allValuesFrom is a built-in OWL property that
% links a restriction class to either a class description or a data
% range. A restriction containing an owl:allValuesFrom constraint is
% used to describe a class of all individuals for which all values of
% the property under consideration are either members of the class
% extension of the class description or are data values within the
% specified data range. In other words, it defines a class of
% individuals x for which holds that if the pair (x,y) is an instance of
% P (the property concerned), then y should be an instance of the class
% description or a value in the data range, respectively.

op allValuesFrom : Property * Class -> Class

   axiom definition_allValuesFrom is
    fa(P : Property, C : Class, x : Individual)
     (Type(x, allValuesFrom(P,C)) <=>
     (fa(y2 : Individual)(Holds(P,x,y2) => Type(y2,C))))

% Not a theorem, only holds for the set extensions of the classes.
%   conjecture theorem_subclass_allValuesFrom_Nothing_Nothing is
%    fa(P : Property)
%      SubClass(allValuesFrom(P, Nothing), Nothing)

   conjecture theorem_subclass_Nothing_allValuesFrom_Nothing is
    fa(P : Property)
      SubClass(Nothing, allValuesFrom(P, Nothing))

%  Not a theorem, only holds for set extensions.
%   conjecture theorem_allValuesFrom_Nothing is
%    fa(P : Property)
%      equivalentClass(allValuesFrom(P, Nothing), Nothing)


% SNARK found no proof: This conjecture false
%  --x might not be related to anything under P.
%   conjecture theorem_extension_subClass_allValuesFrom_Nothing_Nothing is
%     (fa(x : Individual, y : Individual P : Property)
%      Type(x, allValuesFrom(P, Nothing)) => Type(x, Nothing))

% The value constraint owl:someValuesFrom is a built-in OWL property
% that links a restriction class to a class description or a data
% range. A restriction containing an owl:someValuesFrom constraint
% describes a class of all individuals for which at least one value of
% the property concerned is an instance of the class description or a
% data value in the data range. In other words, it defines a class of
% individuals x for which there is at least one y (either an instance of
% the class description or value of the data range) such that the pair
% (x,y) is an instance of P. This does not exclude that there are other
% instances (x,y') of P for which y' does not belong to the class
% description or data range.

op someValuesFrom : Property * Class -> Class
op someValueFrom : Property * Class * Individual -> Individual

   axiom definition_someValuesFrom_RL is
    fa(P : Property, C : Class, x : Individual)
     ((ex(y : Individual)(Holds(P,x,y) & Type(y, C))) =>
       Type(x, someValuesFrom(P,C)))  

   axiom definition_someValuesFrom_LR is
    fa(P : Property, C : Class, x : Individual)
     (Type(x, someValuesFrom(P,C)) =>
       (Holds(P,x,someValueFrom(P, C, x)) & Type(someValueFrom(P, C, x), C))) 


%  SNARK found no proof--maybe x not P related to anything
%   conjecture theorem_someValuesFrom_Thing is
%    fa(P : Property)
%      equivalentClass(someValuesFrom(P, Thing), Thing)

   op False_property : Property

   axiom false_property_doesnt_hold is
    fa(x : Individual, y : Individual)
    ~(Holds(False_property, x, y))

   conjecture not_theorem_someValuesFrom_Thing is
    ex(P : Property)
      ~(equivalentClass(someValuesFrom(P, Thing), Thing))


   conjecture theorem_type_someValuesFrom_Thing is
    fa(P : Property, x : Individual, y : Individual)
      (Holds(P,x,y) =>
       Type(x, someValuesFrom(P, Thing)))

op hasValue : Property * Individual -> Class
 
  axiom definition_hasValue is
    fa(P : Property, x : Individual, y : Individual)
      (Type(x, hasValue(P, y)) <=> Holds(P,x,y))

endspec

cardinality_core = spec
import owl_core


op choice : Class -> Individual

op remove : Individual * Class -> Class


   axiom choice_remove is
     fa(C : Class)
%      ~(equivalentClass(C, Nothing)) =>  %  simplified by SNARK
      ~(Type(choice(C), remove(choice(C), C)))

% turned out not to work. theorem_Cardinality_two_not_three not proved. why?
%   axiom remove_removes is
%    fa(x : Individual, C : Class)
%     ~(Type(x, remove(x, C)))


   axiom remove_nonmember is
     fa(C : Class, x : Individual)
      ~(Type(x, C)) =>
      C = remove(x, C)

   axiom class_decomposition is
     fa(C : Class)
      ~(equivalentClass(C, Nothing)) =>
      equivalentClass(C, addOne(choice(C), remove(choice(C), C)))

op card : Class -> Nat


   axiom card_equivalentClass is
     fa (C1 : Class, C2 : Class)
      equivalentClass(C1, C2) => 
      (card(C1) = card(C2))

   conjecture theorem_type_choice is
     fa(C : Class)
      ~(equivalentClass(C, Nothing)) =>
      Type(choice(C), C)

endspec

owlnat = spec

  axiom zero_identity is
   fa(x : Nat)
    x + 0 = x

  axiom zero_left_identity is
   fa(x : Nat)
    0 + x = x

  axiom successor_is_oneone is
  fa(x : Nat, y : Nat, z : Nat)
   z + x = z + y  => x = y
   

  axiom adder_is_zero is
  fa(x : Nat, y : Nat)
   x + y = x  => y = 0

  axiom equal_implies_gtq is
   fa(x : Nat, y : Nat)
    x = y => x >= y

  axiom reflexivity_of_gtq is
   fa(x : Nat)
    x >= x 

  axiom antisymmetry_of_gtq is
   fa(x : Nat, y : Nat)
   (x >= y & y >= x) => x = y

 axiom transitivity_of_gtq is
  fa(x : Nat, y : Nat, z : Nat)
   (x >= y & y >= z) => x >= z

  axiom zero_gtq is
  fa (y : Nat)
   0 >= y => 0 = y

  axiom successor_gtq is
  fa(x : Nat, y : Nat)
   x + 1 >= y
   =>  (1 + x = y or x >= y)

  conjecture theorem_one_gtq is
  fa(y: Nat)
   1 >= y => (1 = y or 0 = y)

  def owl_nat_prove_options = "(use-resolution t) (use-hyperresolution
  nil) (use-negative-hyperresolution nil) (use-paramodulation)
  (use-factoring) (use-literal-ordering-with-hyperresolution
  'literal-ordering-p)(use-literal-ordering-with-negative-hyperresolution
  'literal-ordering-p)(use-literal-ordering-with-resolution
  'literal-ordering-a)(use-literal-ordering-with-paramodulation
  'literal-ordering-p) (use-ac-connectives) (run-time-limit
  20)(assert-supported nil) (use-code-for-numbers t)
  (print-symbol-ordering) (print-final-rows)"

endspec


cardinality = spec

import cardinality_core


import owlnat


% If Class is finite, its card is the number of syntactically distinct
% elements it has.  Otherwise it is unspecified.

%  The following axiom should be unnecessary with changes in the interface
  axiom card_nonnegative is
    fa(C : Class)
     card(C) >= 0

   axiom card_Nothing is
      fa(C : Class)
       equivalentClass(C, Nothing) =>
       card(C) = 0

   axiom cardzero is
     fa(C : Class)
       card(C) = 0 =>
       equivalentClass(C, Nothing)

   axiom card_addOne_element is
     fa(x : Individual, C : Class)
      Type(x, C) =>
       card(addOne(x, C)) = card(C)

   axiom card_addOne_nonelement is
     fa(x : Individual, C : Class)
      (~(Type(x, C)) =>
       card(addOne(x, C)) = 1 + card(C))

   conjecture theorem_card_of_Nothing_is_zero is
      card(Nothing) = 0

   conjecture theorem_card_of_Thing_not_zero is
      ~(card(Thing) = 0)

   conjecture theorem_card_1 is
     fa(x : Individual)
       card(addOne(x, Nothing)) = 1

   conjecture theorem_card_one_not_Nothing is 
     fa (C : Class)
      card(C) = 1 =>
      ~(equivalentClass(C, Nothing))

%   conjecture theorem_card_one_choice is 
%     fa (C : Class)
%      ~(Type(choice(C), remove(choice(C), C)))

   conjecture theorem_card_zero_remove_is_nothing is
      fa(C : Class)
       0 = card(C) =>
       equivalentClass(remove(choice(C), C), Nothing)


% simplified by snark 3/26/04
   conjecture lemma_not_nothing_card_addone_plus is
     fa(C : Class)
      ~(equivalentClass(C, Nothing)) =>   %% antecedent can be commented out
      card(addOne(choice(C), remove(choice(C), C))) =
       1 + card(remove(choice(C), C))

   conjecture theorem_card_one_remove is
      fa(C : Class)
      ~(equivalentClass(C, Nothing)) =>
       card(C) = 1 + card(remove(choice(C), C))

   conjecture theorem_one_gtq_card_remove_is_nothing is
      fa(C : Class)
       1 >= card(C) =>
       equivalentClass(remove(choice(C), C), Nothing)

   conjecture theorem_cardone is
      fa(C : Class, x : Individual, y : Individual)
        1 = card(C) =>
        Type(x, C) =>
        Type(y, C) => sameAs(x, y)

   conjecture theorem_card_gtq_choice is
      fa(C : Class)
        card(C) >= 1 =>
        Type(choice(C), C)

   conjecture theorem_card_two_not_nothing is
      fa(C : Class)
       2  = card(C) =>
       ~(equivalentClass(C, Nothing))
 
   conjecture theorem_card_two_remove_has_card_one is
      fa(C : Class)
       2 = card(C) =>
       1 = card(remove(choice(C), C))
   
   conjecture theorem_card_two_not_same is
      fa(C : Class)
        2 = card(C) =>
         (ex(x : Individual, y : Individual)
          (Type(x, C) &
           Type(y, C) &
           ~(sameAs(x, y))))

   
   conjecture theorem_card_two_not_three is
      fa(C : Class, x : Individual, y : Individual, z : Individual)
        2 = card(C) =>
        Type(x, C) =>
        Type(y, C) => 
        Type(z, C) => 
	~(AllDifferent(cons(x, cons(y, cons(z, nil)))))

  axiom definition_SubClass_if is
    fa(c1 : Class, c2 : Class)
     (fa(x : Individual)
      Type(x, c1) => Type(x, c2)) =>
     SubClass(c1, c2)

  axiom card_of_subClass is
    fa(c1 : Class, c2 : Class)
     (SubClass(c1, c2) =>
      card(c2) >= card(c1)) 
 
op image : Individual * Property -> Class

% The image of a given individual under a property is that class of
% all individuals that are related to the given individual under that
% property.

axiom definition_image is
  fa(x : Individual, y : Individual, P : Property)
    (Type(y, image(x, P)) <=> Holds(P, x, y))

conjecture theorem_subClass_of_image is
  fa(P : Property, C : Class, x : Individual)
   ((fa(y : Individual) 
     (Type(y, C) => Holds(P, x, y))) =>
   SubClass(C, image(x, P)))

% A restriction containing an owl:maxCardinality constraint describes a
% class of all individuals that have at most N semantically distinct
% values (individuals or data values) for the property concerned, where
% N is the value of the cardinality constraint.

op Cardinality : Property * Nat -> Class

  axiom definition_Cardinality is
  fa(P : Property, n : Nat, x : Individual)
   Type(x, Cardinality(P, n)) <=> card(image(x, P)) = n

  conjecture theorem_Cardinality_one is
  fa(P : Property, x : Individual, y1 : Individual, y2 : Individual)
   Type(x, Cardinality(P, 1)) =>
   (Holds(P, x, y1) & Holds(P, x, y2) => sameAs(y1, y2))

op maxCardinality : Property * Nat -> Class

  axiom definition_maxCardinality is
   fa(P : Property, n : Nat, x : Individual)
    Type(x, maxCardinality(P, n)) <=> n >= card(image(x, P)) 

  conjecture theorem_Cardinality_subClass_maxCardinality is
   fa(P : Property, n : Nat, x : Individual)
    Type(x, Cardinality(P, n)) => Type(x, maxCardinality(P, n))

  conjecture theorem_maxCardinality_one is
  fa(P : Property, x : Individual, y1 : Individual, y2 : Individual)
   Type(x, maxCardinality (P, 1)) =>
   (Holds(P, x, y1) & Holds(P, x, y2) => sameAs(y1, y2))

op minCardinality : Property * Nat -> Class

  axiom definition_minCardinality is
   fa(P : Property, n : Nat, x : Individual)
    Type(x, minCardinality(P, n)) <=>  card(image(x, P)) >= n

  conjecture theorem_Cardinality_subClass_minCardinality is
   fa(P : Property, n : Nat, x : Individual)
    Type(x, Cardinality(P, n)) => Type(x, minCardinality(P, n))

  conjecture theorem_minCardinality_one is
  fa(P : Property, x : Individual)
   Type(x, minCardinality(P, 1)) =>
   (ex(y : Individual) (Holds(P, x, y)))

% observed by SNARK
  conjecture theorem_minCardinality_zero is
  fa(P : Property, x : Individual)
   Type(x, minCardinality(P, 0))


endspec

cardinality_test = spec

import cardinality
  
  conjecture theorem_Cardinality_two_not_three is
  fa(P : Property, x : Individual, 
     y1 : Individual, y2 : Individual, y3 : Individual)
   Type(x, Cardinality(P, 2)) =>
   (Holds(P, x, y1) & Holds(P, x, y2) & Holds(P, x, y3) => 
   ~(AllDifferent(cons(y1, cons(y2, cons(y3, nil))))))

  conjecture theorem_Cardinality_two_not_same is
  fa(P : Property, x : Individual)
   Type(x, Cardinality(P, 2)) =>
    (ex(y1 : Individual, y2 : Individual)
     (Holds(P, x, y1) & Holds(P, x, y2) &
     ~(sameAs(y1, y2))))

  conjecture testcase_cardinality_002 is
  fa(P : Property, n : Nat, x : Individual)
   (Type(x, maxCardinality(P, n)) & 
    Type(x, minCardinality(P, n))) =>
  Type(x, Cardinality(P, n))

  conjecture theorem_Cardinality_not_same_zero is
  fa(P : Property, x : Individual, n : Nat)
   Type(x, Cardinality(P, 0)) =>
    (ex(C : Class)
     fa(y : Individual)
     ((Type(y, C) => Holds(P, x, y))  &
      card(C) = 0))

  conjecture theorem_Cardinality_not_same_one is
  fa(P : Property, x : Individual, n : Nat)
   Type(x, Cardinality(P, 1)) =>
    (ex(C : Class)
     fa(y : Individual)
     ((Type(y, C) => Holds(P, x, y))  &
      card(C) = 1))

  conjecture theorem_minCardinality_not_same_n is
  fa(P : Property, x : Individual, n : Nat)
   Type(x, minCardinality(P, n)) =>
    (ex(C : Class)
     fa(y : Individual)
     ((Type(y, C) => Holds(P, x, y))  &
      card(C)>= n))


  conjecture theorem_maxCardinality_not_different_n is
  fa(P : Property, x : Individual, n : Nat)
   (Type(x, maxCardinality(P, n)) =>
    (fa(C : Class)
     (fa(y : Individual)
      ((Type(y, C) => Holds(P, x, y)))) =>
       n >= card(C)))

  conjecture theorem_Cardinality_not_same_n is
  fa(P : Property, x : Individual, n : Nat)
   Type(x, Cardinality(P, n)) =>
    (ex(C : Class)
     fa(y : Individual)
     ((Type(y, C) => Holds(P, x, y))  &
      card(C)= n))


  conjecture theorem_Cardinality_not_different_n is
  fa(P : Property, x : Individual, n : Nat)
   (Type(x, Cardinality(P, n)) =>
    (fa(C : Class)
     (fa(y : Individual)
      ((Type(y, C) => Holds(P, x, y)))) =>
      n >= card(C)))
  
    op P : Property
    op a : Individual
    op b1 : Individual
    op b2 : Individual
    op b3 : Individual

    axiom antecedent_Cardinality_two is
    Type(a, Cardinality(P, 2)) &
    Holds(P,a,b1) &
    Holds(P,a,b2) &
    Holds(P,a,b3)

    conjecture theorem_Cardinality_two_Alldifferent is
     ~(AllDifferent(cons(b1,cons(b2,cons(b3, nil)))))

endspec
 
properties = spec

import owl_core

% An object property are defined as an instance of the built-in OWL
% class owl:ObjectProperty. A datatype property is defined as an
% instance of the built-in OWL class owl:DatatypeProperty. Both
% owl:ObjectProperty and owl:DatatypeProperty are subclasses of the RDF
% class rdf:Property (see Appendix B).

% NOTE: In OWL Full, object properties and datatype properties are not
% disjoint. Because data values can be treated as individuals, datatype
% properties are effectively subclasses of object properties. In OWL
% Full owl:ObjectProperty is equivalent to rdf:Property In practice,
% this mainly has consequences for the use of
% owl:InverseFunctionalProperty. See also the OWL Full characterization
% in Section 8.1.

op Data? : Individual -> Boolean
 
sort Data = {x : Individual | Data? x}

op DatatypeProperty? : Property -> Boolean

sort DatatypeProperty = {x : Property | DatatypeProperty? x}

% 4.1.1 rdfs:subPropertyOf

% A rdfs:subPropertyOf axiom defines that the property is a subproperty
% of some other property. Formally this means that if P1 is a
% subproperty of P2, then the property extension of P1 (a set of pairs)
% should be a subset of the property extension of P2 (also a set of
% pairs).


  op subPropertyOf : Property * Property -> Boolean

  axiom definition_of_subPropertyOf is
    fa(P1 : Property, P2 : Property)
      subPropertyOf(P1, P2) <=>
       (fa(x : Individual, y : Individual)
        Holds(P1,x,y) => Holds(P2,x,y))

% 4.1.2 rdfs:domain 

% For a property one can define (multiple) rdfs:domain
% axioms. Syntactically, rdfs:domain is a built-in property that links a
% property (some instance of the class rdf:Property) to a class
% description. An rdfs:domain axiom asserts that the subjects of such
% property statements must belong to the class extension of the
% indicated class description.



  op Domain : Property * Class -> Boolean

  axiom definition_of_Domain is
    fa(P : Property, c : Class)
     Domain(P, c) <=>
      (fa(x : Individual, y : Individual)
       (Holds(P,x,y) => Type(x, c)))

% 4.1.3 rdfs:range

% For a property one can define (multiple) rdfs:range
% axioms. Syntactically, rdfs:range is a built-in property that links a
% property (some instance of the class rdf:Property) to to either a
% class description or a data range. An rdfs:range axiom asserts that
% the values of this property must belong to the class extension of the
% class description or to data values in the specified data range.


  op Range : Property * Class -> Boolean

  axiom definition_of_range is
    fa(P : Property, c : Class)
     Range(P, c) <=>
      (fa(x : Individual, y : Individual)
       (Holds(P,x,y) => Type(y, c)))

% 4.2.1 owl:equivalentProperty

% The owl:equivalentProperty construct can be used to state that two
% properties have the same property extension. Syntactically,
% owl:equivalentProperty is a built-in OWL property with rdf:Property as
% both its domain and range.

% NOTE: Property equivalence is not the same as property
% equality. Equivalent properties have the same "values" (i.e., the same
% property extension), but may have different intensional meaning (i.e.,
% denote different concepts). Property equality should be expressed with
% the owl:sameAs construct. As this requires that properties are treated
% as individuals, such axioms are only allowed in OWL Full.

  op equivalentProperty : Property

  axiom definition_of_equivalentProperty is
   fa(P : Property, Q : Property)
     Holds(equivalentProperty, P, Q) <=>
     (fa(x : Individual, y : Individual)
      (Holds(P,x,y) <=> Holds(Q,x,y)))

% observed by SNARK
  conjecture theorem_reflexivity_of_equivalentProperty is
   fa(P : Property)Holds(equivalentProperty, P, P)


% 4.2.2 owl:inverseOf

% Properties have a direction, from domain to range. In practice, people
% often find it useful to define relations in both directions: persons
% own cars, cars are owned by persons. The owl:inverseOf construct can
% be used to define such an inverse relation between properties.

% Syntactically, owl:inverseOf is a built-in OWL property with
% owl:ObjectProperty as its domain and range. An axiom of the form P1
% owl:inverseOf P2 asserts that for every pair (x,y) in the property
% extension of P1, there is a pair (y,x) in the property extension of
% P2, and vice versa. Thus, owl:inverseOf is a symmetric property.

  op inverseOf : Property

  axiom definition_of_inverseOf is
   fa(P : Property, Q : Property)
     Holds(inverseOf, P, Q) <=>
     (fa(x : Individual, y : Individual)
      (Holds(P,x,y) <=> Holds(Q,y,x)))

  conjecture theorem_inverseOf_is_symmetric is
   fa(P : Property, Q : Property, R : Property)
     Holds(inverseOf, P, Q) & Holds(inverseOf, Q, R) =>
     Holds(equivalentProperty, P, R)

% 4.3.1 owl:FunctionalProperty

% A functional property is a property that can have only one (unique)
% value y for each instance x, i.e. there cannot be two distinct values
% y1 and y2 such that the pairs (x,y1) and (x,y2) are both instances of
% this property. Both object properties and datatype properties can be
% declared as "functional". For this purpose, OWL defines the built-in
% class owl:FunctionalProperty as a special subclass of the RDF class
% rdf:Property.


  op FunctionalProperty : Class
  
  axiom Functional_subClassOf_property is
   SubClass(FunctionalProperty, Property)

  axiom definition_of_FunctionalProperty is
   fa(F : Property)
     Type(F, FunctionalProperty) <=>
     (fa(x : Individual, y1 : Individual, y2 : Individual)
      (Holds(F,x,y1) & Holds(F,x,y2)  => y1 = y2))

%% If prop belongs to owl:FunctionalProperty, and subject denotes a
%% resource which is the subject of two prop triples, then the objects of
%% these triples have the same denotation.

% 4.3.2 owl:InverseFunctionalProperty

% If a property is declared to be inverse-functional, then the object of
% a property statement uniquely determines the subject (some
% individual). More formally, if we state that P is an
% owl:InverseFunctionalProperty, then this asserts that a value y can
% only be the value of P for a single instance x, i.e. there cannot be
% two distinct instances x1 and x2 such that both pairs (x1,y) and
% (x2,y) are instances of P.

% Syntactically, an inverse-functional property axiom is specified by
% declaring the property to be an instance of the built-in OWL class
% owl:InverseFunctionalProperty, which is a subclass of the OWL class
% owl:ObjectProperty.

  op InverseFunctionalProperty : Class
  
  axiom InverseFunctional_subClassOf_property is
   SubClass(InverseFunctionalProperty, Property)


  axiom definition_of_InverseFunctionalProperty is
   fa(F : Property)
     Type(F, InverseFunctionalProperty) <=>
     (fa(x1 : Individual, x2 : Individual, y : Individual)
      (Holds(F,x1,y) & Holds(F,x2,y)  => x1 = x2))

  conjecture theorem_inverseOf_Functional_is_InverseFunctional is
   fa(F : Property, G : Property)
     Holds(inverseOf, F, G) =>
       (Type(F, FunctionalProperty) <=> 
        Type(G, InverseFunctionalProperty))

% 4.4.1 owl:TransitiveProperty

% When one defines a property P to be a transitive property, this means
% that if a pair (x,y) is an instance of P, and the pair (y,z) is also
% instance of P, then we can infer the the pair (x,z) is also an
% instance of P.

% Syntactically, a property is defined as being transitive by making it
% an instance of the the built-in OWL class owl:TransitiveProperty,
% which is defined as a subclass of owl:ObjectProperty.

  op TransitiveProperty : Class

  axiom Transitive_subClassOf_property is
   SubClass(TransitiveProperty, Property)

  axiom definition_of_TransitiveProperty is
   fa(F : Property)
     Type(F, TransitiveProperty) <=>
     (fa(x : Individual, y : Individual, z : Individual)
      (Holds(F,x,y) & Holds(F,y,z)  => Holds(F,x,z)))

% Typical examples of transitive properties are properties representing
% certain part-whole relations. For example, we might want to say that
% the subRegionOf property between regions is transitive:

% <owl:TransitiveProperty rdf:ID="subRegionOf"> <rdfs:domain
% rdf:resource="#Region"/> <rdfs:range rdf:resource="#Region"/>
% </owl:TransitiveProperty>

% From this an OWL reasoner should be able to derive that if
% ChiantiClassico, Tuscany and Italy are regions, and ChiantiClassico is
% a subregion of Tuscany, and Tuscany is a subregion of Italy, then
% ChiantiClassico is also a subregion of Italy.

   conjecture example_chianti is
     fa(subRegionOf : Property)
     Type(subRegionOf, TransitiveProperty) =>
      (fa(ChiantiClassico : Individual, 
	 Tuscany : Individual, 
	 Italy : Individual)
          (Holds(subRegionOf, ChiantiClassico, Tuscany) &
	   Holds(subRegionOf, Tuscany, Italy) =>
	  Holds(subRegionOf, ChiantiClassico, Italy)))



% 4.4.2 owl:SymmetricProperty

% A symmetric property is a property for which holds that if the pair
% (x,y) is an instance of P, then the pair (y,x) is also an instance of
% P. Syntactically, a property is defined as symmetric by making it an
% instance of the built-in OWL class owl:SymmetricProperty, a subclass
% of owl:ObjectProperty.

  op SymmetricProperty : Class

  axiom Symmetric_subClassOf_property is
   SubClass(SymmetricProperty, Property)

  axiom definition_of_SymmetricProperty is
   fa(F : Property)
     Type(F, SymmetricProperty) <=>
     (fa(x : Individual, y : Individual)
      (Holds(F,x,y)  => Holds(F,y,x)))


  conjecture theorem_domain_and_range_of_symmetric_are_the_same is
   fa(F : Property, c: Class)
     Type(F, SymmetricProperty) =>
     (Domain(F, c) <=> Range(F, c))

endspec

properties_test = spec

import properties

% If prop belongs to owl:FunctionalProperty, and subject denotes a
% resource which is the subject of two prop triples, then the objects of
% these triples have the same denotation.


  conjecture testcase_FunctionalProperty_Manifest001_test is
     fa(Prop : Property)
     Type(Prop, FunctionalProperty) =>
     (fa(subject : Individual, object1 : Individual, object2 : Individual)
      (Holds(Prop,subject,object1) & 
       Holds(Prop,subject,object2)  => 
       sameAs(object1, object2)))

% Hence any assertion made using
% one of them can be transferred to the other.

 
  conjecture testcase_FunctionalProperty_Manifest002_test is
     fa(Prop : Property)
     Type(Prop, FunctionalProperty) =>
     (fa(subject : Individual, object1 : Individual, object2 : Individual)
      (Holds(Prop,subject,object1) & 
       Holds(Prop,subject,object2)  => 
       (fa (Prop2 : Property, value : Individual) 
	(Holds(Prop2, object1, value) =>
         Holds(Prop2, object2, value)))))


endspec

owl = spec

import owl_class_ops

import property_restriction

import cardinality

import properties

conjecture contradictory is
false

endspec


theorem_one_gtq = prove theorem_one_gtq in owlnat
  options owl_nat_prove_options

theorem_reflexivity_of_equivalentClass = 
  prove theorem_reflexivity_of_equivalentClass in owl_core
  options owl_resolution_prove_options

theorem_not_AllDifferent_cons_xx = 
  prove theorem_not_AllDifferent_cons_xx 
  in owl_core
  options owl_early_prove_options

theorem_type_identity = prove theorem_type_identity in owl_core
   options owl_early_prove_options

theorem_reflexivity_of_sameAs = prove theorem_reflexivity_of_sameAs
   in owl_core
   options owl_early_prove_options 

theorem_singleton = prove  theorem_singleton in owl_core
   options owl_early_prove_options

testcase_AllDifferent_Manifest_test =
prove testcase_AllDifferent_Manifest_test in owl_core_test
   options owl_prove_options

theorem_type_choice = prove theorem_type_choice in cardinality_core
   options owl_prove_options 

theorem_subclass_Nothing_allValuesFrom_Nothing = 
prove theorem_subclass_Nothing_allValuesFrom_Nothing in property_restriction
   options owl_early_prove_options

(*  %% not a theorem, should fail
not_theorem_someValuesFrom_Thing = prove not_theorem_someValuesFrom_Thing 
   in property_restriction
   options owl_prove_options
*)
theorem_type_someValuesFrom_Thing = prove theorem_type_someValuesFrom_Thing 
   in property_restriction
   options owl_early_prove_options

theorem_card_1 = prove theorem_card_1 in cardinality
   options owl_early_prove_options

theorem_card_one_not_Nothing =
   prove theorem_card_one_not_Nothing in cardinality
   options owl_early_prove_options

%theorem_card_one_choice = prove theorem_card_one_choice in cardinality
%   options owl_early_prove_options

theorem_card_zero_remove_is_nothing =
   prove  theorem_card_zero_remove_is_nothing in cardinality
   options owl_early_prove_options 

lemma_not_nothing_card_addone_plus =    %added 20040206 needed for theorem_card_one_remove
prove  lemma_not_nothing_card_addone_plus in cardinality
   options owl_early_prove_options 

theorem_card_one_remove =
prove theorem_card_one_remove in cardinality
   options  owl_number_resolution_options


theorem_one_gtq_card_remove_is_nothing = 
   prove theorem_one_gtq_card_remove_is_nothing in cardinality
   options owl_prove_options

theorem_cardone = prove theorem_cardone in cardinality
   options owl_prove_options

theorem_card_gtq_choice = prove theorem_card_gtq_choice in cardinality
   options owl_prove_options

theorem_card_two_not_nothing =
  prove theorem_card_two_not_nothing
  in cardinality
  options owl_prove_options

theorem_card_two_remove_has_card_one =
  prove theorem_card_two_remove_has_card_one
  in cardinality
  options  owl_number_hyper_options

theorem_card_two_not_same =
  prove theorem_card_two_not_same
  in cardinality
  options owl_prove_options


theorem_card_two_not_three = prove theorem_card_two_not_three
  in cardinality
  options owl_hyper_prove_options 

theorem_card_of_Nothing_is_zero = 
  prove theorem_card_of_Nothing_is_zero in cardinality
  options owl_early_prove_options

  theorem_card_of_Thing_not_zero = 
  prove theorem_card_of_Thing_not_zero in cardinality
  options owl_prove_options

theorem_subClass_of_image = prove theorem_subClass_of_image
  in cardinality
%  using definition_SubClass_if, definition_image
  options owl_resolution_prove_options

theorem_Cardinality_one = prove theorem_Cardinality_one in cardinality
   options owl_prove_options

theorem_Cardinality_subClass_maxCardinality = 
prove theorem_Cardinality_subClass_maxCardinality in cardinality
   options owl_resolution_prove_options

theorem_Cardinality_subClass_minCardinality = 
prove theorem_Cardinality_subClass_minCardinality in cardinality 
   options owl_resolution_prove_options

theorem_maxCardinality_one = prove theorem_maxCardinality_one in cardinality
   options owl_nat_prove_options

theorem_minCardinality_one = prove theorem_minCardinality_one in cardinality
   options owl_nat_prove_options

theorem_minCardinality_zero = prove theorem_minCardinality_zero in cardinality
   options owl_early_prove_options

testcase_cardinality_002 = prove testcase_cardinality_002 in cardinality_test
   options owl_nat_prove_options

theorem_Cardinality_two_not_same = prove theorem_Cardinality_two_not_same
   in cardinality_test
 %%  using definition_Cardinality, theorem_card_two_not_same, definition_image
   options owl_number_hyper_options


theorem_Cardinality_two_not_three = prove theorem_Cardinality_two_not_three 
   in cardinality_test
%   using definition_Cardinality, theorem_card_two_not_three, definition_image
   options   owl_nat_prove_options


theorem_Cardinality_not_same_zero = prove theorem_Cardinality_not_same_zero
   in cardinality_test
   options owl_number_resolution_options

theorem_Cardinality_not_same_one = prove theorem_Cardinality_not_same_one
   in cardinality_test
   options owl_number_hyper_options

theorem_minCardinality_not_same_n = prove theorem_minCardinality_not_same_n
   in cardinality_test
   options owl_number_hyper_options

theorem_Cardinality_not_same_n = prove theorem_Cardinality_not_same_n
   in cardinality_test
   options owl_number_hyper_options

theorem_maxCardinality_not_different_n = 
   prove theorem_maxCardinality_not_different_n
   in cardinality_test
   options owl_nat_prove_options

theorem_Cardinality_not_different_n = 
   prove theorem_Cardinality_not_different_n
   in cardinality_test
   options owl_number_hyper_options

theorem_Cardinality_two_Alldifferent =
   prove theorem_Cardinality_two_Alldifferent
   in cardinality_test
   options owl_prove_options


theorem_intersectionOf_Nothing = 
prove  theorem_intersectionOf_Nothing in owl_class_ops
   options owl_resolution_prove_options %%owl_early_prove_options

theorem_intersectionOf_Thing = 
prove  theorem_intersectionOf_Thing in owl_class_ops
   options owl_resolution_prove_options

theorem_unionOf_Nothing = prove  theorem_unionOf_Nothing in owl_class_ops
   options owl_resolution_prove_options

theorem_unionOf_Thing = prove  theorem_unionOf_Thing in owl_class_ops
   options owl_prove_options

theorem_complementOf_Nothing = 
prove theorem_complementOf_Nothing in owl_class_ops
   options owl_early_prove_options

theorem_complementOf_Thing = 
prove theorem_complementOf_Thing in owl_class_ops
   options owl_resolution_prove_options

theorem_complements_are_disjoint = 
prove theorem_complements_are_disjoint in owl_class_ops
   options owl_resolution_prove_options


test_complementOf_001 = prove test_complementOf_001 in owl_class_ops_test
   options owl_resolution_prove_options

lemma_oneOf_vs_addOne = 
prove lemma_oneOf_vs_addOne in owl_class_ops
   options owl_resolution_prove_options 
  
theorem_oneOf_vs_addOne = prove theorem_oneOf_vs_addOne in owl_class_ops
   options owl_resolution_prove_options


theorem_reflexivity_of_equivalentProperty =
prove theorem_reflexivity_of_equivalentProperty in properties
   options owl_early_prove_options

theorem_inverseOf_is_symmetric = 
prove theorem_inverseOf_is_symmetric in properties
   options owl_prove_options

testcase_FunctionalProperty_Manifest001_test =
prove testcase_FunctionalProperty_Manifest001_test in properties_test
   options owl_prove_options

testcase_FunctionalProperty_Manifest002_test =
prove testcase_FunctionalProperty_Manifest002_test in properties_test
   options owl_prove_options

theorem_inverseOf_Functional_is_InverseFunctional =
   prove theorem_inverseOf_Functional_is_InverseFunctional in properties
   options owl_prove_options

theorem_domain_and_range_of_symmetric_are_the_same =
   prove theorem_domain_and_range_of_symmetric_are_the_same in properties
   options owl_prove_options

example_chianti =
   prove example_chianti in properties
   options owl_prove_options

(*


% uncomment for consistency check:
contradictory = prove contradictory in owl
   options
   "(use-resolution t) (use-hyperresolution) (use-negative-hyperresolution) (use-paramodulation) (use-factoring) (use-literal-ordering-with-hyperresolution 'literal-ordering-p)(use-literal-ordering-with-negative-hyperresolution  'literal-ordering-p)(use-literal-ordering-with-paramodulation 'literal-ordering-p) (use-ac-connectives) (assert-supported t)(run-time-limit 7200) (use-code-for-numbers t) "


*)

