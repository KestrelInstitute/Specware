(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

% A naive category of specifications

% This is to be restructured. We are using a polymorphic category and this
% may change later. Similarly we use polymorphic maps.

% There is a question about qualifiers. The specs that make up
% MetaSlang are all qualified with different names. It is not
% clear how they should be qualified if at all.

% There should be a separate spec for SpecMorphisms as there
% is for Spec. The former should be a refinement of an
% abstract type.

spec
  import /Languages/MetaSlang/Specs/StandardSpec
  import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic
  import Cat qualifying /Library/Structures/Data/Categories/Cocomplete/Polymorphic

  type Morphisms = List Morphism
  type Morphism
  op dom : Morphism -> Spec
  op cod : Morphism -> Spec
  op compose : Morphism -> Morphism -> Morphism

% The following constructs an argument representing the category of specs
% and spec morphisms.  This takes an argument to avoid evaluation at load
% time and thereby avoids problems to do with the order of evaluation in
% the load file.  It would be reasonable to have arguments different from
% (). For example, we might provide a choice of pretty printing operations

  op specCat : () -> Cat.Cat (Spec, Morphism)

  % axiom dom is fa (m : Morphism) Cat.dom specCat m = dom m
  % axiom cod is fa (m : Morphism) Cat.cod specCat m = cod m
end-spec

