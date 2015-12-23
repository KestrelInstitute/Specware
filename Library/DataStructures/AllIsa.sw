(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

%% This spec imports all the specs that get through Isabelle.  They may
%% contain sorrys but at least give legal Isabelle files.  (Actually,
%% this doesn't bother to import any morphisms, because their
%% obligations don't get imported.  So they should be tested
%% separately):

spec
  import Sets
  import Maps
  import Bags
  import Maps#Maps_extended
  import Stacks
  import STBase
  import StructuredTypes

  import SetsAsBags#SetsAsBags
  import SetsAsMaps#SetsAsMaps
  import BagsAsMaps#BagsAsMaps

  import MapsAsSTHTables#MapsAsSTHTables
  import POSet
  import Extensions
  import Collections

%% The proofs of these go through, but they would cause name clashes
%% if they were imported here.  So they are tested separately in
%% test-specware.sh:
%% import MapsAsVectors#MapsAsVectors % name clashes on the MapVec ops?
%% import MapsAsSets#MapsAsSets
%% import SetsAsBagMaps#SetsAsBagMaps
%% import StacksAsCoproducts
%% import StacksAsLists

%% Note: The proofs for these morphisms go through (modulo many sorrys!).  They are tested in test-specware.sh:
%%MapsAsSets#M
%%SetsAsMaps#M
%%SetsAsBagMaps#M
%%SetsAsBags#M
%%BagsAsMaps#M
%%StacksAsCoproducts#M
%%StacksAsLists#M
%%MapsAsSTHTables#M
%%MapsAsVectors#M

end-spec
