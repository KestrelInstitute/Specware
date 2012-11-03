spec

%% Some of the ...Ref specs below broke when I uncommented the remove,
%% foldi, and size operations in Maps.sw (needed to fix other errors).
%% I added refinements for those ops but haven't tested them. -Eric,
%% 10/11/12

%% This imports all the specs that get through Isabelle.  They may
%% contain sorrys but at least give legal Isabelle files.  (Actually,
%% this doesn't bother to import any morphisms, because their
%% obligations don't get imported.  So they should be tested
%% separately):
import AllIsa

import SetsAsLists#SetsAsLists
import SetsAsLists#M
import SetsAsMaps#SetsAsMaps
import SetsAsMaps#M
import SetsAsSTHTables0#SetsAsSTHTables0
import SetsAsSTHTables0#M
import SetsAsBagMaps#SetsAsBagMaps
import SetsAsBagMaps#M
import SetsAsBags#M

import MapsAsVectors#MapsAsVectors
import MapsAsVectors#M
import MapsAsSTHTables#MapsAsSTHTables
import MapsAsSTHTables#M
import MapsAsSets#M
import MapsAsLists
import MapsAsListsRef
import MapsAsBTVectors#MapsAsBTVectors
import MapsAsBTVectors#M

import BagsAsMaps
import BagsAsMaps#M
import BagsAsLists#BagsAsLists
import BagsAsLists#M

import StacksAsVectors#StacksAsVectors
import StacksAsVectors#S %TODO call this morphism M for consistency?

import POSet
import Extensions
import Collections
import StructuredTypes
end-spec
