spec

%% Some of the ...Ref specs below broke when I uncommented the remove,
%% foldi, and size operations in Maps.sw (needed to fix other errors).
%% I added refinements for those ops but haven't tested them. -Eric,
%% 10/11/12

import AllIsa
% These are in AllIsa:
%import Sets
%import Maps#Maps
%import Maps#Maps_extended

import SetsAsLists#SetsAsLists
import SetsAsLists#M
import SetsAsMaps#SetsAsMaps
import SetsAsMaps#M
import SetsAsSTHTables0#SetsAsSTHTables0
import SetsAsSTHTables0#M
import SetsAsBagMaps#SetsAsBagMaps
import SetsAsBagMaps#M
import SetsAsBags#SetsAsBags
import SetsAsBags#M
import SetsAsBagsRef

import MapsAsVectors#MapsAsVectors
import MapsAsVectors#M
import MapsAsSTHTables#MapsAsSTHTables
import MapsAsSTHTables#M
import MapsAsSets
import MapsAsSetsRef
import MapsAsLists
import MapsAsListsRef
import MapsAsBTVectors#MapsAsBTVectors
import MapsAsBTVectors#M

import Bags
import BagsAsMaps
import BagsAsMaps#M
import BagsAsLists#BagsAsLists
import BagsAsLists#M
import BagsAsListsRef

import Stacks
import StacksAsVectors#StacksAsVectors
import StacksAsVectors#S %TODO call this morphism M for consistency?

import POSet
import Extensions
import Collections
import Base
import StructuredTypes
end-spec
