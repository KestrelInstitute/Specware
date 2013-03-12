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

% These morphisms get through Isabelle (modulo sorrys).  Importing
% them seems to cause them to be processed.  However, obligations of
% imported morphisms seem to not be imported into Isabelle specs.  So
% their Isabelle proofs have to be tested separately.  TODO, What does
% it even mean to import a morphism?

import MapsAsSets#M
import SetsAsMaps#M
import SetsAsBagMaps#M

% These ultimately depend on quotient, which prevents getting them through Isabelle:
import SetsAsLists#SetsAsLists
import SetsAsLists#M
import MapsAsLists
import MapsAsListsRef
import BagsAsLists#BagsAsLists  %% includes a quotient
import BagsAsLists#M

%These have incorrect Isabelle obligations (which give errors):
import SetsAsBags#M
import BagsAsMaps#M

%These still need to be triaged:

import SetsAsSTHTables0#SetsAsSTHTables0
import SetsAsSTHTables0#M

import MapsAsVectors#MapsAsVectors
import MapsAsVectors#M

import MapsAsSTHTables#MapsAsSTHTables
import MapsAsSTHTables#M

import MapsAsBTVectors#MapsAsBTVectors
import MapsAsBTVectors#M

import StacksAsVectors#StacksAsVectors
import StacksAsVectors#M

import POSet
import Extensions
import Collections
import StructuredTypes
end-spec
