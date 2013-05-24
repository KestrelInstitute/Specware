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

%% Note: These morphisms are tested separately (in test-specware.sh):
%%SetsAsLists#M
%%MapsAsListsRef % TODO rename?
%%BagsAsLists#M
%%SetsAsBags#M
%%BagsAsMaps#M

% These ultimately depend on quotients, which prevents getting them through Isabelle:
%import SetsAsLists#SetsAsLists %causes name clashes
%import MapsAsLists %leads to name clashes?
%import BagsAsLists#BagsAsLists  %% includes a quotient %causes name clashes?

%These still need to be triaged:

%import SetsAsSTHTables0#SetsAsSTHTables0 % leads to name clashes
%import SetsAsSTHTables0#M

%import MapsAsVectors#MapsAsVectors %casuses name clashes (on the MapVec ops?)
%import MapsAsVectors#M

import MapsAsSTHTables#MapsAsSTHTables
%import MapsAsSTHTables#M

import MapsAsBTVectors#MapsAsBTVectors
%import MapsAsBTVectors#M

import StacksAsVectors#StacksAsVectors
%import StacksAsVectors#M

import Extensions
import Collections
end-spec
