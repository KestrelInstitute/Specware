(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

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

% These ultimately depend on quotients, which prevents getting them through Isabelle:
%import SetsAsLists#SetsAsLists %causes name clashes
%import MapsAsLists %leads to name clashes?
%import BagsAsLists#BagsAsLists  %% includes a quotient %causes name clashes?

%These still need to be triaged:

%% This causes gen-obligs to crash:
%import SetsAsSTHTables0#SetsAsSTHTables0 % leads to name clashes
%import SetsAsSTHTables0#M

import MapsAsBTVectors#MapsAsBTVectors
%import MapsAsBTVectors#M

import StacksAsVectors#StacksAsVectors
%import StacksAsVectors#M

%% The proofs of these morphisms do not go through, due to the use of quotients:
%%SetsAsLists#M
%%MapsAsLists#M
%%BagsAsLists#M


end-spec
