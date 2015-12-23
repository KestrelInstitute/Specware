(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

spec

%% Note: This spec imports all specs in this library for which we can
%% generate Isabelle files.  See the comments in All.sw for the
%% reasons why other files' Isabelle obligations fail to go through.

import Order
import FiniteSet
import FiniteMap
import Assert

%% Note that several of these declare the same type, X, so 'qualifying' is used to prevent name clashes:
import (Empty qualifying Type#Empty)
import (Finite qualifying Type#Finite)
import (Infinite qualifying Type#Infinite)
%% Without the use of 'qualifying', importing both of these would likely result in an inconsistent spec:
import (CountablyInfinite qualifying Type#CountablyInfinite)
import (UncountablyInfinite qualifying Type#UncountablyInfinite)

import TwosComplementNumber
%%import TwosComplementNumber_Refinement %This is a morphism (with trivial proof obligations).
import TwosComplementNumber_ExecOps
import Relation
import OptionExt
import ListExt
import ListFacts
%%import ListExt_Refinement %This is a morphism (with trivial proof obligations)..
import ListExt_ExecOps
import IntegerExt
%% import IntegerExt_Refinement %This is a morphism (with trivial proof obligations)..
import IntegerExt_ExecOps
import FunctionExt
import Bit
import BitList
import Stream
import Sequence
import SizedNats
import SizedInts

% This has name clashes with FiniteMap (e.g., for type FMap.FMap), so
% we can't include it here but have to test it separately (in
% test-specware.sh):

%import FiniteMapAsFiniteSet

endspec
