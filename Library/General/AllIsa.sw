spec

%% Note: This spec imports all specs in this library for which we can generate Isabelle files.

import Order
import FiniteMap
import Assert
import Type#Empty
import Type#Finite
import Type#Infinite
import Type#CountablyInfinite
import Type#UncountablyInfinite
import TwosComplementNumber
import TwosComplementNumber_Refinement
import TwosComplementNumber_ExecOps
import Relation
import OptionExt
import ListExt
import ListExt_Refinement
import ListExt_ExecOps
import IntegerExt
import IntegerExt_Refinement
import IntegerExt_ExecOps
import FunctionExt

%% This contains a quotient, which the Isabelle translator does not currently handle. -EWS
%%import FiniteSetAsList

%% These depend on FiniteSetAsList:
%% import FiniteSetAsListMorphism
%% import FiniteMapAsList
%% import FiniteMapAsListMorphism

%% These cause gen-obligs to crash:
%%import FiniteMapAsFiniteSet
%%import FiniteMapAsFiniteSetMorphism

import Bit
import BitList

%% these do not contain proofs yet:
%% import Rational
%% import Real

%% Proofs for these three do not currently work:
%% import Stream
%% import Sequence
%% import TimedTrace

endspec
