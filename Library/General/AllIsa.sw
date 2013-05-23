spec

%% Note: This spec imports all specs in this library for which we can
%% generate Isabelle files.  See the comments in All.sw for the
%% reasons why other files' Isabelle obligations fail to go through.

import Order
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
% I guess this has name clashes with FiniteMap (e.g., for type
%FMap.FMap).  TODO: However, with this uncommented, gen-obligs on AllIsa.sw
%currently crashes (because of the name clashes?).  gen-obligs on 
%FiniteMapAsFiniteSet by itself works fine:
%import FiniteMapAsFiniteSet
import Bit
import BitList
import Stream
import Sequence
import SizedNats

endspec
