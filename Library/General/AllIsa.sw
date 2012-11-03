spec

%% Note: This spec imports all specs in this library for which we can
%% generate Isabelle files.  See the comments in All.sw for the
%% reasons why other files' Isabelle obligations fail to go through.

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
% I guess this has name clashes with FiniteMap (e.g., for type
%FMap.FMap).  TODO: However, with this uncommented, gen-obligs on AllIsa.sw
%currently crashes (because of the name clashes?).  gen-obligs on 
%FiniteMapAsFiniteSet by itself works fine:
%import FiniteMapAsFiniteSet
import Bit
import BitList
import Stream
import Sequence

endspec
