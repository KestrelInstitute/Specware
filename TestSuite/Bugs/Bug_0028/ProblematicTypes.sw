spec

  %% The following type definition causes a segmentation violation!

  type Filename = String

  %% Three other types from 
  %%   ./Languages/MetaSlang/Specs/Position.sw
  %% have the same problem:

  type LineColumn = Nat
  type LineColumnByte = Nat
  type Position = Nat

  %% findTheSort for any of these returns (:|Some| :|Some| :|None|)
  %% which makes addSort fail in a call to listUnion

  %% The default spec sort map seems to be a hash table plus four entries,
  %%  one for each of the above sorts.  Very curious.

endspec
