(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


%% Name Supply

%% For each prefix, remember the number of the next id.
%% I.e. x0, x1, ...
%%      y0, y1, y2, ...

NameSupply qualifying
spec
  import /Library/Legacy/Utilities/State
  %import /Library/Legacy/DataStructures/StringMapSplay
  import /Library/Structures/Data/Maps/SimpleAsSTHarray

  type NameSupply = Ref (Map (String, Nat))

  op empty : () -> NameSupply
  op fresh : NameSupply -> String -> String

  def empty () =
    Ref emptyMap

  op addName(ns: NameSupply, nm: String, i: Nat): NameSupply =
    (ns := update(!ns, nm, i);
     ns)

  def fresh ns prefix =
    let n =
	case apply (! ns, prefix)
	  of None   -> 0
	   | Some n -> n in
    (ns State.:= update (! ns, prefix, n + 1);
     if n = 0 then prefix
       else prefix ^ "_" ^ show n)

endspec

