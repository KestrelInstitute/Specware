
%% Name Supply

%% For each prefix, remember the number of the next id.
%% I.e. x0, x1, ...
%%      y0, y1, y2, ...

NameSupply qualifying
spec
  %import State  	% ../utilities/state.sl
  import /Library/Legacy/DataStructures/StringMapSplay

  sort NameSupply = Ref (StringMap (Nat))

  op empty : () -> NameSupply
  op fresh : NameSupply -> String -> String

  def empty () =
    Ref StringMap.empty

  def fresh ns prefix =
    let n =
	case StringMap.find (! ns, prefix)
	  of None   -> 0
	   | Some n -> n in
    (ns State.:= StringMap.insert (! ns, prefix, n + 1);
     if n = 0 then prefix
       else prefix ^ "_" ^ toString n)

endspec

