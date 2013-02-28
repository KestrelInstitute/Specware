%Currently does not produce a legal spec.

A = spec
  type rec = {left:tree,right:tree}
  type tree =
    | leaf Nat
    | branch rec
  op total (t:tree) : Nat =
    case t of
    | leaf x -> x
    | branch therec -> (total therec.left) + (total therec.right)
end-spec

isos = spec
  import A
  type rec2 = {first:tree2, second:tree2}
  type tree2
  op isotree : tree -> tree2
  op ositree : tree2 -> tree
  op iso(therec:rec) : rec2 = {first=isotree(therec.left), second=isotree(therec.right)}
  op osi(therec:rec2) : rec = {left=ositree(therec.first), right=ositree(therec.second)}
end-spec

B = isos{isomorphism(iso,osi)}

%% transformed spec:

%% spec  
%% import A
 
%% type tree2
 
%% type rec2 = {first: tree2, second: tree2}
 
%% type tree' =  | branch rec2 | leaf Nat
%% op isotree (x: tree): tree' = case x
%%                                of branch y -> branch(iso y)
%%                                 | leaf y -> leaf y
%% op iso (therec: rec): rec2 = {first = isotree(therec.left), second = isotree(therec.right)}
%% op isotree: tree -> tree'
%% op ositree (x: tree'): tree = case x
%%                                of branch y -> branch(osi y)
%%                                 | leaf y -> leaf y
%% op osi (therec: rec2): rec = {left = ositree(therec.first), right = ositree(therec.second)}
%% op ositree: tree' -> tree
 
%% theorem generated.inverse_iso_is_osi is Function.inverse iso = osi
 
%% theorem generated.inverse_osi_is_iso is Function.inverse osi = iso
 
%% theorem generated.iso__osi is fa(x': rec2) iso(osi x') = x'
 
%% theorem generated.osi__iso is fa(x: rec) osi(iso x) = x
 
%% theorem generated.inverse_iso_is_osi is Function.inverse isotree = ositree
 
%% theorem generated.inverse_osi_is_iso is Function.inverse ositree = isotree
 
%% theorem generated.iso__osi is fa(x': tree') isotree(ositree x') = x'
 
%% theorem generated.osi__iso is fa(x: tree) ositree(isotree x) = x
%% op total' (t: tree'): Nat
%%   = case ositree t
%%      of leaf x -> x
%%       | branch therec -> (total'(isotree(therec.left)) + total'(isotree(therec.right)))
%% end-spec

