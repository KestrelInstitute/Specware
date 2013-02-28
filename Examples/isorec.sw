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

isorec = isos{isomorphism((iso,osi),(isotree,ositree))[unfold osi, unfold ositree]}

%% trace:
% * proc /Examples/isorec
% ;;; Elaborating transform at /Users/westfold/Specware/Examples/isorec#isorec
% ;;; Elaborating spec at /Users/westfold/Specware/Examples/isorec#isos
% ;;; Elaborating spec at /Users/westfold/Specware/Examples/isorec#A
% Domain QId's:
% rec
% tree
% adding definitions
% make derived ops
% make derived op definitions
% mdod: total' not opaque
% 1 non opaque ops to transform.
% rewriting ... 
%   {simplify (unfold Function.o, rewrite Function.id, unfold Option.mapOption, 
%              rewrite Option.isoOption, rewrite List.isoList, 
%              lr generated.inverse_iso_is_osi, lr generated.inverse_osi_is_iso, 
%              lr generated.iso__osi, lr generated.osi__iso, 
%              lr generated.inverse_iso_is_osi, lr generated.inverse_osi_is_iso, 
%              lr generated.iso__osi, lr generated.osi__iso); 
%    simplify (unfold Function.o, rewrite Function.id, unfold Option.mapOption, 
%              rewrite Option.isoOption, rewrite List.isoList, 
%              lr generated.inverse_iso_is_osi, lr generated.inverse_osi_is_iso, 
%              lr generated.iso__osi, lr generated.osi__iso, 
%              lr generated.inverse_iso_is_osi, lr generated.inverse_osi_is_iso, 
%              lr generated.iso__osi, lr generated.osi__iso, unfold osi, unfold ositree, 
%              rewrite total); 
%    simplify (unfold Function.o, rewrite Function.id, unfold Option.mapOption, 
%              unfold total, lr generated.inverse_iso_is_osi, 
%              lr generated.inverse_osi_is_iso, lr generated.iso__osi, 
%              lr generated.osi__iso, lr generated.inverse_iso_is_osi, 
%              lr generated.inverse_osi_is_iso, lr generated.iso__osi, 
%              lr generated.osi__iso, unfold osi, unfold ositree); 
%    SimpStandard}
%% transformed spec:

% spec  
% import A
 
 
% type tree2 =  | branch rec2 | leaf Nat
 
% type rec2 = {first: tree2, second: tree2}
% op iso (therec: rec): rec2 = {first = isotree(therec.left), second = isotree(therec.right)}
% op isotree: tree -> tree2
% op osi (therec: rec2): rec = {left = ositree(therec.first), right = ositree(therec.second)}
% op ositree: tree2 -> tree
% def isotree (x: tree): tree2 = case x
%                                 of branch y -> branch(iso y)
%                                  | leaf y -> leaf y
% def ositree (x: tree2): tree = case x
%                                 of branch y -> branch(osi y)
%                                  | leaf y -> leaf y
 
% theorem generated.inverse_iso_is_osi is Function.inverse iso = osi
 
% theorem generated.inverse_osi_is_iso is Function.inverse osi = iso
 
% theorem generated.iso__osi is fa(x': rec2) iso(osi x') = x'
 
% theorem generated.osi__iso is fa(x: rec) osi(iso x) = x
 
% theorem generated.inverse_iso_is_osi is Function.inverse isotree = ositree
 
% theorem generated.inverse_osi_is_iso is Function.inverse ositree = isotree
 
% theorem generated.iso__osi is fa(x': tree2) isotree(ositree x') = x'
 
% theorem generated.osi__iso is fa(x: tree) ositree(isotree x) = x
% op total' (t: tree2): Nat
%   = case t
%      of branch y -> (total'(y.first) + total'(y.second))
%       | leaf y -> y
% end-spec
