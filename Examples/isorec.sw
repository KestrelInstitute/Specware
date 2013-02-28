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
