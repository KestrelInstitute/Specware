% ======================================================================
% Specs
% ======================================================================

A = spec
import /Library/DataStructures/Extensions
op [a,b,c,d] isoMap: Bijection(a,b) -> Bijection(c,d) -> Bijection(Map(a, c), Map(b, d)) =
  fn iso_elem1 -> fn iso_elem2 -> foldi (fn (x, y, new_m) -> update new_m (iso_elem1 x) (iso_elem2 y)) empty_map

theorem isoMap_over_update is [a,b,c,d]
  fa(m: Map(a,b), x:a, y:b, el_iso1: (a -> c), el_iso2: b -> d)
    isoMap el_iso1 el_iso2 (update m x y) = update (isoMap el_iso1 el_iso2 m) (el_iso1 x) (el_iso2 y)

theorem isoMap_over_empty_map is [a,b,c,d]
  fa(el_iso1: a -> c, el_iso2: b -> d)
    isoMap el_iso1 el_iso2 (empty_map: Map(a,b)) = (empty_map: Map(c,d))

type Nat_+ = {i: Int | i >= -1 }

type Port = Nat

type R = {A: Port,
          B: Map(Nat, Option Port),
          C: Option(Option Port)}

op makeR(): R = {A = 1, B = update empty_map 0 (Some 9), C = Some(Some 7)}

op iso1: Bijection(Option Port, Nat_+) =
  fn oprt -> (case oprt of
                | None -> -1
                | Some p -> p)

op osi1: Bijection(Nat_+, Option Port) =
  fn n -> (if n<0 then None else Some n)

end-spec

B = spec
import /Library/DataStructures/Maps
op [a,b,c,d] isoMap: Bijection(a,b) -> Bijection(c,d) -> Bijection(Map(a, c), Map(b, d)) =
  fn iso_elem1 -> fn iso_elem2 -> foldi (fn (x, y, new_m) -> update new_m (iso_elem1 x) (iso_elem2 y)) empty_map

theorem isoMap_over_update is [a,b,c,d]
  fa(m: Map(a,b), x:a, y:b, el_iso1: (a -> c), el_iso2: b -> d)
    isoMap el_iso1 el_iso2 (update m x y) = update (isoMap el_iso1 el_iso2 m) (el_iso1 x) (el_iso2 y)

theorem isoMap_over_empty_map is [a,b,c,d]
  fa(el_iso1: a -> c, el_iso2: b -> d)
    isoMap el_iso1 el_iso2 (empty_map: Map(a,b)) = (empty_map: Map(c,d))

type Nat_+ = {i: Int | i >= -1 }

type Port = Nat

type R = {A: Option Port,
          B: Map(Option Port, Nat),
          C: Option(Option Port),
          D: Map(Option Port, Option Port)}

op makeR(): R = {A = Some 1, B = update empty_map (Some 0) 9, C = Some(Some 7), D = update empty_map (Some 0) (Some 9)}

op testR(r: R): Bool =
  (case r.A of Some _ -> true | None -> false)  && (case r.C of Some x -> embed? None x | None -> false)

op iso1: Bijection(Option Port, Nat_+) =
  fn oprt -> (case oprt of
                | None -> -1
                | Some p -> p)

op osi1: Bijection(Nat_+, Option Port) =
  fn n -> (if n<0 then None else Some n)

end-spec

% ======================================================================
% spec transform 'isomorphism'
%   op SpecTransform.isomorphism (spc: Spec) (newOptQual : Option String)
%                                (iso_qid_prs: List(QualifiedId * QualifiedId))
%                                (extra_rules: List RuleSpec):  SpecCalc.Env Spec
% ======================================================================

TF_Good_1 = transform A by {isomorphism (iso1, osi1) [lr *.isoMap_over_update, lr *.isoMap_over_empty_map]}

TF_Good_2 = transform B by {isomorphism (iso1, osi1) [lr *.isoMap_over_update, lr *.isoMap_over_empty_map]}
