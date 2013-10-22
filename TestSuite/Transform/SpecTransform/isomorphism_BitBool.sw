% ======================================================================
% Specs
% ======================================================================

Bit = B qualifying spec
 type Bit = | B0 | B1
 op not (b:Bit) : Bit = case b of B0 -> B1 | B1 -> B0
 theorem notnot is 
   fa (b: Bit) not (not b) = b
end-spec

Bit2Bool_Step1 = B qualifying spec
 import Bit
 op toBool : Bijection (Bit, Bool)   = fn b -> case b of B0 -> false | B1 -> true
 op fromBool : Bijection (Bool, Bit) = fn b -> case b of false -> B0 | true  -> B1
end-spec

% ======================================================================
% spec transform 'isomorphism'
%   op SpecTransform.isomorphism (spc: Spec) (newOptQual : Option String)
%                                (iso_qid_prs: List(QualifiedId * QualifiedId))
%                                (extra_rules: List RuleSpec):  SpecCalc.Env Spec
% ======================================================================

% No op with name: toBool
TF_Bad_1 = transform Bit2Bool_Step1 by {isomorphism "new_*" (toBool, fromBool)}
TF_Bad_2 = Bit2Bool_Step1 {isomorphism "new_*" (toBool, fromBool)}

% ERROR: in transform: Expected argument: List Rule (at [B.notnot])
TF_Bad_3 = transform Bit2Bool_Step1 by {isomorphism "new_*" (B.toBool, B.fromBool) [B.notnot] }

% WARNING: Rule-shaped theorem notnot unable to extract any rules!
% FIXME??? Should this be an error instead of a warning?
TF_Bad_4 = transform Bit2Bool_Step1 by {isomorphism "new_*" (B.toBool, B.fromBool) [lr notnot] }

TF_Good_1 = transform Bit2Bool_Step1 by {isomorphism "new_*" [(B.toBool, B.fromBool)] []}
TF_Good_2 = Bit2Bool_Step1 {isomorphism "new_*" [(B.toBool, B.fromBool)] []}

% singleton list argument can omit brackets: (B.toBool, B.fromBool) - second argument iso_qid_prs: List(QualifiedId * QualifiedId))
TF_Good_3 = transform Bit2Bool_Step1 by {isomorphism "new_*" (B.toBool, B.fromBool) []}
                                               
% empty list argument can be omitted - last argument extra_rules: List RuleSpec
TF_Good_4 = transform Bit2Bool_Step1 by {isomorphism "new_*" (B.toBool, B.fromBool)}

% optional argument can be in brackets
% a string does not need string quotes if it is an identifier
TF_Good_5 = transform Bit2Bool_Step1 by {isomorphism [new_*] (B.toBool, B.fromBool)}

% a string does not need string quotes if it is an identifier
TF_Good_6 = transform Bit2Bool_Step1 by {isomorphism new_* (B.toBool, B.fromBool)}

% without the optional argument; no extra_rules
TF_Good_7 = transform Bit2Bool_Step1 by {isomorphism (B.toBool, B.fromBool)}

