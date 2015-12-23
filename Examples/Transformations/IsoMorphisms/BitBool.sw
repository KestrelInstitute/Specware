(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Bit = B qualifying spec
 type Bit = | B0 | B1
 op not (b:Bit) : Bit = case b of B0 -> B1 | B1 -> B0
end-spec

Step1 = spec
 import Bit
 op toBool : Bijection (Bit, Bool)   = fn b -> case b of B0 -> false | B1 -> true
 op fromBool : Bijection (Bool, Bit) = fn b -> case b of false -> B0 | true  -> B1
end-spec

BitBool0 = transform Step1 by {isomorphism "new_*" [(toBool, fromBool)][]}
BitBool = transform Step1 by {trace on; isomorphism "new_*" (toBool, fromBool)}
BitBool1 = transform Step1 by {isomorphism [new_*] (toBool, fromBool)}
BitBool2 = transform Step1 by {isomorphism (toBool, fromBool)}
BitBool3 = transform Step1 by {isomorphism new_* (toBool, fromBool)}

(* Signature of isomorphism function is:
 op SpecTransform.isomorphism (spc: Spec) (newOptQual : Option String)
                              (iso_qid_prs: List(QualifiedId * QualifiedId))
                              (extra_rules: List RuleSpec):  SpecCalc.Env Spec

BitBool0 uses the most general form with a string argument applied (newOptQual),
a list of pairs of QualifiedIds (iso_qid_prs)
and an empty list of rules (extra_rules)
BitBool is the simples form with a newOptQual supplied, 
a singleton list does not require a brackets,
an empty list can be omitted.
BitBool1 shows how an optional argument can be in brackets and a string does not need 
string quotes if it is an identifier.
*)