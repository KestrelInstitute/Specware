(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Demod qualifying
spec
 import ../AbstractSyntax/DeMod
 import RewriteRules

 type DemodRewriteRules  = 
      {unconditional : Demod RewriteRule,
       conditional   : Demod RewriteRule} 

 def addDemodRules(newRules: List RewriteRule,rules: Demod RewriteRule)
     : Demod RewriteRule =
   addRules(map (fn rl -> (rl.lhs,rl)) newRules,
	    rules)

 op  addUnconditionalRule:  RewriteRule * DemodRewriteRules -> DemodRewriteRules
 def addUnconditionalRule(rl,{unconditional,conditional}) =
   {unconditional = addRule(rl.lhs,rl,unconditional),
    conditional   = conditional}

 op  addConditionalRule:  RewriteRule * DemodRewriteRules -> DemodRewriteRules
 def addConditionalRule(rl,{unconditional,conditional}) =
   {unconditional = unconditional,
    conditional   = addRule(rl.lhs,rl,conditional)}

 op  addUnconditionalRules:  List RewriteRule * DemodRewriteRules -> DemodRewriteRules
 def addUnconditionalRules(rls,{unconditional,conditional}) =
   {unconditional = addDemodRules(rls,unconditional),
    conditional   = conditional}

 op  addConditionalRules:  List RewriteRule * DemodRewriteRules -> DemodRewriteRules
 def addConditionalRules(rls,{unconditional,conditional}) =
   {unconditional = unconditional,
    conditional   = addDemodRules(rls,conditional)}

 op  demodRules: RewriteRules -> DemodRewriteRules
 def demodRules rules =
   {unconditional = addDemodRules(rules.unconditional,Demod.empty),
    conditional   = addDemodRules(rules.conditional,Demod.empty)}

 op  mergeDemodRules: List DemodRewriteRules -> DemodRewriteRules
% def mergeDemodRules = 
%     fn [] -> {unconditional = empty,conditional = empty}
%      | [rules] -> rules
%      | rules1::rules2::rules ->
%        let rules1 = {unconditional = mergeRules(rules1.unconditional,
%						 rules2.unconditional),
%		       conditional   = mergeRules(rules1.conditional,
%						 rules2.conditional)}
%	in
%	mergeDemodRules(List.cons(rules1,rules))
 def mergeDemodRules = 
     fn [] -> {unconditional = empty,conditional = empty}
      | [rules] -> rules
      | rules1::rules2::rules ->
        let rules1 = {unconditional = addDemodRules(listRules rules1.unconditional,
						    rules2.unconditional),
		        conditional = addDemodRules(listRules rules1.conditional,
						    rules2.conditional)}
	in
	mergeDemodRules(rules1::rules)


endspec
