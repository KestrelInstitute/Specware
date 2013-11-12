spec
  import MergeRules/MetaProgram

% import MergeRules/Proofs
%  op MergeRules.printMergeRulesProof(pr:MSTerm -> String)(t:TraceTree):String =
%    let indent =  "  " in
% indent ^ "proof -\n" ^
% mkIsarProof pr None t (indent ^ "  ") ^
% indent ^ "(* Final Refinement Step *)\n" ^

% % indent ^ "(*\n" ^
% indent ^ "assume result : \"" ^ pr (traceResult t) ^ "\"\n" ^
% indent ^ "have noassumptions : True by simp\n" ^
% indent ^ "have precondition : \"~" ^ (pr (dnfToTerm (traceFailure t))) ^ "\" by simp\n" ^
% indent ^ "from ok noassumptions precondition result have ?thesis by simp\n" ^
% % indent ^ "*)\n" ^
% indent ^ "show ?thesis sorry\n" ^
% indent ^ "qed\n"
endspec


(*

       assume result : "if o1 h then o4 h_cqt = 0  else o4 h_cqt = 1"    
    have result' : "if o1 h then o4 h_cqt = 0 \<and> True else o4 h_cqt = 1 \<and> True" sorry
    have noassumptions : True by simp
      have precondition : "~False" by simp
      thm ok[OF noassumptions, OF precondition, OF result']
      show ?thesis
        apply (simp add: f1_def f2_def)
        apply (fact ok[OF noassumptions, OF precondition, OF result'])
      done

      *)