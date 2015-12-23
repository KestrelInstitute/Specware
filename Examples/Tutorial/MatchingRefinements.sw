(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Symbols = spec
  type Symbol = (Char | isUpperCase)
endspec


Symbols_Ref = morphism MatchingSpecs#Symbols ->
                       MatchingRefinements#Symbols {}

WordMatching0 = spec

import MatchingSpecs#Words
import MatchingSpecs#Messages
import MatchingSpecs#SymbolMatching

op word_matches_aux?(wrd: Word, msg: Message | length wrd <= length msg): Bool =
  case wrd of [] -> true
            | wsym::wrd1 ->
              let msym::msg1 = msg in
              if symb_matches?(wsym,msym)
                then word_matches_aux?(wrd1,msg1)
                else false
proof Isa "measure (\_lambda(wrd,msg). length wrd)" end-proof

proof Isa -verbatim
lemma word_matches_aux_p_nil[simp]:
  "word_matches_aux_p ([], msg) =
   list_all (Option__Option_P Symbol__Predicate) msg"
  by auto

lemma word_matches_aux_p_cons[simp]:
  "word_matches_aux_p (w#ws, msg) =
   (if length ws < length msg \_and 
       Symbol__Predicate w \_and 
       list_all Symbol__Predicate ws \_and 
       list_all (Option__Option_P Symbol__Predicate) msg
    then (\_exists m ms. msg = m#ms \_and
                  symb_matches_p (w,m) \_and
                  word_matches_aux_p (ws,ms))
    else regular_val)"
  apply (subst (1) word_matches_aux_p.simps)
  by (case_tac msg, auto simp del: word_matches_aux_p.simps)

declare word_matches_aux_p.simps[simp del]
end-proof

theorem word_matches_aux?_spec is
  fa(wrd: Word, msg: Message)
    length wrd <= length msg
      => word_matches_aux?(wrd, msg)
        = (fa(i:Nat) i < length wrd => symb_matches?(wrd@i, msg@i))
proof Isa fa wrd msg.
apply (rule allI)+
apply(induct_tac wrd msg rule: word_matches_aux_p.induct)
apply (case_tac wrda, auto)
apply (case_tac i, auto)
apply (case_tac msga, auto)
end-proof

op word_matches_at?(wrd: Word, msg: Message, pos: Nat): Bool =
  if pos + length wrd > length msg
    then false
    else word_matches_aux?(wrd, removePrefix(msg, pos))

endspec


WordMatching_Ref0 = morphism MatchingSpecs#WordMatching ->
                           WordMatching0 {}


WordMatching = WordMatching0[Symbols_Ref]


WordMatching_Ref =
 morphism MatchingSpecs#WordMatching ->
          MatchingRefinements#WordMatching {}


FindMatches0 = spec

import MatchingSpecs#WordMatching
import MatchingSpecs#Matches

op find_matches_aux(msg: Message, wrd: Word, pos: Nat): Option Nat =
  if pos + length wrd > length msg
    then None
    else if word_matches_at?(wrd,msg,pos)
           then Some pos
           else find_matches_aux(msg, wrd, pos + 1)
proof Isa "measure (\_lambda(msg,wrd,pos). length msg - pos)" end-proof


op find_matches(msg: Message, wrds: List Word): List Match =
  foldl (fn(mtchs,wrd) ->
           case find_matches_aux(msg,wrd,0)
             of Some pos ->
                {word = wrd, position = pos} :: mtchs
              | None -> mtchs)
    []  
    wrds

end-spec


FindMatches_Ref0 = morphism MatchingSpecs#FindMatches ->
                            FindMatches0 {}


FindMatches = FindMatches0[WordMatching_Ref]


FindMatches_Ref = morphism MatchingSpecs#FindMatches ->
                           MatchingRefinements#FindMatches {}

