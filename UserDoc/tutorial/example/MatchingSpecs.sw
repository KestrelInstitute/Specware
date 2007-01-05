Symbols = spec
  type Symbol

  def use_support_list = 
    "(use-resolution t)
    (use-paramodulation t)
    (use-hyperresolution nil)
    (use-negative-hyperresolution nil)
    (assert-supported nil)
    (use-term-ordering :rpo)
    (use-default-ordering nil)
    (use-literal-ordering-with-resolution 'literal-ordering-a)
    (use-literal-ordering-with-paramodulation 'literal-ordering-a)
    (use-literal-ordering-with-hyperresolution 'literal-ordering-p)
    (use-literal-ordering-with-negative-hyperresolution 'literal-ordering-n)
    (declare-predicate-symbol '>= 2 :sort '(boolean number number)
    :alias 'gte)
    (declare-function '+ :any 
     :commutative t :associative t)
    (declare-function '- 2 :alias 'minusBinary)
    (declare-ordering-greaterp 'minusBinary '+ '|Nat.one| '1 '|Nat.zero| '0)   ;;  
    (declare-ordering-greaterp 'snark::< 'snark::=<)
    (declare-ordering-greaterp 'snark::> 'snark::=<)
    (declare-ordering-greaterp 'snark::gte  'snark::=<)
    (declare-ordering-greaterp 'snark::|List.length_Symbol| '+)
    (declare-ordering-greaterp 'snark::|List.length_Symbol| '1)
    (declare-ordering-greaterp 'snark::|List.length_Option_Symbol| '+)
    (declare-ordering-greaterp 'snark::|List.length_Option_Symbol| '1)
    (declare-ordering-greaterp 'snark::|embed_Cons| 'snark::|List.length|)
    (declare-ordering-greaterp 'snark::|embed_Cons| '+)
    (declare-ordering-greaterp 'snark::|embed_Cons| '1)
    (declare-ordering-greaterp 'snark::|List.cons| 'snark::|embed_Cons|)
    (run-time-limit 10)
"
endspec


Words = spec
  import Symbols
  type Word = List Symbol


 axiom length_word_gte_zero is
   fa(wrd:Word)
    0 <= length wrd

 axiom length_word_cons is
   fa(wsym:Symbol, wrd:Word)
    length(cons(wsym,wrd)) = length(wrd) + 1


endspec


Messages = spec
  import Symbols
  type Message = List (Option Symbol)


 axiom length_nthTail is
  fa(msg:Message,pos:Nat)
   pos <= length(msg)
   => length(nthTail(msg,pos)) = length(msg) - pos


  axiom length_cons is
   fa(msg1:Message, msym)
    length(cons(msym,msg1)) = length(msg1) + 1

 
endspec


SymbolMatching = spec
  import Symbols
  import MatchingRichardAxioms#MatchingRichardIntegerAxiomsSpec
  op symb_matches? : Symbol * Option Symbol -> Boolean
  def symb_matches?(s,os) = case os of Some s1 -> s = s1
                                     | None    -> true
endspec


WordMatching = spec

  import Words
  import Messages
  import SymbolMatching


  op word_matches_at? : Word * Message * Nat -> Boolean
  def word_matches_at?(wrd,msg,pos) =
      pos + length wrd <= length msg &&
      (fa(i:Nat) i < length wrd =>
         symb_matches?(nth(wrd,i), nth(msg,pos+i)))
  proof Isa word_matches_at?_Obligation_subsort
  apply(auto)
  end-proof

  proof Isa word_matches_at?_Obligation_subsort0
  apply(auto)
  end-proof

endspec


Matches = spec
  import Words
  type Match = {word : Word, position : Nat}
endspec


FindMatches = spec

  import WordMatching
  import Matches

  op find_matches : Message * List Word -> List Match
  axiom match_finding_lr1 is
        fa(msg,wrds,mtch)
          member(mtch,find_matches(msg,wrds)) =>
          member(mtch.word,wrds)

  axiom match_finding_lr2 is
        fa(msg,wrds,mtch)
          member(mtch,find_matches(msg,wrds)) =>
          word_matches_at?(mtch.word,msg,mtch.position)

  axiom match_finding_lr3 is
        fa(msg,wrds,mtch)
          member(mtch,find_matches(msg,wrds)) =>
          (fa(pos) word_matches_at?(mtch.word,msg,pos) =>
                   pos >= mtch.position)

  axiom match_finding_rl is
        fa(msg,wrds,mtch)
          member(mtch.word,wrds) &&
          word_matches_at?(mtch.word,msg,mtch.position) &&
          (fa(pos) word_matches_at?(mtch.word,msg,pos) =>
                   pos >= mtch.position) =>
          member(mtch,find_matches(msg,wrds))



endspec
