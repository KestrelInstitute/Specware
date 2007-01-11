MatchingRichardSpec = spec


import MatchingObligations#WordMatching0_Oblig
  
  axiom nat_zero_is_zero is
  Nat.zero = 0
  
  axiom nat_one_is_one is
  Nat.one = 1

  axiom plus_zero is
   fa(x:Integer)
    x + 0 = x

  conjecture minus_zero_thm is
    -0 = 0

  conjecture number_minus_zero_thm is
   fa(x:Integer)
    x - 0 = x


  conjecture number_minus_number_zero_thm is
   fa(x:Integer)
    x - x = 0

  axiom gt_implies_lte is
   fa(x:Integer, y:Integer)
    y > x  <=> x+1 <= y

  axiom lt_implies_lte is
   fa(x:Integer, y:Integer)
    x < y  <=> x+1 <= y

  axiom gte_implies_lte is 
   fa(x:Integer, y:Integer)
    y >= x  <=> x <= y

  axiom not_gt_is_lte is 
   fa(x:Integer, y:Integer)
    ~(x > y) => x <= y

  axiom diff_gte_zero_is_lte is
   fa(x:Integer, y:Integer)
    y - x >= 0  => x <= y

  axiom reduction is
   fa(x:Integer,a:Integer, b:Integer)
       x + a <= x + b
    => a <= b

    
%  conjecture one_reduction_theorem is
%   fa (a:Integer, b:Integer)
%       a + 1<= b + 1
%    => a  <=  b 

  axiom chaining is
   fa(x:Integer,a:Integer, b:Integer, c:Integer, d:Integer)
          a <= b + x
        & c + x <= d 
     => a + c <= d + b

  conjecture chaining_left_zero is
   fa(x:Integer,a:Integer, c:Integer, d:Integer)
     a <= x &&
     c + x <= d =>
     a + c <= d

   

 axiom length_Symbol_gte_zero is
   fa(wrd:Word)
    0 <= length wrd

 axiom length_nthTail is
  fa(msg:Message,pos:Nat)
   pos <= length(msg)
   => length(nthTail(msg,pos)) = length(msg) - pos

%% same as p5.
  conjecture word_matches_at?_Obligation_subsort_richard is
    fa(pos:Nat, msg:Message, wrd:Word)
        ~(pos + length wrd > length msg)
     => pos <= length msg

%% same as p6
  conjecture word_matches_at?_Obligation_subsort0_richard is
    fa(pos:Nat, msg:Message, wrd:Word) 
       ~(pos + length wrd > length msg) 
    => length wrd <= length(nthTail(msg,pos))

  conjecture length_cons_theorem is
   fa(msg1:Message, msym)
    length(cons(msym,msg1)) = length(msg1) + 1

%% same as p8
  conjecture word_matches_aux?_Obligation_subsort_2 is
    fa(wrd1:Word, wsym:Symbol, msg1:Message, msym)
        length(cons(wsym,wrd1)) <= length(cons(msym,msg1))
     => length wrd1 <= length msg1 

%  def use_support = 
%    "(use-resolution t)
%    (use-paramodulation t)
%    (use-hyperresolution nil)
%    (use-negative-hyperresolution nil)
%    (assert-supported nil)
%    (use-term-ordering :rpo)
%    (use-default-ordering nil)
%    (use-literal-ordering-with-resolution 'literal-ordering-a)
%    (use-literal-ordering-with-paramodulation 'literal-ordering-a)
%    (use-literal-ordering-with-hyperresolution 'literal-ordering-p)
%    (use-literal-ordering-with-negative-hyperresolution 'literal-ordering-n)
%    (declare-predicate-symbol '>= 2 :sort '(boolean number number)
%    :alias 'gte)
%    (print-rows-when-processed t)
%    (declare-function '+ :any 
%     :commutative t :associative t)
%    (declare-function-symbol 'snark::|embed_Cons_Symbol| 2
%     :sort '(snark::|List_Symbol|
%	     (1 snark::|Symbol|)
%	     (2 snark::|List_Symbol|))
%    )
%    (declare-function-symbol 'snark::|embed_Cons_Option_Symbol| 2
%     :sort '(snark::|List_Option_Symbol|
%	     (1 snark::|Symbol|)
%	     (2 snark::|List_Option_Symbol|))
%    )
%    (declare-ordering-greaterp '+ '0)
%    (declare-ordering-greaterp 'snark::< 'snark::=<)
%    (declare-ordering-greaterp 'snark::> 'snark::=<)
%    (declare-ordering-greaterp 'snark:: gte  'snark::=<)
%    (declare-ordering-greaterp 'snark::|embed_Cons_Symbol| '+)
%    (declare-ordering-greaterp 'snark::|embed_Cons_Symbol| '1)
%    (declare-ordering-greaterp 'snark::|embed_Cons_Option_Symbol| '+)
%    (declare-ordering-greaterp ''snark::|embed_Cons_Option_Symbol| '1)
%    "

  def use_support = 
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
    (declare-ordering-greaterp '+ '0)
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
    (declare-ordering-greaterp 'snark::|List.cons| 'snark::|embed_Cons|)"



endspec

contradictorySpec = spec
import MatchingRichardSpec

conjecture contradictory is
false 
endspec

%one_reduction_theorem =
%prove one_reduction_theorem
%in MatchingRichardSpec

minus_zero_thm =
prove minus_zero_thm
in MatchingRichardSpec
options use_support

number_minus_zero_thm =
prove number_minus_zero_thm
in MatchingRichardSpec
options use_support

number_minus_number_zero_thm =
prove number_minus_number_zero_thm
in MatchingRichardSpec
options use_support

chaining_left_zero =
prove chaining_left_zero
in MatchingRichardSpec

word_matches_at?_Obligation_subsort_richard =
prove word_matches_at?_Obligation_subsort_richard
in MatchingRichardSpec
options use_support

word_matches_at?_Obligation_subsort0_richard =
prove word_matches_at?_Obligation_subsort0_richard
in MatchingRichardSpec
options use_support

%% don't understand proof
length_cons_theorem =
prove  length_cons_theorem
in MatchingRichardSpec
options use_support

%% not proved
word_matches_aux?_Obligation_subsort_2 =
prove word_matches_aux?_Obligation_subsort_2
in MatchingRichardSpec
options use_support



p1 = prove symb_matches?_Obligation_exhaustive in MatchingObligations#SymbolMatching_Oblig


%% One of the word_matches_at?_Obligation is no longer generated because it is trivially true
p2 = prove word_matches_at?_Obligation_subsort  in MatchingObligations#WordMatching_Oblig
p3 = prove word_matches_at?_Obligation_subsort0 in MatchingObligations#WordMatching_Oblig

p5  = prove word_matches_at?_Obligation_subsort   in 
MatchingRichardSpec
options use_support
% MatchingObligations#WordMatching0_Oblig
p6  = prove word_matches_at?_Obligation_subsort0  in 
MatchingRichardSpec
% MatchingObligations#WordMatching0_Oblig
%p7  = prove word_matches_at?_Obligation_subsort1  in MatchingObligations#WordMatching0_Oblig
p8  = prove word_matches_aux?_Obligation_subsort  in MatchingObligations#WordMatching0_Oblig
p9  = prove word_matches_aux?_Obligation_termination in MatchingObligations#WordMatching0_Oblig
p10 = prove word_matches_aux?_Obligation_exhaustive in MatchingObligations#WordMatching0_Oblig

% currently missing from generated obligations:
% p11 = prove ... in MatchingObligations#WordMatching_Ref0_Oblig

p12 = prove find_matches_Obligation_exhaustive   in MatchingObligations#FindMatches0_Oblig
p13 = prove find_matches_aux_Obligation_subsort  in MatchingObligations#FindMatches0_Oblig
p14 = prove find_matches_aux_Obligation_termination in MatchingObligations#FindMatches0_Oblig

p15 = prove match_finding in MatchingObligations#FindMatches_Ref0_Oblig

%% uncomment for consistency check
 

%contradictory =
%prove contradictory in contradictorySpec
%options 
%"(use-resolution t)
%    (use-paramodulation t)
%    (use-factoring)
%    (use-literal-ordering-with-resolution nil)
%    (use-literal-ordering-with-paramodulation nil)
%    (use-term-ordering nil)
%    (use-default-ordering nil)
%    (assert-supported t)
%    (run-time-limit 600)
%    (use-ac-connectives)
%    (use-code-for-numbers nil)
%    (use-term-ordering :rpo)
%    (use-default-ordering nil)
%    (use-literal-ordering-with-resolution 'literal-ordering-a)
%    (use-literal-ordering-with-paramodulation 'literal-ordering-a)
%    (use-literal-ordering-with-hyperresolution 'literal-ordering-p)
%    (use-literal-ordering-with-negative-hyperresolution 'literal-ordering-n)
%    (declare-predicate-symbol '>= 2 :sort '(boolean number number)
%    :alias 'gte)
%    (declare-function '+ :any 
%     :commutative t :associative t)
%    (declare-ordering-greaterp '+ '0)
%    (declare-ordering-greaterp 'snark::< 'snark::=<)
%    (declare-ordering-greaterp 'snark::> 'snark::=<)
%    (declare-ordering-greaterp 'snark::gte  'snark::=<)
%    (declare-ordering-greaterp 'snark::|List.length_Symbol| '+)
%    (declare-ordering-greaterp 'snark::|List.length_Symbol| '1)
%    (declare-ordering-greaterp 'snark::|List.length_Option_Symbol| '+)
%    (declare-ordering-greaterp 'snark::|List.length_Option_Symbol| '1)
%    (declare-ordering-greaterp 'snark::|embed_Cons| 'snark::|List.length|)
%    (declare-ordering-greaterp 'snark::|embed_Cons| '+)
%    (declare-ordering-greaterp 'snark::|embed_Cons| '1)
%    (declare-ordering-greaterp 'snark::|List.cons| 'snark::|embed_Cons|)"