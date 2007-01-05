MatchingRichardIntegerAxiomsSpec = spec


%import MatchingObligations#WordMatching0_Oblig
  
   

  axiom nat_zero_is_zero is
  Nat.zero = 0

%% added to Nat.sw    
  axiom nat_one_is_one is
  Nat.one = 1

%% in prover base
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

%  axiom plus_monotonic is
%    fa(x:Integer, y:Nat)
%     x <= x + y
   

  axiom minus_migration is
    fa(x:Integer, y:Integer, z:Integer)
     x - z + y = x + y - z
     
  axiom gt_implies_lte is
   fa(x:Integer, y:Integer)
    y > x  <=> x + 1 <= y

  axiom lt_implies_lte is
   fa(x:Integer, y:Integer)
    x < y  <=> x + 1 <= y

  axiom not_lte_implies_lte_plus_1 is
   fa(x:Integer, y:Integer)
   ~(y <= x) => x + 1 <= y

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

  conjecture reduction_left_zero is
   fa(x:Integer, b:Integer)
       x <= x + b
    => 0 <= b

  conjecture reduction_right_zero is
   fa(x:Integer,a:Integer)
       x + a <= x
    => a <= 0

  conjecture integer_minus_zero is
    fa(x:Integer) x - 0 = x

  conjecture minus_elimination is
   fa(x:Integer, y:Integer, z:Integer)
       (x - z <= y) =>  x <= y + z

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
    (declare-function '- 2 :alias 'minusBinary)
    (declare-ordering-greaterp '+ 'minusBinary '0)
    (declare-ordering-greaterp 'snark::< 'snark::=<)
    (declare-ordering-greaterp 'snark::> 'snark::=<)
    (declare-ordering-greaterp 'snark::gte  'snark::=<)
    (declare-ordering-greaterp 'snark::|Nat.lte|  'snark::=<)
    (assert-rewrite '(= snark::|Nat.zero| 0) :name 'nat_zero_is_0_rewrite)
    (run-time-limit 60)
"


endspec
   

% axiom length_Symbol_gte_zero is
%   fa(wrd:Word)
%    0 <= length wrd

% axiom length_nthTail is
%  fa(msg:Message,pos:Nat)
%   pos <= length(msg)
%   => length(nthTail(msg,pos)) = length(msg) - pos

%  axiom length_cons is
%   fa(msg1:Message, msym)
%    length(cons(msym,msg1)) = length(msg1) + 1

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



contradictorySpec = spec
import MatchingRichardIntegerAxiomsSpec

conjecture contradictory is
false 
endspec

%one_reduction_theorem =
%prove one_reduction_theorem
%in MatchingRichardIntegerAxiomsSpec

%minus_zero_thm =
%prove minus_zero_thm
%in MatchingRichardIntegerAxiomsSpec
%options use_support

%number_minus_zero_thm =
%prove number_minus_zero_thm
%in MatchingRichardIntegerAxiomsSpec
%options use_support

%number_minus_number_zero_thm =
%prove number_minus_number_zero_thm
%in MatchingRichardIntegerAxiomsSpec
%options use_support

%chaining_left_zero =
%prove chaining_left_zero
%in MatchingRichardIntegerAxiomsSpec

%minus_elimination =
%prove minus_elimination 
%in MatchingRichardIntegerAxiomsSpec
%options use_support

%p6_test_case =
%prove p6_test_case
%in MatchingRichardIntegerAxiomsSpec
%options use_support


%% don't understand proof
%length_cons_theorem =
%prove  length_cons_theorem  % made axiom
%in MatchingRichardAxiomsSpec
%options use_support


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