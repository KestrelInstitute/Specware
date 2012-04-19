Seq qualifying spec

import Stream

proof Isa -hook lemmas_for_earlier_libraries end-proof

(* This spec defines a notion of sequences, which can be finite or infinite. We
use a sum of lists (from the Specware base library) and streams to model
sequences. *)

type Seq a = | fin List a | inf Stream a

(* Sequences are isomorphic to maps whose domain is a contiguous subset of the
natural numbers starting at 0 and either stopping just before some natural
number n (finite sequence of length n) or never stopping (infinite sequence). *)

type SeqMap a = {m: Map(Nat,a) | fa(i:Nat) m definedAt i =>
                                           (fa(j:Nat) j < i => m definedAt j)}

op seq : [a] Bijection (SeqMap a, Seq a) = fn m: SeqMap a ->
  if (ex(i:Nat) m undefinedAt i) then fin (list (fn i:Nat -> m i))
                                 else inf (fn i:Nat -> m @ i)


op seq_1 : [a] Bijection (Seq a, SeqMap a) = inverse seq

proof Isa -hook seq_simps end-proof

% finite and infinite sequences (corresponding to lists and streams):

op   finite? : [a] Seq a -> Bool = embed? fin
op infinite? : [a] Seq a -> Bool = embed? inf

theorem infinite_inf_simp is [a]    fa (s: Stream a) infinite? (inf s)
theorem infinite_fin_simp is [a]    fa (l: List a)   infinite? (fin l) = false
theorem finite_inf_simp is [a]      fa (s: Stream a) finite? (inf s)   = false
theorem finite_fin_simp is [a]      fa (l: List a)   finite? (fin l)
theorem infinite_not_finite is [a]  fa (s: Seq a)  infinite? s = ~(finite? s)


type FinSeq a = (Seq a |   finite?)
type InfSeq a = (Seq a | infinite?)

op [a] list   (s: FinSeq a) : List   a = let fin l = s in l
op [a] stream (s: InfSeq a) : Stream a = let inf t = s in t

% number of elements in finite sequence:

op [a] length (s:FinSeq a) : Nat = length (list s)

theorem length_fin_simp is [a]     fa (l: List a)  length (fin l) = length l

% true iff sequence has length n:

op [a] ofLength? (n:Nat) (s: Seq a) : Bool =
  finite? s && length s = n

theorem ofLength_fin_simp is [a]   
  fa (l: List a, n:Nat)   ofLength? n (fin l) = (length l = n)
theorem ofLength_inf_simp is [a]   
  fa (s: Stream a, n:Nat) ofLength? n (inf s) = false


% true iff n is less than (or equal to) length of sequence:

op [a] <_length (n:Nat, s: Seq a) infixl 20 : Bool =
  infinite? s || n < length s

theorem e_lt_length_inf_simp is [a]   
   fa (s: Stream a, n:Nat) n <_length inf s
theorem e_lt_length_fin_simp is [a]   
   fa (l: List a, n:Nat) (n <_length fin l) =  (n < length l)


op [a] <=_length (n:Nat, s: Seq a) infixl 20 : Bool =
  infinite? s || n <= length s

theorem e_lt_eq_length_inf_simp is [a]   
   fa (s: Stream a, n:Nat) n <=_length inf s
theorem e_lt_eq_length_fin_simp is [a]   
   fa (l: List a, n:Nat) (n <=_length fin l) =  (n <= length l)


% access element at index i (@@ is a totalization of op @, for finite
% sequences):

op [a] @ (s: Seq a, i:Nat | i <_length s) infixl 30 : a =
  case s of
  | fin l -> l @ i
  | inf t -> t   i

op [a] @@ (s: Seq a, i:Nat) infixl 30 : Option a =
  case s of
  | fin l -> l @@ i
  | inf t -> Some (t i)

% empty sequence:

op empty : [a] Seq a = fin []

op [a] empty? (s: Seq a) : Bool = (s = empty)
proof Isa [simp] end-proof

% non-empty sequences:

op nonEmpty? : [a] Seq a -> Bool = ~~ empty?

theorem empty_p_fin is [a]        fa (l: List a)   empty? (fin l) = (l = [])
theorem empty_p_inf is [a]        fa (s: Stream a) empty? (inf s) = false 
theorem nonEmpty_p_fin is [a]     fa (l: List a)   nonEmpty? (fin l) = (l ~= [])
theorem nonEmpty_p_inf is [a]     fa (s: Stream a) nonEmpty? (inf s) 
theorem nonEmpty?_alt_def is [a]  fa (s:Seq a) nonEmpty? s = (s ~= empty)


type Seq1 a = (Seq a | nonEmpty?)

% non-empty finite sequences:

type FinSeq1 a = (FinSeq a | nonEmpty?)

% singleton sequence:

op [a] single (x:a) : Seq a = fin [x]

op [a] theElement (s: Seq a | ofLength? 1 s) : a = the(x:a) s = single x

theorem theElement_single is [a]        fa (x: a) theElement (fin [x]) = x


% membership:

op [a] in? (x:a, s: Seq a) infixl 20 : Bool =
  case s of
  | fin l -> x in? l
  | inf t -> x in? t

op [a] nin? (x:a, s: Seq a) infixl 20 : Bool = ~ (x in? s)

% set of elements of a sequence:

op [a] toSet (s:Seq a) : Set a = fn x:a -> x in? s

% theorem toSet_fin is [a]        fa (l: List a)   toSet (fin l) = set l
% theorem toSet_inf is [a]        fa (s: Stream a) toSet (inf s) = range s 
% ---------------------------------------------------------------------- 
% In SpecWare we have no equivalent to Isabelle's "set l" or "range f"
% use verbatim Isabelle lemmas instead 

proof Isa -hook toSet_simps end-proof


% subsequence starting from index i of length n (note that if s is finite
% and n is 0 then i could be length(s), even though that is not a valid index
% in the sequence):

op [a] subFromLong (s: Seq a, i:Nat, n:Nat | i + n <=_length s) : Seq a =
  case s of
  | fin l -> fin (subFromLong (l, i, n))
  | inf t -> fin (subFromLong (t, i, n))

% subsequence from index i (inclusive) to index j (exclusive); if i = j then we
% could have i = j = length l, even though those are not valid indices:

op [a] subFromTo (s: Seq a, i:Nat, j:Nat | i <= j && j <=_length s) : Seq a =
  case s of
  | fin l -> fin (subFromTo (l, i, j))
  | inf t -> fin (subFromTo (t, i, j))

% extract/remove prefix/suffix of length n:

op [a] prefix (s: Seq a, n:Nat | n <=_length s) : Seq a =
  subFromLong (s, 0, n)

op [a] suffix (s: FinSeq a, n:Nat | n <= length s) : Seq a =
  subFromLong (s, length s - n, n)


% ------------------------------------------------------------------------------
proof Isa -verbatim

(*** convert into SpecWare theorems later ***)

lemma Seq__prefix_fin:
  "Seq__prefix (Seq__Seq__fin l, n)
   = Seq__Seq__fin (List__subFromLong(l, 0, n))"
 by (simp add: Seq__prefix_def)
lemma Seq__prefix_fin2 [simp]:
  "\<lbrakk>n \<le> length l\<rbrakk> 
  \<Longrightarrow> Seq__prefix (Seq__Seq__fin l, n) = Seq__Seq__fin (take n l)"
 by (simp add: List__prefix__def Seq__prefix_fin)
lemma Seq__prefix_fin_whole [simp]:
  "\<lbrakk>length l = n\<rbrakk>
  \<Longrightarrow>  Seq__prefix (Seq__Seq__fin l, n) = Seq__Seq__fin l"
 by (drule sym, simp add: List__subFromLong_whole)
lemma Seq__prefix_fin_whole2 [simp]:
  "\<lbrakk>Seq__finite_p s; Seq__length s = n\<rbrakk> 
  \<Longrightarrow>  Seq__prefix (s, n) = s"
 by (case_tac s, simp_all)
lemma Seq__prefix_fin_whole3 [simp]:
  "\<lbrakk>Seq__ofLength_p n s\<rbrakk> 
  \<Longrightarrow>  Seq__prefix (s, n) = s"
 by (simp add: Seq__ofLength_p_def)
lemma Seq__prefix_inf [simp]:
  "Seq__prefix (Seq__Seq__inf fun, n)
   = Seq__Seq__fin (Stream__subFromLong(fun, 0, n))"
 by (simp add: Seq__prefix_def)

lemma Seq__suffix_fin:
  "Seq__suffix (Seq__Seq__fin l, n)
   = Seq__Seq__fin (List__suffix(l,n))"
 by (simp add: Seq__suffix_def List__suffix_def)
lemma Seq__suffix_fin_whole [simp]:
  "\<lbrakk>length l = n\<rbrakk>
  \<Longrightarrow>  Seq__suffix (Seq__Seq__fin l, n) = Seq__Seq__fin l"
 by (drule sym, simp add: Seq__suffix_fin List__suffix_def List__subFromLong_whole)
lemma Seq__suffix_fin_whole2 [simp]:
  "\<lbrakk>Seq__finite_p s; Seq__length s = n\<rbrakk> \<Longrightarrow>  Seq__suffix (s, n) = s"
 by (case_tac s, simp_all)
lemma Seq__suffix_fin_whole3 [simp]:
  "\<lbrakk>Seq__ofLength_p n s\<rbrakk> \<Longrightarrow>  Seq__suffix (s, n) = s"
 by (simp add: Seq__ofLength_p_def)
lemma Seq__suffix_fin_empty [simp]:
  "Seq__suffix (Seq__Seq__fin l, 0) = Seq__empty"
 by (simp add: Seq__suffix_fin Seq__empty_def length_0_conv [symmetric]
          del: length_0_conv)
lemma Seq__suffix_fin_empty2 [simp]:
  "\<lbrakk>Seq__finite_p s\<rbrakk> \<Longrightarrow>  Seq__suffix (s, 0) = Seq__empty"
 by (case_tac s, simp_all)

end-proof
% ------------------------------------------------------------------------------


op [a] removePrefix (s: Seq a, n:Nat | n <=_length s) : Seq a =
  case s of
  | fin l -> fin (removePrefix (l, n))
  | inf t -> inf (removePrefix (t, n))

op [a] removeSuffix (s: FinSeq a, n:Nat | n <= length s) : Seq a =
  prefix (s, length s - n)


% ------------------------------------------------------------------------------
proof Isa -verbatim

lemma Seq__removePrefix_fin_empty [simp]:
  "\<lbrakk>length l = n\<rbrakk>
  \<Longrightarrow>  Seq__removePrefix (Seq__Seq__fin l, n) = Seq__empty"
 by (simp add: Seq__empty_def)
lemma Seq__removePrefix_inf [simp]:
  "Seq__removePrefix (Seq__Seq__inf fun, n)
   = Seq__Seq__inf (\<lambda>i. fun (i + n))"
 by (simp add: Stream__removePrefix_def)
lemma Seq__removePrefix_whole [simp]:
  "Seq__removePrefix (s, 0) = s"
 by (case_tac s, simp_all add: Stream__removePrefix_def)

lemma Seq__removeSuffix_fin [simp]:
  "Seq__removeSuffix (Seq__Seq__fin l, n)
   = Seq__Seq__fin (take (length l - n) l)"
 by (simp add: Seq__removeSuffix_def List__prefix__def)
lemma Seq__removeSuffix_fin_whole [simp]:
  "Seq__removeSuffix (Seq__Seq__fin l, 0) = Seq__Seq__fin l"
 by simp 
lemma Seq__removeSuffix_fin_whole2 [simp]:
  "\<lbrakk>Seq__finite_p s\<rbrakk> 
  \<Longrightarrow>  Seq__removeSuffix (s, 0) = s"
 by (case_tac s, simp_all)
lemma Seq__removeSuffix_fin_empty [simp]:
  "Seq__removeSuffix (Seq__Seq__fin l, length l) = Seq__empty"
 by (simp add: Seq__empty_def)
lemma Seq__removeSuffix_fin_empty2 [simp]:
  "\<lbrakk>Seq__finite_p s\<rbrakk> 
  \<Longrightarrow>  Seq__removeSuffix (s, Seq__length s) = Seq__empty"
 by (case_tac s, simp_all add: Seq__empty_def)


end-proof
% ------------------------------------------------------------------------------

% specialization of previous four ops to n = 1:

op [a] head (s: Seq1 a) : a = theElement (prefix (s, 1))

op [a] last (s: FinSeq1 a) : a = theElement (suffix (s, 1))

% ------------------------------------------------------------------------------
proof Isa -verbatim

lemma Seq__head_fin [simp]:
  "\<lbrakk>l \<noteq> []\<rbrakk> 
  \<Longrightarrow> Seq__head (Seq__Seq__fin l) = hd l"
  by (simp add: Seq__head_def length_greater_0_conv [symmetric] 
                take_Suc One_nat_def
           del: length_greater_0_conv)

lemma Seq__head_fin2 [simp]:
  "\<lbrakk>s \<noteq> Seq__empty; s = Seq__Seq__fin l\<rbrakk> 
  \<Longrightarrow> Seq__head s = hd l"
  by (simp add: Seq__empty_def)

lemma Seq__head_inf [simp]:
 "\<lbrakk>s \<noteq> Seq__empty; s = Seq__Seq__inf fun\<rbrakk> 
 \<Longrightarrow> Seq__head s = fun 0"
 apply (simp add: Seq__head_def)
 apply (rule_tac t="Stream__subFromLong (fun, 0, 1)"
             and s="[fun 0]" in subst, 
        simp_all)
 apply (simp add: list_eq_iff_nth_eq Stream__length_subFromLong,
        simp add: Stream__subFromLong_def)
 apply (rule sym, rule_tac n=1 in List__list_nth, 
        simp_all add: List__definedOnInitialSegmentOfLength_def)
done

lemma Seq__last_fin [simp]:
  "\<lbrakk>l \<noteq> []\<rbrakk> 
  \<Longrightarrow> Seq__last (Seq__Seq__fin l) = last l"
 apply (simp add: Seq__last_def length_greater_0_conv [symmetric] 
                  Seq__suffix_fin One_nat_def
          del: length_greater_0_conv)
 apply (rule_tac t="List__suffix (l, Suc 0)" and s="[last l]" in subst,
        simp_all (no_asm_simp) add: list_eq_iff_nth_eq)
 apply (simp add: List__suffix_def List__subFromLong_def last_conv_nth)
 apply (rule sym, rule_tac n=1 in List__list_nth, 
        simp_all add: List__definedOnInitialSegmentOfLength_def  One_nat_def)
done

end-proof
% ------------------------------------------------------------------------------

op [a] tail (s: Seq1 a) : Seq a = removePrefix (s, 1)


op [a] butLast (s: FinSeq1 a) : Seq a = removeSuffix (s, 1)


% ------------------------------------------------------------------------------
proof Isa -verbatim

lemma Seq__tail_fin [simp]:
  "Seq__tail (Seq__Seq__fin l) = Seq__Seq__fin (tl l)"
 by (simp add: Seq__tail_def drop_Suc  One_nat_def)
lemma Seq__tail_inf [simp]:
  "Seq__tail (Seq__Seq__inf fun) = Seq__Seq__inf (\<lambda>i. fun (i + 1))"
 by (simp add: Seq__tail_def del: Seq__removePrefix.simps)
lemma Seq__butLast_fin [simp]:
  "Seq__butLast (Seq__Seq__fin l) =  Seq__Seq__fin (butlast l)"
 by (simp add: Seq__butLast_def Seq__removeSuffix_fin butlast_conv_take)

end-proof
% ------------------------------------------------------------------------------

% concatenation (the first sequence must be finite, because it does not make
% sense to concatenate a sequence to one that is already infinite):

op [a] ++ (s1: FinSeq a, s2: Seq a) infixl 25 : Seq a = the (s: Seq a)
  % length of s is at least length of s1:
  length s1 <=_length s &&
  % s starts with s1:
  prefix (s, length s1) = s1 &&
  % s continues with s2:
  removePrefix (s, length s1) = s2


% ------------------------------------------------------------------------------
proof Isa -verbatim

lemma Seq__e_pls_pls_fin [simp]:
  "(Seq__Seq__fin l1) ++ (Seq__Seq__fin l2) = Seq__Seq__fin (l1 @ l2)"
 apply (simp only:  Seq__e_pls_pls_def)
 apply (rule the1I2, rule Seq__e_pls_pls_Obligation_the, auto)
 apply (case_tac x, simp_all)
 apply (rule_tac t="l1 @ l2" 
             and s="take (length l1) list @ drop (length l1) list"
        in subst, 
        simp, simp (no_asm))
done

lemma Seq__e_pls_pls_inf [simp]:
  "(Seq__Seq__fin l) ++ (Seq__Seq__inf fun) = Seq__Seq__inf (l ++ fun)"
 apply (simp only:  Seq__e_pls_pls_def)
 apply (rule the1I2, rule Seq__e_pls_pls_Obligation_the, auto)
 apply (case_tac x, simp_all)
 apply (simp add: Stream__e_pls_pls_def fun_eq_iff not_less, auto)
 apply (simp add: list_eq_iff_nth_eq Stream__subFromLong_def 
                  List__subFromLong_def)
 apply (rotate_tac 1, thin_tac "?P")
 apply (drule_tac x=xa in spec, auto)
 apply (rule sym, drule sym, simp)
 apply (rule_tac n="length l" in List__list_nth, 
        auto simp add: List__definedOnInitialSegmentOfLength_def)
 apply (simp add:  Stream__removePrefix_def )
 apply (drule_tac x="xa - length l" in spec, auto)
done

end-proof
% ------------------------------------------------------------------------------

% prepend/append element (note that |> and <| point into list):

op [a] |> (x:a, s: Seq a) infixr 25 : Seq1 a = single x ++ s


op [a] <| (s: FinSeq a, x:a) infixl 25 : Seq1 a = s ++ single x

% ------------------------------------------------------------------------------
proof Isa -verbatim

lemma Seq___e_bar_gt_fin [simp]:
  "x |> Seq__Seq__fin l = Seq__Seq__fin (x#l)"
 by (simp add: Seq__e_bar_gt_def Seq__single_def)

lemma Seq__e_lt_bar_fin [simp]:
  "Seq__Seq__fin l <| x = Seq__Seq__fin (l@[x])"
 by (simp add: Seq__e_lt_bar_def Seq__single_def)

end-proof
% ------------------------------------------------------------------------------


% update element at index i:

op [a] update (s: Seq a, i:Nat, x:a | i <_length s) : Seq a =
  case s of
  | fin l -> fin (update (l, i, x))
  | inf t -> inf (update (t, i, x))


% quantifications:

op [a] forall? (p: a -> Bool) (s: Seq a) : Bool =
  fa(i:Nat) i <_length s => p (s @ i)

op [a] exists? (p: a -> Bool) (s: Seq a) : Bool =
  ex(i:Nat) i <_length s && p (s @ i)

op [a] exists1? (p: a -> Bool) (s: Seq a) : Bool =
  ex1(i:Nat) i <_length s && p (s @ i)

op [a] foralli? (p: Nat * a -> Bool) (s: Seq a) : Bool =
  fa(i:Nat) i <_length s => p (i, s @ i)

% filter away elements not satisfying predicate:

op [a] filter (p: a -> Bool) (s: Seq a) : Seq a =
  case s of
  | fin l -> fin (filter p l)
  | inf t -> if finite? (fn i:Nat -> p (s @ i)) then fin (filterF (p, t))
                                                else inf (filterI (p, t))

% fold from left/right:

op [a,b] foldl (f: a * b -> b) (base:b) (s: FinSeq a) : b =
  if empty? s then base else foldl f (f (head s, base)) (tail s)


op [a,b] foldr (f: a * b -> b) (base:b) (s: FinSeq a) : b =
  if empty? s then base else f (head s, foldr f base (tail s))

% sequences with the same length:

op [a,b] equiLong (s1: Seq a, s2: Seq b) infixl 20 : Bool =
  % either both infinite:
  (infinite? s1 && infinite? s2) ||
  % or both finite and with the same (finite) length:
  (  finite? s1 &&   finite? s2 && length s1 = length s2)

% ------------------------------------------------------------------------------
proof Isa -verbatim

lemma Seq__equiLong_fin [simp]:
  "Seq__Seq__fin l1 equiLong Seq__Seq__fin l2 = l1 equiLong l2"
  by (simp add: Seq__equiLong_def)
lemma Seq__equiLong_inf [simp]:
  "Seq__Seq__inf fun1 equiLong Seq__Seq__inf fun2"
  by (simp add: Seq__equiLong_def)
lemma Seq__equiLong_fin_inf [simp]:
  "Seq__Seq__fin l equiLong Seq__Seq__inf fun = False"
  by (simp add: Seq__equiLong_def)
lemma Seq__equiLong_inf_fin [simp]:
  "Seq__Seq__inf fun equiLong Seq__Seq__fin l = False"
  by (simp add: Seq__equiLong_def)
lemma Seq__equiLong_refl:
  "(s1::'a Seq__Seq) equiLong s1"
  by (case_tac s1, simp_all add: Seq__equiLong_def)
lemma Seq__equiLong_sym:
  "\<lbrakk>(s1::'a Seq__Seq) equiLong s2\<rbrakk> \<Longrightarrow> s2 equiLong s1"
  by (case_tac s1, simp_all add: Seq__equiLong_def)
lemma Seq__equiLong_trans:
  "\<lbrakk>(s1::'a Seq__Seq) equiLong s2; s2 equiLong s3\<rbrakk> \<Longrightarrow> s1 equiLong s3"
  by (case_tac s1, simp_all add: Seq__equiLong_def)

end-proof
% ------------------------------------------------------------------------------

% convert between sequence of tuples and tuple of sequences:

op [a,b] zip (s1: Seq a, s2: Seq b | s1 equiLong s2) : Seq (a * b) =
  case (s1,s2) of
  | (fin l1, fin l2) -> fin (zip (l1, l2))
  | (inf t1, inf t2) -> inf (zip (t1, t2))


op [a,b,c] zip3 (s1: Seq a, s2: Seq b, s3: Seq c |
                 s1 equiLong s2 && s2 equiLong s3) : Seq (a * b * c) =
  case (s1,s2,s3) of
  | (fin l1, fin l2, fin l3) -> fin (zip3 (l1, l2, l3))
  | (inf t1, inf t2, inf t3) -> inf (zip3 (t1, t2, t3))


% ------------------------------------------------------------------------------
proof Isa -verbatim
lemma Seq__zip3_alt: 
  "\<lbrakk>a equiLong b; b equiLong c \<rbrakk> 
  \<Longrightarrow>  Seq__zip3 (a,b,c) = Seq__zip (a, (Seq__zip (b,c)))"
 by (simp add: Seq__equiLong_def Seq__infinite_p_def Seq__finite_p_def
                 List__zip3_alt Stream__zip3_def Stream__zip_def 
        split: Seq__Seq.split_asm)

lemma Seq__zip_equilong_left:
  "\<lbrakk>a equiLong b\<rbrakk> 
  \<Longrightarrow> x equiLong Seq__zip (a,b) = (x equiLong a)"
 by (simp add: Seq__equiLong_def  Seq__infinite_p_def Seq__finite_p_def
        split: Seq__Seq.split_asm)
end-proof
% ------------------------------------------------------------------------------

op unzip : [a,b] Seq (a * b) -> (Seq a * Seq b | equiLong) = inverse zip

op unzip3 : [a,b,c] Seq (a * b * c) ->
                    {(s1,s2,s3) : Seq a * Seq b * Seq c |
                     s1 equiLong s2 && s2 equiLong s3} = inverse zip3


% homomorphically apply function to all elements of sequence(s):

op [a,b] map (f: a -> b) (s: Seq a) : Seq b =
  case s of
  | fin l -> fin (map f l)
  | inf t -> inf (map f t)

op [a,b,c] map2 (f: a * b -> c)
                (s1: Seq a, s2: Seq b | s1 equiLong s2) : Seq c =
  map f (zip (s1, s2))

op [a,b,c,d] map3 (f: a * b * c -> d)
                  (s1: Seq a, s2: Seq b, s3: Seq c |
                   s1 equiLong s2 && s2 equiLong s3) : Seq d =
  map f (zip3 (s1, s2, s3))

% remove all None elements from a sequence of optional values, and also remove
% the Some wrappers:

op [a] removeNones (s: Seq (Option a)) : Seq a = the (s': Seq a)
  map (embed Some) s' = filter (embed? Some) s

% true iff two sequences of optional values have the same "shape" (i.e. same
% length and matching None and Some values at every position i):

op [a,b] matchingOptionSeqs?
         (s1: Seq (Option a), s2: Seq (Option b)) : Bool =
  s1 equiLong s2 &&
  (fa(i:Nat) i <_length s1 => embed? None (s1@i) = embed? None (s2@i))

% homomorphically apply partial function (captured via Option) to all elements
% of sequence(s), removing elements on which the function is not defined:

op [a,b] mapPartial (f: a -> Option b) (s: Seq a) : Seq b =
  removeNones (map f s)

op [a,b,c] mapPartial2 (f: a * b -> Option c)
                       (s1: Seq a, s2: Seq b | s1 equiLong s2) : Seq c =
  mapPartial f (zip (s1, s2))

op [a,b,c,d] mapPartial3 (f: a * b * c -> Option d)
                         (s1: Seq a, s2: Seq b, s3: Seq c |
                          s1 equiLong s2 && s2 equiLong s3) : Seq d =
  mapPartial f (zip3 (s1, s2, s3))

% reverse (finite) sequence:

op [a] reverse (s: FinSeq a) : FinSeq a = fin (reverse (list s))

% sequence of repeated elements:

op [a] repeat (x:a) (len: Option Nat) : Seq a =
  case len of
  | Some n -> fin (repeat x n)
  | None   -> inf (repeat x)

op [a] allEqualElements? (s: Seq a) : Bool =
  fa (i:Nat, j:Nat) i <_length s && j <_length s => s @ i = s @ j

% extend (finite) sequence leftward/rightward to length n, filling with x:

op [a] extendLeft (s: FinSeq a, x:a, n:Nat | n >= length s) : FinSeq a =
  fin (extendLeft (list s, x, n))


op [a] extendRight (s: FinSeq a, x:a, n:Nat | n >= length s) : FinSeq a =
  fin (extendRight (list s, x, n))

% extend shorter sequence to length of longer sequence, leftward/rightward
% (for leftward case, the two sequences must be either both finite or both
% infinite, because a finite sequence cannot be made infinite by extending
% it leftward; for the rightward case we can have a finite one and an infinite
% one):

op [a,b] equiExtendLeft (s1: Seq a, s2: Seq b, x1:a, x2:b |
                         finite? s1 <=> finite? s2)
                        : (Seq a * Seq b | equiLong) =
  case (s1,s2) of
  | (inf _,  inf _)  -> (s1, s2)  % no change
  | (fin l1, fin l2) -> let (l1',l2') = equiExtendLeft(l1,l2,x1,x2) in
                        (fin l1', fin l2')

% shift list leftward/rightward by n positions, filling with x:

op [a] shiftLeft (s: Seq a, x:a, n:Nat) : Seq a =
  case s of
  | fin l -> fin (shiftLeft (l, x, n))
  | inf t -> inf (shiftLeft (t, n))

op [a] shiftRight (s: Seq a, x:a, n:Nat) : Seq a =
  case s of
  | fin l -> fin (shiftRight (l, x, n))
  | inf t -> inf (shiftRight (t, x, n))

% rotate (finite) sequence leftward/rightward by n positions:

op [a] rotateLeft (s: FinSeq1 a, n:Nat) : FinSeq1 a =
  let n = n mod (length s) in  % rotating by length(s) has no effect
  removePrefix (s, n) ++ prefix (s, n)

op [a] rotateRight (s: FinSeq1 a, n:Nat) : FinSeq1 a =
  let n = n mod (length s) in  % rotating by length(s) has no effect
  suffix (s, n) ++ removeSuffix (s, n)


(* We introduce a notion of "segmented sequence" as a sequence divided into
contiguous and non-overlapping segments. This notion is modeled as a sequence of
segments, where each segment is itself a sequence. We allow a segment to be
non-empty, even though an empty segment does not quite contribute to the
segmentation of the segmented sequence and could be in fact eliminated. If a
segment is infinite, there can be no following segment, because the infinite
segment takes up the whole rest of the segmented sequence: thus, we require each
segment that is followed by some other segment to be finite, via a subtype
constraint.

If the "outer" sequence of segments is infinite, each segment must be finite and
the whole segmented sequence has an infinite number of elements (divided into an
infinite number of finite segments). If the "outer" sequence of segments is
finite, the whole segmented sequence could have either a finite number of
elements (if the last segment is finite) or an infinite number of elements (if
the last segment is infinite). *)

type SegSeq a = {ss: Seq (Seq a) |
                 fa(i:Nat) (i+1) <_length ss =>
                           % writing "finite? (s @ i)" here gives a type
                           % checking error, for some unknown reason:
                           (let Some x = ss @@ i in finite? x)}


% segmented sequences with no empty segments ("proper" segmentation):

type Seg1Seq a = {ss: SegSeq a | forall? nonEmpty? ss}

(* The following op flattens a segmented sequence into a "regular" sequence.  If
we regard the segmented sequence as already "flat" but with "dividers" for the
segments, this op amounts to losing the dividers. *)

op [a] flatten (ss: SegSeq a) : Seq a =
  case ss of
  | fin listOfSeqs ->  % ss is a (finite) list of sequences
    if forall? finite? listOfSeqs then  % all sequences in list are finite
      fin (flatten (map list listOfSeqs))  % flatten list of lists
    else  % one sequence is infinite (must be the last one)
      fin (flatten (map list (butLast listOfSeqs))) ++ last listOfSeqs
        % flatten lists of lists except last and append last (infinite) segment
  | inf streamOfSeqs ->  % ss is an (infinite) stream of sequences (which must
                         % be all finite), i.e. of lists
    if finite? (fn i:Nat -> nonEmpty? (streamOfSeqs i)) then
      fin (flattenF (map list streamOfSeqs))
    else
      inf (flattenI (map list streamOfSeqs))


(* Two segmented sequences (with elements of possibly different types) have the
same "segmentation" if they have the same number of segments and each segment
has the same length as the corresponding segment. *)

op [a,b] sameSegmentation? (ss1: SegSeq a, ss2: SegSeq b) : Bool =
  ss1 equiLong ss2 &&
  (fa(i:Nat) i <_length ss1 => (ss1 @ i) equiLong (ss2 @ i))

(* A segmentation of a sequence can be described by the sequence of the lengths
of its finite segments, optionally followed by an indication of the presence of
a last infinite segment. The last infinite segment can be present only if there
is a finite number of finite segments and if their total length is finite. *)

type Segmentation0 = {finLens : Seq Nat, lastInf : Bool}

op segmentation? (seg:Segmentation0) : Bool =
  seg.lastInf => finite? seg.finLens &&
                 finite? (fn i:Nat -> i < length seg.finLens
                                   && seg.finLens @ i ~= 0)

type Segmentation = (Segmentation0 | segmentation?)

op [a] segmentationOf (ss: SegSeq a) : Segmentation =
  if infinite? ss || forall? finite? ss then
    {finLens = map length ss, lastInf = false}
  else
    {finLens = map length (butLast ss), lastInf = true}

% true iff segmentation could be applied to sequence:

op [a] segmentationFor (seg:Segmentation, s: Seq a) infixl 20 : Bool =
  ex (ss: SegSeq a) seg = segmentationOf ss && flatten ss = s

% unflatten (i.e. segment) sequence according to given segmentation:

op [a] unflatten
       (s: Seq a, seg:Segmentation | seg segmentationFor s) : SegSeq a =
  the (ss: SegSeq a) seg segmentationFor ss && flatten ss = s

% specialization of previous op to sequences of uniform length n > 0:

% ---------------------------------------------------------------------------
% op [a] unflattenU
%        (s: Seq a, n:PosNat | finite? s => n divides length s) : SegSeq a =
%   unflatten (s, {finLens = repeat n None, lastInf = false})
% ---------------------------------------------------------------------------

op [a] unflattenU
       (s: Seq a, n:PosNat | finite? s => n divides length s) : SegSeq a =
  if infinite? s then
    unflatten (s, {finLens = repeat n None, lastInf = false})
  else
    unflatten (s, {finLens = repeat n (Some (length s div n)), lastInf = false})

% sequence without repeated elements (i.e. "injective", if viewed as a map):

op [a] noRepetitions? (s: Seq a) : Bool = Map.injective? (seq_1 s)

type InjSeq a = (Seq a | noRepetitions?)

% ------------------------------------------------------------------------------
proof Isa -verbatim



lemma Seq__noRepetitions_p_fin [simp]:
  "Seq__noRepetitions_p (Seq__Seq__fin l) = distinct l"
 apply (auto simp add: Seq__noRepetitions_p_def 
                       Map__injective_p_def distinct_conv_nth)
 apply (drule_tac x=x1 in spec, simp, drule_tac x=x2 in spec, simp)
done

lemma Seq__noRepetitions_p_inf_aux:
  "Seq__noRepetitions_p (Seq__Seq__inf fun) = inj fun"
 by (auto simp add: Seq__noRepetitions_p_def Map__injective_p_def inj_on_def)

lemma Seq__noRepetitions_p_inf [simp]:
  "Seq__noRepetitions_p (Seq__Seq__inf fun) = Stream__noRepetitions_p fun"
 by (simp add: Stream__noRepetitions_p_def Seq__noRepetitions_p_inf_aux)


end-proof
% ------------------------------------------------------------------------------

% (strictly) ordered (injective) sequence of natural numbers:

op increasingNats? (nats: Seq Nat) : Bool =
  fa(i:Nat) i + 1 <_length nats => nats @ i < nats @ (i+1)

% ------------------------------------------------------------------------------
proof Isa -verbatim

lemma Seq__increasingNats_p_fin [simp]:
  "Seq__increasingNats_p (Seq__Seq__fin l) = List__increasingNats_p l"
 by (auto simp add: Seq__increasingNats_p_def List__increasingNats_p_def)

lemma Seq__increasingNats_p_inf [simp]:
  "Seq__increasingNats_p (Seq__Seq__inf fun) = Stream__increasingNats_p fun"
 by (simp add: Seq__increasingNats_p_def Stream__increasingNats_p_def)

lemma Seq__increasingNats_p_inf_growth:
  "\<lbrakk>Seq__increasingNats_p (Seq__Seq__inf fun)\<rbrakk>
    \<Longrightarrow> \<forall>j. \<exists>i. fun i > j"
 by (simp add: Stream__increasingNats_p_inf_growth)


lemma Seq__increasing_noRepetitions: 
  "\<lbrakk>Seq__increasingNats_p s\<rbrakk> \<Longrightarrow> Seq__noRepetitions_p s"
  by (case_tac s, auto simp add: Stream__increasing_noRepetitions 
                                 List__increasing_noRepetitions)


end-proof
% ------------------------------------------------------------------------------

% ordered sequence of positions of elements satisfying predicate:

op [a] positionsSuchThat (s: Seq a, p: a -> Bool) : InjSeq Nat =
  the (POSs: InjSeq Nat)
    % indices in POSs are ordered:
    increasingNats? POSs &&
    % POSs contains all and only indices of elements satisfying p:
    (fa(i:Nat) i in? POSs <=> i <_length s && p (s @ i))


% leftmost/rightmost position of element satisfying predicate (None if none):

op [a] leftmostPositionSuchThat (s: Seq a, p: a -> Bool) : Option Nat =
  let POSs = positionsSuchThat (s, p) in
  if empty? POSs then None else Some (head POSs)

op [a] rightmostPositionSuchThat (s: Seq a, p: a -> Bool) : Option Nat =
  let POSs = positionsSuchThat (s, p) in
  if empty? POSs || infinite? POSs then None else Some (last POSs)

% ordered list of positions of given element:

op [a] positionsOf (s: Seq a, x:a) : InjSeq Nat =
  positionsSuchThat (s, fn y:a -> y = x)


proof Isa -hook positionsOf_props end-proof


% position of element in injective list that has element:

op [a] positionOf (s: InjSeq a, x:a | x in? s) : Nat =
  theElement (positionsOf (s, x))



% true iff sub occurs within sup at position i:

op [a] subseqAt? (sub: Seq a, i:Nat, sup: Seq a) : Bool =
  if finite? sub then
    (ex (pre: FinSeq a, post: Seq a) pre ++ sub ++ post = sup &&
                                     length pre = i)
  else
    infinite? sup && removePrefix (sup, i) = sub

% return starting positions of all occurrences of sub within sup:

op [a] positionsOfSubseq (sub: Seq a, sup: Seq a) : InjSeq Nat =
  the (POSs: InjSeq Nat)
    % indices in POSs are ordered:
    increasingNats? POSs &&
    % POSs contains all and only indices of occurrence of subl in supl:
    (fa(i:Nat) i in? POSs <=> subseqAt? (sub, i, sup))

% if sub is a subsequence of sup, return starting position of
% leftmost/rightmost occurrence of sub within sup (there could be more than
% one), as well as the sequence of elements following/preceding sub within sup,
% otherwise return None:

op [a] leftmostPositionOfSubseqAndFollowing
       (sub: Seq a, sup: Seq a) : Option (Nat * Seq a) =
  let POSs = positionsOfSubseq (sub, sup) in
  if empty? POSs then None else
  let i = head POSs in
  if finite? sub then
    Some (i, removePrefix (sup, i + length sub))
  else
    Some (i, empty)


op [a] rightmostPositionOfSubseqAndPreceding
       (sub: Seq a, sup: Seq a) : Option (Nat * Seq a) =
  let POSs = positionsOfSubseq (sub, sup) in
  if empty? POSs || infinite? POSs then None else
  let i = last POSs in
  Some (i, prefix (sup, i))

% split sequence at index into preceding elements, element at index, and
% following elements:

op [a] splitAt (s: Seq a, i:Nat | i <_length s) : Seq a * a * Seq a =
  (prefix(s,i), s@i, removePrefix(s,i+1))

% split sequence at leftmost/rightmost element satisfying predicate (None
% if no element satisfies predicate):

op [a] splitAtLeftmost (p: a -> Bool) (s: Seq a)
                       : Option (Seq a * a * Seq a) =
  case leftmostPositionSuchThat (s, p) of
  | Some i -> Some (splitAt (s, i))
  | None   -> None

op [a] splitAtRightmost (p: a -> Bool) (s: Seq a)
                        : Option (Seq a * a * Seq a) =
  case rightmostPositionSuchThat (s, p) of
  | Some i -> Some (splitAt (s, i))
  | None   -> None

% leftmost/rightmost element satisfying predicate (None if none):

op [a] findLeftmost (p: a -> Bool) (s: Seq a) : Option a =
  let sp = filter p s in
  if empty? sp then None else Some (head sp)

op [a] findRightmost (p: a -> Bool) (s: Seq a) : Option a =
  let sp = filter p s in
  if empty? sp || infinite? sp then None else Some (last sp)

% return leftmost/rightmost element satisfying predicate as well as sequence of
% preceding/following elements (None if no element satisfies predicate):

op [a] findLeftmostAndPreceding (p: a -> Bool) (s: Seq a)
                                : Option (a * Seq a) =
  case leftmostPositionSuchThat (s, p) of
  | None   -> None
  | Some i -> Some (s @ i, prefix (s, i))


op [a] findRightmostAndFollowing (p: a -> Bool) (s: Seq a)
                                 : Option (a * Seq a) =
  case rightmostPositionSuchThat (s, p) of
  | None   -> None
  | Some i -> Some (s @ i, removePrefix (s, i))

% delete element from sequence:

op [a] delete (x:a) (s: Seq a) : Seq a =
  filter (fn y:a -> y ~= x) s

% remove from s1 all the elements that occur in s2 (i.e. sequence difference):

op [a] diff (s1: Seq a, s2: Seq a) : Seq a =
  filter (fn x:a -> x nin? s2) s1

% longest common prefix/suffix of two sequences:

% ------------------------------------------------------------
%op [a] longestCommlemmaonPrefix (s1: Seq a, s2: Seq a) : Seq a =
%  if s1 = s2 then s1 else
%  let lmdiff:Nat = minIn (fn lmdiff:Int ->  % leftmost different element
%      lmdiff >= 0 &&
%      lmdiff <_length s1 && lmdiff <_length s2 &&
%      s1 @ lmdiff ~= s2 @ lmdiff)
%  in
%  prefix (s1, lmdiff)
% ------------------------------------------------------------

op [a] longestCommonPrefix (s1: Seq a, s2: Seq a) : Seq a =
  if s1 = s2 then s1 else
  let len:Nat = the(len:Nat)
  len <=_length s1 &&
  len <=_length s2 &&
  prefix (s1, len) = prefix (s2, len) &&
  (ofLength? len s1 || ofLength? len s2 || s1 @ len ~= s2 @ len)
  in
  prefix (s1, len)

% This definition has to be changed

op [a] longestCommonSuffix (s1: FinSeq a, s2: FinSeq a) : FinSeq a =
  fin (longestCommonSuffix (list s1, list s2))

% a permutation of a sequence is represented by a permutation of the sequence
% of natural numbers that are less then the (possibly infinite) length:

op permutation? (prm: Seq Nat) : Bool =
  noRepetitions? prm && (fa(i:Nat) i in? prm <=> i <_length prm)

type Permutation = (Seq Nat | permutation?)

% ------------------------------------------------------------------------------
proof Isa -verbatim

lemma Seq__permutation_p_inf [simp]:
  "Seq__permutation_p (Seq__Seq__inf fun) = Stream__permutation_p fun"
  apply (simp add: Seq__permutation_p_def Stream__permutation_p_def 
                   in_strm_p_def bij_def surj_def, 
                   auto simp add: Stream__noRepetitions_p_def)
  apply (drule spec, clarify, rule exI, rule sym, auto)+
done

end-proof
% ------------------------------------------------------------------------------

% permute by moving element at position i to position prm @ i:

op [a] permute (s: Seq a, prm: Permutation | s equiLong prm) : Seq a =
  the (s': Seq a) s' equiLong s &&
                  (fa(i:Nat) i <_length s => s @ i = s' @ (prm@i))

% true iff s2 is a permutation of s1 (and vice versa):

op [a] permutationOf (s1: Seq a, s2: Seq a) infixl 20 : Bool =
  ex(prm:Permutation) prm equiLong s1 && permute(s1,prm) = s2

% given a comparison function over type a, type Seq a can be linearly
% ordered and compared element-wise and regarding the sequence list as smaller
% than any non-empty sequence:

op [a] compare
       (comp: a * a -> Comparison) (s1: Seq a, s2: Seq a) : Comparison =
  if s1 equiLong s2 &&
     (fa(i:Nat) i <_length s1 => comp (s1 @ i, s2 @ i) = Equal) then
    Equal
  else if empty? s1 then
    Less
  else if empty? s2 then
    Greater
  else
    let hd1 = head s1 in
    let hd2 = head s2 in
    case comp (hd1, hd2) of
    | Less    -> Less
    | Greater -> Greater
    | Equal   -> compare comp (tail s1, tail s2)


% lift isomorphism to sequences, element-wise:

op [a,b] isoSeq : Bijection(a,b) -> Bijection (Seq a, Seq b) =
  fn iso_elem -> map iso_elem








% ------------------------------------------------------------------------------
% -----------------  The proofs ------------------------------------------------
% ------------------------------------------------------------------------------
% Note: for the time being we place Isabelle lemmas that are needed for a proof 
%       and cannot be expressed in SpecWare as "verbatim" lemmas into the
%       preceeding proofs 
% ------------------------------------------------------------------------------

% ------------------------------------------------------------------------------

proof Isa lemmas_for_earlier_libraries
(**************** Move this to List.sw and Map.sw ****************)

lemma Set__finite_nat_max:
  "\<lbrakk>finite {i::nat. p i}\<rbrakk>  \<Longrightarrow> \<exists>n. \<forall>i. (p i \<longrightarrow> i < n)"
  by (simp add: finite_nat_set_iff_bounded )

lemma Set__infinite_nat_growth:
  "\<lbrakk>Set__infinite_p (\<lambda>(i::nat). p i)\<rbrakk>  \<Longrightarrow> \<forall>j. \<exists>i>j. p i"
  apply (simp add: Set__infinite_p_def fun_Compl_def bool_Compl_def) 
  apply (auto simp add: finite_nat_set_iff_bounded Bex_def mem_def not_less)
  apply (drule_tac x="Suc j" in spec, clarify, rule_tac x=x in exI, auto )
done


(************************************************************ 
    this is similar to  Function__fxy_implies_inverse__stp
    but drops the superfluous  assumption Fun_PD P__a f
 ** The proof is the same as before
************************************************************)
    
theorem Function__fxy_implies_inverse__stp2: 
  "\<lbrakk>Function__bijective_p__stp(P__a, P__b) f; 
    Fun_P(P__a, P__b) f; 
    P__a x; 
    P__b y; 
    f x = y\<rbrakk> \<Longrightarrow> 
   x = Function__inverse__stp P__a f y"
  proof -
 assume BIJ: "Function__bijective_p__stp (P__a, P__b) f"
 assume PF: "Fun_P(P__a, P__b) f"
 assume PX: "P__a (x::'a)"
 assume PY: "P__b (y::'b)"
 assume FXY: "f x = y"
 have INV_THE:
      "Function__inverse__stp P__a f y = (THE x. P__a x \<and> f x = y)"
  by (auto simp add: Function__inverse__stp_def)
 from PX FXY have X: "P__a x \<and> f x = y" by auto
 have "\<And>x'. P__a x' \<and> f x' = y \<Longrightarrow> x' = x"
 proof -
  fix x'
  assume "P__a x' \<and> f x' = y"
  hence PX': "P__a x'" and FXY': "f x' = y" by auto
  from FXY FXY' have FXFX': "f x = f x'" by auto
  from BIJ have "inj_on f P__a"
   by (auto simp add: Function__bijective_p__stp_def)
  with PX PX' have "f x = f x' \<Longrightarrow> x = x'"
   by (auto simp add: inj_on_def mem_def)
  with FXFX' show "x' = x" by auto
 qed
 with X have "(THE x. P__a x \<and> f x = y) = x" by (rule the_equality)
 with INV_THE show ?thesis by auto
qed

(************************************************************************)

lemma List__list_1_apply_List__list:
 "\<lbrakk>\<exists>n. f definedOnInitialSegmentOfLength n\<rbrakk>
   \<Longrightarrow> List__list_1 (List__list f) = f"
  apply (cut_tac List__list_subtype_constr)
  apply (simp add: List__list_1_def)
  apply (rule Function__inverse_f_apply__stp, auto simp del: not_ex)
  apply (subst List__list.simps, auto simp del: not_ex)
done

lemma List__list_apply_List__list_1:  "List__list (List__list_1 l) = l"
  apply (cut_tac List__list_subtype_constr)
  apply (simp add: List__list_1_def)
  apply (rule_tac f=List__list in Function__f_inverse_apply__stp, 
         auto simp del: not_ex)
  apply (subst List__list.simps, auto simp del: not_ex)
done


theorem List__increasing_strict_mono: 
  "\<lbrakk>List__increasingNats_p l; i < j; j < length l\<rbrakk> \<Longrightarrow> l ! i < l ! j"
  apply (subgoal_tac "\<forall>i j. j\<noteq>0 \<longrightarrow> j < length l - i \<longrightarrow> l ! i < l ! (i + j)", auto)
  apply (drule_tac x=i in spec, drule_tac x="j-i" in spec, auto)
  apply (simp add: List__increasingNats_p_def)
  apply (rotate_tac -2, erule rev_mp, erule rev_mp, induct_tac ja rule: nat_induct, 
         auto simp add: One_nat_def)
  apply (drule_tac x="ia+n" in spec, auto)
done

theorem List__increasing_strict_mono2: 
  "\<lbrakk>List__increasingNats_p l; i \<le> j; j < length l\<rbrakk> \<Longrightarrow> l ! i \<le> l ! j"
  by (case_tac "i=j", auto simp add: nat_neq_iff,
      drule List__increasing_strict_mono, auto)

lemma List__increasingNats_p_max:
  "\<lbrakk>l \<noteq> []; List__increasingNats_p l\<rbrakk> \<Longrightarrow> \<forall>j. j \<in> set l \<longrightarrow> j \<le> last l"
  by (auto simp add: in_set_conv_nth last_conv_nth List__increasing_strict_mono2)


lemma List__increasing_noRepetitions: 
  "List__increasingNats_p list \<Longrightarrow> distinct list"
  by (auto simp add: distinct_conv_nth nat_neq_iff List__increasing_strict_mono)

lemma List__list_1_definedOnInitialSegmentOfLength:
  "\<exists>n. List__list_1 l definedOnInitialSegmentOfLength n"
  by (cut_tac List__list_1_subtype_constr1, auto)

lemma List__list_eq_list [simp]:
  "List__list (\<lambda>i. if i < length l then Some (l ! i) else None) = l"
  by (auto simp add: list_eq_iff_nth_eq,
      subst List__list_nth, 
      auto simp add:  List__definedOnInitialSegmentOfLength_def not_le)


lemma List__definedOnInitialSegmentOfLength1:
   "\<lbrakk>f i = None; \<forall>i j. i \<in> dom f \<and> j < i \<longrightarrow> j \<in> dom f\<rbrakk>
    \<Longrightarrow> \<exists>n. f definedOnInitialSegmentOfLength n"
  apply (auto simp add: List__definedOnInitialSegmentOfLength_def dom_def)
  apply (drule_tac k="i" and m=id in ex_has_least_nat, auto)
  apply (rule_tac x=x in exI, auto)
  apply (rule classical, auto)
  apply (drule_tac x=i in spec, rotate_tac -1, drule_tac x=x in spec, auto)
done

lemma List__definedOnInitialSegmentOfLength1_iff:
   "\<lbrakk>\<exists>n. f definedOnInitialSegmentOfLength n\<rbrakk>
    \<Longrightarrow> (\<exists>i. i \<notin> dom f) \<and> (\<forall>i j. i \<in> dom f \<and> j < i \<longrightarrow> j \<in> dom f)"
  apply (auto simp add: List__definedOnInitialSegmentOfLength_def )
  apply (drule_tac x=j in spec, auto)
done

(*** move this later to Relation.sw ***)

lemma Relation__injective_p_alt_def:
 "Relation__injective_p m = 
  (\<forall>y \<in> Range m. \<exists>!x. (x, y) \<in> m)" 
 apply (simp add: Relation__injective_p_def Relation__applyi_def,
        auto simp add: mem_def)
 apply(drule_tac x=y in spec, safe)
 apply (simp add: set_eq_iff)
 apply (frule_tac x=xa in spec,drule_tac x=ya in spec,simp add: mem_def)
 apply (thin_tac "?P", simp only: set_eq_iff mem_def, simp)
 apply (drule_tac x=y in bspec)
 apply (simp add: Range_def Domain_def, auto simp add: mem_def)
 apply (drule_tac x=xa in spec, auto simp add: mem_def)
done
 (**************** Move this to Stream.sw *************************)


lemma Stream__unflattenI_lens:
   "\<lbrakk>Set__infinite_p (\<lambda>i. lens i \<noteq> 0)\<rbrakk> \<Longrightarrow> 
    Stream__map length (Stream__unflattenI (s, lens)) = lens"
  apply (drule_tac s=s in Stream__unflattenI_Obligation_the)
  apply (simp add: Stream__unflattenI_def)
  apply (erule the1I2, simp)
done

lemma Stream__unflattenI_flatten:
   "\<lbrakk>Set__infinite_p (\<lambda>i. lens i \<noteq> 0)\<rbrakk> \<Longrightarrow> 
     Stream__flattenI (Stream__unflattenI (s, lens)) = s"
  apply (drule_tac s=s in Stream__unflattenI_Obligation_the)
  apply (simp add: Stream__unflattenI_def)
  apply (erule the1I2, simp)
done

lemma Stream__unflattenU_lens [simp]:
   "\<lbrakk>n > 0\<rbrakk> \<Longrightarrow> Stream__map length (Stream__unflattenU (s, n)) = Stream__repeat n"
  apply (simp add: Stream__unflattenU_def)
  apply (rule Stream__unflattenI_lens, erule Stream__unflattenU_Obligation_subtype)
done

lemma Stream__unflattenU_lens2 [simp]:
   "\<lbrakk>n > 0\<rbrakk> \<Longrightarrow> (\<lambda>i. length (Stream__unflattenU (s, n) i)) = Stream__repeat n"
  apply (frule_tac s=s in Stream__unflattenU_lens)
  apply (simp add: Stream__map_def Stream__repeat_def fun_eq_iff)
done

lemma Stream__unflattenU_flatten [simp]:
   "\<lbrakk>n > 0\<rbrakk> \<Longrightarrow>  Stream__flattenI (Stream__unflattenU (s, n)) = s"
  apply (simp add: Stream__unflattenU_def)
  apply (rule Stream__unflattenI_flatten, 
         erule Stream__unflattenU_Obligation_subtype)
done

lemma Stream__unflattenU_infinite [simp]:
  "\<lbrakk>n > 0\<rbrakk> \<Longrightarrow> \<not> finite (\<lambda>i. Stream__unflattenU (s, n) i \<noteq> [])"
  apply (clarify)
  apply (drule_tac A="UNIV" in rev_finite_subset, auto simp add: mem_def)
  apply (frule_tac s=s in Stream__unflattenU_lens)
  apply (simp only: Stream__map_def Stream__repeat_def fun_eq_iff)
  apply (drule_tac x=x in spec, auto)
done
   
lemma Stream__increasingNats_p_inf_growth:
  "\<lbrakk>Stream__increasingNats_p fun\<rbrakk>
    \<Longrightarrow> \<forall>j. \<exists>i. fun i > j"
 apply (auto simp add: Stream__increasingNats_p_def)
 apply (induct_tac j)
 apply (rule_tac x=1 in exI, drule_tac x=0 in spec, auto)
 apply (rule_tac x="i + 1" in exI, drule_tac x=i in spec, auto)
done

lemma Stream__noRepetitions_p_finite_args:
  "Stream__noRepetitions_p s \<Longrightarrow> finite (\<lambda>i. s i = a)"
  apply (cut_tac F="{a}" and h=s in finite_vimageI)
  apply (auto simp add: vimage_def Collect_def Stream__noRepetitions_p_def)
done

end-proof
% ------------------------------------------------------------------------------




proof Isa seq_Obligation_subtype
  apply (auto simp add: bij_ON_def inj_on_def surj_on_def
                        Seq__SeqMap__subtype_pred_def 
                        definedAt_m_def undefinedAt_m_def)
  (** injectivity: lists  **)
  apply (drule mem_reverse)+
  apply (drule_tac f="List__list_1" in arg_cong)
  apply (simp add: List__list_1_apply_List__list 
                   List__definedOnInitialSegmentOfLength1)
  (** injectivity: streams  **)
  apply (drule mem_reverse)+
  apply (auto simp add: e_at_m_def fun_eq_iff)
  apply (drule_tac x=xa in spec)+
  apply (clarsimp simp add: dom_def)
  (** surjectivity **)
  apply (drule mem_reverse, simp add: Bex_def, subst mem_def, case_tac y, auto)
  (*** ... on lists  **)
  apply (cut_tac l=list in List__list_1_definedOnInitialSegmentOfLength)
  apply (rule_tac x="List__list_1 list" in exI)
  apply (simp add: List__list_apply_List__list_1  
                   List__definedOnInitialSegmentOfLength1_iff)
  (*** ... on streams  **)
  apply (rule_tac x="\<lambda>i. Some (fun i)" in exI, 
         auto simp add: fun_eq_iff e_at_m_def)
end-proof

proof Isa seq_Obligation_subtype0
   apply (simp add: Seq__SeqMap__subtype_pred_def 
                    undefinedAt_m_def definedAt_m_def 
                    List__definedOnInitialSegmentOfLength_def,
          erule exE)
   apply (drule_tac P="\<lambda>i. i \<notin> dom m" and m=id 
          in ex_has_least_nat,  erule exE)
   apply (rule_tac x=x in exI, auto simp add: dom_def)
   apply (drule_tac x=i in spec, rotate_tac -1, drule_tac x=x in spec, auto)
end-proof

proof Isa seq_Obligation_subtype1
   by (simp add: definedAt_m_def undefinedAt_m_def not_ex)
end-proof

% ------------------------------------------------------------------------------
proof Isa seq_simps

lemma Seq__seq_bij:
  "Function__bijective_p__stp(Seq__SeqMap__subtype_pred, TRUE) Seq__seq"
  by (cut_tac Seq__seq_Obligation_subtype, simp add: Seq__seq_def)

lemma Seq__seq_1_fin_simp:
  "Seq__seq_1 (Seq__Seq__fin l) = (\<lambda>i. if i < length l then Some (l ! i) else None)"
  apply (simp add: Seq__seq_1_def, rule sym)
  apply (rule Function__fxy_implies_inverse__stp2)
  apply (rule Seq__seq_bij, 
         simp_all add: Seq__SeqMap__subtype_pred_def definedAt_m_def dom_def)
  apply (auto simp add: Seq__seq_def undefinedAt_m_def dom_def)
done

lemma Seq__seq_1_fin_dom [simp]:
  "i \<in> dom (Seq__seq_1 (Seq__Seq__fin l)) = (i < length l)"
  by (simp add: Seq__seq_1_fin_simp dom_def)

lemma Seq__seq_1_fin_elements [simp]:
  "i \<in> dom (Seq__seq_1 (Seq__Seq__fin l))  \<Longrightarrow> 
     Seq__seq_1 (Seq__Seq__fin l) i = Some (l ! i)"
 by (simp add: Seq__seq_1_fin_simp dom_def split: split_if_asm)


lemma Seq__seq_1_inf_simp:
  "Seq__seq_1 (Seq__Seq__inf fun) = (\<lambda>i. Some (fun i))"
  apply (simp add: Seq__seq_1_def, rule sym)
  apply (rule Function__fxy_implies_inverse__stp2)
  apply (rule Seq__seq_bij, 
         simp_all add: Seq__SeqMap__subtype_pred_def definedAt_m_def dom_def)
  apply (auto simp add: Seq__seq_def undefinedAt_m_def e_at_m_def)
done

lemma Seq__seq_1_inf_dom [simp]:
  "i \<in> dom (Seq__seq_1 (Seq__Seq__inf fun))"
  by (simp add: Seq__seq_1_inf_simp dom_def)

lemma Seq__seq_1_inf_elements [simp]:
  "Seq__seq_1 (Seq__Seq__inf fun) i = Some (fun i)"
 by (simp add: Seq__seq_1_inf_simp dom_def )


end-proof
% ------------------------------------------------------------------------------

proof Isa infinite_inf_simp [simp]  
  by (simp add: Seq__infinite_p_def)
end-proof  

proof Isa infinite_fin_simp [simp]  
  by (simp add: Seq__infinite_p_def)
end-proof  

proof Isa finite_inf_simp [simp]  
  by (simp add: Seq__finite_p_def)
end-proof  

proof Isa finite_fin_simp [simp]  
  by (simp add: Seq__finite_p_def)
end-proof  

proof Isa infinite_not_finite [simp]  
  by (case_tac s, simp_all)
end-proof  

proof Isa length_fin_simp [simp]
  by (simp add: Seq__length_def)
end-proof

proof Isa ofLength_fin_simp [simp]
  by (simp add: Seq__ofLength_p_def)
end-proof

proof Isa ofLength_inf_simp [simp]
  by (simp add: Seq__ofLength_p_def)
end-proof

proof Isa e_lt_length_Obligation_subtype
  by (simp add: Seq__infinite_not_finite)
end-proof

proof Isa e_lt_eq_length_Obligation_subtype
  by (simp add: Seq__infinite_not_finite)
end-proof

proof Isa e_lt_length_inf_simp [simp]   
  by (simp add: Seq__e_lt_length_def)
end-proof

proof Isa e_lt_length_fin_simp [simp]
  by (simp add: Seq__e_lt_length_def)
end-proof

proof Isa e_lt_eq_length_inf_simp [simp]   
  by (simp add: Seq__e_lt_eq_length_def)
end-proof

proof Isa e_lt_eq_length_fin_simp [simp]
  by (simp add: Seq__e_lt_eq_length_def)
end-proof

proof Isa empty_p_fin [simp]
  by (simp add: Seq__empty_def)
end-proof

proof Isa empty_p_inf [simp]
  by (simp add: Seq__empty_def)
end-proof

proof Isa nonEmpty_p_fin [simp]
  by (simp add: Seq__nonEmpty_p_def fun_Compl_def bool_Compl_def Seq__empty_def)
end-proof

proof Isa nonEmpty_p_inf [simp]
  by (simp add: Seq__nonEmpty_p_def fun_Compl_def bool_Compl_def Seq__empty_def)
end-proof
  
proof Isa nonEmpty?_alt_def
  by (cases s, simp_all add: Seq__empty_def)
end-proof

proof Isa theElement_Obligation_the
 apply (case_tac s, auto simp add: Seq__single_def)
 apply (rule_tac x="hd list" in exI, 
        simp add: length_1_hd_conv [symmetric])
end-proof

proof Isa theElement_single [simp]
  apply (simp add:  Seq__theElement_def)
  apply (rule the1I2, rule Seq__theElement_Obligation_the)
  apply (simp_all add: Seq__single_def)
end-proof

proof Isa toSet_fin [simp]
 by (simp add: Seq__toSet_def fun_eq_iff mem_def)
end-proof

proof Isa toSet_inf [simp]
 by (auto simp add: Seq__toSet_def in_strm_p_def,
     drule mem_reverse, auto, auto simp add: mem_def)
end-proof

proof Isa suffix_Obligation_subtype0
 by (auto simp: Seq__e_lt_eq_length_def)
end-proof

% ------------- Isabelle lemmas for toSet
proof Isa toSet_simps 

lemma Seq__toSet_fin [simp]:    "Seq__toSet (Seq__Seq__fin l) = set l"
 by (simp add: Seq__toSet_def fun_eq_iff mem_def)

lemma Seq__toSet_inf [simp]:    "Seq__toSet (Seq__Seq__inf fun) = range fun"
 by (auto simp add: Seq__toSet_def in_strm_p_def,
     drule mem_reverse, auto, auto simp add: mem_def)
end-proof
% ---------------------------------------------------------------------

proof Isa removeSuffix_Obligation_subtype0
 by (auto simp: Seq__e_lt_eq_length_def)
end-proof

proof Isa head_Obligation_subtype
 by (cases s, simp_all add: length_greater_0_conv [symmetric]
                       del: length_greater_0_conv)
end-proof

proof Isa head_Obligation_subtype0
  by (cases s, simp_all add: length_greater_0_conv [symmetric]
                             Stream__length_subFromLong
                        del: length_greater_0_conv)
end-proof

proof Isa last_Obligation_subtype
 by (drule Seq__head_Obligation_subtype, 
     auto simp add: Seq__e_lt_eq_length_def Seq__infinite_not_finite)
end-proof

proof Isa last_Obligation_subtype0
 by (cases s, simp_all add: Seq__suffix_fin,
     rule List__length_suffix,
     simp add: length_greater_0_conv [symmetric] 
          del: length_greater_0_conv)
end-proof

proof Isa tail_Obligation_subtype
 by (rule Seq__head_Obligation_subtype)
end-proof

proof Isa butLast_Obligation_subtype
 by (rule Seq__last_Obligation_subtype)
end-proof


proof Isa e_pls_pls_Obligation_the
  apply (cases s1, simp_all)  
  apply (cases s2)
  apply (rule_tac a="Seq__Seq__fin (list @ lista)" in ex1I, 
         simp_all, clarify)
  apply (case_tac x, simp_all)
  apply (rule_tac t="list @ lista" 
              and s="take (length list) listb @ drop (length list) listb"
         in subst, 
         simp, simp (no_asm))
  apply (thin_tac "?P", thin_tac "?P", 
         rule_tac a="Seq__Seq__inf (list ++ fun)" in ex1I, simp_all)
  apply (simp add: Stream__e_pls_pls_def Seq__infinite_p_def 
                   Stream__removePrefix_def)
  apply (rule_tac s="List__subFromLong(list, 0, length list)" in HOL.trans)
  apply (simp add: Stream__subFromLong_def List__subFromLong_def,
         rule_tac f=List__list in arg_cong, simp add: fun_eq_iff)
  apply (rule List__subFromLong_whole)
  apply (case_tac x, 
         simp_all add: Stream__e_pls_pls_def Seq__infinite_p_def 
                       Stream__removePrefix_def, 
         clarify)
  apply (simp add: fun_eq_iff not_less, auto)
  apply (drule_tac t="List__subFromLong(list, 0, length list)" in HOL.trans)
  apply (rule List__subFromLong_whole [symmetric])
  apply (cut_tac List__list_subtype_constr, 
         simp add: bij_ON_def Stream__subFromLong_def List__subFromLong_def,
         clarify, thin_tac "surj_on ?f ?A ?B")
  apply (drule inj_onD, erule sym)
  apply (thin_tac "?P", thin_tac "?P", simp add: mem_def,
         rule_tac x="length list" in exI, 
         simp add: List__definedOnInitialSegmentOfLength_def)+
  apply (rotate_tac 1, thin_tac "?P", simp add: fun_eq_iff,
         drule_tac x=x in spec, auto)
end-proof

proof Isa e_bar_gt_Obligation_subtype
 by (simp add: Seq__single_def)
end-proof

proof Isa e_bar_gt_Obligation_subtype0
  by (cases s, simp_all add: Seq__single_def)
end-proof

proof Isa e_lt_bar_Obligation_subtype
  by (cases s, simp_all add: Seq__single_def)
end-proof

proof Isa update_Obligation_subtype
  by (auto simp: Seq__e_lt_length_def Seq__infinite_p_def Seq__length_def)
end-proof

proof Isa filter_Obligation_subtype
 by (auto simp: Seq__e_lt_length_def Seq__infinite_p_def)
end-proof

proof Isa filter_Obligation_subtype1
proof (auto simp: Set__infinite_p_def)
 assume "\<not> finite (\<lambda>i. p (t i))"
 hence "(\<lambda>i. p (t i)) \<notin> finite" by (auto simp: mem_def)
 hence "(\<lambda>i. p (t i)) \<in> (- finite)" by auto
 thus "(- finite) (\<lambda>i. p (t i))" by (auto simp: mem_def)
qed
end-proof

proof Isa foldl ()
 by auto
termination
 (**********************************************************************
  STEPHEN - unprovable goal
     Information that sequence is finite has gotten lost 
  **********************************************************************)
 apply (relation "measure (\<lambda>(f,base,s). Seq__length s)", auto)
 apply (case_tac s, auto simp add: Seq__empty_def)
 apply (simp add: Seq__length_def)
 sorry
end-proof


proof Isa foldl_Obligation_subtype
  by (simp add: Seq__nonEmpty_p_alt_def)
end-proof

proof Isa foldl_Obligation_subtype0
  by (simp add: Seq__nonEmpty_p_alt_def)
end-proof

proof Isa foldl_Obligation_subtype1
  by (cases s, simp_all)
end-proof

proof Isa foldr ()
 by auto
termination
 (**********************************************************************
  STEPHEN - unprovable goal
     Information that sequence is finite has gotten lost 
  **********************************************************************)
 apply (relation "measure (\<lambda>(f,base,s). Seq__length s)", auto)
 apply (case_tac s, auto simp add: Seq__empty_def)
 apply (simp add: Seq__length_def)
sorry
end-proof

proof Isa foldr_Obligation_subtype
  by (simp add: Seq__nonEmpty_p_alt_def)
end-proof

proof Isa foldr_Obligation_subtype0
  by (simp add: Seq__nonEmpty_p_alt_def)
end-proof

proof Isa foldr_Obligation_subtype1
  by (cases s, simp_all)
end-proof

proof Isa zip_Obligation_exhaustive
 (**********************************************************************
  Something's wrong: s10 should be s1, s20 should be s2
  **********************************************************************)
 by (simp add: Seq__equiLong_def Seq__infinite_p_def Seq__finite_p_def
        split: Seq__Seq.split_asm)
end-proof

proof Isa zip3_Obligation_exhaustive
 (**********************************************************************
  Something's wrong: s10 should be s1, s20 should be s2, s30 should be s3
  **********************************************************************)
 by (simp add: Seq__equiLong_def Seq__infinite_p_def Seq__finite_p_def
        split: Seq__Seq.split_asm)
end-proof

proof Isa unzip_Obligation_subtype
  (** Many cases, thus the long proof ***)
  apply (simp add: bij_ON_def inj_on_def mem_def surj_on_def Ball_def Bex_def)
  apply (rule conjI, clarify)
  apply (simp add: Seq__equiLong_def)
  apply (case_tac a)
        apply (case_tac b, simp_all)
              apply (case_tac aa)
                    apply (case_tac ba, simp_all)
              defer apply (case_tac ba, simp_all)
        apply (case_tac b, simp_all)
              apply (case_tac aa)
                    apply (case_tac ba, simp_all)
                    apply (case_tac ba, simp_all)
  prefer 3
  apply (cut_tac List__unzip_Obligation_subtype, 
         simp add: bij_ON_def inj_on_def mem_def Ball_def, auto)
  apply (cut_tac Stream__unzip_Obligation_subtype, 
         simp add: bij_def inj_on_def mem_def Ball_def, auto)
  apply (cut_tac Stream__unzip_Obligation_subtype, 
         simp add: bij_def inj_on_def mem_def Ball_def, auto)
  apply (case_tac x)
  apply (cut_tac List__unzip_Obligation_subtype, 
         simp add: bij_ON_def surj_on_def mem_def Ball_def Bex_def, 
         clarify, thin_tac "?P")
  apply (drule_tac x=list in spec, clarify)
  apply (rule_tac x="Seq__Seq__fin a" in exI, 
         rule_tac x="Seq__Seq__fin b" in exI, simp)
  apply (cut_tac Stream__unzip_Obligation_subtype, 
         simp add: bij_def surj_def, 
         clarify, thin_tac "?P")
  apply (drule_tac x="fun" in spec, clarify)
  apply (rule_tac x="Seq__Seq__inf a" in exI, 
         rule_tac x="Seq__Seq__inf b" in exI, simp)
end-proof

proof Isa unzip3_Obligation_subtype
 apply (auto simp add: bij_ON_def)
 apply (simp add: Seq__zip3_alt inj_on_def mem_def Ball_def, clarify)
 apply (cut_tac Seq__unzip_Obligation_subtype,
        simp add: bij_ON_def Seq__zip3_alt inj_on_def mem_def Ball_def, 
        clarify, rotate_tac -1, thin_tac "?P")
 apply (drule_tac x=a in spec, drule_tac x="Seq__zip (aa, b)" in spec, 
        drule mp, simp add: Seq__zip_equilong_left)
 apply (drule_tac x=ab in spec, drule_tac x="Seq__zip (ac, ba)" in spec, 
        drule mp, simp add: Seq__zip_equilong_left)
 apply (drule mp, simp_all, clarify)
 apply (cut_tac Seq__unzip_Obligation_subtype,
        simp add: bij_ON_def Seq__zip3_alt inj_on_def mem_def Ball_def, 
        clarify, rotate_tac -1, thin_tac "?P")
 apply (drule_tac x=aa in spec, drule_tac x=b in spec, 
        drule mp, simp)
 apply (drule_tac x=ac in spec, drule_tac x=ba in spec, 
        drule mp, simp)
 apply (drule mp, simp_all)
 apply (cut_tac Seq__unzip_Obligation_subtype,
        simp add: bij_ON_def surj_on_def mem_def Ball_def Bex_def, 
        clarify, thin_tac "?P",
        drule_tac x=x in spec, clarify)
 apply (cut_tac Seq__unzip_Obligation_subtype,
        simp add: bij_ON_def surj_on_def mem_def Ball_def Bex_def, 
        clarify, rotate_tac 1, thin_tac "?P",
        drule_tac x=b in spec, clarify)
 apply (rule_tac x=a in exI, rule_tac x=aa in exI, 
        auto simp add: Seq__zip_equilong_left)
 apply (rule_tac x=ba in exI, 
        auto simp add: Seq__zip3_alt Seq__zip_equilong_left)
end-proof

proof Isa removeNones_Obligation_the
  apply (case_tac s, simp)
  (* Case 1: Lists *)
  apply (cut_tac l=list in List__removeNones_Obligation_the, clarify)
  apply (rule_tac a="Seq__Seq__fin l_cqt" in ex1I, simp)
  apply (case_tac x, simp, simp)
  apply (case_tac "finite (\<lambda>i. case fun i of None \<Rightarrow> False
                                                  | Some x \<Rightarrow> True)")
  (* Case 2: Finite streams, same proof *)
  apply (cut_tac s="fun" in Stream__removeNonesF_Obligation_the)
  apply (rule_tac s="\<lambda>i. case fun i of None \<Rightarrow> False 
                                             | Some x \<Rightarrow> True"
              and t="\<lambda>i. fun i \<noteq> None" in subst,
         simp add: fun_eq_iff split: option.split, simp)
  apply (clarify, rule_tac a="Seq__Seq__fin l" in ex1I, simp)
  apply (case_tac x, simp, simp) 
  (* Case 2: Infinite streams, same proof *)
  apply (cut_tac s="fun" in Stream__removeNonesI_Obligation_the)
  apply (simp only: Set__infinite_p_def bool_Compl_def fun_Compl_def not_not)
  apply (rule_tac s="\<lambda>i. case fun i of None \<Rightarrow> False 
                                             | Some x \<Rightarrow> True"
              and t="\<lambda>i. fun i \<noteq> None" in subst,
         simp add: fun_eq_iff split: option.split, simp)
  apply (clarify, rule_tac a="Seq__Seq__inf s_cqt" in ex1I, simp)
  apply (case_tac x, simp, simp) 
end-proof

proof Isa matchingOptionSeqs_p_Obligation_subtype
 by (cases s1, auto simp: Seq__equiLong_def Seq__e_lt_length_def)
end-proof

proof Isa extendLeft_Obligation_subtype
 by (cases s, auto simp:)
end-proof

proof Isa extendRight_Obligation_subtype
 by (cases s, auto simp:)
end-proof

proof Isa equiExtendLeft_Obligation_subtype0
 by (cut_tac List__equiExtendLeft_subtype_constr [of l1 l2 x1 x2], simp)
end-proof

proof Isa equiExtendLeft_Obligation_exhaustive
 (**********************************************************************
  Something's wrong: s10 should be s1, s20 should be s2
  **********************************************************************)
 by (simp add: Seq__equiLong_def Seq__infinite_p_def Seq__finite_p_def
        split: Seq__Seq.split_asm)
end-proof

op [a,b] equiExtendRight (s1: Seq a, s2: Seq b, x1:a, x2:b)
                         : (Seq a * Seq b | equiLong) =
  case (s1,s2) of
  | (inf _,  inf _)  -> (s1, s2)  % no change
  | (fin _,  inf _)  -> (s1 ++ repeat x1 None, s2)
  | (inf _,  fin _)  -> (s1, s2 ++ repeat x2 None)
  | (fin l1, fin l2) -> let (l1',l2') = equiExtendRight(l1,l2,x1,x2) in
                        (fin l1', fin l2')


proof Isa equiExtendRight_Obligation_subtype4
 by (cut_tac List__equiExtendRight_subtype_constr [of l1 l2 x1 x2], simp)
end-proof

proof Isa equiExtendRight_Obligation_exhaustive
  by (cases s1, cases s2, simp_all, cases s2, simp_all)
end-proof

proof Isa rotateLeft_Obligation_subtype
 by (cases s, auto)
end-proof

proof Isa rotateLeft_Obligation_subtype0
  by (cases s, auto)
end-proof

proof Isa rotateLeft_Obligation_subtype1
 by (cases s, auto)
end-proof

proof Isa rotateLeft_Obligation_subtype2
 by (cases s, auto)
end-proof

proof Isa rotateLeft_Obligation_subtype3
 by (case_tac s, auto, rule less_le_trans, auto)
end-proof

proof Isa rotateLeft_Obligation_subtype4
 by (case_tac s, auto)
end-proof

proof Isa rotateRight_Obligation_subtype
 by (case_tac s, auto)
end-proof

proof Isa rotateRight_Obligation_subtype0
 by (case_tac s, auto)
end-proof

proof Isa rotateRight_Obligation_subtype1
 by (cases s, simp_all add: Seq__suffix_def)
end-proof

proof Isa rotateRight_Obligation_subtype2
 by (case_tac s, auto)
end-proof

proof Isa rotateRight_Obligation_subtype3
 apply (case_tac s, auto simp add: Seq__suffix_def)
 apply (subgoal_tac "0 + n mod length list \<le> length list")
 apply (drule_tac List__length_subFromLong, simp_all)
end-proof

proof Isa rotateRight_Obligation_subtype4
 by (case_tac s, auto simp add: Seq__suffix_def)
end-proof

proof Isa SegSeq__subsort_pred_Obligation_subtype
  (** STEPHEN **)
  (** goal must be typed: (i::nat) + 1 \<ge> 0" **)
 apply auto
 sorry
end-proof

proof Isa flatten_Obligation_subtype1
  apply (simp add: Seq__SegSeq__subtype_pred_def 
                   List__e_at_at_def list_1_Isa_nth
         split: split_if_asm)
  apply (auto simp add: list_all_length nth_butlast)
end-proof

proof Isa flatten_Obligation_subtype2
 by (rule finite_subset, 
     auto simp add: mem_def Stream__map_def Seq__empty_def  
                    Seq__nonEmpty_p_alt_def)
end-proof

proof Isa flatten_Obligation_subtype3
 apply (simp add: Seq__SegSeq__subtype_pred_def 
                  List__e_at_at_def list_1_Isa_nth
        split: split_if_asm)
 apply (auto simp add: Set__infinite_p_def fun_Compl_def bool_Compl_def 
                       Stream__map_def Seq__empty_def)
 apply (erule notE, rule finite_subset, auto simp add: mem_def)
 apply (drule_tac x=x in spec)
 apply (case_tac "streamOfSeqs x", auto)
end-proof

proof Isa sameSegmentation_p_Obligation_subtype
 by (cases ss1, auto simp: Seq__equiLong_def Seq__e_lt_length_def)
end-proof

proof Isa segmentation_p_Obligation_subtype
  by (cases "Seq__Segmentation0__finLens seg", auto)
end-proof

proof Isa segmentationOf_Obligation_subtype
  by (auto simp add: Seq__forall_p_def Seq__empty_def Seq__nonEmpty_p_alt_def
                     Seq__e_lt_length_def Seq__length_def)
end-proof

proof Isa segmentationOf_Obligation_subtype0
 by (auto simp add: Seq__e_lt_length_Obligation_subtype)
end-proof

proof Isa segmentationOf_Obligation_subtype2
 apply (auto, drule Seq__e_lt_length_Obligation_subtype)
 apply (case_tac ss, 
        simp_all add: Seq__SegSeq__subtype_pred_def 
                      List__e_at_at_def list_1_Isa_nth 
        split: split_if_asm) 
 apply (auto simp add: Seq__segmentation_p_def List__length_subFromLong)
 apply (rule_tac B="{i. i < length list - 1}" in finite_subset, 
        auto simp add: mem_def)
end-proof

proof Isa unflatten_Obligation_the
 (** POSTPONE
  *** use unflatten on Streams and Lists 
  *** we need many more lemmas about segmentation
 ***)
 sorry
end-proof

proof Isa unflattenU_Obligation_subtype
  apply (cases s, 
         auto simp add: Seq__segmentationFor_def Seq__segmentationOf_def)
  apply (rule_tac x="Seq__Seq__inf  
                      (\<lambda>i. Seq__Seq__fin 
                           (Stream__unflattenU (fun, n) i))" in exI,
         auto simp add: Seq__SegSeq__subtype_pred_def Stream__map_def)
end-proof


proof Isa unflattenU_Obligation_subtype1
  apply (cases s, 
         auto simp add: Seq__segmentationFor_def Seq__segmentationOf_def)
  apply (rule_tac x="Seq__Seq__fin  
                       (map Seq__Seq__fin (List__unflatten (list, n)))" in exI,
         auto simp add:  Seq__forall_p_def list_all_iff)
  apply (simp add: Seq__SegSeq__subtype_pred_def List__unflatten_length
                   zdvd_int List__e_at_at_def list_1_Isa_nth)
  apply (frule_tac List__unflatten_length_result, simp add: zdvd_int,
         clarsimp simp add: list_eq_iff_nth_eq List__unflatten_length  zdvd_int
                   list_all_iff)
  apply (rule_tac t = "Seq__list \<circ> Seq__Seq__fin" and s=id in subst,
         simp add: fun_eq_iff,
         rule sym, simp add: zdvd_int List__unflatten_concat )
end-proof

proof Isa increasingNats_p_Obligation_subtype
 by (cases nats, auto)
end-proof

proof Isa positionsSuchThat_Obligation_the
  apply (fold Seq__noRepetitions_p_def, case_tac s)
  (*** Case 1: Lists ***)
  apply (cut_tac l=list and p=p in  List__positionsSuchThat_Obligation_the)
  apply (erule ex1E, clarify, 
         rule_tac a="Seq__Seq__fin POSs" in ex1I, simp_all)
  apply (clarify, case_tac x, simp, clarsimp simp add: in_strm_p_def)
  apply (drule  Stream__increasingNats_p_inf_growth)
  apply (rotate_tac -1, drule_tac x="length list" in spec, clarify)
  apply (rotate_tac -2, drule_tac x="fun i" in spec, simp)
  apply (rotate_tac -1, drule_tac x=i in spec, simp)
  (*** Case 2: infinite Streams ***)
  apply (case_tac "Set__infinite_p (\<lambda>i. p (fun i))")
  apply (frule Set__infinite_nat_growth)
  apply (clarsimp, drule Stream__positionsSuchThatI_Obligation_the)
  apply (erule ex1E, clarify, rule_tac a="Seq__Seq__inf POSs" in ex1I, simp_all)
  apply (clarify, case_tac x, rotate_tac 1, thin_tac "?P", clarsimp)
  apply (case_tac "list=[]", simp)
  apply (rotate_tac -2, drule_tac x="last list" in spec, clarify)
  apply (rotate_tac -3, drule_tac x=i in spec, simp)
  apply (drule List__increasingNats_p_max, simp)
  apply (rotate_tac -1, drule_tac x=i in spec, simp)
  apply (drule_tac x=funa in spec, 
         simp add: Seq__noRepetitions_p_inf_aux Stream__noRepetitions_p_def)
  (*** Case 3: finite Streams ***)
  apply (simp add: Set__infinite_p_def fun_Compl_def bool_Compl_def) 
  apply (frule Stream__positionsSuchThatF_Obligation_the)
  apply (erule ex1E, clarify, rule_tac a="Seq__Seq__fin POSs" in ex1I, simp_all)
  apply (clarify, case_tac x, simp, clarsimp simp add: in_strm_p_def)
  apply (simp add: finite_nat_set_iff_bounded Ball_def mem_def, 
         clarify, thin_tac ?P)
  apply (drule  Stream__increasingNats_p_inf_growth)
  apply (rotate_tac -1, drule_tac x="m" in spec, clarify)
  apply (rotate_tac -2, drule_tac x="funa i" in spec, simp)
  apply (rotate_tac -2, drule_tac x="funa i" in spec, simp)
  apply (rotate_tac -1, drule_tac x=i in spec, simp)
end-proof

proof Isa leftmostPositionSuchThat_Obligation_subtype
  by (simp add: Seq__nonEmpty_p_alt_def)
end-proof

proof Isa rightmostPositionSuchThat_Obligation_subtype
  by (simp add: Seq__nonEmpty_p_alt_def)
end-proof

proof Isa rightmostPositionSuchThat_Obligation_subtype0
 by (auto simp add: Seq__e_lt_length_Obligation_subtype)
end-proof

% ------------------------------------------------------------------------------
proof Isa positionsOf_props

lemma Seq__positionsSuchThat_simps:
  "\<lbrakk>Seq__positionsSuchThat (s,p) = POSs\<rbrakk> \<Longrightarrow>
        Map__injective_p (Seq__seq_1 POSs) 
      \<and> (Seq__increasingNats_p POSs 
      \<and> (\<forall>i. i in? POSs = (i <_length s \<and> p (s @ i))))"
   apply (erule rev_mp, simp add: Seq__positionsSuchThat_def, rule the1I2)
   apply (rule Seq__positionsSuchThat_Obligation_the, auto)
done

lemma Seq__positionsSuchThat_inj [simp]:
  "Map__injective_p (Seq__seq_1 (Seq__positionsSuchThat (s,p)))"
  by (simp add: Seq__positionsSuchThat_simps)

lemma Seq__positionsSuchThat_inc [simp]:
  "Seq__increasingNats_p (Seq__positionsSuchThat (s,p))"
  by (simp add: Seq__positionsSuchThat_simps)

lemma Seq__positionsSuchThat_elements [simp]:
   "i in? Seq__positionsSuchThat (s,p) = (i <_length s \<and> p (s @ i))"
  by (simp add: Seq__positionsSuchThat_simps)

lemma Seq__positionsSuchThat_fin:
   "Seq__positionsSuchThat (Seq__Seq__fin l,p)
     = Seq__Seq__fin (List__positionsSuchThat (l,p))"
   apply (cut_tac s="Seq__Seq__fin l" in Seq__positionsSuchThat_Obligation_the,
          simp add: Seq__positionsSuchThat_def, rule the1I2, simp)
   apply (thin_tac ?P, clarsimp)
   apply (fold Seq__noRepetitions_p_def)
   apply (case_tac x, simp_all)
   apply (simp add: List__positionsSuchThat_def, rule sym, rule the1_equality)
   apply (rule  List__positionsSuchThat_Obligation_the, simp)
   apply (clarsimp simp add: in_strm_p_def,
          drule  Stream__increasingNats_p_inf_growth)
   apply (rotate_tac -1, drule_tac x="length l" in spec, clarify)
   apply (drule_tac x="fun i" in spec, simp)
   apply (drule_tac x=i in spec, simp)
done

lemma Seq__positionsOf_fin:
  "Seq__positionsOf (Seq__Seq__fin l,a) = Seq__Seq__fin (List__positionsOf (l,a))"
  by (simp add: Seq__positionsOf_def List__positionsOf_def 
                Seq__positionsSuchThat_fin)

lemma Seq__positionsSuchThat_inf:
  "\<lbrakk>Set__infinite_p (\<lambda>i. p (s i))\<rbrakk> \<Longrightarrow> 
      Seq__positionsSuchThat (Seq__Seq__inf s,p)
    = Seq__Seq__inf (Stream__positionsSuchThatI (s,p))"
   apply (cut_tac s="Seq__Seq__inf s" in Seq__positionsSuchThat_Obligation_the,
          simp add: Seq__positionsSuchThat_def, rule the1I2, simp)
   apply (rotate_tac 1, thin_tac ?P, clarsimp, fold Seq__noRepetitions_p_def)
   apply (case_tac x, simp_all)
   apply (drule Set__infinite_nat_growth)
   apply (case_tac "list=[]", simp)
   apply (rotate_tac -2, drule_tac x="last list" in spec, clarify)
   apply (rotate_tac -3, drule_tac x=i in spec, simp)
   apply (drule List__increasingNats_p_max, simp)
   apply (rotate_tac -1, drule_tac x=i in spec, simp)
   apply (simp add: Stream__positionsSuchThatI_def, rule sym, rule the1_equality)
   apply (erule  Stream__positionsSuchThatI_Obligation_the, simp)
done

lemma Seq__positionsSuchThat_inf2:
  "\<lbrakk>finite (\<lambda>i. p (s i))\<rbrakk> \<Longrightarrow> 
      Seq__positionsSuchThat (Seq__Seq__inf s,p)
    = Seq__Seq__fin (Stream__positionsSuchThatF (s,p))"
   apply (cut_tac s="Seq__Seq__inf s" in Seq__positionsSuchThat_Obligation_the,
          simp add: Seq__positionsSuchThat_def, rule the1I2, simp)
   apply (rotate_tac 1, thin_tac ?P, clarsimp, fold Seq__noRepetitions_p_def)
   apply (case_tac x, simp_all)
   apply (simp add: Stream__positionsSuchThatF_def, rule sym, rule the1_equality)
   apply (erule  Stream__positionsSuchThatF_Obligation_the, simp)
   apply (clarsimp simp add: in_strm_p_def,
          drule  Stream__increasingNats_p_inf_growth)
   apply (cut_tac Set__finite_nat_max, auto simp add: Collect_def)
   apply (rotate_tac -2, drule_tac x="n" in spec, clarify)
   apply (rotate_tac -2, drule_tac x="fun i" in spec, auto)
done


lemma Seq__positionsSuchThat_inf3:
  "\<lbrakk>\<not> Set__infinite_p (\<lambda>i. p (s i))\<rbrakk> \<Longrightarrow> 
      Seq__positionsSuchThat (Seq__Seq__inf s,p)
    = Seq__Seq__fin (Stream__positionsSuchThatF (s,p))"
 by (simp add: Set__infinite_p_def fun_Compl_def bool_Compl_def 
               Seq__positionsSuchThat_inf2) 

lemma Seq__positionsOf_inf:
  "\<lbrakk>Set__infinite_p (\<lambda>i. s i = a)\<rbrakk> \<Longrightarrow> 
   Seq__positionsOf (Seq__Seq__inf s,a) = Seq__Seq__inf (Stream__positionsOfI (s,a))"
  by (simp add: Seq__positionsOf_def Stream__positionsOfI_def
                Seq__positionsSuchThat_inf)

lemma Seq__positionsOf_inf2:
  "\<lbrakk>finite (\<lambda>i. s i = a)\<rbrakk> \<Longrightarrow> 
   Seq__positionsOf (Seq__Seq__inf s,a) = Seq__Seq__fin (Stream__positionsOfF (s,a))"
  by (simp add: Seq__positionsOf_def Stream__positionsOfF_def
                Seq__positionsSuchThat_inf2)

lemma Seq__positionsOf_inf3:
  "\<lbrakk>\<not> Set__infinite_p (\<lambda>i. s i = a)\<rbrakk> \<Longrightarrow> 
   Seq__positionsOf (Seq__Seq__inf s,a) = Seq__Seq__fin (Stream__positionsOfF (s,a))"
  by (simp add: Seq__positionsOf_def Stream__positionsOfF_def
                Seq__positionsSuchThat_inf3)

(******************************************************************************)

end-proof
% ------------------------------------------------------------------------------

proof Isa positionOf_Obligation_subtype
   apply (fold Seq__noRepetitions_p_def, cases s)
   apply (clarsimp simp add: Seq__positionsOf_fin,
          drule List__positionOf_Obligation_subtype, simp_all)
   apply (frule Stream__positionOf_Obligation_subtype, simp,
          clarsimp simp add: Seq__positionsOf_inf2,
          drule Stream__positionOf_Obligation_subtype0, simp_all)
end-proof

proof Isa subseqAt_p_Obligation_subtype
 by (case_tac pre, auto, case_tac sub__v, auto)
end-proof

proof Isa subseqAt_p_Obligation_subtype0
 by (cases sup__v, auto)
end-proof

proof Isa positionsOfSubseq_Obligation_the
 sorry
end-proof

proof Isa leftmostPositionOfSubseqAndFollowing_Obligation_subtype
  by (simp add: Seq__nonEmpty_p_alt_def)
end-proof
% apply (case_tac sup__v, 
%        simp_all add: Seq__suffix_def Seq__removeSuffix_def Seq__head_def)
% apply (case_tac sub__v, auto)
%
proof Isa leftmostPositionOfSubseqAndFollowing_Obligation_subtype0
 sorry
end-proof

proof Isa rightmostPositionOfSubseqAndPreceding_Obligation_subtype
   by (auto simp: Seq__nonEmpty_p_alt_def)
end-proof

proof Isa rightmostPositionOfSubseqAndPreceding_Obligation_subtype0
 by (auto simp add: Seq__e_lt_length_Obligation_subtype)
end-proof

%  I need a lot more intermediate lemmas before I can prove that
%
%  apply (simp add: Seq__infinite_not_finite, erule conjE)
%  apply (drule_tac 
%         Seq__leftmostPositionOfSubseqAndFollowing_Obligation_subtype1)
%  apply (simp, simp)
proof Isa rightmostPositionOfSubseqAndPreceding_Obligation_subtype1
 sorry
end-proof


proof Isa splitAt_Obligation_subtype
 by (auto simp: Seq__e_lt_length_def Seq__e_lt_eq_length_def)
end-proof

proof Isa splitAt_Obligation_subtype0
 by (auto simp add: Seq__e_lt_length_def Seq__e_lt_eq_length_def)
end-proof

proof Isa splitAtLeftmost_Obligation_subtype
 apply (simp add: Seq__leftmostPositionSuchThat_def Let_def split: split_if_asm)
 apply (case_tac "Seq__positionsSuchThat (s, p)", simp_all add: Seq__empty_def) 
 apply (rotate_tac -1, erule rev_mp)
 apply (simp (no_asm_simp) add: Seq__positionsSuchThat_def)
 apply (rule the1I2, rule Seq__positionsSuchThat_Obligation_the, clarify)
 apply (drule_tac x="hd list" in spec, simp)
 apply (rotate_tac -1, erule rev_mp)
 apply (simp (no_asm_simp) add: Seq__positionsSuchThat_def)
 apply (rule the1I2, rule Seq__positionsSuchThat_Obligation_the, clarify)
 apply (drule_tac x="fun 0" in spec, auto simp add: in_strm_p_def)
end-proof

proof Isa splitAtRightmost_Obligation_subtype
 apply (simp add: Seq__rightmostPositionSuchThat_def Let_def split: split_if_asm)
 apply (case_tac "Seq__positionsSuchThat (s, p)", simp_all add: Seq__empty_def) 
 apply (rotate_tac -1, erule rev_mp)
 apply (simp (no_asm_simp) add: Seq__positionsSuchThat_def)
 apply (rule the1I2, rule Seq__positionsSuchThat_Obligation_the, clarify)
 apply (drule_tac x="last list" in spec, simp)
end-proof

proof Isa findLeftmost_Obligation_subtype
  by (simp add: Seq__nonEmpty_p_alt_def)
end-proof

proof Isa findRightmost_Obligation_subtype
  by (simp add: Seq__nonEmpty_p_alt_def)
end-proof

proof Isa findRightmost_Obligation_subtype0
 by (auto simp add: Seq__e_lt_length_Obligation_subtype)
end-proof

proof Isa findLeftmostAndPreceding_Obligation_subtype
 by (simp add: Seq__splitAtLeftmost_Obligation_subtype)
end-proof

proof Isa findLeftmostAndPreceding_Obligation_subtype0
 by (drule Seq__findLeftmostAndPreceding_Obligation_subtype,
     auto simp add:  Seq__e_lt_length_def Seq__e_lt_eq_length_def)
end-proof

proof Isa findRightmostAndFollowing_Obligation_subtype
 by (simp add: Seq__splitAtRightmost_Obligation_subtype)
end-proof

proof Isa findRightmostAndFollowing_Obligation_subtype0
 by (drule Seq__findRightmostAndFollowing_Obligation_subtype,
     auto simp add:  Seq__e_lt_length_def Seq__e_lt_eq_length_def)
end-proof

proof Isa longestCommonPrefix_Obligation_the
  apply (cases s1, cases s2) prefer 3
  apply (cases s2, simp_all add: Stream__prefix_alt_def [symmetric]) prefer 3
  (* Case 1: List / List *)
  apply (cut_tac ?l1.0=list and ?l2.0=lista in
         List__longestCommonPrefix_Obligation_the, erule ex1E, clarsimp)
  apply (rule_tac a=len in ex1I, simp)
  apply (drule_tac x=x in spec, erule mp, clarify, simp)
  (* Case 2: Stream / List *)
  apply (cut_tac ?l1.0=list and ?l2.0="Stream__prefix (fun, length list)" 
         in List__longestCommonPrefix_Obligation_the, erule ex1E, clarsimp)
  apply (rule_tac a=len in ex1I, simp, thin_tac ?P)
  apply (case_tac "length list = len", simp_all, drule le_neq_trans, simp)
  apply (simp add: Stream__prefix_elements list_eq_iff_nth_eq)
  apply (drule_tac x=x in spec, erule mp, clarify, simp)
  apply (case_tac "length list = x", simp_all, drule le_neq_trans, simp)
  apply (simp add: Stream__prefix_elements list_eq_iff_nth_eq)
  (* Case 3: Stream / Stream *)
  apply (drule Stream__longestCommonPrefix_Obligation_subtype)
  apply (thin_tac "?P", thin_tac "?P", 
         simp add: Integer__hasMax_p_def Integer__isMaxIn_def mem_def,
         clarify)
  apply (rule_tac a="nat i" in ex1I, simp)
  apply (rule notI)
  apply (drule_tac x="i+1" in spec, simp add: Stream__prefix_conv, clarify)
  apply (case_tac "j < nat i", simp,
         simp add: not_less nat_add_distrib less_Suc_eq_le)
  apply (drule_tac x="int x" in spec, simp add: Stream__prefix_conv)
  apply (rule classical, drule_tac x=x in spec, simp)
  (* Case 4: List / Stream <---- TODO *)
  apply (cut_tac ?l2.0=list and ?l1.0="Stream__prefix (fun, length list)" 
         in List__longestCommonPrefix_Obligation_the, erule ex1E, clarsimp)
  apply (rule_tac a=len in ex1I, simp, thin_tac ?P)
  apply (case_tac "length list = len", simp_all, drule le_neq_trans, simp)
  apply (simp add: Stream__prefix_elements list_eq_iff_nth_eq)
  apply (drule_tac x=x in spec, erule mp, clarify, simp)
  apply (case_tac "length list = x", simp_all, drule le_neq_trans, simp)
  apply (simp add: Stream__prefix_elements list_eq_iff_nth_eq)
end-proof

proof Isa longestCommonPrefix_Obligation_subtype
 by (cases s1, simp_all)
end-proof

proof Isa longestCommonPrefix_Obligation_subtype0
 by (cases s2, simp_all)
end-proof

proof Isa longestCommonPrefix_Obligation_subtype1
 by (rule the1I2, erule Seq__longestCommonPrefix_Obligation_the, simp)
end-proof

proof Isa permute_Obligation_the
 apply (case_tac prm, case_tac s) prefer 3 apply (case_tac s) prefer 3 
 apply (simp_all, simp_all add: Seq__permutation_p_def)
 apply (cut_tac l=lista and prm=list in List__permute_Obligation_the)
 apply (simp_all add: List__permutation_p_def, erule ex1E, clarify)
 apply (rule_tac a="Seq__Seq__fin r" in ex1I, simp_all)
 apply (case_tac x, simp_all)
 apply (drule_tac s=funa in Stream__permute_Obligation_the)
 apply (erule ex1E, clarify)
 apply (rule_tac a="Seq__Seq__inf s_cqt" in ex1I, simp_all)
 apply (case_tac x, simp_all)
end-proof

proof Isa permute_Obligation_subtype
 by (cases s, auto simp: Seq__equiLong_def Seq__e_lt_length_def)
end-proof

proof Isa permute_Obligation_subtype0
 apply (cases prm, cases s) prefer 3 apply (cases s, simp_all) 
 apply (cases s_cqt, simp_all)
 apply (cases s_cqt, simp_all)
 apply (simp add: Seq__permutation_p_def, clarify)
 apply (drule spec, auto)
end-proof

proof Isa permutationOf_Obligation_subtype
  by (erule Seq__equiLong_sym)
end-proof

proof Isa compare ()
 by auto
termination
 apply (relation 
        "measure (\<lambda>(comp_v,s1,s2). 
                     if Seq__finite_p s1
                      then if Seq__length s1 <=_length s2
                            then Seq__length s1
                            else Seq__length s2
                      else if Seq__finite_p s2
                            then Seq__length s2
                            else LEAST i. comp_v(s1 @ i, s2 @ i) \<noteq> Equal
                  )", simp)
 apply (case_tac s1, case_tac s2) prefer 3 apply (case_tac s2)
 apply (auto simp add: Seq__empty_def Least_Suc  One_nat_def)
end-proof

proof Isa compare_Obligation_subtype
  by (cases s1, auto simp: Seq__equiLong_def Seq__e_lt_length_def)
end-proof

proof Isa compare_Obligation_subtype0
  by (simp add:  Seq__nonEmpty_p_alt_def)
end-proof

proof Isa compare_Obligation_subtype1
  by (simp add:  Seq__nonEmpty_p_alt_def)
end-proof

proof Isa compare_Obligation_subtype2
  by (simp add:  Seq__nonEmpty_p_alt_def)
end-proof

proof Isa compare_Obligation_subtype3
  by (simp add:  Seq__nonEmpty_p_alt_def)
end-proof

proof Isa isoSeq_Obligation_subtype
  apply (simp (no_asm_simp) add: bij_def inj_on_def surj_def, auto)
  apply (case_tac x , case_tac y) prefer 3 apply (case_tac y, simp_all)
  apply (drule_tac Stream__isoStream_Obligation_subtype, 
         simp add: bij_def inj_on_def)
  apply (drule_tac List__isoList_subtype_constr, 
         simp add: bij_def inj_on_def List__isoList_def)
  apply (case_tac y, simp_all)
  apply (drule_tac List__isoList_subtype_constr, 
         simp add: bij_def surj_def List__isoList_def, clarify,
         drule_tac x=list in spec, clarify,
         rule_tac x= "Seq__Seq__fin x" in exI, auto)
  apply (drule_tac Stream__isoStream_Obligation_subtype,
         simp add: bij_def surj_def, clarify,
         drule_tac x="fun" in spec, clarify,
         rule_tac x= "Seq__Seq__inf x" in exI, auto)
end-proof

endspec
