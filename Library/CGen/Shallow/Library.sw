Library qualifying spec

%% This file contains lemmas that could eventually be pushed into a library somewhere.
%%TODO rephrase as specware lemmas when possible.

import /Library/General/TwosComplementNumber
import /Library/General/TwosComplementNumber_ExecOps  %% TODO: Without this, we get a mergeOpInfo warning for Specware/Library/AllIsa
import /Library/General/FunctionExt
import /Library/General/OptionExt
import /Library/Base/List_Executable

%TODO generalize
theorem toNat_bound_rule is
 fa(bs:Bits1) length bs <= 8 => toNat bs <= 255


(***********************************************************************************************************)
%%TODO generialize these lemmas (way to recognize the constant?):
%%TODO does the simp del below also apply to files that import this file?
proof isa -verbatim

theorem nat_less256 [simp]:
  "((nat i) < (256::nat)) = (i < 256)"
  apply(auto)
  done

theorem nat_less65536 [simp]:
  "((nat i) < (65536::nat)) = (i < 65536)"
  apply(auto)
  done

theorem nat_less4294967296 [simp]:
  "((nat i) < (4294967296::nat)) = (i < 4294967296)"
  apply(auto)
  done

theorem nat_less18446744073709551616 [simp]:
  "((nat i) < (18446744073709551616::nat)) = (i < 18446744073709551616)"
  apply(auto)
  done

theorem nat_less340282366920938463463374607431768211456 [simp]:
  "((nat i) < (340282366920938463463374607431768211456::nat)) = (i < 340282366920938463463374607431768211456)"
  apply(auto)
  done


theorem int_lesseq256 [simp]:
  "((int n) <= (256::int)) = (n <= nat 256)"
  apply(auto)
  done

theorem int_lesseq65536 [simp]:
  "((int n) <= (65536::int)) = (n <= nat 65536)"
  apply(auto)
  done

theorem int_lesseq4294967296 [simp]:
  "((int n) <= (4294967296::int)) = (n <= nat 4294967296)"
  apply(auto)
  done

theorem int_lesseq18446744073709551616 [simp]:
  "((int n) <= (18446744073709551616::int)) = (n <= nat 18446744073709551616)"
  apply(auto)
  done

theorem int_lesseq340282366920938463463374607431768211456 [simp]:
  "((int n) <= (340282366920938463463374607431768211456::int)) = (n <= nat 340282366920938463463374607431768211456)"
  apply(auto)
  done



theorem int_lesseq255 [simp]:
  "((int n) <= (255::int)) = (n <= nat 255)"
  apply(auto)
  done

theorem int_lesseq65535 [simp]:
  "((int n) <= (65535::int)) = (n <= nat 65535)"
  apply(auto)
  done

theorem int_lesseq4294967295 [simp]:
  "((int n) <= (4294967295::int)) = (n <= nat 4294967295)"
  apply(auto)
  done

theorem int_lesseq18446744073709551615 [simp]:
  "((int n) <= (18446744073709551615::int)) = (n <= nat 18446744073709551615)"
  apply(auto)
  done

theorem int_lesseq340282366920938463463374607431768211455 [simp]:
  "((int n) <= (340282366920938463463374607431768211455::int)) = (n <= nat 340282366920938463463374607431768211455)"
  apply(auto)
  done



theorem int_lesseq127 [simp]:
  "((int n) <= (127::int)) = (n <= nat 127)"
  apply(auto)
  done

theorem int_lesseq32767 [simp]:
  "((int n) <= (32767::int)) = (n <= nat 32767)"
  apply(auto)
  done

theorem int_lesseq2147483647 [simp]:
  "((int n) <= (2147483647::int)) = (n <= nat 2147483647)"
  apply(auto)
  done

theorem int_lesseq9223372036854775807 [simp]:
  "((int n) <= (9223372036854775807::int)) = (n <= nat 9223372036854775807)"
  apply(auto)
  done

theorem int_lesseq170141183460469231731687303715884105727 [simp]:
  "((int n) <= (170141183460469231731687303715884105727::int)) = (n <= nat 170141183460469231731687303715884105727)"
  apply(auto)
  done





(* rephrase? *)
theorem not_empty_from_length [simp]:
  "\<lbrakk>length x > 0\<rbrakk> \<Longrightarrow> (x \<noteq> [])"
  apply(auto)
done

(* see Int.int_int_eq and Nat_Transfer.transfer_int_nat_relations*)
theorem int_injective:
  "(int n = int m) = (m = n)"
  apply auto
  done

theorem int_injective_fw:
  "(int n = int m) \<Longrightarrow> (m = n)"
  apply auto
  done

theorem nat_injective:
  "\<lbrakk> n \<ge> 0 ; m \<ge> 0\<rbrakk> \<Longrightarrow> (nat n = nat m) = (m = n)"
  apply auto
  done

theorem nat_injective_fw:
  "\<lbrakk>nat n = nat m ; n \<ge> 0 ; m \<ge> 0\<rbrakk> \<Longrightarrow> (m = n)"
  apply auto
  done

theorem int_monotone:
  "(int m <= int n) = (m <= n)"
  by auto

theorem int_monotone2:
  "(int m <= int n) \<Longrightarrow> (m <= n)"
  by auto



theorem toint_lower_bound:
  "\<lbrakk>bs \<noteq> []\<rbrakk> \<Longrightarrow> (- (2 ^ ((length bs) - 1))) \<le> TwosComplement__toInt bs"
   apply(cut_tac x=bs in TwosComplement__integer_range)
   apply (simp add:not_empty_from_length)
   apply (simp add:TwosComplement__rangeForLength_def TwosComplement__minForLength_def)
   done

theorem toint_lower_bound_chained [simp]:
  "\<lbrakk>bs \<noteq> [] ; k <= (- (2 ^ ((length bs) - 1))) \<rbrakk> \<Longrightarrow> k \<le> TwosComplement__toInt bs"
   apply(cut_tac bs=bs in toint_lower_bound)
   apply(simp_all del:toint_lower_bound)
   done


theorem toint_upper_bound:
  "\<lbrakk>bs \<noteq> []\<rbrakk> \<Longrightarrow> TwosComplement__toInt bs < (2 ^ ((length bs) - 1))"
   apply(cut_tac x=bs in TwosComplement__integer_range)
   apply (simp add:not_empty_from_length)
   apply (simp add:TwosComplement__rangeForLength_def TwosComplement__maxForLength_def)
   done

theorem toint_upper_bound_chained [simp]:
  "\<lbrakk>bs \<noteq> []; k >= (2 ^ ((length bs) - 1))\<rbrakk> \<Longrightarrow> TwosComplement__toInt bs < k"
  apply(cut_tac bs=bs in toint_upper_bound)
  apply(simp_all del:toint_upper_bound)
  done

theorem toint_upper_bound_chained_leq [simp]:
  "\<lbrakk>bs \<noteq> []; k >= ((2 ^ ((length bs) - 1)) - 1)\<rbrakk> \<Longrightarrow> TwosComplement__toInt bs <= k"
  apply(cut_tac k="k + 1" in toint_upper_bound_chained)
  apply(simp_all del:toint_upper_bound_chained)
  done





theorem toNat_bound_chained [simp]: 
  "\<lbrakk>bs \<noteq> [] ; k \<ge> (2 ^ (length bs)) \<rbrakk> \<Longrightarrow> toNat bs < k"
  apply(cut_tac bs=bs in Bits__toNat_bound)
  apply(simp_all  del:Bits__toNat_bound)
done

theorem toNat_bound_chained_int_version [simp]: 
  "\<lbrakk>bs \<noteq> [] ; nat k \<ge> (2 ^ (length bs)) \<rbrakk> \<Longrightarrow> int (toNat bs) < k"
  apply(cut_tac bs=bs and k="nat k" in toNat_bound_chained)
  apply(simp_all  del:Bits__toNat_bound toNat_bound_chained)
done

theorem toNat_bound_chained_leq [simp]: 
  "\<lbrakk>bs \<noteq> [] ; k \<ge> (2 ^ (length bs)) - 1 \<rbrakk> \<Longrightarrow> toNat bs <= k"
  apply(cut_tac k="k + 1" in toNat_bound_chained)
  apply(auto simp del:toNat_bound_chained)
done

(*
theorem toNat_bound_chained_int_version_2 [simp]: 
  "\<lbrakk>bs \<noteq> [] ; nat k \<ge> (2 ^ (length bs)) - 1 \<rbrakk> \<Longrightarrow> int (toNat bs) <= k"
  apply(cut_tac k="k + 1" in toNat_bound_chained_int_version)
  apply(simp, simp)
  defer 1
  apply(simp)
done
*)



theorem mod_upper_bound_chained:
 "\<lbrakk> (n::int) > 0 ; k \<ge> n - 1 \<rbrakk> \<Longrightarrow> (m::int) mod n \<le> k"
  apply(cut_tac a=m and b=n in Divides.pos_mod_bound)
  apply(force)
  apply(simp del: Divides.pos_mod_bound)
  done

theorem mod_lt_chained:
 "\<lbrakk> (n::int) > 0 ; k \<ge> n \<rbrakk> \<Longrightarrow> (m::int) mod n < k"
  apply(cut_tac a=m and b=n in Divides.pos_mod_bound)
  apply(force)
  apply(simp del: Divides.pos_mod_bound)
  done

theorem int_expt [simp]:
  "int (2 ^ (n::nat)) = 2 ^ n"
  apply(simp add: Int.int_power)
  done

theorem mod_lower_bound_chained:
 "\<lbrakk> (n::int) > 0 ; k \<le> 0\<rbrakk> \<Longrightarrow> k \<le> (m::int) mod n"
  apply(cut_tac a=m and b=n in Divides.pos_mod_sign)
  apply(force)
  apply(simp del: Divides.pos_mod_sign)
  done

theorem mod_minus_dividend [simp]:
  "(m - n) mod (n::int) = m mod n"
  apply(cut_tac a="m - n" and b = n in Divides.semiring_div_class.mod_add_self2)
  apply(force)
  done

theorem not_negative_from_bound:
  "\<lbrakk>length bs = (8\<Colon>nat); toNat bs \<le> (127\<Colon>nat)\<rbrakk> \<Longrightarrow> TwosComplement__nonNegative_p bs"
  apply(cut_tac b = "(hd bs)" and bs = "(tl bs)" in Bits__toNat_induct, force)
  apply(case_tac "(hd bs)")
  apply(cut_tac x = bs in TwosComplement__nonNegative_p_alt_def, force)
  apply(simp add: TwosComplement__sign_def)
  apply(simp)
  done


theorem mod_does_nothing_rewrite [simp]:
  "\<lbrakk> x \<ge> 0 ; y > 0\<rbrakk> \<Longrightarrow> ((x::int) mod y = x) = (x < y)"
  apply(auto)
  defer 1
  apply(rule Divides.mod_pos_pos_trivial, force, force)
  apply(cut_tac a=x and b=y in Divides.pos_mod_bound, force)
  apply(arith)
  done

theorem mod_does_nothing_rewrite_alt [simp]:
  "\<lbrakk> x \<ge> 0 ; y > 0\<rbrakk> \<Longrightarrow> (x = (x::int) mod y) = (x < y)"
  apply(cut_tac x=x and y=y in mod_does_nothing_rewrite)
  apply(auto simp del:mod_does_nothing_rewrite)
  done


theorem not_negative_from_bound_gen_helper:
  "\<lbrakk>length bs > 1 ; toNat bs < 2 ^ ((length bs) - 1)\<rbrakk> \<Longrightarrow> hd bs = B0"
  apply(cut_tac b = "(hd bs)" and bs = "(tl bs)" in Bits__toNat_induct, force)
  apply(auto)
  done

theorem not_negative_from_bound_gen:
  "\<lbrakk>length bs > 1 ; toNat bs < 2 ^ ((length bs) - 1)\<rbrakk> \<Longrightarrow> TwosComplement__nonNegative_p bs"
  apply(cut_tac bs=bs in not_negative_from_bound_gen_helper, force, force)
  apply(cut_tac x = bs in TwosComplement__nonNegative_p_alt_def, force)
  apply(simp add: TwosComplement__sign_def)
  done

(* prove length of extendleft *)
theorem length_zeroExtend [simp]:
  "\<lbrakk> n \<ge> length bs\<rbrakk> \<Longrightarrow> length (Bits__zeroExtend(bs, (n::nat))) = n"
  apply(simp add: Bits__zeroExtend_def List__extendLeft_def)
  done


theorem length_signExtend [simp]:
  "\<lbrakk> n \<ge> length bs\<rbrakk> \<Longrightarrow> length (TwosComplement__signExtend(bs, (n::nat))) = n"
  apply(simp add: TwosComplement__signExtend_def List__extendLeft_def)
  done
	

theorem mod_of_toInt65536 [simp]:
  "\<lbrakk> length bs = 16 \<rbrakk> \<Longrightarrow> 
   (TwosComplement__toInt bs) mod (65536\<Colon>int) = int (toNat bs)"
  apply(simp add: TwosComplement__toInt_def)
  done

theorem mod_of_toInt4294967296 [simp]:
  "\<lbrakk> length bs = 32 \<rbrakk> \<Longrightarrow> 
   (TwosComplement__toInt bs) mod (4294967296\<Colon>int) = int (toNat bs)"
  apply(simp add: TwosComplement__toInt_def)
  done

theorem mod_of_toInt18446744073709551616 [simp]:
  "\<lbrakk> length bs = 64 \<rbrakk> \<Longrightarrow> 
   (TwosComplement__toInt bs) mod (18446744073709551616) = int (toNat bs)"
  apply(simp add: TwosComplement__toInt_def)
  done

theorem mod_of_toInt340282366920938463463374607431768211456 [simp]:
  "\<lbrakk> length bs = 128 \<rbrakk> \<Longrightarrow> 
   (TwosComplement__toInt bs) mod (340282366920938463463374607431768211456) = int (toNat bs)"
  apply(simp add: TwosComplement__toInt_def)
  done

theorem toBits_toNat_extend: 
  "\<lbrakk>length bs > 0 ; length bs <= len\<rbrakk> \<Longrightarrow> toBits (toNat bs, len) = Bits__zeroExtend (bs, len)"
  apply(simp add:Bits__zeroExtend_def List__extendLeft_def)
  apply(cut_tac k="len - length bs" and bs=bs in Bits__extendLeft_toNat_B0, force)
  apply(cut_tac bs="(replicate (len - length bs) B0 @ bs)" in Bits__inverse_bits_toNat, force)
  apply(simp)
  done

(* rename *)

(* lemma Bits__extendLeft_toNat_B1_new: 
   "\<lbrakk>bs \<noteq> []; hd bs = B1\<rbrakk>
    \<Longrightarrow>  TwosComplement__toInt (replicate k B1 @ bs) = TwosComplement__toInt bs"
   apply (simp add: TwosComplement__toInt_def)



theorem toBits_toNat_extend: 
  "\<lbrakk>length bs > 0 ; length bs < len ; hd bs = B1\<rbrakk> \<Longrightarrow> toBits (nat (TwosComplement__toInt bs mod 65536), 16) = TwosComplement__signExtend (bs, len)"
  apply(simp add:TwosComplement__signExtend_def List__extendLeft_def)
  apply(cut_tac k="len - length bs" and bs=bs in Bits__extendLeft_toNat_B1_new, force)
  apply(cut_tac bs="(replicate (len - length bs) B0 @ bs)" in Bits__inverse_bits_toNat, force)
  apply(simp)
  done
*)

theorem move_negated_addend:
  "((a::int) - b = c) = (a = b + c)"
  by(arith)

theorem move_negated_addend_2:
  "((a::int) = b - c) = (a + c = b)"
  by(arith)

theorem move_negated_addend_3:
  "((a::int) - b + d = c) = (a + d = b + c)"
  by(arith)


theorem zadd_int_back:
  "int (a + b) = int a + int b"
  by auto

(* drop a hyp? or allow    0 < k  OR   bs = B1 *)
lemma toInt_replicate: 
  "\<lbrakk>bs \<noteq> []; 0 < k; hd bs = B1 \<rbrakk>
   \<Longrightarrow>  TwosComplement__toInt (replicate k B1 @ bs) = TwosComplement__toInt bs"
  apply (simp add: TwosComplement__toInt_def TwosComplement__nonNegative_p_alt_def TwosComplement__sign_def List.hd_append)
  apply(cut_tac bs=bs and k=k in Bits__extendLeft_toNat_B1, force, force)
  apply(simp add: move_negated_addend move_negated_addend_2 move_negated_addend_3)
  apply(cut_tac m="toNat (replicate k B1 @ bs) + 2 ^ length bs" and n="toNat bs + 2 ^ (k + length bs)" in int_injective)
by (metis length_sublists add.commute of_nat_numeral of_nat_power zadd_int_back)


(*
theorem nonNegative_p_replicate_B1:
  "\<lbrakk> hd bs = B1 \<rbrakk> \<Longrightarrow> TwosComplement__nonNegative_p (replicate k B1 @ bs) = False"
  apply(simp add: TwosComplement__nonNegative_p_def TwosComplement__negative_p_def TwosComplement__sign_def  List.hd_append) 
  done

theorem toBits_toInt_extend: 
  "\<lbrakk>length bs > 0 ; length bs < len ; hd bs = B1\<rbrakk> \<Longrightarrow> toBits (nat (TwosComplement__toInt bs mod (2 ^ len)), len) = TwosComplement__signExtend (bs, len)"
  apply(simp add:TwosComplement__signExtend_def List__extendLeft_def TwosComplement__sign_def) 
  apply(cut_tac k="len - length bs" and bs=bs in toInt_replicate, force)
  apply(cut_tac bs="(replicate (len - length bs) B0 @ bs)" in Bits__inverse_bits_toNat, force, force, force)
  apply(simp add: TwosComplement__toInt_def)
  apply(case_tac "TwosComplement__nonNegative_p bs")
  apply(simp_all)
  done
*)




theorem extendLeft_equal_extendLeft [simp]:
 "\<lbrakk> length lst1 = length lst2 ; length lst1 \<le> len \<rbrakk> \<Longrightarrow> 
    ((List__extendLeft (lst1, val1, len) = List__extendLeft (lst2, val2, len))) = 
     ((lst1 = lst2) & (if (length lst1 = len) then True else (val1 = val2)))"
  apply(auto simp add: List__extendLeft_def)
  done


theorem zeroextend_equal_signextend [simp]:
  "\<lbrakk> length bs \<le> len \<rbrakk> \<Longrightarrow> 
  Bits__zeroExtend (bs, len) = TwosComplement__signExtend (bs, len) = (if (length bs = len) then True else TwosComplement__sign bs = B0)"
  apply(auto simp add: TwosComplement__signExtend_def Bits__zeroExtend_def)
  done

theorem toBits_move:
  "\<lbrakk> x < 2 *** len ; len > 0\<rbrakk> \<Longrightarrow> (toBits (x, len) = y) = ((x = toNat y) & (length y = len))"
  apply(cut_tac n=x and len=len in Bits__inverse_toNat_bits, force, force)
  apply(auto simp del: Bits__inverse_toNat_bits)
  done

theorem toNat__replicate_B1: 
  "\<lbrakk>bs \<noteq> []; hd bs = B1\<rbrakk>
   \<Longrightarrow>  toNat (replicate k B1 @ bs)  =
       toNat bs + 2 ^ (k + length bs) - 2 ^ length bs"
  apply(cut_tac bs=bs and k=k in Bits__extendLeft_toNat_B1, force, force)
  apply(simp)
  done

theorem minus_plus_hack_for_nats [simp]:
  " \<lbrakk> x \<ge> y\<rbrakk> \<Longrightarrow> (x::nat) - y + y = x"
  by(arith)

theorem toNat__signExtend_when_negative:
  "\<lbrakk>bs \<noteq> []; hd bs = B1 ; len \<ge> length bs\<rbrakk>
   \<Longrightarrow>  toNat (TwosComplement__signExtend(bs, len))  =
       toNat bs + 2 *** len - 2 ^ length bs"
  apply(cut_tac bs=bs and k="(len - length bs)" in toNat__replicate_B1, force, force)
  apply(simp add: TwosComplement__signExtend_def List__extendLeft_def)
  apply(simp add: TwosComplement__sign_def)
  done

theorem nat_move:
  "\<lbrakk> x >= 0\<rbrakk> \<Longrightarrow> ((nat x = y) = (x = int y))"
  apply(auto)
  done

theorem mod_known:
 "[| y \<ge> (0::int) ;y < m ;  x mod m = y mod m |]  ==> x mod m = y"
  apply(auto)
  done

theorem mod_same_lemma:
  "\<lbrakk> ((x - y) mod m) = (0::int) \<rbrakk> \<Longrightarrow> (x mod m = y mod m)"
  apply(auto simp add: move_negated_addend)
  done


theorem le_trans:
  "\<lbrakk> (a::int) \<le> b ; b \<le> c\<rbrakk> \<Longrightarrow> a \<le> c"
  by auto


theorem int_move_le:
  "\<lbrakk> y >= 0\<rbrakk> \<Longrightarrow> ((int x \<le> y) = (x \<le> nat y))"
  apply(auto)
  done


end-proof %%end large verbatim block
(*******************************************************************************************************)





refine def TwosComplement.tcNumber (i:Int, len:PosNat | i in? rangeForLength len) : TCNumber =
  bits(i mod 2 ** len, len)

proof isa -verbatim
declare List.length_map [simp add]
end-proof


theorem suffix_0 is [a]
  fa(l:List a) suffix(l,0) = []

%% theorem suffix_plus_one is [a]
%%   fa(l:List a, n:Nat)
%%     n < length l =>
%%     suffix(l, n+1) = (l@((length l) - 1 - n)) :: suffix(l,n)


theorem map_drop is [a, b]
  fa(f: a -> b, l: List a, n:Nat) (n <= length l) => ((map f (removePrefix(l,n))) = removePrefix((map f l), n))

theorem map_suffix is [a, b]
  fa(f: a -> b, l: List a, n:Nat) (n <= length l) => ((map f (suffix(l,n))) = suffix((map f l), n))



%% alternate characterization of the type of the digit list passed to fromBigEndian 
op all_less (val:Nat) (lst: List Nat) : Bool = 
   case lst of
   | [] -> true
   | hd::tl -> hd < val && all_less val tl

theorem all_less_intro is
  fa (lst: List Nat, val:Nat) (fa(d:Nat) d in? lst => d < val) = all_less val lst

theorem all_less_becomes is
  fa (lst: List Nat, val:Nat) all_less val lst = (fa(d:Nat) d in? lst => d < val)
        

%% Nice, recursive definition of fromBigEndian.  The one in IntegerExt_ExecOps is tail recursive and not as nice to reason about.
%% This one allows digits to be empty.
%% Could recharacterize the condition on digits to use a recursive function rather than a quantifier.
%% It might also be nice to have a version which directly consumes a list of B0's and B1's.
%% Could use refine def for this, but I want to be sure the tail recursive version is the one that executes.
op fromBigEndian_rec
  (digits:List Nat, base:Nat | base >= 2 && all_less base digits) : Nat =
    case digits of
    | [] -> 0
    | hd::tl -> hd * base***(length tl) + fromBigEndian_rec (tl, base)

theorem fromBigEndian_becomes        is
  fa(digits:List1 Nat, base:Nat)
    (fa(d:Nat) d in? digits => d < base) %% same as all_less base digits
     => base >= 2 => fromBigEndian(digits, base)=fromBigEndian_rec(digits, base)

theorem fromBigEndian_becomes2 is
  fa(digits:List1 Nat, base:Nat)
    all_less base digits
     => base >= 2 => fromBigEndian(digits, base)=fromBigEndian_rec(digits, base)

theorem fromBigEndian_intro is
  fa(digits:List1 Nat, base:Nat)
    all_less base digits %%(fa(d:Nat) d in? digits => d < base)
     => base >= 2 => fromBigEndian_rec(digits, base) = fromBigEndian(digits, base)


%TODO this set characterization also occurs in some frombigendian theorems.
%% theorem all_less_than_becomes2:
%%   "all_less_than(lst, val) = (\<forall>d\<in>set(lst). d<val)"

proof isa -verbatim
declare List.length_map [simp add]
declare Library__fromBigEndian_rec.simps [simp del] (* for speed *)
end-proof

proof isa -verbatim
theorem Library__fromBigEndian_rec_app:
  "Library__fromBigEndian_rec (x @ y, base) = Library__fromBigEndian_rec(x,base) * base ^ (length y) + Library__fromBigEndian_rec(y,base)"
  apply(induct_tac x)
  apply(simp add: Library__fromBigEndian_rec.simps)
  apply(simp add: Library__fromBigEndian_rec.simps Nat.add_mult_distrib Power.monoid_mult_class.power_add)
  done

theorem Library__mod_does_nothing_fw:
  "\<lbrakk> x \<ge> 0 ; y > 0 ; x < y\<rbrakk> \<Longrightarrow> ((x::int) mod y = x)"
  apply(simp add: mod_does_nothing_rewrite)
  done


theorem Library__nmod_does_nothing_rewrite [simp]:
  "\<lbrakk> x \<ge> 0 ; y > 0\<rbrakk> \<Longrightarrow> ((x::nat) mod y = x) = (x < y)"
  apply(auto)
  defer 1
by (metis mod_less_divisor)

theorem Library__nmod_does_nothing_rewrite_alt [simp]:
  "\<lbrakk> x \<ge> 0 ; y > 0\<rbrakk> \<Longrightarrow> (x = (x::nat) mod y) = (x < y)"
  apply(cut_tac x=x and y=y in Library__nmod_does_nothing_rewrite)
  apply(auto simp del:Library__nmod_does_nothing_rewrite)
  done

theorem Library__nmod_does_nothing_fw:
  "\<lbrakk> x \<ge> 0 ; y > 0 ; x < y\<rbrakk> \<Longrightarrow> ((x::nat) mod y = x)"
  apply(simp add: Library__nmod_does_nothing_rewrite)
  done



theorem arithhack2:
  "\<lbrakk> (a::int) < b ; factor >= 0 \<rbrakk> \<Longrightarrow> (a + 1) * factor \<le> (b * factor)"
  apply(case_tac "factor=0", auto)
  done

theorem arithhack3:
  "\<lbrakk> (a::int) < b ; factor >= 0 \<rbrakk> \<Longrightarrow> a * factor + factor \<le> (b * factor)"
  apply(cut_tac a=a and b=b and factor=factor in arithhack2, force, force)
  by (simp add: distrib_right)

theorem arithhack4:
  "\<lbrakk> (a::int) < b ; factor >= 0 ; term < factor \<rbrakk> \<Longrightarrow> a * factor + term < (b * factor)"
  apply(cut_tac a=a and b=b and factor=factor in arithhack3, force, force)
  apply(arith)
  done


theorem narithhack2:
  "\<lbrakk> (a::nat) < b ; factor >= 0 \<rbrakk> \<Longrightarrow> (a + 1) * factor \<le> (b * factor)"
  apply(rule Nat.mult_le_mono1, auto)
  done

theorem narithhack3:
  "\<lbrakk> (a::nat) < b ; factor >= 0 \<rbrakk> \<Longrightarrow> a * factor + factor \<le> (b * factor)"
  apply(cut_tac a=a and b=b and factor=factor in narithhack2, force, force)
  apply(simp add:Nat.add_mult_distrib)
  done

theorem narithhack4:
  "\<lbrakk> (a::nat) < b ; factor >= 0 ; term < factor \<rbrakk> \<Longrightarrow> a * factor + term < (b * factor)"
  apply(cut_tac a=a and b=b and factor=factor in narithhack3, force, force)
  apply(arith)
  done

lemma Library__fromBigEndian_rec_bound [simp]:
  "\<lbrakk>base\<ge>2; Library__all_less base digits\<rbrakk> 
     \<Longrightarrow> Library__fromBigEndian_rec (digits,base) < base ^ (length digits)"
  apply(induct digits, simp_all add:Library__fromBigEndian_rec.simps)
  apply(auto)
  apply(rule narithhack4, force, force, force)
  done

theorem Library__fromBigEndian_rec_app_mod:
  "\<lbrakk> Library__all_less base digits ; base\<ge>2\<rbrakk> \<Longrightarrow> Library__fromBigEndian_rec (moredigits @ digits, base) mod (base^(length digits)) = Library__fromBigEndian_rec(digits,base)"
  apply(simp add: Library__fromBigEndian_rec_app)
  done

theorem all_less_tl [simp]:
  "\<lbrakk> 0 < length lst ;Library__all_less val lst \<rbrakk> \<Longrightarrow> Library__all_less val (tl lst)"
  apply(case_tac lst, auto)
done


theorem all_less_drop [simp]:
  "\<lbrakk> n <= length lst ; Library__all_less val lst \<rbrakk> \<Longrightarrow> Library__all_less val (drop n lst)"
  apply(induct n)
  apply(force)
  apply(auto simp add: List.drop_Suc List.drop_tl)
done


theorem Library__fromBigEndian_rec_drop:
  "\<lbrakk> n \<le> length digits ; Library__all_less base digits ; base \<ge> 2\<rbrakk> \<Longrightarrow>
     Library__fromBigEndian_rec (drop n digits, base) =
     Library__fromBigEndian_rec (digits, base) mod base ^ (length digits - n)"
  apply(cut_tac base="base" and moredigits="take n digits" and digits="drop n digits" in Library__fromBigEndian_rec_app_mod)
  apply(force, force)
apply(simp add: List.append_take_drop_id)
done


theorem Library__fromBigEndian_rec_mod:
 "\<lbrakk>n <= length digits ; Library__all_less base digits ; base \<ge> 2\<rbrakk> \<Longrightarrow> 
  Library__fromBigEndian_rec (digits, base) mod base^(n::nat) = Library__fromBigEndian_rec (List__suffix (digits, n), base)"
  apply(simp add: SW_List.List__suffix_alt Library__fromBigEndian_rec_drop)
done


theorem fromBigEndian_mod:
 "\<lbrakk>length digits > 0 ; n <= length digits ; n > 0 ; Library__all_less 2 digits\<rbrakk> \<Longrightarrow> 
  Integer__fromBigEndian (digits, 2) mod 2^(n::nat) = Integer__fromBigEndian (List__suffix (digits, n), 2)"
  apply(cut_tac base=2 and digits=digits in Library__fromBigEndian_becomes2)
  apply(force, force, force)
  apply(simp add: Library__fromBigEndian_becomes2 SW_List.List__suffix_alt)
  apply(cut_tac base=2 and digits="drop (length digits - n) digits" in Library__fromBigEndian_becomes2)
  apply(force, force, force)
  apply(cut_tac base=2 and digits=digits and n="length digits - n" in Library__fromBigEndian_rec_drop)
  apply(auto)
  done

(* This may match better when n is a constant (because the 2^n will get computed) *)
theorem fromBigEndian_suffix:
 "\<lbrakk>length digits > 0 ; n <= length digits ; n > 0 ; Library__all_less 2 digits\<rbrakk> \<Longrightarrow> 
  Integer__fromBigEndian (List__suffix (digits, n), 2) = Integer__fromBigEndian (digits, 2) mod 2^(n::nat)"
  apply(cut_tac n=n and digits=digits in fromBigEndian_mod)
  apply(auto)
  done

theorem all_less_map_toNat2 [simp]:
  "Library__all_less (2\<Colon>nat) (map toNat2 bs)"
  apply(induct bs)
  apply(auto)
done


theorem mod_diff_drop_right:
  "\<lbrakk> (y::int) mod m = 0 \<rbrakk> \<Longrightarrow> (x - y) mod m = x mod m"
  apply(cut_tac x=x and y=y and m=m in Divides.zdiff_zmod_right)
  apply(simp)
  done

theorem nat_expt [simp]:
  "\<lbrakk> base \<ge> 0\<rbrakk> \<Longrightarrow> (nat (base ^ n)) = (nat base) ^ n"
  thm Int.nat_power_eq
  apply(simp add: Int.nat_power_eq)
  done

theorem expt_dvd_expt_nat:
 "\<lbrakk>(base::nat) > 1\<rbrakk> \<Longrightarrow> (base ^ m dvd base ^ n) = (m \<le> n)"
  apply(safe)
  apply(cut_tac i=base and m=m and n=n in Power.power_dvd_imp_le, force, force, force)
  apply(cut_tac a=base and m=m and n=n in Power.comm_semiring_1_class.le_imp_power_dvd, force, force)
  done

theorem expt_dvd_expt_int [simp]:
 "\<lbrakk>(base::int) > 1\<rbrakk> \<Longrightarrow> (base ^ m dvd base ^ n) = (m \<le> n)"
  apply(cut_tac base="nat base" and m=m and n=n in expt_dvd_expt_nat, force)
  apply(cut_tac x="base ^ m" and y="base ^ n" in Nat_Transfer.transfer_nat_int_relations(4))
  apply(force)
  apply(force)
  apply(auto)
  done

theorem toInt_mod [simp]:
 "\<lbrakk>length bs \<ge> n\<rbrakk> \<Longrightarrow> TwosComplement__toInt bs mod 2^n = int (toNat bs mod 2^n)"
  apply(simp add: TwosComplement__toInt_def Divides.zmod_int, auto)
  apply(rule mod_diff_drop_right)
  apply(cut_tac i="(2\<Colon>int) ^ length bs" and j="(2\<Colon>int) ^ n" in SW_Integer.Integer__divides_iff_modF_0, force)
  apply(auto simp add: Power.power_dvd_imp_le)
  done

theorem toInt_mod_256 [simp]:
 "\<lbrakk>length bs \<ge> 8\<rbrakk> \<Longrightarrow> TwosComplement__toInt bs mod 256 = int (toNat bs mod 256)"
  apply(cut_tac n=8 in toInt_mod)
  apply(auto)
  done

theorem toInt_mod_65536 [simp]:
 "\<lbrakk>length bs \<ge> 16\<rbrakk> \<Longrightarrow> TwosComplement__toInt bs mod 65536 = int (toNat bs mod 65536)"
  apply(cut_tac n=16 in toInt_mod)
  apply(auto)
  done

theorem toInt_mod_4294967296 [simp]:
 "\<lbrakk>length bs \<ge> 32\<rbrakk> \<Longrightarrow> TwosComplement__toInt bs mod 4294967296 = int (toNat bs mod 4294967296)"
  apply(cut_tac n=32 in toInt_mod)
  apply(auto)
  done


theorem toInt_mod_18446744073709551616 [simp]:
 "\<lbrakk>length bs \<ge> 64\<rbrakk> \<Longrightarrow> TwosComplement__toInt bs mod 18446744073709551616 = int (toNat bs mod 18446744073709551616)"
  apply(cut_tac n=64 in toInt_mod)
  apply(auto)
  done


declare BitList.Bits__inverse_toNat_bits [simp add]

(* todo think about n=0. tonat not defined? *)
theorem toNat_suffix:
  "\<lbrakk>n > 0 ; n \<le> length bs\<rbrakk> \<Longrightarrow> toNat (List__suffix (bs, n\<Colon>nat)) = toNat bs mod 2 ^ n"
  apply(case_tac "n=0")
  apply(simp)
  apply(simp add: toNat_def Library__map_suffix fromBigEndian_suffix)
done

theorem toNat_mod:
  "\<lbrakk>n > 0 ; n <= length bs\<rbrakk> \<Longrightarrow> toNat bs mod 2 ^ n = toNat (List__suffix (bs, n\<Colon>nat))"
  apply(cut_tac toNat_suffix, auto)
done


(* TODO see toBits_mod in BitList *)
theorem toBits_mod_toNat:
  "\<lbrakk> n > 0 ; length bs \<ge> n \<rbrakk> \<Longrightarrow> toBits ((toNat bs) mod 2^n, n\<Colon>nat) = List__suffix(bs, n) "
  apply(rule Bits__toNat_inject_rule)
  apply(simp add: toNat_suffix BitList.Bits__bits_length)
  apply(simp)
  apply(simp)
  done


declare TwosComplement__rangeForLength_def [simp]
declare TwosComplement__minForLength_def [simp]
declare TwosComplement__maxForLength_def [simp]
declare fun_Compl_def [simp]

theorem le_int_hack [simp]:
  "(65408 \<le> int x) = (65408 \<le> x)"
  by auto

theorem le_int_hack2 [simp]:
  "(int x \<le> 65663) = (x \<le> 65663)"
  by auto

theorem must_be_high:
  "\<lbrakk> (x::nat) < 256 ; y < 256 \<rbrakk> \<Longrightarrow> (65408 \<le> x * 256 + y) = (x=255 \<and> y \<ge> 128)"
  apply(arith)
  done

theorem nth_to_hd: 
  "\<lbrakk>xs \<noteq> []\<rbrakk> \<Longrightarrow> xs ! 0 = hd xs"
  by (simp add:List.hd_conv_nth)



theorem drop_to_tail: 
  "\<lbrakk>0 < length bs\<rbrakk> \<Longrightarrow> drop (Suc 0) bs = tl bs"
  apply (cut_tac l=bs in SW_List.List__tail__def)
  apply(force)
  apply(simp)
  done

theorem hd_cons_drop_1:
  "\<lbrakk> bs \<noteq> []\<rbrakk> \<Longrightarrow> (hd bs # drop (Suc 0) bs) = bs"
  apply(auto simp add: drop_to_tail)
  done

theorem toNat_split_top_8:
  "\<lbrakk>length bs = 8\<rbrakk> \<Longrightarrow> (toNat bs) = (128 * toNat([bs ! 0]) + toNat(drop 1 bs))"
  apply(cut_tac b="(bs ! 0)" and bs="drop 1 bs" in BitList.Bits__toNat_induct, force)
  apply(simp del: BitList.Bits__toNat_induct SW_List.List__tail__def add: nth_to_hd)
  apply(cut_tac bs=bs in hd_cons_drop_1, force)
  apply(simp only:)
  done

theorem hd_suffix:
  "\<lbrakk> n \<le> length lst ; n > 0\<rbrakk> \<Longrightarrow> hd (List__suffix (lst, n)) = lst!(length lst - n)"
  apply(simp add: SW_List.List__suffix_alt List.hd_drop_conv_nth)
  done

theorem all_less_empty [simp]:
  "Library__all_less val []"
  apply(simp)
  done

theorem all_less_app [simp]:
  "Library__all_less val (x @ y) = ((Library__all_less val x) \<and> (Library__all_less val y))"
  apply(induct_tac x)
  apply(simp only: all_less_empty List.append.append_Nil HOL.simp_thms(22))
  defer 1
  apply(simp)
done

theorem toNat_app:
  "\<lbrakk> x \<noteq> [] ; y \<noteq> [] \<rbrakk> \<Longrightarrow> toNat (x @ y) = toNat(x) * 2 ^ (length y) + toNat(y)"
  apply(simp add: toNat_def Library__fromBigEndian_becomes2 Library__fromBigEndian_rec_app)
  done

theorem take_one [simp]:
  "\<lbrakk> bs \<noteq> [] \<rbrakk> \<Longrightarrow> (take (Suc 0) bs) = (bs ! 0) # []"
  apply(simp add: take_Suc List.hd_conv_nth)
done

theorem nth_0_cons_drop [simp]:
  "\<lbrakk> bs \<noteq> [] \<rbrakk> \<Longrightarrow> (bs ! 0 # drop (Suc 0) bs) = bs"
  apply(cut_tac n=1 and xs=bs in List.append_take_drop_id)
  apply(simp)
  done

theorem toNat_bound_false:
  "\<lbrakk>k \<ge> 2 ^ length bs ; bs \<noteq> []\<rbrakk> \<Longrightarrow> (k \<le> toNat bs) = False"
  apply(cut_tac bs=bs in Bits__toNat_bound)
  apply(force)
  apply(arith)
  done

theorem top_bit_one:
  "\<lbrakk> length bs = 8\<rbrakk> \<Longrightarrow> ((128 \<le> toNat bs) = (bs ! 0 = B1))"
  apply(simp add: toNat_split_top_8)
  apply(auto)
  apply(case_tac "bs ! 0 = B0")
  apply(simp_all)
  apply(simp add: toNat_bound_false)
done


  

theorem expt_lower_bound:
  "(2::nat) ^ (n::nat) >= 1"
  apply(auto)
  done

theorem toNat_bound_when_one:
  "\<lbrakk> hd bs = B1 ; bs \<noteq> []\<rbrakk> \<Longrightarrow> toNat bs \<ge> 1"
  apply(simp add: toNat_def Library__fromBigEndian_becomes2 Library__fromBigEndian_rec_app)
  apply(case_tac bs)
  apply(force)
  apply(simp add: Library__fromBigEndian_rec.simps)
  apply(auto)
  apply(cut_tac n="length list" in expt_lower_bound)
  apply(arith)
  done


theorem hd_take [simp]:
  "\<lbrakk> n <= length lst ; n > 0\<rbrakk> \<Longrightarrow> hd (take n lst) = hd lst"
  apply(case_tac lst)
  apply(auto simp add: take_Cons)
  apply(case_tac "n=0")
  apply(simp)
  apply(cases n)
  apply(auto)
  done


(* TODO kill the other one? *)
theorem toNat_bound_when_one_better:
  "\<lbrakk> hd bs = B1 ; bs \<noteq> []\<rbrakk> \<Longrightarrow> toNat bs \<ge> 2 ^ ((length bs) - 1)"
  apply(simp add: toNat_def Library__fromBigEndian_becomes2 Library__fromBigEndian_rec_app)
  apply(case_tac bs)
  apply(force)
  apply(simp add: Library__fromBigEndian_rec.simps)
done

theorem toNat_bound2:
  "\<lbrakk> bs ! n = B1 ; n < length bs ; n > 0 \<rbrakk> \<Longrightarrow> toNat bs \<ge> 2 ^ (length bs - n - 1)"
  apply(cut_tac x="(take n bs)" and y="drop n bs" in toNat_app)
  apply(force)
  apply(simp)
  apply(simp add: List.append_take_drop_id)
  apply(cut_tac bs="(drop n bs)" in toNat_bound_when_one_better)
  apply(simp add:List.hd_drop_conv_nth)
  apply(simp)
  apply(simp add:  add:List.length_drop)
  done
  
theorem mod_known_nat:
 "[| y \<ge> (0::nat) ;y < m ;  x mod m = y mod m |]  ==> x mod m = y"
  apply(auto)
  done

theorem move_constant_hack:
  "((x::nat) - 65280 < 256) = (x < 65536)"
by auto


theorem mod_diff_drop_right_nat:
  "\<lbrakk> y \<le> x ; (y::nat) mod m = 0 \<rbrakk> \<Longrightarrow> (x - y) mod m = x mod m"
  thm Divides.zdiff_zmod_right
  thm Divides.ring_div_class.mod_diff_right_eq
  apply(cut_tac a=x and b=y and c=m in mod_sub_right_eq)
  apply(simp)
  apply(simp)
  done

lemmas TC_lemmas =
  TwosComplement__rangeForLength_def
  TwosComplement__nonNegative_p_def
  TwosComplement__negative_p_def
  TwosComplement__sign_def

theorem setToPred_negate_Collect:
"setToPred (- Collect P) = (\<lambda>(x::'a) . \<not> (P x))"
by (metis Compl_iff mem_Collect_eq setToPred_def)

declare setToPred_negate_Collect [simp add]

lemma toNat_int_bound:
  "\<lbrakk>length bs = n; n \<ge> 8\<rbrakk> \<Longrightarrow> \<not> (2^n \<le> int (toNat bs))"
  by (auto simp add: zle_int not_le)

theorem must_be_high_generic:
  "\<lbrakk> (x::nat) < 2^(k - n) ; y < 2^n; n < k; 0 < n\<rbrakk> 
   \<Longrightarrow>   (- (2^(n - 1)) \<le> int (x * 2^n) + int y - 2^k)
      = (x = 2^(k - n) - 1 \<and> y \<ge> 2^(n - 1))"
  apply (simp add: algebra_simps, 
         simp only: zpower_int convert_to_nat zadd_int int_int_eq 
                    zless_int zle_int)
  apply (rule iffI, rotate_tac -1, rule context_conjI, auto)
  defer
  (* Goal 2 *)
  apply (rule classical, erule rev_mp,  simp add: not_le)
  apply (rule_tac t="(2^(k - n) - Suc 0) * 2^n + 2^(n - Suc 0)" 
              and s="2^k - 2^(n - Suc 0)"
         in subst,
         simp add: diff_mult_distrib power_add [symmetric],
         simp add: power_sub_1_eq_nat )
  apply (rotate_tac -1, drule_tac k="2^k - 2^(n - Suc 0)" in add_less_mono1, 
         simp)
  (* Goal 3 *)
  apply (rule_tac t="(2^(k - n) - Suc 0) * 2^n + 2^(n - Suc 0)" 
              and s="2^k - 2^(n - Suc 0)"
         in subst,
         simp add: diff_mult_distrib power_add [symmetric],
         simp add: power_sub_1_eq_nat )
  apply (rotate_tac -1, drule_tac k="2^k - 2^(n - Suc 0)" in add_le_mono1, 
         simp)
  (* Goal 1 *)
  apply (rule classical, auto simp add: nat_neq_iff,  erule rev_mp, 
         simp add: not_le less_eq_Suc_le, thin_tac _)
  apply (simp only: add_Suc [symmetric])
        (*** replace y by upper bound **)
  apply (drule_tac c="x * 2^n + 2^(n - Suc 0)" in add_right_mono,
         erule order_trans)
        (*** replace x by upper bound **)
  apply (rotate_tac -1, frule rev_mp, subst Suc_eq_plus1,
         subst le_diff_conv2 [symmetric], auto, thin_tac _)
  apply (rotate_tac -1, drule_tac c="2^n" in mult_right_mono, simp,
         rotate_tac -1, drule_tac c="2^(n - Suc 0)" in add_right_mono,
         rotate_tac -1, drule_tac c="2^n" in add_left_mono,
         erule order_trans)
        (*** now do the math ***)
  apply (frule_tac Integer__expt_monotone, subst add.commute)
  apply (simp add: diff_mult_distrib power_add [symmetric] mult_2 [symmetric]
                   add.assoc [symmetric]  
              )
  apply (cut_tac x=n in power_sub_1_eq_nat, auto)
done


theorem toInt_suffix:
  "\<lbrakk>TwosComplement__toInt bs \<in> TwosComplement__rangeForLength n ;
    n>0; length bs \<ge> n\<rbrakk> \<Longrightarrow> 
  TwosComplement__toInt (List__suffix (bs, n)) = TwosComplement__toInt bs"
  apply(case_tac "length bs = n", simp, drule le_neq_trans, simp)
  apply(auto simp add: TwosComplement__toInt_def TC_lemmas 
                        toNat_suffix  hd_suffix)
  apply(cases "hd bs = B0", simp_all)
  apply(cut_tac x="take (length bs - n) bs" and y="drop (length bs - n) bs" 
            in toNat_app, auto, rotate_tac -1, thin_tac _)
  apply(cut_tac bs="drop (length bs -n) bs" and len=n in Bits__toNat_hd_1, auto)
  apply(cut_tac x="toNat(take (length bs - n) bs)" 
            and y="toNat(drop (length bs - n) bs)" 
            and n=n and k="length bs" in must_be_high_generic, auto)
  apply(rotate_tac -1, erule rev_mp, simp,
        subst hd_conv_nth, simp, simp add: nth_drop)
  (**** now the same argument again ****)
  apply(cut_tac x="take (length bs - n) bs" and y="drop (length bs - n) bs" 
            in toNat_app, auto)
  apply (cut_tac bs="drop (length bs -n) bs" and len=n in Bits__toNat_hd_0,
         simp, simp, simp)
  apply(rotate_tac -1, erule rev_mp, subst hd_conv_nth, simp, simp add: nth_drop)
  (**** and again ****)
  apply(cut_tac x="take (length bs - n) bs" and y="drop (length bs - n) bs" 
            in toNat_app, auto)
  apply(cut_tac x="toNat(take (length bs - n) bs)" 
            and y="toNat(drop (length bs - n) bs)" 
            and n=n and k="length bs" in must_be_high_generic, auto)
  apply (simp add: field_simps,
         simp only: zpower_int convert_to_nat zadd_int int_int_eq 
                    zless_int zle_int)
  apply (simp add: mult_Suc_right [symmetric] power_add [symmetric])
done


theorem div_le_dividend_rule: 
  "\<lbrakk>k \<ge> m\<rbrakk> \<Longrightarrow> (m::nat) div n \<le> k"
  thm Divides.div_le_dividend
  apply(cut_tac m=m and n=n in Divides.div_le_dividend)
  apply(arith)
  done

theorem zdiv_le_dividend:
  "\<lbrakk> m \<ge> 0 ; n > 0\<rbrakk> \<Longrightarrow> (m\<Colon>int) div n \<le> m"
  apply(cut_tac a=m and b'=1 and b=n in Divides.zdiv_mono2)
  apply(force, force, force)
  apply(simp)
  done

theorem zdiv_le_dividend_rule: 
  "\<lbrakk>k \<ge> m ; m\<ge> 0 ; n > 0\<rbrakk> \<Longrightarrow> (m::int) div n \<le> k"
  apply(cut_tac m=m and n=n in zdiv_le_dividend)
  apply(force, force)
  apply(arith)
  done


theorem div_ge_0_chained [simp]:
  "\<lbrakk> (k::int) \<le> 0 ; x \<ge> 0 ; y\<ge>0\<rbrakk> \<Longrightarrow> k \<le> (x div y)"
  apply(cut_tac x=x and y=y in Divides.transfer_nat_int_function_closures(1))
  apply(simp_all)
  done


theorem divT_is_div_if_non_neg:
  "\<lbrakk>(j::int) > 0; i \<ge> 0\<rbrakk> \<Longrightarrow> i divT j = i div j"
  by (auto simp add: divT_def abs_if not_less_iff_gr_or_eq)



end-proof
  
  



(***************************** Proofs start here ******************************)

proof isa fromBigEndian_becomes_Obligation_subtype
  by (auto simp add: Library__all_less_becomes)
end-proof

proof isa all_less_intro
  apply(induct lst)
  apply(auto)
end-proof

proof isa Library__all_less_becomes
  apply (cut_tac val=val and lst=lst in Library__all_less_intro, simp)
end-proof

proof isa fromBigEndian_becomes
  apply(induct digits)
  apply(force)
  apply(simp)
  apply(case_tac "digits=[]")
  apply(simp add: Integer__fromBigEndian_base Library__all_less_becomes)
  apply(cut_tac base=base and digits=digits and a=a in Integer__fromBigEndian_induct)
  apply(force, force)
  apply(simp add: Integer__fromBigEndian_base Library__all_less_becomes)
  apply(force)
  apply(case_tac digits)
  apply(simp)
  apply(arith)
end-proof

proof isa fromBigEndian_intro_Obligation_subtype
  by (auto simp add: Library__all_less_becomes)
end-proof

proof isa fromBigEndian_becomes2_Obligation_subtype
  by (auto simp add: Library__all_less_becomes)
end-proof

proof isa fromBigEndian_becomes2
  apply(simp add: Library__fromBigEndian_becomes Library__all_less_becomes)
end-proof

proof isa fromBigEndian_intro
  apply(cut_tac base=base and digits=digits in Library__fromBigEndian_becomes, force)
  apply(simp add: Library__all_less_becomes, auto)
end-proof

proof isa TwosComplement__tcNumber__2__obligation_refine_def
  apply(simp add: TwosComplement__tcNumber__2_def)
  apply(case_tac "i \<ge> 0")
  apply(simp add: TwosComplement_TC_toBits_pos2)
  apply(simp add: TwosComplement__rangeForLength_def TwosComplement__maxForLength_def nat_injective)
  apply(simp add: TwosComplement_TC_toBits_neg TwosComplement__rangeForLength_def TwosComplement__minForLength_def)
  apply(cut_tac m = "(i mod 2 ^ len)" and n="(i + 2 ^ len)" in nat_injective)
  defer 1
  apply(force)
  apply(cut_tac x=i and m="2 ^ len" and y = "i + 2 ^ len" in mod_known)
  apply(auto)
  apply(cut_tac a="- (2 ^ len)" and b = "- (2 ^ (len - Suc 0))" and c=i in le_trans, force, force)
  apply(cut_tac m="len - Suc 0" and n = len in Integer__expt_monotone, force, force)
  apply(cut_tac a="- (2 ^ len)" and b = "- (2 ^ (len - Suc 0))" and c=i in le_trans, force, force)
  apply(cut_tac m="len - Suc 0" and n = len in Integer__expt_monotone, force, force)
  apply(cut_tac a="- (2 ^ len)" and b = "- (2 ^ (len - Suc 0))" and c=i in le_trans, force, force)
  apply(cut_tac m="len - Suc 0" and n = len in Integer__expt_monotone, force, force)
end-proof

proof isa toNat_bound_rule
  apply(cut_tac Bits__toNat_bound [of "bs"])
  defer 1
  apply(simp)
  apply(cut_tac m="length bs" and n="8" in Integer__expt_monotone)
  apply(simp)
  apply(simp del: Bits__toNat_bound)
end-proof

proof isa suffix_0 [simp]
  apply(simp add: List__suffix__1__obligation_refine_def List__suffix__1_def)
end-proof

proof isa map_suffix
  apply (auto simp add: List__suffix__1__obligation_refine_def List__suffix__1_def List.drop_map)
end-proof

proof isa map_drop
  apply(simp add: List.drop_map)
end-proof

proof isa TwosComplement__tcNumber__2_Obligation_exhaustive
sorry
end-proof

endspec
