%% NOTE: The following files should be kept in sync:
%% Specware/Library/CGen/Library.sw
%% vTPM/Library.sw


spec

%% This file contains lemmas that could eventually be pushed into a library somewhere.
%%TODO rephrase as specware lemmas when possible.

import /Library/General/TwosComplementNumber
import /Library/General/FunctionExt
import /Library/General/OptionExt

theorem expt_monotone_helper is
  fa(n:Nat,k:Nat) (2:Nat) *** (n + k) >= 2 *** n
proof isa
  apply(induct "k")
  apply(simp_all (no_asm_simp))
end-proof

theorem expt_monotone is
  fa(m:Nat, n:Nat) (m <= n) => (2 *** m <= 2 *** n)
proof isa
  apply(rule impE [of "m<= n" "2 ^ m \<le> (2::nat) ^ n"  "2 ^ m \<le> (2::nat) ^ n"]) (* turn \<Longrightarrow> into \<longrightarrow> so we can induct on the whole implication*)
  defer 1
  apply(simp, simp)
  apply(thin_tac "m <= n")
  apply(cut_tac n=m and k="n-m" in expt_monotone_helper)
  apply(auto)
end-proof

%TODO generalize
theorem toNat_bound_rule is
 fa(bs:Bits1) length bs <= 8 => toNat bs <= 255
proof isa
  apply(cut_tac Bits__toNat_bound [of "bs"])
  defer 1
  apply(simp)
  apply(cut_tac m="length bs" and n="8" in expt_monotone)
  apply(simp)
  apply(simp del: Bits__toNat_bound)
end-proof

%%TODO generialize these lemmas (way to recognize the constant?):


%%TODO does the simp del below also apply to files that import this file?
proof isa -verbatim

(* are these the same? *)
declare Nat__digitToString_injective [simp del]
declare SW_String.Nat__digitToString_injective [simp del]



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


theorem int_lesseq127 [simp]:
  "((int n) <= (127::int)) = (n <= nat 127)"
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


theorem nat_injective:
  "\<lbrakk> n \<ge> 0 ; m \<ge> 0\<rbrakk> \<Longrightarrow> (nat n = nat m) = (m = n)"
  apply auto
  done




theorem toint_lower_bound:
  "\<lbrakk>bs \<noteq> []\<rbrakk> \<Longrightarrow> (- (2 ^ ((length bs) - 1))) \<le> TwosComplement__toInt bs"
   apply(cut_tac x=bs in TwosComplement__integer_range)
   apply (simp add:not_empty_from_length)
   apply (simp add:TwosComplement__rangeForLength_def mem_def TwosComplement__minForLength_def)
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
   apply (simp add:TwosComplement__rangeForLength_def mem_def TwosComplement__maxForLength_def)
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




theorem int_monotone:
  "(int m <= int n) = (m <= n)"
  by auto

theorem int_monotone2:
  "(int m <= int n) \<Longrightarrow> (m <= n)"
  by auto

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
  by (metis convert_to_nat_2 int_power number_of_int number_of_is_id  zadd_commute zadd_int_back zero_power2)


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

refine def tcNumber (i:Int, len:PosNat | i in? rangeForLength len) : TCNumber =
  bits(i mod 2 ** len, len)

proof isa TwosComplement__tcNumber__1__obligation_refine_def
  apply(simp add: TwosComplement__tcNumber__1_def)
  apply(case_tac "i \<ge> 0")
  apply(simp add: TwosComplement_TC_toBits_pos2)
  apply(simp add: TwosComplement__rangeForLength_def mem_def TwosComplement__maxForLength_def nat_injective)
  apply(simp add: TwosComplement_TC_toBits_neg TwosComplement__rangeForLength_def mem_def TwosComplement__minForLength_def)
  apply(cut_tac m = "(i mod 2 ^ len)" and n="(i + 2 ^ len)" in nat_injective)
  defer 1
  apply(force)
  apply(cut_tac x=i and m="2 ^ len" and y = "i + 2 ^ len" in mod_known)
  apply(auto)
  apply(cut_tac a="- (2 ^ len)" and b = "- (2 ^ (len - Suc 0))" and c=i in le_trans, force, force)
  apply(cut_tac m="len - Suc 0" and n = len in expt_monotone, force, force)
  apply(cut_tac a="- (2 ^ len)" and b = "- (2 ^ (len - Suc 0))" and c=i in le_trans, force, force)
  apply(cut_tac m="len - Suc 0" and n = len in expt_monotone, force, force)
  apply(cut_tac a="- (2 ^ len)" and b = "- (2 ^ (len - Suc 0))" and c=i in le_trans, force, force)
  apply(cut_tac m="len - Suc 0" and n = len in expt_monotone, force, force)
end-proof


endspec
