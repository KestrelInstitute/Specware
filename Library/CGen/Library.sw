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
theorem int_injective:
  "(int n = int m) = (m = n)"
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

end-proof


endspec
