spec

import Library


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
declare fromBigEndian_rec.simps [simp del] (* for speed *)
end-proof

proof isa -verbatim
theorem fromBigEndian_rec_app:
  "fromBigEndian_rec (x @ y, base) = fromBigEndian_rec(x,base) * base ^ (length y) + fromBigEndian_rec(y,base)"
  apply(induct_tac x)
  apply(simp add: fromBigEndian_rec.simps)
  apply(simp add: fromBigEndian_rec.simps Nat.add_mult_distrib Power.monoid_mult_class.power_add)
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
  apply(simp add:Int.zadd_zmult_distrib)
  done

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

lemma fromBigEndian_rec_bound [simp]:
  "\<lbrakk>base\<ge>2; all_less base digits\<rbrakk> 
     \<Longrightarrow> fromBigEndian_rec (digits,base) < base ^ (length digits)"
  apply(induct digits, simp_all add:fromBigEndian_rec.simps)
  apply(auto)
  apply(rule narithhack4, force, force, force)
  done

theorem fromBigEndian_rec_app_mod:
  "\<lbrakk> all_less base digits ; base\<ge>2\<rbrakk> \<Longrightarrow> fromBigEndian_rec (moredigits @ digits, base) mod (base^(length digits)) = fromBigEndian_rec(digits,base)"
  apply(simp add: fromBigEndian_rec_app)
  done

theorem all_less_tl [simp]:
  "\<lbrakk> 0 < length lst ;all_less val lst \<rbrakk> \<Longrightarrow> all_less val (tl lst)"
  apply(case_tac lst, auto)
done


theorem all_less_drop [simp]:
  "\<lbrakk> n <= length lst ; all_less val lst \<rbrakk> \<Longrightarrow> all_less val (drop n lst)"
  apply(induct n)
  apply(force)
  apply(auto simp add: List.drop_Suc List.drop_tl)
done


theorem fromBigEndian_rec_drop:
  "\<lbrakk> n \<le> length digits ; all_less base digits ; base \<ge> 2\<rbrakk> \<Longrightarrow>
     fromBigEndian_rec (drop n digits, base) =
     fromBigEndian_rec (digits, base) mod base ^ (length digits - n)"
  apply(cut_tac base="base" and moredigits="take n digits" and digits="drop n digits" in fromBigEndian_rec_app_mod)
  apply(force, force)
apply(simp add: List.append_take_drop_id)
done


theorem fromBigEndian_rec_mod:
 "\<lbrakk>n <= length digits ; all_less base digits ; base \<ge> 2\<rbrakk> \<Longrightarrow> 
  fromBigEndian_rec (digits, base) mod base^(n::nat) = fromBigEndian_rec (List__suffix (digits, n), base)"
  apply(simp add: IntegerExt.List__suffix_alt fromBigEndian_rec_drop)
done


theorem fromBigEndian_mod:
 "\<lbrakk>length digits > 0 ; n <= length digits ; n > 0 ; all_less 2 digits\<rbrakk> \<Longrightarrow> 
  Integer__fromBigEndian (digits, 2) mod 2^(n::nat) = Integer__fromBigEndian (List__suffix (digits, n), 2)"
  apply(cut_tac base=2 and digits=digits in fromBigEndian_becomes2)
  apply(force, force, force)
  apply(simp add: fromBigEndian_becomes2 IntegerExt.List__suffix_alt)
  apply(cut_tac base=2 and digits="drop (length digits - n) digits" in fromBigEndian_becomes2)
  apply(force, force, force)
  apply(cut_tac base=2 and digits=digits and n="length digits - n" in fromBigEndian_rec_drop)
  apply(auto)
  done

(* This may match better when n is a constant (because the 2^n will get computed) *)
theorem fromBigEndian_suffix:
 "\<lbrakk>length digits > 0 ; n <= length digits ; n > 0 ; all_less 2 digits\<rbrakk> \<Longrightarrow> 
  Integer__fromBigEndian (List__suffix (digits, n), 2) = Integer__fromBigEndian (digits, 2) mod 2^(n::nat)"
  apply(cut_tac n=n and digits=digits in fromBigEndian_mod)
  apply(auto)
  done

theorem all_less_map_toNat2 [simp]:
  "all_less (2\<Colon>nat) (map toNat2 bs)"
  apply(induct bs)
  apply(auto)
done


theorem mod_diff_drop_right:
  "\<lbrakk> (y::int) mod m = 0 \<rbrakk> \<Longrightarrow> (x - y) mod m = x mod m"
  apply(cut_tac x=x and y=y and m=m in Divides.zdiff_zmod_right)
  apply(simp)
  done

theorem int_expt [simp]:
  "int (2 ^ (n::nat)) = 2 ^ n"
  apply(simp add: Int.int_power)
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
  apply(simp add: toNat_def map_suffix Library.map_suffix fromBigEndian_suffix)
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
declare mem_def [simp]
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
  apply(simp add: IntegerExt.List__suffix_alt List.hd_drop_conv_nth)
  done

theorem all_less_empty [simp]:
  "all_less val []"
  apply(simp)
  done

theorem all_less_app [simp]:
  "all_less val (x @ y) = ((all_less val x) \<and> (all_less val y))"
  apply(induct_tac x)
  apply(simp only: all_less_empty List.append.append_Nil HOL.simp_thms(22))
  defer 1
  apply(simp)
done

theorem toNat_app:
  "\<lbrakk> x \<noteq> [] ; y \<noteq> [] \<rbrakk> \<Longrightarrow> toNat (x @ y) = toNat(x) * 2 ^ (length y) + toNat(y)"
  apply(simp add: toNat_def fromBigEndian_becomes2 fromBigEndian_rec_app)
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
  apply(simp add: toNat_def fromBigEndian_becomes2 fromBigEndian_rec_app)
  apply(case_tac bs)
  apply(force)
  apply(simp add: fromBigEndian_rec.simps)
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
  apply(simp add: toNat_def fromBigEndian_becomes2 fromBigEndian_rec_app)
  apply(case_tac bs)
  apply(force)
  apply(simp add: fromBigEndian_rec.simps)
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
  apply(cut_tac a=x and b=y and c=m in IntegerExt.mod_sub_right_eq)
  apply(simp)
  apply(simp)
  done

lemmas TC_lemmas =
  TwosComplement__rangeForLength_def
  TwosComplement__nonNegative_p_def
  TwosComplement__negative_p_def
  TwosComplement__sign_def

theorem toInt_suffix:
  "\<lbrakk>length bs \<ge> n ; n > 0 ; TwosComplement__toInt bs \<in> TwosComplement__rangeForLength n ; n=8 ; length bs  =16\<rbrakk> \<Longrightarrow> 
  TwosComplement__toInt (List__suffix (bs, n)) = TwosComplement__toInt bs"
   apply(simp add:TwosComplement__toInt_def TC_lemmas  toNat_suffix  hd_suffix)
  apply(auto) 
  apply(cut_tac x="( take(length bs - 8) bs)" and y="(drop 8 bs)" in toNat_app)
  apply(force)
  apply(force)
  apply(simp add: List.append_take_drop_id)
  apply(simp add: must_be_high)
  apply(simp add: top_bit_one)
  apply(cut_tac bs=bs and n=8 in toNat_bound2)
  apply(force, force, force, force)
  apply(cut_tac x="toNat bs" and y="toNat bs - 256*255" and m=256 in mod_known_nat)
  apply(simp_all)
  apply(cut_tac bs=bs in Bits__toNat_bound)
  apply(force)
  apply(simp add: move_constant_hack)
  apply(rule mod_diff_drop_right_nat [symmetric])
  apply(force, force)
  done


  

(*
theorem must_be_high_gen_fw:
  "\<lbrakk> (x::nat) < 2^(len - n) ; y < 2 ^ n ; n < len ; n > 0 ; x < 2^(len - n) - 1\<rbrakk> \<Longrightarrow> 
    x * 2 ^ n + y < 2^len - 2^(n - 1)"
  proof -    assume A1: "x < 2^(len - n) - 1"
    assume A2: "n < len"
    assume A4: "y < 2 ^ n"
    have A3:  "x <= 2^(len - n) - 2" using A1 by auto
    have " x * 2 ^ n <= (2^(len - n) - 2) * 2^n" apply(cut_tac m=x and n=" 2^(len - n) - 1" and k="2^n" in Nat.mult_less_cancel1, simp) using A3 apply(auto) done
    then have " x * 2 ^ n <= (2^len - 2^n - 2^n)" using A2 apply(subst (asm) Nat.diff_mult_distrib)
      apply(subst (asm) Power.monoid_mult_class.power_add [symmetric])
      apply(simp)
      done
    then have " x * 2 ^ n + y <= (2^len - 2^n)" using A4 apply(cut_tac i="x * 2 ^ n" and j="(2^len - 2^n - 2^n)" and k=y and l="2^n" in Nat.add_le_mono)
      apply(force, force)
      apply(subst (asm) Library.minus_plus_hack_for_nats)
      apply(force)
    then show "x * 2 ^ n + y < 2^len - 2^(n - 1)"

  done


theorem must_be_high_gen:
  "\<lbrakk> (x::nat) < 2^(len - n) ; y < 2 ^ n ; n < len ; n > 0 \<rbrakk> \<Longrightarrow> 
    (2^len - 2^(n - 1) \<le> x * 2 ^ n + y)
  = (x=2^(len - n) - 1 \<and> y \<ge> 2 ^ (n  - 1))"
  apply(simp)
  apply(arith)
  done


theorem must_be_high_gen:
  "\<lbrakk> (x::nat) < 2^(len - n) ; y < 2 ^ n ; n=7 ; len =16 \<rbrakk> \<Longrightarrow> 
    (2^len - 2^(n - 1) \<le> x * 2 ^ n + y)
  = (x=2^(len - n) - 1 \<and> y \<ge> 2 ^ (n  - 1))"
  apply(simp)
  apply(arith)
  done

(* TODO consider n = length bs *)
theorem toInt_suffix:
  "\<lbrakk>length bs > n ; n > 0 ; TwosComplement__toInt bs \<in> TwosComplement__rangeForLength n ; length bs  =16\<rbrakk> \<Longrightarrow> 
  TwosComplement__toInt (List__suffix (bs, n)) = TwosComplement__toInt bs"
   apply(simp add:TwosComplement__toInt_def TC_lemmas  toNat_suffix  hd_suffix )
  apply(auto) 
  apply(cut_tac x="( take (length bs - n) bs)" and y="(drop (length bs - n) bs)" in toNat_app)
  apply(force)
  apply(force)
  apply(simp add: List.append_take_drop_id)



  apply(simp add: must_be_high)
  apply(simp add: top_bit_one)
  apply(cut_tac bs=bs and n=8 in toNat_bound2)
  apply(force, force, force, force)
  apply(cut_tac x="toNat bs" and y="toNat bs - 256*255" and m=256 in mod_known_nat)
  apply(simp_all)
  apply(cut_tac bs=bs in Bits__toNat_bound)
  apply(force)
  apply(simp add: move_constant_hack)
  apply(rule mod_diff_drop_right_nat [symmetric])
  apply(force, force)
  done
*)




(* theorem toInt_suffix: *)
(*   "\<lbrakk>length bs \<ge> n ; n > 0 ; TwosComplement__toInt bs \<in> TwosComplement__rangeForLength n ; n=8 ; length bs  =16\<rbrakk> \<Longrightarrow>  *)
(*   TwosComplement__toInt (List__suffix (bs, n)) = TwosComplement__toInt bs" *)
(*    apply(simp add:TwosComplement__toInt_def TC_lemmas  toNat_suffix  hd_suffix ) *)
(*   apply(auto)  *)
(*   apply(cut_tac x="( take(length bs - 8) bs)" and y="(drop 8 bs)" in toNat_app) *)
(*   apply(force) *)
(*   apply(force) *)
(*   apply(simp add: List.append_take_drop_id) *)
(*   apply(simp add: must_be_high) *)
(*   apply(simp add: top_bit_one) *)
(*   apply(cut_tac bs=bs and n=8 in toNat_bound2) *)
(*   apply(force, force, force, force) *)
(*   apply(cut_tac x="toNat bs" and y="toNat bs - 256*255" and m=256 in mod_known_nat) *)
(*   apply(simp_all) *)
(*   apply(cut_tac bs=bs in Bits__toNat_bound) *)
(*   apply(force) *)
(*   apply(simp add: move_constant_hack) *)
(*   apply(rule mod_diff_drop_right_nat [symmetric]) *)
(*   apply(force, force) *)
(*   done *)



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



end-proof



(***************** Proofs start here ******************)

proof isa fromBigEndian_becomes_Obligation_subtype
  by (auto simp add: all_less_becomes)
end-proof

proof isa all_less_intro
  apply(induct lst)
  apply(simp add:mem_def)
  apply(auto)
end-proof

proof isa all_less_becomes
  apply (cut_tac val=val and lst=lst in all_less_intro, simp)
end-proof

proof isa fromBigEndian_becomes
  apply(induct digits)
  apply(force)
  apply(simp)
  apply(case_tac "digits=[]")
  apply(simp add: Integer__fromBigEndian_base all_less_becomes)
  apply(cut_tac base=base and digits=digits and a=a in Integer__fromBigEndian_induct)
  apply(force, force)
  apply(simp add: Integer__fromBigEndian_base all_less_becomes)
  apply(force)
  apply(case_tac digits)
  apply(simp)
  apply(arith)
end-proof

proof isa fromBigEndian_intro_Obligation_subtype
  by (auto simp add: all_less_becomes)
end-proof

proof isa fromBigEndian_becomes2_Obligation_subtype
  by (auto simp add: all_less_becomes)
end-proof

proof isa fromBigEndian_becomes2
  apply(simp add: fromBigEndian_becomes all_less_becomes)
end-proof

proof isa fromBigEndian_intro
  apply(cut_tac base=base and digits=digits in fromBigEndian_becomes, force)
  apply(simp add: all_less_becomes, auto)
end-proof


end-spec
