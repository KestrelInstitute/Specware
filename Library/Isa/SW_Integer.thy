theory SW_Integer
imports SW_Nat Compare Functions Presburger
begin
consts Integer__natural_p :: "int \<Rightarrow> bool"
axioms Integer__backward_compatible_unary_minus_def: 
  "- i = - i"
axioms Integer__negative_integers: 
  "\<lbrakk>\<not> (0 \<le> (i::int))\<rbrakk> \<Longrightarrow> 
   \<exists>(n::Nat__PosNat). Nat__posNat_p n \<and> i = - (int n)"
axioms Integer__negative: 
  "\<lbrakk>Nat__posNat_p n\<rbrakk> \<Longrightarrow> \<not> (0 \<le> - (int n))"
axioms Integer__unary_minus_injective_on_positives: 
  "\<lbrakk>Nat__posNat_p n2; Nat__posNat_p n1; n1 \<noteq> n2\<rbrakk> \<Longrightarrow> 
   - (int n1) \<noteq> - (int n2)"
axioms Integer__minus_negative: 
  "\<lbrakk>Nat__posNat_p n\<rbrakk> \<Longrightarrow> - (- (int n)) = int n"
axioms Integer__minus_zero: 
  "- 0 = 0"
theorem Integer__unary_minus_involution: 
  "- (- (i::int)) = i"
  apply(auto)
  done
types Integer__NonZeroInteger = "int"
consts Integer__abs :: "int \<Rightarrow> nat"
consts Integer__compare :: "int \<times> int \<Rightarrow> Compare__Comparison"
consts Integer__pred :: "nat \<Rightarrow> int"
consts Integer__gcd :: "int \<times> int \<Rightarrow> Nat__PosNat"
axioms Integer__gcd_subtype_constr: 
  "Nat__posNat_p (Integer__gcd dom_gcd)"
consts Integer__lcm :: "int \<times> int \<Rightarrow> nat"
theorem Integer__abs_Obligation_subsort: 
  "\<lbrakk>(x::int) \<ge> 0\<rbrakk> \<Longrightarrow> 0 \<le> x"
  apply(auto)
  done
theorem Integer__abs_Obligation_subsort0: 
  "\<lbrakk>\<not> ((x::int) \<ge> 0)\<rbrakk> \<Longrightarrow> 0 \<le> - x"
  apply(auto)
  done
defs Integer__abs_def [simp]: 
  "Integer__abs x \<equiv> (if x \<ge> 0 then nat x else nat (- x))"
recdef Integer__compare "{}"
  "Integer__compare(x,y)
     = (if x < y then Less else if x > y then Greater else Equal)"
defs Integer__pred_def [simp]: "Integer__pred x \<equiv> int x - 1"
axioms Integer__addition_def1: 
  "(i::int) + 0 = i \<and> 0 + i = i"
theorem Integer__addition_def2_Obligation_subsort: 
  "\<lbrakk>Nat__posNat_p n2; 
    Nat__posNat_p n1; 
    int (n1 + n2) = int (n1 + n2); 
    - (int n1) + - (int n2) = - (int (n1 + n2)); 
    \<not> (n1 \<le> n2)\<rbrakk> \<Longrightarrow> n2 \<le> n1"
  apply(auto)
  done
theorem Integer__addition_def2_Obligation_subsort0: 
  "\<lbrakk>Nat__posNat_p n2; 
    Nat__posNat_p n1; 
    int (n1 + n2) = int (n1 + n2); 
    - (int n1) + - (int n2) = - (int (n1 + n2)); 
    int n1 + - (int n2) 
      = (if n1 \<le> n2 then - (int (n2 - n1)) else int (n1 - n2)); 
    \<not> (n1 \<le> n2)\<rbrakk> \<Longrightarrow> n2 \<le> n1"
  apply(auto)
  done
axioms Integer__addition_def2: 
  "\<lbrakk>Nat__posNat_p n2; Nat__posNat_p n1\<rbrakk> \<Longrightarrow> 
   int (n1 + n2) = int (n1 + n2) 
     \<and> - (int n1) + - (int n2) = - (int (n1 + n2)) 
     \<and> int n1 + - (int n2) 
         = (if n1 \<le> n2 then 
              - (int (n2 - n1))
            else 
              int (n1 - n2)) 
     \<and> - (int n1) + int n2 
         = (if n1 \<le> n2 then 
              int (n2 - n1)
            else 
              - (int (n1 - n2)))"
axioms Integer__subtraction_def: 
  "(x::int) - (y::int) = x + - y"
axioms Integer__multiplication_def: 
  "0 * (y::int) = 0 
     \<and> ((x::int) + 1) * y = x * y + y 
     \<and> (x - 1) * y = x * y - y"
theorem Integer__division_def_Obligation_subsort: 
  "\<lbrakk>(y::Integer__NonZeroInteger) \<noteq> 0; 0 \<le> int (Integer__abs y)\<rbrakk> \<Longrightarrow> 
   int (Integer__abs y) \<noteq> 0"
  apply(auto)
  done
theorem Integer__division_def_Obligation_subsort0: 
  "\<lbrakk>(y::Integer__NonZeroInteger) \<noteq> 0\<rbrakk> \<Longrightarrow> 
   0 \<le> int (Integer__abs (x::int) div Integer__abs y)"
  apply(auto)
  done
axioms Integer__division_def: 
  "\<lbrakk>(y::Integer__NonZeroInteger) \<noteq> 0\<rbrakk> \<Longrightarrow> 
   (x::int) div y = (z::int) 
     = (Integer__abs z = Integer__abs x div Integer__abs y 
          \<and> (x * y \<ge> 0 \<longrightarrow> z \<ge> 0) 
          \<and> (x * y \<le> 0 \<longrightarrow> z \<le> 0))"
axioms Integer__remainder_def: 
  "\<lbrakk>(y::Integer__NonZeroInteger) \<noteq> 0\<rbrakk> \<Longrightarrow> 
   (x::int) mod y = x - y * (x div y)"
axioms Integer__less_than_equal_def: 
  "(x::int) \<le> (y::int) = (0 \<le> y - x)"
axioms Integer__less_than_def: 
  "(x::int) < (y::int) = (x \<le> y \<and> x \<noteq> y)"
end
