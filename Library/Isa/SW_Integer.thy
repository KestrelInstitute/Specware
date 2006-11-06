theory SW_Integer
imports SW_Nat Compare Functions List
begin
consts Integer__natural_p :: "int \<Rightarrow> bool"
defs Integer__natural_p_def [simp]: "Integer__natural_p i \<equiv> 0 \<le> i"
axioms Integer__backward_compatible_unary_minus_def: 
  "- i = - i"
axioms Integer__negative_integers: 
  "\<lbrakk>\<not> (Integer__natural_p i)\<rbrakk> \<Longrightarrow> 
   \<exists>n. (int n \<ge> 0 \<and> Nat__posNat_p n) \<and> i = - (int n)"
axioms Integer__negative: 
  "\<lbrakk>int n \<ge> 0; Nat__posNat_p n\<rbrakk> \<Longrightarrow> \<not> (Integer__natural_p (- (int n)))"
axioms Integer__unary_minus_injective_on_positives: 
  "\<lbrakk>
   int n2 \<ge> 0; Nat__posNat_p n2; int n1 \<ge> 0; Nat__posNat_p n1; 
   n1 \<noteq> n2\<rbrakk> \<Longrightarrow> - (int n1) \<noteq> - (int n2)"
axioms Integer__minus_negative: 
  "\<lbrakk>int n \<ge> 0; Nat__posNat_p n\<rbrakk> \<Longrightarrow> - (- (int n)) = int n"
axioms Integer__minus_zero: 
  "- 0 = 0"
types Integer__NonZeroInteger = "int"
axioms Integer__abs_subtype_constr: 
  "int (abs dom_abs) \<ge> 0"
consts Integer__compare :: "int \<times> int \<Rightarrow> Compare__Comparison"
consts Integer__pred :: "nat \<Rightarrow> int"
consts Integer__gcd :: "int \<times> int \<Rightarrow> Nat__PosNat"
axioms Integer__gcd_subtype_constr: 
  "int (Integer__gcd dom_gcd) \<ge> 0 
     \<and> Nat__posNat_p (Integer__gcd dom_gcd)"
consts Integer__lcm :: "int \<times> int \<Rightarrow> nat"
axioms Integer__lcm_subtype_constr: 
  "int (Integer__lcm dom_lcm) \<ge> 0"
axioms Integer__addition_def1: 
  "i + 0 = i \<and> 0 + i = i"
axioms Integer__addition_def2: 
  "\<lbrakk>int n2 \<ge> 0; Nat__posNat_p n2; int n1 \<ge> 0; Nat__posNat_p n1\<rbrakk> \<Longrightarrow> 
   int n1 + int n2 = int (n1 + n2) 
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
  "x - y = x + - y"
axioms Integer__multiplication_def: 
  "0 * y = 0 
     \<and> (x + 1) * y = x * y + y 
     \<and> (x - 1) * y = x * y - y"
axioms Integer__division_def: 
  "\<lbrakk>y \<noteq> 0\<rbrakk> \<Longrightarrow> 
   x * y = z 
     = (abs z = nat (int (abs x) * int (abs y)) 
          \<and> (x * y \<ge> 0 \<longrightarrow> z \<ge> 0) 
          \<and> (x * y \<le> 0 \<longrightarrow> z \<le> 0))"
axioms Integer__remainder_def: 
  "\<lbrakk>y \<noteq> 0\<rbrakk> \<Longrightarrow> x * y = x - y * (x * y)"
axioms Integer__less_than_equal_def: 
  "x \<le> y = Integer__natural_p (y - x)"
axioms Integer__less_than_def: 
  "x < y = (x \<le> y \<and> x \<noteq> y)"
defs Integer__compare_def: 
  "Integer__compare
     \<equiv> \<lambda> (x,y). 
         if x < y then Less else if x > y then Greater else Equal"
defs Integer__pred_def: "Integer__pred x \<equiv> int x - 1"
end