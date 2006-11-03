theory SW_Integer
imports SW_Nat Compare Functions
begin
consts Integer__natural_p :: "int \<Rightarrow> bool"
axioms Integer__backward_compatible_unary_minus_def: "- i = - i"
axioms Integer__negative_integers: 
  "\<lbrakk>\<not> (Integer__natural_p i)\<rbrakk> \<Longrightarrow> 
   \<exists>n. (n \<ge> 0 \<and> Nat__posNat_p n) \<and> i = - n"
axioms Integer__negative: 
  "\<lbrakk>n \<ge> 0; Nat__posNat_p n\<rbrakk> \<Longrightarrow> \<not> (Integer__natural_p (- n))"
axioms Integer__unary_minus_injective_on_positives: 
  "\<lbrakk>
   n2 \<ge> 0; Nat__posNat_p n2; n1 \<ge> 0; Nat__posNat_p n1; n1 \<noteq> n2\<rbrakk> \<Longrightarrow> 
   - n1 \<noteq> - n2"
axioms Integer__minus_negative: 
  "\<lbrakk>n \<ge> 0; Nat__posNat_p n\<rbrakk> \<Longrightarrow> - (- n) = n"
axioms Integer__minus_zero: "- 0 = 0"
types Integer__NonZeroInteger = "int"
axioms Integer__abs_subtype_constr: "abs dom_abs \<ge> 0"
consts Integer__compare :: "int \<times> int \<Rightarrow> Compare__Comparison"
consts Integer__pred :: "int \<Rightarrow> int"
consts Integer__gcd :: "int \<times> int \<Rightarrow> Nat__PosNat"
axioms Integer__gcd_subtype_constr: 
  "Integer__gcd dom_gcd \<ge> 0 \<and> Nat__posNat_p (Integer__gcd dom_gcd)"
consts Integer__lcm :: "int \<times> int \<Rightarrow> int"
axioms Integer__lcm_subtype_constr: "Integer__lcm dom_lcm \<ge> 0"
axioms Integer__addition_def1: "i + 0 = i \<and> 0 + i = i"
axioms Integer__addition_def2: 
  "\<lbrakk>n2 \<ge> 0; Nat__posNat_p n2; n1 \<ge> 0; Nat__posNat_p n1\<rbrakk> \<Longrightarrow> 
   n1 + n2 = n1 + n2 
     \<and> - n1 + - n2 = - (n1 + n2) 
     \<and> n1 + - n2 
         = (if n1 \<le> n2 then 
              - (Nat__minus(n2,n1))
            else 
              Nat__minus(n1,n2)) 
     \<and> - n1 + n2 
         = (if n1 \<le> n2 then 
              Nat__minus(n2,n1)
            else 
              - (Nat__minus(n1,n2)))"
axioms Integer__subtraction_def: "x - y = x + - y"
axioms Integer__multiplication_def: 
  "0 * y = 0 
     \<and> (x + 1) * y = x * y + y 
     \<and> (x - 1) * y = x * y - y"
axioms Integer__division_def: 
  "\<lbrakk>y \<noteq> 0\<rbrakk> \<Longrightarrow> 
   x * y = z 
     = (abs z = abs x * abs y 
          \<and> (x * y \<ge> 0 \<longrightarrow> z \<ge> 0) 
          \<and> (x * y \<le> 0 \<longrightarrow> z \<le> 0))"
axioms Integer__remainder_def: 
  "\<lbrakk>y \<noteq> 0\<rbrakk> \<Longrightarrow> x * y = x - y * (x * y)"
axioms Integer__less_than_equal_def: 
  "x \<le> y = Integer__natural_p (y - x)"
axioms Integer__less_than_def: "x < y = (x \<le> y \<and> x \<noteq> y)"
defs Integer__compare_def: 
  "Integer__compare
     \<equiv> \<lambda> (x,y). 
         if x < y then Less else if x > y then Greater else Equal"
defs Integer__pred_def: "Integer__pred x \<equiv> x - 1"
end