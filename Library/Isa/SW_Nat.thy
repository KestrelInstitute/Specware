theory SW_Nat
imports SW_Integer
begin
consts Nat__natural_p :: "int \<Rightarrow> bool"
defs Nat__natural_p_def: "Nat__natural_p (i::int) \<equiv> i \<ge> 0"
consts Nat__posNat_p :: "nat \<Rightarrow> bool"
defs Nat__posNat_p_def: "Nat__posNat_p n \<equiv> n > 0"
types Nat__PosNat = "nat"
end
