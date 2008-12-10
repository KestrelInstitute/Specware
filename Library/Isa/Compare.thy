theory Compare
imports Boolean
begin
datatype Compare__Comparison = Equal
                             | Greater
                             | Less
consts Compare__compare :: "Compare__Comparison \<times> Compare__Comparison \<Rightarrow> 
                            Compare__Comparison"
defs Compare__compare_def: 
  "Compare__compare
     \<equiv> (\<lambda> ((cmp1::Compare__Comparison), (cmp2::Compare__Comparison)). 
          if cmp1 = cmp2 then 
            Equal
          else 
            if cmp1 = Less \<or> cmp2 = Greater then 
              Less
            else 
              Greater)"
consts Bool__compare :: "bool \<times> bool \<Rightarrow> Compare__Comparison"
defs Bool__compare_def: 
  "Bool__compare
     \<equiv> (\<lambda> ((x::bool), (y::bool)). 
          if x = y then 
            Equal
          else 
            if x = True then Greater else Less)"
end