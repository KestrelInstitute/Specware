theory Compare
imports Datatype
begin
datatype Compare__Comparison = Equal
                             | Greater
                             | Less
consts Compare__compare :: "Compare__Comparison \<times> Compare__Comparison \<Rightarrow> 
                            Compare__Comparison"
defs Compare__compare_def: 
  "Compare__compare
     \<equiv> \<lambda> (cmp1,cmp2). 
         if cmp1 = cmp2 then 
           Equal
         else 
           if cmp1 = Less \<or> cmp2 = Greater then Less else Greater"
consts Boolean__compare :: "bool \<times> bool \<Rightarrow> Compare__Comparison"
defs Boolean__compare_def: 
  "Boolean__compare
     \<equiv> \<lambda> (x,y). 
         if x = y then 
           Equal
         else 
           if x = True then Greater else Less"
end