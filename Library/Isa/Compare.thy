theory Compare
imports Empty
begin
datatype Compare__Comparison = Equal
                             | Greater
                             | Less
consts Compare__compare :: "Compare__Comparison \<times> Compare__Comparison \<Rightarrow> 
                            Compare__Comparison"
recdef Compare__compare "{}"
  "Compare__compare(cmp1,cmp2)
     = (if cmp1 = cmp2 then 
          Equal
        else 
          if cmp1 = Less \<or> cmp2 = Greater then Less else Greater)"
consts Boolean__compare :: "bool \<times> bool \<Rightarrow> Compare__Comparison"
recdef Boolean__compare "{}"
  "Boolean__compare(x,y)
     = (if x = y then 
          Equal
        else 
          if x = True then Greater else Less)"
end

