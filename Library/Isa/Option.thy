theory Option
imports Compare
begin
consts Option__some :: "'a \<Rightarrow> 'a option"
defs Option__some_def: "Option__some x \<equiv> Some x"
consts Option__none :: "'a option"
defs Option__none_def: "Option__none \<equiv> None"
consts Option__some_p :: "'a option \<Rightarrow> bool"
defs Option__some_p_def: "Option__some_p x \<equiv> x \<noteq> Option__none"
consts Option__none_p :: "'a option \<Rightarrow> bool"
defs Option__none_p_def: "Option__none_p x \<equiv> x = Option__none"
consts Option__compare :: "('a \<times> 'a \<Rightarrow> Compare__Comparison) \<Rightarrow> 
                           'a option \<times> 'a option \<Rightarrow> Compare__Comparison"
end