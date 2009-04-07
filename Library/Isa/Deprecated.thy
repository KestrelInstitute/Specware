theory Deprecated
imports String
begin
consts Function__wfo :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> bool"
consts Option__some :: "'a \<Rightarrow> 'a option"
defs Option__some_def: "Option__some \<equiv> Some"
consts Option__none :: "'a option"
defs Option__none_def: "Option__none \<equiv> None"
end