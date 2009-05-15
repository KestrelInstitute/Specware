theory Boolean
imports IsabelleExtensions
begin
consts Bool__e_tld_tld_tld :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
defs Bool__e_tld_tld_tld_def: 
  "Bool__e_tld_tld_tld p \<equiv> (\<lambda> (x::'a). \<not> (p x))"
consts Bool__e_amp_amp_amp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"	(infixr "&&&" 65)
defs Bool__e_amp_amp_amp_def: 
  "(p1 &&& p2) \<equiv> (\<lambda> (x::'a). p1 x \<and> p2 x)"
consts Bool__e_bar_bar_bar :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"	(infixr "|||" 64)
defs Bool__e_bar_bar_bar_def: 
  "(p1 ||| p2) \<equiv> (\<lambda> (x::'a). p1 x \<or> p2 x)"
theorem Bool__TRUE__def: 
  "TRUE x = True"
  by auto
end