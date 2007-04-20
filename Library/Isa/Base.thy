theory Base
imports Empty String Compare System
begin
consts 
  second  :: "'a * 'b * 'c \<Rightarrow> 'b"
  thirdl  :: "'a * 'b * 'c \<Rightarrow> 'c"
  third   :: "'a * 'b * 'c * 'd \<Rightarrow> 'c"
  fourthl :: "'a * 'b * 'c * 'd \<Rightarrow> 'd"
  fourth  :: "'a * 'b * 'c * 'd * 'e \<Rightarrow> 'd"
  fifthl  :: "'a * 'b * 'c * 'd * 'e \<Rightarrow> 'e"
  fifth   :: "'a * 'b * 'c * 'd * 'e * 'f \<Rightarrow> 'e"

defs
  second_def  [simp]: "second x \<equiv> fst(snd x)"
  thirdl_def  [simp]: "thirdl x \<equiv> snd(snd x)"
  third_def   [simp]: "third x \<equiv> fst(snd(snd x))"
  fourthl_def [simp]: "fourthl x \<equiv> snd(snd(snd x))"
  fourth_def  [simp]: "fourth x \<equiv> fst(snd(snd(snd x)))"
  fifthl_def  [simp]: "fifthl x \<equiv> snd(snd(snd(snd x)))"
  fifth_def   [simp]: "fifth x \<equiv> fst(snd(snd(snd(snd x))))"
end