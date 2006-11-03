theory System
imports String Compare
begin
consts System__fail :: "string \<Rightarrow> 'a"
consts System__debug :: "string \<Rightarrow> 'a"
consts System__proverUseBase_p :: "bool"
consts System__specwareDebug_p :: "bool"
consts System__anyToString :: "'a \<Rightarrow> string"
consts System__print :: "'a \<Rightarrow> 'a"
consts System__warn :: "string \<Rightarrow> 'a"
consts System__time :: "'a \<Rightarrow> 'a"
consts System__getEnv :: "string \<Rightarrow> string option"
consts System__msWindowsSystem_p :: "bool"
consts System__temporaryDirectory :: "string"
consts System__trueFilename :: "string \<Rightarrow> string"
consts System__trueFilePath :: "string list \<times> bool \<Rightarrow> string list"
consts System__withRestartHandler :: "string \<times> (unit \<Rightarrow> unit) \<times> (unit \<Rightarrow> 'a) \<Rightarrow> 'a"
consts System__garbageCollect :: "bool \<Rightarrow> unit"
consts System__hackMemory :: "unit \<Rightarrow> unit"
end