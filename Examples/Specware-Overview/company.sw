(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


Company = spec
  import /Library/DataStructures/Sets

  type Employee
  type Company

  axiom Company_ex is ex (c:Company) true
  axiom Employee_ex is ex (e:Employee) true

  % "fields" of Company
  op name (c : Company) : String
  op employees (c : Company) : Set Employee

  % "methods" of Company
  op num_employees (c : Company) : Nat = size (employees c)

  op add_employee c (e : Employee | ~(e in? (employees c))) :
    { c' : Company | employees c' = set_insert(e,employees c)
                     && name c' = name c }
  op try_add_employee c e : Company =
    if e in? (employees c) then c else add_employee c e

  op remove_employee c (e : Employee | e in? (employees c)) :
    { c' : Company | employees c' = set_delete(e,employees c)
                     && name c' = name c }
  op try_remove_employee c e : Company =
    if e in? (employees c) then remove_employee c e else c
end-spec

%% transformation script

Company1 = transform Company by
{
  maintain (num_employees) [lr Set.size_of_insert,
                        lr Set.size_of_delete]
}

Company2 = spec
  import Company1
  import /Library/DataStructures/StructuredTypes

  op employees_list : Company -> List Employee
  def employees a = L2S (employees_list a)

  theorem employees_l2s is
    fa (c) employees c = L2S (employees_list c)
  proof Isa employees_l2s
    by (auto simp add: employees_def)
  end-proof
end-spec

%% an alternate version of Company2 that does not use Company1 (as the
%% latter currently exposes a bug in gen-obligs)
Company2a = spec
  import Company
  import /Library/DataStructures/StructuredTypes

  op employees_list : Company -> List Employee
  def employees a = L2S (employees_list a)

  theorem employees_l2s is
    fa (c) employees c = L2S (employees_list c)
  proof Isa employees_l2s
    by (simp add: employees_def)
  end-proof
end-spec


Company3 = transform Company2 by
{
  implement (employees, employees_l2s) [ rl L2S_Cons, rl L2S_delete, rl L2S_member ]
}

Company4 = transform Company3 by
{
  finalizeCoType(Company)
}
