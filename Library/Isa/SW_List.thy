theory SW_List
imports Option SW_Integer
begin
axioms List__induction: 
  "\<lbrakk>p []; \<forall>x l. p l \<longrightarrow> p (Cons x l)\<rbrakk> \<Longrightarrow> p l"
axioms List__length_subtype_constr: 
  "int (length dom_length) \<ge> 0"
consts List__nthTail :: "'a list \<times> nat \<Rightarrow> 'a list"
consts List__sublist :: "'a list \<times> nat \<times> nat \<Rightarrow> 'a list"
consts List__foldl :: "('a \<times> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
consts List__foldr :: "('a \<times> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
consts List__diff :: "'a list \<times> 'a list \<Rightarrow> 'a list"
consts List__rev2 :: "'a list \<times> 'a list \<Rightarrow> 'a list"
consts List__find :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"
consts List__tabulate :: "nat \<times> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list"
consts List__firstUpTo :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a list) option"
consts List__splitList :: "('a \<Rightarrow> bool) \<Rightarrow> 
                           'a list \<Rightarrow> ('a list \<times> 'a \<times> 'a list) option"
consts List__locationOf :: "'a list \<times> 'a list \<Rightarrow> (nat \<times> 'a list) option"
consts List__compare :: "('a \<times> 'a \<Rightarrow> Compare__Comparison) \<Rightarrow> 
                         'a list \<times> 'a list \<Rightarrow> Compare__Comparison"
consts List__app :: "('a \<Rightarrow> unit) \<Rightarrow> 'a list \<Rightarrow> unit"
primrec 
  "List__foldl f base [] = base"
  "List__foldl f base (Cons hd_v tl_v) 
     = List__foldl f (f(hd_v,base)) tl_v"
primrec 
  "List__foldr f base [] = base"
  "List__foldr f base (Cons hd_v tl_v) 
     = f(hd_v,List__foldr f base tl_v)"
primrec 
  "List__find p [] = None"
  "List__find p (Cons hd_v tl_v) 
     = (if p hd_v then Some hd_v else List__find p tl_v)"

primrec 
  "List__firstUpTo p [] = None"
  "List__firstUpTo p (Cons hd_v tl_v) 
     = (if p hd_v then 
          Some(hd_v,[])
        else 
          case List__firstUpTo p tl_v
           of None \<Rightarrow> None | Some (x,l1) \<Rightarrow> Some(x,Cons hd_v l1))"
primrec 
  "List__splitList p [] = None"
  "List__splitList p (Cons hd_v tl_v) 
     = (if p hd_v then 
          Some([],hd_v,tl_v)
        else 
          case List__splitList p tl_v
           of None \<Rightarrow> None | Some (l1,x,l2) \<Rightarrow> Some(Cons hd_v l1,x,l2))"
end