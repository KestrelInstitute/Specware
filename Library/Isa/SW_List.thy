theory SW_List
imports Option SW_Nat List
begin
axioms List__induction: 
  "\<lbrakk>(p::'a list \<Rightarrow> bool) []; 
    \<forall>(x::'a) (l::'a list). p l \<longrightarrow> p (Cons x l)\<rbrakk> \<Longrightarrow> p (l::'a list)"
theorem List__length_Obligation_subsort: 
  "0 \<le> 1 + length tl__v"
  apply(auto)
  done
theorem List__null_length: 
  "null l = (length l = 0)"
    apply(case_tac l)
    apply(auto)
  done
theorem List__nth_Obligation_subsort: 
  "\<lbrakk>i < length (Cons (hd__v::'a) (tl__v::'a list)); 
    i < length (Cons hd__v tl__v); 
    \<not> (i = 0)\<rbrakk> \<Longrightarrow> 0 \<le> int i - 1"
  apply(auto)
  done
theorem List__nth_Obligation_subsort0: 
  "\<lbrakk>i < length (Cons (hd__v::'a) tl__v); 
    i < length (Cons hd__v tl__v); 
    \<not> (i = 0)\<rbrakk> \<Longrightarrow> int i - 1 < int (length tl__v)"
  apply(auto)
  done
consts List__nthTail :: "'a list \<times> nat \<Rightarrow> 'a list"
theorem List__nthTail_Obligation_subsort: 
  "\<lbrakk>(i::nat) \<le> length l; i \<le> length l; \<not> (i = 0)\<rbrakk> \<Longrightarrow> \<not> (null l)"
  apply (auto simp add: List__null_length)
  done
theorem List__nthTail_Obligation_subsort0: 
  "\<lbrakk>i \<le> length (l::'a list); i \<le> length l; \<not> (i = 0)\<rbrakk> \<Longrightarrow> 
   0 \<le> int i - 1"
  apply(auto)
  done
recdef List__nthTail "measure (\<lambda>(l,i). i)"
  "List__nthTail(l,0) = l"
  "List__nthTail(l,Suc i) = List__nthTail(tl l,i)"
theorem List__length_nthTail [simp]: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> 
    (length (List__nthTail(l,n))) =  (length l) -  n"
    apply(induct_tac l n rule: List__nthTail.induct)
    apply(auto)
  done
theorem List__last_Obligation_subsort: 
  "\<lbrakk>length (Cons (hd__v::'a) tl__v) > 0; 
    length (Cons hd__v tl__v) > 0; 
    \<not> (tl__v = [])\<rbrakk> \<Longrightarrow> length tl__v > 0"
  apply(auto)
  done
theorem List__butLast_Obligation_subsort: 
  "\<lbrakk>length (Cons (hd__v::'a) tl__v) > 0; 
    length (Cons hd__v tl__v) > 0; 
    \<not> (tl__v = [])\<rbrakk> \<Longrightarrow> length tl__v > 0"
  apply(auto)
  done
consts List__removeFirstElems :: "'a list \<times> nat \<Rightarrow> 'a list"
theorem List__removeFirstElems_Obligation_subsort: 
  "\<lbrakk>(i::nat) \<le> length l; i \<le> length l; \<not> (i = 0)\<rbrakk> \<Longrightarrow> \<not> (null l)"
    apply(auto simp add: List__null_length)
  done
theorem List__removeFirstElems_Obligation_subsort0: 
  "\<lbrakk>i \<le> length (l::'a list); i \<le> length l; \<not> (i = 0)\<rbrakk> \<Longrightarrow> 
   0 \<le> int i - 1"
  apply(auto)
  done
recdef List__removeFirstElems "measure (\<lambda>(l,i). i)"
  "List__removeFirstElems(l,0) = l"
  "List__removeFirstElems(l,Suc i) = List__removeFirstElems(tl l,i)"
theorem List__length_removeFirstElems [simp]: 
  "\<lbrakk>i \<le> length l\<rbrakk> \<Longrightarrow> 
    (length (List__removeFirstElems(l,i))) =  (length l) -  i"
    apply(induct_tac l i rule: List__removeFirstElems.induct)
    apply(auto)
  done
consts List__sublist__collectFirstElems :: "'a list \<times> nat \<Rightarrow> 'a list"
theorem List__sublist__collectFirstElems_Obligation_subsort: 
  "\<lbrakk>(i::nat) \<le> length l; i \<le> length l; \<not> (i = 0)\<rbrakk> \<Longrightarrow> \<not> (null l)"
    apply(auto simp add: List__null_length)
  done
theorem List__sublist__collectFirstElems_Obligation_subsort0: 
  "\<lbrakk>(i::nat) \<le> length l; i \<le> length l; \<not> (i = 0)\<rbrakk> \<Longrightarrow> \<not> (null l)"
    apply(auto simp add: List__null_length)
  done
theorem List__sublist__collectFirstElems_Obligation_subsort1: 
  "\<lbrakk>i \<le> length (l::'a list); i \<le> length l; \<not> (i = 0)\<rbrakk> \<Longrightarrow> 
   0 \<le> int i - 1"
  apply(auto)
  done
recdef List__sublist__collectFirstElems "measure (\<lambda>(l,i). i)"
  "List__sublist__collectFirstElems(l,0) = []"
  "List__sublist__collectFirstElems(l,Suc i) 
     = Cons (hd l) (List__sublist__collectFirstElems(tl l,i))"
consts List__sublist :: "'a list \<times> nat \<times> nat \<Rightarrow> 'a list"
theorem List__sublist_Obligation_subsort: 
  "\<lbrakk>(i::nat) \<le> (j::nat); 
    j \<le> length l; 
    i \<le> j; 
    j \<le> length l\<rbrakk> \<Longrightarrow> i \<le> length l"
  apply(auto)
  done
theorem List__sublist_Obligation_subsort0: 
  "\<lbrakk>i \<le> j; j \<le> length l; i \<le> j; j \<le> length l\<rbrakk> \<Longrightarrow> 
   0 \<le> int j - int i"
  apply(auto)
  done
recdef List__sublist "{}"
  "List__sublist(l,i,j)
     = List__sublist__collectFirstElems(List__removeFirstElems(l,i),j - i)"
theorem List__sublist_whole_Obligation_subsort: 
  "\<lbrakk>(j::nat) = length l\<rbrakk> \<Longrightarrow> 0 \<le> j \<and> j \<le> length l"
  apply(auto)
  done
theorem List__sublist_whole [simp]: 
  "List__sublist(l,0,length l) = l"
    apply(induct_tac l)
    apply(auto)
  done
consts List__foldl :: "('a \<times> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
primrec 
  "List__foldl f base [] = base"
  "List__foldl f base (Cons hd_v tl_v) 
     = List__foldl f (f(hd_v,base)) tl_v"
consts List__foldr :: "('a \<times> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
primrec 
  "List__foldr f base [] = base"
  "List__foldr f base (Cons hd_v tl_v) 
     = f(hd_v,List__foldr f base tl_v)"
consts List__diff :: "'a list \<times> 'a list \<Rightarrow> 'a list"
recdef List__diff "measure (\<lambda>(l1,l2). length l1)"
  "List__diff([],l2) = []"
  "List__diff(Cons hd_v tl_v,l2) 
     = (if hd_v mem l2 then 
          List__diff(tl_v,l2)
        else 
          Cons hd_v (List__diff(tl_v,l2)))"
consts List__rev2 :: "'a list \<times> 'a list \<Rightarrow> 'a list"
recdef List__rev2 "measure (\<lambda>(l,r). length l)"
  "List__rev2([],r) = r"
  "List__rev2(Cons hd_v tl_v,r) 
     = List__rev2(tl_v,Cons hd_v r)"
consts List__find :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"
primrec 
  "List__find p [] = None"
  "List__find p (Cons hd_v tl_v) 
     = (if p hd_v then Some hd_v else List__find p tl_v)"
consts List__tabulate__tabulateAux :: "nat \<times> 'a list \<times> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list"
theorem List__tabulate__tabulateAux_Obligation_subsort: 
  "\<lbrakk>\<not> (i = 0)\<rbrakk> \<Longrightarrow> 0 \<le> int i - 1"
  apply(auto)
  done
theorem List__tabulate__tabulateAux_Obligation_subsort0: 
  "\<lbrakk>\<not> (i = 0)\<rbrakk> \<Longrightarrow> 0 \<le> int i - 1"
  apply(auto)
  done
recdef List__tabulate__tabulateAux "measure (\<lambda>(i,l,f). i)"
  "List__tabulate__tabulateAux(0,l,f) = l"
  "List__tabulate__tabulateAux(Suc i,l,f) 
     = List__tabulate__tabulateAux(i,Cons (f i) l,f)"
consts List__tabulate :: "nat \<times> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list"
recdef List__tabulate "{}"
  "List__tabulate(n,f) = List__tabulate__tabulateAux(n,[],f)"
consts List__firstUpTo :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a list) option"
primrec 
  "List__firstUpTo p [] = None"
  "List__firstUpTo p (Cons hd_v tl_v) 
     = (if p hd_v then 
          Some(hd_v,[])
        else 
          case List__firstUpTo p tl_v
           of None \<Rightarrow> None | Some (x,l1) \<Rightarrow> Some(x,Cons hd_v l1))"
consts List__splitList :: "('a \<Rightarrow> bool) \<Rightarrow> 
                           'a list \<Rightarrow> ('a list \<times> 'a \<times> 'a list) option"
primrec 
  "List__splitList p [] = None"
  "List__splitList p (Cons hd_v tl_v) 
     = (if p hd_v then 
          Some([],hd_v,tl_v)
        else 
          case List__splitList p tl_v
           of None \<Rightarrow> None | Some (l1,x,l2) \<Rightarrow> Some(Cons hd_v l1,x,l2))"
consts List__locationOf__checkPrefix :: "'a list \<times> 'a list \<Rightarrow> 'a list option"
recdef List__locationOf__checkPrefix "measure (\<lambda>(subl,supl). length supl)"
  "List__locationOf__checkPrefix(Cons subhd subtl,Cons suphd suptl) 
     = (if subhd = suphd then 
          List__locationOf__checkPrefix(subtl,suptl)
        else 
          None)"
  "List__locationOf__checkPrefix([],supl) = Some supl"
  "List__locationOf__checkPrefix(subl,supl) = None"
consts List__locationOf__locationOfNonEmpty :: "'a list \<times> 'a list \<times> nat \<Rightarrow> 
                                                (nat \<times> 'a list) option"
theorem List__locationOf__locationOfNonEmpty_Obligation_subsort: 
  "\<lbrakk>Cons (subhd::'a) subtl \<noteq> []; 
    Cons subhd subtl \<noteq> []; 
    List__locationOf__checkPrefix(subtl,suptl) = None\<rbrakk> \<Longrightarrow> 
   0 \<le> (pos::nat) + 1"
  apply(auto)
  done
theorem List__locationOf__locationOfNonEmpty_Obligation_subsort0: 
  "\<lbrakk>Cons (subhd::'a) (subtl::'a list) \<noteq> []; 
    Cons subhd subtl \<noteq> []; 
    \<not> (subhd = (suphd::'a))\<rbrakk> \<Longrightarrow> 0 \<le> (pos::nat) + 1"
  apply(auto)
  done
recdef List__locationOf__locationOfNonEmpty "measure (\<lambda>(subl,supl,pos). length supl)"
  "List__locationOf__locationOfNonEmpty(Cons subhd subtl,[],pos) 
     = None"
  "List__locationOf__locationOfNonEmpty(Cons subhd subtl,
                                        Cons suphd suptl,pos) 
     = (if subhd = suphd then 
          case List__locationOf__checkPrefix(subtl,suptl)
           of None \<Rightarrow> 
              List__locationOf__locationOfNonEmpty(Cons subhd subtl,suptl,
                                                   pos + 1)
            | Some suplrest \<Rightarrow> Some(pos,suplrest)
        else 
          List__locationOf__locationOfNonEmpty(Cons subhd subtl,suptl,
                                               pos + 1))"
consts List__locationOf :: "'a list \<times> 'a list \<Rightarrow> (nat \<times> 'a list) option"
recdef List__locationOf "{}"
  "List__locationOf([],supl) = Some(0,supl)"
  "List__locationOf(subl,supl) 
     = List__locationOf__locationOfNonEmpty(subl,supl,0)"
consts List__compare :: "('a \<times> 'a \<Rightarrow> Compare__Comparison) \<Rightarrow> 
                         'a list \<times> 'a list \<Rightarrow> Compare__Comparison"

consts List__app :: "('a \<Rightarrow> unit) \<Rightarrow> 'a list \<Rightarrow> unit"
consts List__isoList :: " ('a,'b)Functions__Bijection \<Rightarrow> 
                          ('a list,'b list)Functions__Bijection"
axioms List__isoList_subtype_constr: 
  "\<lbrakk>bij dom_isoList\<rbrakk> \<Longrightarrow> bij (List__isoList dom_isoList)"
defs List__isoList_def: "List__isoList iso_elem \<equiv> map iso_elem"
end
