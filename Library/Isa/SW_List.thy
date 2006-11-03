theory SW_List
imports Option SW_Integer
begin
axioms List__induction: 
  "\<lbrakk>p []; \<forall>x l. p l \<longrightarrow> p (Cons x l)\<rbrakk> \<Longrightarrow> p l"
axioms List__length_subtype_constr: "length dom_length \<ge> 0"
consts List__nthTail :: "'a list \<times> int \<Rightarrow> 'a list"
consts List__sublist :: "'a list \<times> int \<times> int \<Rightarrow> 'a list"
consts List__foldl :: "('a \<times> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
consts List__foldr :: "('a \<times> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
consts List__diff :: "'a list \<times> 'a list \<Rightarrow> 'a list"
consts List__rev2 :: "'a list \<times> 'a list \<Rightarrow> 'a list"
consts List__find :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"
consts List__tabulate :: "int \<times> (int \<Rightarrow> 'a) \<Rightarrow> 'a list"
consts List__firstUpTo :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a list) option"
consts List__splitList :: "('a \<Rightarrow> bool) \<Rightarrow> 
                           'a list \<Rightarrow> ('a list \<times> 'a \<times> 'a list) option"
consts List__locationOf :: "'a list \<times> 'a list \<Rightarrow> (int \<times> 'a list) option"
consts List__compare :: "('a \<times> 'a \<Rightarrow> Compare__Comparison) \<Rightarrow> 
                         'a list \<times> 'a list \<Rightarrow> Compare__Comparison"
consts List__app :: "('a \<Rightarrow> unit) \<Rightarrow> 'a list \<Rightarrow> unit"
(* defs List__nthTail_def: 
  "List__nthTail
     \<equiv> \<lambda> (l,i). if i = 0 then l else List__nthTail(tl l,i - 1)" *)
(* defs List__sublist_def: 
  "List__sublist
     \<equiv> \<lambda> (l,i,j). 
         let
         removeFirstElems = 
         \<lambda> (l,i). if i = 0 then l else removeFirstElems(tl l,i - 1)
         in
         let
         collectFirstElems = 
         \<lambda> (l,i). 
           if i = 0 then 
             []
           else 
             Cons (hd l) (collectFirstElems(tl l,i - 1))
         in
         collectFirstElems(removeFirstElems(l,i),j - i)" *)
primrec 
  "List__foldl f base [] = base"
  "List__foldl f base (Cons x y) = List__foldl f (f(x,base)) y"
primrec 
  "List__foldr f base [] = base"
  "List__foldr f base (Cons x y) = f(x,List__foldr f base y)"
(* defs List__diff_def: 
  "List__diff
     \<equiv> \<lambda> (l1,l2). 
         case l1
          of Nil \<Rightarrow> []
           | Cons hd tl \<Rightarrow> 
             if hd mem l2 then 
               List__diff(tl,l2)
             else 
               Cons hd (List__diff(tl,l2))"
defs List__rev2_def: 
  "List__rev2
     \<equiv> \<lambda> (l,r). 
         case l of Nil \<Rightarrow> r | Cons hd tl \<Rightarrow> List__rev2(tl,Cons hd r)" *)
primrec 
  "List__find p [] = None"
  "List__find p (Cons x y) 
     = (if p x then Some x else List__find p y)"
(*
defs List__tabulate_def: 
  "List__tabulate
     \<equiv> \<lambda> (n,f). 
         let
         tabulateAux = 
         \<lambda> (i,l). 
           if i = 0 then 
             l
           else 
             tabulateAux(i - 1,Cons (f (i - 1)) l)
         in
         tabulateAux(n,[])" *)
primrec 
  "List__firstUpTo p [] = None"
  "List__firstUpTo p (Cons x y) 
     = (if p x then 
          Some (x, [])
        else 
          case List__firstUpTo p y
           of None \<Rightarrow> None | Some (x1, l1) \<Rightarrow> Some (x, (Cons x l1)))"
primrec 
  "List__splitList p [] = None"
  "List__splitList p (Cons x y) 
     = (if p x then 
          Some ([], x, y)
        else 
          case List__splitList p y
           of None \<Rightarrow> None
            | Some (l1, x, l2) \<Rightarrow> Some ((Cons x l1), x, l2))"
(*
defs List__locationOf_def: 
  "List__locationOf
     \<equiv> \<lambda> (subl,supl). 
         let
         checkPrefix = 
         \<lambda> (subl,supl). 
           case (subl,supl)
            of (Cons subhd subtl,Cons suphd suptl) \<Rightarrow> 
               if subhd = suphd then checkPrefix(subtl,suptl) else None
             | (Nil,_) \<Rightarrow> Some supl
             | _ \<Rightarrow> None
         in
         let
         locationOfNonEmpty = 
         \<lambda> (subl,supl,pos). 
           let Cons subhd subtl = subl
           in
           case supl
            of Nil \<Rightarrow> None
             | Cons suphd suptl \<Rightarrow> 
               if subhd = suphd then 
                 case checkPrefix(subtl,suptl)
                  of None \<Rightarrow> locationOfNonEmpty(subl,suptl,pos + 1)
                   | Some suplrest \<Rightarrow> Some pos suplrest
               else 
                 locationOfNonEmpty(subl,suptl,pos + 1)
         in
         case subl
          of Nil \<Rightarrow> Some 0 supl | _ \<Rightarrow> locationOfNonEmpty(subl,supl,0)"
defs List__compare_def: 
  "List__compare comp
     \<equiv> \<lambda> (l1,l2). 
         case (l1,l2)
          of (Cons hd1 tl1,Cons hd2 tl2) \<Rightarrow> 
             case comp(hd1,hd2)
              of Equal \<Rightarrow> List__compare comp(tl1,tl2) | result \<Rightarrow> result
           | (Nil,Nil) \<Rightarrow> Equal
           | (Nil,Cons _ _) \<Rightarrow> Less
           | (Cons _ _,Nil) \<Rightarrow> Greater" 
primrec 
  "List__app f [] = ()"
  "List__app f (Cons x y) = f x; List__app f y" *)
end