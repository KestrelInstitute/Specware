theory SW_List
imports Option SW_Integer List
begin
fun List__List_P :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
   "List__List_P P_a (Cons x0 x1) 
      = ((P_a::'a \<Rightarrow> bool) x0 \<and> List__List_P P_a x1)"
 | "List__List_P P_a [] = True"
consts List__definedOnInitialSegmentOfLength :: "(nat \<Rightarrow> 'a option) \<Rightarrow> 
                                                 nat \<Rightarrow> bool"	(infixl "definedOnInitialSegmentOfLength" 60)
defs List__definedOnInitialSegmentOfLength_def: 
  "(f definedOnInitialSegmentOfLength n)
     \<equiv> ((\<forall>(i::nat). i < n \<longrightarrow> Option__some_p (f i)) 
          \<and> (\<forall>(i::nat). i \<ge> n \<longrightarrow> Option__none_p (f i)))"
types 'a List__ListFunction = "nat \<Rightarrow> 'a option"

theorem List__list_Obligation_subsort1: 
  "\<lbrakk>\<exists>(n::nat). (f::nat \<Rightarrow> 'a option) definedOnInitialSegmentOfLength n; 
    (f::'a List__ListFunction) 0 = Some x\<rbrakk> \<Longrightarrow> (i::nat) + 1 \<ge> 0"
  by auto
consts List__list :: "'a List__ListFunction \<Rightarrow> 'a list"



consts List__list_1 :: "'a list \<Rightarrow> 'a List__ListFunction"
defs List__list_1_def: 
  "List__list_1
     \<equiv> Function__inverse__stp
          (\<lambda> (f::nat \<Rightarrow> 'a option). 
             \<exists>(n::nat). f definedOnInitialSegmentOfLength n) List__list"


consts List__tabulate :: "nat \<times> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list"
defs List__tabulate_def: 
  "List__tabulate
     \<equiv> (\<lambda> ((n::nat),(f::nat \<Rightarrow> 'a)). 
          List__list
             (\<lambda> (i::nat). if i < n then Some (f i) else None))"
theorem List__length__def: 
  "length [] = 0"
  by auto
theorem List__length__def1: 
  "length (Cons Wild__Var_0 tl__v) = 1 + length tl__v"
  by auto
theorem List__length_Obligation_subsort: 
  "1 + length tl__v \<ge> 0"
  by auto
consts List__ofLength_p :: "nat \<Rightarrow> 'a list \<Rightarrow> bool"
defs List__ofLength_p_def: 
  "List__ofLength_p n l \<equiv> (length l = n)"

consts List__e_at_at :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option"	(infixl "@@" 70)
defs List__e_at_at_def: "(l @@ i) \<equiv> List__list_1 l i"
theorem List__empty__def: 
  "[] = []"
  by auto
theorem List__length_empty [simp]: 
  "length [] = 0"
  by auto
theorem List__empty_p__def: 
  "null l = (l = [])"
  by (simp add: null_empty)
theorem List__empty_p_length: 
  "null l = (length l = 0)"
   apply(case_tac l)
   apply(auto)
  done
consts List__nonEmpty_p :: "'a list \<Rightarrow> bool"
defs List__nonEmpty_p_def [simp]: "List__nonEmpty_p l \<equiv> (l \<noteq> [])"
types 'a List__List1 = "'a list"
consts List__single :: "'a \<Rightarrow> 'a list"
defs List__single_def: "List__single x \<equiv> [x]"

consts List__theElement__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a"
defs List__theElement__stp_def: 
  "List__theElement__stp P__a l \<equiv> (THE (x::'a). P__a x \<and> l = [x])"

consts List__theElement :: "'a list \<Rightarrow> 'a"
defs List__theElement_def: 
  "List__theElement l \<equiv> (THE (x::'a). l = [x])"

consts List__nin_p :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"	(infixl "nin?" 60)
defs List__nin_p_def: "(x nin? l) \<equiv> (\<not> (x mem l))"

theorem List__subFromLong_Obligation_subsort0: 
  "\<lbrakk>(i::nat) + (n::nat) \<le> length (l::'a list); (j::nat) < n\<rbrakk> \<Longrightarrow> 
   i + j \<ge> 0"
  by auto
theorem List__subFromLong_Obligation_subsort1: 
  "\<lbrakk>(i::nat) + (n::nat) \<le> length l; 
    (j::nat) < n; 
    i + j \<ge> 0\<rbrakk> \<Longrightarrow> i + j < length l"
  by auto
consts List__subFromLong :: "'a list \<times> nat \<times> nat \<Rightarrow> 'a list"
defs List__subFromLong_def: 
  "List__subFromLong
     \<equiv> (\<lambda> ((l::'a list),(i::nat),(n::nat)). 
          List__list
             (\<lambda> (j::nat). 
                if j < n then Some (l ! (i + j)) else None))"
theorem List__subFromTo_Obligation_subsort: 
  "\<lbrakk>i \<le> j; j \<le> length l\<rbrakk> \<Longrightarrow> int j - int i \<ge> 0"
  by auto
theorem List__subFromTo_Obligation_subsort0: 
  "\<lbrakk>i \<le> j; 
    j \<le> length l; 
    i \<ge> 0; 
    int j - int i \<ge> 0\<rbrakk> \<Longrightarrow> 
   int i + (int j - int i) \<le> int (length l)"
  by auto
consts List__subFromTo :: "'a list \<times> nat \<times> nat \<Rightarrow> 'a list"
defs List__subFromTo_def: 
  "List__subFromTo
     \<equiv> (\<lambda> ((l::'a list),(i::nat),(j::nat)). List__subFromLong(l,i,j - i))"
theorem List__subFromTo_whole_Obligation_subsort: 
  "\<lbrakk>0 \<ge> 0; length l \<ge> 0\<rbrakk> \<Longrightarrow> 
   let j = length l in 0 \<le> j \<and> j \<le> length l"
  by auto
theorem List__prefix_Obligation_subsort: 
  "\<lbrakk>(n::nat) \<le> length l; 0 \<ge> 0; n \<ge> 0\<rbrakk> \<Longrightarrow> 
   0 + n \<le> length l"
  by auto
consts List__prefix :: "'a list \<times> nat \<Rightarrow> 'a list"
defs List__prefix_def: 
  "List__prefix \<equiv> (\<lambda> ((l::'a list),(n::nat)). List__subFromLong(l,0,n))"
theorem List__suffix_Obligation_subsort: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> int (length l) - int n \<ge> 0"
  by auto
theorem List__suffix_Obligation_subsort0: 
  "\<lbrakk>n \<le> length l; 
    int (length l) - int n \<ge> 0; 
    n \<ge> 0\<rbrakk> \<Longrightarrow> 
   (int (length l) - int n) + int n 
     \<le> int (length l)"
  by auto
consts List__suffix :: "'a list \<times> nat \<Rightarrow> 'a list"
defs List__suffix_def: 
  "List__suffix
     \<equiv> (\<lambda> ((l::'a list),(n::nat)). 
          List__subFromLong(l,length l - n,n))"
theorem List__removePrefix_Obligation_subsort: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> int (length l) - int n \<ge> 0"
   apply(auto)
  done
theorem List__removePrefix_Obligation_subsort0: 
  "\<lbrakk>n \<le> length l; int (length l) - int n \<ge> 0\<rbrakk> \<Longrightarrow> 
   int (length l) - int n \<le> int (length l)"
  by auto
consts List__removePrefix :: "'a list \<times> nat \<Rightarrow> 'a list"
defs List__removePrefix_def: 
  "List__removePrefix
     \<equiv> (\<lambda> ((l::'a list),(n::nat)). List__suffix(l,length l - n))"
theorem List__length_removePrefix [simp]: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> 
   int (length (List__removePrefix(l,n))) 
     = int (length l) - int n"
   sorry
theorem List__removeSuffix_Obligation_subsort: 
  "\<lbrakk>n \<le> length l\<rbrakk> \<Longrightarrow> int (length l) - int n \<ge> 0"
  by auto
theorem List__removeSuffix_Obligation_subsort0: 
  "\<lbrakk>n \<le> length l; int (length l) - int n \<ge> 0\<rbrakk> \<Longrightarrow> 
   int (length l) - int n \<le> int (length l)"
  by auto
consts List__removeSuffix :: "'a list \<times> nat \<Rightarrow> 'a list"
defs List__removeSuffix_def: 
  "List__removeSuffix
     \<equiv> (\<lambda> ((l::'a list),(n::nat)). List__prefix(l,length l - n))"







theorem List__e_pls_pls_Obligation_subsort: 
  "\<lbrakk>length l = length l1 + length (l2::'a list); 
    length l1 \<ge> 0\<rbrakk> \<Longrightarrow> length l1 \<le> length l"
  by auto
theorem List__e_pls_pls_Obligation_subsort0: 
  "\<lbrakk>length l = length (l1::'a list) + length l2; 
    List__prefix(l,length l1) = l1; 
    length l2 \<ge> 0\<rbrakk> \<Longrightarrow> length l2 \<le> length l"
  by auto


theorem List__e_bar_gt_Obligation_subsort: 
  "List__nonEmpty_p ([x] @ (l::'a list))"
  by auto

theorem List__e_bar_gt__def: 
  "x # l = [x] @ l"
  by auto
theorem List__e_lt_bar_Obligation_subsort: 
  "List__nonEmpty_p ((l::'a list) @ [x])"
  by auto
consts List__e_lt_bar :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a List__List1"	(infixl "<|" 65)
defs List__e_lt_bar_def: "(l <| x) \<equiv> (l @ [x])"


consts List__update :: "'a list \<times> nat \<times> 'a \<Rightarrow> 'a list"
defs List__update_def: 
  "List__update
     \<equiv> (\<lambda> ((l::'a list),(i::nat),(x::'a)). 
          List__list
             (\<lambda> (j::nat). if j = i then Some x else l @@ j))"


consts List__exists1_p :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
defs List__exists1_p_def: 
  "List__exists1_p p l
     \<equiv> (\<exists>!(i::nat). i < length l \<and> p (l ! i))"
consts List__foralli_p :: "(nat \<times> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
defs List__foralli_p_def: 
  "List__foralli_p p l
     \<equiv> (\<forall>(i::nat). i < length l \<longrightarrow> p(i,l ! i))"
theorem List__filter__def: 
  "filter p [] = []"
  by auto
theorem List__filter__def1: 
  "\<lbrakk>p hd__v\<rbrakk> \<Longrightarrow> 
   filter p (Cons hd__v tl__v) 
     = [hd__v] @ filter p tl__v"
  by auto
theorem List__filter__def2: 
  "\<lbrakk>\<not> (p hd__v)\<rbrakk> \<Longrightarrow> 
   filter p (Cons hd__v tl__v) 
     = [] @ filter p tl__v"
  by auto
fun List__foldl :: "('a \<times> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
where
   "List__foldl f base [] = base"
 | "List__foldl f base (Cons hd_v tl_v) 
      = List__foldl f (f(hd_v,base)) tl_v"
fun List__foldr :: "('a \<times> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
where
   "List__foldr f base [] = base"
 | "List__foldr f base (Cons hd_v tl_v) 
      = f(hd_v,List__foldr f base tl_v)"
consts List__equiLong :: "'a list \<Rightarrow> 'b list \<Rightarrow> bool"	(infixl "equiLong" 60)
defs List__equiLong_def: 
  "(l1 equiLong l2) \<equiv> (length l1 = length l2)"


consts List__zip :: "'a list \<times> 'b list \<Rightarrow> ('a \<times> 'b) list"
defs List__zip_def: 
  "List__zip
     \<equiv> (\<lambda> ((l1::'a list),(l2::'b list)). 
          List__list
             (\<lambda> (i::nat). 
                if i < length l1 then 
                  Some (l1 ! i,l2 ! i)
                else 
                  None))"



consts List__zip3 :: "'a list \<times> 'b list \<times> 'c list \<Rightarrow> ('a \<times> 'b \<times> 'c) list"
defs List__zip3_def: 
  "List__zip3
     \<equiv> (\<lambda> ((l1::'a list),(l2::'b list),(l3::'c list)). 
          List__list
             (\<lambda> (i::nat). 
                if i < length l1 then 
                  Some (l1 ! i,l2 ! i,l3 ! i)
                else 
                  None))"

consts List__unzip :: "('a \<times> 'b) list \<Rightarrow> 'a list \<times> 'b list"
defs List__unzip_def: 
  "List__unzip
     \<equiv> Function__inverse__stp (\<lambda> (x,y). x equiLong y) List__zip"


consts List__unzip3 :: "('a \<times> 'b \<times> 'c) list \<Rightarrow> 'a list \<times> 'b list \<times> 'c list"
defs List__unzip3_def: 
  "List__unzip3
     \<equiv> Function__inverse__stp
          (\<lambda> ((l1::'a list),(l2::'b list),(l3::'c list)). 
             l1 equiLong l2 \<and> l2 equiLong l3) List__zip3"



consts List__map2 :: "('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<times> 'b list \<Rightarrow> 'c list"
defs List__map2_def: 
  "List__map2 f
     \<equiv> (\<lambda> ((l1::'a list),(l2::'b list)). map f (List__zip(l1,l2)))"
consts List__map3 :: "('a \<times> 'b \<times> 'c \<Rightarrow> 'd) \<Rightarrow> 
                      'a list \<times> 'b list \<times> 'c list \<Rightarrow> 'd list"
defs List__map3_def: 
  "List__map3 f
     \<equiv> (\<lambda> ((l1::'a list),(l2::'b list),(l3::'c list)). 
          map f (List__zip3(l1,l2,l3)))"

consts List__removeNones :: "'a option list \<Rightarrow> 'a list"
defs List__removeNones_def: 
  "List__removeNones l
     \<equiv> (THE (l_cqt::'a list). 
       map Some l_cqt 
         = filter (\<lambda> (cp::'a option). case cp of Some _ \<Rightarrow> True | _ \<Rightarrow> False) l)"

consts List__matchingOptionLists_p :: "'a option list \<times> 'b option list \<Rightarrow> bool"
defs List__matchingOptionLists_p_def: 
  "List__matchingOptionLists_p
     \<equiv> (\<lambda> ((l1::'a option list),(l2::'b option list)). 
          l1 equiLong l2 
            \<and> (\<forall>(i::nat). 
                 i < length l1 
                   \<longrightarrow> (case l1 ! i of None \<Rightarrow> True | _ \<Rightarrow> False) 
                         = (case l2 ! i of None \<Rightarrow> True | _ \<Rightarrow> False)))"

consts List__mapPartial2 :: "('a \<times> 'b \<Rightarrow> 'c option) \<Rightarrow> 
                             'a list \<times> 'b list \<Rightarrow> 'c list"
defs List__mapPartial2_def: 
  "List__mapPartial2 f
     \<equiv> (\<lambda> ((l1::'a list),(l2::'b list)). 
          filtermap f (List__zip(l1,l2)))"
consts List__mapPartial3 :: "('a \<times> 'b \<times> 'c \<Rightarrow> 'd option) \<Rightarrow> 
                             'a list \<times> 'b list \<times> 'c list \<Rightarrow> 'd list"
defs List__mapPartial3_def: 
  "List__mapPartial3 f
     \<equiv> (\<lambda> ((l1::'a list),(l2::'b list),(l3::'c list)). 
          filtermap f (List__zip3(l1,l2,l3)))"





consts List__repeat :: "'a \<Rightarrow> nat \<Rightarrow> 'a list"
defs List__repeat_def: 
  "List__repeat x n
     \<equiv> List__list (\<lambda> (i::nat). if i < n then Some x else None)"
consts List__allEqualElements_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
defs List__allEqualElements_p__stp_def: 
  "List__allEqualElements_p__stp P__a l
     \<equiv> (\<exists>(x::'a). P__a x \<and> l = List__repeat x (length l))"
consts List__allEqualElements_p :: "'a list \<Rightarrow> bool"
defs List__allEqualElements_p_def: 
  "List__allEqualElements_p l
     \<equiv> (\<exists>(x::'a). l = List__repeat x (length l))"
theorem List__extendLeft_Obligation_subsort: 
  "\<lbrakk>n \<ge> length l\<rbrakk> \<Longrightarrow> int n - int (length l) \<ge> 0"
  by auto
consts List__extendLeft :: "'a list \<times> 'a \<times> nat \<Rightarrow> 'a list"
defs List__extendLeft_def: 
  "List__extendLeft
     \<equiv> (\<lambda> ((l::'a list),(x::'a),(n::nat)). 
          List__repeat x (n - length l) @ l)"
theorem List__extendRight_Obligation_subsort: 
  "\<lbrakk>n \<ge> length l\<rbrakk> \<Longrightarrow> int n - int (length l) \<ge> 0"
  by auto
consts List__extendRight :: "'a list \<times> 'a \<times> nat \<Rightarrow> 'a list"
defs List__extendRight_def: 
  "List__extendRight
     \<equiv> (\<lambda> ((l::'a list),(x::'a),(n::nat)). 
          l @ List__repeat x (n - length l))"
theorem List__equiExtendLeft_Obligation_subsort: 
  "\<lbrakk>length l1 < length l2; length l2 \<ge> 0\<rbrakk> \<Longrightarrow> 
   length l2 \<ge> length l1"
  by auto



consts List__equiExtendLeft :: "'a list \<times> 'b list \<times> 'a \<times> 'b \<Rightarrow> 
                                'a list \<times> 'b list"
defs List__equiExtendLeft_def: 
  "List__equiExtendLeft
     \<equiv> (\<lambda> ((l1::'a list),(l2::'b list),(x1::'a),(x2::'b)). 
          if length l1 < length l2 then 
            (List__extendLeft(l1,x1,length l2),l2)
          else 
            (l1,List__extendLeft(l2,x2,length l1)))"





consts List__equiExtendRight :: "'a list \<times> 'b list \<times> 'a \<times> 'b \<Rightarrow> 
                                 'a list \<times> 'b list"
defs List__equiExtendRight_def: 
  "List__equiExtendRight
     \<equiv> (\<lambda> ((l1::'a list),(l2::'b list),(x1::'a),(x2::'b)). 
          if length l1 < length l2 then 
            (List__extendRight(l1,x1,length l2),l2)
          else 
            (l1,List__extendRight(l2,x2,length l1)))"


consts List__shiftLeft :: "'a list \<times> 'a \<times> nat \<Rightarrow> 'a list"
defs List__shiftLeft_def: 
  "List__shiftLeft
     \<equiv> (\<lambda> ((l::'a list),(x::'a),(n::nat)). 
          List__removePrefix(l @ List__repeat x n,n))"

consts List__shiftRight :: "'a list \<times> 'a \<times> nat \<Rightarrow> 'a list"
defs List__shiftRight_def: 
  "List__shiftRight
     \<equiv> (\<lambda> ((l::'a list),(x::'a),(n::nat)). 
          List__removeSuffix(List__repeat x n @ l,n))"



consts List__rotateLeft :: "'a List__List1 \<times> nat \<Rightarrow> 'a list"
defs List__rotateLeft_def: 
  "List__rotateLeft
     \<equiv> (\<lambda> ((l::'a List__List1),(n::nat)). 
          let n = n mod length l 
          in 
          List__removePrefix(l,n) @ List__prefix(l,n))"



consts List__rotateRight :: "'a List__List1 \<times> nat \<Rightarrow> 'a list"
defs List__rotateRight_def: 
  "List__rotateRight
     \<equiv> (\<lambda> ((l::'a List__List1),(n::nat)). 
          let n = n mod length l 
          in 
          List__suffix(l,n) @ List__removeSuffix(l,n))"



consts List__unflattenL :: "'a list \<times> nat list \<Rightarrow> 'a list list"
defs List__unflattenL_def: 
  "List__unflattenL
     \<equiv> (\<lambda> ((l::'a list),(lens::nat list)). 
          (THE (ll::'a list list). 
          concat ll = l 
            \<and> (\<forall>(i::nat). 
                 i < length ll 
                   \<longrightarrow> length (ll ! i) = lens ! i)))"

consts List__unflatten :: "'a list \<times> Nat__PosNat \<Rightarrow> 'a list list"
defs List__unflatten_def: 
  "List__unflatten
     \<equiv> (\<lambda> ((l::'a list),(n::Nat__PosNat)). 
          List__unflattenL(l,List__repeat n (length l div n)))"
consts List__noRepetitions_p :: "'a list \<Rightarrow> bool"
defs List__noRepetitions_p_def: 
  "List__noRepetitions_p l
     \<equiv> (\<forall>(i::nat) (j::nat). 
          i < length l \<and> (j < length l \<and> i \<noteq> j) 
            \<longrightarrow> l ! i \<noteq> l ! j)"
types 'a List__InjList = "'a list"
theorem List__increasingNats_p_Obligation_subsort: 
  "\<lbrakk>int (i::nat) < int (length nats) - 1; i \<ge> 0\<rbrakk> \<Longrightarrow> 
   i < length nats"
  by auto
theorem List__increasingNats_p_Obligation_subsort0: 
  "\<lbrakk>int i < int (length nats) - 1\<rbrakk> \<Longrightarrow> i + 1 \<ge> 0"
  by auto
theorem List__increasingNats_p_Obligation_subsort1: 
  "\<lbrakk>int (i::nat) < int (length nats) - 1; 
    i + 1 \<ge> 0\<rbrakk> \<Longrightarrow> i + 1 < length nats"
  by auto
consts List__increasingNats_p :: "nat list \<Rightarrow> bool"
defs List__increasingNats_p_def: 
  "List__increasingNats_p nats
     \<equiv> (\<forall>(i::nat). 
          int i < int (length nats) - 1 
            \<longrightarrow> nats ! i < nats ! (i + 1))"

consts List__positionsSuchThat :: "'a list \<times> ('a \<Rightarrow> bool) \<Rightarrow> nat List__InjList"
defs List__positionsSuchThat_def: 
  "List__positionsSuchThat
     \<equiv> (\<lambda> ((l::'a list),(p::'a \<Rightarrow> bool)). 
          (THE (POSs::nat list). 
          List__noRepetitions_p POSs 
            \<and> (List__increasingNats_p POSs 
             \<and> (\<forall>(i::nat). 
                  i mem POSs 
                    = (i < length l \<and> p (l ! i))))))"


consts List__leftmostPositionSuchThat :: "'a list \<times> ('a \<Rightarrow> bool) \<Rightarrow> nat option"
defs List__leftmostPositionSuchThat_def: 
  "List__leftmostPositionSuchThat
     \<equiv> (\<lambda> ((l::'a list),(p::'a \<Rightarrow> bool)). 
          let POSs = List__positionsSuchThat(l,p) 
          in 
          if null POSs then None else Some (hd POSs))"
theorem List__rightmostPositionSuchThat_Obligation_subsort: 
  "\<lbrakk>List__noRepetitions_p (POSs::nat list); 
    List__positionsSuchThat((l::'a list),(p::'a \<Rightarrow> bool)) = POSs; 
    \<not> (null POSs); 
    List__noRepetitions_p POSs; 
    List__List_P (\<lambda> (i_2). i_2 \<ge> 0) POSs\<rbrakk> \<Longrightarrow> 
   List__nonEmpty_p POSs 
     \<and> List__List_P (\<lambda> (i_3). i_3 \<ge> 0) POSs"
  by auto
consts List__rightmostPositionSuchThat :: "'a list \<times> ('a \<Rightarrow> bool) \<Rightarrow> nat option"
defs List__rightmostPositionSuchThat_def: 
  "List__rightmostPositionSuchThat
     \<equiv> (\<lambda> ((l::'a list),(p::'a \<Rightarrow> bool)). 
          let POSs = List__positionsSuchThat(l,p) 
          in 
          if null POSs then None else Some (last POSs))"
consts List__positionsOf :: "'a list \<times> 'a \<Rightarrow> nat List__InjList"
defs List__positionsOf_def: 
  "List__positionsOf
     \<equiv> (\<lambda> ((l::'a list),(x::'a)). 
          List__positionsSuchThat(l,\<lambda> (y::'a). y = x))"


consts List__positionOf :: "'a List__InjList \<times> 'a \<Rightarrow> nat"
defs List__positionOf_def: 
  "List__positionOf
     \<equiv> (\<lambda> ((l::'a List__InjList),(x::'a)). 
          List__theElement (List__positionsOf(l,x)))"
consts List__sublistAt_p :: "'a list \<times> nat \<times> 'a list \<Rightarrow> bool"
defs List__sublistAt_p_def: 
  "List__sublistAt_p
     \<equiv> (\<lambda> ((subl::'a list),(i::nat),(supl::'a list)). 
          \<exists>(pre::'a list) (post::'a list). 
            (pre @ subl) @ post = supl \<and> length pre = i)"

consts List__positionsOfSublist :: "'a list \<times> 'a list \<Rightarrow> nat List__InjList"
defs List__positionsOfSublist_def: 
  "List__positionsOfSublist
     \<equiv> (\<lambda> ((subl::'a list),(supl::'a list)). 
          (THE (POSs::nat list). 
          List__noRepetitions_p POSs 
            \<and> (List__increasingNats_p POSs 
             \<and> (\<forall>(i::nat). 
                  i mem POSs = List__sublistAt_p(subl,i,supl)))))"




consts List__leftmostPositionOfSublistAndFollowing :: "'a list \<times> 'a list \<Rightarrow> 
                                                       (nat \<times> 'a list) option"
defs List__leftmostPositionOfSublistAndFollowing_def: 
  "List__leftmostPositionOfSublistAndFollowing
     \<equiv> (\<lambda> ((subl::'a list),(supl::'a list)). 
          let POSs = List__positionsOfSublist(subl,supl) 
          in 
          if null POSs then 
            None
          else 
            let i = hd POSs 
            in 
            Some (i,List__removePrefix(supl,i + length subl)))"


consts List__rightmostPositionOfSublistAndPreceding :: "'a list \<times> 'a list \<Rightarrow> 
                                                        (nat \<times> 'a list) option"
defs List__rightmostPositionOfSublistAndPreceding_def: 
  "List__rightmostPositionOfSublistAndPreceding
     \<equiv> (\<lambda> ((subl::'a list),(supl::'a list)). 
          let POSs = List__positionsOfSublist(subl,supl) 
          in 
          if null POSs then 
            None
          else 
            let i = last POSs in Some (i,List__prefix(supl,i)))"
theorem List__splitAt_Obligation_subsort: 
  "\<lbrakk>(i::nat) < length l; i \<ge> 0\<rbrakk> \<Longrightarrow> i \<le> length l"
  by auto
theorem List__splitAt_Obligation_subsort0: 
  "\<lbrakk>(i::nat) < length l\<rbrakk> \<Longrightarrow> i + 1 \<ge> 0"
  by auto
theorem List__splitAt_Obligation_subsort1: 
  "\<lbrakk>(i::nat) < length l; i + 1 \<ge> 0\<rbrakk> \<Longrightarrow> i + 1 \<le> length l"
  by auto
consts List__splitAt :: "'a list \<times> nat \<Rightarrow> 'a list \<times> 'a \<times> 'a list"
defs List__splitAt_def: 
  "List__splitAt
     \<equiv> (\<lambda> ((l::'a list),(i::nat)). 
          (List__prefix(l,i),l ! i,List__removePrefix(l,i + 1)))"

consts List__splitAtLeftmost :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                 'a list \<Rightarrow> ('a list \<times> 'a \<times> 'a list) option"
defs List__splitAtLeftmost_def: 
  "List__splitAtLeftmost p l
     \<equiv> (case List__leftmostPositionSuchThat(l,p)
         of Some i \<Rightarrow> Some (List__splitAt(l,i)) | None \<Rightarrow> None)"

consts List__splitAtRightmost :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                  'a list \<Rightarrow> ('a list \<times> 'a \<times> 'a list) option"
defs List__splitAtRightmost_def: 
  "List__splitAtRightmost p l
     \<equiv> (case List__rightmostPositionSuchThat(l,p)
         of Some i \<Rightarrow> Some (List__splitAt(l,i)) | None \<Rightarrow> None)"
theorem List__findLeftmost_Obligation_subsort: 
  "\<lbrakk>filter (p::'a \<Rightarrow> bool) (l::'a list) = lp; \<not> (null lp)\<rbrakk> \<Longrightarrow> 
   List__nonEmpty_p lp"
  by auto
consts List__findLeftmost :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"
defs List__findLeftmost_def: 
  "List__findLeftmost p l
     \<equiv> (let lp = filter p l 
        in 
        (if null lp then None else Some (hd lp)))"
theorem List__findRightmost_Obligation_subsort: 
  "\<lbrakk>filter (p::'a \<Rightarrow> bool) (l::'a list) = lp; \<not> (null lp)\<rbrakk> \<Longrightarrow> 
   List__nonEmpty_p lp"
  by auto
consts List__findRightmost :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"
defs List__findRightmost_def: 
  "List__findRightmost p l
     \<equiv> (let lp = filter p l 
        in 
        (if null lp then None else Some (last lp)))"


consts List__findLeftmostAndPreceding :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                          'a list \<Rightarrow> ('a \<times> 'a list) option"
defs List__findLeftmostAndPreceding_def: 
  "List__findLeftmostAndPreceding p l
     \<equiv> (case List__leftmostPositionSuchThat(l,p)
         of None \<Rightarrow> None | Some i \<Rightarrow> Some (l ! i,List__prefix(l,i)))"


consts List__findRightmostAndFollowing :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                           'a list \<Rightarrow> ('a \<times> 'a list) option"
defs List__findRightmostAndFollowing_def: 
  "List__findRightmostAndFollowing p l
     \<equiv> (case List__rightmostPositionSuchThat(l,p)
         of None \<Rightarrow> None | Some i \<Rightarrow> Some (l ! i,List__removePrefix(l,i)))"
consts List__delete :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
defs List__delete_def: 
  "List__delete x l \<equiv> filter (\<lambda> (y::'a). y \<noteq> x) l"
consts List__diff :: "'a list \<times> 'a list \<Rightarrow> 'a list"
defs List__diff_def: 
  "List__diff
     \<equiv> (\<lambda> ((l1::'a list),(l2::'a list)). 
          filter (\<lambda> (x::'a). x nin? l2) l1)"
theorem List__longestCommonPrefix_Obligation_subsort: 
  "\<lbrakk>(len::nat) \<le> length l1; 
    len \<le> length (l2::'a list); 
    List__prefix(l1,len) = List__prefix(l2,len); 
    \<not> (length l1 = len); 
    \<not> (length l2 = len); 
    len \<ge> 0\<rbrakk> \<Longrightarrow> len < length l1"
  by auto
theorem List__longestCommonPrefix_Obligation_subsort0: 
  "\<lbrakk>(len::nat) \<le> length (l1::'a list); 
    len \<le> length l2; 
    List__prefix(l1,len) = List__prefix(l2,len); 
    \<not> (length l1 = len); 
    \<not> (length l2 = len); 
    len \<ge> 0\<rbrakk> \<Longrightarrow> len < length l2"
  by auto


consts List__longestCommonPrefix :: "'a list \<times> 'a list \<Rightarrow> 'a list"
defs List__longestCommonPrefix_def: 
  "List__longestCommonPrefix
     \<equiv> (\<lambda> ((l1::'a list),(l2::'a list)). 
          List__prefix
            (l1,
             (THE (len::nat). 
             len \<le> length l1 
               \<and> (len \<le> length l2 
                \<and> (List__prefix(l1,len) = List__prefix(l2,len) 
                 \<and> (length l1 = len 
                      \<or> (length l2 = len \<or> l1 ! len \<noteq> l2 ! len)))))))"
consts List__longestCommonSuffix :: "'a list \<times> 'a list \<Rightarrow> 'a list"
defs List__longestCommonSuffix_def: 
  "List__longestCommonSuffix
     \<equiv> (\<lambda> ((l1::'a list),(l2::'a list)). 
          rev (List__longestCommonPrefix(rev l1,rev l2)))"
consts List__permutation_p :: "nat list \<Rightarrow> bool"
defs List__permutation_p_def: 
  "List__permutation_p prm
     \<equiv> (List__noRepetitions_p prm 
          \<and> (\<forall>(i::nat). i mem prm \<longrightarrow> i < length prm))"
types List__Permutation = "nat list"



consts List__permute :: "'a list \<times> List__Permutation \<Rightarrow> 'a list"
defs List__permute_def: 
  "List__permute
     \<equiv> (\<lambda> ((l::'a list),(prm::List__Permutation)). 
          (THE (r::'a list). 
          r equiLong l 
            \<and> (\<forall>(i::nat). 
                 i < length l 
                   \<longrightarrow> l ! i = r ! (prm ! i))))"

consts List__permutationOf :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"	(infixl "permutationOf" 60)
defs List__permutationOf_def: 
  "(l1 permutationOf l2)
     \<equiv> (\<exists>(prm::nat list). 
          List__permutation_p prm 
            \<and> (prm equiLong l1 \<and> List__permute(l1,prm) = l2))"
fun List__compare :: "('a \<times> 'a \<Rightarrow> Compare__Comparison) \<Rightarrow> 
                      'a list \<times> 'a list \<Rightarrow> Compare__Comparison"
where
   "List__compare comp_v(Cons hd1 tl1,Cons hd2 tl2) 
      = (case comp_v(hd1,hd2)
          of Equal \<Rightarrow> List__compare comp_v(tl1,tl2) | result \<Rightarrow> result)"
 | "List__compare comp_v([],[]) = Equal"
 | "List__compare comp_v([],(l2::'a list)) = Less"
 | "List__compare comp_v((l1::'a list),[]) = Greater"
theorem List__isoList_Obligation_subsort: 
  "\<lbrakk>bij iso_elem\<rbrakk> \<Longrightarrow> bij (map iso_elem)"
  apply(simp add: bij_def, auto) 
  (** first subgoal is proved by auto **)
  apply(simp add: surj_def, auto)
  apply (induct_tac y, auto)
  (** subgoal 2.1 is proved by auto, the other one needs some guidance **)
  apply (drule_tac x = "a" in  spec, auto)
  apply (rule_tac x="xa#x" in exI, auto)
  done
consts List__isoList :: " ('a,'b)Function__Bijection \<Rightarrow> 
                          ('a list,'b list)Function__Bijection"
defs List__isoList_def: "List__isoList iso_elem \<equiv> map iso_elem"
theorem List__isoList_subtype_constr: 
  "\<lbrakk>bij dom_isoList\<rbrakk> \<Longrightarrow> bij (List__isoList dom_isoList)"
  apply(simp add:  List__isoList_def List__isoList_Obligation_subsort)
  done
theorem List__nil__def: 
  "[] = []"
  by auto
theorem List__cons__def: 
  "(\<lambda> (x,y). x # y) = (\<lambda> (x,y). x # y)"
  by auto
theorem List__insert__def: 
  "(\<lambda> (x,y). x # y) = (\<lambda> (x,y). x # y)"
  by auto
theorem List__null__def: 
  "null = null"
  by auto
theorem List__hd__def: 
  "RFun List__nonEmpty_p hd = RFun List__nonEmpty_p hd"
  by auto
theorem List__tl__def: 
  "RFun List__nonEmpty_p tl = RFun List__nonEmpty_p tl"
  by auto
theorem List__concat__def: 
  "(\<lambda> (x,y). x @ y) = (\<lambda> (x,y). x @ y)"
  by auto
theorem List__nth__def: 
  "RFun (\<lambda> ((l::'a list),(i::nat)). i < length l) (\<lambda> (x,y). x ! y) 
     = RFun (\<lambda> ((l::'a list),(i::nat)). i < length l) (\<lambda> (x,y). x ! y)"
  by auto
consts List__nthTail :: "'a list \<times> nat \<Rightarrow> 'a list"
defs List__nthTail_def: "List__nthTail \<equiv> List__removePrefix"
theorem List__member__def: 
  "(\<lambda> (x,y). x mem y) = (\<lambda> (x,y). x mem y)"
  by auto
consts List__removeFirstElems :: "'a list \<times> nat \<Rightarrow> 'a list"
defs List__removeFirstElems_def: 
  "List__removeFirstElems \<equiv> List__removePrefix"
consts List__sublist :: "'a list \<times> nat \<times> nat \<Rightarrow> 'a list"
defs List__sublist_def: "List__sublist \<equiv> List__subFromTo"
theorem List__exists__def: 
  "list_ex = list_ex"
  by auto
theorem List__all__def: 
  "list_all = list_all"
  by auto
fun List__rev2 :: "'a list \<times> 'a list \<Rightarrow> 'a list"
where
   "List__rev2([],r) = r"
 | "List__rev2(Cons hd_v tl_v,r) 
      = List__rev2(tl_v,Cons hd_v r)"
theorem List__rev__def: 
  "rev = rev"
  by auto
consts List__find :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"
defs List__find_def: "List__find \<equiv> List__findLeftmost"
consts List__firstUpTo :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a list) option"
defs List__firstUpTo_def: "List__firstUpTo \<equiv> List__findLeftmostAndPreceding"
consts List__splitList :: "('a \<Rightarrow> bool) \<Rightarrow> 
                           'a list \<Rightarrow> ('a list \<times> 'a \<times> 'a list) option"
defs List__splitList_def: "List__splitList \<equiv> List__splitAtLeftmost"
consts List__locationOf :: "'a list \<times> 'a list \<Rightarrow> (nat \<times> 'a list) option"
defs List__locationOf_def: 
  "List__locationOf \<equiv> List__leftmostPositionOfSublistAndFollowing"
fun List__app :: "('a \<Rightarrow> unit) \<Rightarrow> 'a list \<Rightarrow> unit"
where
   "List__app f [] = ()"
 | "List__app f (Cons hd_v tl_v) = List__app f tl_v"
end