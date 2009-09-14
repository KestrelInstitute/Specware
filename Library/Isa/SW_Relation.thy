theory SW_Relation
imports SW_Set
begin
types  ('a,'b)Relation__Relation = "('a \<times> 'b) set"
consts Relation__domain__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                                  ('a, 'b)Relation__Relation \<Rightarrow> 'a set"
defs Relation__domain__stp_def: 
  "Relation__domain__stp P__b r
     \<equiv> (\<lambda> (x::'a). \<exists>(y::'b). P__b y \<and> (x, y) \<in> r)"
consts Relation__domain :: " ('a, 'b)Relation__Relation \<Rightarrow> 'a set"
defs Relation__domain_def: 
  "Relation__domain r \<equiv> (\<lambda> (x::'a). \<exists>(y::'b). (x, y) \<in> r)"
consts Relation__range__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                 ('a, 'b)Relation__Relation \<Rightarrow> 'b set"
defs Relation__range__stp_def: 
  "Relation__range__stp P__a r
     \<equiv> (\<lambda> (y::'b). \<exists>(x::'a). P__a x \<and> (x, y) \<in> r)"
consts Relation__range :: " ('a, 'b)Relation__Relation \<Rightarrow> 'b set"
defs Relation__range_def: 
  "Relation__range r \<equiv> (\<lambda> (y::'b). \<exists>(x::'a). (x, y) \<in> r)"
consts Relation__apply :: " ('a, 'b)Relation__Relation \<Rightarrow> 'a \<Rightarrow> 'b set"
defs Relation__apply_def: 
  "Relation__apply r x \<equiv> (\<lambda> (y::'b). (x, y) \<in> r)"
consts Relation__applyi :: " ('a, 'b)Relation__Relation \<Rightarrow> 'b \<Rightarrow> 'a set"
defs Relation__applyi_def: 
  "Relation__applyi r y \<equiv> (\<lambda> (x::'a). (x, y) \<in> r)"
consts Relation__applys__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                  ('a, 'b)Relation__Relation \<Rightarrow> 'a set \<Rightarrow> 'b set"
defs Relation__applys__stp_def: 
  "Relation__applys__stp P__a r xS
     \<equiv> (\<lambda> (y::'b). \<exists>(x::'a). P__a x \<and> (x \<in> xS \<and> (x, y) \<in> r))"
consts Relation__applys :: " ('a, 'b)Relation__Relation \<Rightarrow> 'a set \<Rightarrow> 'b set"
defs Relation__applys_def: 
  "Relation__applys r xS
     \<equiv> (\<lambda> (y::'b). \<exists>(x::'a). x \<in> xS \<and> (x, y) \<in> r)"
consts Relation__applyis__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                                   ('a, 'b)Relation__Relation \<Rightarrow> 
                                  'b set \<Rightarrow> 'a set"
defs Relation__applyis__stp_def: 
  "Relation__applyis__stp P__b r yS
     \<equiv> (\<lambda> (x::'a). \<exists>(y::'b). P__b y \<and> (y \<in> yS \<and> (x, y) \<in> r))"
consts Relation__applyis :: " ('a, 'b)Relation__Relation \<Rightarrow> 'b set \<Rightarrow> 'a set"
defs Relation__applyis_def: 
  "Relation__applyis r yS
     \<equiv> (\<lambda> (x::'a). \<exists>(y::'b). y \<in> yS \<and> (x, y) \<in> r)"
consts Relation__e_cl_gt__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                                   ('a, 'b)Relation__Relation
                                     \<times>  ('b, 'c)Relation__Relation \<Rightarrow> 
                                   ('a, 'c)Relation__Relation"
defs Relation__e_cl_gt__stp_def: 
  "Relation__e_cl_gt__stp P__b
     \<equiv> (\<lambda> ((r1:: ('a, 'b)Relation__Relation), (r2:: ('b, 'c)Relation__Relation)). 
          \<lambda> ((x::'a), (z::'c)). 
            \<exists>(y::'b). P__b y \<and> ((x, y) \<in> r1 \<and> (y, z) \<in> r2))"
consts Relation__e_cl_gt :: " ('a, 'b)Relation__Relation \<Rightarrow> 
                              ('b, 'c)Relation__Relation \<Rightarrow> 
                              ('a, 'c)Relation__Relation"	(infixl ":>" 64)
defs Relation__e_cl_gt_def: 
  "((r1:: ('a, 'b)Relation__Relation) :> (r2:: ('b, 'c)Relation__Relation))
     \<equiv> (\<lambda> ((x::'a), (z::'c)). 
          \<exists>(y::'b). (x, y) \<in> r1 \<and> (y, z) \<in> r2)"
consts Relation__o__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                             ('b, 'c)Relation__Relation
                               \<times>  ('a, 'b)Relation__Relation \<Rightarrow> 
                             ('a, 'c)Relation__Relation"
defs Relation__o__stp_def: 
  "Relation__o__stp P__b
     \<equiv> (\<lambda> ((r1:: ('b, 'c)Relation__Relation), (r2:: ('a, 'b)Relation__Relation)). 
          Relation__e_cl_gt__stp P__b(r2, r1))"
consts o_R :: " ('b, 'c)Relation__Relation \<Rightarrow> 
                ('a, 'b)Relation__Relation \<Rightarrow>  ('a, 'c)Relation__Relation"	(infixl "o'_R" 64)
defs o_R_def: 
  "((r1:: ('b, 'c)Relation__Relation) o_R (r2:: ('a, 'b)Relation__Relation))
     \<equiv> (r2 :> r1)"
consts Relation__inverse :: " ('a, 'b)Relation__Relation \<Rightarrow> 
                              ('b, 'a)Relation__Relation"
defs Relation__inverse_def: 
  "Relation__inverse r \<equiv> (\<lambda> ((y::'b), (x::'a)). (x, y) \<in> r)"
consts Relation__restrictDomain :: " ('a, 'b)Relation__Relation \<Rightarrow> 
                                    'a set \<Rightarrow>  ('a, 'b)Relation__Relation"	(infixl "restrictDomain" 65)
defs Relation__restrictDomain_def: 
  "(r restrictDomain xS)
     \<equiv> (\<lambda> ((x::'a), (y::'b)). (x, y) \<in> r \<and> x \<in> xS)"
consts Relation__restrictRange :: " ('a, 'b)Relation__Relation \<Rightarrow> 
                                   'b set \<Rightarrow>  ('a, 'b)Relation__Relation"	(infixl "restrictRange" 65)
defs Relation__restrictRange_def: 
  "(r restrictRange yS)
     \<equiv> (\<lambda> ((x::'a), (y::'b)). (x, y) \<in> r \<and> y \<in> yS)"
consts Relation__total_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                   ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs Relation__total_p__stp_def: 
  "Relation__total_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (r:: ('a, 'b)Relation__Relation). 
            RSet P__a (Relation__domain__stp P__b r) 
              = RSet P__a UNIV)"
consts Relation__total_p :: " ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs Relation__total_p_def: 
  "Relation__total_p r \<equiv> (Relation__domain r = UNIV)"
types  ('a,'b)Relation__TotalRelation = " ('a, 'b)Relation__Relation"
consts Relation__surjective_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                        ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs Relation__surjective_p__stp_def: 
  "Relation__surjective_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (r:: ('a, 'b)Relation__Relation). 
            RSet P__b (Relation__range__stp P__a r) 
              = RSet P__b UNIV)"
consts Relation__surjective_p :: " ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs Relation__surjective_p_def: 
  "Relation__surjective_p r \<equiv> (Relation__range r = UNIV)"
types  ('a,'b)Relation__SurjectiveRelation = " ('a, 'b)Relation__Relation"
consts Relation__functional_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                        ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs Relation__functional_p__stp_def: 
  "Relation__functional_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (r:: ('a, 'b)Relation__Relation). 
            \<forall>(x::'a). 
              P__a x 
                \<longrightarrow> Relation__apply r x 
                      \<in> Set__single_p__stp P__b 
                          \<union> Set__empty_p__stp P__b)"
consts Relation__functional_p :: " ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs Relation__functional_p_def: 
  "Relation__functional_p r
     \<equiv> (\<forall>(x::'a). 
          Relation__apply r x \<in> Set__single_p \<union> Set__empty_p)"
types  ('a,'b)Relation__Map = " ('a, 'b)Relation__Relation"
consts Relation__injective_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                       ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs Relation__injective_p__stp_def: 
  "Relation__injective_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (r:: ('a, 'b)Relation__Relation). 
            \<forall>(y::'b). 
              P__b y 
                \<longrightarrow> Relation__applyi r y 
                      \<in> Set__single_p__stp P__a 
                          \<union> Set__empty_p__stp P__a)"
consts Relation__injective_p :: " ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs Relation__injective_p_def: 
  "Relation__injective_p r
     \<equiv> (\<forall>(y::'b). 
          Relation__applyi r y \<in> Set__single_p \<union> Set__empty_p)"
types  ('a,'b)Relation__InjectiveRelation = " ('a, 'b)Relation__Relation"
consts Relation__bijective_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                       ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs Relation__bijective_p__stp_def: 
  "Relation__bijective_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          Relation__total_p__stp(P__a, P__b) 
            \<inter> (Relation__surjective_p__stp(P__a, P__b) 
                 \<inter> (Relation__functional_p__stp(P__a, P__b) 
                      \<inter> Relation__injective_p__stp(P__a, P__b))))"
consts Relation__bijective_p :: " ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs Relation__bijective_p_def: 
  "Relation__bijective_p
     \<equiv> (Relation__total_p 
          \<inter> (Relation__surjective_p 
               \<inter> (Relation__functional_p \<inter> Relation__injective_p)))"
types  ('a,'b)Relation__BijectiveRelation = " ('a, 'b)Relation__Relation"
consts Relation__totalOn_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                    'a set \<Rightarrow> 
                                     ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs Relation__totalOn_p__stp_def: 
  "Relation__totalOn_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (s::'a set). 
            \<lambda> (r:: ('a, 'b)Relation__Relation). 
              RSet P__a (Relation__domain__stp P__b r) = s)"
consts Relation__totalOn_p :: "'a set \<Rightarrow>  ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs Relation__totalOn_p_def: 
  "Relation__totalOn_p s r \<equiv> (Relation__domain r = s)"
consts Relation__surjectiveOn_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                         'b set \<Rightarrow> 
                                          ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs Relation__surjectiveOn_p__stp_def: 
  "Relation__surjectiveOn_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (s::'b set). 
            \<lambda> (r:: ('a, 'b)Relation__Relation). 
              RSet P__b (Relation__range__stp P__a r) = s)"
consts Relation__surjectiveOn_p :: "'b set \<Rightarrow> 
                                     ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs Relation__surjectiveOn_p_def: 
  "Relation__surjectiveOn_p s r \<equiv> (Relation__range r = s)"
consts Relation__bijectiveOn_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                        'a set \<Rightarrow> 
                                        'b set \<Rightarrow> 
                                         ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs Relation__bijectiveOn_p__stp_def: 
  "Relation__bijectiveOn_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (s::'a set). 
            \<lambda> (s_cqt::'b set). 
              Relation__totalOn_p__stp(P__a, P__b) s 
                \<inter> (Relation__surjectiveOn_p__stp(P__a, P__b) s_cqt 
                     \<inter> (Relation__functional_p__stp(P__a, P__b) 
                          \<inter> Relation__injective_p__stp(P__a, P__b))))"
consts Relation__bijectiveOn_p :: "'a set \<Rightarrow> 
                                   'b set \<Rightarrow>  ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs Relation__bijectiveOn_p_def: 
  "Relation__bijectiveOn_p s s_cqt
     \<equiv> (Relation__totalOn_p s 
          \<inter> (Relation__surjectiveOn_p s_cqt 
               \<inter> (Relation__functional_p \<inter> Relation__injective_p)))"
types  ('a,'b)Relation__FiniteRelation = " ('a, 'b)Relation__Relation"
types  ('a,'b)Relation__InfiniteRelation = " ('a, 'b)Relation__Relation"
types  ('a,'b)Relation__CountableRelation = " ('a, 'b)Relation__Relation"
types  ('a,'b)Relation__UncountableRelation = " ('a, 'b)Relation__Relation"
end