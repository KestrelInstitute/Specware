theory SW_Map
imports SW_Relation
begin
consts MapAC__definedAt__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                                  ('a, 'b)Relation__Relation \<times> 'a \<Rightarrow> bool"
defs MapAC__definedAt__stp_def: 
  "MapAC__definedAt__stp P__b
     \<equiv> (\<lambda> ((m:: ('a, 'b)Relation__Relation), (x::'a)). 
          x \<in> Relation__domain__stp P__b m)"
consts MapAC__definedAt :: " ('a, 'b)Relation__Map \<Rightarrow> 'a \<Rightarrow> bool"	(infixl "definedAt" 60)
defs MapAC__definedAt_def: 
  "(m definedAt x) \<equiv> (x \<in> Relation__domain m)"
consts MapAC__undefinedAt__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                                    ('a, 'b)Relation__Relation \<times> 'a \<Rightarrow> bool"
defs MapAC__undefinedAt__stp_def: 
  "MapAC__undefinedAt__stp P__b
     \<equiv> (\<lambda> ((m:: ('a, 'b)Relation__Relation), (x::'a)). 
          x \<notin> Relation__domain__stp P__b m)"
consts MapAC__undefinedAt :: " ('a, 'b)Relation__Map \<Rightarrow> 'a \<Rightarrow> bool"	(infixl "undefinedAt" 60)
defs MapAC__undefinedAt_def: 
  "(m undefinedAt x) \<equiv> (x \<notin> Relation__domain m)"
theorem MapAC__e_at__stp_Obligation_the: 
  "\<lbrakk>Relation__functional_p__stp(\<lambda> ignore. True, P__b) (m::('a \<times> 'b) set); 
    Set_P (\<lambda> (ignore1, (x1::'b)). P__b x1) m; 
    P__b (y::'b); 
    Relation__functional_p__stp(\<lambda> ignore. True, P__b)
       (m:: ('a, 'b)Relation__Relation); 
    MapAC__definedAt__stp P__b(m, (x::'a))\<rbrakk> \<Longrightarrow> 
   \<exists>!(y::'b). P__b y \<and> (x, y) \<in> m"
   sorry
consts MapAC__e_at__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                             ('a, 'b)Relation__Relation \<times> 'a \<Rightarrow> 'b"
defs MapAC__e_at__stp_def: 
  "MapAC__e_at__stp P__b
     \<equiv> (\<lambda> ((m:: ('a, 'b)Relation__Relation), (x::'a)). 
          (THE (y::'b). P__b y \<and> (x, y) \<in> m))"
theorem MapAC__e_at_Obligation_the: 
  "\<lbrakk>Relation__functional_p (m:: ('a, 'b)Relation__Relation); 
    m definedAt x\<rbrakk> \<Longrightarrow> \<exists>!(y::'b). (x, y) \<in> m"
   sorry
consts MapAC__e_at :: " ('a, 'b)Relation__Map \<Rightarrow> 'a \<Rightarrow> 'b"	(infixl "@" 70)
defs MapAC__e_at_def: 
  "((m:: ('a, 'b)Relation__Map) @ (x::'a)) \<equiv> (THE (y::'b). (x, y) \<in> m)"
consts MapAC__e_at_at__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                                ('a, 'b)Relation__Relation \<times> 'a \<Rightarrow> 'b option"
defs MapAC__e_at_at__stp_def: 
  "MapAC__e_at_at__stp P__b
     \<equiv> (\<lambda> ((m:: ('a, 'b)Relation__Relation), (x::'a)). 
          if MapAC__definedAt__stp P__b(m, x) then 
            Some (m @ x)
          else 
            None)"
consts MapAC__e_at_at :: " ('a, 'b)Relation__Map \<Rightarrow> 'a \<Rightarrow> 'b option"	(infixl "@@" 70)
defs MapAC__e_at_at_def: 
  "(m @@ x) \<equiv> (if m definedAt x then Some (m @ x) else None)"
theorem MapAC__e_lt_lt_lt__stp_Obligation_subtype: 
  "\<lbrakk>Relation__functional_p__stp((P__a::'a \<Rightarrow> bool), P__b) (m2::('a \<times> 'b) set); 
    Set_P (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) m2; 
    Relation__functional_p__stp(P__a, P__b) (m1::('a \<times> 'b) set); 
    Set_P (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) m1; 
    Relation__functional_p__stp(P__a, P__b) (m::('a \<times> 'b) set); 
    Set_P (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) m; 
    P__a (x::'a); 
    Relation__functional_p__stp(P__a, P__b) (m2:: ('a, 'b)Relation__Relation); 
    Relation__functional_p__stp(P__a, P__b) (m1:: ('a, 'b)Relation__Relation); 
    Relation__functional_p__stp(P__a, P__b) m; 
    RSet P__a (Relation__domain__stp P__b m) 
      = RSet P__a
           (Relation__domain__stp P__b m1 
              \<union> Relation__domain__stp P__b m2); 
    x \<in> Relation__domain__stp P__b m\<rbrakk> \<Longrightarrow> 
   MapAC__definedAt__stp P__b(m, x)"
   sorry
theorem MapAC__e_lt_lt_lt__stp_Obligation_subtype0: 
  "\<lbrakk>Relation__functional_p__stp((P__a::'a \<Rightarrow> bool), P__b) (m2::('a \<times> 'b) set); 
    Set_P (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) m2; 
    Relation__functional_p__stp(P__a, P__b) (m1::('a \<times> 'b) set); 
    Set_P (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) m1; 
    Relation__functional_p__stp(P__a, P__b) (m::('a \<times> 'b) set); 
    Set_P (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) m; 
    P__a (x::'a); 
    Relation__functional_p__stp(P__a, P__b) (m2:: ('a, 'b)Relation__Relation); 
    Relation__functional_p__stp(P__a, P__b) (m1:: ('a, 'b)Relation__Relation); 
    Relation__functional_p__stp(P__a, P__b) (m:: ('a, 'b)Relation__Relation); 
    RSet P__a (Relation__domain__stp P__b m) 
      = RSet P__a
           (Relation__domain__stp P__b m1 
              \<union> Relation__domain__stp P__b m2); 
    x \<in> Relation__domain__stp P__b m; 
    \<not> (MapAC__definedAt__stp P__b(m2, x))\<rbrakk> \<Longrightarrow> 
   MapAC__definedAt__stp P__b(m1, x)"
   sorry
theorem MapAC__e_lt_lt_lt__stp_Obligation_the: 
  "\<lbrakk>Relation__functional_p__stp(P__a, P__b) (m2::('a \<times> 'b) set); 
    Set_P (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) m2; 
    Relation__functional_p__stp(P__a, P__b) (m1::('a \<times> 'b) set); 
    Set_P (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) m1; 
    Relation__functional_p__stp(P__a, P__b) m; 
    Set_P (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) m; 
    Relation__functional_p__stp(P__a, P__b) m2; 
    Relation__functional_p__stp(P__a, P__b) m1; 
    Relation__functional_p__stp(P__a, P__b) m\<rbrakk> \<Longrightarrow> 
   \<exists>!(m::('a \<times> 'b) set). 
     Relation__functional_p__stp(P__a, P__b) m 
       \<and> (Set_P (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) m 
        \<and> (RSet P__a (Relation__domain__stp P__b m) 
             = RSet P__a
                  (Relation__domain__stp P__b m1 
                     \<union> Relation__domain__stp P__b m2) 
         \<and> (\<forall>(x::'a). 
              P__a x \<and> x \<in> Relation__domain__stp P__b m 
                \<longrightarrow> m @ x 
                      = (if MapAC__definedAt__stp P__b(m2, x) then 
                           m2 @ x
                         else 
                           m1 @ x))))"
   sorry
consts MapAC__e_lt_lt_lt__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                   ('a, 'b)Relation__Relation
                                     \<times>  ('a, 'b)Relation__Relation \<Rightarrow> 
                                   ('a, 'b)Relation__Relation"
defs MapAC__e_lt_lt_lt__stp_def: 
  "MapAC__e_lt_lt_lt__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)Relation__Relation), 
             (m2:: ('a, 'b)Relation__Relation)). 
            (THE (m::('a \<times> 'b) set). 
            (Relation__functional_p__stp(P__a, P__b) m 
               \<and> Set_P
                    (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) m) 
              \<and> (RSet P__a (Relation__domain__stp P__b m) 
                   = RSet P__a
                        (Relation__domain__stp P__b m1 
                           \<union> Relation__domain__stp P__b m2) 
               \<and> (\<forall>(x::'a). 
                    P__a x 
                      \<and> x \<in> Relation__domain__stp P__b m 
                      \<longrightarrow> m @ x 
                            = (if MapAC__definedAt__stp P__b(m2, x) then 
                                 m2 @ x
                               else 
                                 m1 @ x)))))"
theorem MapAC__e_lt_lt_lt_Obligation_subtype: 
  "\<lbrakk>Relation__functional_p (m2:: ('a, 'b)Relation__Relation); 
    Relation__functional_p (m1:: ('a, 'b)Relation__Relation); 
    Relation__functional_p (m:: ('a, 'b)Relation__Relation); 
    Relation__domain m 
      = Relation__domain (m1:: ('a, 'b)Relation__Map) 
          \<union> Relation__domain (m2:: ('a, 'b)Relation__Map); 
    x \<in> Relation__domain m; 
    Relation__functional_p m\<rbrakk> \<Longrightarrow> m definedAt x"
   sorry
theorem MapAC__e_lt_lt_lt_Obligation_subtype0: 
  "\<lbrakk>Relation__functional_p (m2:: ('a, 'b)Relation__Relation); 
    Relation__functional_p (m1:: ('a, 'b)Relation__Relation); 
    Relation__functional_p (m:: ('a, 'b)Relation__Relation); 
    Relation__domain (m:: ('a, 'b)Relation__Map) 
      = Relation__domain m1 
          \<union> Relation__domain (m2:: ('a, 'b)Relation__Map); 
    x \<in> Relation__domain m; 
    \<not> (m2 definedAt x); 
    Relation__functional_p m1\<rbrakk> \<Longrightarrow> m1 definedAt x"
   sorry
theorem MapAC__e_lt_lt_lt_Obligation_the: 
  "\<lbrakk>Relation__functional_p (m2:: ('a, 'b)Relation__Relation); 
    Relation__functional_p m1\<rbrakk> \<Longrightarrow> 
   \<exists>!(m:: ('a, 'b)Relation__Relation). 
     Relation__functional_p m 
       \<and> (Relation__domain m 
            = Relation__domain m1 \<union> Relation__domain m2 
        \<and> (\<forall>(x::'a). 
             x \<in> Relation__domain m 
               \<longrightarrow> m @ x 
                     = (if m2 definedAt x then m2 @ x else m1 @ x)))"
   sorry
consts MapAC__e_lt_lt_lt :: " ('a, 'b)Relation__Map \<Rightarrow> 
                              ('a, 'b)Relation__Map \<Rightarrow>  ('a, 'b)Relation__Map"	(infixl "<<<" 65)
defs MapAC__e_lt_lt_lt_def: 
  "(m1 <<< m2)
     \<equiv> (THE (m:: ('a, 'b)Relation__Relation). 
       Relation__functional_p m 
         \<and> (Relation__domain m 
              = Relation__domain m1 \<union> Relation__domain m2 
          \<and> (\<forall>(x::'a). 
               x \<in> Relation__domain m 
                 \<longrightarrow> m @ x 
                       = (if m2 definedAt x then 
                            m2 @ x
                          else 
                            m1 @ x))))"
theorem MapAC__e_lt_lt_lt_subtype_constr: 
  "\<lbrakk>Relation__functional_p
       (fst (dom__lt_lt_lt::
              ('a, 'b)Relation__Relation \<times>  ('a, 'b)Relation__Relation)); 
    Relation__functional_p (snd dom__lt_lt_lt)\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (let (x,y) = dom__lt_lt_lt in x <<< y)"
   sorry
(* theorem MapAC__update__stp_Obligation_subtype:  *)
(*   "\<lbrakk>Relation__functional_p__stp(P__a, P__b) (m::('a \<times> 'b) set);  *)
(*     Set_P (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) m;  *)
(*     P__a (x::'a);  *)
(*     P__b y;  *)
(*     Relation__functional_p__stp(P__a, P__b) (m:: ('a, 'b)Relation__Relation);  *)
(*     Set_P (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) (Set__single(x, y));  *)
(*     x0 = Set__single(x0, y)\<rbrakk> \<Longrightarrow>  *)
(*    Relation__functional_p__stp(P__a, P__b) *)
(*       (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1) x0)  *)
(*      \<and> Set_P (\<lambda> ((x0_1::'a), (x1_1::'b)). P__a x0_1 \<and> P__b x1_1) x0" *)
(*    sorry *)
consts MapAC__update__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)Relation__Relation \<Rightarrow> 
                              'a \<Rightarrow> 'b \<Rightarrow>  ('a, 'b)Relation__Relation"
defs MapAC__update__stp_def: 
  "MapAC__update__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)Relation__Relation). 
            \<lambda> (x::'a). 
              \<lambda> (y::'b). 
                MapAC__e_lt_lt_lt__stp(P__a, P__b)
                  (m, 
                   RFun
                      (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                      (Set__single(x, y))))"
theorem MapAC__update_Obligation_subtype: 
  "Relation__functional_p (Set__single(x, y))"
   sorry
consts MapAC__update :: " ('a, 'b)Relation__Map \<Rightarrow> 
                         'a \<Rightarrow> 'b \<Rightarrow>  ('a, 'b)Relation__Map"
defs MapAC__update_def: 
  "MapAC__update m x y \<equiv> (m <<< Set__single(x, y))"
theorem MapAC__e_dsh_dsh_Obligation_subtype: 
  "\<lbrakk>Relation__functional_p m\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (m restrictDomain - xS)"
   sorry
consts MapAC__e_dsh_dsh :: " ('a, 'b)Relation__Map \<Rightarrow> 
                            'a set \<Rightarrow>  ('a, 'b)Relation__Map"	(infixl "--" 65)
defs MapAC__e_dsh_dsh_def: "(m -- xS) \<equiv> (m restrictDomain - xS)"
theorem MapAC__e_dsh_dsh_subtype_constr: 
  "\<lbrakk>Relation__functional_p
       (fst (dom__dsh_dsh:: ('a, 'b)Relation__Relation \<times> 'a set))\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (let (x,y) = dom__dsh_dsh in x -- y)"
   sorry
consts mless :: " ('a, 'b)Relation__Map \<Rightarrow> 'a \<Rightarrow>  ('a, 'b)Relation__Map"	(infixl "mless" 65)
defs mless_def [simp]: 
  "((m:: ('a, 'b)Relation__Map) mless x) \<equiv> (m -- Set__single x)"
theorem MapAC__e_dsh_subtype_constr: 
  "\<lbrakk>Relation__functional_p (fst (dom__dsh:: ('a, 'b)Relation__Relation \<times> 'a))\<rbrakk>
    \<Longrightarrow> Relation__functional_p (let (x,y) = dom__dsh in x mless y)"
   sorry
consts MapAC__agree_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                ('a, 'b)Relation__Relation
                                  \<times>  ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs MapAC__agree_p__stp_def: 
  "MapAC__agree_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)Relation__Relation), 
             (m2:: ('a, 'b)Relation__Relation)). 
            Relation__functional_p__stp(P__a, P__b)
               (RFun (\<lambda> ((x0::'a), (x1::'b)). P__a x0 \<and> P__b x1)
                   (m1 \<union> m2)))"
consts MapAC__agree_p :: " ('a, 'b)Relation__Map \<times>  ('a, 'b)Relation__Map \<Rightarrow> 
                          bool"
defs MapAC__agree_p_def: 
  "MapAC__agree_p
     \<equiv> (\<lambda> ((m1:: ('a, 'b)Relation__Map), (m2:: ('a, 'b)Relation__Map)). 
          Relation__functional_p (m1 \<union> m2))"
types  ('a,'b)MapAC__TotalMap = " ('a, 'b)Relation__Map"
theorem MapAC__fromFunction_Obligation_subtype: 
  "Relation__total_p (\<lambda> ((x::'a), (y::'b)). y = (f::'a \<Rightarrow> 'b) x) 
     \<and> Relation__functional_p (\<lambda> ((x::'a), (y::'b)). y = f x)"
   sorry
consts MapAC__fromFunction :: "('a \<Rightarrow> 'b) \<Rightarrow>  ('a, 'b)MapAC__TotalMap"
defs MapAC__fromFunction_def: 
  "MapAC__fromFunction f \<equiv> (\<lambda> ((x::'a), (y::'b)). y = f x)"
theorem MapAC__fromFunction_subtype_constr: 
  "Relation__functional_p (MapAC__fromFunction dom_fromFunction) 
     \<and> Relation__total_p (MapAC__fromFunction dom_fromFunction)"
   sorry
theorem MapAC__toFunction_Obligation_subtype: 
  "Function__bijective_p__stp(\<lambda> ignore. True, Relation__total_p)
      MapAC__fromFunction"
   sorry
consts MapAC__toFunction :: " ('a, 'b)MapAC__TotalMap \<Rightarrow> 'a \<Rightarrow> 'b"
defs MapAC__toFunction_def: 
  "MapAC__toFunction \<equiv> inv MapAC__fromFunction"
theorem MapAC__fromPartialFun_Obligation_subtype: 
  "Relation__functional_p
      (\<lambda> ((x::'a), (y::'b)). (f::'a \<Rightarrow> 'b option) x = Some y)"
   sorry
consts MapAC__fromPartialFun :: "('a \<Rightarrow> 'b option) \<Rightarrow>  ('a, 'b)Relation__Map"
defs MapAC__fromPartialFun_def: 
  "MapAC__fromPartialFun f
     \<equiv> (\<lambda> ((x::'a), (y::'b)). f x = Some y)"
theorem MapAC__fromPartialFun_subtype_constr: 
  "Relation__functional_p (MapAC__fromPartialFun dom_fromPartialFun)"
   sorry
theorem MapAC__toPartialFun_Obligation_subtype: 
  "Function__bijective_p__stp(\<lambda> ignore. True, Relation__functional_p)
      MapAC__fromPartialFun"
   sorry
consts MapAC__toPartialFun :: " ('a, 'b)Relation__Map \<Rightarrow> 'a \<Rightarrow> 'b option"
defs MapAC__toPartialFun_def: 
  "MapAC__toPartialFun \<equiv> inv MapAC__fromPartialFun"
types  ('a,'b)MapAC__SurjectiveMap = " ('a, 'b)Relation__Map"
types  ('a,'b)MapAC__InjectiveMap = " ('a, 'b)Relation__Map"
types  ('a,'b)MapAC__BijectiveMap = " ('a, 'b)Relation__Map"
types  ('a,'b)MapAC__FiniteMap = " ('a, 'b)Relation__Map"
types  ('a,'b)MapAC__InfiniteMap = " ('a, 'b)Relation__Map"
types  ('a,'b)MapAC__CountableMap = " ('a, 'b)Relation__Map"
types  ('a,'b)MapAC__UncountableMap = " ('a, 'b)Relation__Map"
end