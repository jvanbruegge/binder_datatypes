theory PermFreeV_corecursor
  imports PermFreeV_comodel_is_SwapFreshV_comodel PermFree_PermFreeV_comodels
begin  

   
context PermFreeV_comodel
begin


definition pick :: "(var \<times> 'D) set \<Rightarrow> (var \<times> 'D)" where 
"pick K \<equiv> (SOME x_d. x_d \<in> K)"

lemma pick: 
assumes "DestD dd = Ll K"
shows "pick K \<in> K"
unfolding pick_def apply(rule someI_ex) using assms DestD_LmD_NE by blast 


primcorec f :: "'D \<Rightarrow> ptrm" where 
"f d = (case DestD d of 
   Vv x \<Rightarrow> PVr x
  |Inr (Inl (d1,d2)) \<Rightarrow> PAp (f d1) (f d2)
  |Inr (Inr K) \<Rightarrow> let (x,d1) = pick K in PLm x (f d1)
 )"

lemma f_DestD_Vv[simp]: "DestD d = Vv x \<Longrightarrow> f d = PVr x"
by (simp add: f.code)

lemma f_DestD_Aa[simp]: "DestD d = Aa (d1,d2) \<Longrightarrow> f d = PAp (f d1) (f d2)"
by (simp add: f.code)

lemma f_DestD_Ll[simp]: "DestD d = Ll K \<Longrightarrow> (x,d1) = pick K \<Longrightarrow> f d = PLm x (f d1)"
by (auto simp: f.code split: prod.splits)

lemma DestD_cases[case_names Vv Aa Ll]: 
obtains x where "DestD d = Vv x" 
       |d1 d2 where "DestD d = Aa (d1,d2)"
       |K where "DestD d = Ll K"
apply(cases "DestD d", auto) 
by (metis sumE surj_pair)

(* *)
definition g0 where "g0 d \<equiv> abs_trm (f d)"

proposition g0_Vr[simp]: "DestD d = Vv x \<Longrightarrow> g0 d = Vr x"
unfolding g0_def Vr_def by simp

proposition g0_Ap[simp]: "DestD d = Aa (d1,d2) \<Longrightarrow> g0 d = Ap (g0 d1) (g0 d2)"
unfolding g0_def Ap_def by (simp add: abs_trm_PAp)

lemma g0_Lm'[simp]: "DestD d = Ll K \<Longrightarrow> (x,d1) = pick K \<Longrightarrow> g0 d = Lm x (g0 d1)"
unfolding g0_def Lm_def by (simp add: abs_trm_PLm)


(* *)

proposition g0_fresh: 
assumes "freshD x d"
shows "fresh x (g0 d)" 
proof-
  {fix t assume "\<exists>d. freshD x d \<and> t = g0 d"
   hence "fresh x t"
   proof(coinduct rule: fresh_coind)
     case (1 y t)
     then obtain d where d: "freshD y d" and t: "t = g0 d" by auto
     show ?case proof(cases d rule: DestD_cases)
       case (Vv x)
       then show ?thesis unfolding t apply-apply(intro disjI1)  
         using FrVrI[OF d Vv] by auto
     next
       case (Aa d1 d2)
       then show ?thesis unfolding t apply-apply(rule disjI2, rule disjI1)  
         using FrApI[OF d Aa] by auto
     next
       case (Ll K)
       hence Kne: "K \<noteq> {}" using DestD_LmD_NE by auto
       obtain x d1 where 1: "pick K = (x,d1)" by(cases "pick K", auto)
       hence "(x,d1) \<in> K " using pick[OF Ll] by simp
       with Ll 1 show ?thesis unfolding t apply-apply(rule disjI2, rule disjI2) 
         apply(rule exI[of _ x]) apply(rule exI[of _ "g0 d1"]) 
         using FrLmI[OF d Ll] by auto
     qed
   qed
  }
  thus ?thesis using assms by metis
qed

proposition Fvars_g0: 
"Fvars (g0 d) \<subseteq> FvarsD d"
using g0_fresh freshD_def by blast

lemma cmpTrans_id_update: 
"bij \<sigma> \<Longrightarrow> bij \<tau> \<Longrightarrow> (\<sigma> \<circ> \<tau>) = (id(\<sigma> x := \<sigma> (\<tau> x'), \<sigma> (\<tau> x') := \<sigma> x) \<circ> \<sigma> \<circ> (id(x := \<tau> x', \<tau> x' := x) \<circ> \<tau>))"
unfolding fun_eq_iff apply auto
by (metis bij_pointE)+

lemma g0_perm_comp: 
assumes "fsupp \<tau>" "bij \<tau>" "fsupp \<sigma>" "bij \<sigma>"
shows "perm (g0 (permD d \<tau>)) \<sigma> = perm (g0 d) (\<sigma> o \<tau>)"
proof-
  {fix t t'
   assume "\<exists>d \<tau> \<sigma>. fsupp \<tau> \<and> bij \<tau> \<and> fsupp \<sigma> \<and> bij \<sigma> \<and> t = perm (g0 (permD d \<tau>)) \<sigma> \<and> t' = perm (g0 d) (\<sigma> o \<tau>)"
   hence "t = t'"
   proof(coinduct rule: trm_coind')
     case (1 tt tt')
     then obtain dd \<tau> \<sigma> where \<tau>[simp]: "fsupp \<tau>" " bij \<tau>" and \<sigma>[simp]: "fsupp \<sigma>"" bij \<sigma>"
     and tt: "tt = perm (g0 (permD dd \<tau>)) \<sigma>" and tt': "tt' = perm (g0 dd) (\<sigma> o \<tau>)" by blast
     hence \<sigma>\<tau>[simp]: "fsupp (\<sigma> o \<tau>)" " bij (\<sigma> o \<tau>)" 
     using fsupp_o  by (auto simp: bij_o)
     have i\<sigma>[simp]:  "fsupp (inv \<sigma>)" "bij (inv \<sigma>)" by auto

     show ?case proof(cases dd rule: DestD_cases)
       case (Vv x)
       show ?thesis unfolding tt tt' apply-apply(intro disjI1)
       apply(rule exI[of _ "\<sigma> (\<tau> x)"])  using PmVrI[OF \<sigma>\<tau> Vv]  PmVrI[OF \<tau> Vv] tt apply auto   
       by (simp add: Vv)  
     next
       case (Aa d1 d2)
       show ?thesis unfolding tt tt' apply-apply(rule disjI2, rule disjI1) 
       apply(rule exI[of _ "perm (g0 (permD d1 \<tau>)) \<sigma>"]) apply(rule exI[of _ "perm (g0 d1) (\<sigma> o \<tau>)"]) 
       apply(rule exI[of _ "perm (g0 (permD d2 \<tau>)) \<sigma>"]) apply(rule exI[of _ "perm (g0 d2) (\<sigma> o \<tau>)"]) 
       using Aa g0_Ap[OF PmApI[OF _ _ Aa]] apply(intro conjI)
         subgoal by simp 
         subgoal by simp 
         subgoal apply(rule disjI1) apply(rule exI[of _ "d1"], rule exI[of _ "\<tau>"], rule exI[of _ "\<sigma>"])  
           by auto (metis comp_apply)
         subgoal apply(rule disjI1) apply(rule exI[of _ "d2"], rule exI[of _ "\<tau>"], rule exI[of _ "\<sigma>"]) 
           by auto (metis comp_apply) .
     next
       case (Ll K)
       from Ll obtain K\<tau> where Ll\<tau>: "DestD (permD dd \<tau>) = Ll K\<tau>" and K': "(\<forall>x a. (x, a) \<in> K \<longrightarrow> (\<tau> x, permD a \<tau>) \<in> K\<tau>)"
       using PmLmI[OF \<tau> Ll] by auto

       obtain x' d' where 2: "(x',d') \<in> K" "g0 dd = Lm x' (g0 d')"
       using Ll by (metis g0_Lm' pick surj_pair)
       hence tt': "tt' = Lm (\<sigma> (\<tau> x')) (perm (g0 d') (\<sigma> o \<tau>))" using tt' by simp

       obtain x d where 1: "(x,d) \<in> K\<tau>" "g0 (permD dd \<tau>) = Lm x (g0 d)"
       using Ll\<tau> by (metis g0_Lm' pick surj_pair)
       hence tt: "tt = Lm (\<sigma> x) (perm (g0 d) \<sigma>)" unfolding tt by simp
     
       have "(\<tau> x', permD d' \<tau>) \<in> K\<tau>" using 2 K' by auto

       with 1(1) have 
       "(x = \<tau> x' \<or> \<tau> x' \<notin> FvarsD d) \<and> permD (permD d' \<tau>) (id(x := \<tau> x', \<tau> x' := x)) = d"
       using PmBvrI'[OF Ll\<tau>, of "\<tau> x'" "permD d' \<tau>" x d] by auto
       hence "x = \<tau> x' \<or> freshD (\<tau> x') d" and d: "swapD (permD d' \<tau>) x (\<tau> x') = d"
       unfolding freshD_def permD_swapD by auto  
       hence fresh: "\<tau> x' = x \<or> fresh (\<tau> x') (g0 (swapD (permD d' \<tau>) x (\<tau> x')))"  
         using g0_fresh by blast

       have tt: "tt = Lm (\<sigma> x) (perm (g0 (swapD (permD d' \<tau>) x (\<tau> x'))) \<sigma>)"
       using tt unfolding d .
            
       show ?thesis unfolding tt tt' apply-apply(rule disjI2, rule disjI2) 
       apply(rule exI[of _ "\<sigma> x"]) apply(rule exI[of _ "perm (g0 (swapD (permD d' \<tau>) x (\<tau> x'))) \<sigma>"])
       apply(rule exI[of _ "\<sigma> (\<tau> x')"]) apply(rule exI[of _ "perm (g0 d') (\<sigma> \<circ> \<tau>)"]) apply(intro conjI)
         subgoal .. 
         subgoal ..
         subgoal using fresh using fresh_perm by auto
         subgoal apply(rule disjI1) 
         apply(rule exI[of _ d']) apply(rule exI[of _ "(id(x:=\<tau> x',\<tau> x' := x)) o \<tau>"])
         apply(rule exI[of _ "(id(\<sigma> x:=\<sigma> (\<tau> x'),\<sigma> (\<tau> x') := \<sigma> x)) o \<sigma>"])
         apply(intro conjI)
           subgoal using \<tau>(1) fsupp_id fsupp_o fsupp_upd by presburger
           subgoal using \<tau>(2) bij_o by blast
           subgoal using \<sigma>(1) fsupp_id fsupp_o fsupp_upd by presburger
           subgoal using \<sigma>(2) bij_o by blast
           subgoal  by (smt \<sigma> \<tau>  bij_id_upd2 fsupp_id fsupp_upd fun_upd_twist permD_comp permD_swapD 
             perm_comp perm_swap)
           subgoal apply(subst cmpTrans_id_update) by auto . .
    qed
   qed 
  }
  thus ?thesis using assms by blast
qed

proposition g0_perm: 
assumes "fsupp \<tau>" "bij \<tau>"  
shows "g0 (permD d \<tau>) = perm (g0 d) \<tau>"
using g0_perm_comp[OF assms, of id, simplified] .

corollary g0_swapD: 
"swap (g0 d) z1 z2 = g0 (swapD d z1 z2)"
by (metis bij_id_upd2 fsupp_id fsupp_upd g0_perm permD_swapD perm_swap)

proposition g0_Lm[simp]: 
assumes d: "DestD d = Ll K" and xd1: "(x,d1) \<in> K"
shows "g0 d = Lm x (g0 d1)" 
proof-
  obtain x' d1' where xd1': "(x',d1') \<in> K" and g0: "g0 d = Lm x' (g0 d1')"
  by (metis d g0_Lm' pick surj_pair)
  from SwBvrI[OF d] xd1 xd1' have "x' = x \<or> freshD x' d1" and "swapD d1 x' x = d1'"
  by auto
  hence "x' = x \<or> fresh x' (g0 d1)" and "swap (g0 d1) x' x = g0 d1'"
  using g0_fresh g0_swapD by auto
  thus ?thesis unfolding g0 by (metis Lm_swap_rename)
qed

(* Uniqueness: *)
theorem g0_unique: 
assumes a1: "\<And>d x. DestD d = Vv x \<Longrightarrow> g d = Vr x" 
and a2: "\<And> d d1 d2. DestD d = Aa (d1,d2) \<Longrightarrow> g d = Ap (g d1) (g d2)"
and a3: "\<And> d x d1 K. DestD d = Ll K \<Longrightarrow> (x,d1) \<in> K \<Longrightarrow> g d = Lm x (g d1)"
shows "g = g0"
proof-
  {fix t t'
   assume "\<exists>d. t = g d \<and> t' = g0 d"
   hence "t = t'"
   proof(coinduct rule: trm_coind')
     case (1 tt tt')
     then obtain dd where tt: "tt = g dd" "tt' = g0 dd" by auto
     then show ?case proof(cases dd rule: DestD_cases)
       case (Vv x)
       show ?thesis apply(rule disjI1)
       using Vv a1 unfolding tt by auto 
     next
       case (Aa d1 d2)
       show ?thesis apply(rule disjI2, rule disjI1)
       using Aa a2 unfolding tt by auto
     next
       case (Ll K)
       show ?thesis apply(rule disjI2, rule disjI2)
       using Ll a3 unfolding tt  
       by (metis comp_apply g0_Lm' old.prod.exhaust pick swap_id)
     qed
   qed
  }
  thus ?thesis unfolding fun_eq_iff by blast
qed


lemmas g0 = g0_Vr g0_Ap g0_Lm g0_perm Fvars_g0 g0_unique

end (* context PermFreeV_comodel *) 



end


