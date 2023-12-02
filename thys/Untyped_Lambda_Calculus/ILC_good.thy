(* Here we instantiate the general enhanced rule induction to the renaming-equivalence 
relation from Mazza  *)
theory ILC_good    
imports LC2 ILC2 BSmall 
"../Instantiation_Infrastructure/Curry_LFP" 
begin

(* *)
inductive good where 
iVar: "super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> good (iVar x)"
|
iLam: "super xs \<Longrightarrow> good e \<Longrightarrow> good (iLam xs e)"
|
iApp: "good e1 \<Longrightarrow> (\<forall>e2. e2 \<in> sset es2 \<longrightarrow> good e2) \<Longrightarrow> 
  (\<forall>e2 e2'. {e2,e2'} \<subseteq> sset es2 \<longrightarrow> touchedSuperT e2 = touchedSuperT e2') 
  \<Longrightarrow> good (iApp e1 es2)"


(* INSTANTIATING THE ABSTRACT SETTING: *)

(* PREPARING THE INSTANTIATION: *)

lemma good_finite_touchedSuperT: 
"good e \<Longrightarrow> finite (touchedSuperT e)"
proof(induct rule: good.induct)
  case (iVar x)
  then show ?case  
  by (metis finite.emptyI finite_singleton touchedSuper_iVar_singl)
next
  case (iLam xs e)
  then show ?case by auto
next
  case (iApp e1 es2)
  obtain e2 where e2: "e2 \<in> sset es2"  
  using shd_sset by blast+
  hence 0: "touchedSuperT ` sset es2 = {touchedSuperT e2}" 
  using iApp(4) by blast
  have "finite (\<Union> (touchedSuperT ` sset es2))" 
  unfolding 0 using iApp(3) e2 by auto    
  thus ?case using iApp by (metis finite_UnI touchedSuper_iApp)
qed


(* INSTANTIATING THE CComponents LOCALE: *)

type_synonym T = "itrm"

definition Tmap :: "(ivar \<Rightarrow> ivar) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> irrename f"

fun Tfvars :: "T \<Rightarrow> ivar set" where 
"Tfvars e = FFVars e"



interpretation CComponents where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars 
and Bmap = Bmap and Bvars = Bvars and wfB = wfB and bsmall = bsmall
apply standard unfolding ssbij_def Tmap_def  
using small_Un small_def iterm.card_of_FFVars_bounds
apply (auto simp: iterm.rrename_id0s map_prod.comp 
iterm.rrename_comp0s inf_A bsmall_def intro!: ext split: option.splits)
apply (simp add: iterm.set_bd_UNIV) 
apply (simp add: comp_def dstream.map_comp)
apply (simp add: dstream_map_ident_strong)
unfolding bsmall_def touchedSuper_def  
using super_Un_ddset_triv  
by (smt (verit) finite_Un rev_finite_subset) 

lemma wfBij_presSuper: "wfBij = presSuper"
unfolding wfBij_def presSuper_def fun_eq_iff apply safe
  subgoal for \<sigma> xs apply(erule allE[of _ "Some xs"]) by auto 
  subgoal for \<sigma> xs apply(erule allE[of _ "Some xs"]) by auto 
  subgoal for \<sigma> xxs apply(cases xxs) by auto 
  subgoal for \<sigma> xxs apply(cases xxs) by auto .

definition G :: "(T \<Rightarrow> bool) \<Rightarrow> B \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>R xxs t.  
         (\<exists>xs x. xxs = None \<and> t = iVar x \<and> 
                 super xs \<and> x \<in> dsset xs) 
         \<or>
         (\<exists>xs e. xxs = Some xs \<and> t = iLam xs e \<and>  
                    super xs \<and> R e)
         \<or> 
         (\<exists>e1 es2. xxs = None \<and> t = iApp e1 es2 \<and> 
                   R e1 \<and> (\<forall>e. e \<in> sset es2 \<longrightarrow> R e) \<and> 
                   (\<forall>e2 e2'. {e2,e2'} \<subseteq> sset es2 \<longrightarrow> touchedSuperT e2 = touchedSuperT e2') )"
 

(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma G_mmono: "R \<le> R' \<Longrightarrow> G R xxs t \<Longrightarrow> G R' xxs t"
unfolding G_def by fastforce


(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma G_eequiv: 
"ssbij \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> G R xxs t \<Longrightarrow> 
 G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Bmap \<sigma> xxs) (Tmap \<sigma> t)"
unfolding G_def apply(elim disjE)
  subgoal apply(rule disjI3_1)
  subgoal apply(elim exE) subgoal for xs x
  apply(rule exI[of _ "dsmap \<sigma> xs"]) 
  apply(rule exI[of _ "\<sigma> x"]) 
  unfolding ssbij_def small_def Tmap_def wfBij_def
  apply simp by (metis option.simps(5)) . .
  (* *)
  subgoal apply(rule disjI3_2)
  subgoal apply(elim exE) subgoal for xs e
  apply(rule exI[of _ "dsmap \<sigma> xs"]) 
  apply(rule exI[of _ "irrename \<sigma> e"])  
  unfolding ssbij_def small_def Tmap_def wfBij_def
  apply (simp add: iterm.rrename_comps) by (metis option.simps(5)) . . 
  (* *)
  subgoal apply(rule disjI3_3) 
  subgoal apply(elim exE) subgoal for e1 es2
  apply(rule exI[of _ "irrename \<sigma> e1"]) 
  apply(rule exI[of _ "smap (irrename \<sigma>) es2"]) 
  unfolding ssbij_def small_def Tmap_def wfBij_presSuper 
  apply (simp add: iterm.rrename_comps image_def) 
  by (metis inv_simp1 iterm.rrename_bijs iterm.rrename_inv_simps touchedSuperT_irrename) . . .

(* *)

lemma G_wfB: "G R xxs t \<Longrightarrow> wfB xxs"
unfolding G_def by auto 

lemma eextend_to_wfBij: 
assumes "wfB xxs" "small A" "bsmall A" "A' \<subseteq> A" "Bvars xxs \<inter> A' = {}"
shows "\<exists>\<rho>. ssbij \<rho> \<and> wfBij \<rho> \<and> \<rho> ` Bvars xxs \<inter> A = {} \<and> id_on A' \<rho>" 
proof(cases xxs)
  case None
  thus ?thesis apply(intro exI[of _ id]) unfolding ssbij_def by auto
next
  case (Some xs)
  hence 0: "super xs" "|A| <o |UNIV::ivar set|" "finite (touchedSuper A)" "A' \<subseteq> A"
  "dsset xs \<inter> A' = {}"
  using assms by (auto split: option.splits simp: small_def bsmall_def) 
  show ?thesis using extend_super[OF 0] apply safe
  subgoal for \<rho> apply(rule exI[of _ \<rho>]) 
  using Some by (auto split: option.splits simp: wfBij_presSuper ssbij_def) .
qed 


interpretation Reneqv : IInduct1 
where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars and Bmap = Bmap and Bvars = Bvars 
and wfB = wfB and bsmall = bsmall and GG = G
apply standard
using G_mmono G_eequiv G_wfB eextend_to_wfBij by auto


(* *)

lemma good_I: "good t = Reneqv.II t" 
unfolding good_def Reneqv.II_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R tt apply(rule iffI)
  subgoal apply(elim disjE exE conjE)
    \<^cancel>\<open>iVar: \<close>
    subgoal for xs x apply(rule exI[of _ None]) apply(rule disjI3_1) by auto
    \<^cancel>\<open>iLam: \<close> 
    subgoal for xs e apply(rule exI[of _ "Some xs"]) apply(rule disjI3_2) by auto 
    \<^cancel>\<open>iApp: \<close>
    subgoal apply(rule exI[of _ None]) apply(rule disjI3_3) by auto .
    (* *)
  subgoal apply(elim disjE exE conjE)
    \<^cancel>\<open>iVar: \<close>
    subgoal apply(rule disjI3_1) by auto
    \<^cancel>\<open>iLam: \<close>
    subgoal apply(rule disjI3_2) by auto
    \<^cancel>\<open>iApp: \<close>
    subgoal apply(rule disjI3_3) by auto . . .
  

lemma III_bsmall: "Reneqv.II t \<Longrightarrow> bsmall (Tfvars t)"
apply simp
  unfolding good_I[symmetric] 
  unfolding bsmall_def using good_finite_touchedSuperT touchedSuperT_def by auto 

lemma Tvars_dsset: "dsset xs \<inter> (Tfvars t - dsset xs) = {}" 
  "|Tfvars t - dsset xs| <o |UNIV::ivar set|"
  "Reneqv.II t \<Longrightarrow> finite (touchedSuper (Tfvars t - dsset ys))"
subgoal using Diff_disjoint .
subgoal using ILC2.small_def card_of_minus_bound ssmall_Tfvars by blast
subgoal apply(subgoal_tac "bsmall (Tfvars t)")
  subgoal unfolding bsmall_def 
    by (meson Diff_subset rev_finite_subset touchedSuper_mono) 
  subgoal by (metis III_bsmall) . .

lemma G_rrefresh: 
"(\<forall>t. R t \<longrightarrow> Reneqv.II t) \<Longrightarrow> 
 (\<forall>\<sigma> t. ssbij \<sigma> \<and> wfBij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> 
 G R xxs t \<Longrightarrow> 
 \<exists>yys. Bvars yys \<inter> Tfvars t = {} \<and> G R yys t"
apply(subgoal_tac "Reneqv.II t") defer
apply (metis Reneqv.GG_mmono2 Reneqv.II.simps predicate1I)
subgoal premises p using p apply-
apply(frule G_wfB)
unfolding G_def Tmap_def apply safe
  subgoal for xs x 
  apply(rule exI[of _ None])  
  apply(intro conjI)
    subgoal by simp 
    subgoal apply(rule disjI3_1) 
    apply(rule exI[of _ xs]) 
    apply(rule exI[of _ x])
    apply simp . .
  (* *)
  subgoal for xs e
  apply(frule refresh_super[OF Tvars_dsset(1,2) Tvars_dsset(3)[OF p(4)]])
  apply safe
  subgoal for f
  apply(rule exI[of _ "Some (dsmap f xs)"])  
  apply(intro conjI) 
    subgoal unfolding id_on_def presSuper_def by auto
    subgoal apply(rule disjI3_2)
    apply(rule exI[of _ "dsmap f xs"]) 
    apply(rule exI[of _ "irrename f e"])  
    unfolding presSuper_def apply simp apply(intro conjI)
      subgoal apply(subst iLam_irrename[of "f"]) unfolding id_on_def by auto
      subgoal apply(subst irrename_eq_itvsubst_iVar)
        subgoal unfolding ssbij_def by auto
        subgoal unfolding ssbij_def by auto
        subgoal unfolding id_on_def ssbij_def wfBij_def 
        by (auto simp: irrename_eq_itvsubst_iVar split: option.splits) . . . .
  (* *)
  subgoal for e1 es2 
  apply(rule exI[of _ None])  
  apply(intro conjI)
    subgoal by simp 
    subgoal apply(rule disjI3_3) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "es2"]) 
    apply(cases t) by simp . . .
 

(* FINALLY, INTERPRETING THE IInduct LOCALE: *)

interpretation Reneqv : IInduct
where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars and 
Bmap = Bmap and Bvars = Bvars and wfB = wfB and bsmall = bsmall 
and GG = G
apply standard using III_bsmall G_rrefresh by auto

(* *)


(* FROM ABSTRACT BACK TO CONCRETE: *)
thm good.induct[no_vars] 

corollary BE_induct_good[consumes 2, case_names iVar iLam iApp]: 
assumes par: "\<And>p. small (Pfvars p) \<and> bsmall (Pfvars p)"
and st: "good t"  
and iVar: "\<And>xs x p. 
  super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow>
  R p (iVar x)"
and iLam: "\<And>e xs p. 
  dsset xs \<inter> Pfvars p = {} \<Longrightarrow> 
  super xs \<Longrightarrow> good e \<Longrightarrow> (\<forall>p'. R p' e) \<Longrightarrow> 
  R p (iLam xs e)" 
and iApp: "\<And>e1 es2 p. 
  good e1 \<Longrightarrow> (\<forall>p'. R p' e1) \<Longrightarrow> 
  (\<forall>e. e \<in> sset es2 \<longrightarrow> good e \<and> (\<forall>p'. R p' e)) \<Longrightarrow> 
  (\<forall>e2 e2'. {e2,e2'} \<subseteq> sset es2 \<longrightarrow> touchedSuperT e2 = touchedSuperT e2') \<Longrightarrow> 
  R p (iApp e1 es2)"
shows "R p t"
unfolding good_I
using par st 
unfolding bsmall_def[symmetric] apply(elim Reneqv.BE_iinduct[where R = "\<lambda>p t. R p t"])
  subgoal unfolding good_I by simp
  subgoal for p B t apply(subst (asm) G_def) 
  unfolding good_I[symmetric] apply(elim disjE exE)
    subgoal using iVar by auto 
    subgoal using iLam by auto  
    subgoal using iApp by auto . . 

(* ... and with fixed parameters: *)
corollary BE_induct_good'[consumes 2, case_names iVar iLam iApp]: 
assumes par: "small A \<and> bsmall A"
and st: "good t"  
and iVar: "\<And>xs x. 
  super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow>
  R (iVar x)"
and iLam: "\<And>e xs. 
  dsset xs \<inter> A = {} \<Longrightarrow> 
  super xs \<Longrightarrow> good e \<Longrightarrow> R e \<Longrightarrow> 
  R (iLam xs e)" 
and iApp: "\<And>e1 es2. 
  good e1 \<Longrightarrow> R e1 \<Longrightarrow> 
  (\<forall>e. e \<in> sset es2 \<longrightarrow> good e \<and> R e) \<Longrightarrow> 
  (\<forall>e2 e2'. {e2,e2'} \<subseteq> sset es2 \<longrightarrow> touchedSuperT e2 = touchedSuperT e2') \<Longrightarrow> 
  R (iApp e1 es2)"
shows "R t"
apply(rule BE_induct_good[of "\<lambda>_::unit. A"]) using assms by auto


(* Also inferring equivariance from the general infrastructure: *)
corollary irrename_good:
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" "presSuper f"
and r: "good e" 
shows "good (irrename f e)"
using assms unfolding good_I using Reneqv.II_equiv[of e f]
unfolding Tmap_def ssbij_def wfBij_presSuper by auto


(* Other properties: *)


lemma touchedSuperT_itvsubst: "touchedSuperT (itvsubst f t) = \<Union> ((touchedSuperT o f) ` (FFVars t))"
unfolding touchedSuperT_def by (auto simp: touchedSuper_UN )

lemma good_FFVars_RSuper: "good e \<Longrightarrow> FFVars e \<subseteq> RSuper"
apply(induct rule: good.induct) unfolding RSuper_def 
  by auto (metis superOf_subOf)

lemma good_FFVars_super: "good e \<Longrightarrow> x \<in> FFVars e \<Longrightarrow> \<exists>xs. super xs \<and> x \<in> dsset xs"
apply(drule good_FFVars_RSuper) unfolding RSuper_def2 by auto

lemma UN_touchedSuperT_super_eq: 
assumes f: "\<And>xs x x'. super xs \<Longrightarrow> {x,x'} \<subseteq> dsset xs \<Longrightarrow> touchedSuperT (f x) = touchedSuperT (f x')"
and AA': "A \<subseteq> RSuper" "A' \<subseteq> RSuper" "touchedSuper A = touchedSuper A'"
shows "(\<Union>x\<in>A. touchedSuperT (f x)) = (\<Union>x'\<in>A'. touchedSuperT (f x'))"
proof safe
  fix y x assume x: "x \<in> A" and y: "y \<in> touchedSuperT (f x)"
  then obtain xs where xs: "super xs" "x \<in> dsset xs" using AA' unfolding RSuper_def2 by auto
  then obtain x' where x': "x' \<in> dsset xs" "x' \<in> A'" using AA' x xs unfolding touchedSuper_def by fastforce
  hence "touchedSuperT (f x) = touchedSuperT (f x')" using f xs x x' by blast
  thus "y \<in> (\<Union>x'\<in>A'. touchedSuperT (f x'))" using y x' by auto
next
  fix y x' assume x': "x' \<in> A'" and y: "y \<in> touchedSuperT (f x')"
  then obtain xs where xs: "super xs" "x' \<in> dsset xs" using AA' unfolding RSuper_def2 by auto
  then obtain x where x: "x \<in> dsset xs" "x \<in> A" using AA' x' xs unfolding touchedSuper_def by fastforce
  hence "touchedSuperT (f x) = touchedSuperT (f x')" using f xs x x' by blast
  thus "y \<in> (\<Union>x\<in>A. touchedSuperT (f x))" using y x by auto
qed
  


lemma good_itvsubst:
assumes r: "good e" and rr: 
    "\<And>xs x. super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> good (f x)"
    "\<And>xs x x'. super xs \<Longrightarrow> {x,x'} \<subseteq> dsset xs \<Longrightarrow> 
     touchedSuperT (f x) = touchedSuperT (f x')" 
and s: "|SSupp f| <o |UNIV::ivar set|"  
and f: "finite (touchedSuper (IImsupp f))"  
shows "good (itvsubst f e)"
proof-
  have ims: "|IImsupp f| <o |UNIV::ivar set|" 
  using s ILC.SSupp_IImsupp_bound by auto
  have par: "small (IImsupp f) \<and> bsmall (IImsupp f)"
  using ims f unfolding small_def   
  using var_stream_class.Un_bound bsmall_Un bsmall_def by blast
  show ?thesis using par r proof(induct rule: BE_induct_good')
    case (iVar xs x)
    then show ?case using s rr by auto
  next
    case (iLam e xs)
    show ?case using iLam apply(subst iterm.subst)
      subgoal using s by blast
      subgoal using s by auto 
      subgoal apply(rule good.iLam) by auto .
  next
    case (iApp e1 es2)
    then show ?case apply(subst iterm.subst)
      subgoal using s by auto
      subgoal apply(rule good.iApp)
        subgoal by auto
        subgoal by auto
        subgoal apply clarsimp subgoal for e2 e2' unfolding touchedSuperT_itvsubst apply clarsimp
        apply(rule UN_touchedSuperT_super_eq)
          subgoal using rr by auto
          subgoal unfolding RSuper_def2 using good_FFVars_super by auto  
          subgoal unfolding RSuper_def2 using good_FFVars_super by auto 
          subgoal unfolding touchedSuperT_def by blast . . . . 
  qed
qed


lemma good_sset_touchedSuper: 
"(\<And>e e'. {e,e'} \<subseteq> sset es \<Longrightarrow> good e \<and> touchedSuperT e =  touchedSuperT e') \<Longrightarrow> 
e \<in> sset es \<Longrightarrow> touchedSuper (\<Union> (FFVars ` (sset es))) = touchedSuper (FFVars e)"
unfolding touchedSuper_UN using touchedSuperT_def by blast

lemma touchedSuper_IImsupp_imkSubst: 
"super xs \<Longrightarrow> (\<And>e e'. {e,e'} \<subseteq> sset es \<Longrightarrow> good e \<and> touchedSuperT e =  touchedSuperT e') \<Longrightarrow> e \<in> sset es \<Longrightarrow> 
 touchedSuper (IImsupp (imkSubst xs es)) \<subseteq> 
 {xs} \<union> touchedSuper (FFVars e)"
using touchedSuper_IImsupp_imkSubst good_sset_touchedSuper by blast


lemma super_good_finite_touchedSuper_imkSubst: 
"super xs \<Longrightarrow> (\<And>e e'. {e,e'} \<subseteq> sset es \<Longrightarrow> good e \<and> touchedSuperT e =  touchedSuperT e') 
 \<Longrightarrow> finite (touchedSuper (IImsupp (imkSubst xs es)))"
by (metis Supervariables.touchedSuper_IImsupp_imkSubst bot.extremum finite.insertI 
finite_Un good_finite_touchedSuperT insert_subset rev_finite_subset snth_sset touchedSuperT_def good_sset_touchedSuper)
        
lemma good_imkSubst:
assumes r: "good e" and xs: "super xs" and rr: "\<And>e e'. {e,e'} \<subseteq> sset es \<Longrightarrow> good e \<and> touchedSuperT e =  touchedSuperT e'" 
shows "good (itvsubst (imkSubst xs es) e)"
apply(rule good_itvsubst[OF r])
  subgoal by (metis bot.extremum iVar imkSubst_def insert_subset rr snth_sset) 
  subgoal by (metis bot.extremum imkSubst_def insert_subset rr singleton_inject snth_sset touchedSuper_iVar xs)
  subgoal by simp
  subgoal using rr super_good_finite_touchedSuper_imkSubst xs by blast .

  

end