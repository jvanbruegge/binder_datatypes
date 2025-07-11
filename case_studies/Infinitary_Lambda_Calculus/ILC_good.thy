(* Here we instantiate the general enhanced rule induction to the renaming-equivalence 
relation from Mazza  *)
theory ILC_good    
  imports "Untyped_Lambda_Calculus.LC" BSmall ILC2 Curry_LFP
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

definition Tperm :: "(ivar \<Rightarrow> ivar) \<Rightarrow> T \<Rightarrow> T" where 
"Tperm f \<equiv> irrename f"

fun Tsupp :: "T \<Rightarrow> ivar set" where 
"Tsupp e = FFVars e"



interpretation CComponents where
Tperm = Tperm and Tsupp = Tsupp 
and Bperm = Bperm and Bsupp = Bsupp and bnd = bnd and bsmall = bsmall
apply standard unfolding isPerm_def Tperm_def  
using iterm.set_bd_UNIV
apply (auto simp: iterm.permute_id0 map_prod.comp
iterm.permute_comp0 infinite_UNIV bsmall_def intro!: ext small_Un split: option.splits)
apply (simp add: iterm.set_bd_UNIV small_def) 
   apply (simp add: comp_def dstream.map_comp)
  using dsset_card_ls small_def apply blast
apply (simp add: dstream_map_ident_strong)
unfolding bsmall_def touchedSuper_def  
using super_Un_ddset_triv  
by (smt (verit) finite_Un rev_finite_subset) 

lemma presBnd_presSuper: "presBnd = presSuper"
unfolding presBnd_def presSuper_def fun_eq_iff apply safe
  subgoal for \<sigma> xs apply(erule allE[of _ "Some xs"]) by auto 
  subgoal for \<sigma> xs apply(erule allE[of _ "Some xs"]) by auto 
  subgoal for \<sigma> xxs apply(cases xxs) by auto 
  subgoal for \<sigma> xxs apply(cases xxs) by auto .

definition G :: "B \<Rightarrow> (T \<Rightarrow> bool) \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>xxs R t.  
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

lemma G_mmono: "R \<le> R' \<Longrightarrow> G xxs R t \<Longrightarrow> G xxs R' t"
unfolding G_def by fastforce


(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma G_eequiv: 
"isPerm \<sigma> \<Longrightarrow> presBnd \<sigma> \<Longrightarrow> G xxs R t \<Longrightarrow> 
 G  (Bperm \<sigma> xxs) (\<lambda>t'. R (Tperm (inv \<sigma>) t')) (Tperm \<sigma> t)"
unfolding G_def apply(elim disj_forward)
  subgoal
  subgoal apply(elim exE) subgoal for xs x
  apply(rule exI[of _ "dsmap \<sigma> xs"]) 
  apply(rule exI[of _ "\<sigma> x"]) 
  unfolding isPerm_def small_def Tperm_def presBnd_def
  apply simp by (metis option.simps(5)) . .
  (* *)
  subgoal
  subgoal apply(elim exE) subgoal for xs e
  apply(rule exI[of _ "dsmap \<sigma> xs"]) 
  apply(rule exI[of _ "irrename \<sigma> e"])  
  unfolding isPerm_def small_def Tperm_def presBnd_def
  apply (simp add: iterm.permute_comp) by (metis option.simps(5)) . . 
  (* *)
  subgoal
  subgoal apply(elim exE) subgoal for e1 es2
  apply(rule exI[of _ "irrename \<sigma> e1"]) 
  apply(rule exI[of _ "smap (irrename \<sigma>) es2"]) 
  unfolding isPerm_def small_def Tperm_def presBnd_presSuper 
  apply (simp add: iterm.permute_comp image_def) 
  by (metis inv_simp1 iterm.permute_bij iterm.permute_inv_simp touchedSuperT_irrename) . . .

(* *)

lemma G_bnd: "G xxs R t \<Longrightarrow> bnd xxs"
unfolding G_def by auto 

lemma eextend_to_presBnd: 
assumes "bnd xxs" "small A" "bsmall A" "A' \<subseteq> A" "Bsupp xxs \<inter> A' = {}"
shows "\<exists>\<rho>. isPerm \<rho> \<and> presBnd \<rho> \<and> \<rho> ` Bsupp xxs \<inter> A = {} \<and> id_on A' \<rho>" 
proof(cases xxs)
  case None
  thus ?thesis apply(intro exI[of _ id]) unfolding isPerm_def by auto
next
  case (Some xs)
  hence 0: "super xs" "|A| <o |UNIV::ivar set|" "finite (touchedSuper A)" "A' \<subseteq> A"
  "dsset xs \<inter> A' = {}"
  using assms by (auto split: option.splits simp: small_def bsmall_def) 
  show ?thesis using extend_super[OF 0] apply safe
  subgoal for \<rho> apply(rule exI[of _ \<rho>]) 
  using Some by (auto split: option.splits simp: presBnd_presSuper isPerm_def) .
qed 


interpretation Reneqv : IInduct1 
where Tperm = Tperm and Tsupp = Tsupp and Bperm = Bperm and Bsupp = Bsupp 
and bnd = bnd and bsmall = bsmall and GG = G
apply standard
using G_mmono G_eequiv G_bnd eextend_to_presBnd by auto


(* *)

lemma good_I: "good t = Reneqv.II t" 
unfolding good_def Reneqv.II_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def ex_simps conj_disj_distribL ex_disj_distrib apply clarify
  subgoal for R tt apply(rule iffI)
    by auto .
  

lemma III_bsmall: "Reneqv.II t \<Longrightarrow> bsmall (Tsupp t)"
apply simp
  unfolding good_I[symmetric] 
  unfolding bsmall_def using good_finite_touchedSuperT touchedSuperT_def by auto 

lemma Tvars_dsset: "dsset xs \<inter> (Tsupp t - dsset xs) = {}" 
  "|Tsupp t - dsset xs| <o |UNIV::ivar set|"
  "Reneqv.II t \<Longrightarrow> finite (touchedSuper (Tsupp t - dsset ys))"
subgoal using Diff_disjoint .
subgoal using small_def card_of_minus_bound ssmall_Tsupp by blast
subgoal apply(subgoal_tac "bsmall (Tsupp t)")
  subgoal unfolding bsmall_def 
    by (meson Diff_subset rev_finite_subset touchedSuper_mono) 
  subgoal by (metis III_bsmall) . .

lemma G_rrefresh: 
"(\<forall>t. R t \<longrightarrow> Reneqv.II t) \<Longrightarrow> 
 (\<forall>\<sigma> t. isPerm \<sigma> \<and> presBnd \<sigma> \<and> R t \<longrightarrow> R (Tperm \<sigma> t)) \<Longrightarrow> 
 G xxs R t \<Longrightarrow> 
 \<exists>yys. Bsupp yys \<inter> Tsupp t = {} \<and> G yys R t"
apply(subgoal_tac "Reneqv.II t") defer
apply (metis Reneqv.GG_mmono2 Reneqv.II.simps predicate1I)
subgoal premises p using p apply-
apply(frule G_bnd)
  unfolding G_def Tperm_def ex_simps conj_disj_distribL ex_disj_distrib
  apply (elim disj_forward)
    apply simp
   apply force
  by simp .
 

(* FINALLY, INTERPRETING THE IInduct LOCALE: *)

interpretation Reneqv : IInduct
where Tperm = Tperm and Tsupp = Tsupp and 
Bperm = Bperm and Bsupp = Bsupp and bnd = bnd and bsmall = bsmall 
and GG = G
apply standard using III_bsmall G_rrefresh by auto

(* *)


(* FROM ABSTRACT BACK TO CONCRETE: *)
thm good.induct[no_vars] 

corollary strong_induct_good[consumes 2, case_names iVar iLam iApp]: 
assumes par: "\<And>p. small (Psupp p) \<and> bsmall (Psupp p)"
and st: "good t"  
and iVar: "\<And>xs x p. 
  super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow>
  R p (iVar x)"
and iLam: "\<And>e xs p. 
  dsset xs \<inter> Psupp p = {} \<Longrightarrow> 
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

corollary strong_induct_good'[consumes 1, case_names bsmall Bound iVar iLam iApp]: 
assumes st: "good t" 
and bsmall: "\<And>p. bsmall (Psupp p)"
and "\<And>p. |Psupp p| <o |UNIV::ivar set|"
and iVar: "\<And>xs x p. 
  super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow>
  R (iVar x) p"
and iLam: "\<And>e xs p. 
  dsset xs \<inter> Psupp p = {} \<Longrightarrow> 
  super xs \<Longrightarrow> good e \<Longrightarrow> (\<forall>p'. R e p') \<Longrightarrow> 
  R (iLam xs e) p" 
and iApp: "\<And>e1 es2 p. 
  good e1 \<Longrightarrow> (\<forall>p'. R e1 p') \<Longrightarrow>
  (\<And>e. e \<in> sset es2 \<Longrightarrow> \<forall>p'. R e p') \<Longrightarrow>
  (\<forall>e. e \<in> sset es2 \<longrightarrow> good e) \<Longrightarrow> 
  (\<forall>e2 e2'. {e2,e2'} \<subseteq> sset es2 \<longrightarrow> touchedSuperT e2 = touchedSuperT e2') \<Longrightarrow> 
  R (iApp e1 es2) p"
shows "\<forall>p. R t p"
using strong_induct_good[of Psupp t "\<lambda>p t. R t p"] assms unfolding small_def by auto

(* Also inferring equivariance from the general infrastructure: *)
corollary irrename_good:
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" "presSuper f"
and r: "good e" 
shows "good (irrename f e)"
using assms unfolding good_I using Reneqv.II_equiv[of e f]
unfolding Tperm_def isPerm_def presBnd_presSuper by auto


(* Other properties: *)


lemma touchedSuperT_itvsubst: "|ILC.SSupp f| <o |UNIV :: ivar set| \<Longrightarrow> touchedSuperT (itvsubst f t) = \<Union> ((touchedSuperT o f) ` (FFVars t))"
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
and s: "|ILC.SSupp f| <o |UNIV::ivar set|"  
and f: "finite (touchedSuper (ILC.IImsupp f))"  
shows "good (itvsubst f e)"
using r proof (binder_induction e avoiding: "ILC.IImsupp f" rule: strong_induct_good')
  case (iLam ea xs)
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
        subgoal apply clarsimp subgoal for e2 e2' unfolding touchedSuperT_itvsubst[OF s] apply clarsimp
        apply(rule UN_touchedSuperT_super_eq)
          subgoal using rr by auto
          subgoal using good_FFVars_RSuper by presburger
          subgoal using good_FFVars_RSuper by presburger
          subgoal unfolding touchedSuperT_def by blast . . . . 
qed (auto simp: bsmall_def ILC.SSupp_IImsupp_bound s f rr)

lemma good_sset_touchedSuper: 
"(\<And>e e'. {e,e'} \<subseteq> sset es \<Longrightarrow> good e \<and> touchedSuperT e =  touchedSuperT e') \<Longrightarrow> 
e \<in> sset es \<Longrightarrow> touchedSuper (\<Union> (FFVars ` (sset es))) = touchedSuper (FFVars e)"
unfolding touchedSuper_UN using touchedSuperT_def by blast

lemma touchedSuper_IImsupp_imkSubst: 
"super xs \<Longrightarrow> (\<And>e e'. {e,e'} \<subseteq> sset es \<Longrightarrow> good e \<and> touchedSuperT e =  touchedSuperT e') \<Longrightarrow> e \<in> sset es \<Longrightarrow> 
 touchedSuper (ILC.IImsupp (imkSubst xs es)) \<subseteq> 
 {xs} \<union> touchedSuper (FFVars e)"
using touchedSuper_IImsupp_imkSubst good_sset_touchedSuper by blast


lemma super_good_finite_touchedSuper_imkSubst: 
"super xs \<Longrightarrow> (\<And>e e'. {e,e'} \<subseteq> sset es \<Longrightarrow> good e \<and> touchedSuperT e =  touchedSuperT e') 
 \<Longrightarrow> finite (touchedSuper (ILC.IImsupp (imkSubst xs es)))"
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
