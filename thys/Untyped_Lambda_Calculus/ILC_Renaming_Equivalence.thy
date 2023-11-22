(* Here we instantiate the general enhanced rule induction to the renaming-equivalence 
relation from Mazza  *)
theory ILC_Renaming_Equivalence
imports LC2 ILC2 "../Instantiation_Infrastructure/Curry_LFP" 
Supervariables
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)
inductive reneqv where
 iVar: "super xs \<Longrightarrow> {x,x'} \<subseteq> dsset xs \<Longrightarrow> reneqv (iVar x) (iVar x')"
|iLam: "super xs \<Longrightarrow> reneqv e e' \<Longrightarrow> reneqv (iLam xs e) (iLam xs e')"
|iApp: 
"reneqv e1 e1' \<Longrightarrow>
 (\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<longrightarrow> reneqv e e') 
 \<Longrightarrow>
 reneqv (iApp e1 es2) (iApp e1' es2')"

thm reneqv_def

(* INSTANTIATING THE CComponents LOCALE: *)

type_synonym T = "itrm \<times> itrm"

definition Tmap :: "(ivar \<Rightarrow> ivar) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> map_prod (rrename f) (rrename f)"

fun Tfvars :: "T \<Rightarrow> ivar set" where 
"Tfvars (e1,e2) = FFVars e1 \<union> FFVars e2"

type_synonym B = "ivar dstream option"

fun Bmap :: "(ivar \<Rightarrow> ivar) \<Rightarrow> B \<Rightarrow> B" where 
"Bmap f xxs = (case xxs of None \<Rightarrow> None
                          |Some xs \<Rightarrow> Some (dsmap f xs))"

fun Bvars :: "B \<Rightarrow> ivar set" where 
"Bvars xxs = (case xxs of None \<Rightarrow> {}
                         |Some xs \<Rightarrow> dsset xs)"

fun wfB :: "B \<Rightarrow> bool" where 
"wfB xxs = (case xxs of None \<Rightarrow> True
                       |Some xs \<Rightarrow> super xs)"

definition bsmall :: "ivar set \<Rightarrow> bool" where 
"bsmall X \<equiv> finite {xs . super xs \<and> X \<inter> dsset xs \<noteq> {}}"

lemma super_dsset_singl: 
 "super ys \<Longrightarrow> {xs . super xs \<and> dsset ys \<inter> dsset xs \<noteq> {}} = {ys}"
apply safe 
apply (meson Int_emptyD super_disj)
by (simp add: dsset_range)

lemma super_Un_ddset_triv: "{xs. super xs \<and> (A \<union> B) \<inter> dsset xs \<noteq> {}} \<subseteq>  
   {xs. super xs \<and> A \<inter> dsset xs \<noteq> {}} \<union> 
   {xs. super xs \<and> B \<inter> dsset xs \<noteq> {}}"
by auto

interpretation CComponents where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars and Bmap = Bmap and Bvars = Bvars 
and wfB = wfB and bsmall = bsmall
apply standard unfolding ssbij_def Tmap_def  
using small_Un small_def iterm.card_of_FFVars_bounds
apply (auto simp: iterm.rrename_id0s map_prod.comp 
iterm.rrename_comp0s inf_A bsmall_def intro!: ext split: option.splits)
apply (simp add: iterm.set_bd_UNIV) 
apply (simp add: comp_def dstream.map_comp)
apply (simp add: dstream_map_ident_strong)
unfolding bsmall_def apply(frule super_dsset_singl) apply auto
using super_Un_ddset_triv  
by (smt (verit) finite_Un rev_finite_subset) 

definition G :: "(T \<Rightarrow> bool) \<Rightarrow> B \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>R xxs t.  
         (\<exists>xs x x'. xxs = None \<and> fst t = iVar x \<and> snd t = iVar x' \<and> 
                    super xs \<and> {x,x'} \<subseteq> dsset xs) 
         \<or>
         (\<exists>xs e e'. xxs = Some xs \<and> fst t = iLam xs e \<and> snd t = iLam xs e' \<and> 
                    super xs \<and> R (e,e'))
         \<or> 
         (\<exists>e1 e1' es2 es2'. xxs = None \<and> fst t = iApp e1 es2 \<and> snd t = iApp e1' es2' \<and> 
                            R (e1,e1') \<and> (\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<longrightarrow> R (e,e')))"
 

(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma G_mmono: "R \<le> R' \<Longrightarrow> G R xxs t \<Longrightarrow> G R' xxs t"
unfolding G_def by fastforce


(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma G_eequiv: 
"ssbij \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> G R xxs t \<Longrightarrow> 
 G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Bmap \<sigma> xxs) (Tmap \<sigma> t)"
unfolding G_def apply(elim disjE)
  subgoal apply(rule disjI3_1)
  subgoal apply(elim exE) subgoal for xs x x'
  apply(rule exI[of _ "dsmap \<sigma> xs"]) 
  apply(rule exI[of _ "\<sigma> x"]) apply(rule exI[of _ "\<sigma> x'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def wfBij_def
  apply simp by (metis option.simps(5)) . .
  (* *)
  subgoal apply(rule disjI3_2)
  subgoal apply(elim exE) subgoal for xs e e'
  apply(rule exI[of _ "dsmap \<sigma> xs"]) 
  apply(rule exI[of _ "rrename \<sigma> e"]) 
  apply(rule exI[of _ "rrename \<sigma> e'"])  
  apply(cases t) unfolding ssbij_def small_def Tmap_def wfBij_def
  apply (simp add: iterm.rrename_comps) by (metis option.simps(5)) . . 
  (* *)
  subgoal apply(rule disjI3_3)
  subgoal apply(elim exE) subgoal for e1 e1' es2 es2'
  apply(rule exI[of _ "rrename \<sigma> e1"]) apply(rule exI[of _ "rrename \<sigma> e1'"]) 
  apply(rule exI[of _ "smap (rrename \<sigma>) es2"]) apply(rule exI[of _ "smap (rrename \<sigma>) es2'"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  apply (simp add: iterm.rrename_comps) 
  by (metis image_in_bij_eq iterm.rrename_bijs iterm.rrename_inv_simps) . . .



(* *)

lemma G_wfB: "G R B t \<Longrightarrow> wfB B"
unfolding G_def by auto 


lemma extend_super: 
assumes "super xs" "|A| <o |UNIV::ivar set|" 
 "finite {xs. super xs \<and> A \<inter> dsset xs \<noteq> {}}" "A' \<subseteq> A" "dsset xs \<inter> A' = {}"
shows "\<exists>\<rho>. bij (\<rho>::ivar\<Rightarrow>ivar) \<and> |supp \<rho>| <o |UNIV::ivar set| \<and> (\<forall>xs. super xs \<longleftrightarrow> super (dsmap \<rho> xs)) \<and> \<rho> ` (dsset xs) \<inter> A = {} \<and> id_on A' \<rho>"
sorry

lemma eextend_to_wfBij: 
assumes "wfB xxs" "small A" "bsmall A" "A' \<subseteq> A" "Bvars xxs \<inter> A' = {}"
shows "\<exists>\<rho>. ssbij \<rho> \<and> wfBij \<rho> \<and> \<rho> ` Bvars xxs \<inter> A = {} \<and> id_on A' \<rho>" 
proof(cases xxs)
  case None
  thus ?thesis apply(intro exI[of _ id]) unfolding ssbij_def by auto
next
  case (Some xs)
  hence 0: "super xs" "|A| <o |UNIV::ivar set|" "finite {xs. super xs \<and> A \<inter> dsset xs \<noteq> {}}" "A' \<subseteq> A"
  "dsset xs \<inter> A' = {}"
  using assms by (auto split: option.splits simp: small_def bsmall_def) 
  show ?thesis using extend_super[OF 0] apply safe
  subgoal for \<rho> apply(rule exI[of _ \<rho>]) 
  using Some by (auto split: option.splits simp: wfBij_def ssbij_def) .
qed 


interpretation Reneqv : IInduct1 
where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars and Bmap = Bmap and Bvars = Bvars 
and wfB = wfB and bsmall = bsmall and GG = G
apply standard
using G_mmono G_eequiv G_wfB eextend_to_wfBij by auto


(* *)

lemma reneqv_I: "reneqv t1 t2 = Reneqv.II (t1,t2)" 
unfolding reneqv_def Reneqv.II_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R tt1 tt2 apply(rule iffI)
  subgoal apply(elim disjE exE conjE)
    \<^cancel>\<open>iVar: \<close>
    subgoal for xs x x' apply(rule exI[of _ None]) apply(rule disjI3_1) by auto
    \<^cancel>\<open>iLam: \<close> 
    subgoal for xs e e' apply(rule exI[of _ "Some xs"]) apply(rule disjI3_2) by auto 
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
  
lemma reneqv_FFvars_super: 
"reneqv e1 e2 \<Longrightarrow> 
  {xs. super xs \<and> FFVars e1 \<inter> dsset xs \<noteq> {}} = {xs. super xs \<and> FFVars e2 \<inter> dsset xs \<noteq> {}} 
  \<and>
  finite {xs. super xs \<and> FFVars e1 \<inter> dsset xs \<noteq> {}} \<and> 
  finite {xs. super xs \<and> FFVars e2 \<inter> dsset xs \<noteq> {}}"
sorry

lemma III_bsmall: "Reneqv.II t \<Longrightarrow> bsmall (Tfvars t)"
apply(cases t)
  subgoal for e1 e2 apply simp
  unfolding reneqv_I[symmetric] apply(drule reneqv_FFvars_super)
  unfolding bsmall_def[symmetric] 
  using bsmall_Un by auto .



thm refresh
lemma refresh_super: 
assumes V: " dsset xs \<inter> V = {}" "|V| <o |UNIV::ivar set|" 
  "finite {xs. super xs \<and> V \<inter> dsset xs \<noteq> {}}"
and xs: "super xs"  
shows "\<exists>f. bij (f::ivar\<Rightarrow>ivar) \<and> |supp f| <o |UNIV::ivar set| \<and> 
               \<comment> \<open> dsset xs' \<inter> dsset xs = {} \<and>  \<close>dsset (dsmap f xs) \<inter> V = {} \<and>
           id_on V f \<and> (\<forall>ys. super ys \<longleftrightarrow> super (dsmap f ys))"
using extend_super[OF xs V(2) V(3) _ V(1), simplified]
apply safe subgoal for \<rho> apply(intro exI[of _ \<rho>]) 
unfolding id_on_def by auto .


lemma Tvars_dsset: "dsset xs \<inter> (Tfvars t - dsset xs) = {}" 
  "|Tfvars t - dsset xs| <o |UNIV::ivar set|"
using ILC2.small_def card_of_minus_bound ssmall_Tfvars by blast+

lemma Tvars_dsset_finite: "Reneqv.II t \<Longrightarrow> finite {xs. super xs \<and> (Tfvars t - dsset ys) \<inter> dsset (xs::ivar dstream) \<noteq> {}}"
apply(subgoal_tac "bsmall (Tfvars t)")
  subgoal unfolding bsmall_def 
    by (smt (verit) Collect_mono Diff_Int_distrib2 empty_Diff rev_finite_subset)
  subgoal by (metis III_bsmall) . 

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
  subgoal for xs x x' 
  apply(rule exI[of _ None])  
  apply(intro conjI)
    subgoal by simp 
    subgoal apply(rule disjI3_1) 
    apply(rule exI[of _ xs]) 
    apply(rule exI[of _ x])
    apply(rule exI[of _ x']) 
    apply(cases t) apply simp . .
  (* *)
  subgoal for xs e e' 
  apply(frule refresh_super[OF Tvars_dsset Tvars_dsset_finite[OF p(4)]])
  apply safe
  subgoal for f
  apply(rule exI[of _ "Some (dsmap f xs)"])  
  apply(intro conjI) 
    subgoal unfolding id_on_def apply auto  
      by (smt (verit, ccfv_SIG) Diff_Int_distrib Diff_disjoint Diff_empty Int_emptyD Tfvars.simps Un_iff bij_betw_apply bij_imp_bij_betw dstream.set_map iterm.set(3) prod.collapse super_disj)
    subgoal apply(rule disjI3_2)
    apply(rule exI[of _ "dsmap f xs"]) 
    apply(rule exI[of _ "rrename f e"]) 
    apply(rule exI[of _ "rrename f e'"]) 
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst iLam_rrename[of "f"]) unfolding id_on_def by auto
      subgoal apply(subst rrename_eq_itvsubst_iVar)
        subgoal unfolding ssbij_def by auto
        subgoal unfolding ssbij_def by auto
        subgoal by (smt (verit, best) Diff_iff Un_iff iLam_rrename id_on_def 
           rrename_eq_itvsubst_iVar) . 
        subgoal unfolding id_on_def ssbij_def wfBij_def by (auto split: option.splits) . . .
  (* *)
  subgoal for e1 e1' es2 es2'
  apply(rule exI[of _ None])  
  apply(intro conjI)
    subgoal by simp 
    subgoal apply(rule disjI3_3) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e1'"])
    apply(rule exI[of _ "es2"]) 
    apply(rule exI[of _ "es2'"]) 
    apply(cases t) by simp . . .
 

(* FINALLY, INTERPRETING THE IInduct LOCALE: *)

interpretation Reneqv : IInduct
where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars and Bmap = Bmap and Bvars = Bvars 
and wfB = wfB and bsmall = bsmall and GG = G
apply standard using III_bsmall G_rrefresh by auto

(* *)


(* FROM ABSTRACT BACK TO CONCRETE: *)
thm reneqv.induct[no_vars] 

thm bsmall_def[of "Pfvars p"]

corollary BE_induct_reneqv: 
assumes par: "\<And>p. small (Pfvars p) \<and> finite {xs. super xs \<and> Pfvars p \<inter> dsset xs \<noteq> {}}"
and st: "reneqv t1 t2"  
and iVar: "\<And>xs x x' p. 
  super xs \<Longrightarrow> {x,x'} \<subseteq> dsset xs \<Longrightarrow>
  R p (iVar x) (iVar x')"
and iLam: "\<And>e e' xs p. 
  dsset xs \<inter> Pfvars p = {} \<Longrightarrow> 
  reneqv e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> 
  R p (iLam xs e) (iLam xs e')" 
and iApp: "\<And>e1 e1' es2 es2' p. 
  reneqv e1 e1' \<Longrightarrow> (\<forall>p'. R p' e1 e1') \<Longrightarrow> 
  (\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<longrightarrow> reneqv e e' \<and> (\<forall>p'. R p' e e')) \<Longrightarrow> 
  R p (iApp e1 es2) (iApp e1' es2')"
shows "R p t1 t2"
unfolding reneqv_I
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by simp
  subgoal using par st 
  unfolding bsmall_def[symmetric] apply(elim Reneqv.BE_iinduct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
    subgoal unfolding reneqv_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding reneqv_I[symmetric] apply(elim disjE exE)
      subgoal using iVar by auto 
      subgoal using iLam by auto  
      subgoal using iApp by auto . . .

end