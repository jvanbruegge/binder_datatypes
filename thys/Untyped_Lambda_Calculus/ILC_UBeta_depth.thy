(* version of uniform (parallel) reduction that tracks the applicative depth 
(i.e., the number of application operators on top of) of the affected redex (\<Rightarrow>d from Mazza) *)
theory ILC_UBeta_depth
imports ILC_uniform
begin

(* head reduction: *)
definition hred :: "ivar iterm \<Rightarrow> ivar iterm \<Rightarrow> bool" where 
"hred e e' \<equiv> \<exists> xs e1 es2. e = iApp (iLam xs e1) es2 \<and> e' = itvsubst (imkSubst xs es2) e1"

lemma hred_irrename: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> hred e e' \<Longrightarrow> hred (irrename \<sigma> e) (irrename \<sigma> e')"
unfolding hred_def apply(elim exE) subgoal for xs e1 es2
  apply(rule exI[of _ "dsmap \<sigma> xs"])
  apply(rule exI[of _ "irrename \<sigma> e1"])  
  apply(rule exI[of _ "smap (irrename \<sigma>) es2"])   
  apply (simp add: iterm.rrename_comps) apply(subst irrename_itvsubst_comp) apply auto
  apply(subst imkSubst_smap_irrename_inv) unfolding ssbij_def apply auto 
  apply(subst irrename_eq_itvsubst_iVar'[of _ e1]) unfolding ssbij_def apply auto
  apply(subst itvsubst_comp) 
    subgoal by (metis SSupp_imkSubst imkSubst_smap_irrename_inv)
    subgoal by (smt (verit, best) SSupp_def VVr_eq_Var card_of_subset_bound mem_Collect_eq not_in_supp_alt o_apply subsetI) 
    subgoal apply(rule itvsubst_cong)
      subgoal using SSupp_irrename_bound by blast
      subgoal using card_SSupp_itvsubst_imkSubst_irrename_inv ssbij_def by auto
   subgoal for x apply simp apply(subst iterm.subst(1))
      subgoal using card_SSupp_imkSubst_irrename_inv[unfolded ssbij_def] by auto
      subgoal by simp . . . .

lemma hred_reneqv: 
assumes "reneqv e ee" "hred e e'" "hred ee ee'" 
shows "reneqv e' ee'"
using assms reneqv_head_reduction unfolding hred_def by auto 

lemma hred_reneqvS: 
assumes "reneqvS es ees" "stream_all2 hred es es'" and "stream_all2 hred ees ees'"
shows "reneqvS es' ees'"
using hred_reneqv assms unfolding reneqvS_def stream_all2_iff_snth sset_range  
by simp (smt (verit) image_iff)

lemma hred_uniform: 
assumes "hred e e'" and "uniform e"
shows "uniform e'"
using assms hred_reneqv unfolding uniform_def3 by blast

lemma hred_uniformS: 
assumes "stream_all2 hred es es'" and "uniformS es"
shows "uniformS es'"
using assms hred_reneqvS unfolding uniformS_def3 by blast




(* TO DOCUMENT in the paper: 
Mazza is very informal when defining \<Rightarrow> (the uniform step relation, def. 7). 
One way to make this rigorous was to define reduction of a countable number of 
(i.e., a stream of) terms in parallel, and to flatten from matrix to streams when we get to 
application. (Mazza fails to discuss this 'escalation" to matrices... )
*)
(* Mazza defines this relation to uniform terms. I only sufficient uniformity assumptions 
(avoiding redundant ones) *)
inductive ustepD :: "nat \<Rightarrow> itrm stream \<Rightarrow> itrm stream \<Rightarrow> bool" where
  Beta: "uniformS es \<Longrightarrow> stream_all2 hred es es' \<Longrightarrow> ustepD 0 es es'"
| iAppL: "uniformS (sflat ess) \<Longrightarrow> ustepD d es es' \<Longrightarrow> ustepD (Suc d) (smap2 iApp es ess) (smap2 iApp es' ess)"
| iAppR: "uniformS es \<Longrightarrow> ustepD d (sflat ess) (sflat ess') \<Longrightarrow> ustepD (Suc d) (smap2 iApp es ess) (smap2 iApp es ess')"
(* lambda's are not counted, as it is the *applicative* depth *)
| Xi: "super xs \<Longrightarrow> ustepD d es es' \<Longrightarrow> ustepD d (smap (iLam xs) es) (smap (iLam xs) es')"

thm ustepD_def

lemma ustepD_uniformS:
assumes "ustepD d es es'" 
shows "uniformS es \<and> uniformS es'"
using assms proof(induct rule: ustepD.induct)
  case Beta 
  then show ?case using hred_uniformS by simp
next
  case iAppL
  then show ?case unfolding uniformS_smap2_iApp_iff by auto
next
  case iAppR 
  then show ?case unfolding uniformS_smap2_iApp_iff by auto
next
  case Xi
  then show ?case using uniformS_smap2_iLam_iff by auto
qed

lemma hred_def2: 
assumes t: "uniform t"
shows 
"hred t tt \<longleftrightarrow> 
   (\<exists>xs e1 es2. super xs \<and> t = iApp (iLam xs e1) es2 \<and> tt = itvsubst (imkSubst xs es2) e1)"
unfolding hred_def by (metis iLam_switch_to_super t)

lemma hred_reneqv': 
assumes r: "reneqv e ee" "hred e e'"
shows "\<exists>ee'. hred ee ee' \<and> reneqv e' ee'"
proof-
  have u: "uniform e" using r unfolding uniform_def by auto
  show ?thesis using r
  unfolding hred_def2[OF u] 
  apply(auto dest!: reneqv_iApp_casesL reneqv_iLam_casesL) 
  by (metis hred_def r(1) reneqv_head_reduction)
qed

lemma hred_reneqvS': 
assumes r: "reneqvS es ees" "stream_all2 hred es es'"
shows "\<exists>ees'. stream_all2 hred ees ees' \<and> reneqvS es' ees'"
proof-
  have "\<forall>i. \<exists>ee'. hred (snth ees i) ee' \<and> reneqv (snth es' i) ee'"
  using assms unfolding stream_all2_iff_snth reneqvS_def sset_range image_def
  using hred_reneqv' by simp blast
  then obtain EE' where EE': "\<forall>i. hred (snth ees i) (EE' i) \<and> reneqv (snth es' i) (EE' i)"
  by metis
  show ?thesis apply(rule exI[of _ "smap EE' nats"])
  using EE' assms unfolding stream_all2_iff_snth reneqvS_def sset_range image_def 
  by simp (metis (no_types, lifting) hred_reneqv)
qed

(* *)

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* PREPARING THE INSTANTIATION: *)

lemma ustepD_finite_touchedSuperT: 
"ustepD d es1 es2 \<Longrightarrow> 
 finite (\<Union> (touchedSuperT ` (sset es1))) \<and> finite (\<Union> (touchedSuperT ` (sset es2)))"
using uniformS_finite_touchedSuperT ustepD_uniformS by blast


(* INSTANTIATING THE CComponents LOCALE: *)

type_synonym T = "nat \<times> itrm stream \<times> itrm stream"

definition Tmap :: "(ivar \<Rightarrow> ivar) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> map_prod id (map_prod (smap (irrename f)) (smap (irrename f)))"

fun Tfvars :: "T \<Rightarrow> ivar set" where 
"Tfvars (d,es1,es2) = \<Union> (FFVars ` (sset es1)) \<union> \<Union> (FFVars ` (sset es2))"


lemma card_sset_le[simp,intro!]: "|sset xs| <o |UNIV::ivar set|"
using countable_card_ivar countable_sset by blast

thm stream.map_cong0[no_vars]

interpretation CComponents where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars
and Bmap = Bmap and Bvars = Bvars and wfB = wfB and bsmall = bsmall
apply standard unfolding ssbij_def Tmap_def  
  using small_Un small_def iterm.card_of_FFVars_bounds
  apply (auto simp: dstream.map_comp dstream_map_ident_strong
 dstream.map_comp iterm.rrename_id0s map_prod.comp iterm.rrename_comp0s inf_A fun_eq_iff stream.map_comp
    intro!: 
var_sum_class.UN_bound var_sum_class.Un_bound 
stream.map_ident_strong iterm.rrename_cong_ids intro!: ext split: option.splits)
  apply auto 
 unfolding bsmall_def touchedSuper_def apply(frule super_dsset_singl) apply auto
  using super_Un_ddset_triv  
  by (smt (verit) finite_Un rev_finite_subset) 

(* 
lemma wfBij_presSuper: "wfBij = presSuper"
unfolding wfBij_def presSuper_def fun_eq_iff apply safe
  subgoal for \<sigma> xs apply(erule allE[of _ "Some xs"]) by auto 
  subgoal for \<sigma> xs apply(erule allE[of _ "Some xs"]) by auto 
  subgoal for \<sigma> xxs apply(cases xxs) by auto 
  subgoal for \<sigma> xxs apply(cases xxs) by auto .
*)

definition G :: "(T \<Rightarrow> bool) \<Rightarrow> B \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>R xxs t.  
         (\<exists>es es'. xxs = None \<and> fst t = 0 \<and> fst (snd t) = es \<and> snd (snd t) = es' \<and> 
                   uniformS es \<and> stream_all2 hred es es')
         \<or>
         (\<exists>d es es' ess. xxs = None \<and> fst t = Suc d \<and> fst (snd t) = smap2 iApp es ess \<and> snd (snd t) = smap2 iApp es' ess \<and> 
                       uniformS (sflat ess) \<and> R (d, es, es')) 
         \<or>
         (\<exists>es d ess ess'. xxs = None \<and> fst t = Suc d \<and> fst (snd t) = smap2 iApp es ess \<and> snd (snd t) = smap2 iApp es ess' \<and> 
                        uniformS es \<and> R (d, sflat ess, sflat ess'))
         \<or>
         (\<exists>xs d es es'. xxs = Some xs \<and> fst t = d \<and> fst (snd t) = smap (iLam xs) es \<and> snd (snd t) = smap (iLam xs) es' \<and> 
                      super xs \<and> R (d, es, es'))"


(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma G_mmono: "R \<le> R' \<Longrightarrow> G R xxs t \<Longrightarrow> G R' xxs t"
unfolding G_def by fastforce

declare iterm.rrename_id0s[simp]

lemma smap2_smap: "smap2 f (smap g xs) (smap h ys) = smap2 (\<lambda>x y. f (g x) (h y)) xs ys"
by (simp add: smap2_alt)

lemma uniformS_irrename: 
"bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
 uniformS es \<Longrightarrow> uniformS (smap (irrename \<sigma>) es)"
unfolding uniformS_def4 stream.set_map  
using irrename_reneqv by auto


lemma uniformS_sflat: "uniformS (sflat ess) \<longleftrightarrow> (\<forall>i j i' j'. 
  reneqv (snth2 ess (i,j)) (snth2 ess (i',j')))"
unfolding uniformS_def4 sset_sflat apply auto
apply (metis snth_sset) by (metis More_Stream.theN)

(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma G_eequiv: "ssbij \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> G R xxs t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Bmap \<sigma> xxs) (Tmap \<sigma> t)"
unfolding G_def apply(elim disjE)
  subgoal apply(rule disjI4_1)
  subgoal apply(elim exE) subgoal for es es'  
  apply(rule exI[of _ "smap (irrename \<sigma>) es"])  
  apply(rule exI[of _ "smap (irrename \<sigma>) es'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def wfBij_presSuper
  apply (simp add: iterm.rrename_comps uniformS_irrename) unfolding stream_all2_iff_snth
  using hred_irrename by auto . .
  (* *)
  subgoal apply(rule disjI4_2)
  subgoal apply(elim exE) subgoal for d es es' ess
  apply(rule exI[of _ d])
  apply(rule exI[of _ "smap (irrename \<sigma>) es"]) apply(rule exI[of _ "smap (irrename \<sigma>) es'"]) 
  apply(rule exI[of _ "smap (smap (irrename \<sigma>)) ess"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def wfBij_presSuper
  apply (simp add: iterm.rrename_comp0s stream.map_comp smap2_smap uniformS_irrename  
     uniformS_sflat irrename_reneqv) . . .
  (* *)
  subgoal apply(rule disjI4_3)
  subgoal apply(elim exE) subgoal for es d ess ess'
  apply(rule exI[of _ "smap (irrename \<sigma>) es"]) 
  apply(rule exI[of _ d])
  apply(rule exI[of _ "smap (smap (irrename \<sigma>)) ess"]) 
  apply(rule exI[of _ "smap (smap (irrename \<sigma>)) ess'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def  
  apply (simp add: iterm.rrename_comp0s stream.map_comp smap2_smap smap_sflat) 
  by (metis ILC_Renaming_Equivalence.wfBij_presSuper id_apply inv_o_simp1 iterm.rrename_bijs iterm.rrename_inv_simps smap_sflat stream.map_comp stream.map_id0 uniformS_irrename)
  . .  
  (* *)
  subgoal apply(rule disjI4_4)
  subgoal apply(elim exE) subgoal for xs d es es'
  apply(rule exI[of _ "dsmap \<sigma> xs"])
  apply(rule exI[of _ d])
  apply(rule exI[of _ "smap (irrename \<sigma>) es"]) apply(rule exI[of _ "smap (irrename \<sigma>) es'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def  
  apply (simp add: iterm.rrename_comp0s stream.map_comp smap2_smap)
    by (metis (no_types, lifting) comp_apply irrename_simps(3) presSuper_def stream.map_cong wfBij_presSuper) 
   . . . 


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


interpretation Ustep : IInduct1 
where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars and Bmap = Bmap and Bvars = Bvars 
and wfB = wfB and bsmall = bsmall and GG = G
apply standard
using G_mmono G_eequiv G_wfB eextend_to_wfBij by auto

(* *)
 
lemma ustepD_I: "ustepD d t1 t2 = Ustep.II (d,t1,t2)" 
unfolding ustepD_def Ustep.II_def lfp_curry3 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R d tt1 tt2 apply(rule iffI)
  subgoal apply(elim disjE exE conjE)
    \<^cancel>\<open>Beta: \<close>
    subgoal apply(rule exI[of _ None]) apply(rule disjI4_1) by auto
    \<^cancel>\<open>iAppL: \<close>
    subgoal apply(rule exI[of _ None]) apply(rule disjI4_2) by auto
    \<^cancel>\<open>iAppR: \<close>
    subgoal apply(rule exI[of _ None])  apply(rule disjI4_3) by auto
    \<^cancel>\<open>Xi: \<close>
    subgoal for xs es es' apply(rule exI[of _ "Some xs"]) apply(rule disjI4_4) by auto .
  subgoal apply(elim conjE disjE exE)
    \<^cancel>\<open>Beta: \<close>
    subgoal apply(rule disjI4_1) by auto
    \<^cancel>\<open>iAppL: \<close>
    subgoal apply(rule disjI4_2) by auto
    \<^cancel>\<open>iAppR: \<close>
    subgoal apply(rule disjI4_3) by auto
    \<^cancel>\<open>Xi: \<close>
    subgoal apply(rule disjI4_4) by auto . . .

lemma III_bsmall: "Ustep.II t \<Longrightarrow> bsmall (Tfvars t)"
apply(cases t)
  subgoal for e1 e2 apply simp
  unfolding ustepD_I[symmetric]  
  apply(rule bsmall_Un) unfolding bsmall_def touchedSuperT_def 
  using touchedSuperT_def 
  touchedSuper_UN ustepD_finite_touchedSuperT by auto .


lemma Tvars_dsset: "dsset xs \<inter> (Tfvars t - dsset xs) = {}" 
  "|Tfvars t - dsset xs| <o |UNIV::ivar set|"
  "Ustep.II t \<Longrightarrow> finite (touchedSuper (Tfvars t - dsset ys))"
subgoal using Diff_disjoint .
subgoal using ILC2.small_def card_of_minus_bound ssmall_Tfvars by blast
subgoal apply(subgoal_tac "bsmall (Tfvars t)")
  subgoal unfolding bsmall_def 
    by (meson Diff_subset rev_finite_subset touchedSuper_mono) 
  subgoal by (metis III_bsmall) . .

lemma G_rrefresh: 
"(\<forall>t. R t \<longrightarrow> Ustep.II t) \<Longrightarrow>  
 (\<forall>\<sigma> t. ssbij \<sigma> \<and> wfBij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> 
 G R xxs t \<Longrightarrow> 
 \<exists>yys. Bvars yys \<inter> Tfvars t = {} \<and> G R yys t"
apply(subgoal_tac "Ustep.II t") defer
apply (metis Ustep.GG_mmono2 Ustep.II.simps predicate1I)
subgoal premises p using p apply-
apply(frule G_wfB)
unfolding G_def Tmap_def apply safe 
  subgoal for es es'
  apply(rule exI[of _ None])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto .
  (* *)
  subgoal for d  es es' ess
  apply(rule exI[of _ None])  
  apply(intro conjI)
    subgoal by simp 
    subgoal apply(rule disjI4_2) 
    apply(rule exI[of _ "d"]) 
    apply(rule exI[of _ "es"]) 
    apply(rule exI[of _ "es'"])
    apply(rule exI[of _ "ess"]) 
    apply(cases t) apply simp . .
  (* *)
  subgoal for es d ess ess' 
  apply(rule exI[of _ None])  
  apply(intro conjI)
    subgoal by simp 
    subgoal apply(rule disjI4_3) 
    apply(rule exI[of _ "es"]) 
    apply(rule exI[of _ d])
    apply(rule exI[of _ "ess"])
    apply(rule exI[of _ "ess'"]) 
    apply(cases t) apply auto . .
  (* *) 
  subgoal for xs d es es'
  apply(frule refresh_super[OF Tvars_dsset(1,2) Tvars_dsset(3)[OF p(4)]])
  apply safe
  subgoal for f
  apply(rule exI[of _ "Some (dsmap f xs)"])  
  apply(intro conjI)  
    subgoal unfolding id_on_def presSuper_def  
    by (cases t, auto) 

    subgoal apply(rule disjI4_4) 
    apply(rule exI[of _ "dsmap f xs"]) 
    apply(rule exI[of _ "fst t"]) 
    apply(rule exI[of _ "smap (irrename f) es"]) 
    apply(rule exI[of _ "smap (irrename f) es'"]) 
    apply(cases t) unfolding presSuper_def apply simp apply(intro conjI)
      subgoal unfolding stream.map_comp apply(rule stream.map_cong0) 
        apply(subst iLam_irrename[of "f"]) unfolding id_on_def by auto
      subgoal unfolding stream.map_comp apply(rule stream.map_cong0) 
        apply(subst iLam_irrename[of "f"]) unfolding id_on_def by auto 
      subgoal unfolding ssbij_def wfBij_presSuper presSuper_def by auto 
  . . . . . 
      


(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation Ustep: IInduct where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars and 
Bmap = Bmap and Bvars = Bvars and wfB = wfB and bsmall = bsmall 
and GG = G
apply standard using III_bsmall G_rrefresh by auto

(* *)



(* FROM ABSTRACT BACK TO CONCRETE: *)
thm ustepD.induct[no_vars] 

corollary BE_induct_ustepD[consumes 2, case_names Beta iAppL iAppR Xi]: 
assumes par: "\<And>p. small (Pfvars p) \<and> bsmall (Pfvars p)"
and st: "ustepD d t1 t2"  
and Beta: "\<And>d es es' p. 
  stream_all2 hred es es' \<Longrightarrow> 
  R p d es es'"
and iAppL: "\<And>d es es' ess p. 
  ustepD d es es' \<Longrightarrow> (\<forall>p'. R p' d es es') \<Longrightarrow> 
  R p (Suc d) (smap2 iApp es ess) (smap2 iApp es' ess)"
and iAppR: "\<And>d ess ess' es p. 
  ustepD d (sflat ess) (sflat ess') \<Longrightarrow> (\<forall>p'. R p' d (sflat ess) (sflat ess')) \<Longrightarrow> 
  R p (Suc d) (smap2 iApp es ess) (smap2 iApp es ess')"
and Xi: "\<And>d es es' xs p. 
  dsset xs \<inter> Pfvars p = {} \<Longrightarrow> 
  ustepD d es es' \<Longrightarrow> (\<forall>p'. R p' d es es') \<Longrightarrow> 
  R p d (smap (iLam xs) es) (smap (iLam xs) es')" 
shows "R p d t1 t2"
unfolding ustepD_I
apply(subgoal_tac "case (d,t1,t2) of (d, t1, t2) \<Rightarrow> R p d t1 t2")
  subgoal by simp
  subgoal using par st apply(elim Ustep.BE_iinduct[where R = "\<lambda>p (d,t1,t2). R p d t1 t2"])
    subgoal unfolding ustepD_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding ustepD_I[symmetric] apply(elim disjE exE)
      subgoal using Beta by auto
      subgoal using iAppL by auto  
      subgoal using iAppR by auto  
      subgoal using Xi by auto . . .

(* ... and with fixed parameters: *)
corollary BE_induct_ustepD'[consumes 2, case_names Beta iAppL iAppR Xi]: 
assumes par: "small A \<and> bsmall A"
and st: "ustepD d t1 t2"  
and Beta: "\<And>d es es'. stream_all2 hred es es' \<Longrightarrow> R d es es'"
and iAppL: "\<And>d es es' ess. 
  ustepD d es es' \<Longrightarrow> R d es es' \<Longrightarrow> 
  R (Suc d) (smap2 iApp es ess) (smap2 iApp es' ess)"
and iAppR: "\<And>d ess ess' es. 
  ustepD d (sflat ess) (sflat ess') \<Longrightarrow> R d (sflat ess) (sflat ess') \<Longrightarrow> 
  R (Suc d) (smap2 iApp es ess) (smap2 iApp es ess')"
and Xi: "\<And>d es es' xs. 
  dsset xs \<inter> A = {} \<Longrightarrow> 
  ustepD d es es' \<Longrightarrow> R d es es' \<Longrightarrow> 
  R d (smap (iLam xs) es) (smap (iLam xs) es')" 
shows "R d t1 t2"
apply(rule BE_induct_ustepD[of "\<lambda>_::unit. A"]) using assms by auto

(* Also inferring equivariance from the general infrastructure: *)
corollary irrename_ustepD:
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" "presSuper f"
and r: "ustepD d es es'" 
shows "ustepD d (smap (irrename f) es) (smap (irrename f) es')"
using assms unfolding ustepD_I using Ustep.II_equiv[of "(d,es,es')" f]
unfolding Tmap_def ssbij_def wfBij_presSuper by auto


(* Other properties: *)

(* The following captures the freshness assumption for beta (coming from the "parameter" 
predicate hred as part of ustepD. So fresh induction will use both 
the avoidance from the ustepD Xi rule and this one (for hred).  Contrast this with 
beta, which does not "hide" any freshness assumptions inside parameter predicates, 
so its rule induction covers both beta and Xi. *)
lemma hred_eq_avoid: 
assumes A: "small A" and r: "hred e e'"
shows "\<exists> xs e1 es2. dsset xs \<inter> \<Union> (FFVars ` (sset es2)) = {} \<and> dsset xs \<inter> A = {} \<and>
            e = iApp (iLam xs e1) es2 \<and> e' = itvsubst (imkSubst xs es2) e1"
proof-
  obtain xs e1 es2 where e: "e = iApp (iLam xs e1) es2" and e': "e' = itvsubst (imkSubst xs es2) e1" 
  using r unfolding hred_def by auto
  define B where B: "B = A \<union> \<Union> (FFVars ` (sset es2))"
  have "small B" unfolding B by (metis A Tfvars.simps Un_absorb small_Un ssmall_Tfvars)
  then obtain xs' e1' where 0: "iLam xs e1 = iLam xs' e1'" "dsset xs' \<inter> B = {}"
  using iLam_avoid by (meson small_def)

  obtain f where f: "bij f" "|supp f| <o |UNIV::ivar set|" "id_on (FFVars (iLam xs e1)) f" 
  and 1: "xs' = dsmap f xs" "e1' = irrename f e1" using 0(1) unfolding iLam_inject by auto
  show ?thesis apply(intro exI[of _ xs'] exI[of _ e1'] exI[of _ es2]) apply(intro conjI)
    subgoal using 0(2) unfolding B by auto
    subgoal using 0(2) unfolding B by auto
    subgoal unfolding e 0(1) ..
    subgoal unfolding e' 0(1) 1 apply(subst irrename_eq_itvsubst_iVar')
      subgoal by fact  subgoal by fact
      subgoal apply(subst itvsubst_comp)
        subgoal by simp
        subgoal by (simp add: f(2))   
        apply(subst itvsubst_cong) apply auto 
        apply (simp add: SSupp_itvsubst_bound f(2))
        by (metis (full_types) "0"(1) "1"(1) Diff_iff f(1) f(3) id_on_def imkSubst_idle 
          imkSubst_smap iterm.set(3)) . . 
qed

lemma hred_FFVars: "hred e e' \<Longrightarrow> FFVars e' \<subseteq> FFVars e"
unfolding hred_def by auto (metis imkSubst_def iterm.set(1) singletonD snth_sset)+

lemma ustepD_FFVars: "ustepD es es' \<Longrightarrow> (\<forall>i. FFVars (snth es' i) \<subseteq> FFVars (snth es i))"
apply(induct rule: ustepD.induct) 
using hred_FFVars apply (auto simp: sset_smap2 sset_range snth_sflat stream_all2_iff_snth )
by (metis in_mono nat2_nat1 snth2.simps)
          
 

end