(* uniform (parallel) reduction (\<Rightarrow> from Mazza) *)
theory ILC_UBeta
imports ILC2 "../Instantiation_Infrastructure/Curry_LFP" 
begin


datatype ctxt = Hole | ApL ctxt "itrm stream" | ApR itrm ctxt | Lm "ivar dstream" ctxt


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

(* *)

definition nat2 :: "nat \<Rightarrow> nat \<times> nat" where 
"nat2 \<equiv> SOME f. bij f"

lemma bij_nat2: "bij nat2" 
by (metis bij_prod_decode nat2_def someI_ex)

fun snth2 where "snth2 xss (i,j) = snth (snth xss i) j"

definition sflat :: "'a stream stream \<Rightarrow> 'a stream" where 
"sflat xss \<equiv> smap (\<lambda>i. snth2 xss (nat2 i)) nats"

lemma snth_sflat: "snth (sflat xss) i = snth2 xss (nat2 i)"
by (simp add: sflat_def)

lemma smap_sflat: "smap f (sflat xss) = sflat (smap (smap f) xss)"
unfolding sflat_def 
unfolding stream.map_comp apply(rule stream.map_cong0) 
subgoal for z by (cases "nat2 z", auto) . 

(* *)

inductive ustep :: "itrm stream \<Rightarrow> itrm stream \<Rightarrow> bool" where
  Beta: "stream_all2 hred es es' \<Longrightarrow> ustep es es'"
| iAppL: "ustep es es' \<Longrightarrow> ustep (smap2 iApp es ess) (smap2 iApp es' ess)"
| iAppR: "ustep (sflat ess) (sflat ess') \<Longrightarrow> ustep (smap2 iApp es ess) (smap2 iApp es ess')"
| Xi: "ustep es es' \<Longrightarrow> ustep (smap (iLam xs) es) (smap (iLam xs) es')"

thm ustep_def


(* INSTANTIATING THE Components LOCALE: *)

type_synonym T = "itrm stream \<times> itrm stream"

definition Tmap :: "(ivar \<Rightarrow> ivar) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> map_prod (smap (irrename f)) (smap (irrename f))"

fun Tfvars :: "T \<Rightarrow> ivar set" where 
"Tfvars (es1,es2) = \<Union> (FFVars ` (sset es1)) \<union> \<Union> (FFVars ` (sset es2))"


lemma card_sset_le[simp,intro!]: "|sset xs| <o |UNIV::ivar set|"
using countable_card_ivar countable_sset by blast

thm stream.map_cong0[no_vars]




interpretation Components where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars
apply standard unfolding ssbij_def Tmap_def  
  using small_Un small_def iterm.card_of_FFVars_bounds
  apply (auto simp: iterm.rrename_id0s map_prod.comp iterm.rrename_comp0s inf_A fun_eq_iff stream.map_comp
    intro!: var_sum_class.UN_bound var_sum_class.Un_bound stream.map_ident_strong iterm.rrename_cong_ids)
  by auto 

definition G :: "(T \<Rightarrow> bool) \<Rightarrow> ivar set \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>R B t.  
         (\<exists>es es'. B = {} \<and> fst t = es \<and> snd t = es' \<and> 
                      stream_all2 hred es es')
         \<or>
         (\<exists>es es' ess. B = {} \<and> fst t = smap2 iApp es ess \<and> snd t = smap2 iApp es' ess \<and> 
                       R (es,es')) 
         \<or>
         (\<exists>es ess ess'. B = {} \<and> fst t = smap2 iApp es ess \<and> snd t = smap2 iApp es ess' \<and> 
                        R (sflat ess,sflat ess'))
         \<or>
         (\<exists>xs es es'. B = dsset xs \<and> fst t = smap (iLam xs) es \<and> snd t = smap (iLam xs) es' \<and> 
                       R (es,es'))"


(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma G_mono: "R \<le> R' \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> G R' B t"
unfolding G_def by fastforce

lemma stream_all2_iff_snth: "stream_all2 P xs ys \<longleftrightarrow> (\<forall>i. P (snth xs i) (snth ys i))"
unfolding stream_all2_def BNF_Def.Grp_def apply auto 
  using in_mono apply fastforce unfolding OO_def apply auto 
  apply(rule exI[of _ "szip xs ys"]) apply auto 
  apply (simp add: stream_eq_nth)  
  apply (metis fst_conv prod.sel(2) snth_szip theN)
  apply (simp add: stream_eq_nth)  
  apply (metis fst_conv prod.sel(2) snth_szip theN) .

declare iterm.rrename_id0s[simp]

lemma smap2_smap: "smap2 f (smap g xs) (smap h ys) = smap2 (\<lambda>x y. f (g x) (h y)) xs ys"
by (simp add: smap2_alt)


(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma G_equiv: "ssbij \<sigma> \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (image \<sigma> B) (Tmap \<sigma> t)"
unfolding G_def apply(elim disjE)
  subgoal apply(rule disjI4_1)
  subgoal apply(elim exE) subgoal for es es'  
  apply(rule exI[of _ "smap (irrename \<sigma>) es"])  
  apply(rule exI[of _ "smap (irrename \<sigma>) es'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  apply (simp add: iterm.rrename_comps) unfolding stream_all2_iff_snth
  using hred_irrename by auto . .
  (* *)
  subgoal apply(rule disjI4_2)
  subgoal apply(elim exE) subgoal for es es' ess
  apply(rule exI[of _ "smap (irrename \<sigma>) es"]) apply(rule exI[of _ "smap (irrename \<sigma>) es'"]) 
  apply(rule exI[of _ "smap (smap (irrename \<sigma>)) ess"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  by (simp add: iterm.rrename_comp0s stream.map_comp smap2_smap) . .
  (* *)
  subgoal apply(rule disjI4_3)
  subgoal apply(elim exE) subgoal for es ess ess'
  apply(rule exI[of _ "smap (irrename \<sigma>) es"]) 
  apply(rule exI[of _ "smap (smap (irrename \<sigma>)) ess"]) 
  apply(rule exI[of _ "smap (smap (irrename \<sigma>)) ess'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def  
  apply (simp add: iterm.rrename_comp0s stream.map_comp smap2_smap smap_sflat) 
  by (metis inv_o_simp1 iterm.rrename_bijs iterm.rrename_inv_simps smap_sflat stream.map_comp stream.map_id) . . 
  (* *)
  subgoal apply(rule disjI4_4)
  subgoal apply(elim exE) subgoal for xs es es'
  apply(rule exI[of _ "dsmap \<sigma> xs"])
  apply(rule exI[of _ "smap (irrename \<sigma>) es"]) apply(rule exI[of _ "smap (irrename \<sigma>) es'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def  
  apply (simp add: iterm.rrename_comp0s stream.map_comp smap2_smap) 
    by (metis (no_types, lifting) comp_apply irrename_simps(3) stream.map_cong0) . . . 

lemma Tvars_dsset: "(Tfvars t - dsset xs) \<inter> dsset xs = {}" "|Tfvars t - dsset xs| <o |UNIV::ivar set|"
apply auto by (meson card_of_minus_bound small_Tfvars small_def)

lemma G_refresh: 
"(\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> 
 \<exists>C. small C \<and> C \<inter> Tfvars t = {} \<and> G R C t"
unfolding G_def Tmap_def apply safe (* HERE *)
  subgoal for es es'
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI4_1) 
    apply(rule exI[of _ "fst t"]) 
    apply(rule exI[of _ "snd t"]) 
    apply(cases t) by simp . 
  (* *)
  subgoal for e1 e1' es2 
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI4_2) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e1'"])
    apply(rule exI[of _ "es2"]) 
    apply(cases t) apply simp . .
  (* *)
  subgoal for e1 e2 es2' 
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI4_3) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e2"])
    apply(rule exI[of _ "es2'"]) 
    apply(cases t) apply auto . .
  (* *) 
  subgoal for xs es es'
  using refresh[OF Tvars_dsset, of xs t]  apply safe
  subgoal for f
  apply(rule exI[of _ "f ` (dsset xs)"])  
  apply(intro conjI)
    subgoal using small_image by auto
    subgoal unfolding id_on_def by auto (metis DiffI Int_emptyD image_eqI)
    subgoal apply(rule disjI4_4) 
    apply(rule exI[of _ "dsmap f xs"]) 
    apply(rule exI[of _ "smap (irrename f) es"]) 
    apply(rule exI[of _ "smap (irrename f) es'"]) 
    apply(cases t)  apply simp apply(intro conjI)
      subgoal unfolding stream.map_comp apply(rule stream.map_cong0) 
        apply(subst iLam_irrename[of "f"]) unfolding id_on_def by auto
      subgoal unfolding stream.map_comp apply(rule stream.map_cong0) 
        apply(subst iLam_irrename[of "f"]) unfolding id_on_def by auto 
      subgoal unfolding ssbij_def by auto . . . . 


(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation Istep: Induct where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars and G = G
apply standard 
  using G_mono G_equiv G_refresh by auto

(* *)

lemma ustep_I: "ustep t1 t2 = Istep.I (t1,t2)" 
unfolding ustep_def Istep.I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R tt1 tt2 apply(rule iffI)
  subgoal apply(elim disjE exE)
    \<^cancel>\<open>Beta: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp) apply(rule disjI4_1) by auto
    \<^cancel>\<open>iAppL: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp)  apply(rule disjI4_2) by auto
    \<^cancel>\<open>iAppR: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp)  apply(rule disjI4_3) by auto
    \<^cancel>\<open>Xi: \<close>
    subgoal for es es' xs apply(rule exI[of _ "dsset xs"], rule conjI, simp) apply(rule disjI4_4) by auto .
  subgoal apply(elim conjE disjE exE)
    \<^cancel>\<open>Beta: \<close>
    subgoal apply(rule disjI4_1) by auto
    \<^cancel>\<open>iAppL: \<close>
    subgoal apply(rule disjI4_2) by auto
    \<^cancel>\<open>iAppR: \<close>
    subgoal apply(rule disjI4_3) by auto
    \<^cancel>\<open>Xi: \<close>
    subgoal apply(rule disjI4_4) by auto . . .

(* FROM ABSTRACT BACK TO CONCRETE: *)
thm ustep.induct[no_vars] 

corollary BE_induct_ustep[consumes 2, case_names Beta iAppL iAppR Xi]: 
assumes par: "\<And>p. small (Pfvars p)"
and st: "ustep t1 t2"  
and Beta: "\<And>es es' p. 
  stream_all2 hred es es' \<Longrightarrow> 
  R p es es'"
and iAppL: "\<And>es es' ess p. 
  ustep es es' \<Longrightarrow> (\<forall>p'. R p' es es') \<Longrightarrow> 
  R p (smap2 iApp es ess) (smap2 iApp es' ess)"
and iAppR: "\<And>ess ess' es p. 
  ustep (sflat ess) (sflat ess') \<Longrightarrow> (\<forall>p'. R p' (sflat ess) (sflat ess')) \<Longrightarrow> 
  R p (smap2 iApp es ess) (smap2 iApp es ess')"
and Xi: "\<And>es es' xs p. 
  dsset xs \<inter> Pfvars p = {} \<Longrightarrow> 
  ustep es es' \<Longrightarrow> (\<forall>p'. R p' es es') \<Longrightarrow> 
  R p (smap (iLam xs) es) (smap (iLam xs) es')" 
shows "R p t1 t2"
unfolding ustep_I
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by simp
  subgoal using par st apply(elim Istep.BE_induct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
    subgoal unfolding ustep_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding ustep_I[symmetric] apply(elim disjE exE)
      subgoal using Beta by auto
      subgoal using iAppL by auto  
      subgoal using iAppR by auto  
      subgoal using Xi by auto . . .

(* ... and with fixed parameters: *)
corollary BE_induct_ustep'[consumes 2, case_names Beta iAppL iAppR Xi]: 
assumes par: "small A"
and st: "ustep t1 t2"  
and Beta: "\<And>es es'. stream_all2 hred es es' \<Longrightarrow> R es es'"
and iAppL: "\<And>es es' ess. 
  ustep es es' \<Longrightarrow> R es es' \<Longrightarrow> 
  R (smap2 iApp es ess) (smap2 iApp es' ess)"
and iAppR: "\<And>ess ess' es. 
  ustep (sflat ess) (sflat ess') \<Longrightarrow> R (sflat ess) (sflat ess') \<Longrightarrow> 
  R (smap2 iApp es ess) (smap2 iApp es ess')"
and Xi: "\<And>es es' xs. 
  dsset xs \<inter> A = {} \<Longrightarrow> 
  ustep es es' \<Longrightarrow> R es es' \<Longrightarrow> 
  R (smap (iLam xs) es) (smap (iLam xs) es')" 
shows "R t1 t2"
apply(rule BE_induct_ustep[of "\<lambda>_::unit. A"]) using assms by auto

(* Also inferring equivariance from the general infrastructure: *)
corollary irrename_ustep:
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" 
and r: "ustep es es'" 
shows "ustep (smap (irrename f) es) (smap (irrename f) es')"
using assms unfolding ustep_I using Istep.I_equiv[of "(es,es')" f]
unfolding Tmap_def ssbij_def by auto


lemma hred_eq_avoid: 
assumes "small A"
and "hred e e'"
shows "\<exists> xs e1 es2. dsset xs \<inter> \<Union> (FFVars ` (sset es2)) = {} \<and> dsset xs \<inter> A = {} \<and>
            e = iApp (iLam xs e1) es2 \<and> e' = itvsubst (imkSubst xs es2) e1"
sorry
(* this captures the freshness assumption for beta (I proved it in another theory) *)

 

end