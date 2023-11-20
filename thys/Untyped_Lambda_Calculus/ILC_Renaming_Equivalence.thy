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

(* INSTANTIATING THE Components LOCALE: *)

type_synonym T = "itrm \<times> itrm"

definition Tmap :: "(ivar \<Rightarrow> ivar) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> map_prod (rrename f) (rrename f)"

fun Tfvars :: "T \<Rightarrow> ivar set" where 
"Tfvars (e1,e2) = FFVars e1 \<union> FFVars e2"


interpretation Components where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars
apply standard unfolding ssbij_def Tmap_def  
  using small_Un small_def iterm.card_of_FFVars_bounds
  apply (auto simp: iterm.rrename_id0s map_prod.comp iterm.rrename_comp0s inf_A)
  using var_sum_class.Un_bound by blast

definition G :: "(T \<Rightarrow> bool) \<Rightarrow> ivar set \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>R B t.  
         (\<exists>xs x x'. B = {} \<and> fst t = iVar x \<and> snd t = iVar x' \<and> 
                    super xs \<and> {x,x'} \<subseteq> dsset xs) 
         \<or>
         (\<exists>xs e e'. B = dsset xs \<and> fst t = iLam xs e \<and> snd t = iLam xs e' \<and> 
                    super xs \<and> R (e,e'))
         \<or> 
         (\<exists>e1 e1' es2 es2'. B = {} \<and> fst t = iApp e1 es2 \<and> snd t = iApp e1' es2' \<and> 
                            R (e1,e1') \<and> (\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<longrightarrow> R (e,e')))"
 

(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma G_mmono: "R \<le> R' \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> G R' B t"
unfolding G_def by fastforce


definition wfBij where "wfBij \<sigma> \<equiv> \<forall>xs. super xs \<longleftrightarrow> super (dsmap \<sigma> xs)"
(* we defined closedness looking at the possible values of B in G: *)
definition closed where "closed X \<equiv> X = {} \<or> (\<exists>xs. super xs \<and> X = dsset xs)"
(* no need for this more elaborate setting: *)
(* \<forall>xs. super xs \<and> dsset xs \<inter> X \<noteq> {} \<longrightarrow> dsset xs \<subseteq> X *)


(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma G_eequiv: "ssbij \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (image \<sigma> B) (Tmap \<sigma> t)"
unfolding G_def apply(elim disjE)
  subgoal apply(rule disjI3_1)
  subgoal apply(elim exE) subgoal for xs x x'
  apply(rule exI[of _ "dsmap \<sigma> xs"]) 
  apply(rule exI[of _ "\<sigma> x"]) apply(rule exI[of _ "\<sigma> x'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def wfBij_def
  by simp . .
  (* *)
  subgoal apply(rule disjI3_2)
  subgoal apply(elim exE) subgoal for xs e e'
  apply(rule exI[of _ "dsmap \<sigma> xs"]) 
  apply(rule exI[of _ "rrename \<sigma> e"]) 
  apply(rule exI[of _ "rrename \<sigma> e'"])  
  apply(cases t) unfolding ssbij_def small_def Tmap_def wfBij_def
  by (simp add: iterm.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI3_3)
  subgoal apply(elim exE) subgoal for e1 e1' es2 es2'
  apply(rule exI[of _ "rrename \<sigma> e1"]) apply(rule exI[of _ "rrename \<sigma> e1'"]) 
  apply(rule exI[of _ "smap (rrename \<sigma>) es2"]) apply(rule exI[of _ "smap (rrename \<sigma>) es2'"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  apply (simp add: iterm.rrename_comps) 
  by (metis image_in_bij_eq iterm.rrename_bijs iterm.rrename_inv_simps) . . .

lemma Tvars_dsset: "(Tfvars t - dsset xs) \<inter> dsset xs = {}" "|Tfvars t - dsset xs| <o |UNIV::ivar set|"
apply auto by (meson card_of_minus_bound small_Tfvars small_def)

(* *)

lemma G_closed: "G R B t \<Longrightarrow> closed B"
unfolding G_def closed_def by auto 

lemma wfBij_id[simp,intro]: "wfBij id" unfolding wfBij_def by simp

lemma wfBij_comp[simp]: "ssbij \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> wfBij \<tau> \<Longrightarrow> wfBij (\<tau> o \<sigma>)"
unfolding wfBij_def by (metis ssbij_def dstream.map_comp)

lemma wfBij_inv[simp]: "ssbij \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> wfBij (inv \<sigma>)"
unfolding wfBij_def ssbij_def 
by (metis bij_imp_bij_inv dstream.map_comp dstream.map_id inv_inv_eq inv_o_simp1 supp_inv_bound)

lemma dsset_dsmap_inv_NE: "bij \<sigma> \<Longrightarrow> dsset xs \<inter> \<sigma> ` A \<noteq> {} \<longleftrightarrow> dsset (dsmap (inv \<sigma>) xs) \<inter> A \<noteq> {}"
by (metis bij_betw_def bij_imp_bij_betw bij_imp_bij_inv dsset_dsmap image_Int_empty inf_commute)

lemma closed_wfBij: "ssbij \<sigma> \<Longrightarrow> wfBij \<sigma> \<Longrightarrow> closed A \<Longrightarrow> closed (\<sigma> ` A)"
unfolding closed_def apply clarify  
by (metis ILC2.ssbij_def dstream.set_map wfBij_def)
(*
  subgoal for xs x  apply(subst image_in_bij_eq)
    subgoal unfolding ssbij_def by simp
    subgoal apply(frule wfBij_inv)
      subgoal by simp
      subgoal apply(subst (asm) dsset_dsmap_inv_NE)
        subgoal unfolding ssbij_def by simp
        subgoal by (metis ILC2.ssbij_def IntD2 bij_bij_betw_inv dstream.set_map inf.absorb1 
                    rev_image_eqI supp_inv_bound wfBij_def) . . . . 
*)

(* *)
lemma small_ssbij_closed: 
assumes s: "small A" "small B" "small A'" "A \<inter> A' = {}" and c: "closed A" 
shows "\<exists>\<rho>. ssbij \<rho> \<and> wfBij \<rho> \<and> \<rho> ` A \<inter> B = {} \<and> (\<forall>a\<in>A'. \<rho> a = a)" 
using c unfolding closed_def proof(elim disjE exE conjE)
  assume A: "A = {}"
  show ?thesis apply(rule exI[of _ id]) unfolding A ssbij_def by auto
next
  fix xs assume xs: "super xs" and A: "A = dsset xs"
  obtain xs' where xs': "super xs'" and xss': "xs \<noteq> xs'"
  using xs super_infinite by (smt (verit, del_insts) Collect_cong Collect_conv_if finite.simps)
  hence ds: "dsset xs \<inter> dsset xs' = {}" using super_disj xs by auto
  show ?thesis
  sorry
qed
  


thm refresh
lemma refresh_super: 
assumes V: "V \<inter> dsset xs = {}" "|V| <o |UNIV::ivar set|" "super xs"  
shows "\<exists>f xs'. bij (f::ivar\<Rightarrow>ivar) \<and> |supp f| <o |UNIV::ivar set| \<and> 
               dsset xs' \<inter> dsset xs = {} \<and> dsset xs' \<inter> V = {} \<and>
               dsmap f xs = xs' \<and> id_on V f \<and> (\<forall>ys. super ys \<longleftrightarrow> super (dsmap f ys))"
proof-
  define A A' B where A: "A \<equiv> dsset xs" and A': "A' = V" and B: "B \<equiv> V \<union> dsset xs"
  have 0: "small A" "small B" "small A'" "A \<inter> A' = {}" "closed A"
  unfolding A A' B closed_def using V 
  apply auto 
  using small_Un small_def apply blast
  using small_def super_disj by fastforce+
  show ?thesis using small_ssbij_closed[OF 0] 
  apply safe subgoal for f apply(intro exI[of _ f] exI[of _ "dsmap f xs"]) 
  unfolding ssbij_def wfBij_def A A' B id_on_def by auto .
qed

lemma G_rrefresh: 
"(\<forall>\<sigma> t. ssbij \<sigma> \<and> wfBij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> 
 \<exists>C. small C \<and> C \<inter> Tfvars t = {} \<and> G R C t"
apply(frule G_closed)
unfolding G_def Tmap_def apply safe
  subgoal for xs x x'
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI3_1) 
    apply(rule exI[of _ xs]) 
    apply(rule exI[of _ x])
    apply(rule exI[of _ x']) 
    apply(cases t) apply simp . .
  (* *)
  subgoal for xs e e'
  apply(frule refresh_super[OF Tvars_dsset, of xs t]) apply safe
  subgoal for f
  apply(rule exI[of _ "f ` (dsset xs)"])  
  apply(intro conjI)
    subgoal using small_dsset small_image by auto
    subgoal unfolding id_on_def by auto (metis DiffI Int_emptyD image_eqI)
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
        subgoal unfolding id_on_def ssbij_def wfBij_def by auto . . .
  (* *)
  subgoal for e1 e1' es2 es2'
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI3_3) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e1'"])
    apply(rule exI[of _ "es2"]) 
    apply(rule exI[of _ "es2'"]) 
    apply(cases t) by simp . . 
 

(* FINALLY, INTERPRETING THE IInduct LOCALE: *)

interpretation Reneqv : IInduct where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars and G = G and closed = closed and wfBij = wfBij 
apply standard 
  using G_mmono G_eequiv 
  G_closed wfBij_id wfBij_comp wfBij_inv closed_wfBij small_ssbij_closed
  G_rrefresh by auto  

(* *)

lemma reneqv_I: "reneqv t1 t2 = Reneqv.I (t1,t2)" 
unfolding reneqv_def Reneqv.I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R tt1 tt2 apply(rule iffI)
  subgoal apply(elim disjE exE conjE)
    \<^cancel>\<open>iVar: \<close>
    subgoal for xs x x' apply(rule exI[of _ "{}"], rule conjI, simp) apply(rule disjI3_1) by auto
    \<^cancel>\<open>iLam: \<close> 
    subgoal for xs e e' apply(rule exI[of _ "dsset xs"], rule conjI, simp) apply(rule disjI3_2) by auto 
    \<^cancel>\<open>iApp: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp) apply(rule disjI3_3) by auto .
    (* *)
  subgoal apply(elim disjE exE conjE)
    \<^cancel>\<open>iVar: \<close>
    subgoal apply(rule disjI3_1) by auto
    \<^cancel>\<open>iLam: \<close>
    subgoal apply(rule disjI3_2) by auto
    \<^cancel>\<open>iApp: \<close>
    subgoal apply(rule disjI3_3) by auto . . .

(* FROM ABSTRACT BACK TO CONCRETE: *)
thm reneqv.induct[no_vars] 

corollary BE_induct_reneqv: 
assumes par: "\<And>p. small (Pfvars p)"
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
  subgoal using par st apply(elim Reneqv.BE_induct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
    subgoal unfolding reneqv_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding reneqv_I[symmetric] apply(elim disjE exE)
      subgoal using iVar by auto 
      subgoal using iLam by auto  
      subgoal using iApp by auto . . .

end