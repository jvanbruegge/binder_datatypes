(* Here we instantiate the general enhanced rule induction to the "reneqv" predicate from Mazza  *)
theory ILC_uniform
imports LC2 ILC2 "../Instantiation_Infrastructure/Curry_LFP" 
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

consts ivarOf :: "var \<Rightarrow> ivar"

axiomatization where inject_ivarOf: "inj ivarOf"

lemma inj_ivarOf[simp]: "ivarOf x = ivarOf y \<longleftrightarrow> x = y"
by (meson injD inject_ivarOf)

consts super :: "ivar dstream \<Rightarrow> bool"

axiomatization where 
 super_disj:  "\<And>xs xs'. super xs \<Longrightarrow> super xs' \<Longrightarrow> xs \<noteq> xs' \<Longrightarrow> dsset xs \<inter> dsset xs' = {}"
and 
 super_exhaust: "\<And>x. \<exists>xs. super xs \<and> x \<in> dsset xs"
and 
 super_countable: "countable {xs . super xs}"
and 
 super_infinite: "infinite {xs . super xs}"
and 
 super_ivarOf: "\<And>xs. super xs \<Longrightarrow> dsset xs \<subseteq> range ivarOf"


consts superOf :: "var \<Rightarrow> ivar dstream"
axiomatization where bij_superOf: "bij_betw superOf UNIV {xs. super xs}"

definition subOf where "subOf xs \<equiv> SOME x. superOf x = xs"

lemma superOf_subOf[simp]: "super xs \<Longrightarrow> superOf (subOf xs) = xs"
by (metis (mono_tags, lifting) bij_betw_def bij_superOf imageE mem_Collect_eq someI_ex subOf_def)

lemma subOf_superOf[simp]: "subOf (superOf x) = x"
by (metis (mono_tags, lifting) bij_betw_imp_inj_on bij_superOf inv_f_f someI_ex subOf_def)

lemma subOf_inj[simp]: "super xs \<Longrightarrow> super ys \<Longrightarrow> subOf xs = subOf ys \<longleftrightarrow> xs = ys"
by (metis superOf_subOf)

lemma superOf_inj[simp]: "superOf x = superOf y \<longleftrightarrow> x = y"
by (metis subOf_superOf)

lemma super_superOf[simp]: "super (superOf x)"
using bij_betw_apply bij_superOf by fastforce

(* *)

consts natOf :: "nat list \<Rightarrow> nat"
axiomatization where inject_natOf: "inj natOf"

lemma inj_natOf[simp]: "natOf p = natOf p \<longleftrightarrow> p = p"
by (meson injD inject_natOf)

(***********************)
(*    *)


consts tr :: "trm \<Rightarrow> nat list \<Rightarrow> itrm"

axiomatization where 
tr_Var[simp]: "tr (Var x) p = iVar (dsnth (superOf x) (natOf p))"
and 
tr_Lam[simp]: "tr (Lam x e) p = iLam (superOf x) (tr e p)"
and 
tr_App[simp]: "tr (App e1 e2) p = iApp (tr e1 p) (smap (\<lambda>n. tr e2 (n # p)) nats)"



(* *)

(* todo: this could be equivariant in spite of super? *)
inductive reneqv where
 iVar: "{x,x'} \<subseteq> dsset xs \<Longrightarrow> reneqv (iVar x) (iVar x')"
|iLam: "super xs \<Longrightarrow> reneqv e e' \<Longrightarrow> reneqv (iLam xs e) (iLam xs e')"
|iApp: 
"reneqv e1 e1' \<Longrightarrow>
 (\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<longrightarrow> reneqv e e') 
 \<Longrightarrow>
 reneqv (iApp e1 es2) (iApp e1' es2')"

thm reneqv_def


(* INSTANTIATING THE Components LOCALE: *)

type_synonym T = "itrm"

definition Tmap :: "(ivar \<Rightarrow> ivar) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> rrename f"

fun Tfvars :: "T \<Rightarrow> ivar set" where 
"Tfvars e = FFVars e"


interpretation Components where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars
apply standard unfolding ssbij_def Tmap_def  
  using small_Un small_def iterm.card_of_FFVars_bounds
  apply (auto simp: iterm.rrename_id0s map_prod.comp iterm.rrename_comp0s inf_A) .

definition G :: "(T \<Rightarrow> bool) \<Rightarrow> ivar set \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>R B t.  
         (\<exists>x. B = {} \<and> t = iVar x) 
         \<or> 
         (\<exists>xs e. B = dsset xs \<and> t = iLam xs e \<and> 
                 R e)
         \<or> 
         (\<exists>e1 es2. B = {} \<and> t = iApp e1 es2 \<and> 
                   R e1 \<and> 
                   (\<forall>e2. e2 \<in> sset es2 \<longrightarrow> R e2 \<and> FFVars e1 \<inter> FFVars e2 = {}) \<and> 
                   (\<forall>e2 e2'. e2 \<in> sset es2 \<and> e2' \<in> sset es2 \<and> e2 \<noteq> e2' \<longrightarrow> FFVars e2 \<inter> FFVars e2' = {})
         )"

(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma G_mono: "R \<le> R' \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> G R' B t"
unfolding G_def by auto

(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma G_equiv: "ssbij \<sigma> \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (image \<sigma> B) (Tmap \<sigma> t)"
unfolding G_def apply(elim disjE)
  subgoal apply(rule disjI3_1)
  subgoal apply(elim exE) subgoal for x 
  apply(rule exI[of _ "\<sigma> x"]) 
  unfolding ssbij_def small_def Tmap_def 
  apply auto . . .
(* *)
  subgoal apply(rule disjI3_2)
  subgoal apply(elim exE) subgoal for xs e
  apply(rule exI[of _ "dsmap \<sigma> xs"])
  apply(rule exI[of _ "rrename \<sigma> e"])  
  unfolding ssbij_def small_def Tmap_def  
  apply (simp add: iterm.rrename_comps) . . .
  (* *)
  subgoal apply(rule disjI3_3)
  subgoal apply(elim exE) subgoal for e1 es2
  apply(rule exI[of _ "rrename \<sigma> e1"]) 
  apply(rule exI[of _ "smap (rrename \<sigma>) es2"]) 
  unfolding ssbij_def small_def Tmap_def 
  apply (fastforce simp add: iterm.rrename_comps) . . . .

lemma Tvars_dsset: "(Tfvars t - dsset xs) \<inter> dsset xs = {}" "|Tfvars t - dsset xs| <o |UNIV::ivar set|"
apply auto using card_of_minus_bound iterm.set_bd_UNIV by blast

lemma G_refresh: 
"(\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> small B \<Longrightarrow> G R B t \<Longrightarrow> 
 \<exists>C. small C \<and> C \<inter> Tfvars t = {} \<and> G R C t"
unfolding G_def Tmap_def apply safe
  subgoal for x
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI3_1) 
    apply simp . .
  (* *)
  subgoal for xs e  
  using refresh[OF Tvars_dsset, of xs t] apply safe
  subgoal for f
  apply(rule exI[of _ "f ` (dsset xs)"])  
  apply(intro conjI)
    subgoal using small_dsset small_image by auto
    subgoal unfolding id_on_def by auto 
    subgoal apply(rule disjI3_2)
    apply(rule exI[of _ "dsmap f xs"]) 
    apply(rule exI[of _ "rrename f e"]) 
    apply simp apply(intro conjI)
      subgoal apply(subst iLam_rrename[of "f"]) unfolding id_on_def by auto
      subgoal apply(subst rrename_eq_itvsubst_iVar)
        subgoal unfolding ssbij_def by auto
        subgoal unfolding ssbij_def by auto
        subgoal apply(subst rrename_eq_itvsubst_iVar[symmetric]) unfolding ssbij_def by auto . . . . 
  (* *)
  subgoal for e1 es2
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI3_3) 
    apply(rule exI[of _ "e1"])  
    apply(rule exI[of _ "es2"]) 
    apply simp . . .
 

(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation iLam: Induct where dummy = "undefined :: ivar" and 
Tmap = Tmap and Tfvars = Tfvars and G = G
apply standard 
  using G_mono G_equiv G_refresh by auto

(* *)

lemma reneqv_I: "reneqv t = iLam.I t" 
unfolding reneqv_def iLam.I_def apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R tt apply(rule iffI)
  subgoal apply(elim disjE exE conjE)
    \<^cancel>\<open>iVar: \<close>
    subgoal for x apply(rule exI[of _ "{}"], rule conjI, simp) apply(rule disjI3_1) by auto
    \<^cancel>\<open>iLam: \<close>
    subgoal for e xs apply(rule exI[of _ "dsset xs"], rule conjI, simp)  apply(rule disjI3_2) by auto 
    \<^cancel>\<open>iApp: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp)  apply(rule disjI3_3) by auto .
  subgoal apply(elim conjE disjE exE)
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
and st: "reneqv t"  
and iVar: "\<And>x p. R p (iVar x)"
and iLam: "\<And>e xs p. 
  dsset xs \<inter> Pfvars p = {} \<Longrightarrow> 
  reneqv e \<Longrightarrow> (\<forall>p'. R p' e) \<Longrightarrow> R p (iLam xs e)" 
and iApp: "\<And>e1 es2 p.
    reneqv e1 \<Longrightarrow> (\<forall>p'. R p' e1) \<Longrightarrow>
    (\<forall>e2. e2 \<in> sset es2 \<longrightarrow> (reneqv e2 \<and> (\<forall>p'. R p' e2)) \<and> FFVars e1 \<inter> FFVars e2 = {}) \<Longrightarrow>
    (\<forall>e2 e2'. e2 \<in> sset es2 \<and> e2' \<in> sset es2 \<and> e2 \<noteq> e2' \<longrightarrow> FFVars e2 \<inter> FFVars e2' = {}) \<Longrightarrow> 
    R p (iApp e1 es2)"
shows "R p t"
unfolding reneqv_I
apply(subgoal_tac "R p t") (* this is overkill here, but I keep the general pattern *)
  subgoal by simp
  subgoal using par st apply(elim iLam.BE_induct[where R = "\<lambda>p t. R p t"])
    subgoal unfolding reneqv_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding reneqv_I[symmetric] apply(elim disjE exE)
      subgoal for x using iVar by auto
      subgoal using iLam by auto  
      subgoal using iApp by auto . . .

end