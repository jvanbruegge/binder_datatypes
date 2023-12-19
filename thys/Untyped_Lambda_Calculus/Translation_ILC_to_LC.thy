(* The translations back and forth between the infinitary and finitary lambda-calculi *)
theory Translation_ILC_to_LC
imports ILC_relations_more Super_Recursor
begin

(* Translating (affine, uniform) finitary lambda to finitary-lambda *)


(* *)
definition B :: "(var term) set" where "B \<equiv> UNIV"


(* Restricting a (supervariable-preserving) ivar-permutation to a ver-permutation *)
definition restr :: "(ivar \<Rightarrow> ivar) \<Rightarrow> var \<Rightarrow> var" where 
"restr f x \<equiv> subOf (dsmap f (superOf x))"

lemma restr_id[simp]: "restr id = id"
unfolding restr_def by auto

lemma restr_comp: "bij f \<Longrightarrow> |supp f| <o |UNIV::ivar set| \<Longrightarrow> presSuper f \<Longrightarrow> 
bij g \<Longrightarrow> |supp g| <o |UNIV::ivar set| \<Longrightarrow> presSuper g \<Longrightarrow> 
restr (g o f) = restr g o restr f"
unfolding restr_def fun_eq_iff 
apply(subst dstream_map_comp[symmetric]) 
by (auto simp add: presSuper_def)

lemma bij_restr: 
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" "presSuper f"
shows "bij (restr f)"
proof-
  have 0: "\<And>d. dsmap f (dsmap (inv f) d) = d" 
  using f(1,2) by (simp add: dstream.map_comp)
  show ?thesis unfolding bij_def[of "restr f"] inj_def surj_def restr_def apply safe
    subgoal using f by (metis bij_imp_bij_inv dstream.map_comp dstream.map_id inv_o_simp1 
       presSuper_def subOf_superOf superOf_subOf super_superOf supp_inv_bound)
    subgoal for y by (metis 0 f(3) presSuper_def subOf_inj subOf_superOf super_superOf) .
qed

term "subOf ` (touchedSuper (supp f))"

lemma supp_restr: 
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" 
shows "supp (restr f) \<subseteq> subOf ` (touchedSuper (supp f))"
unfolding restr_def supp_def image_def touchedSuper_def 
by auto (smt (verit, ccfv_threshold) disjoint_iff dstream_map_ident_strong mem_Collect_eq subOf_superOf super_superOf)

lemma card_supp_restr: 
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" "bsmall (supp f)" "presSuper f"
shows "|supp (restr f)| <o |UNIV::var set|" 
proof-
  have "|supp (restr f)| \<le>o |subOf ` (touchedSuper (supp f))|"
  using supp_restr[OF f(1,2)] by auto
  also have "|subOf ` (touchedSuper (supp f))| <o |UNIV::var set|"
  using f(3) unfolding bsmall_def by (simp add: finite_card_var)
  finally show ?thesis .
qed

lemma finite_supp_restr: 
assumes "bij f" "|supp f| <o |UNIV::ivar set|" "bsmall (supp f)" "presSuper f"
shows "finite (supp (restr f))" 
using card_supp_restr[OF assms] unfolding finite_iff_le_card_var .

lemma restr_cong_id: 
assumes "bij f" "|supp f| <o |UNIV::ivar set|" "bsmall (supp f)" "presSuper f"
and "\<And>y x. y \<in> FFVars e \<Longrightarrow> x \<in> dsset (superOf y) \<Longrightarrow> f x = x" "z \<in> LC.FFVars e"
shows "restr f z = z"
using assms unfolding restr_def by (simp add: dstream_map_ident_strong)


(* *)

definition iVarB where "iVarB x \<equiv> Var (subOf (fst (theSN x)))"
definition iLamB where "iLamB (xs::ivar dstream) b \<equiv> Lam (subOf xs) b"
definition iAppB where "iAppB b1 bs2 \<equiv> App b1 (snth bs2 0)"
definition renB where "renB f b \<equiv> rrename (restr f) b"
definition FVarsB where "FVarsB b \<equiv> \<Union> ((dsset o superOf) ` (FFVars b))"


lemma iVarB_B: "super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> iVarB x \<in> B"
unfolding B_def by auto

lemma iAppB_B: "b1 \<in> B \<Longrightarrow> sset bs2 \<subseteq> B \<Longrightarrow> iAppB b1 bs2 \<in> B"
unfolding B_def by auto

lemma iLamB_B: "b \<in> B \<Longrightarrow> super xs \<Longrightarrow> iLamB xs b \<in> B"
unfolding B_def by auto

lemma renB_B: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
  b \<in> B \<Longrightarrow> renB \<sigma> b \<in> B"
unfolding B_def by auto

lemma renB_id: "b \<in> B \<Longrightarrow> renB id b = b"
unfolding renB_def by auto

lemma renB_comp: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
    bij \<tau> \<Longrightarrow> |supp \<tau>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<tau>) \<Longrightarrow> presSuper \<tau> \<Longrightarrow> 
    b \<in> B \<Longrightarrow> renB (\<tau> o \<sigma>) b = renB \<tau> (renB \<sigma> b)"
unfolding renB_def apply(subst restr_comp) 
  by (auto simp add: bij_restr card_supp_restr term.rrename_comps)

lemma renB_cong: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
   (\<forall>xs \<in> touchedSuper (FVarsB b). dsmap \<sigma> xs = xs) \<Longrightarrow> 
   renB \<sigma> b = b"
unfolding renB_def FVarsB_def apply(rule term.rrename_cong_ids)
by (auto simp: bij_restr card_supp_restr restr_def touchedSuper_UN intro: restr_cong_id)

lemma renB_FVarsB: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
   x \<in> FVarsB (renB \<sigma> b) \<longleftrightarrow> inv \<sigma> x \<in> FVarsB b"
unfolding renB_def FVarsB_def apply safe
  subgoal by simp (metis (no_types, lifting) bij_restr card_supp_restr dstream.set_map image_in_bij_eq inv_simp2 
    presSuper_def restr_def superOf_subOf super_superOf term.FFVars_rrenames)
  subgoal by simp (metis bij_restr card_supp_restr dstream.set_map image_in_bij_eq inv_simp1 presSuper_def 
    restr_def superOf_subOf super_superOf term.FFVars_rrenames) .

lemma renB_iVarB[simp]: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
  super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> 
  renB \<sigma> (iVarB x) = iVarB (\<sigma> x)"
unfolding renB_def iVarB_def apply(subst rrename_simps)
  subgoal by (auto simp add: bij_restr)
  subgoal by (auto simp add: card_supp_restr)
  subgoal unfolding restr_def apply(cases "theSN x", cases "theSN (\<sigma> x)") 
  by simp (smt (verit, ccfv_SIG) RSuper_def UN_iff bij_betw_def bij_betw_inv_into bij_superOf 
     dstream.set_map dtheN image_in_bij_eq inv_simp2 mem_Collect_eq presSuper_def superOf_subOf 
     theSN_unique) .

lemma renB_iAppB[simp]: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
   b1 \<in> B \<Longrightarrow> sset bs2 \<subseteq> B \<Longrightarrow>
   renB \<sigma> (iAppB b1 bs2) = iAppB (renB \<sigma> b1) (smap (renB \<sigma>) bs2)"
unfolding renB_def iAppB_def apply(subst rrename_simps)
  subgoal by (auto simp add: bij_restr)
  subgoal by (auto simp add: card_supp_restr)
  subgoal by auto .

lemma renB_iLamB[simp]: "bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
   b \<in> B \<Longrightarrow> super xs \<Longrightarrow> 
   renB \<sigma> (iLamB xs b) = iLamB (dsmap \<sigma> xs) (renB \<sigma> b)"
unfolding renB_def iLamB_def apply(subst rrename_simps)
  subgoal by (auto simp add: bij_restr)
  subgoal by (auto simp add: card_supp_restr)
  subgoal using restr_def superOf_subOf by auto .

lemma FVarsB_iVarB: "super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> touchedSuper (FVarsB (iVarB x)) \<subseteq> touchedSuper {x}"
unfolding FVarsB_def iVarB_def apply(cases "theSN x") 
  by auto (metis (mono_tags, lifting) Int_emptyD dtheN insert_subset mem_Collect_eq mk_disjoint_insert 
   singletonI superOf_subOf super_dsset_RSuper theSN_unique touchedSuper_def)

(* Unlike FVarsB_iVarB, we have that 
FVarsB_iAppB and FVarsB_iLamB actually even hold in a "raw", stronger version, with touchedSuper removed and with 
FVarsB_iLamB formulated as follows: "b \<in> B \<Longrightarrow> super xs \<Longrightarrow> FVarsB (iLamB xs b) \<subseteq> FVarsB b - dsset xs" *)
lemma FVarsB_iAppB: "b1 \<in> B \<Longrightarrow> sset bs2 \<subseteq> B \<Longrightarrow> 
 touchedSuper (FVarsB (iAppB b1 bs2)) \<subseteq> 
 touchedSuper (FVarsB b1) \<union> \<Union> ((touchedSuper o FVarsB) ` (sset bs2))"
unfolding FVarsB_def iAppB_def touchedSuper_def by (fastforce simp: shd_sset)

lemma FVarsB_iLamB: "b \<in> B \<Longrightarrow> super xs \<Longrightarrow>
  touchedSuper (FVarsB (iLamB xs b)) \<subseteq> touchedSuper (FVarsB b) - {xs}"
unfolding FVarsB_def iLamB_def touchedSuper_def
by auto (metis Int_emptyD subOf_superOf super_disj super_superOf)

interpretation T' : ILC_SuperRec where 
B = B and iVarB = iVarB and iAppB = iAppB and iLamB = iLamB and renB = renB and FVarsB = FVarsB
apply standard
using iVarB_B iAppB_B iLamB_B renB_B renB_id renB_comp 
renB_iVarB renB_iAppB renB_iLamB
FVarsB_iVarB FVarsB_iAppB FVarsB_iLamB apply auto  
by (auto simp add: renB_cong renB_FVarsB)  


(* END PRODUCT: *)

definition tr' :: "itrm \<Rightarrow> trm" where "tr' = T'.rec"

lemma tr'_iVar[simp]: "super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> tr' (iVar x) = Var (subOf (fst (theSN x)))"
using T'.rec_iVar unfolding tr'_def iVarB_def by auto

lemma tr'_iLam[simp]: "super xs \<Longrightarrow> good e \<Longrightarrow> tr' (iLam xs e) = Lam (subOf xs) (tr' e)"
using T'.rec_iLam unfolding tr'_def iLamB_def by auto

lemma tr'_iApp[simp]: "good e1 \<Longrightarrow> (\<forall>e2\<in>sset es2. good e2) \<Longrightarrow> 
  (\<forall>e2 e2'. {e2,e2'} \<subseteq> sset es2 \<longrightarrow> touchedSuperT e2 = touchedSuperT e2') \<Longrightarrow> 
  tr' (iApp e1 es2) = App (tr' e1) (tr' (snth es2 0))"
using T'.rec_iApp unfolding tr'_def iAppB_def by auto

lemma irrename_tr':
"good e \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp f) \<Longrightarrow> presSuper f \<Longrightarrow>
 tr' (irrename f e) = rrename (restr f) (tr' e)"
using T'.rec_irrename unfolding tr'_def renB_def by auto

lemma FFVars_tr': 
assumes "good e" "x \<in> LC.FFVars (tr' e)"
shows "dsset (superOf x) \<inter> ILC.FFVars e \<noteq> {}"
proof-
  have "superOf x \<in> touchedSuper (ILC.FFVars e)"
  using assms using T'.FVarsB_rec  FVarsB_def unfolding tr'_def  by (auto simp: touchedSuper_Union)
  thus ?thesis unfolding touchedSuper_def by auto
qed

(* *)

lemma reneqv_good: "reneqv e e' \<Longrightarrow> good e \<and> good e'"
apply(induct rule: reneqv.induct) 
  subgoal by(auto intro: good.intros) 
  subgoal by(auto intro: good.intros) 
  subgoal apply(rule conjI)
    subgoal apply(rule good.iApp) using reneqv_touchedSuperT_eq by blast+
    subgoal apply(rule good.iApp) using reneqv_touchedSuperT_eq by blast+ . .

lemma uniform_good: "uniform e \<Longrightarrow> good e"
using reneqv_good unfolding uniform_def3 by auto

lemma uniformS_good: 
"uniformS es2 \<Longrightarrow> 
 (\<forall>e2\<in>sset es2. good e2) \<and> 
 (\<forall>e2 e2'. {e2,e2'} \<subseteq> sset es2 \<longrightarrow> touchedSuperT e2 = touchedSuperT e2')"
unfolding uniformS_def4 using reneqv_good reneqv_touchedSuperT_eq by auto 


(* We recover Mazza's desired definition: *)

thm tr'_iVar 

lemma tr'_iLam_uniform[simp]: "super xs \<Longrightarrow> uniform e \<Longrightarrow> tr' (iLam xs e) = Lam (subOf xs) (tr' e)"
using uniform_good by auto

lemma tr'_iApp_uniform[simp]: "uniform e1 \<Longrightarrow> uniformS es2 \<Longrightarrow> 
  tr' (iApp e1 es2) = App (tr' e1) (tr' (snth es2 0))"
by (simp add: uniformS_good uniform_good)

lemma irrename_tr'_uniform:
"uniform e \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp f) \<Longrightarrow> presSuper f \<Longrightarrow>
 tr' (irrename f e) = rrename (restr f) (tr' e)"
using uniform_good irrename_tr' by auto

lemma FFVars_tr'_uniform: 
assumes "uniform e" "x \<in> LC.FFVars (tr' e)"
shows "dsset (superOf x) \<inter> ILC.FFVars e \<noteq> {}"
using assms FFVars_tr'  uniform_good by auto



end 
