(* The translations back and forth between the infinitary and finitary lambda-calculi *)
theory Translation_ILC_to_LC
imports ILC_relations_more Super_Recursor
begin

(* Translating (affine, uniform) finitary lambda to finitary-lambda *)


(* *)
definition B :: "(var term) set" where "B \<equiv> UNIV"


(*
term ivarOf

definition varOf :: "ivar \<Rightarrow> var" where 
"varOf \<equiv> SOME f. f o ivarOf = id"

find_theorems ivarOf

lemma inj_ex_comp: "inj g \<Longrightarrow> \<exists>f. f o g = id"
using inv_o_cancel by blast

lemma varOf_o_ivarOf: "varOf o ivarOf = id"
by (smt (verit, ccfv_threshold) inj_ex_comp ivarOf_inj someI_ex varOf_def)

lemma varOf_ivarOf[simp]: "varOf (ivarOf x) = x"
using varOf_o_ivarOf unfolding fun_eq_iff by auto
*)




thm dstream.map_comp[no_vars]

lemma dstream_map_comp: 
"bij (f::ivar\<Rightarrow>ivar) \<Longrightarrow> |supp f| <o |UNIV::ivar set| \<Longrightarrow> bij g \<Longrightarrow> |supp g| <o |UNIV::ivar set| \<Longrightarrow> 
 dsmap g o dsmap f = dsmap (g \<circ> f)"
using dstream.map_comp unfolding fun_eq_iff by auto


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

lemma bij_restr: "bij f \<Longrightarrow> |supp f| <o |UNIV::ivar set| \<Longrightarrow> presSuper f \<Longrightarrow> bij (restr f)"
sorry

lemma card_supp_restr: "bij f \<Longrightarrow> |supp f| <o |UNIV::ivar set| \<Longrightarrow> presSuper f \<Longrightarrow> 
   |supp (restr f)| <o |UNIV::var set|"
sorry



(* *)


definition iVarB where "iVarB x \<equiv> Var (subOf (fst (theSN x)))"
definition iLamB where "iLamB (xs::ivar dstream) b \<equiv> Lam (subOf xs) b"
definition iAppB where "iAppB b1 bs2 \<equiv> App b1 (snth bs2 0)"
definition renB where "renB f b \<equiv> rrename (restr f) b"
definition FVarsB where "FVarsB b \<equiv> \<Union> ((dsset o superOf) ` (FFVars b))"


lemma iVarB_B: "x \<in> RSuper \<Longrightarrow> iVarB x \<in> B"
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
   (\<forall>x \<in> FVarsB b. \<sigma> x = x) \<Longrightarrow> 
   renB \<sigma> b = b"
sorry

lemma renB_FVarsB: "\<And>\<sigma> x b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
   x \<in> FVarsB (renB \<sigma> b) \<longleftrightarrow> inv \<sigma> x \<in> FVarsB b"
sorry

lemma renB_iVarB[simp]: "\<And>\<sigma> x. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
  x \<in> RSuper \<Longrightarrow> 
  renB \<sigma> (iVarB x) = iVarB (\<sigma> x)"
sorry

lemma renB_iAppB[simp]: "\<And>\<sigma> b1 bs2. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
   b1 \<in> B \<Longrightarrow> sset bs2 \<subseteq> B \<Longrightarrow>
   renB \<sigma> (iAppB b1 bs2) = iAppB (renB \<sigma> b1) (smap (renB \<sigma>) bs2)"
sorry

lemma renB_iLamB[simp]: "\<And>\<sigma> xs b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
   b \<in> B \<Longrightarrow> super xs \<Longrightarrow> 
   renB \<sigma> (iLamB xs b) = iLamB (dsmap \<sigma> xs) (renB \<sigma> b)"
sorry 

lemma FVarsB_iVarB: "\<And>x. x \<in> RSuper \<Longrightarrow> FVarsB (iVarB x) \<subseteq> {x}"
sorry

lemma FVarsB_iAppB: "\<And>b1 bs2. b1 \<in> B \<Longrightarrow> sset bs2 \<subseteq> B \<Longrightarrow> FVarsB (iAppB b1 bs2) \<subseteq> 
 FVarsB b1 \<union> \<Union> (FVarsB ` (sset bs2))"
sorry

lemma FVarsB_iLamB: "\<And>xs b. b \<in> B \<Longrightarrow> super xs \<Longrightarrow> FVarsB (iLamB xs b) \<subseteq> FVarsB b - dsset xs"
sorry

interpretation T' : ILC_SuperRec where 
B = B and iVarB = iVarB and iAppB = iAppB and iLamB = iLamB and renB = renB and FVarsB = FVarsB
apply standard
using iVarB_B iAppB_B iLamB_B renB_B renB_id renB_comp 
renB_iVarB renB_iAppB renB_iLamB
FVarsB_iVarB FVarsB_iAppB FVarsB_iLamB apply auto
by (auto simp add: renB_cong renB_FVarsB)  


(* END PRODUCT: *)

definition tr' :: "itrm \<Rightarrow> trm" where "tr' = T'.rec"

lemma tr'_iVar[simp]: "x \<in> RSuper \<Longrightarrow> tr' (iVar x) = Var (subOf (fst (theSN x)))"
using T'.rec_iVar unfolding tr'_def iVarB_def by auto

lemma tr'_iLam[simp]: "super xs \<Longrightarrow> good e \<Longrightarrow> tr' (iLam xs e) = Lam (subOf xs) (tr' e)"
using T'.rec_iLam unfolding tr'_def iLamB_def by auto

lemma tr'_iApp[simp]: "good e1 \<Longrightarrow> (\<forall>e2\<in>sset es2. good e2) \<Longrightarrow> 
  tr' (iApp e1 es2) = App (tr' e1) (tr' (snth es2 0))"
using T'.rec_iApp unfolding tr'_def iAppB_def by auto

lemma irrename_tr':
"good e \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp f) \<Longrightarrow> presSuper f \<Longrightarrow>
 tr' (irrename f e) = rrename (restr f) (tr' e)"
using T'.rec_irrename unfolding tr'_def renB_def by auto

lemma FFVars_tr': 
"good e \<Longrightarrow> x \<in> LC.FFVars (tr' e) \<Longrightarrow> dsset (superOf x) \<subseteq> ILC.FFVars e"
using T'.FVarsB_rec unfolding tr'_def FVarsB_def by auto



end 
