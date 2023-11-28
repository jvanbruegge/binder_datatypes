theory Super_Recursor
imports BSmall Supervariables ILC_Good 
begin


(* "SUPER" RECURSOR (i.e., restricted to supervariable binders)  *)


locale ILC_SuperRec = 
fixes B :: "'b set"
and iVarB :: "ivar \<Rightarrow> 'b" 
and iAppB :: "'b \<Rightarrow> 'b stream \<Rightarrow> 'b"
and iLamB :: "ivar dstream \<Rightarrow> 'b \<Rightarrow> 'b"
and renB :: "(ivar \<Rightarrow> ivar) \<Rightarrow> 'b \<Rightarrow> 'b"
and FVarsB :: "'b \<Rightarrow> ivar set"
assumes 
(* closedness: *)
iVarB_B[simp,intro]: "\<And>xs x. super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> iVarB x \<in> B"
and 
iAppB_B[simp,intro]: "\<And>b1 bs2. b1 \<in> B \<Longrightarrow> sset bs2 \<subseteq> B \<Longrightarrow> iAppB b1 bs2 \<in> B"
and 
iLamB_B[simp,intro]: "\<And>xs b. b \<in> B \<Longrightarrow> super xs \<Longrightarrow> iLamB xs b \<in> B"
and 
renB_B[simp]: "\<And>\<sigma> b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
  b \<in> B \<Longrightarrow> renB \<sigma> b \<in> B"
and 
(* proper axioms: *)
renB_id[simp,intro]: "\<And>b. b \<in> B \<Longrightarrow> renB id b = b"
and 
renB_comp[simp,intro]: "\<And>b \<sigma> \<tau>. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
    bij \<tau> \<Longrightarrow> |supp \<tau>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<tau>) \<Longrightarrow> presSuper \<tau> \<Longrightarrow> 
    b \<in> B \<Longrightarrow> renB (\<tau> o \<sigma>) b = renB \<tau> (renB \<sigma> b)"
and 
renB_cong[simp]: "\<And>\<sigma> b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
   (\<forall>x \<in> FVarsB b. \<sigma> x = x) \<Longrightarrow> 
   renB \<sigma> b = b"
and 
renB_FVarsB[simp]: "\<And>\<sigma> x b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
   x \<in> FVarsB (renB \<sigma> b) \<longleftrightarrow> inv \<sigma> x \<in> FVarsB b"
and 
(* *)
renB_iVarB[simp]: "\<And>\<sigma> x. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
  super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> 
  renB \<sigma> (iVarB x) = iVarB (\<sigma> x)"
and 
renB_iAppB[simp]: "\<And>\<sigma> b1 bs2. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
   b1 \<in> B \<Longrightarrow> sset bs2 \<subseteq> B \<Longrightarrow>
   renB \<sigma> (iAppB b1 bs2) = iAppB (renB \<sigma> b1) (smap (renB \<sigma>) bs2)"
and 
renB_iLamB[simp]: "\<And>\<sigma> xs b. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
   b \<in> B \<Longrightarrow> super xs \<Longrightarrow> 
   renB \<sigma> (iLamB xs b) = iLamB (dsmap \<sigma> xs) (renB \<sigma> b)"
(* *)
and 
FVarsB_iVarB: "\<And>xs x. super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> touchedSuper (FVarsB (iVarB x)) \<subseteq> touchedSuper {x}"
and 
FVarsB_iAppB: "\<And>b1 bs2. b1 \<in> B \<Longrightarrow> sset bs2 \<subseteq> B \<Longrightarrow> FVarsB (iAppB b1 bs2) \<subseteq> 
 FVarsB b1 \<union> \<Union> (FVarsB ` (sset bs2))"
and 
FVarsB_iLamB: "\<And>xs b. b \<in> B \<Longrightarrow> super xs \<Longrightarrow> FVarsB (iLamB xs b) \<subseteq> FVarsB b - dsset xs"
begin 

definition morFromTrm where 
"morFromTrm H \<equiv> 
 (\<forall>e. good e \<longrightarrow> H e \<in> B) \<and>  
 (\<forall>xs x. super xs \<and> x \<in> dsset xs \<longrightarrow> H (iVar x) = iVarB x) \<and> 
 (\<forall>e1 es2. good e1 \<and> (\<forall>e2\<in>sset es2. good e2) \<longrightarrow> H (iApp e1 es2) = iAppB (H e1) (smap H es2)) \<and> 
 (\<forall>xs e. super xs \<and> good e \<longrightarrow> H (iLam xs e) = iLamB xs (H e)) \<and> 
 (\<forall>\<sigma> e. good e \<and> bij \<sigma> \<and> |supp \<sigma>| <o |UNIV::ivar set| \<and> bsmall (supp \<sigma>) \<and> presSuper \<sigma>  
          \<longrightarrow> H (irrename \<sigma> e) = renB \<sigma> (H e)) \<and> 
 (\<forall>e. good e \<longrightarrow> touchedSuper (FVarsB (H e)) \<subseteq> touchedSuper (FFVars e))"

lemma ex_morFromTrm: "\<exists>H. morFromTrm H"
sorry
(* will use this: *)
thm iLam_inject_super (* TODO: have this for vanilla Lam and iLam too (and in general, 
such a tight support for f is useful); also infer the version for a fresh ys; 
maybe instead of "good e" I can just have "finite (touchedSuperT e)", i.e., "bsmall e"?
Also, FVarsB_iAppB and FVarsB_iLamB could probably also be relaxed to factor in touchedSuper. *)

definition rec where "rec \<equiv> SOME H. morFromTrm H"

lemma morFromTrm_rec: "morFromTrm rec"
by (metis ex_morFromTrm rec_def someI_ex)

lemma rec_B[simp,intro!]: "good e \<Longrightarrow> rec e \<in> B" 
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_iVar[simp]: "super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> rec (iVar x) = iVarB x"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_iApp[simp]: "good e1 \<Longrightarrow> (\<forall>e2\<in>sset es2. good e2) \<Longrightarrow> rec (iApp e1 es2) = iAppB (rec e1) (smap rec es2)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_iLam[simp]: "super xs \<Longrightarrow> good e \<Longrightarrow> rec (iLam xs e) = iLamB xs (rec e)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_irrename: "good e \<Longrightarrow> bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::ivar set| \<Longrightarrow> bsmall (supp \<sigma>) \<Longrightarrow> presSuper \<sigma> \<Longrightarrow> 
 rec (irrename \<sigma> e) = renB \<sigma> (rec e)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma FVarsB_rec: "good e \<Longrightarrow> touchedSuper (FVarsB (rec e)) \<subseteq> touchedSuper (FFVars e)"
using morFromTrm_rec unfolding morFromTrm_def by auto

lemma rec_unique: 
assumes gd: "good e"
and "\<And>e. good e \<Longrightarrow> H e \<in> B" 
"\<And>xs x. super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> H (iVar x) = iVarB x" 
"\<And>e1 es2. good e1 \<Longrightarrow> (\<forall>e2\<in>sset es2. good e2) \<Longrightarrow> H (iApp e1 es2) = iAppB (H e1) (smap H es2)"
"\<And>xs e. super xs \<Longrightarrow> good e \<Longrightarrow> H (iLam xs e) = iLamB xs (H e)"
shows "H e = rec e" 
using gd apply(induct e)
using assms by (auto cong: stream.map_cong)  

end (* context ILC_SuperRec *)

end 