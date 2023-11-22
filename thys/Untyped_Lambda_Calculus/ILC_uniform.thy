(* Here we instantiate the general enhanced rule induction to the "reneqv" predicate from Mazza  *)
theory ILC_uniform
imports ILC_Renaming_Equivalence
begin

definition uniform :: "ivar iterm \<Rightarrow> bool" 
where "uniform e \<equiv> \<exists>e'. reneqv e e'" 

lemma uniform_finite_touchedUponT: "uniform e \<Longrightarrow> finite (touchedSuperT e)"
using reneqv_finite_touchedSuperT uniform_def by blast

(* We already know equivariance from the general infrastructure: *)
lemma rrename_reneqv:
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" "presSuper f"
and r: "reneqv e e'" 
shows "reneqv (rrename f e) (rrename f e')"
using assms unfolding reneqv_I using Reneqv.II_equiv[of "(e,e')" f]
unfolding Tmap_def ssbij_def wfBij_presSuper by auto

find_theorems reneqv

(* Symmetry follows by normal induction: *)
lemma reneweqv_sym:
"reneqv e e' \<Longrightarrow> reneqv e' e"
apply(induct rule: reneqv.induct) 
apply (auto intro: reneqv.intros)  
by (metis Un_iff iApp insert_subset)

lemma uniform_def2: "uniform e \<longleftrightarrow> (\<exists>e'. reneqv e' e)"
unfolding uniform_def using reneweqv_sym by auto

(* But to prove transitivity we will need inversion rules, which for the lambda cases 
will require (1) the custom presSuper equivariance and (2) a custom supervariable-based injectivity for 
lambda.  *)


lemma reneqv_iVar_casesL:
"reneqv (iVar x) e' \<Longrightarrow> 
 (\<exists> xs x'. e' = iVar x' \<and> super xs \<and> {x,x'} \<subseteq> dsset xs)"
apply(erule reneqv.cases) by auto

lemma reneqv_iVar_casesR:
"reneqv e (iVar x') \<Longrightarrow> 
 (\<exists> xs x. e = iVar x \<and> super xs \<and> {x,x'} \<subseteq> dsset xs)"
apply(erule reneqv.cases) by auto

lemma iLam_inject_super: 
assumes u: "uniform (iLam xs e)" and eq: "iLam xs e = iLam xs' e'" and super: "super xs" "super xs'"
shows "\<exists>f. bij f \<and> |supp f| <o |UNIV::ivar set| \<and> presSuper f \<and> 
       id_on (ILC.FFVars (iLam xs e)) f \<and> id_on (- (dsset xs \<union> dsset xs')) f \<and> 
           dsmap f xs = xs' \<and> rrename f e = e'"
proof-
  obtain f where f: "bij f \<and> |supp f| <o |UNIV::ivar set| \<and> id_on (FFVars (iLam xs e)) f \<and> 
     dsmap f xs = xs' \<and> rrename f e = e'" using eq unfolding iLam_inject by auto
  hence i: "inj_on f (dsset xs)" unfolding bij_def inj_on_def by auto
  define A where A: "A = FFVars (iLam xs e)"
  have 0: "|A| <o |UNIV::ivar set|" "finite (touchedSuper A)" "A \<inter> dsset xs = {}"
     "A \<inter> dsset xs' = {}" "bij_betw f (dsset xs) (dsset xs')" "dsmap f xs = xs'"
    subgoal unfolding A using iterm.set_bd_UNIV by blast
    subgoal unfolding A using touchedSuperT_def u uniform_finite_touchedUponT by fastforce
    subgoal unfolding A by auto
    subgoal unfolding A eq by auto
    subgoal using f unfolding bij_def bij_betw_def inj_on_def using i by auto
    subgoal using f by auto .
  show ?thesis using extend_super2[OF super 0] apply safe
  subgoal for g apply(rule exI[of _ g]) using f unfolding A eq_on_def id_on_def 
    by (metis DiffI ILC.rrename_cong dstream.map_cong0 iterm.set(3)) .
qed

lemma reneqv_iLam_casesL:
assumes xs: "super xs" and rr: "reneqv (iLam xs e) ee'"
shows "\<exists> e'. ee' = iLam xs e' \<and> reneqv e e'"
proof-
  obtain xsa ea ea' where il: "iLam xs e = iLam xsa ea" and ee': "ee' = iLam xsa ea'" 
  and xsa: "super xsa" and r: "reneqv ea ea'" 
  using rr by cases auto

  have u: "uniform (iLam xsa ea)" using rr unfolding uniform_def ee' il by auto
  
  obtain f where f: "bij f" "|supp f| <o |UNIV::ivar set|" "presSuper f" 
  "id_on (FFVars (iLam xsa ea)) f" "id_on (- (dsset xsa \<union> dsset xs)) f" 
  and xsaa: "dsmap f xsa = xs" and e: "e = rrename f ea"
  using iLam_inject_super[OF u il[symmetric] xsa xs] by auto

  have ff: "f ` (dsset xsa) = dsset xs" by (simp add: f(1) f(2) xsaa[symmetric])

  have "FFVars (iLam xs e) \<inter> dsset xs = {}" by auto
  hence "FFVars ee' \<inter> dsset xs = {}"  
  using reneqv_touchedSuperT_eq[OF rr] xs unfolding touchedSuperT_def touchedSuper_def by auto
  hence "FFVars ea' \<inter> dsset xs \<subseteq> dsset xsa" unfolding ee' by auto
  hence fv: "FFVars ea' \<inter> dsset xs = {} \<or> xs = xsa"  
  using super_disj[OF xs xsa] by auto


  show ?thesis apply(rule exI[of _ "rrename f ea'"]) apply(intro conjI)
    subgoal unfolding ee' unfolding iLam_inject apply(rule exI[of _ f]) apply(intro conjI)
      subgoal by fact
      subgoal by fact
      subgoal apply simp using f(5) fv unfolding id_on_def by auto
      subgoal by fact
      subgoal .. . 
    subgoal unfolding e using f(1) f(2) f(3) r rrename_reneqv by blast . 
qed

lemma reneqv_iLam_casesR:
assumes xs: "super xs'" and rr: "reneqv ee (iLam xs' e')"
shows "\<exists> e. ee = iLam xs' e \<and> reneqv e e'"
using reneqv_iLam_casesL reneweqv_sym rr xs by blast

lemma reneqv_iApp_casesL:
assumes rr: "reneqv (iApp e1 es2) ee'"
shows "\<exists> e1' es2'. ee' = iApp e1' es2' \<and> reneqv e1 e1' \<and> 
          (\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<longrightarrow> reneqv e e')"
using assms by cases auto

lemma reneqv_iApp_casesR:
assumes rr: "reneqv ee (iApp e1' es2')"
shows "\<exists> e1 es2. ee = iApp e1 es2 \<and> reneqv e1 e1' \<and> 
          (\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<longrightarrow> reneqv e e')"
using assms by cases auto

lemma reneqv_trans:
"reneqv e e' \<Longrightarrow> reneqv e' e'' \<Longrightarrow> reneqv e e''"
proof(induct arbitrary: e'' rule: reneqv.induct)
  case (iVar xs x x')
  then show ?case using reneqv_iVar_casesL[OF iVar(3)]
  using super_disj by (auto intro!: reneqv.iVar) 
next
  case (iLam xs e e')
  then show ?case using reneqv.iLam reneqv_iLam_casesL by blast
next
  case (iApp e1 e1' es2 es2')
  obtain e1'' es2'' where e'': "e'' = iApp e1'' es2''" 
  and 1: "reneqv e1' e1''" 
  and 2: "(\<forall>e e'. {e, e'} \<subseteq> sset es2' \<union> sset es2'' \<longrightarrow> reneqv e e')"
  using reneqv_iApp_casesL[OF iApp(4)] by auto
  show ?case unfolding e'' apply(rule reneqv.iApp)
    subgoal using iApp.hyps(2) 1 by blast
    subgoal using iApp.hyps(3) 2  
    by auto (meson reneweqv_sym snth_sset)+ .
qed

lemma uniform_def3: "uniform e \<longleftrightarrow> reneqv e e"
using reneqv_trans reneweqv_sym uniform_def by blast

end