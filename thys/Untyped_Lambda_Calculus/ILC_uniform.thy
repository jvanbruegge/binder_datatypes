(* Here we instantiate the general enhanced rule induction to the "reneqv" predicate from Mazza  *)
theory ILC_uniform
imports ILC_Renaming_Equivalence 
begin


definition uniform :: "ivar iterm \<Rightarrow> bool" 
where "uniform e \<equiv> \<exists>e'. reneqv e e'" 

lemma uniform_finite_touchedUponT: "uniform e \<Longrightarrow> finite (touchedSuperT e)"
using reneqv_finite_touchedSuperT uniform_def by blast

(* Symmetry follows by normal induction: *)
lemma reneqv_sym:
"reneqv e e' \<Longrightarrow> reneqv e' e"
apply(induct rule: reneqv.induct) 
by (auto intro!: reneqv.intros)  

lemma uniform_def2: "uniform e \<longleftrightarrow> (\<exists>e'. reneqv e' e)"
unfolding uniform_def using reneqv_sym by auto

(* But to prove transitivity we will need inversion rules, which for the lambda case
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



lemma uniform_iLam_inject_super: 
assumes u: "uniform (iLam xs e)" and eq: "iLam xs e = iLam xs' e'" and super: "super xs" "super xs'"
shows "\<exists>f. bij f \<and> |supp f| <o |UNIV::ivar set| \<and> presSuper f \<and> finite (touchedSuper (supp f)) \<and>
       id_on (ILC.FFVars (iLam xs e)) f \<and> id_on (- (dsset xs \<union> dsset xs')) f \<and> 
       id_on (dsset xs) (f o f) \<and> dsmap f xs = xs' \<and> irrename f e = e'"
apply(rule iLam_inject_super) using assms  
by (metis finite_Diff2 finite_singleton touchedSuper_iLam uniform_finite_touchedUponT, auto)


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
  and xsaa: "dsmap f xsa = xs" and e: "e = irrename f ea"
  using uniform_iLam_inject_super[OF u il[symmetric] xsa xs] by auto

  have ff: "f ` (dsset xsa) = dsset xs" by (simp add: f(1) f(2) xsaa[symmetric])

  have "FFVars (iLam xs e) \<inter> dsset xs = {}" by auto
  hence "FFVars ee' \<inter> dsset xs = {}"  
  using reneqv_touchedSuperT_eq[OF rr] xs unfolding touchedSuperT_def touchedSuper_def by auto
  hence "FFVars ea' \<inter> dsset xs \<subseteq> dsset xsa" unfolding ee' by auto
  hence fv: "FFVars ea' \<inter> dsset xs = {} \<or> xs = xsa"  
  using super_disj[OF xs xsa] by auto

  show ?thesis apply(rule exI[of _ "irrename f ea'"]) apply(intro conjI)
    subgoal unfolding ee' unfolding iLam_inject apply(rule exI[of _ f]) apply(intro conjI)
      subgoal by fact
      subgoal by fact
      subgoal apply simp using f(5) fv unfolding id_on_def by auto
      subgoal by fact
      subgoal .. . 
    subgoal unfolding e using f(1) f(2) f(3) r irrename_reneqv by blast . 
qed

lemma reneqv_iLam_casesR:
assumes xs: "super xs'" and rr: "reneqv ee (iLam xs' e')"
shows "\<exists> e. ee = iLam xs' e \<and> reneqv e e'"
using reneqv_iLam_casesL reneqv_sym rr xs by blast

lemma reneqv_iLam_iff:
assumes "super xs"
shows "reneqv (iLam xs e) (iLam xs e') \<longleftrightarrow> reneqv e e'"
by (metis assms iLam_same_inject reneqv.iLam reneqv_iLam_casesR)

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

lemma reneqv_iApp_iff:
"reneqv (iApp e1 es2) (iApp e1' es2') \<longleftrightarrow> 
 reneqv e1 e1' \<and> (\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<longrightarrow> reneqv e e')"
apply(subst reneqv.simps) by auto

(* goes by normal induction, once we have the inversion rules: *)
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
    by auto (meson reneqv_sym snth_sset)+ .
qed 

lemma uniform_def3: "uniform e \<longleftrightarrow> reneqv e e"
using reneqv_trans reneqv_sym uniform_def by blast

corollary irrename_uniform:
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" "presSuper f"
and r: "uniform (e::itrm)" 
shows "uniform (irrename f e)"
using assms unfolding uniform_def3 
by (intro irrename_reneqv) auto

(* *)  (* requires strong induction: *)
lemma reneqv_itvsubst:
assumes r: "reneqv e e'" and rr: "\<And>xs x x'. super xs \<Longrightarrow> {x, x'} \<subseteq> dsset xs \<longrightarrow> reneqv (f x) (f' x')" 
and s: "|SSupp f| <o |UNIV::ivar set|" "|SSupp f'| <o |UNIV::ivar set|"
and f: "finite (touchedSuper (IImsupp f))" "finite (touchedSuper (IImsupp f'))"
shows "reneqv (itvsubst f e) (itvsubst f' e')"
proof-
  have ims: "|IImsupp f| <o |UNIV::ivar set|" "|IImsupp f'| <o |UNIV::ivar set|"
  using s ILC.SSupp_IImsupp_bound by auto
  have par: "small (IImsupp f \<union> IImsupp f') \<and> bsmall (IImsupp f \<union> IImsupp f')"
  using ims f unfolding small_def   
  using var_stream_class.Un_bound bsmall_Un bsmall_def by blast
  show ?thesis using par r rr proof(induct rule: strong_induct_reneqv')
    case (iVar xs x x')
    then show ?case using s by auto
  next
    case (iLam e e' xs)
    show ?case using iLam apply(subst iterm.subst)
      subgoal using s by auto
      subgoal using s by auto
      apply(subst iterm.subst)
        subgoal using s by auto
        subgoal using s by auto
        subgoal apply(rule reneqv.iLam) by auto .
  next
    case (iApp e1 e1' es2 es2')
    then show ?case apply(subst iterm.subst)
      subgoal using s by auto
      apply(subst iterm.subst)
        subgoal using s by auto
        subgoal apply(rule reneqv.iApp) apply auto  
        by (meson reneqv_trans reneqv_sym)+ .
  qed 
qed

(* *)

definition "reneqvS es es' \<equiv> \<forall>e e'. {e,e'} \<subseteq> sset es \<union> sset es' \<longrightarrow> reneqv e e'"

lemma reneweqvS_sym:
"reneqvS es es' \<Longrightarrow> reneqvS es' es"
unfolding reneqvS_def by auto

lemma reneweqvS_trans:
"reneqvS es es' \<Longrightarrow> reneqvS es' es'' \<Longrightarrow> reneqvS es es''"
unfolding reneqvS_def  using reneqv_trans shd_sset by auto blast+


definition "uniformS es \<equiv> \<exists>es'. reneqvS es es'"

lemma uniformS_def2: "uniformS es \<longleftrightarrow> (\<exists>es'. reneqvS es' es)"
unfolding uniformS_def using reneweqvS_sym by blast

lemma uniformS_def3: "uniformS es \<longleftrightarrow> reneqvS es es"
unfolding uniformS_def using reneweqvS_sym reneweqvS_trans by blast

lemma uniformS_def4: 
"uniformS es = (\<forall>e e'. {e, e'} \<subseteq> sset es \<union> sset es \<longrightarrow> reneqv e e')"
using uniformS_def3[unfolded reneqvS_def] .

lemma uniformS_smap2_iApp_iff: 
"uniformS (smap2 iApp es ess) \<longleftrightarrow> uniformS es \<and> uniformS (sflat ess)"
unfolding uniformS_def4 sset_sflat sset_smap2 unfolding sset_range apply auto
  apply (metis iApp_inject reneqv_iApp_casesR)
  subgoal for i j i' j' apply(erule allE[of _ "iApp (es !! i) (ess !! i)"])
  apply(erule allE[of _ "iApp (es !! i') (ess !! i')"]) apply auto
  using reneqv_iApp_casesR by fastforce
  subgoal by (metis Un_iff insert_subset rangeI reneqv.iApp sset_range) .

lemma uniformS_smap2_iLam_iff:
assumes "super xs"
shows "uniformS (smap (iLam xs) es) \<longleftrightarrow> uniformS es"
using assms unfolding uniformS_def4 by (force simp: image_def reneqv_iLam_iff) 

lemma uniformS_sset_uniform: "uniformS es \<Longrightarrow> e \<in> sset es \<Longrightarrow> uniform e"
using reneqvS_def uniformS_def2 uniform_def3 by auto

lemma uniformS_touchedSuperT_eq: 
"uniformS es \<Longrightarrow> {e,e'} \<subseteq> sset es \<Longrightarrow> touchedSuperT e = touchedSuperT e'"
using reneqvS_def reneqv_touchedSuperT_eq uniformS_def3 by auto

lemma uniformS_touchedSuper_eq: 
"uniformS es \<Longrightarrow> {e,e'} \<subseteq> sset es \<Longrightarrow> touchedSuper (FFVars e) = touchedSuper (FFVars e')"
using uniformS_touchedSuperT_eq touchedSuperT_def by auto

lemma uniformS_touchedSuper: 
"uniformS es \<Longrightarrow> e \<in> sset es \<Longrightarrow> touchedSuper (\<Union> (FFVars ` (sset es))) = touchedSuper (FFVars e)"
unfolding touchedSuper_UN  
by auto (metis empty_subsetI insert_subset touchedSuperT_def uniformS_touchedSuperT_eq) 

(* *)

lemma uniformS_touchedSuper_IImsupp_imkSubst: 
"super xs \<Longrightarrow> uniformS es \<Longrightarrow> e \<in> sset es \<Longrightarrow> touchedSuper (IImsupp (imkSubst xs es)) \<subseteq> 
 {xs} \<union> touchedSuper (FFVars e)"
using touchedSuper_IImsupp_imkSubst uniformS_touchedSuper by blast

lemma uniformS_touchedSuper_IImsupp_imkSubst':
"super xs \<Longrightarrow> uniformS es \<Longrightarrow> e \<in> sset es \<Longrightarrow> 
  ys \<noteq> xs \<Longrightarrow> ys \<notin> touchedSuper (ILC.FFVars e) \<Longrightarrow> 
  ys \<notin> touchedSuper (ILC.IImsupp (imkSubst xs es))"
using uniformS_touchedSuper_IImsupp_imkSubst by auto

lemma uniformS_touchedSuper_IImsupp_imkSubst'':
"super xs \<Longrightarrow> super ys \<Longrightarrow> uniformS es \<Longrightarrow> e \<in> sset es \<Longrightarrow> 
  ys \<noteq> xs \<Longrightarrow> dsset ys \<inter> ILC.FFVars e = {} \<Longrightarrow> 
  dsset ys \<inter> ILC.IImsupp (imkSubst xs es) = {}"
using uniformS_touchedSuper_IImsupp_imkSubst' unfolding touchedSuper_def by blast

lemma super_uniformS_finite_touchedSuper_imkSubst: 
"super xs \<Longrightarrow> uniformS es \<Longrightarrow> finite (touchedSuper (IImsupp (imkSubst xs es)))"
by (metis finite_insert insert_is_Un rev_finite_subset snth_sset touchedSuperT_def 
touchedSuper_IImsupp_imkSubst uniformS_sset_uniform uniformS_touchedSuper uniform_finite_touchedUponT)



(* *)

(* Mazza Lemma 11: *)
lemma reneqv_imkSubst:
assumes r: "reneqv e e'" and xs: "super xs" and rr: "reneqvS es es'" 
shows "reneqv (itvsubst (imkSubst xs es) e) (itvsubst (imkSubst xs es') e')"
apply(rule reneqv_itvsubst[OF r])
  subgoal by (smt (verit, del_insts) Un_iff imkSubst_def inf.absorb_iff2 inf_bot_right 
     insert_subset reneqv.simps reneqvS_def rr singleton_insert_inj_eq snth_sset touchedSuper_iVar xs)
  subgoal by simp
  subgoal by simp
  subgoal using rr super_uniformS_finite_touchedSuper_imkSubst uniformS_def xs by blast
  subgoal using rr super_uniformS_finite_touchedSuper_imkSubst uniformS_def2 xs by blast .

(* Mazza Lemma 12: *)
lemma uniform_imkSubst:
assumes u: "uniform e" and xs: "super xs" and rr: "uniformS es" 
shows "uniform (itvsubst (imkSubst xs es) e)"
using reneqv_imkSubst rr u uniformS_def3 uniform_def3 xs by blast


(* Inversion/simplification rules for "uniform": *)

lemma uniform_iVar[simp]:
"uniform (iVar x) \<longleftrightarrow> (\<exists>xs. super xs \<and> x \<in> dsset xs)"
unfolding uniform_def3 by (meson bot.extremum iVar insert_subset reneqv_iVar_casesR)

lemma uniform_iLam_iff[simp]:
assumes xs: "super xs" 
shows "uniform (iLam xs e) \<longleftrightarrow> uniform e"
unfolding uniform_def3  
by (meson iLam reneqv_iLam_casesL reneqv_trans reneqv_sym xs)

(* It is impossible to express uniformity in terms of itself alone, 
this is why renaming equivalence was necessary... same as with parametricity etc.*)
lemma uniform_iApp_iff:
"uniform (iApp e es) \<longleftrightarrow> 
 uniform e \<and> (\<forall>e e'. {e,e'} \<subseteq> sset es \<longrightarrow> reneqv e e')"
unfolding uniform_def3 using iApp reneqv_iApp_casesL by fastforce

lemma uniform_iApp_case:
"uniform (iApp e es) \<Longrightarrow>
 uniform e \<and> (\<forall>e' \<in> sset es. uniform e')"
unfolding uniform_iApp_iff unfolding uniform_def3 by auto

(* Other properties: *)

lemma uniform_iLam_imp: "uniform (iLam xs e) \<Longrightarrow> \<exists> xs' e'. super xs' \<and> uniform e' \<and> iLam xs e = iLam xs' e'"
by (smt (verit, del_insts) iterm.distinct(5) iterm.distinct(6) reneqv.simps uniform_def2)

lemma super_bsmall: "super xs \<Longrightarrow> bsmall (dsset xs)"
by (metis bsmall_def finite.emptyI finite_insert super_dsset_singl touchedSuper_def)

lemma uniform_iLam_imp_avoid: 
assumes u: "uniform (iLam xs e)" and A: "small A" "bsmall A"
shows "\<exists> xs' e'. super xs' \<and> uniform e' \<and> iLam xs e = iLam xs' e' \<and> dsset xs' \<inter> A = {}"
proof-
  obtain xs' e' where xs': "super xs'" and e': "uniform e'" and il: "iLam xs e = iLam xs' e'"
  using uniform_iLam_imp[OF u] by auto
  define B where B: "B = A \<union> dsset xs' \<union> FFVars (iLam xs e)"
  have bsB: "bsmall B" unfolding B apply(intro ILC_Renaming_Equivalence.bsmall_Un)
    subgoal by fact
    subgoal using super_bsmall[OF xs'] .
    subgoal using u bsmall_def touchedSuperT_def uniform_finite_touchedUponT by fastforce .
  hence BB: "finite (touchedSuper B)" unfolding bsmall_def by auto
  have BBB: "|B| <o |UNIV::ivar set|"  
    by (metis B ILC2.small_def assms(2) card_dsset_ivar iterm.set_bd_UNIV var_stream_class.Un_bound)
  obtain xs'' where xxs'': "super xs''" "B \<inter> dsset xs'' = {}" 
    by (smt (verit) Collect_cong Int_commute bsB bsmall_def super_infinite touchedSuper_def)
  obtain f where xs'': "xs'' = dsmap f xs'" and f: "bij_betw f (dsset xs') (dsset xs'')" "id_on (- dsset xs') f" 
  by (metis ex_dsmap)
  obtain g where g: "bij g" "|supp g| <o |UNIV::ivar set|"
      "presSuper g" "g ` dsset xs' \<inter> B = {}" "id_on (- dsset xs' \<inter> - dsset xs'') g" 
      "eq_on (dsset xs') g f"
  using extend_super1[OF xs' xxs''(1) BBB BB xxs''(2), of "{}", simplified, OF f(1) xs''[symmetric]]
  by auto

  
  show ?thesis apply(intro exI[of _ xs''] exI[of _ "irrename g e'"], safe)
    subgoal by fact
    subgoal using e' g(1) g(2) g(3) irrename_uniform by presburger
    subgoal unfolding il xs'' iLam_inject apply(rule exI[of _ g], safe)
      subgoal by fact subgoal by fact
      subgoal using g(5) unfolding id_on_def apply simp  
        by (metis B DiffI UnCI disjoint_iff il iterm.set(3) xxs''(2))
      subgoal apply(rule dsmap_cong)
        subgoal by (simp add: g(1) inj_on_def)
        subgoal using bij_betw_def f(1) by blast
        subgoal by (meson eq_on_def g(6)) . .
    subgoal using B xxs''(2) by blast . 
qed
     
lemma iLam_switch_to_super: 
assumes u: "uniform (iApp (iLam xs e1) es2)"
shows 
"\<exists>xs' e1'. super xs' \<and> iLam xs e1 = iLam xs' e1' \<and> 
           itvsubst (imkSubst xs es2) e1 = itvsubst (imkSubst xs' es2) e1' \<and> 
           (\<forall>e\<in>sset es2. dsset xs' \<inter> FFVars e = {})"
proof- 
  obtain e2 where e2: "e2 \<in> sset es2" 
    using snth_sset by blast
  
  have uu: "\<And>e. e \<in> sset es2 \<Longrightarrow> uniform e"
  using u uniform_iApp_case by blast
  have u': "uniform (iLam xs e1)" using u uniform_iApp_iff by blast

  have fves2: "touchedSuper (\<Union> (FFVars ` (sset es2))) = touchedSuper (FFVars e2) "  
    by (metis e2 iApp_inject reneqvS_def reneqv_iApp_casesL u uniformS_def3 uniformS_touchedSuper uniform_def3)

  have ss: "small (\<Union> (FFVars ` (sset es2)))" 
  unfolding small_def apply(rule var_prod_class.UN_bound)
    subgoal by (simp add: countable_card_ivar countable_sset)
    subgoal using iterm.set_bd_UNIV by blast .

  have bs: "bsmall (\<Union> (FFVars ` (sset es2)))"
  unfolding bsmall_def fves2 unfolding bsmall_def[symmetric]  
  using bsmall_def e2 touchedSuperT_def uniform_finite_touchedUponT uu by presburger

  obtain xs' e1' where xs': "super xs'" and e1': "uniform e1'" and il: "iLam xs e1 = iLam xs' e1'" 
   "dsset xs' \<inter> (\<Union> (FFVars ` (sset es2))) = {}"
  using bs ss u' uniform_iLam_imp_avoid by blast

  obtain f where f: "bij f" "|supp f| <o |UNIV::ivar set|" "id_on (ILC.FFVars (iLam xs e1)) f" 
  "dsmap f xs = xs'" "irrename f e1 = e1'" using il[unfolded iLam_inject] by auto
  
  show ?thesis apply(intro exI[of _ xs'] exI[of _ "irrename f e1"], safe)
    subgoal by fact
    subgoal unfolding il f ..
    subgoal apply(subst irrename_eq_itvsubst_iVar')
      subgoal by fact
      subgoal by fact
      subgoal apply(subst itvsubst_comp)
        subgoal by simp
        subgoal using f(2) by auto
        subgoal apply(rule itvsubst_cong)
          subgoal by simp
          subgoal by (simp add: SSupp_itvsubst_bound f(2))
          subgoal apply simp unfolding f(4)[symmetric] 
            by (metis (full_types) Diff_iff f(1) f(3) f(4) id_on_def il(1) imkSubst_def 
            imkSubst_smap iterm.set(3)) . . .
     subgoal using il(2) by auto .
qed
          
lemma reneqv_head_reduction: 
assumes r: "reneqv (iApp (iLam xs e1) es2) (iApp (iLam ys d1) ds2)"
shows "reneqv (itvsubst (imkSubst xs es2) e1) (itvsubst (imkSubst ys ds2) d1)"
proof-  (* we needed some delicate renaming lemmas, to turn 
   the bound sequences into supervariables, to allow for the nice inversion rules 
  for renaming equivalence to pop up... *)
  have uu: "uniform (iApp (iLam xs e1) es2)" "uniform (iApp (iLam ys d1) ds2)"
  using r using uniform_def uniform_def2 by auto
  obtain xs' e1' where x0: "super xs'" and x1: "iLam xs e1 = iLam xs' e1'"
         and x2: "itvsubst (imkSubst xs es2) e1 = itvsubst (imkSubst xs' es2) e1'"
         and x3: "\<forall>e\<in>sset es2. dsset xs' \<inter> FFVars e = {}"
  using uu iLam_switch_to_super by fastforce
  hence ux': "uniform (iApp (iLam xs' e1') es2)"  
  using uu by auto
  obtain ys' d1' where y0: "super ys'" and y1: "iLam ys d1 = iLam ys' d1'"
         and y2: "itvsubst (imkSubst ys ds2) d1 = itvsubst (imkSubst ys' ds2) d1'"
         and y3: "\<forall>e\<in>sset ds2. dsset ys' \<inter> FFVars e = {}"
  using uu iLam_switch_to_super by fastforce
  hence uy': "uniform (iApp (iLam ys' d1') ds2)"  
  using uu by auto
  have r: "reneqv (iApp (iLam xs' e1') es2) (iApp (iLam ys' d1') ds2)"
  using r x1 y1 by auto 
  hence "reneqv (iLam xs' e1') (iLam ys' d1')" and rr: "\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset ds2 \<longrightarrow> reneqv e e'"
  using reneqv_iApp_casesR by fastforce+
  then obtain ee1' where il: "iLam ys' d1' = iLam xs' ee1'" and r: "reneqv e1' ee1'"
  using reneqv_iLam_casesL x0 by blast
  hence yy1: "iLam ys d1 = iLam xs' ee1'" using y1 by simp

  have itv: "itvsubst (imkSubst xs es2) e1 = itvsubst (imkSubst xs' es2) e1'"
  using iLam_eq_imkSubst[OF x1] .
  have iitv: "itvsubst (imkSubst ys ds2) d1 = itvsubst (imkSubst xs' ds2) ee1'"
  using iLam_eq_imkSubst[OF yy1] . 
  
  show ?thesis unfolding itv iitv apply(rule reneqv_imkSubst)
  using r x0 rr unfolding reneqvS_def by auto
qed

lemma uniform_head_reduction: 
assumes u: "uniform (iApp (iLam xs e1) es2)"
shows "uniform (itvsubst (imkSubst xs es2) e1)"
using assms unfolding uniform_def3 by (elim reneqv_head_reduction) 

(* *)

lemma uniformS_finite_touchedSuperT: 
"uniformS es \<Longrightarrow> finite (\<Union> (touchedSuperT ` (sset es)))"
by (metis Un_absorb equals0I 
finite.emptyI finite_UN infinite_Un touchedSuper_iApp 
uniformS_def4 uniformS_sset_uniform uniform_finite_touchedUponT uniform_iApp_iff)

(* not true (and not claimed by Mazza *)
(*
lemma istep_uniform:
assumes "istep e e'" and "uniform e"
shows "uniform e'"
*)


end