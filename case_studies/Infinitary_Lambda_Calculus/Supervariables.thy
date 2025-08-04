theory Supervariables 
imports Embed_var_ivar 
begin 


(*****)
(* A bijection between ivar and nat \<times> ivar that "tabulates ivar" *)

lemma card_nat_le_dstream: "|UNIV::nat set| \<le>o |UNIV:: ivar dstream set|"
unfolding card_of_ordLeq[symmetric] apply(rule exI[of _ "Abs_dstream o (smap iVariable) o fromN"])
unfolding inj_def 
by simp (smt (verit) Abs_dstream_inverse injD iVariable_inj 
mem_Collect_eq sdistinct_def2 sdistinct_fromN siterate.sel(1) smap_simps(1) snth_smap)

lemma card_ivar_dstream_nat: "|UNIV:: ivar set| =o |UNIV :: (nat \<times> ivar) set|"
proof-
  have "|UNIV :: (nat \<times> ivar) set| =o |(UNIV::nat set) \<times> (UNIV:: ivar set)|" by auto
  also have "|(UNIV::nat set) \<times> (UNIV:: ivar set)| =o |UNIV:: ivar set|"
  apply(subst card_of_Times_infinite_simps)
  using More_Stream.infinite infinite_iff_card_of_nat
     apply auto[2]
  using Field_natLeq var_class.large apply force
  by (rule TrueI)
  finally show ?thesis using ordIso_symmetric by auto
qed
 
definition tab where "tab \<equiv> SOME (f::ivar \<Rightarrow> nat \<times> ivar). bij f"

lemma bij_tab: "bij tab"
unfolding tab_def 
using card_ivar_dstream_nat unfolding card_of_ordIso[symmetric]  
by (metis tfl_some)

lemma inj_tab: "inj tab" and surj_tab: "surj tab"
using bij_tab unfolding bij_def by auto

lemma tab_inj[simp]: "tab x = tab y \<longleftrightarrow> x = y"
by (simp add: bij_tab bij_implies_inject)

definition "untab \<equiv> inv tab"

lemma bij_untab: "bij untab"
by (simp add: bij_tab untab_def)
lemma inj_untab: "inj untab" and surj_untab: "surj untab"
using bij_untab unfolding bij_def by auto

lemma untab_inj[simp]: "untab x = untab y \<longleftrightarrow> x = y"
by (simp add: bij_untab bij_implies_inject)

lemma tab_untab[simp]: "tab (untab x) = x"
by (simp add: bij_tab untab_def)

lemma untab_tab[simp]: "untab (tab x) = x"
by (simp add: bij_tab untab_def)


lemma dsnth_untab_exhaust: "\<exists>xs. (\<exists>x. \<forall>n. dsnth xs n = untab (n,x)) \<and> y \<in> dsset xs"
proof-
  obtain x n0 where y: "y = untab (n0,x)"  
    by (metis prod.collapse untab_tab)
  define dxs where "dxs \<equiv> smap (\<lambda>n. untab (n, x)) nats"
  have "\<exists>xs. \<forall>n. xs !#! n = untab (n, x)"
  apply(rule inj_ex_dsnth) unfolding inj_def by auto
  thus ?thesis using y    
  by (metis dsnth.rep_eq dsset.rep_eq snth_sset)
qed


(*****)
(* Supervariables *)

definition superOf' where 
"superOf' x \<equiv> SOME xs. \<forall>n. dsnth xs n = untab (n,x)"

lemma superOf': "\<forall>n. dsnth (superOf' x) n = untab (n,x)"
unfolding superOf'_def apply(rule someI_ex)  
by (metis dsnth_untab_exhaust dtheN snd_conv untab_inj) 

lemma superOf'_inj[simp]: "superOf' x = superOf' y \<longleftrightarrow> x = y"
using superOf' by (metis Pair_inject tab_untab)

lemma inj_superOf': "inj superOf'" 
unfolding inj_def by auto

(* *)

definition superOf :: "var \<Rightarrow> ivar dstream" where 
"superOf \<equiv> superOf' o ivarOf"

lemma superOf_inj[simp]: "superOf x = superOf y \<longleftrightarrow> x = y"
unfolding superOf_def by auto

lemma inj_superOf: "inj superOf" 
unfolding inj_def by auto

(* *)

definition super :: "ivar dstream \<Rightarrow> bool" where 
"super xs \<equiv> \<exists>x. \<forall>n. dsnth xs n = untab (n,ivarOf x)"

lemma super_disj:  "super xs \<Longrightarrow> super xs' \<Longrightarrow> xs \<noteq> xs' \<Longrightarrow> dsset xs \<inter> dsset xs' = {}"
unfolding super_def  dsset_range by (auto simp: dstream_eq_nth)

lemma super_superOf[simp]: "super (superOf x)"
by (simp add: superOf' superOf_def super_def)

lemma super_imp_superOf: "super xs \<Longrightarrow> \<exists>x. xs = superOf x"
by (metis Int_emptyD comp_apply dsset_range range_eqI superOf' superOf_def super_def super_disj)

lemma card_super: "|UNIV::var set| =o |{xs . super xs}|"
apply(rule card_of_ordIsoI[of superOf])
unfolding bij_betw_def 
using inj_superOf super_imp_superOf by fastforce

lemma super_countable: "countable {xs . super xs}"
using card_super  
by (meson card_of_nat card_var countable_card_of_nat ordIso_iff_ordLeq ordIso_transitive ordIso_transitive)
 
lemma super_infinite: "infinite {xs . super xs}"
using card_super infinite_var card_of_ordIso_finite by blast

lemma bij_superOf: "bij_betw superOf UNIV {xs. super xs}"
by (smt (verit) UNIV_I bij_betwI' mem_Collect_eq superOf_inj super_imp_superOf super_superOf)

definition subOf where "subOf xs \<equiv> SOME x. superOf x = xs"

lemma superOf_subOf[simp]: "super xs \<Longrightarrow> superOf (subOf xs) = xs"
by (metis (mono_tags, lifting) bij_betw_def bij_superOf imageE mem_Collect_eq someI_ex subOf_def)

lemma subOf_superOf[simp]: "subOf (superOf x) = x"
by (metis (mono_tags, lifting) bij_betw_imp_inj_on bij_superOf inv_f_f someI_ex subOf_def)

lemma subOf_inj[simp]: "super xs \<Longrightarrow> super ys \<Longrightarrow> subOf xs = subOf ys \<longleftrightarrow> xs = ys"
by (metis superOf_subOf)


(* The set of supervariables "touched" by a set, or by an iterm: *)

definition touchedSuper :: "ivar set \<Rightarrow> ivar dstream set" where 
"touchedSuper X \<equiv> {xs. super xs \<and> X \<inter> dsset xs \<noteq> {}}"

lemma touchedSuper_emp[simp,intro!]: "touchedSuper {} = {}"
unfolding touchedSuper_def by auto

lemma touchedSuper_mono: "X \<subseteq> Y \<Longrightarrow> touchedSuper X \<subseteq> touchedSuper Y"
using disjoint_iff unfolding touchedSuper_def by auto

lemma touchedSuper_Union: 
"touchedSuper (\<Union> (F ` I)) = (\<Union>i\<in>I. touchedSuper (F i))"
unfolding touchedSuper_def by auto

lemma touchedSuper_UN: "touchedSuper (\<Union> XX) = \<Union> (touchedSuper  ` XX)"
unfolding touchedSuper_def apply auto .

lemma touchedSuper_UN': 
"touchedSuper (\<Union> KK) = \<Union> {touchedSuper K | K . K \<in> KK}"
unfolding touchedSuper_def by auto

definition touchedSuperT :: "itrm \<Rightarrow> ivar dstream set" where 
"touchedSuperT t \<equiv> touchedSuper (FFVars t)"

lemma touchedSuper_iVar_singl: "touchedSuperT (iVar x) = {} \<or> (\<exists>xs. touchedSuperT (iVar x) = {xs})"
proof-
  {fix xs xs' assume "{xs,xs'} \<subseteq> touchedSuperT (iVar x)" and "xs \<noteq> xs'"
   hence False unfolding touchedSuperT_def touchedSuper_def  
     by auto (meson Int_emptyD super_disj)
  }
  thus ?thesis 
    by auto (metis insertI1 insert_absorb subsetI subset_singletonD)
qed

lemma touchedSuper_iVar[simp]: "super xs \<Longrightarrow> x \<in> dsset xs \<Longrightarrow> touchedSuperT (iVar x) = {xs}"
unfolding touchedSuperT_def touchedSuper_def by auto (meson Int_emptyD super_disj)

lemma touchedSuper_iLam[simp]: "super ys \<Longrightarrow> touchedSuperT (iLam ys e) = touchedSuperT e - {ys}"
unfolding touchedSuperT_def touchedSuper_def 
by auto (auto simp: Diff_Int_distrib2 Int_emptyD super_disj)

lemma touchedSuper_iApp[simp]: "touchedSuperT (iApp e es) = touchedSuperT e \<union> \<Union> (touchedSuperT ` (sset es))"
unfolding touchedSuperT_def touchedSuper_def by auto

lemma super_dsset_singl: 
 "super ys \<Longrightarrow> {xs . super xs \<and> dsset ys \<inter> dsset xs \<noteq> {}} = {ys}"
apply safe 
apply (meson Int_emptyD super_disj)
by (simp add: dsset_range)

lemma super_touchedSuper_dsset[simp]: "super xs \<Longrightarrow> touchedSuper (dsset xs) = {xs}"
using super_dsset_singl touchedSuper_def by auto

lemma touchedSuper_dsset_superOf[simp]: "touchedSuper (dsset (superOf x)) = {superOf x}"
by auto

lemma touchedSuper_Un: "touchedSuper (A \<union> A') = touchedSuper A \<union> touchedSuper A'"
unfolding touchedSuper_def by auto





(* The notion of a function preserving supervariables: *)
definition "presSuper \<sigma> \<equiv> \<forall>xs. super xs \<longleftrightarrow> super (dsmap \<sigma> xs)"  

(* *)

lemma touchedSuperT_irrename[simp]: 
"bij f \<and> |supp f| <o |UNIV::ivar set| \<Longrightarrow> presSuper f \<Longrightarrow> 
 touchedSuperT (irrename f e) = (dsmap f) ` (touchedSuperT e)"
unfolding touchedSuperT_def touchedSuper_def image_def 
by auto (smt (verit, ccfv_threshold) Int_emptyD bij_betw_inv_into dstream.map_comp dstream.map_id 
dstream.set_map image_in_bij_eq inv_inv_eq inv_o_simp1 presSuper_def supp_inv_bound)+ 



lemma presSuper_id[simp,intro]: "presSuper id"
unfolding presSuper_def by auto

lemma presSuper_comp: 
"bij f \<Longrightarrow> |supp f| <o |UNIV::ivar set| \<Longrightarrow> presSuper f \<Longrightarrow> 
 bij g \<Longrightarrow> |supp g| <o |UNIV::ivar set| \<Longrightarrow> presSuper g \<Longrightarrow> 
 presSuper (g o f)"
unfolding presSuper_def by (auto simp: dstream.map_comp[symmetric])

lemma presSuper_inv: 
"bij f \<Longrightarrow> |supp f| <o |UNIV::ivar set| \<Longrightarrow> presSuper f \<Longrightarrow> presSuper (inv f)"
by (metis bij_bij_betw_inv dstream.map_comp inv_o_simp2 presSuper_def presSuper_id supp_inv_bound)

lemma touchedSuper_supp_comp: 
"touchedSuper (supp (g \<circ> f)) \<subseteq> touchedSuper (supp g) \<union> touchedSuper (supp f)"
unfolding touchedSuper_def using supp_o by fastforce

lemma touchedSuper_image: 
"bij f \<Longrightarrow> |supp f| <o |UNIV::ivar set| \<Longrightarrow> presSuper f \<Longrightarrow> 
touchedSuper (f ` A) = (dsmap f) ` (touchedSuper A)"
unfolding touchedSuper_def apply safe  
  subgoal for xs _ a  unfolding image_def apply simp  
    by (smt (verit) Int_emptyD bij_betw_inv_into dstream.map_comp 
    dstream.map_id dstream.set_map 
    image_in_bij_eq inv_inv_eq inv_o_simp2 presSuper_def supp_inv_bound)
  subgoal unfolding presSuper_def by (auto simp: image_def dssset_dsmap' presSuper_def) 
  subgoal unfolding presSuper_def by (auto simp: image_def dssset_dsmap' presSuper_def) .

lemma touchedSuper_supp_inv: 
"bij f \<Longrightarrow> |supp f| <o |UNIV::ivar set| \<Longrightarrow> presSuper f \<Longrightarrow> 
touchedSuper (supp (inv f)) = dsmap f ` (touchedSuper (supp f))"
unfolding supp_inv by (simp add: touchedSuper_image)

(* *)

lemma touchedSuper_IImsupp_imkSubst: 
"super xs \<Longrightarrow> touchedSuper (IImsupp (imkSubst xs es)) \<subseteq> {xs} \<union> touchedSuper (\<Union> (FFVars ` (sset es)))"
unfolding touchedSuper_def IImsupp_def SSupp_def imkSubst_def apply auto 
apply (meson disjoint_iff imkSubst_idle super_disj)
apply (metis Int_emptyD UN_I snth_sset) . 





(* *)


lemma extend_super1: 
assumes xs: "super xs" and ys: "super ys" and 
A: "|A| <o |UNIV::ivar set|" "finite (touchedSuper A)" "A \<inter> dsset ys = {}"
and A': "A' \<subseteq> A" "dsset xs \<inter> A' = {}"
and f: "bij_betw f (dsset xs) (dsset ys)" "dsmap f xs = ys" 
shows "\<exists>\<rho>. bij (\<rho>::ivar\<Rightarrow>ivar) \<and> |supp \<rho>| <o |UNIV::ivar set| \<and> finite (touchedSuper (supp \<rho>)) \<and> 
   presSuper \<rho> \<and> \<rho> ` (dsset xs) \<inter> A = {} \<and> 
   id_on A' \<rho> \<and> id_on (- (dsset xs \<union> dsset ys)) \<rho> \<and> eq_on (dsset xs) \<rho> f \<and> 
   id_on (dsset xs) (\<rho> o \<rho>)"
proof- 
  obtain g where g: "bij_betw g (dsset ys) (dsset xs)" "dsmap g ys = xs" using ex_dsmap by auto
  define \<rho> where "\<rho> \<equiv> \<lambda>z. if z \<in> dsset xs then f z else if z \<in> dsset ys then g z else z"
  have i: "inj_on f (dsset xs)" "inj_on g (dsset ys)" using f(1) g(1) unfolding bij_betw_def by auto
  have s: "supp \<rho> \<subseteq> dsset xs \<union> dsset ys"   
    unfolding \<rho>_def supp_def by auto 
  hence ss: "touchedSuper (supp \<rho>) \<subseteq> touchedSuper (dsset xs) \<union> touchedSuper (dsset ys)"
    unfolding touchedSuper_def by auto
  have io: "id_on (- (dsset xs \<union> dsset ys)) \<rho>" 
  unfolding \<rho>_def id_on_def by auto
  have 0: "dsmap \<rho> xs = ys" "dsmap \<rho> ys = xs"
    subgoal unfolding \<rho>_def using f(1) f(2) dsset_range apply(intro dsnth_dsmap_cong) 
    apply auto using dsmap_alt i(1) by auto 
    subgoal unfolding \<rho>_def using g(1) g(2) dsset_range apply(intro dsnth_dsmap_cong) 
    using i 
    by auto (metis Int_emptyD dsnth_dsmap f(2) i(1) rangeI super_disj xs ys) .

  have 1: "\<And>zs. super zs \<Longrightarrow> zs \<notin> {xs,ys} \<Longrightarrow> dsmap \<rho> zs = zs"
  unfolding \<rho>_def apply(intro dsnth_dsmap_cong) unfolding id_on_def apply auto 
  apply (metis Int_emptyD dsset_range rangeI super_disj ys)
  apply (metis Int_emptyD dsset_range rangeI super_disj ys(1))  
  by (metis Int_emptyD dsset_range rangeI super_disj xs)

  show ?thesis apply(rule exI[of _ \<rho>], intro conjI)
    subgoal using f g unfolding bij_def inj_def surj_def bij_betw_def inj_on_def apply auto 
      apply (smt (verit, ccfv_SIG) Int_emptyD ys(1) \<rho>_def image_iff super_disj xs)
      apply (smt (verit, del_insts) Int_emptyD \<rho>_def bij_betw_iff_bijections f(1) g(1) super_disj xs ys(1)) .
    subgoal using s by (simp add: card_dsset_ivar card_of_subset_bound infinite_class.Un_bound)
    subgoal using ss by (simp add: finite_subset xs ys)
    subgoal unfolding presSuper_def apply clarify subgoal for zs  
    apply(cases "zs \<in> {xs,ys}")
      subgoal using 0 ys(1) xs by auto
      subgoal using 1  
      by simp (smt (verit, ccfv_threshold) "0"(1) "0"(2) \<open>bij \<rho>\<close> bij_implies_inject dsnth_dsmap dsnth_dsmap_cong inj_onI) . .
    subgoal unfolding \<rho>_def apply auto 
      by (meson Int_emptyD assms(5) bij_betw_apply f(1)) 
    subgoal unfolding id_on_def \<rho>_def 
      using assms(5) assms(6) assms(7) by auto 
    subgoal by fact
    subgoal unfolding \<rho>_def eq_on_def by auto 
    subgoal unfolding \<rho>_def id_on_def apply simp 
      by (metis bij_betw_apply dsnth_dsmap dtheN f(1) f(2) g(2) i(1) i(2) 
       singleton_insert_inj_eq touchedSuper_iVar xs ys) .
qed

lemma extend_super2: 
assumes xs: "super xs" and ys: "super ys" and 
A: "|A| <o |UNIV::ivar set|" "finite (touchedSuper A)" "A \<inter> dsset xs = {}" "A \<inter> dsset ys = {}"
and f: "bij_betw f (dsset xs) (dsset ys)" "dsmap f xs = ys" 
shows "\<exists>\<rho>. bij (\<rho>::ivar\<Rightarrow>ivar) \<and> |supp \<rho>| <o |UNIV::ivar set| \<and> finite (touchedSuper (supp \<rho>)) \<and>
   presSuper \<rho> \<and> \<rho> ` (dsset xs) \<inter> A = {} \<and> 
   id_on A \<rho> \<and> id_on (- (dsset xs \<union> dsset ys)) \<rho> \<and> eq_on (dsset xs) \<rho> f \<and> 
   id_on (dsset xs) (\<rho> o \<rho>)"
apply(rule extend_super1) using assms by auto

lemma extend_super: 
assumes xs: "super xs" and A: "|A| <o |UNIV::ivar set|" "finite (touchedSuper A)" and A': "A' \<subseteq> A" "dsset xs \<inter> A' = {}"
shows "\<exists>\<rho>. bij (\<rho>::ivar\<Rightarrow>ivar) \<and> |supp \<rho>| <o |UNIV::ivar set| \<and> presSuper \<rho> \<and> \<rho> ` (dsset xs) \<inter> A = {} \<and> id_on A' \<rho> \<and> 
           id_on (dsset xs) (\<rho> o \<rho>)"
proof- 
  obtain ys where ys: "super ys" "A \<inter> dsset ys = {}" "ys \<noteq> xs"
    by (smt (verit, del_insts) assms(3) finite.simps insert_subset mem_Collect_eq set_eq_subset subset_eq super_infinite touchedSuper_def)

  obtain f where f: "bij_betw f (dsset xs) (dsset ys)" "dsmap f xs = ys" "id_on (- dsset xs) f" using ex_dsmap by auto
  obtain g where g: "bij_betw g (dsset ys) (dsset xs)" "dsmap g ys = xs" "id_on (- dsset ys) g" using ex_dsmap by auto
  define \<rho> where "\<rho> \<equiv> \<lambda>z. if z \<in> dsset xs then f z else if z \<in> dsset ys then g z else z"
  have i: "inj_on f (dsset xs)" "inj_on g (dsset ys)" using f(1) g(1) unfolding bij_betw_def by auto
  have s: "supp \<rho> \<subseteq> supp f \<union> supp g"  "supp f \<subseteq> dsset xs"  "supp g \<subseteq> dsset ys" 
    subgoal unfolding \<rho>_def supp_def by auto
    subgoal using f(3) unfolding supp_def id_on_def by auto
    subgoal using g(3) unfolding supp_def id_on_def by auto .
  have 0: "dsmap \<rho> xs = ys" "dsmap \<rho> ys = xs"
    subgoal unfolding \<rho>_def using f(1) f(2) dsset_range apply(intro dsnth_dsmap_cong) 
    apply auto using dsmap_alt i(1) by auto 
    subgoal unfolding \<rho>_def using g(1) g(2) dsset_range apply(intro dsnth_dsmap_cong) 
    using i by auto (metis Int_emptyD bij_betw_apply g(1) rangeI super_disj xs ys(1) ys(3)) .

  have 1: "\<And>zs. super zs \<Longrightarrow> zs \<notin> {xs,ys} \<Longrightarrow> dsmap \<rho> zs = zs"
  unfolding \<rho>_def apply(intro dsnth_dsmap_cong) using f(3) g(3) unfolding id_on_def apply auto 
  apply (meson Int_emptyD super_disj xs ys(1) ys(3)) 
  apply (metis Int_emptyD dsset_range rangeI super_disj ys(1))  
  by (metis Int_emptyD dsset_range rangeI super_disj xs)

  show ?thesis apply(rule exI[of _ \<rho>], intro conjI)
    subgoal using f g unfolding bij_def inj_def surj_def bij_betw_def inj_on_def apply auto 
      apply (smt (verit, ccfv_SIG) Int_emptyD ys(1) \<rho>_def image_iff super_disj xs)
      apply (smt (verit, del_insts) Int_emptyD \<rho>_def bij_betw_iff_bijections f(1) g(1) super_disj xs ys(1)) .
    subgoal using s by (simp add: card_dsset_ivar card_of_subset_bound infinite_class.Un_bound)
    subgoal unfolding presSuper_def apply clarify subgoal for zs  
    apply(cases "zs \<in> {xs,ys}")
      subgoal using 0 ys(1) xs by auto
      subgoal using 1  
      by simp (smt (verit, ccfv_threshold) "0"(1) "0"(2) \<open>bij \<rho>\<close> bij_implies_inject dsnth_dsmap dsnth_dsmap_cong inj_onI) . .
    subgoal unfolding \<rho>_def 
      by auto (meson Int_emptyD bij_betw_apply f(1) ys(2))
    subgoal unfolding id_on_def \<rho>_def 
      using assms(4) assms(5) ys(2) by auto 
    subgoal using f unfolding id_on_def \<rho>_def apply simp 
      by (metis dsnth_dsmap dsset_dsmap dtheN g(2) i(1) i(2) 
       image_eqI singleton_insert_inj_eq touchedSuper_iVar xs ys(1)) .
qed


thm refresh
lemma refresh_super: 
assumes V: " dsset xs \<inter> V = {}" "|V| <o |UNIV::ivar set|" 
  "finite (touchedSuper V)"
and xs: "super xs"  
shows "\<exists>f. bij (f::ivar\<Rightarrow>ivar) \<and> |supp f| <o |UNIV::ivar set| \<and> 
           dsset (dsmap f xs) \<inter> V = {} \<and>
           id_on V f \<and> presSuper f"
using extend_super[OF xs V(2) V(3) _ V(1), simplified]
apply safe subgoal for \<rho> apply(intro exI[of _ \<rho>]) 
unfolding id_on_def by auto .


(* *)

(* the range of supervariables: *)
definition "RSuper \<equiv> \<Union> (dsset ` (range superOf))"

lemma super_dsset_RSuper: "super xs \<Longrightarrow> dsset xs \<subseteq> RSuper"
by (metis RSuper_def UN_iff range_eqI subsetI superOf_subOf)

lemma RSuper_def2: "RSuper = \<Union> (dsset ` {xs. super xs})"
unfolding RSuper_def apply auto 
  using super_superOf apply blast  
  by (metis superOf_subOf)

definition theSN where 
"theSN x \<equiv> SOME xs_i. super (fst xs_i) \<and> x = dsnth (fst xs_i) (snd xs_i)"

lemma theSN': "x \<in> RSuper \<Longrightarrow> super (fst (theSN x)) \<and> x = dsnth (fst (theSN x)) (snd (theSN x))"
unfolding theSN_def RSuper_def apply(rule someI_ex)  
by simp (metis dtheN super_superOf)  

lemma theSN: "x \<in> RSuper \<Longrightarrow> (xs,i) = theSN x \<Longrightarrow> super xs \<and> dsnth xs i = x"
by (metis fst_conv snd_conv theSN')

lemma theSN_unique: 
"x \<in> RSuper \<Longrightarrow> (xs,i) = theSN x \<Longrightarrow> super ys \<and> dsnth ys j = x \<Longrightarrow> ys = xs \<and> j = i"
by (metis Int_emptyD dsset_range dtheN_dsnth rangeI super_disj theSN) 

lemma theSN_ex: "super xs \<Longrightarrow> \<exists> x \<in> RSuper. (xs,i) = theSN x"
by (metis (full_types) RSuper_def Union_iff dsset_range imageI rangeI super_imp_superOf surjective_pairing theSN_unique)

(* This summarizes the only properties we are interested in about theSN, 
which in turn will be used to prove the correctness of the supervariable-based 
renaming extension. 
It ways that theSN is a bijection between 
(1) the set of all variables that appear in supervariables 
and 
(2) the pairs (xs,n) indicating specific supervariables xs and positions n (where the 
variable is located)
*)

lemma bij_theSN: 
"bij_betw theSN RSuper ({xs. super xs} \<times> (UNIV::nat set))"
unfolding bij_betw_def inj_on_def apply auto
  apply (metis theSN')
  apply (meson UnionI imageI rangeI theSN)
  by (metis imageI theSN_ex)

lemma super_subOf_theN_eq: "super xs \<Longrightarrow> super ys \<Longrightarrow> x \<in> dsset ys \<Longrightarrow> subOf (fst (theSN x)) = subOf xs \<Longrightarrow> xs = ys"
by (metis dtheN prod.collapse subsetD superOf_subOf super_dsset_RSuper theSN_unique)


(* *)

lemma iLam_inject_super: 
assumes u: "finite (touchedSuperT e)" and 
eq: "iLam xs e = iLam xs' e'" and super: "super xs" "super xs'"
shows "\<exists>f. bij f \<and> |supp f| <o |UNIV::ivar set| \<and> presSuper f \<and> finite (touchedSuper (supp f)) \<and> 
       id_on (ILC.FFVars (iLam xs e)) f \<and> id_on (- (dsset xs \<union> dsset xs')) f \<and> 
       id_on (dsset xs) (f o f) \<and>
       dsmap f xs = xs' \<and> irrename f e = e'"
proof(cases "xs = xs'")
  case True
  thus ?thesis apply(intro exI[of _ id]) 
  apply (auto simp add: presSuper_def) 
  using eq iLam_same_inject unfolding touchedSuper_def supp_def by auto
next
  case False
  hence ds: "dsset xs \<inter> dsset xs' = {}" using super  
    using super_disj by blast
  obtain f where f: "bij f \<and> |supp f| <o |UNIV::ivar set| \<and> id_on (FFVars (iLam xs e)) f \<and> 
     id_on (dsset xs) (f \<circ> f) \<and> 
     dsmap f xs = xs' \<and> irrename f e = e'" using iLam_inject_strong[OF eq ds] by auto
  hence i: "inj_on f (dsset xs)" unfolding bij_def inj_on_def by auto
  define A where A: "A = FFVars (iLam xs e)"
  have 0: "|A| <o |UNIV::ivar set|" "finite (touchedSuper A)" "A \<inter> dsset xs = {}"
     "A \<inter> dsset xs' = {}" "bij_betw f (dsset xs) (dsset xs')" "dsmap f xs = xs'"
    subgoal unfolding A using iterm.set_bd_UNIV by blast
    subgoal unfolding A using touchedSuperT_def u  
      using super(1) touchedSuper_iLam by auto
    subgoal unfolding A by auto
    subgoal unfolding A eq by auto
    subgoal using f unfolding bij_def bij_betw_def inj_on_def using i by auto
    subgoal using f by auto .
  show ?thesis using extend_super2[OF super 0] apply safe
  subgoal for g apply(rule exI[of _ g]) using f unfolding A eq_on_def id_on_def 
    by simp (metis dstream.map_cong iterm.permute_cong) .
qed


end 