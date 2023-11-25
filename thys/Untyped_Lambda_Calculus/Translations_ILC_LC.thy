(* The translations back and forth between the infinitary and finitary lambda-calculi *)
theory Translations_ILC_LC
imports ILC_uniform ILC_affine ILC_beta
begin


lemma istep_FFVars: "istep e e' \<Longrightarrow> ILC.FFVars e' \<subseteq> ILC.FFVars e"
apply(induct rule: istep.induct) 
by (auto simp: imkSubst_def) (metis in_mono snth_sset snth_supd_diff snth_supd_same theN)

(* *)
lemma tvsubst_affine':
assumes f: "|SSupp f| <o |UNIV::ivar set|" and af: "\<And>x. affine (f x)"
and fv: "\<And>x y. x \<noteq> y \<Longrightarrow> FFVars (f x) \<inter> FFVars (f y) = {}"
and r: "affine (e::itrm)" 
shows "affine (itvsubst f e)"
proof-
  have ims: "|IImsupp f| <o |UNIV::ivar set|"  
  using f ILC.SSupp_IImsupp_bound by auto
  have par: "small (IImsupp f)"
  using ims f unfolding small_def by blast
  show ?thesis using par r proof(induct rule: BE_induct_affine')
    case (iVar x)
    then show ?case using f af by auto
  next
    case (iLam e xs)
    show ?case using iLam apply(subst iterm.subst)
      subgoal using f by auto
      subgoal by auto
      subgoal apply(rule affine.iLam) by auto .
  next
    case (iApp e1 es2)
    then show ?case apply(subst iterm.subst)
      subgoal using f by auto
      subgoal apply(rule affine.iApp) using fv
      by auto (metis Int_emptyD)+ .
  qed 
qed

(* Strengthening the previous result with "{x,y} \<subseteq> FFVars e " 
(which seems to prevent the above proof by induction), otherwise the result is 
not strong enough to instantiate to imakeSubst... *)
lemma tvsubst_affine:
assumes f: "|SSupp f| <o |UNIV::ivar set|" and af: "\<And>x. affine (f x)"
and fv: "\<And>x y. {x,y} \<subseteq> FFVars e \<Longrightarrow> x \<noteq> y \<Longrightarrow> FFVars (f x) \<inter> FFVars (f y) = {}"
and r: "affine (e::itrm)" 
shows "affine (itvsubst f e)"
proof-
  obtain xs and x::ivar where x: "x \<in> dsset xs" 
    using dsset_range by blast 
  define t where "t = iLam xs (iVar x)"
  have t: "FFVars t = {}" "affine t" unfolding t_def using x by (auto intro: affine.intros)
  
  have fve: "\<And>e. |FFVars e| <o |UNIV::ivar set|" 
    by (simp add: iterm.set_bd_UNIV)

  have "|\<Union> ((FFVars o f) ` (FFVars e))| \<le>o |Sigma (FFVars e) (FFVars o f)|"
  by (rule card_of_UNION_Sigma)
  also have "|Sigma (FFVars e) (FFVars o f)| <o |UNIV::ivar set|"
  apply(rule stable_elim)
    subgoal by (metis exists_fresh UNIV_I card_ivar card_of_Field_ordIso card_of_nat 
         finite_iff_ordLess_natLeq natLeq_Card_order ordIso_equivalence(3) ordIso_ordLess_trans 
         ordLess_ordIso_trans stable_cardSuc stable_ordIso1)
    subgoal by fact
    subgoal unfolding o_def using fve . .
  finally have ffv: "|\<Union> ((FFVars o f) ` (FFVars e))| <o |UNIV::ivar set|" . 

  define g where "g \<equiv> \<lambda>x. if x \<in> FFVars e then f x 
                                           else if x \<in> \<Union> ((FFVars o f) ` (FFVars e)) then t 
                                           else iVar x"
  have sg: "SSupp g \<subseteq> FFVars e \<union> \<Union> ((FFVars o f) ` (FFVars e))" unfolding g_def SSupp_def by auto

  have g: "|SSupp g| <o |UNIV::ivar set|" "\<And>x. affine (g x)"
  "\<And>x y. x \<noteq> y \<Longrightarrow> FFVars (g x) \<inter> FFVars (g y) = {}"
     subgoal using sg by (meson card_of_subset_bound ffv fve var_stream_class.Un_bound)
     subgoal by (simp add: af affine.iVar g_def t(2)) 
     subgoal using fv unfolding g_def by (simp add: fv t(1)) . 

  have 0: "itvsubst f e = itvsubst g e" apply(rule itvsubst_cong)
    using f g unfolding g_def by auto

  show ?thesis unfolding 0
  using tvsubst_affine'[OF g r] by simp
qed
     
lemma imkSubst_affine:
assumes r: "affine e" and 
fv: "\<And>e1. e1 \<in> sset es \<Longrightarrow> affine e1 \<and> FFVars e \<inter> FFVars e1 = {}"
"\<And>i j. i \<noteq> j \<Longrightarrow> FFVars (snth es i) \<inter> FFVars (snth es j) = {}"
shows "affine (itvsubst (imkSubst xs es) e)"
apply(rule tvsubst_affine)
using assms apply auto 
  apply (simp add: imkSubst_def)
  by (metis Int_emptyD dtheN imkSubst_def iterm.set(1) singletonD snth_sset)


(* TO DOCUMENT IN THE PAPER: 
An example where normal induction would not work, but fresh induction with empty parameters 
is helpful -- namely, the "bonus" freshness assumption allows us to assume xs fresh for es, 
which is crucial in the beta case. *)
lemma istep_affine:
assumes "istep e e'" and "affine e"
shows "affine e'"
proof-
  have "small {}" by simp
  thus ?thesis using assms apply(induct rule: BE_induct_istep')
    subgoal for xs e1 es2 apply(rule imkSubst_affine)
    unfolding affine_iApp_iff by auto 
    subgoal unfolding affine_iApp_iff using istep_FFVars by fastforce
    subgoal unfolding affine_iApp_iff using istep_FFVars 
    by simp (smt (verit, ccfv_SIG) Int_subset_empty1 More_Stream.theN disjoint_iff snth_sset snth_supd_diff snth_supd_same)
    subgoal by auto . 
qed

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

lemma set_stake: "set (stake i xs) = snth xs ` {..<i}"
unfolding set_conv_nth by force

lemma set_sdrop: "sset (sdrop i xs) = snth xs ` {i ..}"
unfolding sset_range apply auto 
apply (simp add: sdrop_snth) 
by (metis add_diff_inverse_nat not_less rangeI sdrop_snth)


lemma sset_supd[simp]: "sset (supd es i e) = {snth es j | j . j \<noteq> i} \<union> {e}"
unfolding supd_def apply auto unfolding set_sdrop set_stake apply auto
  apply (metis Suc_n_not_le_n snth.simps(2))
  by (metis atLeast_iff imageI lessThan_iff not_less not_less_eq_eq not_less_iff_gr_or_eq 
    sdrop.simps(2) set_sdrop)


lemma uniform_head_reduction: 
assumes u: "uniform (iApp (iLam xs e1) es2)"
shows "uniform (itvsubst (imkSubst xs es2) e1)"
proof- (* we needed some delicate renaming lemmas, to turn 
   the bound sequence into a supervariable *)
  obtain xs' e1' where 0: "super xs'" and 1: "iLam xs e1 = iLam xs' e1'"
         and 2: "itvsubst (imkSubst xs es2) e1 = itvsubst (imkSubst xs' es2) e1'"
         and 3: "\<forall>e\<in>sset es2. dsset xs' \<inter> FFVars e = {}"
    using assms iLam_switch_to_super by fastforce
    hence u: "uniform (iApp (iLam xs' e1') es2)"  
      using assms by auto
    show ?thesis unfolding 2 apply(rule uniform_imkSubst)
      subgoal using u unfolding uniform_iApp_iff uniform_iLam_iff[OF 0] by simp
      subgoal by fact
      subgoal using u unfolding uniform_iApp_iff uniformS_def3  
        by (simp add: reneqvS_def) .
qed

(* not true (and not claimed by Mazza *)
(*
lemma istep_uniform:
assumes "istep e e'" and "uniform e"
shows "uniform e'"
*)


(*******)
(* Translating lambda to (affine, uniform) infinitary-lambda *)

definition theSN where 
"theSN x \<equiv> SOME xs_i. super (fst xs_i) \<and> x = dsnth (fst xs_i) (snd xs_i)"

lemma theSN': "x \<in> \<Union> (dsset ` (range superOf)) \<Longrightarrow> super (fst (theSN x)) \<and> x = dsnth (fst (theSN x)) (snd (theSN x))"
unfolding theSN_def apply(rule someI_ex)  
by simp (metis dtheN super_superOf)  

lemma theSN: "x \<in> \<Union> (dsset ` (range superOf)) \<Longrightarrow> (xs,i) = theSN x \<Longrightarrow> super xs \<and> dsnth xs i = x"
by (metis fst_conv snd_conv theSN')

lemma theSN_unique: 
"x \<in> \<Union> (dsset ` (range superOf)) \<Longrightarrow> (xs,i) = theSN x \<Longrightarrow> super ys \<and> dsnth ys j = x \<Longrightarrow> ys = xs \<and> j = i"
by (metis Int_emptyD dsset_range dtheN_dsnth rangeI super_disj theSN) 

lemma theSN_ex: "super xs \<Longrightarrow> \<exists> x \<in> \<Union> (dsset ` (range superOf)). (xs,i) = theSN x "
by (metis (full_types) Union_iff dsset_range imageI rangeI super_imp_superOf surjective_pairing theSN_unique)

(* The summarizes the only properties we are interested in about theSN, 
which in turn will be used to prove the correctness of the supervariable-based 
renaming extension: *)
lemma bij_theSN: 
"bij_betw theSN (\<Union> (dsset ` (range superOf))) ({xs. super xs} \<times> (UNIV::nat set))"
unfolding bij_betw_def inj_on_def apply auto
  apply (metis dtheN fst_conv snd_conv super_superOf theSN' theSN_ex)
  apply (meson UnionI imageI rangeI theSN)
  by (metis UN_simps(10) imageI theSN_ex)

(* Extending a renaming on variables to one on ivariables via "superOf"; 
essentially, renaming is applied in block to all "super-variables", 
and those ivars that do not participate in supervariables are left unchanged.
*)
definition ext :: "(var \<Rightarrow> var) \<Rightarrow> ivar \<Rightarrow> ivar" where 
"ext f x \<equiv> if x \<in> \<Union> (dsset ` (range superOf)) 
   then let (xs,i) = theSN x in dsnth (superOf (f (subOf xs))) i
   else x"

lemma bij_ext: "bij f \<Longrightarrow> bij (ext f)" 
unfolding bij_def inj_on_def surj_def ext_def apply (auto split: prod.splits simp: image_def)
apply (smt (verit, ccfv_SIG) UN_I comp_apply dtheN inj_image_mem_iff inj_onD inj_untab prod.inject range_eqI 
           subOf_superOf superOf' superOf_def super_superOf theSN_unique)
apply (metis dsset_range range_eqI)  
apply (metis dsset_range rangeI)  
by (metis dsset_range dtheN fst_conv range_eqI snd_conv subOf_superOf super_superOf theSN' theSN_ex)
  
lemma supp_ext: "supp (ext f) \<subseteq> {x. \<exists>xs. x \<in> dsset xs \<and> super xs \<and> subOf xs \<in> supp f}"
unfolding supp_def  apply auto 
by (smt (verit, del_insts) case_prod_conv dsset_range ext_def prod.collapse range_eqI superOf_subOf theSN')

lemma supp_ext': "supp (ext f) \<subseteq> \<Union> (dsset ` ({xs . super xs} \<inter> subOf -` (supp f)))"
using supp_ext by fastforce

lemma card_supp_ext: 
assumes "|supp f| <o |UNIV::var set|"
shows "|supp (ext f)| <o |UNIV::ivar set|"
proof-
  have "|supp (ext f)| \<le>o |\<Union> (dsset ` ({xs . super xs} \<inter> subOf -` (supp f)))|"
  using supp_ext' card_of_mono1 by blast
  also have "|\<Union> (dsset ` ({xs . super xs} \<inter> subOf -` (supp f)))| \<le>o 
             |Sigma ({xs . super xs} \<inter> subOf -` (supp f)) dsset|"
  using card_of_UNION_Sigma .
  also have "|Sigma ({xs . super xs} \<inter> subOf -` (supp f)) dsset| \<le>o |UNIV::var set|"
  apply(rule card_of_Sigma_ordLeq_infinite)
    subgoal by (simp add: infinite_var)
    subgoal by (metis Int_left_absorb bij_betw_def bij_superOf inf_le2 le_inf_iff surj_imp_ordLeq) 
    subgoal using dsset_natLeq card_var ordIso_iff_ordLeq ordLeq_transitive by blast .
  also have "|UNIV::var set| <o |UNIV::ivar set|" 
    using card_var_ivar .
  finally show ?thesis .
qed

(* *)

consts tr :: "trm \<Rightarrow> nat list \<Rightarrow> itrm"

axiomatization where 
tr_Var[simp]: "tr (Var x) p = iVar (dsnth (superOf x) (natOf p))"
and 
tr_Lam[simp]: "tr (Lam x e) p = iLam (superOf x) (tr e p)"
and 
tr_App[simp]: "tr (App e1 e2) p = iApp (tr e1 (p @ [0])) (smap (\<lambda>n. tr e2 (p @ [Suc n])) nats)"

lemma FFVars_tr: 
"{subOf xs | xs . dsset xs \<inter> ILC.FFVars (tr e p) \<noteq> {}} \<subseteq> LC.FFVars e"
sorry
  
lemma rrename_tr:
assumes "bij f" and "|supp f| <o |UNIV::var set|"
shows "tr (rrename f e) p = irrename (ext f) (tr e p)"
sorry


end 
