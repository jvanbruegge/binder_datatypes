(* Here we instantiate the general enhanced rule induction to the "affine" predicate from Mazza  *)
theory ILC_affine
imports ILC2 "Prelim.Curry_LFP"
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

lemma Tvars_dsset: "(iFV t - dsset xs) \<inter> dsset xs = {}" "|iFV t - dsset xs| <o |UNIV::ivar set|"
apply auto using card_of_minus_bound iterm.set_bd_UNIV by blast

inductive affine  :: "itrm \<Rightarrow> bool" where
 iVr[simp,intro!]: "affine (iVr x)"
|iLm: "affine e \<Longrightarrow> affine (iLm xs e)"
|iAp:
"affine e1 \<Longrightarrow>
 (\<And>e2. e2 \<in> sset es2 \<Longrightarrow> affine e2) \<Longrightarrow>
 (\<And>e2. e2 \<in> sset es2 \<Longrightarrow> iFV e1 \<inter> iFV e2 = {}) \<Longrightarrow>
 (\<And>i j. i \<noteq> j \<Longrightarrow> iFV (snth es2 i) \<inter> iFV (snth es2 j) = {})
 \<Longrightarrow>
 affine (iAp e1 es2)"

binder_inductive affine
  subgoal premises prems for R B t
    using prems(2-)
     apply safe
    subgoal for x
      apply(rule exI[of _ "{}"])
      apply(intro conjI)
      subgoal by simp
      subgoal unfolding isPerm_def small_def by auto
      done
    subgoal for e xs
      using refresh[OF Tvars_dsset, of xs t] apply safe
      subgoal for f
        apply(rule exI[of _ "f ` (dsset xs)"])
        apply(intro conjI)
        subgoal by simp
        subgoal apply(rule disjI3_2)
          apply(rule exI[of _ "irrename f e"])
          apply(rule exI[of _ "dsmap f xs"])
          apply simp
          subgoal apply(subst iLm_irrename[of "f"]) unfolding id_on_def by auto . . .
        (* *)
    subgoal for e1 es2
      apply(rule exI[of _ "{}"])
      apply(intro conjI)
      subgoal by simp
      subgoal apply(rule disjI3_3)
        apply(rule exI[of _ "e1"])
        apply(rule exI[of _ "es2"])
        apply simp . . .
  done

thm affine.strong_induct
thm affine.equiv

(* ... and equivariance gives us a nice iLm inversion rule: *)

lemma affine_App_case:
"affine (iAp e1 es2) \<Longrightarrow>
 affine e1 \<and>
 (\<forall>e2. e2 \<in> sset es2 \<longrightarrow> affine e2 \<and> iFV e1 \<inter> iFV e2 = {}) \<Longrightarrow>
 (\<forall>i j. i \<noteq> j \<longrightarrow> iFV (snth es2 i) \<inter> iFV (snth es2 j) = {})"
apply(subst (asm) affine.simps) by auto

lemma affine_iApp_iff:
"affine (iAp e1 es2) \<longleftrightarrow>
 (affine e1 \<and>
  (\<forall>e2. e2 \<in> sset es2 \<longrightarrow> affine e2 \<and> iFV e1 \<inter> iFV e2 = {}) \<and>
  (\<forall>i j. i \<noteq> j \<longrightarrow> iFV (snth es2 i) \<inter> iFV (snth es2 j) = {}))"
apply(subst affine.simps) by auto

lemma affine_iLm_case:
assumes "affine (iLm xs e)"
shows "affine e"
proof-
  obtain xs' e' where 0: "iLm xs e = iLm xs' e'" and "affine e'"
  using assms by (smt (verit, del_insts) affine.cases iterm.distinct(2) iterm.distinct(4))
  thus ?thesis using 0 unfolding iterm.inject
  by (metis iterm.inject(3) affine.equiv)
qed

lemma affine_iLm_iff[simp]:
"affine (iLm xs e) \<longleftrightarrow> affine e"
using affine.simps affine_iLm_case by blast

(* Other properties: *)

(* *)
lemma tvsubst_affine':
assumes f: "|SSupp f| <o |UNIV::ivar set|" and af: "\<And>x. affine (f x)"
and fv: "\<And>x y. x \<noteq> y \<Longrightarrow> iFV (f x) \<inter> iFV (f y) = {}"
and r: "affine (e::itrm)"
shows "affine (itvsubst f e)"
using r proof (binder_induction e avoiding: "IImsupp f" rule: affine.strong_induct)
  case (iLm ea xs)
  show ?case using iLm apply(subst iterm.subst)
      subgoal using f by auto
      subgoal by auto
      subgoal apply(rule affine.iLm) by auto .
next
  case (iAp e1 es2)
  then show ?case apply(subst iterm.subst)
      subgoal using f by auto
      subgoal apply(rule affine.iAp) using fv f
      by auto (metis Int_emptyD)+ .
qed (auto simp: f ILC.SSupp_IImsupp_bound af)

(* Strengthening the previous result with "{x,y} \<subseteq> iFV e "
(which seems to prevent the above proof by induction), otherwise the result is
not strong enough to instantiate to imakeSubst... *)
lemma tvsubst_affine:
assumes f: "|SSupp f| <o |UNIV::ivar set|" and af: "\<And>x. affine (f x)"
and fv: "\<And>x y. {x,y} \<subseteq> iFV e \<Longrightarrow> x \<noteq> y \<Longrightarrow> iFV (f x) \<inter> iFV (f y) = {}"
and r: "affine (e::itrm)"
shows "affine (itvsubst f e)"
proof-
  obtain xs and x::ivar where x: "x \<in> dsset xs"
    using dsset_range by blast
  define t where "t = iLm xs (iVr x)"
  have t: "iFV t = {}" "affine t" unfolding t_def using x by (auto intro: affine.intros)

  have fve: "\<And>e. |iFV e| <o |UNIV::ivar set|"
    by (simp add: iterm.set_bd_UNIV)

  have "|\<Union> ((iFV o f) ` (iFV e))| \<le>o |Sigma (iFV e) (iFV o f)|"
  by (rule card_of_UNION_Sigma)
  also have "|Sigma (iFV e) (iFV o f)| <o |UNIV::ivar set|"
  apply(rule stable_elim)
    subgoal by (metis exists_fresh UNIV_I card_ivar card_of_Field_ordIso card_of_nat
         finite_iff_ordLess_natLeq natLeq_Card_order ordIso_equivalence(3) ordIso_ordLess_trans
         ordLess_ordIso_trans stable_cardSuc stable_ordIso1)
    subgoal by fact
    subgoal unfolding o_def using fve . .
  finally have ffv: "|\<Union> ((iFV o f) ` (iFV e))| <o |UNIV::ivar set|" .

  define g where "g \<equiv> \<lambda>x. if x \<in> iFV e then f x
                                           else if x \<in> \<Union> ((iFV o f) ` (iFV e)) then t
                                           else iVr x"
  have sg: "SSupp g \<subseteq> iFV e \<union> \<Union> ((iFV o f) ` (iFV e))" unfolding g_def SSupp_def by auto

  have g: "|SSupp g| <o |UNIV::ivar set|" "\<And>x. affine (g x)"
  "\<And>x y. x \<noteq> y \<Longrightarrow> iFV (g x) \<inter> iFV (g y) = {}"
     subgoal using sg by (meson card_of_subset_bound ffv fve var_stream_class.Un_bound)
     subgoal by (simp add: af g_def t(2))
     subgoal using fv unfolding g_def by (simp add: fv t(1)) .

  have 0: "itvsubst f e = itvsubst g e" apply(rule itvsubst_cong)
    using f g unfolding g_def by auto

  show ?thesis unfolding 0
  using tvsubst_affine'[OF g r] by simp
qed


lemma imkSubst_affine:
assumes r: "affine e" and
fv: "\<And>e1. e1 \<in> sset es \<Longrightarrow> affine e1 \<and> iFV e \<inter> iFV e1 = {}"
"\<And>i j. i \<noteq> j \<Longrightarrow> iFV (snth es i) \<inter> iFV (snth es j) = {}"
shows "affine (itvsubst (imkSubst xs es) e)"
apply(rule tvsubst_affine)
using assms apply auto
  apply (simp add: imkSubst_def)
  by (metis Int_emptyD dtheN imkSubst_def iterm.set(1) singletonD snth_sset)

lemma imkSubst_affine_strong:
assumes r: "affine e" and
fv: "\<And>e1. e1 \<in> sset es \<Longrightarrow> affine e1 \<and> iFV e \<inter> iFV e1 \<subseteq> dsset xs"
"\<And>i j. i \<noteq> j \<Longrightarrow> iFV (snth es i) \<inter> iFV (snth es j) = {}"
shows "affine (itvsubst (imkSubst xs es) e)"
apply(rule tvsubst_affine)
using assms apply auto
  apply (simp add: imkSubst_def)
  by (smt (verit, best) IntI disjoint_insert(2) dtheN imkSubst_def in_mono iterm.set(1)
  mk_disjoint_insert singletonD snth_sset)

end