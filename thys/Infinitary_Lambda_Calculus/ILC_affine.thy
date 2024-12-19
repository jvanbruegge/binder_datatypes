(* Here we instantiate the general enhanced rule induction to the "affine" predicate from Mazza  *)
theory ILC_affine
imports ILC2 "Prelim.Curry_LFP"
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

lemma Tvars_dsset: "(FFVars t - dsset xs) \<inter> dsset xs = {}" "|FFVars t - dsset xs| <o |UNIV::ivar set|"
apply auto using card_of_minus_bound iterm.set_bd_UNIV by blast

inductive affine  :: "itrm \<Rightarrow> bool" where
 iVar[simp,intro!]: "affine (iVar x)"
|iLam: "affine e \<Longrightarrow> affine (iLam xs e)"
|iApp:
"affine e1 \<Longrightarrow>
 (\<And>e2. e2 \<in> sset es2 \<Longrightarrow> affine e2) \<Longrightarrow>
 (\<And>e2. e2 \<in> sset es2 \<Longrightarrow> FFVars e1 \<inter> FFVars e2 = {}) \<Longrightarrow>
 (\<And>i j. i \<noteq> j \<Longrightarrow> FFVars (snth es2 i) \<inter> FFVars (snth es2 j) = {})
 \<Longrightarrow>
 affine (iApp e1 es2)"

binder_inductive affine
  unfolding isPerm_def induct_rulify_fallback
  subgoal for R B \<sigma> t
    apply(elim disjE)
    subgoal apply(rule disjI3_1)
      subgoal apply(elim exE) subgoal for x
        apply(rule exI[of _ "\<sigma> x"])
        apply auto
        done
      done
    done
    (* *)
    subgoal apply(rule disjI3_2)
      subgoal apply(elim exE) subgoal for e xs
        apply(rule exI[of _ "irrename \<sigma> e"])
        apply(rule exI[of _ "dsmap \<sigma> xs"])
        apply (simp add: iterm.permute_comp)
        done
      done
    done
    (* *)
    subgoal apply(rule disjI3_3)
      subgoal apply(elim exE) subgoal for e1 es2
        apply(rule exI[of _ "irrename \<sigma> e1"])
        apply(rule exI[of _ "smap (irrename \<sigma>) es2"])
        apply (fastforce simp add: iterm.permute_comp bij_implies_inject)
        done
      done
    done
  done
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
          subgoal apply(subst iLam_irrename[of "f"]) unfolding id_on_def by auto . . .
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

(* ... and equivariance gives us a nice iLam inversion rule: *)

lemma affine_App_case:
"affine (iApp e1 es2) \<Longrightarrow>
 affine e1 \<and>
 (\<forall>e2. e2 \<in> sset es2 \<longrightarrow> affine e2 \<and> FFVars e1 \<inter> FFVars e2 = {}) \<Longrightarrow>
 (\<forall>i j. i \<noteq> j \<longrightarrow> FFVars (snth es2 i) \<inter> FFVars (snth es2 j) = {})"
apply(subst (asm) affine.simps) by auto

lemma affine_iApp_iff:
"affine (iApp e1 es2) \<longleftrightarrow>
 (affine e1 \<and>
  (\<forall>e2. e2 \<in> sset es2 \<longrightarrow> affine e2 \<and> FFVars e1 \<inter> FFVars e2 = {}) \<and>
  (\<forall>i j. i \<noteq> j \<longrightarrow> FFVars (snth es2 i) \<inter> FFVars (snth es2 j) = {}))"
apply(subst affine.simps) by auto

lemma affine_iLam_case:
assumes "affine (iLam xs e)"
shows "affine e"
proof-
  obtain xs' e' where 0: "iLam xs e = iLam xs' e'" and "affine e'"
  using assms by (smt (verit, del_insts) affine.cases iterm.distinct(2) iterm.distinct(4))
  thus ?thesis using 0 unfolding iLam_inject
  by (metis iLam_inject affine.equiv)
qed

lemma affine_iLam_iff[simp]:
"affine (iLam xs e) \<longleftrightarrow> affine e"
using affine.simps affine_iLam_case by blast

(* Other properties: *)

(* *)
lemma tvsubst_affine':
assumes f: "|SSupp f| <o |UNIV::ivar set|" and af: "\<And>x. affine (f x)"
and fv: "\<And>x y. x \<noteq> y \<Longrightarrow> FFVars (f x) \<inter> FFVars (f y) = {}"
and r: "affine (e::itrm)"
shows "affine (itvsubst f e)"
using r proof (binder_induction e avoiding: "IImsupp f" rule: affine.strong_induct)
  case (iLam ea xs)
  show ?case using iLam apply(subst iterm.subst)
      subgoal using f by auto
      subgoal by auto
      subgoal apply(rule affine.iLam) by auto .
next
  case (iApp e1 es2)
  then show ?case apply(subst iterm.subst)
      subgoal using f by auto
      subgoal apply(rule affine.iApp) using fv f
      by auto (metis Int_emptyD)+ .
qed (auto simp: f ILC.SSupp_IImsupp_bound af)

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

lemma imkSubst_affine_strong:
assumes r: "affine e" and
fv: "\<And>e1. e1 \<in> sset es \<Longrightarrow> affine e1 \<and> FFVars e \<inter> FFVars e1 \<subseteq> dsset xs"
"\<And>i j. i \<noteq> j \<Longrightarrow> FFVars (snth es i) \<inter> FFVars (snth es j) = {}"
shows "affine (itvsubst (imkSubst xs es) e)"
apply(rule tvsubst_affine)
using assms apply auto
  apply (simp add: imkSubst_def)
  by (smt (verit, best) IntI disjoint_insert(2) dtheN imkSubst_def in_mono iterm.set(1)
  mk_disjoint_insert singletonD snth_sset)

end