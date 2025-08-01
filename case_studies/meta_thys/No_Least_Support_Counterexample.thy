theory No_Least_Support_Counterexample
  imports
   "HOL-Library.Stream"
   "HOL-Library.Countable_Set_Type"
   "HOL-Cardinals.Cardinals"
begin

type_synonym atom = "nat suc" (* uncountable variable type *)

definition cbij :: "(atom \<Rightarrow> atom) \<Rightarrow> bool" (* countable-support bijections *) where 
  "cbij \<sigma> \<equiv> bij \<sigma> \<and> countable {x. \<sigma> x \<noteq> x}"

lemma card_of_atom: "|UNIV :: atom set| =o card_suc |UNIV :: nat set|"
  by (simp add: card_order_card_suc ordIso_symmetric)

lemma card_suc_greater_set: "card_order r \<Longrightarrow> A \<le>o r \<Longrightarrow> A <o card_suc r"
  using card_suc_greater ordLeq_ordLess_trans by blast

lemma countable_iff_le_card_atom: "countable A \<longleftrightarrow> |A| <o |UNIV::atom set|"
  by (auto simp add: countable_card_of_nat card_suc_ordLess_imp_ordLeq card_suc_greater_set
    ordLess_ordIso_trans[OF _ ordIso_symmetric[OF card_of_atom]]
    dest: ordLess_ordIso_trans[OF _ card_of_atom])

lemma countable_sset: "countable (sset s)"
  unfolding sset_range by auto

lemma stream_eq_nth: "xs = ys \<longleftrightarrow> (\<forall>i. snth xs i = snth ys i)"
  by (metis smap_alt stream_smap_nats)

lemma exists_subset_compl:
  assumes "Cinfinite r" "r \<le>o |UNIV::atom set|" "|U \<union> S::atom set| <o r"
  shows "\<exists>B. U \<inter> B = {} \<and> B \<inter> S = {} \<and> |U| =o |B|"
proof -
  have 1: "|U| <o r" using assms(3) using card_of_Un1 ordLeq_ordLess_trans by blast
  have "|-(U \<union> S)| =o |UNIV::atom set|" using assms(2,3)
    by (metis boolean_algebra.disj_cancel_right card_of_UNIV card_of_atom countable_Un_iff
      countable_iff_le_card_atom not_ordLess_ordIso ordLeq_iff_ordLess_or_ordIso ordLess_ordLeq_trans)
  then have "|U| <o |-(U \<union> S)|" using ordLess_ordLeq_trans[OF 1 assms(2)] ordIso_symmetric ordLess_ordIso_trans by fast
  then obtain B where 1: "B \<subseteq> -(U \<union> S)" "|U| =o |B|"
    by (meson internalize_card_of_ordLeq2 ordLess_imp_ordLeq)
  then have "U \<inter> B = {}" "B \<inter> S = {}" by blast+
  then show ?thesis using 1 by blast
qed

lemma countable_cbij: 
assumes s: "countable A" "countable B" "countable A'" "A \<inter> A' = {}"
shows "\<exists>\<sigma>. cbij \<sigma> \<and> \<sigma> ` A \<inter> B = {} \<and> (\<forall>a\<in>A'. \<sigma> a = a)"
proof-
  obtain D where D: "D \<inter> B = {}" "D \<inter> A = {}" "D \<inter> A' = {}" and DA: "|D| =o |A|"
    using exists_subset_compl[of _ A "A' \<union> B"]
      Field_card_of Int_Un_distrib Int_commute Un_empty card_of_Card_order
      card_of_UNIV cinfinite_def countable_Un_iff countable_iff_le_card_atom
       ordIso_symmetric s(1-3) Cinfinite_card_suc Field_card_suc natLeq_Cinfinite natLeq_card_order
    by (smt (verit, ccfv_threshold))
  then obtain u where u: "bij_betw u A D"  
  using card_of_ordIso ordIso_symmetric by blast
  hence u: "u ` A = D" "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> u a = u b \<longleftrightarrow> a = b"
  unfolding bij_betw_def inj_on_def by auto

  let ?iu = "inv_into A u" 
  have iu: "bij_betw ?iu D A"
  using u by (metis bij_betw_def bij_betw_inv_into inj_on_def)
  hence iu: "?iu ` D = A" "\<And>a b. a \<in> D \<Longrightarrow> b \<in> D \<Longrightarrow> ?iu a = ?iu b \<longleftrightarrow> a = b"
  unfolding bij_betw_def inj_on_def by auto

  define v where "v \<equiv> \<lambda>a. if a \<in> A then u a else if a \<in> D then ?iu a else a"
  have v[simp]: "\<And>a. a \<in> A \<Longrightarrow> v a = u a" "\<And>a. a \<in> D \<Longrightarrow> v a = ?iu a"
  "\<And>a. a \<notin> A \<and> a \<notin> D \<Longrightarrow> v a = a"
  using D(2) unfolding v_def by auto

  have cas: "\<And>a. a \<in> A \<or> a \<in> D \<or> (a \<notin> A \<and> a \<notin> D)" by auto

  have "v x = v y \<Longrightarrow> x = y" for x y
    using D(2) iu(1) u(1) u(2) by (auto simp: v_def image_image inj_on_def split: if_splits)
  moreover have "\<exists>x. y = v x" for y
    using iu(1) u(1) v(1-3) by (metis f_inv_into_f inv_into_into)
  ultimately have bv: "bij v"
    unfolding bij_def inj_def image_def
    by blast

  have sv: "{x. v x \<noteq> x} \<subseteq> A \<union> D" using v(3) by blast

  show ?thesis apply(rule exI[of _ v], intro conjI)
    subgoal using bv sv s(1) u(1) unfolding cbij_def
      by (metis countable_Un_iff countable_image countable_subset)
    subgoal using D(1) u(1) by auto
    subgoal using sv D(3) s(4) by auto . 
qed

definition "eq_ae s t = finite {i. snth s i \<noteq> snth t i}" (*almost everywhere equal streams*)

lemma eq_ae_suffix: "eq_ae s t = (\<exists>i. sdrop i s = sdrop i t)"
  unfolding eq_ae_def
proof (safe, goal_cases)
  case 1
  then show ?case
    apply (intro exI[of _ "Max (insert 0 (Suc ` {i. s !! i \<noteq> t !! i}))"])
    apply (auto simp: Max.insert_remove smap_alt[of id, simplified stream.map_id id_apply]
      mono_Max_commute[symmetric, of Suc, simplified mono_def, simplified] sdrop_snth
      simp flip: snth.simps)
    apply (smt (verit) Collect_empty_eq Max_less_iff add.commute less_add_Suc2 mem_Collect_eq verit_comp_simplify1(1))
    done
next
  case (2 i)
  then show ?case
    by (safe intro!: finite_subset[of _ "{0 ..< i}", simplified])
      (metis add_diff_inverse_nat atLeast0LessThan lessThan_iff sdrop_snth)
qed

lemma eq_ae_refl: "eq_ae s s"
  by (auto simp: eq_ae_def)

lemma eq_ae_sym: "eq_ae s t \<Longrightarrow> eq_ae t s"
  by (auto simp: eq_ae_def elim: finite_subset[rotated])

lemma eq_ae_trans: "eq_ae s t \<Longrightarrow> eq_ae t u \<Longrightarrow> eq_ae s u"
  unfolding eq_ae_suffix
  apply (elim exE)
  subgoal for i j
    apply (rule exI[of _ "max i j"])
    apply (metis add.commute max.commute nat_minus_add_max sdrop_add)
    done
  done

lemma eq_ae_equivp: "equivp eq_ae"
  by (simp add: eq_ae_refl eq_ae_sym eq_ae_trans equivpI reflpI sympI transpI)

quotient_type item = "atom stream" / eq_ae
  by (rule eq_ae_equivp)

lift_definition perm_item :: "(atom \<Rightarrow> atom) \<Rightarrow> item \<Rightarrow> item" (infix "\<bullet>" 65) is smap
  unfolding eq_ae_suffix
  apply (elim exE)
  subgoal for f s t i
    by (rule exI[of _ i]) auto
  done

definition supports where
  "supports A t = (\<forall>\<sigma>. cbij \<sigma> \<longrightarrow> (\<forall>a\<in>A. \<sigma> a = a) \<longrightarrow> \<sigma> \<bullet> t = t)"

(* next 3 lemmas show that item is a nominal set *)
lemma perm_item_id: "id \<bullet> t = t"
 by (transfer) (auto simp: eq_ae_refl stream.map_id)
lemma perm_item_comp: "cbij \<sigma> \<Longrightarrow> cbij \<tau> \<Longrightarrow> (\<sigma> o \<tau>) \<bullet> t = \<sigma> \<bullet> (\<tau> \<bullet> t)"
  by (transfer) (auto simp: eq_ae_refl stream.map_comp)
lemma countable_support: "\<exists>A. countable A \<and> supports A t"
  unfolding supports_def
  apply transfer
  subgoal for s
    by (auto simp: eq_ae_refl stream.map_ident cong: stream.map_cong intro: exI[of _ "sset s"] countable_sset)
  done

definition "atom = (SOME f :: nat \<Rightarrow> atom. inj f)"

lemma atom_inj[simp]: "atom x = atom y \<longleftrightarrow> x = y"
  by (metis Cinfinite_card_suc Field_natLeq cinfinite_def infinite_countable_subset injD atom_def
    natLeq_card_order natLeq_cinfinite someI_ex)

lift_definition inats :: "item" is "smap atom nats" .

lemma supports_inats: "supports (atom ` {n ..}) inats"
  unfolding supports_def
  by transfer
    (force simp: stream.map_comp eq_ae_suffix intro: stream.map_cong)

(* assuming the existence of a minimal support set for any item we derive a contradiction *)
lemma counterexample:
  assumes minimal: "\<forall>t. \<exists>A. countable A \<and> supports A t \<and> (\<forall>B. countable B \<longrightarrow> supports B t \<longrightarrow> A \<subseteq> B)"
  shows False
proof -
  from minimal obtain A where "countable A" "supports A inats" "\<forall>B. countable B \<longrightarrow> supports B inats \<longrightarrow> A \<subseteq> B"
    by blast
  then have *: "A \<subseteq> atom ` {n..}" for n
    using supports_inats[of n] by auto
  have "atom x \<notin> A" for x
    using *[of "Suc x"] by auto
  with countable_cbij[of "range atom" "range atom" A] \<open>countable A\<close> obtain \<sigma> where
    "cbij \<sigma>" "\<sigma> ` range atom \<inter> range atom = {}" "\<forall>a\<in>A. \<sigma> a = a"
    by auto
  then show False
    using \<open>supports A inats\<close>[unfolded supports_def, rule_format, where \<sigma> = \<sigma>]
    by transfer (auto simp: stream.map_comp o_def eq_ae_suffix stream_eq_nth)
qed

end