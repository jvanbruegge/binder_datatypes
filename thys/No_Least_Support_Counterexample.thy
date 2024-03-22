theory No_Least_Support_Counterexample
  imports
   "Prelim.FixedUncountableVars"
   "Prelim.Prelim"
   "Prelim.More_Stream"
begin

definition small :: "ivar set \<Rightarrow> bool" where 
  "small A \<equiv> |A| <o |UNIV::ivar set|"

definition ssbij :: "(ivar \<Rightarrow> ivar) \<Rightarrow> bool" (* small-support bijections *) where 
  "ssbij \<sigma> \<equiv> bij \<sigma> \<and> |supp \<sigma>| <o |UNIV::ivar set|"

lemma small_Un: "small A \<Longrightarrow> small B \<Longrightarrow> small (A \<union> B)"
  using countable_iff_le_card_ivar small_def by auto
lemma small_Diff: "small A \<Longrightarrow> small (A - B)"
  using countable_iff_le_card_ivar small_def by auto
lemma small_Int: "small A \<Longrightarrow> small (A \<inter> B)"
  by (metis Diff_Diff_Int small_Diff)

lemma exists_subset_compl:
  assumes "Cinfinite r" "r \<le>o |UNIV::ivar set|" "|U \<union> S::ivar set| <o r"
  shows "\<exists>B. U \<inter> B = {} \<and> B \<inter> S = {} \<and> |U| =o |B|"
proof -
  have 1: "|U| <o r" using assms(3) using card_of_Un1 ordLeq_ordLess_trans by blast
  have "|-(U \<union> S)| =o |UNIV::ivar set|"
    using card_of_Un_diff_infinite[OF
        cinfinite_imp_infinite[OF cinfinite_mono[OF assms(2) conjunct1[OF assms(1)]]]
        ordLess_ordLeq_trans[OF assms(3,2)]
    ]
    by (simp add: Compl_eq_Diff_UNIV)
  then have "|U| <o |-(U \<union> S)|" using ordLess_ordLeq_trans[OF 1 assms(2)] ordIso_symmetric ordLess_ordIso_trans by fast
  then obtain B where 1: "B \<subseteq> -(U \<union> S)" "|U| =o |B|"
    by (meson internalize_card_of_ordLeq2 ordLess_imp_ordLeq)
  then have "U \<inter> B = {}" "B \<inter> S = {}" by blast+
  then show ?thesis using 1 by blast
qed

lemma small_ssbij: 
assumes s: "small A" "small B" "small A'" "A \<inter> A' = {}"
shows "\<exists>\<sigma>. ssbij \<sigma> \<and> \<sigma> ` A \<inter> B = {} \<and> (\<forall>a\<in>A'. \<sigma> a = a)"
proof-
  obtain D where D: "D \<inter> B = {}" "D \<inter> A = {}" "D \<inter> A' = {}" and DA: "|D| =o |A|"
    using exists_subset_compl[of _ A "A' \<union> B"]
    by (smt (verit, best) Field_card_of Int_Un_distrib Int_commute Un_empty card_of_Card_order
      card_of_UNIV cinfinite_def countable_Un_iff countable_iff_le_card_ivar infinite_ivar
      ordIso_symmetric s(1) s(2) s(3) small_def)

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

  have bv: "bij v"
  unfolding bij_def inj_def image_def apply auto 
  apply (metis (mono_tags, lifting) D(2) Int_emptyD f_inv_into_f imageI iu(1) u(1) u(2) v_def)
  by (metis f_inv_into_f inv_into_into iu(1) u(1) v(2) v_def) 

  have sv: "supp v \<subseteq> A \<union> D" unfolding supp_def using v(3) by blast

  show ?thesis apply(rule exI[of _ v], intro conjI)
    subgoal using bv sv s(1) unfolding ssbij_def small_def
      by (meson DA card_of_Un_ordLess_infinite card_of_mono1 infinite_ivar ordIso_ordLess_trans ordLeq_ordLess_trans)
    subgoal using D(1) u(1) by auto
    subgoal using sv D(3) s(4) unfolding supp_def by auto . 
qed

definition "eq_ae s t = finite {i. snth s i \<noteq> snth t i}"

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

quotient_type item = "ivar stream" / eq_ae
  by (rule eq_ae_equivp)

lift_definition map_item :: "(ivar \<Rightarrow> ivar) \<Rightarrow> item \<Rightarrow> item" is smap
  unfolding eq_ae_suffix
  apply (elim exE)
  subgoal for f s t i
    apply (rule exI[of _ i])
    apply auto
    done
  done

definition supports where
  "supports A t = (\<forall>\<sigma>. ssbij \<sigma> \<longrightarrow> (\<forall>a\<in>A. \<sigma> a = a) \<longrightarrow> map_item \<sigma> t = t)"

(* next 3 lemmas show that item is a nominal set *)
lemma map_item_id: "map_item id = id"
 by (rule ext, transfer) (auto simp: eq_ae_refl)
lemma map_item_comp: "ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> map_item (\<sigma> o \<tau>) = map_item \<sigma> o map_item \<tau>"
  by (rule ext, transfer) (auto simp: eq_ae_refl stream.map_comp)
lemma small_support: "\<exists>A. small A \<and> supports A t"
  unfolding supports_def
  apply transfer
  subgoal for s
    apply (rule exI[of _ "sset s"])
    apply safe
    subgoal
      unfolding small_def
      using countable_card_ivar countable_sset by blast
    subgoal
      by (auto simp: eq_ae_refl stream.map_ident cong: stream.map_cong)
    done
  done

definition "ivar = (SOME f :: nat \<Rightarrow> ivar. inj f)"

lemma ivar_inj[simp]: "ivar x = ivar y \<longleftrightarrow> x = y"
  by (metis infinite_countable_subset infinite_ivar injD ivar_def someI_ex)

lift_definition inats :: "item" is "smap ivar nats" .

lemma small_from: "small (ivar ` {n ..})"
  unfolding small_def
  by (rule countable_card_ivar) auto

lemma supports_inats: "supports (ivar ` {n ..}) inats"
  unfolding supports_def
  apply transfer
  apply safe
  subgoal for n \<sigma>
    by (auto simp: stream.map_comp eq_ae_suffix intro!: exI[of _ n] stream.map_cong)
  done

(* assuming the existence of a minimal support set for any item we derive a contradiction *)
context
  assumes minimal: "\<forall>t. \<exists>A. small A \<and> supports A t \<and> (\<forall>B. small B \<longrightarrow> supports B t \<longrightarrow> A \<subseteq> B)"
begin

lemma False
proof -
  from minimal obtain A where "small A" "supports A inats" "\<forall>B. small B \<longrightarrow> supports B inats \<longrightarrow> A \<subseteq> B"
    by blast
  then have *: "A \<subseteq> ivar ` {n..}" for n
    using small_from[of n] supports_inats[of n]
    by auto
  have "ivar x \<notin> A" for x
    using *[of "Suc x"] by auto
  with small_ssbij[of "range ivar" "range ivar" A] small_from[of 0] \<open>small A\<close> obtain \<sigma> where
    "ssbij \<sigma>" "\<sigma> ` range ivar \<inter> range ivar = {}" "\<forall>a\<in>A. \<sigma> a = a"
    by auto
  then show False
    using \<open>supports A inats\<close>[unfolded supports_def, rule_format, where \<sigma> = \<sigma>]
    by transfer (auto simp: stream.map_comp o_def eq_ae_suffix stream_eq_nth)
qed

end

end