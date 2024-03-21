theory No_Least_Support_Counterexample
  imports Generic_Barendregt_Enhanced_Rule_Induction "HOL-Library.Stream"
    "Infinitary_Lambda_Calculus.Embed_var_ivar"
begin

locale Nominal = Small dummy
for dummy :: 'A
+
fixes (* 'T: term-like entities *)
Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
assumes  
Tmap_id: "Tmap id = id"
and
Tmap_comp: "\<And>\<sigma> \<tau>. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap (\<sigma> o \<tau>) = Tmap \<sigma> o Tmap \<tau>"
and
small_support: "\<And>t. \<exists>A. small A \<and> (\<forall>\<sigma>. ssbij \<sigma> \<longrightarrow> (\<forall>a\<in>A. \<sigma> a = a) \<longrightarrow> Tmap \<sigma> t = t)"
begin

definition supports where
  "supports A t = (\<forall>\<sigma>. ssbij \<sigma> \<longrightarrow> (\<forall>a\<in>A. \<sigma> a = a) \<longrightarrow> Tmap \<sigma> t = t)"

lemma small_Diff: "small A \<Longrightarrow> small (A - B)"
  by (meson Diff_subset card_of_subset_bound small_def)
lemma small_Int: "small A \<Longrightarrow> small (A \<inter> B)"
  by (metis Diff_Diff_Int small_Diff)

end

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

quotient_type 'a item = "'a stream" / eq_ae
  by (rule eq_ae_equivp)

lift_definition map_item :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a item \<Rightarrow> 'b item" is smap
  unfolding eq_ae_suffix
  apply (elim exE)
  subgoal for f s t i
    apply (rule exI[of _ i])
    apply auto
    done
  done

interpretation Small "undefined :: ivar"
  by standard (simp_all add: regularCard_ivar infinite)

interpretation Nominal "undefined :: ivar" map_item
  apply standard
  subgoal
    by (rule ext, transfer) (auto simp: eq_ae_refl)
  subgoal for \<sigma> \<tau>
    by (rule ext, transfer) (auto simp: eq_ae_refl stream.map_comp)
  subgoal for t
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
  done

lift_definition inats :: "ivar item" is "smap iVariable nats" .

lemma small_from: "small (iVariable ` {n ..})"
  unfolding small_def
  by (rule countable_card_ivar) auto

lemma supports_inats: "supports (iVariable ` {n ..}) inats"
  unfolding supports_def
  apply transfer
  apply safe
  subgoal for n \<sigma>
    by (auto simp: stream.map_comp eq_ae_suffix intro!: exI[of _ n] stream.map_cong)
  done

context
  assumes minimal: "\<exists>A. small A \<and> supports A t \<and> (\<forall>B. small B \<longrightarrow> supports B t \<longrightarrow> A \<subseteq> B)"
begin

lemma False
proof -
  from minimal obtain A where "small A" "supports A inats" "\<forall>B. small B \<longrightarrow> supports B inats \<longrightarrow> A \<subseteq> B"
    by blast
  then have *: "A \<subseteq> iVariable ` {n..}" for n
    using small_from[of n] supports_inats[of n]
    by auto
  have "iVariable x \<notin> A" for x
    using *[of "Suc x"] by auto
  with small_ssbij[of "range iVariable" "range iVariable" A] small_from[of 0] \<open>small A\<close> obtain \<sigma> where
    "ssbij \<sigma>" "\<sigma> ` range iVariable \<inter> range iVariable = {}" "\<forall>a\<in>A. \<sigma> a = a"
    by auto
  then show False
    using \<open>supports A inats\<close>[unfolded supports_def, rule_format, where \<sigma> = \<sigma>]
    by transfer (auto simp: stream.map_comp o_def eq_ae_suffix stream_eq_nth)
qed

end

end