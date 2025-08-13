theory Support
  imports "Prelim.Prelim"
begin

lemma notin_supp: "x \<notin> supp f \<Longrightarrow> f x = x"
  unfolding supp_def by blast

lemma imsupp_absorb[simp]: "supp f \<union> imsupp f = imsupp f"
  unfolding imsupp_def by blast

definition SSupp :: "('a \<Rightarrow> 't) \<Rightarrow> ('a \<Rightarrow> 't) \<Rightarrow> 'a set" where
  "SSupp Inj \<equiv> \<lambda>f. { a. f a \<noteq> Inj a }"

definition IImsupp :: "('a \<Rightarrow> 't) \<Rightarrow> ('t \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 't) \<Rightarrow> 'b set" where
  "IImsupp Inj Vr \<equiv> \<lambda>\<rho>. (\<Union>a\<in>SSupp Inj \<rho>. Vr (\<rho> a))"

lemma SSupp_Inj[simp]: "SSupp Inj Inj = {}"
  unfolding SSupp_def by simp

lemma SSupp_Inj_comp[simp]: "inj Inj \<Longrightarrow> SSupp Inj (Inj \<circ> f) = supp f"
  unfolding SSupp_def supp_def using injD by fastforce
lemma IImsupp_Inj_comp[simp]: "inj Inj \<Longrightarrow> (\<And>a. FVars (Inj a) = {a}) \<Longrightarrow> SSupp Inj (Inj \<circ> f) \<union> IImsupp Inj FVars (Inj \<circ> f) = imsupp f"
  unfolding IImsupp_def SSupp_def imsupp_def supp_def comp_def using injD
  by (smt (verit, ccfv_SIG) Collect_cong UNION_singleton_eq_range image_cong)

lemma IImsupp_Inj[simp]: "IImsupp Inj Vr Inj = {}"
  unfolding IImsupp_def by simp

lemma SSupp_Inj_bound[simp]: "|SSupp Inj Inj| <o |UNIV::'a set|"
  by simp
lemma SSupp_Inj_bound'[simp]: "Cinfinite r \<Longrightarrow> |SSupp Inj Inj| <o r"
  by (simp add: Cinfinite_gt_empty)

lemma SSupp_fun_upd_subset:
  "SSupp Inj (f(x := t)) \<subseteq> insert x (SSupp Inj f)"
  by (simp add: SSupp_def subset_eq)

lemma IImsupp_fun_upd_subset:
  "IImsupp Inj (Vrs::_ \<Rightarrow> 'a set) (f(x := t)) \<subseteq> insert x (Vrs t \<union> IImsupp Inj Vrs f)"
  "IImsupp Inj (Vrs2:: _ \<Rightarrow> 'b set) (g(x := t)) \<subseteq> Vrs2 t \<union> IImsupp Inj Vrs2 g"
  unfolding IImsupp_def
   apply (smt (verit) SSupp_fun_upd_subset UN_iff UnCI fun_upd_apply insert_iff subset_eq)
  by (smt (verit, ccfv_threshold) SSupp_fun_upd_subset UN_iff UnCI fun_upd_apply insert_iff subset_eq)

lemma SSupp_fun_upd_bound[simp]: "Cinfinite r \<Longrightarrow> |SSupp Inj (f(x := t))| <o r \<longleftrightarrow> |SSupp Inj f| <o r"
  using SSupp_fun_upd_subset card_of_subset_bound
  by (metis fun_upd_idem_iff fun_upd_upd insert_bound)

lemma IImsupp_Inj_bound[simp]: "|IImsupp Inj FVars Inj| <o |UNIV::'a set|"
  by simp

lemma IImsupp_Un: "IImsupp Inj (\<lambda>x. Vrs1 x \<union> Vrs2 x) \<rho> = IImsupp Inj Vrs1 \<rho> \<union> IImsupp Inj Vrs2 \<rho>"
  unfolding IImsupp_def by blast

lemma SSupp_comp_subset: "SSupp Inj (g \<circ> f) \<subseteq> SSupp Inj g \<union> supp f"
proof (rule subsetI, unfold SSupp_def mem_Collect_eq Un_iff comp_apply)
  fix x
  assume a: "g (f x) \<noteq> Inj x"
  show "g x \<noteq> Inj x \<or> x \<in> supp f"
  proof (cases "x \<in> supp f")
    case False
    then show ?thesis using a notin_supp by metis
  qed blast
qed

lemma SSupp_comp_bound: "Cinfinite r \<Longrightarrow> |SSupp Inj g| <o r \<Longrightarrow> |supp f| <o r \<Longrightarrow> |SSupp Inj (g \<circ> f)| <o r"
  using card_of_subset_bound[OF SSupp_comp_subset] Un_Cinfinite_ordLess by blast

lemma SSupp_type_copy: "type_definition Rep Abs UNIV \<Longrightarrow> SSupp (Abs \<circ> Inj) \<rho> = SSupp Inj (Rep \<circ> \<rho>)"
  unfolding SSupp_def by (metis UNIV_I comp_apply type_definition_def)

lemma IImsupp_type_copy: "type_definition Rep Abs UNIV \<Longrightarrow> IImsupp (Abs \<circ> Inj) (Vrs \<circ> Rep) \<rho> = IImsupp Inj Vrs (Rep \<circ> \<rho>)"
  unfolding IImsupp_def using SSupp_type_copy by fastforce

lemma notin_SSupp: "a \<notin> SSupp Inj f \<Longrightarrow> f a = Inj a"
  unfolding SSupp_def by blast

lemma IImsupp_chain1:
  assumes "\<And>a. Vrs2 (Inj2 a) = {a}" "\<rho>1 = \<rho>' \<or> \<rho>1 = \<rho>2"
  shows "(\<Union>x\<in>SSupp Inj2 \<rho>1. \<Union>x\<in>Vrs2 (\<rho>' x). Vrs2 (\<rho>2 x)) \<subseteq> IImsupp Inj2 Vrs2 \<rho>2 \<union> IImsupp Inj2 Vrs2 \<rho>'"
  apply (unfold IImsupp_def)
  apply (rule subsetI)
  apply (erule UN_E)+
  subgoal for x y z
    apply (rule case_split[of "z \<in> SSupp Inj2 \<rho>2"])
     apply blast
    apply (drule notin_SSupp)
    apply (simp only:)
    apply (subst (asm) assms)
    apply (drule singletonD)
    apply hypsubst_thin
    apply (rule case_split[of "y \<in> SSupp Inj2 \<rho>'"])
     apply (rule UnI2)
     apply (rule UN_I)
      apply assumption
     apply assumption
    apply (drule notin_SSupp)
    apply (simp only:)
    apply (subst (asm) assms)
    apply (drule singletonD)
    apply hypsubst_thin
    apply (rule UnI1)
    apply (rule UN_I)
    using assms(2)
     apply (metis (mono_tags, lifting) SSupp_def mem_Collect_eq)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
     apply (rule arg_cong[of _ _ Vrs2])
     apply assumption
    apply (subst assms)
    apply (rule singletonI)
    done
  done

lemma IImsupp_chain2:
  assumes "\<And>a. Vrs2 (Inj2 a) = {a}" "\<And>a. Vrs3 (Inj1 a) = {}"
  shows "(\<Union>x\<in>SSupp Inj1 \<rho>1. \<Union>x\<in>Vrs3 (\<rho>' x). Vrs2 (\<rho>2 x)) \<subseteq> IImsupp Inj2 Vrs2 \<rho>2 \<union> IImsupp Inj1 Vrs3 \<rho>'"
  apply (unfold IImsupp_def)
  apply (rule subsetI)
  apply (erule UN_E)+
  subgoal for x y z
    apply (rule case_split[of "z \<in> SSupp Inj2 \<rho>2"])
     apply blast
    apply (drule notin_SSupp)
    apply (simp only:)
    apply (subst (asm) assms)
    apply (drule singletonD)
    apply hypsubst_thin
    apply (rule case_split[of "y \<in> SSupp Inj1 \<rho>'"])
     apply (rule UnI2)
     apply (rule UN_I)
      apply assumption
     apply assumption
    apply (drule notin_SSupp)
    apply (simp only:)
    apply (subst (asm) assms)
    apply (erule emptyE)
    done
  done

lemma IImsupp_chain3:
  assumes "\<And>a. Vrs2 (Inj2 a) = {}"
  shows "(\<Union>x\<in>SSupp Inj1 \<rho>1. \<Union>x\<in>Vrs3 (\<rho>' x). Vrs2 (\<rho>2 x)) \<subseteq> IImsupp Inj2 Vrs2 \<rho>2"
  apply (unfold IImsupp_def)
  apply (rule subsetI)
  apply (erule UN_E)+
  subgoal for x y z
    apply (rule case_split[of "z \<in> SSupp Inj2 \<rho>2"])
     apply blast
    apply (drule notin_SSupp)
    apply (simp only:)
    apply (subst (asm) assms)
    apply (erule emptyE)
    done
  done

lemma IImsupp_chain4:
  assumes "\<And>a. Vrs (Inj a) = {}"
  shows "h ` (\<Union>x\<in>SSupp Inj \<rho>2. Vrs (\<rho>' x)) \<subseteq> imsupp h \<union> IImsupp Inj Vrs \<rho>'"
  apply (rule subsetI)
  apply (erule imageE)
  apply hypsubst
  subgoal for _ x
    apply (rule case_split[of "h x = x"])
     apply (rule UnI2)
     apply (unfold IImsupp_def)[1]
     apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<in>)"]])
      apply assumption
     apply (erule UN_E)
     apply (erule thin_rl)
    subgoal for y
      apply (rule case_split[of "y \<in> SSupp Inj \<rho>'"])
       apply (rule UN_I)
        apply assumption
       apply assumption
      apply (drule notin_SSupp)
      apply (simp only:)
      apply (subst (asm) assms)
      apply (erule emptyE)
      done
    apply (rule UnI1)
    apply (unfold imsupp_def supp_def) by blast
  done

end