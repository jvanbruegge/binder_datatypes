theory MRBNF_Recursor
  imports "./MRBNF_Composition"
begin

ML_file \<open>../Tools/mrbnf_fp_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_fp.ML\<close>

lemma card_of_subset_bound: "\<lbrakk> B \<subseteq> A ; |A| <o x \<rbrakk> \<Longrightarrow> |B| <o x"
  using card_of_mono1 ordLeq_ordLess_trans by blast
lemma card_of_minus_bound: "|A| <o |UNIV::'a set| \<Longrightarrow> |A - B| <o |UNIV::'a set|"
  by (rule card_of_subset_bound[OF Diff_subset])

lemma exists_subset_compl:
  assumes "infinite (UNIV::'b set)" "|U \<union> S::'b set| <o |UNIV::'b set|"
  shows "\<exists>B. U \<inter> B = {} \<and> B \<inter> S = {} \<and> |U| =o |B|"
proof -
  have 1: "|U| <o |UNIV::'b set|" using assms(2) using card_of_Un1 ordLeq_ordLess_trans by blast
  have "|-(U \<union> S)| =o |UNIV::'b set|" using infinite_UNIV_card_of_minus[OF assms(1,2)]
    by (simp add: Compl_eq_Diff_UNIV)
  then have "|U| <o |-(U \<union> S)|" using 1 ordIso_symmetric ordLess_ordIso_trans by blast
  then obtain B where 1: "B \<subseteq> -(U \<union> S)" "|U| =o |B|"
    by (meson internalize_card_of_ordLeq2 ordLess_imp_ordLeq)
  then have "U \<inter> B = {}" "B \<inter> S = {}" by blast+
  then show ?thesis using 1 by blast
qed

lemma exists_suitable_aux:
  assumes "infinite (UNIV::'a set)" "|U \<union> (S - U)::'a set| <o |UNIV::'a set|"
  shows "\<exists>(u::'a \<Rightarrow> 'a). bij u \<and> |supp u| <o |UNIV::'a set| \<and> imsupp u \<inter> (S - U) = {} \<and> u ` U \<inter> S = {}"
proof -
  have 1: "|U| <o |UNIV::'a set|" using assms(2) using card_of_Un1 ordLeq_ordLess_trans by blast
  obtain B where 2: "U \<inter> B = {}" "B \<inter> (S - U) = {}" "|U| =o |B|"
    using exists_subset_compl[OF assms(1,2)] by blast
  obtain u where 3: "bij u" "|supp u| <o |UNIV::'a set|" "bij_betw u U B" "imsupp u \<inter> (S - U) = {}"
    using ordIso_ex_bij_betw_supp[OF assms(1) 1 2(3,1) Diff_disjoint 2(2)] by blast
  then have "u ` U \<subseteq> B" unfolding bij_betw_def by blast
  then have "u ` U \<inter> S = {}" using 2 by blast
  then show ?thesis using 3 by blast
qed

lemma fst_comp_map_prod: "h \<circ> fst = fst \<circ> map_prod h id" by auto

lemma imsupp_same_subset: "\<lbrakk> a \<notin> B ; a \<in> A ; imsupp f \<inter> A \<subseteq> B \<rbrakk> \<Longrightarrow> f a = a"
  unfolding imsupp_def supp_def by blast

lemma arg_cong3: "\<lbrakk> a1 = a2 ; b1 = b2 ; c1 = c2 \<rbrakk> \<Longrightarrow> h a1 b1 c1 = h a2 b2 c2"
  by simp

lemma exists_bij_betw:
  fixes L R h::"'a \<Rightarrow> 'a"
  assumes "infinite (UNIV::'a set)" "bij R" "bij L" "bij h" "f2 x = h ` f2 y"
    and u: "|f1 (A x) \<union> g (A x)::'a set| <o |UNIV::'a set|" "f1 (A x) \<inter> g (A x) = {}" "f1 (A x) = L ` f2 x"
    and w: "|(f1 (B y)) \<union> (g (B y))::'a set| <o |UNIV::'a set|" "f1 (B y) \<inter> g (B y) = {}" "f1 (B y) = R ` f2 y"
  shows "\<exists>(u::'a \<Rightarrow> 'a) (w::'a \<Rightarrow> 'a).
    bij u \<and> |supp u| <o |UNIV::'a set| \<and> imsupp u \<inter> g (A x) = {} \<and> u ` f1 (A x) \<inter> f1 (A x) = {}
  \<and> bij w \<and> |supp w| <o |UNIV::'a set| \<and> imsupp w \<inter> g (B y) = {} \<and> w ` f1 (B y) \<inter> f1 (B y) = {}
  \<and> eq_on (f2 y) (u \<circ> L \<circ> h) (w \<circ> R)"
proof -
  have 1: "|f1 (A x)| <o |UNIV::'a set|" "|f1 (B y)| <o |UNIV::'a set|"
    using card_of_Un1 card_of_Un2 ordLeq_ordLess_trans u(1) w(1) by blast+
  have "|f1 (A x) \<union> g (A x) \<union> f1 (B y) \<union> g (B y)| <o |UNIV::'a set|" (is "|?A| <o _")
    using card_of_Un_ordLess_infinite[OF assms(1) u(1) w(1)] Un_assoc by metis
  then have "|-?A| =o |UNIV::'a set|"
    by (rule infinite_UNIV_card_of_minus[OF assms(1) _, unfolded Compl_eq_Diff_UNIV[symmetric]])
  then have "|f1 (A x)| <o |-?A|" by (rule ordLess_ordIso_trans[OF 1(1) ordIso_symmetric])

  then obtain C where C: "C \<subseteq> -?A" "|f1 (A x)| =o |C|"
    using ordLess_imp_ordLeq[THEN iffD1[OF internalize_card_of_ordLeq2]] by metis
  then have 3: "f1 (A x) \<inter> C = {}" "C \<inter> g (A x) = {}" "f1 (B y) \<inter> C = {}" "C \<inter> g (B y) = {}" by blast+

  obtain u::"'a \<Rightarrow> 'a" where x: "bij u" "|supp u| <o |UNIV::'a set|" "bij_betw u (f1 (A x)) C" "imsupp u \<inter> g (A x) = {}"
    using ordIso_ex_bij_betw_supp[OF assms(1) 1(1) C(2) 3(1) u(2) 3(2)] by blast

  have "bij_betw (inv R) (f1 (B y)) (f2 y)" unfolding bij_betw_def by (simp add: assms(2) inj_on_def w(3))
  moreover have "bij_betw h (f2 y) (f2 x)" using bij_imp_bij_betw assms(4,5) by auto
  moreover have "bij_betw L (f2 x) (f1 (A x))" unfolding bij_betw_def by (simp add: assms(3) inj_on_def u(3))
  ultimately have 4: "bij_betw (u \<circ> L \<circ> h \<circ> inv R) (f1 (B y)) C" using bij_betw_trans x(3) by blast

  obtain w::"'a \<Rightarrow> 'a" where y: "bij w" "|supp w| <o |UNIV::'a set|" "bij_betw w (f1 (B y)) C"
    "imsupp w \<inter> g (B y) = {}" "eq_on (f1 (B y)) w (u \<circ> L \<circ> h \<circ> inv R)"
    using ex_bij_betw_supp[OF assms(1) 1(2) 4 3(3) w(2) 3(4)] by blast

  have "eq_on (f2 y) (u \<circ> L \<circ> h) (w \<circ> R)" using y(5) unfolding eq_on_def using assms(2) w(3) by auto
  moreover have "u ` f1 (A x) \<inter> f1 (A x) = {}" "w ` f1 (B y) \<inter> f1 (B y) = {}" using bij_betw_imp_surj_on x(3) y(3) 3(1,3) by blast+
  ultimately show ?thesis using x(1,2,4) y(1,2,4) by blast
qed

lemmas exists_bij_betw_refl = exists_bij_betw[OF _ _ _ bij_id image_id[symmetric], unfolded o_id]

lemma imsupp_id_on: "imsupp u \<inter> A = {} \<Longrightarrow> id_on A u"
  unfolding imsupp_def supp_def id_on_def by blast

lemma imsupp_image_subset: "u ` A \<inter> A = {} \<Longrightarrow> A \<subseteq> imsupp u"
  unfolding imsupp_def supp_def by auto

lemma Int_subset_empty1: "A \<inter> B = {} \<Longrightarrow> C \<subseteq> A \<Longrightarrow> C \<inter> B = {}" by blast
lemma Int_subset_empty2: "A \<inter> B = {} \<Longrightarrow> C \<subseteq> B \<Longrightarrow> A \<inter> C = {}" by blast
lemma exists_map_prod_id: "(a, b) \<in> map_prod f id ` A \<Longrightarrow> \<exists>c. (c, b) \<in> A \<and> a = f c" by auto

lemma in_UNIV_simp: "A \<and> x \<in> UNIV \<longleftrightarrow> A" by auto
lemma prod_case_lam_simp: "(\<lambda>y x. (case x of (a, b) \<Rightarrow> f a b) = (case y of (a, b) \<Rightarrow> g a b))
  = (\<lambda>(a1, b1) (a2, b2). f a2 b2 = g a1 b1)" by auto

lemma forall_imp_map_prod_id: "(\<forall>t pd p. (t, pd) \<in> map_prod f id ` A \<longrightarrow> g t pd p) = (\<forall>t pd p. (t, pd) \<in> A \<longrightarrow> g (f t) pd p)"
  by fastforce

lemma image_prod_f_g: "(a, b) \<in> (\<lambda>x. (u x, g (u x))) ` A \<longleftrightarrow> a \<in> u ` A \<and> b = g a" by blast
lemma Int_Un_empty: "A \<inter> (B \<union> C \<union> D) = {} \<longleftrightarrow> A \<inter> B = {} \<and> A \<inter> (C \<union> D) = {}" by blast

lemma image_prod_f_g': "(a, b) \<in> (\<lambda>x. (w x, g x)) ` A = (\<exists>x. x \<in> A \<and> a = w x \<and> b = g x)" by blast
lemma inv_id_middle: "bij u \<Longrightarrow> inv w (g (u z)) = u z \<Longrightarrow> (inv u \<circ> (inv w \<circ> g \<circ> u)) z = id z" by simp
lemma inv_id_middle2: "bij R \<Longrightarrow> bij g \<Longrightarrow> (g \<circ> R) z2 = (u \<circ> L) z2 \<Longrightarrow> (inv R \<circ> (inv g \<circ> u \<circ> L)) z2 = id z2"
  by (metis bij_inv_eq_iff comp_apply id_apply)

lemma eq_onD: "eq_on A u w \<Longrightarrow> z \<in> A \<Longrightarrow> u z = w z"
  unfolding eq_on_def by blast

lemma comp_pair:
  "(\<lambda>(a, b). (a, u a b)) \<circ> (\<lambda>t. (g t, w t)) = (\<lambda>t. (g t, u (g t) (w t)))"
  "(\<lambda>(a, b). (z a, u a b)) \<circ> (\<lambda>t. (g t, w t)) = (\<lambda>t. (z (g t), u (g t) (w t)))"
  by auto

lemma bij_if: "bij g \<Longrightarrow> bij (if P then id else g)" by simp
lemma supp_if: "|supp (u::'a \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> |supp (if P then id else u)| <o |UNIV::'a set|" using supp_id_bound by auto
lemma imsupp_if_empty: "imsupp u \<inter> A = {} \<Longrightarrow> imsupp (if P then id else u) \<inter> A = {}" unfolding imsupp_def supp_def by simp
lemma image_if_empty: "u ` A \<inter> B = {} \<Longrightarrow> (P \<Longrightarrow> A \<inter> B = {}) \<Longrightarrow> (if P then id else u) ` A \<inter> B = {}" by simp

ML_file \<open>../Tools/mrbnf_recursor_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_recursor.ML\<close>

end