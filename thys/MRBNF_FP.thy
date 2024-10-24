theory MRBNF_FP
  imports "MRBNF_Composition"
begin

lemma card_of_subset_bound: "\<lbrakk> B \<subseteq> A ; |A| <o x \<rbrakk> \<Longrightarrow> |B| <o x"
  using card_of_mono1 ordLeq_ordLess_trans by blast
lemma card_of_minus_bound: "|A| <o r \<Longrightarrow> |A - B| <o r"
  by (rule card_of_subset_bound[OF Diff_subset])

lemma exists_subset_compl:
  assumes "Cinfinite r" "r \<le>o |UNIV::'b set|" "|U \<union> S::'b set| <o r"
  shows "\<exists>B. U \<inter> B = {} \<and> B \<inter> S = {} \<and> |U| =o |B|"
proof -
  have 1: "|U| <o r" using assms(3) using card_of_Un1 ordLeq_ordLess_trans by blast
  have "|-(U \<union> S)| =o |UNIV::'b set|"
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

lemma exists_suitable_aux:
  assumes "Cinfinite r" "r \<le>o |UNIV::'a set|" "P \<Longrightarrow> |U \<union> (S - U)::'a set| <o r"
  shows "\<exists>(u::'a \<Rightarrow> 'a). P \<longrightarrow> bij u \<and> |supp u| <o r \<and> imsupp u \<inter> (S - U) = {} \<and> u ` U \<inter> S = {}"
proof -
  have 1: "P \<Longrightarrow> |U| <o r" using assms(3) using card_of_Un1 ordLeq_ordLess_trans by blast
  obtain B where 2: "P \<Longrightarrow> U \<inter> B = {}" "P \<Longrightarrow> B \<inter> (S - U) = {}" "P \<Longrightarrow> |U| =o |B|"
    using exists_subset_compl[OF assms(1,2,3)] by blast
  obtain u where 3: "bij u" "P \<Longrightarrow> |supp u| <o r" "P \<Longrightarrow> bij_betw u U B" "P \<Longrightarrow> imsupp u \<inter> (S - U) = {}"
    using ordIso_ex_bij_betw_supp[OF assms(1) 1 2(3,1) Diff_disjoint 2(2)] by blast
  then have "P \<Longrightarrow> u ` U \<subseteq> B" unfolding bij_betw_def by blast
  then have "P \<Longrightarrow> u ` U \<inter> S = {}" using 2 by blast
  then show ?thesis using 3 by blast
qed

lemma fst_comp_map_prod: "h \<circ> fst = fst \<circ> map_prod h id" by auto

lemma imsupp_same_subset: "\<lbrakk> a \<notin> B ; a \<in> A ; imsupp f \<inter> A \<subseteq> B \<rbrakk> \<Longrightarrow> f a = a"
  unfolding imsupp_def supp_def by blast

lemma arg_cong3: "\<lbrakk> a1 = a2 ; b1 = b2 ; c1 = c2 \<rbrakk> \<Longrightarrow> h a1 b1 c1 = h a2 b2 c2"
  by simp

definition eq_bij_betw where
  "eq_bij_betw r u w g A B x y f1 f2 h L R \<equiv>
    bij u \<and> |supp u| <o r \<and> imsupp u \<inter> g (A x) = {} \<and> u ` f1 (A x) \<inter> f1 (A x) = {}
  \<and> bij w \<and> |supp w| <o r \<and> imsupp w \<inter> g (B y) = {} \<and> w ` f1 (B y) \<inter> f1 (B y) = {}
  \<and> eq_on (f2 y) (u \<circ> L \<circ> h) (w \<circ> R)"

lemma exists_bij_betw:
  fixes L R h::"'a \<Rightarrow> 'a"
  assumes "Cinfinite r" "r \<le>o |UNIV::'a set|" "bij R" "bij L" "bij h" "f2 x = h ` f2 y"
    and u: "|f1 (A x) \<union> g (A x)::'a set| <o r" "f1 (A x) \<inter> g (A x) = {}" "f1 (A x) = L ` f2 x"
    and w: "|(f1 (B y)) \<union> (g (B y))::'a set| <o r" "f1 (B y) \<inter> g (B y) = {}" "f1 (B y) = R ` f2 y"
  shows "\<exists>(u::'a \<Rightarrow> 'a) (w::'a \<Rightarrow> 'a).
    bij u \<and> |supp u| <o r \<and> imsupp u \<inter> g (A x) = {} \<and> u ` f1 (A x) \<inter> f1 (A x) = {}
  \<and> bij w \<and> |supp w| <o r \<and> imsupp w \<inter> g (B y) = {} \<and> w ` f1 (B y) \<inter> f1 (B y) = {}
  \<and> eq_on (f2 y) (u \<circ> L \<circ> h) (w \<circ> R)"
proof -
  have 1: "|f1 (A x)| <o r" "|f1 (B y)| <o r"
    using card_of_Un1 card_of_Un2 ordLeq_ordLess_trans u(1) w(1) by blast+
  then have 2: "|f1 (A x)| <o |UNIV::'a set|" "|f1 (B y)| <o |UNIV::'a set|"
    using ordLess_ordLeq_trans[OF _ assms(2)] by blast+
  have "|f1 (A x) \<union> g (A x) \<union> f1 (B y) \<union> g (B y)| <o r" (is "|?A| <o _")
    using Un_Cinfinite_ordLess[OF u(1) w(1) assms(1)] Un_assoc by metis
  then have "|-?A| =o |UNIV::'a set|"
    apply -
    apply (rule card_of_Un_diff_infinite[of "UNIV::'a set" ?A, unfolded Compl_eq_Diff_UNIV[symmetric]])
     apply (rule cinfinite_imp_infinite)
     apply (rule cinfinite_mono)
      apply (rule assms(2))
     apply (rule conjunct1[OF assms(1)])
    apply (rule ordLess_ordLeq_trans)
     apply assumption
    apply (rule assms(2))
    done
  then have "|f1 (A x)| <o |-?A|" by (rule ordLess_ordIso_trans[OF 2(1) ordIso_symmetric])

  then obtain C where C: "C \<subseteq> -?A" "|f1 (A x)| =o |C|"
    using ordLess_imp_ordLeq[THEN iffD1[OF internalize_card_of_ordLeq2]] by metis
  then have 3: "f1 (A x) \<inter> C = {}" "C \<inter> g (A x) = {}" "f1 (B y) \<inter> C = {}" "C \<inter> g (B y) = {}" by blast+

  obtain u::"'a \<Rightarrow> 'a" where x: "bij u" "|supp u| <o r" "bij_betw u (f1 (A x)) C" "imsupp u \<inter> g (A x) = {}"
    using ordIso_ex_bij_betw_supp[OF assms(1) 1(1) C(2) 3(1) u(2) 3(2)] by blast

  have "bij_betw (inv R) (f1 (B y)) (f2 y)" unfolding bij_betw_def by (simp add: assms(3) inj_on_def w(3))
  moreover have "bij_betw h (f2 y) (f2 x)" using bij_imp_bij_betw assms(5,6) by auto
  moreover have "bij_betw L (f2 x) (f1 (A x))" unfolding bij_betw_def by (simp add: assms(4) inj_on_def u(3))
  ultimately have 4: "bij_betw (u \<circ> L \<circ> h \<circ> inv R) (f1 (B y)) C" using bij_betw_trans x(3) by blast

  obtain w::"'a \<Rightarrow> 'a" where y: "bij w" "|supp w| <o r" "bij_betw w (f1 (B y)) C"
    "imsupp w \<inter> g (B y) = {}" "eq_on (f1 (B y)) w (u \<circ> L \<circ> h \<circ> inv R)"
    using ex_bij_betw_supp[OF assms(1) 1(2) 4 3(3) w(2) 3(4)] by blast

  have "eq_on (f2 y) (u \<circ> L \<circ> h) (w \<circ> R)" using y(5) unfolding eq_on_def using assms(3) w(3) by auto
  moreover have "u ` f1 (A x) \<inter> f1 (A x) = {}" "w ` f1 (B y) \<inter> f1 (B y) = {}" using bij_betw_imp_surj_on x(3) y(3) 3(1,3) by blast+
  ultimately show ?thesis using x(1,2,4) y(1,2,4) by blast
qed

lemmas exists_bij_betw_def = exists_bij_betw[unfolded eq_bij_betw_def[symmetric]]

definition eq_bij_betw_refl where
 "eq_bij_betw_refl r u w g A B x y f1 f2 L R \<equiv>
    bij u \<and> |supp u| <o r \<and> imsupp u \<inter> g (A x) = {} \<and> u ` f1 (A x) \<inter> f1 (A x) = {}
  \<and> bij w \<and> |supp w| <o r \<and> imsupp w \<inter> g (B y) = {} \<and> w ` f1 (B y) \<inter> f1 (B y) = {}
  \<and> eq_on f2 (u \<circ> L) (w \<circ> R)"

lemmas exists_bij_betw_refl = exists_bij_betw[OF _ _ _ _ bij_id image_id[symmetric], unfolded o_id]
lemmas exists_bij_betw_refl_UNIV = exists_bij_betw_refl[OF conjI[OF iffD2[OF cinfinite_iff_infinite] card_of_Card_order] ordLeq_refl[OF card_of_Card_order]]

lemmas exists_bij_betw_refl_def = exists_bij_betw_refl[unfolded eq_bij_betw_refl_def[symmetric]]

lemma imsupp_id_on: "imsupp u \<inter> A = {} \<Longrightarrow> id_on A u"
  unfolding imsupp_def supp_def id_on_def by blast

lemma imsupp_image_subset: "u ` A \<inter> A = {} \<Longrightarrow> A \<subseteq> imsupp u"
  unfolding imsupp_def supp_def by auto

lemma Int_subset_empty1: "A \<inter> B = {} \<Longrightarrow> C \<subseteq> A \<Longrightarrow> C \<inter> B = {}" by blast
lemma Int_subset_empty2: "A \<inter> B = {} \<Longrightarrow> C \<subseteq> B \<Longrightarrow> A \<inter> C = {}" by blast
lemma exists_map_prod_id: "(a, b) \<in> map_prod f id ` A \<Longrightarrow> \<exists>c. (c, b) \<in> A \<and> a = f c" by auto

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
lemma supp_if': "Cinfinite r \<Longrightarrow> |supp u| <o r \<Longrightarrow> |supp (if P then id else u)| <o r" using supp_id_bound' by auto
lemma imsupp_if_empty: "imsupp u \<inter> A = {} \<Longrightarrow> imsupp (if P then id else u) \<inter> A = {}" unfolding imsupp_def supp_def by simp
lemma image_if_empty: "u ` A \<inter> B = {} \<Longrightarrow> (P \<Longrightarrow> A \<inter> B = {}) \<Longrightarrow> (if P then id else u) ` A \<inter> B = {}" by simp

lemma Int_Un_emptyI1: "A \<inter> (B \<union> C) = {} \<Longrightarrow> A \<inter> B = {}" by blast
lemma Int_Un_emptyI2: "A \<inter> (B \<union> C) = {} \<Longrightarrow> A \<inter> C = {}" by blast

lemma imsupp_comp_image: "bij f \<Longrightarrow> imsupp (f \<circ> g \<circ> inv f) = f ` imsupp g"
  apply (auto simp: supp_def imsupp_def bij_inv_eq_iff image_in_bij_eq)
  by (smt (verit, del_insts) imageI inv_simp1 mem_Collect_eq)

lemma id_on_comp3: "c z = z \<Longrightarrow> b (c z) = c z \<Longrightarrow> a z = z \<Longrightarrow> (a \<circ> b \<circ> c) z = z"
  by simp
lemma id_on_comp2: "b z = z \<Longrightarrow> a z = z \<Longrightarrow> (a \<circ> b) z = z" by simp
lemma id_on_both: "a z = z \<Longrightarrow> b z = z \<Longrightarrow> a z = b z" by simp

lemma not_imageI: "bij f \<Longrightarrow> a \<notin> A \<Longrightarrow> f a \<notin> f ` A" by force

lemma Un_bound:
  assumes inf: "infinite (UNIV :: 'a set)"
    and "|A1| <o |UNIV::'a set|" and "|A2| <o |UNIV::'a set|"
  shows "|A1 \<union> A2| <o |UNIV::'a set|"
  using assms card_of_Un_ordLess_infinite by blast

lemma imsupp_supp_bound: "infinite (UNIV::'a set) \<Longrightarrow> |imsupp g| <o |UNIV::'a set| \<longleftrightarrow> |supp g| <o |UNIV::'a set|"
  by (metis Un_bound card_of_image imsupp_def ordLeq_ordLess_trans supp_ordleq_imsupp)

lemma image_imsupp_subset: "f ` A \<subseteq> imsupp f \<union> A"
  unfolding imsupp_def supp_def by auto

lemma Un_mono': "A \<subseteq> C \<union> X \<Longrightarrow> B \<subseteq> D \<union> X \<Longrightarrow> A \<union> B \<subseteq> C \<union> D \<union> X" by blast
lemma Diff_Un_disjunct: "B \<inter> C = {} \<Longrightarrow> A - B \<union> C = (A \<union> C) - B" by blast
lemma UN_empty': "A = {} \<Longrightarrow> \<Union> (B ` A) = {}" by auto

lemma subset_If: "(P \<Longrightarrow> X \<subseteq> A) \<Longrightarrow> (\<not>P \<Longrightarrow> X \<subseteq> B) \<Longrightarrow> X \<subseteq> (if P then A else B)"
  by simp

lemma not_in_imsupp_same: "z \<notin> imsupp f \<Longrightarrow> f z = z"
  unfolding imsupp_def supp_def by blast
lemma not_in_imsupp_same2: "z \<notin> imsupp f \<union> imsupp g \<Longrightarrow> f z = g z"
  using not_in_imsupp_same by (metis UnCI)
lemma Diff_image_not_in_imsupp: "(\<And>x. x \<in> B \<Longrightarrow> x \<notin> imsupp f) \<Longrightarrow> f ` A - B = f ` (A - B)"
  unfolding supp_def imsupp_def by fastforce
lemma ball_not_eq_imsupp: "x \<in> B \<Longrightarrow> x \<notin> A \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> x \<notin> imsupp f) \<Longrightarrow> \<forall>xa\<in>A. x \<noteq> f xa"
  unfolding imsupp_def supp_def by fastforce

definition compSS :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "compSS f g \<equiv> f \<circ> g \<circ> inv f"

lemma compSS_comp0:
  fixes f g h::"'a \<Rightarrow> 'a"
  assumes "infinite (UNIV::'a set)" "bij f" "|supp f| <o |UNIV::'a set|" "bij g" "|supp g| <o |UNIV::'a set|" "|supp h| <o |UNIV::'a set|"
  shows "(compSS f \<circ> compSS g) h = compSS (f \<circ> g) h"
proof -
  have "|supp (g \<circ> h \<circ> inv g)| <o |UNIV::'a set|"
    by (simp add: supp_comp_bound assms supp_inv_bound)
  then show ?thesis unfolding compSS_def
    by (simp add: comp_assoc[symmetric] o_inv_distrib assms)
qed

lemma compSS_cong_id:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "bij f" "|supp p| <o |UNIV::'a set|" and cong: "\<And>a. a \<in> imsupp p \<Longrightarrow> f a = a"
  shows "compSS f p = p"
proof -
  have 1: "imsupp f \<inter> imsupp p = {}"
    by (meson Int_emptyI assms(1) bij_imsupp_supp_ne cong not_in_supp_alt)
  then show ?thesis unfolding compSS_def using imsupp_commute
    by (metis assms(1) bij_is_surj inv_inv_eq o_inv_o_cancel surj_imp_inj_inv)
qed

lemma imsupp_compSS:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "infinite (UNIV::'a set)" "bij f" "|supp f| <o |UNIV::'a set|" "|supp p| <o |UNIV::'a set|"
  shows "imsupp (compSS f p) = f ` imsupp p"
  unfolding compSS_def
  using assms(2) by (rule imsupp_comp_image)

lemma comp_middle: "f (h z) = h z \<Longrightarrow> g (h z) = h z \<Longrightarrow> (f \<circ> g \<circ> h) z = h z"
  by simp

(* tvsubst helper lemmas *)
lemma bij_not_eq_twice: "bij g \<Longrightarrow> g a \<noteq> a \<Longrightarrow> g (g a) \<noteq> g a"
  by simp
lemma bij_not_equal_iff: "bij f \<Longrightarrow> a \<noteq> b \<longleftrightarrow> f a \<noteq> f b"
  by simp
lemma bij_id_imsupp: "bij f \<Longrightarrow> f a = a \<Longrightarrow> a \<notin> imsupp f"
  unfolding imsupp_def supp_def
  by (simp add: bij_inv_eq_iff image_in_bij_eq)
lemma id_o_commute: "id \<circ> f = f \<circ> id" by simp
lemma fst_o_f: "fst \<circ> (\<lambda>(x, y). (f x, g x y)) = f \<circ> fst"
  by auto
lemma exists_fresh: "|A::'a set| <o |UNIV::'a set| \<Longrightarrow> \<exists>a::'a. a \<notin> A"
  by (metis UNIV_eq_I ordLess_irreflexive)
lemma swap_fresh: "y \<notin> A \<Longrightarrow> x \<in> id(x := y, y := x) ` A \<Longrightarrow> False"
  by auto
lemma forall_in_eq_UNIV: "\<forall>c. (c::'a) \<in> X \<Longrightarrow> X = (UNIV :: 'a set)" by blast
lemma image_const: "a \<in> X \<Longrightarrow> \<forall>c. c \<in> (\<lambda>_. c) ` X" by simp
lemma ordIso_ordLess_False: "a =o b \<Longrightarrow> a <o b \<Longrightarrow> False"
  by (simp add: not_ordLess_ordIso)
lemma Union_UN_swap: "\<Union> (\<Union>x\<in>A. P x) = (\<Union>x\<in>A. \<Union>(P x))" by blast
lemma UN_cong: "(\<And>x. x \<in> A \<Longrightarrow> P x = Q x) \<Longrightarrow> \<Union>(P ` A) = \<Union>(Q ` A)" by simp
lemma supp_swap_bound: "infinite (UNIV :: 'a set) \<Longrightarrow> |supp (id (x := y, y := x :: 'a))| <o |UNIV::'a set|"
  by (rule ordLeq_ordLess_trans[OF card_of_mono1[OF supp_swap_le] finite_ordLess_infinite2])
    (auto simp: cinfinite_imp_infinite)
lemma UN_single: "\<Union>(f ` {a}) = f a" by simp

lemma disjointI: "(\<And>x. x \<in> A \<Longrightarrow> x \<notin> B) \<Longrightarrow> A \<inter> B = {}"
  by blast
lemma notin_empty_eq_True: "x \<notin> {} = True"
  by simp
lemma disjoint_single: "{x} \<inter> A = {} \<longleftrightarrow> x \<notin> A"
  by blast

lemma finite_singleton: "finite {x}" by blast

lemma ex_avoiding_bij:
  fixes f :: "'a \<Rightarrow> 'a" and I D A :: "'a set"
  assumes  "|supp f| <o |UNIV :: 'a set|" "bij f" "infinite (UNIV :: 'a set)"
    "|I| <o |UNIV :: 'a set|" "id_on I f"
    "|D| <o |UNIV :: 'a set|" "D \<inter> A = {}" "|A| <o |UNIV :: 'a set|"
  shows "\<exists>(g::'a \<Rightarrow> 'a). bij g \<and> |supp g| <o |UNIV::'a set| \<and> imsupp g \<inter> A = {} \<and>
    (\<forall>a. a \<in> (imsupp f - A) \<union> D \<and> f a \<notin> A \<longrightarrow> g a = f a) \<and> id_on I g"
  apply (rule exI[of _ "avoiding_bij f I D A"])
  apply (rule conjI avoiding_bij assms)+
  done

lemma id_on_empty: "id_on {} f"
  unfolding id_on_def by simp

lemma image_Int_empty: "bij f \<Longrightarrow> f ` A \<inter> B = {} \<longleftrightarrow> A \<inter> inv f ` B = {}"
  by force
lemma eq_bij_betw_refl_prems:
  assumes "eq_bij_betw_refl r u w g A B x y f1 f2 L R"
  shows "bij u" "|supp u| <o r"
    "bij w" "|supp w| <o r"
  using assms unfolding eq_bij_betw_refl_def by auto
lemma eq_bij_betw_refl_imsupp:
  assumes "eq_bij_betw_refl r u w g A B x y f1 f2 L R"
  shows "imsupp u \<inter> g (A x) = {} \<and> imsupp w \<inter> g (B y) = {}"
  using assms unfolding eq_bij_betw_refl_def by auto
lemma eq_bij_betw_prems:
  assumes "eq_bij_betw r u w g A B x y f1 f2 h L R"
  shows "bij u" "|supp u| <o r"
    "bij w" "|supp w| <o r"
  using assms unfolding eq_bij_betw_def by auto
lemma id_on_eq: "id_on A f \<Longrightarrow> id_on B g \<Longrightarrow> A = B \<Longrightarrow> x \<in> A \<Longrightarrow> f x = g x"
  unfolding id_on_def by simp

lemma notin_supp: "x \<notin> supp f \<Longrightarrow> f x = x"
  unfolding supp_def by blast

lemmas imsupp_id_empty = trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left]

lemma pred_fun_If: "pred_fun P Q f \<Longrightarrow> pred_fun P Q (\<lambda>x. if P x then f x else undefined)"
  by simp
lemma snd_comp_mk_prod: "snd \<circ> (\<lambda>x. (g x, f x)) = f"
  by auto

lemma supp_id_bound_cmin: "Card_order r \<Longrightarrow> |supp (id::'a \<Rightarrow> _)| <o r \<Longrightarrow> |supp (id::'a \<Rightarrow> _)| <o cmin |UNIV| r"
  using cmin_greater supp_id_bound by blast

lemma Int_image_imsupp: "imsupp f \<inter> A = {} \<Longrightarrow> A \<inter> f ` B = {} \<longleftrightarrow> A \<inter> B = {}"
  unfolding imsupp_def supp_def by (smt (verit) UnCI disjoint_iff image_iff mem_Collect_eq)

lemma Collect_prod_beta: "{(x, y). P x y} = {p. P (fst p) (snd p)}"
  by auto

lemma prod_sets_simps:
  "\<Union>(Basic_BNFs.fsts ` A) = fst ` A"
  "\<Union>(Basic_BNFs.snds ` A) = snd ` A"
  by force+

lemmas induct_impliesI = impI[unfolded HOL.induct_implies_def[symmetric]]
lemmas induct_impliesE = impE[unfolded HOL.induct_implies_def[symmetric]]
lemmas induct_mp = mp[unfolded HOL.induct_implies_def[symmetric]]
lemmas induct_conjI = conjI[unfolded HOL.induct_conj_def[symmetric]]
lemmas induct_forallI = allI[unfolded HOL.induct_forall_def[symmetric]]

lemma induct_equal_refl: "HOL.induct_equal x x"
  unfolding HOL.induct_equal_def by (rule refl)

lemma large_imp_infinite: "natLeq \<le>o |UNIV::'a set| \<Longrightarrow> infinite (UNIV::'a set)"
  using infinite_iff_natLeq_ordLeq by blast

lemma insert_bound: "infinite (UNIV::'a set) \<Longrightarrow> |insert x A| <o |UNIV::'a set| \<longleftrightarrow> |A| <o |UNIV::'a set|"
  by (metis card_of_Un_singl_ordLess_infinite insert_is_Un)

ML_file \<open>../Tools/mrbnf_fp_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_fp_def_sugar.ML\<close>
ML_file \<open>../Tools/mrbnf_fp.ML\<close>

ML_file \<open>../Tools/mrbnf_recursor_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_recursor.ML\<close>

lemma extend_fresh:
  fixes A B::"'a set"
  assumes "|B| <o |UNIV::'a set|" "|B| <o |UNIV::'a set| \<Longrightarrow> |A \<union> B| <o |UNIV::'a set|" "infinite (UNIV::'a set)"
  shows "\<exists>\<rho>. bij \<rho> \<and> |supp \<rho>| <o |UNIV::'a set| \<and> \<rho> ` B \<inter> A = {} \<and> \<rho> ` B \<inter> B = {} \<and> id_on (A - B) \<rho> \<and> (\<forall>x. \<rho> (\<rho> x) = x)"
  using eextend_fresh[of B "A \<union> B" "A - B", OF assms(1,2,3), OF assms(1)]
  unfolding Int_Un_distrib fun_eq_iff o_apply id_apply
  by blast

named_theorems refresh_extends
named_theorems refresh_smalls
named_theorems refresh_simps
named_theorems refresh_intros
named_theorems refresh_elims

ML \<open>
local
  open BNF_Util
  open BNF_FP_Util
in

fun refreshability_tac verbose supps instss G_thm eqvt_thm smalls simps ctxt =
  let
    val extend_thms = Named_Theorems.get ctxt "MRBNF_FP.refresh_extends";
    val small_thms = smalls @ Named_Theorems.get ctxt "MRBNF_FP.refresh_smalls";
    val simp_thms = simps @ Named_Theorems.get ctxt "MRBNF_FP.refresh_simps";
    val intro_thms = Named_Theorems.get ctxt "MRBNF_FP.refresh_intros";
    val elim_thms = Named_Theorems.get ctxt "MRBNF_FP.refresh_elims";
    val n = length supps;
    fun case_tac NONE _ prems ctxt = HEADGOAL (Method.insert_tac ctxt prems THEN' 
        K (if verbose then print_tac ctxt "pre_simple_auto" else all_tac)) THEN SOLVE (auto_tac ctxt)
      | case_tac (SOME insts) params prems ctxt =
        let
val _ = prems |> map (Thm.pretty_thm ctxt #> verbose ? @{print tracing});
          fun mk_supp ts = @{map 2} (fn s => fn t => s $ t) supps ts |>
            Library.foldl1 (HOLogic.mk_binop \<^const_name>\<open>sup\<close>)
          val (defs, assms) = chop (n + 1) prems;
          val Bts = defs
            |> map (fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of);
          val B = hd Bts;
          val ts = tl Bts;
          val other_tss = assms
            |> filter (can (fn thm => thm RSN (3, eqvt_thm)))
            |> map (snd o strip_comb o HOLogic.dest_Trueprop o Thm.prop_of);
          val A = map mk_supp (ts :: other_tss)
            |> Library.foldl1 (HOLogic.mk_binop \<^const_name>\<open>sup\<close>);
          val fresh = infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt B), SOME (Thm.cterm_of ctxt A)]
            @{thm extend_fresh};
          val _ = (verbose ? @{print tracing}) fresh

          fun case_inner_tac fs fprems ctxt =
            let 
              val _ = (verbose ? @{print tracing}) fs
              val f = hd fs |> snd |> Thm.term_of;
              val ex_f = infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt f)] exI;
              val ex_B' = infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt (mk_image f $ B))] exI;
              val args = params |> map (snd #> Thm.term_of);
              val xs = @{map 2} (fn i => fn a => Thm.cterm_of ctxt
                (case i of SOME t => t $ f $ a | NONE => a)) insts args;
val _ = fprems |> map (Thm.pretty_thm ctxt #> verbose ? @{print tracing});
              val eqvt_thm = eqvt_thm OF take 2 fprems;
              val extra_assms = assms RL (eqvt_thm :: extend_thms);
              val id_onI = fprems RL @{thms id_on_antimono};
val _ = extra_assms |> map (Thm.pretty_thm ctxt #> verbose ? @{print tracing});
            in
              HEADGOAL (rtac ctxt ex_B' THEN' rtac ctxt conjI THEN'
                REPEAT_ALL_NEW (resolve_tac ctxt (conjI :: fprems)) THEN'
                K (if verbose then print_tac ctxt "pre_inst" else all_tac) THEN'
                EVERY' (map (fn x => rtac ctxt (infer_instantiate' ctxt [NONE, SOME x] exI)) xs) THEN'
                Method.insert_tac ctxt (assms @ extra_assms @ fprems) THEN'
                SELECT_GOAL (unfold_tac ctxt defs) THEN'
                K (if verbose then print_tac ctxt "pre_auto" else all_tac) THEN'
                SELECT_GOAL (mk_auto_tac (ctxt
                  addsimps (simp_thms @ defs @ fprems)
                  addSIs (ex_f :: id_onI @ intro_thms)
                  addSEs elim_thms) 0 10) THEN_ALL_NEW (SELECT_GOAL (print_tac ctxt "auto failed")))
            end;
          val small_ctxt = ctxt addsimps small_thms;
        in EVERY1 [
          rtac ctxt (fresh RS exE),
          SELECT_GOAL (auto_tac (small_ctxt addsimps [hd defs])),
          REPEAT_DETERM_N 2 o (asm_simp_tac small_ctxt),
          SELECT_GOAL (unfold_tac ctxt @{thms Int_Un_distrib Un_empty}),
          REPEAT_DETERM o etac ctxt conjE,
          Subgoal.SUBPROOF (fn focus =>
            case_inner_tac (#params focus) (#prems focus) (#context focus)) ctxt
        ] end;
  in
    unfold_tac ctxt @{thms conj_disj_distribL ex_disj_distrib} THEN EVERY1 [
      rtac ctxt (G_thm RSN (2, cut_rl)),
      REPEAT_ALL_NEW (eresolve_tac ctxt @{thms exE conjE disj_forward}),
      EVERY' (map (fn insts => Subgoal.SUBPROOF (fn focus =>
        case_tac insts (#params focus) (#prems focus) (#context focus)) ctxt) instss)
    ]
  end;

end;
\<close>

end
