theory Prelim
  imports Card_Prelim
begin

declare bij_imp_bij_inv[simp]
declare bij_comp[simp]
declare bij_id[intro!]
declare map_prod.id[simp]
declare eq_OO[simp] declare OO_eq[simp]
declare inv_inv_eq[simp]

lemma bij_imp_bij_betw: "bij f \<Longrightarrow> bij_betw f A (f ` A)"
  apply(rule inj_on_imp_bij_betw) unfolding bij_def inj_def inj_on_def by auto

lemma bij_bij_betw_inv: "bij u \<Longrightarrow> bij_betw u A B = bij_betw (inv u) B A"
  by (metis bij_betw_imp_inj_on bij_betw_imp_surj_on bij_imp_bij_betw bij_imp_bij_inv image_inv_f_f)

lemma conversep_def:
"conversep r = (\<lambda> a b. r b a)" by auto

lemma bij_comp2: "bij u \<Longrightarrow> bij v \<Longrightarrow> bij (\<lambda>a. v (u a))"
  unfolding o_def[symmetric] using bij_comp by blast

lemma snd_o_is_snd:"snd \<circ> (\<lambda>(x, y). (f0 (x, y), y)) = snd"
  by fastforce

lemma fst_o_is_fst:"fst \<circ> (\<lambda>(x, y). (x, f0 (x, y))) = fst"
  by fastforce

lemma bij_implies_inject: "bij f \<Longrightarrow> f a = f a' \<longleftrightarrow> a = a'"
  unfolding bij_def inj_on_def by auto

lemma inv_simp1[simp]: "bij u \<Longrightarrow> inv u (u x) = x"
  by (simp add: bij_is_inj)

lemma inv_o_simp1[simp]: "bij u \<Longrightarrow> inv u \<circ> u = id"
  unfolding o_def by auto

lemma inv_simp2[simp]: "bij u \<Longrightarrow> u (inv u x) = x"
  by (simp add: bij_is_surj surj_f_inv_f)

lemma inv_o_simp2[simp]: "bij u \<Longrightarrow> u \<circ> inv u = id"
  unfolding o_def by auto

lemma bij_inv_rev: "bij f \<Longrightarrow> a = inv f b \<longleftrightarrow> b = f a"
  by auto

lemma case_in[case_names L uL not]:
  assumes "a \<in> L \<Longrightarrow> P" and "a \<notin> L \<Longrightarrow> a \<in> u ` L \<Longrightarrow> P" and "a \<notin> L \<Longrightarrow> a \<notin> u ` L \<Longrightarrow> P"
  shows P  using assms by auto

(* Properties of bijections *)
lemma bij_iff:
  "bij u \<longleftrightarrow> (\<exists> v. v \<circ> u = id \<and> u \<circ> v = id)"
  by (meson bij_is_inj bij_is_surj inv_o_cancel o_bij surj_iff)

lemma bij_iff1:
  "bij u \<longleftrightarrow> (\<exists> v. bij v \<and> v \<circ> u = id \<and> u \<circ> v = id)"
  by (meson bij_is_inj bij_is_surj inv_o_cancel o_bij surj_iff)

(* Combinators: *)
definition id_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "id_on A f \<equiv> \<forall> a. a \<in> A \<longrightarrow> f a = a"

lemma id_onI: "(\<And>a. a \<in> A \<Longrightarrow> f a = a) \<Longrightarrow> id_on A f"
  unfolding id_on_def by blast

lemma id_on_id[simp,intro!]: "id_on A id"
  unfolding id_on_def by auto

lemma id_on_insert[simp]: "id_on (insert x A) f \<longleftrightarrow> f x = x \<and> id_on A f"
  unfolding id_on_def by blast

lemma id_on_Diff: "id_on (A - B) f \<Longrightarrow> id_on B f \<Longrightarrow> id_on A f"
  unfolding id_on_def by blast

definition "eq_on A f g \<equiv> \<forall> a. a \<in> A \<longrightarrow> f a = g a"

lemma eq_onI: "(\<And>a. a \<in> A \<Longrightarrow> f a = g a) \<Longrightarrow> eq_on A f g"
  unfolding eq_on_def by simp

lemma eq_on_refl[simp,intro!]: "eq_on A f f" unfolding eq_on_def by auto

lemma eq_on_sym: "eq_on A f g \<Longrightarrow> eq_on A g f" unfolding eq_on_def by auto

lemma eq_on_trans: "eq_on A f g \<Longrightarrow> eq_on A g h \<Longrightarrow> eq_on A f h" unfolding eq_on_def by auto

lemma eq_on_mono: "A \<subseteq> B \<Longrightarrow> eq_on B f g \<Longrightarrow> eq_on A f g" unfolding eq_on_def by auto

lemma eq_on_emp[simp,intro!]: "eq_on {} f g" unfolding eq_on_def by auto

lemma eq_on_inv1: "bij f \<Longrightarrow> bij g \<Longrightarrow> eq_on A f g \<Longrightarrow> eq_on (f ` A) (inv f) (inv g)"
  unfolding eq_on_def by (metis image_iff inv_simp1)

lemma eq_on_inv2: "bij f \<Longrightarrow> bij g \<Longrightarrow> eq_on A f g \<Longrightarrow> eq_on (g ` A) (inv f) (inv g)"
  unfolding eq_on_def by (metis image_iff inv_simp1)

lemma eq_on_comp1: "eq_on A g1 g2 \<Longrightarrow> eq_on (g1 ` A) f1 f2 \<Longrightarrow> eq_on A (f1 \<circ> g1) (f2 \<circ> g2)"
  unfolding eq_on_def by simp
lemma eq_on_comp2: "eq_on A g1 g2 \<Longrightarrow> eq_on (g2 ` A) f1 f2 \<Longrightarrow> eq_on A (f1 \<circ> g1) (f2 \<circ> g2)"
  unfolding eq_on_def by simp

lemma id_on_image_comp: "bij g \<Longrightarrow> id_on A f \<Longrightarrow> id_on B g \<Longrightarrow> (inv g \<circ> f) ` A = B \<Longrightarrow> A = B"
  unfolding id_on_def by fastforce

lemma eq_on_image: "eq_on A f g \<Longrightarrow> f ` A = g ` A"
  unfolding eq_on_def by auto

lemma eq_on_between: "bij f \<Longrightarrow> bij g \<Longrightarrow> bij f2 \<Longrightarrow> bij g2 \<Longrightarrow> eq_on A f g \<Longrightarrow>
  eq_on B f2 g2 \<Longrightarrow> (inv g2 \<circ> g) ` A = B \<Longrightarrow> eq_on A (inv f2 \<circ> f) (inv g2 \<circ> g)"
  unfolding eq_on_def by (metis bij_pointE comp_eq_dest_lhs imageI inv_simp1)

lemma eq_on_inv_f_f: "bij f \<Longrightarrow> eq_on (f ` A) g1 g2 \<Longrightarrow> eq_on A (inv f \<circ> g1 \<circ> f) (inv f \<circ> g2 \<circ> f)"
  unfolding eq_on_def by simp

(* The support of f: *)
definition supp :: "('a \<Rightarrow> 'a) => 'a set" where
  "supp f \<equiv> {a . f a \<noteq> a}"

(* The support of f factoring in image too: *)
definition imsupp :: "('a \<Rightarrow> 'a) => 'a set" where
  "imsupp f \<equiv> supp f \<union> f ` supp f"

lemma supp_id: "supp id = {}"
  unfolding supp_def by auto

lemma imsupp_id: "imsupp id = {}"
  unfolding imsupp_def supp_id by auto

lemma imsupp_id_fun_upd: "imsupp (id(a:=b)) = (if a = b then {} else {a, b})"
  unfolding imsupp_def supp_def by auto

lemma imsupp_empty_IntD1: "A \<inter> imsupp f = {} \<Longrightarrow> f x \<in> A \<longleftrightarrow> x \<in> A"
  unfolding imsupp_def supp_def by force
lemma imsupp_empty_IntD2: "A \<inter> imsupp f = {} \<Longrightarrow> x \<in> A \<Longrightarrow> f x = x"
  unfolding imsupp_def supp_def by force
lemma in_imsupp: "f x \<in> imsupp f \<longleftrightarrow> x \<in> imsupp f"
  unfolding imsupp_def supp_def by auto

lemma supp_inv:
  assumes "bij f"
  shows "supp (inv f) = f ` (supp f)"
  using assms unfolding supp_def apply auto
  by (smt CollectI UNIV_I bij_betw_inv_into_right image_iff)

lemma supp_o:
  "supp (g \<circ> f) \<subseteq> supp g \<union> supp f"
  unfolding supp_def by auto

lemma finite_supp_comp: "finite (supp f) \<Longrightarrow> finite (supp g) \<Longrightarrow> finite (supp (g \<circ> f))"
  using supp_o by (metis finite_UnI finite_subset)

declare card_of_Card_order[intro]
declare card_of_card_order_on[intro]

lemma infinite_imsupp_ordLeq_supp:
  assumes "infinite (supp f)"
  shows "|imsupp f| \<le>o |supp f|"
  unfolding imsupp_def
  by (rule card_of_Un_ordLeq_infinite_Field) (auto simp: assms)

lemma supp_incl_imsupp:
  "supp f \<subseteq> imsupp f" unfolding imsupp_def by auto

lemma supp_ordleq_imsupp:
  "|supp f| \<le>o |imsupp f|"
  using card_of_mono1[OF supp_incl_imsupp] .

lemma imsupp_commute: "imsupp f \<inter> imsupp g = {} \<Longrightarrow> f \<circ> g = g \<circ> f"
proof (rule ext, goal_cases ext)
  case (ext x)
  then show ?case by (cases "f x = x"; cases "g x = x") (auto simp: imsupp_def supp_def)
qed

lemma imsupp_idle:
  assumes "imsupp f \<inter> imsupp g = {}" and "g a \<in> imsupp f"
  shows "g a = a"
  using assms unfolding imsupp_def supp_def by auto

lemma imsupp_idle2:
  assumes "imsupp g \<inter> imsupp f = {}"
  shows "f a = a \<or> g (f a) = f a"
  using assms unfolding imsupp_def supp_def by auto

lemma imsupp_inv:
  assumes "bij f"
  shows "imsupp (inv f) = imsupp f"
  using assms unfolding imsupp_def supp_def
  by (fastforce simp: bij_def inv_f_eq bij_is_surj surj_f_inv_f
      bijection.inv_right_eq_iff bijection.intro)

lemma imsupp_o: "imsupp (g \<circ> f) \<subseteq> imsupp g \<union> imsupp f"
  unfolding imsupp_def unfolding supp_def by auto

lemma imsupp_disj_comp:
  assumes "A \<inter> imsupp g1 = {}" and "A \<inter> imsupp g2 = {}"
  shows "A \<inter> imsupp (g2 \<circ> g1) = {}"
  using assms by (smt UnE disjoint_iff_not_equal imsupp_o subsetCE)

lemma infinite_imsupp_ordIso_supp:
  assumes "infinite (supp f)"
  shows "|imsupp f| =o |supp f|"
  by (simp add: assms infinite_imsupp_ordLeq_supp ordIso_iff_ordLeq supp_ordleq_imsupp)

lemma UNIV_prod: "UNIV = UNIV \<times> UNIV"
  by auto

lemma bij_the_inv_revert: "bij f \<Longrightarrow> (x = the_inv f y) = (f x = y)"
  using bij_is_inj bij_is_surj f_the_inv_into_f the_inv_f_f by fastforce

(* Bijecive wrapper: *)

definition asBij :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "asBij f \<equiv> if bij f then f else id"

lemma bij_impl_asBij[simp]: "bij f \<Longrightarrow> asBij f = f"
  by (simp add: asBij_def)

lemma bij_asBij: "bij (asBij f)" unfolding asBij_def by auto

lemma inj_asBij: "inj (asBij f)" using bij_asBij
  unfolding bij_def by auto


(*****)
(* Extension of a "bijection-between" two disjoint sets of the same type to one on the whole universe: *)
definition extU :: "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
  where "extU L K gg a \<equiv> if a \<in> L then gg a else if a \<in> K then the_inv_into L gg a else a"

lemma extU:
  assumes gg: "bij_betw gg L K" and LK: "L \<inter> K = {}"
  shows "bij (extU L K gg) \<and> eq_on L (extU L K gg) gg \<and> bij_betw (extU L K gg) L K \<and>
       eq_on K (extU L K gg) (the_inv_into L gg) \<and>
       supp (extU L K gg) \<subseteq> L \<union> K \<and> imsupp (extU L K gg) \<subseteq> L \<union> K \<and>
       id_on (- (L \<union> K)) (extU L K gg)"
proof(intro conjI)
  let ?g = "extU L K gg" note g = extU_def[abs_def, simp]
  note bij_betw_def[simp] inj_on_def[simp]
  show "bij ?g"
    using LK unfolding bij_def inj_on_def image_def apply (auto simp del: bij_implies_inject)
    apply (metis bij_betw_def f_the_inv_into_f gg)
    apply (metis bij_betwE bij_betw_the_inv_into disjoint_iff_not_equal gg)
    apply (metis bij_betw_def gg order_refl the_inv_into_into)
    apply (metis bij_betwE bij_betw_the_inv_into disjoint_iff_not_equal gg)
    using gg apply (auto simp add: the_inv_into_f_eq simp del: bij_implies_inject)
    by (smt IntI LK bij_betw_def empty_iff f_the_inv_into_f gg id_apply imageI the_inv_into_onto)
      (*  *)
  show "eq_on L ?g gg" unfolding eq_on_def by auto
  thus "bij_betw ?g L K" using gg by (auto simp del: bij_implies_inject)
  show "eq_on K ?g (the_inv_into L gg)" using LK unfolding eq_on_def by auto
  show "supp ?g \<subseteq> L \<union> K" unfolding supp_def by auto
  thus "imsupp ?g \<subseteq> L \<union> K" using LK unfolding imsupp_def apply auto
    using bij_betwE gg apply blast by (meson bij_betwE bij_betw_the_inv_into gg)
  show "id_on (- (L \<union> K)) ?g" by (auto simp: id_on_def)
qed

lemmas bij_extU = extU[THEN conjunct1]
lemmas eq_on_extU = extU[THEN conjunct2, THEN conjunct1]
lemmas bij_betw_extU = extU[THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas eq_on_inv_betw_extU = extU[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas supp_inv_betw_extU = extU[THEN conjunct2, THEN conjunct2,
    THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas imsupp_inv_betw_extU = extU[THEN conjunct2, THEN conjunct2,
    THEN conjunct2, THEN conjunct2, THEN conjunct2]

lemma cinfinite_imp_infinite: "cinfinite |A| \<Longrightarrow> infinite A"
  by (simp add: cinfinite_def)
lemma cinfinite_iff_infinite: "cinfinite |A| = infinite A"
  by (simp add: cinfinite_def)

lemma ex_bij_betw_supp:
  fixes A B C :: "'a set"
  assumes i: "Cinfinite r" and
  bound: "|A| <o r"
  and AB: "bij_betw uu A B" and emp: "A \<inter> B = {}" "A \<inter> C = {}" "B \<inter> C = {}"
shows "EX u. bij u \<and> |supp u| <o r \<and> bij_betw u A B \<and> imsupp u \<inter> C = {} \<and>
             eq_on A u uu"
proof-
  have abo: "|A| =o |B|" using AB
    using card_of_ordIso by blast
  hence b2: "|B| <o r" using bound
    using ordIso_ordLess_trans ordIso_symmetric by blast
  define u where "u \<equiv> extU A B uu"
  show ?thesis apply(rule exI[of _ u])
    using extU[OF AB emp(1), unfolded u_def[symmetric]] apply auto
    apply (meson Un_Cinfinite_bound_strict b2 bound card_of_mono1 i ordLeq_ordLess_trans)
  using assms by auto
qed

lemmas ex_bij_betw_supp_UNIV = ex_bij_betw_supp[OF conjI[OF iffD2[OF cinfinite_iff_infinite] card_of_Card_order],
    of "UNIV::'a set" "_::'a set"]

lemma ex_bij_betw_supp':
  fixes A B C :: "'a set"
  assumes i: "Cinfinite r" and
  bound: "|A| <o r"
  and AB: "bij_betw uu A B" and int: "eq_on (A\<inter>B) uu id"
shows "\<exists> u. bij u \<and> |supp u| <o r \<and> bij_betw u A B \<and> eq_on A u uu"
proof-
  define AA BB CC where AA: "AA = A - B" and BB: "BB = B - A" and CC: "CC = A \<inter> B"
  note defs = AA BB CC
  have 0: "|AA| <o r"
  "bij_betw uu AA BB" "AA \<inter> BB = {}" "AA \<inter> CC = {}" "BB \<inter> CC = {}"
     subgoal using AA bound card_of_diff ordLeq_ordLess_trans by blast
     subgoal by (smt (verit, del_insts) AA AB BB DiffE DiffI Diff_Diff_Int bij_betw_iff_bijections
               eq_on_def id_apply int)
     subgoal unfolding defs by auto
     subgoal unfolding defs by auto
     subgoal unfolding defs by auto .
  show ?thesis using ex_bij_betw_supp[OF i 0]
  apply safe subgoal for u apply(rule exI[of _ u], safe)
    subgoal by (smt (verit, ccfv_SIG) AA AB CC DiffI Diff_Diff_Int bij_betw_cong
      eq_on_def id_apply imsupp_empty_IntD2 inf_commute int)
    subgoal by (smt (verit, best) AA CC DiffI Diff_Diff_Int Int_commute eq_on_def
      id_apply imsupp_empty_IntD2 int) . .
qed

lemma ordIso_ex_bij_betw_supp:
  fixes A B C :: "'a set"
  assumes i: "Cinfinite r" and
  bound: "|A| <o r"
  and AB: "|A| =o |B|" and emp: "A \<inter> B = {}" "A \<inter> C = {}" "B \<inter> C = {}"
shows "EX u. bij u \<and> |supp u| <o r \<and> bij_betw u A B \<and> imsupp u \<inter> C = {}"
proof-
  obtain uu where AB: "bij_betw uu A B"
    using AB unfolding card_of_ordIso[symmetric] by blast
  have "EX u. bij u \<and> |supp u| <o r \<and> bij_betw u A B \<and> imsupp u \<inter> C = {}
    \<and> eq_on A u uu"
  apply(rule ex_bij_betw_supp) using assms AB by auto
  thus ?thesis by auto
qed
lemmas ordIso_ex_bij_betw_supp_UNIV = ordIso_ex_bij_betw_supp[OF conjI[OF iffD2[OF cinfinite_iff_infinite] card_of_Card_order],
    of "UNIV::'a set" "_::'a set"]

abbreviation Grp where "Grp \<equiv> BNF_Def.Grp UNIV"

lemma Grp_o: "Grp (f o g) = Grp g OO Grp f"
  unfolding Grp_def fun_eq_iff relcompp_apply by auto

lemma bij_imp_inv: "bij f \<Longrightarrow> (inv f a = a) \<longleftrightarrow> f a = a"
  by (metis inv_simp1 inv_simp2)

lemma bij_imp_inv': "bij f \<Longrightarrow> (inv f a = b) \<longleftrightarrow> f b = a"
  by (metis inv_simp1 inv_simp2)

lemma two_inv: "bij u \<Longrightarrow> bij v \<Longrightarrow> inv u \<circ> inv v \<circ> (v \<circ> u) = id"
  by auto

lemma id_on_image: "id_on A f \<Longrightarrow> f ` A = A"
  unfolding id_on_def by (auto simp: image_iff)

lemma id_on_comp: "id_on A g \<Longrightarrow> id_on A (f o g) = id_on (g ` A) f"
  unfolding id_on_def by auto

lemma id_onD: "id_on A f \<Longrightarrow> x \<in> A \<Longrightarrow> f x = x"
  unfolding id_on_def by auto

lemma id_on_inv: "bij f \<Longrightarrow> id_on A f \<Longrightarrow> id_on A (inv f)"
  unfolding id_on_def by (simp add: bij_imp_inv)

lemma id_on_antimono: "id_on A f \<Longrightarrow> B \<subseteq> A \<Longrightarrow> id_on B f"
  unfolding id_on_def by auto

lemma id_on_inv_f_f: "bij f \<Longrightarrow> id_on (f ` A) g \<Longrightarrow> id_on A (inv f \<circ> g \<circ> f)"
  unfolding id_on_def by simp

lemma rel_set_image:
  "\<And> R f A B. rel_set R (f ` A) B = rel_set (\<lambda>x. R (f x)) A B"
  "\<And> R g A B. rel_set R A (g ` B) = rel_set (\<lambda>x y. R x (g y)) A B"
  unfolding rel_set_def by auto

lemma rel_set_mono_strong:
  "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> R x y \<Longrightarrow> S x y) \<Longrightarrow> rel_set R A B \<Longrightarrow> rel_set S A B"
  unfolding rel_set_def by force

lemma imsupp_alt: "bij f \<Longrightarrow> imsupp f = supp f \<union> supp (inv f)"
  by (auto simp: imsupp_def supp_inv)

definition "avoiding_bij f I D A = (SOME g :: 'a \<Rightarrow> 'a.
   bij g \<and> |supp g| <o |UNIV::'a set| \<and> imsupp g \<inter> A = {} \<and>
   (\<forall>a. a \<in> (imsupp f - A) \<union> D \<and> f a \<notin> A \<longrightarrow> g a = f a) \<and> id_on I g)"

lemma avoiding_bij:
  fixes f :: "'a \<Rightarrow> 'a" and I D A :: "'a set"
  assumes  "|supp f| <o |UNIV :: 'a set|" "bij f" "infinite (UNIV :: 'a set)"
    "|I| <o |UNIV :: 'a set|" "id_on I f"
    "|D| <o |UNIV :: 'a set|" "D \<inter> A = {}" "|A| <o |UNIV :: 'a set|"
  shows
    "bij (avoiding_bij f I D A)" (is "?A (avoiding_bij f I D A)")
    "|supp (avoiding_bij f I D A)| <o |UNIV :: 'a set|" (is "?B (avoiding_bij f I D A)")
    "imsupp (avoiding_bij f I D A) \<inter> A = {}" (is "?C (avoiding_bij f I D A)")
    "\<forall>a. a \<in> (imsupp f - A) \<union> D \<and> f a \<notin> A \<longrightarrow> avoiding_bij f I D A a = f a"  (is "?D (avoiding_bij f I D A)")
    "id_on I (avoiding_bij f I D A)"   (is "?E (avoiding_bij f I D A)")
proof -
  let ?P = "\<lambda>f. ?A f \<and> ?B f \<and> ?C f \<and> ?D f \<and> ?E f"
  have "|A| \<le>o |UNIV - (A \<union> imsupp f \<union> D \<union> I)|"
    by (rule ordLeq_ordIso_trans[OF ordLess_imp_ordLeq ordIso_symmetric])
      (auto simp: imsupp_def intro!: card_of_Un_diff_infinite card_of_Un_ordLess_infinite assms
        ordLeq_ordLess_trans[OF card_of_image])
  then obtain h where "inj_on h A" and hA: "h ` A \<subseteq> - (A \<union> imsupp f \<union> D \<union> I)"
    unfolding card_of_ordLeq[symmetric] by auto
  then have h: "bij_betw h A (h ` A)" "A \<inter> h ` A = {}" unfolding bij_betw_def by blast+
  define g where "g = extU A (h ` A) h"
  then have g: "bij g" "eq_on A g h" "|supp g| <o |UNIV :: 'a set|"
    "supp g \<subseteq> A \<union> - (A \<union> imsupp f \<union> D \<union> I)"
    "imsupp (inv g) \<subseteq> A \<union> - (A \<union> imsupp f \<union> D \<union> I)"
    "bij_betw g A (h ` A)"
    using extU[OF h] assms hA
    by (force simp: imsupp_inv
      elim!: ordLeq_ordLess_trans[OF card_of_mono1 card_of_Un_ordLess_infinite]
      intro!: ordLeq_ordLess_trans[OF card_of_image])+
  with assms have "bij (g o f o inv g)" "|supp (g o f o inv g)| <o |UNIV::'a set|"
    by (auto simp: supp_inv intro!: ordLeq_ordLess_trans[OF card_of_image]
      ordLeq_ordLess_trans[OF card_of_mono1[OF supp_o] card_of_Un_ordLess_infinite])
  moreover have "imsupp (g o f o inv g) \<inter> A = {}"
  proof (safe intro!: empty_iff[THEN iffD2])
    fix a
    assume "a \<in> imsupp (g o f o inv g)"
    moreover
    assume "a \<in> A"
    have "inv g a \<in> - (A \<union> imsupp f \<union> D \<union> I)"
    proof -
      have "\<forall>X Y a. \<not> X \<subseteq> Y \<or> a \<notin> X \<or> a \<in> Y" by blast
      moreover
      from \<open>bij g\<close> have "g (inv g a) = a" by simp
      ultimately show ?thesis
        by (metis ComplD \<open>a \<in> A\<close> g_def extU_def[of A "h ` A" h "inv g a"] hA imageI sup_ge1)
    qed
    then have "f (inv g a) = inv g a"
      unfolding imsupp_def supp_def by auto
    with g(1) have "g (f (inv g a)) = a" by auto
    ultimately show False using g(1) \<open>bij f\<close>
      unfolding imsupp_def supp_def by (auto simp: bij_implies_inject)
  qed
  moreover
  { fix a
    assume a: "a \<in> imsupp f - A \<union> D" "f a \<notin> A"
    with g(5) assms(7) have "inv g a = a"
      unfolding imsupp_def[of "inv g"] supp_def by auto
    moreover
    from a g(4) \<open>bij f\<close> have "g (f a) = f a"
      unfolding imsupp_def supp_def by (auto simp: bij_implies_inject)
    ultimately have "(g o f o inv g) a = f a"
      by simp
  }
  moreover
  { fix a
    assume "a \<in> I"
    then have "(g o f o inv g) a = a"
      unfolding o_apply
      apply (cases "a \<in> A")
       apply (metis Int_commute calculation(3) imsupp_empty_IntD2 o_apply)
      apply (metis (no_types) ComplD assms(5) bij_is_inj extU_def[of A "h ` A" h "a"] g(1) g_def hA id_onD inf_sup_ord(4) o_apply o_inv_o_cancel subsetCE)
      done
  }
  then have "id_on I (g o f o inv g)" by (simp add: id_on_def)
  ultimately have "?P (g o f o inv g)" by blast
  from someI[of ?P, OF this] have "?P (avoiding_bij f I D A)" unfolding avoiding_bij_def by simp
  then show "?A (avoiding_bij f I D A)" "?B (avoiding_bij f I D A)" "?C (avoiding_bij f I D A)"
            "?D (avoiding_bij f I D A)" "?E (avoiding_bij f I D A)"
    by auto
qed

lemma bij_imsupp_supp_ne:
assumes "bij f" and "supp f \<inter> A = {}"
shows "imsupp f \<inter> A = {}"
using assms unfolding imsupp_def apply auto
  by (smt CollectI disjoint_iff_not_equal inv_simp1 supp_def)

lemma imsupp_image_empty_IntI:
  assumes "B \<inter> imsupp g = {}" "A \<inter> B = {}"
  shows "g ` A \<inter> B = {}"
  using assms by (auto simp: imsupp_empty_IntD1)

lemma conj_context_mono: "P1 \<longrightarrow> Q1 \<Longrightarrow> (P1 \<Longrightarrow> P2 \<longrightarrow> Q2) \<Longrightarrow> (P1 \<and> P2) \<longrightarrow> (Q1 \<and> Q2)"
  by iprover

lemma rel_set_UN_D: "rel_set (\<lambda>x y. X x = Y y) A B \<Longrightarrow> (\<Union>a \<in> A. X a) = (\<Union>b \<in> B. Y b)"
  by (fastforce simp: rel_set_def)

lemma relcompp_conversep_Grp: "R OO conversep (Grp f) = (\<lambda>x y. R x (f y))"
  unfolding fun_eq_iff Grp_def by auto

lemma not_in_supp_alt: "x \<notin> supp f \<longleftrightarrow> f x = x"
  unfolding supp_def by auto

lemmas Grp_UNIV_id = eq_alt[symmetric]

lemma supp_id_bound: "|supp id| <o |UNIV :: 'a set|"
  by (simp add: card_of_empty4 supp_id)
lemma supp_id_bound': "Cinfinite r \<Longrightarrow> |supp id| <o r"
  by (simp add: supp_id Cinfinite_gt_empty)

lemma supp_the_inv_f_o_f_bound: "inj f \<Longrightarrow> |supp (the_inv f o f)| <o |UNIV|"
  by (smt f_the_inv_into_f fun.map_cong inv_o_cancel pointfree_idE supp_id_bound)

lemma bij_the_inv_f_o_f: "bij f \<Longrightarrow> bij (the_inv f o f)"
  by (simp add: bij_betw_the_inv_into)

lemma supp_the_inv:
  assumes "inj f"
  shows "supp (the_inv f) \<subseteq> supp f \<union> f ` (supp f)"
  using assms unfolding supp_def
  by (auto simp: image_iff) (metis the_inv_f_f)

lemma supp_inv_bound:
  assumes b: "bij f" and s: "|supp f| <o r"
  shows "|supp (inv f)| <o r"
  unfolding supp_inv[OF b]
  using s card_of_image ordLeq_ordLess_trans by blast

lemma insert_bound: "Cinfinite r \<Longrightarrow> |A| <o r \<Longrightarrow> |insert x A| <o r"
  by (metis Card_order_iff_ordLeq_card_of card_of_Field_ordIso card_of_Un_singl_ordLess_infinite1 cinfinite_def insert_is_Un ordLess_ordIso_trans ordLess_ordLeq_trans)

lemma single_bound: "Cinfinite r \<Longrightarrow> |{x}| <o r"
  by (simp add: Cinfinite_gt_empty insert_bound)

lemma Un_Cinfinite_ordLess: "|A| <o r \<Longrightarrow> |B| <o r \<Longrightarrow> Cinfinite r \<Longrightarrow> |A \<union> B| <o r"
  using Un_Cinfinite_bound_strict .
 (* apply (simp add: cinfinite_def) *)

lemma supp_the_inv_bound_gen:
  "Cinfinite r \<Longrightarrow> inj f \<Longrightarrow> |supp f| <o r \<Longrightarrow> |supp (the_inv f)| <o r"
  by (rule ordLeq_ordLess_trans[OF card_of_mono1[OF supp_the_inv]]
    Un_Cinfinite_ordLess ordLeq_ordLess_trans[OF card_of_image] | assumption)+

lemma Ball_neq: "(\<forall>x\<in>A. z \<noteq> x) \<longleftrightarrow> z \<notin> A"
  by auto

lemma id_on_Un: "id_on (A \<union> B) f \<longleftrightarrow> id_on A f \<and> id_on B f"
  unfolding id_on_def by auto

lemma type_definition_quot_type: "type_definition Rep Abs (UNIV // Collect (case_prod R)) \<Longrightarrow>
  equivp R \<Longrightarrow> quot_type R Abs Rep"
  unfolding quot_type_def
  by (auto 0 3 simp: equivp_implies_part_equivp quotient_def equivp_def
     type_definition.Rep_inverse type_definition.Rep_inject type_definition.Abs_inverse
     dest: type_definition.Rep)

lemma Int_emptyD: "A \<inter> B = {} \<Longrightarrow> x \<in> A \<Longrightarrow> x \<notin> B"
  by auto

definition "hidden_id = id"

lemma id_hid_o_hid: "id = hidden_id o hidden_id"
  unfolding hidden_id_def by simp

lemma emp_bound[simp]: "|{}::'a set| <o |UNIV::'b set|"
  by (rule card_of_empty4[THEN iffD2, OF UNIV_not_empty])

lemma regularCard_csum: "Cinfinite r \<Longrightarrow> Cinfinite s \<Longrightarrow> regularCard r \<Longrightarrow> regularCard s \<Longrightarrow> regularCard (r +c s)"
  apply (cases "r \<le>o s")
   apply (rule regularCard_ordIso[of s]; (auto intro!: Cinfinite_Cnotzero csum_absorb2'[THEN ordIso_symmetric]))
  apply (rule regularCard_ordIso[of r]; (auto intro!: Cinfinite_Cnotzero csum_absorb1'[THEN ordIso_symmetric] ordLess_imp_ordLeq))
  done

lemma regularCard_cprod: "Cinfinite r \<Longrightarrow> Cinfinite s \<Longrightarrow> regularCard r \<Longrightarrow> regularCard s \<Longrightarrow> regularCard (r *c s)"
  apply (cases "r \<le>o s")
   apply (rule regularCard_ordIso[of s]; (auto intro!: Cinfinite_Cnotzero cprod_infinite2'[THEN ordIso_symmetric]))
  apply (rule regularCard_ordIso[of r]; (auto intro!: Cinfinite_Cnotzero cprod_infinite1'[THEN ordIso_symmetric] ordLess_imp_ordLeq))
  done

locale infinite_regular_card_order =
  fixes r
  assumes card_order: "card_order r"
  and cinfinite: "cinfinite r"
  and regularCard: "regularCard r"
begin

lemma Card_order: "Card_order r"
  using card_order card_order_on_Card_order by blast

lemma Cinfinite: "Cinfinite r"
  using Card_order cinfinite by blast

lemma Cnotzero: "Cnotzero r"
  using Cinfinite_Cnotzero Cinfinite by blast

end

lemma infinite_regular_card_order_csum:
  "infinite_regular_card_order r \<Longrightarrow> infinite_regular_card_order s \<Longrightarrow> infinite_regular_card_order (r +c s)"
  unfolding infinite_regular_card_order_def
  by (meson card_order_csum card_order_on_Card_order cinfinite_csum regularCard_csum)

lemma infinite_regular_card_order_cprod:
  "infinite_regular_card_order r \<Longrightarrow> infinite_regular_card_order s \<Longrightarrow> infinite_regular_card_order (r *c s)"
  unfolding infinite_regular_card_order_def
  by (meson card_order_cprod card_order_on_Card_order cinfinite_cprod regularCard_cprod)

lemma infinite_regular_card_order_natLeq:
  "infinite_regular_card_order natLeq"
  unfolding infinite_regular_card_order_def
  by (simp add: natLeq_card_order natLeq_cinfinite regularCard_natLeq)

lemma infinite_regular_card_order_Un: "infinite_regular_card_order r \<Longrightarrow> |A| <o r \<Longrightarrow> |B| <o r \<Longrightarrow> |A \<union> B| <o r"
  using infinite_regular_card_order.Card_order regularCard_Un infinite_regular_card_order_def
  by blast

lemma infinite_regular_card_order_UN: "infinite_regular_card_order r \<Longrightarrow> |A| <o r \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> |B a| <o r) \<Longrightarrow> |\<Union>(B ` A)| <o r"
  by (simp add: infinite_regular_card_order.Card_order infinite_regular_card_order_def regularCard_UNION_bound)

lemma infinite_regular_card_order_ordLess_cprod: "infinite_regular_card_order r \<Longrightarrow> infinite_regular_card_order p \<Longrightarrow> |x| <o r \<Longrightarrow> |x| <o p *c r"
  using ordLess_ordLeq_trans[OF _ ordLeq_cprod2[OF infinite_regular_card_order.Cnotzero]] infinite_regular_card_order.Card_order
  by blast

lemma csum_less_mono:
  assumes Cinfinite: "Cinfinite r" "Cinfinite q"
  and Card_order: "Card_order r'" "Card_order q'"
  and less: "r <o r'" "q <o q'"
shows "r +c q <o r' +c q'"
proof (cases "r \<le>o q")
  case True
  have 1: "r +c q =o q" by (rule csum_absorb2[OF Cinfinite(2) True])
  have 2: "Cinfinite r'" using cinfinite_mono[OF ordLess_imp_ordLeq[OF less(1)]] Cinfinite(1) Card_order(1) by blast
  have 3: "q' \<le>o r' +c q'" by (rule ordLeq_csum2[OF Card_order(2)])
  show ?thesis
    apply (rule ordIso_ordLess_trans[OF 1])
    apply (rule ordLess_ordLeq_trans[OF less(2) 3])
    done
next
  case False
  then have 1: "q \<le>o r" by (simp add: Cinfinite ordLeq_iff_ordLess_or_ordIso)
  have 2: "r +c q =o r" by (rule csum_absorb1[OF Cinfinite(1) 1])
  have 3: "Cinfinite q'" using cinfinite_mono[OF ordLess_imp_ordLeq[OF less(2)]] Cinfinite(2) Card_order(2) by blast
  have 4: "r' \<le>o r' +c q'" by (rule ordLeq_csum1[OF Card_order(1)])
  show ?thesis
    apply (rule ordIso_ordLess_trans[OF 2])
    apply (rule ordLess_ordLeq_trans[OF less(1) 4])
    done
qed

corollary cardSuc_leq_csum:
  assumes Cinfinite: "Cinfinite r" "Cinfinite q"
  and Card_order: "Card_order r" "Card_order q"
shows "cardSuc (r +c q) \<le>o cardSuc r +c cardSuc q"
  unfolding csum_def
  apply (rule cardSuc_least[OF card_of_Card_order card_of_Card_order])
  unfolding csum_def[symmetric]
  by (rule csum_less_mono[OF Cinfinite cardSuc_Card_order[OF Card_order(1)] cardSuc_Card_order[OF Card_order(2)]
      cardSuc_greater[OF Card_order(1)] cardSuc_greater[OF Card_order(2)]])

corollary cardSuc_leq_csum_ifco:
  assumes "infinite_regular_card_order r" "infinite_regular_card_order q"
  shows "cardSuc (r +c q) \<le>o cardSuc r +c cardSuc q"
  by (rule cardSuc_leq_csum[OF
    infinite_regular_card_order.Cinfinite[OF assms(1)] infinite_regular_card_order.Cinfinite[OF assms(2)]
    infinite_regular_card_order.Card_order[OF assms(1)] infinite_regular_card_order.Card_order[OF assms(2)]
  ])

lemma cprod_less_mono:
  assumes Cinfinite: "Cinfinite r" "Cinfinite q"
  and Card_order: "Card_order r" "Card_order q" "Card_order r'" "Card_order q'"
  and less: "r <o r'" "q <o q'"
shows "r *c q <o r' *c q'"
proof (cases "r \<le>o q")
  case True
  have 1: "r *c q =o q" by (rule cprod_infinite2'[OF Cinfinite_Cnotzero[OF Cinfinite(1)] Cinfinite(2) True])
  have 2: "Cinfinite r'" using cinfinite_mono[OF ordLess_imp_ordLeq[OF less(1)]] Cinfinite(1) Card_order(3) by blast
  have 3: "q' \<le>o r' *c q'" by (rule ordLeq_cprod2[OF Cinfinite_Cnotzero[OF 2] Card_order(4)])
  show ?thesis
    apply (rule ordIso_ordLess_trans[OF 1])
    apply (rule ordLess_ordLeq_trans[OF less(2) 3])
    done
next
  case False
  then have 1: "q \<le>o r" by (simp add: Cinfinite ordLeq_iff_ordLess_or_ordIso)
  have 2: "r *c q =o r" by (rule cprod_infinite1'[OF Cinfinite(1) Cinfinite_Cnotzero[OF Cinfinite(2)] 1])
  have 3: "Cinfinite q'" using cinfinite_mono[OF ordLess_imp_ordLeq[OF less(2)]] Cinfinite(2) Card_order(4) by blast
  have 4: "r' \<le>o r' *c q'" by (rule ordLeq_cprod1[OF Card_order(3) Cinfinite_Cnotzero[OF 3]])
  show ?thesis
    apply (rule ordIso_ordLess_trans[OF 2])
    apply (rule ordLess_ordLeq_trans[OF less(1) 4])
    done
qed

corollary cardSuc_leq_cprod:
  assumes Cinfinite: "Cinfinite r" "Cinfinite q"
  and Card_order: "Card_order r" "Card_order q"
shows "cardSuc (r *c q) \<le>o cardSuc r *c cardSuc q"
  unfolding cprod_def
  apply (rule cardSuc_least[OF card_of_Card_order card_of_Card_order])
  unfolding cprod_def[symmetric]
  by (rule cprod_less_mono[OF Cinfinite Card_order
      cardSuc_Card_order[OF Card_order(1)] cardSuc_Card_order[OF Card_order(2)]
      cardSuc_greater[OF Card_order(1)] cardSuc_greater[OF Card_order(2)]])

corollary cardSuc_leq_cprod_ifco:
  assumes "infinite_regular_card_order r" "infinite_regular_card_order q"
  shows "cardSuc (r *c q) \<le>o cardSuc r *c cardSuc q"
  by (rule cardSuc_leq_cprod[OF
    infinite_regular_card_order.Cinfinite[OF assms(1)] infinite_regular_card_order.Cinfinite[OF assms(2)]
    infinite_regular_card_order.Card_order[OF assms(1)] infinite_regular_card_order.Card_order[OF assms(2)]
  ])

lemma infinite_regular_card_order_Un_csum:
  assumes irco: "infinite_regular_card_order r"
                "infinite_regular_card_order r1"
                "infinite_regular_card_order r2"
       and lhs: "|x1| <o r *c r1"
       and rhs: "|x2| <o r *c r2"
  shows "|x1 \<union> x2| <o r *c (r1 +c r2)"
proof -
  have co_lhs: "infinite_regular_card_order (r *c r1)"
    by (rule infinite_regular_card_order_cprod[OF irco(1,2)])
  have lhs': "|x1| <o r *c r1 +c r *c r2"
    by (rule ordLess_ordLeq_trans[OF lhs ordLeq_csum1[OF infinite_regular_card_order.Card_order[OF co_lhs]]])
  have lhs_dis: "|x1| <o r *c (r1 +c r2)"
    by (rule ordLess_ordIso_trans[OF lhs' cprod_csum_distrib1])

  have co_rhs: "infinite_regular_card_order (r *c r2)"
    by (rule infinite_regular_card_order_cprod[OF irco(1,3)])
  have rhs': "|x2| <o r *c r1 +c r *c r2"
    by (rule ordLess_ordLeq_trans[OF rhs ordLeq_csum2[OF infinite_regular_card_order.Card_order[OF co_rhs]]])
  have rhs_dis: "|x2| <o r *c (r1 +c r2)"
    by (rule ordLess_ordIso_trans[OF rhs' cprod_csum_distrib1])

  have co: "infinite_regular_card_order (r *c (r1 +c r2))"
    by (rule infinite_regular_card_order_cprod[OF irco(1) infinite_regular_card_order_csum[OF irco(2,3)]])
  show ?thesis
    by (rule infinite_regular_card_order_Un[OF co lhs_dis rhs_dis])
qed

(*
typedef 'a suc = "Field (cardSuc |UNIV :: 'a set| )"
  using Field_cardSuc_not_empty by auto

setup_lifting type_definition_suc

lift_definition card_suc :: "'a rel \<Rightarrow> 'a suc rel" is "\<lambda>_. cardSuc |UNIV :: 'a set|"
  by (auto simp: Field_def Range.simps Domain.simps)

lemma Field_card_suc: "Field (card_suc r) = UNIV"
  unfolding Field_def Range.simps Domain.simps set_eq_iff Un_iff eqTrueI[OF UNIV_I] ex_simps simp_thms
  by transfer (auto simp: Field_def Range.simps Domain.simps)

lemma card_suc_alt: "card_suc r = dir_image (cardSuc |UNIV :: 'a set| ) Abs_suc"
  unfolding card_suc_def dir_image_def by auto

lemma cardSuc_ordIso_card_suc:
  assumes "card_order r"
  shows "cardSuc r =o card_suc (r :: 'a rel)"
proof -
  have "cardSuc (r :: 'a rel) =o cardSuc |UNIV :: 'a set|"
    using cardSuc_invar_ordIso card_of_unique assms
    by (simp add: card_order_on_Card_order)
  also have "cardSuc |UNIV :: 'a set| =o card_suc (r :: 'a rel)"
    unfolding card_suc_alt
    by (rule dir_image_ordIso) (simp_all add: inj_on_def Abs_suc_inject)
  finally show ?thesis .
qed

lemma Card_order_card_suc: "card_order r \<Longrightarrow> Card_order (card_suc r)"
  using cardSuc_ordIso_card_suc
  by (metis Card_order_ordIso2 cardSuc_Card_order card_order_on_Card_order)

lemma card_order_card_suc: "card_order r \<Longrightarrow> card_order (card_suc r)"
  using Field_card_suc Card_order_card_suc by metis

lemma card_suc_greater: "card_order r \<Longrightarrow> r <o card_suc r"
  by (metis Field_card_order cardSuc_greater cardSuc_ordIso_card_suc ordLess_ordIso_trans)
*)

lemma infinite_regular_card_order_card_suc:
  "card_order r \<Longrightarrow> Cinfinite r \<Longrightarrow> infinite_regular_card_order (card_suc r)"
  unfolding infinite_regular_card_order_def
  by (meson Cinfinite_cardSuc Cinfinite_cong cardSuc_ordIso_card_suc card_order_card_suc regularCard_card_suc)

lemma card_suc_greater_set: "\<lbrakk> card_order r ; A \<le>o r \<rbrakk> \<Longrightarrow> A <o card_suc r"
  using card_suc_greater ordLeq_ordLess_trans by blast

lemma exists_univ_eq: "\<And>x y. (x = y) = (\<exists>z. z \<in> UNIV \<and> z = x \<and> z = y)"
  by simp
lemma empty_subset_conj: "{} \<subseteq> A \<and> P \<longleftrightarrow> P"
  by simp
lemma rel_subset_imp: "\<lbrakk> \<forall>z6\<in>fst ` s. \<forall>y6\<in>snd ` s. R1 z6 y6 \<longrightarrow> R2 z6 y6 ; s \<subseteq> {(x, y). R1 x y} \<rbrakk> \<Longrightarrow> s \<subseteq> {(x, y). R2 x y}"
  by fastforce
lemma rel_ex_fst: "\<lbrakk> s \<subseteq> {(x, y). R1 x y} ; y \<in> snd ` s \<rbrakk> \<Longrightarrow> \<exists>x. x \<in> fst ` s \<and> R1 x y"
  by fastforce
lemma rel_ex_snd: "\<lbrakk> s \<subseteq> {(x, y). R1 x y} ; x \<in> fst ` s \<rbrakk> \<Longrightarrow> \<exists>y. y \<in> snd ` s \<and> R1 x y"
  by fastforce
lemma image_id: "id ` A = A"
  by simp
lemma OO_cong: "a = b \<Longrightarrow> c = d \<Longrightarrow> a OO c = b OO d"
  by simp
lemma conversep_cong: "a = b \<Longrightarrow> a\<inverse>\<inverse> = b\<inverse>\<inverse>"
  by simp
lemma ex_UNIV_id: "x \<in> UNIV \<Longrightarrow> \<exists>z. z \<in> UNIV \<and> id z = x \<and> f z = f x"
  by simp
lemma in_alt_top: "(\<lambda>x. f x \<subseteq> {_. True}) = (\<lambda>_. True)"
  by simp

lemma image_in_bij_eq: "bij f \<Longrightarrow> (a \<in> f ` A) = (inv f a \<in> A)"
  by force

lemma supp_comp_bound:
  assumes bound: "|supp f| <o |UNIV::'a set|" "|supp g| <o |UNIV::'a set|"
  and inf: "infinite (UNIV::'a set)"
  shows "|supp (g \<circ> f)| <o |UNIV::'a set|"
proof -
  from inf bound(2,1) have "|supp g \<union> supp f| <o |UNIV::'a set|" by (rule card_of_Un_ordLess_infinite)
  then show ?thesis using supp_o
    by (metis card_of_mono1 ordLeq_ordLess_trans)
qed

lemma prod_in_Collect_iff: "(a, b) \<in> {(x, y). A x y} \<longleftrightarrow> A a b" by blast

lemma Grp_UNIV_def: "Grp f = (\<lambda>x. (=) (f x))"
  unfolding Grp_def by auto

definition cmin where "cmin r s \<equiv> if r <o s then r +c czero else czero +c s"

lemma cmin1:
  assumes "Card_order r" "Card_order s"
  shows "cmin r s \<le>o r"
unfolding cmin_def proof (cases "r <o s", unfold if_P if_not_P)
  case True
  then show "r +c czero \<le>o r" by (simp add: assms(1) csum_czero1 ordIso_imp_ordLeq)
next
  case False
  have "Well_order r" "Well_order s" using assms by auto
  then have "s \<le>o r" using False using not_ordLeq_iff_ordLess by blast
  moreover have "czero +c s =o s" using assms csum_czero2 by blast
  ultimately show "czero +c s \<le>o r" using ordIso_ordLeq_trans by blast
qed

lemma cmin2:
  assumes "Card_order r" "Card_order s"
  shows "cmin r s \<le>o s"
unfolding cmin_def proof (cases "r <o s", unfold if_P if_not_P)
  case True
  then show "r +c czero \<le>o s" using assms(1) csum_czero1 ordIso_ordLeq_trans ordLess_imp_ordLeq by blast
next
  case False
  then show "czero +c s \<le>o s" using ordIso_ordLeq_trans using assms(2) csum_czero2 ordIso_imp_ordLeq by blast
qed

lemma cmin_greater:
  assumes "Card_order s1" "Card_order s2" "r <o s1" "r <o s2"
  shows "r <o cmin s1 s2"
unfolding cmin_def proof (cases "s1 <o s2", unfold if_P if_not_P)
  case True
  have "s1 =o s1 +c czero" using assms(1) csum_czero1 ordIso_symmetric by blast
  then show "r <o s1 +c czero" using assms(3) ordLess_ordIso_trans by blast
next
  case False
  have "s2 =o czero +c s2" using assms(2) csum_czero2 ordIso_symmetric by blast
  then show "r <o czero +c s2" using assms(4) ordLess_ordIso_trans by blast
qed

lemma cmin_Card_order:
  assumes "Card_order s1" "Card_order s2"
  shows "Card_order (cmin s1 s2)"
  by (simp add: Card_order_csum cmin_def)

lemma cmin_Cinfinite:
  assumes "Cinfinite s1" "Cinfinite s2"
  shows "Cinfinite (cmin s1 s2)"
unfolding cmin_def proof (cases "s1 <o s2", unfold if_P if_not_P)
  case True
  have "s1 +c czero =o s1" using assms(1) csum_czero1 by blast
  then show "Cinfinite (s1 +c czero)" using Cinfinite_cong assms(1) ordIso_symmetric by blast
next
  case False
  have "czero +c s2 =o s2" using assms(2) csum_czero2 by blast
  then show "Cinfinite (czero +c s2)" using Cinfinite_cong assms(2) ordIso_symmetric by blast
qed

lemma cmin_regularCard:
  assumes "regularCard s1" "regularCard s2" "Cinfinite s1" "Cinfinite s2"
  shows "regularCard (cmin s1 s2)"
unfolding cmin_def proof (cases "s1 <o s2", unfold if_P if_not_P)
  case True
  have "s1 +c czero =o s1" using assms(3) csum_czero1 by blast
  then show "regularCard (s1 +c czero)" using regularCard_ordIso ordIso_symmetric assms by blast
next
  case False
  have "czero +c s2 =o s2" using assms(4) csum_czero2 by blast
  then show "regularCard (czero +c s2)" using regularCard_ordIso ordIso_symmetric assms by blast
qed

(*  *)

definition natOf :: "nat list \<Rightarrow> nat" where
"natOf \<equiv> SOME f . inj f"

lemma inject_natOf: "inj natOf"
by (metis ex_inj natOf_def someI_ex)

lemma inj_natOf[simp]: "natOf p = natOf p \<longleftrightarrow> p = p"
by (meson injD inject_natOf)

lemma ex_push_inwards: "(\<exists>x. P x \<and> (\<exists>y. Q x y)) \<longleftrightarrow> (\<exists>y. \<exists>x. Q x y \<and> P x)"
  by blast

lemma ex_conjunct2: "\<exists>x. P x \<and> Q x \<Longrightarrow> \<exists>x. Q x"
  by auto

lemma eextend_fresh:
  fixes A A' B::"'a set"
  assumes "|B| <o |UNIV::'a set|" "|A| <o |UNIV::'a set|" "infinite (UNIV::'a set)"
    "A' \<subseteq> A" "B \<inter> A' = {}"
shows "\<exists>\<rho>. bij \<rho> \<and> |supp \<rho>| <o |UNIV::'a set| \<and> \<rho> ` B \<inter> A = {} \<and> id_on A' \<rho> \<and> \<rho> \<circ> \<rho> = id"
proof-
  have "|- (A \<union> B)| =o |UNIV::'a set|"
    using card_of_Un_diff_infinite[OF assms(3), unfolded Compl_eq_Diff_UNIV[symmetric]]
      assms(1) assms(2) assms(3) card_of_Un_ordLess_infinite by blast
  hence "|B| <o |- (A \<union> B)|"
    using assms(1) ordIso_symmetric ordLess_ordIso_trans by blast
  then obtain f where f: "inj_on f B" "f ` B \<subseteq> - (A \<union> B)"
    by (meson card_of_ordLeq ordLeq_iff_ordLess_or_ordIso)

  then have f1: "f ` B \<inter> B = {}" "f ` B \<inter> A = {}" by blast+

  define g where "g \<equiv> \<lambda>a. if a \<in> B then f a else (if a \<in> f ` B then inv_into B f a else a)"
  have 1: "g \<circ> g = id"
    unfolding g_def comp_def id_def
    apply (rule ext)
    subgoal for x
      apply (cases "x \<in> B")
        apply (subst if_P, assumption)+
        apply (subst if_not_P)
        using f1 apply blast
        apply (subst if_P)
        apply (erule imageI)
        apply (rule inv_into_f_f)
        apply (rule f)
      apply assumption
      apply (subst if_not_P, assumption)+
      apply (cases "x \<in> f ` B")
        apply (subst if_P, assumption)+
        apply (subst if_P)
        apply (erule inv_into_into)
        apply (erule f_inv_into_f)
      apply (subst if_not_P, assumption)+
      apply (rule refl)
      done
    done
  then have 2: "bij g" using o_bij by blast

  have 3: "id_on A' g" unfolding id_on_def g_def using f1 assms(4,5) by auto
  have 4: "g ` B \<inter> A = {}" unfolding g_def using f1 by simp

  have "supp g \<subseteq> B \<union> g ` B" unfolding g_def supp_def by auto
  then have 5: "|supp g| <o |UNIV::'a set|"
    by (meson assms(1,3) card_of_Un_ordLess_infinite card_of_image card_of_mono1 ordLeq_ordLess_trans)

  show ?thesis using 1 2 3 4 5 by blast
qed

lemma extend_id_on:
  assumes g: "bij g" "|supp (g::'a \<Rightarrow> 'a)| <o |UNIV::'a set|" "id_on (A - B1) g" "g \<circ> g = id" "g ` B1 \<inter> B1 = {}"
  and B: "B2 \<subseteq> B1"
shows "\<exists>f. bij f \<and> |supp f| <o |UNIV::'a set| \<and> eq_on B2 f g \<and> id_on (A - B2) f \<and> f \<circ> f = id \<and> f ` B2 \<inter> B2 = {}"
proof -
  define f where "f \<equiv> \<lambda>a. if a \<in> B2 then g a else (if a \<in> g ` B2 then inv g a else a)"
  have 1: "f \<circ> f = id" unfolding f_def comp_def id_def
    apply (rule ext)
    subgoal for x
      apply (cases "x \<in> B2")
       apply (cases "g x \<in> B2")
        apply (unfold if_P if_not_P)
      using g(4) apply (simp add: pointfree_idE)
       apply (simp add: g(1))
      apply (cases "x \<in> g ` B2")
       apply (unfold if_P if_not_P)
       apply (simp add: g(1) image_in_bij_eq)
      apply (rule refl)
      done
    done
  then have 2: "bij f" using o_bij by blast
  have 3: "|supp f| <o |UNIV::'a set|" using g(2) unfolding f_def supp_def
    by (smt (verit, best) Collect_mono card_of_subset_bound g(1) inv_simp1)
  have 4: "eq_on B2 f g" unfolding eq_on_def f_def by auto
  have 5: "id_on (A - B2) f" using g(2-5) unfolding id_on_def f_def
    by (metis B DiffD1 DiffD2 DiffI IntE IntI bij_def equals0D g(1) image_Int inf.absorb_iff2 inv_unique_comp)
  have 6: "f ` B2 \<inter> B2 = {}" unfolding f_def using g(4,5) B by auto

  show ?thesis using 1 2 3 4 5 6 by blast
qed

lemma inv_invol: "f \<circ> f = id \<Longrightarrow> inv f = f"
  using inv_unique_comp by blast

lemma disjoint_invol:
  fixes g::"'a \<Rightarrow> 'a"
  assumes "bij g" "|supp g| <o |UNIV::'a set|" "A \<inter> B = {}" "g ` A = B" "id_on C g"
  shows "\<exists>f. bij f \<and> |supp f| <o |UNIV::'a set| \<and> eq_on A f g \<and> f \<circ> f = id \<and> id_on C f"
proof -
  define f where "f \<equiv> \<lambda>a. if a \<in> A then g a else (if a \<in> B then inv g a else a)"
  have 1: "f \<circ> f = id" unfolding f_def comp_def id_def
    apply (rule ext)
    subgoal for x
      apply (cases "x \<in> A")
      using assms(1,3,4) apply auto[1]
      apply (unfold if_not_P)
      apply (cases "x \<in> B")
       apply (unfold if_P if_not_P)
      using assms(1,4) apply force
      apply (rule refl)
      done
    done
  then have 2: "bij f" using o_bij by blast
  have 3: "|supp f| <o |UNIV::'a set|" using assms(2) unfolding f_def supp_def
    by (smt (verit) Collect_mono assms(1) bij_imp_inv' card_of_subset_bound)
  have 4: "eq_on A f g" unfolding f_def eq_on_def by simp
  have 5: "id_on C f" using assms(5) unfolding f_def id_on_def
    by (simp add: assms(1) bij_imp_inv)
  show ?thesis using 1 2 3 4 5 by blast
qed

lemma image_inv_iff: "bij f \<Longrightarrow> (A = f ` B) = (inv f ` A = B)"
  by force

end