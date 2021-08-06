theory Prelim
  imports Card_Prelim
begin
  
abbreviation (input) "any \<equiv> undefined"

declare bij_imp_bij_inv[simp]
declare bij_comp[simp]
declare bij_id[intro!]
declare map_prod.id[simp]
declare eq_OO[simp] declare OO_eq[simp]
declare inv_inv_eq[simp]

lemma bij_imp_bij_betw: "bij f \<Longrightarrow> bij_betw f A (f ` A)"
  apply(rule inj_on_imp_bij_betw) unfolding bij_def inj_def inj_on_def by auto

lemma bij_bij_betw_inv: "bij u \<Longrightarrow> bij_betw u A B \<Longrightarrow> bij_betw (inv u) B A"
  by (metis bij_betw_imp_inj_on bij_betw_imp_surj_on bij_imp_bij_betw bij_imp_bij_inv image_inv_f_f)

lemma conversep_def: 
"conversep r = (\<lambda> a b. r b a)" by auto


lemma bij_comp2: "bij u \<Longrightarrow> bij v \<Longrightarrow> bij (\<lambda>a. v (u a))"
  unfolding o_def[symmetric] using bij_comp by blast
  
lemma snd_o_is_snd:"snd \<circ> (\<lambda>(x, y). (f0 (x, y), y)) = snd"
  by fastforce

lemma fst_o_is_fst:"fst \<circ> (\<lambda>(x, y). (x, f0 (x, y))) = fst"
  by fastforce

lemma bij_implies_inject[simp]: "bij f \<Longrightarrow> f a = f a' \<longleftrightarrow> a = a'"
  unfolding bij_def inj_on_def by auto

lemma inv_simp1[simp]: "bij u \<Longrightarrow> inv u (u x) = x"
  by (simp add: bij_is_inj)

lemma inv_o_simp1[simp]: "bij u \<Longrightarrow> inv u o u = id"
  unfolding o_def by auto

lemma inv_simp2[simp]: "bij u \<Longrightarrow> u (inv u x) = x"
  by (simp add: bij_is_surj surj_f_inv_f)

lemma inv_o_simp2[simp]: "bij u \<Longrightarrow> u o inv u = id"
  unfolding o_def by auto
    
lemma bij_inv_rev: "bij f \<Longrightarrow> a = inv f b \<longleftrightarrow> b = f a"
  by auto

(* Helps working with arbitrary BNFs: *)
declare [[typedef_overloaded, bnf_internals]]

lemma case_in[case_names L uL not]:
  assumes "a \<in> L \<Longrightarrow> P" and "a \<notin> L \<Longrightarrow> a \<in> u ` L \<Longrightarrow> P" and "a \<notin> L \<Longrightarrow> a \<notin> u ` L \<Longrightarrow> P"
  shows P  using assms by auto

(* Properties of bijections *)
lemma bij_iff:
  "bij u \<longleftrightarrow> (\<exists> v. v o u = id \<and> u o v = id)"
  by (meson bij_is_inj bij_is_surj inv_o_cancel o_bij surj_iff)

lemma bij_iff1:
  "bij u \<longleftrightarrow> (\<exists> v. bij v \<and> v o u = id \<and> u o v = id)"
  by (meson bij_is_inj bij_is_surj inv_o_cancel o_bij surj_iff)

(* Combinators: *)
definition id_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "id_on A f \<equiv> \<forall> a. a \<in> A \<longrightarrow> f a = a"

lemma id_on_id[simp,intro!]: "id_on A id"
  unfolding id_on_def by auto

definition "eq_on A f g \<equiv> \<forall> a. a \<in> A \<longrightarrow> f a = g a"

lemma eq_on_refl[simp,intro!]: "eq_on A f f" unfolding eq_on_def by auto

lemma eq_on_sym: "eq_on A f g \<Longrightarrow> eq_on A g f" unfolding eq_on_def by auto

lemma eq_on_trans: "eq_on A f g \<Longrightarrow> eq_on A g h \<Longrightarrow> eq_on A f h" unfolding eq_on_def by auto

lemma eq_on_mono: "A \<subseteq> B \<Longrightarrow> eq_on B f g \<Longrightarrow> eq_on A f g" unfolding eq_on_def by auto

lemma eq_on_emp[simp,intro!]: "eq_on {} f g" unfolding eq_on_def by auto

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
  "supp (g o f) \<subseteq> supp g \<union> supp f"
  unfolding supp_def by auto

lemma finite_supp_comp: "finite (supp f) \<Longrightarrow> finite (supp g) \<Longrightarrow> finite (supp (g o f))"
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

lemma imsupp_commute: "imsupp f \<inter> imsupp g = {} \<Longrightarrow> f o g = g o f"
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
  shows "A \<inter> imsupp (g2 o g1) = {}"
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

lemma ex_bij_betw_supp:
  fixes A B C :: "'a set"
  assumes i: "infinite (UNIV :: 'a set)" and 
  bound: "|A| <o |UNIV :: 'a set|"
  and AB: "bij_betw uu A B" and emp: "A \<inter> B = {}" "A \<inter> C = {}" "B \<inter> C = {}"
shows "EX u. bij u \<and> |supp u| <o |UNIV::'a set| \<and> bij_betw u A B \<and> imsupp u \<inter> C = {} \<and> 
             eq_on A u uu"
proof-
  have abo: "|A| =o |B|" using AB 
    using card_of_ordIso by blast
  hence b2: "|B| <o |UNIV :: 'a set|" using bound   
    using ordIso_ordLess_trans ordIso_symmetric by blast
  define u where "u \<equiv> extU A B uu"
  show ?thesis apply(rule exI[of _ u])
    using extU[OF AB emp(1), unfolded u_def[symmetric]] apply auto  
    apply (metis abo bound card_of_Un_infinite card_of_mono1 finite_Un 
finite_ordLess_infinite2 i ordIso_iff_ordLeq ordLeq_ordLess_trans)
  using assms by auto 
qed

lemma ordIso_ex_bij_betw_supp:
  fixes A B C :: "'a set"
  assumes i: "infinite (UNIV :: 'a set)" and 
  bound: "|A| <o |UNIV :: 'a set|"
  and AB: "|A| =o |B|" and emp: "A \<inter> B = {}" "A \<inter> C = {}" "B \<inter> C = {}"
shows "EX u. bij u \<and> |supp u| <o |UNIV::'a set| \<and> bij_betw u A B \<and> imsupp u \<inter> C = {}"
proof-   
  obtain uu where AB: "bij_betw uu A B" 
    using AB unfolding card_of_ordIso[symmetric] by blast
  have "EX u. bij u \<and> |supp u| <o |UNIV::'a set| \<and> bij_betw u A B \<and> imsupp u \<inter> C = {} 
    \<and> eq_on A u uu"
  apply(rule ex_bij_betw_supp) using assms AB by auto 
  thus ?thesis by auto
qed

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
      (auto simp: imsupp_def intro!: infinite_UNIV_card_of_minus card_of_Un_ordLess_infinite assms
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
      unfolding imsupp_def supp_def by auto
  qed
  moreover
  { fix a
    assume a: "a \<in> imsupp f - A \<union> D" "f a \<notin> A"
    with g(5) assms(7) have "inv g a = a"
      unfolding imsupp_def[of "inv g"] supp_def by auto
    moreover
    from a g(4) \<open>bij f\<close> have "g (f a) = f a"
      unfolding imsupp_def supp_def by auto
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

lemma bij_swap: "bij (id (x := y, y := x))"
  unfolding bij_def inj_def by (auto simp: image_iff)

lemma supp_swap_le: "supp (id (x := y, y := x)) \<subseteq> {x, y}"
  unfolding supp_def by auto

lemma not_in_supp_alt: "x \<notin> supp f \<longleftrightarrow> f x = x"
  unfolding supp_def by auto

lemmas Grp_UNIV_id = eq_alt[symmetric]

lemma supp_id_bound: "|supp id| <o |UNIV :: 'a set|"
  by (simp add: card_of_empty4 supp_id)

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

lemma Un_Cinfinite_ordLess: "|A| <o r \<Longrightarrow> |B| <o r \<Longrightarrow> Cinfinite r \<Longrightarrow> |A \<union> B| <o r"
  by (simp add: cinfinite_def)

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

lemma emp_bound: "|{}| <o |UNIV|"
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

end