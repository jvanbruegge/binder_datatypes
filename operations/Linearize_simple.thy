theory Linearize_simple
  imports "Binders.MRBNF_Composition"
begin

typedecl ('a, 'b, 'c) F
consts map_F :: "('a :: var \<Rightarrow> 'a) \<Rightarrow> ('b :: var \<Rightarrow> 'b) \<Rightarrow>
  ('c \<Rightarrow> 'c') \<Rightarrow> ('a, 'b, 'c) F \<Rightarrow> ('a, 'b, 'c') F"
consts set1_F :: "('a :: var, 'b :: var, 'c) F \<Rightarrow> 'a set"
consts set2_F :: "('a :: var, 'b :: var, 'c) F \<Rightarrow> 'b set"
consts set3_F :: "('a :: var, 'b :: var, 'c) F \<Rightarrow> 'c set"
consts rrel_F :: "('c \<Rightarrow> 'c' \<Rightarrow> bool) \<Rightarrow> ('a :: var, 'b :: var, 'c) F \<Rightarrow> ('a, 'b, 'c') F \<Rightarrow> bool"

declare [[typedef_overloaded]]
mrbnf "('a :: var, 'b :: var, 'c) F"
  map: map_F
  sets: free: set1_F bound: set2_F live: set3_F
  bd: natLeq
  rel: rrel_F
  var_class: var
  sorry

axiomatization where
(* The next property assumes that nonrepetitive elements exist: *)
  ex_nonrep: "\<exists>x. \<forall>x'. (\<exists> R. rrel_F R x x') \<longrightarrow> (\<exists> f. x' = map_F id id f x)"

abbreviation "rel_F \<equiv> mr_rel_F"


(* Then notion of two items having the same shape (w.r.t. the 3rd position): *)
definition eq_shape :: "('a1::var,'a2::var,'a3) F \<Rightarrow> ('a1,'a2,'a3) F \<Rightarrow> bool" where 
  "eq_shape x x' \<equiv> \<exists> R. rel_F id id R x x'"

definition nonrep :: "('a1::var,'a2::var,'a3) F \<Rightarrow> bool" where 
  "nonrep x \<equiv> \<forall> x'. eq_shape x x' \<longrightarrow> (\<exists> f. x' = map_F id id f x)"

lemma op_eq_triv_sym: "(\<lambda>x. (=) (g x)) = (\<lambda>x z. z = g x)"
  by force

lemma nonrep_map_F:
  fixes x :: "('a1::var,'a2::var,'a3) F"
    and v :: "'a1 \<Rightarrow> 'a1" and u :: "'a2\<Rightarrow>'a2"
  assumes v: "|supp v| <o |UNIV :: 'a1 set|"  and u: "bij u" "|supp u| <o |UNIV :: 'a2 set|" 
  assumes "nonrep x"
  shows "nonrep (map_F v u id x)"
unfolding nonrep_def eq_shape_def proof safe
  fix y' :: "('a1,'a2,'a3) F" and R
  let ?y = "map_F v u id x"
  assume r: "rel_F id id R ?y y'"
  have "rel_F (v o id) (u o id) (R OO (=)) x y'"
    using r unfolding F.mr_rel_map(1)[OF v u supp_id_bound bij_id supp_id_bound]
    by (simp add: OO_def Grp_def) 
  then obtain x' where xx': "rel_F id id R x x'" and y': "y' = map_F v u id x'" 
    unfolding mr_rel_F_def o_id F.rel_compp eq_alt F.rel_Grp F.map_id
    apply atomize_elim
    apply (clarsimp simp: Grp_def id_def[symmetric] F.in_rel[OF v u]
        F.map_comp u v supp_id_bound)
    subgoal for z
      apply (rule exI[of _ "map_F id id snd z"] conjI)
      apply (auto simp: F.rel_map F.set_map F.map_comp u v supp_id_bound intro!: F.rel_refl_strong)
      done
    done
  obtain f where x': "x' = map_F id id f x" 
    using assms xx' unfolding nonrep_def eq_shape_def by auto
  show "\<exists>f. y' = map_F id id f ?y"
    apply(rule exI[of _ f])
    apply (auto simp: x' y' F.map_comp supp_id_bound u v)
    done
qed

(* Here we would need pullback preservation if there were lives left *)
lemma nonrep_map_F_rev:
  fixes x :: "('a1::var,'a2::var,'a3) F" and u :: "'a2\<Rightarrow>'a2"
  assumes u: "bij u" "|supp u| <o |UNIV :: 'a2 set|" 
  assumes "nonrep (map_F id u id x)"
  shows "nonrep x"
  unfolding nonrep_def eq_shape_def proof safe
  fix x' :: "('a1,'a2,'a3) F" and R 
  let ?y = "map_F id u id x"  let ?y' = "map_F id u id x'"
  assume r: "rel_F id id R x x'"
  hence "rel_F id id R ?y ?y'" 
    unfolding F.mr_rel_map(1)[OF supp_id_bound u supp_id_bound bij_id supp_id_bound]
    using F.mr_rel_map(2)[OF supp_id_bound bij_id supp_id_bound supp_id_bound u, of R x x' id]
    by (simp add: OO_def Grp_def)
  then obtain f where "?y' = map_F id id f ?y" 
    using assms unfolding nonrep_def eq_shape_def by auto
  hence y':"?y' = map_F id u f x"
    by (simp add: F.map_comp supp_id_bound u)
  hence "rel_F id u (Grp id) x' (map_F id u f x)"
    unfolding F.mr_rel_Grp[OF supp_id_bound u]
    by (auto simp: Grp_def)
  hence "rel_F id id (Grp f) x x'"
    apply(subst F.mr_rel_flip[OF bij_id supp_id_bound bij_id supp_id_bound, simplified, symmetric])
    unfolding F.mr_rel_map(3)[OF supp_id_bound u bij_id supp_id_bound u] Grp_def
    by (auto simp add: u conversep_def OO_def supp_id_bound elim!: F.mr_rel_mono_strong0[rotated 6])
  thus "\<exists>f. x' = map_F id id f x"
    apply(intro exI[of _ f])  unfolding eq_alt F.mr_rel_Grp[OF supp_id_bound bij_id supp_id_bound] by (simp add: Grp_def)
qed

lemma nonrep_mapF_bij:
  fixes x :: "('a1::var,'a2::var,'a3) F" and g::"'a3\<Rightarrow>'a3"
  assumes g: "bij g" and x: "nonrep x"
  shows "nonrep (map_F id id g x)" (is "nonrep ?x'")
  unfolding nonrep_def eq_shape_def proof safe
  fix y' :: "('a1,'a2,'a3)F" and R'
  let ?y = "map_F id id (inv g) y'" 
  let ?R = "Grp g OO R' OO conversep (Grp g)"
  assume "rel_F id id R' ?x' y'"
  hence "rel_F id id ?R x ?y"
    unfolding F.mr_rel_map(1)[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound]
      F.mr_rel_map(3)[OF supp_id_bound bij_id supp_id_bound bij_id supp_id_bound bij_id supp_id_bound] 
    by (simp add: g Grp_def OO_def o_def id_def)
  with x obtain f where "?y = map_F id id f x" 
    unfolding nonrep_def eq_shape_def by auto
  thus "\<exists>f'. y' = map_F id id f' ?x'"
    apply(intro exI[of _ "g o f o inv g"])
    apply(auto simp add: g F.map_comp o_assoc[symmetric] supp_id_bound F.map_id
      dest!: arg_cong[where f = "map_F id id g" and y = "map_F id id f x"])
    done
qed

lemma nonrep_mapF_bij_2:
  fixes x :: "('a1::var,'a2::var,'a3) F"
    and v :: "'a1 \<Rightarrow> 'a1" and u :: "'a2\<Rightarrow>'a2" and g::"'a3\<Rightarrow>'a3"
  assumes v: "|supp v| <o |UNIV :: 'a1 set|" and u: "bij u" "|supp u| <o |UNIV :: 'a2 set|"
    and g: "bij g" and x: "nonrep x"
  shows "nonrep (map_F v u g x)" 
proof-
  have "nonrep (map_F v u id x)" (is "nonrep ?x'") by (simp add: nonrep_map_F v u x)
  hence "nonrep (map_F id id g ?x')" using g nonrep_mapF_bij u by blast
  thus ?thesis
    by (simp add: F.map_comp supp_id_bound u v)
qed

typedef ('a1::var,'a2::var,'a3::var) F' = "{x :: ('a1,'a2,'a3) F. nonrep x}"
  unfolding mem_Collect_eq nonrep_def eq_shape_def mr_rel_F_def F.map_id id_apply
  unfolding id_def[symmetric]
  by (rule ex_nonrep)

setup_lifting type_definition_F'

lift_definition set1_F' :: "('a1::var,'a2::var,'a3::var) F' \<Rightarrow> 'a1 set" is set1_F .
lift_definition set2_F' :: "('a1::var,'a2::var,'a3::var) F' \<Rightarrow> 'a2 set" is set2_F .
lift_definition set3_F' :: "('a1::var,'a2::var,'a3::var) F' \<Rightarrow> 'a3 set" is set3_F .

lift_definition map_F' :: "('a1::var \<Rightarrow> 'a1) \<Rightarrow> ('a2::var \<Rightarrow> 'a2) \<Rightarrow> ('a3::var \<Rightarrow> 'a3) 
  \<Rightarrow> ('a1,'a2,'a3) F' \<Rightarrow> ('a1,'a2,'a3) F'"
  is "\<lambda>v u f. map_F (asSS v) (asSS (asBij u)) (asBij f)" 
  unfolding asBij_def asSS_def by (auto simp: supp_id_bound intro: nonrep_mapF_bij_2)

lift_definition rrel_F' :: "('a1::var,'a2::var,'a3::var) F' \<Rightarrow> ('a1,'a2,'a3) F' \<Rightarrow> bool"
  is "rrel_F (=)" .

(* Verifying the axioms of a MRBNF for F':  *)

lemma F'_map_id: "map_F' id id id = id"
  by (rule ext, transfer) (auto simp: F.map_id asSS_def)

lemma F'_map_comp1_:
  fixes u1 v1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 v2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 v3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|" "|supp v1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|" "bij v2" "|supp v2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|" "bij v3" "|supp v3| <o |UNIV :: 'a3 set|"
  shows "map_F' (v1 o u1) (v2 o u2) (v3 o u3) = map_F' v1 v2 v3 o map_F' u1 u2 u3"
  using assms by (intro ext, transfer)
    (auto simp: F.map_comp assms asBij_def asSS_def supp_comp_bound supp_id_bound infinite_UNIV)

lemma F'_set1_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "set1_F' (map_F' u1 u2 u3 b) = u1 ` set1_F' b"
  using assms by transfer (auto simp: F.set_map asSS_def)

lemma F'_set2_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "set2_F' (map_F' u1 u2 u3 b) = u2 ` set2_F' b"
  using assms by transfer (auto simp: F.set_map asSS_def)

lemma F'_set3_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "set3_F' (map_F' u1 u2 u3 b) = u3 ` set3_F' b"
  using assms by transfer (auto simp: F.set_map asSS_def)

lemma F'_map_cong_[fundef_cong]:
  fixes u1 v1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 v2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 v3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|" "|supp v1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|" "bij v2" "|supp v2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|" "bij v3" "|supp v3| <o |UNIV :: 'a3 set|"
    and "\<forall> a \<in> set1_F' x. u1 a = v1 a"
    and "\<forall> a \<in> set2_F' x. u2 a = v2 a"
    and "\<forall> a \<in> set3_F' x. u3 a = v3 a"
  shows "map_F' u1 u2 u3 x = map_F' v1 v2 v3 x"
  using assms by transfer (auto intro: F.map_cong simp: asSS_def)

lemma F'_set1_bd: "\<And>b. |set1_F' b| <o natLeq"
  by transfer (simp add: F.set_bd)
lemma F'_set2_bd: "\<And>b. |set2_F' b| <o natLeq"
  by transfer (simp add: F.set_bd)
lemma F'_set3_bd: "\<And>b. |set3_F' b| <o natLeq"
  by transfer (simp add: F.set_bd)

lemma F'_rel_comp_leq_: "rrel_F' OO rrel_F' \<le> rrel_F'"
  apply (intro predicate2I, transfer)
  by (simp add: F.rel_eq)

lemma rrel_F_map_F3:
  fixes x :: "('a :: var,'b :: var,'c) F"
  shows "rrel_F (Grp (f :: 'c \<Rightarrow> 'c)) x y = rrel_F (=) (map_F id id f x) y"
  unfolding F.rel_map
  by (auto simp: Grp_def elim!: F.rel_mono_strong)

lemma asSS: "|supp u| <o |UNIV :: 'a set| \<Longrightarrow> asSS (u :: 'a \<Rightarrow> 'a) = u"
  unfolding asSS_def by auto

lemma F'_in_rel:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes u1: "|supp u1| <o |UNIV :: 'a1 set|"
    and u2: "bij u2" "|supp u2| <o |UNIV :: 'a2 set|" 
    and u3: "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "rrel_F' (map_F' u1 u2 u3 x) y = (\<exists>z. map_F' id id id z = x \<and> map_F' u1 u2 u3 z = y)"
  using assms
  apply (transfer fixing: u1 u2 u3)
  apply (auto simp: F.rel_map asSS supp_id_bound
    trans[OF rrel_F_map_F3[of u3, symmetric] F.in_rel[of u1 u2],
    simplified F.map_comp u1 u2 u3 supp_id_bound bij_id o_id True_implies_equals id_o])
  subgoal for z
    apply (rule exI[of _ "map_F id id fst z"])
    apply (auto simp: F.set_map supp_id_bound F.map_comp Grp_def
      intro!: F.map_cong nonrep_map_F_rev[OF bij_id supp_id_bound])
    done
  subgoal for z
    apply (rule exI[of _ "map_F id id (\<lambda>x. (x, u3 x)) z"])
    apply (auto simp: F.set_map supp_id_bound F.map_comp Grp_def
      intro!: F.map_cong)
    done
  done

lemma F'_strong:
  assumes "rrel_F' x x'" 
    and "rrel_F' x x'"
  shows "rrel_F' x x'" 
  using assms apply transfer unfolding mr_rel_F_def F.map_id by fastforce

mrbnf "('a::var, 'b::var, 'c::var) F'"
  map: map_F'
  sets: free: set1_F' bound: set2_F' bound: set3_F'
  bd: natLeq
  rel: rrel_F'
  var_class: var
  subgoal by (rule F'_map_id)
  subgoal by (rule F'_map_comp1_)
  subgoal by (rule F'_map_cong_; blast)
  subgoal by (auto simp: F'_set1_map_)
  subgoal by (auto simp: F'_set2_map_)
  subgoal by (auto simp: F'_set3_map_)
  subgoal by (rule infinite_regular_card_order_natLeq)
  subgoal by (rule F'_set1_bd)
  subgoal by (rule F'_set2_bd)
  subgoal by (rule F'_set3_bd)
  subgoal by (rule F'_rel_comp_leq_)
  subgoal by (simp, (rule F'_in_rel); assumption)
  done

end