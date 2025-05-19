theory Linearize
  imports "Binders.MRBNF_Composition"
begin

(* This theory we start with an MRBNF F, which is assumed (in the imported theory 
Common_Data_Codata_Bindings) to have the following characteristics:
  ** is map-constrained to small-support endofunctions in the 1st position, 
  ** is map-constrained to small-support endobijections in the 2nd position,  
  ** is unconstrained in the 3rd and 4th position.   
We show that applying the nonrepetitiveness construction at the 3rd position (on which F is assumed 
to be pullback-preserving), we transform it into an MRBNF F' that has the same characteristics 
as F except that the 3rd position becomes map-constrained to small-support endobijections.  
*)

typedecl ('a, 'b, 'c, 'd) F
consts map_F :: "('a :: var \<Rightarrow> 'a) \<Rightarrow> ('b :: var \<Rightarrow> 'b) \<Rightarrow>
  ('c \<Rightarrow> 'c') \<Rightarrow> ('d \<Rightarrow> 'd') \<Rightarrow> ('a, 'b, 'c, 'd) F \<Rightarrow> ('a, 'b, 'c', 'd') F"
consts set1_F :: "('a :: var, 'b :: var, 'c, 'd) F \<Rightarrow> 'a set"
consts set2_F :: "('a :: var, 'b :: var, 'c, 'd) F \<Rightarrow> 'b set"
consts set3_F :: "('a :: var, 'b :: var, 'c, 'd) F \<Rightarrow> 'c set"
consts set4_F :: "('a :: var, 'b :: var, 'c, 'd) F \<Rightarrow> 'd set"
consts rrel_F :: "('c \<Rightarrow> 'c' \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'd' \<Rightarrow> bool) \<Rightarrow> ('a :: var, 'b :: var, 'c, 'd) F \<Rightarrow> ('a, 'b, 'c', 'd') F \<Rightarrow> bool"

declare [[typedef_overloaded]]
mrbnf "('a :: var, 'b :: var, 'c, 'd) F"
  map: map_F
  sets: free: set1_F bound: set2_F live: set3_F live: set4_F
  bd: natLeq
  rel: rrel_F
  var_class: var
  sorry

ML \<open>map (fn x => x+1) [1, 2, 3] \<close>

ML \<open>@{term "map (\<lambda>x. x+1) [(1::int), 2, 3]"} \<close>
ML \<open>Const ("List.list.Nil", @{typ"int list"})\<close>

ML \<open>@{thm refl}\<close>

print_mrbnfs
declare [[ML_print_depth=10000]]
ML \<open>MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the \<close>

axiomatization where
(* The next property assumes preservation of pullbacks on the third position. 
   NB: All MRBNFs already preserve _weak_ pullbacks, i.e., they satisfy the following property 
   without uniqueness.  *)
  F_rel_map_set2_strong: 
  "\<And> R S (x :: ('a :: var,'b :: var,'c,'d) F) y.
    rrel_F R S x y =
      (\<exists>!z. set3_F z \<subseteq> {(x, y). R x y} \<and>
            set4_F z \<subseteq> {(x, y). S x y} \<and> map_F id id fst fst z = x \<and> map_F id id snd snd z = y)"
  and
(* The next property assumes that nonrepetitive elements exist: *)
  ex_nonrep: "\<exists>x. \<forall>x'. (\<exists> R. rrel_F R (=) x x') \<longrightarrow> (\<exists> f. x' = map_F id id f id x)"

abbreviation "rel_F \<equiv> mr_rel_F"

(* Important consequence of preservation of pullbacks (which is actually equivalent to it): 
The relator is closed under intersections. *)
lemma F_strong:
  "rel_F id id R3 R4 x y \<Longrightarrow> rel_F id id Q3 Q4 x y \<Longrightarrow> rel_F id id (inf R3 Q3) (inf R4 Q4) x y"
  unfolding F.map_id mr_rel_F_def
  apply (frule F.mr_rel_mono_strong0[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound,
    of _ _ _ _ top top, unfolded mr_rel_F_def F.map_id]; auto?)
  apply (drule F_rel_map_set2_strong[THEN iffD1, of top])
  apply (unfold F.in_rel[OF supp_id_bound bij_id supp_id_bound, unfolded id_apply F.map_id OO_Grp_alt]
    id_def[symmetric])
  apply clarsimp
  subgoal for z l r
    apply (frule spec2[of _ l z])
    apply (drule spec2[of _ r z])
    apply auto
    done
  done

(* Another important consequence: the following "exchange"-property, which could be read: 
Since the atoms have a fixed position, we can permute the relations: *)
lemma rel_F_exchange: 
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F" and x' :: "('a1,'a2,'a3','a4') F"
  assumes "rel_F id id R2 R3 x x'" and "rel_F id id Q2 Q3 x x'"
  shows "rel_F id id R2 Q3 x x'" 
  apply (rule F.mr_rel_mono_strong0[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound F_strong[OF assms]])
     apply auto
  done

(* Then notion of two items having the same shape (w.r.t. the 3rd position): *)
definition sameShape1 :: "('a1::var,'a2::var,'a3,'a4) F \<Rightarrow> ('a1,'a2,'a3,'a4) F \<Rightarrow> bool" where 
  "sameShape1 x x' \<equiv> \<exists> R. rel_F id id R (=) x x'"

definition nonrep2 :: "('a1::var,'a2::var,'a3,'a4) F \<Rightarrow> bool" where 
  "nonrep2 x \<equiv> \<forall> x'. sameShape1 x x' \<longrightarrow> (\<exists> f. x' = map_F id id f id x)"

lemma op_eq_triv_sym: "(\<lambda>x. (=) (g x)) = (\<lambda>x z. z = g x)"
  by force

lemma nonrep2_map_F:
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F"
    and v :: "'a1 \<Rightarrow> 'a1" and u :: "'a2\<Rightarrow>'a2" and g :: "'a4 \<Rightarrow> 'b4"
  assumes v: "|supp v| <o |UNIV :: 'a1 set|"  and u: "bij u" "|supp u| <o |UNIV :: 'a2 set|" 
  assumes "nonrep2 x"
  shows "nonrep2 (map_F v u id g x)"
unfolding nonrep2_def sameShape1_def proof safe
  fix y' :: "('a1,'a2,'a3,'b4) F" and R
  let ?y = "map_F v u id g x"
  assume r: "rel_F id id R (=) ?y y'"
  have "rel_F (v o id) (u o id) (R OO (=)) (Grp id OO Grp g) x y'"
    using r unfolding F.mr_rel_map(1)[OF v u supp_id_bound bij_id supp_id_bound]
    by (simp add: OO_def Grp_def op_eq_triv_sym[of g]) 
  then obtain x' where xx': "rel_F id id R (=) x x'" and y': "y' = map_F v u id g x'" 
    unfolding mr_rel_F_def o_id F.rel_compp eq_alt F.rel_Grp F.map_id
    apply atomize_elim
    apply (clarsimp simp: Grp_def id_def[symmetric] F.in_rel[OF v u]
        F.map_comp u v supp_id_bound)
    subgoal for z
      apply (rule exI[of _ "map_F id id snd snd z"] conjI)
      apply (auto simp: F.rel_map F.set_map F.map_comp u v supp_id_bound intro!: F.rel_refl_strong)
      done
    done
  obtain f where x': "x' = map_F id id f id x" 
    using assms xx' unfolding nonrep2_def sameShape1_def by auto
  show "\<exists>f. y' = map_F id id f id ?y"
    apply(rule exI[of _ f])
    apply (auto simp: x' y' F.map_comp supp_id_bound u v)
    done
qed

(* Here we need pullback preservation: *)
lemma nonrep2_map_F_rev:
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F" and u :: "'a2\<Rightarrow>'a2" and g :: "'a4 \<Rightarrow> 'b4"
  assumes u: "bij u" "|supp u| <o |UNIV :: 'a2 set|" 
  assumes "nonrep2 (map_F id u id g x)"
  shows "nonrep2 x"
  unfolding nonrep2_def sameShape1_def proof safe
  fix x' :: "('a1,'a2,'a3,'a4) F" and R 
  let ?y = "map_F id u id g x"  let ?y' = "map_F id u id g x'"
  assume r: "rel_F id id R (=) x x'"
  hence "rel_F id id R (=) ?y ?y'" 
    unfolding F.mr_rel_map(1)[OF supp_id_bound u supp_id_bound bij_id supp_id_bound]
    using F.mr_rel_map(2)[OF supp_id_bound bij_id supp_id_bound supp_id_bound u, of R "(=)" x x' id g]
    by (simp add: op_eq_triv_sym[of g] OO_def Grp_def)
  then obtain f where "?y' = map_F id id f id ?y" 
    using assms unfolding nonrep2_def sameShape1_def by auto
  hence y':"?y' = map_F id u f g x"
    by (simp add: F.map_comp supp_id_bound u)
  hence "rel_F id u (Grp id) (Grp g) x' (map_F id u f g x)"
    unfolding F.mr_rel_Grp[OF supp_id_bound u]
    by (auto simp: Grp_def)
  hence "rel_F id id (Grp f) (Grp g OO conversep (Grp g)) x x'"
    apply(subst F.mr_rel_flip[OF bij_id supp_id_bound bij_id supp_id_bound, simplified, symmetric])
    unfolding F.mr_rel_map(3)[OF supp_id_bound u bij_id supp_id_bound u] Grp_def
    by (auto simp add: u conversep_def OO_def supp_id_bound elim!: F.mr_rel_mono_strong0[rotated 6])
  from rel_F_exchange[OF this r]
  have "rel_F id id (Grp f) (=) x x'" .
  thus "\<exists>f. x' = map_F id id f id x"
    apply(intro exI[of _ f])  unfolding eq_alt F.mr_rel_Grp[OF supp_id_bound bij_id supp_id_bound] by (simp add: Grp_def)
qed

lemma nonrep2_mapF_bij:
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F" and g::"'a3\<Rightarrow>'a3"
  assumes g: "bij g" and x: "nonrep2 x"
  shows "nonrep2 (map_F id id g id x)" (is "nonrep2 ?x'")
  unfolding nonrep2_def sameShape1_def proof safe
  fix y' :: "('a1,'a2,'a3,'a4)F" and R'
  let ?y = "map_F id id (inv g) id y'" 
  let ?R = "Grp g OO R' OO conversep (Grp g)"
  assume "rel_F id id R' (=) ?x' y'"
  hence "rel_F id id ?R (=) x ?y"
    unfolding F.mr_rel_map(1)[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound]
      F.mr_rel_map(3)[OF supp_id_bound bij_id supp_id_bound bij_id supp_id_bound bij_id supp_id_bound] 
    by (simp add: g Grp_def OO_def o_def id_def)
  with x obtain f where "?y = map_F id id f id x" 
    unfolding nonrep2_def sameShape1_def by auto
  thus "\<exists>f'. y' = map_F id id f' id ?x'"
    apply(intro exI[of _ "g o f o inv g"])
    apply(auto simp add: g F.map_comp o_assoc[symmetric] supp_id_bound F.map_id
      dest!: arg_cong[where f = "map_F id id g id" and y = "map_F id id f id x"])
    done
qed

lemma nonrep2_mapF_bij_2:
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F"
    and v :: "'a1 \<Rightarrow> 'a1" and u :: "'a2\<Rightarrow>'a2" and g::"'a3\<Rightarrow>'a3" and f::"'a4\<Rightarrow>'a4'"
  assumes v: "|supp v| <o |UNIV :: 'a1 set|" and u: "bij u" "|supp u| <o |UNIV :: 'a2 set|"
    and g: "bij g" and x: "nonrep2 x"
  shows "nonrep2 (map_F v u g f x)" 
proof-
  have "nonrep2 (map_F v u id f x)" (is "nonrep2 ?x'") by (simp add: nonrep2_map_F v u x)
  hence "nonrep2 (map_F id id g id ?x')" using g nonrep2_mapF_bij u by blast
  thus ?thesis
    by (simp add: F.map_comp supp_id_bound u v)
qed

typedef ('a1::var,'a2::var,'a3::var,'a4) F' = "{x :: ('a1,'a2,'a3,'a4) F. nonrep2 x}"
  unfolding mem_Collect_eq nonrep2_def sameShape1_def mr_rel_F_def F.map_id id_apply
  unfolding id_def[symmetric]
  by (rule ex_nonrep)

setup_lifting type_definition_F'

definition set1_F' :: "('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> 'a1 set" where "set1_F' = set1_F o Rep_F'"
definition set2_F' :: "('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> 'a2 set" where "set2_F' = set2_F o Rep_F'"
definition set3_F' :: "('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> 'a3 set" where "set3_F' = set3_F o Rep_F'"
definition set4_F' :: "('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> 'a4 set" where "set4_F' = set4_F o Rep_F'"

definition asSS :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "asSS f \<equiv> if |supp f| <o |UNIV :: 'a set| then f else id"

definition map_F' :: "('a1::var \<Rightarrow> 'a1) \<Rightarrow> ('a2::var \<Rightarrow> 'a2) \<Rightarrow> ('a3::var \<Rightarrow> 'a3) \<Rightarrow> ('a4 \<Rightarrow> 'a4') 
  \<Rightarrow> ('a1,'a2,'a3,'a4) F' \<Rightarrow> ('a1,'a2,'a3,'a4') F'"
  where "map_F' v u f g = Abs_F' o map_F (asSS v) (asSS (asBij u)) (asBij f) g o Rep_F'"

definition rrel_F' :: "('a4 \<Rightarrow> 'a4' \<Rightarrow> bool) \<Rightarrow> ('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> ('a1,'a2,'a3,'a4') F' \<Rightarrow> bool"
  where "rrel_F' R x x' = rrel_F (=) R (Rep_F' x) (Rep_F' x')"

lift_definition rrel_F'_orig :: "('a4 \<Rightarrow> 'a4' \<Rightarrow> bool) \<Rightarrow> ('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> ('a1,'a2,'a3,'a4') F' \<Rightarrow> bool"
  is "rrel_F (=)" .

(* Verifying the axioms of a MRBNF for F':  *)

lemma F'_map_id: "map_F' id id id id = id"
  by (rule ext) (simp add: F.map_id asSS_def map_F'_def Rep_F'_inverse)

lemma F'_map_comp1_:
  fixes u1 v1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 v2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 v3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|" "|supp v1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|" "bij v2" "|supp v2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|" "bij v3" "|supp v3| <o |UNIV :: 'a3 set|"
  shows "map_F' (v1 o u1) (v2 o u2) (v3 o u3) (g o f) = map_F' v1 v2 v3 g o map_F' u1 u2 u3 f"
  using assms by (intro ext)
    (simp add: F.map_comp assms asBij_def asSS_def supp_comp_bound supp_id_bound infinite_UNIV
      map_F'_def nonrep2_mapF_bij_2[OF assms(1,3,4,7)] Rep_F'[simplified] Abs_F'_inverse)

lemma F'_set1_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "set1_F' (map_F' u1 u2 u3 f b) = u1 ` set1_F' b"
  using assms by (simp add: F.set_map asSS_def set1_F'_def map_F'_def
      nonrep2_mapF_bij_2[OF assms(1-4)] Abs_F'_inverse Rep_F'[simplified])

lemma F'_set2_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "set2_F' (map_F' u1 u2 u3 f b) = u2 ` set2_F' b"
  using assms by (simp add: F.set_map asSS_def set2_F'_def map_F'_def
      nonrep2_mapF_bij_2[OF assms(1-4)] Abs_F'_inverse Rep_F'[simplified])

lemma F'_set3_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "set3_F' (map_F' u1 u2 u3 f b) = u3 ` set3_F' b"
  using assms by (simp add: F.set_map asSS_def set3_F'_def map_F'_def
      nonrep2_mapF_bij_2[OF assms(1-4)] Abs_F'_inverse Rep_F'[simplified])

lemma F'_set4_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "set4_F' (map_F' u1 u2 u3 f b) = f ` set4_F' b"
  using assms by (simp add: F.set_map asSS_def set4_F'_def map_F'_def
      nonrep2_mapF_bij_2[OF assms(1-4)] Abs_F'_inverse Rep_F'[simplified])

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
    and "\<forall> a \<in> set4_F' x. f a = g a"
  shows "map_F' u1 u2 u3 f x = map_F' v1 v2 v3 g x"
  using assms
  unfolding map_F'_def set1_F'_def set2_F'_def set3_F'_def set4_F'_def asSS_def
  by (simp add: F.map_cong[of u1 u2 v1 v2])

thm F.map_cong[of u1 u2 v1 v2 "(Rep_F' x)" "(Rep_F' x)" u3 v3 f g]

lemma F'_set1_bd: "\<And>b. |set1_F' b| <o natLeq"
  unfolding set1_F'_def
  by (subst o_apply) (rule F.set_bd)
lemma F'_set2_bd: "\<And>b. |set2_F' b| <o natLeq"
  unfolding set2_F'_def
  by (subst o_apply) (rule F.set_bd)
lemma F'_set3_bd: "\<And>b. |set3_F' b| <o natLeq"
  unfolding set3_F'_def
  by (subst o_apply) (rule F.set_bd)
lemma F'_set4_bd: "\<And>b. |set4_F' b| <o natLeq"
  unfolding set4_F'_def
  by (subst o_apply) (rule F.set_bd)

lemma F'_rel_comp_leq_: "rrel_F' Q OO rrel_F' R \<le> rrel_F' (Q OO R)"
  apply (rule predicate2I)
  apply (auto simp: rrel_F'_def F.rel_compp[of "(=)", simplified])
  done


lemma rrel_F_map_F3:
  fixes x :: "('a :: var,'b :: var,'c,'d) F"
  shows "rrel_F (Grp (f :: 'c \<Rightarrow> 'c)) R x y = rrel_F (=) R (map_F id id f id x) y"
  unfolding F.rel_map Grp_def
  apply (rule iffI)
  apply (erule F.rel_mono_strong; simp)+
  done

lemma asSS: "|supp u| <o |UNIV :: 'a set| \<Longrightarrow> asSS (u :: 'a \<Rightarrow> 'a) = u"
  unfolding asSS_def by simp

lemma F'_in_rel:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes u1: "|supp u1| <o |UNIV :: 'a1 set|"
    and u2: "bij u2" "|supp u2| <o |UNIV :: 'a2 set|" 
    and u3: "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "rrel_F' R (map_F' u1 u2 u3 id x) y =
    (\<exists>z. set4_F' z \<subseteq> {(x, y). R x y} \<and> map_F' id id id fst z = x \<and> map_F' u1 u2 u3 snd z = y)"
  using assms
  unfolding rrel_F'_def set4_F'_def map_F'_def
  apply (simp add: asSS Abs_F'_inverse nonrep2_mapF_bij_2[OF assms(1,2,3,4)] Rep_F'[simplified])
  apply (simp add: Rep_F'[simplified] asSS F.rel_map supp_id_bound)
  apply (simp add: trans[OF rrel_F_map_F3[of u3, symmetric] F.in_rel[of u1 u2],
    simplified F.map_comp u1 u2 u3 supp_id_bound bij_id o_id True_implies_equals id_o])
  apply (auto)
  unfolding Grp_def
  subgoal for z
    apply (rule exI[of _ "Abs_F' (map_F id id fst id z)"])
    apply (simp add: supp_id_bound F.map_comp[of id id id id id fst fst id]
      nonrep2_map_F_rev[OF bij_id supp_id_bound, of fst] Abs_F'_inverse Rep_F'[simplified])
    apply (intro conjI)
    subgoal
      by(simp add: F.set_map(4) supp_id_bound)
    subgoal
      by(rule Rep_F'_inverse)
    subgoal
      apply (auto simp: supp_id_bound F.map_comp intro!: F.map_cong)
      sorry
      done
  subgoal for z
    apply (rule exI[of _ "map_F id id (\<lambda>x. (x, u3 x)) id (Rep_F' z)"])
    apply (simp add: Abs_F'_inverse Rep_F'[simplified]
        nonrep2_mapF_bij_2 supp_id)
    apply (auto simp: F.set_map supp_id_bound F.map_comp intro: F.map_cong)
    done
  done


lemma F'_strong:
  assumes "rrel_F' R x x'" 
    and "rrel_F' Q x x'"
  shows "rrel_F' (inf R Q) x x'" 
  using assms F_strong[of "(=)" _ _ _ "(=)"] 
  by(simp add: rrel_F'_def mr_rel_F_def F.map_id)

find_theorems "(\<And>x. _  = _)  \<Longrightarrow> _ = _ "

mrbnf "('a::var, 'b::var, 'c::var, 'd) F'"
  map: map_F'
  sets: free: set1_F' bound: set2_F' bound: set3_F' live: set4_F'
  bd: natLeq
  rel: rrel_F'
  var_class: var
  subgoal by (rule F'_map_id)
  subgoal by (rule F'_map_comp1_)
  subgoal by (rule F'_map_cong_; blast)
  subgoal by (standard, simp add: F'_set1_map_)
  subgoal by (standard, simp add: F'_set2_map_)
  subgoal by (standard, simp add: F'_set3_map_)
  subgoal by (standard, simp add: F'_set4_map_)
  subgoal by (rule infinite_regular_card_order_natLeq)
  subgoal by (rule F'_set1_bd)
  subgoal by (rule F'_set2_bd)
  subgoal by (rule F'_set3_bd)
  subgoal by (rule F'_set4_bd)
  subgoal by (rule F'_rel_comp_leq_)
  subgoal by (rule F'_in_rel)
  done

end