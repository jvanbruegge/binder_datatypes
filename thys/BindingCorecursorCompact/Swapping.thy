theory Swapping 
imports Infinitary_Lambda_Terms
begin

(* Nominal-logic-style swapping: *)
definition nswapping :: "('c \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'c) \<Rightarrow>  bool" where
"nswapping swp \<equiv> 
  (\<forall> c x. swp c x x = c) \<and> 
  (\<forall> c x y. swp (swp c x y) x y = c) \<and> 
  (\<forall> x y c z1 z2. swp (swp c x y) z1 z2 = swp (swp c z1 z2) (sw x z1 z2) (sw y z1 z2))"

lemma nswapping_sym0: "nswapping swp \<Longrightarrow> swp (swp c x y) y x = c"
unfolding nswapping_def
proof safe
  assume 1:"\<forall>c x. swp c x x = c" and 2:"\<forall>c x y. swp (swp c x y) x y = c" 
    and 3:"\<forall>x y c z1 z2. swp (swp c x y) z1 z2 = swp (swp c z1 z2) (sw x z1 z2) (sw y z1 z2)"
  show "swp (swp c x y) y x = c"
    unfolding 3[rule_format, of c x y] by(simp add: 2)
qed

lemma nswapping_sym1: assumes "nswapping swp" shows "swp c x y = swp c y x"
  using nswapping_sym0[OF assms] assms
  unfolding nswapping_def by metis

definition supports :: "('c \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'c) \<Rightarrow> var set \<Rightarrow> 'c \<Rightarrow> bool" where
  "supports swp A c \<equiv> \<forall> x y. x \<notin> A \<and> y \<notin> A \<longrightarrow> swp c x y = c"

(* The nominal notion of freshness (adapted to use countability instead of finiteness) *)
definition nfresh:: "('c \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'c) \<Rightarrow> var \<Rightarrow> 'c \<Rightarrow> bool" where
  "nfresh swp x c \<equiv> countable {y . swp c y x \<noteq> c}"

lemma supports_nfresh: 
assumes cA: "countable A" and supp: "supports swp A d" and z: "z \<notin> A"
shows "nfresh swp z d"
proof- 
  have "{y . swp d y z \<noteq> d} \<subseteq> A"
  using supp z unfolding supports_def by auto
  thus ?thesis unfolding nfresh_def using cA  
    by (meson countable_subset)
qed

lemma nfresh_supports: 
assumes swp: "nswapping swp"
and nf: "nfresh swp z c"
shows "\<exists>A. countable A \<and> supports swp A c \<and> z \<notin> A"
apply(rule exI[of _ "{y. swp c y z \<noteq> c}"], intro conjI)
  subgoal using nf unfolding nfresh_def .
  subgoal unfolding supports_def proof auto
    fix x y assume 0: "swp c x z = c" "swp c y z = c"
    show "swp c x y = c"
    proof(cases "x = y")
      case True
      thus ?thesis by (metis nswapping_def swp)
    next
      case False 
      have "swp (swp c z y) z x = swp (swp c z x) (sw z z x) (sw y z x)"
      by (metis nswapping_def swp)
      thus ?thesis by (metis 0 False nswapping_sym0 sw_def swp)
    qed
  qed
  subgoal by (simp, metis nswapping_def swp) .

(* Next is an alternative definition of freshness.
The two definitions are equivalent under the assumptions 
of swapping (which correspond exactTransly to the assumptions about permutation-actTransion).
NB: No need to assume finite support to prove their equivalence! 
*)
lemma nfresh_altDef: 
assumes swp: "nswapping swp"
shows "nfresh swp z c \<longleftrightarrow> (\<exists>A. countable A \<and> supports swp A c \<and> z \<notin> A)"
by (smt (verit) countable_subset mem_Collect_eq nfresh_def nfresh_supports subsetI supports_def swp)


definition countable_supp :: "('c \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> bool" where
  "countable_supp swp c \<equiv>
  \<exists> A. countable A \<and> supports swp A c"

(* *)

lemma fun_upd_id_same[simp]: "id(x := x) = id"
  by auto

lemma id_swapTwice: "id(x := y, y := x) \<circ> id(x := y, y := x) = id"
  by auto

lemma id_swapTwice2: 
"id(sw x z1 z2 := sw y z1 z2, sw y z1 z2 := sw x z1 z2) \<circ> id(z1 := z2, z2 := z1) = 
 id(z1 := z2, z2 := z1) \<circ> id(x := y, y := x)" 
apply (rule ext) by (simp add: sw_def)

definition fsupp :: "(var \<Rightarrow> var) \<Rightarrow> bool" where 
"fsupp \<sigma> \<equiv> finite {x . \<sigma> x \<noteq> x}"

lemma fsupp_id[simp,intro!]: "fsupp id"
  unfolding fsupp_def by auto  

lemmas Fun.bij_id[intro!]

lemma fsupp_upd[simp]: "fsupp (\<sigma>(x:=y)) = fsupp \<sigma>"
proof-
  have "{z . (\<sigma>(x:=y)) z \<noteq> z} \<subseteq> {z . \<sigma> z \<noteq> z} \<union> {x}" unfolding fsupp_def by auto
  moreover have "{z . \<sigma> z \<noteq> z} \<subseteq> {z . (\<sigma>(x:=y)) z \<noteq> z} \<union> {x}" unfolding fsupp_def by auto
  ultimately show ?thesis unfolding fsupp_def
    by (meson finite.emptyI finite.insertI finite_UnI finite_subset)
qed

lemma bij_id_upd2[simp,intro!]: "bij (id(x:=y,y:=x))"
unfolding id_def bij_def inj_def surj_def by simp metis

lemma fsupp_o: 
assumes "fsupp \<sigma>" and "fsupp \<tau>"
shows "fsupp (\<tau> o \<sigma>)"
proof-
  have "{z . (\<tau> o \<sigma>) z \<noteq> z} \<subseteq> {z . \<sigma> z \<noteq> z} \<union> {z . \<tau> z \<noteq> z}" by auto
  thus ?thesis using assms unfolding fsupp_def using infinite_super by auto
qed

definition "supp \<sigma> \<equiv> {x. \<sigma> x \<noteq> x}" 
definition "imsupp \<sigma> \<equiv> supp \<sigma> \<union> \<sigma> ` (supp \<sigma>)"
definition "csupp \<sigma> \<equiv> countable (supp \<sigma>)" 

lemma supp_o: "supp (\<tau> o \<sigma>) \<subseteq> supp \<sigma> \<union> supp \<tau>"
proof-
  have "{z . (\<tau> o \<sigma>) z \<noteq> z} \<subseteq> {z . \<sigma> z \<noteq> z} \<union> {z . \<tau> z \<noteq> z}" by auto
  thus ?thesis  
  by (simp add: countable_subset supp_def)
qed

lemma imsupp_o: "imsupp (\<tau> o \<sigma>) \<subseteq> imsupp \<sigma> \<union> imsupp \<tau>"
using supp_o unfolding imsupp_def image_def apply auto 
apply fastforce+ 
by (metis (mono_tags) comp_eq_dest_lhs mem_Collect_eq supp_def) 


lemma csupp_o: 
assumes "csupp \<sigma>" and "csupp \<tau>"
shows "csupp (\<tau> o \<sigma>)"
by (meson assms countable_Un countable_subset csupp_def supp_o)

lemmas bij_o = Fun.bij_comp

lemma csupp_id[simp,intro!]: "csupp id"
  unfolding csupp_def 
  by (simp add: supp_def)

lemma csupp_upd[simp]: "csupp (\<sigma>(x:=y)) = csupp \<sigma>"
proof-
  have "{z . (\<sigma>(x:=y)) z \<noteq> z} \<subseteq> {z . \<sigma> z \<noteq> z} \<union> {x}" unfolding csupp_def by auto
  moreover have "{z . \<sigma> z \<noteq> z} \<subseteq> {z . (\<sigma>(x:=y)) z \<noteq> z} \<union> {x}" unfolding csupp_def by auto
  ultimately show ?thesis unfolding csupp_def supp_def 
    by (meson countable_Un countable_empty countable_insert countable_subset) 
qed

(* Set-based versions: *)

definition nswappingOn :: "'c set \<Rightarrow> ('c \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'c) \<Rightarrow>  bool" where
"nswappingOn D swp \<equiv> 
  (\<forall> c x. c \<in> D \<longrightarrow> swp c x x = c) \<and> 
  (\<forall> c x y. c \<in> D \<longrightarrow> swp (swp c x y) x y = c) \<and> 
  (\<forall> x y c z1 z2. c \<in> D \<longrightarrow> swp (swp c x y) z1 z2 = swp (swp c z1 z2) (sw x z1 z2) (sw y z1 z2))"


end 