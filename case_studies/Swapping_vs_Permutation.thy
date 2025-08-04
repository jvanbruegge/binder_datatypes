(* This theory formalizes the connection between swapping and permutation-action.
It covers:
(1)the equivalence of the two alternative axiomatizations of nominal sets (which both define
freshness from swapping), as well as
(2) an extension of this equivalence factoring in an independent freeness-like operator
(more loosely connected to swapping, as in the swap/free models.
*)

theory Swapping_vs_Permutation
  imports
    "HOL-Library.Countable_Set_Type"
begin


class cinf = countable +
  assumes infinite: "infinite (UNIV :: 'a set)"

instantiation nat :: cinf begin
instance by standard auto
end

lemma exists_fresh: "finite (A :: 'v :: cinf set) \<Longrightarrow> \<exists>x. x \<notin> A"
  using ex_new_if_finite infinite by auto

definition sw :: "'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v" where
"sw x y z \<equiv> if x = y then z else if x = z then y else x"

lemma sw_eqL[simp,intro!]: "\<And> x y z. sw x x y = y"
and sw_eqR[simp,intro!]: "\<And> x y z. sw x y x = y"
and sw_diff[simp]: "\<And> x y z. x \<noteq> y \<Longrightarrow> x \<noteq> z \<Longrightarrow> sw x y z = x"
  unfolding sw_def by auto

lemma sw_sym: "sw x y z = sw x z y"
and sw_id[simp]: "sw x y y = x"
and sw_sw: "sw (sw x y z) y1 z1 = sw (sw x y1 z1) (sw y y1 z1) (sw z y1 z1)"
and sw_invol[simp]: "sw (sw x y z) y z = x"
  unfolding sw_def by auto

lemma sw_invol2: "sw (sw x y z) z y = x"
  by (simp add: sw_sym)

lemma sw_inj[iff]: "sw x z1 z2 = sw y z1 z2 \<longleftrightarrow> x = y"
  unfolding sw_def by auto

lemma sw_surj: "\<exists>y. x = sw y z1 z2"
  by (metis sw_invol)

definition "sb a x y \<equiv> if a = y then x else a"

lemma list_induct_Pair[case_names Nil Cons]:
"P [] \<Longrightarrow> (\<And>z1 z2 z1z2s. P z1z2s  \<Longrightarrow> P ((z1,z2) # z1z2s)) \<Longrightarrow> P z1z2s"
by (metis list.inducts surj_pair)

(* Nominal-logic-style swapping: *)
definition nswapping :: "('c \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'c) \<Rightarrow>  bool" where
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

definition supports :: "('c \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'c) \<Rightarrow> 'v :: cinf set \<Rightarrow> 'c \<Rightarrow> bool" where
  "supports swp A c \<equiv> \<forall> x y. x \<notin> A \<and> y \<notin> A \<longrightarrow> swp c x y = c"


(* The nominal notion of freshness *)
definition nfresh:: "('c \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'c) \<Rightarrow> 'v :: cinf \<Rightarrow> 'c \<Rightarrow> bool" where
  "nfresh swp x c \<equiv> finite {y . swp c y x \<noteq> c}"

lemma supports_nfresh:
assumes fA: "finite A" and supp: "supports swp A d" and z: "z \<notin> A"
shows "nfresh swp z d"
proof-
  have "{y . swp d y z \<noteq> d} \<subseteq> A"
  using supp z unfolding supports_def by auto
  thus ?thesis unfolding nfresh_def using fA by (meson rev_finite_subset)
qed

lemma nfresh_supports:
assumes swp: "nswapping swp"
and nf: "nfresh swp z c"
shows "\<exists>A. finite A \<and> supports swp A c \<and> z \<notin> A"
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
of swapping (which correspond exactly to the assumptions about permutation-action).
NB: No need to assume finite support to prove their equivalence!
*)
lemma nfresh_altDef:
assumes swp: "nswapping swp"
shows "nfresh swp z c \<longleftrightarrow> (\<exists>A. finite A \<and> supports swp A c \<and> z \<notin> A)"
by (meson nfresh_supports supports_nfresh swp)


definition finite_supp :: "('c \<Rightarrow> 'v :: cinf \<Rightarrow> 'v \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> bool" where
  "finite_supp swp c \<equiv>
  \<exists> A. finite A \<and> supports swp A c"

(* Set-based version of the axioms: *)
definition nswappingOn :: "'a set \<Rightarrow> ('a \<Rightarrow> 'v :: cinf \<Rightarrow> 'v \<Rightarrow> 'a) \<Rightarrow> bool" where
"nswappingOn D swp \<equiv>
(\<forall>d x. d \<in> D \<longrightarrow> swp d x x = d) \<and>
(\<forall>d x y. d \<in> D \<longrightarrow> swp (swp d x y) x y = d) \<and>
(\<forall>x y d z1 z2. d \<in> D \<longrightarrow> swp (swp d x y) z1 z2 = swp (swp d z1 z2) (sw x z1 z2) (sw y z1 z2))"

lemma nswapping_nswappingOn: "nswapping swp \<Longrightarrow> nswappingOn D swp"
unfolding nswapping_def nswappingOn_def by auto

thm nswapping_def[no_vars]

thm nswapping_def

lemma fun_upd_id_same[simp]: "id(x := x) = id"
  by auto

lemma id_swapTwice: "id(x := y, y := x) \<circ> id(x := y, y := x) = id"
  by auto

lemma id_swapTwice2:
"id(sw x z1 z2 := sw y z1 z2, sw y z1 z2 := sw x z1 z2) \<circ> id(z1 := z2, z2 := z1) =
 id(z1 := z2, z2 := z1) \<circ> id(x := y, y := x)"
apply (rule ext) by (simp add: sw_def)

definition fsupp :: "('v :: cinf \<Rightarrow> 'v) \<Rightarrow> bool" where
"fsupp \<sigma> \<equiv> finite {x . \<sigma> x \<noteq> x}"

lemma fsupp_id[simp,intro!]: "fsupp id"
  unfolding fsupp_def by auto

lemmas Fun.bij_id[simp,intro!]

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

lemmas bij_o = Fun.bij_comp

definition permut :: "('c \<Rightarrow> ('v :: cinf \<Rightarrow> 'v) \<Rightarrow> 'c) \<Rightarrow> bool" where
"permut perm \<equiv>
  (\<forall> c. perm c id = c) \<and>
  (\<forall> c \<sigma> \<tau>. bij \<sigma> \<and> fsupp \<sigma> \<and> bij \<tau> \<and> fsupp \<tau> \<longrightarrow> perm (perm c \<sigma>) \<tau> = perm c (\<tau> o \<sigma>))"


(* One direction: *)

definition toSwp :: "('c \<Rightarrow> ('v :: cinf \<Rightarrow> 'v) \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'c)" where
"toSwp perm c x y = perm c (id(x:=y,y:=x))"

theorem nswapping_toSwp:
assumes "permut perm"
shows "nswapping (toSwp perm)"
proof-
  have [simp]: "\<And>c \<sigma> \<tau>. bij \<sigma> \<Longrightarrow> fsupp \<sigma> \<Longrightarrow> bij \<tau> \<Longrightarrow> fsupp \<tau>  \<Longrightarrow> perm (perm c \<sigma>) \<tau> = perm c (\<tau> \<circ> \<sigma>) "
   using assms unfolding permut_def by auto
  show ?thesis using assms unfolding nswapping_def permut_def toSwp_def
  by (auto simp add: id_swapTwice id_swapTwice2)
qed

(* The other direction: *)

(* Composition of a list of transpositions:   *)
fun compose :: "('v :: cinf \<times> 'v) list \<Rightarrow> ('v \<Rightarrow> 'v)" where
 "compose [] = id"
|"compose ((z1,z2) # z1z2s) = (id(z1:=z2,z2:=z1)) o compose z1z2s"

lemma compose_append: "compose (z1z2s @ z1z2s') c = compose z1z2s (compose z1z2s' c)"
by(induct z1z2s) auto

(* Action of a list of transpositions: *)
fun act :: "('c \<Rightarrow> 'v :: cinf \<Rightarrow> 'v \<Rightarrow> 'c) \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 'c \<Rightarrow> 'c" where
 "act swp [] c = c"
|"act swp ((z1,z2) # z1z2s) c = swp (act swp z1z2s c) z1 z2"

lemma act_append: "act swp (z1z2s @ z1z2s') c = act swp z1z2s (act swp z1z2s' c)"
by(induct z1z2s) auto




(*Preliminary lemmas about swapping algebras*)
lemma compose_hd_sym:"compose ((x,y) # z1z2s) = compose ((y,x) # z1z2s)"
  unfolding compose.simps(2) by auto

lemma act_hd_sym: assumes "nswapping swp"
  shows "act swp ((x,y) # z1z2s) c = act swp ((y,x) # z1z2s) c"
  unfolding act.simps(2) using nswapping_sym1[OF assms] by presburger

lemma compose_disj_supp_commutes: assumes"{x1,x2} \<inter> {y1,y2} = {}"
  shows "compose ((x1,x2) # (y1,y2) # z1z2s) = compose ((y1,y2) # (x1,x2) # z1z2s)"
  unfolding compose.simps(2) o_assoc using assms fun_upd_twist by auto

lemma act_disj_supp_commutes: assumes "nswapping swp" "{x1,x2} \<inter> {y1,y2} = {}"
  shows "act swp ((x1,x2) # (y1,y2) # z1z2s) c = act swp ((y1,y2) # (x1,x2) # z1z2s) c"
  unfolding act.simps(2) sw_def
    assms(1)[unfolded nswapping_def, THEN conjunct2, THEN conjunct2, rule_format, of _ y1 y2 x1 x2]
  using assms(2) by fastforce

lemma bij_compose[simp,intro!]: "bij (compose x1x2s)"
apply(induct x1x2s, safe) subgoal unfolding compose.simps by blast
subgoal for a b x1x2s unfolding compose.simps by (simp add: bij_o)
done

lemma compose_diff_implies_diff_im: "compose x1x2s x \<noteq> x
  \<Longrightarrow> compose x1x2s (compose x1x2s x) \<noteq> compose x1x2s x"
  using bij_compose bij_is_inj by (metis injD)

lemma compose_support0:assumes "\<forall> p. p \<in> set x1x2s \<longrightarrow> x \<noteq> fst p \<and> x \<noteq> snd p"
  shows "compose x1x2s x = x"
  using assms
proof(induct x1x2s, simp)
  fix a x1x2s
  assume ih':"\<forall>p. p \<in> set x1x2s \<longrightarrow> x \<noteq> fst p \<and> x \<noteq> snd p \<Longrightarrow> compose x1x2s x = x"
    and h':"\<forall>p. p \<in> set (a # x1x2s) \<longrightarrow> x \<noteq> fst p \<and> x \<noteq> snd p"
  obtain a1 a2 where a:"a = (a1,a2)" by fastforce
  have h:"\<forall>p. p \<in> set x1x2s \<longrightarrow> x \<noteq> fst p \<and> x \<noteq> snd p" "x \<noteq> a1" "x \<noteq> a2"
    apply (simp add: h') using a h' apply auto .
  have ih:"compose x1x2s x = x" by(rule ih'[OF h(1)])
  show "compose (a # x1x2s) x = x"
    unfolding a compose.simps by(simp add: h ih)
qed


lemma compose_support:"compose x1x2s x \<noteq> x \<Longrightarrow> (\<exists> p. p \<in> set x1x2s \<and> (x = fst p \<or> x = snd p))"
  using compose_support0 by blast

lemma compose_support_im:"compose x1x2s x \<noteq> x \<Longrightarrow>
  (\<exists> p. p \<in> set x1x2s \<and> (compose x1x2s x = fst p \<or> compose x1x2s x = snd p))"
  using compose_support0 compose_diff_implies_diff_im by metis

lemma compose_leftmost_eq: assumes notem:"x1x2s \<noteq> []"
  and tail:"\<forall> p. p \<in> set (tl x1x2s) \<longrightarrow> x2 \<noteq> fst p \<and> x2 \<noteq> snd p"
  and neq:"x1 \<noteq> x2"
shows "(compose x1x2s x2 = x1) = (hd x1x2s = (x1,x2) \<or> hd x1x2s = (x2,x1))"
proof(cases x1x2s, simp add: notem, safe)
  fix a b list
  assume hp:"x1x2s = (a, b) # list" "x1 = compose ((a, b) # list) x2"
    "hd ((a, b) # list) \<noteq> (x2, compose ((a, b) # list) x2)"
  have eq:"list = tl x1x2s" using hp(1) by simp
  show "hd ((a, b) # list) = (compose ((a, b) # list) x2, x2)"
    using hp(2) neq unfolding compose.simps o_apply eq compose_support0[OF tail]
    by (metis fun_upd_apply hp(2) hp(3) id_apply list.sel(1))
next
  fix a b list
  assume hp:"x1x2s = (a, b) # list" "hd ((a, b) # list) = (x1, x2)"
  have eq:"list = tl x1x2s" "(a,b) = (x1,x2)" using hp by simp_all
  show "compose ((a, b) # list) x2 = x1"
    unfolding eq compose.simps o_apply compose_support0[OF tail] by simp
next
  fix a b list
  assume hp:"x1x2s = (a, b) # list" "hd ((a, b) # list) = (x2, x1)"
  have eq:"list = tl x1x2s" "(a,b) = (x2,x1)" using hp by simp_all
  show "compose ((a, b) # list) x2 = x1"
    unfolding eq compose.simps o_apply compose_support0[OF tail] by simp
qed

lemma compose_head_same:"compose ((x,x)#x1x2s) x = compose x1x2s x"
  unfolding compose.simps by simp

lemma compose_leftmost1: assumes notem:"x1x2s \<noteq> []"
  and tail:"\<forall> p. p \<in> set (tl x1x2s) \<longrightarrow> x2 \<noteq> fst p \<and> x2 \<noteq> snd p"
  and head:"hd x1x2s = (x1,x2)"
shows "compose x1x2s x2 = x1"
  apply (cases "x1 = x2")
  subgoal using compose_head_same assms by (metis compose_support0 list.exhaust_sel)
  subgoal using compose_leftmost_eq[OF notem tail] head by simp
  done

lemma compose_leftmost2: assumes notem:"x1x2s \<noteq> []"
  and tail:"\<forall> p. p \<in> set (tl x1x2s) \<longrightarrow> x2 \<noteq> fst p \<and> x2 \<noteq> snd p"
  and head:"hd x1x2s = (x2,x1)"
shows "compose x1x2s x2 = x1"
  apply (cases "x1 = x2")
  subgoal using compose_head_same assms by (metis compose_support0 list.exhaust_sel)
  subgoal using compose_leftmost_eq[OF notem tail] head by simp
  done

lemma compose_pair_fix:"compose [(x,y)] z = z \<Longrightarrow> x \<noteq> y \<Longrightarrow> (x \<noteq> z \<and> y \<noteq> z)"
  unfolding compose.simps by auto


lemma compose_pair_push_left: assumes "compose [(a,b),(x0, x2)] x2 = x1"
  shows "\<exists> a0 b0.
          compose [(a,b),(x0, x2)] = compose [(x1,x2),(a0,b0)] \<and> x2 \<notin> {a0,b0}"
proof(cases "x0 = x1")
  case True
  show ?thesis unfolding True
  proof(cases "a = b")
    assume ab:"a = b"
    obtain xx where xx:"xx \<noteq> x1" "xx \<noteq> x2"
       using exists_fresh[of "{x1,x2}"] by auto
    show "\<exists> a0 b0. compose [(a,b),(x1, x2)] = compose [(x1,x2),(a0,b0)] \<and> x2 \<notin> {a0,b0}"
       unfolding ab compose.simps apply(rule exI[of _ xx], rule exI[of _ xx])
       using xx by simp
  next
    assume ab:"a \<noteq> b"
    have  abfix:"compose [(a,b)] x1 = x1"
        using assms unfolding True compose.simps by simp
    have ab_x1:"a \<noteq> x1" "b \<noteq> x1"
        by(auto simp add: compose_pair_fix[OF abfix ab])
    show "\<exists> a0 b0. compose [(a,b),(x1, x2)] = compose [(x1,x2),(a0,b0)] \<and> x2 \<notin> {a0,b0}"
      apply (cases "a = x2")
      subgoal apply(rule exI[of _ x1], rule exI[of _ b])
      unfolding compose.simps using ab ab_x1
          by (simp add: fun_upd_comp fun_upd_twist)
      subgoal apply(cases "b = x2")
        subgoal apply(rule exI[of _ x1], rule exI[of _ a])
            unfolding compose.simps using ab ab_x1 fun_upd_twist by auto
        subgoal apply(rule exI[of _ a], rule exI[of _ b])
            unfolding compose.simps using ab_x1 fun_upd_twist by auto
        done
      done
  qed
next
  case False
  have step2:"compose [(a,b)] x0 = x1"
      using assms by simp
  have ab:"{x1,x0}={a,b}"
      using compose_support[OF False[symmetric, unfolded step2[symmetric]]]
        compose_support_im[OF False[symmetric, unfolded step2[symmetric]]]
      unfolding step2 using False by auto
  show ?thesis
  proof (cases "x0 = x2")
    assume comx2:"x0 = x2"
    obtain x00 where x00:"x00 \<notin> {x1,x2}"
        using exists_fresh by (meson finite.emptyI finite.insertI)
    show ?thesis unfolding comx2 apply(rule exI[of _ x00], rule exI[of _ x00], simp, safe)
      subgoal using ab unfolding comx2 by fastforce
      subgoal using x00 by blast done
  next
    assume comx2:"x0 \<noteq> x2"
    show ?thesis
      apply(cases "x1 = x2")
        subgoal apply(rule exI[of _ "x0"],
            rule exI[of _ "x0"], safe, simp_all add: comx2[symmetric])
          using ab comx2 unfolding compose.simps
          by (metis doubleton_eq_iff fun_upd_twist id_swapTwice)
        subgoal apply(rule exI[of _ x1], rule exI[of _ "x0"], safe,
            simp_all add: comx2[symmetric]) using comx2 ab
          by (smt comp_id doubleton_eq_iff fun_upd_comp
                    fun_upd_other fun_upd_same fun_upd_twist fun_upd_upd id_apply)
        done
  qed
qed


lemma compose_push_left:
  fixes x1x2s :: "('v \<times> 'v :: cinf) list"
  assumes notem:"x1x2s \<noteq> []"
  and inset:"\<exists> p. p \<in> set x1x2s \<and> (x2 = fst p \<or> x2 = snd p)"
  and image:"compose x1x2s x2 = x1"
shows "\<exists> x1x2s'. length x1x2s' = length x1x2s
  \<and> compose x1x2s' = compose x1x2s \<and> hd x1x2s' = (x1,x2)
  \<and> (\<forall> p. p \<in> set (tl x1x2s') \<longrightarrow> x2 \<noteq> fst p \<and> x2 \<noteq> snd p)"
  using assms
proof(induct x1x2s arbitrary: x1 x2 rule: length_induct, simp)
  fix x1x2s :: "('v \<times> 'v :: cinf) list" and x1 x2
  assume ih: "\<forall>ys :: ('v \<times> 'v :: cinf) list. length ys < length x1x2s \<longrightarrow>
            ys \<noteq> [] \<longrightarrow>
            (\<forall>x. (\<exists>a b. (a, b) \<in> set ys \<and> (x = a \<or> x = b)) \<longrightarrow>
                 (\<exists>x1x2s'.
                     length x1x2s' = length ys \<and>
                     compose x1x2s' = compose ys \<and>
                     hd x1x2s' = (compose ys x, x) \<and>
                     (\<forall>a b. (a, b) \<in> set (tl x1x2s') \<longrightarrow> x \<noteq> a \<and> x \<noteq> b)))"
    and neq:"x1x2s \<noteq> []"
    and inset:"\<exists> a b. (a,b) \<in> set x1x2s \<and> (x2 = a \<or> x2 = b)"
    and comp:"compose x1x2s x2 = x1"
  show "\<exists>x1x2s'.
          length x1x2s' = length x1x2s \<and>
          compose x1x2s' = compose x1x2s \<and> hd x1x2s' = (x1, x2)
         \<and> (\<forall>a b. (a, b) \<in> set (tl x1x2s') \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b)"
    apply(cases x1x2s, simp add:neq)
  proof safe
    fix a b and y1y2s :: "('v \<times> 'v :: cinf) list"
    assume x1x2s:"x1x2s = (a,b) # y1y2s"
    show "\<exists>x1x2s'.
     length x1x2s' = length ((a,b) # y1y2s) \<and>
     compose x1x2s' = compose ((a,b) # y1y2s) \<and> hd x1x2s' = (x1, x2)
     \<and> (\<forall> a b. (a,b) \<in> set (tl x1x2s') \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b)"
      apply (cases y1y2s)
      subgoal proof(intro exI[of _ "[(x1,x2)]"])
        assume empty:"y1y2s = []"
        show "length [(x1, x2)] = length ((a, b) # y1y2s) \<and>
          compose [(x1, x2)] = compose ((a, b) # y1y2s) \<and>
          hd [(x1, x2)] = (x1, x2) \<and> (\<forall>a b. (a, b) \<in> set (tl [(x1, x2)]) \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b)"
          using comp inset unfolding x1x2s empty compose.simps by force
      qed
      subgoal for aa list proof(cases "\<forall>a b. (a, b) \<in> set (y1y2s) \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b")
        assume ny:"y1y2s = aa # list"
          and casen:"\<forall>a b. (a, b) \<in> set y1y2s \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b"
        have fromcasen:"compose y1y2s x2 = x2"
          using compose_support0 casen by force
        have fromcasen2:"compose [(a,b)] x2 = x1"
          unfolding comp[symmetric] x1x2s compose.simps o_apply fromcasen by simp
        have seteq:"x1 \<noteq> x2 \<Longrightarrow> {a,b}={x1,x2}"
          using fromcasen2 unfolding compose.simps
          using casen doubleton_eq_iff inset x1x2s by fastforce
        have eqeq:"x1 = x2 \<Longrightarrow> a = b" using fromcasen2 unfolding compose.simps
          by (metis Pair_inject casen compose_pair_fix fromcasen2 inset set_ConsD x1x2s)
        show ?thesis apply(rule exI[of _ "(x1,x2) # y1y2s"], simp add: casen, cases "x1 = x2")
          subgoal using eqeq by simp
          subgoal using seteq compose_hd_sym fromcasen2 by auto
          done
      next
        assume ny:"y1y2s = aa # list"
          and casey:" \<not> (\<forall>a b. (a, b) \<in> set y1y2s \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b)"
        have expair:"\<exists> a b. (a, b) \<in> set y1y2s \<and> (x2 = a \<or> x2 = b)" using casey by blast
        obtain z1z2s :: "('v \<times> 'v :: cinf) list" where z1z2s:"length z1z2s = length y1y2s"
          "compose z1z2s = compose y1y2s" "hd z1z2s = (compose y1y2s x2, x2)"
          "\<forall>a b. (a, b) \<in> set (tl z1z2s) \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b"
          using ih[rule_format, of y1y2s x2, OF _ _ expair] using ny x1x2s by auto
        have step:"compose ((a, b) # y1y2s) = compose ((a,b)#(compose y1y2s x2, x2)# tl z1z2s)"
          unfolding compose.simps(2)[of a b] z1z2s(2)[symmetric] using z1z2s(3)
          by (metis length_0_conv list.exhaust_sel list.simps(3) ny z1z2s(1) z1z2s(2))
        have step0:"compose ((a, b) # y1y2s) x2  = compose [(a,b),(compose y1y2s x2, x2)] x2"
          unfolding step unfolding compose.simps
          using z1z2s(4) compose_support0 by fastforce
        have step1:"compose [(a,b),(compose y1y2s x2, x2)] x2 = x1"
          using step0 comp x1x2s by auto
        obtain a0 b0 where final:
          "compose [(a,b),(compose y1y2s x2, x2)] = compose [(x1,x2),(a0,b0)]" "x2 \<notin> {a0,b0}"
          using compose_pair_push_left[OF step1] by blast
        show ?thesis
          apply(rule exI[of _ "(x1,x2) # (a0,b0) # tl z1z2s"], safe)
          subgoal by (simp add: ny z1z2s(1))
          subgoal using final unfolding step unfolding compose.simps by (simp add: o_assoc)
          subgoal by simp
          subgoal using final z1z2s(4) by auto
          subgoal using final z1z2s(4) by auto
          done
      qed
      done
  qed
qed

lemma compose_push_left_last: assumes notem:"x1x2s \<noteq> []"
  and last:"last x1x2s = (x0,x2)"
  and image:"compose x1x2s x2 = x1"
shows "\<exists> x1x2s'. length x1x2s' = length x1x2s
  \<and> compose x1x2s' = compose x1x2s \<and> hd x1x2s' = (x1,x2)
  \<and> (\<forall> p. p \<in> set (tl x1x2s') \<longrightarrow> x2 \<noteq> fst p \<and> x2 \<noteq> snd p)"
  apply(intro compose_push_left[OF notem _ image])
  using last last_in_set notem by fastforce

lemma act_compose_pair_push_left: assumes comp:"compose [(a,b),(y, x2)] x2 = x1"
  and swp:"nswapping swp"
  shows "\<exists> a0 b0. compose [(a,b),(y, x2)] = compose [(x1,x2),(a0,b0)] \<and>
          act swp [(a,b),(y, x2)] = act swp [(x1,x2),(a0,b0)] \<and> x2 \<notin> {a0,b0}"
proof(cases "y = x1")
  case True
  show ?thesis unfolding True
  proof(cases "a = b")
    assume ab:"a = b"
    obtain xx where xx:"xx \<noteq> x1" "xx \<noteq> x2"
       using exists_fresh[of "{x1,x2}"] by blast
     show "\<exists> a0 b0. compose [(a, b), (x1, x2)] = compose [(x1, x2), (a0, b0)] \<and>
            act swp [(a,b),(x1, x2)] = act swp [(x1,x2),(a0,b0)] \<and> x2 \<notin> {a0,b0}"
       unfolding ab act.simps compose.simps apply(rule exI[of _ xx], rule exI[of _ xx],
           safe, simp_all add: xx[symmetric])
       unfolding swp[unfolded nswapping_def, THEN conjunct1, rule_format] using xx by fast
  next
    assume ab:"a \<noteq> b"
    have  abfix:"compose [(a,b)] x1 = x1"
        using assms unfolding True compose.simps by simp
    have ab_x1:"a \<noteq> x1" "b \<noteq> x1"
        by(auto simp add: compose_pair_fix[OF abfix ab])
      show "\<exists> a0 b0. compose [(a, b), (x1, x2)] = compose [(x1, x2), (a0, b0)] \<and>
            act swp [(a,b),(x1, x2)] = act swp [(x1,x2),(a0,b0)] \<and> x2 \<notin> {a0,b0}"
      apply (cases "a = x2")
      subgoal apply(rule exI[of _ x1], rule exI[of _ b])
        unfolding act.simps compose.simps
        swp[unfolded nswapping_def, THEN conjunct2, THEN conjunct2, rule_format, of _ x1 b]
        using ab ab_x1 by force
      subgoal apply(cases "b = x2")
        subgoal apply(rule exI[of _ x1], rule exI[of _ a])
          unfolding act.simps compose.simps
          swp[unfolded nswapping_def, THEN conjunct2, THEN conjunct2, rule_format, of _ x1 a]
          using ab ab_x1 apply safe subgoal by (simp add: fun_upd_comp fun_upd_twist)
          subgoal by (simp add: nswapping_sym1[OF swp]) done
        subgoal apply(rule exI[of _ a], rule exI[of _ b])
          using ab_x1 apply simp
          using  act_disj_supp_commutes[OF swp, of a b x1 x2 "[]"] by force
        done
      done
  qed
next
  case False
  have step2:"compose [(a,b)] y = x1"
      using assms by simp
  have ab:"{x1,y}={a,b}"
      using compose_support[OF False[symmetric, unfolded step2[symmetric]]]
        compose_support_im[OF False[symmetric, unfolded step2[symmetric]]]
      unfolding step2 using False by auto
  show ?thesis
  proof (cases "y = x2")
    assume comx2:"y = x2"
    obtain x0 where x0:"x0 \<notin> {x1,x2}"
        using exists_fresh by (meson finite.emptyI finite.insertI)
      show ?thesis unfolding comx2 apply(rule exI[of _ x0], rule exI[of _ x0], simp, safe)
      subgoal using ab unfolding comx2 by fastforce
      subgoal using ab unfolding comx2 act.simps
        unfolding swp[unfolded nswapping_def, THEN conjunct1, rule_format]
        by (metis doubleton_eq_iff nswapping_sym1 swp)
      subgoal using x0 by blast done
  next
    assume comx2:"y \<noteq> x2"
    show ?thesis
      apply(cases "x1 = x2")
        subgoal apply(rule exI[of _ "y"],
            rule exI[of _ "y"], simp_all add: comx2[symmetric])
          using ab comx2 unfolding act.simps
          unfolding swp[unfolded nswapping_def, THEN conjunct1, rule_format]
          apply(cases "x2=a", simp) using doubleton_eq_iff
          subgoal apply safe subgoal by (simp add: doubleton_eq_iff fun_upd_twist id_swapTwice)
            subgoal using nswapping_sym0[OF swp, of _ y x2] by auto done
          subgoal apply safe subgoal by (simp add: doubleton_eq_iff id_swapTwice) subgoal
            using
              swp[unfolded nswapping_def, THEN conjunct2, THEN conjunct1, rule_format, of _ y x2]
            by auto done
          done
        subgoal apply(rule exI[of _ x1], rule exI[of _ "y"],
            simp_all add: comx2[symmetric]) proof(cases "a = x1")
          assume neq:"x1 \<noteq> x2" and ttr:"a = x1"
          have byy:"b = y" using ab ttr doubleton_eq_iff by fastforce
          show "id(a := b, b := a) \<circ> id(y := x2, x2 := y)
              = id(x1 := x2, x2 := x1) \<circ> id(x1 := y, y := x1)
              \<and>
              act swp [(a, b), (y, x2)] = act swp [(x1, x2), (x1, y)]"
            apply safe
            subgoal unfolding ttr byy using comx2 neq by auto
            subgoal unfolding ttr byy act.simps
            swp[unfolded nswapping_def, THEN conjunct2, THEN conjunct2, rule_format, of _ y x2]
            unfolding sw_eqR sw_diff[OF neq[symmetric] comx2[symmetric]] by simp done
        next
          assume neq:"x1 \<noteq> x2" and fls:"a \<noteq> x1"
          have bx1:"b = x1" and ay:"a = y" using ab fls doubleton_eq_iff[of x1 y a b] by auto
          show "id(a := b, b := a) \<circ> id(y := x2, x2 := y)
              = id(x1 := x2, x2 := x1) \<circ> id(x1 := y, y := x1)
              \<and>
              act swp [(a, b), (y, x2)] = act swp [(x1, x2), (x1, y)]"
            apply safe
            subgoal unfolding bx1 ay using comx2 neq by auto
            subgoal unfolding bx1 ay act.simps
            swp[unfolded nswapping_def, THEN conjunct2, THEN conjunct2, rule_format, of _ y x2]
            unfolding sw_eqL sw_diff[OF comx2[symmetric] neq[symmetric]]
            nswapping_sym1[OF swp, of _ y] by simp done
        qed
        done
  qed
qed

lemma act_compose_push_left:
  fixes x1x2s :: "('v \<times> 'v :: cinf) list"
  assumes notem:"x1x2s \<noteq> []"
  and swp:"nswapping swp"
  and inset:"\<exists> p. p \<in> set x1x2s \<and> (x2 = fst p \<or> x2 = snd p)"
  and image:"compose x1x2s x2 = x1"
shows "\<exists> x1x2s'. length x1x2s' = length x1x2s
  \<and> act swp x1x2s' = act swp x1x2s
  \<and> compose x1x2s' = compose x1x2s
  \<and> hd x1x2s' = (x1,x2)
  \<and> (\<forall> p. p \<in> set (tl x1x2s') \<longrightarrow> x2 \<noteq> fst p \<and> x2 \<noteq> snd p)"
  using notem inset image
proof(induct x1x2s arbitrary: x1 x2 rule: length_induct, simp)
  fix x1x2s :: "('v \<times> 'v :: cinf) list" and x1 x2
  assume ih: "\<forall>ys :: ('v \<times> 'v :: cinf) list. length ys < length x1x2s \<longrightarrow>
            ys \<noteq> [] \<longrightarrow>
            (\<forall>x. (\<exists>a b. (a, b) \<in> set ys \<and> (x = a \<or> x = b)) \<longrightarrow>
                 (\<exists>x1x2s'.
                     length x1x2s' = length ys \<and>
                     act swp x1x2s' = act swp ys \<and>
                     compose x1x2s' = compose ys \<and>
                     hd x1x2s' = (compose ys x, x) \<and>
                     (\<forall>a b. (a, b) \<in> set (tl x1x2s') \<longrightarrow> x \<noteq> a \<and> x \<noteq> b)))"
    and neq:"x1x2s \<noteq> []"
    and inset:"\<exists> a b. (a,b) \<in> set x1x2s \<and> (x2 = a \<or> x2 = b)"
    and comp:"compose x1x2s x2 = x1"
  show "\<exists>x1x2s'.
          length x1x2s' = length x1x2s \<and>
          act swp x1x2s' = act swp x1x2s \<and> compose x1x2s' = compose x1x2s \<and>
          hd x1x2s' = (x1, x2) \<and> (\<forall>a b. (a, b) \<in> set (tl x1x2s') \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b)"
    apply(cases x1x2s, simp add:neq)
  proof safe
    fix a b y1y2s
    assume x1x2s:"x1x2s = (a,b) # y1y2s"
    show "\<exists>x1x2s'.
     length x1x2s' = length ((a,b) # y1y2s) \<and>
     act swp x1x2s' = act swp ((a,b) # y1y2s)  \<and> compose x1x2s' = compose ((a, b) # y1y2s)
     \<and> hd x1x2s' = (x1, x2)
     \<and> (\<forall> a b. (a,b) \<in> set (tl x1x2s') \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b)"
      apply (cases y1y2s)
      subgoal proof(intro exI[of _ "[(x1,x2)]"])
        assume empty:"y1y2s = []"
        have eqset:"{a,b} = {x1,x2}" using comp inset
          unfolding x1x2s empty compose.simps by force
        show "length [(x1, x2)] = length ((a, b) # y1y2s) \<and>
          act swp [(x1, x2)] = act swp ((a, b) # y1y2s) \<and>
          compose [(x1, x2)] = compose ((a, b) # y1y2s) \<and>
          hd [(x1, x2)] = (x1, x2) \<and> (\<forall>a b. (a, b) \<in> set (tl [(x1, x2)]) \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b)"
          using eqset unfolding empty act.simps apply (simp, safe)
          subgoal by (metis doubleton_eq_iff nswapping_sym1 swp)
          subgoal by (metis doubleton_eq_iff fun_upd_twist) done
      qed
      subgoal for aa list proof(cases "\<forall>a b. (a, b) \<in> set (y1y2s) \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b")
        assume ny:"y1y2s = aa # list"
          and casen:"\<forall>a b. (a, b) \<in> set y1y2s \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b"
        have fromcasen:"compose y1y2s x2 = x2"
          using compose_support0 casen by force
        have fromcasen2:"compose [(a,b)] x2 = x1"
          unfolding comp[symmetric] x1x2s compose.simps o_apply fromcasen by simp
        have seteq:"x1 \<noteq> x2 \<Longrightarrow> {a,b}={x1,x2}"
          using fromcasen2 unfolding compose.simps
          using casen doubleton_eq_iff inset x1x2s by fastforce
        have eqeq:"x1 = x2 \<Longrightarrow> a = b" using fromcasen2 unfolding compose.simps
          by (metis Pair_inject casen compose_pair_fix fromcasen2 inset set_ConsD x1x2s)
        show ?thesis apply(rule exI[of _ "(x1,x2) # y1y2s"], simp add: casen, cases "x1 = x2")
          subgoal using eqeq
            apply simp unfolding act.simps
              unfolding swp[unfolded nswapping_def, THEN conjunct1, rule_format] by simp
            (*using casen inset x1x2s by auto*)
          subgoal using seteq act_hd_sym[OF swp] fromcasen2 by fastforce
          done
      next
        assume ny:"y1y2s = aa # list"
          and casey:" \<not> (\<forall>a b. (a, b) \<in> set y1y2s \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b)"
        have expair:"\<exists> a b. (a, b) \<in> set y1y2s \<and> (x2 = a \<or> x2 = b)" using casey by blast
        obtain z1z2s where z1z2s:"length z1z2s = length y1y2s"
          "compose z1z2s = compose y1y2s"
          "act swp z1z2s = act swp y1y2s" "hd z1z2s = (compose y1y2s x2, x2)"
          "\<forall>a b. (a, b) \<in> set (tl z1z2s) \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b"
          using ih[rule_format, of y1y2s x2, OF _ _ expair] using ny x1x2s by auto
        have step:"compose ((a, b) # y1y2s) = compose ((a,b)#(compose y1y2s x2, x2)# tl z1z2s)"
          unfolding compose.simps(2)[of a b] z1z2s(2)[symmetric] using z1z2s(4)
          by (metis length_0_conv list.exhaust_sel list.simps(3) ny z1z2s(1) z1z2s(2))
        have step_act:"act swp ((a, b) # y1y2s) = act swp ((a,b)#(compose y1y2s x2, x2)# tl z1z2s)"
          unfolding act.simps(2)[of swp a b] z1z2s(3)[symmetric] using z1z2s(4)
          by (metis length_0_conv list.exhaust_sel list.simps(3) ny z1z2s(1) z1z2s(3))
        have step0:"compose ((a, b) # y1y2s) x2  = compose [(a,b),(compose y1y2s x2, x2)] x2"
          unfolding step unfolding compose.simps
          using z1z2s(5) compose_support0 by fastforce
        have step1:"compose [(a,b),(compose y1y2s x2, x2)] x2 = x1"
          using step0 comp x1x2s by auto
        obtain a0 b0 where final:
          "compose [(a,b),(compose y1y2s x2, x2)] = compose [(x1,x2),(a0,b0)]"
          "act swp [(a,b),(compose y1y2s x2, x2)] = act swp [(x1,x2),(a0,b0)]"
          "x2 \<notin> {a0,b0}"
          using act_compose_pair_push_left[OF step1 swp] by blast
        show ?thesis
          apply(rule exI[of _ "(x1,x2) # (a0,b0) # tl z1z2s"], safe)
          subgoal by (simp add: ny z1z2s(1))
          subgoal using final(2) unfolding step_act unfolding act.simps by metis
          subgoal using final unfolding step unfolding compose.simps by (simp add: o_assoc)
          subgoal by simp
          subgoal using final z1z2s(5) by auto
          subgoal using final z1z2s(5) by auto
          done
      qed
      done
  qed
qed

(* Every finite permutation is the composition of a list of permutations: *)
lemma fsupp_ex_compose:
assumes "fsupp \<sigma>" "bij \<sigma>"
shows "\<exists> z1z2s :: ('v \<times> 'v :: cinf) list. \<sigma> = compose z1z2s"
  using assms
proof(induct "card {x. \<sigma> x \<noteq> x}" arbitrary: \<sigma> rule: less_induct)
  fix \<sigma> :: "'v \<Rightarrow> 'v"
  assume ih:"\<And>\<sigma>' :: 'v \<Rightarrow> 'v. card {x. \<sigma>' x \<noteq> x} < card {x. \<sigma> x \<noteq> x} \<Longrightarrow>
                fsupp \<sigma>' \<Longrightarrow> bij \<sigma>' \<Longrightarrow> \<exists>z1z2s. \<sigma>' = compose z1z2s"
    and fsupp:"fsupp \<sigma>" and bij:"bij \<sigma>"
  show "\<exists>z1z2s. \<sigma> = compose z1z2s" apply (cases "card {x. \<sigma> x \<noteq> x}")
    subgoal apply(rule exI[of _ "[]"], simp add: fsupp[unfolded fsupp_def]) by fastforce
    subgoal for n proof-
      assume succ:"card {x. \<sigma> x \<noteq> x} = Suc n"
      obtain x1 x2 where x1x2:"\<sigma> x2 = x1" "x1 \<noteq> x2"
        using succ by fastforce
      have supp':"{x. (compose [(x1,x2)] o \<sigma>) x \<noteq> x} \<subseteq> {x. \<sigma> x \<noteq> x}-{x2}"
        apply safe
        subgoal for x unfolding o_apply
          by (metis bij bij_is_inj compose_support injD
              list.set(1) list.simps(15) prod.sel(1) prod.sel(2) singletonD x1x2(1) x1x2(2))
        subgoal unfolding o_apply x1x2 compose.simps using x1x2(2) by simp
        done
      obtain z1z2s' where z1z2s':"compose z1z2s' = compose [(x1,x2)] o \<sigma>"
        using ih[of "compose [(x1,x2)] o \<sigma>"] supp'
        by (smt bij bij_o card_Diff1_less card_eq_0_iff compose.simps(1)
            compose.simps(2) bij_compose finite_Diff fsupp fsupp_id fsupp_o
            fsupp_upd less_le less_trans
            mem_Collect_eq psubset_card_mono succ x1x2(1) x1x2(2) zero_less_Suc)
      show "\<exists>z1z2s. \<sigma> = compose z1z2s"
        by(rule exI[of _ "(x1,x2) # z1z2s'"], auto simp add: z1z2s')
    qed
    done
qed

(* Need a sharper version, that guarantees nonredundancy: *)

lemma fsupp_ex_compose_strong:
assumes "fsupp \<sigma>" "bij \<sigma>"
shows "\<exists> z1z2s. \<sigma> = compose z1z2s \<and> {x. \<sigma> x \<noteq> x} = fst ` (set z1z2s) \<union> snd ` (set z1z2s)"
using assms proof(induct "card {x. \<sigma> x \<noteq> x}" arbitrary: \<sigma> rule: less_induct)
  case less note ih = less(1) and fsupp = less(2) and bij = less(3)
  show ?case proof (cases "card {x. \<sigma> x \<noteq> x}")
    case 0 thus ?thesis
    apply - apply(rule exI[of _ "[]"], simp add: fsupp[unfolded fsupp_def]) by fastforce
  next
    case (Suc n)
    then obtain x1 x2 where x1x2: "\<sigma> x2 = x1" "x1 \<noteq> x2" by fastforce
    have supp': "{x. (compose [(x1,x2)] o \<sigma>) x \<noteq> x} \<subseteq> {x. \<sigma> x \<noteq> x} - {x2}"
    apply safe
      subgoal for x unfolding o_apply
      by (metis bij bij_is_inj compose_support injD
           list.set(1) list.simps(15) prod.sel(1) prod.sel(2) singletonD x1x2(1) x1x2(2))
      subgoal unfolding o_apply x1x2 compose.simps using x1x2(2) by simp .
      obtain z1z2s' where z1z2s':"compose z1z2s' = compose [(x1,x2)] o \<sigma>"
      and 0: "{x. (compose [(x1, x2)] \<circ> \<sigma>) x \<noteq> x} = fst ` set z1z2s' \<union> snd ` set z1z2s'"
        using ih[of "compose [(x1,x2)] o \<sigma>"] supp'
        by (smt bij bij_o card_Diff1_less card_eq_0_iff compose.simps(1)
            compose.simps(2) bij_compose finite_Diff fsupp fsupp_id fsupp_o
            fsupp_upd less_le less_trans
            mem_Collect_eq psubset_card_mono Suc x1x2(1) x1x2(2) zero_less_Suc)
    show ?thesis
        apply(rule exI[of _ "(x1,x2) # z1z2s'"], auto simp add: z1z2s')
        apply (smt (z3) "0" UnE compose_support_im list.set(1) list.set(2) mem_Collect_eq o_apply
          prod.sel(1) prod.sel(2) singletonD)
         apply (auto simp add: x1x2)
        apply (metis bij bij_is_inj injD x1x2(1) x1x2(2))
       using "0" insert_absorb supp' by auto
  qed
qed

lemma auxx: "x12 # z1z2s' = h1 @ h2 \<Longrightarrow> (h1 = [] \<and> h2 = x12 # z1z2s') \<or> (\<exists>h1'. h1 = x12 # h1' \<and> z1z2s' = h1' @ h2)"
by (metis Cons_eq_append_conv)

(* *)
definition nonredundant where
"nonredundant z1z2s \<equiv>
 (\<forall> h1 h2. z1z2s = h1 @ h2 \<longrightarrow> {x. compose h2 x \<noteq> x} = fst ` (set h2) \<union> snd ` (set h2))"

lemma nonredundant_append:
"nonredundant (h1 @ h2) \<Longrightarrow> nonredundant h2"
unfolding nonredundant_def by simp

lemma nonredundant_Cons:
"nonredundant (z1z2 # h) \<Longrightarrow> nonredundant h"
unfolding nonredundant_def by simp

lemma nonredundant_compose:
"nonredundant h \<Longrightarrow> {x. compose h x \<noteq> x} = fst ` (set h) \<union> snd ` (set h)"
unfolding nonredundant_def by simp

(* *)

lemma fsupp_ex_compose_even_stronger:
assumes "fsupp \<sigma>" "bij \<sigma>"
shows "\<exists> z1z2s. \<sigma> = compose z1z2s \<and> nonredundant z1z2s"
using assms proof(induct "card {x. \<sigma> x \<noteq> x}" arbitrary: \<sigma> rule: less_induct)
  case less note ih = less(1) and fsupp = less(2) and bij = less(3)
  show ?case proof (cases "card {x. \<sigma> x \<noteq> x}")
    case 0 thus ?thesis
    by (intro exI[of _ "[]"], fastforce simp add: fsupp[unfolded fsupp_def] nonredundant_def)
  next
    case (Suc n)
    then obtain x1 x2 where x1x2: "\<sigma> x2 = x1" "x1 \<noteq> x2" by fastforce
    have supp': "{x. (compose [(x1,x2)] o \<sigma>) x \<noteq> x} \<subseteq> {x. \<sigma> x \<noteq> x} - {x2}"
    apply safe
      subgoal for x unfolding o_apply
      by (metis bij bij_is_inj compose_support injD
           list.set(1) list.simps(15) prod.sel(1) prod.sel(2) singletonD x1x2(1) x1x2(2))
      subgoal unfolding o_apply x1x2 compose.simps using x1x2(2) by simp .
      obtain z1z2s' where z1z2s':"compose z1z2s' = compose [(x1,x2)] o \<sigma>"
      and 0: "compose [(x1, x2)] \<circ> \<sigma> = compose z1z2s' \<and> nonredundant z1z2s'"
        using ih[of "compose [(x1,x2)] o \<sigma>"] supp'
        by (smt (verit, ccfv_threshold) Diff_empty Suc bij bij_compose bij_o card.infinite
           card_Diff1_less card_mono compose.simps(1) compose.simps(2) finite_Diff_insert
           fsupp fsupp_id fsupp_o fsupp_upd linorder_not_le mem_Collect_eq nat.simps(3)
           order_less_le_trans x1x2(1) x1x2(2))
    show ?thesis unfolding nonredundant_def
    apply(rule exI[of _ "(x1,x2) # z1z2s'"], auto simp add: z1z2s')
      subgoal using compose_support by blast
      subgoal for h1 h2 x y  apply(drule auxx) apply (cases h1)
        subgoal apply simp apply(cases "compose z1z2s' x = x2")
          subgoal by (metis (mono_tags, lifting) "0" comp_def comp_eq_id_dest compose.simps(1)
          compose.simps(2) compose_diff_implies_diff_im fun_upd_same id_swapTwice x1x2)
          subgoal apply(cases "compose z1z2s' x = x2")
            subgoal by simp
            subgoal apply(cases "compose z1z2s' x = x1")
              subgoal apply simp by (metis comp_apply compose_pair_fix x1x2(1) z1z2s')
              subgoal apply simp using "0" Un_iff append_Nil imageI mem_Collect_eq prod.sel(1)
              unfolding nonredundant_def by (metis (mono_tags, lifting)) . . .
        subgoal apply simp
          by (metis (mono_tags, lifting) "0" nonredundant_def Un_iff fst_eqD imageI mem_Collect_eq) .
      subgoal for h1 h2 x y  apply(drule auxx) apply (cases h1)
        subgoal apply simp apply(cases "compose z1z2s' y = x2")
          subgoal by (metis (mono_tags, lifting) "0" comp_def comp_eq_id_dest compose.simps(1)
          compose.simps(2) compose_diff_implies_diff_im fun_upd_same id_swapTwice x1x2)
          subgoal apply(cases "compose z1z2s' y = x2")
            subgoal by simp
            subgoal apply(cases "compose z1z2s' y = x1")
              subgoal apply simp by (metis comp_apply compose_pair_fix x1x2(1) z1z2s')
              subgoal apply simp using "0" nonredundant_def Un_iff append_Nil imageI mem_Collect_eq prod.sel(2)
               by (metis (mono_tags, lifting)) . . .
        subgoal apply simp
        	by (metis (mono_tags, lifting) "0" nonredundant_def  UnCI image_eqI mem_Collect_eq prod.sel(2)) . .
  qed
qed

(* decomposition as transpositions: *)
definition asTrans :: "('v :: cinf \<Rightarrow> 'v) \<Rightarrow> ('v \<times> 'v) list" where
"asTrans \<sigma> \<equiv> SOME z1z2s. \<sigma> = compose z1z2s"

lemma compose_asTrans: "fsupp \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> compose (asTrans \<sigma>) = \<sigma>"
  unfolding asTrans_def
  by (erule (1) someI2_ex[OF fsupp_ex_compose]) simp


(* For swapping algebras, compose uniquely determines the action *)
lemma compose_act_unique:
fixes z1z2s :: "('v \<times> 'v :: cinf) list"
assumes swp:"nswapping swp"
and compeq:"compose z1z2s = compose z1z2s'"
shows "act swp z1z2s = act swp z1z2s'"
  using compeq
proof(induct "length z1z2s + length z1z2s'"  arbitrary: z1z2s z1z2s' rule: less_induct)
  fix z1z2s z1z2s' :: "('v \<times> 'v :: cinf) list"
  assume ih:"\<And> x1x2s x1x2s' :: ('v \<times> 'v :: cinf) list.
           length x1x2s + length x1x2s' < length z1z2s + length z1z2s' \<Longrightarrow>
           compose x1x2s = compose x1x2s' \<Longrightarrow> act swp x1x2s = act swp x1x2s'"
    and comp:"compose z1z2s = compose z1z2s'"
  show "act swp z1z2s = act swp z1z2s'"
  proof(cases "compose z1z2s = id")
    case True
    have True':"compose z1z2s' = id" using comp True by argo
    show ?thesis
    proof(cases "z1z2s = []")
      assume em:"z1z2s = []"
      show "act swp z1z2s = act swp z1z2s'"
        apply(cases "z1z2s' = []", simp add: em)
      proof-
        assume notem:"z1z2s' \<noteq> []"
        obtain a b x1x2s' where abtl:"z1z2s' = (a,b) # x1x2s'" using notem compose.cases by blast
        have step_comp:"compose [(a,b)] = compose x1x2s'" using comp unfolding em abtl
          unfolding compose.simps  by (metis id_comp id_swapTwice o_assoc)
        show "act swp z1z2s = act swp z1z2s'"
          apply(cases "a = b")
          subgoal unfolding em abtl apply simp unfolding act.simps(2)
            swp[unfolded nswapping_def, THEN conjunct1, rule_format, of _ b ]
            apply(intro ih) unfolding abtl em step_comp[symmetric] by simp_all
          subgoal proof-
            assume anb:"a \<noteq> b"
            have triv:"x1x2s' \<noteq> []" using step_comp anb unfolding compose.simps
              using compose.simps(1) by (metis comp_id fun_upd_eqD fun_upd_id_same)
            have triv2:"compose x1x2s' b = a" unfolding step_comp[symmetric]
              unfolding compose.simps by simp
            have triv3:"\<exists>p. p \<in> set x1x2s' \<and> (b = fst p \<or> b = snd p)"
              using anb compose_support triv2 by blast
            obtain y1y2s' where y1y2s':
              "length x1x2s' = length ((a,b) # y1y2s')"
              "compose x1x2s' = compose ((a,b) # y1y2s')"
              "act swp x1x2s' = act swp ((a,b) # y1y2s')"
              using act_compose_push_left[OF triv swp triv3 triv2]
              by (metis length_0_conv list.exhaust_sel triv)
            have last:"compose [] = compose y1y2s'"
              using step_comp unfolding y1y2s'
              unfolding compose.simps
              by (metis True' abtl comp_assoc comp_id compose.simps(2) fun.map_id y1y2s'(2))
            show "act swp z1z2s = act swp z1z2s'"
              unfolding abtl em act.simps(2) y1y2s' unfolding
              swp[unfolded nswapping_def, THEN conjunct2, THEN conjunct1, rule_format, of _ a b]
              apply(rule ih[OF _ last]) unfolding em abtl using y1y2s'(1) by simp
          qed
          done
      qed
    next
      assume notem:"z1z2s \<noteq> []"
      obtain a b x1x2s where abtl:"z1z2s = (a,b) # x1x2s" using notem compose.cases by blast
      have step_comp:"compose [(a,b)] = compose x1x2s" using True unfolding abtl
        compose.simps by (metis comp_assoc id_comp id_swapTwice)
      show "act swp z1z2s = act swp z1z2s'"
        apply(cases "a = b")
        subgoal unfolding abtl apply simp unfolding act.simps(2)
            swp[unfolded nswapping_def, THEN conjunct1, rule_format, of _ b ]
          apply(intro ih) unfolding abtl step_comp[symmetric]
          by (simp_all add:True comp[symmetric])
        subgoal proof-
          assume anb:"a \<noteq> b"
          have triv:"x1x2s \<noteq> []" using step_comp anb unfolding compose.simps
            using compose.simps(1) by (metis comp_id fun_upd_eqD fun_upd_id_same)
          have triv2:"compose x1x2s b = a" unfolding step_comp[symmetric]
            unfolding compose.simps by simp
          have triv3:"\<exists>p. p \<in> set x1x2s \<and> (b = fst p \<or> b = snd p)"
            using anb compose_support triv2 by blast
          obtain y1y2s where y1y2s:
            "length x1x2s = length ((a,b) # y1y2s)"
            "compose x1x2s = compose ((a,b) # y1y2s)"
            "act swp x1x2s = act swp ((a,b) # y1y2s)"
            using act_compose_push_left[OF triv swp triv3 triv2]
          by (metis length_0_conv list.exhaust_sel triv)
          have last:"compose [] = compose y1y2s"
            using step_comp unfolding y1y2s
            unfolding compose.simps
            by (metis True abtl comp_assoc comp_id compose.simps(2) fun.map_id y1y2s(2))
          show "act swp z1z2s = act swp z1z2s'"
            unfolding abtl act.simps(2) y1y2s
              swp[unfolded nswapping_def, THEN conjunct2, THEN conjunct1, rule_format, of _ a b]
            apply(rule ih) unfolding abtl using y1y2s(1) apply simp using True comp last by force
        qed
        done
    qed
  next
    case False
    have nem:"z1z2s \<noteq> []" using False compose.simps(1) by blast
    have nem':"z1z2s' \<noteq> []" using False unfolding comp using compose.simps(1) by blast
    obtain x1 x2 where x1x2:"compose z1z2s x2 = x1""x1 \<noteq> x2"
      using False by fastforce
    have hp:"\<exists> p. p \<in> set z1z2s \<and> (x2 = fst p \<or> x2 = snd p)"
      using x1x2 compose_support by blast
    have x1x2':"compose z1z2s' x2 = x1"
      using x1x2 unfolding comp by simp
    have hp':"\<exists> p. p \<in> set z1z2s' \<and> (x2 = fst p \<or> x2 = snd p)"
      using x1x2' x1x2(2) compose_support by blast
    obtain x1x2s where x1x2s:"length ((x1,x2) # x1x2s) = length z1z2s"
      "act swp ((x1,x2) # x1x2s) = act swp z1z2s"
      "compose ((x1,x2) # x1x2s) = compose z1z2s"
      using act_compose_push_left[OF nem swp hp x1x2(1)]
      by (metis length_0_conv list.exhaust_sel nem)
    obtain x1x2s' where x1x2s':"length ((x1,x2) # x1x2s') = length z1z2s'"
      "act swp ((x1,x2) # x1x2s') = act swp z1z2s'"
      "compose ((x1,x2) # x1x2s') = compose z1z2s'"
      using act_compose_push_left[OF nem' swp hp' x1x2']
      by (metis length_0_conv list.exhaust_sel nem')
    have fromih:"act swp x1x2s = act swp x1x2s'"
      apply(intro ih) using x1x2s x1x2s' apply simp
      by (metis comp comp_assoc compose.simps(2) fun.map_id id_swapTwice x1x2s'(3) x1x2s(3))
    show ?thesis
      unfolding x1x2s(2)[symmetric] x1x2s'(2)[symmetric] act.simps
      using fromih by simp
  qed
qed

lemma compose_act_unique2:
assumes "nswapping swp"
and "compose z1z2s = compose z1z2s'"
shows "act swp z1z2s c = act swp z1z2s' c"
using compose_act_unique[OF assms] by auto

definition toPerm :: "('c \<Rightarrow> 'v :: cinf \<Rightarrow> 'v \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> 'c)" where
"toPerm swp c \<sigma> \<equiv> act swp (asTrans \<sigma>) c"

theorem permut_toPerm:
fixes swp :: "'c \<Rightarrow> 'v :: cinf \<Rightarrow> 'v \<Rightarrow> 'c"
assumes "nswapping swp"
shows "permut (toPerm swp)"
unfolding permut_def proof safe
  fix c
  have 0: "act swp (asTrans id) = act swp []"
  using assms by (intro compose_act_unique) (auto simp: compose_asTrans)
  show "toPerm swp c id = c" unfolding toPerm_def 0 by simp
next
  fix c and \<sigma> \<tau> :: "'v \<Rightarrow> 'v" assume 0: "bij \<sigma>" "fsupp \<sigma>" "bij \<tau>" "fsupp \<tau>"
  have 1: "act swp (asTrans \<tau> @ asTrans \<sigma>) = act swp (asTrans (\<tau> \<circ> \<sigma>))"
  using assms
  by (intro compose_act_unique) (auto simp: 0 fun_eq_iff compose_append compose_asTrans fsupp_o bij_o)
  show "toPerm swp (toPerm swp c \<sigma>) \<tau> = toPerm swp c (\<tau> \<circ> \<sigma>)"
  unfolding toPerm_def unfolding act_append[symmetric] 1 ..
qed


lemma fsupp_compose[simp,intro!]: "fsupp (compose z1z2s)"
proof(induct z1z2s rule: list_induct_Pair)
  case Nil
  then show ?case by (auto simp add: fsupp_def)
next
  case (Cons z1 z2 z1z2s)
  have "{x. compose ((z1, z2) # z1z2s) x \<noteq> x} \<subseteq>
        {x. compose z1z2s x \<noteq> x} \<union> {z1,z2}" by auto
  with Cons show ?case unfolding fsupp_def
  	by (meson finite.emptyI finite.insertI finite_UnI finite_subset)
qed

(* End results: *)
thm fsupp_compose bij_compose
thm permut_toPerm
thm nswapping_toSwp


(* Some properties of swapping and permutation on terms: *)

(* *)
lemma toPerm_toSwp_compose:
assumes 1: "permut prm"
shows "toPerm (toSwp prm) a (compose z1z2s) = prm a (compose z1z2s)"
proof(induct z1z2s arbitrary: a rule: list_induct_Pair)
  case Nil
  then show ?case
  by simp (metis assms comp_id fun.map_ident nswapping_toSwp permut_def permut_toPerm)
next
  case (Cons z1 z2 z1z2s)
  then show ?case
  	by (smt (verit, ccfv_threshold) act.simps(2) assms bij_compose bij_id_upd2 compose.simps(2)
     compose_act_unique2 compose_asTrans fsupp_compose fsupp_id fsupp_upd nswapping_toSwp
     permut_def toPerm_def toSwp_def)
qed

theorem toPerm_toSwp:
assumes 1: "permut prm" and 2: "fsupp \<sigma>" "bij \<sigma>"
shows "toPerm (toSwp prm) a \<sigma> = prm a \<sigma>"
by (metis "1" assms(2) assms(3) compose_asTrans toPerm_toSwp_compose)

lemma toPerm_id_update_eq:
assumes "nswapping swp"
shows "toPerm swp c (id(z1 := z2, z2 := z1)) = swp c z1 z2"
by (metis (no_types, opaque_lifting) act.simps(1) act.simps(2) assms bij_compose comp_id
compose.simps(1) compose.simps(2) compose_act_unique compose_asTrans fsupp_compose toPerm_def)

theorem toSwp_toPerm:
assumes "nswapping swp"
shows "toSwp (toPerm swp) = swp"
unfolding toSwp_def fun_eq_iff toPerm_id_update_eq[OF assms] by simp


(* Extension to include a free-variable-like operator: *)

(* This predicate is called "swapping" in the paper
"Recursive Function Definition for Types with Binders" by Michael Norrish,
where what we call the swap/free recursor was introduced: *)

definition swappingFvars :: "('c \<Rightarrow> 'v :: cinf \<Rightarrow> 'v \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'v set) \<Rightarrow> bool" where
"swappingFvars swp fvars \<equiv>
  (\<forall> c x. swp c x x = c) \<and>
  (\<forall> c x y. swp (swp c x y) x y = c) \<and>
  (\<forall> c x y. x \<notin> fvars c \<and> y \<notin> fvars c \<longrightarrow> swp c x y = c) \<and>
  (\<forall> x c z1 z2. x \<in> fvars (swp c z1 z2) \<longleftrightarrow> sw x z1 z2 \<in> fvars c)"

lemma nswapping_imp_swappingFvars_def2:
"nswapping swp \<and>
  (\<forall> c x y. x \<notin> fvars c \<and> y \<notin> fvars c \<longrightarrow> swp c x y = c) \<and>
  (\<forall> x c z1 z2. x \<in> fvars (swp c z1 z2) \<longleftrightarrow> sw x z1 z2 \<in> fvars c)
 \<Longrightarrow> swappingFvars swp fvars"
unfolding nswapping_def swappingFvars_def by auto

(* Equivalent version of the above using freshness instead of swapping: *)
definition swapping :: "('c \<Rightarrow> 'v :: cinf \<Rightarrow> 'v \<Rightarrow> 'c) \<Rightarrow> ('v \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool" where
"swapping swp frs \<equiv>
  (\<forall> c x. swp c x x = c) \<and>
  (\<forall> c x y. swp (swp c x y) x y = c) \<and>
  (\<forall> c x y. frs x c \<and> frs y c \<longrightarrow> swp c x y = c) \<and>
  (\<forall> x c z1 z2. frs x (swp c z1 z2) \<longleftrightarrow> frs (sw x z1 z2) c)"


(* permutFvars is the permutation-based counterpart of the swappingFvars predicate.
Unlike permut for nswapping, this is not a perfect counterpart, since
the connection only works in one direction, in that permutFvars is a stronger axiomatization
than swappingFvars (since the latter misses the compositionality axiom).
*)

definition permutFvars :: "('c \<Rightarrow> ('v :: cinf \<Rightarrow> 'v) \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'v set) \<Rightarrow> bool" where
"permutFvars prm fvars \<equiv>
  (\<forall>c. prm c id = c) \<and>
  (\<forall>c \<sigma> \<tau>. bij \<sigma> \<and> fsupp \<sigma> \<and> bij \<tau> \<and> fsupp \<tau> \<longrightarrow> prm (prm c \<sigma>) \<tau> = prm c (\<tau> \<circ> \<sigma>)) \<and>
  (\<forall> c \<sigma>. bij \<sigma> \<and> fsupp \<sigma> \<and> (\<forall>x \<in> fvars c. \<sigma> x = x) \<longrightarrow> prm c \<sigma> = c) \<and>
  (\<forall> x c \<sigma>. bij \<sigma> \<and> fsupp \<sigma> \<longrightarrow> (x \<in> fvars (prm c \<sigma>) \<longleftrightarrow> inv \<sigma> x \<in> fvars c))"

lemma permutFvars_def2:
"permutFvars prm fvars \<longleftrightarrow>
  permut prm \<and>
  (\<forall> c \<sigma>. bij \<sigma> \<and> fsupp \<sigma> \<and> (\<forall>x \<in> fvars c. \<sigma> x = x) \<longrightarrow> prm c \<sigma> = c) \<and>
  (\<forall> x c \<sigma>. bij \<sigma> \<and> fsupp \<sigma> \<longrightarrow> (x \<in> fvars (prm c \<sigma>) \<longleftrightarrow> inv \<sigma> x \<in> fvars c))"
unfolding permutFvars_def permut_def by auto

(* *)

definition permutFvars' :: "('c \<Rightarrow> ('v :: cinf \<Rightarrow> 'v) \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'v set) \<Rightarrow> bool" where
"permutFvars' prm fvars \<equiv>
  (\<forall>c. prm c id = c) \<and>
  (\<forall>c \<sigma> \<tau>. bij \<sigma> \<and> fsupp \<sigma> \<and> bij \<tau> \<and> fsupp \<tau> \<longrightarrow> prm (prm c \<sigma>) \<tau> = prm c (\<tau> \<circ> \<sigma>)) \<and>
  (\<forall> c \<sigma>. bij \<sigma> \<and> fsupp \<sigma> \<and> (\<forall>x \<in> fvars c. \<sigma> x = x) \<longrightarrow> prm c \<sigma> = c)"

lemma permutFvars'_def2:
"permutFvars' prm fvars \<longleftrightarrow>
  permut prm \<and>
  (\<forall> c \<sigma>. bij \<sigma> \<and> fsupp \<sigma> \<and> (\<forall>x \<in> fvars c. \<sigma> x = x) \<longrightarrow> prm c \<sigma> = c)"
unfolding permutFvars'_def permut_def by auto

lemma permutFvars_permutFvars':
"permutFvars prm fvars \<Longrightarrow> permutFvars' prm fvars"
unfolding permutFvars_def2 permutFvars'_def2 by auto

(* *)
theorem swappingFvars_toSwp:
assumes "permutFvars perm fvars"
shows "swappingFvars (toSwp perm) fvars"
apply(rule nswapping_imp_swappingFvars_def2)
using assms unfolding permutFvars_def2 apply safe
  subgoal using nswapping_toSwp by blast
  subgoal for c x y apply(erule allE[of _ c], erule allE[of _ "id(x:=y,y:=x)"])
  unfolding toSwp_def by auto
  subgoal for x c z1 z2 apply(erule allE[of _ x], elim allE[of _ c],
      elim allE[of _ "id(z1:=z2,z2:=z1)"]) unfolding toSwp_def sw_def
    by (metis (no_types, lifting) bij_id_upd2 fsupp_id fsupp_upd fun_upd_other
    fun_upd_same id_apply id_swapTwice inv_unique_comp)
  subgoal for x c z1 z2 apply(erule allE[of _ x], elim allE[of _ c],
      elim allE[of _ "id(z1:=z2,z2:=z1)"]) unfolding toSwp_def sw_def
    by (metis bij_id_upd2 eq_id_iff fsupp_id fsupp_upd fun_upd_apply
    id_swapTwice inv_unique_comp) .

(* NB: The theorem in the opposite direction, namely
"swappingFvars swp fvars \<Longrightarrow> permutFvars (toPerm swp) fvars"
 does not hold, for the reasons mentioned above.

Instead, we must assume nswapping too in order for this to work:
*)


lemma toPerm_cong_id_compose:
assumes s: "swappingFvars swp fvars" and n: "nswapping swp"
and 2: "\<forall>x\<in>fvars c. (compose z1z2s) x = x"
and 3: "nonredundant z1z2s"
shows "toPerm swp c (compose z1z2s) = c"
proof-
  have "permut (toPerm swp)"
  	by (simp add: n permut_toPerm)
  hence aux:  "\<And>c. toPerm swp c id = c"
   "\<And>c \<sigma> \<tau>. bij \<sigma> \<Longrightarrow> fsupp \<sigma> \<Longrightarrow> bij \<tau> \<and> fsupp \<tau> \<Longrightarrow>
    toPerm swp c (\<tau> \<circ> \<sigma>) = toPerm swp (toPerm swp c \<sigma>) \<tau>"
  unfolding permut_def by auto
  show ?thesis
  using 2 3 proof(induction z1z2s arbitrary: c rule: list_induct_Pair)
    case Nil
    then show ?case
  	by simp (metis fun.map_ident n o_id permut_def permut_toPerm)
  next
    case (Cons z1 z2 z1z2s)
    have nr: "nonredundant z1z2s"
    	using Cons.prems(2) nonredundant_Cons by blast
     have 0: \<open>\<And>z2 z1 c. toPerm swp c (id(z1 := z2, z2 := z1)) = swp c z1 z2\<close>
     by (simp add: n toPerm_id_update_eq)

    show ?case  unfolding compose.simps(2) apply(subst aux(2))
    subgoal by auto subgoal by auto subgoal by auto
    subgoal unfolding toPerm_id_update_eq[OF n] apply(subst Cons.IH)
      subgoal using Cons(2,3)  apply - apply(drule nonredundant_compose)
      by simp (smt (verit, best) fun_upd_apply id_apply insert_iff mem_Collect_eq)
      subgoal using Cons(3) nonredundant_Cons by blast
      subgoal by (smt (verit) Cons.prems(1) 0 \<open>\<forall>x\<in>fvars c. compose z1z2s x = x\<close> aux(1)
         comp_def comp_id compose.simps(2) fun_upd_id_same fun_upd_other fun_upd_same
         fun_upd_triv fun_upd_twist id_apply id_comp id_swapTwice
         prod.sel(1) rewriteR_comp_comp s swappingFvars_def type_copy_map_cong0) . .
  qed
qed

lemma toPerm_cong_id:
assumes s: "swappingFvars swp fvars" and n: "nswapping swp"
and 1: "bij \<sigma>" "fsupp \<sigma>" and 2: "\<forall>x\<in>fvars c. \<sigma> x = x"
shows "toPerm swp c \<sigma> = c"
using assms fsupp_ex_compose_even_stronger n toPerm_cong_id_compose by fastforce

lemma inv_id_upd[simp]:
"inv (id(z1 := z2, z2 := z1)) = id(z1 := z2, z2 := z1)"
unfolding fun_eq_iff by (metis id_swapTwice inv_unique_comp)

lemma toPerm_free_compose:
assumes s: "swappingFvars swp fvars" and n: "nswapping swp"
and 1: "bij (compose z1z2s)" "fsupp (compose z1z2s)"
shows "x \<in> fvars (toPerm swp c (compose z1z2s)) \<longleftrightarrow> inv (compose z1z2s) x \<in> fvars c"
proof-
  have "permut (toPerm swp)"
  	by (simp add: n permut_toPerm)
  hence aux:  "\<And>c. toPerm swp c id = c"
   "\<And>c \<sigma> \<tau>. bij \<sigma> \<Longrightarrow> fsupp \<sigma> \<Longrightarrow> bij \<tau> \<Longrightarrow> fsupp \<tau> \<Longrightarrow>
    toPerm swp c (\<tau> \<circ> \<sigma>) = toPerm swp (toPerm swp c \<sigma>) \<tau>"
  unfolding permut_def by auto
  show ?thesis using 1 proof(induction z1z2s arbitrary: c x rule: list_induct_Pair)
    case Nil
    then show ?case using n s toPerm_cong_id by fastforce
  next
    case (Cons z1 z2 z1z2s)
    show ?case unfolding compose.simps apply(subst aux(2))
      subgoal by auto subgoal by auto subgoal by auto  subgoal by auto
      subgoal unfolding toPerm_id_update_eq[OF n]
      unfolding s[unfolded swappingFvars_def, THEN conjunct2, THEN conjunct2,
          THEN conjunct2, rule_format]
      apply(subst Cons.IH)
        subgoal by auto subgoal by auto
        subgoal apply(subst o_inv_distrib) by auto . .
  qed
qed

lemma toPerm_free:
assumes s: "swappingFvars swp fvars" and n: "nswapping swp"
and 1: "bij \<sigma>" "fsupp \<sigma>"
shows "x \<in> fvars (toPerm swp c \<sigma>) \<longleftrightarrow> inv \<sigma> x \<in> fvars c"
by (metis assms compose_asTrans toPerm_free_compose)

theorem permutFvars_toPerm:
assumes s: "swappingFvars swp fvars" and n: "nswapping swp"
shows "permutFvars (toPerm swp) fvars"
unfolding permutFvars_def2
using assms toPerm_cong_id[OF assms] toPerm_free[OF assms] permut_toPerm by auto

theorem permutFvars'_toPerm:
assumes s: "swappingFvars swp fvars" and n: "nswapping swp"
shows "permutFvars' (toPerm swp) fvars"
by (simp add: n permutFvars_permutFvars' permutFvars_toPerm s)


(* *)

(* thm toSwp_toPerm toPerm_toSwp
thm permutFvars_toPerm
thm swappingFvars_toSwp
*)

(* Relevant theorems for our case: *)

thm fsupp_ex_compose_strong[of f] compose.simps[no_vars]




end