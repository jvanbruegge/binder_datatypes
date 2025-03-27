theory Infinitary_Lambda_Terms
  imports Prelim "HOL-Cardinals.Cardinals" "HOL-Library.Countable_Set" "HOL-Library.FuncSet"
begin

(* This theory defines infinitary terms and their basic operators: constructors, 
destructor, freshness, swapping and substitution; and proves many properties 
connecting these operators. The terms are constructed by quotienting pre-terms to 
alpha-equivalence. 
*)


(*********************)
(* Variables *)

(* We take a type of variables having cardinality Aleph_1, the smallest uncountable cardinal. 
(Though regular uncountable cardinal would do.) *)
typedef var = "{x::nat set. x \<in> Field (cardSuc natLeq)}" 
 by simp (metis Field_cardSuc_not_empty Field_natLeq all_not_in_conv natLeq_card_order)

lemma bij_betw_Rep_var: "bij_betw Rep_var (UNIV::var set) (Field (cardSuc natLeq))"
by (smt (verit, best) Abs_var_inverse Rep_var Rep_var_inject UNIV_I bij_betwI' mem_Collect_eq)

lemma card_var: "|UNIV::var set| =o cardSuc natLeq"
proof-
  have "|UNIV::var set| =o |Field (cardSuc natLeq)|"
  using bij_betw_Rep_var card_of_ordIso by auto
  also have "|Field (cardSuc natLeq)| =o cardSuc natLeq" 
    by (simp add: natLeq_Card_order)
  finally show ?thesis .
qed

lemma le_card_var: "natLeq <o cardSuc natLeq"
using cardSuc_greater natLeq_Card_order by blast

lemma infinite_var: "infinite (UNIV::var set)" 
using Field_natLeq bij_betw_Rep_var bij_betw_finite natLeq_Card_order by fastforce

lemma regularCard_var: "regularCard |UNIV::var set|" 
using Cinfinite_cardSuc card_var natLeq_Cinfinite ordIso_symmetric 
regularCard_cardSuc regularCard_ordIso by blast

lemma countable_iff_lq_natLeq: "countable A \<longleftrightarrow> |A| \<le>o natLeq"
unfolding countable_def 
by (metis Field_card_of UNIV_I card_of_mono2 card_of_nat card_of_ordLeq ordLeq_ordIso_trans subsetI)

lemma countable_iff_le_card_var: "countable A \<longleftrightarrow> |A| <o |UNIV::var set|"
proof-
  have "countable A \<longleftrightarrow> |A| <o cardSuc natLeq"
  unfolding countable_iff_lq_natLeq 
  by (simp add: natLeq_Card_order)
  also have "\<dots> \<longleftrightarrow> |A| <o |UNIV::var set|" 
    by (meson card_var not_ordLess_ordIso ordIso_iff_ordLeq ordLeq_iff_ordLess_or_ordIso ordLeq_transitive)
  finally show ?thesis .
qed

lemma countable_card_var: "countable A \<Longrightarrow> |A| <o |UNIV::var set|"
using countable_iff_le_card_var by auto

lemma finite_card_var: "finite A \<Longrightarrow> |A| <o |UNIV::var set|"
using infinite_var by auto

lemma countable_exists_countable_var: 
assumes "countable (A::var set)"
shows "\<exists>B. B \<inter> A = {} \<and> infinite B"
apply(rule exI[of _ "-A"])
by simp (metis Compl_eq_Diff_UNIV assms card_of_Well_order countable_card_var 
not_ordLeq_iff_ordLess ordLeq_iff_ordLess_or_ordIso uncountable_infinite uncountable_minus_countable)

lemma countable_exists_finite_var: 
assumes "countable (A::var set)"
shows "\<exists>B. B \<inter> A = {} \<and> finite B \<and> card B = n"
proof-
  obtain B' where B': "B' \<inter> A = {}" and iB': "infinite B'"
  using countable_exists_countable_var[OF assms] by auto
  obtain B where "B \<subseteq> B' \<and> finite B \<and> card B = n"
  using iB' by (meson infinite_arbitrarily_large)
  thus ?thesis using B' by auto
qed

lemma countable_exists_list_var: 
assumes "countable (A::var set)"
shows "\<exists>xs. set xs \<inter> A = {} \<and> distinct xs \<and> length xs = n"
by (metis assms countable_exists_finite_var distinct_remdups finite_list length_remdups_card_conv set_remdups)

lemma exists_var: 
assumes "countable (X::var set)"
shows "\<exists>x. x \<notin> X"
by (metis Int_absorb assms countable_exists_countable_var disjoint_iff finite.emptyI)

lemma finite_exists_var:
assumes "finite X"
shows "\<exists> x::var. x \<notin> X"
by (simp add: assms ex_new_if_finite infinite_var)


(*********************)
(* (Infinitary) Pre-(infinitary)terms *)

codatatype ptrm = PVr (getPVr:var) | 
                  PAp (getPApL:ptrm) (getPApR:ptrm) | 
                  PLm (getPLmV:var) (getPLmT:ptrm)

(* NB: All operators on pre-terms will have names prefixed by "p", e.g., "pfresh". 
We reserve the standard names, e.g., "fresh", for later when we introduced 
actTransual (infinitary) terms (via quotienting). 
*)

(* Freshness *)

coinductive pfresh :: "var \<Rightarrow> ptrm \<Rightarrow> bool" where 
 PVr[intro]: "z \<noteq> x \<Longrightarrow> pfresh z (PVr x)"
|PAp[intro]: "pfresh z t1 \<Longrightarrow> pfresh z t2 \<Longrightarrow> pfresh z (PAp t1 t2)"
|PLm[intro]: "z = x \<or> pfresh z t \<Longrightarrow> pfresh z (PLm x t)"

thm pfresh.coinduct

lemma pfresh_simps[simp]: 
"pfresh z (PVr x) \<longleftrightarrow> z \<noteq> x"
"pfresh z (PAp t1 t2) \<longleftrightarrow> pfresh z t1 \<and> pfresh z t2"
"pfresh z (PLm x t) \<longleftrightarrow> z = x \<or> pfresh z t"
  using pfresh.cases by blast+

(***********************)
(* Pick fresh variables *)

(* 
lemma finite_neg_imp: 
assumes "finite {x. \<not> \<phi> x}" and "finite {x. \<chi> x}"
shows "finite {x. \<phi> x \<longrightarrow> \<chi> x}"
using finite_UnI[OF assms]  by (simp add: Collect_imp_eq Collect_neg_eq)
*)

(* Auximilary concept to prove cocountability of pfresh (i.e., countability of the free vars) *)
fun fvi :: "nat \<Rightarrow> ptrm \<Rightarrow> var set" where 
"fvi 0 t = {}"
|
"fvi (Suc i) (PVr x) = {x}"
|
"fvi (Suc i) (PAp t1 t2) = fvi i t1 \<union> fvi i t2"
|
"fvi (Suc i) (PLm x t) = fvi i t - {x}"

lemma pfresh_fvi: "{x . \<not> pfresh x t} \<subseteq> (\<Union>i. fvi i t)" 
proof-
  {fix x assume "\<forall>i. x \<notin> fvi i t"
   hence "pfresh x t"
   proof(coinduct rule: pfresh.coinduct)
     case (pfresh x t)
     show ?case proof(cases t)
       case (PVr x1)
       then show ?thesis using pfresh apply simp 
         using fvi.simps(2) by blast
     next
       case (PAp x21 x22)
       then show ?thesis using pfresh apply simp 
         by (metis UnI1 UnI2 fvi.simps(3))
     next
       case (PLm x31 x32)
       then show ?thesis using pfresh apply auto
         using fvi.simps(4) by blast
     qed
   qed 
  }
  thus ?thesis by auto
qed

lemma finite_fvi: "finite (fvi i t)"
apply(induct i arbitrary: t) 
  subgoal by auto
  subgoal for i t by (cases t, auto) .

lemma countable_Union_fvi: "countable (\<Union>i. fvi i t)"
apply(rule countable_UN)  
using finite_fvi countable_finite by auto

lemma cocountable_pfresh: "countable {x . \<not> pfresh x t}"
using countable_Union_fvi countable_subset pfresh_fvi by blast

lemma cocountable_list_pfresh: "countable {x . \<exists> t \<in> set ts. \<not> pfresh x t}"
proof (induct ts) 
  case Nil
  then show ?case using infinite_var by auto
next
  case (Cons t ts)
  have "{x. \<exists>t\<in>set (t # ts). \<not> pfresh x t} \<subseteq> 
   {x. \<not> pfresh x t} \<union> {x. \<exists>s\<in>set ts. \<not> pfresh x s}" by auto 
  then show ?case using Cons
    by (simp add: cocountable_pfresh countable_subset)
qed 

lemma exists_pfresh_set:
assumes "countable X"
shows "\<exists> z. z \<notin> X \<and> z \<notin> set xs \<and> (\<forall>t \<in> set ts. pfresh z t)"
proof-
  have 0: "countable (X \<union> set xs \<union> {x. \<exists>s\<in>set ts. \<not> pfresh x s})" 
    using assms 
    using cocountable_list_pfresh uncountable_infinite by auto 
  show ?thesis using exists_var[OF 0] by simp
qed

lemma exists_pfresh:
"\<exists> z. z \<notin> set xs \<and> (\<forall>t \<in> set ts. pfresh z t)"
using exists_pfresh_set by blast

definition ppickFreshS :: "var set \<Rightarrow> var list \<Rightarrow> ptrm list \<Rightarrow> var" where 
"ppickFreshS X xs ts \<equiv> SOME z. z \<notin> X \<and> z \<notin> set xs \<and> (\<forall>t \<in> set ts. pfresh z t)" 

lemma ppickFreshS: 
assumes "countable X"
shows "ppickFreshS X xs ts \<notin> X \<and> ppickFreshS X xs ts \<notin> set xs \<and> 
       (\<forall>t \<in> set ts. pfresh (ppickFreshS X xs ts) t)"
using exists_pfresh_set[OF assms] unfolding ppickFreshS_def 
by (rule someI_ex)

lemmas ppickFreshS_set = ppickFreshS[THEN conjunct1]
and ppickFreshS_var = ppickFreshS[THEN conjunct2, THEN conjunct1]
and ppickFreshS_ptrm = ppickFreshS[THEN conjunct2, THEN conjunct2, unfolded Ball_def, rule_format]

(* Unconditional form of ppick-pfresh, without any set: *)
definition "ppickFresh \<equiv> ppickFreshS {}"

lemmas ppickFresh_var = ppickFreshS_var[OF countable_empty, unfolded ppickFresh_def[symmetric]]
and ppickFresh_ptrm = ppickFreshS_ptrm[OF countable_empty, unfolded ppickFresh_def[symmetric]]

(* Swapping *)

definition sw :: "var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var" where 
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

primcorec pswap :: "ptrm \<Rightarrow> var \<Rightarrow> var \<Rightarrow> ptrm" where 
"pswap tt z1 z2 = 
 (case tt of PVr x \<Rightarrow> PVr (sw x z1 z2)
            |PAp s t \<Rightarrow> PAp (pswap s z1 z2) (pswap t z1 z2)
            |PLm x t \<Rightarrow> PLm (sw x z1 z2) (pswap t z1 z2)
 )"

lemma pswap_PVr[simp]: "pswap (PVr x) z1 z2 = PVr (sw x z1 z2)"
by (simp add: pswap.ctr)
lemma pswap_PAp[simp]: "pswap (PAp s t) z1 z2 = PAp (pswap s z1 z2) (pswap t z1 z2)"
by (simp add: pswap.ctr)
lemma pswap_PLm[simp]: "pswap (PLm x t) z1 z2 = PLm (sw x z1 z2) (pswap t z1 z2)"
by (simp add: pswap.ctr)

find_theorems name: ptrm name: split

lemma pswap_sym: "pswap s y z = pswap s z y"
apply (coinduction arbitrary: s) by (auto split: ptrm.split simp: sw_def)

lemma pswap_id[simp]: "pswap s y y = s"
apply (coinduction arbitrary: s) by (auto split: ptrm.split simp: sw_def)

lemma pswap_pswap: 
"pswap (pswap s y z) y1 z1 = pswap (pswap s y1 z1) (sw y y1 z1) (sw z y1 z1)"
apply (coinduction arbitrary: s)  
apply (simp add: ptrm.case_eq_if) 
using sw_sw unfolding is_PVr_def  is_PAp_def is_PLm_def by auto 

lemma pswap_invol[simp]: "pswap (pswap s y z) y z = s"
apply (coinduction arbitrary: s) apply (auto simp: is_PVr_def is_PAp_def is_PLm_def split: ptrm.split)
  apply (metis is_PVr_def pswap.disc_iff(1))  
  by (metis is_PAp_def pswap.disc_iff(2))

lemma pswap_invol2: "pswap (pswap s y z) z y = s"
  by (simp add: pswap_sym)

lemma pswap_inj[iff]: "pswap s z1 z2 = pswap t z1 z2 \<longleftrightarrow> s = t"
proof-
  {assume "\<exists>z1 z2. pswap s z1 z2 = pswap t z1 z2"
   hence "s = t"
   apply(coinduct rule: ptrm.coinduct) apply (auto simp: is_PVr_def is_PAp_def is_PLm_def) 
   apply (metis pswap_PVr pswap_invol2) 
   apply (metis pswap_PVr pswap_invol2) 
   apply (metis pswap_PAp pswap_invol2)
   apply (metis pswap_PAp pswap_invol2)
   apply blast apply blast+ .
  }
  thus ?thesis by auto
qed

lemma pswap_surj: "\<exists>t. s = pswap t z1 z2"
  by (metis pswap_invol)

lemma pswap_pfresh_iff[simp]: 
"pfresh (sw x z1 z2) (pswap s z1 z2) \<longleftrightarrow> pfresh x s"
proof-
  {assume "\<exists>z1 z2. pfresh (sw x z1 z2) (pswap s z1 z2)"
   hence "pfresh x s"
   apply(coinduct rule: pfresh.coinduct) apply (elim exE)
   subgoal for x s z1 z2
   apply(cases s)
     subgoal apply(rule disjI1) by auto
     subgoal apply(rule disjI2, rule disjI1) by auto
     subgoal apply(rule disjI2, rule disjI2) by auto . .
  }
  moreover
  {fix xx ss assume "\<exists>x s z1 z2. pfresh x s \<and> xx = sw x z1 z2 \<and> ss = pswap s z1 z2"
   hence "pfresh xx ss"
   apply(coinduct rule: pfresh.coinduct) apply (elim exE)
   subgoal for xx ss x s z1 z2
   apply(cases s)
     subgoal apply(rule disjI1) by auto
     subgoal apply(rule disjI2, rule disjI1) by auto
     subgoal apply(rule disjI2, rule disjI2) by auto . .
  }
  ultimately show ?thesis by blast
qed

lemma pfresh_pswap_iff: 
"pfresh x (pswap s z1 z2) = pfresh (sw x z1 z2) s"
  by (metis sw_invol pswap_pfresh_iff)

coinductive alpha :: "ptrm \<Rightarrow> ptrm \<Rightarrow> bool" where 
 PVr[intro]: 
"alpha (PVr x) (PVr x)"
|PAp[intro]: 
"alpha s s' \<Longrightarrow> alpha t t' \<Longrightarrow> alpha (PAp s t) (PAp s' t')"
|PLm[intro]: 
"(z = x \<or> pfresh z t) \<Longrightarrow> (z = x' \<or> pfresh z t') 
 \<Longrightarrow> alpha (pswap t z x) (pswap t' z x') \<Longrightarrow> alpha (PLm x t) (PLm x' t')"

lemma alpha_PVr_eq[simp]: "alpha (PVr x) t \<longleftrightarrow> t = PVr x"
by (auto elim: alpha.cases)

lemma alpha_eq_PVr[simp]: "alpha t (PVr x) \<longleftrightarrow> t = PVr x"
by (auto elim: alpha.cases)

lemma alpha_PAp_cases[elim, case_names PApc]: 
assumes "alpha (PAp s1 s2) t"
obtains t1 t2 where "t = PAp t1 t2" and "alpha s1 t1" and "alpha s2 t2"
using assms by (auto elim: alpha.cases)

lemma alpha_PAp_cases2[elim, case_names PApc]: 
assumes "alpha t (PAp s1 s2)"  
obtains t1 t2 where "t = PAp t1 t2" and "alpha t1 s1" and "alpha t2 s2"
using assms by (auto elim: alpha.cases)

lemma alpha_PLm_cases[elim, case_names PLmc]: 
assumes "alpha (PLm x s) t'"
obtains x' s' z where "t' = PLm x' s'" 
and "z = x \<or> pfresh z s" and "z = x' \<or> pfresh z s'" 
and "alpha (pswap s z x) (pswap s' z x')"
using assms by cases auto

lemma alpha_pswap: 
assumes "alpha s s'" shows "alpha (pswap s z1 z2) (pswap s' z1 z2)"
proof-
  {fix ss ss' assume "\<exists>s s' z1 z2. alpha s s' \<and> ss = pswap s z1 z2 \<and> ss' = pswap s' z1 z2"
   hence "alpha ss ss'"
   apply(coinduct rule: alpha.coinduct) apply (elim exE)
   subgoal for ss ss' s s' z1 z2
   apply(elim conjE) apply(erule alpha.cases)
     subgoal by auto
     subgoal by auto
     subgoal for z x t x' t'
     apply(rule disjI2, rule disjI2) 
     apply(rule exI[of _ "sw z z1 z2"]) 
     apply(rule exI[of _ "sw x z1 z2"]) apply(rule exI[of _ "pswap t z1 z2"])
     apply(rule exI[of _ "sw x' z1 z2"]) apply(rule exI[of _ "pswap t' z1 z2"])
     using pswap_pswap by auto . .
   }
   thus ?thesis using assms by blast
qed 

lemma alpha_refl[simp,intro!]: "alpha s s"
proof-
  {fix s1 s2 :: ptrm
   assume "s1 = s2"
   hence "alpha s1 s2"
   apply(coinduct) by (metis ptrm.exhaust)
  }
  thus ?thesis by auto
qed

lemma alpha_sym: 
assumes "alpha s t" shows "alpha t s" 
using assms apply(coinduct) subgoal for s1 s2
apply(erule alpha.cases) by auto .

lemma alpha_pfresh_imp: 
assumes "alpha t t'" and "pfresh y t" shows "pfresh y t'" 
proof-
  {assume "\<exists>t. alpha t t' \<and> pfresh y t"
   hence "pfresh y t'"
   apply(coinduct) apply(elim exE conjE) 
   subgoal for y t' t apply(erule alpha.cases)
     subgoal by auto
     subgoal by auto
     subgoal for z x tt x' tt' apply(rule disjI2, rule disjI2)
     apply(rule exI[of _ y], simp) 
     apply(subgoal_tac "y = x' \<or> 
        (alpha (pswap ((pswap (pswap tt z x) z x')) x x') tt' \<and> pfresh y (pswap (pswap tt z x) z x')) \<or> 
        pfresh y t")
       subgoal apply auto 
         using pfresh_pswap_iff apply auto 
         apply (metis alpha_pswap pswap_invol sw_diff sw_eqR) 
         apply (metis alpha_pswap pswap_invol2 sw_diff) 
         apply (metis pswap_invol2 sw_diff)  
         by (metis alpha_pswap pswap_invol2 sw_diff)
       subgoal by auto . . .
  }
  thus ?thesis using assms by blast
qed 

lemma alpha_pfresh_iff: 
assumes "alpha s t"  
shows "pfresh x s \<longleftrightarrow> pfresh x t"
using alpha_pfresh_imp alpha_sym assms by blast

lemma pswap_pfresh_alpha: 
assumes "pfresh z1 t" and "pfresh z2 t"
shows "alpha (pswap t z1 z2) t"
proof-
  {fix tt assume "\<exists>z1 z2. tt = pswap t z1 z2 \<and> pfresh z1 t \<and> pfresh z2 t"
   hence "alpha tt t"
   apply(coinduct) apply(elim exE conjE)
   subgoal for tt t z1 z2 apply(cases t)
     subgoal by auto
     subgoal by auto
     subgoal apply(rule disjI2, rule disjI2) apply clarsimp  
       by (metis alpha_refl pswap_id pswap_sym sw_diff sw_eqL sw_sym) . .
  }
  thus ?thesis using assms by auto
qed 



(* NB: When we switch from terms to infinite-terms, and more generally from induction 
to coinduction for alpha, we replace the any depth-based argument, whose only purpose 
was to accommodate induction "up to" the transitive closure of alpha, 
with genuine reasoning about the transitive closure. I.e., we prove that 
the refl-transitive closure of alpha is a bisimulation according to the operator definining 
alpha as greatest bisimulaton.*)

lemma alpha_Lm_pfresh_multi:
assumes al: "alpha (PLm x t) (PLm x' t')"  
shows "\<exists>z t1 t2. z\<notin>{x,x'} \<and> pfresh z t \<and> pfresh z t' \<and> alpha (pswap t z x) t1 \<and> alpha t1 t2 \<and> alpha t2 (pswap t' z x')"
proof-
  obtain u where al: "alpha (pswap t u x) (pswap t' u x')" 
  and u: "u = x \<or> pfresh u t" and u': "u = x' \<or> pfresh u t'" 
  using al by (cases rule: alpha.cases, auto)
  obtain z where z: "z\<notin>{u,x,x'}" "pfresh z t" "pfresh z t'" 
         using exists_pfresh[of "[u,x,x']" "[t,t']"] by auto
  have tt: "alpha (pswap t z x) (pswap (pswap t u x) u z)" 
  by (smt (verit, ccfv_threshold) alpha_pswap pswap_invol pswap_pfresh_alpha pswap_pswap sw_diff sw_eqL u z)
  have tt': "alpha (pswap t' z x') (pswap (pswap t' u x') u z)" 
  by (smt (verit, ccfv_threshold) alpha_pswap pswap_invol pswap_pfresh_alpha pswap_pswap sw_diff sw_eqL u' z)
  show ?thesis apply(rule exI[of _ z], rule exI[of _ "pswap (pswap t u x) u z"], 
  rule exI[of _ "pswap (pswap t' u x') u z"], intro conjI)
    subgoal using z by auto
    subgoal using z by auto
    subgoal using z by auto
    subgoal using tt by auto
    subgoal by (meson al alpha_pswap)  
    subgoal by (simp add: alpha_sym tt') .
qed

lemma alphaT_Lm_pfresh1:
assumes al: "alpha (PLm x t) (PLm x' t')"  
shows "\<exists>z. z\<notin>{x,x'} \<and> pfresh z t \<and> pfresh z t' \<and> alpha\<^sup>*\<^sup>* (pswap t z x) (pswap t' z x')"
using alpha_Lm_pfresh_multi[OF assms] by auto

lemma alphaT_pswap: assumes "alpha\<^sup>*\<^sup>* s s'" shows "alpha\<^sup>*\<^sup>* (pswap s z1 z2) (pswap s' z1 z2)"
using assms apply(induct) using alpha_pswap by auto (meson rtranclp.simps)

lemma alphaT_PVr:
assumes al: "alpha\<^sup>*\<^sup>* (PAp t1 t2) (PAp t1' t2')"  
shows "alpha\<^sup>*\<^sup>* t1 t1' \<and> alpha\<^sup>*\<^sup>* t2 t2'"
proof-
  {fix t t' assume "alpha\<^sup>*\<^sup>* t t'"
   hence "\<forall>t1 t2 t1' t2'. t = PAp t1 t2 \<and> t' = PAp t1' t2' \<longrightarrow> alpha\<^sup>*\<^sup>* t1 t1' \<and> alpha\<^sup>*\<^sup>* t2 t2'"
   apply(induct) by fastforce+
  }
  thus ?thesis using assms by metis
qed

lemma alphaT_Lm_pfresh:
assumes al: "alpha\<^sup>*\<^sup>* (PLm x t) (PLm x' t')"  
shows "\<exists>z. (z = x \<or> pfresh z t) \<and> (z = x' \<or> pfresh z t') \<and> alpha\<^sup>*\<^sup>* (pswap t z x) (pswap t' z x')"
proof-
  {fix t1 t2 
   assume "alpha\<^sup>*\<^sup>* t1 t2"
   hence "\<forall> x t x' t'. t1 = PLm x t \<and> t2 = PLm x' t' \<longrightarrow> 
         (\<exists>z. z \<notin> {x,x'} \<and> pfresh z t \<and> pfresh z t' \<and> alpha\<^sup>*\<^sup>* (pswap t z x) (pswap t' z x'))"
   proof induct
     case base
     then show ?case
     using alphaT_Lm_pfresh1 by blast
   next
     case (step t2 t3)
     show ?case proof safe
       fix x1 t1' x3 t3' assume t1: "t1 = PLm x1 t1'" and t3: "t3 = PLm x3 t3'"
       from `alpha t2 t3` t3 obtain x2 t2' where t2: "t2 = PLm x2 t2'" 
         by (meson alpha_PLm_cases alpha_sym)
       from alphaT_Lm_pfresh1[OF `alpha t2 t3`[unfolded t2 t3]] obtain z where 
       z: "z \<notin> {x2, x3}" "pfresh z t2'" "pfresh z t3' " "alpha\<^sup>*\<^sup>* (pswap t2' z x2) (pswap t3' z x3)"
       by auto
       from step(3)[rule_format, of x1 t1' x2 t2', unfolded t1 t2, simplified]
       obtain zz where zz: "zz \<notin> {x1,x2}" "pfresh zz t1'" "pfresh zz t2'" "alpha\<^sup>*\<^sup>* (pswap t1' zz x1) (pswap t2' zz x2)"
       by auto
       obtain u where u: "u \<notin> {z,zz,x1,x2,x3}" "pfresh u t1'" "pfresh u t2'" "pfresh u t3'"
       using exists_pfresh[of "[z,zz,x1,x2,x3]" "[t1',t2',t3']"] by auto
       have a1: "alpha (pswap t1' u x1) (pswap (pswap t1' zz x1) u zz)" 
         by (smt (verit) alpha_pswap pswap_invol2 pswap_pfresh_alpha pswap_pswap sw_diff sw_eqL u(2) zz(2))
       have a2: "alpha\<^sup>*\<^sup>* (pswap (pswap t1' zz x1) u zz) (pswap (pswap t2' zz x2) u zz)"
       using alphaT_pswap[OF zz(4)] by auto
       have a3: "alpha (pswap (pswap t2' zz x2) u zz) (pswap t2' u x2)"
       by (metis alpha_pswap pswap_invol2 pswap_pfresh_alpha pswap_pswap sw_diff sw_eqR u(3) zz(3))
       have a4: "alpha (pswap t2' u x2) (pswap (pswap t2' z x2) u z)" 
       by (metis alpha_pswap pswap_invol2 pswap_pfresh_alpha pswap_pswap sw_diff sw_eqR u(3) z(2))
       have a5: "alpha\<^sup>*\<^sup>* (pswap (pswap t2' z x2) u z) (pswap (pswap t3' z x3) u z)"
       by (simp add: alphaT_pswap z(4))
       have a6: "alpha (pswap (pswap t3' z x3) u z) (pswap t3' u x3)"
       by (metis alpha_pswap pswap_invol2 pswap_pfresh_alpha pswap_pswap sw_diff sw_eqR u(4) z(3))
       from a1 a2 a3 a4 a5 a6 have a: "alpha\<^sup>*\<^sup>* (pswap t1' u x1) (pswap t3' u x3)" by auto
       show "\<exists>z. z \<notin> {x1,x3} \<and> pfresh z t1' \<and> pfresh z t3' \<and> alpha\<^sup>*\<^sup>* (pswap t1' z x1) (pswap t3' z x3)"
       apply(rule exI[of _ u]) using u a by auto
     qed
   qed 
  } 
  thus ?thesis using assms by metis
qed

lemma alphaT_cases: assumes "alpha\<^sup>*\<^sup>* t t'"
shows 
 "(\<exists>x x'. t = PVr x' \<and> t' = PVr x') \<or> 
  (\<exists>t1 t2 t1' t2'. t = PAp t1 t2 \<and> t' = PAp t1' t2') \<or> 
  (\<exists>x tt x' tt'. t = PLm x tt \<and> t' = PLm x' tt')"
using assms apply induct apply auto
using ptrm.exhaust_sel by blast

lemma alphaT_alpha: 
assumes "alpha\<^sup>*\<^sup>* t1 t2" shows "alpha t1 t2"
using assms apply(coinduct) subgoal for t1 t2
apply(frule alphaT_cases) apply auto
  using alphaT_PVr apply blast  
  using alphaT_PVr apply blast  
  using alphaT_Lm_pfresh by blast .

lemma alpha_trans:
assumes "alpha t t'" and "alpha t' t''" 
shows "alpha t t''"
using alphaT_alpha by (meson assms rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)

(* *)

lemma alpha_PLm_strong_elim: 
assumes "alpha (PLm x t) (PLm x' t')"
and "z = x \<or> pfresh z t" and "z = x' \<or> pfresh z t'"
shows "alpha (pswap t z x) (pswap t' z x')"
proof-
  obtain zz where zz: "zz = x \<or> pfresh zz t" "zz = x' \<or> pfresh zz t'"
    "alpha (pswap t zz x) (pswap t' zz x')"
    using alpha_PLm_cases[OF assms(1)] by (smt ptrm.inject(3))
  have sw1: "alpha (pswap t z x) (pswap (pswap t zz x) zz z)"
  unfolding pswap_pswap[of t zz x] 
  by (metis alpha_refl alpha_pswap assms(2) 
   sw_diff sw_eqL sw_eqR pswap_pfresh_alpha pswap_id pswap_invol pswap_sym zz(1))
  have sw2: "alpha (pswap (pswap t' zz x') zz z) (pswap t' z x')"
  unfolding pswap_pswap[of t' zz x'] 
  by (metis alpha_refl alpha_pswap assms(3) sw_diff sw_eqL sw_eqR 
     pswap_pfresh_alpha pswap_id pswap_invol pswap_sym zz(2))
  show ?thesis
  by (meson alpha_pswap alpha_trans sw1 sw2 zz(3))
qed

lemma pfresh_pswap_alpha: 
assumes "y = x \<or> pfresh y t" and "z = x \<or> pfresh z t"
shows "alpha (pswap (pswap t y x) z y) (pswap t z x)"
by (smt assms pswap_pswap alpha_refl alpha_pswap sw_diff sw_eqR pswap_pfresh_alpha pswap_id pswap_invol2)

lemma pfresh_sw_pswap_pswap: 
assumes "sw y' z1 z2 \<noteq> y" and "y = sw x z1 z2 \<or> pfresh y (pswap t z1 z2)"
and "y' = x \<or> pfresh y' t"  
shows "pfresh (sw y' z1 z2) (pswap (pswap t z1 z2) y (sw x z1 z2))"
using assms pfresh_pswap_iff sw_diff sw_eqR sw_invol by smt


(* Strong inversion for alpha: *)

lemma alpha_cases_strong': 
assumes a: "alpha a1 a2" and A: "countable A" and b: 
"(\<And>x. a1 = PVr x \<Longrightarrow> a2 = PVr x \<Longrightarrow> P)"
"(\<And>s s' t t'. a1 = PAp s t \<Longrightarrow> a2 = PAp s' t' \<Longrightarrow> alpha s s' \<Longrightarrow> alpha t t' \<Longrightarrow> P)"
"(\<And>z x t x' t'. a1 = PLm x t \<Longrightarrow> a2 = PLm x' t' \<Longrightarrow> z \<notin> {x,x'} \<Longrightarrow> z \<notin> A  \<Longrightarrow> pfresh z t \<Longrightarrow> pfresh z t' \<Longrightarrow>
 alpha (pswap t z x) (pswap t' z x') \<Longrightarrow> P)" 
shows P
using a proof cases
  case (PVr x)
  then show ?thesis using b(1) by auto
next
  case (PAp s s' t t')
  then show ?thesis using b(2) by auto
next
  case (PLm z x t x' t')
  have "countable (A \<union> {x,x',z} \<union> {x. \<not> pfresh x t} \<union> {x. \<not> pfresh x t'})"
  by (simp add: A cocountable_pfresh) 
  then obtain zz where zz: "zz \<notin> {x,x',z}" "pfresh zz t" "pfresh zz t'" "zz \<notin> A"
  by (smt (verit, best) UnI1 UnI2 exists_var mem_Collect_eq) 
  show ?thesis apply(rule b(3)[where z = zz and x = x and t = t and t' = t']) using PLm zz  
    using alpha_pswap a alpha_PLm_strong_elim by auto
qed

lemma alpha_cases_strong'': 
assumes a: "alpha a1 a2" and b: 
"(\<And>x. a1 = PVr x \<Longrightarrow> a2 = PVr x \<Longrightarrow> P)"
"(\<And>s s' t t'. a1 = PAp s t \<Longrightarrow> a2 = PAp s' t' \<Longrightarrow> alpha s s' \<Longrightarrow> alpha t t' \<Longrightarrow> P)"
and c: 
"(\<And>z x t x' t'. a1 = PLm x t \<Longrightarrow> a2 = PLm x' t' \<Longrightarrow> z \<notin> {x,x'} \<Longrightarrow> 
  z \<notin> set xs \<Longrightarrow> (\<forall>t\<in>set ts. pfresh z t)  \<Longrightarrow> pfresh z t \<Longrightarrow> pfresh z t' \<Longrightarrow> 
 alpha (pswap t z x) (pswap t' z x') \<Longrightarrow> P)"
shows "P" 
proof-
  have 1: "countable (set xs \<union> (\<Union>t\<in>set ts. {x. \<not> pfresh x t}))"
  by (metis List.finite_set cocountable_pfresh countable_UN countable_Un uncountable_infinite)
  show ?thesis  
  using alpha_cases_strong'[OF a 1 b] c by auto
qed



(*********************)
(* (Infinitary) terms via quotienting pre-(infinitary) terms *)


quotient_type trm = ptrm / alpha
  unfolding equivp_def fun_eq_iff using alpha_sym alpha_trans alpha_refl by blast

(* Lifted concepts, from terms to tterms: *)
lift_definition Vr :: "var \<Rightarrow> trm" is PVr .
lift_definition Ap :: "trm \<Rightarrow> trm \<Rightarrow> trm" is PAp by auto
lift_definition Lm :: "var \<Rightarrow> trm \<Rightarrow> trm" is PLm by auto
lift_definition swap :: "trm \<Rightarrow> var \<Rightarrow> var \<Rightarrow> trm" is pswap 
  using alpha_pswap by auto
lift_definition fresh :: "var \<Rightarrow> trm \<Rightarrow> bool" is pfresh
  using alpha_pfresh_iff by blast
(*lift_definition ddepth :: "trm \<Rightarrow> nat" is depth
  using alpha_same_depth by blast *)

lift_definition is_Vr :: "trm \<Rightarrow> bool" is is_PVr  
unfolding is_PVr_def by fastforce
lift_definition is_Ap :: "trm \<Rightarrow> bool" is is_PAp  
unfolding is_PAp_def by fastforce
lift_definition is_Lm :: "trm \<Rightarrow> bool" is is_PLm  
unfolding is_PLm_def using alpha.cases by fastforce

lift_definition getVr :: "trm \<Rightarrow> var" is getPVr  
unfolding getPVr_def by (auto split: ptrm.splits)
lift_definition getApL :: "trm \<Rightarrow> trm" is getPApL  
unfolding getPApL_def by (auto split: ptrm.splits)
lift_definition getApR :: "trm \<Rightarrow> trm" is getPApR  
unfolding getPApR_def by (auto split: ptrm.splits)
definition getAp where "getAp t \<equiv> (getApL t, getApR t)" 

definition getLm :: "trm \<Rightarrow> (var \<times> trm) set" where 
"getLm t \<equiv> {(x,s) . t = Lm x s}" 

lemma Vr_getVr[simp]: "is_Vr t \<Longrightarrow> Vr (getVr t) = t"
apply transfer by simp

lemma Ap_getApL_getApR[simp]: "is_Ap t \<Longrightarrow> Ap (getApL t) (getApR t) = t"
apply transfer by simp

lemma Ap_getAp[simp]: "is_Ap t \<Longrightarrow> getAp t = (t1,t2) \<Longrightarrow> Ap t1 t2 = t"
unfolding getAp_def by auto

lemma Lm_getLm[simp]: "is_Lm t \<Longrightarrow> (x,t') \<in> getLm t \<Longrightarrow> Lm x t' = t"
unfolding getLm_def by auto

lemma trm_is_nchotomy: "is_Vr t \<or> is_Ap t \<or> is_Lm t"
apply transfer using pswap.exhaust by blast

term abs_trm
term rep_trm

lemma [simp]: "abs_trm (rep_trm t) = t"  
  by (meson Quotient3_abs_rep Quotient3_trm)

lemma [simp,intro!]: "alpha (rep_trm (abs_trm t)) t" 
  by (simp add: Quotient3_trm rep_abs_rsp_left)

lemma [simp]: "pfresh z (rep_trm (abs_trm t)) \<longleftrightarrow> pfresh z t"
  using fresh.abs_eq fresh.rep_eq by auto

lemma swap_idem[simp]:
"swap (swap t z x) z x = t"
  by transfer simp

lemma fresh_PVr[simp]: "fresh x (Vr y) \<longleftrightarrow> x \<noteq> y" 
	by (simp add: Vr_def fresh.abs_eq)

lemma fresh_Ap[simp]: "fresh z (Ap t1 t2) \<longleftrightarrow> fresh z t1 \<and> fresh z t2"
  by transfer auto

lemma fresh_Lm[simp]: "fresh z (Lm x t) \<longleftrightarrow> (z = x \<or> fresh z t)"
  by transfer auto

lemma Lm_swap_rename: 
assumes "z = x \<or> fresh z t "
shows "Lm z (swap t z x) = Lm x t" 
using assms apply transfer 
  using alpha.PLm by auto 

lemma abs_trm_PVr: "abs_trm (PVr x) = Vr x"
  by (simp add: Vr.abs_eq)

lemma abs_trm_PAp: "abs_trm (PAp t1 t2) = Ap (abs_trm t1) (abs_trm t2)"
  by (simp add: Ap.abs_eq)

lemma abs_trm_PLm: "abs_trm (PLm x t) = Lm x (abs_trm t)"
  by (simp add: Lm.abs_eq)

lemma abs_trm_pswap: "abs_trm (pswap t z1 z2) = swap (abs_trm t) z1 z2"
  by (simp add: swap.abs_eq)

lemma swap_Vr[simp]: "swap (Vr x) z1 z2 = Vr (sw x z1 z2)"
  apply transfer by simp 

lemma swap_Ap[simp]: "swap (Ap t1 t2) z1 z2 = Ap (swap t1 z1 z2) (swap t2 z1 z2)"
  apply transfer by simp

lemma swap_Lm[simp]: "swap (Lm x t) z1 z2 = Lm (sw x z1 z2) (swap t z1 z2)"
  apply transfer by simp 

lemma Lm_sameVar_inj[simp]: "Lm x t = Lm x t1 \<longleftrightarrow> t = t1" 
apply(transfer) by (metis alpha.PLm alpha_PLm_strong_elim pswap_id)

lemma Lm_eq_swap: 
assumes "Lm x t = Lm x1 t1"
shows "t = swap t1 x x1" 
proof(cases "x = x1")
  case True
  thus ?thesis using assms Lm_swap_rename by fastforce
next
  case False
  thus ?thesis  
  	by (metis Lm_sameVar_inj Lm_swap_rename assms fresh_Lm)
qed

lemma alpha_rep_abs_trm: "alpha (rep_trm (abs_trm t)) t" 
  by simp

lemma swap_fresh_eq: assumes x:"fresh x t" and y:"fresh y t"
  shows "swap t x y = t"
  using pswap_pfresh_alpha x y unfolding fresh.rep_eq
  by (metis (full_types) Quotient3_abs_rep Quotient3_trm swap.abs_eq trm.abs_eq_iff)

lemma bij_sw:"bij (\<lambda> x. sw x z1 z2)"
  unfolding sw_def bij_def inj_def surj_def by smt

lemma sw_set: "x \<in> X = ((sw x z1 z2) \<in> (\<lambda> x. sw x z1 z2) ` X)"
  using bij_sw by blast

(* *)

thm ptrm.exhaust[no_vars]

lemma trm_nchotomy: 
"(\<exists>x. tt = Vr x) \<or> (\<exists>t1 t2. tt = Ap t1 t2) \<or> (\<exists>x t. tt = Lm x t)"
apply transfer using ptrm.nchotomy by (metis alpha_refl ptrm.exhaust) 

lemma trm_exhaust[case_names Vr Ap Lm, cases type: trm]:
"(\<And>x. tt = Vr x \<Longrightarrow> P) \<Longrightarrow>
(\<And>t1 t2. tt = Ap t1 t2 \<Longrightarrow> P) \<Longrightarrow> (\<And>x t. tt = Lm x t \<Longrightarrow> P) \<Longrightarrow> P"
using trm_nchotomy by blast

lemmas trm_cases = trm_exhaust

lemma Vr_Ap_diff[simp]: "Vr x \<noteq> Ap t1 t2"  "Ap t1 t2 \<noteq> Vr x" 
by (transfer,blast)+ 

lemma Vr_Lm_diff[simp]: "Vr x \<noteq> Lm y t"  "Lm y t \<noteq> Vr x" 
apply (metis Lm.abs_eq Quotient3_abs_rep Quotient3_trm Vr.abs_eq alpha_PVr_eq alpha_eq_PVr alpha_rep_abs_trm ptrm.distinct(3))
by (transfer,blast)

lemma Ap_Lm_diff[simp]: "Ap t1 t2 \<noteq> Lm y t"  "Lm y t \<noteq> Ap t1 t2" 
	by (transfer,blast)+

lemma Vr_inj[simp]: "(Vr x = Vr y) \<longleftrightarrow> x = y"  
apply transfer by auto

lemma Ap_inj[simp]: "(Ap t1 t2 = Ap t1' t2') \<longleftrightarrow> t1 = t1' \<and> t2 = t2'"  
apply transfer by auto

(* free vars as abbreviation *)
abbreviation PFvars :: "ptrm \<Rightarrow> var set" where 
  "PFvars t \<equiv> {x. \<not> pfresh x t}"
abbreviation Fvars :: "trm \<Rightarrow> var set" where 
  "Fvars t \<equiv> {x. \<not> fresh x t}"
  
lemma countable_Fvars: "countable (Fvars t)"
  unfolding fresh.rep_eq using cocountable_pfresh by simp   

lemma exists_fresh_set:
assumes "countable X"
shows "\<exists> z. z \<notin> X \<and> z \<notin> set xs \<and> (\<forall>t \<in> set ts. fresh z t)"
using assms apply transfer 
	using exists_pfresh_set by presburger

definition pickFreshS :: "var set \<Rightarrow> var list \<Rightarrow> trm list \<Rightarrow> var" where 
"pickFreshS X xs ts \<equiv> SOME z. z \<notin> X \<and> z \<notin> set xs \<and> 
                 (\<forall>t \<in> set ts. fresh z t)" 

lemma pickFreshS: 
assumes "countable X"
shows 
"pickFreshS X xs ts \<notin> X \<and> 
 pickFreshS X xs ts \<notin> set xs \<and> 
 (\<forall>t \<in> set ts. fresh (pickFreshS X xs ts) t)"
using exists_fresh_set[OF assms] unfolding pickFreshS_def 
  by (rule someI_ex)

lemmas pickFreshS_set = pickFreshS[THEN conjunct1]
and pickFreshS_var = pickFreshS[THEN conjunct2, THEN conjunct1]
and pickFreshS_ptrm = pickFreshS[THEN conjunct2, THEN conjunct2, unfolded Ball_def, rule_format]

(* Unconditional form of pick-fresh, without any set: *)
definition "pickFresh \<equiv> pickFreshS {}"

lemmas pickFresh_var = pickFreshS_var[OF countable_empty, unfolded pickFresh_def[symmetric]]
and pickFresh_ptrm = pickFreshS_ptrm[OF countable_empty, unfolded pickFresh_def[symmetric]]

(* Interestingly, this nominal-style charactTranserization of freshness works for 
now works countability instead of finiteness (i.e., one cardinal-level up) *)
lemma fresh_swap_nominal_style: 
"fresh x t \<longleftrightarrow> countable {y. swap t y x \<noteq> t}"
proof
  assume "fresh x t"
  hence "{y. swap t y x \<noteq> t} \<subseteq> {y. \<not> fresh y t}"
  	by (auto, meson swap_fresh_eq)
  thus "countable {y. swap t y x \<noteq> t}"  
  	using countable_Fvars countable_subset by blast
next
  assume "countable {y. swap t y x \<noteq> t}"
  moreover have "countable {y. \<not> fresh y t}" using countable_Fvars .
  ultimately have "countable ({y. \<not> fresh y t} \<union> {y. swap t y x \<noteq> t} \<union> {x})"
  by blast
  hence "countable {y. \<not> fresh y t \<or> swap t y x \<noteq> t \<or> y = x}" 
  by (smt (verit) UnCI countable_subset insert_iff mem_Collect_eq subsetI) 
  then obtain y where "fresh y t" and "y \<noteq> x" and "swap t y x = t" 
  using exists_var by auto
  thus "fresh x t" by (metis Lm_swap_rename fresh_Lm)
qed

(* Fresh cases: *)
thm cocountable_pfresh

lemma trm_nchotomy_fresh_countable: 
assumes A: "countable A" 
shows "(\<exists>x. tt = Vr x) \<or> (\<exists>t1 t2. tt = Ap t1 t2) \<or> (\<exists>x t. x \<notin> A \<and> tt = Lm x t)"
proof(cases tt)
  case (Vr x)
  then show ?thesis by auto
next
  case (Ap t1 t2)
  then show ?thesis by auto
next
  case (Lm x t)
  have "countable (A \<union> {x} \<union> {z. \<not> fresh z t})"  
    by (simp add: A countable_Fvars) 
  then obtain z where z: "z \<notin> A" "z \<noteq> x" "fresh z t"  
    by (metis (no_types, lifting) UnCI exists_var insert_iff mem_Collect_eq)   
  show ?thesis apply(intro disjI2 exI[of _ z] exI[of _ "swap t z x"])
  using Lm z Lm_swap_rename by auto
qed

lemma trm_nchotomy_fresh: 
"(\<exists>x. tt = Vr x) \<or> (\<exists>t1 t2. tt = Ap t1 t2) \<or> (\<exists>x t. x \<notin> set xs \<and> (\<forall>t\<in>set ts. fresh x t) \<and> tt = Lm x t)"
proof-
  have "countable (set xs \<union> (\<Union>t\<in>set ts. {u. \<not> fresh u t}))"
  by (metis List.finite_set countable_Fvars countable_UN countable_Un uncountable_infinite)
  from trm_nchotomy_fresh_countable[OF this]
  show ?thesis by auto
qed

lemma trm_cases_fresh_countable[consumes 1, case_names Vr Ap Lm]:
"countable A \<Longrightarrow> 
 (\<And>x. tt = Vr x \<Longrightarrow> P) \<Longrightarrow>
 (\<And>t1 t2. tt = Ap t1 t2 \<Longrightarrow> P) \<Longrightarrow> 
 (\<And>x t. x \<notin> A \<Longrightarrow> tt = Lm x t \<Longrightarrow> P) \<Longrightarrow> P"
using trm_nchotomy_fresh_countable by metis

lemma trm_cases_fresh[case_names Vr Ap Lm, cases type: trm]:
"(\<And>x. tt = Vr x \<Longrightarrow> P) \<Longrightarrow>
 (\<And>t1 t2. tt = Ap t1 t2 \<Longrightarrow> P) \<Longrightarrow> 
 (\<And>x t. x \<notin> set xs \<Longrightarrow> (\<forall>t\<in>set ts. fresh x t) \<Longrightarrow> tt = Lm x t \<Longrightarrow> P) \<Longrightarrow> P"
using trm_nchotomy_fresh by metis

(* *)

thm ptrm.coinduct[no_vars]
thm alpha.coinduct[of R t1 t2]

(* Compatibility of unary and binary predicates with alpha-equivalence 
(needed for proving stronger coinduction rules for term equality and freshness): *)
definition "compatAlpha1 P \<equiv> \<forall>t s. P t \<and> alpha t s \<longrightarrow> P s" 
definition "compatAlpha2 R \<equiv> \<forall>t t' s s'. R t t' \<and> alpha t s \<and> alpha t' s' \<longrightarrow> R s s'"

lemma alpha_coinduct_strong[consumes 1]: 
(* need to replace all term equalities with alpha, to obtain a suitable coinduction for 
equality on the quotient type *)
assumes R: "R t t'" and c: "compatAlpha2 R"
and b: "\<And>tt tt'.
    R tt tt' \<Longrightarrow>
    (\<exists>x. alpha tt (PVr x) \<and> alpha tt' (PVr x)) \<or>
    (\<exists>s s' t t'. alpha tt (PAp s t) \<and> alpha tt' (PAp s' t') \<and> (R s s' \<or> alpha s s') \<and> (R t t' \<or> alpha t t')) \<or>
    (\<exists>z x t x' t'.
        alpha tt (PLm x t) \<and>
        alpha tt' (PLm x' t') \<and> (z = x \<or> pfresh z t) \<and> (z = x' \<or> pfresh z t') \<and> 
        (R (pswap t z x) (pswap t' z x') \<or> alpha (pswap t z x) (pswap t' z x')))"
shows "alpha t t'" 
using R apply(coinduct)
subgoal for t t' apply(drule b) apply(elim disjE exE)
  subgoal for x apply(rule disjI1) by auto
  subgoal for ss ss' tt tt' apply(rule disjI2, rule disjI1) 
    by (smt (verit, ccfv_threshold) alpha_PAp_cases2 c compatAlpha2_def trm.abs_eq_iff)
  subgoal for z x tt x' tt' apply(rule disjI2, rule disjI2) 
  apply(cases t)
    subgoal by auto
    subgoal by auto
    subgoal apply(cases t')
      subgoal by auto
      subgoal by auto
      subgoal apply simp 
        by (smt (verit, ccfv_SIG) Quotient3_def Quotient3_trm alpha_PLm_strong_elim 
       alpha_pfresh_iff c compatAlpha2_def pfresh_simps(3)) . . . .

theorem trm_coind[consumes 1]: 
assumes R: "R t t'"
and b: "\<And>tt tt'.
    R tt tt' \<Longrightarrow>
    (\<exists>x. tt = Vr x \<and> tt' = Vr x) \<or>
    (\<exists>s s' t t'. tt = Ap s t \<and> tt' = Ap s' t' \<and> (R s s' \<or> s = s') \<and> (R t t' \<or> t = t')) \<or>
    (\<exists>z x t x' t'.
        tt = Lm x t \<and> tt' = Lm x' t' \<and> (z = x \<or> fresh z t) \<and> (z = x' \<or> fresh z t') \<and> 
        (R (swap t z x) (swap t' z x') \<or> swap t z x = swap t' z x'))"
shows "t = t'" 
proof-
  obtain pt pt' where 0: "pt = rep_trm t \<and> pt' = rep_trm t'" by auto
  have "R (abs_trm pt) (abs_trm pt')"
  using R by (simp add: "0")
  hence "alpha pt pt'" 
  apply(coinduct rule: alpha_coinduct_strong) 
  subgoal unfolding compatAlpha2_def by (metis trm.abs_eq_iff)
  subgoal for pt pt' apply(drule b) apply(elim disjE exE)
    subgoal for x apply(rule disjI1)
      by (metis Vr.abs_eq alpha_PVr_eq alpha_eq_PVr alpha_rep_abs_trm)
    subgoal for s s' t t' apply(rule disjI2, rule disjI1) unfolding swap_def Ap_def 
    apply simp unfolding trm.abs_eq_iff 
      by (metis Quotient3_abs_rep Quotient3_trm alpha_refl) 
    subgoal for z x t x' t' apply(rule disjI2, rule disjI2)
      unfolding swap_def fresh_def Lm_def  apply simp unfolding trm.abs_eq_iff 
      by blast . .
  thus ?thesis 
    using "0" Quotient3_rel_rep Quotient3_trm by fastforce
qed


(* The natural high-level coinduction for fresh is suprisingly difficult to 
prove: we need an entire saga. *)

thm pfresh.coinduct[of R t1 t2]

thm alpha.cases[no_vars]
  
inductive pswapConnect :: "var \<Rightarrow> ptrm \<Rightarrow> ptrm \<Rightarrow> bool" where 
Refl: "pswapConnect z t t"
|
Step: "pswapConnect z t t' \<Longrightarrow> z \<notin> {x,y} \<Longrightarrow> pswapConnect z t (pswap t' x y)"

lemma pswapConnec_pfresh: "pswapConnect z t t' \<Longrightarrow> pfresh z t \<longleftrightarrow> pfresh z t'"
apply(induct rule: pswapConnect.induct) by (simp_all add: pfresh_pswap_iff)

lemma pswapConnec_trans: 
assumes "pswapConnect z t t'" "pswapConnect z t' t''" shows "pswapConnect z t t''"
using assms(2,1) apply(induct rule: pswapConnect.induct)
using Step by auto

lemma PVr_pswapConnect: 
assumes "pswapConnect z (PVr x) t'" 
shows "\<exists>x'. t' = PVr x' \<and> (x \<noteq> z \<longleftrightarrow> x' \<noteq> z)"
proof-
  {fix t assume "pswapConnect z t t'"
   then have "\<forall>x. t = PVr x \<longrightarrow> (\<exists>x'. t' = PVr x' \<and> (x \<noteq> z \<longleftrightarrow> x' \<noteq> z))"
   apply induct by (auto simp: sw_def)
  }
  thus ?thesis using assms by auto
qed

lemma PAp_pswapConnect: 
assumes "pswapConnect z (PAp t1 t2) t'" 
shows "\<exists>t1' t2'. t' = PAp t1' t2' \<and> pswapConnect z t1 t1' \<and> pswapConnect z t2 t2'"
proof-
  {fix t assume "pswapConnect z t t'"
   then have "\<forall>t1 t2. t = PAp t1 t2 \<longrightarrow> 
        (\<exists>t1' t2'. t' = PAp t1' t2' \<and> pswapConnect z t1 t1' \<and> pswapConnect z t2 t2')"
   apply induct by (auto simp: pswapConnect.intros) 
  }
  thus ?thesis using assms by auto
qed

lemma PLm_pswapConnect: 
assumes "pswapConnect z (PLm x t1) t'" 
shows "\<exists>x' t1'. t' = PLm x' t1' \<and> pswapConnect z t1 t1' \<and> (x \<noteq> z \<longleftrightarrow> x' \<noteq> z)"
proof-
  {fix t assume "pswapConnect z t t'"
   then have "\<forall>x t1. t = PLm x t1 \<longrightarrow> 
        (\<exists>x' t1'. t' = PLm x' t1' \<and> pswapConnect z t1 t1' \<and> (x \<noteq> z \<longleftrightarrow> x' \<noteq> z))"
   apply induct by (auto simp: pswapConnect.intros sw_def)  
  }
  thus ?thesis using assms by auto
qed

lemma pfresh_coinduct_strong[consumes 1]: 
assumes R: "R x t" and cc: "\<And>x. compatAlpha1 (R x)"
and bb: "\<And>xx tt.
    R xx tt \<Longrightarrow>
    (\<exists>z x. xx = z \<and> alpha tt (PVr x) \<and> z \<noteq> x) \<or>
    (\<exists>z t1 t2. xx = z \<and> alpha tt (PAp t1 t2) \<and> (R z t1 \<or> pfresh z t1) \<and> (R z t2 \<or> pfresh z t2)) \<or>
    (\<exists>z x t. xx = z \<and> alpha tt (PLm x t) \<and> (z = x \<or> R z t \<or> pfresh z t))"
shows "pfresh x t"
proof-
  define Q where "Q \<equiv> \<lambda>z t. \<exists>t'. pswapConnect z t t' \<and> R z t'"
  {assume "Q x t" 
   hence ?thesis proof(coinduct)
     case (pfresh u t)
     then obtain t' where tt': "pswapConnect u t t'" and R: "R u t'" unfolding Q_def by auto
     then show ?case proof(cases t)
       case (PVr x)
       obtain x' where t': "t' = PVr x'" and xx': "x \<noteq> u \<longleftrightarrow> x' \<noteq> u"
       using PVr_pswapConnect[OF tt'[unfolded PVr]] by auto
       then show ?thesis apply-apply(rule disjI1) 
       unfolding PVr using bb[OF R] by auto
     next
       case (PAp t1 t2)
       obtain t1' t2' where t': "t' = PAp t1' t2'" 
       and tt1': "pswapConnect u t1 t1'" and tt2': "pswapConnect u t2 t2'"
       using PAp_pswapConnect[OF tt'[unfolded PAp]] by auto
       show ?thesis unfolding PAp apply-apply(rule disjI2, rule disjI1, simp) apply(rule conjI)
         subgoal unfolding Q_def using bb[OF R] tt' unfolding t' using tt1' apply simp 
         by (metis alpha_PAp_cases alpha_pfresh_iff alpha_sym cc compatAlpha1_def 
           pswapConnec_pfresh ptrm.distinct(5) ptrm.sel(2))
         subgoal unfolding Q_def using bb[OF R] tt' unfolding t' using tt1' apply simp 
         by (metis alpha_PAp_cases alpha_pfresh_iff alpha_sym cc compatAlpha1_def 
           pswapConnec_pfresh ptrm.distinct(5) ptrm.inject(2) tt2') . 
     next
       case (PLm x t1)
       obtain x' t1' where t': "t' = PLm x' t1'" 
       and tt1': "pswapConnect u t1 t1'" and "x' \<noteq> u \<longleftrightarrow> x \<noteq> u"
       using PLm_pswapConnect[OF tt'[unfolded PLm]] by auto
       {assume 0: "u \<noteq> x" "\<not> pfresh u t1" 
        obtain xx' tt1' where al: "alpha t' (PLm xx' tt1')" and 1: "(u = xx' \<or> R u tt1' \<or> pfresh u tt1')"
        using bb[OF R, simplified, unfolded t'] t' by auto
        hence 1: "R u tt1'"  
          by (metis "0"(1) "0"(2) alpha_pfresh_iff local.PLm pfresh_simps(3) pswapConnec_pfresh tt')
        obtain z where z: "z \<notin> {x,x',xx',u}" "pfresh z t1'" "pfresh z tt1'"
        and 2: "alpha (pswap t1' z x') (pswap tt1' z xx')" 
        using al unfolding t' apply-apply(erule alpha_cases_strong''[where xs = "[x,x',xx',u]" and ts = "[t1',tt1']"])
        by auto
        define T1' where T1': "T1' \<equiv> pswap (pswap t1' z x') z xx'"
        have al: "alpha T1' tt1'"
        using 2 unfolding T1' by (metis alpha_pswap pswap_invol)
        have "pswapConnect u t1' T1'" unfolding T1'  
        by (smt (verit, del_insts) "0"(1) "0"(2) Refl Step T1' \<open>(x' \<noteq> u) = (x \<noteq> u)\<close> al 
        alpha_pfresh_iff insertE pfresh_pswap_iff pswapConnec_pfresh singletonD sw_eqL tt1' z(2) z(3))
        hence 3: "pswapConnect u t1 T1'" 
        using tt1' pswapConnec_trans by blast
        have 4: "R u T1'" using 1 al  
          by (meson alpha_sym cc compatAlpha1_def)
        have "\<exists>t1'. pswapConnect u t1 t1' \<and> R u t1'" using 3 4 by auto
       }
       thus ?thesis unfolding PLm apply-apply(rule disjI2, rule disjI2, simp) 
       subgoal unfolding Q_def by auto .
     qed
   qed
  }
  thus ?thesis using R unfolding Q_def using pswapConnect.Refl by blast
qed

theorem fresh_coind[consumes 1]: 
assumes R: "R x t"  
and b: "\<And>xx tt.
    R xx tt \<Longrightarrow>
    (\<exists>x. tt = Vr x \<and> xx \<noteq> x) \<or>
    (\<exists>t1 t2. tt = Ap t1 t2 \<and> (R xx t1 \<or> fresh xx t1) \<and> (R xx t2 \<or> fresh xx t2)) \<or>
    (\<exists>x t. tt = Lm x t \<and> (xx = x \<or> R xx t \<or> fresh xx t))"
shows "fresh x t"
proof-
  obtain pt where 0: "pt = rep_trm t" by auto
  have "R x (abs_trm pt)"
  using R by (simp add: "0")
  hence "pfresh x pt" 
  apply(coinduct rule: pfresh_coinduct_strong) 
  subgoal unfolding compatAlpha1_def by (metis trm.abs_eq_iff)
  subgoal for xx pt apply(drule b) apply(elim disjE exE)
    subgoal for x apply(rule disjI1)
      by (metis Vr.abs_eq alpha_PVr_eq alpha_eq_PVr alpha_rep_abs_trm)
    subgoal for s t apply(rule disjI2, rule disjI1) unfolding swap_def Ap_def fresh_def
    apply simp unfolding trm.abs_eq_iff 
      by (metis Quotient3_abs_rep Quotient3_trm) 
    subgoal for x t apply(rule disjI2, rule disjI2)
      unfolding swap_def fresh_def Lm_def apply simp unfolding trm.abs_eq_iff 
      by fastforce . .
  thus ?thesis 
  using "0" fresh.rep_eq by blast 
qed

(* end saga *)

(**********************)

(* Substitution *)

(* NB: This is definable using swapping-based recursion, 
but we define it here "by hand" so that we do not introduce dependency from 
the swapping-based models, and thus keep all properties of terms in one theory. 
(This is a decision informed by formal engineering rather than mathematical elegance.)
*)

coinductive substRel :: "trm \<Rightarrow> trm \<Rightarrow> var \<Rightarrow> trm \<Rightarrow> bool" where 
 substRel_Vr_same: 
"substRel (Vr x) s x s"
|substRel_Vr_diff: 
"x \<noteq> y \<Longrightarrow> substRel (Vr x) s y (Vr x)"
|substRel_Ap: 
"substRel t1 s y t1' \<Longrightarrow> substRel t2 s y t2' \<Longrightarrow>
 substRel (Ap t1 t2) s y (Ap t1' t2')"
|substRel_Lm: 
"x \<noteq> y \<Longrightarrow> fresh x s \<Longrightarrow> substRel t s y t' \<Longrightarrow> 
 substRel (Lm x t) s y (Lm x t')"

lemma substRel_Vr_invert: 
assumes "substRel (Vr x) t y t'" 
shows "(x = y \<and> t = t') \<or> (x \<noteq> y \<and> t' = Vr x)"
using assms by (cases rule: substRel.cases) auto

lemma substRel_Ap_invert: 
assumes "substRel (Ap t1 t2) s y t'" 
shows "\<exists>t1' t2'. t' = Ap t1' t2' \<and> substRel t1 s y t1' \<and> substRel t2 s y t2'"
using assms by (cases rule: substRel.cases) auto

lemma substRel_Lm_invert_aux: 
assumes "substRel (Lm x t) s y tt'" 
shows "\<exists>x1 t1 t1'. 
  x1 \<noteq> y \<and> fresh x1 s \<and> 
  Lm x t = Lm x1 t1 \<and> tt' = Lm x1 t1' \<and> substRel t1 s y t1'"
using assms by (cases rule: substRel.cases) auto

lemma fresh_sw_swap[simp]: "fresh (sw x z1 z2) (swap s z1 z2) \<longleftrightarrow> fresh x s"
apply transfer by auto 

lemma substRel_swap: 
assumes "substRel t s y tt" 
shows "substRel (swap t z1 z2) (swap s z1 z2) (sw y z1 z2) (swap tt z1 z2)"
proof-
  {fix t' s' y' tt'
   assume "\<exists>t s y tt z1 z2. t' = swap t z1 z2 \<and> s' = swap s z1 z2 \<and> y' = sw y z1 z2 \<and> tt' = swap tt z1 z2
       \<and> substRel t s y tt"
   hence "substRel t' s' y' tt'"
   proof(coinduct rule: substRel.coinduct)
     case (substRel t' s' y' tt')
     then obtain t s y tt z1 z2 where 0: "t' = swap t z1 z2" 
     "s' = swap s z1 z2" "y' = sw y z1 z2" "tt' = swap tt z1 z2" 
     and sr: "substRel t s y tt" by auto
     from sr show ?case proof(cases)
       case substRel_Vr_same
       then show ?thesis apply-apply(rule disjI1) using 0 by auto
     next
       case (substRel_Vr_diff x)
       then show ?thesis apply-apply(rule disjI2, rule disjI1) using 0 by auto
     next
       case (substRel_Ap t1 t1' t2 t2')
       then show ?thesis apply-apply(rule disjI2, rule disjI2, rule disjI1) using 0 apply auto  
       by blast+
     next
       case (substRel_Lm x t1 t1')
       then show ?thesis apply-apply(rule disjI2, rule disjI2, rule disjI2) 
       apply(rule exI[of _ "sw x z1 z2"]) apply(rule exI[of _ "sw y z1 z2"])
       apply(rule exI[of _ "swap s z1 z2"]) 
       apply(rule exI[of _ "swap t1 z1 z2"]) apply(rule exI[of _ "swap t1' z1 z2"])
       using 0 apply auto
       by blast  
     qed
   qed
  }
  thus ?thesis using assms by metis
qed

lemma substRel_fresh: 
assumes "substRel t s y t'" and "fresh x1 t" "x1 \<noteq> y" "fresh x1 s" 
shows "fresh x1 t'"
proof-
  have "\<exists> t s y. substRel t s y t' \<and> fresh x1 t \<and> x1 \<noteq> y \<and> fresh x1 s"
  using assms by auto
  thus ?thesis
  apply(coinduct rule: fresh_coind) apply clarsimp
  subgoal for xx tt t s y apply(erule substRel.cases) apply auto
    apply (metis fresh_Ap fresh_Lm fresh_PVr trm_nchotomy)
    by blast . 
qed

lemma substRel_Lm_invert: 
assumes "substRel (Lm x t) s y tt'" and 0: "x \<noteq> y" "fresh x s"
shows "\<exists>t'. tt' = Lm x t' \<and> substRel t s y t'"
using substRel_Lm_invert_aux[OF assms(1)] proof(elim exE conjE)
  fix x1 t1 t1'
  assume 1: "x1 \<noteq> y" "fresh x1 s" "Lm x t = Lm x1 t1"
  "substRel t1 s y t1'" "tt' = Lm x1 t1'"
  have 2: "t = swap t1 x x1" by (simp add: "1"(3) Lm_eq_swap) 
  hence 3: "x = x1 \<or> fresh x t1"  
  	by (metis "1"(3) fresh_Lm) 
  have 4: "s = swap s x x1" "y = sw y x x1"
   apply (simp add: "1"(2) assms(3) swap_fresh_eq) 
   using "1"(1) assms(2) sw_def by presburger
  show ?thesis
  apply(rule exI[of _ "swap t1' x x1"], safe) 
    subgoal unfolding 1 apply(rule sym, rule Lm_swap_rename)
    using 3 substRel_fresh[OF 1(4) _ 0] by auto
    subgoal unfolding 2 apply(subst 4(1), subst 4(2)) 
    using substRel_swap[OF 1(4)] . . 
qed

(***********************)
(* The term destructor*) 
abbreviation (input) Vv :: "'a1 \<Rightarrow> 'a1 + 'a2 + 'a3" where "Vv \<equiv> Inl"
abbreviation (input) Aa :: "'a2 \<Rightarrow> 'a1 + 'a2 + 'a3" where "Aa \<equiv> Inr o Inl"
abbreviation (input) Ll :: "'a3 \<Rightarrow> 'a1 + 'a2 + 'a3" where "Ll \<equiv> Inr o Inr"
definition Dest :: "trm \<Rightarrow> var + trm \<times> trm + (var \<times> trm) set" where 
"Dest t \<equiv> 
 if is_Vr t then Vv (getVr t)
 else if is_Ap t then Aa (getAp t)
 else Ll (getLm t)"

lemma is_Vr_def2: "is_Vr t \<longleftrightarrow> (\<exists>x. t = Vr x)"
apply transfer unfolding is_PVr_def by auto
lemma is_Ap_def2: "is_Ap t \<longleftrightarrow> (\<exists>t1 t2. t = Ap t1 t2)"
apply transfer unfolding is_PAp_def by auto
lemma is_Lm_def2: "is_Lm t \<longleftrightarrow> (\<exists>x t'. t = Lm x t')"
apply transfer unfolding is_PLm_def by (meson alpha_PLm_cases alpha_refl alpha_sym)

lemma getLm_NE: "is_Lm t \<Longrightarrow> getLm t \<noteq> {}"
unfolding is_Lm_def2 getLm_def by auto

definition "getSomeL xs ts t \<equiv> SOME x_t'. x_t' \<in> getLm t \<and> fst x_t' \<notin> set xs \<and> (\<forall>t'\<in>set ts. fresh (fst x_t') t')"

lemma getSomeL: "is_Lm t \<Longrightarrow> 
getSomeL xs ts t \<in> getLm t \<and> fst (getSomeL xs ts t) \<notin> set xs \<and> (\<forall>t'\<in>set ts. fresh (fst (getSomeL xs ts t)) t')"
unfolding getSomeL_def 
apply(rule someI_ex) unfolding is_Lm_def2 getLm_def 
by simp (metis Ap_Lm_diff(1) Vr_Lm_diff(1) trm_cases_fresh)

lemma Lm_getSomeL: "is_Lm t \<Longrightarrow> getSomeL xs ts t = (x,t') \<Longrightarrow> t = Lm x t' \<and> x \<notin> set xs \<and> (\<forall>s\<in>set ts. fresh x s)"
using getSomeL by (metis Lm_getLm fst_conv)

definition "getSomeLV xs ts \<equiv> fst o getSomeL xs ts"
definition "getSomeLT xs ts \<equiv> snd o getSomeL xs ts"

lemma Lm_getSomeLV_getSomeLT: 
"is_Lm t \<Longrightarrow> Lm (getSomeLV xs ts t) (getSomeLT xs ts t) = t 
 \<and> getSomeLV xs ts t \<notin> set xs \<and> (\<forall>s\<in>set ts. fresh (getSomeLV xs ts t) s)"
by (metis Lm_getSomeL comp_def getSomeLT_def getSomeLV_def prod.exhaust_sel)

lemma Dest_Vv_Vr: "Dest t = Vv x \<longleftrightarrow> t = Vr x"
unfolding Dest_def apply(cases t, auto simp: is_Vr_def2)   
using Vr_getVr is_Vr_def2 by fastforce+

lemma Dest_Aa_Ap: "Dest t = Aa (t1,t2) \<longleftrightarrow> t = Ap t1 t2"
unfolding Dest_def apply(cases t, auto simp: is_Ap_def2)   
apply (metis Vr_Ap_diff(1) is_Vr_def2)
apply (metis Ap_getAp Ap_inj is_Ap_def2)
apply (metis Ap_getAp Ap_inj is_Ap_def2)
by (metis Ap_getApL_getApR Ap_inj getAp_def is_Ap_def2)

lemma Dest_Ll_Lm: "(\<exists>K. Dest t = Ll K \<and> (x,t') \<in> K) \<longleftrightarrow> t = Lm x t'"
unfolding Dest_def apply(cases t, simp_all)   
  using is_Vr_def2 apply blast
  using is_Ap_def2 apply blast
  by (simp add: getLm_def is_Ap_def2 is_Vr_def2)

(* *)

lemma fresh_Dest_Vr: "fresh z t \<Longrightarrow> Dest t = Vv x \<Longrightarrow> z \<noteq> x"
unfolding Dest_def apply(cases t, auto split: if_splits)
using getLm_NE unfolding is_Vr_def2 is_Ap_def2 is_Lm_def2 apply auto 
by (meson Vr_getVr Vr_inj is_Vr_def2)

lemma fresh_Dest_Ap: "fresh z t \<Longrightarrow> Dest t = Aa (t1, t2) \<Longrightarrow> fresh z t1 \<and> fresh z t2"
unfolding Dest_def apply(cases t, auto split: if_splits)
using getLm_NE unfolding is_Vr_def2 is_Ap_def2 is_Lm_def2 apply auto 
by (metis Ap_getAp fresh_Ap is_Ap_def2)+

lemma fresh_Dest_Lm: 
"fresh z t \<Longrightarrow> Dest t = Ll K \<Longrightarrow> (x,t') \<in> K \<Longrightarrow> 
 (z = x \<or> fresh z t')"
unfolding Dest_def apply(cases t, auto split: if_splits)
using getLm_NE unfolding is_Vr_def2 is_Ap_def2 is_Lm_def2 apply auto 
by (metis Lm_getLm fresh_Lm is_Lm_def2)+

lemma swap_Dest_Vr: "Dest t = Vv x \<Longrightarrow> Dest (swap t z1 z2) = Vv (sw x z1 z2)"
unfolding Dest_def apply(cases t, auto split: if_splits)
using getLm_NE unfolding is_Vr_def2 is_Ap_def2 is_Lm_def2 apply auto 
by (metis Vr_getVr Vr_inj is_Vr_def2)

lemma swap_Dest_Ap: "Dest t = Aa (t1,t2) \<Longrightarrow> 
  Dest (swap t z1 z2) = Aa (swap t1 z1 z2, swap t2 z1 z2)"
unfolding Dest_def apply(cases t, auto)
using getLm_NE unfolding is_Vr_def2 is_Ap_def2 is_Lm_def2 apply auto 
by (metis Ap_getApL_getApR Ap_inj Pair_inject getAp_def is_Ap_def2)

lemma swap_Dest_Lm: "Dest tt = Ll K \<Longrightarrow> 
  \<exists>K'. Dest (swap tt z1 z2) = Ll K' \<and>  
  (\<forall>x t. (x,t) \<in> K \<longrightarrow> (sw x z1 z2, swap t z1 z2) \<in> K')"
unfolding Dest_def apply(cases tt rule: trm_cases, auto)
using getLm_NE unfolding is_Vr_def2 is_Ap_def2 is_Lm_def2 apply auto 
by (smt (verit) getLm_def mem_Collect_eq old.prod.case swap_Lm)

lemma Dest_Lm_rename: 
"Dest tt = Ll K \<Longrightarrow> {(x,t),(x',t')} \<subseteq> K \<Longrightarrow> 
 (x' = x \<or> fresh x' t) \<and> swap t x' x = t'"
unfolding Dest_def apply(cases tt rule: trm_cases, auto)
using getLm_NE unfolding is_Vr_def2 is_Ap_def2 is_Lm_def2 apply auto 
apply (metis Lm_getLm fresh_Lm is_Lm_def2)
by (metis Lm_eq_swap Lm_getLm is_Lm_def2)

lemma Dest_Vr[simp]: "Dest (Vr x) = Vv x"
by (simp add: Dest_Vv_Vr)

lemma Dest_Ap[simp]: "Dest (Ap t1 t2) = Aa (t1,t2)"
using Dest_Aa_Ap by auto 

lemma Dest_Lm: "Dest (Lm x t) = Ll {(x',swap t x' x) | x' .  x' = x \<or> fresh x' t }"
using Dest_Ll_Lm[of "Lm x t"]  
unfolding Dest_def apply auto 
using is_Ap_def2 Lm_eq_swap Lm_swap_rename apply auto
by (metis fresh_Lm)

lemma Dest_Lm': "Dest (Lm x t) = Ll K \<Longrightarrow> (x,t) \<in> K"
unfolding Dest_Lm using Lm_eq_swap by auto

(* *)

primcorec presubst :: "trm \<Rightarrow> trm \<Rightarrow> var \<Rightarrow> ptrm" where 
"presubst t s y = 
 (if is_Vr t then if y = getVr t then rep_trm s else PVr (getVr t)
  else if is_Ap t then PAp (presubst (getApL t) s y) (presubst (getApR t) s y)
  else PLm (getSomeLV [y] [s] t) (presubst (getSomeLT [y] [s] t) s y)
 )"

lemma presubst_Vr[simp]: "presubst (Vr x) s y = (if y = x then rep_trm s else PVr x)"
apply(subst presubst.code) apply simp  
by (metis Vr_getVr Vr_inj is_Vr_def2)

lemma presubst_Ap: "presubst (Ap t1 t2) s y = PAp (presubst t1 s y) (presubst t2 s y)"
apply(subst presubst.code) apply simp  
by (metis Ap_getApL_getApR Ap_inj Vr_Ap_diff(1) is_Ap_def2 is_Vr_def2)

lemma presubst_Lm: "\<exists>x' t'. Lm x' t' = Lm x t \<and> x' \<noteq> y \<and> fresh x' s \<and> 
  presubst (Lm x t) s y = PLm x' (presubst t' s y)"
apply(subst presubst.code) apply simp  
by (metis Ap_Lm_diff(1) Ap_getApL_getApR Lm_getSomeLV_getSomeLT Vr_Lm_diff(1) Vr_getVr list.set_intros(1) trm_is_nchotomy)

lemma substRel_presubst: "substRel t s y (abs_trm (presubst t s y))"
proof-
  {fix tt assume tt: "tt = abs_trm (presubst t s y)"
   hence "substRel t s y tt" 
   proof(coinduct)
     case (substRel t s y tt) note tt = substRel
     show ?case proof(cases t rule: trm_cases_fresh[where xs = "[y]" and ts = "[s]"])
       case (Vr x)
       show ?thesis using tt unfolding Vr by (simp split: if_splits add: abs_trm_PVr) 
     next
       case (Ap t1 t2)
       then show ?thesis using tt unfolding Ap  
         by (simp add: abs_trm_PAp presubst_Ap)
     next
       case (Lm x1 t1)
       then obtain x' t' where 1: "t = Lm x' t'" "x' \<noteq> y \<and> fresh x' s"
       "presubst t s y = PLm x' (presubst t' s y)"   
       using presubst_Lm  by metis
       show ?thesis using tt[unfolded 1(3)] apply(intro disjI2)
       apply(rule exI[of _ x']) apply(rule exI[of _ y]) apply(rule exI[of _ s])
       apply(rule exI[of _ t']) apply(rule exI[of _ "abs_trm (presubst t' s y)"])
       apply (simp add: 1) by (simp add: Lm.abs_eq)
     qed
   qed
  }
  thus ?thesis by metis
qed

lemma substRel_total: 
"\<exists>t'. substRel t s y t'"
using substRel_presubst by blast

lemma substRel_functional: 
assumes "substRel t s y t'" and "substRel t s y tt'"
shows "t' = tt'"
proof-
  have "\<exists>t s y. substRel t s y t' \<and> substRel t s y tt'"   
  using assms by auto 
  thus ?thesis  
  proof(coinduct rule: trm_coind)
    case (1 tt tt')
    then obtain t s y where sb: "substRel t s y tt" "substRel t s y tt'" by auto
    show ?case proof(cases t rule: trm_cases_fresh[where xs = "[y]" and ts = "[s,tt,tt']"])
      case (Vr x)
      then show ?thesis using sb  
        by (metis substRel_Vr_invert trm_exhaust)
    next
      case (Ap t1 t2)
      then show ?thesis using sb by (meson substRel_Ap_invert)
    next
      case (Lm x' t')
      then show ?thesis using substRel_Lm_invert[OF sb(1)[unfolded Lm]]
      substRel_Lm_invert[OF sb(2)[unfolded Lm]] by simp (metis Lm_eq_swap)
    qed
  qed 
qed

definition subst :: "trm \<Rightarrow> trm \<Rightarrow> var \<Rightarrow> trm" where 
"subst t s x \<equiv> SOME tt. substRel t s x tt"

lemma substRel_subst: "substRel t s x (subst t s x)"
by (simp add: someI_ex substRel_total subst_def)

lemma substRel_subst_unique: "substRel t s x tt \<Longrightarrow> tt = subst t s x"
by (simp add: substRel_functional substRel_subst)

lemma 
subst_Vr[simp]: "subst (Vr x) t z = (if x = z then t else Vr x)"
and 
subst_Ap[simp]: "subst (Ap s1 s2) t z = Ap (subst s1 t z) (subst s2 t z)"
and
subst_Lm[simp]: 
"x \<noteq> z \<Longrightarrow> fresh x t \<Longrightarrow> subst (Lm x s) t z = Lm x (subst s t z)" 
subgoal by (metis substRel_Vr_invert substRel_subst)
subgoal by (metis substRel_Ap substRel_subst substRel_subst_unique)
subgoal by (meson substRel_Lm substRel_functional substRel_subst) . 

lemma fresh_subst_1:
assumes "fresh z (subst s t x)" "z \<noteq> x"
shows "fresh z s"
proof-
  have "\<exists>x t. fresh z (subst s t x) \<and> z \<noteq> x" using assms by auto
  thus ?thesis 
  apply(coinduct rule: fresh_coind) 
  by (smt (verit, best) fresh_Ap fresh_Lm fresh_PVr substRel.cases substRel_subst substRel_subst_unique)
qed

lemma fresh_subst_2:
assumes "fresh z (subst s t x)" "\<not> fresh z t"
shows "fresh x s"
proof-
  have "\<exists>z t. fresh z (subst s t x) \<and> \<not> fresh z t" using assms by auto
  thus ?thesis 
  proof(coinduct rule: fresh_coind) 
    case (1 xx tt)
    then obtain z t where f: "fresh z (subst tt t xx)" "\<not> fresh z t" by auto
    show ?case 
    proof(cases tt rule: trm_cases_fresh[where xs = "[x,z]" and ts = "[t]"])
      case (Vr y) 
      then show ?thesis using f by auto
    next
      case (Ap t1 t2)
      then show ?thesis using f by auto
    next
      case (Lm x t)
      then show ?thesis using f by fastforce
    qed
  qed 
qed

lemma fresh_subst_3:
assumes "z = x \<or> fresh z s" "fresh x s \<or> fresh z t"
shows "fresh z (subst s t x)"
proof-
  {fix tt 
   assume "\<exists> s t x. tt = subst s t x \<and> (z = x \<or> fresh z s) \<and> (fresh x s \<or> fresh z t)"
   hence "fresh z tt"
   proof(coinduct rule: fresh_coind)
     case (1 xx tt)
     then obtain s t x where tt: "tt = subst s t x" "xx = x \<or> fresh xx s" "fresh x s \<or> fresh xx t"
     by auto
     show ?case 
     proof(cases s rule: trm_cases_fresh[where xs = "[x,xx]" and ts = "[t]"])
       case (Vr y)
       then show ?thesis apply(cases "y = x")
         subgoal unfolding tt(1) using tt(2,3)  
         using trm_nchotomy by fastforce
         subgoal apply(intro disjI1) unfolding tt(1) using tt(2,3) by auto .
     next
       case (Ap t1 t2)
       then show ?thesis using tt by auto
     next
       case (Lm x t)
       then show ?thesis using tt by fastforce
     qed
   qed 
  }
  thus ?thesis using assms by metis
qed

lemma fresh_subst:
"fresh z (subst s t x) \<longleftrightarrow> (z = x \<or> fresh z s) \<and> (fresh x s \<or> fresh z t)"
by (metis fresh_subst_1 fresh_subst_2 fresh_subst_3)

lemma fresh_subst_id[simp]: 
assumes "fresh x s" shows "subst s t x = s"
proof-
  {fix ss assume "\<exists> t x. ss = subst s t x \<and> fresh x s"
   hence "ss = s"
   proof(coinduct rule: trm_coind)
     case (1 tt tt')
     then obtain t x where tt: "tt = subst tt' t x" "fresh x tt'" by auto
     show ?case 
     proof(cases tt' rule: trm_cases_fresh[where xs = "[x]" and ts = "[t]"])
       case (Vr x)
       then show ?thesis using tt by auto
     next
       case (Ap t1 t2)
       then show ?thesis using tt by auto
     next
       case (Lm x' t')
       then show ?thesis using tt by simp (metis Lm_eq_swap)
     qed
   qed
  }
  thus ?thesis using assms by metis
qed 

lemma subst_Vr_id[simp]: "subst s (Vr x) x = s"
proof-
  {fix ss assume "\<exists> x. ss = subst s (Vr x) x"
   hence "ss = s"
   proof(coinduct rule: trm_coind)
     case (1 tt tt')
     then obtain x where tt: "tt = subst tt' (Vr x) x" by auto
     show ?case 
     proof(cases tt' rule: trm_cases_fresh[where xs = "[x]" and ts = "[]"])
       case (Vr x)
       then show ?thesis using tt by auto
     next
       case (Ap t1 t2)
       then show ?thesis using tt by auto
     next
       case (Lm x' t')
       then show ?thesis using tt by simp (metis Lm_eq_swap)
     qed
   qed
  }
  thus ?thesis by metis
qed 

lemma Lm_swap_cong:
assumes "z = x \<or> fresh z s" "z = y \<or> fresh z t" and "swap s z x = swap t z y"
shows "Lm x s = Lm y t"
using assms by (metis Lm_swap_rename)

lemma fresh_swap_1: 
assumes "fresh x (swap t z1 z2)"
shows "fresh (sw x z1 z2) t"
proof-
  {fix xx assume "\<exists> x. xx = sw x z1 z2 \<and> fresh x (swap t z1 z2)"
   hence "fresh xx t"
   proof(coinduct rule: fresh_coind)
     case (1 xx tt)
     then obtain x where tt: "xx = sw x z1 z2" "fresh x (swap tt z1 z2)" by auto
     show ?case 
     apply (cases tt) using tt by fastforce+
   qed
  }
  thus ?thesis using assms by metis
qed 

lemma fresh_swap[simp]: "fresh x (swap t z1 z2) \<longleftrightarrow> fresh (sw x z1 z2) t"
  by (metis fresh_sw_swap sw_invol) 

lemma swap_id[simp]: "swap t x x = t"
using Lm_eq_swap by force

lemma swap_cmpTrans: 
"swap (swap t x y) z1 z2 = swap (swap t z1 z2) (sw x z1 z2) (sw y z1 z2)"
by (metis id_apply map_fun_apply pswap_pswap swap.abs_eq swap_def)

(* *)

lemma swap_subst: 
"swap (subst s t x) z1 z2 = subst (swap s z1 z2) (swap t z1 z2) (sw x z1 z2)"
proof-
  {fix ss ss' assume "\<exists> s t x. ss = swap (subst s t x) z1 z2 \<and> ss' = subst (swap s z1 z2) (swap t z1 z2) (sw x z1 z2)"
   hence "ss = ss'"
   proof(coinduct rule: trm_coind)
     case (1 tt tt')
     then obtain s t x where tt: "tt = swap (subst s t x) z1 z2" "
     tt' = subst (swap s z1 z2) (swap t z1 z2) (sw x z1 z2)" by auto
     show ?case 
     proof(cases s rule: trm_cases_fresh[where xs = "[x,z1,z2]" and ts = "[t]"])
       case (Vr xx)
       then show ?thesis using tt trm_nchotomy by auto blast
     next
       case (Ap t1 t2)
       then show ?thesis using tt by auto
     next
       case (Lm x' t')
       then show ?thesis using tt 
       by simp (smt (verit, best) Lm_eq_swap fresh_sw_swap subst_Lm sw_diff sw_inj) 
     qed
   qed
  }
  thus ?thesis by metis
qed 

lemma subst_Lm_same[simp]: "subst (Lm x s) t x = Lm x s"
by simp

lemma fresh_subst_same: 
assumes "y \<noteq> z" shows "fresh y (subst t (Vr z) y)"
by (simp add: assms fresh_subst_3)

lemma subst_comp_same: 
"subst (subst s t x) t1 x = subst s (subst t t1 x) x"
proof-
  {fix ss ss' assume "\<exists> s t x t1. ss = subst (subst s t x) t1 x \<and> ss' = subst s (subst t t1 x) x"
   hence "ss = ss'"
   proof(coinduct rule: trm_coind)
     case (1 tt tt')
     then obtain s t x t1 where tt: "tt = subst (subst s t x) t1 x" "tt' = subst s (subst t t1 x) x"
     by auto 
     show ?case 
     proof(cases s rule: trm_cases_fresh[where xs = "[x]" and ts = "[t,t1]"])
       case (Vr xx)
       then show ?thesis using tt trm_nchotomy by auto blast
     next
       case (Ap t1 t2)
       then show ?thesis using tt by auto
     next
       case (Lm x' t')
       then show ?thesis using tt  
       by simp (metis Lm_eq_swap fresh_subst subst_Lm) 
     qed
   qed
  }
  thus ?thesis by metis
qed 


lemma subst_comp_diff: 
assumes "x \<noteq> x1" "fresh x t1"
shows "subst (subst s t x) t1 x1 = subst (subst s t1 x1) (subst t t1 x1) x"
proof-
  {fix ss ss' assume "\<exists> s t x t1 x1. x \<noteq> x1 \<and> fresh x t1 \<and> 
   ss = subst (subst s t x) t1 x1 \<and> ss' = subst (subst s t1 x1) (subst t t1 x1) x"
   hence "ss = ss'"
   proof(coinduct rule: trm_coind)
     case (1 tt tt')
     then obtain s t x t1 x1 where tt: "x \<noteq> x1" "fresh x t1"
     "tt = subst (subst s t x) t1 x1" 
     "tt' = subst (subst s t1 x1) (subst t t1 x1) x" by auto
     show ?case 
     proof(cases s rule: trm_cases_fresh[where xs = "[x,x1]" and ts = "[t,t1]"])
       case (Vr xx)
       then show ?thesis using tt trm_nchotomy by simp blast
     next
       case (Ap t1 t2)
       then show ?thesis using tt by simp blast
     next
       case (Lm x' t')
       then show ?thesis using tt  
       by simp (metis Lm_eq_swap fresh_subst subst_Lm) 
     qed
   qed
  }
  thus ?thesis using assms by metis
qed 

lemma subst_comp_diff_var: 
assumes "x \<noteq> x1" "x \<noteq> z1"
shows "subst (subst s t x) (Vr z1) x1 = 
       subst (subst s (Vr z1) x1) (subst t (Vr z1) x1) x"
apply(rule subst_comp_diff)
using assms by auto

lemma subst_chain: 
assumes "fresh u s" 
shows "subst (subst s (Vr u) x) t u = subst s t x"
proof-
  {fix ss ss' assume "\<exists> s u x t. fresh u s \<and> 
   ss = subst (subst s (Vr u) x) t u \<and> ss' = subst s t x"
   hence "ss = ss'"
   proof(coinduct rule: trm_coind)
     case (1 tt tt')
     then obtain s u x t where tt: "fresh u s" 
     "tt = subst (subst s (Vr u) x) t u" "tt' = subst s t x" by auto
     show ?case 
     proof(cases s rule: trm_cases_fresh[where xs = "[x,u]" and ts = "[t]"])
       case (Vr xx)
       then show ?thesis using tt trm_nchotomy by simp blast
     next
       case (Ap t1 t2)
       then show ?thesis using tt by simp blast
     next
       case (Lm x' t')
       then show ?thesis using tt by simp (metis Lm_eq_swap) 
     qed
   qed
  }
  thus ?thesis using assms by metis
qed 

lemma subst_repeated_Vr: 
"subst (subst t (Vr x) y) (Vr u) x = 
 subst (subst t (Vr u) x) (Vr u) y"
proof-
  {fix ss ss' assume "\<exists> t x y u.  
   ss = subst (subst t (Vr x) y) (Vr u) x \<and> ss' = subst (subst t (Vr u) x) (Vr u) y"
   hence "ss = ss'"
   proof(coinduct rule: trm_coind)
     case (1 tt tt')
     then obtain t x y u where tt: "tt = subst (subst t (Vr x) y) (Vr u) x"
     "tt' = subst (subst t (Vr u) x) (Vr u) y" by auto
     show ?case 
     proof(cases t rule: trm_cases_fresh[where xs = "[x,y,u]" and ts = "[]"])
       case (Vr xx)
       then show ?thesis using tt trm_nchotomy by simp 
     next
       case (Ap t1 t2)
       then show ?thesis using tt by auto
     next
       case (Lm x' t')
       then show ?thesis using tt by simp (metis Lm_eq_swap) 
     qed
   qed
  }
  thus ?thesis by metis
qed 

lemma subst_commute_same: 
"subst (subst d (Vr u) x) (Vr u) y = subst (subst d (Vr u) y) (Vr u) x"
by (metis subst_Vr_id subst_repeated_Vr)

lemma subst_commute_diff: 
assumes "x \<noteq> v" "y \<noteq> u" "x \<noteq> y"
shows "subst (subst t (Vr u) x) (Vr v) y = subst (subst t (Vr v) y) (Vr u) x"
by (metis assms fresh_PVr fresh_subst_id subst_comp_diff_var)

lemma subst_same_id: 
assumes "z1 \<noteq> y"
shows "subst (subst t (Vr z1) y) (Vr z2) y = subst t (Vr z1) y"
using assms subst_Vr subst_comp_same by presburger

lemma swap_from_subst: 
assumes yy: "yy\<notin>{z1,z2}" "fresh yy t"  
shows "swap t z1 z2 = subst (subst (subst t (Vr yy) z1) (Vr z1) z2) (Vr z2) yy"
proof-
  {fix ss ss' assume "\<exists> yy t. yy\<notin>{z1,z2} \<and> fresh yy t \<and> 
   ss = swap t z1 z2 \<and> ss' = subst (subst (subst t (Vr yy) z1) (Vr z1) z2) (Vr z2) yy"
   hence "ss = ss'"
   proof(coinduct rule: trm_coind)
     case (1 tt tt')
     then obtain yy t where tt: "yy \<notin> {z1, z2}" "fresh yy t"
     "tt = swap t z1 z2" "tt' = subst (subst (subst t (Vr yy) z1) (Vr z1) z2) (Vr z2) yy" by auto
     show ?case 
     proof(cases t rule: trm_cases_fresh[where xs = "[yy,z1,z2]" and ts = "[]"])
       case (Vr xx)
       then show ?thesis using tt trm_nchotomy by simp 
     next
       case (Ap t1 t2)
       then show ?thesis using tt by auto
     next
       case (Lm x' t')
       then show ?thesis using tt by simp (metis Lm_eq_swap) 
     qed
   qed
  }
  thus ?thesis using assms by metis
qed 

lemma subst_two_ways': 
fixes t yy x
assumes yy: "yy\<notin>{z1,z2}"  "yy'\<notin>{z1,z2}"  "x \<notin> {yy,yy'}"
defines "tt \<equiv> subst (subst t (Vr x) yy) (Vr x) yy'"
shows "subst (subst (subst tt (Vr yy) z1) (Vr z1) z2) (Vr z2) yy = 
       subst (subst (subst tt (Vr yy') z1) (Vr z1) z2) (Vr z2) yy'"
(is "?L = ?R")
proof-
  have "?L = swap tt z1 z2"
  apply(rule sym, rule swap_from_subst)
  using assms fresh_PVr fresh_subst by auto
  also have "\<dots> = ?R" apply(rule swap_from_subst)
  using assms fresh_PVr fresh_subst by auto
  finally show ?thesis .
qed

lemma subst_two_ways'': 
assumes "xx \<notin> {x, z1, z2, uu, vv} \<and> fresh xx t"
"vv \<notin> {x, z1, z2} \<and> fresh vv t"
"yy \<notin> {z1, z2} \<and> fresh yy t"
shows 
"subst (subst (subst (subst (subst t (Vr xx) x) (Vr vv) z1) (Vr z1) z2) (Vr z2) vv) (Vr vv) xx =
 subst (subst (subst (subst t (Vr yy) z1) (Vr z1) z2) (Vr z2) yy) (Vr vv) (sw x z1 z2)"
(is "?L = ?R")
proof-
  have "?L = subst (swap (subst t (Vr xx) x) z1 z2) (Vr vv) xx"
  apply (subst swap_from_subst[of vv])  
  	using assms fresh_PVr fresh_subst by auto
  also have "\<dots> = ?R"
  apply (subst swap_from_subst[symmetric, of yy]) using assms  
  	by (auto simp: subst_repeated_Vr swap_subst)
  finally show ?thesis .
qed

(* Equational reformulation of the above, to be transported to the models: 
We take advantage of the fact that z1 is different from all the items assumed 
pfresh in the previous lemma. *)
lemma subst_two_ways''_aux: 
fixes t z1 xx z2 vv   
assumes "xx \<notin> {x, z1, z2, uu, vv}"
"vv \<notin> {x, z1, z2}"
"yy \<notin> {z1, z2}" 
defines "tt \<equiv> subst (subst (subst t (Vr z1) xx) (Vr z1) yy) (Vr z1) vv"
shows 
"subst (subst (subst (subst (subst tt (Vr xx) x) (Vr vv) z1) (Vr z1) z2) (Vr z2) vv) (Vr vv) xx =
 subst (subst (subst (subst tt (Vr yy) z1) (Vr z1) z2) (Vr z2) yy) (Vr vv) (sw x z1 z2)"
apply(rule subst_two_ways'')
using assms fresh_subst fresh_subst_same fresh_PVr fresh_subst by auto

thm pfresh.cases[no_vars]

lemma fresh_cases[cases pred: fresh, case_names Vr Ap Lm]:
"fresh a1 a2 \<Longrightarrow>
(\<And>z x. a1 = z \<Longrightarrow> a2 = Vr x \<Longrightarrow> z \<noteq> x \<Longrightarrow> P) \<Longrightarrow>
(\<And>z t1 t2. a1 = z \<Longrightarrow> a2 = Ap t1 t2 \<Longrightarrow> fresh z t1 \<Longrightarrow> fresh z t2 \<Longrightarrow> P) \<Longrightarrow>
(\<And>z x t. a1 = z \<Longrightarrow> a2 = Lm x t \<Longrightarrow> z = x \<or> fresh z t \<Longrightarrow> P) \<Longrightarrow> P"
apply transfer by (auto, metis alpha_refl pfresh.simps)

(* Var-for-var presubstitution on variables: *)
definition vss :: "var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var" where 
"vss x y z = (if x = z then y else x)"


(* *)

lemma fresh_subst_eq_swap: 
assumes "fresh z t"
shows "subst t (Vr z) x = swap t z x" 
proof-
  {fix ss ss' assume "\<exists> z t x. fresh z t \<and> 
   ss = subst t (Vr z) x \<and> ss' = swap t z x"
   hence "ss = ss'"
   proof(coinduct rule: trm_coind)
     case (1 tt tt')
     then obtain z t x where tt: "fresh z t \<and> tt = subst t (Vr z) x \<and> tt' = swap t z x" by auto
     show ?case 
     proof(cases t rule: trm_cases_fresh[where xs = "[z,x]" and ts = "[]"])
       case (Vr xx)
       then show ?thesis using tt trm_nchotomy by simp fastforce
     next
       case (Ap t1 t2)
       then show ?thesis using tt by auto
     next
       case (Lm x' t')
       then show ?thesis using tt by simp (metis Lm_eq_swap) 
     qed
   qed
  }
  thus ?thesis using assms by metis
qed 

lemma Lm_subst_rename: 
assumes "z = x \<or> fresh z t"
shows "Lm z (subst t (Vr z) x) = Lm x t"
using Lm_swap_rename assms fresh_subst_eq_swap subst_Vr_id by presburger

lemma Lm_subst_cong: 
"z = x \<or> fresh z s \<Longrightarrow> z = y \<or> fresh z t \<Longrightarrow> 
subst s (Vr z) x = subst t (Vr z) y \<Longrightarrow> Lm x s = Lm y t"
by (metis Lm_subst_rename)

lemma Lm_eq_elim:  
"Lm x s = Lm y t \<Longrightarrow> z = x \<or> fresh z s \<Longrightarrow> z = y \<or> fresh z t 
 \<Longrightarrow> 
 swap s z x = swap t z y"
apply transfer by (meson alpha_PLm_strong_elim) 

lemma Lm_eq_elim_subst:  
"Lm x s = Lm y t \<Longrightarrow> z = x \<or> fresh z s \<Longrightarrow> z = y \<or> fresh z t 
 \<Longrightarrow> 
 subst s (Vr z) x = subst t (Vr z) y"
by (smt (verit, ccfv_threshold) Lm_eq_elim Lm_subst_rename swap_id)

(* *)


(* Environments mapping variables to terms *)

typedef fenv = "{f :: var \<Rightarrow> trm . finite {x. f x \<noteq> Vr x}}"
using not_finite_existsD by auto

definition get :: "fenv \<Rightarrow> var \<Rightarrow> trm" where 
"get f x \<equiv> Rep_fenv f x"

definition upd :: "fenv \<Rightarrow> var \<Rightarrow> trm \<Rightarrow> fenv" where 
"upd f x t = Abs_fenv ((Rep_fenv f)(x:=t))"

definition suppEnv :: "fenv \<Rightarrow> var set" where 
"suppEnv f \<equiv> {x. get f x \<noteq> Vr x}"

lemma finite_suppEnv: "finite (suppEnv f)" 
using Rep_fenv get_def suppEnv_def by auto

lemma finite_upd: 
assumes "finite {x. f x \<noteq> Vr x}"
shows "finite {x. (f(y:=t)) x \<noteq> Vr x}"
proof-
  have "{x. (f(y:=t)) x \<noteq> Vr x} \<subseteq> {x. f x \<noteq> Vr x} \<union> {y}"
  by auto
  thus ?thesis 
  by (metis (full_types) assms finite_insert insert_is_Un rev_finite_subset sup.commute)
qed

lemma getupd_same[simp]: "get (upd f x t) x = t"
and getupd_diff[simp]: "x \<noteq> y \<Longrightarrow> get (upd f x t) y = get f y"
and upd_upd_same[simp]: "upd (upd f x t) x s = upd f x s"
and upd_upd_diff: "x \<noteq> y \<Longrightarrow> upd (upd f x t) y s = upd (upd f y s) x t"
and suppEnv_get[simp]: "x \<notin> suppEnv \<rho> \<Longrightarrow> get \<rho> x = Vr x"
unfolding get_def upd_def using Rep_fenv finite_upd 
by (auto simp: fun_upd_twist Abs_fenv_inverse get_def suppEnv_def)  

(* *)
abbreviation rename where "rename t x y \<equiv> subst t (Vr x) y"


(* Alternative (asymmetric) definition of alpha-equivaloence: *)

coinductive alpha' :: "ptrm \<Rightarrow> ptrm \<Rightarrow> bool" where 
 PVr[intro]: 
"alpha' (PVr x) (PVr x)"
|PAp[intro]: 
"alpha' s s' \<Longrightarrow> alpha' t t' \<Longrightarrow> alpha' (PAp s t) (PAp s' t')"
|PLm[intro]: 
"x' = x \<or> pfresh x' t \<Longrightarrow> alpha' (pswap t x' x) t' \<Longrightarrow> alpha' (PLm x t) (PLm x' t')"

lemma alpha_imp_alpha': 
assumes "alpha t1 t2" shows "alpha' t1 t2"
using assms proof coinduct
  case (alpha' t1 t2)
  then show ?case proof cases
    case (PVr x)
    then show ?thesis by auto
  next
    case (PAp s s' t t')
    then show ?thesis by auto
  next
    case (PLm z x t x' t')
    then show ?thesis apply(intro disjI2) apply auto   
      apply (metis alpha_pfresh_iff pswap_pfresh_iff pswap_sym sw_eqR)
      apply (metis alpha_pswap pswap_invol2)   
      apply (meson alpha.PLm alpha_pfresh_iff pfresh_simps(3))
      by (metis Lm_eq_swap abs_trm_PLm alpha' swap.abs_eq trm.abs_eq_iff)
  qed
qed

lemma alpha'_pswap: 
assumes "alpha' s s'" shows "alpha' (pswap s z1 z2) (pswap s' z1 z2)"
proof-
  {fix ss ss' assume "\<exists>s s' z1 z2. alpha' s s' \<and> ss = pswap s z1 z2 \<and> ss' = pswap s' z1 z2"
   hence "alpha' ss ss'"
   apply(coinduct rule: alpha'.coinduct) apply (elim exE)
   subgoal for ss ss' s s' z1 z2
   apply(elim conjE) apply(erule alpha'.cases)
     subgoal by auto
     subgoal by auto
     subgoal for x' x t t'
     apply(rule disjI2, rule disjI2) apply(rule exI[of _ "sw x' z1 z2"])  apply(rule exI[of _ "sw x z1 z2"])
     apply(rule exI[of _ "pswap t z1 z2"]) apply(rule exI[of _ "pswap t' z1 z2"])
     using pswap_pswap by auto . .
   }
   thus ?thesis using assms by blast
qed 

(* *)

lemma alpha'_refl[simp,intro!]: "alpha' s s" 
  by (simp add: alpha_imp_alpha')

lemma alpha'_pfresh_imp: 
assumes "alpha' t t'" and "pfresh y t" shows "pfresh y t'" 
proof-
  {assume "\<exists>t. alpha' t t' \<and> pfresh y t"
   hence "pfresh y t'"
   apply(coinduct) apply(elim exE conjE) 
   subgoal for y t' t apply(erule alpha'.cases)
     subgoal by auto
     subgoal by auto
     subgoal for x' x tt tt' apply(rule disjI2, rule disjI2) apply auto apply(rule exI[of _ "pswap tt x' x"]) apply auto  
       apply (simp add: pfresh_pswap_iff) by (metis pfresh_pswap_iff pswap_invol2 sw_diff) . . 
  }
  thus ?thesis using assms by blast
qed 

lemma alpha'_sym: 
assumes "alpha' s t" shows "alpha' t s" 
using assms apply(coinduct) subgoal for s1 s2
apply(erule alpha'.cases) apply auto 
apply (simp add: alpha'_pfresh_imp pfresh_pswap_iff)  
by (metis alpha'_pswap pswap_invol2) .

lemma alpha'_pfresh_iff: 
assumes "alpha' s t"  
shows "pfresh x s \<longleftrightarrow> pfresh x t"
using alpha'_pfresh_imp alpha'_sym assms by blast

lemma pswap_pfresh_alpha': 
assumes "pfresh z1 t" and "pfresh z2 t"
shows "alpha' (pswap t z1 z2) t"
proof-
  {fix tt assume "\<exists>z1 z2. tt = pswap t z1 z2 \<and> pfresh z1 t \<and> pfresh z2 t"
   hence "alpha' tt t"
   apply(coinduct) apply(elim exE conjE)
   subgoal for tt t z1 z2 apply(cases t)
     subgoal by auto
     subgoal by auto
     subgoal apply(rule disjI2, rule disjI2) apply clarsimp 
     by (metis alpha'_refl pswap_id pswap_invol pswap_pfresh_iff pswap_sym sw_diff sw_eqL sw_eqR) 
     . . 
  }
  thus ?thesis using assms by auto
qed 

(* *)

lemma alpha'T_pswap: assumes "alpha'\<^sup>*\<^sup>* s s'" shows "alpha'\<^sup>*\<^sup>* (pswap s z1 z2) (pswap s' z1 z2)"
using assms apply(induct) using alpha'_pswap by auto (meson rtranclp.simps)

lemma alpha'T_PVr:
assumes al: "alpha'\<^sup>*\<^sup>* (PAp t1 t2) (PAp t1' t2')"  
shows "alpha'\<^sup>*\<^sup>* t1 t1' \<and> alpha'\<^sup>*\<^sup>* t2 t2'"
proof-
  {fix t t' assume "alpha'\<^sup>*\<^sup>* t t'"
   hence "\<forall>t1 t2 t1' t2'. t = PAp t1 t2 \<and> t' = PAp t1' t2' \<longrightarrow> alpha'\<^sup>*\<^sup>* t1 t1' \<and> alpha'\<^sup>*\<^sup>* t2 t2'"
   apply(induct) apply auto 
   apply (smt (verit, best) alpha'.simps ptrm.distinct(5) ptrm.sel(2) rtranclp.simps)
   by (smt (verit) alpha'.cases ptrm.sel(3) ptrm.simps(9) rtranclp.simps)
  }
  thus ?thesis using assms by metis
qed

lemma alpha'T_Lm_pfresh:
assumes al: "alpha'\<^sup>*\<^sup>* (PLm x t) (PLm x' t')"  
shows "(x' = x \<or> pfresh x' t) \<and> alpha'\<^sup>*\<^sup>* (pswap t x' x) t'"
proof-
  {fix t1 t2 
   assume "alpha'\<^sup>*\<^sup>* t1 t2"
   hence "\<forall> x t x' t'. t1 = PLm x t \<and> t2 = PLm x' t' \<longrightarrow> 
         (x' = x \<or> pfresh x' t) \<and> alpha'\<^sup>*\<^sup>* (pswap t x' x) t'"
   proof induct
     case base
     then show ?case  
       by force 
   next
     case (step t2 t3)
     then show ?case proof clarify
       fix x1 t1' x3 t3' assume t1: "t1 = PLm x1 t1'" and t3: "t3 = PLm x3 t3'"
       from `alpha' t2 t3` t3 obtain x2 t2' where t2: "t2 = PLm x2 t2'"  
         by (metis alpha'.cases ptrm.simps(9)) 

       note st = step(3)[rule_format, of x1 t1' x2 t2', unfolded t1 t2, simplified]
       hence 12: "x2 = x1 \<or> pfresh x2 t1'" and al12: "alpha'\<^sup>*\<^sup>* (pswap t1' x2 x1) t2'" by auto
       hence al12: "alpha'\<^sup>*\<^sup>* (pswap (pswap t1' x2 x1) x3 x2) (pswap t2' x3 x2)"
       using alpha'T_pswap by auto

       have 23: "x3 = x2 \<or> pfresh x3 t2'" and al23: "alpha' (pswap t2' x3 x2) t3'"
       using step(2) unfolding t2 t3  by (auto elim: alpha'.cases)

       have al0: "alpha'\<^sup>*\<^sup>* (pswap t1' x3 x1) (pswap (pswap t1' x2 x1) x3 x2)" 
       by (smt (verit, ccfv_threshold) 23 st
       alpha'_pfresh_iff alpha_imp_alpha' converse_rtranclp_induct pfresh_pswap_alpha 
       pfresh_pswap_iff pswap_invol2 r_into_rtranclp sw_eqR)

       have 13:  "x3 = x1 \<or> pfresh x3 t1'" 
         by (smt (verit, ccfv_threshold) "23" alpha'_pfresh_iff converse_rtranclp_induct pfresh_pswap_iff st sw_diff)

       have al13: "alpha'\<^sup>*\<^sup>* (pswap t1' x3 x1) t3'" using al0 al12 al23 by auto
       
       show "(x3 = x1 \<or> pfresh x3 t1') \<and> alpha'\<^sup>*\<^sup>* (pswap t1' x3 x1) t3'" using 13 al13 by simp
     qed
   qed 
  } 
  thus ?thesis using assms by metis
qed

lemma alpha'T_cases: assumes "alpha'\<^sup>*\<^sup>* t t'"
shows 
 "(\<exists>x x'. t = PVr x' \<and> t' = PVr x') \<or> 
  (\<exists>t1 t2 t1' t2'. t = PAp t1 t2 \<and> t' = PAp t1' t2') \<or> 
  (\<exists>x tt x' tt'. t = PLm x tt \<and> t' = PLm x' tt')"
using assms apply induct apply (auto elim: alpha'.cases) 
using ptrm.exhaust_sel by blast

lemma alpha'T_alpha': 
assumes "alpha'\<^sup>*\<^sup>* t1 t2" shows "alpha' t1 t2"
using assms apply(coinduct) subgoal for t1 t2
apply(frule alpha'T_cases) apply auto
  using alpha'T_PVr apply blast  
  using alpha'T_PVr apply blast  
  using alpha'T_Lm_pfresh by blast+ .

lemma alpha'_trans:
assumes "alpha' t t'" and "alpha' t' t''" 
shows "alpha' t t''"
using alpha'T_alpha' by (meson assms converse_rtranclp_into_rtranclp r_into_rtranclp)

(* *)

lemma alpha'_imp_alpha: 
assumes "alpha' t1 t2" shows "alpha t1 t2"
using assms proof coinduct
  case (alpha t1 t2)
  then show ?case proof cases
    case (PVr x)
    then show ?thesis by auto
  next
    case (PAp s s' t t')
    then show ?thesis by auto
  next
    case (PLm x' x t t')
    obtain z where z: "z \<notin> {x,x'}" "pfresh z t" "pfresh z t'"
    using exists_pfresh[of "[x,x']" "[t,t']"] by auto
    have "alpha' (pswap (pswap t x' x) z x') (pswap t' z x')" 
    using alpha'_pswap[OF PLm(4)] . 
    moreover 
    have "alpha' (pswap (pswap t x' x) z x') (pswap t z x)" 
    by (metis alpha_imp_alpha' local.PLm(3) pfresh_pswap_alpha pswap_id z(2))
    ultimately have al: "alpha' (pswap t z x) (pswap t' z x')"  
      by (meson alpha'_sym alpha'_trans)
    show ?thesis using PLm z al apply(intro disjI2)  
    apply(rule exI[of _ z]) by auto
  qed
qed

lemma alpha_eq_alpha': "alpha = alpha'"
using alpha'_imp_alpha alpha_imp_alpha' by fastforce

lemmas alpha'_eq_alpha = alpha_eq_alpha'[symmetric]

(* Now proving the equality-coinduction for terms induced by the definition of alpha', 
similarly to that induced by the definition of alpha *)

thm alpha_coinduct_strong
lemma alpha'_coinduct_strong[consumes 1]: 
(* need to replace all term equalities with alpha', to obtain a suitable coinduction for 
equality on the quotient type *)
assumes R: "R t t'" and c: "compatAlpha2 R"
and b: "\<And>tt tt'.
    R tt tt' \<Longrightarrow>
    (\<exists>x. alpha' tt (PVr x) \<and> alpha' tt' (PVr x)) \<or>
    (\<exists>s s' t t'. alpha' tt (PAp s t) \<and> alpha' tt' (PAp s' t') \<and> (R s s' \<or> alpha' s s') \<and> (R t t' \<or> alpha' t t')) \<or>
    (\<exists>x t x' t'.
        alpha' tt (PLm x t) \<and>
        alpha' tt' (PLm x' t') \<and> 
        (x' = x \<or> pfresh x' t) \<and> 
        (R (pswap t x' x) t' \<or> alpha' (pswap t x' x) t'))"
shows "alpha' t t'" 
unfolding alpha'_eq_alpha apply(rule alpha_coinduct_strong[of R, OF R c])
subgoal for tt tt' apply(drule b) apply(elim disjE exE)
  subgoal apply(rule disjI1) unfolding alpha'_eq_alpha by auto
  subgoal apply(rule disjI2, rule disjI1) unfolding alpha'_eq_alpha by auto
  subgoal apply(rule disjI2, rule disjI2) unfolding alpha'_eq_alpha 
  by fastforce+ . .

theorem trm_coind'[consumes 1]: 
assumes R: "R t t'"
and b: "\<And>tt tt'.
    R tt tt' \<Longrightarrow>
    (\<exists>x. tt = Vr x \<and> tt' = Vr x) \<or>
    (\<exists>s s' t t'. tt = Ap s t \<and> tt' = Ap s' t' \<and> (R s s' \<or> s = s') \<and> (R t t' \<or> t = t')) \<or>
    (\<exists>x t x' t'.
        tt = Lm x t \<and> tt' = Lm x' t' \<and> (x' = x \<or> fresh x' t) \<and> 
        (R (swap t x' x) t' \<or> swap t x' x = t'))"
shows "t = t'" 
proof-
  obtain pt pt' where 0: "pt = rep_trm t \<and> pt' = rep_trm t'" by auto
  have "R (abs_trm pt) (abs_trm pt')"
  using R by (simp add: "0")
  hence "alpha' pt pt'" 
  apply(coinduct rule: alpha'_coinduct_strong) 
  subgoal unfolding compatAlpha2_def by (metis trm.abs_eq_iff)
  subgoal for pt pt' unfolding alpha'_eq_alpha apply(drule b) apply(elim disjE exE)
    subgoal for x apply(rule disjI1)
      by (metis Vr.abs_eq alpha_PVr_eq alpha_eq_PVr alpha_rep_abs_trm)
    subgoal for s s' t t' apply(rule disjI2, rule disjI1) unfolding swap_def Ap_def 
    apply simp unfolding trm.abs_eq_iff 
      by (metis Quotient3_abs_rep Quotient3_trm alpha_refl) 
    subgoal for x t x' t' apply(rule disjI2, rule disjI2)
      unfolding swap_def fresh_def Lm_def apply simp unfolding trm.abs_eq_iff 
      by (metis (full_types) Quotient3_abs_rep Quotient3_trm alpha_rep_abs_trm alpha_sym) . .
  thus ?thesis unfolding alpha'_eq_alpha
    using "0" Quotient3_rel_rep Quotient3_trm by fastforce
qed

theorem trm_coind''[consumes 1]: 
assumes R: "R t t'"
and b: "\<And>tt tt'.
    R tt tt' \<Longrightarrow>
    (\<exists>x. tt = Vr x \<and> tt' = Vr x) \<or>
    (\<exists>s s' t t'. tt = Ap s t \<and> tt' = Ap s' t' \<and> (R s s' \<or> s = s') \<and> (R t t' \<or> t = t')) \<or>
    (\<exists>x t x' t'.
        tt = Lm x t \<and> tt' = Lm x' t' \<and> (x' = x \<or> fresh x' t) \<and> 
        (R (rename t x' x) t' \<or> rename t x' x = t'))"
shows "t = t'" 
using assms(1) apply(elim trm_coind') 
subgoal for tt tt' apply(drule assms(2)) apply (elim disjE exE)
  subgoal by auto
  subgoal by auto
  subgoal for x t x' t' apply(intro disjI2)
  apply(rule exI[of _ x], rule exI[of _ t], rule exI[of _ x'], rule exI[of _ t'])
  using fresh_subst_eq_swap by auto . .


(* Variable-for-variable substitution (renaming) in variables *)

definition "sb x y z \<equiv> if x = z then y else x"


(* *) 
lemma subst_Dest_Vr: 
assumes "Dest t = Vv x"
shows "Dest (subst t t1 z2) = (if x = z2 then Dest t1 else Vv x)"
proof-
  have t: "t = Vr x" using assms 
    using Dest_Vv_Vr by blast
  show ?thesis unfolding t by simp
qed

lemma subst_Dest_Ap: "Dest t = Aa (t1,t2) \<Longrightarrow> 
  Dest (subst t t1 z2) = Aa (subst t1 t1 z2, subst t2 t1 z2)"
unfolding Dest_def apply(cases t, auto)
using getLm_NE unfolding is_Vr_def2 is_Ap_def2 is_Lm_def2 apply auto 
by (metis Ap_getApL_getApR Ap_inj Pair_inject getAp_def is_Ap_def2)

lemma subst_Dest_Lm: "Dest tt = Ll K \<Longrightarrow> 
  \<exists>K'. Dest (subst tt t1 z2) = Ll K' \<and>  
  (\<forall>x t. fresh x t1 \<and> x \<noteq> z2 \<and> (x,t) \<in> K \<longrightarrow> (x, subst t t1 z2) \<in> K')"
unfolding Dest_def apply(cases tt rule: trm_cases, auto)
using getLm_NE unfolding is_Vr_def2 is_Ap_def2 is_Lm_def2 apply auto
apply (metis Ap_Lm_diff(1) substRel_Lm_invert_aux substRel_subst)
apply (metis Vr_Lm_diff(1) substRel_Lm_invert_aux substRel_subst)
using getLm_def prod.simps(2) by auto


end