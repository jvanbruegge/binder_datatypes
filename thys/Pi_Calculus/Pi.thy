(* the syntax of pi-calculus *)

theory Pi
  imports  "Binders.General_Customization" "Prelim.FixedCountableVars"
begin

(* DATATYPE DECLARTION  *)

declare [[mrbnf_internals]]
binder_datatype 'a "term" =
  Zero
| Sum "'a term" "'a term"
| Par "'a term" "'a term" (infixl "\<parallel>" 300)
| Bang "'a term"
| Match 'a 'a "'a term"
| Out 'a 'a "'a term"
| Inp 'a x::'a t::"'a term" binds x in t
| Res x::'a t::"'a term" binds x in t
for
  vvsubst: vvsubst
  tvsubst: tvsubst

(****************************)
(* DATATYPE-SPECIFIC CUSTOMIZATION  *)


(* Monomorphising: *)
type_synonym trm = "var term"

lemma singl_bound: "|{a}| <o |UNIV::var set|"
  by (rule finite_ordLess_infinite2[OF finite_singleton cinfinite_imp_infinite[OF term_pre.UNIV_cinfinite]])

lemma ls_UNIV_iff_finite: "|A| <o |UNIV::var set| \<longleftrightarrow> finite A"
using finite_iff_le_card_var by blast

lemma supp_id_update_le[simp,intro!]:
"|supp (id(x := y))| <o |UNIV::var set|"
by (metis finite.emptyI finite.insertI finite_card_var imsupp_id_fun_upd imsupp_supp_bound infinite_var)


(* Some lighter notations: *)

abbreviation "rrename \<equiv> permute_term"
abbreviation "FFVars \<equiv> FVars_term"

(* *)

(* Enabling some simplification rules: *)

lemmas term.permute_id[simp] term.permute_cong_id[simp]
term.FVars_permute[simp]

lemmas term.vvsubst_permute[simp]


(* Supply of fresh variables *)

lemma finite_FFVars: "finite (FFVars P)"
unfolding ls_UNIV_iff_finite[symmetric]
by (simp add: term.set_bd_UNIV)

lemma exists_fresh:
"\<exists> z. z \<notin> set xs \<and> (\<forall>P \<in> set Ps. z \<notin> FFVars P)"
proof-
  have 0: "|set xs \<union> \<Union> (FFVars ` (set Ps))| <o |UNIV::var set|"
  unfolding ls_UNIV_iff_finite
  using finite_FFVars by blast
  then obtain x where "x \<notin> set xs \<union> \<Union> (FFVars ` (set Ps))"
    by (metis UNIV_eq_I finite_iff_le_card_var large_imp_infinite term_pre.var_large)
  thus ?thesis by auto
qed

(* Properties of the constructors *)

lemma bij_map_term_pre: "bij f \<Longrightarrow> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set| \<Longrightarrow> bij (map_term_pre (id::var \<Rightarrow>var) f (permute_term f) id)"
  apply (rule iffD2[OF bij_iff])
    apply (rule exI[of _ "map_term_pre id (inv f) (permute_term (inv f)) id"])
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
   apply assumption
  apply (rule conjI)
   apply (rule trans)
    apply (rule term_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 term.permute_comp0 term.permute_id0
  apply (rule term_pre.map_id0)
  apply (rule trans)
   apply (rule term_pre.map_comp0[symmetric])
        apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp2 term.permute_comp0 term.permute_id0
  apply (rule term_pre.map_id0)
  done

lemma map_term_pre_inv_simp: "bij f \<Longrightarrow> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set| \<Longrightarrow>
inv (map_term_pre (id::_::var \<Rightarrow> _) f (permute_term f) id) = map_term_pre id (inv f) (permute_term (inv f)) id"
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
  apply assumption
  apply (rule inv_unique_comp)
   apply (rule trans)
    apply (rule term_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
   defer
  apply (rule trans)
    apply (rule term_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 inv_o_simp2 term.permute_comp0 term.permute_id0 term_pre.map_id0
   apply (rule refl)+
  done

lemma Abs_set3: "term_ctor v = Inp y (x::var) e \<Longrightarrow> \<exists>x' e'. term_ctor v = Inp y x' e' \<and> x' \<in> set2_term_pre v \<and> e' \<in> set3_term_pre v"
  unfolding Inp_def term.TT_inject0
  apply (erule exE)
  apply (erule conjE)+
  subgoal for f
apply (drule iffD2[OF bij_imp_inv', rotated, of "map_term_pre id f (permute_term f) id"])
     apply (rule bij_map_term_pre)
      apply assumption+
    apply (rule exI)
    apply (rule exI)
    apply (rule conjI)
     apply (rule exI[of _ "id"])
     apply (rule conjI bij_id supp_id_bound id_on_id)+
    apply (drule sym)
    unfolding term.permute_id0 term_pre.map_id map_term_pre_inv_simp
    unfolding map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] map_sum_def sum.case
      map_prod_def prod.case id_def
    apply assumption
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
unfolding set2_term_pre_def set3_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] sum_set_simps
    map_sum_def sum.case Union_empty Un_empty_left map_prod_def prod.case prod_set_simps
      ccpo_Sup_singleton Un_empty_right id_on_def image_single[symmetric]
  unfolding term.FVars_permute[OF bij_imp_bij_inv supp_inv_bound]
  unfolding image_single image_set_diff[OF bij_is_inj[OF bij_imp_bij_inv], symmetric]
    image_in_bij_eq[OF bij_imp_bij_inv] inv_inv_eq image_in_bij_eq[OF term.permute_bij[OF bij_imp_bij_inv supp_inv_bound]]
  term.permute_inv_simp[OF bij_imp_bij_inv supp_inv_bound] inv_simp2
  unfolding term.permute_comp[OF bij_imp_bij_inv supp_inv_bound] inv_o_simp2 term.permute_id
  apply (rule conjI bij_imp_bij_inv supp_inv_bound singletonI | assumption)+
  done
  done

lemma Abs_avoid: "|A::var set| <o |UNIV::var set| \<Longrightarrow> \<exists>x' e'. Inp y x e = Inp y x' e' \<and> x' \<notin> A"
  apply (erule term.TT_fresh_cases[of _ "Inp y x e"])
   apply (drule sym)
  apply (frule Abs_set3)
  apply (erule exE conjE)+
  apply (rule exI)+
  apply (rule conjI)
   apply (rule trans)
    apply (rule sym)
    apply assumption
  apply (rotate_tac 3)
   apply assumption
  apply (drule iffD1[OF disjoint_iff])
  apply (erule allE)
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma Abs_rrename:
"bij (\<sigma>::var\<Rightarrow>var) \<Longrightarrow> |supp \<sigma>| <o |UNIV:: var set| \<Longrightarrow>
 (\<And>a'. a' \<in> FVars_term e - {a::var} \<Longrightarrow> \<sigma> a' = a') \<Longrightarrow> Inp b a e = Inp b (\<sigma> a) (permute_term \<sigma> e)"
  using term.inject id_on_def
  by (smt (verit, ccfv_SIG) term.permute(8) term.permute_cong_id term.set(8))

(* Bound properties (needed as auxiliaries): *)

lemma supp_swap_bound[simp,intro!]: "|supp (x \<leftrightarrow> xx)| <o |UNIV:: var set|"
by (simp add: cinfinite_imp_infinite term.UNIV_cinfinite)


(* Swapping and unary substitution, as abbreviations: *)
abbreviation "sswap P (x::var) y \<equiv> rrename (x \<leftrightarrow> y) P"
abbreviation usub :: "trm \<Rightarrow> var \<Rightarrow> var \<Rightarrow> trm" ("_[_'/_]" [900, 400, 400] 900)
  where "usub P (y::var) x \<equiv> vvsubst (id(x:=y)) P"

(* *)

lemma usub_swap_disj:
assumes "{u,v} \<inter> {x,y} = {}"
shows "usub (sswap P u v) x y = sswap (usub P x y) u v"
proof-
  note term.vvsubst_permute[simp del]
  show ?thesis using assms
  apply(subst term.vvsubst_permute[symmetric]) apply auto
  apply(subst term.map_comp) apply auto
  apply(subst term.vvsubst_permute[symmetric]) apply auto
  apply(subst term.map_comp) apply auto
  apply(rule term.map_cong0)
    using term_pre.supp_comp_bound apply auto
    by (smt (verit, ccfv_SIG) swap_simps(1,2,3))
qed

lemma rrename_o_swap:
"rrename ((y::var) \<leftrightarrow> yy o x \<leftrightarrow> xx) P =
 sswap (sswap P x xx) y yy"
apply(subst term.permute_comp[symmetric])
by auto

(* *)

lemma sswap_simps[simp]: "sswap Zero (y::var) x = Zero"
"sswap (Sum P Q) (y::var) x = Sum (sswap P y x) (sswap Q y x)"
"sswap (Par P Q) (y::var) x = Par (sswap P y x) (sswap Q y x)"
"sswap (Bang P) (y::var) x = Bang (sswap P y x)"
"sswap (Match u v P) (y::var) x = Match ((y \<leftrightarrow> x) u) ((y \<leftrightarrow> x) v) (sswap P y x)"
"sswap (Out u v P) (y::var) x = Out ((y \<leftrightarrow> x) u) ((y \<leftrightarrow> x) v) (sswap P y x)"
"sswap (Inp u v P) (y::var) x = Inp ((y \<leftrightarrow> x) u) ((y \<leftrightarrow> x) v) (sswap P y x)"
"sswap (Res v P) (y::var) x = Res ((y \<leftrightarrow> x) v) (sswap P y x)"
  by auto

lemma FFVars_swap[simp]: "FFVars (sswap P y x) =
 (x \<leftrightarrow> y) ` (FFVars P)"
apply(subst term.FVars_permute) by (auto simp: swap_sym)

lemma FFVars_swap'[simp]: "{x::var,y} \<inter> FFVars P = {} \<Longrightarrow> sswap P x y = P"
apply(rule term.permute_cong_id) apply auto by (metis swap_def)

(* *)

lemma Inp_inject_swap': "Inp u v P = Inp u' v' P' \<longleftrightarrow>
  u = u' \<and>
  (\<exists>z. (z \<notin> FFVars P \<or> z = v) \<and> (z \<notin> FFVars P' \<or> z = v') \<and>
       sswap P z v = sswap P' z v')"
  by (smt (z3) swap_sym term.inject(6))

lemma Inp_refresh': "v' \<notin> FFVars P \<or> v' = v \<Longrightarrow>
   Inp u v P = Inp u v' (sswap P v' v)"
  by (simp add: swap_sym)

lemma Inp_refresh:
"xx \<notin> FFVars P \<or> xx = x \<Longrightarrow> Inp a x P = Inp a xx (sswap P x xx)"
  using Inp_refresh' by simp

(* *)

lemma Res_inject_swap': "Res v P = Res v' P' \<longleftrightarrow>
  (\<exists>z. (z \<notin> FFVars P \<or> z = v) \<and> (z \<notin> FFVars P' \<or> z = v') \<and>
       sswap P z v = sswap P' z v')"
  by (smt (verit, ccfv_threshold) swap_sym term.inject(7))

lemma Res_refresh': "v' \<notin> FFVars P \<or> v' = v \<Longrightarrow>
   Res v P = Res v' (sswap P v' v)"
  by (simp add: swap_sym)

lemma Res_refresh:
"xx \<notin> FFVars P \<or> xx = x \<Longrightarrow> Res x P = Res xx (sswap P x xx)"
  using Res_refresh' by simp
(* *)

lemma FFVars_usub[simp]: "FFVars (usub P y x) =
 (if x \<in> FFVars P then FFVars P - {x} \<union> {y} else FFVars P)"
apply(subst term.set_map) by auto

lemma usub_simps_free[simp]: "\<And>y x. usub Zero (y::var) x = Zero"
"\<And>y x P Q. usub (Sum P Q) (y::var) x = Sum (usub P y x) (usub Q y x)"
"\<And>y x P Q. usub (Par P Q) (y::var) x = Par (usub P y x) (usub Q y x)"
"\<And>y x P. usub (Bang P) (y::var) x = Bang (usub P y x)"
"\<And>y x u v P. usub (Match u v P) (y::var) x = Match (sb u y x) (sb v y x) (usub P y x)"
"usub (Out u v P) (y::var) x = Out (sb u y x) (sb v y x) (usub P y x)"
by (auto simp: sb_def)

lemma usub_Inp'[simp]:
"v \<notin> {x,y} \<Longrightarrow> u \<noteq> v \<Longrightarrow> usub (Inp u v P) (y::var) x = Inp (sb u y x) v (usub P y x)"
apply(subst term.map)
  subgoal by auto
  subgoal by (auto simp: imsupp_def supp_def)
  subgoal by auto
  subgoal by (auto simp: sb_def) .

lemma usub_Inp[simp]:
assumes v: "v \<notin> {x,y}"
shows "usub (Inp u v P) (y::var) x = Inp (sb u y x) v (usub P y x)"
proof-
  obtain v' where v': "v' \<notin> {u,v,x,y}" "v' \<notin> FFVars P"
  using exists_fresh[of "[u,v,x,y]" "[P]"] by auto
  define P' where P': "P' = sswap P v' v"
  have 0: "Inp u v P = Inp u v' P'" unfolding v' P'
    using Inp_refresh' v'(2) by blast
  have 1: "usub P' y x = sswap (usub P y x) v' v"
  unfolding P' apply(rule usub_swap_disj) using v v' by auto
  have 2: "Inp (sb u y x) v (usub P y x) = Inp (sb u y x) v' (usub P' y x)"
  using v v' unfolding v' 1  unfolding term.inject
  by (metis FFVars_usub Un_iff insert_Diff insert_iff swap_sym)
  show ?thesis using v' unfolding 0 2 by auto
qed

lemma usub_Res[simp]:
"v \<notin> {x,y} \<Longrightarrow> usub (Res v P) (y::var) x = Res v (usub P y x)"
apply(subst term.map)
  subgoal by auto
  subgoal by (auto simp: imsupp_def supp_def)
  subgoal by auto .

lemmas usub_simps = usub_simps_free usub_Inp usub_Res


(* *)



lemma rrename_usub[simp]:
assumes \<sigma>: "bij \<sigma>" "|supp \<sigma>| <o |UNIV::var set|"
shows "rrename \<sigma> (usub P u (x::var)) = usub (rrename \<sigma> P) (\<sigma> u) (\<sigma> x)"
using assms
apply(binder_induction P avoiding: "supp \<sigma>" u x rule: term.strong_induct)
using assms by (auto simp: sb_def bij_implies_inject)

lemma sw_sb:
"sw (sb z u x) z1 z2 = sb (sw z z1 z2) (sw u z1 z2) (sw x z1 z2)"
unfolding sb_def sw_def by auto


lemma swap_usub:
"sswap (usub P (u::var) x) z1 z2 = usub (sswap P z1 z2) ((z1 \<leftrightarrow> z2) u) ((z1 \<leftrightarrow> z2) x)"
apply(binder_induction P avoiding: u x z1 z2 rule: term.strong_induct)
  subgoal
  apply(subst sswap_simps) apply(subst usub_simps) by auto
  subgoal apply(subst sswap_simps | subst usub_simps)+ by presburger
  subgoal apply(subst sswap_simps | subst usub_simps)+ by presburger
  subgoal apply(subst sswap_simps | subst usub_simps)+ by presburger
  subgoal apply(subst sswap_simps | subst usub_simps)+
    by (metis Pi.supp_swap_bound Swapping.bij_swap rrename_usub sswap_simps(5) usub_simps_free(5))
  subgoal apply(subst sswap_simps | subst usub_simps)+
    by (metis Pi.supp_swap_bound Swapping.bij_swap rrename_usub sswap_simps(6) usub_simps_free(6))
  subgoal apply(subst sswap_simps | subst usub_simps)+
    subgoal by auto
    subgoal apply(subst sswap_simps | subst usub_simps)+
      subgoal unfolding sw_def sb_def
        by (meson Swapping.bij_swap bij_implies_inject insertE singleton_iff)
      by (simp add: bij_implies_inject sb_def)
    done
  subgoal apply(subst sswap_simps | subst usub_simps)+
    subgoal by auto
    subgoal apply(subst sswap_simps | subst usub_simps)+
      subgoal unfolding sw_def sb_def apply auto
        by (metis swap_def)+
      unfolding sw_sb by presburger . .

lemma usub_refresh:
assumes "xx \<notin> FFVars P \<or> xx = x"
shows "usub P u x = usub (sswap P x xx) u xx"
proof-
  note term.vvsubst_permute[simp del]
  show ?thesis using assms
  apply(subst term.vvsubst_permute[symmetric]) apply simp
    subgoal by auto
    subgoal apply(subst term.map_comp)
      subgoal by auto
      subgoal by auto
      subgoal apply(rule term.map_cong0)
        using term_pre.supp_comp_bound apply auto
         apply (smt (verit, ccfv_threshold) swap_simps(3))
        by (smt (verit, best) swap_simps(3))
        . .
qed

lemma Inp_eq_usub: 
  assumes il: "Inp x y Q = Inp x y' Q'"
  shows "usub Q z y = usub Q' z y'"
  using il usub_refresh by auto

lemma swap_commute:
"{y,yy} \<inter> {x,xx} = {} \<Longrightarrow>
 sswap (sswap P y yy) x xx = sswap (sswap P x xx) y yy"
apply(subst term.permute_comp)
apply auto
apply(subst term.permute_comp)
apply auto
apply(rule term.permute_cong)
      apply (auto simp: term_pre.supp_comp_bound)
  by (simp add: swap_def)

end
