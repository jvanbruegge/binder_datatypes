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

lemma Inp_inject: "(Inp x y e = Inp x' y' e') \<longleftrightarrow>
  x = x' \<and>
  (\<exists>f. bij f \<and> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set|
  \<and> id_on (FVars_term e - {y}) f \<and> f y = y' \<and> permute_term f e = e')"
  unfolding term.set
  unfolding Inp_def term.TT_inject0 map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_term_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_term_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_term_pre_def
    Un_empty_right UN_single by auto

lemma Res_inject: "(Res y e = Res y' e') \<longleftrightarrow>
  (\<exists>f. bij f \<and> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set|
  \<and> id_on (FVars_term e - {y}) f \<and> f y = y' \<and> permute_term f e = e')"
  unfolding term.set
  unfolding Res_def term.TT_inject0 map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_term_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_term_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_term_pre_def
    Un_empty_right UN_single by auto

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
  using Inp_inject id_on_def by blast

(* Bound properties (needed as auxiliaries): *)

lemma supp_swap_bound[simp,intro!]: "|supp (id(x::var := xx, xx := x))| <o |UNIV:: var set|"
by (simp add: cinfinite_imp_infinite supp_swap_bound term.UNIV_cinfinite)


(* Swapping and unary substitution, as abbreviations: *)
abbreviation "swap P (x::var) y \<equiv> rrename (id(x:=y,y:=x)) P"
abbreviation usub :: "trm \<Rightarrow> var \<Rightarrow> var \<Rightarrow> trm" ("_[_'/_]" [900, 400, 400] 900)
  where "usub P (y::var) x \<equiv> vvsubst (id(x:=y)) P"

(* *)

lemma usub_swap_disj:
assumes "{u,v} \<inter> {x,y} = {}"
shows "usub (swap P u v) x y = swap (usub P x y) u v"
proof-
  note term.vvsubst_permute[simp del]
  show ?thesis using assms
  apply(subst term.vvsubst_permute[symmetric]) apply auto
  apply(subst term.map_comp) apply auto
  apply(subst term.vvsubst_permute[symmetric]) apply auto
  apply(subst term.map_comp) apply auto
  apply(rule term.map_cong0)
    using term_pre.supp_comp_bound by auto
qed

lemma rrename_o_swap:
"rrename (id(y::var := yy, yy := y) o id(x := xx, xx := x)) P =
 swap (swap P x xx) y yy"
apply(subst term.permute_comp[symmetric])
by auto

(* *)

lemma swap_simps[simp]: "swap Zero (y::var) x = Zero"
"swap (Sum P Q) (y::var) x = Sum (swap P y x) (swap Q y x)"
"swap (Par P Q) (y::var) x = Par (swap P y x) (swap Q y x)"
"swap (Bang P) (y::var) x = Bang (swap P y x)"
"swap (Match u v P) (y::var) x = Match (sw u y x) (sw v y x) (swap P y x)"
"swap (Out u v P) (y::var) x = Out (sw u y x) (sw v y x) (swap P y x)"
"swap (Inp u v P) (y::var) x = Inp (sw u y x) (sw v y x) (swap P y x)"
"swap (Res v P) (y::var) x = Res (sw v y x) (swap P y x)"
by (auto simp: sw_def)

lemma FFVars_swap[simp]: "FFVars (swap P y x) =
 (\<lambda>u. sw u x y) ` (FFVars P)"
apply(subst term.FVars_permute) by (auto simp: sw_def)

lemma FFVars_swap'[simp]: "{x::var,y} \<inter> FFVars P = {} \<Longrightarrow> swap P x y = P"
apply(rule term.permute_cong_id) by auto

(* *)

lemma Inp_inject_swap: "Inp u v P = Inp u' v' P' \<longleftrightarrow>
  u = u' \<and> (v' \<notin> FFVars P \<or> v' = v) \<and> swap P v' v = P'"
unfolding Inp_inject apply(rule iffI)
  subgoal unfolding id_on_def apply (auto simp: bij_implies_inject)
  apply(rule term.permute_cong) by (auto simp: bij_implies_inject)
  subgoal apply clarsimp
  apply(rule exI[of _ "id(v':=v,v:=v')"]) unfolding id_on_def by auto .

lemma Inp_inject_swap': "Inp u v P = Inp u' v' P' \<longleftrightarrow>
  u = u' \<and>
  (\<exists>z. (z \<notin> FFVars P \<or> z = v) \<and> (z \<notin> FFVars P' \<or> z = v') \<and>
       swap P z v = swap P' z v')"
unfolding Inp_inject_swap apply(rule iffI)
  subgoal apply clarsimp apply(rule exI[of _ v']) by auto
  subgoal by (metis Inp_inject_swap) .

lemma Inp_refresh': "v' \<notin> FFVars P \<or> v' = v \<Longrightarrow>
   Inp u v P = Inp u v' (swap P v' v)"
using Inp_inject_swap by auto

lemma Inp_refresh:
"xx \<notin> FFVars P \<or> xx = x \<Longrightarrow> Inp a x P = Inp a xx (swap P x xx)"
using Inp_refresh'
  by (metis Inp_refresh' fun_upd_twist)

(* *)

lemma Res_inject_swap: "Res v P = Res v' P' \<longleftrightarrow>
  (v' \<notin> FFVars P \<or> v' = v) \<and> swap P v' v = P'"
unfolding Res_inject apply(rule iffI)
  subgoal unfolding id_on_def apply (auto simp: bij_implies_inject)
  apply(rule term.permute_cong) by (auto simp: bij_implies_inject)
  subgoal apply clarsimp
  apply(rule exI[of _ "id(v':=v,v:=v')"]) unfolding id_on_def by auto .

lemma Res_inject_swap': "Res v P = Res v' P' \<longleftrightarrow>
  (\<exists>z. (z \<notin> FFVars P \<or> z = v) \<and> (z \<notin> FFVars P' \<or> z = v') \<and>
       swap P z v = swap P' z v')"
unfolding Res_inject_swap apply(rule iffI)
  subgoal apply clarsimp apply(rule exI[of _ v']) by auto
  subgoal by (metis Inp_inject_swap)  .

lemma Res_refresh': "v' \<notin> FFVars P \<or> v' = v \<Longrightarrow>
   Res v P = Res v' (swap P v' v)"
using Res_inject_swap by auto

lemma Res_refresh:
"xx \<notin> FFVars P \<or> xx = x \<Longrightarrow> Res x P = Res xx (swap P x xx)"
by (metis Res_inject_swap fun_upd_twist)

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
  define P' where P': "P' = swap P v' v"
  have 0: "Inp u v P = Inp u v' P'" unfolding v' P'
    using Inp_inject_swap v'(2) by blast
  have 1: "usub P' y x = swap (usub P y x) v' v"
  unfolding P' apply(rule usub_swap_disj) using v v' by auto
  have 2: "Inp (sb u y x) v (usub P y x) = Inp (sb u y x) v' (usub P' y x)"
  using v v' unfolding v' 1  unfolding Inp_inject_swap by auto
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
"swap (usub P (u::var) x) z1 z2 = usub (swap P z1 z2) (sw u z1 z2) (sw x z1 z2)"
apply(binder_induction P avoiding: u x z1 z2 rule: term.strong_induct)
  subgoal
  apply(subst swap_simps) apply(subst usub_simps) by auto
  subgoal apply(subst swap_simps | subst usub_simps)+ by presburger
  subgoal apply(subst swap_simps | subst usub_simps)+ by presburger
  subgoal apply(subst swap_simps | subst usub_simps)+ by presburger
  subgoal apply(subst swap_simps | subst usub_simps)+
  unfolding sw_sb by presburger
  subgoal apply(subst swap_simps | subst usub_simps)+
  unfolding sw_sb by presburger
  subgoal apply(subst swap_simps | subst usub_simps)+
    subgoal by auto
    subgoal apply(subst swap_simps | subst usub_simps)+
      subgoal unfolding sw_def sb_def by auto
      unfolding sw_sb by presburger .
  subgoal apply(subst swap_simps | subst usub_simps)+
    subgoal by auto
    subgoal apply(subst swap_simps | subst usub_simps)+
      subgoal unfolding sw_def sb_def by auto
      unfolding sw_sb by presburger . .

lemma usub_refresh:
assumes "xx \<notin> FFVars P \<or> xx = x"
shows "usub P u x = usub (swap P x xx) u xx"
proof-
  note term.vvsubst_permute[simp del]
  show ?thesis using assms
  apply(subst term.vvsubst_permute[symmetric]) apply simp
    subgoal by auto
    subgoal apply(subst term.map_comp)
      subgoal by auto
      subgoal by auto
      subgoal apply(rule term.map_cong0)
      using term_pre.supp_comp_bound by auto . .
qed

lemma Inp_eq_usub: 
  assumes il: "Inp x y Q = Inp x y' Q'"
  shows "usub Q z y = usub Q' z y'"
  by (metis (no_types, lifting) Inp_inject_swap Inp_refresh il usub_refresh)

lemma swap_commute:
"{y,yy} \<inter> {x,xx} = {} \<Longrightarrow>
 swap (swap P y yy) x xx = swap (swap P x xx) y yy"
apply(subst term.permute_comp)
apply auto
apply(subst term.permute_comp)
apply auto
apply(rule term.permute_cong)
by (auto simp: term_pre.supp_comp_bound)

end
