theory SystemF
  imports "thys/MRBNF_Recursor" "HOL-Library.FSet"
begin

datatype \<kappa> = Star ("\<star>") | Arrow \<kappa> \<kappa> (infixr "\<rightarrow>" 40)
(* binder datatype 'a \<tau> = TyVar 'a | Arrow "'a \<tau>" "'a \<tau>" (infixr "\<rightarrow>" 40)
                          | TyApp "'a \<tau>" "'a \<tau>" (infixr "@" 40)
                          | TyAll \<alpha>::'a bound::"'a \<tau>" tybody::"'a \<tau>" binds \<alpha> in tybody (infixr "\<forall>_<_._" 30)

*)
ML \<open>
val tyctors = [
  (("TyVar", (NONE : mixfix option)), [@{typ 'var}]),
  (("TyArr", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("TyApp", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("TyAll", NONE), [@{typ 'bvar}, @{typ 'brec}])
]
val tyspec = {
  fp_b = @{binding "\<tau>"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = tyctors,
  map_b = @{binding ty_vvsubst},
  tvsubst_b = @{binding ty_tvsubst}
}
\<close>
declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Sugar.create_binder_datatype tyspec lthy
in lthy' end\<close>
print_theorems
print_mrbnfs


(* binder_datatype ('a,'b) term =
  Var 'b
| App "('a,'b) term" "('a,'b) term"
| Lam x::'b ty::"'a \<tau>" t::"('a,'b) term" binds x in t
| TyApp "('a,'b) term" "'a \<tau>"
| TyLam \<alpha>::'a body::"('a,'b) term" binds \<alpha> in body
*)

ML \<open>
val ctors = [
  (("Var", (NONE : mixfix option)), [@{typ 'var}]),
  (("App", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("Lam", NONE), [@{typ 'bvar}, @{typ "'tyvar \<tau>"}, @{typ 'brec}]),
  (("TyApp", NONE), [@{typ 'rec}, @{typ "'tyvar \<tau>"}]),
  (("TyLam", NONE), [@{typ 'btyvar}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "term"},
  vars = [
    (dest_TFree @{typ 'tyvar}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'btyvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0], [0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst},
  tvsubst_b = @{binding tvsubst}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Sugar.create_binder_datatype spec lthy
in lthy' end\<close>
print_theorems
print_mrbnfs

(* unary substitution *)
lemma IImsupp_VVr_empty: "IImsupp VVr = {}"
  unfolding IImsupp_def SSupp_VVr_empty UN_empty Un_empty_left
  apply (rule refl)
  done

lemma tvsubst_VVr_func: "tvsubst VVr t = t"
  apply (rule terms.TT_plain_co_induct)
  subgoal for x
    apply (rule case_split[of "isVVr (terms_ctor x)"])
     apply (unfold isVVr_def)[1]
     apply (erule exE)
    subgoal premises prems for a
      unfolding prems
      apply (rule tvsubst_VVr)
      apply (rule SSupp_VVr_bound)
        done
      apply (rule trans)
       apply (rule tvsubst_cctor_not_isVVr)
          apply (rule SSupp_VVr_bound)
      unfolding IImsupp_VVr_empty
         apply (rule Int_empty_right)
      unfolding tvnoclash_terms_def Int_Un_distrib Un_empty
        apply (rule conjI)
         apply (rule iffD2[OF disjoint_iff], rule allI, rule impI, assumption)
        apply (rule iffD2[OF disjoint_iff], rule allI, rule impI)
      unfolding UN_iff Set.bex_simps
        apply (rule ballI)
        apply assumption+
      apply (rule arg_cong[of _ _ terms_ctor])
      apply (rule trans)
      apply (rule terms_pre.map_cong)
                 apply (rule supp_id_bound bij_id)+
           apply (assumption | rule refl)+
      unfolding id_def[symmetric] terms_pre.map_id
      apply (rule refl)
      done
    done

lemma finite_singleton: "finite {x}" by blast
lemma singl_bound: "|{a}| <o |UNIV::'a::var_terms_pre set|"
  by (rule finite_ordLess_infinite2[OF finite_singleton cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite]])

lemma SSupp_upd_bound:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a terms"
  shows "|SSupp (f (a:=t))| <o |UNIV::'a set| \<longleftrightarrow> |SSupp f| <o |UNIV::'a set|"
  unfolding SSupp_def
  apply (auto simp only: fun_upd_apply singl_bound ordLeq_refl split: if_splits
      elim!: ordLeq_ordLess_trans[OF card_of_mono1 ordLess_ordLeq_trans[OF terms_pre.Un_bound], rotated]
      intro: card_of_mono1)
  done

corollary SSupp_upd_VVr_bound: "|SSupp (VVr(a:=(t::'a::var_terms_pre terms)))| <o |UNIV::'a set|"
  apply (rule iffD2[OF SSupp_upd_bound])
  apply (rule SSupp_VVr_bound)
  done

lemma supp_subset_id_on: "supp f \<subseteq> A \<Longrightarrow> id_on (B - A) f"
  unfolding supp_def id_on_def by blast

lemma rrename_simps:
  assumes "bij (f::'a::var_terms_pre \<Rightarrow> 'a)" "|supp f| <o |UNIV::'a set|"
  shows "rrename_terms f (Var a) = Var (f a)"
    "rrename_terms f (App e1 e2) = App (rrename_terms f e1) (rrename_terms f e2)"
    "rrename_terms f (Abs x \<tau> e) = Abs (f x) \<tau> (rrename_terms f e)"
  unfolding Var_def App_def Abs_def terms.rrename_cctors[OF assms] map_terms_pre_def comp_def
    Abs_terms_pre_inverse[OF UNIV_I] map_sum_def sum.case map_prod_def prod.case id_def
    apply (rule refl)+
  done

lemma App_inject[simp]: "(App a b = App c d) = (a = c \<and> b = d)"
proof
  assume "App a b = App c d"
  then show "a = c \<and> b = d"
    unfolding App_def fun_eq_iff terms.TT_injects0
      map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] map_sum_def sum.case prod.map_id
      Abs_terms_pre_inject[OF UNIV_I UNIV_I]
    by blast
qed simp
lemma Var_inject[simp]: "(Var a = Var b) = (a = b)"
  apply (rule iffI[rotated])
   apply (rule arg_cong[of _ _ Var])
  apply assumption
  unfolding Var_def terms.TT_injects0 map_terms_pre_def comp_def map_sum_def sum.case Abs_terms_pre_inverse[OF UNIV_I]
  id_def Abs_terms_pre_inject[OF UNIV_I UNIV_I] sum.inject
  apply (erule exE conjE)+
  apply assumption
  done
lemma Abs_inject: "(Abs x \<tau> e = Abs x' \<tau>' e') = (\<exists>f. bij f \<and> |supp (f::'a::var_terms_pre \<Rightarrow> 'a)| <o |UNIV::'a set|
  \<and> id_on (FFVars_terms (Abs x \<tau> e)) f \<and> f x = x' \<and> \<tau> = \<tau>' \<and> rrename_terms f e = e')"
  unfolding terms.set
  unfolding Abs_def terms.TT_injects0 map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_terms_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_terms_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_terms_pre_def
    Un_empty_right UN_single
  apply (rule refl)
  done

lemma bij_map_terms_pre: "bij f \<Longrightarrow> |supp (f::'a::var_terms_pre \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij (map_terms_pre (id::_::var_terms_pre \<Rightarrow> _) f (rrename_terms f) id)"
  apply (rule iffD2[OF bij_iff])
    apply (rule exI[of _ "map_terms_pre id (inv f) (rrename_terms (inv f)) id"])
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
   apply assumption
  apply (rule conjI)
   apply (rule trans)
    apply (rule terms_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 terms.rrename_comp0s terms.rrename_id0s
  apply (rule terms_pre.map_id0)
  apply (rule trans)
   apply (rule terms_pre.map_comp0[symmetric])
        apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp2 terms.rrename_comp0s terms.rrename_id0s
  apply (rule terms_pre.map_id0)
  done

lemma map_terms_pre_inv_simp: "bij f \<Longrightarrow> |supp (f::'a::var_terms_pre \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> inv (map_terms_pre (id::_::var_terms_pre \<Rightarrow> _) f (rrename_terms f) id) = map_terms_pre id (inv f) (rrename_terms (inv f)) id"
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
  apply assumption
  apply (rule inv_unique_comp)
   apply (rule trans)
    apply (rule terms_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
   defer
  apply (rule trans)
    apply (rule terms_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 inv_o_simp2 terms.rrename_comp0s terms.rrename_id0s terms_pre.map_id0
   apply (rule refl)+
  done

lemma Abs_set3: "terms_ctor v = Abs x \<tau> e \<Longrightarrow> \<exists>x' e'. terms_ctor v = Abs x' \<tau> e' \<and> x' \<in> set2_terms_pre v \<and> e' \<in> set3_terms_pre v"
  unfolding Abs_def terms.TT_injects0
  apply (erule exE)
  apply (erule conjE)+
  subgoal for f
apply (drule iffD2[OF bij_imp_inv', rotated, of "map_terms_pre id f (rrename_terms f) id"])
     apply (rule bij_map_terms_pre)
      apply assumption+
    apply (rule exI)
    apply (rule exI)
    apply (rule conjI)
     apply (rule exI[of _ "id"])
     apply (rule conjI bij_id supp_id_bound id_on_id)+
    apply (drule sym)
    unfolding terms.rrename_id0s terms_pre.map_id map_terms_pre_inv_simp
    unfolding map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] map_sum_def sum.case
      map_prod_def prod.case id_def
    apply assumption
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
unfolding set2_terms_pre_def set3_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] sum_set_simps
    map_sum_def sum.case Union_empty Un_empty_left map_prod_def prod.case prod_set_simps
      ccpo_Sup_singleton Un_empty_right id_on_def image_single[symmetric]
  unfolding terms.FFVars_rrenames[OF bij_imp_bij_inv supp_inv_bound]
  unfolding image_single image_set_diff[OF bij_is_inj[OF bij_imp_bij_inv], symmetric]
    image_in_bij_eq[OF bij_imp_bij_inv] inv_inv_eq image_in_bij_eq[OF terms.rrename_bijs[OF bij_imp_bij_inv supp_inv_bound]]
  terms.rrename_inv_simps[OF bij_imp_bij_inv supp_inv_bound] inv_simp2
  unfolding terms.rrename_comps[OF bij_imp_bij_inv supp_inv_bound] inv_o_simp2 terms.rrename_ids
  apply (rule conjI bij_imp_bij_inv supp_inv_bound singletonI | assumption)+
  done
  done

lemma Abs_avoid: "|A::'a::var_terms_pre set| <o |UNIV::'a set| \<Longrightarrow> \<exists>x' e'. Abs x \<tau> e = Abs x' \<tau> e' \<and> x' \<notin> A"
  apply (drule terms.TT_fresh_nchotomys[of _ "Abs x \<tau> e"])
  apply (erule exE)
  apply (erule conjE)
   apply (drule sym)
  apply (frule Abs_set3)
  apply (erule exE conjE)+
  apply (rule exI)+
  apply (rule conjI)
   apply (rule trans)
    apply (rule sym)
    apply assumption
  apply (rotate_tac 2)
   apply assumption
  apply (drule iffD1[OF disjoint_iff])
  apply (erule allE)
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma VVr_eq_Var: "VVr a = Var a"
  unfolding VVr_def Var_def comp_def \<eta>_def
  by (rule refl)

(* small step semantics *)
no_notation Set.member  ("(_/ : _)" [51, 51] 50)

definition fresh :: "'a::var_terms_pre \<Rightarrow> ('a * 'b) fset \<Rightarrow> bool" ("(_/ \<sharp> _)" [51, 51] 50) where
  "fresh x \<Gamma> \<equiv> x |\<notin>| fst |`| \<Gamma>"

lemma isin_rename: "bij f \<Longrightarrow> (f x, \<tau>) |\<in>| map_prod f id |`| \<Gamma> \<longleftrightarrow> (x, \<tau>) |\<in>| \<Gamma>"
  by force

abbreviation extend :: "('a * \<tau>) fset \<Rightarrow> 'a::var_terms_pre \<Rightarrow> \<tau> \<Rightarrow> ('a * \<tau>) fset" ("(_,_:_)" [52, 52, 52] 53) where
  "extend \<Gamma> a \<tau> \<equiv> finsert (a, \<tau>) \<Gamma>"

inductive Step :: "'a::var_terms_pre terms \<Rightarrow> 'a terms \<Rightarrow> bool" (infixr "\<^bold>\<longrightarrow>" 25) where
  ST_Beta: "App (Abs x \<tau> e) e2 \<^bold>\<longrightarrow> tvsubst (VVr(x:=e2)) e"
| ST_App: "e1 \<^bold>\<longrightarrow> e1' \<Longrightarrow> App e1 e2 \<^bold>\<longrightarrow> App e1' e2"

inductive Ty :: "('a::var_terms_pre * \<tau>) fset \<Rightarrow> 'a terms \<Rightarrow> \<tau> \<Rightarrow> bool" ("_ \<turnstile>\<^sub>t\<^sub>y _ : _" [25, 25, 25] 26) where
  Ty_Var: "(x, \<tau>) |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y Var x : \<tau>"
| Ty_App: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y e1 : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2 ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y e2 : \<tau>\<^sub>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y App e1 e2 : \<tau>\<^sub>2"
| Ty_Abs: "\<lbrakk> x \<sharp> \<Gamma> ; \<Gamma>,x:\<tau> \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y Abs x \<tau> e : \<tau> \<rightarrow> \<tau>\<^sub>2"

binder_inductive Ty where 3: x
  sorry
print_theorems

lemma provided:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows
    (* equivariance *)
    "(x, \<tau>) |\<in>| \<Gamma> \<Longrightarrow> (f x, \<tau>) |\<in>| map_prod f id |`| \<Gamma>"
    "x \<sharp> \<Gamma> \<Longrightarrow> f x \<sharp> map_prod f id |`| \<Gamma>"
    (* equivariance of extend *)
    "map_prod f id |`| (\<Gamma>,x:\<tau>) = (map_prod f id |`| \<Gamma>),f x:\<tau>"
    (* freshness *)
    "\<lbrakk> x \<sharp> \<Gamma> ; \<Gamma>,x:\<tau> \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2 \<rbrakk> \<Longrightarrow> x \<notin> \<Union>(Basic_BNFs.fsts ` fset \<Gamma>)"
   apply (simp add: assms isin_rename)
  unfolding fresh_def
  apply (metis Product_Type.fst_comp_map_prod assms(1) bij_not_equal_iff fimageE fset.map_comp)
   apply simp
  using fmember.rep_eq image_iff apply fastforce
  done

lemma rename_Ty_aux:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes
    "bij f" "|supp f| <o |UNIV::'a set|" "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>'"
  shows "map_prod f id |`| \<Gamma> \<turnstile>\<^sub>t\<^sub>y vvsubst f e : \<tau>'"
  apply (rule Ty.induct[OF assms(3)])
  unfolding terms_vvsubst_rrename[OF assms(1,2)] rrename_simps[OF assms(1,2)]
    apply (rule Ty_Var)
    apply (rule provided)
      apply (rule assms)+
  apply assumption
   apply (rule Ty_App)
    apply assumption+
  apply (rule Ty_Abs)
   apply (rule provided)
     apply (rule assms)+
   apply assumption
  unfolding provided[OF assms(1,2)]
  apply assumption
  done

lemma rename_Ty:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>' \<longleftrightarrow> map_prod f id |`| \<Gamma> \<turnstile>\<^sub>t\<^sub>y vvsubst f e : \<tau>'"
  apply (rule iffI)
   apply (rule rename_Ty_aux)
     apply (rule assms)+
   apply assumption
  apply (drule rename_Ty_aux[rotated -1])
    apply (rule bij_imp_bij_inv)
    apply (rule assms)
   apply (rule supp_inv_bound)
    apply (rule assms)+
  unfolding terms.map_comp[OF assms(2) supp_inv_bound[OF assms]]
    inv_o_simp1[OF assms(1)] terms.map_id map_prod.comp id_o map_prod.id fset.map_comp fset.map_id
  apply assumption
  done

definition cl :: "(('a::var_terms_pre \<times> \<tau>) fset \<Rightarrow> 'a terms \<Rightarrow> \<tau> \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> \<tau>) fset \<Rightarrow> 'a terms \<Rightarrow> \<tau> \<Rightarrow> 'b \<Rightarrow> bool" where
  "cl P \<Gamma> e \<tau> \<rho> \<equiv> (\<forall>f. bij f \<and> |supp f| <o |UNIV::'a set| \<longrightarrow> P (map_prod f id |`| \<Gamma>) (vvsubst f e) \<tau> \<rho>)"

lemmas clI = allI[THEN iffD2[OF meta_eq_to_obj_eq[OF cl_def]], unfolded atomize_imp[symmetric]]

lemma clD:
  fixes e::"'a::var_terms_pre terms" and f::"'a \<Rightarrow> 'a"
assumes "cl P \<Gamma> e \<tau> \<rho>" and "bij f" "|supp f| <o |UNIV::'a set|"
shows "P (map_prod f id |`| \<Gamma>) (vvsubst f e) \<tau> \<rho>"
  apply (rule mp[OF spec[OF assms(1)[unfolded cl_def]]])
  apply (rule conjI)
   apply (rule assms)+
  done

lemma cl_ext: "cl P \<Gamma> e \<tau> \<rho> \<Longrightarrow> P \<Gamma> e \<tau> \<rho>"
  unfolding cl_def
  apply (erule allE)
  apply (erule impE)
   apply (rule conjI)
    apply (rule bij_id)
   apply (rule supp_id_bound)
  unfolding map_prod.id fset.map_id terms.map_id
  apply assumption
  done

lemma cl_vvsubst:
  fixes e::"'a::var_terms_pre terms"
  assumes f: "bij f" "|supp f| <o |UNIV::'a set|" and cl: "cl P \<Gamma> e \<tau> \<rho>"
  shows "cl P (map_prod f id |`| \<Gamma>) (vvsubst f e) \<tau> \<rho>"
  unfolding cl_def
  apply (rule allI impI)+
  apply (erule conjE)
  unfolding fset.map_comp terms.map_comp[OF f(2)] map_prod.comp id_o
  apply (rule clD[OF cl])
   apply (rule bij_comp)
    apply (rule f)
   apply assumption
  apply (rule supp_comp_bound)
    apply (rule f)
   apply assumption
  apply (rule cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite])
  done

lemma cl_cl: "cl (cl P) = cl P"
  unfolding cl_def
  apply (rule ext)+
  apply (rule iffI)
   apply (rule allI)
   apply (rule impI)
   apply (erule allE)
   apply (erule conjE)
   apply (erule impE)
    apply (rule conjI)
     apply assumption+
   apply (erule allE)
   apply (erule impE)
    apply (rule conjI)
     apply (rule bij_id)
    apply (rule supp_id_bound)
  unfolding map_prod.id fset.map_id terms.map_id
   apply assumption
  apply (rule allI impI)+
  apply (erule allE conjE)+
  apply (erule impE)
   defer
  unfolding fset.map_comp map_prod.comp id_o terms.map_comp
   apply assumption
  apply (rule conjI)
   apply (rule bij_comp)
    apply assumption+
  apply (rule supp_comp_bound)
    apply assumption+
  apply (rule cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite])
  done

lemma TT_inject: "(terms_ctor a = terms_ctor b) = (\<exists>(f::'a::var_terms_pre \<Rightarrow> 'a). bij f \<and> |supp f| <o |UNIV::'a set|
  \<and> id_on (\<Union>(FFVars_terms ` set3_terms_pre a) - set2_terms_pre a) f \<and> map_terms_pre id f (vvsubst f) id a = b)"
  unfolding terms.TT_injects0 conj_assoc[symmetric]
  apply (rule ex_cong)
  apply (erule conjE)+
  unfolding terms_vvsubst_rrename
  apply (rule refl)
  done

(*no_notation extend ("(_,_:_)")*)

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

lemma Ty_fresh_induct_param[consumes 1, case_names Bound Ty_Var Ty_App Ty_Abs]:
  fixes K::"'p \<Rightarrow> 'a::var_terms_pre set" and e::"'a terms"
  assumes x: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>" and bound: "\<forall>\<rho>. |K \<rho>| <o |UNIV::'a set|"
    and Ty_Var: "\<And>x \<tau> \<Gamma> \<rho>. (x, \<tau>) |\<in>| \<Gamma> \<Longrightarrow> P \<Gamma> (Var x) \<tau> \<rho>"
    and Ty_App: "\<And>\<Gamma> e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2 \<rho>. \<Gamma> \<turnstile>\<^sub>t\<^sub>y e1 : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2 \<Longrightarrow> \<forall>\<rho>. P \<Gamma> e1 (\<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2) \<rho>
      \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y e2 : \<tau>\<^sub>1 \<Longrightarrow> \<forall>\<rho>. P \<Gamma> e2 \<tau>\<^sub>1 \<rho> \<Longrightarrow> P \<Gamma> (App e1 e2) \<tau>\<^sub>2 \<rho>"
    and Ty_Abs: "\<And>x \<Gamma> \<tau> e \<tau>\<^sub>2 \<rho>. x \<notin> K \<rho> \<Longrightarrow> x \<sharp> \<Gamma> \<Longrightarrow> extend \<Gamma> x \<tau> \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2 \<Longrightarrow> \<forall>\<rho>. P (extend \<Gamma> x \<tau>) e \<tau>\<^sub>2 \<rho> \<Longrightarrow> P \<Gamma> (Abs x \<tau> e) (\<tau> \<rightarrow> \<tau>\<^sub>2) \<rho>"
  shows "\<forall>\<rho>. P \<Gamma> e \<tau> \<rho>"
  apply (rule allI)
  apply (rule cl_ext[of P])
  apply (rule spec[OF Ty.induct[OF x, of "\<lambda>\<Gamma> e \<tau>. \<forall>\<rho>. cl P \<Gamma> e \<tau> \<rho>"]])

  (* Nonbinding case *)
    apply (rule allI)
    apply (rule clI)
    apply (erule conjE)
  unfolding terms.map
    apply (rule Ty_Var)
    apply (rule provided)
      apply assumption+
  (* And again *)
  apply (rule allI)
   apply (rule clI)
   apply (erule conjE)
  unfolding terms.map
   apply (rule Ty_App)
      apply (assumption | (rule allI, (erule allE)+, rule clD[of P]) | rule iffD1[OF rename_Ty])+
  (* binding case *)
  subgoal for \<rho> x \<Gamma> \<tau> e \<tau>2
  apply (rule allI)
  apply (rule clI[of P])
    apply (erule conjE)
    subgoal for \<rho> f
      apply (rule exE[OF Abs_avoid])
       apply (rule terms_pre.Un_bound)
      apply (rule terms_pre.Un_bound)
        apply (rule iffD2[OF imsupp_supp_bound[OF cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite]]])
        apply assumption
        apply (rule spec[OF bound])
       apply (rule terms_pre.UNION_bound)
      apply (rule ordLess_ordLeq_trans[of "|fset \<Gamma>|"])
apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} "FSet.fset"))
      ) 1\<close>)
        apply (rule terms.var_large)
       apply (rule ordLess_ordLeq_trans[of "|Basic_BNFs.fsts _|"])
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name prod}))
      ) 1\<close>)
      apply (rule terms.var_large)
     apply (erule exE conjE)+

       apply (rule iffD2[OF fun_cong[of _ _ \<rho>]])
        apply (rule arg_cong3[OF refl _ refl, of _ _ P])
        apply (rule arg_cong2[OF refl, of _ _ vvsubst])
        apply assumption
      unfolding Un_iff de_Morgan_disj
       apply (erule conjE)+
      unfolding terms.map
       apply (rule Ty_Abs)
          apply assumption
         apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ fresh]])
          apply (rule not_in_imsupp_same[symmetric])
          apply assumption
         apply (rule provided)
          apply assumption+

        apply (unfold Abs_inject)[1]
        apply (erule exE conjE)+
        apply hypsubst
        apply (rule exE[OF ex_avoiding_bij])
                apply (rotate_tac -3)
                apply assumption
               apply assumption
              apply (rule cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite])
             apply (rule emp_bound)
            apply (rule id_on_empty)
           apply (rule singl_bound[of "x"])
          apply (rule iffD2[OF disjoint_single])
          apply (rule provided)
             apply assumption+
      apply (rule terms_pre.UNION_bound)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} "FSet.fset"))
      ) 1\<close>)
          apply (rule terms.var_large)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name prod}))
      ) 1\<close>)
      apply (rule terms.var_large)
        apply (erule conjE allE)+
        apply (erule impE)
         prefer 2
         apply (rule iffD2[OF arg_cong2[of _ _ _ _ fresh]])
          apply (rule sym)
           apply assumption
          prefer 2
          apply (drule provided(2)[rotated -1])
            apply (rotate_tac -6)
            apply assumption+
         apply (rule iffD1[OF fun_cong[OF fun_cong [OF fset.rel_eq]]])
         apply (rule iffD2[OF fset.rel_map(2)])
         apply (rule fset.rel_refl_strong)
         apply (rule iffD1[OF fun_cong[OF fun_cong[OF prod.rel_eq]]])
         apply (rule iffD2[OF prod.rel_map(2)])
         apply (rule prod.rel_refl_strong)
          apply (rule not_in_imsupp_same[symmetric])
      apply (drule trans[OF Int_commute])
          apply (unfold disjoint_iff)[1]
          apply (erule allE)
          apply (erule impE)
           apply (rule UN_I)
            apply assumption+
      apply (rule id_apply[symmetric])

         apply (rule conjI)
          apply (rule UnI2)
         apply (rule singletonI)
        apply assumption

       apply (rule iffD2[OF arg_cong3[OF _ refl refl, of _ _ Ty]])
        apply (rule arg_cong3[OF refl _ refl, of _ _ extend])
        apply (rule not_in_imsupp_same[symmetric])
        apply assumption
      unfolding provided(3)[symmetric]
       apply (rule iffD1[OF rename_Ty])
      apply assumption+


       apply (unfold Abs_inject)[1]
       apply (erule exE conjE)+
       apply hypsubst
       apply (unfold terms_vvsubst_rrename[symmetric])[1]
       apply (rule exE[OF ex_avoiding_bij])
               apply (rotate_tac -3)
               apply assumption
              apply assumption
             apply (rule cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite])
            prefer 2
            apply assumption
           apply (rule terms.card_of_FFVars_bounds)
          apply (rule singl_bound[of "x"])
         apply (rule iffD2[OF disjoint_single])
         apply (rule provided)
            apply assumption+
        apply (rule terms_pre.UNION_bound)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} "FSet.fset"))
      ) 1\<close>)
          apply (rule terms.var_large)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name prod}))
      ) 1\<close>)
        apply (rule terms.var_large)
       apply (erule conjE)+
       apply (rotate_tac -2)
      apply (erule allE)
       apply (rule iffD2[OF arg_cong3[OF _ _ refl, of _ _ _ _ Ty]])
         apply (rule arg_cong3[OF refl _ refl, of _ _ extend])
         apply (rule sym)
         apply (erule impE)
          apply (rule conjI)
           apply (rule UnI2)
           apply (rule singletonI)
          apply assumption
         apply assumption
        apply (rule terms.map_cong0)
          apply assumption
         apply (rotate_tac -4)
      apply assumption
        apply (unfold terms.set)[1]
      subgoal for y e' f' g z
        apply (rule case_split[of "z \<in> {x}"])
          apply (drule singletonD)
         apply hypsubst_thin
         apply (erule impE)
          apply (rule conjI)
           apply (rule UnI2)
           apply (rule singletonI)
          apply assumption
         apply (rule sym)
         apply assumption
        apply (drule id_onD)
         apply (rule DiffI)
          apply assumption
         apply assumption
        apply (drule id_onD)
         apply (rule DiffI)
          apply assumption
         apply assumption
        apply (rule trans)
         apply assumption
        apply (rule sym)
        apply assumption
        done
      subgoal for y e' f' g
       apply (rule iffD2[OF arg_cong3[OF _ refl refl, of _ _ Ty]])
      apply (rule trans)
        apply (rule arg_cong3[OF _ refl refl, of _ _ extend])
          prefer 2
          apply (rule provided(3)[symmetric, of "g"])
        apply assumption+
      apply (rule iffD1[OF fun_cong[OF fun_cong [OF fset.rel_eq]]])
         apply (rule iffD2[OF fset.rel_map(2)])
         apply (rule fset.rel_refl_strong)
         apply (rule iffD1[OF fun_cong[OF fun_cong[OF prod.rel_eq]]])
         apply (rule iffD2[OF prod.rel_map(2)])
         apply (rule prod.rel_refl_strong)
          apply (drule trans[OF Int_commute])
          apply (unfold disjoint_iff)[1]
          apply (erule allE)+
          apply (rotate_tac -1)
          apply (erule impE)
           apply (rule UN_I)
            apply assumption
           apply assumption
          apply (rule not_in_imsupp_same[symmetric])
          apply assumption
         apply (rule id_apply[symmetric])
        apply (rule iffD1[OF rename_Ty])
          apply assumption+
        done
      apply (rule allI)
      apply (rule iffD2[OF fun_cong[of "P _ _ _"]])
       apply (rule arg_cong3[OF _ refl refl])
       apply (rule arg_cong3[OF refl _ refl, of _ _ extend])
       apply (rule not_in_imsupp_same[symmetric])
       apply assumption
      unfolding provided(3)[symmetric]
      apply (rule clD[of P, rotated])
        apply assumption+
      apply (unfold Abs_inject)
      apply (erule exE conjE)+
      apply hypsubst_thin
      apply (unfold terms_vvsubst_rrename[symmetric])
      apply (rule exE[OF ex_avoiding_bij])
              apply (rotate_tac -3)
              apply assumption
      apply assumption
            apply (rule cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite])
           prefer 2
           apply assumption
          apply (rule terms.card_of_FFVars_bounds)
         apply (rule singl_bound)
        apply (rule iffD2[OF disjoint_single])
      apply (rule provided)
        apply assumption+
      apply (rule terms_pre.UNION_bound)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} "FSet.fset"))
      ) 1\<close>)
          apply (rule terms.var_large)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name prod}))
      ) 1\<close>)
       apply (rule terms.var_large)
      apply (erule conjE)+
      apply (rotate_tac -2)
      apply (erule allE)
      apply (rule iffD2[OF fun_cong[of "cl _ _ _ _"]])
       apply (rule fun_cong[of "cl _ _ _"])
       apply (rule arg_cong3[OF refl _ _, of _ _ _ _ cl])
        apply (rule arg_cong3[OF _ _ refl, of _ _ _ _ extend])
      defer
        apply (erule impE)
         prefer 2
         apply (rule sym)
         apply assumption
        apply (rule conjI)
         apply (rule UnI2)
         apply (rule singletonI)
        apply assumption
       apply (rule terms.map_cong0)
         apply assumption
        apply (rotate_tac -4)
      apply assumption+
      subgoal for y e' \<rho> f' g z
        apply (rule case_split[of "z \<in> {x}"])
         apply (drule singletonD)
         apply hypsubst_thin
         apply (erule impE)
          apply (rule conjI)
           apply (rule UnI2)
           apply (rule singletonI)
          apply assumption
         apply (rule sym)
         apply assumption
        unfolding terms.set
        apply (drule id_onD, rule DiffI, assumption+)+
        apply (rule trans)
         apply assumption
        apply (rule sym)
        apply assumption
        done
       apply (rule iffD2[OF fun_cong[of "cl _ _ _ _"]])
        apply (rule fun_cong[of "cl _ _ _"])
        apply (rule arg_cong3[OF refl _ refl, of _ _ cl])
        apply (rule provided(3)[symmetric, of _ x])
         apply assumption+
       apply (rule cl_vvsubst)
         apply assumption+
       apply (erule allE)
       apply assumption
  apply (rule iffD1[OF fun_cong[OF fun_cong [OF fset.rel_eq]]])
         apply (rule iffD2[OF fset.rel_map(2)])
         apply (rule fset.rel_refl_strong)
         apply (rule iffD1[OF fun_cong[OF fun_cong[OF prod.rel_eq]]])
         apply (rule iffD2[OF prod.rel_map(2)])
         apply (rule prod.rel_refl_strong)
          apply (drule trans[OF Int_commute])
       apply (unfold disjoint_iff)[1]
       apply (rule not_in_imsupp_same[symmetric])
       apply (erule allE)+
       apply (rotate_tac -1)
       apply (erule impE)
        apply (rule UN_I)
         apply assumption+
      apply (rule id_apply[symmetric])
      done
  done
  done

lemma Ty_fresh_induct:
  fixes A::"'a::var_terms_pre set" and e::"'a terms"
  assumes "|A| <o |UNIV::'a set|" and x: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>"
    and Ty_Var: "\<And>x \<tau> \<Gamma>. (x, \<tau>) |\<in>| \<Gamma> \<Longrightarrow> P \<Gamma> (Var x) \<tau>"
    and Ty_App: "\<And>\<Gamma> e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2. \<Gamma> \<turnstile>\<^sub>t\<^sub>y e1 : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2 \<Longrightarrow> P \<Gamma> e1 (\<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y e2 : \<tau>\<^sub>1 \<Longrightarrow> P \<Gamma> e2 \<tau>\<^sub>1 \<Longrightarrow> P \<Gamma> (App e1 e2) \<tau>\<^sub>2"
    and Ty_Abs: "\<And>x \<Gamma> \<tau> e \<tau>\<^sub>2. x \<notin> A \<union> fst ` fset \<Gamma> \<union> FFVars_terms (Abs x \<tau> e) \<Longrightarrow> x \<sharp> \<Gamma> \<Longrightarrow> \<Gamma>,x:\<tau> \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2 \<Longrightarrow> P (\<Gamma>,x:\<tau>) e \<tau>\<^sub>2 \<Longrightarrow> P \<Gamma> (Abs x \<tau> e) (\<tau> \<rightarrow> \<tau>\<^sub>2)"
  shows "P \<Gamma> e \<tau>"
  apply (rule mp[OF spec[OF Ty_fresh_induct_param[of _ _ _ "\<lambda>\<rho>. case \<rho> of (\<Gamma>, e) \<Rightarrow> A \<union> fst ` fset \<Gamma> \<union> FFVars_terms e" "\<lambda>\<Gamma> e \<tau> \<rho>. \<rho> = (\<Gamma>, e) \<longrightarrow> P \<Gamma> e \<tau>"]]])
  apply (rule assms)+
       apply (rule allI)
  subgoal for x
    apply (rule prod.exhaust[of x])
    apply hypsubst_thin
    unfolding prod.case
    apply (rule terms.Un_bound)
     apply (rule terms.Un_bound)
    apply (rule assms(1))
     apply (rule ordLeq_ordLess_trans[OF card_of_image])
     apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} "FSet.fset"))) 1\<close>)
     apply (rule terms_pre.var_large)
    apply (rule terms.set_bd_UNIV)
    done
     apply (rule impI)
     apply (rule Ty_Var)
     apply assumption
    apply (rule impI)
  apply (erule allE, erule impE, rule refl)+
    apply (rule Ty_App)
       apply assumption+
   apply (rule impI)
   apply (rule Ty_Abs)
  subgoal for x \<Gamma> \<tau> e \<tau>2 y
    apply (rule prod.exhaust[of y])
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
    unfolding prod.case Un_iff de_Morgan_disj
    apply (erule conjE)+
    apply (rule conjI)+
     apply assumption+
    done
     apply assumption+
   apply (erule allE)
   apply (erule impE)
    apply (rule refl)
   apply assumption
  apply (rule refl)
  done

lemmas Ty_induct_strong = Ty_fresh_induct[OF emp_bound, unfolded Un_empty_left]

inductive_cases
  Ty_VarE[elim]: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y Var x : \<tau>"
  and Ty_AppE[elim]: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y App e1 e2 : \<tau>\<^sub>2"
print_theorems

lemma provided_strong:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a" and \<Gamma>::"('a \<times> \<tau>) fset"
  shows "bij f \<Longrightarrow> |supp f| <o |UNIV::'a set| \<Longrightarrow> x \<sharp> \<Gamma> \<longleftrightarrow> f x \<sharp> map_prod f id |`| \<Gamma>"
  apply (rule iffI)
   apply (rule provided)
  apply assumption+
  apply (drule provided[rotated -1])
    apply (rule bij_imp_bij_inv)
  apply assumption
  apply (rule supp_inv_bound)
  apply assumption+
  unfolding inv_simp1 fset.map_comp comp_def prod.map_comp id_def
  unfolding id_def[symmetric] prod.map_id fset.map_id
  apply assumption
  done

(* automate with binder_inductive_cases *)
lemma Ty_AbsE:
  fixes e::"'a::var_terms_pre terms" and A::"'a set"
  assumes "\<Gamma> \<turnstile>\<^sub>t\<^sub>y Abs x \<tau>\<^sub>1 e : \<tau>" "|A| <o |UNIV::'a set|"
    and "\<And>y e' \<tau>' \<tau>\<^sub>2. y \<notin> A \<Longrightarrow> Abs x \<tau>\<^sub>1 e = Abs y \<tau>' e' \<Longrightarrow> \<tau> = (\<tau>' \<rightarrow> \<tau>\<^sub>2) \<Longrightarrow> y \<sharp> \<Gamma> \<Longrightarrow> \<Gamma>,y:\<tau>' \<turnstile>\<^sub>t\<^sub>y e' : \<tau>\<^sub>2 \<Longrightarrow> P"
  shows P
  apply (rule mp[OF Ty_fresh_induct[OF assms(2,1), of "\<lambda>\<Gamma>' e' \<tau>'. \<Gamma>' = \<Gamma> \<and> e' = Abs x \<tau>\<^sub>1 e \<and> \<tau>' = \<tau> \<longrightarrow> P"]])
     apply (rule impI, (erule conjE)+, rotate_tac -2, erule notE[rotated], rule terms.distinct)+
   apply (rule impI)
   apply (erule conjE)+
   apply hypsubst
  unfolding Un_iff de_Morgan_disj
   apply (erule conjE)+
   apply (rule assms(3))
       apply assumption
      apply (rule sym)
      apply assumption+
  apply (rule conjI refl)+
  done
lemma Ty_AbsE':
  assumes "\<Gamma> \<turnstile>\<^sub>t\<^sub>y Abs x \<tau>\<^sub>1 e : \<tau>" "x \<notin> \<Union>(Basic_BNFs.fsts ` fset \<Gamma>)"
and "\<And>\<tau>\<^sub>2. \<tau> = (\<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2) \<Longrightarrow> x \<sharp> \<Gamma> \<Longrightarrow> \<Gamma>,x:\<tau>\<^sub>1 \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2 \<Longrightarrow> P"
shows "P"
  apply (rule Ty_AbsE)
    apply (rule assms(1))
  apply (rule terms_pre.UNION_bound)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} "FSet.fset"))
      ) 1\<close>)
          apply (rule terms.var_large)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name prod}))
      ) 1\<close>)
   apply (rule terms.var_large)

  unfolding Abs_inject
  apply (erule exE conjE)+
  apply hypsubst

  apply (rule exE[OF ex_avoiding_bij])
          apply assumption+
        apply (rule cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite])
       apply (rule terms.set_bd_UNIV)
      apply assumption
     apply (rule singl_bound)
    apply (rule iffD2[OF disjoint_single])
  apply (rule assms(2))
apply (rule terms_pre.UNION_bound)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} "FSet.fset"))
      ) 1\<close>)
          apply (rule terms.var_large)
         apply (rule ordLess_ordLeq_trans)
      apply (raw_tactic \<open>resolve_tac @{context} (
        BNF_Def.set_bd_of_bnf (the (BNF_Def.bnf_of @{context} @{type_name prod}))
      ) 1\<close>)
   apply (rule terms.var_large)
  apply (erule conjE)+

  apply (rule assms(3))
    apply assumption
   apply (drule iffD1[OF arg_cong2[of _ _ _ _ "\<lambda>a b. a \<sharp> b"], rotated -1])
     apply (erule allE)
     apply (erule impE)
      prefer 2
      apply (rule sym)
      apply assumption
     apply (rule conjI)
      apply (rule UnI2)
      apply (rule singletonI)
     apply assumption
    prefer 2
    apply (rule iffD2[OF provided_strong])
      apply (rotate_tac -6)
      apply assumption+
 apply (rule iffD1[OF fun_cong[OF fun_cong [OF fset.rel_eq]]])
         apply (rule iffD2[OF fset.rel_map(2)])
         apply (rule fset.rel_refl_strong)
         apply (rule iffD1[OF fun_cong[OF fun_cong[OF prod.rel_eq]]])
         apply (rule iffD2[OF prod.rel_map(2)])
         apply (rule prod.rel_refl_strong)
  apply (drule trans[OF Int_commute])
       apply (unfold disjoint_iff)[1]
    apply (rule not_in_imsupp_same[symmetric])
    apply (erule allE)+
    apply (rotate_tac -1)
    apply (erule impE)
     apply (rule UN_I)
      apply assumption+
   apply (rule id_apply[symmetric])

  apply (rule iffD2[OF rename_Ty])
    apply (rotate_tac -5)
    apply assumption+
  unfolding provided
  apply (rule iffD2[OF arg_cong3[OF _ _ refl, of _ _ _ _ Ty], rotated -1])
    apply assumption
   apply (rule arg_cong3[OF _ _ refl, of _ _ _ _ extend])
  apply (rule sym)
apply (rule iffD1[OF fun_cong[OF fun_cong [OF fset.rel_eq]]])
         apply (rule iffD2[OF fset.rel_map(2)])
         apply (rule fset.rel_refl_strong)
         apply (rule iffD1[OF fun_cong[OF fun_cong[OF prod.rel_eq]]])
         apply (rule iffD2[OF prod.rel_map(2)])
         apply (rule prod.rel_refl_strong)
  apply (drule trans[OF Int_commute])
       apply (unfold disjoint_iff)[1]
     apply (rule not_in_imsupp_same[symmetric])
     apply (rotate_tac -1)
     apply (erule allE)
     apply (erule impE)
      apply (rule UN_I)
       apply assumption+
    apply (rule id_apply[symmetric])
   apply (erule allE)
   apply (erule impE)
    prefer 2
    apply assumption
   apply (rule conjI)
    apply (rule UnI2)
    apply (rule singletonI)
   apply assumption
  apply (rule trans[rotated])
   apply (rule fun_cong[OF terms_vvsubst_rrename])
    apply assumption+
  apply (rule terms.map_cong0)
    apply assumption+
  subgoal for y e' \<tau>' \<tau>2 f g z
    apply (rule case_split[of "z \<in> {x}"])
     apply (drule singletonD)
     apply hypsubst
     apply (erule allE)
     apply (erule impE)
      prefer 2
      apply assumption
     apply (rule conjI)
      apply (rule UnI2)
      apply (rule singletonI)
     apply assumption
    unfolding terms.set
    apply (drule id_onD, rule DiffI, assumption+)+
    apply (rule trans)
     apply assumption
    apply (rule sym)
    apply assumption
    done
  done

context begin
ML_file \<open>Tools/binder_induction.ML\<close>
end

lemma context_invariance: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y e : \<tau>' \<Longrightarrow> \<forall>x\<in>FFVars_terms e. \<forall>\<tau>. (x, \<tau>) |\<in>| \<Gamma> \<longrightarrow> (x, \<tau>) |\<in>| \<Gamma>' \<Longrightarrow> \<Gamma>' \<turnstile>\<^sub>t\<^sub>y e : \<tau>'"
proof (binder_induction \<Gamma> e \<tau>' arbitrary: \<Gamma>' avoiding: \<Gamma>' rule: Ty_fresh_induct_param)
  case (Ty_Var x \<tau> \<Gamma> \<Gamma>')
  then show ?case by (auto intro: Ty.Ty_Var)
next
  case (Ty_App \<Gamma> e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2 \<Gamma>')
  then show ?case unfolding terms.set by (meson Ty.Ty_App UnI1 UnI2)
next
  case (Ty_Abs x \<Gamma> \<tau> e \<tau>\<^sub>2 \<Gamma>')
  then have "\<forall>y\<in>FFVars_terms e. \<forall>\<tau>'. (y, \<tau>') |\<in>| \<Gamma>,x:\<tau> \<longrightarrow> (y, \<tau>') |\<in>| \<Gamma>',x:\<tau>"
    by (metis DiffI terms.set(3) fimageI finsert_iff fresh_def fst_conv fsts.cases prod_set_simps(1))
  moreover have "x \<sharp> \<Gamma>'" using Ty_Abs unfolding fresh_def
    by (metis UN_I fimageE fmember.rep_eq fsts.intros)
  ultimately show ?case using Ty_Abs by (auto intro: Ty.Ty_Abs)
qed

lemma substitution: "\<lbrakk> \<Gamma>,x:\<tau>' \<turnstile>\<^sub>t\<^sub>y e : \<tau> ; x \<sharp> \<Gamma> ; {||} \<turnstile>\<^sub>t\<^sub>y v : \<tau>' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y tvsubst (VVr(x:=v)) e : \<tau>"
proof (binder_induction e arbitrary: \<Gamma> \<tau> avoiding: \<Gamma> x v rule: terms.strong_induct)
  case (Var a \<Gamma> \<tau>)
  then have 2: "(a, \<tau>) |\<in>| \<Gamma>,x:\<tau>'" by blast
  from \<open>{||} \<turnstile>\<^sub>t\<^sub>y v : \<tau>'\<close> have 3: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y v : \<tau>'" using context_invariance by blast
  then show ?case unfolding terms.subst[OF SSupp_upd_VVr_bound] unfolding fun_upd_def
  proof (cases "a = x")
    case True
    then have "\<tau> = \<tau>'" using 2 Var(1) unfolding fresh_def
      by (metis Var(2) Pair_inject finsertE fresh_def fst_eqD rev_fimage_eqI)
    then show "\<Gamma> \<turnstile>\<^sub>t\<^sub>y (if a = x then v else VVr a) : \<tau>" using True 3 by simp
  next
    case False
    then have "(a, \<tau>) |\<in>| \<Gamma>" using 2 by blast
    then show "\<Gamma> \<turnstile>\<^sub>t\<^sub>y (if a = x then v else VVr a) : \<tau>" unfolding VVr_eq_Var using False Ty.Ty_Var by auto
  qed
next
  case (App e1 e2 \<Gamma> \<tau>)
  from App(3) obtain \<tau>\<^sub>1 where "\<Gamma>,x:\<tau>' \<turnstile>\<^sub>t\<^sub>y e1 : \<tau>\<^sub>1 \<rightarrow> \<tau>" "\<Gamma>,x:\<tau>' \<turnstile>\<^sub>t\<^sub>y e2 : \<tau>\<^sub>1" by blast
  then have "\<Gamma> \<turnstile>\<^sub>t\<^sub>y tvsubst (VVr(x := v)) e1 : \<tau>\<^sub>1 \<rightarrow> \<tau>" "\<Gamma> \<turnstile>\<^sub>t\<^sub>y tvsubst (VVr(x := v)) e2 : \<tau>\<^sub>1" using App by blast+
  then have "\<Gamma> \<turnstile>\<^sub>t\<^sub>y App (tvsubst (VVr(x := v)) e1) (tvsubst (VVr(x := v)) e2) : \<tau>" using Ty_App by blast
  then show ?case unfolding terms.subst(2)[OF SSupp_upd_VVr_bound, symmetric] .
next
  case (Abs y \<tau>\<^sub>1 e \<Gamma> \<tau>)
  then have 1: "y \<notin> IImsupp (VVr(x:=v))" by (simp add: IImsupp_def SSupp_def)
  have "y \<notin> \<Union>(Basic_BNFs.fsts ` fset (\<Gamma>,x:\<tau>'))" using Abs(1) unfolding fresh_def by auto
  then obtain \<tau>\<^sub>2 where 2: "(\<Gamma>,x:\<tau>'),y:\<tau>\<^sub>1 \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2" "\<tau> = (\<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2)" using Abs(3) Ty_AbsE' by metis
  moreover have "(\<Gamma>,x:\<tau>'),y:\<tau>\<^sub>1 = (\<Gamma>,y:\<tau>\<^sub>1),x:\<tau>'" by blast
  moreover have "x \<sharp> \<Gamma>,y:\<tau>\<^sub>1" using Abs(1,4) unfolding fresh_def by auto
  ultimately have "\<Gamma>,y:\<tau>\<^sub>1 \<turnstile>\<^sub>t\<^sub>y tvsubst (VVr(x := v)) e : \<tau>\<^sub>2" using Abs(2,5) by metis
  moreover have "y \<sharp> \<Gamma>" using Abs(1) unfolding fresh_def
    by (metis UN_I UnI1 fimageE fmember.rep_eq fsts.intros)
  ultimately show ?case unfolding terms.subst(3)[OF SSupp_upd_VVr_bound 1] using Ty_Abs 2(2) by blast
qed

theorem progress: "{||} \<turnstile>\<^sub>t\<^sub>y e : \<tau> \<Longrightarrow> (\<exists>x \<tau> e'. e = Abs x \<tau> e') \<or> (\<exists>e'. e \<^bold>\<longrightarrow> e')"
proof (induction "{||} :: ('a::var_terms_pre * \<tau>) fset" e \<tau> rule: Ty.induct)
  case (Ty_App e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2)
  from Ty_App(2) show ?case using ST_Beta ST_App by blast
qed auto

theorem preservation: "\<lbrakk> {||} \<turnstile>\<^sub>t\<^sub>y e : \<tau> ; e \<^bold>\<longrightarrow> e' \<rbrakk> \<Longrightarrow> {||} \<turnstile>\<^sub>t\<^sub>y e' : \<tau>"
proof (induction "{||} :: ('a::var_terms_pre * \<tau>) fset" e \<tau> arbitrary: e' rule: Ty.induct)
  case (Ty_App e1 \<tau>\<^sub>1 \<tau>\<^sub>2 e2)
  from Ty_App(5) show ?case
  proof cases
    case (ST_Beta x \<tau> e e2')
    then have "{||} \<turnstile>\<^sub>t\<^sub>y App (Abs x \<tau> e) e2 : \<tau>\<^sub>2" using Ty_App Ty.Ty_App by fastforce
    have "{||} \<turnstile>\<^sub>t\<^sub>y Abs x \<tau>\<^sub>1 e : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2" using Ty_App ST_Beta
      by (smt (verit, ccfv_SIG) Abs_inject App_inject Ty.cases \<tau>.inject terms.distinct(2, 4))
    then have "{||},x:\<tau>\<^sub>1 \<turnstile>\<^sub>t\<^sub>y e : \<tau>\<^sub>2" by (auto elim: Ty_AbsE')
    then have "{||} \<turnstile>\<^sub>t\<^sub>y tvsubst (VVr(x := e2')) e : \<tau>\<^sub>2" using substitution ST_Beta(1) Ty_App(3) unfolding fresh_def by fastforce
    then show ?thesis using ST_Beta by simp
  next
    case (ST_App e e1' e2')
    then have "{||} \<turnstile>\<^sub>t\<^sub>y e1' : \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2" using Ty_App by simp
    then show ?thesis using Ty_App Ty.Ty_App ST_App by fastforce
  qed
next
  case (Ty_Abs x \<tau> e \<tau>\<^sub>2)
  from \<open>Abs x \<tau> e \<^bold>\<longrightarrow> e'\<close> show ?case by cases auto
qed auto

end