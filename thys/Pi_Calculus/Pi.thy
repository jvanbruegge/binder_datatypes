(* the syntax of pi-calculus *)

theory Pi
imports "../MRBNF_Recursor" "HOL-Library.FSet" 
 "../Instantiation_Infrastructure/FixedCountableVars"
 "../General_Customization"
begin 


(* DATATYPE DECLARTION  *)

(* binder_datatype 'a term =
  Zero
| Sum "'a term" "'a term"
| Par "'a term" "'a term"
| Bang "'a term" 
| Match 'a 'a "'a term" 
| Match 'a 'a "'a term" 
| Inp x::'a 'a t::"'a term" binds x in t
| Res x::'a t::"'a term" binds x in t
*)

ML \<open>
val ctors = [
  (("Zero", (NONE : mixfix option)), []),
  (("Sum", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("Par", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("Bang", NONE), [@{typ 'rec}]),
  (("Match", NONE), [@{typ 'var}, @{typ 'var}, @{typ 'rec}]),
  (("Out", NONE), [@{typ 'var}, @{typ 'var}, @{typ 'rec}]),
  (("Inp", NONE), [@{typ 'var}, @{typ 'bvar}, @{typ 'brec}]),
  (("Res", NONE), [@{typ 'bvar}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "term"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
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


(****************************)
(* DATATYPE-SPECIFIC CUSTOMIZATION  *)


(* Monomorphising: *)
instance var :: var_term_pre apply standard 
  using Field_natLeq infinite_iff_card_of_nat infinite_var
  by (auto simp add: regularCard_var)

type_synonym trm = "var term"

lemma singl_bound: "|{a}| <o |UNIV::var set|"
  by (rule finite_ordLess_infinite2[OF finite_singleton cinfinite_imp_infinite[OF term_pre.UNIV_cinfinite]])


(* Some lighter notations: *)

abbreviation "rrename \<equiv> rrename_term"
abbreviation "FFVars \<equiv> FFVars_term"

(* *)

(* Enabling some simplification rules: *)

lemmas term.rrename_ids[simp] term.rrename_cong_ids[simp]
term.FFVars_rrenames[simp]

lemmas term_vvsubst_rrename[simp]



(* *)
(* Properties of renaming (variable-for-variable substitution) *)

proposition rrename_simps[simp]:
  assumes "bij (f::var \<Rightarrow> var)" "|supp f| <o |UNIV::var set|"
  shows "rrename_term f Zero = Zero"
    "rrename_term f (Sum e1 e2) = Sum (rrename_term f e1) (rrename_term f e2)"
    "rrename_term f (Par e1 e2) = Par (rrename_term f e1) (rrename_term f e2)"
    "rrename_term f (Bang e) = Bang (rrename_term f e)"
    "rrename_term f (Match x y e) = Match (f x) (f y) (rrename_term f e)"
    "rrename_term f (Out x y e) = Out (f x) (f y) (rrename_term f e)"
    "rrename_term f (Inp x y e) = Inp (f x) (f y) (rrename_term f e)"
    "rrename_term f (Res x e) = Res (f x) (rrename_term f e)"
  unfolding Zero_def Sum_def Par_def Bang_def Match_def Out_def Inp_def Res_def term.rrename_cctors[OF assms] map_term_pre_def comp_def
    Abs_term_pre_inverse[OF UNIV_I] map_sum_def sum.case map_prod_def prod.case id_def
    apply (rule refl)+
  done

lemma rrename_cong: 
"bij f \<Longrightarrow> |supp f| <o |UNIV::var set| \<Longrightarrow> (\<And>z. z \<in> FFVars w \<Longrightarrow> f z = g z) \<Longrightarrow> rrename f w = rrename g w"
sorry

(* Properties of the constructors *)

proposition Sum_inject[simp]: "(Sum a b = Sum c d) = (a = c \<and> b = d)"
unfolding Sum_def fun_eq_iff term.TT_injects0
map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] map_sum_def sum.case prod.map_id
Abs_term_pre_inject[OF UNIV_I UNIV_I]
by auto 

proposition Par_inject[simp]: "(Par a b = Par c d) = (a = c \<and> b = d)"
unfolding Par_def fun_eq_iff term.TT_injects0
map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] map_sum_def sum.case prod.map_id
Abs_term_pre_inject[OF UNIV_I UNIV_I] by auto

proposition Bang_inject[simp]: "(Bang a = Bang b) = (a = b)"
unfolding Bang_def fun_eq_iff term.TT_injects0
map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] map_sum_def sum.case prod.map_id
Abs_term_pre_inject[OF UNIV_I UNIV_I] by auto

proposition Match_inject[simp]: "(Match x1 y1 a1 = Match x2 y2 a2) = (x1 = x2 \<and> y1 = y2 \<and> a1 = a2)"
unfolding Match_def fun_eq_iff term.TT_injects0
map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] map_sum_def sum.case prod.map_id
Abs_term_pre_inject[OF UNIV_I UNIV_I] by auto

proposition Out_inject[simp]: "(Out x1 y1 a1 = Out x2 y2 a2) = (x1 = x2 \<and> y1 = y2 \<and> a1 = a2)"
unfolding Out_def fun_eq_iff term.TT_injects0
map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] map_sum_def sum.case prod.map_id
Abs_term_pre_inject[OF UNIV_I UNIV_I] by auto

lemma Inp_inject: "(Inp x y e = Inp x' y' e') \<longleftrightarrow> 
  x = x' \<and> 
  (\<exists>f. bij f \<and> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set|
  \<and> id_on (FFVars_term e - {y}) f \<and> f y = y' \<and> rrename_term f e = e')"
  unfolding term.set  
  unfolding Inp_def term.TT_injects0 map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_term_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_term_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_term_pre_def
    Un_empty_right UN_single by auto

lemma bij_map_term_pre: "bij f \<Longrightarrow> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set| \<Longrightarrow> bij (map_term_pre (id::var \<Rightarrow>var) f (rrename_term f) id)"
  apply (rule iffD2[OF bij_iff])
    apply (rule exI[of _ "map_term_pre id (inv f) (rrename_term (inv f)) id"])
  apply (frule bij_imp_bij_inv)
  apply (frule supp_inv_bound)
   apply assumption
  apply (rule conjI)
   apply (rule trans)
    apply (rule term_pre.map_comp0[symmetric])
         apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp1 term.rrename_comp0s term.rrename_id0s
  apply (rule term_pre.map_id0)
  apply (rule trans)
   apply (rule term_pre.map_comp0[symmetric])
        apply (assumption | rule supp_id_bound)+
  unfolding id_o inv_o_simp2 term.rrename_comp0s term.rrename_id0s
  apply (rule term_pre.map_id0)
  done

lemma map_term_pre_inv_simp: "bij f \<Longrightarrow> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set| \<Longrightarrow> 
inv (map_term_pre (id::_::var_term_pre \<Rightarrow> _) f (rrename_term f) id) = map_term_pre id (inv f) (rrename_term (inv f)) id"
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
  unfolding id_o inv_o_simp1 inv_o_simp2 term.rrename_comp0s term.rrename_id0s term_pre.map_id0
   apply (rule refl)+
  done

lemma Abs_set3: "term_ctor v = Inp y (x::var) e \<Longrightarrow> \<exists>x' e'. term_ctor v = Inp y x' e' \<and> x' \<in> set2_term_pre v \<and> e' \<in> set3_term_pre v"
  unfolding Inp_def term.TT_injects0
  apply (erule exE)
  apply (erule conjE)+
  subgoal for f
apply (drule iffD2[OF bij_imp_inv', rotated, of "map_term_pre id f (rrename_term f) id"])
     apply (rule bij_map_term_pre)
      apply assumption+
    apply (rule exI)
    apply (rule exI)
    apply (rule conjI)
     apply (rule exI[of _ "id"])
     apply (rule conjI bij_id supp_id_bound id_on_id)+
    apply (drule sym)
    unfolding term.rrename_id0s term_pre.map_id map_term_pre_inv_simp
    unfolding map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] map_sum_def sum.case
      map_prod_def prod.case id_def
    apply assumption
    apply (raw_tactic \<open>hyp_subst_tac @{context} 1\<close>)
unfolding set2_term_pre_def set3_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] sum_set_simps
    map_sum_def sum.case Union_empty Un_empty_left map_prod_def prod.case prod_set_simps
      ccpo_Sup_singleton Un_empty_right id_on_def image_single[symmetric]
  unfolding term.FFVars_rrenames[OF bij_imp_bij_inv supp_inv_bound]
  unfolding image_single image_set_diff[OF bij_is_inj[OF bij_imp_bij_inv], symmetric]
    image_in_bij_eq[OF bij_imp_bij_inv] inv_inv_eq image_in_bij_eq[OF term.rrename_bijs[OF bij_imp_bij_inv supp_inv_bound]]
  term.rrename_inv_simps[OF bij_imp_bij_inv supp_inv_bound] inv_simp2
  unfolding term.rrename_comps[OF bij_imp_bij_inv supp_inv_bound] inv_o_simp2 term.rrename_ids
  apply (rule conjI bij_imp_bij_inv supp_inv_bound singletonI | assumption)+
  done
  done

lemma Abs_avoid: "|A::var set| <o |UNIV::var set| \<Longrightarrow> \<exists>x' e'. Inp y x e = Inp y x' e' \<and> x' \<notin> A"
  apply (drule term.TT_fresh_nchotomys[of _ "Inp y x e"])
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

lemma Abs_rrename: 
"bij (\<sigma>::var\<Rightarrow>var) \<Longrightarrow> |supp \<sigma>| <o |UNIV:: var set| \<Longrightarrow>   
 (\<And>a'. a' \<in> FFVars_term e - {a::var} \<Longrightarrow> \<sigma> a' = a') \<Longrightarrow> Inp b a e = Inp b (\<sigma> a) (rrename_term \<sigma> e)"
  using Inp_inject id_on_def by blast

(* Bound properties (needed as auxiliaries): *)

lemma supp_swap_bound[simp,intro!]: "|supp (id(x::var := xx, xx := x))| <o |UNIV:: var set|"
by (simp add: cinfinite_imp_infinite supp_swap_bound term.UNIV_cinfinite)



(* Compositionality properties of renaming and term-for-variable substitution *)

(*
lemma tvsubst_comp: 
assumes s[simp]: "|SSupp \<sigma>| <o |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"
shows "tvsubst (\<sigma>::var\<Rightarrow>trm) (tvsubst \<tau> e) = tvsubst (tvsubst \<sigma> \<circ> \<tau>) e"
proof-
  note SSupp_tvsubst_bound'[OF s, simp]
  show ?thesis
  apply(induct e rule: term.fresh_induct[where A = "IImsupp \<sigma> \<union> IImsupp \<tau>"])
    subgoal using Un_bound[OF s]  
      using var_ID_class.Un_bound SSupp_IImsupp_bound s(1) s(2) by blast
    subgoal by simp
    subgoal by simp
    subgoal for x t apply(subgoal_tac "x \<notin> IImsupp (\<lambda>a. tvsubst \<sigma> (\<tau> a))") 
      subgoal by simp
      subgoal using IImsupp_tvsubst_su'[OF s(1)] by blast . . 
qed

lemma rrename_tvsubst_comp: 
assumes b[simp]: "bij (\<sigma>::var\<Rightarrow>var)" and s[simp]: "|supp \<sigma>| <o |UNIV:: var set|" "|SSupp \<tau>| <o |UNIV:: var set|"
shows "rrename_term \<sigma> (tvsubst \<tau> e) = tvsubst (rrename_term \<sigma> \<circ> \<tau>) e"
proof-
  note SSupp_rrename_bound'[OF b s, simp]
  show ?thesis
  apply(induct e rule: term.fresh_induct[where A = "IImsupp \<tau> \<union> imsupp \<sigma>"])
    subgoal using s(1) s(2) Un_bound SSupp_IImsupp_bound imsupp_supp_bound infinite_var by blast
    subgoal by simp 
    subgoal by simp
    subgoal for x t apply simp apply(subgoal_tac "x \<notin> IImsupp (\<lambda>a. rrename_term  \<sigma> (\<tau> a))") 
      subgoal unfolding imsupp_def supp_def by simp
      subgoal using IImsupp_rrename_su' b s(1) by blast . .
qed

(* Equivariance of unary substitution: *)

lemma tvsubst_rrename_comp[simp]: 
assumes s[simp]: "bij (\<sigma>::var\<Rightarrow>var)" "|supp \<sigma>| <o |UNIV::var set|"
shows "tvsubst (rrename_term \<sigma> \<circ> Var(x := e2)) e1 = tvsubst (Var(\<sigma> x := rrename_term \<sigma> e2)) (rrename_term \<sigma> e1)"
proof-
  note SSupp_rrename_update_bound[OF assms, unfolded comp_def, simplified, simp]
  note SSupp_update_rrename_bound[unfolded fun_upd_def, simplified, simp] 
  show ?thesis
  apply(induct e1 rule: term.fresh_induct[where A = "{x} \<union> FFVars_term e2 \<union> imsupp \<sigma>"])
    subgoal by (meson Un_bound imsupp_supp_bound infinite_var s(2) singl_bound term.set_bd_UNIV) 
    subgoal by auto 
    subgoal by simp
    subgoal for y t apply simp apply(subgoal_tac 
      "y \<notin> IImsupp ((\<lambda>a. rrename_term \<sigma> (if a = x then e2 else Var a))) \<and> 
      \<sigma> y \<notin> IImsupp (\<lambda>a. if a = \<sigma> x then rrename_term \<sigma> e2 else Var a)") 
      subgoal unfolding imsupp_def supp_def by simp
      subgoal unfolding IImsupp_def imsupp_def SSupp_def supp_def by auto . .
qed

(* Unary substitution versus swapping: *)
lemma tvsubst_Var_rrename_term: 
assumes xx: "xx \<notin> FFVars_term e1 - {x}"
shows "tvsubst (Var((x::var) := e2)) e1 = tvsubst (Var(xx := e2)) (rrename_term (id(x := xx, xx := x)) e1)"
proof-
  show ?thesis using xx
  apply(induct e1 rule: term.fresh_induct[where A = "{x,xx} \<union> FFVars_term e2"])
    subgoal by (metis insert_is_Un term.set(1) term.set(2) term.set_bd_UNIV)
    subgoal by simp
    subgoal by auto
    subgoal for y t apply simp apply(subgoal_tac 
      "y \<notin> IImsupp (Var(x := e2)) \<and> y \<notin> IImsupp (Var(xx := e2))") 
      subgoal unfolding imsupp_def supp_def by auto
      subgoal unfolding IImsupp_def imsupp_def SSupp_def supp_def by auto . .
qed
*)

(* Swapping and unary substitution, as abbreviations: *)
abbreviation "swap P x y \<equiv> rrename (id(x:=y,y:=x)) P"
abbreviation "usub P y x \<equiv> vvsubst (id(x:=y)) P"







end