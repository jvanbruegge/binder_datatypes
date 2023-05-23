theory LC_Barendregt_Enhanced_Instance
  imports "thys/MRBNF_Recursor" "HOL-Library.FSet" "FixedCountableVars"
  Curry_LFP "thys/Generic_Barendregt_Enhanced_Rule_Induction"
begin 

(* binder_datatype 'a term =
  Var 'a
| App "'a term" "'a term"
| Abs x::'a t::"'a term" binds x in t
*)

ML \<open>
val ctors = [
  (("Var", (NONE : mixfix option)), [@{typ 'var}]),
  (("App", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("Abs", NONE), [@{typ 'bvar}, @{typ 'brec}])
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
print_mrbnfs

(* Monomorphising: *)
instance var :: var_term_pre apply standard 
  using Field_natLeq infinite_iff_card_of_nat infinite_var
  by (auto simp add: regularCard_var)

type_synonym trm = "var term"

(* *)

(* unary substitution *)
lemma IImsupp_VVr_empty: "IImsupp VVr = {}"
  unfolding IImsupp_def SSupp_VVr_empty UN_empty Un_empty_left
  apply (rule refl)
  done

lemma tvsubst_VVr_func: "tvsubst VVr t = t"
  apply (rule term.TT_plain_co_induct)
  subgoal for x
    apply (rule case_split[of "isVVr (term_ctor x)"])
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
      unfolding tvnoclash_term_def Int_Un_distrib Un_empty
        apply (rule conjI)
         apply (rule iffD2[OF disjoint_iff], rule allI, rule impI, assumption)
        apply (rule iffD2[OF disjoint_iff], rule allI, rule impI)
      unfolding UN_iff Set.bex_simps
        apply (rule ballI)
        apply assumption+
      apply (rule arg_cong[of _ _ term_ctor])
      apply (rule trans)
      apply (rule term_pre.map_cong)
                 apply (rule supp_id_bound bij_id)+
           apply (assumption | rule refl)+
      unfolding id_def[symmetric] term_pre.map_id
      apply (rule refl)
      done
    done

lemma finite_singleton: "finite {x}" by blast
lemma singl_bound: "|{a}| <o |UNIV::'a::var_term_pre set|"
  by (rule finite_ordLess_infinite2[OF finite_singleton cinfinite_imp_infinite[OF term_pre.UNIV_cinfinite]])

lemma SSupp_upd_bound:
  fixes f::"var \<Rightarrow> trm"
  shows "|SSupp (f (a:=t))| <o |UNIV::var set| \<longleftrightarrow> |SSupp f| <o |UNIV::var set|"
  unfolding SSupp_def
  apply (auto simp only: fun_upd_apply singl_bound ordLeq_refl split: if_splits
      elim!: ordLeq_ordLess_trans[OF card_of_mono1 ordLess_ordLeq_trans[OF term_pre.Un_bound], rotated]
      intro: card_of_mono1)
  done

corollary SSupp_upd_VVr_bound: "|SSupp (VVr(a:=(t::trm)))| <o |UNIV::var set|"
  apply (rule iffD2[OF SSupp_upd_bound])
  apply (rule SSupp_VVr_bound)
  done

lemma fvars_subset_id_on: "supp f \<subseteq> A \<Longrightarrow> id_on (B - A) f"
  unfolding supp_def id_on_def by blast

proposition rrename_simps[simp]:
  assumes "bij (f::var \<Rightarrow> var)" "|supp f| <o |UNIV::var set|"
  shows "rrename_term f (Var a) = Var (f a)"
    "rrename_term f (App e1 e2) = App (rrename_term f e1) (rrename_term f e2)"
    "rrename_term f (Abs x e) = Abs (f x) (rrename_term f e)"
  unfolding Var_def App_def Abs_def term.rrename_cctors[OF assms] map_term_pre_def comp_def
    Abs_term_pre_inverse[OF UNIV_I] map_sum_def sum.case map_prod_def prod.case id_def
    apply (rule refl)+
  done

proposition App_inject[simp]: "(App a b = App c d) = (a = c \<and> b = d)"
proof
  assume "App a b = App c d"
  then show "a = c \<and> b = d"
    unfolding App_def fun_eq_iff term.TT_injects0
      map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I] map_sum_def sum.case prod.map_id
      Abs_term_pre_inject[OF UNIV_I UNIV_I]
    by blast
qed simp

proposition Var_inject[simp]: "(Var a = Var b) = (a = b)"
  apply (rule iffI[rotated])
   apply (rule arg_cong[of _ _ Var])
  apply assumption
  unfolding Var_def term.TT_injects0 map_term_pre_def comp_def map_sum_def sum.case Abs_term_pre_inverse[OF UNIV_I]
  id_def Abs_term_pre_inject[OF UNIV_I UNIV_I] sum.inject
  apply (erule exE conjE)+
  apply assumption
  done

lemma Abs_inject: "(Abs x e = Abs x' e') = (\<exists>f. bij f \<and> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set|
  \<and> id_on (FFVars_term (Abs x e)) f \<and> f x = x' \<and> rrename_term f e = e')"
  unfolding term.set
  unfolding Abs_def term.TT_injects0 map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I]
    map_sum_def sum.case map_prod_def prod.case id_def Abs_term_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    set3_term_pre_def sum_set_simps Union_empty Un_empty_left prod_set_simps cSup_singleton set2_term_pre_def
    Un_empty_right UN_single
  apply (rule refl)
  done

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

lemma map_term_pre_inv_simp: "bij f \<Longrightarrow> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set| \<Longrightarrow> inv (map_term_pre (id::_::var_term_pre \<Rightarrow> _) f (rrename_term f) id) = map_term_pre id (inv f) (rrename_term (inv f)) id"
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

lemma Abs_set3: "term_ctor v = Abs (x::var) e \<Longrightarrow> \<exists>x' e'. term_ctor v = Abs x' e' \<and> x' \<in> set2_term_pre v \<and> e' \<in> set3_term_pre v"
  unfolding Abs_def term.TT_injects0
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

lemma Abs_avoid: "|A::var set| <o |UNIV::var set| \<Longrightarrow> \<exists>x' e'. Abs x e = Abs x' e' \<and> x' \<notin> A"
  apply (drule term.TT_fresh_nchotomys[of _ "Abs x e"])
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


(* *)

lemmas rrename_simps[simp] 
find_theorems tvsubst 

find_theorems "_::_::var_term_pre" "regularCard"

lemma rrename_term_tvsubst: "bij (\<sigma>::var\<Rightarrow>var) \<Longrightarrow> |supp \<sigma>| <o |UNIV:: var set| \<Longrightarrow>  
     |SSupp \<tau>| <o |UNIV:: var set| \<Longrightarrow>
     rrename_term \<sigma> (tvsubst \<tau> e) = tvsubst (rrename_term \<sigma> \<circ> \<tau>) (rrename_term \<sigma> e)"
sorry

lemma tvsubst_o: "|SSupp \<sigma>| <o |UNIV:: var set| \<Longrightarrow>  
     |SSupp \<tau>| <o |UNIV:: var set| \<Longrightarrow>
     tvsubst \<sigma> (tvsubst \<tau> e) = tvsubst (tvsubst \<sigma> \<circ> \<tau>) e"
sorry

lemma [simp]: "bij (\<sigma>::var\<Rightarrow>var) \<Longrightarrow> |supp \<sigma>| <o |UNIV:: var set| \<Longrightarrow>  
      rrename_term \<sigma> o (VVr(a := e)) = VVr (\<sigma> a := rrename_term \<sigma> e)"
sorry

lemmas SSupp_upd_VVr_bound[simp,intro]
lemmas supp_inv_bound[simp]
lemmas term.rrename_ids[simp]
lemmas bij_swap[simp]

lemma supp_swap_bound[intro]: "|supp (id(x::var := xx, xx := x))| <o |UNIV:: var set|"
by (simp add: cinfinite_imp_infinite supp_swap_bound term.UNIV_cinfinite)

lemmas supp_id_bound[simp]

lemma rrename_term_cong_id[simp]: 
"bij (\<sigma>::var\<Rightarrow>var) \<Longrightarrow> |supp \<sigma>| <o |UNIV:: var set| \<Longrightarrow>   
 \<forall>a\<in>FFVars_term e. \<sigma> a = (a::var) \<Longrightarrow> rrename_term \<sigma> e = e"
sorry

lemma Abs_rrename_term: 
"bij (\<sigma>::var\<Rightarrow>var) \<Longrightarrow> |supp \<sigma>| <o |UNIV:: var set| \<Longrightarrow>   
 \<forall>a'\<in>FFVars_term e - {a::var}. \<sigma> a' = a' \<Longrightarrow> Abs a e = Abs (\<sigma> a) (rrename_term \<sigma> e)"
sorry

lemma tvsubst_VVr_rrename_term: 
"xx \<notin> FFVars_term e1 - {x} \<Longrightarrow> 
 tvsubst (VVr((x::var) := e2)) e1 = tvsubst (VVr(xx := e2)) (rrename_term (id(x := xx, xx := x)) e1)"
sorry


(* INSTANTIATING THE ABSTRACT SETTING: *)

(* INSTATIATING THE Small LOCALE (INDEPENDENTLY OF THE CONSIDERED INDUCTIVE PREDICATE *) 

print_locales
interpretation Small where dummy = "undefined :: var" 
apply standard
  apply (simp add: infinite_var)  
  using term_prevar_term_prevar_sumterm_prevar_prodIDterm_prevar_prodID_class.regular by blast
 

(* AN EXAMPLE INDUCTIVE DEFINITION *)
(* (a reduced form of) small step semantics *) 

inductive step :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta: "step (App (Abs x e1) e2) (tvsubst (VVr(x:=e2)) e1)"
| AppL: "step e1 e1' \<Longrightarrow> step (App e1 e2) (App e1' e2)"
| Xi: "step e e' \<Longrightarrow> step (Abs x e) (Abs x e')"
|PBeta: "step e1 e1' \<Longrightarrow> step e2 e2' \<Longrightarrow> step (App (Abs x e1) e2) (tvsubst (VVr(x:=e2')) e1')"

lemmas step_def = nitpick_unfold(173)

(* INSTANTIATING THE Components LOCALE: *)

type_synonym T = "trm \<times> trm"
type_synonym V = "var list" (* in this case, could have also taken to be 'a option; 
and the most uniform approach would have been 'a + unit + 'a + 'a *)


definition Tmap :: "(var \<Rightarrow> var) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> map_prod (rrename_term f) (rrename_term f)"

fun Tfvars :: "T \<Rightarrow> var set" where 
"Tfvars (e1,e2) = FFVars_term e1 \<union> FFVars_term e2"

definition Vmap :: "(var \<Rightarrow> var) \<Rightarrow> V \<Rightarrow> V" where 
"Vmap \<equiv> map"

fun Vfvars :: "V \<Rightarrow> var set" where 
"Vfvars v = set v"

interpretation Components where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars
and Vmap = Vmap and Vfvars = Vfvars 
apply standard unfolding ssbij_def Tmap_def Vmap_def
  using small_Un small_def term.card_of_FFVars_bounds
  apply (auto simp: term.FFVars_rrenames term.rrename_id0s map_prod.comp term.rrename_comp0s inf_A)  
  by auto 

  
definition G :: "(T \<Rightarrow> bool) \<Rightarrow> V \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>R v t.  
         (\<exists>x e1 e2. v = [x] \<and> fst t = App (Abs x e1) e2 \<and> snd t = tvsubst (VVr(x := e2)) e1)
         \<or>
         (\<exists>e1 e1' e2. v = [] \<and> fst t = App e1 e2 \<and> snd t = App e1' e2 \<and> R (e1,e1')) 
         \<or>
         (\<exists>x e e'. v = [x] \<and> fst t = Abs x e \<and> snd t = Abs x e' \<and> R (e,e'))
         \<or>
         (\<exists>x e1 e1' e2 e2'. v = [x] \<and> fst t = App (Abs x e1) e2 \<and> snd t = tvsubst (VVr(x := e2')) e1' \<and> 
            R (e1,e1') \<and> R (e2,e2'))"


(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma GG_mono: "\<And>R R' k v t. R \<le> R' \<Longrightarrow> G R v t \<Longrightarrow> G R' v t"
unfolding G_def by fastforce

lemma GG_equiv: "\<And>\<sigma> R v t. ssbij \<sigma> \<Longrightarrow> G R v t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Vmap \<sigma> v) (Tmap \<sigma> t)"
unfolding G_def subgoal for \<sigma> R v t apply(elim disjE)
  subgoal apply(rule disjI1)
  subgoal apply(elim exE) subgoal for x e1 e2 
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename_term \<sigma> e1"]) apply(rule exI[of _ "rrename_term \<sigma> e2"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def apply simp
  apply(subst rrename_term_tvsubst) by auto . .
  (* *)
  subgoal apply(rule disjI2, rule disjI1)
  subgoal apply(elim exE) subgoal for e1 e1' e2
  apply(rule exI[of _ "rrename_term \<sigma> e1"]) apply(rule exI[of _ "rrename_term \<sigma> e1'"]) 
  apply(rule exI[of _ "rrename_term \<sigma> e2"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  by (simp add: term.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI2, rule disjI2, rule disjI1)
  subgoal apply(elim exE) subgoal for x e e'
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename_term \<sigma> e"]) apply(rule exI[of _ "rrename_term \<sigma> e'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  by (simp add: term.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI2, rule disjI2, rule disjI2)
  subgoal apply(elim exE) subgoal for x e1 e1' e2 e2'
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename_term \<sigma> e1"]) apply(rule exI[of _ "rrename_term \<sigma> e1'"]) 
  apply(rule exI[of _ "rrename_term \<sigma> e2"]) apply(rule exI[of _ "rrename_term \<sigma> e2'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  apply (simp add: term.rrename_comps) apply(subst rrename_term_tvsubst) by auto . . . .
  

lemma fresh: "\<exists>xx. xx \<notin> Tfvars t"  
by (metis Abs_avoid Tfvars.elims term.card_of_FFVars_bounds term.set(2))

lemma GG_fresh: 
"\<And>R v t. (\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> G R v t \<Longrightarrow> 
         \<exists>w. Vfvars w  \<inter> Tfvars t = {} \<and> G R w t"
subgoal for R v t
using fresh[of t] unfolding G_def Tmap_def Vmap_def apply safe
  subgoal for xx x e1 e2
  apply(rule exI[of _ "[xx]"])  
  apply(rule conjI)
    subgoal unfolding ssbij_def small_def Vmap_def by auto 
    subgoal apply(rule disjI1) 
    apply(rule exI[of _ "xx"]) 
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e1"])
    apply(rule exI[of _ "e2"])
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst Abs_rrename_term[of "id(x:=xx,xx:=x)"]) by auto
      subgoal apply(subst tvsubst_VVr_rrename_term) by auto . .
  (* *)
  subgoal for xx e1 e1' e2
  apply(rule exI[of _ "[]"])  
  apply(rule conjI)
    subgoal unfolding ssbij_def small_def Vmap_def by auto 
    subgoal apply(rule disjI2, rule disjI1) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e1'"])
    apply(rule exI[of _ "e2"]) 
    apply(cases t)  apply simp . .
  (* *)
  subgoal for xx x e e'
  apply(rule exI[of _ "[xx]"])  
  apply(rule conjI)
    subgoal unfolding ssbij_def small_def Vmap_def by auto 
    subgoal apply(rule disjI2, rule disjI2, rule disjI1) 
    apply(rule exI[of _ "xx"]) 
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e"])
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e'"])
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst Abs_rrename_term[of "id(x:=xx,xx:=x)"]) by auto
      subgoal apply(subst Abs_rrename_term[of "id(x:=xx,xx:=x)"]) by auto
      subgoal by (metis supp_swap_bound Prelim.bij_swap small_def ssbij_def) . . 
  (* *)
  subgoal for xx x e1 e1' e2 e2'
  apply(rule exI[of _ "[xx]"])  
  apply(rule conjI)
    subgoal unfolding ssbij_def small_def Vmap_def by auto 
    subgoal apply(rule disjI2, rule disjI2, rule disjI2)
    apply(rule exI[of _ "xx"]) 
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e1"])
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e1'"])
    apply(rule exI[of _ "e2"])
    apply(rule exI[of _ "e2'"])
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst Abs_rrename_term[of "id(x:=xx,xx:=x)"]) by auto
      subgoal apply(subst tvsubst_VVr_rrename_term) apply auto apply(subst (asm) FFVars_tvsubst)
      apply (auto split: if_splits)  by (metis FVars_VVr singletonI) 
      subgoal by (metis supp_swap_bound Prelim.bij_swap small_def ssbij_def) . . . .
  (* *)


(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation Induct where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars
and Vmap = Vmap and Vfvars = Vfvars and G = G
apply standard 
  using GG_mono GG_equiv GG_fresh by auto

(* *)
lemmas I_def = nitpick_unfold(178) 

lemma step_I: "step t1 t2 = I (t1,t2)" 
  unfolding step_def I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
  unfolding fun_eq_iff G_def apply safe
    subgoal apply simp by metis
    subgoal by auto
    subgoal by auto
    subgoal apply simp by metis
    subgoal by auto
    subgoal by auto
    subgoal apply simp by metis
    subgoal by auto .

(* FROM ABSTRACT BACK TO CONCRETE: *)
thm step.induct[no_vars]

corollary BE_induct_step: "(\<And>p. small (Pfvars p)) \<Longrightarrow> 
step t1 t2 \<Longrightarrow> 
(\<And>x e e2 p. x \<notin> Pfvars p \<Longrightarrow> x \<notin> FFVars_term e2 \<Longrightarrow> R p (App (Abs x e) e2) (tvsubst (VVr(x := e2)) e)) \<Longrightarrow>
(\<And>e1 e1' e2 p. step e1 e1' \<Longrightarrow> (\<forall>p'. R p' e1 e1') \<Longrightarrow> R p (App e1 e2) (App e1' e2)) \<Longrightarrow> 
(\<And>e e' x p. x \<notin> Pfvars p \<Longrightarrow> step e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> R p (Abs x e) (Abs x e')) \<Longrightarrow> 
(\<And>x e e' e2 e2' p. x \<notin> Pfvars p \<Longrightarrow> step e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> step e2 e2' \<Longrightarrow> (\<forall>p'. R p' e2 e2') \<Longrightarrow> 
   x \<notin> FFVars_term e2 \<Longrightarrow> (x \<in> FFVars_term e' \<Longrightarrow> x \<notin> FFVars_term e2') \<Longrightarrow> 
   R p (App (Abs x e) e2) (tvsubst (VVr(x := e2')) e')) \<Longrightarrow>
 R p t1 t2"
unfolding step_I
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by auto
  subgoal apply(erule BE_induct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
  unfolding G_def apply auto apply(subst (asm) FFVars_tvsubst) by (auto split: if_splits) . 


end