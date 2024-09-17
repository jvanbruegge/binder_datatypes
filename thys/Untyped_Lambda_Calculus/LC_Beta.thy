(* Here we instantiate the general enhanced rule induction to beta reduction
for the (untyped) lambda-calculus *)
theory LC_Beta 
imports LC "Binders.Generic_Barendregt_Enhanced_Rule_Induction" "Prelim.Curry_LFP" "Prelim.More_Stream" LC_Head_Reduction
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

abbreviation Tsupp where "Tsupp a b \<equiv> FFVars a \<union> FFVars b"
lemma fresh: "\<exists>xx. xx \<notin> Tsupp (t1::trm) t2"
  unfolding prod.collapse
  by (metis (no_types, lifting) exists_var finite_iff_le_card_var term.Un_bound term.set_bd_UNIV)

inductive step :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta: "step (App (Lam x e1) e2) (tvsubst (Var(x:=e2)) e1)"
| AppL: "step e1 e1' \<Longrightarrow> step (App e1 e2) (App e1' e2)"
| AppR: "step e2 e2' \<Longrightarrow> step (App e1 e2) (App e1 e2')"
| Xi: "step e e' \<Longrightarrow> step (Lam x e) (Lam x e')"

binder_inductive step
for perms: rrename rrename and supps: FFVars FFVars
   \<comment> \<open>properties of LS-Nominal sets\<close>
  apply (auto simp: o_def split_beta term.rrename_comps fun_eq_iff isPerm_def
    small_def term.card_of_FFVars_bounds term.Un_bound infinite_UNIV) [12]
  subgoal for \<sigma> R B t  \<comment> \<open>equivariance\<close>
    by (elim disj_forward case_prodE)
      (auto simp: isPerm_def term.rrename_comps rrename_tvsubst_comp
         | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
         | ((rule exI[of _ "\<sigma> _"])+; auto))+
  subgoal premises prems for R B t1 t2  \<comment> \<open>refreshability\<close>
    apply (tactic \<open>refreshability_tac @{term B} @{term "Tsupp t1 t2"}
      @{thm prems(3)} @{thms emp_bound singl_bound term.Un_bound term.card_of_FFVars_bounds infinite}
      [SOME [@{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"},
             @{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "(\<lambda>f e. e) :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"}],
       NONE,
       NONE,
       SOME [@{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"}]]
      @{thms Lam_inject}
      @{thms prems(2) Lam_eq_tvsubst term.rrename_cong_ids[symmetric]}
      @{context}\<close>)
    done
(*
    apply (rule exE[OF eextend_fresh[of B "Tsupp t1 t2" "Tsupp t1 t2 - B"]])
    subgoal apply (rule cut_rl[OF _ prems(3)]) by (auto simp add: emp_bound singl_bound)
    subgoal by (simp add: term.Un_bound term.card_of_FFVars_bounds)
    subgoal by (simp add: infinite)
    subgoal by simp
    subgoal by simp
    apply (erule conjE)+
    apply (rule exI, rule conjI, assumption)
    apply (insert prems(3))
    apply (elim disj_forward exE)
    subgoal premises prems2 for xb xaa e1a e2a
      apply (rule exI[of _ "xb xaa"])
      apply (rule exI[of _ "rrename xb e1a"])
      apply (rule exI[of _ "e2a"])
      apply (auto simp: Lam_inject prems2
          intro!: id_on_antimono[OF prems2(4)] prems(2) exI[of _ xb] Lam_eq_tvsubst term.rrename_cong_ids[symmetric])
      using prems(4)
      apply (auto intro!: id_on_antimono[OF prems(4)] simp: prems)
apply (auto simp: )
      done
    subgoal for f e1 e1' e2
      apply (rule exI[of _ "e1"])
      apply (rule exI[of _ "e1'"])
      apply (rule exI[of _ "e2"])
      apply auto
      done
    subgoal for f e2 e2' e1
      apply (rule exI[of _ "e2"])
      apply (rule exI[of _ "e2'"])
      apply (rule exI[of _ "e1"])
      apply auto
      done
    subgoal for f e e' x
      apply (rule exI[of _ "rrename f e"])
      apply (rule exI[of _ "rrename f e'"])
      apply (rule exI[of _ "f x"])
      apply (auto simp add: Lam_inject id_on_def
          intro!: prems(2) exI[of _ f] Lam_eq_tvsubst term.rrename_cong_ids[symmetric])
      done
    done
*)
  done

thm step.strong_induct
thm step.equiv

(* ALTERNATIVE manual instantiation without the automation provided by binder_inductive *)
(*
declare [[inductive_internal]]
inductive step :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta: "step (App (Lam x e1) e2) (tvsubst (Var(x:=e2)) e1)" binds "{x}"
| AppL: "step e1 e1' \<Longrightarrow> step (App e1 e2) (App e1' e2)"
| AppR: "step e2 e2' \<Longrightarrow> step (App e1 e2) (App e1 e2')"
| Xi: "step e e' \<Longrightarrow> step (Lam x e) (Lam x e')" binds "{x}"

(* INSTANTIATING THE LSNominalSet LOCALE: *)

type_synonym T = "trm \<times> trm"

definition Tperm :: "(var \<Rightarrow> var) \<Rightarrow> T \<Rightarrow> T" where 
"Tperm f \<equiv> map_prod (rrename_term f) (rrename_term f)"

fun Tsupp :: "T \<Rightarrow> var set" where 
"Tsupp (e1,e2) = FFVars_term e1 \<union> FFVars_term e2"


interpretation LSNominalSet where 
Tperm = Tperm and Tsupp = Tsupp
apply standard unfolding isPerm_def Tperm_def  
  using small_Un small_def term.card_of_FFVars_bounds
  apply (auto simp: term.rrename_id0s map_prod.comp term.rrename_comp0s infinite_UNIV)
  using var_sum_class.Un_bound by blast

definition G :: "var set \<Rightarrow> (T \<Rightarrow> bool) \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>B R t.  
         (\<exists>x e1 e2. B = {x} \<and> fst t = App (Lam x e1) e2 \<and> snd t = tvsubst (Var(x := e2)) e1)
         \<or>
         (\<exists>e1 e1' e2. B = {} \<and> fst t = App e1 e2 \<and> snd t = App e1' e2 \<and> 
                      R (e1,e1')) 
         \<or>
         (\<exists>e1 e2 e2'. B = {} \<and> fst t = App e1 e2 \<and> snd t = App e1 e2' \<and> 
                      R (e2,e2')) 
         \<or>
         (\<exists>x e e'. B = {x} \<and> fst t = Lam x e \<and> snd t = Lam x e' \<and> R (e,e'))"


(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma G_mono: "R \<le> R' \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G B R' t"
unfolding G_def by fastforce

(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma G_equiv: "isPerm \<sigma> \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G  (image \<sigma> B) (\<lambda>t'. R (Tperm (inv \<sigma>) t')) (Tperm \<sigma> t)"
  unfolding G_def
  by (elim disj_forward exE; cases t)
    (auto simp: Tperm_def isPerm_def
         term.rrename_comps rrename_tvsubst_comp
         | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
         | ((rule exI[of _ "\<sigma> _"])+; auto))+
(*
unfolding G_def apply(elim disjE)
  subgoal apply(rule disjI4_1)
  subgoal apply(elim exE) subgoal for x e1 e2
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename_term \<sigma> e1"])  
  apply(rule exI[of _ "rrename_term \<sigma> e2"])  
  apply(cases t) unfolding isPerm_def small_def Tperm_def 
  apply (simp add: term.rrename_comps) apply(subst rrename_tvsubst_comp) by auto . .
  (* *)
  subgoal apply(rule disjI4_2)
  subgoal apply(elim exE) subgoal for e1 e1' e2 
  apply(rule exI[of _ "rrename_term \<sigma> e1"]) apply(rule exI[of _ "rrename_term \<sigma> e1'"]) 
  apply(rule exI[of _ "rrename_term \<sigma> e2"]) 
  apply(cases t) unfolding isPerm_def small_def Tperm_def 
  by (simp add: term.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI4_3)
  subgoal apply(elim exE) subgoal for e1 e2 e2' 
  apply(rule exI[of _ "rrename_term \<sigma> e1"]) 
  apply(rule exI[of _ "rrename_term \<sigma> e2"]) apply(rule exI[of _ "rrename_term \<sigma> e2'"]) 
  apply(cases t) unfolding isPerm_def small_def Tperm_def 
  by (simp add: term.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI4_4)
  subgoal apply(elim exE) subgoal for x e e'
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename_term \<sigma> e"]) apply(rule exI[of _ "rrename_term \<sigma> e'"]) 
  apply(cases t) unfolding isPerm_def small_def Tperm_def  
  by (simp add: term.rrename_comps) . . .
*)

lemma fresh: "\<exists>xx. xx \<notin> Tsupp t"  
by (metis Lam_avoid Tsupp.elims term.card_of_FFVars_bounds term.set(2))

(* NB: The entities affected by variables are passed as witnesses to exI 
with x and (the fresh) xx swapped, whereas the non-affected ones are passed 
as they are. 
*)

lemma G_refresh: 
"(\<forall>\<sigma> t. isPerm \<sigma> \<and> R t \<longrightarrow> R (Tperm \<sigma> t)) \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> 
 \<exists>C. small C \<and> C \<inter> Tsupp t = {} \<and> G C R t"
  using fresh[of t] unfolding G_def Tperm_def
(**)isPerm_def conj_assoc[symmetric]
  unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib
  by (elim disj_forward exE; simp)
    ((rule exI, rule conjI[rotated], assumption) |
    (((rule exI conjI)+)?, rule Lam_refresh tvsubst_refresh) |
    (cases t; auto))+
(**)
(*
  apply safe
  subgoal for xx x e1 e2 
  apply(rule exI[of _ "{xx}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding isPerm_def small_def by auto 
    subgoal apply(rule disjI4_1)
    apply(rule exI[of _ "xx"]) 
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e1"]) 
    apply(rule exI[of _ "e2"]) 
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst Lam_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal apply(subst tvsubst_Var_rrename) 
      apply (auto split: if_splits) . . . 
  (* *)
  subgoal for xx e1 e1' e2 
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding isPerm_def small_def by auto 
    subgoal apply(rule disjI4_2) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e1'"])
    apply(rule exI[of _ "e2"]) 
    apply(cases t) apply simp . .
  (* *)
  subgoal for xx e1 e2 e2' 
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding isPerm_def small_def by auto 
    subgoal apply(rule disjI4_3) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e2"])
    apply(rule exI[of _ "e2'"]) 
    apply(cases t) apply simp . .
  (* *)
  subgoal for xx x e e'
  apply(rule exI[of _ "{xx}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding isPerm_def small_def by auto 
    subgoal apply(rule disjI4_4) 
    apply(rule exI[of _ "xx"]) 
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e"])
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e'"])
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst Lam_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal apply(subst Lam_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal by (metis supp_swap_bound Prelim.bij_swap isPerm_def) . . .
  (* *)
*)


(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation Step: Induct where
Tperm = Tperm and Tsupp = Tsupp and G = G
apply standard 
  using G_mono G_equiv G_refresh by auto

(* *)

lemma step_I: "step t1 t2 = Step.I (t1,t2)" 
unfolding step_def Step.I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R tt1 tt2 apply(rule iffI)
  subgoal apply(elim disjE exE)
    \<^cancel>\<open>Beta: \<close>
    subgoal for x e1 e2 apply(rule exI[of _ "{x}"], rule conjI, simp) apply(rule disjI4_1) by auto 
    \<^cancel>\<open>AppL: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp)  apply(rule disjI4_2) by auto
    \<^cancel>\<open>AppR: \<close>
    subgoal apply(rule exI[of _ "{}"], rule conjI, simp)  apply(rule disjI4_3) by auto
    \<^cancel>\<open>Xi: \<close>
    subgoal for e e' x apply(rule exI[of _ "{x}"], rule conjI, simp)  apply(rule disjI4_4) by auto .
  subgoal apply(elim conjE disjE exE)
    \<^cancel>\<open>Beta: \<close>
    subgoal apply(rule disjI4_1) by auto
    \<^cancel>\<open>AppL: \<close>
    subgoal apply(rule disjI4_2) by auto
    \<^cancel>\<open>AppR: \<close>
    subgoal apply(rule disjI4_3) by auto
    \<^cancel>\<open>Xi: \<close>
    subgoal apply(rule disjI4_4) by auto . . .
*)

(* Other properties: *)

(* *)
lemma red_step: "red e ee \<Longrightarrow> step e ee"
by (metis red_def step.Beta)

lemma red_step2: "stream_all2 red es ees \<Longrightarrow> stream_all2 step es ees"
  unfolding stream_all2_iff_snth using red_step by auto


end