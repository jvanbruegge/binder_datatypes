(* Here we instantiate the general enhanced rule induction to 
the "early" pi-calculus transition system.
the adjective refers to the fact that inputs are instantiated 
at transition time (whereas a "late" semantics would 
have transitons with bound inputs)
 *)
theory Pi_Transition
imports Commitment
begin

hide_const trans


(* INSTANTIATING THE ABSTRACT SETTING: *)

(* INSTATIATING THE Small LOCALE (INDEPENDENTLY OF THE CONSIDERED INDUCTIVE PREDICATE *) 

print_locales

(* The "late" transition relation  *)
inductive trans :: "trm \<Rightarrow> cmt \<Rightarrow> bool" where
Inp: "\<comment> \<open>Present in Bengtson: x \<notin> {a,u} \<Longrightarrow> \<close>
trans (Inp a x P) (Finp a u (usub P u x))"
(* |
Out: "trans (Out a x P) (Fout a x P)"
|
Tau: "trans P (Tau P)"
|
Match: "trans P C \<Longrightarrow> trans (Match a a P) C"
|
Sum1: "trans P1 C \<Longrightarrow> trans (Sum P1 P2) C"
|
Sum2: "trans P2 C \<Longrightarrow> trans (Sum P1 P2) C"
*)
|
Open: "trans P (Fout a x P') \<Longrightarrow> a \<noteq> x \<Longrightarrow> 
       trans (Res x P) (Bout a x P')"
|
ScopeF: "trans P (Cmt act P') \<Longrightarrow> \<not> is_bout act \<Longrightarrow> x \<notin> vars act \<Longrightarrow> 
   trans (Res x P) (Cmt act (Res x P'))"
|
ScopeB: "trans P (Bout a x P') \<Longrightarrow> y \<notin> {a,x} \<Longrightarrow> x \<notin> {a} \<union> FFVars P
   \<Longrightarrow> 
   trans (Res y P) (Bout a x (Res y P'))"
|
Par1: "trans P1 (Cmt act P1') \<Longrightarrow> 
   \<^cancel>\<open>present in Bengtson but not needed (and will be an 'output' 
      of strong induction) : bvars act \<inter> fvars act = {} \<Longrightarrow> \<close>  
   bvars act \<inter> FFVars P1 = {} \<Longrightarrow> 
   bvars act \<inter> FFVars P2 = {} \<Longrightarrow> 
   trans (Par P1 P2) (Cmt act (Par P1' P2))" 
(* |
Par2: "trans P2 (Cmt act P2') \<Longrightarrow> bvars act \<inter> FFVars P1 = {} \<Longrightarrow> 
   trans (Par P1 P2) (Cmt act (Par P1 P2'))" *)
|
Com1: "trans P1 (Finp a x P1') \<Longrightarrow> trans P2 (Fout a x P2') \<Longrightarrow> 
   trans (Par P1 P2) (Tau (Par P1' P2'))" 
(* |
Com2: "trans P1 (Fout a x P1') \<Longrightarrow> trans P2 (Finp a x P2') \<Longrightarrow> 
   trans (Par P1 P2) (Tau (Par P1' P2'))"  *)
|
Close1: "trans P1 (Finp a x P1') \<Longrightarrow> trans P2 (Bout a x  P2') \<Longrightarrow>
    \<^cancel>\<open>  x \<noteq> a seems essential, and not an artifact \<close> 
   x \<notin> {a} \<union> FFVars P1 \<^cancel>\<open>\<union> FFVars P2 was in Bengtson\<close>  \<Longrightarrow>
   trans (Par P1 P2) (Tau (Res x (Par P1' P2')))" 
(*  
x fresh P1  x=/=a
trans (P1=[xx/x]) (Finp a[xx/x[xx/x])] xx P1' \<Longrightarrow> trans P2 (Bout a xx  P2'[xx/x]) 
\<Longrightarrow>
trans (Par P1 P2) (Bout a xx (Par P1'[xx/x] P2'[xx/x])) 
*)
(* |
Close2: "trans P1 (Bout a x P1') \<Longrightarrow> trans P2 (Finp a x P2') \<Longrightarrow> 
   x \<notin> {a} \<union> FFVars P1 \<union> FFVars P2 \<Longrightarrow>
   trans (Par P1 P2) (Bout a x (Par P1' P2'))" 
|
Bang: "trans (Par P (Bang P)) C \<Longrightarrow> trans (Bang P) C"
*)


(* INSTANTIATING THE Components LOCALE: *)

type_synonym T = "trm \<times> cmt"
type_synonym V = "var list" 


definition Tmap :: "(var \<Rightarrow> var) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> map_prod (rrename f) (rrename_commit f)"

fun Tfvars :: "T \<Rightarrow> var set" where 
"Tfvars (e1,e2) = FFVars e1 \<union> FFVars_commit e2"

(*
definition Vmap :: "(var \<Rightarrow> var) \<Rightarrow> V \<Rightarrow> V" where 
"Vmap \<equiv> map"

fun Vfvars :: "V \<Rightarrow> var set" where 
"Vfvars v = set v"
*)

lemmas commit_internal.FFVars_rrenames[simp]

interpretation Components where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars
apply standard unfolding ssbij_def Tmap_def 
  using small_Un small_def term.card_of_FFVars_bounds
    commit_internal.card_of_FFVars_bounds(2)
  apply (auto simp: term.rrename_id0s map_prod.comp term.rrename_comp0s 
        commit_internal.rrename_cong_ids(2)
        commit_internal.rrename_id0s commit_internal.rrename_comp0s(2)
          inf_A) 
  by blast 

lemma small_bvars[simp,intro!]: "small (bvars act)"
by (cases act, auto)

definition G :: "var set \<Rightarrow> (T \<Rightarrow> bool) \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>B R t.
 \<^cancel>\<open>Inp: \<close>  
 (\<exists>x a u P. 
    B = {x} \<and> fst t = Inp a x P \<and> snd t = Finp a u (usub P u x) 
 \<comment> \<open>\<and> x \<notin> {a,u} \<close>)
 \<or>  \<^cancel>\<open>Open: \<close> 
 (\<exists>P a x P'. 
    B = {x} \<and> fst t = Res x P \<and> snd t = Bout a x P' \<and> 
    a \<noteq> x \<and> 
    R (P,Fout a x P')) 
 \<or>  \<^cancel>\<open>ScopeF: \<close> 
 (\<exists> P act P' x.  
    B = {x} \<and> fst t = Res x P \<and> snd t = Cmt act (Res x P') \<and>  
    \<not> is_bout act \<and> x \<notin> vars act \<and> 
    R (P, Cmt act P'))
 \<or>  \<^cancel>\<open>ScopeB: \<close> 
 (\<exists> P a x P' y. 
    B = {x,y} \<and> fst t = Res y P \<and> snd t = Bout a x (Res y P') \<and>  
    y \<notin> {a,x} \<and> x \<notin> {a} \<union> FFVars P \<and>  
    R (P, Bout a x P'))
 \<or>  \<^cancel>\<open>Par1: \<close> 
 (\<exists>P1 act P1' P2. 
    B = bvars act \<and> fst t = Par P1 P2 \<and> snd t = Cmt act (Par P1' P2) \<and> 
    bvars act \<inter> FFVars P1 = {} \<and> 
    bvars act \<inter> FFVars P2 = {} \<and> 
    R (P1, Cmt act P1'))
 \<or> \<^cancel>\<open>Com1: \<close> 
 (\<exists>P1 a x P1' P2 P2'. 
    B = {} \<and> fst t = Par P1 P2 \<and> snd t = Tau (Par P1' P2') \<and>  
    R (P1, Finp a x P1') \<and> R (P2, Fout a x P2'))
 \<or> \<^cancel>\<open>Close1: \<close> 
 (\<exists>P1 a x P1' P2 P2'. 
    B = {x} \<and> fst t = Par P1 P2 \<and> snd t = Tau (Res x (Par P1' P2')) \<and> 
    x \<notin> {a} \<union> FFVars P1 \<and> 
    R (P1, Finp a x P1') \<and> R (P2, Bout a x P2'))
"


(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma GG_mono: "R \<le> R' \<Longrightarrow> G v R t \<Longrightarrow> G v R' t"
unfolding G_def by (smt (z3) le_boolE le_funD)


(* *)

(* lemma FFVars_commit_Cmt[simp]: "FFVars_commit (Cmt act P) = FFVars P" *)
 

(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma GG_equiv: "ssbij \<sigma> \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G (image \<sigma> B) (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Tmap \<sigma> t)"
  unfolding G_def
  by (elim disj_forward exE; cases t)
    (auto simp: Tmap_def ssbij_def
         term.rrename_comps action.map_comp action.map_id
         | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
         | (rule exI[of _ "map_action \<sigma> _"])
         | ((rule exI[of _ "\<sigma> _"])+; auto))+
(*
  unfolding G_def
        apply(elim disjE)
  (* Inp: *)
  subgoal apply(rule disjI7_1)
  subgoal apply(elim exE) subgoal for x a u P
  apply(rule exI[of _ "\<sigma> x"]) apply(rule exI[of _ "\<sigma> a"]) 
  apply(rule exI[of _ "\<sigma> u"]) apply(rule exI[of _ "rrename \<sigma> P"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  by (simp add: term.rrename_comps) . . 
  (* Open: *)
  subgoal apply(rule disjI7_2)
  subgoal apply(elim exE) subgoal for P a x P'
  apply(rule exI[of _ "rrename \<sigma> P"])
  apply(rule exI[of _ "\<sigma> a"]) apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename \<sigma> P'"])   
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  by (simp add: term.rrename_comps) . . 
  (* ScopeF: *)
  subgoal apply(rule disjI7_3)
  subgoal apply(elim exE) subgoal for P act P' x
  apply(rule exI[of _ "rrename \<sigma> P"])
  apply(rule exI[of _ "map_action \<sigma> act"])
  apply(rule exI[of _ "rrename \<sigma> P'"])
  apply(rule exI[of _ "\<sigma> x"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def  
  apply (simp add: term.rrename_comps) 
  by (auto simp add: action.map_id action.map_comp) . .
  (* ScopeB: *)
  subgoal apply(rule disjI7_4)
  subgoal apply(elim exE) subgoal for P a x P' y
  apply(rule exI[of _ "rrename \<sigma> P"])
  apply(rule exI[of _ "\<sigma> a"]) 
  apply(rule exI[of _ "\<sigma> x"]) 
  apply(rule exI[of _ "rrename \<sigma> P'"])
  apply(rule exI[of _ "\<sigma> y"])   
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  apply (simp add: term.rrename_comps) 
  by auto . .
  (* Par1: *)
  subgoal apply(rule disjI7_5)
  subgoal apply(elim exE) subgoal for P1 act P1' P2
  apply(rule exI[of _ "rrename \<sigma> P1"])
  apply(rule exI[of _ "map_action \<sigma> act"])
  apply(rule exI[of _ "rrename \<sigma> P1'"])
  apply(rule exI[of _ "rrename \<sigma> P2"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  apply (simp add: term.rrename_comps)  
  by (auto simp add: action.map_id action.map_comp) . .
  (* Com1: *)
  subgoal apply(rule disjI7_6)
  subgoal apply(elim exE) subgoal for P1 a x P1' P2 P2'
  apply(rule exI[of _ "rrename \<sigma> P1"])
  apply(rule exI[of _ "\<sigma> a"])
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename \<sigma> P1'"])
  apply(rule exI[of _ "rrename \<sigma> P2"])
  apply(rule exI[of _ "rrename \<sigma> P2'"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  by (simp add: term.rrename_comps) . .
  (* Close1: *)
  subgoal apply(rule disjI7_7)
  subgoal apply(elim exE) subgoal for P1 a x P1' P2 P2'
  apply(rule exI[of _ "rrename \<sigma> P1"])
  apply(rule exI[of _ "\<sigma> a"])
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename \<sigma> P1'"])
  apply(rule exI[of _ "rrename \<sigma> P2"])
  apply(rule exI[of _ "rrename \<sigma> P2'"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  apply (simp add: term.rrename_comps)
  by auto . . .
*)

(* *)



(*  *)

find_theorems FFVars vvsubst


(* Supply of fresh variables: *)

lemma finite_Tfvars: "finite (Tfvars t)"
using finite_iff_le_card_var small_Tfvars small_def by blast

lemma exists_fresh:
"\<exists> z. z \<notin> set xs \<and> (\<forall>t \<in> set ts. z \<notin> Tfvars t)"
proof-
  have 0: "|set xs \<union> \<Union> (Tfvars ` (set ts))| <o |UNIV::var set|" 
  unfolding ls_UNIV_iff_finite  
  using finite_Tfvars by blast
  then obtain x where "x \<notin> set xs \<union> \<Union> (Tfvars ` (set ts))"
  by (meson ex_new_if_finite finite_iff_le_card_var 
    infinite_iff_natLeq_ordLeq var_term_pre_class.large)
  thus ?thesis by auto
qed

lemma finite_vars: "finite (vars act)"
  by (cases act) auto

lemma exists_fresh':
"\<exists> z. z \<notin> set xs \<and> (\<forall>t \<in> set as. z \<notin> vars t) \<and> (\<forall>t \<in> set ts. z \<notin> Tfvars t)"
proof-
  have 0: "|set xs \<union> \<Union> (Tfvars ` (set ts)) \<union> \<Union> (vars ` (set as))| <o |UNIV::var set|" 
  unfolding ls_UNIV_iff_finite
  using finite_Tfvars finite_vars by blast
  then obtain x where "x \<notin> set xs \<union> \<Union> (Tfvars ` (set ts)) \<union> \<Union> (vars ` (set as))"
  by (meson ex_new_if_finite finite_iff_le_card_var 
    infinite_iff_natLeq_ordLeq var_term_pre_class.large)
  thus ?thesis by auto
qed

ML \<open>fun gen_fresh ctxt xs0 acts0 ts0 = HEADGOAL (Subgoal.FOCUS_PARAMS (fn {context = ctxt, params = cps, ...} =>
  let
    val ps = map (Thm.term_of o snd) cps;
    fun mk zs T = filter (fn t => fastype_of t = T) ps |> append zs |> HOLogic.mk_list T |> Thm.cterm_of ctxt;
    val xs = mk xs0 @{typ var};
    val acts = mk acts0 @{typ "var action"};
    val ts = mk ts0 @{typ "var term * var commit"};
    val thm = infer_instantiate' ctxt [SOME xs, SOME acts, SOME ts] @{thm exists_fresh'} RS exE;
  in HEADGOAL (resolve_tac ctxt [thm]) end) ctxt)\<close>

lemma ssbij_swap: "ssbij (id(x := y, y := x))"
  by (auto simp: ssbij_def)

lemma R_forw_subst: "R (x, y) \<Longrightarrow> (\<And>x y. R (x, y) \<Longrightarrow> R (f x, g y)) \<Longrightarrow> z = g y \<Longrightarrow> R (f x, z)"
  by blast

lemma FFVars_commit_Cmt: "FFVars_commit (Cmt act P) = fvars act \<union> (FFVars P - bvars act)"
  by (cases act) auto

lemma not_is_bout_bvars: "\<not> is_bout act \<longleftrightarrow> bvars act = {}"
  by (cases act) auto

lemma empty_bvars_vars_fvars: "bvars act = {} \<Longrightarrow> vars act = fvars act"
  by (cases act) auto

lemma bvars_swapa: "bvars act = {} \<Longrightarrow> bvars (swapa act x xx) = {}"
  by (cases act) auto

lemma fvars_swapa: "xx \<in> fvars (swapa act x xx) \<longleftrightarrow> x \<in> fvars act"
  by (cases act) auto

lemma swapa_idle: "xx \<notin> vars act \<Longrightarrow> x \<notin> vars act \<Longrightarrow> swapa act x xx = act"
  by (cases act) auto

lemmas act_var_simps = not_is_bout_bvars empty_bvars_vars_fvars bvars_swapa fvars_swapa swapa_idle

(* NB: The entities affected by variables are passed as witnesses to exI 
with x and (the fresh) xx swapped, whereas the non-affected ones are passed 
as they are. 
*)
lemma G_refresh: 
  assumes "(\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t))"
  shows "small B \<Longrightarrow> G B R t \<Longrightarrow> \<exists>C. small C \<and> C \<inter> Tfvars t = {} \<and> G C R t"
unfolding G_def
(**)ssbij_def conj_assoc[symmetric]
  unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib ex_simps(1,2)[symmetric]
    ex_comm[where P = P for P :: "_ set \<Rightarrow> _ \<Rightarrow> _"]
  apply (elim disj_forward exE; simp; tactic \<open>REPEAT_DETERM_N 2 (gen_fresh @{context} [] [] [@{term t}])\<close>; clarsimp)
        apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl])
        | (erule (1) R_forw_subst[of R, OF _ assms[unfolded Tmap_def, simplified, rule_format, OF conjI[OF ssbij_swap]]]; simp?)
        | (cases t; auto simp only: fst_conv snd_conv Tfvars.simps term.set FFVars_commit_simps FFVars_commit_Cmt act_var_simps))+) [3]
  subgoal for P a x P' y z1 z2
    apply (rule exI[of _ "swap P y z1"])
    apply (rule exI[of _ a])
    apply (rule exI[of _ z2])
    apply (rule conjI) apply assumption
    apply (rule exI[of _ "swap (swap P' x z2) y z1"])
    apply (rule exI[of _ z1])
    apply (rule conjI) apply assumption
    apply clarsimp
    apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl] refl)))
     apply (cases t; auto) []
    apply (rule conjI, (cases t; auto) [])
    apply (rule conjI[OF sym])
    apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl] refl)))
     apply (cases t; simp)
    apply (smt (verit, best) image_iff sw_diff sw_eqR)
    apply (rule conjI)
     apply (cases t; simp)
    apply (smt (verit, best) image_iff sw_diff sw_eqR)
    apply (erule (1) R_forw_subst[of R, OF _ assms[unfolded Tmap_def, simplified, rule_format, OF conjI[OF ssbij_swap]]]; simp?)
    apply (rule conjI)
     apply (cases t; simp)
     apply (smt (verit, best) image_iff sw_diff sw_eqR)
     apply (cases t; simp)
    apply (simp add: swap_commute term.rrename_comps[where w="swap P' y z1"] supp_comp_bound[OF _ _ inf_A]
      term.rrename_cong_ids[symmetric])
    done
  subgoal for P1 act P1' P2 z1 z2
    using bvars_act_bout[of act]
    apply (elim disjE exE)
    apply (rule exI[of _ act])
     apply (cases t; auto)
    subgoal for a b
      apply (intro exI[of _ "bout a z1"] conjI)
       apply (cases t; simp)
      apply (intro exI[of _ "swap P1' b z1"] conjI)
       apply (cases t; simp)
       apply (cases t; simp)
       apply (cases t; simp)
       apply (cases t; simp)
      apply (metis Bout_inj)
      done
    done
    apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl])
        | (erule (1) R_forw_subst[of R, OF _ assms[unfolded Tmap_def, simplified, rule_format, OF conjI[OF ssbij_swap]]]; simp?)
        | (cases t; auto simp only: fst_conv snd_conv Tfvars.simps term.set FFVars_commit_simps FFVars_commit_Cmt act_var_simps))+) []
  subgoal for P1 a x P1' P2 P2' z1 z2
    apply (rule exI[of _ a])
    apply (rule exI[of _ z1])
    apply (rule conjI) apply assumption
    apply (rule exI[of _ "swap P1' x z1"])
    apply (rule exI[of _ "swap P2' x z1"])
    apply (intro conjI)
        apply (cases t; simp add: Res_refresh[of z1 "Par P1' P2'" x])
       apply assumption
      apply (cases t; simp)
     apply (drule assms[unfolded Tmap_def, simplified, rule_format, OF conjI[OF ssbij_swap], of _ _ x z1])
     apply (cases t; simp)
    apply (drule assms[unfolded Tmap_def, simplified, rule_format, OF conjI[OF ssbij_swap], of _ _ x z1])
    apply (cases t; simp)
    apply (metis Bout_inj)
    done
(*
  using assms
unfolding G_def Tmap_def apply(elim disjE exE conjE)
  (* Inp: *) 
  subgoal for x a u P
  using exists_fresh[of "[]" "[t]"] apply(elim exE conjE)
  subgoal for xx
  apply(rule exI[of _ "{xx}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI7_1) 
    apply(rule exI[of _ "xx"]) 
    apply(rule exI[of _ "a"])
    apply(rule exI[of _ "u"]) 
    apply(rule exI[of _ "swap P x xx"])
    apply(cases t) 
    by (simp add: Inp_refresh usub_refresh) . .
  (* Open: *)
  subgoal for P a x P'
  using exists_fresh[of "[]" "[t]"] apply(elim exE conjE)
  subgoal for xx
  apply(rule exI[of _ "{xx}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI7_2) 
    apply(rule exI[of _ "swap P x xx"])
    apply(rule exI[of _ "a"]) 
    apply(rule exI[of _ "xx"])
    apply(rule exI[of _ "swap P' x xx"]) 
    apply(cases t)  apply simp apply(intro conjI)
      subgoal using Res_refresh by blast
      subgoal by auto
      apply(erule allE[of _ "id(x:=xx,xx:=x)"])
      apply(erule allE[of _ "P"])
      apply(erule allE[of _ "Fout a x P'"]) 
      by (auto simp: ssbij_def split: if_splits ) . .
  (* ScopeF: *)
  subgoal for P act P' x
    unfolding not_is_bout_bvars
    subgoal
    using exists_fresh[of "[]" "[t]"] apply(elim exE conjE)
    subgoal for xx
    apply(rule exI[of _ "{xx}"])  
    apply(intro conjI)
      subgoal by simp
      subgoal unfolding ssbij_def small_def by auto 
      subgoal apply(rule disjI7_3) 
      apply(rule exI[of _ "swap P x xx"])
      apply(rule exI[of _ "swapa act x xx"]) 
      apply(rule exI[of _ "swap P' x xx"])
      apply(rule exI[of _ "xx"]) 
      apply(cases t) apply simp apply(intro conjI)
        subgoal using Res_refresh by blast
        subgoal using Res_refresh apply(cases act, simp_all split: if_splits)  
        by blast+
        subgoal by auto
        subgoal apply(erule allE[of _ "id(x:=xx,xx:=x)"])
        apply(erule allE[of _ "P"])
        apply(erule allE[of _ "Cmt act P'"]) 
        by (auto simp: ssbij_def split: if_splits ) . . . .
  (* ScopeB: *)
  subgoal for P a x P' y
  using exists_fresh[of "[a,x,y]" "[t]"] apply(elim exE conjE)
  subgoal for yy
  using exists_fresh[of "[a,x,y,yy]" "[t]"] apply(elim exE conjE)
  subgoal for xx  
  apply(rule exI[of _ "{xx,yy}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def  by auto 
    subgoal apply(rule disjI7_4)
    apply(rule exI[of _ "swap P y yy"])
    apply(rule exI[of _ "a"]) 
    apply(rule exI[of _ "xx"])
    apply(rule exI[of _ "swap (swap P' x xx) y yy"]) 
    apply(cases t) apply (simp add: sw_def) apply(intro conjI)
      subgoal using Res_refresh by auto
      apply(erule allE[of _ "id(x:=xx,xx:=x) o id(y:=yy,yy:=y)"])
      apply(erule allE[of _ "P"])
      apply(erule allE[of _ "Bout a x P'"]) 
      apply clarify apply(rule exI[of _ yy])     
      apply (simp add: ssbij_def rrename_o_swap split: if_splits)
      apply safe 
        subgoal using infinite_var not_ordLeq_ordLess supp_comp_bound by blast
        subgoal by (metis (no_types, lifting) Res_inject_swap Res_refresh) 
        subgoal using not_ordLess_ordLeq term_pre.supp_comp_bound by blast
        subgoal using Res_refresh by blast
        subgoal by (metis Res_inject_swap Res_refresh)
        subgoal apply(subgoal_tac "swap (swap P y yy) x xx = swap P y yy")
        defer subgoal apply(rule FFVars_swap') by (auto simp: sw_def)
        apply(subst swap_commute) by auto . . . .
  (* Par1 *)
  subgoal for P1 act P1' P2
  using bvars_act_bout[of act] apply(elim disjE exE)
    subgoal
    using exists_fresh[of "[]" "[t]"] apply(elim exE conjE)
    subgoal for yy
    apply(rule exI[of _ "{}"])  
    apply(intro conjI)
      subgoal by simp
      subgoal unfolding ssbij_def small_def by auto 
      subgoal apply(rule disjI7_5) 
      apply(rule exI[of _ P1])
      apply(rule exI[of _ act]) 
      apply(rule exI[of _ P1'])
      apply(rule exI[of _ P2]) 
      apply(cases t) by simp  . . 
    (* *)
    subgoal for a b
    using exists_fresh[of "[a,b]" "[t]"] apply(elim exE conjE)
    subgoal for bb
    apply(rule exI[of _ "{bb}"])  
    apply(intro conjI)
      subgoal by simp
      subgoal unfolding ssbij_def small_def by auto 
      subgoal apply(rule disjI7_5)
      apply(rule exI[of _ P1]) 
      apply(rule exI[of _ "bout a bb"]) 
      apply(rule exI[of _ "swap P1' b bb"])
      apply(rule exI[of _ P2]) 
      apply(cases t) apply simp  
      by (metis Bout_inj) . . . 
  (* Com1: *)
  subgoal for P1 a x P1' P2 P2'
  apply(rule exI[of _ "{}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI7_6) 
      apply(rule exI[of _ P1])
      apply(rule exI[of _ a]) 
      apply(rule exI[of _ x])
      apply(rule exI[of _ P1']) 
      apply(rule exI[of _ P2]) 
      apply(rule exI[of _ P2']) 
      apply(cases t) by simp . 
  (* Close1: *)
  subgoal for P1 a x P1' P2 P2'
  using exists_fresh[of "[a,x]" "[t]"] apply(elim exE conjE)
  subgoal for xx
  apply(rule exI[of _ "{xx}"])  
  apply(intro conjI)
    subgoal by simp
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI7_7)
    apply(rule exI[of _ "swap P1 x xx"]) 
    apply(rule exI[of _ a]) 
    apply(rule exI[of _ xx])
    apply(rule exI[of _ "swap P1' x xx"])
    apply(rule exI[of _ P2]) 
    apply(rule exI[of _ "swap P2' x xx"]) 
    apply(cases t) apply simp apply(intro conjI)
      subgoal by (simp add: Res_inject_swap fun_upd_twist)
      subgoal apply(erule allE[of _ "id(x:=xx,xx:=x)"])
      apply(erule allE[of _ "P1"])
      apply(erule allE[of _ "Finp a x P1'"])      
      by (auto simp: ssbij_def split: if_splits)  
      subgoal apply(erule allE[of _ "id(x:=xx,xx:=x)"])
      apply(erule allE[of _ "P1"])
      apply(erule allE[of _ "Bout a x P1'"])      
      apply (simp add: ssbij_def split: if_splits)  
      by (metis Bout_inj)+ . . .
*) .

(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation Trans: Induct where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars and G = G
apply standard 
  using GG_mono GG_equiv G_refresh by auto


lemma trans_I: "trans t1 t2 = Trans.I (t1,t2)" 
unfolding trans_def Trans.I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R PP QQ apply(rule iffI)
  subgoal apply(elim disjE exE)
    \<^cancel>\<open>Inp: \<close>
    subgoal for a x P apply(rule exI[of _ "{x}"], rule conjI, simp) apply(rule disjI7_1) by auto
    \<^cancel>\<open>Open: \<close>
    subgoal for P a x apply(rule exI[of _ "{x}"], rule conjI, simp) apply(rule disjI7_2) by auto
    \<^cancel>\<open>ScopeF: \<close> 
    subgoal for P act P' x apply(rule exI[of _ "{x}"], rule conjI, simp) apply(rule disjI7_3) by auto
    \<^cancel>\<open>ScopeB: \<close> 
    subgoal for P a x P' y 
    apply(rule exI[of _ "{x, y}"], rule conjI, simp) apply(rule disjI7_4) 
    by (fastforce simp: sw_def)
    \<^cancel>\<open>Par1: \<close>
    subgoal for P1 act P1' P2 apply(rule exI[of _ "bvars act"], rule conjI, simp) 
    apply(rule disjI7_5) by auto
    \<^cancel>\<open>Com1: \<close> 
    subgoal for P1 a x P1' P2 apply(rule exI[of _ "{}"], rule conjI, simp) apply(rule disjI7_6) by auto
    \<^cancel>\<open>Close1: \<close> 
    subgoal for P1 a x P1' P2 apply(rule exI[of _ "{x}"], rule conjI, simp) apply(rule disjI7_7) by auto .
    (* *)
  subgoal apply(elim conjE disjE exE)
    \<^cancel>\<open>Inp: \<close>
    subgoal apply(rule disjI7_1) by auto
    \<^cancel>\<open>Open: \<close>
    subgoal apply(rule disjI7_2) by fastforce
    \<^cancel>\<open>ScopeF: \<close> 
    subgoal apply(rule disjI7_3) by auto
    \<^cancel>\<open>ScopeB: \<close> 
    subgoal apply(rule disjI7_4) by (fastforce simp: sw_def)
    \<^cancel>\<open>Par1: \<close>
    subgoal apply(rule disjI7_5) by auto
    \<^cancel>\<open>Com1: \<close> 
    subgoal apply(rule disjI7_6) by auto
    \<^cancel>\<open>Close1: \<close> 
    subgoal apply(rule disjI7_7) by auto . . .

(* FROM ABSTRACT BACK TO CONCRETE: *)
thm trans.induct[of P C \<phi>, no_vars]

corollary strong_induct_trans[consumes 2, case_names Inp Open ScopeF ScopeB Par1 Com1 Close1]: 
assumes 
par: "\<And>p. small (Pfvars p)" 
and tr: "trans P C"
and Inp: 
"\<And>x a u P p. x \<notin> {a, u} \<Longrightarrow> 
    \<phi> p (Inp a x P) (Finp a u (usub P u x))"
and Open:  
"\<And>P a x P' p. x \<notin> Pfvars p \<Longrightarrow> x \<noteq> a \<Longrightarrow> 
    trans P (Fout a x P') \<Longrightarrow> (\<forall>p'. \<phi> p' P (Fout a x P')) \<Longrightarrow> a \<noteq> x \<Longrightarrow> 
    \<phi> p (Res x P) (Bout a x P')"
and ScopeF: 
"\<And>P act P' y p. y \<notin> Pfvars p \<Longrightarrow> y \<notin> fvars act \<Longrightarrow> 
    trans P (Cmt act P') \<Longrightarrow> (\<forall>p'. \<phi> p' P (Cmt act P')) \<Longrightarrow> y \<notin> vars act \<Longrightarrow> 
    \<phi> p (Res y P) (Cmt act (Res y P'))"
and ScopeB: 
"\<And>P a x P' y p. {x,y} \<inter> Pfvars p = {} \<Longrightarrow> a \<notin> {x,y} \<Longrightarrow> 
    trans P (Bout a x P') \<Longrightarrow> (\<forall>p'. \<phi> p' P (Bout a x P')) \<Longrightarrow> y \<notin> {a, x} \<Longrightarrow> x \<notin> {a} \<union> FFVars P \<Longrightarrow>
    \<phi> p (Res y P) (Bout a x (Res y P'))" 
and Par1: 
"\<And>P1 act P1' P2 p. bvars act \<inter> (Pfvars p \<union> fvars act) = {} \<Longrightarrow> 
    trans P1 (Cmt act P1') \<Longrightarrow>
    (\<forall>p'. \<phi> p' P1 (Cmt act P1')) \<Longrightarrow>
    bvars act \<inter> FFVars P1 = {} \<Longrightarrow> 
    bvars act \<inter> FFVars P2 = {} \<Longrightarrow> 
    \<phi> p (Par P1 P2) (Cmt act (Par P1' P2))"
and Com1: 
"\<And>P1 a x P1' P2 P2' p. 
    trans P1 (Finp a x P1') \<Longrightarrow>
    (\<forall>p'. \<phi> p' P1 (Finp a x P1')) \<Longrightarrow> 
    trans P2 (Fout a x P2') \<Longrightarrow> 
    (\<forall>p'. \<phi> p' P2 (Fout a x P2')) \<Longrightarrow> 
    \<phi> p (Par P1 P2) (Tau (Par P1' P2'))"
and Close1: 
"\<And>P1 a x P1' P2 P2' p. x \<notin> Pfvars p \<Longrightarrow> x \<notin> FFVars P2 \<Longrightarrow> 
    trans P1 (Finp a x P1') \<Longrightarrow>
    (\<forall>p'. \<phi> p' P1 (Finp a x P1')) \<Longrightarrow>
    trans P2 (Bout a x P2') \<Longrightarrow>
    (\<forall>p'. \<phi> p' P2 (Bout a x P2')) \<Longrightarrow> 
    x \<notin> {a} \<union> FFVars P1 \<Longrightarrow> 
    \<phi> p (Par P1 P2) (Tau (Res x (Par P1' P2')))"
shows "\<phi> p P C" 
apply(subgoal_tac "case (P,C) of (P, C) \<Rightarrow> \<phi> p P C")
  subgoal by simp
  subgoal using par tr apply(elim Trans.strong_induct[where R = "\<lambda>p (P,C). \<phi> p P C"])
    subgoal unfolding trans_I by simp
    subgoal for p v t apply(subst (asm) G_def) 
    unfolding trans_I[symmetric] apply(elim disjE exE)
      subgoal using Inp by auto
      subgoal using Open by auto
      subgoal for Pa act P' y using ScopeF[of y p act] by (cases act, auto) 
      subgoal using ScopeB by auto
      subgoal for P1 act P1' P2 using Par1[of act] by (cases act, auto)
      subgoal using Com1 by auto
      subgoal using Close1 by auto . . .

(* Also inferring equivariance from the general infrastructure: *)
corollary rrename_pstep:
assumes f: "bij f" "|supp f| <o |UNIV::var set|" 
and r: "trans P C" 
shows "trans (rrename f P) (rrename_commit f C)"
using assms unfolding trans_I using Trans.I_equiv[of "(P,C)" f]
unfolding Tmap_def ssbij_def by auto



end