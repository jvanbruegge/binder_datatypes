(* Here we instantiate the general enhanced rule induction to 
the (todo: lazy/eager) pi-calculus transition system
 *)
theory Pi_Transition
imports Pi  "../Instantiation_Infrastructure/Curry_LFP" 
"../Generic_Barendregt_Enhanced_Rule_Induction"
begin

ML \<open>
Multithreading.parallel_proofs := 4
\<close>

local_setup \<open>fn lthy =>
let
  val name1 = "commit_internal"
  val name2 = "commit"
  val T1 = @{typ "'var term"}
  val T2 = @{typ "'var * 'var * 'var term +'var * 'var * 'var term + 'var * 'bvar * 'brec"}
  val Xs = map dest_TFree []
  val resBs = map dest_TFree [@{typ 'var}, @{typ 'bvar}, @{typ 'brec}, @{typ 'rec}]
  val rel = [[0]]

  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify1 = Binding.prefix_name (name1 ^ "_pre_")
  val qualify2 = Binding.prefix_name (name2 ^ "_pre_")

  (* Step 1: Create pre-MRBNF *)
  val ((mrbnf1, tys1), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline qualify1 flatten_tyargs Xs []
    [(dest_TFree @{typ 'var}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var)] T1
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)
  val ((mrbnf2, tys2), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline qualify2 flatten_tyargs Xs []
    [(dest_TFree @{typ 'var}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var)] T2
    (accum, lthy);

  val (tys, _, (mrbnfs as [mrbnf1, mrbnf2], (accum, lthy))) =
      MRBNF_Comp.normalize_mrbnfs (K I) [] (map (map dest_TFree) [snd tys1, snd tys2])
      [] (K (resBs @ Xs)) NONE [mrbnf1, mrbnf2] (accum, lthy);

  (* Step 2: Seal the pre-MRBNF with a typedef *)
  val ((mrbnf1, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name (name1 ^ "_pre")) true (fst tys1) [] mrbnf1 lthy
  val ((mrbnf2, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name (name2 ^ "_pre")) true (fst tys2) [] mrbnf2 lthy

  (* Step 3: Register the pre-MRBNF as a BNF in its live variables *)
  val (bnf1, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf1 lthy
  val (bnf2, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf2 lthy

  (* Step 4: Create fixpoint of pre-MRBNF *)
  val (res, lthy) = MRBNF_FP.construct_binder_fp MRBNF_Util.Least_FP [
    ((name1, mrbnf1), 1), ((name2, mrbnf2), 1)
  ] rel lthy;
in lthy end
\<close>
print_theorems

definition Finp :: "'a::{var_commit_pre,var_commit_internal_pre} \<Rightarrow> 'a \<Rightarrow> 'a term \<Rightarrow> 'a commit" where
  "Finp x y t \<equiv> commit_ctor (Abs_commit_pre (Inl (x, y, t)))"
definition Fout :: "'a::{var_commit_pre,var_commit_internal_pre} \<Rightarrow> 'a \<Rightarrow> 'a term \<Rightarrow> 'a commit" where
  "Fout x y t \<equiv> commit_ctor (Abs_commit_pre (Inr (Inl (x, y, t))))"
definition Bout :: "'a::{var_commit_pre,var_commit_internal_pre} \<Rightarrow> 'a \<Rightarrow> 'a term \<Rightarrow> 'a commit" where
  "Bout x y t \<equiv> commit_ctor (Abs_commit_pre (Inr (Inr (x, y, commit_internal_ctor (Abs_commit_internal_pre t)))))"

lemma FFVars_commit_simps[simp]:
  "FFVars_commit (Finp x y t) = {x, y} \<union> FFVars_term t"
  "FFVars_commit (Fout x y t) = {x, y} \<union> FFVars_term t"
  "FFVars_commit (Bout x y t) = {x} \<union> (FFVars_term t - {y})"
  apply (unfold Bout_def Finp_def Fout_def)
  apply (rule trans)
     apply (rule commit_internal.FFVars_cctors)
    defer
    apply (rule trans, rule commit_internal.FFVars_cctors)
    defer
    apply (rule trans, rule commit_internal.FFVars_cctors)
  apply (unfold set1_commit_pre_def comp_def Abs_commit_pre_inverse[OF UNIV_I] map_prod_simp
    UN_empty UN_empty2 prod_set_simps set3_commit_pre_def cSup_singleton Un_empty_left Un_empty_right
    Sup_empty set2_commit_pre_def set4_commit_pre_def UN_single map_sum.simps sum_set_simps
  )
    apply (rule arg_cong2[OF refl, of _ _ "(\<union>)"])
apply (rule arg_cong2[OF _ refl, of _ _ minus])
  apply (rule trans)
   apply (rule commit_internal.FFVars_cctors)
  apply (unfold set1_commit_internal_pre_def comp_def Abs_commit_internal_pre_inverse[OF UNIV_I] map_prod_simp prod_set_simps
    UN_empty cSup_singleton Un_empty_left Un_empty_right set3_commit_internal_pre_def empty_Diff
    set4_commit_internal_pre_def
  )
    apply auto
  done

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* INSTATIATING THE Small LOCALE (INDEPENDENTLY OF THE CONSIDERED INDUCTIVE PREDICATE *) 

print_locales
interpretation Small where dummy = "undefined :: var" 
apply standard
by (simp_all add: infinite_var regularCard_var)  


abbreviation "usub P y x \<equiv> vvsubst (id(x:=y)) P"
 

(* AN EXAMPLE INDUCTIVE DEFINITION *)
(* (a reduced form of) small trans semantics *) 
find_theorems vvsubst
inductive trans :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
Inp: "trans (Inp a x P) (usub P y x)"
|
Out: "trans (Out a x P) (usub P y x)"




term 
| App: "trans e1 e1' \<Longrightarrow> trans e2 e2' \<Longrightarrow> trans (App e1 e2) (App e1' e2')"
| Xi: "trans e e' \<Longrightarrow> trans (Abs x e) (Abs x e')"
| PBeta: "trans e1 e1' \<Longrightarrow> trans e2 e2' \<Longrightarrow> trans (App (Abs x e1) e2) (tvsubst (Var(x:=e2')) e1')"

thm trans_def

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
  apply (auto simp: term.rrename_id0s map_prod.comp term.rrename_comp0s inf_A)  
  by auto 

definition G :: "(T \<Rightarrow> bool) \<Rightarrow> V \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>R v t.  
         (v = [] \<and> fst t = snd t)
         \<or>
         (\<exists>e1 e1' e2 e2'. v = [] \<and> fst t = App e1 e2 \<and> snd t = App e1' e2' \<and> 
                           R (e1,e1') \<and> R (e2,e2')) 
         \<or>
         (\<exists>x e e'. v = [x] \<and> fst t = Abs x e \<and> snd t = Abs x e' \<and> R (e,e'))
         \<or>
         (\<exists>x e1 e1' e2 e2'. v = [x] \<and> fst t = App (Abs x e1) e2 \<and> snd t = tvsubst (Var(x := e2')) e1' \<and> 
            R (e1,e1') \<and> R (e2,e2'))"


(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma GG_mono: "R \<le> R' \<Longrightarrow> G R v t \<Longrightarrow> G R' v t"
unfolding G_def by fastforce

(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma GG_equiv: "ssbij \<sigma> \<Longrightarrow> G R v t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Vmap \<sigma> v) (Tmap \<sigma> t)"
unfolding G_def apply(elim disjE)
  subgoal apply(rule disjI1)
  subgoal  
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  by simp . 
  (* *)
  subgoal apply(rule disjI2, rule disjI1)
  subgoal apply(elim exE) subgoal for e1 e1' e2 e2'
  apply(rule exI[of _ "rrename_term \<sigma> e1"]) apply(rule exI[of _ "rrename_term \<sigma> e1'"]) 
  apply(rule exI[of _ "rrename_term \<sigma> e2"]) apply(rule exI[of _ "rrename_term \<sigma> e2'"])
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
  apply (simp add: term.rrename_comps) apply(subst rrename_tvsubst_comp) by auto
 . . . 
  

lemma fresh: "\<exists>xx. xx \<notin> Tfvars t"  
by (metis Abs_avoid Tfvars.elims term.card_of_FFVars_bounds term.set(2))

(* NB: The entities affected by variables are passed as witnesses to exI 
with x and (the fresh) xx swapped, whereas the non-affected ones are passed 
as they are. 
*)
lemma GG_fresh: 
"(\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> G R v t \<Longrightarrow> 
 \<exists>w. Vfvars w  \<inter> Tfvars t = {} \<and> G R w t"
using fresh[of t] unfolding G_def Tmap_def Vmap_def apply safe
  subgoal for xx
  apply(rule exI[of _ "[]"])  
  apply(rule conjI)
    subgoal unfolding ssbij_def small_def Vmap_def by auto 
    subgoal apply(rule disjI1) by simp .
  (* *)
  subgoal for xx e1 e1' e2 e2'
  apply(rule exI[of _ "[]"])  
  apply(rule conjI)
    subgoal unfolding ssbij_def small_def Vmap_def by auto 
    subgoal apply(rule disjI2, rule disjI1) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e1'"])
    apply(rule exI[of _ "e2"]) 
    apply(rule exI[of _ "e2'"])
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
      subgoal apply(subst Abs_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal apply(subst Abs_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal by (metis supp_swap_bound Prelim.bij_swap ssbij_def) . . 
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
      subgoal apply(subst Abs_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal apply(subst tvsubst_Var_rrename_term) 
      apply (auto split: if_splits)   
      by blast
      subgoal by (metis supp_swap_bound Prelim.bij_swap ssbij_def) . . . 
  (* *)


(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation Induct where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars
and Vmap = Vmap and Vfvars = Vfvars and G = G
apply standard 
  using GG_mono GG_equiv GG_fresh by auto

(* *)

lemma trans_I: "trans t1 t2 = I (t1,t2)" 
  unfolding trans_def I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
  unfolding fun_eq_iff G_def apply safe 
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal apply simp by metis
    subgoal by (metis fst_conv snd_conv)
    subgoal by (metis fst_conv snd_conv)
    subgoal by (metis fst_conv snd_conv)
    subgoal by (metis fst_conv snd_conv) .

(* FROM ABSTRACT BACK TO CONCRETE: *)
thm trans.induct[no_vars]

corollary BE_induct_trans: "(\<And>p. small (Pfvars p)) \<Longrightarrow> 
trans t1 t2 \<Longrightarrow> 
(\<And>e p. R p e e) \<Longrightarrow>
(\<And>e1 e1' e2 e2' p. trans e1 e1' \<Longrightarrow> 
  (\<forall>p'. R p' e1 e1') \<Longrightarrow> (\<forall>p'. R p' e2 e2') \<Longrightarrow> R p (App e1 e2) (App e1' e2')) \<Longrightarrow> 
(\<And>e e' x p. x \<notin> Pfvars p \<Longrightarrow> trans e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> R p (Abs x e) (Abs x e')) \<Longrightarrow> 
(\<And>x e e' e2 e2' p. x \<notin> Pfvars p \<Longrightarrow> trans e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> trans e2 e2' \<Longrightarrow> (\<forall>p'. R p' e2 e2') \<Longrightarrow> 
   x \<notin> FFVars_term e2 \<Longrightarrow> (x \<in> FFVars_term e' \<Longrightarrow> x \<notin> FFVars_term e2') \<Longrightarrow> 
   R p (App (Abs x e) e2) (tvsubst (VVr(x := e2')) e')) \<Longrightarrow>
 R p t1 t2"
unfolding trans_I
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by auto
  subgoal apply(erule BE_induct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
  unfolding G_def apply (auto split: if_splits)
    by (metis (no_types, lifting)) .


end