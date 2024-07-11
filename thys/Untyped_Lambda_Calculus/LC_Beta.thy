(* Here we instantiate the general enhanced rule induction to beta reduction
for the (untyped) lambda-calculus *)
theory LC_Beta 
imports LC "Binders.Generic_Barendregt_Enhanced_Rule_Induction" "Prelim.Curry_LFP" "Prelim.More_Stream" LC_Head_Reduction
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)
(*
binder_inductive sillystep :: "trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> bool" where
  "sillystep (Lam x a) b c d e" binds "{x}"
where
  map: "\<lambda>f ((a,b), c, d, e). ((rrename f a,rrename f b), rrename f c, rrename f d, rrename f e)"
  set: "\<lambda>((a,b), c, d, e). FFVars a \<union> FFVars b \<union> FFVars c \<union> FFVars d \<union> FFVars e"
         apply (auto simp: o_def split_beta term.rrename_comps fun_eq_iff ssbij_def
           small_def term.card_of_FFVars_bounds term.Un_bound)
  subgoal premises prems for R b c d e x a
  proof -
    obtain y where "y \<notin> FFVars a \<union> FFVars b \<union> FFVars c \<union> FFVars d \<union> FFVars e \<union> {x}"
      sorry
    then show ?thesis
      by (intro exI[of _ "{y}"])
        (auto simp: singl_bound Lam_refresh[of y a x])
  qed
  done

binder_inductive step :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta: "step (App (Lam x e1) e2) (tvsubst (Var(x:=e2)) e1)" binds "{x}"
| AppL: "step e1 e1' \<Longrightarrow> step (App e1 e2) (App e1' e2)"
| AppR: "step e2 e2' \<Longrightarrow> step (App e1 e2) (App e1 e2')"
| Xi: "step e e' \<Longrightarrow> step (Lam x e) (Lam x e')" binds "{x}"
where
  map: "\<lambda>f (a,b). ((rrename f a,rrename f b))"
  set: "\<lambda>(a,b). FFVars a \<union> FFVars b"
         apply (auto simp: o_def split_beta term.rrename_comps fun_eq_iff ssbij_def
           small_def term.card_of_FFVars_bounds term.Un_bound) [6]
  subgoal for \<sigma> R B t
    sorry
  subgoal for R B t
    sorry
  done

binder_inductive stepD :: "nat \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta: "stepD 0 (App (Lam x e1) e2) (tvsubst (Var(x:=e2)) e1)" binds "{x}"
| AppL: "stepD d e1 e1' \<Longrightarrow> stepD (Suc d) (App e1 e2) (App e1' e2)"
| AppR: "stepD d e2 e2' \<Longrightarrow> stepD (Suc d) (App e1 e2) (App e1 e2')"
| Xi: "stepD d e e' \<Longrightarrow> stepD d (Lam x e) (Lam x e')" binds "{x}"
where
  map: "\<lambda>f (n,a,b). ((n,rrename f a,rrename f b))"
  set: "\<lambda>(_,a,b). FFVars a \<union> FFVars b"
         apply (auto simp: o_def split_beta term.rrename_comps fun_eq_iff ssbij_def
           small_def term.card_of_FFVars_bounds term.Un_bound) [6]
  subgoal for \<sigma> R B t
    sorry
  subgoal for R B t
    sorry
  done

lemma **: "Induct (\<lambda>f (b, e, e'). (b, rrename f e, rrename f e'))
 (\<lambda>(_, e, e'). FFVars e \<union> FFVars e')
 (\<lambda>B p (b, x1, x2).
     (\<exists>x e1 e2.
         B = {x} \<and>
         \<not> b \<and> x1 = App (Lam x e1) e2 \<and> x2 = tvsubst (Var(x := e2)) e1) \<or>
     (\<exists>e1 e1' e2.
         B = {} \<and> \<not> b \<and> x1 = App e1 e2 \<and> x2 = App e1' e2 \<and> p (False, e1, e1')) \<or>
     (\<exists>e2 e2' e1.
         B = {} \<and> \<not> b \<and> x1 = App e1 e2 \<and> x2 = App e1 e2' \<and> p (False, e2, e2')) \<or>
     (\<exists>e e' x. B = {x} \<and> \<not> b \<and> x1 = Lam x e \<and> x2 = Lam x e' \<and> p (True, e, e')) \<or>
     (\<exists>e1 e1' e2.
         B = {} \<and> b \<and> x1 = App e1 e2 \<and> x2 = App e1' e2 \<and> p (False, e1, e1')) \<or>
     (\<exists>e2 e2' e1.
         B = {} \<and> b \<and> x1 = App e1 e2 \<and> x2 = App e1 e2' \<and> p (False, e2, e2')) \<or>
     (\<exists>e e' x. B = {x} \<and> b \<and> x1 = Lam x e \<and> x2 = Lam x e' \<and> p (False, e, e')))"
  sorry
binder_inductive step1 :: "trm \<Rightarrow> trm \<Rightarrow> bool" and step2 :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta1: "step1 (App (Lam x e1) e2) (tvsubst (Var(x:=e2)) e1)" binds "{x}"
| AppL1: "step1 e1 e1' \<Longrightarrow> step1 (App e1 e2) (App e1' e2)"
| AppR1: "step1 e2 e2' \<Longrightarrow> step1 (App e1 e2) (App e1 e2')"
| Xi1: "step2 e e' \<Longrightarrow> step1 (Lam x e) (Lam x e')" binds "{x}"
| AppL2: "step1 e1 e1' \<Longrightarrow> step2 (App e1 e2) (App e1' e2)"
| AppR2: "step1 e2 e2' \<Longrightarrow> step2 (App e1 e2) (App e1 e2')"
| Xi2: "step1 e e' \<Longrightarrow> step2 (Lam x e) (Lam x e')" binds "{x}"
where
  map: "\<lambda>f (b,e,e'). ((b,rrename f e,rrename f e'))"
  set: "\<lambda>(_,e,e'). FFVars e \<union> FFVars e'"
  apply (auto simp: o_def split_beta term.rrename_comps fun_eq_iff ssbij_def
           small_def term.card_of_FFVars_bounds term.Un_bound) [5]
  subgoal for R R' B t
    by (auto)
  subgoal for \<sigma> R B t
    sorry
  subgoal for R B t
    sorry
  done

lemma lr: "(step1 x1 x2 \<longrightarrow>
Induct1.I
(\<lambda>B p (b, x1, x2).
     (\<exists>x e1 e2.
         B = {x} \<and>
         \<not> b \<and> x1 = App (Lam x e1) e2 \<and> x2 = tvsubst (Var(x := e2)) e1) \<or>
     (\<exists>e1 e1' e2.
         B = {} \<and> \<not> b \<and> x1 = App e1 e2 \<and> x2 = App e1' e2 \<and> p (False, e1, e1')) \<or>
     (\<exists>e2 e2' e1.
         B = {} \<and> \<not> b \<and> x1 = App e1 e2 \<and> x2 = App e1 e2' \<and> p (False, e2, e2')) \<or>
     (\<exists>e e' x. B = {x} \<and> \<not> b \<and> x1 = Lam x e \<and> x2 = Lam x e' \<and> p (True, e, e')) \<or>
     (\<exists>e1 e1' e2.
         B = {} \<and> b \<and> x1 = App e1 e2 \<and> x2 = App e1' e2 \<and> p (False, e1, e1')) \<or>
     (\<exists>e2 e2' e1.
         B = {} \<and> b \<and> x1 = App e1 e2 \<and> x2 = App e1 e2' \<and> p (False, e2, e2')) \<or>
     (\<exists>e e' x. B = {x} \<and> b \<and> x1 = Lam x e \<and> x2 = Lam x e' \<and> p (False, e, e')))
 (False, x1, x2)) \<and>
 (step2 x1 x2 \<longrightarrow>
Induct1.I
(\<lambda>B p (b, x1, x2).
     (\<exists>x e1 e2.
         B = {x} \<and>
         \<not> b \<and> x1 = App (Lam x e1) e2 \<and> x2 = tvsubst (Var(x := e2)) e1) \<or>
     (\<exists>e1 e1' e2.
         B = {} \<and> \<not> b \<and> x1 = App e1 e2 \<and> x2 = App e1' e2 \<and> p (False, e1, e1')) \<or>
     (\<exists>e2 e2' e1.
         B = {} \<and> \<not> b \<and> x1 = App e1 e2 \<and> x2 = App e1 e2' \<and> p (False, e2, e2')) \<or>
     (\<exists>e e' x. B = {x} \<and> \<not> b \<and> x1 = Lam x e \<and> x2 = Lam x e' \<and> p (True, e, e')) \<or>
     (\<exists>e1 e1' e2.
         B = {} \<and> b \<and> x1 = App e1 e2 \<and> x2 = App e1' e2 \<and> p (False, e1, e1')) \<or>
     (\<exists>e2 e2' e1.
         B = {} \<and> b \<and> x1 = App e1 e2 \<and> x2 = App e1 e2' \<and> p (False, e2, e2')) \<or>
     (\<exists>e e' x. B = {x} \<and> b \<and> x1 = Lam x e \<and> x2 = Lam x e' \<and> p (False, e, e')))
 (True, x1, x2))"
  apply (rule step1_step2.induct)
        apply (rule Induct1.I.intros[OF Induct.axioms(1)[OF **], rotated])
         apply (unfold prod.case) [1]
         apply (rule disjI1)
         apply (rule exI conjI refl notI TrueI | assumption)+
        apply simp
       apply (rule Induct1.I.intros[OF Induct.axioms(1)[OF **], rotated])
        apply (unfold prod.case) [1]
        apply (rule disjI2, rule disjI1)
        apply (rule exI conjI refl notI TrueI | assumption)+
       apply simp
      apply (rule Induct1.I.intros[OF Induct.axioms(1)[OF **], rotated])
       apply (unfold prod.case) [1]
       apply (rule disjI2, rule disjI2, rule disjI1)
       apply (rule exI conjI refl notI TrueI | assumption)+
      apply simp
     apply (rule Induct1.I.intros[OF Induct.axioms(1)[OF **], rotated])
      apply (unfold prod.case) [1]
      apply (rule disjI2, rule disjI2, rule disjI2, rule disjI1)
      apply (rule exI conjI refl notI TrueI | assumption)+
     apply simp
    apply (rule Induct1.I.intros[OF Induct.axioms(1)[OF **], rotated])
     apply (unfold prod.case) [1]
     apply (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1)
     apply (rule exI conjI refl notI TrueI | assumption)+
    apply simp
   apply (rule Induct1.I.intros[OF Induct.axioms(1)[OF **], rotated])
    apply (unfold prod.case) [1]
    apply (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1)
    apply (rule exI conjI refl notI TrueI | assumption)+
   apply simp
  apply (rule Induct1.I.intros[OF Induct.axioms(1)[OF **], rotated])
   apply (unfold prod.case) [1]
   apply (rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2)
   apply (rule exI conjI refl notI TrueI | assumption)+
  apply simp
  done

lemma rl: "Induct1.I
(\<lambda>B p (b, x1, x2).
     (\<exists>x e1 e2.
         B = {x} \<and>
         \<not> b \<and> x1 = App (Lam x e1) e2 \<and> x2 = tvsubst (Var(x := e2)) e1) \<or>
     (\<exists>e1 e1' e2.
         B = {} \<and> \<not> b \<and> x1 = App e1 e2 \<and> x2 = App e1' e2 \<and> p (False, e1, e1')) \<or>
     (\<exists>e2 e2' e1.
         B = {} \<and> \<not> b \<and> x1 = App e1 e2 \<and> x2 = App e1 e2' \<and> p (False, e2, e2')) \<or>
     (\<exists>e e' x. B = {x} \<and> \<not> b \<and> x1 = Lam x e \<and> x2 = Lam x e' \<and> p (True, e, e')) \<or>
     (\<exists>e1 e1' e2.
         B = {} \<and> b \<and> x1 = App e1 e2 \<and> x2 = App e1' e2 \<and> p (False, e1, e1')) \<or>
     (\<exists>e2 e2' e1.
         B = {} \<and> b \<and> x1 = App e1 e2 \<and> x2 = App e1 e2' \<and> p (False, e2, e2')) \<or>
     (\<exists>e e' x. B = {x} \<and> b \<and> x1 = Lam x e \<and> x2 = Lam x e' \<and> p (False, e, e'))) t
 \<Longrightarrow>
 (\<forall>x1 x2. t = (False, x1, x2) \<longrightarrow> step1 x1 x2) \<and>
 (\<forall>x1 x2. t = (True, x1, x2) \<longrightarrow> step2 x1 x2)"
  apply (erule Induct1.I.induct[OF Induct.axioms(1)[OF **]])
  apply (elim conjE case_prodE disjE exE; hypsubst_thin)
        apply (unfold prod.inject)
        apply (simp only: step1_step2.intros(1) simp_thms all_simps imp_conjL)
       apply (simp only: step1_step2.intros(2) simp_thms all_simps imp_conjL)
      apply (simp only: step1_step2.intros(3) simp_thms all_simps imp_conjL)
     apply (simp only: step1_step2.intros(4) simp_thms all_simps imp_conjL)
    apply (simp only: step1_step2.intros(5) simp_thms all_simps imp_conjL)
   apply (simp only: step1_step2.intros(6) simp_thms all_simps imp_conjL)
  apply (simp only: step1_step2.intros(7) simp_thms all_simps imp_conjL)
  done

lemma
"(step1 x1 x2 =
Induct1.I
(\<lambda>B p (b, x1, x2).
     (\<exists>x e1 e2.
         B = {x} \<and>
         \<not> b \<and> x1 = App (Lam x e1) e2 \<and> x2 = tvsubst (Var(x := e2)) e1) \<or>
     (\<exists>e1 e1' e2.
         B = {} \<and> \<not> b \<and> x1 = App e1 e2 \<and> x2 = App e1' e2 \<and> p (False, e1, e1')) \<or>
     (\<exists>e2 e2' e1.
         B = {} \<and> \<not> b \<and> x1 = App e1 e2 \<and> x2 = App e1 e2' \<and> p (False, e2, e2')) \<or>
     (\<exists>e e' x. B = {x} \<and> \<not> b \<and> x1 = Lam x e \<and> x2 = Lam x e' \<and> p (True, e, e')) \<or>
     (\<exists>e1 e1' e2.
         B = {} \<and> b \<and> x1 = App e1 e2 \<and> x2 = App e1' e2 \<and> p (False, e1, e1')) \<or>
     (\<exists>e2 e2' e1.
         B = {} \<and> b \<and> x1 = App e1 e2 \<and> x2 = App e1 e2' \<and> p (False, e2, e2')) \<or>
     (\<exists>e e' x. B = {x} \<and> b \<and> x1 = Lam x e \<and> x2 = Lam x e' \<and> p (False, e, e')))
 (False, x1, x2))"
"(step2 x1 x2 =
Induct1.I
(\<lambda>B p (b, x1, x2).
     (\<exists>x e1 e2.
         B = {x} \<and>
         \<not> b \<and> x1 = App (Lam x e1) e2 \<and> x2 = tvsubst (Var(x := e2)) e1) \<or>
     (\<exists>e1 e1' e2.
         B = {} \<and> \<not> b \<and> x1 = App e1 e2 \<and> x2 = App e1' e2 \<and> p (False, e1, e1')) \<or>
     (\<exists>e2 e2' e1.
         B = {} \<and> \<not> b \<and> x1 = App e1 e2 \<and> x2 = App e1 e2' \<and> p (False, e2, e2')) \<or>
     (\<exists>e e' x. B = {x} \<and> \<not> b \<and> x1 = Lam x e \<and> x2 = Lam x e' \<and> p (True, e, e')) \<or>
     (\<exists>e1 e1' e2.
         B = {} \<and> b \<and> x1 = App e1 e2 \<and> x2 = App e1' e2 \<and> p (False, e1, e1')) \<or>
     (\<exists>e2 e2' e1.
         B = {} \<and> b \<and> x1 = App e1 e2 \<and> x2 = App e1 e2' \<and> p (False, e2, e2')) \<or>
     (\<exists>e e' x. B = {x} \<and> b \<and> x1 = Lam x e \<and> x2 = Lam x e' \<and> p (False, e, e')))
 (True, x1, x2))"
  using lr rl by blast+

binder_inductive a and b where
  "b (x :: var) \<Longrightarrow> a (x :: var) (z :: trm)" binds "{x :: var}"
| "a y z \<Longrightarrow> b x"
where map: "\<lambda>_. id" set: "\<lambda>_. {}"
  sorry
thm a_def
thm a_b_def
*)

inductive step :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta: "step (App (Lam x e1) e2) (tvsubst (Var(x:=e2)) e1)"
| AppL: "step e1 e1' \<Longrightarrow> step (App e1 e2) (App e1' e2)"
| AppR: "step e2 e2' \<Longrightarrow> step (App e1 e2) (App e1 e2')"
| Xi: "step e e' \<Longrightarrow> step (Lam x e) (Lam x e')"

(* INSTANTIATING THE Components LOCALE: *)

type_synonym T = "trm \<times> trm"

definition Tmap :: "(var \<Rightarrow> var) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> map_prod (rrename_term f) (rrename_term f)"

fun Tfvars :: "T \<Rightarrow> var set" where 
"Tfvars (e1,e2) = FFVars_term e1 \<union> FFVars_term e2"


interpretation Components where 
Tmap = Tmap and Tfvars = Tfvars
apply standard unfolding ssbij_def Tmap_def  
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
lemma G_equiv: "ssbij \<sigma> \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G  (image \<sigma> B) (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Tmap \<sigma> t)"
  unfolding G_def
  by (elim disj_forward exE; cases t)
    (auto simp: Tmap_def ssbij_def
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
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  apply (simp add: term.rrename_comps) apply(subst rrename_tvsubst_comp) by auto . .
  (* *)
  subgoal apply(rule disjI4_2)
  subgoal apply(elim exE) subgoal for e1 e1' e2 
  apply(rule exI[of _ "rrename_term \<sigma> e1"]) apply(rule exI[of _ "rrename_term \<sigma> e1'"]) 
  apply(rule exI[of _ "rrename_term \<sigma> e2"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  by (simp add: term.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI4_3)
  subgoal apply(elim exE) subgoal for e1 e2 e2' 
  apply(rule exI[of _ "rrename_term \<sigma> e1"]) 
  apply(rule exI[of _ "rrename_term \<sigma> e2"]) apply(rule exI[of _ "rrename_term \<sigma> e2'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def 
  by (simp add: term.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI4_4)
  subgoal apply(elim exE) subgoal for x e e'
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename_term \<sigma> e"]) apply(rule exI[of _ "rrename_term \<sigma> e'"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def  
  by (simp add: term.rrename_comps) . . .
*)


lemma fresh: "\<exists>xx. xx \<notin> Tfvars t"  
by (metis Lam_avoid Tfvars.elims term.card_of_FFVars_bounds term.set(2))

(* NB: The entities affected by variables are passed as witnesses to exI 
with x and (the fresh) xx swapped, whereas the non-affected ones are passed 
as they are. 
*)

lemma G_refresh: 
"(\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> 
 \<exists>C. small C \<and> C \<inter> Tfvars t = {} \<and> G C R t"
  using fresh[of t] unfolding G_def Tmap_def
(**)ssbij_def conj_assoc[symmetric]
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
    subgoal unfolding ssbij_def small_def by auto 
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
    subgoal unfolding ssbij_def small_def by auto 
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
    subgoal unfolding ssbij_def small_def by auto 
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
    subgoal unfolding ssbij_def small_def by auto 
    subgoal apply(rule disjI4_4) 
    apply(rule exI[of _ "xx"]) 
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e"])
    apply(rule exI[of _ "rrename_term (id(x:=xx,xx:=x)) e'"])
    apply(cases t)  apply simp apply(intro conjI)
      subgoal apply(subst Lam_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal apply(subst Lam_rrename[of "id(x:=xx,xx:=x)"]) by auto
      subgoal by (metis supp_swap_bound Prelim.bij_swap ssbij_def) . . .
  (* *)
*)


(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation Step: Induct where
Tmap = Tmap and Tfvars = Tfvars and G = G
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

(* FROM ABSTRACT BACK TO CONCRETE: *)
thm step.induct[no_vars]

corollary strong_induct_step[consumes 2, case_names Beta AppL AppR Xi]: 
assumes par: "\<And>p. small (Pfvars p)"
and st: "step t1 t2"  
and Beta: "\<And>x e1 e2 p. 
  x \<notin> Pfvars p \<Longrightarrow> x \<notin> FFVars_term e2 \<Longrightarrow> 
  R p (App (Lam x e1) e2) (tvsubst (VVr(x := e2)) e1)"
and AppL: "\<And>e1 e1' e2 p. 
  step e1 e1' \<Longrightarrow> (\<forall>p'. R p' e1 e1') \<Longrightarrow> 
  R p (App e1 e2) (App e1' e2)"
and AppR: "\<And>e1 e2 e2' p. 
  step e2 e2' \<Longrightarrow> (\<forall>p'. R p' e2 e2') \<Longrightarrow> 
  R p (App e1 e2) (App e1 e2')"
and Xi: "\<And>e e' x p. 
  x \<notin> Pfvars p \<Longrightarrow> 
  step e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> 
  R p (Lam x e) (Lam x e')" 
shows "R p t1 t2"
unfolding step_I
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by simp
  subgoal using par st apply(elim Step.strong_induct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
    subgoal unfolding step_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding step_I[symmetric] apply(elim disjE exE)
      subgoal for x e1 e2  using Beta[of x p e2 e1] by auto
      subgoal using AppL by auto  
      subgoal using AppR by auto  
      subgoal using Xi by auto . . .

corollary strong_induct_step'[consumes 1, case_names Bound Beta AppL AppR Xi]: 
assumes st: "step t1 t2"
and par: "\<And>p. |Pfvars p| <o |UNIV::var set|"
and Beta: "\<And>x e1 e2 p. 
  x \<notin> Pfvars p \<Longrightarrow> x \<notin> FFVars_term e2 \<Longrightarrow> 
  R (App (Lam x e1) e2) (tvsubst (VVr(x := e2)) e1) p"
and AppL: "\<And>e1 e1' e2 p. 
  step e1 e1' \<Longrightarrow> (\<forall>p'. R e1 e1' p') \<Longrightarrow> 
  R (App e1 e2) (App e1' e2) p"
and AppR: "\<And>e1 e2 e2' p. 
  step e2 e2' \<Longrightarrow> (\<forall>p'. R e2 e2' p') \<Longrightarrow> 
  R (App e1 e2) (App e1 e2') p"
and Xi: "\<And>e e' x p. 
  x \<notin> Pfvars p \<Longrightarrow> 
  step e e' \<Longrightarrow> (\<forall>p'. R e e' p') \<Longrightarrow> 
  R (Lam x e) (Lam x e') p" 
shows "\<forall>p. R t1 t2 p"
using strong_induct_step[of Pfvars t1 t2 "\<lambda>p t1 t2. R t1 t2 p"] assms unfolding small_def by auto


(* Also inferring equivariance from the general infrastructure: *)
corollary rrename_step:
assumes f: "bij f" "|supp f| <o |UNIV::var set|" 
and r: "step e e'" 
shows "step (rrename f e) (rrename f e')"
using assms unfolding step_I using Step.I_equiv[of "(e,e')" f]
unfolding Tmap_def ssbij_def by auto


(* Other properties: *)

(* *)
lemma red_step: "red e ee \<Longrightarrow> step e ee"
by (metis red_def step.Beta)

lemma red_step2: "stream_all2 red es ees \<Longrightarrow> stream_all2 step es ees"
  unfolding stream_all2_iff_snth using red_step by auto


end