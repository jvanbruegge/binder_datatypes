theory PrettyPrinting
imports "Untyped_Lambda_Calculus.LC" (*BSmall*) "Prelim.Curry_LFP" (* ILC2 *)
"Binders.Generic_Strong_Rule_Induction"
begin

(* *)
(* raw terms: *)
datatype rtrm = VAR var | APP rtrm rtrm | LAM var rtrm

fun Vrs where 
"Vrs (VAR x) = {x}"
|
"Vrs (APP T S) = Vrs T \<union> Vrs S"
|
"Vrs (LAM x T) = {x} \<union> Vrs T"

lemma finite_Vrs[intro]: "finite (Vrs T)"
by (induct T, auto)

fun rrrename where 
"rrrename f (VAR x) = VAR (f x)"
|
"rrrename f (APP T S) = APP (rrrename f T) (rrrename f S)"
|
"rrrename f (LAM x T) = LAM (f x) (rrrename f T)"

lemma rrrename_id[simp]: "rrrename id = id"
apply(rule ext) subgoal for T by (induct T, auto) .

lemma rrrename_o[simp]: "rrrename (g o f) = rrrename g o rrrename f"
apply(rule ext) subgoal for T by (induct T, auto) .

lemma rrrename_Vrs[simp]: "Vrs (rrrename f T) = f ` (Vrs T)"
by (induct T, auto)

lemma rrrename_cong: 
"\<forall>x\<in>Vrs T. f x = x \<Longrightarrow> rrrename f T = T"
by (induct T, auto)


(* ASCII-only variables: *)
consts AVr :: "var set"

axiomatization where infinite_AVr: "infinite AVr"

term usub

inductive ppr :: "trm \<Rightarrow> rtrm \<Rightarrow> bool" where
  Vr_VAR: "x \<in> AVr \<Longrightarrow> ppr (Vr x) (VAR x)"
| Ap_APP: "ppr t T \<Longrightarrow> ppr s S \<Longrightarrow> ppr (Ap t s) (APP T S)"
| Lm_LAM: "y \<in> AVr \<Longrightarrow> y \<notin> {x} \<union> FFVars t \<Longrightarrow>  
    ppr (usub t y x) T \<Longrightarrow> ppr (Lm x t) (LAM y T)"


(* INSTANTIATING THE ABSTRACT SETTING: *)

(* PREPARING THE INSTANTIATION: *)

type_synonym B = "(var \<times> var) set"

fun Bperm :: "(var \<Rightarrow> var) \<Rightarrow> B \<Rightarrow> B" where 
"Bperm f = image (map_prod f f)"

fun Bsupp :: "B \<Rightarrow> var set" where 
"Bsupp XY = image fst XY \<comment> \<open>\<union> image snd XY \<close>"

fun bnd :: "B \<Rightarrow> bool" where 
"bnd XY \<longleftrightarrow> finite XY \<and> image snd XY \<subseteq> AVr"


fun bsmall :: "var set \<Rightarrow> bool"
where 
"bsmall XY = finite XY" 

(*
lemma ppr_touchedSuperT: 
"ppr e1 e2 \<Longrightarrow> touchedSuperT e1 = touchedSuperT e2 \<and> finite (touchedSuperT e1) \<and> finite (touchedSuperT e2) "
proof(induct rule: ppr.induct)
  case (iVr xs x x')
  then show ?case by auto 
next
  case (iLm xs e e')
  then show ?case by auto
next
  case (iAp e1 e1' es2 es2')
  obtain e2 e2' where e2: "e2 \<in> sset es2" and e2': "e2' \<in> sset es2'" 
  using shd_sset by blast+
  hence 0: "touchedSuperT ` sset es2 = {touchedSuperT e2}" "touchedSuperT ` sset es2' = {touchedSuperT e2}"
  using iAp(3) by auto
  have "\<Union> (touchedSuperT ` sset es2) = \<Union> (touchedSuperT ` sset es2') \<and>
       finite (\<Union> (touchedSuperT ` sset es2)) \<and> finite (\<Union> (touchedSuperT ` sset es2'))" 
  unfolding 0 using iAp(3) e2 e2' by auto    
  thus ?case using iAp by simp
qed

lemmas ppr_touchedSuperT_eq = ppr_touchedSuperT[THEN conjunct1]
lemmas ppr_finite_touchedSuperT = ppr_touchedSuperT[THEN conjunct2]
*)

(* INSTANTIATING THE CComponents LOCALE: *)

type_synonym T = "trm \<times> rtrm"

definition Tperm :: "(var \<Rightarrow> var) \<Rightarrow> T \<Rightarrow> T" where 
"Tperm f \<equiv> map_prod (rrename f) (rrrename f)"

fun Tsupp :: "T \<Rightarrow> var set" where 
"Tsupp (e1,e2) = FFVars e1 \<union> Vrs e2"



interpretation CComponents where
Tperm = Tperm and Tsupp = Tsupp 
and Bperm = Bperm and Bsupp = Bsupp and bnd = bnd and bsmall = bsmall
apply standard unfolding isPerm_def Tperm_def  apply auto
  subgoal apply(rule ext) by (auto simp add: term.rrename_comps image_def)
  subgoal by (simp add: Un_bound finite_Vrs infinite_var small_def term.set_bd_UNIV)
  subgoal by (simp add: rrrename_cong)
  subgoal apply(rule ext) using image_iff by fastforce
  subgoal using finite_iff_le_card_var small_def by blast 
  subgoal unfolding image_def by force 
  (* subgoal unfolding image_def sledgehammer by force . *) sorry
  subgoal unfolding image_def by (metis (mono_tags, lifting) Un_iff fst_conv mem_Collect_eq snd_conv) 
  subgoal  
    by (smt (verit, del_insts) Un_iff fst_conv fst_map_prod imageI snd_conv snd_map_prod surj_pair) .



lemma presBnd_imp: "presBnd \<sigma> \<Longrightarrow> \<sigma> ` AVr \<subseteq> AVr"
unfolding presBnd_def apply auto subgoal for x apply(erule allE[of _ "{(undefined,x)}"])
apply auto
 by auto .

(*
lemma presBnd_presSuper: "presBnd = presSuper"
unfolding presBnd_def presSuper_def fun_eq_iff apply safe
  subgoal for \<sigma> xs apply(erule allE[of _ "Some xs"]) by auto 
  subgoal for \<sigma> xs apply(erule allE[of _ "Some xs"]) by auto 
  subgoal for \<sigma> xxs apply(cases xxs) by auto 
  subgoal for \<sigma> xxs apply(cases xxs) by auto .
*)

(*
inductive ppr :: "trm \<Rightarrow> rtrm \<Rightarrow> bool" where
  Vr_VAR: "x \<in> AVr \<Longrightarrow> ppr (Vr x) (VAR x)"
| Ap_APP: "ppr t T \<Longrightarrow> ppr s S  \<Longrightarrow> ppr (Ap t s) (APP T S)"
| Lm_LAM: "y \<notin> {x} \<union> FFVars t \<union> Vrs T \<Longrightarrow>  
    ppr (usub t y x) t' \<Longrightarrow> ppr (Lm x t) (LAM y T)"
*)

definition G :: "B \<Rightarrow> (T \<Rightarrow> bool) \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>B R tt.  
         (\<exists>x. B = {} \<and> fst tt = Vr x \<and> snd tt = VAR x \<and> 
              x \<in> AVr) 
         \<or>
         (\<exists>t T s S. B = {} \<and> fst tt = Ap t s \<and> snd tt = APP T S \<and> 
                    R (t,T) \<and> R (s,S))
         \<or> 
         (\<exists>y x t T. B = {(x,y)} \<and> fst tt = Lm x t \<and> snd tt = LAM y T \<and> 
                    y \<in> AVr \<and> y \<notin> {x} \<union> FFVars t \<and> R (usub t y x,T))"
 

(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma G_mmono: "R \<le> R' \<Longrightarrow> G xxs R t \<Longrightarrow> G xxs R' t"
unfolding G_def by fastforce 

(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma G_eequiv: 
"isPerm \<sigma> \<Longrightarrow> presBnd \<sigma> \<Longrightarrow> G B R tt \<Longrightarrow> 
 G  (Bperm \<sigma> B) (\<lambda>tt'. R (Tperm (inv \<sigma>) tt')) (Tperm \<sigma> tt)"
unfolding G_def apply(drule presBnd_imp) apply(elim disjE)
  subgoal apply(rule disjI3_1)
  subgoal apply(elim exE) subgoal for x
  apply(rule exI[of _ "\<sigma> x"])  
  apply(cases tt) unfolding isPerm_def small_def Tperm_def by auto . . 
  (* *)
  subgoal apply(rule disjI3_2)
  subgoal apply(elim exE) subgoal for t T s S
  apply(rule exI[of _ "rrename \<sigma> t"]) 
  apply(rule exI[of _ "rrrename \<sigma> T"])
  apply(rule exI[of _ "rrename \<sigma> s"]) 
  apply(rule exI[of _ "rrrename \<sigma> S"])  
  apply(cases tt) unfolding isPerm_def small_def Tperm_def 
  by simp (metis comp_apply id_apply inv_o_simp1 rrrename_id rrrename_o 
    term.rrename_bijs term.rrename_inv_simps) . . 
  (* *)
  subgoal apply(rule disjI3_3)
  subgoal apply(elim exE) subgoal for y x t T
  apply(rule exI[of _ "\<sigma> y"]) apply(rule exI[of _ "\<sigma> x"]) 
  apply(rule exI[of _ "rrename \<sigma> t"]) apply(rule exI[of _ "rrrename \<sigma> T"]) 
  apply(cases tt) unfolding isPerm_def small_def Tperm_def apply simp 
    by (metis comp_apply id_apply imageI inv_o_simp1 not_imageI rrrename_id rrrename_o subsetD term.rrename_bijs term.rrename_inv_simps)
   . . .



(* *)

lemma G_bnd: "G B R tt \<Longrightarrow> bnd B"
unfolding G_def by auto

lemma eextend_to_presBnd: 
assumes "bnd B" "small A" "bsmall A" "A' \<subseteq> A" "Bsupp B \<inter> A' = {}"
shows "\<exists>\<rho>. isPerm \<rho> \<and> presBnd \<rho> \<and> \<rho> ` Bsupp B \<inter> A = {} \<and> id_on A' \<rho>" 
sorry
(* proof(cases xxs)
  case None
  thus ?thesis apply(intro exI[of _ id]) unfolding isPerm_def by auto
next
  case (Some xs)
  hence 0: "super xs" "|A| <o |UNIV::ivar set|" "finite (touchedSuper A)" "A' \<subseteq> A"
  "dsset xs \<inter> A' = {}"
  using assms by (auto split: option.splits simp: small_def bsmall_def) 
  show ?thesis using extend_super[OF 0] apply safe
  subgoal for \<rho> apply(rule exI[of _ \<rho>]) 
  using Some by (auto split: option.splits simp: presBnd_presSuper isPerm_def) .
qed 
*)


interpretation Ppr : IInduct1 
where Tperm = Tperm and Tsupp = Tsupp and Bperm = Bperm and Bsupp = Bsupp 
and bnd = bnd and bsmall = bsmall and GG = G
apply standard
using G_mmono G_eequiv G_bnd eextend_to_presBnd by auto


(* *)

lemma ppr_I: "ppr t1 t2 = Ppr.II (t1,t2)" 
unfolding ppr_def Ppr.II_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R tt1 tt2 apply(rule iffI)
  subgoal apply(elim disjE exE conjE)
    \<^cancel>\<open>Vr_VAR: \<close>
    subgoal for x apply(rule exI[of _ "{}"]) apply(rule disjI3_1) by auto
    \<^cancel>\<open>Ap_APP: \<close>
    subgoal for t T s S apply(rule exI[of _ "{}"]) apply(rule disjI3_2) by auto 
    \<^cancel>\<open>Lm_LAM: \<close>
    subgoal for y x t T apply(rule exI[of _ "{(x,y)}"]) apply(rule disjI3_3) by auto . 
    (* *)
  subgoal apply(elim disjE exE conjE)
    \<^cancel>\<open>iVr: \<close>
    subgoal apply(rule disjI3_1) by auto
    \<^cancel>\<open>iLm: \<close>
    subgoal apply(rule disjI3_2) by auto
    \<^cancel>\<open>iAp: \<close>
    subgoal apply(rule disjI3_3) by auto . . .
  

lemma III_bsmall: "Ppr.II t \<Longrightarrow> bsmall (Tsupp t)"
apply(cases t)
  subgoal for e1 e2  
    apply auto by (simp add: finite_iff_le_card_var term.card_of_FFVars_bounds) .

(*
lemma Tvars_dsset: "dsset xs \<inter> (Tsupp t - dsset xs) = {}" 
  "|Tsupp t - dsset xs| <o |UNIV::ivar set|"
  "Ppr.II t \<Longrightarrow> finite (touchedSuper (Tsupp t - dsset ys))"
subgoal using Diff_disjoint .
subgoal using small_def card_of_minus_bound ssmall_Tsupp by blast
subgoal apply(subgoal_tac "bsmall (Tsupp t)")
  subgoal unfolding bsmall_def 
    by (meson Diff_subset rev_finite_subset touchedSuper_mono) 
  subgoal by (metis III_bsmall) . .
*)

lemma G_rrefresh: 
"(\<forall>tt. R tt \<longrightarrow> Ppr.II tt) \<Longrightarrow> 
 (\<forall>\<sigma> t. isPerm \<sigma> \<and> presBnd \<sigma> \<and> R tt \<longrightarrow> R (Tperm \<sigma> tt)) \<Longrightarrow> 
 G B R tt \<Longrightarrow> 
 \<exists>B'. Bsupp B' \<inter> Tsupp tt = {} \<and> G B' R tt"
apply(cases tt) subgoal for t T apply apply simp
apply(subgoal_tac "Ppr.II tt") defer


term term (*
apply (metis Ppr.GG_mmono2 Ppr.II.simps predicate1I)
subgoal premises p using p apply-
apply(frule G_bnd)
unfolding G_def Tperm_def apply safe
  subgoal for xs x x' 
  apply(rule exI[of _ None])  
  apply(intro conjI)
    subgoal by simp 
    subgoal apply(rule disjI3_1) 
    apply(rule exI[of _ xs]) 
    apply(rule exI[of _ x])
    apply(rule exI[of _ x']) 
    apply(cases t) apply simp . .
  (* *)
  subgoal for xs e e' 
  apply(frule refresh_super[OF Tvars_dsset(1,2) Tvars_dsset(3)[OF p(4)]])
  apply safe
  subgoal for f
  apply(rule exI[of _ "Some (dsmap f xs)"])  
  apply(intro conjI) 
    subgoal unfolding id_on_def presSuper_def by (cases t, auto) 
    subgoal apply(rule disjI3_2)
    apply(rule exI[of _ "dsmap f xs"]) 
    apply(rule exI[of _ "irrename f e"]) 
    apply(rule exI[of _ "irrename f e'"]) 
    apply(cases t) unfolding presSuper_def apply simp apply(intro conjI)
      subgoal apply(subst iLm_irrename[of "f"]) unfolding id_on_def by auto
      subgoal apply(subst irrename_eq_itvsubst_iVr)
        subgoal unfolding isPerm_def by auto
        subgoal unfolding isPerm_def by auto
        subgoal by (smt (verit, best) Diff_iff Un_iff iLm_irrename id_on_def 
           irrename_eq_itvsubst_iVr) . 
        subgoal unfolding id_on_def isPerm_def presBnd_def by (auto split: option.splits) . . .
  (* *)
  subgoal for e1 e1' es2 es2'
  apply(rule exI[of _ None])  
  apply(intro conjI)
    subgoal by simp 
    subgoal apply(rule disjI3_3) 
    apply(rule exI[of _ "e1"]) 
    apply(rule exI[of _ "e1'"])
    apply(rule exI[of _ "es2"]) 
    apply(rule exI[of _ "es2'"]) 
    apply(cases t) by simp . . .
 

(* FINALLY, INTERPRETING THE IInduct LOCALE: *)

interpretation Ppr : IInduct
where Tperm = Tperm and Tsupp = Tsupp and 
Bperm = Bperm and Bsupp = Bsupp and bnd = bnd and bsmall = bsmall 
and GG = G
apply standard using III_bsmall G_rrefresh by auto

(* *)


(* FROM ABSTRACT BACK TO CONCRETE: *)
thm ppr.induct[no_vars] 

corollary strong_induct_ppr[consumes 2, case_names iVr iLm iAp]: 
assumes par: "\<And>p. small (Psupp p) \<and> bsmall (Psupp p)"
and st: "ppr t1 t2"  
and iVr: "\<And>xs x x' p. 
  super xs \<Longrightarrow> {x,x'} \<subseteq> dsset xs \<Longrightarrow>
  R p (iVr x) (iVr x')"
and iLm: "\<And>e e' xs p. 
  dsset xs \<inter> Psupp p = {} \<Longrightarrow> 
  super xs \<Longrightarrow> ppr e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> 
  R p (iLm xs e) (iLm xs e')" 
and iAp: "\<And>e1 e1' es2 es2' p. 
  ppr e1 e1' \<Longrightarrow> (\<forall>p'. R p' e1 e1') \<Longrightarrow> 
  (\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<longrightarrow> ppr e e' \<and> (\<forall>p'. R p' e e')) \<Longrightarrow> 
  R p (iAp e1 es2) (iAp e1' es2')"
shows "R p t1 t2"
unfolding ppr_I
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by simp
  subgoal using par st 
  unfolding bsmall_def[symmetric] apply(elim Ppr.strong_iinduct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
    subgoal unfolding ppr_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding ppr_I[symmetric] apply(elim disjE exE)
      subgoal using iVr by auto 
      subgoal using iLm by auto  
      subgoal using iAp by auto . . .

corollary strong_induct_ppr''[consumes 1, case_names bsmall Bound iVr iLm iAp]:
  assumes  "ppr t1 t2"
and bsmall: "\<And>(p::'a). bsmall (PFVars p)"
assumes bound: "\<And>(p::'a). |PFVars p| <o |UNIV::ivar set|"
and iVr: "\<And>xs x x' p.
  super xs \<Longrightarrow> {x,x'} \<subseteq> dsset xs \<Longrightarrow>
  R (iVr x) (iVr x') p"
and iLm: "\<And>e e' xs p.
  dsset xs \<inter> PFVars p = {} \<Longrightarrow>
  super xs \<Longrightarrow> ppr e e' \<Longrightarrow> (\<forall>p'. R e e' p') \<Longrightarrow>
  R (iLm xs e) (iLm xs e') p"
and iAp: "\<And>e1 e1' es2 es2' p.
  ppr e1 e1' \<Longrightarrow> (\<forall>p'. R e1 e1' p') \<Longrightarrow>
  (\<And>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<Longrightarrow> ppr e e') \<Longrightarrow>
  (\<And>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<Longrightarrow> \<forall>p'. R e e' p') \<Longrightarrow>
  R (iAp e1 es2) (iAp e1' es2') p"
shows "\<forall>(p::'a). R t1 t2 p"
using assms strong_induct_ppr[of PFVars t1 t2 "\<lambda>p t1 t2. R t1 t2 p"] unfolding small_def by auto

(* ... and with fixed parameters: *)
corollary strong_induct_ppr'[consumes 2, case_names iVr iLm iAp]: 
assumes par: "small A \<and> bsmall A"
and st: "ppr t1 t2"  
and iVr: "\<And>xs x x'. 
  super xs \<Longrightarrow> {x,x'} \<subseteq> dsset xs \<Longrightarrow>
  R (iVr x) (iVr x')"
and iLm: "\<And>e e' xs. 
  dsset xs \<inter> A = {} \<Longrightarrow> 
  super xs \<Longrightarrow> ppr e e' \<Longrightarrow> R e e' \<Longrightarrow> 
  R (iLm xs e) (iLm xs e')" 
and iAp: "\<And>e1 e1' es2 es2'. 
  ppr e1 e1' \<Longrightarrow> R e1 e1' \<Longrightarrow> 
  (\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<longrightarrow> ppr e e' \<and> R e e') \<Longrightarrow> 
  R (iAp e1 es2) (iAp e1' es2')"
shows "R t1 t2"
apply(rule strong_induct_ppr[of "\<lambda>_::unit. A"]) using assms by auto

(* Also inferring equivariance from the general infrastructure: *)
corollary irrename_ppr:
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" "presSuper f"
and r: "ppr e e'" 
shows "ppr (irrename f e) (irrename f e')"
using assms unfolding ppr_I using Ppr.II_equiv[of "(e,e')" f]
unfolding Tperm_def isPerm_def presBnd_presSuper by auto

  

end