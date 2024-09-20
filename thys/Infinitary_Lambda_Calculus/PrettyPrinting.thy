theory PrettyPrinting
imports "Untyped_Lambda_Calculus.LC" (*BSmall*) "Prelim.Curry_LFP" (* ILC2 *)
"Binders.Generic_Barendregt_Enhanced_Rule_Induction"
begin

(* *)
(* raw terms: *)
datatype rtrm = VAR var | APP rtrm rtrm | LAM var rtrm

fun Vars where 
"Vars (VAR x) = {x}"
|
"Vars (APP T S) = Vars T \<union> Vars S"
|
"Vars (LAM x T) = {x} \<union> Vars T"

lemma finite_Vars[intro]: "finite (Vars T)"
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

lemma rrrename_Vars[simp]: "Vars (rrrename f T) = f ` (Vars T)"
by (induct T, auto)

lemma rrrename_cong: 
"\<forall>x\<in>Vars T. f x = x \<Longrightarrow> rrrename f T = T"
by (induct T, auto)


(* ASCII-only variables: *)
consts AVar :: "var set"

axiomatization where infinite_AVar: "infinite AVar"

term usub

inductive ppr :: "trm \<Rightarrow> rtrm \<Rightarrow> bool" where
  Var_VAR: "x \<in> AVar \<Longrightarrow> ppr (Var x) (VAR x)"
| App_APP: "ppr t T \<Longrightarrow> ppr s S  \<Longrightarrow> ppr (App t s) (APP T S)"
| Lam_LAM: "y \<notin> {x} \<union> FFVars t \<union> Vars T \<Longrightarrow>  
    ppr (usub t y x) t' \<Longrightarrow> ppr (Lam x t) (LAM y T)"


(* INSTANTIATING THE ABSTRACT SETTING: *)

(* PREPARING THE INSTANTIATION: *)

type_synonym B = "(var \<times> var) set"

fun Bperm :: "(var \<Rightarrow> var) \<Rightarrow> B \<Rightarrow> B" where 
"Bperm f = image (map_prod f f)"

fun Bsupp :: "B \<Rightarrow> var set" where 
"Bsupp XY = image fst XY \<union> image snd XY"

fun bnd :: "B \<Rightarrow> bool" where 
"bnd XY \<longleftrightarrow> finite XY \<and> image snd XY \<subseteq> AVar"

(*
lemma reneqv_touchedSuperT: 
"reneqv e1 e2 \<Longrightarrow> touchedSuperT e1 = touchedSuperT e2 \<and> finite (touchedSuperT e1) \<and> finite (touchedSuperT e2) "
proof(induct rule: reneqv.induct)
  case (iVar xs x x')
  then show ?case by auto 
next
  case (iLam xs e e')
  then show ?case by auto
next
  case (iApp e1 e1' es2 es2')
  obtain e2 e2' where e2: "e2 \<in> sset es2" and e2': "e2' \<in> sset es2'" 
  using shd_sset by blast+
  hence 0: "touchedSuperT ` sset es2 = {touchedSuperT e2}" "touchedSuperT ` sset es2' = {touchedSuperT e2}"
  using iApp(3) by auto
  have "\<Union> (touchedSuperT ` sset es2) = \<Union> (touchedSuperT ` sset es2') \<and>
       finite (\<Union> (touchedSuperT ` sset es2)) \<and> finite (\<Union> (touchedSuperT ` sset es2'))" 
  unfolding 0 using iApp(3) e2 e2' by auto    
  thus ?case using iApp by simp
qed

lemmas reneqv_touchedSuperT_eq = reneqv_touchedSuperT[THEN conjunct1]
lemmas reneqv_finite_touchedSuperT = reneqv_touchedSuperT[THEN conjunct2]
*)

(* INSTANTIATING THE CComponents LOCALE: *)

type_synonym T = "trm \<times> rtrm"

definition Tperm :: "(var \<Rightarrow> var) \<Rightarrow> T \<Rightarrow> T" where 
"Tperm f \<equiv> map_prod (rrename f) (rrrename f)"

fun Tsupp :: "T \<Rightarrow> var set" where 
"Tsupp (e1,e2) = FFVars e1 \<union> Vars e2"



interpretation CComponents where
Tperm = Tperm and Tsupp = Tsupp 
and Bperm = Bperm and Bsupp = Bsupp and bnd = bnd and bsmall = finite
apply standard unfolding isPerm_def Tperm_def  apply auto
  subgoal apply(rule ext) by (auto simp add: term.rrename_comps image_def)
  subgoal by (simp add: Un_bound finite_Vars infinite_var small_def term.set_bd_UNIV)
  subgoal by (simp add: rrrename_cong)
  subgoal apply(rule ext) using image_iff by fastforce
  subgoal using finite_iff_le_card_var small_def by blast 
  subgoal unfolding image_def by force
  subgoal unfolding image_def by force
  subgoal unfolding image_def by (metis (mono_tags, lifting) Un_iff fst_conv mem_Collect_eq snd_conv) 
  subgoal  
    by (smt (verit, del_insts) Un_iff fst_conv fst_map_prod imageI snd_conv snd_map_prod surj_pair) .


lemma presBnd_imp: "presBnd \<sigma> \<Longrightarrow> \<sigma> ` AVar \<subseteq> AVar"
unfolding presBnd_def apply auto subgoal for x apply(erule allE[of _ "{(undefined,x)}"]) by auto .

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
  Var_VAR: "x \<in> AVar \<Longrightarrow> ppr (Var x) (VAR x)"
| App_APP: "ppr t T \<Longrightarrow> ppr s S  \<Longrightarrow> ppr (App t s) (APP T S)"
| Lam_LAM: "y \<notin> {x} \<union> FFVars t \<union> Vars T \<Longrightarrow>  
    ppr (usub t y x) t' \<Longrightarrow> ppr (Lam x t) (LAM y T)"
*)

definition G :: "B \<Rightarrow> (T \<Rightarrow> bool) \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>B R tt.  
         (\<exists>x. B = {} \<and> fst tt = Var x \<and> snd tt = VAR x \<and> 
              x \<in> AVar) 
         \<or>
         (\<exists>t T s S. B = {} \<and> fst tt = App t s \<and> snd tt = APP T S \<and> 
                    R (t,T) \<and> R (s,S))
         \<or> 
         (\<exists>y x t T. B = {(x,y)} \<and> fst tt = Lam x t \<and> snd tt = LAM y T \<and> 
                    y \<notin> {x} \<union> FFVars t \<union> Vars T \<and> R (t,T))"
 

(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma G_mmono: "R \<le> R' \<Longrightarrow> G xxs R t \<Longrightarrow> G xxs R' t"
unfolding G_def by fastforce

lemma "snd ` map_prod \<sigma> \<sigma> ` B \<subseteq> AVar \<longleftrightarrow> \<sigma> ` B \<subseteq> AVar"

(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma G_eequiv: 
"isPerm \<sigma> \<Longrightarrow> presBnd \<sigma> \<Longrightarrow> G B R tt \<Longrightarrow> 
 G  (Bperm \<sigma> B) (\<lambda>tt'. R (Tperm (inv \<sigma>) tt')) (Tperm \<sigma> tt)"
unfolding G_def apply(drule presBnd_imp) apply(elim disjE)
  subgoal apply(rule disjI3_1)
  subgoal apply(elim exE) subgoal for x
  apply(rule exI[of _ "\<sigma> x"])  
  apply(cases tt) unfolding isPerm_def small_def Tperm_def by auto 
  (* *)
  subgoal apply(rule disjI3_2)
  subgoal apply(elim exE) subgoal for xs e e'
  apply(rule exI[of _ "dsmap \<sigma> xs"]) 
  apply(rule exI[of _ "irrename \<sigma> e"]) 
  apply(rule exI[of _ "irrename \<sigma> e'"])  
  apply(cases t) unfolding isPerm_def small_def Tperm_def presBnd_def
  apply (simp add: iterm.rrename_comps) by (metis option.simps(5)) . . 
  (* *)
  subgoal apply(rule disjI3_3)
  subgoal apply(elim exE) subgoal for e1 e1' es2 es2'
  apply(rule exI[of _ "irrename \<sigma> e1"]) apply(rule exI[of _ "irrename \<sigma> e1'"]) 
  apply(rule exI[of _ "smap (irrename \<sigma>) es2"]) apply(rule exI[of _ "smap (irrename \<sigma>) es2'"])
  apply(cases t) unfolding isPerm_def small_def Tperm_def 
  apply (simp add: iterm.rrename_comps) 
  by (metis image_in_bij_eq iterm.rrename_bijs iterm.rrename_inv_simps) . . .



(* *)

lemma G_bnd: "G xxs R t \<Longrightarrow> bnd xxs"
unfolding G_def by auto 

lemma eextend_to_presBnd: 
assumes "bnd xxs" "small A" "bsmall A" "A' \<subseteq> A" "Bsupp xxs \<inter> A' = {}"
shows "\<exists>\<rho>. isPerm \<rho> \<and> presBnd \<rho> \<and> \<rho> ` Bsupp xxs \<inter> A = {} \<and> id_on A' \<rho>" 
proof(cases xxs)
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


interpretation Reneqv : IInduct1 
where Tperm = Tperm and Tsupp = Tsupp and Bperm = Bperm and Bsupp = Bsupp 
and bnd = bnd and bsmall = bsmall and GG = G
apply standard
using G_mmono G_eequiv G_bnd eextend_to_presBnd by auto


(* *)

lemma reneqv_I: "reneqv t1 t2 = Reneqv.II (t1,t2)" 
unfolding reneqv_def Reneqv.II_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
unfolding fun_eq_iff G_def apply clarify
subgoal for R tt1 tt2 apply(rule iffI)
  subgoal apply(elim disjE exE conjE)
    \<^cancel>\<open>iVar: \<close>
    subgoal for xs x x' apply(rule exI[of _ None]) apply(rule disjI3_1) by auto
    \<^cancel>\<open>iLam: \<close> 
    subgoal for xs e e' apply(rule exI[of _ "Some xs"]) apply(rule disjI3_2) by auto 
    \<^cancel>\<open>iApp: \<close>
    subgoal apply(rule exI[of _ None]) apply(rule disjI3_3) by auto .
    (* *)
  subgoal apply(elim disjE exE conjE)
    \<^cancel>\<open>iVar: \<close>
    subgoal apply(rule disjI3_1) by auto
    \<^cancel>\<open>iLam: \<close>
    subgoal apply(rule disjI3_2) by auto
    \<^cancel>\<open>iApp: \<close>
    subgoal apply(rule disjI3_3) by auto . . .
  

lemma III_bsmall: "Reneqv.II t \<Longrightarrow> bsmall (Tsupp t)"
apply(cases t)
  subgoal for e1 e2 apply simp
  unfolding reneqv_I[symmetric] apply(drule reneqv_touchedSuperT)
  apply(rule bsmall_Un) unfolding bsmall_def touchedSuperT_def by auto .



lemma Tvars_dsset: "dsset xs \<inter> (Tsupp t - dsset xs) = {}" 
  "|Tsupp t - dsset xs| <o |UNIV::ivar set|"
  "Reneqv.II t \<Longrightarrow> finite (touchedSuper (Tsupp t - dsset ys))"
subgoal using Diff_disjoint .
subgoal using small_def card_of_minus_bound ssmall_Tsupp by blast
subgoal apply(subgoal_tac "bsmall (Tsupp t)")
  subgoal unfolding bsmall_def 
    by (meson Diff_subset rev_finite_subset touchedSuper_mono) 
  subgoal by (metis III_bsmall) . .

lemma G_rrefresh: 
"(\<forall>t. R t \<longrightarrow> Reneqv.II t) \<Longrightarrow> 
 (\<forall>\<sigma> t. isPerm \<sigma> \<and> presBnd \<sigma> \<and> R t \<longrightarrow> R (Tperm \<sigma> t)) \<Longrightarrow> 
 G xxs R t \<Longrightarrow> 
 \<exists>yys. Bsupp yys \<inter> Tsupp t = {} \<and> G yys R t"
apply(subgoal_tac "Reneqv.II t") defer
apply (metis Reneqv.GG_mmono2 Reneqv.II.simps predicate1I)
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
      subgoal apply(subst iLam_irrename[of "f"]) unfolding id_on_def by auto
      subgoal apply(subst irrename_eq_itvsubst_iVar)
        subgoal unfolding isPerm_def by auto
        subgoal unfolding isPerm_def by auto
        subgoal by (smt (verit, best) Diff_iff Un_iff iLam_irrename id_on_def 
           irrename_eq_itvsubst_iVar) . 
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

interpretation Reneqv : IInduct
where Tperm = Tperm and Tsupp = Tsupp and 
Bperm = Bperm and Bsupp = Bsupp and bnd = bnd and bsmall = bsmall 
and GG = G
apply standard using III_bsmall G_rrefresh by auto

(* *)


(* FROM ABSTRACT BACK TO CONCRETE: *)
thm reneqv.induct[no_vars] 

corollary strong_induct_reneqv[consumes 2, case_names iVar iLam iApp]: 
assumes par: "\<And>p. small (Psupp p) \<and> bsmall (Psupp p)"
and st: "reneqv t1 t2"  
and iVar: "\<And>xs x x' p. 
  super xs \<Longrightarrow> {x,x'} \<subseteq> dsset xs \<Longrightarrow>
  R p (iVar x) (iVar x')"
and iLam: "\<And>e e' xs p. 
  dsset xs \<inter> Psupp p = {} \<Longrightarrow> 
  super xs \<Longrightarrow> reneqv e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> 
  R p (iLam xs e) (iLam xs e')" 
and iApp: "\<And>e1 e1' es2 es2' p. 
  reneqv e1 e1' \<Longrightarrow> (\<forall>p'. R p' e1 e1') \<Longrightarrow> 
  (\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<longrightarrow> reneqv e e' \<and> (\<forall>p'. R p' e e')) \<Longrightarrow> 
  R p (iApp e1 es2) (iApp e1' es2')"
shows "R p t1 t2"
unfolding reneqv_I
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by simp
  subgoal using par st 
  unfolding bsmall_def[symmetric] apply(elim Reneqv.BE_iinduct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
    subgoal unfolding reneqv_I by simp
    subgoal for p B t apply(subst (asm) G_def) 
    unfolding reneqv_I[symmetric] apply(elim disjE exE)
      subgoal using iVar by auto 
      subgoal using iLam by auto  
      subgoal using iApp by auto . . .

corollary strong_induct_reneqv''[consumes 1, case_names bsmall Bound iVar iLam iApp]:
  assumes  "reneqv t1 t2"
and bsmall: "\<And>(p::'a). bsmall (PFVars p)"
assumes bound: "\<And>(p::'a). |PFVars p| <o |UNIV::ivar set|"
and iVar: "\<And>xs x x' p.
  super xs \<Longrightarrow> {x,x'} \<subseteq> dsset xs \<Longrightarrow>
  R (iVar x) (iVar x') p"
and iLam: "\<And>e e' xs p.
  dsset xs \<inter> PFVars p = {} \<Longrightarrow>
  super xs \<Longrightarrow> reneqv e e' \<Longrightarrow> (\<forall>p'. R e e' p') \<Longrightarrow>
  R (iLam xs e) (iLam xs e') p"
and iApp: "\<And>e1 e1' es2 es2' p.
  reneqv e1 e1' \<Longrightarrow> (\<forall>p'. R e1 e1' p') \<Longrightarrow>
  (\<And>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<Longrightarrow> reneqv e e') \<Longrightarrow>
  (\<And>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<Longrightarrow> \<forall>p'. R e e' p') \<Longrightarrow>
  R (iApp e1 es2) (iApp e1' es2') p"
shows "\<forall>(p::'a). R t1 t2 p"
using assms strong_induct_reneqv[of PFVars t1 t2 "\<lambda>p t1 t2. R t1 t2 p"] unfolding small_def by auto

(* ... and with fixed parameters: *)
corollary strong_induct_reneqv'[consumes 2, case_names iVar iLam iApp]: 
assumes par: "small A \<and> bsmall A"
and st: "reneqv t1 t2"  
and iVar: "\<And>xs x x'. 
  super xs \<Longrightarrow> {x,x'} \<subseteq> dsset xs \<Longrightarrow>
  R (iVar x) (iVar x')"
and iLam: "\<And>e e' xs. 
  dsset xs \<inter> A = {} \<Longrightarrow> 
  super xs \<Longrightarrow> reneqv e e' \<Longrightarrow> R e e' \<Longrightarrow> 
  R (iLam xs e) (iLam xs e')" 
and iApp: "\<And>e1 e1' es2 es2'. 
  reneqv e1 e1' \<Longrightarrow> R e1 e1' \<Longrightarrow> 
  (\<forall>e e'. {e,e'} \<subseteq> sset es2 \<union> sset es2' \<longrightarrow> reneqv e e' \<and> R e e') \<Longrightarrow> 
  R (iApp e1 es2) (iApp e1' es2')"
shows "R t1 t2"
apply(rule strong_induct_reneqv[of "\<lambda>_::unit. A"]) using assms by auto

(* Also inferring equivariance from the general infrastructure: *)
corollary irrename_reneqv:
assumes f: "bij f" "|supp f| <o |UNIV::ivar set|" "presSuper f"
and r: "reneqv e e'" 
shows "reneqv (irrename f e) (irrename f e')"
using assms unfolding reneqv_I using Reneqv.II_equiv[of "(e,e')" f]
unfolding Tperm_def isPerm_def presBnd_presSuper by auto

  

end