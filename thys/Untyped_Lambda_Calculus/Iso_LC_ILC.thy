(* Mazza's isomorphism between affine uniform ILC and LC *)

theory Iso_LC_ILC 
imports Translation_LC_to_ILC  Translation_ILC_to_LC ILC_affine 
"HOL-Library.Sublist" LC_Beta
begin

term tr
term tr'

find_theorems name: prefix
term "prefix a b" 

find_theorems tr 


lemma tr_FFVars_super: 
"x \<in> ILC.FFVars (tr e p) \<Longrightarrow> \<exists>xs p'. super xs \<and> x = dsnth xs (natOf p')"
apply(induct e arbitrary: p x)  
  subgoal using super_superOf by fastforce
  subgoal by auto
  subgoal by auto .


lemma tr_FFVars_prefix: 
"x \<in> ILC.FFVars (tr e p) \<Longrightarrow> super xs \<Longrightarrow> x = dsnth xs (natOf p') \<Longrightarrow> prefix p p'"
apply(induct e arbitrary: p x xs) apply safe
  subgoal by simp (metis dsnth.rep_eq dsset.rep_eq dtheN_dsnth injD 
     inject_natOf insert_absorb insert_disjoint(1) prefix_order.order_refl snth_sset super_disj super_superOf)
  subgoal by simp (metis append_prefixD) 
  subgoal by auto .

lemma not_prefix_FFVars_tr_disjoint: 
"\<not> prefix p p' \<Longrightarrow> \<not> prefix p' p \<Longrightarrow> ILC.FFVars (tr e p) \<inter> ILC.FFVars (tr e' p') = {}"
by (metis disjoint_iff prefix_same_cases tr_FFVars_prefix tr_FFVars_super)


(* Mazza's lemma 15(1) (remember that 15(2) comes for free from our recursor) *) thm reneqv_tr
lemma affine_tr: "affine (tr e p)"
apply(induct e arbitrary: p)
  apply auto unfolding affine_iApp_iff apply auto 
  apply (metis Zero_not_Suc append1_eq_conv append_eq_append_conv length_append_singleton prefix_def tr_FFVars_prefix tr_FFVars_super)
  by (metis Cons_prefix_Cons Int_emptyD Suc_inject not_prefix_FFVars_tr_disjoint same_prefix_prefix)


(* Mazza Lemma 16 *)
lemma reneqv_tr': "reneqv s t \<Longrightarrow> tr' s = tr' t"
apply(induct rule: reneqv.induct)
  subgoal by simp (metis dtheN prod.collapse subsetD super_dsset_RSuper theSN_unique)
  subgoal using tr'_iLam_uniform by (metis uniform_def uniform_def2)
  subgoal for s t apply(subst tr'_iApp_uniform)
    subgoal unfolding uniform_def by auto
    subgoal unfolding uniformS_def4 by auto
    subgoal apply(subst tr'_iApp_uniform)
      subgoal unfolding uniform_def2 by auto
      subgoal unfolding uniformS_def4 by auto
      subgoal using shd_sset by auto . . .

lemma IImsupp_Var: "LC.IImsupp (Var(x := e)) \<subseteq> FFVars e \<union> {x}"
unfolding LC.IImsupp_def LC.SSupp_def by auto

lemma IImsupp_Var': "y \<noteq> x \<and> y \<notin> FFVars e \<Longrightarrow> y \<notin> LC.IImsupp (Var(x := e))"
using IImsupp_Var by auto 

lemma uniformS_touchedSuper_IImsupp_imkSubst':
"super xs \<Longrightarrow> uniformS es \<Longrightarrow> e \<in> sset es \<Longrightarrow> 
  ys \<noteq> xs \<Longrightarrow> ys \<notin> touchedSuper (ILC.FFVars e) \<Longrightarrow> 
  ys \<notin> touchedSuper (ILC.IImsupp (imkSubst xs es))"
using uniformS_touchedSuper_IImsupp_imkSubst by auto

lemma uniformS_touchedSuper_IImsupp_imkSubst'':
"super xs \<Longrightarrow> super ys \<Longrightarrow> uniformS es \<Longrightarrow> e \<in> sset es \<Longrightarrow> 
  ys \<noteq> xs \<Longrightarrow> dsset ys \<inter> ILC.FFVars e = {} \<Longrightarrow> 
  dsset ys \<inter> ILC.IImsupp (imkSubst xs es) = {}"
using uniformS_touchedSuper_IImsupp_imkSubst' unfolding touchedSuper_def by blast

(*
lemma "super xs \<Longrightarrow> uniformS es \<Longrightarrow> e \<in> sset es \<Longrightarrow> 
 {xsa. super xsa \<and> ILC.IImsupp (imkSubst xs es) \<inter> dsset xsa \<noteq> {}} \<subseteq> 
 {xs} \<union> {xs. super xs \<and> ILC.FFVars e \<inter> dsset xs \<noteq> {}}"
*)

(* Mazza's lemma 17 *)
lemma tr_tvsubst_Var_reneqv: 
(* This assumption made by Mazza is not needed: 
assumes "\<And>i j. i \<noteq> j \<Longrightarrow> \<not> prefix (snth ps i) (snth ps j)" *)
shows "reneqv
         (tr (tvsubst (Var(x:=e)) ee) q) 
         (itvsubst (imkSubst (superOf x) (smap (tr e) ps)) (tr ee q))"
proof-
  define A where "A = {x} \<union> FFVars e"
  have A: "|A| <o |UNIV::var set|" unfolding A_def 
    by (meson card_of_Un_singl_ordLess_infinite1 infinite_var term.set_bd_UNIV)
  thus ?thesis proof(induct arbitrary: q ps rule : trm_strong_induct)
    case (Var x)
    then show ?case apply(subst term.subst(1))
      subgoal by auto
      subgoal by auto (metis dsset_range empty_iff imkSubst_idle insert_iff rangeI reneqv_tr 
        subOf_superOf super_superOf touchedSuper_iVar tr_Var) .
  next
    case (App t1 t2)
    then show ?case apply(subst term.subst(2))
      subgoal by auto
      subgoal apply (simp add: reneqv_iApp_iff) apply safe
        using App.hyps(1,2) reneqv_trans reneqv_sym apply blast+    
        using App.hyps(2) reneqv_trans reneqv_sym by blast .
  next
    case (Lam y t)
    then show ?case apply(subst term.subst(3))
      subgoal by auto
      subgoal unfolding A_def using IImsupp_Var by fastforce
      subgoal unfolding A_def tr_Lam apply (subst iterm.subst(3))
        subgoal by auto
        subgoal using uniformS_touchedSuper_IImsupp_imkSubst 
        subgoal apply(subgoal_tac "superOf y \<notin> touchedSuper (ILC.IImsupp (imkSubst (superOf x) (smap (tr e) ps)))")
          subgoal unfolding touchedSuper_def by auto
          subgoal  apply(rule uniformS_touchedSuper_IImsupp_imkSubst'[where e = "tr e (shd ps)"]) 
            subgoal by auto   subgoal by auto
            subgoal apply auto  by (meson image_eqI shd_sset)
            subgoal by simp  subgoal by (metis FFVars_tr UnI2 image_eqI subOf_superOf subset_eq) . . .
        subgoal apply(subst reneqv_iLam_iff)
          subgoal by auto
          subgoal using Lam.hyps(2) by fastforce . . .
  qed
qed

(* difference from the above is that we have a different position q' *)
lemma tr_tvsubst_Var_reneqv':  
shows "reneqv
         (tr (tvsubst (Var(x:=e)) ee) q) 
         (itvsubst (imkSubst (superOf x) (smap (tr e) ps)) (tr ee q'))"
using reneqv_trans tr_tvsubst_Var_reneqv by blast

(* *)

lemma touchedSuper_Un: "touchedSuper (A \<union> A') = touchedSuper A \<union> touchedSuper A'"
unfolding touchedSuper_def by auto

lemma super_subOf_theN_eq: "super xs \<Longrightarrow> super ys \<Longrightarrow> x \<in> dsset ys \<Longrightarrow> subOf (fst (theSN x)) = subOf xs \<Longrightarrow> xs = ys"
by (metis dtheN prod.collapse subsetD superOf_subOf super_dsset_RSuper theSN_unique)


lemma FFVars_touchedSuperT_imkSubst_UN_incl: 
assumes xs: "super xs" and 0: "touchedSuperT e2 = touchedSuperT e2'"
and 1: "(\<forall>e2 e2'. {e2, e2'} \<subseteq> sset ts \<longrightarrow> touchedSuperT e2 = touchedSuperT e2')"
shows "(\<Union>x\<in>ILC.FFVars e2. touchedSuperT (imkSubst xs ts x)) \<subseteq>
       (\<Union>x'\<in>ILC.FFVars e2'. touchedSuperT (imkSubst xs ts x'))"
proof safe
  fix x y
  assume x: "x \<in> ILC.FFVars e2" and y: "y \<in> touchedSuperT (imkSubst xs ts x)"
  show "y \<in> (\<Union>x'\<in>ILC.FFVars e2'. touchedSuperT (imkSubst xs ts x'))"
  proof(cases "x \<in> dsset xs")
    case True note xx = True
    then obtain x' where x': "x' \<in> ILC.FFVars e2'" "x' \<in> dsset xs" 
    using xs 0 x unfolding touchedSuperT_def touchedSuper_def by auto
    obtain i where xi: "x = dsnth xs i" using xx by (metis dtheN)
    hence ii: "imkSubst xs ts x = snth ts i" by simp
    obtain i' where xi': "x' = dsnth xs i'" using x' by (metis dtheN)
    hence ii': "imkSubst xs ts x' = snth ts i'" by simp
    have y': "y \<in> touchedSuperT (imkSubst xs ts x')"
    using y 1 unfolding ii ii' sset_range image_def by auto
    thus ?thesis using x' by auto
  next
    case False note xx = False
    hence ii: "imkSubst xs ts x = iVar x" by simp
    obtain xs1 where xs1: "super xs1" "xs1 \<noteq> xs" "x \<in> dsset xs1"
    using xx touchedSuperT_def touchedSuper_def y by auto   
    obtain x' where x': "x'\<in>ILC.FFVars e2'" "x' \<in> dsset xs1"
    using 0 x xs1 unfolding touchedSuperT_def touchedSuper_def by auto
    hence "x' \<notin> dsset xs" using xs1 by (metis IntI empty_iff super_disj xs)
    hence ii': "imkSubst xs ts x' = iVar x'" by simp
    have y': "y \<in> touchedSuperT (imkSubst xs ts x')" 
    using touchedSuper_iVar x'(2) xs1(1) xs1(3) y unfolding ii ii' by auto
    show ?thesis using y' x'(1) by auto
  qed
qed

lemma FFVars_touchedSuperT_imkSubst_UN: 
assumes xs: "super xs" and 0: "touchedSuperT e2 = touchedSuperT e2'"
and 1: "(\<forall>e2 e2'. {e2, e2'} \<subseteq> sset ts \<longrightarrow> touchedSuperT e2 = touchedSuperT e2')"
shows "(\<Union>x\<in>ILC.FFVars e2. touchedSuperT (imkSubst xs ts x)) =
       (\<Union>x'\<in>ILC.FFVars e2'. touchedSuperT (imkSubst xs ts x'))"
apply standard
  subgoal apply(rule FFVars_touchedSuperT_imkSubst_UN_incl) using assms by auto
  subgoal apply(rule FFVars_touchedSuperT_imkSubst_UN_incl) using assms by auto .  
    

(* Lemma 18 from Mazza: *)
(* Here rule induction for good is needed. There is no way to to induction on "uniform" 
directly (and a genralization for reneqv is not clear); 
also structural induction on t would not work, as the proof would fail 
in the lambda case because we would not know xs is a supervariable 
(and we would not be able to recover it).

So "good" acts like a bit of an "interpolant" (a sweet spot) between "uniform" 
(which does not have induction) and "reneqv" (which being binary it is too heavy). 

And we actually need *fresh induction* for good (so an application of our 
rule induction meta-theory), because in the lambda-case we must avoid xs and the free vars of the 
ts's. 
*)
lemma tr'_itvsubst_good_uniformS: 
assumes txs: "super xs" "uniformS ts" and t: "uniform t" 
shows "tr' (itvsubst (imkSubst xs ts) t) = 
       tvsubst (Var((subOf xs):=(tr' (snth ts 0)))) (tr' t)"
proof-
  have t: "good t" using t  
    by (simp add: uniform_good)
  define A where "A = dsset xs \<union> \<Union> (ILC.FFVars ` (sset ts))"
  obtain t2 where t2: "t2 \<in> sset ts"  
    using snth_sset by blast
  have g: "(\<forall>e2\<in>sset ts. good e2) \<and> (\<forall>e2 e2'. {e2, e2'} \<subseteq> sset ts \<longrightarrow> touchedSuperT e2 = touchedSuperT e2')"
  using txs(2) uniformS_good by auto
  have "touchedSuper (\<Union> (ILC.FFVars ` sset ts)) = touchedSuper (ILC.FFVars t2)"
  using t2 g apply auto unfolding touchedSuperT_def  
  apply (smt (verit, ccfv_SIG) touchedSuper_UN UN_iff image_iff)
   by (metis UN_iff touchedSuper_Union)
  hence 0: "touchedSuper (dsset xs \<union> \<Union> (ILC.FFVars ` sset ts)) = 
    touchedSuper (dsset xs) \<union> touchedSuper (ILC.FFVars t2)"
  unfolding touchedSuper_Un by auto

  have A: "ILC2.small A \<and> bsmall A" apply(rule conjI)
    subgoal unfolding A_def ILC2.small_def
    by (metis ILC_UBeta.Tfvars.simps ILC_UBeta.Tvars_dsset(2) Un_Diff_cancel 
    card_dsset_ivar sup.idem var_stream_class.Un_bound)   
    subgoal unfolding A_def bsmall_def unfolding 0  
      by (metis g bsmall_def finite_Un good_finite_touchedSuperT super_bsmall t2 touchedSuperT_def txs(1)) .
  
  (* NB: while good t is needed for induction, 
    the "uniformS t assumption cannot be replaced by the following: 
     "(\<forall>e2\<in>sset ts. good e2) \<and> (\<forall>e2 e2'. {e2, e2'} \<subseteq> sset ts \<longrightarrow> touchedSuperT e2 = touchedSuperT e2')" 
      because this would fail to prove the Var case (where, as Mazza also notes, the lemma reneqv_tr' is essential). 
  *)
  then show ?thesis using t txs apply(induct rule: BE_induct_good')
    subgoal for ys x apply auto 
      apply (metis bot.extremum imkSubst_def insert_subset 
       reneqvS_def reneqv_tr' shd_sset snth_sset sup.idem super_subOf_theN_eq uniformS_def3)
      by (metis dtheN fst_conv imkSubst_idle snd_conv theSN' theSN_ex tr'_iVar) 
    (* *)
    defer
    subgoal for e1 es2 apply(subst tr'_iApp)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal apply(subst iterm.subst(2))
      subgoal by auto
      subgoal apply(subst tr'_iApp)
        subgoal using g good_imkSubst by auto
        subgoal using g good_imkSubst by auto
        subgoal apply clarsimp  apply (simp add: touchedSuperT_itvsubst ) 
        apply(drule uniformS_good) subgoal for e2 e2'  
        by (metis FFVars_touchedSuperT_imkSubst_UN) .
        subgoal using shd_sset by fastforce . . .
    (* *)
    subgoal for e ys apply(subst tr'_iLam)
      apply auto apply(subst iterm.subst(3))
        subgoal by auto 
        subgoal unfolding A_def apply(rule uniformS_touchedSuper_IImsupp_imkSubst''[where e = "shd ts"])
          using shd_sset super_touchedSuper_dsset by fastforce+
        subgoal apply(subst term.subst(3))
          subgoal by auto subgoal unfolding A_def apply(rule IImsupp_Var') 
          apply simp by (metis (no_types, lifting) FFVars_tr' Int_Un_emptyI1 
           Int_Un_emptyI2 Int_absorb UN_I disjoint_iff empty_not_insert shd_sset 
           superOf_subOf super_touchedSuper_dsset touchedSuper_emp uniformS_good)      
          subgoal apply(subst tr'_iLam) 
            subgoal unfolding A_def by auto
            subgoal using g good_imkSubst by auto
            subgoal by auto . . . . 
qed



(* Theorem 9 from Mazza: *)
(* Theorem 9(1): *)
lemma tr'_tr: "tr' (tr e p) = e"
apply(induct e arbitrary: p) 
  subgoal for x p apply simp apply(subst tr'_iVar[of "superOf x"]) 
    subgoal by auto
    subgoal by (simp add: dsset_range)
    subgoal by (metis fst_eqD subOf_superOf super_superOf theSN theSN_ex) .
  subgoal apply simp apply(subst tr'_iApp_uniform) 
    subgoal by blast
    subgoal unfolding uniformS_def4 by auto
    subgoal by auto .
  subgoal by simp .

(* Theorem 9(2): *)
(* We again need "good" induction for the same reason: because 
structural induction does not take 
care of the supervariable assumptiin in the lambda-case. But this 
time regular induction works, no need fresh induction like before. 
Note also that "uniform t" is also needed in the induction, otherwise 
the iApp case does not go through. 
*)
lemma tr_tr': 
assumes t: "uniform t"
shows "reneqv (tr (tr' t) p) t" 
proof-
have tt: "good t" using uniform_good[OF t] .
show ?thesis using tt t
apply(induct arbitrary: p rule: good.induct) 
  subgoal for xs x p apply clarsimp  
    apply(rule reneqv.iVar[of xs]) 
    by auto (metis dsset_range rangeI subsetD superOf_subOf super_dsset_RSuper 
       super_subOf_theN_eq theSN') 
  subgoal for xs t p apply(subst tr'_iLam) 
    subgoal by simp
    subgoal by simp
    subgoal apply simp apply(rule reneqv.iLam) by auto .
  subgoal for t1 ts p apply(subst tr'_iApp) 
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal apply simp apply(rule reneqv.iApp) 
      subgoal unfolding uniform_iApp_iff by auto
      subgoal unfolding sset_range image_def  
      by simp (smt (verit, ccfv_threshold) bot.extremum insert_subset reneqv_trans 
         reneqv_sym snth.simps(1) snth_sset uniform_iApp_case uniform_iApp_iff) . . .
qed

(* *)
definition red where 
"red e ee \<equiv> \<exists>x e1 e2. e = App (Lam x e1) e2 \<and> ee = tvsubst (Var(x:=e2)) e1"

lemma red_step: "red e ee \<Longrightarrow> step e ee"
by (metis red_def step.Beta)

lemma red_step2: "stream_all2 red es ees \<Longrightarrow> stream_all2 step es ees"
unfolding stream_all2_iff_snth using red_step by auto



lemma tr'_hred_red: 
assumes ttt: "hred t tt" and t: "uniform t"
shows "red (tr' t) (tr' tt)"
using ttt t unfolding red_def hred_def2[OF t] 
by (metis reneqv_iApp_iff tr'_iApp_uniform tr'_iLam_uniform tr'_itvsubst_good_uniformS 
   uniformS_def4 uniform_def3 uniform_iLam_iff)

lemma tr'_hred_red2: 
assumes "uniformS ts" "stream_all2 hred ts ts'"
shows "stream_all2 red (smap tr' ts) (smap tr' ts')"
using assms unfolding stream_all2_iff_snth 
by (simp add: tr'_hred_red uniformS_sset_uniform)

(* Theorem 19(4) (generalized for our (necessarily stream-based) version of 
uniform step (see previous discussion, when introducing ustep, for why) *)
lemma ustep_step: "ustep ts ss \<Longrightarrow> stream_all2 step (smap tr' ts) (smap tr' ss)"
proof(induct rule: ustep.induct)
  case (Beta es es')
  then show ?case using red_step2 tr'_hred_red2 by blast
next
  case (iAppL ess es es')
  then show ?case unfolding stream_all2_iff_snth  apply clarsimp subgoal for i
    apply(subst tr'_iApp_uniform)
      subgoal using snth_sset uniformS_sset_uniform ustep_uniformS by blast
      subgoal unfolding uniformS_sflat unfolding uniformS_def4 sset_range by auto
      apply(subst tr'_iApp_uniform)
        subgoal using snth_sset uniformS_sset_uniform ustep_uniformS by blast
        subgoal unfolding uniformS_sflat unfolding uniformS_def4 sset_range by auto
        subgoal apply(rule step.AppL) by auto . .
next
  case (iAppR es ess ess')
  then show ?case unfolding stream_all2_iff_snth  apply clarsimp subgoal for i
    apply(subst tr'_iApp_uniform)
      subgoal using snth_sset uniformS_sset_uniform ustep_uniformS by blast
      subgoal unfolding uniformS_sflat unfolding uniformS_def4 sset_range image_def 
      by simp (metis snth2.simps uniformS_sflat ustep_uniformS)
      apply(subst tr'_iApp_uniform)
        subgoal using snth_sset uniformS_sset_uniform ustep_uniformS by blast
        subgoal unfolding uniformS_sflat unfolding uniformS_def4 sset_range image_def 
        by simp (metis snth2.simps uniformS_sflat ustep_uniformS)
        subgoal apply(rule step.AppR) unfolding snth_sflat  
        by (metis nat2_nat1 snth.simps(1) snth2.simps) . .
next
  case (Xi xs es es')
  then show ?case unfolding stream_all2_iff_snth apply clarsimp subgoal for i
    apply(subst tr'_iLam_uniform)
      subgoal by simp
      subgoal using snth_sset uniformS_sset_uniform ustep_uniformS by blast
      subgoal apply(subst tr'_iLam_uniform)
        subgoal by simp
        subgoal using snth_sset uniformS_sset_uniform ustep_uniformS by blast
      subgoal apply(rule step.Xi) by auto . . .
qed


find_theorems uniformS ustep
 
(* *)
(* Theorem 19(3): *)
lemma step_ustep: "step e ee \<Longrightarrow> 
  \<exists>tts. ustep (smap (tr e) ps) tts \<and> 
        stream_all2 reneqv tts (smap (tr ee) ps)"
proof(induct arbitrary: ps rule: step.induct)
  case (Beta x e1 e2 ps)
  define qs where qs: "qs \<equiv> \<lambda>p. smap (\<lambda>n. tr e2 (p @ [Suc n])) nats"
  term "smap (\<lambda>p. itvsubst (imkSubst (superOf x) (smap (tr e2) ps)) (tr e1 p)) ps"
  thm tr_tvsubst_Var_reneqv'
  show ?case apply(intro exI[of _ 
   "smap (\<lambda>p. itvsubst (imkSubst (superOf x) (smap (\<lambda>n. tr e2 (p @ [Suc n])) nats)) (tr e1 (p @ [0]))) ps"] conjI)
    subgoal apply simp apply(rule ustep.Beta)
      subgoal unfolding uniformS_def4 apply clarsimp
      apply(rule reneqv.iApp) 
        subgoal apply(rule reneqv.iLam) using reneqv_tr by auto
        subgoal by auto . 
      subgoal unfolding stream_all2_iff_snth hred_def by auto .
    subgoal unfolding stream_all2_iff_snth apply auto subgoal for i 
    (* Below I put undefined because the choice of the position stream does not matter *)
    apply(rule reneqv_trans[OF tr_tvsubst_Var_reneqv'[of x e2 e1 "ps !! i" undefined "ps !! i @ [0]"], 
        THEN reneqv_sym]) apply(rule reneqv_imkSubst)
    unfolding reneqvS_def by auto . .    
next
  case (AppL e1 e1' e2 ps) 
  have 0: "smap (\<lambda>p. iApp (tr e1 (p @ [0])) (smap (\<lambda>n. tr e2 (p @ [Suc n])) nats)) ps 
    = smap2 iApp (smap (\<lambda>p. tr e1 (p @ [0])) ps) 
      (smap (\<lambda>p. smap (\<lambda>n. tr e2 (p @ [Suc n])) nats) ps)" 
  by (auto simp: stream_eq_nth)
  define qs where qs: "qs = smap (\<lambda>p. p @ [0]) ps"
  obtain tts where tts: "ustep (smap (tr e1) qs) tts" 
  "stream_all2 reneqv tts (smap (tr e1') qs)" using AppL(2)[of qs] by auto
  define tts' where "tts' = smap2 iApp tts
      (smap (\<lambda>p. smap (\<lambda>n. tr e2 (p @ [Suc n])) nats) ps)"  
  show ?case apply simp apply(intro exI[of _ tts'] conjI) unfolding tts'_def
    subgoal unfolding 0 apply(rule ustep.iAppL)
      subgoal unfolding uniformS_sflat by auto
      subgoal using tts(1) unfolding qs unfolding stream.map_comp o_def . .
    subgoal unfolding stream_all2_iff_snth apply auto
    apply(rule reneqv.iApp)
      subgoal using tts(2) unfolding stream_all2_iff_snth qs by auto
      subgoal by auto . .   
next
  case (AppR e2 e2' e1 ps)  
  have 0: "smap (\<lambda>p. iApp (tr e1 (p @ [0])) (smap (\<lambda>n. tr e2 (p @ [Suc n])) nats)) ps 
    = smap2 iApp (smap (\<lambda>p. tr e1 (p @ [0])) ps) 
      (smap (\<lambda>p. smap (\<lambda>n. tr e2 (p @ [Suc n])) nats) ps)" 
  by (auto simp: stream_eq_nth)
  define qs where qs: "qs \<equiv> \<lambda>n. smap (\<lambda>p. p @ [Suc n]) ps"  

  have "\<forall>n. \<exists>tts. ustep (smap (tr e2) (qs n)) tts \<and> 
   stream_all2 reneqv tts (smap (tr e2') (qs n))" using AppR(2) by auto 
  then obtain tts where 
  00: "\<And>n. ustep (smap (tr e2) (qs n)) (tts n) \<and> 
       stream_all2 reneqv (tts n) (smap (tr e2') (qs n))" 
   by metis
  define ttss where "ttss \<equiv> smap tts nats"
  have ttss: "\<And>n. ustep (smap (tr e2) (qs n)) (snth ttss n)"
       "\<And>n. stream_all2 reneqv (snth ttss n) (smap (tr e2') (qs n))" 
  using 00 unfolding ttss_def by auto
  
  define tts' where "tts' = smap2 iApp (smap (\<lambda>p. tr e1 (p @ [0])) ps) ttss"  
  show ?case apply simp apply(intro exI[of _ tts'] conjI) unfolding tts'_def
    subgoal unfolding 0 apply(rule ustep.iAppR)
      subgoal unfolding uniformS_def4 by auto
      subgoal using ttss(1) unfolding qs unfolding stream.map_comp o_def sorry .
    subgoal unfolding stream_all2_iff_snth apply auto
    apply(rule reneqv.iApp)
      subgoal using ttss(2) unfolding stream_all2_iff_snth qs by auto
      subgoal unfolding sset_range image_def  
      by simp (metis (mono_tags, lifting) reneqv_sym reneqv_tr reneqv_trans snth_smap stream_all2_iff_snth ttss(2)) . . 
next
  case (Xi e e' x)
  then obtain tts where tts: "ustep (smap (tr e) ps) tts" "stream_all2 reneqv tts (smap (tr e') ps)"
  by auto
  have 0: "smap (\<lambda>p. iLam (superOf x) (tr e p)) ps = 
           smap (iLam (superOf x)) (smap (tr e) ps)"
  unfolding stream_eq_nth by auto
  show ?case apply(intro exI[of _ "smap (iLam (superOf x)) tts"] conjI)
    subgoal apply simp unfolding 0 apply(rule ustep.Xi) using tts(1) by auto
    subgoal using tts(2) unfolding stream_all2_iff_snth by (auto intro: reneqv.iLam) .
qed



(*
lemma step_ustep: "stream_all2 step es ees \<Longrightarrow> 
  \<exists>tts. ustep (smap (\<lambda>e. tr e p) es) tts \<and> 
        stream_all2 reneqv tts (smap (\<lambda>e. tr ee p) ees)"
sorry 
*)
  





end