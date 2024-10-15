(* Mazza's isomorphism between affine uniform ILC and LC *)

theory Iso_LC_ILC 
imports Translation_LC_to_ILC Translation_ILC_to_LC ILC_affine 
"HOL-Library.Sublist" "Untyped_Lambda_Calculus.LC_Beta_depth"
begin


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
  apply auto unfolding affine_iAp_iff apply auto 
  apply (metis Zero_not_Suc append1_eq_conv append_eq_append_conv length_append_singleton prefix_def tr_FFVars_prefix tr_FFVars_super)
  by (metis Cons_prefix_Cons Int_emptyD Suc_inject not_prefix_FFVars_tr_disjoint same_prefix_prefix)


(* Mazza Lemma 16 *)
lemma reneqv_tr': "reneqv s t \<Longrightarrow> tr' s = tr' t"
apply(induct rule: reneqv.induct)
  subgoal by simp (metis dtheN prod.collapse subsetD super_dsset_RSuper theSN_unique)
  subgoal using tr'_iLm_uniform by (metis uniform_def uniform_def2)
  subgoal for s t apply(subst tr'_iAp_uniform)
    subgoal unfolding uniform_def by auto
    subgoal unfolding uniformS_def4 by auto
    subgoal apply(subst tr'_iAp_uniform)
      subgoal unfolding uniform_def2 by auto
      subgoal unfolding uniformS_def4 by auto
      subgoal using shd_sset by auto . . .


(* Mazza's lemma 17 *)
lemma tr_tvsubst_Vr_reneqv: 
(* This assumption made by Mazza is not needed: 
assumes "\<And>i j. i \<noteq> j \<Longrightarrow> \<not> prefix (snth ps i) (snth ps j)" *)
shows "reneqv
         (tr (tvsubst (Vr(x:=e)) ee) q) 
         (itvsubst (imkSubst (superOf x) (smap (tr e) ps)) (tr ee q))"
proof (binder_induction ee arbitrary: q ps avoiding: x e rule: Lterm.strong_induct)
  case (Vr x q ps)
  then show ?case apply(subst Lterm.subst(1))
      subgoal by auto
      subgoal by auto (metis dsset_range empty_iff imkSubst_idle insert_iff rangeI reneqv_tr 
        subOf_superOf super_superOf touchedSuper_iVr tr_Vr) .
next
  case (Ap t1 t2 q ps)
  then show ?case apply(subst Lterm.subst(2))
      subgoal by auto
      subgoal apply (simp add: reneqv_iAp_iff) apply safe
        using Ap.hyps(1,2) reneqv_trans reneqv_sym apply blast+    
        using Ap.hyps(2) reneqv_trans reneqv_sym by blast .
next
  case (Lm y t q ps)
  then show ?case apply(subst Lterm.subst(3))
      subgoal by auto
      subgoal using IImsupp_Vr by fastforce
      subgoal unfolding tr_Lm apply (subst ILterm.subst(3))
        subgoal by auto
        subgoal using uniformS_touchedSuper_IImsupp_imkSubst 
        subgoal apply(subgoal_tac "superOf y \<notin> touchedSuper (ILC.IImsupp (imkSubst (superOf x) (smap (tr e) ps)))")
          subgoal unfolding touchedSuper_def by auto
          subgoal  apply(rule uniformS_touchedSuper_IImsupp_imkSubst'[where e = "tr e (shd ps)"]) 
            subgoal by auto   subgoal by auto
            subgoal apply auto  by (meson image_eqI shd_sset)
            subgoal by simp  subgoal by (metis FFVars_tr UnI2 image_eqI subOf_superOf subset_eq) . . .
        subgoal apply(subst reneqv_iLm_iff)
          subgoal by auto
          subgoal using Lm.hyps(2) by fastforce . . .
qed

(* difference from the above lemma (tr_tvsubst_Vr_reneqv) 
is that we have a different position q' *)
lemma tr_tvsubst_Vr_reneqv':  
shows "reneqv
         (tr (tvsubst (Vr(x:=e)) ee) q) 
         (itvsubst (imkSubst (superOf x) (smap (tr e) ps)) (tr ee q'))"
using reneqv_trans tr_tvsubst_Vr_reneqv by blast

(* *)

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
    hence ii: "imkSubst xs ts x = iVr x" by simp
    obtain xs1 where xs1: "super xs1" "xs1 \<noteq> xs" "x \<in> dsset xs1"
    using xx touchedSuperT_def touchedSuper_def y by auto   
    obtain x' where x': "x'\<in>ILC.FFVars e2'" "x' \<in> dsset xs1"
    using 0 x xs1 unfolding touchedSuperT_def touchedSuper_def by auto
    hence "x' \<notin> dsset xs" using xs1 by (metis IntI empty_iff super_disj xs)
    hence ii': "imkSubst xs ts x' = iVr x'" by simp
    have y': "y \<in> touchedSuperT (imkSubst xs ts x')" 
    using touchedSuper_iVr x'(2) xs1(1) xs1(3) y unfolding ii ii' by auto
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
(* Here rule induction for good is needed. There is no way to do induction on "uniform" 
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
       tvsubst (Vr((subOf xs):=(tr' (snth ts 0)))) (tr' t)"
proof-
  have t: "good t" using t  
    by (simp add: uniform_good)
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
  
  (* NB: while good t is needed for induction, 
    the "uniformS t assumption cannot be replaced by the following: 
     "(\<forall>e2\<in>sset ts. good e2) \<and> (\<forall>e2 e2'. {e2, e2'} \<subseteq> sset ts \<longrightarrow> touchedSuperT e2 = touchedSuperT e2')" 
      because this would fail to prove the Vr case (where, as Mazza also notes, the lemma reneqv_tr' is essential). 
  *)
  from t txs show ?thesis proof (binder_induction t avoiding: xs ts rule: strong_induct_good')
    case bsmall
    then show ?case unfolding bsmall_def 0
      by (metis g bsmall_def finite_Un good_finite_touchedSuperT super_bsmall t2 touchedSuperT_def txs(1))
  next
    case (iVr ys x)
    then show ?case apply auto 
      apply (metis bot.extremum imkSubst_def insert_subset 
       reneqvS_def reneqv_tr' shd_sset snth_sset sup.idem super_subOf_theN_eq uniformS_def3)
      by (metis dtheN fst_conv imkSubst_idle snd_conv theSN' theSN_ex tr'_iVr)
  next
    case (iLm e xsa)
    then show ?case apply(subst tr'_iLm)
      apply auto apply(subst ILterm.subst(3))
        subgoal by auto 
        subgoal apply(rule uniformS_touchedSuper_IImsupp_imkSubst''[where e = "shd ts"])
          using shd_sset super_touchedSuper_dsset by fastforce+
        subgoal apply(subst Lterm.subst(3))
          subgoal by auto subgoal apply(rule IImsupp_Vr') 
          apply simp by (metis (no_types, lifting) FFVars_tr' Int_Un_emptyI1 
           Int_Un_emptyI2 Int_absorb UN_I disjoint_iff empty_not_insert shd_sset 
           superOf_subOf super_touchedSuper_dsset touchedSuper_emp uniformS_good)      
          subgoal apply(subst tr'_iLm) 
            subgoal by auto
            subgoal using g good_imkSubst by auto
            subgoal by auto . . .
  next
    case (iAp e1 es2)
    then show ?case apply(subst tr'_iAp)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal apply(subst ILterm.subst(2))
      subgoal by auto
      subgoal apply(subst tr'_iAp)
        subgoal using g good_imkSubst by auto
        subgoal using g good_imkSubst by auto
        subgoal apply clarsimp  apply (simp add: touchedSuperT_itvsubst ) 
        apply(drule uniformS_good) subgoal for e2 e2'  
        by (metis FFVars_touchedSuperT_imkSubst_UN) .
        subgoal using shd_sset by fastforce . . .
  qed
qed


(* Theorem 19 from Mazza (his main theorem): *)
(* Theorem 19(1): *)
lemma tr'_tr: "tr' (tr e p) = e"
apply(induct e arbitrary: p) 
  subgoal for x p apply simp apply(subst tr'_iVr[of "superOf x"]) 
    subgoal by auto
    subgoal by (simp add: dsset_range)
    subgoal by (metis fst_eqD subOf_superOf super_superOf theSN theSN_ex) .
  subgoal apply simp apply(subst tr'_iAp_uniform) 
    subgoal by blast
    subgoal unfolding uniformS_def4 by auto
    subgoal by auto .
  subgoal by simp .

(* Theorem 19(2): *)
(* We again need "good" induction for the same reason: because 
structural induction does not take 
care of the supervariable assumptiin in the lambda-case. But this 
time regular induction works, no need fresh induction like before. 
Note also that "uniform t" is also needed in the induction, otherwise 
the iAp case does not go through. 
*)
lemma tr_tr': 
assumes t: "uniform t"
shows "reneqv (tr (tr' t) p) t" 
proof-
have tt: "good t" using uniform_good[OF t] .
show ?thesis using tt t
apply(induct arbitrary: p rule: good.induct) 
  subgoal for xs x p apply clarsimp  
    apply(rule reneqv.iVr[of xs]) 
    by auto (metis dsset_range rangeI subsetD superOf_subOf super_dsset_RSuper 
       super_subOf_theN_eq theSN') 
  subgoal for xs t p apply(subst tr'_iLm) 
    subgoal by simp
    subgoal by simp
    subgoal apply simp apply(rule reneqv.iLm) by auto .
  subgoal for t1 ts p apply(subst tr'_iAp) 
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal apply simp apply(rule reneqv.iAp) 
      subgoal unfolding uniform_iAp_iff by auto
      subgoal unfolding sset_range image_def  
      by simp (smt (verit, ccfv_threshold) bot.extremum insert_subset reneqv_trans 
         reneqv_sym snth.simps(1) snth_sset uniform_iAp_case uniform_iAp_iff) . . .
qed


(* *)

lemma tr'_hred_red: 
assumes ttt: "hred t tt" and t: "uniform t"
shows "red (tr' t) (tr' tt)"
using ttt t unfolding red_def hred_def2[OF t] 
by (metis reneqv_iAp_iff tr'_iAp_uniform tr'_iLm_uniform tr'_itvsubst_good_uniformS 
   uniformS_def4 uniform_def3 uniform_iLm_iff)

lemma tr'_hred_red2: 
assumes "uniformS ts" "stream_all2 hred ts ts'"
shows "stream_all2 red (smap tr' ts) (smap tr' ts')"
using assms unfolding stream_all2_iff_snth 
by (simp add: tr'_hred_red uniformS_sset_uniform)

(* *)
(* Theorem 19(3): *)
lemma stepD_ustepD: "stepD d e ee \<Longrightarrow> 
  \<exists>ts. ustepD d (smap (tr e) ps) ts \<and> 
       stream_all2 reneqv ts (smap (tr ee) ps)"
proof(induct arbitrary: ps rule: stepD.induct)
  case (Beta x e1 e2 ps)
  define qs where qs: "qs \<equiv> \<lambda>p. smap (\<lambda>n. tr e2 (p @ [Suc n])) nats"
  term "smap (\<lambda>p. itvsubst (imkSubst (superOf x) (smap (tr e2) ps)) (tr e1 p)) ps"
  thm tr_tvsubst_Vr_reneqv'
  show ?case apply(intro exI[of _ 
   "smap (\<lambda>p. itvsubst (imkSubst (superOf x) (smap (\<lambda>n. tr e2 (p @ [Suc n])) nats)) (tr e1 (p @ [0]))) ps"] conjI)
    subgoal apply simp apply(rule ustepD.Beta)
      subgoal unfolding uniformS_def4 apply clarsimp
      apply(rule reneqv.iAp) 
        subgoal apply(rule reneqv.iLm) using reneqv_tr by auto
        subgoal by auto . 
      subgoal unfolding stream_all2_iff_snth hred_def by auto .
    subgoal unfolding stream_all2_iff_snth apply auto subgoal for i 
    (* Below I put undefined because the choice of the position stream does not matter *)
    apply(rule reneqv_trans[OF tr_tvsubst_Vr_reneqv'[of x e2 e1 "ps !! i" undefined "ps !! i @ [0]"], 
        THEN reneqv_sym]) apply(rule reneqv_imkSubst)
    unfolding reneqvS_def by auto . .    
next
  case (ApL d e1 e1' e2 ps) 
  have 0: "smap (\<lambda>p. iAp (tr e1 (p @ [0])) (smap (\<lambda>n. tr e2 (p @ [Suc n])) nats)) ps 
    = smap2 iAp (smap (\<lambda>p. tr e1 (p @ [0])) ps) 
      (smap (\<lambda>p. smap (\<lambda>n. tr e2 (p @ [Suc n])) nats) ps)" 
  by (auto simp: stream_eq_nth)
  define qs where qs: "qs = smap (\<lambda>p. p @ [0]) ps"
  obtain tts where tts: "ustepD d (smap (tr e1) qs) tts" 
  "stream_all2 reneqv tts (smap (tr e1') qs)" using ApL(2)[of qs] by auto
  define tts' where "tts' = smap2 iAp tts
      (smap (\<lambda>p. smap (\<lambda>n. tr e2 (p @ [Suc n])) nats) ps)"  
  show ?case apply simp apply(intro exI[of _ tts'] conjI) unfolding tts'_def
    subgoal unfolding 0 apply(rule ustepD.iApL)
      subgoal unfolding uniformS_sflat by auto
      subgoal using tts(1) unfolding qs unfolding stream.map_comp o_def . .
    subgoal unfolding stream_all2_iff_snth apply auto
    apply(rule reneqv.iAp)
      subgoal using tts(2) unfolding stream_all2_iff_snth qs by auto
      subgoal by auto . .   
next
  case (ApR d e2 e2' e1 ps)   
  have 0: "smap (\<lambda>p. iAp (tr e1 (p @ [0])) (smap (\<lambda>n. tr e2 (p @ [Suc n])) nats)) ps 
    = smap2 iAp (smap (\<lambda>p. tr e1 (p @ [0])) ps) 
      (smap (\<lambda>p. smap (\<lambda>n. tr e2 (p @ [Suc n])) nats) ps)" 
  by (auto simp: stream_eq_nth)

  define qss where qss: "qss = smap (\<lambda>p. smap (\<lambda>n. p @ [Suc n]) nats) ps" 
  have 333: "smap (smap (tr e2)) qss = smap (\<lambda>p. smap (\<lambda>n. tr e2 (p @ [Suc n])) nats) ps"
  unfolding stream_eq_nth qss by auto
  define qs :: "nat list stream" where qs: "qs = sflat qss"

  have 33: "smap (tr e2) qs = sflat (smap (\<lambda>p. smap (\<lambda>n. tr e2 (p @ [Suc n])) nats) ps)"
  unfolding qs smap_sflat 333 ..

  from ApR  obtain tts where 
  tts: "ustepD d (smap (tr e2) qs) tts" "stream_all2 reneqv tts (smap (tr e2') qs)"
  by auto

  obtain ttss where 22: "tts = sflat ttss" using ex_sflat by blast
  have 222: "\<And> i j. ttss !! i !! j = tts !! (nat1 (i,j))"
  unfolding 22 by (simp add: snth_sflat)

  define tts' where "tts' = smap2 iAp (smap (\<lambda>p. tr e1 (p @ [0])) ps) ttss"  
  show ?case apply simp apply(intro exI[of _ tts'] conjI) unfolding tts'_def
    subgoal unfolding 0 apply(rule ustepD.iApR)
      subgoal unfolding uniformS_def4 by auto
      subgoal using tts(1) unfolding 22 33 . .
    subgoal unfolding stream_all2_iff_snth apply auto
    apply(rule reneqv.iAp)
      subgoal unfolding stream_all2_iff_snth by auto
      subgoal unfolding sset_range image_def  
      unfolding 222 using tts(1,2) unfolding stream_all2_iff_snth    
      apply simp using reneqv_sym reneqv_trans by blast+ . .
next
  case (Xi d e e' x)
  then obtain tts where tts: "ustepD d (smap (tr e) ps) tts" "stream_all2 reneqv tts (smap (tr e') ps)"
  by auto
  have 0: "smap (\<lambda>p. iLm (superOf x) (tr e p)) ps = 
           smap (iLm (superOf x)) (smap (tr e) ps)"
  unfolding stream_eq_nth by auto
  show ?case apply(intro exI[of _ "smap (iLm (superOf x)) tts"] conjI)
    subgoal apply simp unfolding 0 apply(rule ustepD.Xi) using tts(1) by auto
    subgoal using tts(2) unfolding stream_all2_iff_snth by (auto intro: reneqv.iLm) .
qed


(* Theorem 19(4) (generalized for our (necessarily stream-based) version of 
uniform step (see previous discussion, when introducing ustepD, for why) *)
lemma ustepD_stepD: "ustepD d ts ss \<Longrightarrow> stream_all2 (stepD d) (smap tr' ts) (smap tr' ss)"
proof(induct rule: ustepD.induct)
  case (Beta es es')
  then show ?case using red_stepD2 tr'_hred_red2 by blast
next
  case (iApL ess d es es')
  then show ?case unfolding stream_all2_iff_snth  apply clarsimp subgoal for i
    apply(subst tr'_iAp_uniform)
      subgoal using snth_sset uniformS_sset_uniform ustepD_uniformS by blast
      subgoal unfolding uniformS_sflat unfolding uniformS_def4 sset_range by auto
      apply(subst tr'_iAp_uniform)
        subgoal using snth_sset uniformS_sset_uniform ustepD_uniformS by blast
        subgoal unfolding uniformS_sflat unfolding uniformS_def4 sset_range by auto
        subgoal apply(rule stepD.ApL) by auto . .
next
  case (iApR es d ess ess')
  then show ?case unfolding stream_all2_iff_snth  apply clarsimp subgoal for i
    apply(subst tr'_iAp_uniform)
      subgoal using snth_sset uniformS_sset_uniform ustepD_uniformS by blast
      subgoal unfolding uniformS_sflat unfolding uniformS_def4 sset_range image_def 
      by simp (metis snth2.simps uniformS_sflat ustepD_uniformS)
      apply(subst tr'_iAp_uniform)
        subgoal using snth_sset uniformS_sset_uniform ustepD_uniformS by blast
        subgoal unfolding uniformS_sflat unfolding uniformS_def4 sset_range image_def 
        by simp (metis snth2.simps uniformS_sflat ustepD_uniformS)
        subgoal apply(rule stepD.ApR) unfolding snth_sflat  
        by (metis nat2_nat1 snth.simps(1) snth2.simps) . .
next
  case (Xi xs d es es')
  then show ?case unfolding stream_all2_iff_snth apply clarsimp subgoal for i
    apply(subst tr'_iLm_uniform)
      subgoal by simp
      subgoal using snth_sset uniformS_sset_uniform ustepD_uniformS by blast
      subgoal apply(subst tr'_iLm_uniform)
        subgoal by simp
        subgoal using snth_sset uniformS_sset_uniform ustepD_uniformS by blast
      subgoal apply(rule stepD.Xi) by auto . . .
qed


(* *)


lemma usetpD_snth_eq: 
"ustepD d ts ss \<Longrightarrow> snth ts i = snth ts j \<Longrightarrow> snth ss i = snth ss j"
apply(induct arbitrary: i j rule: ustepD.induct)
  subgoal unfolding stream_all2_iff_snth using hred_determ by metis
  subgoal by (metis iAp_inject snth_smap2)  
  subgoal apply simp unfolding snth_sflat  
    by (metis nat2_nat1 snth2.simps stream_eq_nth)
  subgoal by (metis iLm_same_inject snth_smap) .

(* Closer to how Mazza defines things informally, namely
he only "paralelizes" the definition in the iApR case 
(without acknowledging though that parallelization should happen hereditarily): 
 *)
inductive ustepD' :: "nat \<Rightarrow> ilterm \<Rightarrow> ilterm \<Rightarrow> bool" where
  Beta: "uniform e \<Longrightarrow> hred e e' \<Longrightarrow> ustepD' 0 e e'"
| iApL: "uniformS es \<Longrightarrow> ustepD' d e e' \<Longrightarrow> ustepD' (Suc d) (iAp e es) (iAp e' es)"
| iApR: "uniform e \<Longrightarrow> ustepD d es es' \<Longrightarrow> ustepD' (Suc d) (iAp e es) (iAp e es')"
| Xi: "super xs \<Longrightarrow> ustepD' d e e' \<Longrightarrow> ustepD' d (iLm xs e) (iLm xs e')"


lemma uniformS_sconst: "uniformS (sconst e) \<longleftrightarrow> uniform e"
unfolding uniformS_def4 uniform_def3 by auto

lemma stream_all2_sconst: "stream_all2 R (sconst a) (sconst b) \<longleftrightarrow> R a b"
unfolding stream_all2_iff_snth by auto

lemma sconst_iAp: "sconst (iAp e es) = smap2 iAp (sconst e) (sconst es)"
unfolding stream_eq_nth by auto

lemma sconst_iLm: "sconst (iLm xs e) = smap (iLm xs) (sconst e)"
unfolding stream_eq_nth by auto

lemma snth_sflat_scons: "snth (sflat (sconst es)) k = snth es (snd (nat2 k))"
unfolding snth_sflat by (cases "nat2 k", auto)

(* This brings home the intuition that uniform reduction takes place synchronously 
on all the elements of the stream; namely, no matter how these are shuffled, 
the reduction predicate holds. 
*)
lemma usetpD_snth_shuffle: 
assumes 1: "ustepD d es es'"
shows "ustepD d (smap (\<lambda>i. es !! (f i)) nats) (smap (\<lambda>i. es' !! (f i)) nats)"
using 1 proof(induct arbitrary: f rule: ustepD.induct)
  case (Beta es es')
  then show ?case 
  apply(intro ustepD.Beta) 
  unfolding uniformS_def4 stream_all2_iff_snth sset_range image_def
  by auto
next
  case (iApL ess d es es' f)
  have 0: "\<And> es ess. smap (\<lambda>i. smap2 iAp es ess !! f i) nats = 
                      smap2 iAp (smap (\<lambda>i. es !! f i) nats) (smap (\<lambda>i. ess !! f i) nats)"
  unfolding stream_eq_nth by auto
  show ?case unfolding 0 apply(rule ustepD.iApL)
    subgoal using iApL(1) unfolding uniformS_sflat by auto
    subgoal using iApL(3) . .
next
  case (iApR es d ess ess' f)
  have 0: "\<And> es ess. smap (\<lambda>i. smap2 iAp es ess !! f i) nats = 
                      smap2 iAp (smap (\<lambda>i. es !! f i) nats) (smap (\<lambda>i. ess !! f i) nats)"
  unfolding stream_eq_nth by auto
  define g where g: "g \<equiv> \<lambda>k. nat1 (case nat2 k of (i,j) \<Rightarrow> (f i, j))"
  have 1: "\<And> ess j. snth (sflat (smap (\<lambda>i. ess !! f i) nats)) j = snth (smap (\<lambda>i. sflat ess !! g i) nats) j"
  unfolding g snth_sflat subgoal for ees k by (cases "nat2 k", auto) .
  hence 1: "\<And> ess. sflat (smap (\<lambda>i. ess !! f i) nats) = smap (\<lambda>i. sflat ess !! g i) nats" 
  unfolding stream_eq_nth by auto
  show ?case unfolding 0 apply(rule ustepD.iApR)
    subgoal using iApR(1) unfolding uniformS_def4 by auto
    subgoal using iApR(3) unfolding 1 . .
next
  case (Xi xs d es es' f)
  have 0: "\<And> xs es. smap (\<lambda>i. smap (iLm xs) es !! f i) nats = 
                     smap (iLm xs) (smap (\<lambda>i. es !! f i) nats)"
  unfolding stream_eq_nth by auto
  show ?case unfolding 0 apply(rule ustepD.Xi)
    subgoal using Xi(1) unfolding uniformS_sflat by auto
    subgoal using Xi(3) . .
qed


lemma ustepD_sflat_sconst:
"ustepD d es es' \<Longrightarrow> ustepD d (sflat (sconst es)) (sflat (sconst es'))"
apply(drule usetpD_snth_shuffle[where f = "\<lambda>k. snd (nat2 k)"])
unfolding snth_sflat_scons[symmetric] by (metis stream_smap_nats)

lemma ustepD'_ustepD_sconst: 
"ustepD' d e e' \<Longrightarrow> ustepD d (sconst e) (sconst e')"
apply(induct rule: ustepD'.induct)
  subgoal apply(rule ustepD.Beta) unfolding uniformS_sconst stream_all2_sconst by auto 
  subgoal unfolding sconst_iAp apply(rule ustepD.iApL) 
  unfolding uniformS_sflat unfolding uniformS_def4  
  by fastforce
  subgoal for e d es es' unfolding sconst_iAp apply(rule ustepD.iApR) 
  unfolding uniformS_def4 uniform_def3  
    subgoal by auto
    subgoal (* this requires ustepD_sflat_sconst , which would not easily go by induction, 
     so I was led to the shuffling generalization usetpD_snth_shuffle *)
    using ustepD_sflat_sconst by auto .
  subgoal unfolding sconst_iLm apply(rule ustepD.Xi) 
  unfolding uniformS_def4 uniform_def3 by fastforce+ .

(* For the converse direction (from ustepD t ustepD') we need another consequence of 
our shuffling generalization: *)
lemma snth_snth_sflat: "snth (snth ess i) j = snth (sflat ess) (nat1 (i,j))"
unfolding snth_sflat by auto

lemma ustepD_sflat_snth: 
"ustepD d (sflat ess) (sflat ess') \<Longrightarrow> ustepD d (ess !! i) (ess' !! i)"
apply(drule usetpD_snth_shuffle[where f = "\<lambda>j. nat1 (i,j)"])
unfolding snth_sflat by simp (metis stream_smap_nats)

lemma ustepD_ustepD'_snth: 
"ustepD d es es' \<Longrightarrow> ustepD' d (snth es i) (snth es' i)"
apply(induct arbitrary: i rule: ustepD.induct)
  subgoal apply(rule ustepD'.Beta) unfolding uniformS_def4 stream_all2_iff_snth uniform_def3 by auto
  subgoal for ess d es es' i unfolding snth_smap2 apply(rule ustepD'.iApL) 
  unfolding uniformS_def4 stream_all2_iff_snth uniform_def3 sset_range image_def snth_sflat 
  by simp (metis nat2_nat1 snth2.simps)
  subgoal for es d ess ess' i unfolding snth_smap2 apply(rule ustepD'.iApR)   
  unfolding uniformS_def4 stream_all2_iff_snth uniform_def3 sset_range image_def snth_sflat 
    subgoal by auto
    subgoal (* here we need the shuffling lemma's "other" consequence, ustepD_sflat_snth: *)
    using ustepD_sflat_snth by auto .
  subgoal unfolding snth_smap apply(rule ustepD'.Xi) by auto .


(* Now Theorem 19(3,4) exactly in Mazza's formulations: *)

(* Theorem 19(4)*)
lemma ustepD'_stepD: "ustepD' d t s \<Longrightarrow> stepD d (tr' t) (tr' s)" 
apply(drule ustepD'_ustepD_sconst)
apply(drule ustepD_stepD)  
by (simp add: smap_sconst stream_all2_sconst)

(* Theorem 19(3): *)
lemma stepD_ustepD': "stepD d e ee \<Longrightarrow> 
  \<exists>t. ustepD' d (tr e p) t \<and> reneqv t (tr ee p)"  
apply(drule stepD_ustepD[of _ _ _ "sconst p"]) apply safe
subgoal for ts apply(rule exI[of _ "snth ts 0"]) apply safe
  subgoal apply(drule ustepD_ustepD'_snth[of _ _ _ 0]) by simp
  subgoal unfolding stream_all2_iff_snth  
  by simp (metis snth.simps(1)) . .


end