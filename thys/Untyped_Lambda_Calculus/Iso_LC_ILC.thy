(* Mazza's isomorphism between affine uniform ILC and LC *)

theory Iso_LC_ILC 
imports Translation_LC_to_ILC  Translation_ILC_to_LC ILC_affine 
"HOL-Library.Sublist"
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

thm uniformS_touchedSuper_IImsupp_imkSubst[no_vars]

lemma uniformS_touchedSuper_IImsupp_imkSubst':
"super xs \<Longrightarrow> uniformS es \<Longrightarrow> e \<in> sset es \<Longrightarrow> 
  ys \<noteq> xs \<Longrightarrow> ys \<notin> touchedSuper (ILC.FFVars e) \<Longrightarrow> 
  ys \<notin> touchedSuper (ILC.IImsupp (imkSubst xs es))"
using uniformS_touchedSuper_IImsupp_imkSubst by auto

(*
lemma "super xs \<Longrightarrow> uniformS es \<Longrightarrow> e \<in> sset es \<Longrightarrow> 
 {xsa. super xsa \<and> ILC.IImsupp (imkSubst xs es) \<inter> dsset xsa \<noteq> {}} \<subseteq> 
 {xs} \<union> {xs. super xs \<and> ILC.FFVars e \<inter> dsset xs \<noteq> {}}"
*)

(* Mazza's lemma 17 *)
lemma 
assumes "\<And>i j. i \<noteq> j \<Longrightarrow> \<not> prefix (snth ps i) (snth ps j)"
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
        using App.hyps(1,2) reneqv_trans reneweqv_sym apply blast+    
        using App.hyps(2) reneqv_trans reneweqv_sym by blast .
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



end