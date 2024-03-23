theory Pi_cong
  imports Commitment
begin

(* Structural congurence *)
inductive cong :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "(\<equiv>\<^sub>\<pi>)" 40) where
  "P = Q \<Longrightarrow> P \<equiv>\<^sub>\<pi> Q"
| "Par P Q \<equiv>\<^sub>\<pi> Par Q P"
| "Par (Par P Q) R \<equiv>\<^sub>\<pi> Par P (Par Q R)"
| "Par P Zero \<equiv>\<^sub>\<pi> P"
| "x \<noteq> y \<Longrightarrow> Res x (Res y P) \<equiv>\<^sub>\<pi> Res y (Res x P)"
| "Res x Zero \<equiv>\<^sub>\<pi> Zero"
| "Bang P \<equiv>\<^sub>\<pi> Par P (Bang P)"
| "x \<notin> FFVars Q \<Longrightarrow> Res x (Par P Q) \<equiv>\<^sub>\<pi> Par (Res x P) Q"

thm cong_def

(* INSTANTIATING THE Components LOCALE: *)

type_synonym T = "trm \<times> trm"
type_synonym V = "var list" 


definition Tmap :: "(var \<Rightarrow> var) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> map_prod (rrename f) (rrename f)"

fun Tfvars :: "T \<Rightarrow> var set" where 
"Tfvars (e1,e2) = FFVars e1 \<union> FFVars e2"

(*
definition Vmap :: "(var \<Rightarrow> var) \<Rightarrow> V \<Rightarrow> V" where 
"Vmap \<equiv> map"

fun Vfvars :: "V \<Rightarrow> var set" where 
"Vfvars v = set v"
*)

interpretation Components where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars
apply standard unfolding ssbij_def Tmap_def 
  using small_Un small_def term.card_of_FFVars_bounds
  apply (auto simp: term.rrename_id0s map_prod.comp term.rrename_comp0s inf_A) 
  by blast

definition G :: "var set \<Rightarrow> (T \<Rightarrow> bool) \<Rightarrow> T \<Rightarrow> bool" where
  "G \<equiv> \<lambda>B p t.
    (\<exists>P Q. B = {} \<and> fst t = P \<and> snd t = Q \<and> P = Q) \<or>
    (\<exists>P Q. B = {} \<and> fst t = Par P Q \<and> snd t = Par Q P) \<or>
    (\<exists>P Q R. B = {} \<and> fst t = Par (Par P Q) R \<and> snd t = Par P (Par Q R)) \<or>
    (\<exists>P. B = {} \<and> fst t = Par P Zero \<and> snd t = P) \<or>
    (\<exists>x y P. B = {x, y} \<and> fst t = Res x (Res y P) \<and> snd t = Res y (Res x P) \<and> x \<noteq> y) \<or>
    (\<exists>x. B = {x} \<and> fst t = Res x Zero \<and> snd t = Zero) \<or>
    (\<exists>P. B = {} \<and> fst t = Bang P \<and> snd t = Par P (Bang P)) \<or>
    (\<exists>x Q P. B = {x} \<and> fst t = Res x (Par P Q) \<and> snd t = Par (Res x P) Q \<and> x \<notin> FFVars Q)"

lemma GG_mono: "R \<le> R' \<Longrightarrow> G v R t \<Longrightarrow> G v R' t"
  unfolding G_def by force

lemma GG_equiv: "ssbij \<sigma> \<Longrightarrow> small B \<Longrightarrow> G B R t \<Longrightarrow> G (image \<sigma> B) (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Tmap \<sigma> t)"
  unfolding G_def
  by (elim disj_forward exE; cases t)
    (auto simp: Tmap_def ssbij_def term.rrename_comps
         | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
         | ((rule exI[of _ "\<sigma> _"])+; auto))+

(* same proofs as for transition *)
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

lemma ssbij_swap: "ssbij (id(x := y, y := x))"
  by (auto simp: ssbij_def)

lemma R_forw_subst: "R (x, y) \<Longrightarrow> (\<And>x y. R (x, y) \<Longrightarrow> R (f x, g y)) \<Longrightarrow> z = g y \<Longrightarrow> R (f x, z)"
  by blast

lemma G_refresh: 
  assumes "(\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t))"
  shows "small B \<Longrightarrow> G B R t \<Longrightarrow> \<exists>C. small C \<and> C \<inter> Tfvars t = {} \<and> G C R t"
unfolding G_def
(**)ssbij_def conj_assoc[symmetric]
unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib ex_simps(1,2)[symmetric]
    ex_comm[where P = P for P :: "_ set \<Rightarrow> _ \<Rightarrow> _"]
apply (elim disj_forward exE; simp; clarsimp)
        apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl])
        | (erule (1) R_forw_subst[of R, OF _ assms[unfolded Tmap_def, simplified, rule_format, OF conjI[OF ssbij_swap]]]; simp?)
        | (cases t; auto simp only: fst_conv snd_conv Tfvars.simps term.set))+) [3]
  done

interpretation Cong: Induct where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars and G = G
apply standard 
  using GG_mono GG_equiv G_refresh by auto

lemma cong_I: "(t1 \<equiv>\<^sub>\<pi> t2) = Cong.I (t1, t2)"
  unfolding cong_def Cong.I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
  unfolding fun_eq_iff G_def apply clarify
  subgoal for R PP QQ apply(rule iffI)
    subgoal apply(elim disjE exE)
      subgoal by force
      subgoal for P Q by force
      subgoal for P Q R by force
      subgoal by force
      subgoal for x y P by (metis fst_conv small_two snd_conv)
      subgoal by auto
      subgoal for P by simp
      subgoal for x P Q by auto
      done
    subgoal apply(elim conjE disjE exE)
             apply force+
      done
    done
  done

(* FROM ABSTRACT BACK TO CONCRETE: *)
thm cong.induct[of P C \<phi>, no_vars]

corollary strong_induct_cong[consumes 2]:
  assumes
    par: "\<And>p. small (Pfvars p)"
  and cg: "P \<equiv>\<^sub>\<pi> Q"
  and rules: "\<And>P Q p. P = Q \<Longrightarrow> \<phi> P Q p"
"\<And>P Q p. \<phi> (Par P Q) (Par Q P) p"
"\<And>P Q R p. \<phi> (Par (Par P Q) R) (Par P (Par Q R)) p"
"\<And>P p. \<phi> (Par P Zero) P p"
"\<And>x y P p. {x, y} \<inter> Pfvars p = {} \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<phi> (Res x (Res y P)) (Res y (Res x P)) p"
"\<And>x p. x \<notin> Pfvars p \<Longrightarrow> \<phi> (Res x Zero) Zero p"
"\<And>P p. \<phi> (Bang P) (Par P (Bang P)) p"
"\<And>x Q P p. x \<notin> Pfvars p \<Longrightarrow> x \<notin> FFVars Q \<Longrightarrow> \<phi> (Res x (Par P Q)) (Par (Res x P) Q) p"
shows "\<phi> P Q p"
  apply(subgoal_tac "case (P,Q) of (P, Q) \<Rightarrow> \<phi> P Q p")
  subgoal by simp
  subgoal using par cg apply(elim Cong.strong_induct[where R = "\<lambda>p (P,Q). \<phi> P Q p"])
    subgoal unfolding cong_I by simp
    subgoal for p v t apply(subst (asm) G_def) 
      unfolding cong_I[symmetric] apply(elim disjE exE)
      subgoal using rules(1) by force
      subgoal using rules(2) by force
      subgoal using rules(3) by force
      subgoal using rules(4) by force
      subgoal using rules(5) by force
      subgoal using rules(6) by force
      subgoal using rules(7) by force
      subgoal using rules(8) by force
      done
    done
  done

(* Also inferring equivariance from the general infrastructure: *)
corollary rrename_cong:
assumes f: "bij f" "|supp f| <o |UNIV::var set|" 
and r: "P \<equiv>\<^sub>\<pi> Q" 
shows "rrename f P \<equiv>\<^sub>\<pi> rrename f Q"
using assms unfolding cong_I using Cong.I_equiv[of "(P,Q)" f]
unfolding Tmap_def ssbij_def by auto

inductive trans :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "(\<rightarrow>)" 30) where
  "Par (Out x z P) (Inp x y Q) \<rightarrow> Par P (usub Q z y)"
| "P \<rightarrow> Q \<Longrightarrow> Par P R \<rightarrow> Par P Q"
| "P \<rightarrow> Q \<Longrightarrow> Res x P \<rightarrow> Res x Q"
| "P \<equiv>\<^sub>\<pi> P' \<Longrightarrow> P' \<rightarrow> Q' \<Longrightarrow> Q' \<equiv>\<^sub>\<pi> Q \<Longrightarrow> P \<rightarrow> Q"

thm trans_def

definition G_trans :: "var set \<Rightarrow> (T \<Rightarrow> bool) \<Rightarrow> T \<Rightarrow> bool" where
  "G_trans \<equiv> \<lambda>B p t.
    (\<exists>x z P y Q. B = {y} \<and> fst t = Par (Out x z P) (Inp x y Q) \<and> snd t = Par P (usub Q z y)) \<or>
    (\<exists>P Q R. B = {} \<and> fst t = Par P R \<and> snd t = Par P Q \<and> p (P, Q)) \<or>
    (\<exists>P Q x. B = {x} \<and> fst t = Res x P \<and> snd t = Res x Q \<and> p (P, Q)) \<or>
    (\<exists>P P' Q' Q. B = {} \<and> fst t = P \<and> snd t = Q \<and> (P \<equiv>\<^sub>\<pi> P') \<and> p (P', Q') \<and> (Q' \<equiv>\<^sub>\<pi> Q))"

lemma GG_trans_mono: "R \<le> R' \<Longrightarrow> G_trans v R t \<Longrightarrow> G_trans v R' t"
  unfolding G_trans_def by blast

lemma GG_trans_equiv: "ssbij \<sigma> \<Longrightarrow> small B \<Longrightarrow> G_trans B R t \<Longrightarrow> G_trans (image \<sigma> B) (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Tmap \<sigma> t)"
  unfolding G_trans_def
  apply (elim disj_forward exE; cases t)
  apply  (auto simp: Tmap_def ssbij_def term.rrename_comps
         | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
         | ((rule exI[of _ "\<sigma> _"])+; auto))+
  by (metis Pi_cong.rrename_cong bij_imp_inv' term.rrename_bijs term.rrename_inv_simps)

lemma G_trans_refresh: 
  assumes "(\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t))"
  shows "small B \<Longrightarrow> G_trans B R t \<Longrightarrow> \<exists>C. small C \<and> C \<inter> Tfvars t = {} \<and> G_trans C R t"
unfolding G_trans_def
(**)ssbij_def conj_assoc[symmetric]
  unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib ex_simps(1,2)[symmetric]
    ex_comm[where P = P for P :: "_ set \<Rightarrow> _ \<Rightarrow> _"]
  apply (elim disj_forward exE; simp; clarsimp)
  apply (cases t; auto simp only: fst_conv snd_conv Tfvars.simps term.set)
  subgoal for x z P y Q
    apply (rule exE[OF exists_fresh[of "[x, y, z]" "[(P, Q)]"]])
    subgoal for w
      apply (rule exI[of _ w])
      apply simp
      by (meson Inp_refresh usub_refresh)
    done
  apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl])
        | (erule (1) R_forw_subst[of R, OF _ assms[unfolded Tmap_def, simplified, rule_format, OF conjI[OF ssbij_swap]]]; simp?)
        | (cases t; auto simp only: fst_conv snd_conv Tfvars.simps term.set))+)
  done

interpretation Trans: Induct where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars and G = G_trans
apply standard 
  using GG_trans_mono GG_trans_equiv G_trans_refresh by auto

lemma trans_I: "trans t1 t2 = Trans.I (t1,t2)"
unfolding trans_def Trans.I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
  unfolding fun_eq_iff G_trans_def apply clarify
subgoal for R PP QQ apply(rule iffI)
  subgoal apply(elim disjE exE)
    subgoal by fastforce
    subgoal by force
    subgoal by force
    subgoal by force
    done
  subgoal apply(elim disjE exE)
    subgoal by fastforce
    done
  done
  done

thm trans.induct[of P Q \<phi>, no_vars]

corollary strong_induct_trans[consumes 2]:
  assumes par: "\<And>p. small (Pfvars p)"
  and tr: "trans P Q"
  and rules:
  "\<And>x z P y Q p. y \<notin> Pfvars p \<Longrightarrow> \<phi> (Par (Out x z P) (Inp x y Q)) (Par P (usub Q z y)) p"
  "\<And>P Q R p. P \<rightarrow> Q \<Longrightarrow> (\<And>p. \<phi> P Q p) \<Longrightarrow> \<phi> (Par P R) (Par P Q) p"
  "\<And>P Q x p. x \<notin> Pfvars p \<Longrightarrow> P \<rightarrow> Q \<Longrightarrow> (\<And>p. \<phi> P Q p) \<Longrightarrow> \<phi> (Res x P) (Res x Q) p"
  "\<And>P P' Q' Q p. P \<equiv>\<^sub>\<pi> P' \<Longrightarrow> P' \<rightarrow> Q' \<Longrightarrow> (\<And>p. \<phi> P' Q' p) \<Longrightarrow> Q' \<equiv>\<^sub>\<pi> Q \<Longrightarrow> \<phi> P Q p"
shows "\<phi> P Q p"
apply(subgoal_tac "case (P,Q) of (P, Q) \<Rightarrow> \<phi> P Q p")
  subgoal by simp
  subgoal using par tr apply(elim Trans.strong_induct[where R = "\<lambda>p (P,Q). \<phi> P Q p"])
    subgoal unfolding trans_I by simp
    subgoal for p v t apply(subst (asm) G_trans_def) 
      unfolding trans_I[symmetric] apply(elim disjE exE)
      subgoal using rules(1) by auto
      subgoal using rules(2) by auto
      subgoal using rules(3) by auto
      subgoal using rules(4) by auto
      done
    done
  done

(* Also inferring equivariance from the general infrastructure: *)
corollary rrename_trans:
assumes f: "bij f" "|supp f| <o |UNIV::var set|" 
and r: "trans P Q" 
shows "trans (rrename f P) (rrename f Q)"
using assms unfolding trans_I using Trans.I_equiv[of "(P,Q)" f]
unfolding Tmap_def ssbij_def by auto

end