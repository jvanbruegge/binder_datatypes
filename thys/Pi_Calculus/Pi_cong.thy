theory Pi_cong
  imports Commitment
begin

type_synonym T = "trm \<times> trm"
type_synonym V = "var list" 


fun Tperm :: "(var \<Rightarrow> var) \<Rightarrow> T \<Rightarrow> T" where 
  "Tperm f = map_prod (rrename f) (rrename f)"

fun Tsupp :: "T \<Rightarrow> var set" where 
  "Tsupp (e1,e2) = FFVars e1 \<union> FFVars e2"

lemma fresh: "\<exists>xx. xx \<notin> Tsupp (t :: trm \<times> trm)"
  using Tsupp.simps[of "fst t" "snd t"] unfolding prod.collapse
  by (metis (no_types, lifting) exists_var finite_iff_le_card_var term.Un_bound term.set_bd_UNIV)

(* Structural congurence *)
binder_inductive cong :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "(\<equiv>\<^sub>\<pi>)" 40) where
  "P = Q \<Longrightarrow> P \<equiv>\<^sub>\<pi> Q"
| "Par P Q \<equiv>\<^sub>\<pi> Par Q P"
| "Par (Par P Q) R \<equiv>\<^sub>\<pi> Par P (Par Q R)"
| "Par P Zero \<equiv>\<^sub>\<pi> P"
| "x \<noteq> y \<Longrightarrow> Res x (Res y P) \<equiv>\<^sub>\<pi> Res y (Res x P)" binds "{x, y}"
| "Res x Zero \<equiv>\<^sub>\<pi> Zero" binds "{x}"
| "Bang P \<equiv>\<^sub>\<pi> Par P (Bang P)"
| "x \<notin> FFVars Q \<Longrightarrow> Res x (Par P Q) \<equiv>\<^sub>\<pi> Par (Res x P) Q" binds "{x}"
where perm: Tperm supp: Tsupp
         apply (auto simp: o_def split_beta term.rrename_comps fun_eq_iff isPerm_def
      small_def term.card_of_FFVars_bounds term.Un_bound) [6]
  subgoal for \<sigma> R B t
    apply (cases t)
    apply simp
    by (elim disj_forward case_prodE)
      (auto simp: isPerm_def term.rrename_comps
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | ((rule exI[of _ "\<sigma> _"])+; auto))+
  subgoal premises prems for R B t
    apply (cases t)
    apply simp
    using fresh[of t] prems(2-) unfolding
      (**)isPerm_def conj_assoc[symmetric] split_beta
    unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib
    apply (elim disj_forward exE; simp)
      apply ((rule exI, rule conjI[rotated], assumption) |
        (((rule exI conjI)+)?, rule Res_refresh) |
        (cases t; auto))+
    done
  done

(* FROM ABSTRACT BACK TO CONCRETE: *)
thm cong.induct[of P C \<phi>, no_vars]

corollary strong_induct_cong[consumes 2]:
  assumes
    par: "\<And>p. small (Psupp p)"
    and cg: "P \<equiv>\<^sub>\<pi> Q"
    and rules: "\<And>P Q p. P = Q \<Longrightarrow> \<phi> P Q p"
    "\<And>P Q p. \<phi> (Par P Q) (Par Q P) p"
    "\<And>P Q R p. \<phi> (Par (Par P Q) R) (Par P (Par Q R)) p"
    "\<And>P p. \<phi> (Par P Zero) P p"
    "\<And>x y P p. {x, y} \<inter> Psupp p = {} \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<phi> (Res x (Res y P)) (Res y (Res x P)) p"
    "\<And>x p. x \<notin> Psupp p \<Longrightarrow> \<phi> (Res x Zero) Zero p"
    "\<And>P p. \<phi> (Bang P) (Par P (Bang P)) p"
    "\<And>x Q P p. x \<notin> Psupp p \<Longrightarrow> x \<notin> FFVars Q \<Longrightarrow> \<phi> (Res x (Par P Q)) (Par (Res x P) Q) p"
  shows "\<phi> P Q p"
  apply(subgoal_tac "case (P,Q) of (P, Q) \<Rightarrow> \<phi> P Q p")
  subgoal by simp
  subgoal using par cg apply(elim cong.strong_induct[where R = "\<lambda>p (P,Q). \<phi> P Q p"])
    subgoal using cong.alt_def by blast
    subgoal for p v t
      apply (cases t)
      apply simp
      by (meson disjoint_single rules(1) rules(2) rules(3) rules(4) rules(5) rules(6) rules(7) rules(8))
    done
  done

(* Also inferring equivariance from the general infrastructure: *)
corollary rrename_cong:
  assumes f: "bij f" "|supp f| <o |UNIV::var set|" 
    and r: "P \<equiv>\<^sub>\<pi> Q" 
  shows "rrename f P \<equiv>\<^sub>\<pi> rrename f Q"
  using assms unfolding cong.alt_def using cong.equiv[of "(P,Q)" f]
  unfolding Tperm.simps isPerm_def by auto

lemma finite_Tsupp: "finite (Tsupp t)"
  by (metis FFVars_commit_simps(5) Tsupp.simps finite_FFVars_commit finite_Un prod.collapse)

lemma exists_fresh:
  "\<exists> z. z \<notin> set xs \<and> (\<forall>t \<in> set ts. z \<notin> Tsupp t)"
proof-
  have 0: "|set xs \<union> \<Union> (Tsupp ` (set ts))| <o |UNIV::var set|"
    unfolding ls_UNIV_iff_finite
    using finite_Tsupp by blast
  then obtain x where "x \<notin> set xs \<union> \<Union> (Tsupp ` (set ts))"
    by (meson ex_new_if_finite finite_iff_le_card_var
        infinite_iff_natLeq_ordLeq var_term_pre_class.large)
  thus ?thesis by auto
qed

lemma R_forw_subst: "R (x, y) \<Longrightarrow> (\<And>x y. R (x, y) \<Longrightarrow> R (f x, g y)) \<Longrightarrow> z = g y \<Longrightarrow> R (f x, z)"
  by blast
lemma isPerm_swap: "isPerm (id(x := y, y := x))"
  by (auto simp: isPerm_def MRBNF_FP.supp_swap_bound infinite_UNIV)

binder_inductive trans :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "(\<rightarrow>)" 30) where
  "Par (Out x z P) (Inp x y Q) \<rightarrow> Par P (usub Q z y)" binds "{y}"
| "P \<rightarrow> Q \<Longrightarrow> Par P R \<rightarrow> Par P Q"
| "P \<rightarrow> Q \<Longrightarrow> Res x P \<rightarrow> Res x Q" binds "{x}"
| "P \<equiv>\<^sub>\<pi> P' \<Longrightarrow> P' \<rightarrow> Q' \<Longrightarrow> Q' \<equiv>\<^sub>\<pi> Q \<Longrightarrow> P \<rightarrow> Q"
where perm: Tperm supp: Tsupp
         apply (auto simp: o_def split_beta term.rrename_comps fun_eq_iff isPerm_def
      small_def term.card_of_FFVars_bounds term.Un_bound) [6]
  subgoal for \<sigma> R B t
    apply (cases t)
    apply simp
    apply (elim disj_forward exE; cases t)
       apply  (auto simp: isPerm_def term.rrename_comps
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | ((rule exI[of _ "\<sigma> _"])+; auto))+
    by (metis Pi_cong.rrename_cong bij_imp_inv' term.rrename_bijs term.rrename_inv_simps)
  subgoal premises prems for R B t
  proof -
    define G_trans where "G_trans \<equiv> \<lambda>B p t.
                (\<exists>x z P y Q. B = {y} \<and> fst t = Out x z P \<parallel> Inp x y Q \<and> snd t = P \<parallel> Q[z/y]) \<or>
                (\<exists>P Q R. B = {} \<and> fst t = P \<parallel> R \<and> snd t = P \<parallel> Q \<and> p (P, Q)) \<or>
                (\<exists>P Q x. B = {x} \<and> fst t = Res x P \<and> snd t = Res x Q \<and> p (P, Q)) \<or> (\<exists>P P' Q' Q. B = {} \<and> fst t = P \<and> snd t = Q \<and> P \<equiv>\<^sub>\<pi> P' \<and> p (P', Q') \<and> Q' \<equiv>\<^sub>\<pi> Q)"
    { assume assms: "(\<forall>\<sigma> t. isPerm \<sigma> \<and> R t \<longrightarrow> R (Tperm \<sigma> t))"
      have "small B \<Longrightarrow> G_trans B R t \<Longrightarrow> \<exists>C. small C \<and> C \<inter> Tsupp t = {} \<and> G_trans C R t"
        unfolding G_trans_def isPerm_def conj_assoc[symmetric]
        unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib ex_simps(1,2)[symmetric]
          ex_comm[where P = P for P :: "_ set \<Rightarrow> _ \<Rightarrow> _"]
        apply (elim disj_forward exE; simp; clarsimp)
          apply (cases t; auto simp only: fst_conv snd_conv Tsupp.simps term.set)
        subgoal for x z P y Q
          apply (rule exE[OF exists_fresh[of "[x, y, z]" "[(P, Q)]"]])
          subgoal for w
            apply (rule exI[of _ w])
            apply simp
            by (meson Inp_refresh usub_refresh)
          done
         apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl])
              | (erule (1) R_forw_subst[of R, OF _ assms[unfolded Tperm.simps, simplified, rule_format, OF conjI[OF isPerm_swap]]]; simp?)
              | (cases t; auto simp only: fst_conv snd_conv Tsupp.simps term.set))+)
        done
    }
    then show ?thesis unfolding G_trans_def using prems by force
  qed
  done

thm trans.induct[of P Q \<phi>, no_vars]

corollary strong_induct_trans[consumes 2]:
  assumes par: "\<And>p. small (Psupp p)"
    and tr: "trans P Q"
    and rules:
    "\<And>x z P y Q p. y \<notin> Psupp p \<Longrightarrow> \<phi> (Par (Out x z P) (Inp x y Q)) (Par P (usub Q z y)) p"
    "\<And>P Q R p. P \<rightarrow> Q \<Longrightarrow> (\<And>p. \<phi> P Q p) \<Longrightarrow> \<phi> (Par P R) (Par P Q) p"
    "\<And>P Q x p. x \<notin> Psupp p \<Longrightarrow> P \<rightarrow> Q \<Longrightarrow> (\<And>p. \<phi> P Q p) \<Longrightarrow> \<phi> (Res x P) (Res x Q) p"
    "\<And>P P' Q' Q p. P \<equiv>\<^sub>\<pi> P' \<Longrightarrow> P' \<rightarrow> Q' \<Longrightarrow> (\<And>p. \<phi> P' Q' p) \<Longrightarrow> Q' \<equiv>\<^sub>\<pi> Q \<Longrightarrow> \<phi> P Q p"
  shows "\<phi> P Q p"
  apply(subgoal_tac "case (P,Q) of (P, Q) \<Rightarrow> \<phi> P Q p")
  subgoal by simp
  subgoal using par tr apply(elim trans.strong_induct[where R = "\<lambda>p (P,Q). \<phi> P Q p"])
    subgoal unfolding trans.alt_def by blast
    subgoal for p v t
      apply (cases t)
      apply simp
      apply(elim disjE exE)
      subgoal using rules(1) by auto
      subgoal using rules(2) trans.alt_def[symmetric] by auto
      subgoal using rules(3) trans.alt_def[symmetric] by auto
      subgoal using rules(4) trans.alt_def[symmetric] by auto
      done
    done
  done

(* Also inferring equivariance from the general infrastructure: *)
corollary rrename_trans:
  assumes f: "bij f" "|supp f| <o |UNIV::var set|" 
    and r: "trans P Q" 
  shows "trans (rrename f P) (rrename f Q)"
  using assms unfolding cong.alt_def using cong.equiv[of "(P,Q)" f]
  using isPerm_def trans.alt_def trans.equiv by fastforce

end