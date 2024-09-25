theory Pi_Transition_Early
  imports Pi_Transition_Common
begin

inductive trans :: "trm \<Rightarrow> cmt \<Rightarrow> bool" where
  InpE: "trans (Inp a x P) (Finp a y (P[y/x]))"
| ComLeftE: "\<lbrakk> trans P (Finp a x P') ; trans Q (Fout a x Q') \<rbrakk> \<Longrightarrow> trans (P \<parallel> Q) (Tau (P' \<parallel> Q'))"
| CloseLeftE: "\<lbrakk> trans P (Finp a x P') ; trans Q (Bout a x Q') ; x \<notin> {a} \<union> FFVars P \<rbrakk> \<Longrightarrow> trans (P \<parallel> Q) (Tau (Res x (P' \<parallel> Q')))"
| Open: "\<lbrakk> trans P (Fout a x P') ; a \<noteq> x \<rbrakk> \<Longrightarrow> trans (Res x P) (Bout a x P')"
| ScopeFree: "\<lbrakk> trans P (Cmt \<alpha> P') ; fra \<alpha> ; x \<notin> ns \<alpha> \<rbrakk> \<Longrightarrow> trans (Res x P) (Cmt \<alpha> (Res x P'))"
| ScopeBound: "\<lbrakk> trans P (Bout a x P') ; y \<notin> {a, x} ; x \<notin> FFVars P \<union> {a} \<rbrakk> \<Longrightarrow> trans (Res y P) (Bout a x (Res y P'))"
| ParLeft: "\<lbrakk> trans P (Cmt \<alpha> P') ; bns \<alpha> \<inter> (FFVars P \<union> FFVars Q) = {} \<rbrakk> \<Longrightarrow> trans (P \<parallel> Q) (Cmt \<alpha> (P' \<parallel> Q))"

lemma Bout_inject: "(Bout x y t = Bout x' y' t') \<longleftrightarrow>
  x = x' \<and>
  (\<exists>f. bij f \<and> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set|
  \<and> id_on (FFVars_term t - {y}) f \<and> f y = y' \<and> rrename_term f t = t')"
  by (auto 0 4 simp: id_on_def intro!: exI[of _ "id(y:=y', y':=y)"] rrename_cong)
declare Bout_inj[simp del]

lemma ns_alt: "ns \<alpha> = bns \<alpha> \<union> fns \<alpha>"
  by (cases \<alpha>) auto

lemma vars_alt: "vars \<alpha> = bns \<alpha> \<union> fns \<alpha>"
  by (cases \<alpha>) auto

(*
lemma Cmt_inject: "(Cmt \<alpha> t = Cmt \<alpha>' t') \<longleftrightarrow>
  (\<exists>f. bij f \<and> |supp (f::var \<Rightarrow> var)| <o |UNIV::var set|
  \<and> id_on (fvars \<alpha> \<union> (FFVars t - bvars \<alpha>)) f \<and> map_action f \<alpha> = \<alpha>' \<and> rrename_term f t = t')"
  apply (cases \<alpha>; cases \<alpha>')
                      apply (auto simp: Bout_inject intro!: term.rrename_cong_ids[symmetric] elim!: id_onD)
  sorry
*)
fun rrename_action where
  "rrename_action f (finp x y) = finp x y"
| "rrename_action f (fout x y) = fout x y"
| "rrename_action f (bout x y) = bout x (f y)"
| "rrename_action f (binp x y) = binp x (f y)"
| "rrename_action f tau = tau"


lemma bvars_rrename_action[simp]: "bvars (rrename_action f \<alpha>) = f ` bvars \<alpha>"
  by (cases \<alpha>) auto

lemma Cmt_rename_action: "bij (f :: var \<Rightarrow> var) \<Longrightarrow> |supp f| <o |UNIV :: var set| \<Longrightarrow> id_on (FFVars P - bvars \<alpha>) f \<Longrightarrow>
  Cmt \<alpha> P = Cmt (rrename_action f \<alpha>) (rrename f P)"
  by (cases \<alpha>)
    (force simp: Bout_inject id_on_def intro!: exI[of _ f] term.rrename_cong_ids[symmetric] rrename_cong)+

lemma Cmt_rename_action_Par: "bij (f :: var \<Rightarrow> var) \<Longrightarrow> |supp f| <o |UNIV :: var set| \<Longrightarrow> id_on (FFVars P \<union> FFVars Q - bvars \<alpha>) f \<Longrightarrow>
  Cmt \<alpha> (P \<parallel> Q) = Cmt (rrename_action f \<alpha>) (rrename f P \<parallel> rrename f Q)"
  by (subst Cmt_rename_action[of f]) auto

lemma "R Paa (Cmt \<alpha>' P'a) \<Longrightarrow>
    bvars \<alpha>' \<inter> (FFVars Paa \<union> FFVars Qaa) = {} \<Longrightarrow>
    R (rrename xa Paa) (rrename_commit xa (Cmt \<alpha>' P'a)) \<Longrightarrow>
    bij xa \<Longrightarrow>
    |supp xa| <o |UNIV :: var set| \<Longrightarrow>
    xa ` bvars \<alpha>' \<inter> bvars \<alpha>' = {} \<Longrightarrow>
    xa ` bvars \<alpha>' \<inter> FFVars (Paa \<parallel> Qaa) = {} \<Longrightarrow>
    xa ` bvars \<alpha>' \<inter> FFVars_commit (Cmt \<alpha>' (P'a \<parallel> Qaa)) = {} \<Longrightarrow>
    xa ` bvars \<alpha>' \<inter> FFVars Paa = {} \<Longrightarrow>
    xa ` bvars \<alpha>' \<inter> FFVars_commit (Cmt \<alpha>' P'a) = {} \<Longrightarrow>
    id_on (Tsupp (Paa \<parallel> Qaa) (Cmt \<alpha>' (P'a \<parallel> Qaa)) \<union> Tsupp Paa (Cmt \<alpha>' P'a) - bvars \<alpha>')
     xa \<Longrightarrow>
    \<forall>x. xa (xa x) = x \<Longrightarrow>
    xa ` bvars \<alpha>' = bvars (rrename_action xa \<alpha>') \<and>
    Paa \<parallel> Qaa = Paa \<parallel> rrename xa Qaa \<and>
    Cmt \<alpha>' (P'a \<parallel> Qaa) = Cmt (rrename_action xa \<alpha>') (rrename xa P'a \<parallel> rrename xa Qaa) \<and>
    R Paa (Cmt (rrename_action xa \<alpha>') (rrename xa P'a)) \<and>
    bvars (rrename_action xa \<alpha>') \<inter> FFVars Paa = {} \<and>
    bvars (rrename_action xa \<alpha>') \<inter> FFVars (rrename xa Qaa) = {} "
      apply (auto 0 10 simp: FFVars_commit_Cmt Int_Un_distrib intro!: exI[of _ xa] intro!: term.rrename_cong_ids[symmetric] Cmt_rename_action Cmt_rename_action_Par elim!: id_onD
        cong[OF cong[OF refl[of R] refl], THEN iffD1, rotated -1, of _ _ "Cmt _ _"] id_on_antimono)
(*  apply (subst Cmt_rename_action[of xa])
     apply (auto elim!: id_on_antimono)
*)
  done
  

binder_inductive trans
  subgoal for R B \<sigma> x1 x2
    apply simp
    apply (elim disj_forward)
    by (auto simp: isPerm_def
        term.rrename_comps action.map_comp action.map_id
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | (rule exI[of _ "map_action \<sigma> _"])
        | (rule exI[of _ "rrename \<sigma> _"])
        | ((rule exI[of _ "\<sigma> _"])+; auto))+
  subgoal premises prems for R B P Q
(*
    apply (tactic \<open>refreshability_tac true
      [@{term "FFVars :: trm \<Rightarrow> var set"}, @{term "FFVars_commit :: cmt \<Rightarrow> var set"}]
      [@{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"}, @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"},
       @{term "rrename_action :: (var \<Rightarrow> var) \<Rightarrow> var action \<Rightarrow> var action"}]
      [SOME [NONE, SOME 1, SOME 0, NONE],
       NONE,
       SOME [NONE, NONE, SOME 1, SOME 0, NONE, SOME 0],
       SOME [SOME 0, NONE, SOME 1, SOME 0],
       SOME [SOME 0, NONE, SOME 0, SOME 1],
       SOME [SOME 0, NONE, SOME 1, SOME 0, SOME 1],
       SOME [NONE, SOME 2, SOME 0, SOME 0]]
      @{thm prems(3)} @{thm prems(2)} @{thms }
      @{thms emp_bound singl_bound insert_bound card_of_minus_bound term.Un_bound term.card_of_FFVars_bounds commit_internal.card_of_FFVars_bounds infinite_UNIV bns_bound}
      @{thms Res_inject Inp_inject Bout_inject FFVars_commit_Cmt ns_alt vars_alt}
      @{thms Inp_eq_usub term.rrename_cong_ids term.rrename_cong_ids[symmetric] arg_cong2[where f=Cmt] action.map_ident_strong cong[OF arg_cong2[OF _ refl] refl, of _ _ Bout]
         Cmt_rename_action Cmt_rename_action_Par}
      @{thms cong[OF cong[OF refl[of R] refl], THEN iffD1, rotated -1, of _ _ "Bout _ _ _"] id_onD id_on_antimono
             cong[OF cong[OF refl[of R] refl], THEN iffD1, rotated -1, of _ _ "Fout _ _ _"]
             cong[OF cong[OF refl[of R] refl], THEN iffD1, rotated -1, of _ _ "Cmt _ _"]
             cong[OF cong[OF refl[of R] term.rrename_cong_ids], THEN iffD1, rotated -1, of _ _ _ "Finp _ _ _"]} @{context}\<close>)
*)
  proof -
    define G where "G \<equiv> \<lambda>B p x1 x2.
                (\<exists>a x P y. B = {x} \<and> x1 = Inp a x P \<and> x2 = Finp a y (P[y/x])) \<or>
                (\<exists>P a x P' Q Q'. B = {} \<and> x1 = P \<parallel> Q \<and> x2 = Tau (P' \<parallel> Q') \<and> p P (Finp a x P') \<and> p Q (Fout a x Q')) \<or>
                (\<exists>P a x P' Q Q'. B = {x} \<and> x1 = P \<parallel> Q \<and> x2 = Tau (Res x (P' \<parallel> Q')) \<and> p P (Finp a x P') \<and> p Q (Bout a x Q') \<and> x \<notin> {a} \<union> FFVars P) \<or>
                (\<exists>P a x P'. B = {x} \<and> x1 = Res x P \<and> x2 = Bout a x P' \<and> p P (Fout a x P') \<and> a \<noteq> x) \<or>
                (\<exists>P \<alpha> P' x. B = insert x (bvars \<alpha>) \<and> x1 = Res x P \<and> x2 = Cmt \<alpha> (Res x P') \<and> p P (Cmt \<alpha> P') \<and> fra \<alpha> \<and> x \<notin> ns \<alpha>) \<or>
                (\<exists>P a x P' y. B = {x, y} \<and> x1 = Res y P \<and> x2 = Bout a x (Res y P') \<and> p P (Bout a x P') \<and> y \<notin> {a, x} \<and> x \<notin> FFVars P \<union> {a}) \<or>
                (\<exists>P \<alpha> P' Q. B = bvars \<alpha> \<and> x1 = P \<parallel> Q \<and> x2 = Cmt \<alpha> (P' \<parallel> Q) \<and> p P (Cmt \<alpha> P') \<and> bvars \<alpha> \<inter> (FFVars P \<union> FFVars Q) = {})"
    { assume assms: "(\<forall>\<sigma> x1 x2. isPerm \<sigma> \<and> R x1 x2 \<longrightarrow> R (rrename \<sigma> x1) (rrename_commit \<sigma> x2))"
      have "G B R P Q \<Longrightarrow> \<exists>C. C \<inter> Tsupp P Q = {} \<and> G C R P Q"
        unfolding G_def
          (**)isPerm_def conj_assoc[symmetric]
        unfolding ex_push_inwards conj_disj_distribL ex_disj_distrib ex_simps(1,2)[symmetric]
          ex_comm[where P = P for P :: "_ set \<Rightarrow> _ \<Rightarrow> _"]
        apply (elim disj_forward exE; simp; tactic \<open>REPEAT_DETERM_N 2 (gen_fresh @{context} [] [] [@{term P}, @{term Q}])\<close>; clarsimp)
              apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl])
               | (erule (1) R_forw_subst[of R, OF _ assms[simplified, rule_format, OF conjI[OF isPerm_swap]]]; simp?)
               | (auto simp only: fst_conv snd_conv term.set FFVars_commit_simps FFVars_commit_Cmt act_var_simps))+)[2]
              apply (metis Inp_refresh usub_refresh)
             apply (metis Inp_refresh usub_refresh)

        subgoal for P1 a x P1' P2 P2' z1 z2
          apply (rule exI[of _ a])
          apply (rule exI[of _ z1])
          apply (rule conjI) apply assumption
          apply safe
          apply (rule exI[of _ "swap P1' x z1"])
          apply (rule exI[of _ "swap P2' x z1"])
          apply (intro conjI)
              apply (simp add: Res_refresh[of z1 "Par P1' P2'" x])
             apply (drule assms[simplified, rule_format, OF conjI[OF isPerm_swap], of _ _ x z1])
             apply simp
            apply (drule assms[simplified, rule_format, OF conjI[OF isPerm_swap], of _ _ x z1])
            apply simp
            apply (metis Bout_inj)
          apply assumption+
          done

           apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl])
              | (erule (1) R_forw_subst[of R, OF _ assms[simplified, rule_format, OF conjI[OF isPerm_swap]]]; simp?)
              | (auto simp only: fst_conv snd_conv term.set FFVars_commit_simps FFVars_commit_Cmt act_var_simps))+) [1]
        apply (simp_all add: Bout_inj)
        apply (smt (verit) Diff_disjoint Diff_empty FFVars_commit_Cmt Int_Un_eq(3) Un_empty Un_iff action.simps(65) action.simps(66) action.simps(68) action.simps(69) bns.simps(1) empty_bvars_vars_fvars insert_disjoint(2) insert_not_empty ns.elims term.set(8))

        subgoal for P a x P' y z1 z2
          apply (rule exI[of _ "swap P y z1"])
          apply (rule exI[of _ a])
          apply (rule exI[of _ z2])
          apply (rule conjI) apply simp
          apply (rule exI[of _ "swap (swap P' x z2) y z1"])
          apply (rule exI[of _ z1])
          apply (rule conjI) apply simp
          apply clarsimp
          apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl] refl)))
           apply auto[]
          apply (rule conjI[OF sym])
           apply ((((rule exI conjI)+)?, (assumption | rule Inp_refresh Res_refresh usub_refresh arg_cong2[where f=Cmt, OF refl] refl)))
          apply simp
           apply (smt (verit, best) image_iff sw_diff sw_eqR)
          apply (rule conjI)
           apply (erule (1) R_forw_subst[of R, OF _ assms[simplified, rule_format, OF conjI[OF isPerm_swap]]]; (simp add: Bout_inj)?)
           apply (rule conjI)
            apply (smt (verit, best) image_iff sw_diff sw_eqR)
           apply (simp add: swap_commute term.rrename_comps[where w="swap P' y z1"] supp_comp_bound[OF _ _ infinite_UNIV]
              term.rrename_cong_ids[symmetric])
          apply (smt (verit, best) image_iff sw_diff sw_eqR)
          done

        subgoal for P1 act P1' P2 z1 z2
          using bvars_act_bout[of act]
          apply (elim disjE exE)
            apply (rule exI[of _ act])
            apply auto
          subgoal for a b
            apply (intro exI[of _ "bout a z1"] conjI)
              apply simp
             apply simp
            apply (intro exI[of _ "swap P1' b z1"] conjI)
              apply (simp add: Bout_inj)
             apply (simp add: Bout_inj)
             apply (metis Bout_inj)
            apply simp
            done

          subgoal for a b
            apply (intro exI[of _ "binp a z1"] conjI)
             apply simp+
             apply (metis Binp_inj)
            done
          done
        done
    } note 1 = this
    then show ?thesis using prems(2,3) unfolding G_def isPerm_def by simp
    qed
  done
print_theorems

thm trans.strong_induct

end
