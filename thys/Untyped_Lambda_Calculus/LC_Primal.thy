(* Here we instantiate the general enhanced rule induction to beta reduction
for the (untyped) lambda-calculus *)
theory LC_Primal
imports LC "Binders.Generic_Barendregt_Enhanced_Rule_Induction" "Prelim.Curry_LFP" "Prelim.More_Stream" "HOL-Computational_Algebra.Primes"
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)
inductive print :: "trm \<Rightarrow> string \<Rightarrow> bool" where
  "print (Var (Variable x)) [char_of x]"
| "print t1 s1 \<Longrightarrow> print t2 s2 \<Longrightarrow> print (App t1 t2) (''('' @ s1 @ '' '' @ s2 @ '')'')"
| "Variable y \<notin> FFVars t - {x} \<Longrightarrow> print (sswap t x (Variable y)) s \<Longrightarrow>
    print (Lam x t) (''(%'' @ [char_of y] @ ''. '' @ s @ '')'')"

(* *)

primrec prime_var where
  "prime_var (Variable x) = prime x"

inductive primal :: "trm \<Rightarrow> bool" where
  Var: "prime_var x \<Longrightarrow> primal (Var x)"
| App: "primal e1 \<Longrightarrow> primal e2 \<Longrightarrow> primal (App e1 e2)"
| Lam: "prime_var x \<Longrightarrow> primal e \<Longrightarrow> primal  (Lam x e)"

definition G
where
"G \<equiv> \<lambda>B R e.
   (\<exists>x. B = None \<and> e = Var x \<and> prime_var x) \<or>
   (\<exists>e1 e2. B = None \<and> e = App e1 e2 \<and> R e1 \<and> R e2) \<or>
   (\<exists>x e'. B = Some x \<and> e = Lam x e' \<and> prime_var x \<and> R e')"

lemma finite_set_option[simp]: "finite (set_option x)"
  by (cases x) auto

interpretation CComponents where 
Tperm = permute_term and
Tsupp = FVars_term and
Bperm = map_option and
Bsupp = set_option and
bnd = "pred_option prime_var" and
bsmall = "\<lambda>_. True"
  apply standard
  apply (auto simp add: term.permute_id0 term.permute_comp0 term.set_bd_UNIV
    isPerm_def small_def card_set_var
    option.map_id0 option.map_comp fun_eq_iff option.set_map
    intro!: option.map_ident_strong finite_card_var)
  done

lemma presBnd_alt: "presBnd \<sigma> \<longleftrightarrow> (\<forall>x. prime_var (\<sigma> x) \<longleftrightarrow> prime_var x)"
  unfolding presBnd_def by (auto simp: option.pred_set)

lemma infinite_prime_var: "infinite {x. prime_var x}"
  apply (rule contrapos_nn[OF primes_infinite])
  apply (erule finite_surj[of _ _ "\<lambda>x. case x of Variable x \<Rightarrow> x"])
  apply (auto simp: image_def split: var.splits)
  done

lemma refresh_prime_var:
  assumes"prime_var a" "small A" "B \<subseteq> A" "a \<notin> B"
  shows "\<exists>\<rho>. isPerm \<rho> \<and> presBnd \<rho> \<and> \<rho> a \<notin> A \<and> id_on B \<rho>"
proof -
  from assms(1,2) obtain b where "prime_var b" "b \<notin> insert a A"
    apply atomize_elim
    apply (simp add: small_def ls_UNIV_iff_finite)
    apply (drule Diff_infinite_finite[OF finite_insert[THEN iffD2, of _ a] infinite_prime_var])
    apply (smt (verit, best) Collect_mono Diff_eq_empty_iff finite.simps insert_compr)
    done
  then show ?thesis
    apply -
    apply (rule exI[of _ "a \<leftrightarrow> b"])
    apply (auto simp: isPerm_def presBnd_alt assms(1,4) set_mp[OF assms(3)] id_on_def)
      apply (metis assms(1) swap_def)
     apply (metis assms(1) swap_def)
    by (metis assms(3,4) subsetD swap_simps(3))
qed

interpretation Step: IInduct where
Tperm = rrename and
Tsupp = FFVars and
Bperm = map_option and
Bsupp = set_option and
bnd = "pred_option prime_var" and
bsmall = "\<lambda>_. True" and
GG = G
  apply standard
  subgoal for R R' x e
    by (auto simp: G_def)
  subgoal for \<sigma> R x e
    unfolding presBnd_alt isPerm_def
    apply (auto simp: G_def term.permute_comp)
    by (metis inv_simp1 term.permute_bij term.permute_inv_simp)+
  subgoal
    by (auto simp: G_def)
  subgoal for x A B
    apply (cases x)
     apply (auto simp: isPerm_id intro: exI[of _ id] refresh_prime_var)
    done
  subgoal
    by simp
  subgoal for R x e
    apply (cases x)
     apply (auto simp: G_def)
    apply blast
    done
  done

lemma primal_II: "primal e = Step.II e"
  unfolding primal_def Step.II_def
  apply (rule arg_cong2[of _ _ _ _ lfp]; simp add: fun_eq_iff G_def)
  apply clarify
  apply force
  done

lemma primal_param_induct[consumes 2, case_names Var App Lam]:
"(\<And>p. small (Psupp p)) \<Longrightarrow>
primal x \<Longrightarrow>
(\<And>x p. prime_var x \<Longrightarrow> P p (Var x)) \<Longrightarrow>
(\<And>e1 e2 p. primal e1 \<Longrightarrow> P p e1 \<Longrightarrow> primal e2 \<Longrightarrow> P p e2 \<Longrightarrow> P p (App e1 e2)) \<Longrightarrow>
(\<And>x e p. x \<notin> Psupp p \<Longrightarrow> prime_var x \<Longrightarrow> primal e \<Longrightarrow> P p e \<Longrightarrow> P p (Lam x e)) \<Longrightarrow>
P p x"
  apply (erule Step.BE_iinduct[simplified])
   apply (fold primal_II)
   apply assumption
  apply (auto simp: G_def)
  done

lemma primal_avoid_induct[consumes 2, case_names Var App Lam]:
"small A \<Longrightarrow>
primal x \<Longrightarrow>
(\<And>x p. prime_var x \<Longrightarrow> P (Var x)) \<Longrightarrow>
(\<And>e1 e2 p. primal e1 \<Longrightarrow> P e1 \<Longrightarrow> primal e2 \<Longrightarrow> P e2 \<Longrightarrow> P (App e1 e2)) \<Longrightarrow>
(\<And>x e p. x \<notin> A \<Longrightarrow> prime_var x \<Longrightarrow> primal e \<Longrightarrow> P e \<Longrightarrow> P (Lam x e)) \<Longrightarrow>
P x"
  by (rule primal_param_induct[where P = "\<lambda>_. P" and Psupp = "\<lambda>_. A"])

lemma small_IImsupp_SSupp: "small (IImsupp f) \<Longrightarrow> small (SSupp f)"
  by (metis IImsupp_def card_of_subset_bound small_def sup_ge1)

lemma primal_tvsubst:
  "small (IImsupp f) \<Longrightarrow> primal t \<Longrightarrow> (\<forall>x. prime_var x \<longrightarrow> primal (f x)) \<Longrightarrow> primal (tvsubst f t)"
  apply (rule primal_avoid_induct[where P = "\<lambda>t. primal (tvsubst f t)"])
  apply assumption
  apply assumption
    apply (auto simp: small_def dest!: small_IImsupp_SSupp[unfolded small_def] intro: primal.intros)
  done

end