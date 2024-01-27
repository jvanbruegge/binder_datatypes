(* Here we instantiate the general enhanced rule induction to beta reduction
for the (untyped) lambda-calculus *)
theory LC_Primal
imports LC2 "Prelim.Curry_LFP" "Prelim.More_Stream" "HOL-Computational_Algebra.Primes"
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

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

interpretation CComponents where dummy = "undefined :: var" and 
Tmap = rrename_term and
Tfvars = FFVars_term and
Bmap = map_option and
Bvars = set_option and
wfB = "pred_option prime_var" and
bsmall = "\<lambda>_. True"
  apply standard
  apply (auto simp add: term.rrename_id0s term.rrename_comp0s term.set_bd_UNIV
    ssbij_def small_def card_set_var
    option.map_id0 option.map_comp fun_eq_iff option.set_map
    intro!: option.map_ident_strong finite_card_var)
  done

lemma wfBij_alt: "wfBij \<sigma> \<longleftrightarrow> (\<forall>x. prime_var (\<sigma> x) \<longleftrightarrow> prime_var x)"
  unfolding wfBij_def by (auto simp: option.pred_set)

lemma infinite_prime_var: "infinite {x. prime_var x}"
  apply (rule contrapos_nn[OF primes_infinite])
  apply (erule finite_surj[of _ _ "\<lambda>x. case x of Variable x \<Rightarrow> x"])
  apply (auto simp: image_def split: var.splits)
  done

lemma refresh_prime_var:
  assumes"prime_var a" "small A" "B \<subseteq> A" "a \<notin> B"
  shows "\<exists>\<rho>. ssbij \<rho> \<and> wfBij \<rho> \<and> \<rho> a \<notin> A \<and> id_on B \<rho>"
proof -
  from assms(1,2) obtain b where "prime_var b" "b \<notin> insert a A"
    apply atomize_elim
    apply (simp add: small_def ls_UNIV_iff_finite)
    apply (drule Diff_infinite_finite[OF finite_insert[THEN iffD2, of _ a] infinite_prime_var])
    apply (smt (verit, best) Collect_mono Diff_eq_empty_iff finite.simps insert_compr)
    done
  then show ?thesis
    apply -
    apply (rule exI[of _ "id(a := b, b := a)"])
    apply (auto simp: ssbij_def wfBij_alt assms(1,4) set_mp[OF assms(3)] id_on_def)
    done
qed

interpretation Step: IInduct where dummy = "undefined :: var" and 
Tmap = rrename and
Tfvars = FFVars and
Bmap = map_option and
Bvars = set_option and
wfB = "pred_option prime_var" and
bsmall = "\<lambda>_. True" and
GG = G
  apply standard
  subgoal for R R' x e
    by (auto simp: G_def)
  subgoal for \<sigma> R x e
    unfolding wfBij_alt ssbij_def
    by (auto simp: G_def term.rrename_comps)
  subgoal
    by (auto simp: G_def)
  subgoal for x A B
    apply (cases x)
     apply (auto simp: ssbij_id intro: exI[of _ id] refresh_prime_var)
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
"(\<And>p. small (Pfvars p)) \<Longrightarrow>
primal x \<Longrightarrow>
(\<And>x p. prime_var x \<Longrightarrow> P p (Var x)) \<Longrightarrow>
(\<And>e1 e2 p. primal e1 \<Longrightarrow> P p e1 \<Longrightarrow> primal e2 \<Longrightarrow> P p e2 \<Longrightarrow> P p (App e1 e2)) \<Longrightarrow>
(\<And>x e p. x \<notin> Pfvars p \<Longrightarrow> prime_var x \<Longrightarrow> primal e \<Longrightarrow> P p e \<Longrightarrow> P p (Lam x e)) \<Longrightarrow>
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
  by (rule primal_param_induct[where P = "\<lambda>_. P" and Pfvars = "\<lambda>_. A"])

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