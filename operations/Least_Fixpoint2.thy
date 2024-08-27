theory Least_Fixpoint2
  imports "Binders.MRBNF_Composition" "Binders.MRBNF_FP"
begin

declare [[mrbnf_internals]]

(*
binder_datatype 'a term =
  Var 'a
| App "'a term" "'a term"
| Lam2 x::'a t::"'a term" x2::'a t2::"'a term" binds x in t, binds x2 in t t2
*)

ML \<open>
val ctor_T1_Ts = [
  [@{typ 'var}],
  [@{typ 'rec}, @{typ 'rec}],
  [@{typ 'b1}, @{typ "'brec1"}, @{typ 'b2}, @{typ "'brec2"}]
]
\<close>

ML \<open>
val T1 = BNF_FP_Util.mk_sumprodT_balanced ctor_T1_Ts
val name1 = "term";
val rel = [[([], [0]), ([], [0, 1])]];
Multithreading.parallel_proofs := 4
\<close>

declare [[quick_and_dirty]]
declare [[ML_print_depth=1000]]
declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val Xs = map dest_TFree []
  val resBs = map dest_TFree [@{typ 'var}, @{typ 'b1}, @{typ 'b2}, @{typ 'brec1}, @{typ 'brec2}, @{typ 'rec}]

  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify1 = Binding.prefix_name (name1 ^ "_pre_")
  val accum = (MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds)

  (* Step 1: Create pre-MRBNF *)
  val ((mrbnf1, tys1), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline qualify1 flatten_tyargs Xs []
    [(dest_TFree @{typ 'var}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'b1}, MRBNF_Def.Bound_Var),
      (dest_TFree @{typ 'b2}, MRBNF_Def.Bound_Var)] T1
    (accum, lthy)
  val _ = @{print} "comp"

  (* Step 2: Seal the pre-MRBNF with a typedef *)
  val ((mrbnf1, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name (name1 ^ "_pre")) true (fst tys1) [] mrbnf1 lthy
  val _ = @{print} "seal"

  (* Step 3: Register the pre-MRBNF as a BNF in its live variables *)
  val (bnf1, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf1 lthy
  val _ = @{print} "register"
in lthy end
\<close>
print_theorems
print_mrbnfs

declare [[quick_and_dirty=false]]

lemmas infinite_UNIV = cinfinite_imp_infinite[OF term_pre.UNIV_cinfinite]


(********************** BINDER FIXPOINT CONSTRUCTION **************************************)

typ "('a, 'b1, 'b2, 'brec1, 'brec2, 'rec) term_pre"

datatype ('a::var_term_pre) raw_term = raw_term_ctor "('a, 'a, 'a, 'a raw_term, 'a raw_term, 'a raw_term) term_pre"

primrec permute_raw_term :: "('a::var_term_pre \<Rightarrow> 'a) \<Rightarrow> 'a raw_term \<Rightarrow> 'a raw_term" where
  "permute_raw_term f (raw_term_ctor x) = raw_term_ctor (map_term_pre f f f id id id (
    map_term_pre id id id (permute_raw_term f) (permute_raw_term f) (permute_raw_term f) x
  ))"

lemma permute_raw_simp:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "permute_raw_term f (raw_term_ctor x) = raw_term_ctor (map_term_pre f f f (permute_raw_term f) (permute_raw_term f) (permute_raw_term f) x)"
  apply (rule trans)
   apply (rule permute_raw_term.simps)
  apply (subst term_pre.map_comp)
      apply (rule supp_id_bound bij_id assms)+
  apply (unfold id_o o_id)
  apply (rule refl)
  done

inductive free_raw_term :: "'a::var_term_pre \<Rightarrow> 'a raw_term \<Rightarrow> bool" where
  "a \<in> set1_term_pre x \<Longrightarrow> free_raw_term a (raw_term_ctor x)"
| "z \<in> set4_term_pre x \<Longrightarrow> free_raw_term a z \<Longrightarrow> a \<notin> set2_term_pre x \<union> set3_term_pre x \<Longrightarrow> free_raw_term a (raw_term_ctor x)"
| "z \<in> set5_term_pre x \<Longrightarrow> free_raw_term a z \<Longrightarrow> a \<notin> set3_term_pre x \<Longrightarrow> free_raw_term a (raw_term_ctor x)"
| "z \<in> set6_term_pre x \<Longrightarrow> free_raw_term a z \<Longrightarrow> free_raw_term a (raw_term_ctor x)"

definition FVars_raw_term :: "'a::var_term_pre raw_term \<Rightarrow> 'a set" where
  "FVars_raw_term x \<equiv> { a. free_raw_term a x }"

coinductive alpha_term :: "'a::var_term_pre raw_term \<Rightarrow> 'a raw_term \<Rightarrow> bool" where
  "\<lbrakk> bij g ; |supp g| <o |UNIV::'a set| ; suppGr f1 \<union> suppGr f2 \<subseteq> suppGr g ;
    bij f1 ; |supp f1| <o |UNIV::'a set| ; id_on (\<Union>(FVars_raw_term ` set4_term_pre x) - (set2_term_pre x \<union> set3_term_pre x)) f1 ;
    bij f2 ; |supp f2| <o |UNIV::'a set| ; id_on (\<Union>(FVars_raw_term ` set5_term_pre x) - set3_term_pre x) f2 ;
    mr_rel_term_pre id g g (\<lambda>x. alpha_term (permute_raw_term f1 x)) (\<lambda>x. alpha_term (permute_raw_term f2 x)) alpha_term x y
  \<rbrakk> \<Longrightarrow> alpha_term (raw_term_ctor x) (raw_term_ctor y)"
monos conj_context_mono term_pre.mr_rel_mono[OF supp_id_bound]

(****************** PROOFS ******************)

lemma permute_raw_id: "permute_raw_term id x = x"
  apply (rule raw_term.induct[of _ x])
  apply (rule trans)
   apply (rule permute_raw_simp)
    apply (rule bij_id supp_id_bound)+
  apply (rule trans)
   apply (rule arg_cong[of _ _ raw_term_ctor])
   apply (rule trans[rotated])
    apply (rule term_pre.map_id)
   apply (rule term_pre.map_cong)
                   apply (rule bij_id supp_id_bound)+
         apply (rule refl trans[OF _ id_apply[symmetric]] | assumption)+
  done

lemma permute_raw_comps:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a" and g::"'a \<Rightarrow> 'a"
  assumes f_prems: "bij f" "|supp f| <o |UNIV::'a set|"
    and g_prems: "bij g" "|supp g| <o |UNIV::'a set|"
  shows "permute_raw_term f (permute_raw_term g x) = permute_raw_term (f \<circ> g) x"
  sorry

lemma permute_raw_congs:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a" and g::"'a \<Rightarrow> 'a"
  assumes f_prems: "bij f" "|supp f| <o |UNIV::'a set|"
    and g_prems: "bij g" "|supp g| <o |UNIV::'a set|"
  shows "(\<And>a. a \<in> FVars_raw_term x \<Longrightarrow> f a = g a) \<Longrightarrow> permute_raw_term f x = permute_raw_term g x"
  sorry

lemma FVars_raw_intros:
  "a \<in> set1_term_pre x \<Longrightarrow> a \<in> FVars_raw_term (raw_term_ctor x)"
  "z \<in> set4_term_pre x \<Longrightarrow> a \<in> FVars_raw_term z \<Longrightarrow> a \<notin> set2_term_pre x \<union> set3_term_pre x \<Longrightarrow> a \<in> FVars_raw_term (raw_term_ctor x)"
  "z \<in> set5_term_pre x \<Longrightarrow> a \<in> FVars_raw_term z \<Longrightarrow> a \<notin> set3_term_pre x \<Longrightarrow> a \<in> FVars_raw_term (raw_term_ctor x)"
  "z \<in> set6_term_pre x \<Longrightarrow> a \<in> FVars_raw_term z \<Longrightarrow> a \<in> FVars_raw_term (raw_term_ctor x)"
     apply (unfold FVars_raw_term_def mem_Collect_eq)
     apply (erule free_raw_term.intros | assumption)+
  done

lemma alpha_refl:
  fixes x::"'a::var_term_pre raw_term"
  shows "alpha_term x x"
proof -
  have x: "\<forall>(x::'a raw_term) y. x = y \<longrightarrow> alpha_term x y"
    apply (rule allI impI)+
    apply (erule alpha_term.coinduct)
    apply hypsubst_thin
    apply (unfold triv_forall_equality)
    subgoal for x
      apply (rule raw_term.exhaust[of x])
      apply hypsubst_thin
      apply (rule exI)+
      apply (rule conjI, rule refl supp_id_bound bij_id id_on_id)+
      apply (rule conjI)
       apply (rule subsetI)
       apply (erule UnE)+
        apply assumption+
      apply (rule conjI, rule refl supp_id_bound bij_id id_on_id)+
      apply (unfold term_pre.mr_rel_id[symmetric] permute_raw_id)
      apply (rule term_pre.rel_refl_strong)
        apply (rule disjI1 refl)+
      done
    done

  show ?thesis by (rule x[THEN spec, THEN spec, THEN mp[OF _ refl]])
qed

lemma suppGr_inv: "bij f \<Longrightarrow> bij g \<Longrightarrow> suppGr f \<subseteq> suppGr g \<Longrightarrow> suppGr (inv f) \<subseteq> suppGr (inv g)"
  unfolding suppGr_def using bij_imp_inv[of f] bij_imp_inv[of g] 
  apply auto
  subgoal 
  proof -
    fix x :: 'a
    assume a1: "bij f"
    assume a2: "bij g"
    assume a3: "{(x, f x) |x. f x \<noteq> x} \<subseteq> {(x, g x) |x. g x \<noteq> x}"
    assume "\<And>a. (inv f a = a) = (f a = a)"
    assume a4: "f x \<noteq> x"
    have "\<forall>a f. (\<exists>aa. (\<forall>ab. (aa::'a) = ab \<or> f ab \<noteq> (a::'a)) \<and> f aa = a) \<or> \<not> bij f"
      by (metis (no_types) bij_pointE)
    then obtain aa :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" and aaa :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
      f5: "\<forall>a f. (\<forall>ab. aa a f = ab \<or> f ab \<noteq> a) \<and> f (aa a f) = a \<or> \<not> bij f"
      by moura
    then have "\<exists>a. (aa x f, x) = (a, g a) \<and> g a \<noteq> a"
      using a4 a3 a1 by (smt (z3) mem_Collect_eq subset_iff)
    then show "inv f x = inv g x"
      using f5 a2 a1 by (metis (no_types) Pair_inject inv_simp1)
  qed
  by blast

lemma suppGr_comp:
  assumes "bij h1" "bij g" "bij f" "suppGr f \<subseteq> suppGr g"
  shows "suppGr (h1 \<circ> f) \<subseteq> suppGr (h1 \<circ> g)"
proof -
  { fix x
    assume a: "h1 (f x) \<noteq> x"
    have "h1 (g x) = h1 (f x)"
    proof (cases "f x = x")
      case False
      then show ?thesis using a assms(4) unfolding suppGr_def by auto
    next
      case True
      then show ?thesis sorry
    qed
  }
  then show ?thesis unfolding suppGr_def by auto
qed

lemma alpha_bij:
  fixes f::"'a::var_term_pre \<Rightarrow> 'a" and g::"'a \<Rightarrow> 'a" and f2'::"'a \<Rightarrow> 'a"
  assumes f_prems: "bij h1" "|supp h1| <o |UNIV::'a set|"
    and g_prems: "bij h2" "|supp h2| <o |UNIV::'a set|"
  shows "eq_on (FVars_raw_term x) h1 h2 \<Longrightarrow> alpha_term x y \<Longrightarrow> alpha_term (permute_raw_term h1 x) (permute_raw_term h2 y)"
proof -
  have x: "\<forall>(x::'a raw_term) y. (\<exists>x' y' f g. bij f \<and> |supp f| <o |UNIV::'a set| \<and> bij g \<and> |supp g| <o |UNIV::'a set|
    \<and> x = permute_raw_term f x' \<and> y = permute_raw_term g y' \<and> eq_on (FVars_raw_term x') f g \<and> alpha_term x' y')
    \<longrightarrow> alpha_term x y"
    apply (rule allI impI)+
    apply (erule alpha_term.coinduct)
    apply (erule exE conjE)+
    apply (erule alpha_term.cases)
    apply hypsubst
    apply (unfold triv_forall_equality)
    subgoal for h1 h2 g f1 f2 x y

      thm ex_avoiding_bij[of f1 "\<Union> (FVars_raw_term ` set5_term_pre x) - set3_term_pre x" "set3_term_pre x"]

      apply (subgoal_tac "bij f2'")
       apply (subgoal_tac "|supp (f2'::'a \<Rightarrow> 'a)| <o |UNIV::'a set|")
      apply (subgoal_tac "eq_on (\<Union> (FVars_raw_term ` set5_term_pre x)) f2' f2")
      apply (rule exI[of _ "h2 \<circ> g \<circ> inv h1"])
      apply (rule exI[of _ "h2 \<circ> f1' \<circ> inv h1"])
      apply (rule exI[of _ "h2 \<circ> f2' \<circ> inv h1"])
      apply (rule exI)+
      apply (rule conjI, rule permute_raw_simp, (rule supp_id_bound bij_id | assumption)+)+
      apply (rule conjI, (rule bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound infinite_UNIV | assumption)+)+

      apply (rule conjI[rotated])+
             apply (rule iffD2[OF term_pre.mr_rel_map(1)])
                       apply (assumption | rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV bij_imp_bij_inv supp_inv_bound)+
             apply (unfold id_o o_id)
             apply (rule iffD2[OF term_pre.mr_rel_map(3)])
                        apply (assumption | rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV bij_imp_bij_inv supp_inv_bound)+
             apply (unfold comp_assoc inv_id id_o o_id Grp_UNIV_id conversep_eq OO_eq relcompp_conversep_Grp Grp_OO)
             apply (subst inv_o_simp1, assumption)+
             apply (unfold id_o o_id comp_assoc[symmetric])
             apply (subst inv_o_simp1, assumption)+
             apply (unfold id_o o_id)
             apply (erule term_pre.mr_rel_mono_strong0[rotated -7])
        (* REPEAT_DETERM *)
                          apply (rule ballI)
                          apply (rule trans)
                          apply (rule id_apply)
                          apply (rule sym)
                          apply (rule trans[OF comp_apply])
                          apply (rule inv_f_eq[OF bij_is_inj])
                          apply assumption
                          apply (rule sym)
                          apply (erule eq_onD)
                          apply (erule FVars_raw_intros)
        (* END REPEAT_DETERM *)
                          apply (rule ballI, rule refl)+
      prefer 2
      (* REPEAT_DETERM *)
                         apply (rule ballI)
                         apply (rule ballI)
                         apply (rule impI)
      apply (rule disjI1)
                         apply (rule exI)
                         apply (rule exI)
                         apply (rule exI[of _ h2])
                         apply (rule exI[of _ h2])
                         apply (rule conjI, assumption)+
                         apply (rule conjI[rotated])+
                          apply assumption
                          apply (rule eq_on_refl)
                          apply (rule refl)
      apply (rule trans)
                          apply (rule permute_raw_comps)
                        apply (assumption | rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV bij_imp_bij_inv supp_inv_bound)+
                         apply (unfold comp_assoc)
                         apply (subst inv_o_simp1, assumption)
                         apply (unfold o_id)
                         apply (rule trans)
                          apply (rule permute_raw_comps[symmetric])
                          apply (assumption | rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV bij_imp_bij_inv supp_inv_bound)+
                         apply (rule arg_cong[of _ _ "permute_raw_term h2"])
                         apply (rule permute_raw_congs)
                          apply assumption+
                          apply (erule eq_onD)
                          apply (rule UN_I)
                          apply assumption+



qed













  