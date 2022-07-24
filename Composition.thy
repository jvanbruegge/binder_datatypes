theory Composition
  imports "thys/MRBNF_Composition"
begin

ML \<open>
Multithreading.parallel_proofs := 0;
\<close>

datatype \<kappa> =
  Star ("\<star>")
  | KArrow \<kappa> \<kappa> (infixr "\<rightarrow>" 50)

(*
binder_datatype 'var \<tau> =
  | TyVar 'var
  | TyArrow
  | TyApp "'var \<tau>" "'var \<tau>"
  | TyForall a::"'var" \<kappa> t::"'var \<tau>" binds a in t

  \<down>

  'tyvar
+ unit
+ 'rec * 'rec
+ 'btyvar * \<kappa> * 'body
*)

declare [[ML_print_depth=10000000]]
local_setup \<open>fn lthy =>
let
  val systemf_type_name = "\<tau>_pre"
  val systemf_type = @{typ "'tyvar + unit + 'rec * 'rec + 'btyvar * \<kappa> * 'body"}
  val Xs = []
  val resBs = map dest_TFree [@{typ 'tyvar}, @{typ 'btyvar}, @{typ 'body}, @{typ 'rec}]
  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify = Binding.prefix_name (systemf_type_name ^ "_")

  val ((mrbnf, tys), (accum, lthy')) = MRBNF_Comp.mrbnf_of_typ false MRBNF_Def.Smart_Inline qualify flatten_tyargs Xs []
    [(dest_TFree @{typ 'tyvar}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'btyvar}, MRBNF_Def.Bound_Var)] systemf_type
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)
  val ((mrbnf, (Ds, info)), lthy'') = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name systemf_type_name) true (fst tys) [] mrbnf lthy'
  val (bnf, lthy''') = MRBNF_Def.register_mrbnf_as_bnf mrbnf lthy''
in lthy''' end
\<close>
print_bnfs

ML \<open>
val tau = the (MRBNF_Def.mrbnf_of @{context} "Composition.\<tau>_pre")
\<close>

ML_file \<open>Tools/mrbnf_fp_tactics.ML\<close>
ML_file \<open>Tools/mrbnf_fp.ML\<close>

ML \<open>
Multithreading.parallel_proofs := 0;
\<close>

local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Fp.construct_binder_fp MRBNF_Util.Least_FP
    [(("\<tau>", tau), 2)] [[0]] lthy
in
  lthy'
end
\<close>

print_theorems
term "\<tau>_ctor"

lemma infinite_var_\<tau>_pre: "infinite (UNIV :: 'a::var_\<tau>_pre set)"
  using card_of_ordLeq_finite cinfinite_def infinite_regular_card_order.Cinfinite infinite_regular_card_order_card_suc natLeq_Card_order natLeq_card_order natLeq_cinfinite var_DEADID_class.large by blast

(******************** Definitions for variable-for-variable substitution ***********)
typedef 'a :: var_\<tau>_pre ssfun = "{f :: 'a \<Rightarrow> 'a. |supp f| <o |UNIV::'a set|}"
  by (auto intro!: exI[of _ id] simp: supp_id_bound)

setup_lifting type_definition_ssfun

lift_definition idSS :: "'a ::var_\<tau>_pre ssfun" is id
  by (simp add: supp_id_bound)

lemma supp_comp_bound_var_\<tau>_pre: "\<lbrakk> |supp f| <o |UNIV::'a::var_\<tau>_pre set| ; |supp g| <o |UNIV::'a set| \<rbrakk> \<Longrightarrow> |supp (g \<circ> f)| <o |UNIV::'a set|"
  using infinite_var_\<tau>_pre supp_comp_bound by blast

context
  fixes u :: "'a :: var_\<tau>_pre \<Rightarrow> 'a"
  assumes u: "bij u" "|supp u| <o |UNIV::'a set|"
begin
  lift_definition compSS :: "'a ::var_\<tau>_pre ssfun \<Rightarrow> 'a ssfun" is "\<lambda>p. u o p o inv u"
    by (simp add: supp_comp_bound_var_\<tau>_pre supp_inv_bound u)
end

lemma compSS_id: "compSS id = id"
  supply supp_id_bound[transfer_rule] bij_id[transfer_rule] by (rule ext, transfer) auto
lemma compSS_comp:
  fixes f :: "'a::var_\<tau>_pre \<Rightarrow> 'a" and g :: "'a \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|" "bij g" "|supp g| <o |UNIV::'a set|"
  shows "compSS (f \<circ> g) = compSS f \<circ> compSS g"
  supply assms[transfer_rule] bij_comp[transfer_rule] supp_comp_bound_var_\<tau>_pre[transfer_rule]
  by (rule ext, transfer) (auto simp: fun_eq_iff assms o_inv_distrib)
lemma compSS_cong_id:
  fixes f :: "'a::var_\<tau>_pre \<Rightarrow> 'a" and d :: "'a ssfun"
  assumes "bij f" "|supp f| <o |UNIV|" "\<And>a. a \<in> imsupp (Rep_ssfun d) \<Longrightarrow> f a = a"
  shows "compSS f d = d"
  supply assms(1,2)[transfer_rule]
  using assms(3)
  apply (transfer fixing: f)
  oops

lemma imsupp_ssfun_bound:
  fixes p :: "'a::var_\<tau>_pre ssfun"
  shows "|imsupp (Rep_ssfun p)| <o |UNIV::'a set|"
  unfolding imsupp_def
  apply (rule card_of_Un_ordLess_infinite)
    apply (rule infinite_var_\<tau>_pre)
  using Rep_ssfun apply blast
  by (metis Rep_ssfun card_of_image mem_Collect_eq ordLeq_ordLess_trans)

definition CCTOR' :: "('a::var_\<tau>_pre, 'a, 'a ssfun \<Rightarrow> 'a \<tau>, 'a ssfun \<Rightarrow> 'a \<tau>) \<tau>_pre \<Rightarrow> 'a ssfun \<Rightarrow> 'a \<tau>" where
  "CCTOR' \<equiv> \<lambda>F p. \<tau>_ctor (map_\<tau>_pre (Rep_ssfun p) id (\<lambda>R. R p) (\<lambda>R. R p) F)"
definition CCTOR :: "('a::var_\<tau>_pre, 'a, 'a \<tau> \<times> ('a ssfun \<Rightarrow> 'a \<tau>), 'a \<tau> \<times> ('a ssfun \<Rightarrow> 'a \<tau>)) \<tau>_pre \<Rightarrow> 'a ssfun \<Rightarrow> 'a \<tau>" where
  "CCTOR = (\<lambda>F p. \<tau>_ctor (map_\<tau>_pre (Rep_ssfun p) id ((\<lambda>R. R p) o snd) ((\<lambda>R. R p) o snd) F))"
(*definition Umap :: "('a::var_\<tau>_pre \<Rightarrow> 'a) \<Rightarrow> 'a \<tau> \<Rightarrow> ('a ssfun \<Rightarrow> 'a \<tau>) \<Rightarrow> ('a ssfun \<Rightarrow> 'a \<tau>)" where
  "Umap f t pu \<equiv> \<lambda>c. rrename_\<tau> f (pu (compSS (inv f) c))"*)
definition Umap :: "('a::var_\<tau>_pre \<Rightarrow> 'a) \<Rightarrow> 'a \<tau> \<Rightarrow> 'a \<tau> \<Rightarrow> 'a \<tau>" where
  "Umap f t \<equiv> rrename_\<tau> f"
definition UFVars :: "'a::var_\<tau>_pre \<tau> \<Rightarrow> 'a \<tau> \<Rightarrow> 'a set" where
  "UFVars t \<equiv> FFVars_\<tau>"
lemma Umap_id0: "Umap id t = id"
  unfolding Umap_def
  by (rule \<tau>.rrename_id0s)
lemma Umap_cong_id:
  fixes f :: "'a::var_\<tau>_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|" "\<And>z. z \<in> UFVars t w \<Longrightarrow> f z = z"
  shows "Umap f t w = w"
  using assms unfolding Umap_def UFVars_def
  by (rule \<tau>.rrename_cong_ids)

(***************************************************************************************)















ML_file \<open>Tools/mrbnf_recursor.ML\<close>

local_setup \<open>fn lthy =>
let
  fun rtac ctxt = resolve_tac ctxt o single
  val model_ext_tacs = {
    small_avoiding_sets = [fn ctxt => rtac ctxt @{thm emp_bound} 1],
    Umap_id0 = fn ctxt => resolve_tac ctxt @{thms Umap_id0} 1,
    Umap_comp0 = fn ctxt => Skip_Proof.cheat_tac ctxt 1,
    Umap_cong_ids = map (fn thm => fn ctxt => EVERY1 [
      resolve_tac ctxt [thm],
      REPEAT_DETERM o (Goal.assume_rule_tac ctxt ORELSE' assume_tac ctxt)
    ]) @{thms Umap_cong_id},
    in_UFVars_Umap = [fn ctxt => Skip_Proof.cheat_tac ctxt 1],
    Umap_Uctor = fn ctxt => Skip_Proof.cheat_tac ctxt 1
  };
  val model_tacs = {
    small_avoiding_sets = [fn ctxt => rtac ctxt @{thm emp_bound} 1],
    Umap_id0 = fn ctxt => resolve_tac ctxt @{thms \<tau>.rrename_id0s} 1,
    Umap_comp0 = fn ctxt => Skip_Proof.cheat_tac ctxt 1,
    Umap_cong_ids = map (fn thm => fn ctxt => EVERY1 [
      resolve_tac ctxt [thm],
      REPEAT_DETERM o (Goal.assume_rule_tac ctxt ORELSE' assume_tac ctxt)
    ]) @{thms \<tau>.rrename_cong_ids},
    in_UFVars_Umap = [fn ctxt => Skip_Proof.cheat_tac ctxt 1],
    Umap_Uctor = fn ctxt => Skip_Proof.cheat_tac ctxt 1
  };
  val parameter_tacs = {
    Pmap_id0 = fn ctxt => rtac ctxt @{thm compSS_id} 1,
    Pmap_comp0 = fn ctxt => EVERY1 [rtac ctxt @{thm compSS_comp}, REPEAT_DETERM o assume_tac ctxt],
    Pmap_cong_ids = [fn ctxt => Skip_Proof.cheat_tac ctxt 1],
    in_PFVars_Pmap = [fn ctxt => Skip_Proof.cheat_tac ctxt 1],
    small_PFVars = [fn ctxt => rtac ctxt @{thm imsupp_ssfun_bound} 1]
  };
  val model_ext = {
    U = @{typ "'a::var_\<tau>_pre \<tau>"},
    term_quotient = SOME {
      qT = @{typ "'a::var_\<tau>_pre \<tau>"},
      qmap = @{term rrename_\<tau>},
      qctor = @{term \<tau>_ctor}
    },
    UFVars = [@{term "UFVars"}],
    Umap = @{term "Umap"},
    Uctor = @{term CCTOR},
    avoiding_sets = [@{term "{} :: 'a::var_\<tau>_pre set"}],
    mrbnf = tau,
    parameters = {
      P = @{typ "'a::var_\<tau>_pre ssfun"},
      PFVars = [@{term "\<lambda>p. imsupp (Rep_ssfun p)"}],
      Pmap = @{term "compSS"},
      axioms = parameter_tacs
    },
    axioms = model_ext_tacs
  };
  val model = {
    U = @{typ "'a::var_\<tau>_pre \<tau>"},
    term_quotient = NONE,
    UFVars = [@{term "FFVars_\<tau>"}],
    Umap = @{term "rrename_\<tau>"},
    Uctor = @{term CCTOR'},
    avoiding_sets = [@{term "{} :: 'a::var_\<tau>_pre set"}],
    mrbnf = tau,
    parameters = {
      P = @{typ "'a::var_\<tau>_pre ssfun"},
      PFVars = [@{term "\<lambda>p. imsupp (Rep_ssfun p)"}],
      Pmap = @{term "compSS"},
      axioms = parameter_tacs
    },
    axioms = model_tacs
  };
  val lthy' = MRBNF_Recursor.create_binding_recursor model_ext lthy
in lthy' end
\<close>

end
