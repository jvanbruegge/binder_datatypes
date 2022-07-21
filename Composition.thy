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

lemma image_in_bij_eq: "bij f \<Longrightarrow> (a \<in> f ` A) = (inv f a \<in> A)"
  by force

lemma supp_comp_bound:
  assumes bound: "|supp f| <o |UNIV::'a set|" "|supp g| <o |UNIV::'a set|"
  and inf: "infinite (UNIV::'a set)"
  shows "|supp (g \<circ> f)| <o |UNIV::'a set|"
proof -
  from inf bound(2,1) have "|supp g \<union> supp f| <o |UNIV::'a set|" by (rule card_of_Un_ordLess_infinite)
  then show ?thesis using supp_o
    by (metis card_of_mono1 ordLeq_ordLess_trans)
qed

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

ML_file \<open>Tools/mrbnf_recursor.ML\<close>

definition FFVars_\<tau>' :: "'a::var_\<tau>_pre \<tau> \<Rightarrow> 'a \<tau> \<Rightarrow> 'a set"
  where "FFVars_\<tau>' \<equiv> undefined"
definition rrename_\<tau>' :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a::var_\<tau>_pre \<tau> \<Rightarrow> 'a \<tau> \<Rightarrow> 'a \<tau>"
  where "rrename_\<tau>' \<equiv> undefined"

local_setup \<open>fn lthy =>
let
  val model_tacs = {
    Umap_id0 = fn ctxt => resolve_tac ctxt @{thms \<tau>.rrename_id0s} 1,
    Umap_comp0 = fn ctxt => Skip_Proof.cheat_tac ctxt 1,
    Umap_cong_ids = map (fn thm => fn ctxt => EVERY1 [
      resolve_tac ctxt [thm],
      REPEAT_DETERM o (Goal.assume_rule_tac ctxt ORELSE' assume_tac ctxt)
    ]) @{thms \<tau>.rrename_cong_ids},
    in_UFVars_Umap = [fn ctxt => Skip_Proof.cheat_tac ctxt 1]
  };
  val parameter_tacs = {
    Pmap_id0 = fn ctxt => Skip_Proof.cheat_tac ctxt 1,
    Pmap_comp0 = fn ctxt => Skip_Proof.cheat_tac ctxt 1,
    Pmap_cong_ids = [fn ctxt => Skip_Proof.cheat_tac ctxt 1],
    in_PFVars_Pmap = [fn ctxt => Skip_Proof.cheat_tac ctxt 1],
    small_PFVars = [fn ctxt => Skip_Proof.cheat_tac ctxt 1]
  };
  val model_ext = {
    U = @{typ "'a::var_\<tau>_pre \<tau>"},
    term_quotient = SOME {
      qT = @{typ "'a::var_\<tau>_pre \<tau>"},
      qmap = @{term rrename_\<tau>}
    },
    UFVars = [@{term "FFVars_\<tau>'"}],
    Umap = @{term "rrename_\<tau>'"},
    Uctor = @{term \<tau>_ctor},
    parameters = {
      P = @{typ "unit"},
      PFVars = [@{term "\<lambda>_. {}"}],
      Pmap = @{term "id :: ('a => 'a) => 'a => 'a"},
      axioms = parameter_tacs
    },
    axioms = model_tacs
  };
  val model = {
    U = @{typ "'a::var_\<tau>_pre \<tau>"},
    term_quotient = NONE,
    UFVars = [@{term "FFVars_\<tau>"}],
    Umap = @{term "rrename_\<tau>"},
    Uctor = @{term \<tau>_ctor},
    parameters = {
      P = @{typ "unit"},
      PFVars = [@{term "\<lambda>_. {}"}],
      Pmap = @{term "id :: ('a => 'a) => 'a => 'a"},
      axioms = parameter_tacs
    },
    axioms = model_tacs
  };
  val lthy' = MRBNF_Recursor.create_binding_recursor model lthy
in lthy' end
\<close>

end
