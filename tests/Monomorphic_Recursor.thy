theory Monomorphic_Recursor
  imports "../operations/Fixpoint"
begin

typedecl U1
typedecl U2

typedecl P

typedecl Var

instantiation Var :: var_T1_pre begin instance sorry end
instantiation Var :: var_T2_pre begin instance sorry end

consts Pmap :: "(Var \<Rightarrow> Var) \<Rightarrow> (Var \<Rightarrow> Var) \<Rightarrow> P \<Rightarrow> P"
consts PFVars_1 :: "P \<Rightarrow> Var set"
consts PFVars_2 :: "P \<Rightarrow> Var set"
consts avoiding_set1 :: "Var set"
consts avoiding_set2 :: "Var set"

consts U1map :: "(Var \<Rightarrow> Var) \<Rightarrow> (Var \<Rightarrow> Var) \<Rightarrow> (Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b) T1 \<Rightarrow> U1 \<Rightarrow> U1"
consts U2map :: "(Var \<Rightarrow> Var) \<Rightarrow> (Var \<Rightarrow> Var) \<Rightarrow> (Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b) T2 \<Rightarrow> U2 \<Rightarrow> U2"

consts U1FVars_1 :: "(Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b) T1 \<Rightarrow> U1 \<Rightarrow> Var set"
consts U1FVars_2 :: "(Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b) T1 \<Rightarrow> U1 \<Rightarrow> Var set"
consts U2FVars_1 :: "(Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b) T2 \<Rightarrow> U2 \<Rightarrow> Var set"
consts U2FVars_2 :: "(Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b) T2 \<Rightarrow> U2 \<Rightarrow> Var set"

consts U1ctor :: "(Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b, Var, Var,
  (Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b) T1 \<times> (P \<Rightarrow> U1),
  (Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b) T1 \<times> (P \<Rightarrow> U1),
  (Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b) T2 \<times> (P \<Rightarrow> U2),
  (Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b) T2 \<times> (P \<Rightarrow> U2)
) T1_pre \<Rightarrow> P \<Rightarrow> U1"
consts U2ctor :: "(Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b, Var, Var,
  (Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b) T1 \<times> (P \<Rightarrow> U1),
  (Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b) T1 \<times> (P \<Rightarrow> U1),
  (Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b) T2 \<times> (P \<Rightarrow> U2),
  (Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b) T2 \<times> (P \<Rightarrow> U2)
) T2_pre \<Rightarrow> P \<Rightarrow> U2"

axiomatization where
  (* parameter axioms *)
  Pmap_id0: "Pmap id id d = d"
  and Pmap_comp0: "bij f1 \<Longrightarrow> |supp f1| <o |UNIV::Var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp f2| <o |UNIV::Var set| \<Longrightarrow>
  bij g1 \<Longrightarrow> |supp g1| <o |UNIV::Var set| \<Longrightarrow> bij g2 \<Longrightarrow> |supp g2| <o |UNIV::Var set| \<Longrightarrow>
  Pmap (g1 \<circ> f1) (g2 \<circ> f2) d = (Pmap g1 g2 \<circ> Pmap f1 f2) d"
  and Pmap_cong_id: "bij f1 \<Longrightarrow> |supp f1| <o |UNIV::Var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp f2| <o |UNIV::Var set| \<Longrightarrow>
  (\<And>a. a \<in> PFVars_1 d \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> PFVars_2 d \<Longrightarrow> f2 a = a) \<Longrightarrow>
  Pmap f1 f2 d = d"
  and PFVars_Pmap_1: "bij f1 \<Longrightarrow> |supp f1| <o |UNIV::Var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp f2| <o |UNIV::Var set| \<Longrightarrow>
  PFVars_1 (Pmap f1 f2 d) = f1 ` PFVars_1 d"
  and PFVars_Pmap_2: "bij f1 \<Longrightarrow> |supp f1| <o |UNIV::Var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp f2| <o |UNIV::Var set| \<Longrightarrow>
  PFVars_2 (Pmap f1 f2 d) = f2 ` PFVars_2 d"
  and small_PFVars_1: "|PFVars_1 d| <o |UNIV::Var set|"
  and small_PFVars_2: "|PFVars_2 d| <o |UNIV::Var set|"
  and small_avoiding_set1: "|avoiding_set1::Var set| <o |UNIV::Var set|"
  and small_avoiding_set2: "|avoiding_set2::Var set| <o |UNIV::Var set|"
  (* model 1 axioms *)
  and U1map_id0: "U1map id id (t1::(Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b) T1) u1 = u1"
  and U1map_comp0: "bij f1 \<Longrightarrow> |supp f1| <o |UNIV::Var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp f2| <o |UNIV::Var set| \<Longrightarrow>
  bij g1 \<Longrightarrow> |supp g1| <o |UNIV::Var set| \<Longrightarrow> bij g2 \<Longrightarrow> |supp g2| <o |UNIV::Var set| \<Longrightarrow>
  U1map (g1 \<circ> f1) (g2 \<circ> f2) t1 u1 = (U1map g1 g2 t1 \<circ> U1map f1 f2 t1) u1"
  and U1map_cong_id: "bij f1 \<Longrightarrow> |supp f1| <o |UNIV::Var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp f2| <o |UNIV::Var set| \<Longrightarrow>
  (\<And>a. a \<in> U1FVars_1 t1 u1 \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> U1FVars_2 t1 u1 \<Longrightarrow> f2 a = a) \<Longrightarrow>
  U1map f1 f2 t1 u1 = u1"
  and U1map_Uctor: "bij f1 \<Longrightarrow> |supp f1| <o |UNIV::Var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp f2| <o |UNIV::Var set| \<Longrightarrow>
  U1map f1 f2 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) (U1ctor y p)
= U1ctor (map_T1_pre f1 f2 id id f1 f2
    (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
    (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
    (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
    (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
 y) (Pmap f1 f2 p)"
  and U1FVars_subset_1: "set5_T1_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T1_pre) \<inter> (PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T1_pre y \<union> set8_T1_pre y \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FFVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y \<union> set10_T1_pre y \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FFVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  U1FVars_1 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) (U1ctor y p) \<subseteq> FFVars_T11 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> PFVars_1 p \<union> avoiding_set1"
  and U1FVars_subset_2: "set6_T1_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T1_pre) \<inter> (PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T1_pre y \<union> set8_T1_pre y \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FFVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y \<union> set10_T1_pre y \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  U1FVars_2 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) (U1ctor y p) \<subseteq> FFVars_T12 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> PFVars_2 p \<union> avoiding_set2"
  (* model 2 axioms *)
  and U2map_id0: "U2map id id (t2::(Var, Var, 'a::{var_T1_pre,var_T2_pre}, 'b) T2) u2 = u2"
  and U2map_comp0: "bij f1 \<Longrightarrow> |supp f1| <o |UNIV::Var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp f2| <o |UNIV::Var set| \<Longrightarrow>
  bij g1 \<Longrightarrow> |supp g1| <o |UNIV::Var set| \<Longrightarrow> bij g2 \<Longrightarrow> |supp g2| <o |UNIV::Var set| \<Longrightarrow>
  U2map (g1 \<circ> f1) (g2 \<circ> f2) t2 u2 = (U2map g1 g2 t2 \<circ> U2map f1 f2 t2) u2"
  and U2map_cong_id: "bij f1 \<Longrightarrow> |supp f1| <o |UNIV::Var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp f2| <o |UNIV::Var set| \<Longrightarrow>
  (\<And>a. a \<in> U2FVars_1 t2 u2 \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> U2FVars_2 t2 u2 \<Longrightarrow> f2 a = a) \<Longrightarrow>
  U2map f1 f2 t2 u2 = u2"
  and U2map_Uctor: "bij f1 \<Longrightarrow> |supp f1| <o |UNIV::Var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp f2| <o |UNIV::Var set| \<Longrightarrow>
  U2map f1 f2 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y2)) (U2ctor y2 p)
= U2ctor (map_T2_pre f1 f2 id id f1 f2
    (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
    (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
    (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
    (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
 y2) (Pmap f1 f2 p)"
  and U2FVars_subset_1: "set5_T2_pre (y2::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T2_pre) \<inter> (PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T2_pre y2 \<union> set8_T2_pre y2 \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FFVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y2 \<union> set10_T2_pre y2 \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FFVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  U2FVars_1 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y2)) (U2ctor y2 p) \<subseteq> FFVars_T21 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y2)) \<union> PFVars_1 p \<union> avoiding_set1"
  and U2FVars_subset_2: "set6_T2_pre y2 \<inter> (PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T2_pre y2 \<union> set8_T2_pre y2 \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FFVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y2 \<union> set10_T2_pre y2 \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  U2FVars_2 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y2)) (U2ctor y2 p) \<subseteq> FFVars_T22 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y2)) \<union> PFVars_2 p \<union> avoiding_set2"
print_theorems

lemmas U1FVars_subsets = U1FVars_subset_1 U1FVars_subset_2
lemmas U2FVars_subsets = U2FVars_subset_1 U2FVars_subset_2

ML \<open>
val nvars = 2

val parameters = {
  P = @{typ P},
  Pmap = @{term Pmap},
  PFVarss = [@{term PFVars_1}, @{term PFVars_2}],
  avoiding_sets = [@{term avoiding_set1}, @{term avoiding_set2}],
  min_bound = false,
  validity = NONE : { pred: term, valid_Pmap: Proof.context -> tactic } option,
  axioms = {
    Pmap_id0 = fn ctxt => resolve_tac ctxt @{thms Pmap_id0} 1,
    Pmap_comp0 = fn ctxt => resolve_tac ctxt @{thms Pmap_comp0} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    Pmap_cong_id = fn ctxt => resolve_tac ctxt @{thms Pmap_cong_id} 1 THEN REPEAT_DETERM (
      assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1
    ),
    PFVars_Pmaps = replicate nvars (fn ctxt => resolve_tac ctxt @{thms PFVars_Pmap_1 PFVars_Pmap_2} 1 THEN REPEAT_DETERM (assume_tac ctxt 1)),
    small_PFVarss = replicate nvars (fn ctxt => resolve_tac ctxt @{thms small_PFVars_1 small_PFVars_2} 1),
    small_avoiding_sets = replicate nvars (fn ctxt => resolve_tac ctxt @{thms small_avoiding_set1 small_avoiding_set2} 1)
  }
};

val T1_model = {
  binding = @{binding mono_T1},
  U = @{typ U1},
  UFVarss = [@{term U1FVars_1}, @{term U1FVars_2}],
  Umap = @{term U1map},
  Uctor = @{term U1ctor},
  validity = NONE : { pred: term, valid_Umap: Proof.context -> tactic, valid_Uctor: Proof.context -> tactic } option,
  axioms = {
    Umap_id0 = fn ctxt => resolve_tac ctxt @{thms U1map_id0} 1,
    Umap_comp0 = fn ctxt => resolve_tac ctxt @{thms U1map_comp0} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    Umap_cong_id = fn ctxt => resolve_tac ctxt @{thms U1map_cong_id} 1 THEN REPEAT_DETERM (
      assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1
    ),
    Umap_Uctor = fn ctxt => resolve_tac ctxt @{thms U1map_Uctor} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    UFVars_subsets = replicate nvars (fn ctxt => resolve_tac ctxt @{thms U1FVars_subset_1 U1FVars_subset_2} 1 THEN
      REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1))
  }
};

val T2_model = {
  binding = @{binding mono_T2},
  U = @{typ U2},
  UFVarss = [@{term U2FVars_1}, @{term U2FVars_2}],
  Umap = @{term U2map},
  Uctor = @{term U2ctor},
  validity = NONE : { pred: term, valid_Umap: Proof.context -> tactic, valid_Uctor: Proof.context -> tactic } option,
  axioms = {
    Umap_id0 = fn ctxt => resolve_tac ctxt @{thms U2map_id0} 1,
    Umap_comp0 = fn ctxt => resolve_tac ctxt @{thms U2map_comp0} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    Umap_cong_id = fn ctxt => resolve_tac ctxt @{thms U2map_cong_id} 1 THEN REPEAT_DETERM (
      assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1
    ),
    Umap_Uctor = fn ctxt => resolve_tac ctxt @{thms U2map_Uctor} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    UFVars_subsets = replicate nvars (fn ctxt => resolve_tac ctxt @{thms U2FVars_subset_1 U2FVars_subset_2} 1 THEN
      REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1))
  }
};

val fp_res = the (MRBNF_FP_Def_Sugar.fp_result_of @{context} "Fixpoint.T1");
\<close>

local_setup \<open>fn lthy =>
let
  val qualify = I
  val (ress, lthy) = MRBNF_Recursor.create_binding_recursor qualify fp_res parameters [T1_model, T2_model] lthy;
  val _ = @{print} ress
in lthy end
\<close>
