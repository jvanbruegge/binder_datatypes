theory Recursor
  imports "./Fixpoint"
begin

typedecl ('var, 'tyvar, 'a, 'b) U1
typedecl ('var, 'tyvar, 'a, 'b) U2

typedecl ('var, 'tyvar) P

consts Pmap :: "('var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var) \<Rightarrow> ('tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar) \<Rightarrow> ('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar) P"
consts PFVars_1 :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}) P \<Rightarrow> 'var set"
consts PFVars_2 :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}) P \<Rightarrow> 'tyvar set"
consts avoiding_set1 :: "'var::{var_T1_pre,var_T2_pre} set"
consts avoiding_set2 :: "'tyvar::{var_T1_pre,var_T2_pre} set"

consts U1map :: "('var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var) \<Rightarrow> ('tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar) \<Rightarrow> ('var, 'tyvar, 'a, 'b) T1 \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1 \<Rightarrow> ('var, 'tyvar, 'a, 'c) U1"
consts U2map :: "('var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var) \<Rightarrow> ('tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar) \<Rightarrow> ('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2 \<Rightarrow> ('var, 'tyvar, 'a, 'c) U2"

consts U1FVars_1 :: "('var, 'tyvar, 'a, 'b) T1 \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a, 'b) U1 \<Rightarrow> 'var set"
consts U1FVars_2 :: "('var, 'tyvar, 'a, 'b) T1 \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a, 'b) U1 \<Rightarrow> 'tyvar set"
consts U2FVars_1 :: "('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a, 'b) U2 \<Rightarrow> 'var set"
consts U2FVars_2 :: "('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a, 'b) U2 \<Rightarrow> 'tyvar set"

consts U1ctor :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a, 'b, 'var, 'tyvar,
  ('var, 'tyvar, 'a, 'b) T1 \<times> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1),
  ('var, 'tyvar, 'a, 'b) T1 \<times> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1),
  ('var, 'tyvar, 'a, 'b) T2 \<times> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2),
  ('var, 'tyvar, 'a, 'b) T2 \<times> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2)
) T1_pre \<Rightarrow> ('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1"
consts U2ctor :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a, 'b, 'var, 'tyvar,
  ('var, 'tyvar, 'a, 'b) T1 \<times> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1),
  ('var, 'tyvar, 'a, 'b) T1 \<times> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1),
  ('var, 'tyvar, 'a, 'b) T2 \<times> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2),
  ('var, 'tyvar, 'a, 'b) T2 \<times> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2)
) T2_pre \<Rightarrow> ('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2"

axiomatization where
  (* parameter axioms *)
  Pmap_id0: "Pmap id id = id"
  and Pmap_comp0: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  bij g1 \<Longrightarrow> |supp (g1::'var \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij g2 \<Longrightarrow> |supp (g2::'tyvar \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  Pmap (g1 \<circ> f1) (g2 \<circ> f2) = Pmap g1 g2 \<circ> Pmap f1 f2"
  and Pmap_cong_id: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  (\<And>a. a \<in> PFVars_1 d \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> PFVars_2 d \<Longrightarrow> f2 a = a) \<Longrightarrow>
  Pmap f1 f2 d = d"
  and PFVars_Pmap_1: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  PFVars_1 (Pmap f1 f2 d) = f1 ` PFVars_1 d"
  and PFVars_Pmap_2: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  PFVars_2 (Pmap f1 f2 d) = f2 ` PFVars_2 d"
  and small_PFVars_1: "|PFVars_1 d| <o |UNIV::'var set|"
  and small_PFVars_2: "|PFVars_2 d| <o |UNIV::'tyvar set|"
  and small_avoiding_set1: "|avoiding_set1::'var set| <o |UNIV::'var set|"
  and small_avoiding_set2: "|avoiding_set2::'tyvar set| <o |UNIV::'tyvar set|"
  (* model 1 axioms *)
  and U1map_id0: "U1map id id (t1::('var, 'tyvar, 'a, 'b) T1) = id"
  and U1map_comp0: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  bij g1 \<Longrightarrow> |supp (g1::'var \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij g2 \<Longrightarrow> |supp (g2::'tyvar \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U1map (g1 \<circ> f1) (g2 \<circ> f2) t1 = U1map g1 g2 t1 \<circ> U1map f1 f2 t1"
  and U1map_cong_id: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  (\<And>a. a \<in> U1FVars_1 t1 u1 \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> U1FVars_2 t1 u1 \<Longrightarrow> f2 a = a) \<Longrightarrow>
  U1map f1 f2 t1 u1 = u1"
  and U1FVars_Umap_1: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U1FVars_1 (rrename_T1 f1 f2 t1) (U1map f1 f2 t1 u1) = f1 ` U1FVars_1 t1 u1"
  and U1FVars_Umap_2: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U1FVars_2 (rrename_T1 f1 f2 t1) (U1map f1 f2 t1 u1) = f2 ` U1FVars_2 t1 u1"
  and U1map_Uctor: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
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
  and U2map_id0: "U2map id id (t2::('var, 'tyvar, 'a, 'b) T2) = id"
  and U2map_comp0: "bij f1 \<Longrightarrow> |supp (f1::'var \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  bij g1 \<Longrightarrow> |supp (g1::'var \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij g2 \<Longrightarrow> |supp (g2::'tyvar \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U2map (g1 \<circ> f1) (g2 \<circ> f2) t2 = U2map g1 g2 t2 \<circ> U2map f1 f2 t2"
  and U2map_cong_id: "bij f1 \<Longrightarrow> |supp (f1::'var \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  (\<And>a. a \<in> U2FVars_1 t2 u2 \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> U2FVars_2 t2 u2 \<Longrightarrow> f2 a = a) \<Longrightarrow>
  U2map f1 f2 t2 u2 = u2"
  and U2FVars_Umap_1: "bij f1 \<Longrightarrow> |supp (f1::'var \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U2FVars_1 (rrename_T2 f1 f2 t2) (U2map f1 f2 t2 u2) = f1 ` U2FVars_1 t2 u2"
  and U2FVars_Umap_2: "bij f1 \<Longrightarrow> |supp (f1::'var \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U2FVars_2 (rrename_T2 f1 f2 t2) (U2map f1 f2 t2 u2) = f2 ` U2FVars_2 t2 u2"
  and U2map_Uctor: "bij f1 \<Longrightarrow> |supp (f1::'var \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U2map f1 f2 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y2)) (U2ctor y2 p)
= U2ctor (map_T2_pre f1 f2 id id f1 f2
    (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
    (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
    (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
    (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))))
 y2) (Pmap f1 f2 p)"
  and U2FVars_subset_1: "set5_T2_pre (y2::(_, _, 'a, 'b, _, _, _, _, _, _) T2_pre) \<inter> (PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
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

(**********************************************************************)
(*                            DEFINITIONS                             *)
(**********************************************************************)

type_synonym ('var, 'tyvar, 'a, 'b) pre_T1 = "('var, 'tyvar, 'a, 'b, 'var, 'tyvar,
  ('var, 'tyvar, 'a, 'b) raw_T1, ('var, 'tyvar, 'a, 'b) raw_T1,
  ('var, 'tyvar, 'a, 'b) raw_T2, ('var, 'tyvar, 'a, 'b) raw_T2
) T1_pre"
type_synonym ('var, 'tyvar, 'a, 'b) pre_T2 = "('var, 'tyvar, 'a, 'b, 'var, 'tyvar,
  ('var, 'tyvar, 'a, 'b) raw_T1, ('var, 'tyvar, 'a, 'b) raw_T1,
  ('var, 'tyvar, 'a, 'b) raw_T2, ('var, 'tyvar, 'a, 'b) raw_T2
) T2_pre"

definition suitable11 :: "(('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) pre_T1 \<Rightarrow> ('var, 'tyvar) P \<Rightarrow> 'var \<Rightarrow> 'var) \<Rightarrow> bool" where
  "suitable11 \<equiv> \<lambda>pick. \<forall>x p. bij (pick x p) \<and> |supp (pick x p)| <o |UNIV::'var set|
  \<and> imsupp (pick x p) \<inter> ((FVars_T11 (raw_T1_ctor x) \<union> PFVars_1 p \<union> avoiding_set1) - set5_T1_pre x) = {}
  \<and> (pick x p) ` set5_T1_pre x \<inter> (FVars_T11 (raw_T1_ctor x) \<union> PFVars_1 p \<union> avoiding_set1) = {}"

definition suitable12 :: "(('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) pre_T1 \<Rightarrow> ('var, 'tyvar) P \<Rightarrow> 'tyvar \<Rightarrow> 'tyvar) \<Rightarrow> bool" where
  "suitable12 \<equiv> \<lambda>pick. \<forall>x p. bij (pick x p) \<and> |supp (pick x p)| <o |UNIV::'tyvar set|
  \<and> imsupp (pick x p) \<inter> ((FVars_T12 (raw_T1_ctor x) \<union> PFVars_2 p \<union> avoiding_set2) - set6_T1_pre x) = {}
  \<and> (pick x p) ` set6_T1_pre x \<inter> (FVars_T12 (raw_T1_ctor x) \<union> PFVars_2 p \<union> avoiding_set2) = {}"

definition suitable21 :: "(('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) pre_T2 \<Rightarrow> ('var, 'tyvar) P \<Rightarrow> 'var \<Rightarrow> 'var) \<Rightarrow> bool" where
  "suitable21 \<equiv> \<lambda>pick. \<forall>x p. bij (pick x p) \<and> |supp (pick x p)| <o |UNIV::'var set|
  \<and> imsupp (pick x p) \<inter> ((FVars_T21 (raw_T2_ctor x) \<union> PFVars_1 p \<union> avoiding_set1) - set5_T2_pre x) = {}
  \<and> (pick x p) ` set5_T2_pre x \<inter> (FVars_T21 (raw_T2_ctor x) \<union> PFVars_1 p \<union> avoiding_set1) = {}"

definition suitable22 :: "(('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) pre_T2 \<Rightarrow> ('var, 'tyvar) P \<Rightarrow> 'tyvar \<Rightarrow> 'tyvar) \<Rightarrow> bool" where
  "suitable22 \<equiv> \<lambda>pick. \<forall>x p. bij (pick x p) \<and> |supp (pick x p)| <o |UNIV::'tyvar set|
  \<and> imsupp (pick x p) \<inter> ((FVars_T22 (raw_T2_ctor x) \<union> PFVars_2 p \<union> avoiding_set2) - set6_T2_pre x) = {}
  \<and> (pick x p) ` set6_T2_pre x \<inter> (FVars_T22 (raw_T2_ctor x) \<union> PFVars_2 p \<union> avoiding_set2) = {}"

lemmas suitable_defs = suitable11_def suitable12_def suitable21_def suitable22_def

abbreviation "abs_T1 \<equiv> quot_type.abs alpha_T1 Abs_T1"
abbreviation "abs_T2 \<equiv> quot_type.abs alpha_T2 Abs_T2"

definition U1map' :: "('var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var) \<Rightarrow> ('tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar) \<Rightarrow> ('var, 'tyvar, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T1 \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1 \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1" where
  "U1map' f1 f2 x \<equiv> U1map f1 f2 (abs_T1 x)"
definition U2map' :: "('var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var) \<Rightarrow> ('tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar) \<Rightarrow> ('var, 'tyvar, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T2 \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2 \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2" where
  "U2map' f1 f2 x \<equiv> U2map f1 f2 (abs_T2 x)"

definition U1FVars_1' :: "('var, 'tyvar, 'a, 'b) raw_T1 \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) U1 \<Rightarrow> 'var set" where
  "U1FVars_1' t \<equiv> U1FVars_1 (abs_T1 t)"
definition U1FVars_2' :: "('var, 'tyvar, 'a, 'b) raw_T1 \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) U1 \<Rightarrow> 'tyvar set" where
  "U1FVars_2' t \<equiv> U1FVars_2 (abs_T1 t)"
definition U2FVars_1' :: "('var, 'tyvar, 'a, 'b) raw_T2 \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) U2 \<Rightarrow> 'var set" where
  "U2FVars_1' t \<equiv> U2FVars_1 (abs_T2 t)"
definition U2FVars_2' :: "('var, 'tyvar, 'a, 'b) raw_T2 \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) U2 \<Rightarrow> 'tyvar set" where
  "U2FVars_2' t \<equiv> U2FVars_2 (abs_T2 t)"

definition PU1map :: "('var \<Rightarrow> 'var) \<Rightarrow> ('tyvar \<Rightarrow> 'tyvar) \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) T1 \<Rightarrow> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1) \<Rightarrow> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1)" where
  "PU1map f1 f2 t \<equiv> \<lambda>pu p. U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))"
definition PU2map :: "('var \<Rightarrow> 'var) \<Rightarrow> ('tyvar \<Rightarrow> 'tyvar) \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) T2 \<Rightarrow> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2) \<Rightarrow> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2)" where
  "PU2map f1 f2 t \<equiv> \<lambda>pu p. U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p))"
definition PU1map' :: "('var \<Rightarrow> 'var) \<Rightarrow> ('tyvar \<Rightarrow> 'tyvar) \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T1 \<Rightarrow> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1) \<Rightarrow> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1)" where
  "PU1map' f1 f2 t \<equiv> \<lambda>pu p. U1map' f1 f2 t (pu (Pmap (inv f1) (inv f2) p))"
definition PU2map' :: "('var \<Rightarrow> 'var) \<Rightarrow> ('tyvar \<Rightarrow> 'tyvar) \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) raw_T2 \<Rightarrow> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2) \<Rightarrow> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2)" where
  "PU2map' f1 f2 t \<equiv> \<lambda>pu p. U2map' f1 f2 t (pu (Pmap (inv f1) (inv f2) p))"

definition U1ctor' :: "_ \<Rightarrow> _ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) U1" where
  "U1ctor' y \<equiv> U1ctor (map_T1_pre id id id id id id (map_prod abs_T1 id) (map_prod abs_T1 id) (map_prod abs_T2 id) (map_prod abs_T2 id) y)"
definition U2ctor' :: "_ \<Rightarrow> _ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) U2" where
  "U2ctor' y \<equiv> U2ctor (map_T2_pre id id id id id id (map_prod abs_T1 id) (map_prod abs_T1 id) (map_prod abs_T2 id) (map_prod abs_T2 id) y)"

lemma suitable_bij:
  "suitable11 pick1 \<Longrightarrow> bij (pick1 x p)"
  "suitable12 pick2 \<Longrightarrow> bij (pick2 x p)"
  "suitable21 pick3 \<Longrightarrow> bij (pick3 x' p)"
  "suitable22 pick4 \<Longrightarrow> bij (pick4 x' p)"
     apply (unfold suitable_defs)
     apply ((erule allE conjE)+, assumption)+
  done

lemma suitable_supp_bound:
  "suitable11 pick1 \<Longrightarrow> |supp (pick1 x (p::('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}) P))| <o |UNIV::'var set|"
  "suitable12 pick2 \<Longrightarrow> |supp (pick2 x p)| <o |UNIV::'tyvar set|"
  "suitable21 pick3 \<Longrightarrow> |supp (pick3 x' p)| <o |UNIV::'var set|"
  "suitable22 pick4 \<Longrightarrow> |supp (pick4 x' p)| <o |UNIV::'tyvar set|"
     apply (unfold suitable_defs)
     apply ((erule allE conjE)+, assumption)+
  done

function f_T1 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) U1"
  and f_T2 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2" where
  "f_T1 pick1 pick2 pick3 pick4 (raw_T1_ctor x) p = (if suitable11 pick1 \<and> suitable12 pick2 \<and> suitable21 pick3 \<and> suitable22 pick4 then
  U1ctor' (map_T1_pre id id id id id id
    (\<lambda>t. (t, f_T1 pick1 pick2 pick3 pick4 t)) (\<lambda>t. (t, f_T1 pick1 pick2 pick3 pick4 t))
    (\<lambda>t. (t, f_T2 pick1 pick2 pick3 pick4 t)) (\<lambda>t. (t, f_T2 pick1 pick2 pick3 pick4 t)) (
  map_T1_pre id id id id (pick1 x p) (pick2 x p) id
    (rename_T1 (pick1 x p) (pick2 x p)) id (rename_T2 (pick1 x p) id) x
  )) p
else undefined)"
| "f_T2 pick1 pick2 pick3 pick4 (raw_T2_ctor x) p = (if suitable11 pick1 \<and> suitable12 pick2 \<and> suitable21 pick3 \<and> suitable22 pick4 then
  U2ctor' (map_T2_pre id id id id id id
    (\<lambda>t. (t, f_T1 pick1 pick2 pick3 pick4 t)) (\<lambda>t. (t, f_T1 pick1 pick2 pick3 pick4 t))
    (\<lambda>t. (t, f_T2 pick1 pick2 pick3 pick4 t)) (\<lambda>t. (t, f_T2 pick1 pick2 pick3 pick4 t)) (
  map_T2_pre id id id id (pick3 x p) (pick4 x p) id
    (rename_T1 (pick3 x p) (pick4 x p)) id (rename_T2 (pick3 x p) id) x
  )) p
else undefined)"
     apply pat_completeness
  by simp_all
termination
  apply (relation "inv_image {(x, y). case x of
    Inl t1 \<Rightarrow> (case y of Inl t1' \<Rightarrow> subshape_T1_T1 t1 t1' | Inr t2 \<Rightarrow> subshape_T1_T2 t1 t2)
  | Inr t2 \<Rightarrow> (case y of Inl t1 \<Rightarrow> subshape_T2_T1 t2 t1 | Inr t2' \<Rightarrow> subshape_T2_T2 t2 t2')
 } (map_sum (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd))")
          apply (rule wf_inv_image)
          apply (rule T1.wf_subshape)

(* ALLGOALS *)
  subgoal
    apply (unfold in_inv_image map_sum.simps comp_def snd_conv fst_conv mem_Collect_eq prod.case sum.case)
    apply (erule conjE)+
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
     apply (rule T1_pre.set_map T2_pre.set_map)
           apply (rule supp_id_bound bij_id | erule suitable_bij suitable_supp_bound | assumption)+
    apply (
        (unfold image_id, erule T1.set_subshapes)
        | (erule T1.set_subshape_images[rotated -1], (rule bij_id supp_id_bound | erule suitable_bij suitable_supp_bound | assumption)+))
    done

(* copied from above *)
  subgoal
    apply (unfold in_inv_image map_sum.simps comp_def snd_conv fst_conv mem_Collect_eq prod.case sum.case)
    apply (erule conjE)+
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
     apply (rule T1_pre.set_map T2_pre.set_map)
           apply (rule supp_id_bound bij_id | erule suitable_bij suitable_supp_bound | assumption)+
    apply (
        (unfold image_id, erule T1.set_subshapes)
        | (erule T1.set_subshape_images[rotated -1], (rule bij_id supp_id_bound | erule suitable_bij suitable_supp_bound | assumption)+))
    done
  subgoal
    apply (unfold in_inv_image map_sum.simps comp_def snd_conv fst_conv mem_Collect_eq prod.case sum.case)
    apply (erule conjE)+
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
     apply (rule T1_pre.set_map T2_pre.set_map)
           apply (rule supp_id_bound bij_id | erule suitable_bij suitable_supp_bound | assumption)+
    apply (
        (unfold image_id, erule T1.set_subshapes)
        | (erule T1.set_subshape_images[rotated -1], (rule bij_id supp_id_bound | erule suitable_bij suitable_supp_bound | assumption)+))
    done
  subgoal
    apply (unfold in_inv_image map_sum.simps comp_def snd_conv fst_conv mem_Collect_eq prod.case sum.case)
    apply (erule conjE)+
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
     apply (rule T1_pre.set_map T2_pre.set_map)
           apply (rule supp_id_bound bij_id | erule suitable_bij suitable_supp_bound | assumption)+
    apply (
        (unfold image_id, erule T1.set_subshapes)
        | (erule T1.set_subshape_images[rotated -1], (rule bij_id supp_id_bound | erule suitable_bij suitable_supp_bound | assumption)+))
    done
  subgoal
    apply (unfold in_inv_image map_sum.simps comp_def snd_conv fst_conv mem_Collect_eq prod.case sum.case)
    apply (erule conjE)+
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
     apply (rule T1_pre.set_map T2_pre.set_map)
           apply (rule supp_id_bound bij_id | erule suitable_bij suitable_supp_bound | assumption)+
    apply (
        (unfold image_id, erule T1.set_subshapes)
        | (erule T1.set_subshape_images[rotated -1], (rule bij_id supp_id_bound | erule suitable_bij suitable_supp_bound | assumption)+))
    done
  subgoal
    apply (unfold in_inv_image map_sum.simps comp_def snd_conv fst_conv mem_Collect_eq prod.case sum.case)
    apply (erule conjE)+
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
     apply (rule T1_pre.set_map T2_pre.set_map)
           apply (rule supp_id_bound bij_id | erule suitable_bij suitable_supp_bound | assumption)+
    apply (
        (unfold image_id, erule T1.set_subshapes)
        | (erule T1.set_subshape_images[rotated -1], (rule bij_id supp_id_bound | erule suitable_bij suitable_supp_bound | assumption)+))
    done
  subgoal
    apply (unfold in_inv_image map_sum.simps comp_def snd_conv fst_conv mem_Collect_eq prod.case sum.case)
    apply (erule conjE)+
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
     apply (rule T1_pre.set_map T2_pre.set_map)
           apply (rule supp_id_bound bij_id | erule suitable_bij suitable_supp_bound | assumption)+
    apply (
        (unfold image_id, erule T1.set_subshapes)
        | (erule T1.set_subshape_images[rotated -1], (rule bij_id supp_id_bound | erule suitable_bij suitable_supp_bound | assumption)+))
    done
  subgoal
    apply (unfold in_inv_image map_sum.simps comp_def snd_conv fst_conv mem_Collect_eq prod.case sum.case)
    apply (erule conjE)+
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
     apply (rule T1_pre.set_map T2_pre.set_map)
           apply (rule supp_id_bound bij_id | erule suitable_bij suitable_supp_bound | assumption)+
    apply (
        (unfold image_id, erule T1.set_subshapes)
        | (erule T1.set_subshape_images[rotated -1], (rule bij_id supp_id_bound | erule suitable_bij suitable_supp_bound | assumption)+))
    done
  done
print_theorems

lemma f_T1_simp: "suitable11 pick1 \<Longrightarrow> suitable12 pick2 \<Longrightarrow> suitable21 pick3 \<Longrightarrow> suitable22 pick4 \<Longrightarrow>
  f_T1 pick1 pick2 pick3 pick4 (raw_T1_ctor x) p =
    U1ctor' (map_T1_pre id id id id (pick1 x p) (pick2 x p)
      (\<lambda>t. (t, f_T1 pick1 pick2 pick3 pick4 t))
      (\<lambda>t. (rename_T1 (pick1 x p) (pick2 x p) t, f_T1 pick1 pick2 pick3 pick4 (rename_T1 (pick1 x p) (pick2 x p) t)))
      (\<lambda>t. (t, f_T2 pick1 pick2 pick3 pick4 t))
      (\<lambda>t. (rename_T2 (pick1 x p) id t, f_T2 pick1 pick2 pick3 pick4 (rename_T2 (pick1 x p) id t)))
     x) p"
  apply (unfold f_T1.simps)
  apply (subst if_P)
   apply ((rule conjI)?, assumption)+
  apply (rule arg_cong2[OF _ refl, of _ _ U1ctor'])
  apply (rule trans)
   apply (rule T1_pre.map_comp)
                apply (rule supp_id_bound bij_id | erule suitable_bij suitable_supp_bound)+
  apply (unfold id_o o_id)
  apply (unfold comp_def)
  apply (rule refl)
  done
lemma f_T2_simp: "suitable11 pick1 \<Longrightarrow> suitable12 pick2 \<Longrightarrow> suitable21 pick3 \<Longrightarrow> suitable22 pick4 \<Longrightarrow>
  f_T2 pick1 pick2 pick3 pick4 (raw_T2_ctor x) p =
    U2ctor' (map_T2_pre id id id id (pick3 x p) (pick4 x p)
      (\<lambda>t. (t, f_T1 pick1 pick2 pick3 pick4 t))
      (\<lambda>t. (rename_T1 (pick3 x p) (pick4 x p) t, f_T1 pick1 pick2 pick3 pick4 (rename_T1 (pick3 x p) (pick4 x p) t)))
      (\<lambda>t. (t, f_T2 pick1 pick2 pick3 pick4 t))
      (\<lambda>t. (rename_T2 (pick3 x p) id t, f_T2 pick1 pick2 pick3 pick4 (rename_T2 (pick3 x p) id t)))
     x) p"
  apply (unfold f_T2.simps)
  apply (subst if_P)
   apply ((rule conjI)?, assumption)+
  apply (rule arg_cong2[OF _ refl, of _ _ U2ctor'])
  apply (rule trans)
   apply (rule T2_pre.map_comp)
                apply (rule supp_id_bound bij_id | erule suitable_bij suitable_supp_bound)+
  apply (unfold id_o o_id)
  apply (unfold comp_def)
  apply (rule refl)
  done

definition "pick1_0 \<equiv> SOME pick. suitable11 pick"
definition "pick2_0 \<equiv> SOME pick. suitable12 pick"
definition "pick3_0 \<equiv> SOME pick. suitable21 pick"
definition "pick4_0 \<equiv> SOME pick. suitable22 pick"

definition "f0_T1 \<equiv> f_T1 pick1_0 pick2_0 pick3_0 pick4_0"
definition "f0_T2 \<equiv> f_T2 pick1_0 pick2_0 pick3_0 pick4_0"

abbreviation "rep_T1 \<equiv> quot_type.rep Rep_T1"
abbreviation "rep_T2 \<equiv> quot_type.rep Rep_T2"

definition "ff0_T1 t \<equiv> f0_T1 (rep_T1 t)"
definition "ff0_T2 t \<equiv> f0_T2 (rep_T2 t)"

definition noclash_T1 :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) pre_T1 \<Rightarrow> bool" where
  "noclash_T1 x \<equiv> (
    (set5_T1_pre x \<inter> (set1_T1_pre x \<union> \<Union>(FVars_T11 ` set7_T1_pre x) \<union> \<Union>(FVars_T21 ` set9_T1_pre x)) = {})
    \<and> (set6_T1_pre x \<inter> (set2_T1_pre x \<union> \<Union>(FVars_T12 ` set7_T1_pre x) \<union> \<Union>(FVars_T22 ` set9_T1_pre x) \<union> \<Union>(FVars_T22 ` set10_T1_pre x)) = {})
  )"
definition noclash_T2 :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) pre_T2 \<Rightarrow> bool" where
  "noclash_T2 x \<equiv> (
    (set5_T2_pre x \<inter> (set1_T2_pre x \<union> \<Union>(FVars_T11 ` set7_T2_pre x) \<union> \<Union>(FVars_T21 ` set9_T2_pre x)) = {})
    \<and> (set6_T2_pre x \<inter> (set2_T2_pre x \<union> \<Union>(FVars_T12 ` set7_T2_pre x) \<union> \<Union>(FVars_T22 ` set9_T2_pre x) \<union> \<Union>(FVars_T22 ` set10_T2_pre x)) = {})
  )"

type_synonym ('var, 'tyvar, 'a, 'b) pre_TT1 = "('var, 'tyvar, 'a, 'b, 'var, 'tyvar,
  ('var, 'tyvar, 'a, 'b) T1, ('var, 'tyvar, 'a, 'b) T1,
  ('var, 'tyvar, 'a, 'b) T2, ('var, 'tyvar, 'a, 'b) T2
) T1_pre"
type_synonym ('var, 'tyvar, 'a, 'b) pre_TT2 = "('var, 'tyvar, 'a, 'b, 'var, 'tyvar,
  ('var, 'tyvar, 'a, 'b) T1, ('var, 'tyvar, 'a, 'b) T1,
  ('var, 'tyvar, 'a, 'b) T2, ('var, 'tyvar, 'a, 'b) T2
) T2_pre"

definition nnoclash_T1 :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) pre_TT1 \<Rightarrow> bool" where
  "nnoclash_T1 x \<equiv> (
    (set5_T1_pre x \<inter> (set1_T1_pre x \<union> \<Union>(FFVars_T11 ` set7_T1_pre x) \<union> \<Union>(FFVars_T21 ` set9_T1_pre x)) = {})
    \<and> (set6_T1_pre x \<inter> (set2_T1_pre x \<union> \<Union>(FFVars_T12 ` set7_T1_pre x) \<union> \<Union>(FFVars_T22 ` set9_T1_pre x) \<union> \<Union>(FFVars_T22 ` set10_T1_pre x)) = {})
  )"
definition nnoclash_T2 :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) pre_TT2 \<Rightarrow> bool" where
  "nnoclash_T2 x \<equiv> (
    (set5_T2_pre x \<inter> (set1_T2_pre x \<union> \<Union>(FFVars_T11 ` set7_T2_pre x) \<union> \<Union>(FFVars_T21 ` set9_T2_pre x)) = {})
    \<and> (set6_T2_pre x \<inter> (set2_T2_pre x \<union> \<Union>(FFVars_T12 ` set7_T2_pre x) \<union> \<Union>(FFVars_T22 ` set9_T2_pre x) \<union> \<Union>(FFVars_T22 ` set10_T2_pre x)) = {})
  )"

definition XXl1 where
  "XXl1 pick1 pick2 pick3 pick4 f1 f2 p x \<equiv>
    map_T1_pre f1 f2 id id (f1 \<circ> pick1 x (Pmap (inv f1) (inv f2) p)) (f2 \<circ> pick2 x (Pmap (inv f1) (inv f2) p))
      (\<lambda>t. (rename_T1 f1 f2 t, PU1map' f1 f2 t (f_T1 pick1 pick2 pick3 pick4 t)))
      (\<lambda>t. (rename_T1 (f1 \<circ> pick1 x (Pmap (inv f1) (inv f2) p)) (f2 \<circ> pick2 x (Pmap (inv f1) (inv f2) p)) t, PU1map' f1 f2
        (rename_T1 (pick1 x (Pmap (inv f1) (inv f2) p)) (pick2 x (Pmap (inv f1) (inv f2) p)) t)
        (f_T1 pick1 pick2 pick3 pick4 (rename_T1 (pick1 x (Pmap (inv f1) (inv f2) p)) (pick2 x (Pmap (inv f1) (inv f2) p)) t))
      ))
      (\<lambda>t. (rename_T2 f1 f2 t, PU2map' f1 f2 t (f_T2 pick1 pick2 pick3 pick4 t)))
      (\<lambda>t. (rename_T2 (f1 \<circ> pick1 x (Pmap (inv f1) (inv f2) p)) f2 t, PU2map' f1 f2
        (rename_T2 (pick1 x (Pmap (inv f1) (inv f2) p)) id t)
        (f_T2 pick1 pick2 pick3 pick4 (rename_T2 (pick1 x (Pmap (inv f1) (inv f2) p)) id t))
      ))
      x
  "
definition XXl2 where
  "XXl2 pick1 pick2 pick3 pick4 f1 f2 p x \<equiv>
    map_T2_pre f1 f2 id id (f1 \<circ> pick3 x (Pmap (inv f1) (inv f2) p)) (f2 \<circ> pick4 x (Pmap (inv f1) (inv f2) p))
      (\<lambda>t. (rename_T1 f1 f2 t, PU1map' f1 f2 t (f_T1 pick1 pick2 pick3 pick4 t)))
      (\<lambda>t. (rename_T1 (f1 \<circ> pick3 x (Pmap (inv f1) (inv f2) p)) (f2 \<circ> pick4 x (Pmap (inv f1) (inv f2) p)) t, PU1map' f1 f2
        (rename_T1 (pick3 x (Pmap (inv f1) (inv f2) p)) (pick4 x (Pmap (inv f1) (inv f2) p)) t)
        (f_T1 pick1 pick2 pick3 pick4 (rename_T1 (pick3 x (Pmap (inv f1) (inv f2) p)) (pick4 x (Pmap (inv f1) (inv f2) p)) t))
      ))
      (\<lambda>t. (rename_T2 f1 f2 t, PU2map' f1 f2 t (f_T2 pick1 pick2 pick3 pick4 t)))
      (\<lambda>t. (rename_T2 (f1 \<circ> pick3 x (Pmap (inv f1) (inv f2) p)) f2 t, PU2map' f1 f2
        (rename_T2 (pick3 x (Pmap (inv f1) (inv f2) p)) id t)
        (f_T2 pick1 pick2 pick3 pick4 (rename_T2 (pick3 x (Pmap (inv f1) (inv f2) p)) id t))
      ))
      x
  "

definition XXr1 where
  "XXr1 pick1 pick2 pick3 pick4 f1 f2 p x \<equiv>
    map_T1_pre f1 f2 id id
      (pick1 (map_T1_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p \<circ> f1)
      (pick2 (map_T1_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p \<circ> f2)
      (\<lambda>t. (rename_T1 f1 f2 t, f_T1 pick1 pick2 pick3 pick4 (rename_T1 f1 f2 t)))
      (\<lambda>t. (rename_T1
        (pick1 (map_T1_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p \<circ> f1)
        (pick2 (map_T1_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p \<circ> f2)
       t, f_T1 pick1 pick2 pick3 pick4 (rename_T1
        (pick1 (map_T1_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p \<circ> f1)
        (pick2 (map_T1_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p \<circ> f2)
       t)
      ))
      (\<lambda>t. (rename_T2 f1 f2 t, f_T2 pick1 pick2 pick3 pick4 (rename_T2 f1 f2 t)))
      (\<lambda>t. (rename_T2
        (pick1 (map_T1_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p \<circ> f1)
        f2
       t, f_T2 pick1 pick2 pick3 pick4 (rename_T2
        (pick1 (map_T1_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p \<circ> f1)
        f2
       t)
      ))
      x
  "
definition XXr2 where
  "XXr2 pick1 pick2 pick3 pick4 f1 f2 p x \<equiv>
    map_T2_pre f1 f2 id id
      (pick3 (map_T2_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p \<circ> f1)
      (pick4 (map_T2_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p \<circ> f2)
      (\<lambda>t. (rename_T1 f1 f2 t, f_T1 pick1 pick2 pick3 pick4 (rename_T1 f1 f2 t)))
      (\<lambda>t. (rename_T1
        (pick3 (map_T2_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p \<circ> f1)
        (pick4 (map_T2_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p \<circ> f2)
       t, f_T1 pick1 pick2 pick3 pick4 (rename_T1
        (pick3 (map_T2_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p \<circ> f1)
        (pick4 (map_T2_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p \<circ> f2)
       t)
      ))
      (\<lambda>t. (rename_T2 f1 f2 t, f_T2 pick1 pick2 pick3 pick4 (rename_T2 f1 f2 t)))
      (\<lambda>t. (rename_T2
        (pick3 (map_T2_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p \<circ> f1)
        f2
       t, f_T2 pick1 pick2 pick3 pick4 (rename_T2
        (pick3 (map_T2_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p \<circ> f1)
        f2
       t)
      ))
      x
  "

(**********************************************************************)
(*                               PROOFS                               *)
(**********************************************************************)

lemma pick_id_ons:
  "suitable11 pick1 \<Longrightarrow> id_on ((\<Union>(FVars_T11 ` set8_T1_pre x) - set5_T1_pre x) \<union> (\<Union>(FVars_T21 ` set10_T1_pre x) - set5_T1_pre x)) (pick1 x p)"
  "suitable12 pick2 \<Longrightarrow> id_on (\<Union>(FVars_T12 ` set8_T1_pre x) - set6_T1_pre x) (pick2 x p)"
  "suitable21 pick3 \<Longrightarrow> id_on ((\<Union>(FVars_T11 ` set8_T2_pre y) - set5_T2_pre y) \<union> (\<Union>(FVars_T21 ` set10_T2_pre y) - set5_T2_pre y)) (pick3 y p)"
  "suitable22 pick4 \<Longrightarrow> id_on (\<Union>(FVars_T12 ` set8_T2_pre y) - set6_T2_pre y) (pick4 y p)"
     apply (unfold suitable_defs Int_Un_distrib Un_empty Un_Diff Diff_idemp T1.FVars_ctors)

(* ALLGOALS *)
     apply (erule allE conjE)+
     apply (rule imsupp_id_on)
     apply ((unfold Int_Un_distrib Un_empty)[1])?
     apply ((rule conjI)?, assumption)+
    (* copied from above*)
    apply (erule allE conjE)+
    apply (rule imsupp_id_on)
    apply ((unfold Int_Un_distrib Un_empty)[1])?
    apply ((rule conjI)?, assumption)+
   apply (erule allE conjE)+
   apply (rule imsupp_id_on)
   apply ((unfold Int_Un_distrib Un_empty)[1])?
   apply ((rule conjI)?, assumption)+
  apply (erule allE conjE)+
  apply (rule imsupp_id_on)
  apply ((unfold Int_Un_distrib Un_empty)[1])?
  apply ((rule conjI)?, assumption)+
  done

lemma pick_id_ons':
  "suitable11 pick1 \<Longrightarrow> id_on (\<Union>(FVars_T11 ` set8_T1_pre x) - set5_T1_pre x) (pick1 x p)"
  "suitable11 pick1 \<Longrightarrow> id_on (\<Union>(FVars_T21 ` set10_T1_pre x) - set5_T1_pre x) (pick1 x p)"
  "suitable12 pick2 \<Longrightarrow> id_on (\<Union>(FVars_T12 ` set8_T1_pre x) - set6_T1_pre x) (pick2 x p)"
  "suitable21 pick3 \<Longrightarrow> id_on (\<Union>(FVars_T11 ` set8_T2_pre y) - set5_T2_pre y) (pick3 y p)"
  "suitable21 pick3 \<Longrightarrow> id_on (\<Union>(FVars_T21 ` set10_T2_pre y) - set5_T2_pre y) (pick3 y p)"
  "suitable22 pick4 \<Longrightarrow> id_on (\<Union>(FVars_T12 ` set8_T2_pre y) - set6_T2_pre y) (pick4 y p)"
       apply -
       apply (drule pick_id_ons[unfolded id_on_Un], ((erule conjE)+)?, assumption)+
  done

lemma pick_id_on_images:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows
    "suitable11 pick1 \<Longrightarrow> id_on (f1 ` ((\<Union>(FVars_T11 ` set8_T1_pre x) - set5_T1_pre x) \<union> (\<Union>(FVars_T21 ` set10_T1_pre x) - set5_T1_pre x))) (pick1 (map_T1_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p)"
    "suitable12 pick2 \<Longrightarrow> id_on (f2 ` (\<Union>(FVars_T12 ` set8_T1_pre x) - set6_T1_pre x)) (pick2 (map_T1_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p)"
    "suitable21 pick3 \<Longrightarrow> id_on (f1 ` ((\<Union>(FVars_T11 ` set8_T2_pre y) - set5_T2_pre y) \<union> (\<Union>(FVars_T21 ` set10_T2_pre y) - set5_T2_pre y))) (pick3 (map_T2_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) y) p)"
    "suitable22 pick4 \<Longrightarrow> id_on (f2 ` (\<Union>(FVars_T12 ` set8_T2_pre y) - set6_T2_pre y)) (pick4 (map_T2_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) y) p)"
     apply -
    (* EVERY' (map ... pick_id_ons) *)
     apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ id_on], rotated])
      apply (erule pick_id_ons(1))
     apply (subst T1_pre.set_map T2_pre.set_map T1.FVars_renames image_set_diff[OF bij_is_inj] comp_def image_comp image_UN,
      ((rule supp_id_bound bij_id assms)+)?
      )+
     apply (unfold image_UN[symmetric])
     apply (subst image_set_diff[OF bij_is_inj, symmetric], rule assms)+
     apply (unfold image_Un[symmetric])?
     apply (rule refl)
    (* copied from above (incremented index) *)
    apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ id_on], rotated])
     apply (erule pick_id_ons(2))
    apply (subst T1_pre.set_map T2_pre.set_map T1.FVars_renames image_set_diff[OF bij_is_inj] comp_def image_comp image_UN,
      ((rule supp_id_bound bij_id assms)+)?
      )+
    apply (unfold image_UN[symmetric])
    apply (subst image_set_diff[OF bij_is_inj, symmetric], rule assms)+
    apply (unfold image_Un[symmetric])?
    apply (rule refl)
   apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ id_on], rotated])
    apply (erule pick_id_ons(3))
   apply (subst T1_pre.set_map T2_pre.set_map T1.FVars_renames image_set_diff[OF bij_is_inj] comp_def image_comp image_UN,
      ((rule supp_id_bound bij_id assms)+)?
      )+
   apply (unfold image_UN[symmetric])
   apply (subst image_set_diff[OF bij_is_inj, symmetric], rule assms)+
   apply (unfold image_Un[symmetric])?
   apply (rule refl)
  apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ id_on], rotated])
   apply (erule pick_id_ons(4))
  apply (subst T1_pre.set_map T2_pre.set_map T1.FVars_renames image_set_diff[OF bij_is_inj] comp_def image_comp image_UN,
      ((rule supp_id_bound bij_id assms)+)?
      )+
  apply (unfold image_UN[symmetric])
  apply (subst image_set_diff[OF bij_is_inj, symmetric], rule assms)+
  apply (unfold image_Un[symmetric])?
  apply (rule refl)
  done

lemma pick_id_on_images':
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows
    "suitable11 pick1 \<Longrightarrow> id_on (f1 ` (\<Union>(FVars_T11 ` set8_T1_pre x) - set5_T1_pre x)) (pick1 (map_T1_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p)"
    "suitable11 pick1 \<Longrightarrow> id_on (f1 ` (\<Union>(FVars_T21 ` set10_T1_pre x) - set5_T1_pre x)) (pick1 (map_T1_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p)"
    "suitable12 pick2 \<Longrightarrow> id_on (f2 ` (\<Union>(FVars_T12 ` set8_T1_pre x) - set6_T1_pre x)) (pick2 (map_T1_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) x) p)"
    "suitable21 pick3 \<Longrightarrow> id_on (f1 ` (\<Union>(FVars_T11 ` set8_T2_pre y) - set5_T2_pre y)) (pick3 (map_T2_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) y) p)"
    "suitable21 pick3 \<Longrightarrow> id_on (f1 ` (\<Union>(FVars_T21 ` set10_T2_pre y) - set5_T2_pre y)) (pick3 (map_T2_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) y) p)"
    "suitable22 pick4 \<Longrightarrow> id_on (f2 ` (\<Union>(FVars_T12 ` set8_T2_pre y) - set6_T2_pre y)) (pick4 (map_T2_pre f1 f2 id id f1 f2 (rename_T1 f1 f2) (rename_T1 f1 f2) (rename_T2 f1 f2) (rename_T2 f1 f2) y) p)"
       apply -
       apply (drule pick_id_on_images[OF assms, unfolded image_Un id_on_Un], ((erule conjE)+)?, assumption)+
  done

(* lower axioms to raw type *)
lemma U1map'_U1ctor': "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U1map' f1 f2 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) (U1ctor' y p)
= U1ctor' (map_T1_pre f1 f2 id id f1 f2
    (\<lambda>(t, pu). (rename_T1 f1 f2 t, PU1map' f1 f2 t pu))
    (\<lambda>(t, pu). (rename_T1 f1 f2 t, PU1map' f1 f2 t pu))
    (\<lambda>(t, pu). (rename_T2 f1 f2 t, PU2map' f1 f2 t pu))
    (\<lambda>(t, pu). (rename_T2 f1 f2 t, PU2map' f1 f2 t pu))
 y) (Pmap f1 f2 p)"
  apply (unfold U1map'_def U2map'_def U1ctor'_def U2ctor'_def PU1map'_def PU2map'_def T1.TT_abs_ctors)
  apply (subst T1_pre.map_comp T2_pre.map_comp, (rule supp_id_bound bij_id)+)
  apply (unfold fst_comp_map_prod)
  apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric], (rule supp_id_bound bij_id)+)
  apply (rule trans)
   apply (rule U1map_Uctor U2map_Uctor)
      apply assumption+
  apply (rule arg_cong2[OF _ refl, of _ _ U1ctor] arg_cong2[OF _ refl, of _ _ U2ctor])
  apply (rule trans)
   apply (rule T1_pre.map_comp T2_pre.map_comp)
                apply (rule supp_id_bound bij_id | assumption)+
  apply (rule sym)
  apply (rule trans)
   apply (rule T1_pre.map_comp T2_pre.map_comp)
                apply (rule supp_id_bound bij_id | assumption)+
  apply (unfold id_o o_id)
  apply (rule T1_pre.map_cong T2_pre.map_cong)
                      apply (rule supp_id_bound bij_id | assumption)+
            apply (unfold comp_def case_prod_map_prod split_beta fst_map_prod snd_map_prod map_prod_simp id_def)
    (* ALLGOALS (refl ORELSE ...) *) apply (rule refl)+
     apply (rule iffD2[OF prod.inject])
     apply (rule conjI)
      apply (unfold rrename_T1_def rrename_T2_def)[1]
      apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule supp_id_bound bij_id | assumption)+
      apply (rule T1.TT_alpha_quotient_syms)
     apply (rule refl)
    (* copied from above *)
    apply (rule iffD2[OF prod.inject])
    apply (rule conjI)
     apply (unfold rrename_T1_def rrename_T2_def)[1]
     apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
     apply (rule T1.alpha_bij_eqs[THEN iffD2])
         apply (rule supp_id_bound bij_id | assumption)+
     apply (rule T1.TT_alpha_quotient_syms)
    apply (rule refl)
   apply (rule iffD2[OF prod.inject])
   apply (rule conjI)
    apply (unfold rrename_T1_def rrename_T2_def)[1]
    apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
    apply (rule T1.alpha_bij_eqs[THEN iffD2])
        apply (rule supp_id_bound bij_id | assumption)+
    apply (rule T1.TT_alpha_quotient_syms)
   apply (rule refl)
  apply (rule iffD2[OF prod.inject])
  apply (rule conjI)
   apply (unfold rrename_T1_def rrename_T2_def)[1]
   apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
   apply (rule T1.alpha_bij_eqs[THEN iffD2])
       apply (rule supp_id_bound bij_id | assumption)+
   apply (rule T1.TT_alpha_quotient_syms)
  apply (rule refl)
  done
lemma U2map'_Uctor': "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U2map' f1 f2 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst y2)) (U2ctor' y2 p)
= U2ctor' (map_T2_pre f1 f2 id id f1 f2
    (\<lambda>(t, pu). (rename_T1 f1 f2 t, PU1map' f1 f2 t pu))
    (\<lambda>(t, pu). (rename_T1 f1 f2 t, PU1map' f1 f2 t pu))
    (\<lambda>(t, pu). (rename_T2 f1 f2 t, PU2map' f1 f2 t pu))
    (\<lambda>(t, pu). (rename_T2 f1 f2 t, PU2map' f1 f2 t pu))
 y2) (Pmap f1 f2 p)"
  (* same tactic as above *)
  apply (unfold U1map'_def U2map'_def U1ctor'_def U2ctor'_def PU1map'_def PU2map'_def T1.TT_abs_ctors)
  apply (subst T1_pre.map_comp T2_pre.map_comp, (rule supp_id_bound bij_id)+)
  apply (unfold fst_comp_map_prod)
  apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric], (rule supp_id_bound bij_id)+)
  apply (rule trans)
   apply (rule U1map_Uctor U2map_Uctor)
      apply assumption+
  apply (rule arg_cong2[OF _ refl, of _ _ U1ctor] arg_cong2[OF _ refl, of _ _ U2ctor])
  apply (rule trans)
   apply (rule T1_pre.map_comp T2_pre.map_comp)
                apply (rule supp_id_bound bij_id | assumption)+
  apply (rule sym)
  apply (rule trans)
   apply (rule T1_pre.map_comp T2_pre.map_comp)
                apply (rule supp_id_bound bij_id | assumption)+
  apply (unfold id_o o_id)
  apply (rule T1_pre.map_cong T2_pre.map_cong)
                      apply (rule supp_id_bound bij_id | assumption)+
            apply (unfold comp_def case_prod_map_prod split_beta fst_map_prod snd_map_prod map_prod_simp id_def)
            apply (rule refl)+
     apply (rule iffD2[OF prod.inject])
     apply (rule conjI)
      apply (unfold rrename_T1_def rrename_T2_def)[1]
      apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule supp_id_bound bij_id | assumption)+
      apply (rule T1.TT_alpha_quotient_syms)
     apply (rule refl)
    apply (rule iffD2[OF prod.inject])
    apply (rule conjI)
     apply (unfold rrename_T1_def rrename_T2_def)[1]
     apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
     apply (rule T1.alpha_bij_eqs[THEN iffD2])
         apply (rule supp_id_bound bij_id | assumption)+
     apply (rule T1.TT_alpha_quotient_syms)
    apply (rule refl)
   apply (rule iffD2[OF prod.inject])
   apply (rule conjI)
    apply (unfold rrename_T1_def rrename_T2_def)[1]
    apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
    apply (rule T1.alpha_bij_eqs[THEN iffD2])
        apply (rule supp_id_bound bij_id | assumption)+
    apply (rule T1.TT_alpha_quotient_syms)
   apply (rule refl)
  apply (rule iffD2[OF prod.inject])
  apply (rule conjI)
   apply (unfold rrename_T1_def rrename_T2_def)[1]
   apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
   apply (rule T1.alpha_bij_eqs[THEN iffD2])
       apply (rule supp_id_bound bij_id | assumption)+
   apply (rule T1.TT_alpha_quotient_syms)
  apply (rule refl)
  done

lemmas FVars_def2s = T1.alpha_FVarss(1)[OF T1.TT_alpha_quotient_syms(1),
    unfolded fun_cong[OF meta_eq_to_obj_eq[OF FFVars_T11_def], symmetric]
    ] T1.alpha_FVarss(2)[OF T1.TT_alpha_quotient_syms(2),
    unfolded fun_cong[OF meta_eq_to_obj_eq[OF FFVars_T21_def], symmetric]
    ] T1.alpha_FVarss(3)[OF T1.TT_alpha_quotient_syms(1),
    unfolded fun_cong[OF meta_eq_to_obj_eq[OF FFVars_T12_def], symmetric]
    ] T1.alpha_FVarss(4)[OF T1.TT_alpha_quotient_syms(2),
    unfolded fun_cong[OF meta_eq_to_obj_eq[OF FFVars_T22_def], symmetric]
    ]

lemma U1FVars'_subsets: "set5_T1_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T1_pre) \<inter> (PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T1_pre y \<union> set8_T1_pre y \<Longrightarrow> U1FVars_1' t (pu p) \<subseteq> FVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y \<union> set10_T1_pre y \<Longrightarrow> U2FVars_1' t (pu p) \<subseteq> FVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  U1FVars_1' (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) (U1ctor' y p) \<subseteq> FVars_T11 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> PFVars_1 p \<union> avoiding_set1"
  "set6_T1_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T1_pre) \<inter> (PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T1_pre y \<union> set8_T1_pre y \<Longrightarrow> U1FVars_2' t (pu p) \<subseteq> FVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y \<union> set10_T1_pre y \<Longrightarrow> U2FVars_2' t (pu p) \<subseteq> FVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  U1FVars_2' (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) (U1ctor' y p) \<subseteq> FVars_T12 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> PFVars_2 p \<union> avoiding_set2"
   apply -
  subgoal
    apply (unfold U1FVars_1'_def U1FVars_2'_def U2FVars_1'_def U2FVars_2'_def U1ctor'_def U2ctor'_def FVars_def2s T1.TT_abs_ctors)
    apply (subst T1_pre.map_comp T2_pre.map_comp, (rule supp_id_bound bij_id)+)
    apply (unfold fst_comp_map_prod)
    apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric], (rule supp_id_bound bij_id)+)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (subst T1_pre.map_comp T2_pre.map_comp, (rule supp_id_bound bij_id)+)
     apply (unfold fst_comp_map_prod)
     apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric], (rule supp_id_bound bij_id)+)
     apply (rule refl)
    apply (rule U1FVars_subsets U2FVars_subsets)
      apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)
      apply (unfold image_id image_Un[symmetric])
      apply assumption
      (* ALLGOALS *)
     apply ((subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)+, unfold image_id)?
     apply (subst (asm) T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)+
     apply (unfold image_Un[symmetric])
     apply (drule exists_map_prod_id)
     apply (erule exE)
     apply (erule conjE)
     apply hypsubst
     apply assumption
      (* copied from above *)
    apply ((subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)+, unfold image_id)?
    apply (subst (asm) T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)+
    apply (unfold image_Un[symmetric])
    apply (drule exists_map_prod_id)
    apply (erule exE)
    apply (erule conjE)
    apply hypsubst
    apply assumption
    done

(* copied from above *)
  subgoal
    apply (unfold U1FVars_1'_def U1FVars_2'_def U2FVars_1'_def U2FVars_2'_def U1ctor'_def U2ctor'_def FVars_def2s T1.TT_abs_ctors)
    apply (subst T1_pre.map_comp T2_pre.map_comp, (rule supp_id_bound bij_id)+)
    apply (unfold fst_comp_map_prod)
    apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric], (rule supp_id_bound bij_id)+)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (subst T1_pre.map_comp T2_pre.map_comp, (rule supp_id_bound bij_id)+)
     apply (unfold fst_comp_map_prod)
     apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric], (rule supp_id_bound bij_id)+)
     apply (rule refl)
    apply (rule U1FVars_subsets U2FVars_subsets)
      apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)
      apply (unfold image_id image_Un[symmetric])
      apply assumption
      (* ALLGOALS *)
     apply ((subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)+, unfold image_id)?
     apply (subst (asm) T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)+
     apply (unfold image_Un[symmetric])
     apply (drule exists_map_prod_id)
     apply (erule exE)
     apply (erule conjE)
     apply hypsubst
     apply assumption
      (* copied from above *)
    apply ((subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)+, unfold image_id)?
    apply (subst (asm) T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)+
    apply (unfold image_Un[symmetric])
    apply (drule exists_map_prod_id)
    apply (erule exE)
    apply (erule conjE)
    apply hypsubst
    apply assumption
    done
  done

lemma U2FVars'_subsets: "set5_T2_pre (y2::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T2_pre) \<inter> (PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T2_pre y2 \<union> set8_T2_pre y2 \<Longrightarrow> U1FVars_1' t (pu p) \<subseteq> FVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y2 \<union> set10_T2_pre y2 \<Longrightarrow> U2FVars_1' t (pu p) \<subseteq> FVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  U2FVars_1' (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst y2)) (U2ctor' y2 p) \<subseteq> FVars_T21 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst y2)) \<union> PFVars_1 p \<union> avoiding_set1"
  "set6_T2_pre y2 \<inter> (PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T2_pre y2 \<union> set8_T2_pre y2 \<Longrightarrow> U1FVars_2' t (pu p) \<subseteq> FVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y2 \<union> set10_T2_pre y2 \<Longrightarrow> U2FVars_2' t (pu p) \<subseteq> FVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  U2FVars_2' (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst y2)) (U2ctor' y2 p) \<subseteq> FVars_T22 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst y2)) \<union> PFVars_2 p \<union> avoiding_set2"
  (* same tactic as above *)
   apply -
  subgoal
    apply (unfold U1FVars_1'_def U1FVars_2'_def U2FVars_1'_def U2FVars_2'_def U1ctor'_def U2ctor'_def FVars_def2s T1.TT_abs_ctors)
    apply (subst T1_pre.map_comp T2_pre.map_comp, (rule supp_id_bound bij_id)+)
    apply (unfold fst_comp_map_prod)
    apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric], (rule supp_id_bound bij_id)+)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (subst T1_pre.map_comp T2_pre.map_comp, (rule supp_id_bound bij_id)+)
     apply (unfold fst_comp_map_prod)
     apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric], (rule supp_id_bound bij_id)+)
     apply (rule refl)
    apply (rule U1FVars_subsets U2FVars_subsets)
      apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)
      apply (unfold image_id image_Un[symmetric])
      apply assumption
      (* ALLGOALS *)
     apply ((subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)+, unfold image_id)?
     apply (subst (asm) T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)+
     apply (unfold image_Un[symmetric])
     apply (drule exists_map_prod_id)
     apply (erule exE)
     apply (erule conjE)
     apply hypsubst
     apply assumption
      (* copied from above *)
    apply ((subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)+, unfold image_id)?
    apply (subst (asm) T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)+
    apply (unfold image_Un[symmetric])
    apply (drule exists_map_prod_id)
    apply (erule exE)
    apply (erule conjE)
    apply hypsubst
    apply assumption
    done

(* copied from above *)
  subgoal
    apply (unfold U1FVars_1'_def U1FVars_2'_def U2FVars_1'_def U2FVars_2'_def U1ctor'_def U2ctor'_def FVars_def2s T1.TT_abs_ctors)
    apply (subst T1_pre.map_comp T2_pre.map_comp, (rule supp_id_bound bij_id)+)
    apply (unfold fst_comp_map_prod)
    apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric], (rule supp_id_bound bij_id)+)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (subst T1_pre.map_comp T2_pre.map_comp, (rule supp_id_bound bij_id)+)
     apply (unfold fst_comp_map_prod)
     apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric], (rule supp_id_bound bij_id)+)
     apply (rule refl)
    apply (rule U1FVars_subsets U2FVars_subsets)
      apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)
      apply (unfold image_id image_Un[symmetric])
      apply assumption
      (* ALLGOALS *)
     apply ((subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)+, unfold image_id)?
     apply (subst (asm) T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)+
     apply (unfold image_Un[symmetric])
     apply (drule exists_map_prod_id)
     apply (erule exE)
     apply (erule conjE)
     apply hypsubst
     apply assumption
      (* copied from above *)
    apply ((subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)+, unfold image_id)?
    apply (subst (asm) T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id)+)+
    apply (unfold image_Un[symmetric])
    apply (drule exists_map_prod_id)
    apply (erule exE)
    apply (erule conjE)
    apply hypsubst
    apply assumption
    done
  done

lemma Pmap_imsupp_empty:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
    "imsupp f1 \<inter> PFVars_1 p = {}" "imsupp f2 \<inter> PFVars_2 p = {}"
  shows "Pmap f1 f2 p = p"
  apply (rule Pmap_cong_id)
       apply (rule assms)+
   apply (erule id_onD[OF imsupp_id_on, rotated], rule assms)+
  done

lemma U1ctor_rename:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows
    "(\<And>t pu p. (t, pu) \<in> set7_T1_pre y \<union> set8_T1_pre y \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FFVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y \<union> set10_T1_pre y \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FFVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T1_pre y \<union> set8_T1_pre y \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FFVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y \<union> set10_T1_pre y \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  imsupp f1 \<inter> (FFVars_T11 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  imsupp f2 \<inter> (FFVars_T12 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  f1 ` set5_T1_pre y \<inter> set5_T1_pre y = {} \<Longrightarrow> f2 ` set6_T1_pre y \<inter> set6_T1_pre y = {} \<Longrightarrow>
  U1ctor y p = U1ctor (map_T1_pre f1 f2 id id f1 f2
    (\<lambda>(t, pu). (rrename_T1 f1 f2 t, PU1map f1 f2 t pu)) (\<lambda>(t, pu). (rrename_T1 f1 f2 t, PU1map f1 f2 t pu))
    (\<lambda>(t, pu). (rrename_T2 f1 f2 t, PU2map f1 f2 t pu)) (\<lambda>(t, pu). (rrename_T2 f1 f2 t, PU2map f1 f2 t pu))
  y) p"
  apply (rule sym)
  apply (rule trans)
   apply (rule trans)
    apply (rule arg_cong2[OF refl, of _ _ U1ctor] arg_cong2[OF refl, of _ _ U2ctor])
    apply (rule Pmap_imsupp_empty[symmetric, OF assms(1-4)])
     apply ((unfold Int_Un_distrib Un_empty)[1], (erule conjE)+, assumption)+
   apply (unfold PU1map_def PU2map_def)
   apply (rule U1map_Uctor[symmetric] U2map_Uctor[symmetric])
      apply (rule assms)+
  apply (rule U1map_cong_id U2map_cong_id)
       apply (rule assms)+
    (* ALLGOALS *)
   apply (drule set_rev_mp)
    apply (rule U1FVars_subsets U2FVars_subsets)
      apply (erule Int_subset_empty1[OF Int_Un_emptyI2[OF
          trans[OF arg_cong2[OF refl Un_assoc[symmetric], of "(\<inter>)"]]
          ] imsupp_image_subset])
      apply assumption+
   apply (erule id_onD[OF imsupp_id_on, rotated], assumption)
    (* copied from above *)
  apply (drule set_rev_mp)
   apply (rule U1FVars_subsets U2FVars_subsets)
     apply (erule Int_subset_empty1[OF Int_Un_emptyI2[OF
          trans[OF arg_cong2[OF refl Un_assoc[symmetric], of "(\<inter>)"]]
          ] imsupp_image_subset])
     apply assumption+
  apply (erule id_onD[OF imsupp_id_on, rotated], assumption)
  done
lemma U2ctor_rename:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows
    "(\<And>t pu p. (t, pu) \<in> set7_T2_pre y \<union> set8_T2_pre y \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FFVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y \<union> set10_T2_pre y \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FFVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T2_pre y \<union> set8_T2_pre y \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FFVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y \<union> set10_T2_pre y \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  imsupp f1 \<inter> (FFVars_T21 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) \<union> PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  imsupp f2 \<inter> (FFVars_T22 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) \<union> PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  f1 ` set5_T2_pre y \<inter> set5_T2_pre y = {} \<Longrightarrow> f2 ` set6_T2_pre y \<inter> set6_T2_pre y = {} \<Longrightarrow>
  U2ctor y p = U2ctor (map_T2_pre f1 f2 id id f1 f2
    (\<lambda>(t, pu). (rrename_T1 f1 f2 t, PU1map f1 f2 t pu)) (\<lambda>(t, pu). (rrename_T1 f1 f2 t, PU1map f1 f2 t pu))
    (\<lambda>(t, pu). (rrename_T2 f1 f2 t, PU2map f1 f2 t pu)) (\<lambda>(t, pu). (rrename_T2 f1 f2 t, PU2map f1 f2 t pu))
  y) p"
    (* same tactic as above *)
  apply (rule sym)
  apply (rule trans)
   apply (rule trans)
    apply (rule arg_cong2[OF refl, of _ _ U1ctor] arg_cong2[OF refl, of _ _ U2ctor])
    apply (rule Pmap_imsupp_empty[symmetric, OF assms(1-4)])
     apply ((unfold Int_Un_distrib Un_empty)[1], (erule conjE)+, assumption)+
   apply (unfold PU1map_def PU2map_def)
   apply (rule U1map_Uctor[symmetric] U2map_Uctor[symmetric])
      apply (rule assms)+
  apply (rule U1map_cong_id U2map_cong_id)
       apply (rule assms)+
    (* ALLGOALS *)
   apply (drule set_rev_mp)
    apply (rule U1FVars_subsets U2FVars_subsets)
      apply (erule Int_subset_empty1[OF Int_Un_emptyI2[OF
          trans[OF arg_cong2[OF refl Un_assoc[symmetric], of "(\<inter>)"]]
          ] imsupp_image_subset])
      apply assumption+
   apply (erule id_onD[OF imsupp_id_on, rotated], assumption)
    (* copied from above *)
  apply (drule set_rev_mp)
   apply (rule U1FVars_subsets U2FVars_subsets)
     apply (erule Int_subset_empty1[OF Int_Un_emptyI2[OF
          trans[OF arg_cong2[OF refl Un_assoc[symmetric], of "(\<inter>)"]]
          ] imsupp_image_subset])
     apply assumption+
  apply (erule id_onD[OF imsupp_id_on, rotated], assumption)
  done

lemmas infinite_UNIV = cinfinite_imp_infinite[OF T1_pre.UNIV_cinfinite]

lemma U1ctor_cong:
  fixes f1 g1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2 g2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
    "bij g1" "|supp g1| <o |UNIV::'var set|" "bij g2" "|supp g2| <o |UNIV::'tyvar set|"
  shows
    "(\<And>t pu p. (t, pu) \<in> set7_T1_pre y \<union> set8_T1_pre y \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FFVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y \<union> set10_T1_pre y \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FFVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T1_pre y \<union> set8_T1_pre y \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FFVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y \<union> set10_T1_pre y \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T1_pre y' \<union> set8_T1_pre y' \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FFVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y' \<union> set10_T1_pre y' \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FFVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T1_pre y' \<union> set8_T1_pre y' \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FFVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y' \<union> set10_T1_pre y' \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  imsupp f1 \<inter> (FFVars_T11 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  imsupp f2 \<inter> (FFVars_T12 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  imsupp g1 \<inter> (FFVars_T11 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y')) \<union> PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  imsupp g2 \<inter> (FFVars_T12 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y')) \<union> PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  f1 ` set5_T1_pre y \<inter> set5_T1_pre y = {} \<Longrightarrow> f2 ` set6_T1_pre y \<inter> set6_T1_pre y = {} \<Longrightarrow>
  g1 ` set5_T1_pre y' \<inter> set5_T1_pre y' = {} \<Longrightarrow> g2 ` set6_T1_pre y' \<inter> set6_T1_pre y' = {} \<Longrightarrow>
  mr_rel_T1_pre (inv g1 \<circ> f1) (inv g2 \<circ> f2) id (=) (inv g1 \<circ> f1) (inv g2 \<circ> f2)
    (\<lambda>(t, pu) (t', pu'). rrename_T1 f1 f2 t = rrename_T1 g1 g2 t' \<and>
      PU1map f1 f2 t pu = PU1map g1 g2 t' pu')
  (\<lambda>(t, pu) (t', pu'). rrename_T1 f1 f2 t = rrename_T1 g1 g2 t' \<and>
      PU1map f1 f2 t pu = PU1map g1 g2 t' pu')
  (\<lambda>(t, pu) (t', pu'). rrename_T2 f1 f2 t = rrename_T2 g1 g2 t' \<and>
      PU2map f1 f2 t pu = PU2map g1 g2 t' pu')
  (\<lambda>(t, pu) (t', pu'). rrename_T2 f1 f2 t = rrename_T2 g1 g2 t' \<and>
      PU2map f1 f2 t pu = PU2map g1 g2 t' pu')
  y y' \<Longrightarrow> U1ctor y p = U1ctor y' p"
  apply (rule trans)
   apply (rule U1ctor_rename[OF assms(1-4)] U2ctor_rename[OF assms(1-4)])
          apply assumption+
  apply (rule sym)
  apply (rule trans)
   apply (rule U1ctor_rename[OF assms(5-8)] U2ctor_rename[OF assms(5-8)])
          apply assumption+
  apply (rule sym)
  apply (rule arg_cong2[OF _ refl, of _ _ U1ctor] arg_cong2[OF _ refl, of _ _ U2ctor])
  apply (rule iffD2[OF fun_cong[OF fun_cong[OF T1_pre.mr_rel_eq[symmetric]]]]
      iffD2[OF fun_cong[OF fun_cong[OF T2_pre.mr_rel_eq[symmetric]]]]
      )
  apply (rule iffD2[OF T1_pre.mr_rel_map(1)] iffD2[OF T2_pre.mr_rel_map(1)])
                apply (rule supp_id_bound bij_id assms)+
  apply (unfold id_o o_id OO_eq Grp_UNIV_id)
  apply (rule iffD2[OF T1_pre.mr_rel_map(3)] iffD2[OF T2_pre.mr_rel_map(3)])
                   apply (rule supp_id_bound bij_id assms)+
  apply (unfold inv_id id_o Grp_UNIV_id OO_eq conversep_eq)
  apply (unfold relcompp_conversep_Grp)
  apply (rule T1_pre.mr_rel_mono_strong T2_pre.mr_rel_mono_strong)
              apply (rule supp_comp_bound supp_inv_bound infinite_UNIV supp_id_bound bij_id bij_comp bij_imp_bij_inv assms)+
       apply assumption
      apply (unfold case_prod_beta Grp_UNIV_def prod.inject)
    (* ALLGOALS passive_case OR ... *)
    (* passive case *)
      apply (rule ballI impI)+
      apply assumption
    (* default case *)
     apply (rule ballI impI)+
     apply (erule conjE)
     apply (rule conjI)
      apply assumption
     apply assumption
    (* copied from above *)
    apply (rule ballI impI)+
    apply (erule conjE)
    apply (rule conjI)
     apply assumption
    apply assumption
   apply (rule ballI impI)+
   apply (erule conjE)
   apply (rule conjI)
    apply assumption
   apply assumption
  apply (rule ballI impI)+
  apply (erule conjE)
  apply (rule conjI)
   apply assumption
  apply assumption
  done

lemma U2ctor_cong:
  fixes f1 g1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2 g2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
    "bij g1" "|supp g1| <o |UNIV::'var set|" "bij g2" "|supp g2| <o |UNIV::'tyvar set|"
  shows
    "(\<And>t pu p. (t, pu) \<in> set7_T2_pre y \<union> set8_T2_pre y \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FFVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y \<union> set10_T2_pre y \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FFVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T2_pre y \<union> set8_T2_pre y \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FFVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y \<union> set10_T2_pre y \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T2_pre y' \<union> set8_T2_pre y' \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FFVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y' \<union> set10_T2_pre y' \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FFVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T2_pre y' \<union> set8_T2_pre y' \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FFVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y' \<union> set10_T2_pre y' \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  imsupp f1 \<inter> (FFVars_T21 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) \<union> PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  imsupp f2 \<inter> (FFVars_T22 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) \<union> PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  imsupp g1 \<inter> (FFVars_T21 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y')) \<union> PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  imsupp g2 \<inter> (FFVars_T22 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y')) \<union> PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  f1 ` set5_T2_pre y \<inter> set5_T2_pre y = {} \<Longrightarrow> f2 ` set6_T2_pre y \<inter> set6_T2_pre y = {} \<Longrightarrow>
  g1 ` set5_T2_pre y' \<inter> set5_T2_pre y' = {} \<Longrightarrow> g2 ` set6_T2_pre y' \<inter> set6_T2_pre y' = {} \<Longrightarrow>
  mr_rel_T2_pre (inv g1 \<circ> f1) (inv g2 \<circ> f2) id (=) (inv g1 \<circ> f1) (inv g2 \<circ> f2)
    (\<lambda>(t, pu) (t', pu'). rrename_T1 f1 f2 t = rrename_T1 g1 g2 t' \<and>
      PU1map f1 f2 t pu = PU1map g1 g2 t' pu')
  (\<lambda>(t, pu) (t', pu'). rrename_T1 f1 f2 t = rrename_T1 g1 g2 t' \<and>
      PU1map f1 f2 t pu = PU1map g1 g2 t' pu')
  (\<lambda>(t, pu) (t', pu'). rrename_T2 f1 f2 t = rrename_T2 g1 g2 t' \<and>
      PU2map f1 f2 t pu = PU2map g1 g2 t' pu')
  (\<lambda>(t, pu) (t', pu'). rrename_T2 f1 f2 t = rrename_T2 g1 g2 t' \<and>
      PU2map f1 f2 t pu = PU2map g1 g2 t' pu')
  y y' \<Longrightarrow> U2ctor y p = U2ctor y' p"
    (* same tactic as above *)
  apply (rule trans)
   apply (rule U1ctor_rename[OF assms(1-4)] U2ctor_rename[OF assms(1-4)])
          apply assumption+
  apply (rule sym)
  apply (rule trans)
   apply (rule U1ctor_rename[OF assms(5-8)] U2ctor_rename[OF assms(5-8)])
          apply assumption+
  apply (rule sym)
  apply (rule arg_cong2[OF _ refl, of _ _ U1ctor] arg_cong2[OF _ refl, of _ _ U2ctor])
  apply (rule iffD2[OF fun_cong[OF fun_cong[OF T1_pre.mr_rel_eq[symmetric]]]]
      iffD2[OF fun_cong[OF fun_cong[OF T2_pre.mr_rel_eq[symmetric]]]]
      )
  apply (rule iffD2[OF T1_pre.mr_rel_map(1)] iffD2[OF T2_pre.mr_rel_map(1)])
                apply (rule supp_id_bound bij_id assms)+
  apply (unfold id_o o_id OO_eq Grp_UNIV_id)
  apply (rule iffD2[OF T1_pre.mr_rel_map(3)] iffD2[OF T2_pre.mr_rel_map(3)])
                   apply (rule supp_id_bound bij_id assms)+
  apply (unfold inv_id id_o Grp_UNIV_id OO_eq conversep_eq)
  apply (unfold relcompp_conversep_Grp)
  apply (rule T1_pre.mr_rel_mono_strong T2_pre.mr_rel_mono_strong)
              apply (rule supp_comp_bound supp_inv_bound infinite_UNIV supp_id_bound bij_id bij_comp bij_imp_bij_inv assms)+
       apply assumption
      apply (unfold case_prod_beta Grp_UNIV_def prod.inject)
    (* ALLGOALS passive_case OR ... *)
    (* passive case *)
      apply (rule ballI impI)+
      apply assumption
    (* default case *)
     apply (rule ballI impI)+
     apply (erule conjE)
     apply (rule conjI)
      apply assumption
     apply assumption
    (* copied from above *)
    apply (rule ballI impI)+
    apply (erule conjE)
    apply (rule conjI)
     apply assumption
    apply assumption
   apply (rule ballI impI)+
   apply (erule conjE)
   apply (rule conjI)
    apply assumption
   apply assumption
  apply (rule ballI impI)+
  apply (erule conjE)
  apply (rule conjI)
   apply assumption
  apply assumption
  done

lemmas T1_pre_set_map_ids = T1_pre.set_map[OF supp_id_bound supp_id_bound supp_id_bound bij_id supp_id_bound bij_id supp_id_bound, unfolded image_id]
lemmas T2_pre_set_map_ids = T2_pre.set_map[OF supp_id_bound supp_id_bound supp_id_bound bij_id supp_id_bound bij_id supp_id_bound, unfolded image_id]

lemma U1ctor'_cong:
  fixes f1 g1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2 g2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
    "bij g1" "|supp g1| <o |UNIV::'var set|" "bij g2" "|supp g2| <o |UNIV::'tyvar set|"
  shows
    "(\<And>t pu p. (t, pu) \<in> set7_T1_pre y \<union> set8_T1_pre y \<Longrightarrow> U1FVars_1' t (pu p) \<subseteq> FVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y \<union> set10_T1_pre y \<Longrightarrow> U2FVars_1' t (pu p) \<subseteq> FVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T1_pre y \<union> set8_T1_pre y \<Longrightarrow> U1FVars_2' t (pu p) \<subseteq> FVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y \<union> set10_T1_pre y \<Longrightarrow> U2FVars_2' t (pu p) \<subseteq> FVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T1_pre y' \<union> set8_T1_pre y' \<Longrightarrow> U1FVars_1' t (pu p) \<subseteq> FVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y' \<union> set10_T1_pre y' \<Longrightarrow> U2FVars_1' t (pu p) \<subseteq> FVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T1_pre y' \<union> set8_T1_pre y' \<Longrightarrow> U1FVars_2' t (pu p) \<subseteq> FVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y' \<union> set10_T1_pre y' \<Longrightarrow> U2FVars_2' t (pu p) \<subseteq> FVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  imsupp f1 \<inter> (FVars_T11 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  imsupp f2 \<inter> (FVars_T12 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  imsupp g1 \<inter> (FVars_T11 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst y')) \<union> PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  imsupp g2 \<inter> (FVars_T12 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst y')) \<union> PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  f1 ` set5_T1_pre y \<inter> set5_T1_pre y = {} \<Longrightarrow> f2 ` set6_T1_pre y \<inter> set6_T1_pre y = {} \<Longrightarrow>
  g1 ` set5_T1_pre y' \<inter> set5_T1_pre y' = {} \<Longrightarrow> g2 ` set6_T1_pre y' \<inter> set6_T1_pre y' = {} \<Longrightarrow>
  mr_rel_T1_pre (inv g1 \<circ> f1) (inv g2 \<circ> f2) id (=) (inv g1 \<circ> f1) (inv g2 \<circ> f2)
    (\<lambda>(t, pu) (t', pu'). alpha_T1 (rename_T1 f1 f2 t) (rename_T1 g1 g2 t') \<and>
      PU1map' f1 f2 t pu = PU1map' g1 g2 t' pu')
  (\<lambda>(t, pu) (t', pu'). alpha_T1 (rename_T1 f1 f2 t) (rename_T1 g1 g2 t') \<and>
      PU1map' f1 f2 t pu = PU1map' g1 g2 t' pu')
  (\<lambda>(t, pu) (t', pu'). alpha_T2 (rename_T2 f1 f2 t) (rename_T2 g1 g2 t') \<and>
      PU2map' f1 f2 t pu = PU2map' g1 g2 t' pu')
  (\<lambda>(t, pu) (t', pu'). alpha_T2 (rename_T2 f1 f2 t) (rename_T2 g1 g2 t') \<and>
      PU2map' f1 f2 t pu = PU2map' g1 g2 t' pu')
  y y' \<Longrightarrow> U1ctor' y p = U1ctor' y' p"
  apply (unfold U1ctor'_def U2ctor'_def)
  apply (rule U1ctor_cong[OF assms] U2ctor_cong[OF assms])
                  apply (unfold T1_pre_set_map_ids T2_pre_set_map_ids image_id image_Un[symmetric])
    (* REPEAT_DETERM *)
                  apply (drule exists_map_prod_id)
                  apply (erule exE conjE)+
                  apply hypsubst
                  apply (unfold U1FVars_1'_def[symmetric] U1FVars_2'_def[symmetric] U2FVars_1'_def[symmetric] U2FVars_2'_def[symmetric] FVars_def2s[symmetric])[1]
                  apply assumption
    (* copied from above *)
                 apply (drule exists_map_prod_id)
                 apply (erule exE conjE)+
                 apply hypsubst
                 apply (unfold U1FVars_1'_def[symmetric] U1FVars_2'_def[symmetric] U2FVars_1'_def[symmetric] U2FVars_2'_def[symmetric] FVars_def2s[symmetric])[1]
                 apply assumption
                apply (drule exists_map_prod_id)
                apply (erule exE conjE)+
                apply hypsubst
                apply (unfold U1FVars_1'_def[symmetric] U1FVars_2'_def[symmetric] U2FVars_1'_def[symmetric] U2FVars_2'_def[symmetric] FVars_def2s[symmetric])[1]
                apply assumption
               apply (drule exists_map_prod_id)
               apply (erule exE conjE)+
               apply hypsubst
               apply (unfold U1FVars_1'_def[symmetric] U1FVars_2'_def[symmetric] U2FVars_1'_def[symmetric] U2FVars_2'_def[symmetric] FVars_def2s[symmetric])[1]
               apply assumption
              apply (drule exists_map_prod_id)
              apply (erule exE conjE)+
              apply hypsubst
              apply (unfold U1FVars_1'_def[symmetric] U1FVars_2'_def[symmetric] U2FVars_1'_def[symmetric] U2FVars_2'_def[symmetric] FVars_def2s[symmetric])[1]
              apply assumption
             apply (drule exists_map_prod_id)
             apply (erule exE conjE)+
             apply hypsubst
             apply (unfold U1FVars_1'_def[symmetric] U1FVars_2'_def[symmetric] U2FVars_1'_def[symmetric] U2FVars_2'_def[symmetric] FVars_def2s[symmetric])[1]
             apply assumption
            apply (drule exists_map_prod_id)
            apply (erule exE conjE)+
            apply hypsubst
            apply (unfold U1FVars_1'_def[symmetric] U1FVars_2'_def[symmetric] U2FVars_1'_def[symmetric] U2FVars_2'_def[symmetric] FVars_def2s[symmetric])[1]
            apply assumption
           apply (drule exists_map_prod_id)
           apply (erule exE conjE)+
           apply hypsubst
           apply (unfold U1FVars_1'_def[symmetric] U1FVars_2'_def[symmetric] U2FVars_1'_def[symmetric] U2FVars_2'_def[symmetric] FVars_def2s[symmetric])[1]
           apply assumption
    (* end REPEAT_DETERM *)
    (* REPEAT_DETERM *)
  subgoal
    apply (erule trans[OF arg_cong2[OF refl arg_cong2[OF arg_cong2[OF _ refl, of _ _ "(\<union>)"] refl, of _ _ "(\<union>)"], of _ _ "(\<inter>)"], rotated])
    apply (unfold FFVars_T11_def FFVars_T12_def FFVars_T21_def FFVars_T22_def T1_ctor_def T2_ctor_def)[1]
    apply (rule T1.alpha_FVarss)
    apply (rule T1.alpha_transs)
     apply (rule T1.TT_Quotient_rep_abss)
    apply (rule alpha_T1_alpha_T2.intros)
          apply (rule bij_id supp_id_bound id_on_id)+
    apply (subst (2) T1_pre.map_comp T2_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
    apply (unfold fst_comp_map_prod[symmetric])
    apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric])
         apply (rule supp_id_bound bij_id)+
    apply (subst T1_pre.map_comp T2_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
    apply (unfold id_o o_id)
    apply (rule iffD2[OF T1_pre.mr_rel_map(1)] iffD2[OF T2_pre.mr_rel_map(1)])
                  apply (rule supp_id_bound bij_id)+
    apply (unfold id_o o_id Grp_UNIV_id OO_eq T1.rename_ids)
    apply (unfold mr_rel_T1_pre_def mr_rel_T2_pre_def T1_pre.map_id T2_pre.map_id)[1]
    apply (rule T1_pre.rel_refl_strong T2_pre.rel_refl_strong)
        apply (unfold Grp_OO comp_def)
        apply (rule refl T1.TT_Quotient_rep_abss)+
    done
      (* copied from above *)
  subgoal
    apply (erule trans[OF arg_cong2[OF refl arg_cong2[OF arg_cong2[OF _ refl, of _ _ "(\<union>)"] refl, of _ _ "(\<union>)"], of _ _ "(\<inter>)"], rotated])
    apply (unfold FFVars_T11_def FFVars_T12_def FFVars_T21_def FFVars_T22_def T1_ctor_def T2_ctor_def)[1]
    apply (rule T1.alpha_FVarss)
    apply (rule T1.alpha_transs)
     apply (rule T1.TT_Quotient_rep_abss)
    apply (rule alpha_T1_alpha_T2.intros)
          apply (rule bij_id supp_id_bound id_on_id)+
    apply (subst (2) T1_pre.map_comp T2_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
    apply (unfold fst_comp_map_prod[symmetric])
    apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric])
         apply (rule supp_id_bound bij_id)+
    apply (subst T1_pre.map_comp T2_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
    apply (unfold id_o o_id)
    apply (rule iffD2[OF T1_pre.mr_rel_map(1)] iffD2[OF T2_pre.mr_rel_map(1)])
                  apply (rule supp_id_bound bij_id)+
    apply (unfold id_o o_id Grp_UNIV_id OO_eq T1.rename_ids)
    apply (unfold mr_rel_T1_pre_def mr_rel_T2_pre_def T1_pre.map_id T2_pre.map_id)[1]
    apply (rule T1_pre.rel_refl_strong T2_pre.rel_refl_strong)
        apply (unfold Grp_OO comp_def)
        apply (rule refl T1.TT_Quotient_rep_abss)+
    done
  subgoal
    apply (erule trans[OF arg_cong2[OF refl arg_cong2[OF arg_cong2[OF _ refl, of _ _ "(\<union>)"] refl, of _ _ "(\<union>)"], of _ _ "(\<inter>)"], rotated])
    apply (unfold FFVars_T11_def FFVars_T12_def FFVars_T21_def FFVars_T22_def T1_ctor_def T2_ctor_def)[1]
    apply (rule T1.alpha_FVarss)
    apply (rule T1.alpha_transs)
     apply (rule T1.TT_Quotient_rep_abss)
    apply (rule alpha_T1_alpha_T2.intros)
          apply (rule bij_id supp_id_bound id_on_id)+
    apply (subst (2) T1_pre.map_comp T2_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
    apply (unfold fst_comp_map_prod[symmetric])
    apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric])
         apply (rule supp_id_bound bij_id)+
    apply (subst T1_pre.map_comp T2_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
    apply (unfold id_o o_id)
    apply (rule iffD2[OF T1_pre.mr_rel_map(1)] iffD2[OF T2_pre.mr_rel_map(1)])
                  apply (rule supp_id_bound bij_id)+
    apply (unfold id_o o_id Grp_UNIV_id OO_eq T1.rename_ids)
    apply (unfold mr_rel_T1_pre_def mr_rel_T2_pre_def T1_pre.map_id T2_pre.map_id)[1]
    apply (rule T1_pre.rel_refl_strong T2_pre.rel_refl_strong)
        apply (unfold Grp_OO comp_def)
        apply (rule refl T1.TT_Quotient_rep_abss)+
    done
  subgoal
    apply (erule trans[OF arg_cong2[OF refl arg_cong2[OF arg_cong2[OF _ refl, of _ _ "(\<union>)"] refl, of _ _ "(\<union>)"], of _ _ "(\<inter>)"], rotated])
    apply (unfold FFVars_T11_def FFVars_T12_def FFVars_T21_def FFVars_T22_def T1_ctor_def T2_ctor_def)[1]
    apply (rule T1.alpha_FVarss)
    apply (rule T1.alpha_transs)
     apply (rule T1.TT_Quotient_rep_abss)
    apply (rule alpha_T1_alpha_T2.intros)
          apply (rule bij_id supp_id_bound id_on_id)+
    apply (subst (2) T1_pre.map_comp T2_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
    apply (unfold fst_comp_map_prod[symmetric])
    apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric])
         apply (rule supp_id_bound bij_id)+
    apply (subst T1_pre.map_comp T2_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
    apply (unfold id_o o_id)
    apply (rule iffD2[OF T1_pre.mr_rel_map(1)] iffD2[OF T2_pre.mr_rel_map(1)])
                  apply (rule supp_id_bound bij_id)+
    apply (unfold id_o o_id Grp_UNIV_id OO_eq T1.rename_ids)
    apply (unfold mr_rel_T1_pre_def mr_rel_T2_pre_def T1_pre.map_id T2_pre.map_id)[1]
    apply (rule T1_pre.rel_refl_strong T2_pre.rel_refl_strong)
        apply (unfold Grp_OO comp_def)
        apply (rule refl T1.TT_Quotient_rep_abss)+
    done
      (* END REPEAT_DETERM *)
      apply assumption+
  apply (rule iffD2[OF T1_pre.mr_rel_map(1)] iffD2[OF T2_pre.mr_rel_map(1)])
                apply (rule supp_id_bound bij_id supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv infinite_UNIV assms)+
  apply (unfold Grp_UNIV_id OO_eq id_o o_id)
  apply (rule iffD2[OF T1_pre.mr_rel_map(3)] iffD2[OF T2_pre.mr_rel_map(3)])
                   apply (rule supp_id_bound bij_id supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv infinite_UNIV assms)+
  apply (unfold inv_id id_o o_id Grp_UNIV_id OO_eq conversep_eq)
  apply (unfold relcompp_conversep_Grp Grp_OO)
  apply (rule T1_pre.mr_rel_mono_strong T2_pre.mr_rel_mono_strong)
              apply (rule supp_id_bound bij_id supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv infinite_UNIV assms)+
       apply assumption
    (* REPEAT_DETERM (passive_case ORELSE default_case) *)
    (* passive case *)
      apply (rule ballI impI)+
      apply assumption
    (* default_case *)
  subgoal
    apply (rule ballI impI)+
    apply (unfold case_prod_beta fst_map_prod snd_map_prod rrename_T1_def rrename_T2_def)[1]
    apply (erule conjE)
    apply (rule conjI)
     apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
      (* REPEAT_DETERM *)
     apply (rule T1.alpha_transs)
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule assms)+
      apply (rule T1.TT_Quotient_rep_abss)
     apply (rule T1.alpha_syms)
      (* copied from above *)
     apply (rule T1.alpha_transs)
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule assms)+
      apply (rule T1.TT_Quotient_rep_abss)
     apply (rule T1.alpha_syms)
      (* END REPEAT_DETERM *)
     apply assumption
    apply (unfold PU1map_def PU2map_def PU1map'_def PU2map'_def U1map'_def U2map'_def id_def)
    apply assumption
    done
      (* copied from above *)
  subgoal
    apply (rule ballI impI)+
    apply (unfold case_prod_beta fst_map_prod snd_map_prod rrename_T1_def rrename_T2_def)[1]
    apply (erule conjE)
    apply (rule conjI)
     apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
      (* REPEAT_DETERM *)
     apply (rule T1.alpha_transs)
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule assms)+
      apply (rule T1.TT_Quotient_rep_abss)
     apply (rule T1.alpha_syms)
      (* copied from above *)
     apply (rule T1.alpha_transs)
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule assms)+
      apply (rule T1.TT_Quotient_rep_abss)
     apply (rule T1.alpha_syms)
      (* END REPEAT_DETERM *)
     apply assumption
    apply (unfold PU1map_def PU2map_def PU1map'_def PU2map'_def U1map'_def U2map'_def id_def)
    apply assumption
    done
  subgoal
    apply (rule ballI impI)+
    apply (unfold case_prod_beta fst_map_prod snd_map_prod rrename_T1_def rrename_T2_def)[1]
    apply (erule conjE)
    apply (rule conjI)
     apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
      (* REPEAT_DETERM *)
     apply (rule T1.alpha_transs)
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule assms)+
      apply (rule T1.TT_Quotient_rep_abss)
     apply (rule T1.alpha_syms)
      (* copied from above *)
     apply (rule T1.alpha_transs)
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule assms)+
      apply (rule T1.TT_Quotient_rep_abss)
     apply (rule T1.alpha_syms)
      (* END REPEAT_DETERM *)
     apply assumption
    apply (unfold PU1map_def PU2map_def PU1map'_def PU2map'_def U1map'_def U2map'_def id_def)
    apply assumption
    done
  subgoal
    apply (rule ballI impI)+
    apply (unfold case_prod_beta fst_map_prod snd_map_prod rrename_T1_def rrename_T2_def)[1]
    apply (erule conjE)
    apply (rule conjI)
     apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
      (* REPEAT_DETERM *)
     apply (rule T1.alpha_transs)
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule assms)+
      apply (rule T1.TT_Quotient_rep_abss)
     apply (rule T1.alpha_syms)
      (* copied from above *)
     apply (rule T1.alpha_transs)
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule assms)+
      apply (rule T1.TT_Quotient_rep_abss)
     apply (rule T1.alpha_syms)
      (* END REPEAT_DETERM *)
     apply assumption
    apply (unfold PU1map_def PU2map_def PU1map'_def PU2map'_def U1map'_def U2map'_def id_def)
    apply assumption
    done
  done

lemma U2ctor'_cong:
  fixes f1 g1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2 g2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
    "bij g1" "|supp g1| <o |UNIV::'var set|" "bij g2" "|supp g2| <o |UNIV::'tyvar set|"
  shows
    "(\<And>t pu p. (t, pu) \<in> set7_T2_pre y \<union> set8_T2_pre y \<Longrightarrow> U1FVars_1' t (pu p) \<subseteq> FVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y \<union> set10_T2_pre y \<Longrightarrow> U2FVars_1' t (pu p) \<subseteq> FVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T2_pre y \<union> set8_T2_pre y \<Longrightarrow> U1FVars_2' t (pu p) \<subseteq> FVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y \<union> set10_T2_pre y \<Longrightarrow> U2FVars_2' t (pu p) \<subseteq> FVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T2_pre y' \<union> set8_T2_pre y' \<Longrightarrow> U1FVars_1' t (pu p) \<subseteq> FVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y' \<union> set10_T2_pre y' \<Longrightarrow> U2FVars_1' t (pu p) \<subseteq> FVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T2_pre y' \<union> set8_T2_pre y' \<Longrightarrow> U1FVars_2' t (pu p) \<subseteq> FVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y' \<union> set10_T2_pre y' \<Longrightarrow> U2FVars_2' t (pu p) \<subseteq> FVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  imsupp f1 \<inter> (FVars_T21 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) \<union> PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  imsupp f2 \<inter> (FVars_T22 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) \<union> PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  imsupp g1 \<inter> (FVars_T21 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst y')) \<union> PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  imsupp g2 \<inter> (FVars_T22 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst y')) \<union> PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  f1 ` set5_T2_pre y \<inter> set5_T2_pre y = {} \<Longrightarrow> f2 ` set6_T2_pre y \<inter> set6_T2_pre y = {} \<Longrightarrow>
  g1 ` set5_T2_pre y' \<inter> set5_T2_pre y' = {} \<Longrightarrow> g2 ` set6_T2_pre y' \<inter> set6_T2_pre y' = {} \<Longrightarrow>
  mr_rel_T2_pre (inv g1 \<circ> f1) (inv g2 \<circ> f2) id (=) (inv g1 \<circ> f1) (inv g2 \<circ> f2)
    (\<lambda>(t, pu) (t', pu'). alpha_T1 (rename_T1 f1 f2 t) (rename_T1 g1 g2 t') \<and>
      PU1map' f1 f2 t pu = PU1map' g1 g2 t' pu')
  (\<lambda>(t, pu) (t', pu'). alpha_T1 (rename_T1 f1 f2 t) (rename_T1 g1 g2 t') \<and>
      PU1map' f1 f2 t pu = PU1map' g1 g2 t' pu')
  (\<lambda>(t, pu) (t', pu'). alpha_T2 (rename_T2 f1 f2 t) (rename_T2 g1 g2 t') \<and>
      PU2map' f1 f2 t pu = PU2map' g1 g2 t' pu')
  (\<lambda>(t, pu) (t', pu'). alpha_T2 (rename_T2 f1 f2 t) (rename_T2 g1 g2 t') \<and>
      PU2map' f1 f2 t pu = PU2map' g1 g2 t' pu')
  y y' \<Longrightarrow> U2ctor' y p = U2ctor' y' p"
  apply (unfold U1ctor'_def U2ctor'_def)
  apply (rule U1ctor_cong[OF assms] U2ctor_cong[OF assms])
                  apply (unfold T1_pre_set_map_ids T2_pre_set_map_ids image_id image_Un[symmetric])
    (* REPEAT_DETERM *)
                  apply (drule exists_map_prod_id)
                  apply (erule exE conjE)+
                  apply hypsubst
                  apply (unfold U1FVars_1'_def[symmetric] U1FVars_2'_def[symmetric] U2FVars_1'_def[symmetric] U2FVars_2'_def[symmetric] FVars_def2s[symmetric])[1]
                  apply assumption
    (* copied from above *)
                 apply (drule exists_map_prod_id)
                 apply (erule exE conjE)+
                 apply hypsubst
                 apply (unfold U1FVars_1'_def[symmetric] U1FVars_2'_def[symmetric] U2FVars_1'_def[symmetric] U2FVars_2'_def[symmetric] FVars_def2s[symmetric])[1]
                 apply assumption
                apply (drule exists_map_prod_id)
                apply (erule exE conjE)+
                apply hypsubst
                apply (unfold U1FVars_1'_def[symmetric] U1FVars_2'_def[symmetric] U2FVars_1'_def[symmetric] U2FVars_2'_def[symmetric] FVars_def2s[symmetric])[1]
                apply assumption
               apply (drule exists_map_prod_id)
               apply (erule exE conjE)+
               apply hypsubst
               apply (unfold U1FVars_1'_def[symmetric] U1FVars_2'_def[symmetric] U2FVars_1'_def[symmetric] U2FVars_2'_def[symmetric] FVars_def2s[symmetric])[1]
               apply assumption
              apply (drule exists_map_prod_id)
              apply (erule exE conjE)+
              apply hypsubst
              apply (unfold U1FVars_1'_def[symmetric] U1FVars_2'_def[symmetric] U2FVars_1'_def[symmetric] U2FVars_2'_def[symmetric] FVars_def2s[symmetric])[1]
              apply assumption
             apply (drule exists_map_prod_id)
             apply (erule exE conjE)+
             apply hypsubst
             apply (unfold U1FVars_1'_def[symmetric] U1FVars_2'_def[symmetric] U2FVars_1'_def[symmetric] U2FVars_2'_def[symmetric] FVars_def2s[symmetric])[1]
             apply assumption
            apply (drule exists_map_prod_id)
            apply (erule exE conjE)+
            apply hypsubst
            apply (unfold U1FVars_1'_def[symmetric] U1FVars_2'_def[symmetric] U2FVars_1'_def[symmetric] U2FVars_2'_def[symmetric] FVars_def2s[symmetric])[1]
            apply assumption
           apply (drule exists_map_prod_id)
           apply (erule exE conjE)+
           apply hypsubst
           apply (unfold U1FVars_1'_def[symmetric] U1FVars_2'_def[symmetric] U2FVars_1'_def[symmetric] U2FVars_2'_def[symmetric] FVars_def2s[symmetric])[1]
           apply assumption
    (* end REPEAT_DETERM *)
    (* REPEAT_DETERM *)
  subgoal
    apply (erule trans[OF arg_cong2[OF refl arg_cong2[OF arg_cong2[OF _ refl, of _ _ "(\<union>)"] refl, of _ _ "(\<union>)"], of _ _ "(\<inter>)"], rotated])
    apply (unfold FFVars_T11_def FFVars_T12_def FFVars_T21_def FFVars_T22_def T1_ctor_def T2_ctor_def)[1]
    apply (rule T1.alpha_FVarss)
    apply (rule T1.alpha_transs)
     apply (rule T1.TT_Quotient_rep_abss)
    apply (rule alpha_T1_alpha_T2.intros)
          apply (rule bij_id supp_id_bound id_on_id)+
    apply (subst (2) T1_pre.map_comp T2_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
    apply (unfold fst_comp_map_prod[symmetric])
    apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric])
         apply (rule supp_id_bound bij_id)+
    apply (subst T1_pre.map_comp T2_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
    apply (unfold id_o o_id)
    apply (rule iffD2[OF T1_pre.mr_rel_map(1)] iffD2[OF T2_pre.mr_rel_map(1)])
                  apply (rule supp_id_bound bij_id)+
    apply (unfold id_o o_id Grp_UNIV_id OO_eq T1.rename_ids)
    apply (unfold mr_rel_T1_pre_def mr_rel_T2_pre_def T1_pre.map_id T2_pre.map_id)[1]
    apply (rule T1_pre.rel_refl_strong T2_pre.rel_refl_strong)
        apply (unfold Grp_OO comp_def)
        apply (rule refl T1.TT_Quotient_rep_abss)+
    done
      (* copied from above *)
  subgoal
    apply (erule trans[OF arg_cong2[OF refl arg_cong2[OF arg_cong2[OF _ refl, of _ _ "(\<union>)"] refl, of _ _ "(\<union>)"], of _ _ "(\<inter>)"], rotated])
    apply (unfold FFVars_T11_def FFVars_T12_def FFVars_T21_def FFVars_T22_def T1_ctor_def T2_ctor_def)[1]
    apply (rule T1.alpha_FVarss)
    apply (rule T1.alpha_transs)
     apply (rule T1.TT_Quotient_rep_abss)
    apply (rule alpha_T1_alpha_T2.intros)
          apply (rule bij_id supp_id_bound id_on_id)+
    apply (subst (2) T1_pre.map_comp T2_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
    apply (unfold fst_comp_map_prod[symmetric])
    apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric])
         apply (rule supp_id_bound bij_id)+
    apply (subst T1_pre.map_comp T2_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
    apply (unfold id_o o_id)
    apply (rule iffD2[OF T1_pre.mr_rel_map(1)] iffD2[OF T2_pre.mr_rel_map(1)])
                  apply (rule supp_id_bound bij_id)+
    apply (unfold id_o o_id Grp_UNIV_id OO_eq T1.rename_ids)
    apply (unfold mr_rel_T1_pre_def mr_rel_T2_pre_def T1_pre.map_id T2_pre.map_id)[1]
    apply (rule T1_pre.rel_refl_strong T2_pre.rel_refl_strong)
        apply (unfold Grp_OO comp_def)
        apply (rule refl T1.TT_Quotient_rep_abss)+
    done
  subgoal
    apply (erule trans[OF arg_cong2[OF refl arg_cong2[OF arg_cong2[OF _ refl, of _ _ "(\<union>)"] refl, of _ _ "(\<union>)"], of _ _ "(\<inter>)"], rotated])
    apply (unfold FFVars_T11_def FFVars_T12_def FFVars_T21_def FFVars_T22_def T1_ctor_def T2_ctor_def)[1]
    apply (rule T1.alpha_FVarss)
    apply (rule T1.alpha_transs)
     apply (rule T1.TT_Quotient_rep_abss)
    apply (rule alpha_T1_alpha_T2.intros)
          apply (rule bij_id supp_id_bound id_on_id)+
    apply (subst (2) T1_pre.map_comp T2_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
    apply (unfold fst_comp_map_prod[symmetric])
    apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric])
         apply (rule supp_id_bound bij_id)+
    apply (subst T1_pre.map_comp T2_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
    apply (unfold id_o o_id)
    apply (rule iffD2[OF T1_pre.mr_rel_map(1)] iffD2[OF T2_pre.mr_rel_map(1)])
                  apply (rule supp_id_bound bij_id)+
    apply (unfold id_o o_id Grp_UNIV_id OO_eq T1.rename_ids)
    apply (unfold mr_rel_T1_pre_def mr_rel_T2_pre_def T1_pre.map_id T2_pre.map_id)[1]
    apply (rule T1_pre.rel_refl_strong T2_pre.rel_refl_strong)
        apply (unfold Grp_OO comp_def)
        apply (rule refl T1.TT_Quotient_rep_abss)+
    done
  subgoal
    apply (erule trans[OF arg_cong2[OF refl arg_cong2[OF arg_cong2[OF _ refl, of _ _ "(\<union>)"] refl, of _ _ "(\<union>)"], of _ _ "(\<inter>)"], rotated])
    apply (unfold FFVars_T11_def FFVars_T12_def FFVars_T21_def FFVars_T22_def T1_ctor_def T2_ctor_def)[1]
    apply (rule T1.alpha_FVarss)
    apply (rule T1.alpha_transs)
     apply (rule T1.TT_Quotient_rep_abss)
    apply (rule alpha_T1_alpha_T2.intros)
          apply (rule bij_id supp_id_bound id_on_id)+
    apply (subst (2) T1_pre.map_comp T2_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
    apply (unfold fst_comp_map_prod[symmetric])
    apply (subst T1_pre.map_comp[symmetric] T2_pre.map_comp[symmetric])
         apply (rule supp_id_bound bij_id)+
    apply (subst T1_pre.map_comp T2_pre.map_comp)
         apply (rule supp_id_bound bij_id)+
    apply (unfold id_o o_id)
    apply (rule iffD2[OF T1_pre.mr_rel_map(1)] iffD2[OF T2_pre.mr_rel_map(1)])
                  apply (rule supp_id_bound bij_id)+
    apply (unfold id_o o_id Grp_UNIV_id OO_eq T1.rename_ids)
    apply (unfold mr_rel_T1_pre_def mr_rel_T2_pre_def T1_pre.map_id T2_pre.map_id)[1]
    apply (rule T1_pre.rel_refl_strong T2_pre.rel_refl_strong)
        apply (unfold Grp_OO comp_def)
        apply (rule refl T1.TT_Quotient_rep_abss)+
    done
      (* END REPEAT_DETERM *)
      apply assumption+
  apply (rule iffD2[OF T1_pre.mr_rel_map(1)] iffD2[OF T2_pre.mr_rel_map(1)])
                apply (rule supp_id_bound bij_id supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv infinite_UNIV assms)+
  apply (unfold Grp_UNIV_id OO_eq id_o o_id)
  apply (rule iffD2[OF T1_pre.mr_rel_map(3)] iffD2[OF T2_pre.mr_rel_map(3)])
                   apply (rule supp_id_bound bij_id supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv infinite_UNIV assms)+
  apply (unfold inv_id id_o o_id Grp_UNIV_id OO_eq conversep_eq)
  apply (unfold relcompp_conversep_Grp Grp_OO)
  apply (rule T1_pre.mr_rel_mono_strong T2_pre.mr_rel_mono_strong)
              apply (rule supp_id_bound bij_id supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv infinite_UNIV assms)+
       apply assumption
    (* REPEAT_DETERM (passive_case ORELSE default_case) *)
    (* passive case *)
      apply (rule ballI impI)+
      apply assumption
    (* default_case *)
  subgoal
    apply (rule ballI impI)+
    apply (unfold case_prod_beta fst_map_prod snd_map_prod rrename_T1_def rrename_T2_def)[1]
    apply (erule conjE)
    apply (rule conjI)
     apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
      (* REPEAT_DETERM *)
     apply (rule T1.alpha_transs)
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule assms)+
      apply (rule T1.TT_Quotient_rep_abss)
     apply (rule T1.alpha_syms)
      (* copied from above *)
     apply (rule T1.alpha_transs)
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule assms)+
      apply (rule T1.TT_Quotient_rep_abss)
     apply (rule T1.alpha_syms)
      (* END REPEAT_DETERM *)
     apply assumption
    apply (unfold PU1map_def PU2map_def PU1map'_def PU2map'_def U1map'_def U2map'_def id_def)
    apply assumption
    done
      (* copied from above *)
  subgoal
    apply (rule ballI impI)+
    apply (unfold case_prod_beta fst_map_prod snd_map_prod rrename_T1_def rrename_T2_def)[1]
    apply (erule conjE)
    apply (rule conjI)
     apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
      (* REPEAT_DETERM *)
     apply (rule T1.alpha_transs)
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule assms)+
      apply (rule T1.TT_Quotient_rep_abss)
     apply (rule T1.alpha_syms)
      (* copied from above *)
     apply (rule T1.alpha_transs)
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule assms)+
      apply (rule T1.TT_Quotient_rep_abss)
     apply (rule T1.alpha_syms)
      (* END REPEAT_DETERM *)
     apply assumption
    apply (unfold PU1map_def PU2map_def PU1map'_def PU2map'_def U1map'_def U2map'_def id_def)
    apply assumption
    done
  subgoal
    apply (rule ballI impI)+
    apply (unfold case_prod_beta fst_map_prod snd_map_prod rrename_T1_def rrename_T2_def)[1]
    apply (erule conjE)
    apply (rule conjI)
     apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
      (* REPEAT_DETERM *)
     apply (rule T1.alpha_transs)
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule assms)+
      apply (rule T1.TT_Quotient_rep_abss)
     apply (rule T1.alpha_syms)
      (* copied from above *)
     apply (rule T1.alpha_transs)
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule assms)+
      apply (rule T1.TT_Quotient_rep_abss)
     apply (rule T1.alpha_syms)
      (* END REPEAT_DETERM *)
     apply assumption
    apply (unfold PU1map_def PU2map_def PU1map'_def PU2map'_def U1map'_def U2map'_def id_def)
    apply assumption
    done
  subgoal
    apply (rule ballI impI)+
    apply (unfold case_prod_beta fst_map_prod snd_map_prod rrename_T1_def rrename_T2_def)[1]
    apply (erule conjE)
    apply (rule conjI)
     apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
      (* REPEAT_DETERM *)
     apply (rule T1.alpha_transs)
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule assms)+
      apply (rule T1.TT_Quotient_rep_abss)
     apply (rule T1.alpha_syms)
      (* copied from above *)
     apply (rule T1.alpha_transs)
      apply (rule T1.alpha_bij_eqs[THEN iffD2])
          apply (rule assms)+
      apply (rule T1.TT_Quotient_rep_abss)
     apply (rule T1.alpha_syms)
      (* END REPEAT_DETERM *)
     apply assumption
    apply (unfold PU1map_def PU2map_def PU1map'_def PU2map'_def U1map'_def U2map'_def id_def)
    apply assumption
    done
  done

lemma U1map'_alpha: "alpha_T1 t t' \<Longrightarrow> U1map' f1 f2 t = U1map' f1 f2 t'"
  apply (unfold U1map'_def U2map'_def)
  apply (rule arg_cong3[OF refl refl, of _ _ U1map] arg_cong3[OF refl refl, of _ _ U2map]) (* mk_arg_cong (nvars + 1) *)
  apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
  apply assumption
  done
lemma U2map'_alpha: "alpha_T2 t t' \<Longrightarrow> U2map' f1 f2 t = U2map' f1 f2 t'"
  (* same tactic as above *)
  apply (unfold U1map'_def U2map'_def)
  apply (rule arg_cong3[OF refl refl, of _ _ U1map] arg_cong3[OF refl refl, of _ _ U2map]) (* mk_arg_cong (nvars + 1) *)
  apply (rule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])
  apply assumption
  done

lemma PU1map'_alpha: "alpha_T1 t t' \<Longrightarrow> PU1map' f1 f2 t = PU1map' f1 f2 t'"
  apply (unfold PU1map'_def PU2map'_def)
  apply (rule ext)
  apply (rule ext)
  apply (unfold U1map'_alpha U2map'_alpha)
  apply (rule refl)
  done
lemma PU2map'_alpha: "alpha_T2 t t' \<Longrightarrow> PU2map' f1 f2 t = PU2map' f1 f2 t'"
  (* same tactic as above *)
  apply (unfold PU1map'_def PU2map'_def)
  apply (rule ext)
  apply (rule ext)
  apply (unfold U1map'_alpha U2map'_alpha)
  apply (rule refl)
  done

lemma alpha_ctor_picks1:
  "suitable11 pick1 \<Longrightarrow> suitable12 pick2 \<Longrightarrow> suitable21 pick3 \<Longrightarrow> suitable22 pick4 \<Longrightarrow>
  alpha_T1 (raw_T1_ctor x) (raw_T1_ctor (
    map_T1_pre id id id id id id fst fst fst fst (
      map_T1_pre id id id id (pick1 x p) (pick2 x p)
        (\<lambda>t. (t, f_T1 pick1 pick2 pick3 pick4 t))
        (\<lambda>t. (rename_T1 (pick1 x p) (pick2 x p) t, f_T1 pick1 pick2 pick3 pick4 (rename_T1 (pick1 x p) (pick2 x p) t)))
        (\<lambda>t. (t, f_T2 pick1 pick2 pick3 pick4 t))
        (\<lambda>t. (rename_T2 (pick1 x p) id t, f_T2 pick1 pick2 pick3 pick4 (rename_T2 (pick1 x p) id t)))
        x
      )
    ))"
  apply (subst T1_pre.map_comp T2_pre.map_comp)
           apply (rule supp_id_bound bij_id | erule suitable_bij suitable_supp_bound)+
  apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
  apply (rule alpha_T1_alpha_T2.intros[rotated -1])
        apply (rule iffD2[OF T1_pre.mr_rel_map(3), rotated -1] iffD2[OF T2_pre.mr_rel_map(3), rotated -1])
                      apply (unfold inv_id id_o o_id Grp_UNIV_id conversep_eq OO_eq)[1]
                      apply (subst inv_o_simp1, erule suitable_bij)+
                      apply (unfold relcompp_conversep_Grp)
                      apply (unfold mr_rel_T1_pre_def T1_pre.map_id mr_rel_T2_pre_def T2_pre.map_id)
                      apply (rule T1_pre.rel_refl_strong T2_pre.rel_refl_strong)
                      apply (rule refl T1.alpha_refls)+
                      apply (rule supp_id_bound bij_id | erule suitable_bij suitable_supp_bound)+
   apply (erule pick_id_ons)+
  done
lemma alpha_ctor_picks2:
  "suitable11 pick1 \<Longrightarrow> suitable12 pick2 \<Longrightarrow> suitable21 pick3 \<Longrightarrow> suitable22 pick4 \<Longrightarrow>
  alpha_T2 (raw_T2_ctor x) (raw_T2_ctor (
    map_T2_pre id id id id id id fst fst fst fst (
      map_T2_pre id id id id (pick3 x p) (pick4 x p)
        (\<lambda>t. (t, f_T1 pick1 pick2 pick3 pick4 t))
        (\<lambda>t. (rename_T1 (pick3 x p) (pick4 x p) t, f_T1 pick1 pick2 pick3 pick4 (rename_T1 (pick3 x p) (pick4 x p) t)))
        (\<lambda>t. (t, f_T2 pick1 pick2 pick3 pick4 t))
        (\<lambda>t. (rename_T2 (pick3 x p) id t, f_T2 pick1 pick2 pick3 pick4 (rename_T2 (pick3 x p) id t)))
        x
      )
    ))"
  (* same tactic as above *)
  apply (subst T1_pre.map_comp T2_pre.map_comp)
           apply (rule supp_id_bound bij_id | erule suitable_bij suitable_supp_bound)+
  apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
  apply (rule alpha_T1_alpha_T2.intros[rotated -1])
        apply (rule iffD2[OF T1_pre.mr_rel_map(3), rotated -1] iffD2[OF T2_pre.mr_rel_map(3), rotated -1])
                      apply (unfold inv_id id_o o_id Grp_UNIV_id conversep_eq OO_eq)[1]
                      apply (subst inv_o_simp1, erule suitable_bij)+
                      apply (unfold relcompp_conversep_Grp)
                      apply (unfold mr_rel_T1_pre_def T1_pre.map_id mr_rel_T2_pre_def T2_pre.map_id)
                      apply (rule T1_pre.rel_refl_strong T2_pre.rel_refl_strong)
                      apply (rule refl T1.alpha_refls)+
                      apply (rule supp_id_bound bij_id | erule suitable_bij suitable_supp_bound)+
   apply (erule pick_id_ons)+
  done
lemmas alpha_ctor_picks = alpha_ctor_picks1 alpha_ctor_picks2

lemma image_Int_empty: "bij f \<Longrightarrow> f ` A \<inter> B = {} \<longleftrightarrow> A \<inter> inv f ` B = {}"
  by force

lemma int_empties1:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
    and imsupp_prems: "imsupp f1 \<inter> avoiding_set1 = {}" "imsupp f2 \<inter> avoiding_set2 = {}"
  shows "set5_T1_pre (XXl1 pick1 pick2 pick3 pick4 f1 f2 p x) \<inter>
  (FVars_T11 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst (XXl1 pick1 pick2 pick3 pick4 f1 f2 p x)))
  \<union> PFVars_1 p \<union> avoiding_set1) = {}"
    "set6_T1_pre (XXl1 pick1 pick2 pick3 pick4 f1 f2 p x) \<inter>
  (FVars_T12 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst (XXl1 pick1 pick2 pick3 pick4 f1 f2 p x)))
  \<union> PFVars_2 p \<union> avoiding_set2) = {}"
   apply (unfold XXl1_def XXr1_def)
  subgoal
    apply (subst T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)
    apply (subst T1_pre.map_comp)
               apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+
    apply (unfold id_o o_id comp_def[of fst] fst_conv)
    apply (unfold T1.FVars_ctors)
    apply (subst T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_comp[unfolded comp_def])
    apply (subst T1.FVars_renames, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_comp[symmetric] image_UN[symmetric])
    apply (subst image_set_diff[OF bij_is_inj, symmetric], rule f_prems)+
    apply (unfold image_Un[symmetric])
    apply (unfold Int_Un_distrib Un_empty)[1]
    apply (rule conjI)+
      prefer 2
      apply (rule iffD2[OF image_Int_empty])
       apply (rule f_prems)
      apply (subst PFVars_Pmap_1[symmetric])
          prefer 5
          apply (insert suitable_prems)[1]
          apply (unfold suitable_defs)[1]
          apply (erule allE conjE)+
          apply (unfold Int_Un_distrib Un_empty)[1]
          apply (erule conjE)+
          apply assumption
         apply (rule f_prems supp_inv_bound bij_imp_bij_inv)+
     prefer 2
     apply (rule imsupp_image_empty_IntI)
      apply (rule trans[OF Int_commute])
      apply (rule imsupp_prems)
     apply (insert suitable_prems)[1]
     apply (unfold suitable_defs)[1]
     apply (erule allE conjE)+
     apply (unfold Int_Un_distrib Un_empty)[1]
     apply (erule conjE)+
     apply assumption
    apply (rule trans[OF image_Int[OF bij_is_inj, symmetric]])
     apply (rule f_prems)
    apply (unfold image_is_empty)
    apply (insert suitable_prems)
    apply (subst image_set_diff[OF bij_is_inj, symmetric], erule suitable_bij)+
    apply (unfold suitable_defs Int_Un_distrib Un_empty T1.FVars_ctors)
    apply (erule allE conjE)+
    apply (rule conjI)+
        apply assumption+ (* assumption ORELSE ... *)
      apply (rule trans[OF image_Int[OF bij_is_inj, symmetric]])
       apply assumption
      apply (rule iffD2[OF image_is_empty])
      apply (rule Diff_disjoint)
      (* end *)
     apply assumption
    apply (rule trans[OF image_Int[OF bij_is_inj, symmetric]])
     apply assumption
    apply (rule iffD2[OF image_is_empty])
    apply (rule Diff_disjoint)
    done

  subgoal
    apply (subst T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)
    apply (subst T1_pre.map_comp)
               apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+
    apply (unfold id_o o_id comp_def[of fst] fst_conv)
    apply (unfold T1.FVars_ctors)
    apply (subst T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_comp[unfolded comp_def])
    apply (subst T1.FVars_renames, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_comp[symmetric] image_UN[symmetric])
    apply (subst image_set_diff[OF bij_is_inj, symmetric], rule f_prems)+
    apply (unfold image_Un[symmetric])
    apply (unfold Int_Un_distrib Un_empty)[1]
    apply (rule conjI)+
      prefer 2
      apply (rule iffD2[OF image_Int_empty])
       apply (rule f_prems)
      apply (subst PFVars_Pmap_1[symmetric] PFVars_Pmap_2[symmetric])
          prefer 5
          apply (insert suitable_prems)[1]
          apply (unfold suitable_defs)[1]
          apply (erule allE conjE)+
          apply (unfold Int_Un_distrib Un_empty)[1]
          apply (erule conjE)+
          apply assumption
         apply (rule f_prems supp_inv_bound bij_imp_bij_inv)+
     prefer 2
     apply (rule imsupp_image_empty_IntI)
      apply (rule trans[OF Int_commute])
      apply (rule imsupp_prems)
     apply (insert suitable_prems)[1]
     apply (unfold suitable_defs)[1]
     apply (erule allE conjE)+
     apply (unfold Int_Un_distrib Un_empty)[1]
     apply (erule conjE)+
     apply assumption
    apply (rule trans[OF image_Int[OF bij_is_inj, symmetric]])
     apply (rule f_prems)
    apply (unfold image_is_empty)
    apply (insert suitable_prems)
    apply (subst image_set_diff[OF bij_is_inj, symmetric], erule suitable_bij)+
    apply (unfold suitable_defs Int_Un_distrib Un_empty T1.FVars_ctors)
    apply (erule allE conjE)+
    apply (rule conjI)+
        apply assumption+
      apply (rule trans[OF image_Int[OF bij_is_inj, symmetric]])
       apply assumption
      apply (rule iffD2[OF image_is_empty])
      apply (rule Diff_disjoint)
     apply assumption+
    done
  done

ML \<open>
val fp_res = the (MRBNF_FP_Def_Sugar.fp_result_of @{context} "Fixpoint.T1")
val quotient = #quotient_fp fp_res
val raw = #raw_fp fp_res
\<close>

lemma int_empties2:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
    and imsupp_prems: "imsupp f1 \<inter> avoiding_set1 = {}" "imsupp f2 \<inter> avoiding_set2 = {}"
  shows "set5_T1_pre (XXr1 pick1 pick2 pick3 pick4 f1 f2 p x) \<inter>
  (FVars_T11 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst (XXr1 pick1 pick2 pick3 pick4 f1 f2 p x)))
  \<union> PFVars_1 p \<union> avoiding_set1) = {}"
    "set6_T1_pre (XXr1 pick1 pick2 pick3 pick4 f1 f2 p x) \<inter>
  (FVars_T12 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst (XXr1 pick1 pick2 pick3 pick4 f1 f2 p x)))
  \<union> PFVars_2 p \<union> avoiding_set2) = {}"
   apply (unfold XXr1_def)

  subgoal
    apply (subst T1_pre.set_map)
           apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+
    apply (subst T1_pre.map_comp)
               apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+
    apply (unfold id_o o_id comp_def[of fst] fst_conv T1.FVars_ctors)
    apply (subst T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_comp[unfolded comp_def])
    apply (subst T1.FVars_renames, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_UN[symmetric] image_Un[symmetric])
    apply (subst image_set_diff[OF bij_is_inj, symmetric], (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_comp[symmetric])
    apply (subst id_on_image[OF conjunct1[OF pick_id_on_images(1)[unfolded image_Un id_on_Un]]] id_on_image[OF conjunct2[OF pick_id_on_images(1)[unfolded image_Un id_on_Un]]]
        id_on_image[OF pick_id_on_images(2)] id_on_image[OF pick_id_on_images(2)]
        , (rule f_prems suitable_prems)+)+    apply (unfold image_Un[symmetric] T1.FVars_ctors[symmetric])
    apply (subst T1_pre.set_map[symmetric])
           prefer 8
           apply (subst T1.FVars_renames[symmetric])
               prefer 5
               apply (tactic \<open>EqSubst.eqsubst_tac @{context} [0] [#rename_simp (#inner raw)] 1\<close>)
                   prefer 5
                   apply (insert suitable_prems)[1]
                   apply (unfold suitable_defs)
                   apply (erule conjE allE)+
                   apply assumption
                  apply (rule f_prems supp_id_bound bij_id)+
    done

(* same tactic as above *)
  subgoal
    apply (subst T1_pre.set_map)
           apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+
    apply (subst T1_pre.map_comp)
               apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+
    apply (unfold id_o o_id comp_def[of fst] fst_conv T1.FVars_ctors)
    apply (subst T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_comp[unfolded comp_def])
    apply (subst T1.FVars_renames, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_UN[symmetric] image_Un[symmetric])
    apply (subst image_set_diff[OF bij_is_inj, symmetric], (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_comp[symmetric])
    apply (subst id_on_image[OF conjunct1[OF pick_id_on_images(1)[unfolded image_Un id_on_Un]]] id_on_image[OF conjunct2[OF pick_id_on_images(1)[unfolded image_Un id_on_Un]]]
        id_on_image[OF pick_id_on_images(2)] id_on_image[OF pick_id_on_images(2)]
        , (rule f_prems suitable_prems)+)+
    apply (unfold image_Un[symmetric] T1.FVars_ctors[symmetric])
    apply (subst T1_pre.set_map[symmetric])
           prefer 8
           apply (subst T1.FVars_renames[symmetric])
               prefer 5
               apply (tactic \<open>EqSubst.eqsubst_tac @{context} [0] [#rename_simp (#inner raw)] 1\<close>)
                   prefer 5
                   apply (insert suitable_prems)[1]
                   apply (unfold suitable_defs)
                   apply (erule conjE allE)+
                   apply assumption
                  apply (rule f_prems supp_id_bound bij_id)+
    done
  done

lemma int_empties3:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
    and imsupp_prems: "imsupp f1 \<inter> avoiding_set1 = {}" "imsupp f2 \<inter> avoiding_set2 = {}"
  shows "set5_T2_pre (XXl2 pick1 pick2 pick3 pick4 f1 f2 p x) \<inter>
  (FVars_T21 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst (XXl2 pick1 pick2 pick3 pick4 f1 f2 p x)))
  \<union> PFVars_1 p \<union> avoiding_set1) = {}"
    "set6_T2_pre (XXl2 pick1 pick2 pick3 pick4 f1 f2 p x) \<inter>
  (FVars_T22 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst (XXl2 pick1 pick2 pick3 pick4 f1 f2 p x)))
  \<union> PFVars_2 p \<union> avoiding_set2) = {}"
   apply (unfold XXl2_def XXr2_def)
  subgoal
    apply (subst T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)
    apply (subst T2_pre.map_comp)
               apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+
    apply (unfold id_o o_id comp_def[of fst] fst_conv)
    apply (unfold T1.FVars_ctors)
    apply (subst T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_comp[unfolded comp_def])
    apply (subst T1.FVars_renames, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_comp[symmetric] image_UN[symmetric])
    apply (subst image_set_diff[OF bij_is_inj, symmetric], rule f_prems)+
    apply (unfold image_Un[symmetric])
    apply (unfold Int_Un_distrib Un_empty)[1]
    apply (rule conjI)+
      prefer 2
      apply (rule iffD2[OF image_Int_empty])
       apply (rule f_prems)
      apply (subst PFVars_Pmap_1[symmetric])
          prefer 5
          apply (insert suitable_prems)[1]
          apply (unfold suitable_defs)[1]
          apply (erule allE conjE)+
          apply (unfold Int_Un_distrib Un_empty)[1]
          apply (erule conjE)+
          apply assumption
         apply (rule f_prems supp_inv_bound bij_imp_bij_inv)+
     prefer 2
     apply (rule imsupp_image_empty_IntI)
      apply (rule trans[OF Int_commute])
      apply (rule imsupp_prems)
     apply (insert suitable_prems)[1]
     apply (unfold suitable_defs)[1]
     apply (erule allE conjE)+
     apply (unfold Int_Un_distrib Un_empty)[1]
     apply (erule conjE)+
     apply assumption
    apply (rule trans[OF image_Int[OF bij_is_inj, symmetric]])
     apply (rule f_prems)
    apply (unfold image_is_empty)
    apply (insert suitable_prems)
    apply (subst image_set_diff[OF bij_is_inj, symmetric], erule suitable_bij)+
    apply (unfold suitable_defs Int_Un_distrib Un_empty T1.FVars_ctors)
    apply (erule allE conjE)+
    apply (rule conjI)+
        apply assumption+ (* assumption ORELSE ... *)
      apply (rule trans[OF image_Int[OF bij_is_inj, symmetric]])
       apply assumption
      apply (rule iffD2[OF image_is_empty])
      apply (rule Diff_disjoint)
      (* end *)
     apply assumption
    apply (rule trans[OF image_Int[OF bij_is_inj, symmetric]])
     apply assumption
    apply (rule iffD2[OF image_is_empty])
    apply (rule Diff_disjoint)
    done

  subgoal
    apply (subst T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)
    apply (subst T2_pre.map_comp)
               apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+
    apply (unfold id_o o_id comp_def[of fst] fst_conv)
    apply (unfold T1.FVars_ctors)
    apply (subst T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_comp[unfolded comp_def])
    apply (subst T1.FVars_renames, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_comp[symmetric] image_UN[symmetric])
    apply (subst image_set_diff[OF bij_is_inj, symmetric], rule f_prems)+
    apply (unfold image_Un[symmetric])
    apply (unfold Int_Un_distrib Un_empty)[1]
    apply (rule conjI)+
      prefer 2
      apply (rule iffD2[OF image_Int_empty])
       apply (rule f_prems)
      apply (subst PFVars_Pmap_1[symmetric] PFVars_Pmap_2[symmetric])
          prefer 5
          apply (insert suitable_prems)[1]
          apply (unfold suitable_defs)[1]
          apply (erule allE conjE)+
          apply (unfold Int_Un_distrib Un_empty)[1]
          apply (erule conjE)+
          apply assumption
         apply (rule f_prems supp_inv_bound bij_imp_bij_inv)+
     prefer 2
     apply (rule imsupp_image_empty_IntI)
      apply (rule trans[OF Int_commute])
      apply (rule imsupp_prems)
     apply (insert suitable_prems)[1]
     apply (unfold suitable_defs)[1]
     apply (erule allE conjE)+
     apply (unfold Int_Un_distrib Un_empty)[1]
     apply (erule conjE)+
     apply assumption
    apply (rule trans[OF image_Int[OF bij_is_inj, symmetric]])
     apply (rule f_prems)
    apply (unfold image_is_empty)
    apply (insert suitable_prems)
    apply (subst image_set_diff[OF bij_is_inj, symmetric], erule suitable_bij)+
    apply (unfold suitable_defs Int_Un_distrib Un_empty T1.FVars_ctors)
    apply (erule allE conjE)+
    apply (rule conjI)+
        apply assumption+
      apply (rule trans[OF image_Int[OF bij_is_inj, symmetric]])
       apply assumption
      apply (rule iffD2[OF image_is_empty])
      apply (rule Diff_disjoint)
     apply assumption+
    done
  done

lemma int_empties4:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
    and imsupp_prems: "imsupp f1 \<inter> avoiding_set1 = {}" "imsupp f2 \<inter> avoiding_set2 = {}"
  shows "set5_T2_pre (XXr2 pick1 pick2 pick3 pick4 f1 f2 p x) \<inter>
  (FVars_T21 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst (XXr2 pick1 pick2 pick3 pick4 f1 f2 p x)))
  \<union> PFVars_1 p \<union> avoiding_set1) = {}"
    "set6_T2_pre (XXr2 pick1 pick2 pick3 pick4 f1 f2 p x) \<inter>
  (FVars_T22 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst (XXr2 pick1 pick2 pick3 pick4 f1 f2 p x)))
  \<union> PFVars_2 p \<union> avoiding_set2) = {}"
   apply (unfold XXr2_def)

  subgoal
    apply (subst T2_pre.set_map)
           apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+
    apply (subst T2_pre.map_comp)
               apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+
    apply (unfold id_o o_id comp_def[of fst] fst_conv T1.FVars_ctors)
    apply (subst T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_comp[unfolded comp_def])
    apply (subst T1.FVars_renames, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_UN[symmetric] image_Un[symmetric])
    apply (subst image_set_diff[OF bij_is_inj, symmetric], (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_comp[symmetric])
    apply (subst pick_id_on_images'[THEN id_on_image], (rule f_prems suitable_prems)+)+    apply (unfold image_Un[symmetric] T1.FVars_ctors[symmetric])
    apply (subst T2_pre.set_map[symmetric])
           prefer 8
           apply (subst T1.FVars_renames[symmetric])
               prefer 5
               apply (subst T1.rename_simps)
                   prefer 5
                   apply (insert suitable_prems)[1]
                   apply (unfold suitable_defs)
                   apply (erule conjE allE)+
                   apply assumption
                  apply (rule f_prems supp_id_bound bij_id)+
    done

(* same tactic as above *)
  subgoal
    apply (subst T2_pre.set_map)
           apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+
    apply (subst T2_pre.map_comp)
               apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+
    apply (unfold id_o o_id comp_def[of fst] fst_conv T1.FVars_ctors)
    apply (subst T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_comp[unfolded comp_def])
    apply (subst T1.FVars_renames, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_UN[symmetric] image_Un[symmetric])
    apply (subst image_set_diff[OF bij_is_inj, symmetric], (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
    apply (unfold image_comp[symmetric])
    apply (subst pick_id_on_images'[THEN id_on_image], (rule f_prems suitable_prems)+)+    apply (unfold image_Un[symmetric] T1.FVars_ctors[symmetric])
    apply (subst T2_pre.set_map[symmetric])
           prefer 8
           apply (subst T1.FVars_renames[symmetric])
               prefer 5
               apply (subst T1.rename_simps)
                   prefer 5
                   apply (insert suitable_prems)[1]
                   apply (unfold suitable_defs)
                   apply (erule conjE allE)+
                   apply assumption
                  apply (rule f_prems supp_id_bound bij_id)+
    done
  done

lemma U1FVars'_alpha:
  "alpha_T1 t1 t1' \<Longrightarrow> U1FVars_1' t1 = U1FVars_1' t1'"
  "alpha_T1 t1 t1' \<Longrightarrow> U1FVars_2' t1 = U1FVars_2' t1'"
   apply (unfold U1FVars_1'_def U1FVars_2'_def)
   apply (rule arg_cong[of _ _ U1FVars_1] arg_cong[of _ _ U1FVars_2],
      erule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])+
  done
lemma U2FVars'_alpha:
  "alpha_T2 t2 t2' \<Longrightarrow> U2FVars_1' t2 = U2FVars_1' t2'"
  "alpha_T2 t2 t2' \<Longrightarrow> U2FVars_2' t2 = U2FVars_2' t2'"
   apply (unfold U2FVars_1'_def U2FVars_2'_def)
   apply (rule arg_cong[of _ _ U2FVars_1] arg_cong[of _ _ U2FVars_2],
      erule T1.TT_Quotient_total_abs_eq_iffs[THEN iffD2])+
  done

lemma conj_spec1: "(\<forall>x. P x) \<and> Q \<Longrightarrow> P x \<and> Q" by blast
lemma conj_spec2: "P \<and> (\<forall>x. Q x) \<Longrightarrow> P \<and> Q x" by blast
lemmas conj_spec = conj_spec1[THEN conj_spec2]
lemma conj_impI1: "(P \<longrightarrow> Q) \<and> P' \<Longrightarrow> P \<Longrightarrow> Q \<and> P'" by simp
lemma conj_impI2: "P \<and> (P' \<longrightarrow> Q) \<Longrightarrow> P' \<Longrightarrow> P \<and> Q" by simp
lemmas conj_impI = conj_impI1[OF conj_impI2]

lemma f_UFVars':
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
  shows
    "U1FVars_1' t1 (f_T1 pick1 pick2 pick3 pick4 t1 p) \<subseteq> FVars_T11 t1 \<union> PFVars_1 p \<union> avoiding_set1"
    "U1FVars_2' t1 (f_T1 pick1 pick2 pick3 pick4 t1 p) \<subseteq> FVars_T12 t1 \<union> PFVars_2 p \<union> avoiding_set2"
    "U2FVars_1' t2 (f_T2 pick1 pick2 pick3 pick4 t2 p) \<subseteq> FVars_T21 t2 \<union> PFVars_1 p \<union> avoiding_set1"
    "U2FVars_2' t2 (f_T2 pick1 pick2 pick3 pick4 t2 p) \<subseteq> FVars_T22 t2 \<union> PFVars_2 p \<union> avoiding_set2"
proof -
  note pick_prems =
    suitable_bij(1)[OF suitable_prems(1)] suitable_supp_bound(1)[OF suitable_prems(1)]
    suitable_bij(2)[OF suitable_prems(2)] suitable_supp_bound(2)[OF suitable_prems(2)]
    suitable_bij(3)[OF suitable_prems(3)] suitable_supp_bound(3)[OF suitable_prems(3)]
    suitable_bij(4)[OF suitable_prems(4)] suitable_supp_bound(4)[OF suitable_prems(4)]
  have "(U1FVars_1' t1 (f_T1 pick1 pick2 pick3 pick4 t1 p) \<subseteq> FVars_T11 t1 \<union> PFVars_1 p \<union> avoiding_set1
      \<and> U1FVars_2' t1 (f_T1 pick1 pick2 pick3 pick4 t1 p) \<subseteq> FVars_T12 t1 \<union> PFVars_2 p \<union> avoiding_set2)
    \<and> (U2FVars_1' t2 (f_T2 pick1 pick2 pick3 pick4 t2 p) \<subseteq> FVars_T21 t2 \<union> PFVars_1 p \<union> avoiding_set1
      \<and> U2FVars_2' t2 (f_T2 pick1 pick2 pick3 pick4 t2 p) \<subseteq> FVars_T22 t2 \<union> PFVars_2 p \<union> avoiding_set2)"
    apply (rule conj_spec[OF T1.TT_subshape_induct[of
            "\<lambda>t. \<forall>p. (U1FVars_1' t (f_T1 pick1 pick2 pick3 pick4 t p) \<subseteq> FVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1
        \<and> U1FVars_2' t (f_T1 pick1 pick2 pick3 pick4 t p) \<subseteq> FVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2)"
            "\<lambda>t. \<forall>p. (U2FVars_1' t (f_T2 pick1 pick2 pick3 pick4 t p) \<subseteq> FVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1
        \<and> U2FVars_2' t (f_T2 pick1 pick2 pick3 pick4 t p) \<subseteq> FVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2)"
            ]])
     apply (rule allI)
    subgoal for t p
      apply (rule raw_T1.exhaust[of t])
      apply hypsubst_thin
      subgoal premises prems for x
        apply (rule conjI)
        subgoal
          apply (subst T1.alpha_FVarss)
           apply (rule alpha_ctor_picks[OF suitable_prems])
          apply (subst U1FVars'_alpha U2FVars'_alpha)
           apply (rule alpha_ctor_picks[OF suitable_prems])
          apply (unfold f_T1_simp[OF suitable_prems] f_T2_simp[OF suitable_prems])
          apply (rule U1FVars'_subsets U2FVars'_subsets)
            apply (subst T1_pre.set_map T2_pre.set_map)
                   apply (rule supp_id_bound bij_id pick_prems)+
            apply (insert suitable_prems(1))[1]
            apply (unfold suitable_defs Int_Un_distrib Un_empty)[1]
            apply (erule allE conjE)+
            apply ((rule conjI)?, assumption)+
            (* REPEAT_DETERM *)
           apply (subst (asm) T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id pick_prems)+)+
           apply (erule UnE)
            apply (erule imageE)
            apply (unfold prod.inject)
            apply (erule conjE)
            apply hypsubst
            apply (rule prems[THEN spec, THEN conjunct1])
            apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
            (* copied from above *)
           apply (erule imageE)
           apply (unfold prod.inject)
           apply (erule conjE)
           apply hypsubst
           apply (rule prems[THEN spec, THEN conjunct1])
           apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
              apply (rule pick_prems bij_id supp_id_bound)+
            (* end REPEAT_DETERM *)
            (* copied from above *)
          apply (subst (asm) T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id pick_prems)+)+
          apply (erule UnE)
           apply (erule imageE)
           apply (unfold prod.inject)
           apply (erule conjE)
           apply hypsubst
           apply (rule prems[THEN spec, THEN conjunct1])
           apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
            (* copied from above *)
          apply (erule imageE)
          apply (unfold prod.inject)
          apply (erule conjE)
          apply hypsubst
          apply (rule prems[THEN spec, THEN conjunct1])
          apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
             apply (rule pick_prems bij_id supp_id_bound)+
            (* end REPEAT_DETERM *)
          done
        subgoal (* copied from above, incremented suitable_prems index, and used conjunct2 with prems *)
          apply (subst T1.alpha_FVarss)
           apply (rule alpha_ctor_picks[OF suitable_prems])
          apply (subst U1FVars'_alpha U2FVars'_alpha)
           apply (rule alpha_ctor_picks[OF suitable_prems])
          apply (unfold f_T1_simp[OF suitable_prems] f_T2_simp[OF suitable_prems])
          apply (rule U1FVars'_subsets U2FVars'_subsets)
            apply (subst T1_pre.set_map T2_pre.set_map)
                   apply (rule supp_id_bound bij_id pick_prems)+
            apply (insert suitable_prems(2))[1]
            apply (unfold suitable_defs Int_Un_distrib Un_empty)[1]
            apply (erule allE conjE)+
            apply ((rule conjI)?, assumption)+
            (* REPEAT_DETERM *)
           apply (subst (asm) T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id pick_prems)+)+
           apply (erule UnE)
            apply (erule imageE)
            apply (unfold prod.inject)
            apply (erule conjE)
            apply hypsubst
            apply (rule prems[THEN spec, THEN conjunct2])
            apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
            (* copied from above *)
           apply (erule imageE)
           apply (unfold prod.inject)
           apply (erule conjE)
           apply hypsubst
           apply (rule prems[THEN spec, THEN conjunct2])
           apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
              apply (rule pick_prems bij_id supp_id_bound)+
            (* end REPEAT_DETERM *)
            (* copied from above *)
          apply (subst (asm) T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id pick_prems)+)+
          apply (erule UnE)
           apply (erule imageE)
           apply (unfold prod.inject)
           apply (erule conjE)
           apply hypsubst
           apply (rule prems[THEN spec, THEN conjunct2])
           apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
            (* copied from above *)
          apply (erule imageE)
          apply (unfold prod.inject)
          apply (erule conjE)
          apply hypsubst
          apply (rule prems[THEN spec, THEN conjunct2])
          apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
             apply (rule pick_prems bij_id supp_id_bound)+
            (* end REPEAT_DETERM *)
          done
        done
      done
        (* copied from above, using raw_T2.exhaust, incremented suitable_prems *)
    apply (rule allI)
    subgoal for t p
      apply (rule raw_T2.exhaust[of t])
      apply hypsubst_thin
      subgoal premises prems for x
        apply (rule conjI)
        subgoal
          apply (subst T1.alpha_FVarss)
           apply (rule alpha_ctor_picks[OF suitable_prems])
          apply (subst U1FVars'_alpha U2FVars'_alpha)
           apply (rule alpha_ctor_picks[OF suitable_prems])
          apply (unfold f_T1_simp[OF suitable_prems] f_T2_simp[OF suitable_prems])
          apply (rule U1FVars'_subsets U2FVars'_subsets)
            apply (subst T1_pre.set_map T2_pre.set_map)
                   apply (rule supp_id_bound bij_id pick_prems)+
            apply (insert suitable_prems(3))[1]
            apply (unfold suitable_defs Int_Un_distrib Un_empty)[1]
            apply (erule allE conjE)+
            apply ((rule conjI)?, assumption)+
            (* REPEAT_DETERM *)
           apply (subst (asm) T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id pick_prems)+)+
           apply (erule UnE)
            apply (erule imageE)
            apply (unfold prod.inject)
            apply (erule conjE)
            apply hypsubst
            apply (rule prems[THEN spec, THEN conjunct1])
            apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
            (* copied from above *)
           apply (erule imageE)
           apply (unfold prod.inject)
           apply (erule conjE)
           apply hypsubst
           apply (rule prems[THEN spec, THEN conjunct1])
           apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
              apply (rule pick_prems bij_id supp_id_bound)+
            (* end REPEAT_DETERM *)
            (* copied from above *)
          apply (subst (asm) T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id pick_prems)+)+
          apply (erule UnE)
           apply (erule imageE)
           apply (unfold prod.inject)
           apply (erule conjE)
           apply hypsubst
           apply (rule prems[THEN spec, THEN conjunct1])
           apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
            (* copied from above *)
          apply (erule imageE)
          apply (unfold prod.inject)
          apply (erule conjE)
          apply hypsubst
          apply (rule prems[THEN spec, THEN conjunct1])
          apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
             apply (rule pick_prems bij_id supp_id_bound)+
            (* end REPEAT_DETERM *)
          done
        subgoal (* copied from above, incremented suitable_prems index, and used conjunct2 with prems *)
          apply (subst T1.alpha_FVarss)
           apply (rule alpha_ctor_picks[OF suitable_prems])
          apply (subst U1FVars'_alpha U2FVars'_alpha)
           apply (rule alpha_ctor_picks[OF suitable_prems])
          apply (unfold f_T1_simp[OF suitable_prems] f_T2_simp[OF suitable_prems])
          apply (rule U1FVars'_subsets U2FVars'_subsets)
            apply (subst T1_pre.set_map T2_pre.set_map)
                   apply (rule supp_id_bound bij_id pick_prems)+
            apply (insert suitable_prems(4))[1]
            apply (unfold suitable_defs Int_Un_distrib Un_empty)[1]
            apply (erule allE conjE)+
            apply ((rule conjI)?, assumption)+
            (* REPEAT_DETERM *)
           apply (subst (asm) T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id pick_prems)+)+
           apply (erule UnE)
            apply (erule imageE)
            apply (unfold prod.inject)
            apply (erule conjE)
            apply hypsubst
            apply (rule prems[THEN spec, THEN conjunct2])
            apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
            (* copied from above *)
           apply (erule imageE)
           apply (unfold prod.inject)
           apply (erule conjE)
           apply hypsubst
           apply (rule prems[THEN spec, THEN conjunct2])
           apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
              apply (rule pick_prems bij_id supp_id_bound)+
            (* end REPEAT_DETERM *)
            (* copied from above *)
          apply (subst (asm) T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id pick_prems)+)+
          apply (erule UnE)
           apply (erule imageE)
           apply (unfold prod.inject)
           apply (erule conjE)
           apply hypsubst
           apply (rule prems[THEN spec, THEN conjunct2])
           apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
            (* copied from above *)
          apply (erule imageE)
          apply (unfold prod.inject)
          apply (erule conjE)
          apply hypsubst
          apply (rule prems[THEN spec, THEN conjunct2])
          apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
             apply (rule pick_prems bij_id supp_id_bound)+
            (* end REPEAT_DETERM *)
          done
        done
      done
    done
  then show
    "U1FVars_1' t1 (f_T1 pick1 pick2 pick3 pick4 t1 p) \<subseteq> FVars_T11 t1 \<union> PFVars_1 p \<union> avoiding_set1"
    "U1FVars_2' t1 (f_T1 pick1 pick2 pick3 pick4 t1 p) \<subseteq> FVars_T12 t1 \<union> PFVars_2 p \<union> avoiding_set2"
    "U2FVars_1' t2 (f_T2 pick1 pick2 pick3 pick4 t2 p) \<subseteq> FVars_T21 t2 \<union> PFVars_1 p \<union> avoiding_set1"
    "U2FVars_2' t2 (f_T2 pick1 pick2 pick3 pick4 t2 p) \<subseteq> FVars_T22 t2 \<union> PFVars_2 p \<union> avoiding_set2"
       apply -
       apply ((erule conjE)+, assumption)+
    done
qed

lemma XXl_U1FVars':
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
    and IH: "\<And>y p. subshape_T1_T1 y (raw_T1_ctor x) \<Longrightarrow> f_T1 pick1 pick2 pick3 pick4 (rename_T1 f1 f2 y) p = PU1map' f1 f2 y (f_T1 pick1 pick2 pick3 pick4 y) p"
  shows "(t, pu) \<in> set7_T1_pre (XXl1 pick1 pick2 pick3 pick4 f1 f2 p' x) \<union> set8_T1_pre (XXl1 pick1 pick2 pick3 pick4 f1 f2 p' x) \<Longrightarrow>
       U1FVars_1' t (pu p) \<subseteq> FVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1"
    "(t, pu) \<in> set7_T1_pre (XXl1 pick1 pick2 pick3 pick4 f1 f2 p' x) \<union> set8_T1_pre (XXl1 pick1 pick2 pick3 pick4 f1 f2 p' x) \<Longrightarrow>
       U1FVars_2' t (pu p) \<subseteq> FVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2"
   apply (unfold XXl1_def)
   apply (subst (asm) T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
   apply (erule UnE)
    (* REPEAT_DETERM *)
    apply (erule imageE)
    apply (unfold prod.inject)
    apply (erule conjE)
    apply hypsubst_thin
    apply (subst IH[symmetric])
     apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
    apply ((rule supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
    apply (subst T1.rename_comps)?
    apply ((rule f_prems supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
    apply (unfold id_o o_id)?
    apply (rule f_UFVars'[OF suitable_prems])
    (* copied from above *)
   apply (erule imageE)
   apply (unfold prod.inject)
   apply (erule conjE)
   apply hypsubst_thin
   apply (subst IH[symmetric])
    apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
       apply ((rule supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
   apply (subst T1.rename_comps)?
           apply ((rule f_prems supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
   apply (unfold id_o o_id)?
   apply (rule f_UFVars'[OF suitable_prems])
    (* END goal1 *)
    (* copied from above *)
  apply (subst (asm) T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
  apply (erule UnE)
    (* REPEAT_DETERM *)
   apply (erule imageE)
   apply (unfold prod.inject)
   apply (erule conjE)
   apply hypsubst_thin
   apply (subst IH[symmetric])
    apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
   apply ((rule supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
   apply (subst T1.rename_comps)?
   apply ((rule f_prems supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
   apply (unfold id_o o_id)?
   apply (rule f_UFVars'[OF suitable_prems])
    (* copied from above *)
  apply (erule imageE)
  apply (unfold prod.inject)
  apply (erule conjE)
  apply hypsubst_thin
  apply (subst IH[symmetric])
   apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
      apply ((rule supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
  apply (subst T1.rename_comps)?
          apply ((rule f_prems supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
  apply (unfold id_o o_id)?
  apply (rule f_UFVars'[OF suitable_prems])
  done

lemma XXl_U1FVars'_2:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
    and IH: "\<And>y p. subshape_T1_T2 y (raw_T2_ctor x) \<Longrightarrow> f_T1 pick1 pick2 pick3 pick4 (rename_T1 f1 f2 y) p = PU1map' f1 f2 y (f_T1 pick1 pick2 pick3 pick4 y) p"
  shows "(t, pu) \<in> set7_T2_pre (XXl2 pick1 pick2 pick3 pick4 f1 f2 p' x) \<union> set8_T2_pre (XXl2 pick1 pick2 pick3 pick4 f1 f2 p' x) \<Longrightarrow>
       U1FVars_1' t (pu p) \<subseteq> FVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1"
    "(t, pu) \<in> set7_T2_pre (XXl2 pick1 pick2 pick3 pick4 f1 f2 p' x) \<union> set8_T2_pre (XXl2 pick1 pick2 pick3 pick4 f1 f2 p' x) \<Longrightarrow>
       U1FVars_2' t (pu p) \<subseteq> FVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2"
   apply (unfold XXl2_def)
   apply (subst (asm) T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
   apply (erule UnE)
    (* REPEAT_DETERM *)
    apply (erule imageE)
    apply (unfold prod.inject)
    apply (erule conjE)
    apply hypsubst_thin
    apply (subst IH[symmetric])
     apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
    apply ((rule supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
    apply (subst T1.rename_comps)?
    apply ((rule f_prems supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
    apply (unfold id_o o_id)?
    apply (rule f_UFVars'[OF suitable_prems])
    (* copied from above *)
   apply (erule imageE)
   apply (unfold prod.inject)
   apply (erule conjE)
   apply hypsubst_thin
   apply (subst IH[symmetric])
    apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
       apply ((rule supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
   apply (subst T1.rename_comps)?
           apply ((rule f_prems supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
   apply (unfold id_o o_id)?
   apply (rule f_UFVars'[OF suitable_prems])
    (* END goal1 *)
    (* copied from above *)
  apply (subst (asm) T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
  apply (erule UnE)
    (* REPEAT_DETERM *)
   apply (erule imageE)
   apply (unfold prod.inject)
   apply (erule conjE)
   apply hypsubst_thin
   apply (subst IH[symmetric])
    apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
   apply ((rule supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
   apply (subst T1.rename_comps)?
   apply ((rule f_prems supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
   apply (unfold id_o o_id)?
   apply (rule f_UFVars'[OF suitable_prems])
    (* copied from above *)
  apply (erule imageE)
  apply (unfold prod.inject)
  apply (erule conjE)
  apply hypsubst_thin
  apply (subst IH[symmetric])
   apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
      apply ((rule supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
  apply (subst T1.rename_comps)?
          apply ((rule f_prems supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
  apply (unfold id_o o_id)?
  apply (rule f_UFVars'[OF suitable_prems])
  done

lemma XXl_U2FVars':
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
    and IH: "\<And>y p. subshape_T2_T1 y (raw_T1_ctor x) \<Longrightarrow> f_T2 pick1 pick2 pick3 pick4 (rename_T2 f1 f2 y) p = PU2map' f1 f2 y (f_T2 pick1 pick2 pick3 pick4 y) p"
  shows  "(t2, pu2) \<in> set9_T1_pre (XXl1 pick1 pick2 pick3 pick4 f1 f2 p' x) \<union> set10_T1_pre (XXl1 pick1 pick2 pick3 pick4 f1 f2 p' x) \<Longrightarrow>
       U2FVars_1' t2 (pu2 p) \<subseteq> FVars_T21 t2 \<union> PFVars_1 p \<union> avoiding_set1"
    "(t2, pu2) \<in> set9_T1_pre (XXl1 pick1 pick2 pick3 pick4 f1 f2 p' x) \<union> set10_T1_pre (XXl1 pick1 pick2 pick3 pick4 f1 f2 p' x) \<Longrightarrow>
       U2FVars_2' t2 (pu2 p) \<subseteq> FVars_T22 t2 \<union> PFVars_2 p \<union> avoiding_set2"
    (* same tactic as above *)
   apply (unfold XXl1_def)
   apply (subst (asm) T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
   apply (erule UnE)
    (* REPEAT_DETERM *)
    apply (erule imageE)
    apply (unfold prod.inject)
    apply (erule conjE)
    apply hypsubst_thin
    apply (subst IH[symmetric])
     apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
    apply ((rule supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
    apply (subst T1.rename_comps)?
    apply ((rule f_prems supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
    apply (unfold id_o o_id)?
    apply (rule f_UFVars'[OF suitable_prems])
    (* copied from above *)
   apply (erule imageE)
   apply (unfold prod.inject)
   apply (erule conjE)
   apply hypsubst_thin
   apply (subst IH[symmetric])
    apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
       apply ((rule supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
   apply (subst T1.rename_comps)?
           apply ((rule f_prems supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
   apply (unfold id_o o_id)?
   apply (rule f_UFVars'[OF suitable_prems])
    (* END goal1 *)
    (* copied from above *)
  apply (subst (asm) T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
  apply (erule UnE)
    (* REPEAT_DETERM *)
   apply (erule imageE)
   apply (unfold prod.inject)
   apply (erule conjE)
   apply hypsubst_thin
   apply (subst IH[symmetric])
    apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
   apply ((rule supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
   apply (subst T1.rename_comps)?
   apply ((rule f_prems supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
   apply (unfold id_o o_id)?
   apply (rule f_UFVars'[OF suitable_prems])
    (* copied from above *)
  apply (erule imageE)
  apply (unfold prod.inject)
  apply (erule conjE)
  apply hypsubst_thin
  apply (subst IH[symmetric])
   apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
      apply ((rule supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
  apply (subst T1.rename_comps)?
          apply ((rule f_prems supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
  apply (unfold id_o o_id)?
  apply (rule f_UFVars'[OF suitable_prems])
  done

lemma XXl_U2FVars'_2:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
    and IH: "\<And>y p. subshape_T2_T2 y (raw_T2_ctor x) \<Longrightarrow> f_T2 pick1 pick2 pick3 pick4 (rename_T2 f1 f2 y) p = PU2map' f1 f2 y (f_T2 pick1 pick2 pick3 pick4 y) p"
  shows  "(t2, pu2) \<in> set9_T2_pre (XXl2 pick1 pick2 pick3 pick4 f1 f2 p' x) \<union> set10_T2_pre (XXl2 pick1 pick2 pick3 pick4 f1 f2 p' x) \<Longrightarrow>
       U2FVars_1' t2 (pu2 p) \<subseteq> FVars_T21 t2 \<union> PFVars_1 p \<union> avoiding_set1"
    "(t2, pu2) \<in> set9_T2_pre (XXl2 pick1 pick2 pick3 pick4 f1 f2 p' x) \<union> set10_T2_pre (XXl2 pick1 pick2 pick3 pick4 f1 f2 p' x) \<Longrightarrow>
       U2FVars_2' t2 (pu2 p) \<subseteq> FVars_T22 t2 \<union> PFVars_2 p \<union> avoiding_set2"
    (* same tactic as above *)
   apply (unfold XXl2_def)
   apply (subst (asm) T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
   apply (erule UnE)
    (* REPEAT_DETERM *)
    apply (erule imageE)
    apply (unfold prod.inject)
    apply (erule conjE)
    apply hypsubst_thin
    apply (subst IH[symmetric])
     apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
    apply ((rule supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
    apply (subst T1.rename_comps)?
    apply ((rule f_prems supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
    apply (unfold id_o o_id)?
    apply (rule f_UFVars'[OF suitable_prems])
    (* copied from above *)
   apply (erule imageE)
   apply (unfold prod.inject)
   apply (erule conjE)
   apply hypsubst_thin
   apply (subst IH[symmetric])
    apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
       apply ((rule supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
   apply (subst T1.rename_comps)?
           apply ((rule f_prems supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
   apply (unfold id_o o_id)?
   apply (rule f_UFVars'[OF suitable_prems])
    (* END goal1 *)
    (* copied from above *)
  apply (subst (asm) T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
  apply (erule UnE)
    (* REPEAT_DETERM *)
   apply (erule imageE)
   apply (unfold prod.inject)
   apply (erule conjE)
   apply hypsubst_thin
   apply (subst IH[symmetric])
    apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
   apply ((rule supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
   apply (subst T1.rename_comps)?
   apply ((rule f_prems supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
   apply (unfold id_o o_id)?
   apply (rule f_UFVars'[OF suitable_prems])
    (* copied from above *)
  apply (erule imageE)
  apply (unfold prod.inject)
  apply (erule conjE)
  apply hypsubst_thin
  apply (subst IH[symmetric])
   apply (erule T1.set_subshape_images[rotated -1, OF imageI] T1.set_subshapes)
      apply ((rule supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
  apply (subst T1.rename_comps)?
          apply ((rule f_prems supp_id_bound bij_id | (insert suitable_prems)[1], erule suitable_bij suitable_supp_bound)+)?
  apply (unfold id_o o_id)?
  apply (rule f_UFVars'[OF suitable_prems])
  done

lemma XXr_U1FVars':
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "(t, pu) \<in> set7_T1_pre (XXr1 pick1 pick2 pick3 pick4 f1 f2 p' x) \<union> set8_T1_pre (XXr1 pick1 pick2 pick3 pick4 f1 f2 p' x) \<Longrightarrow>
       U1FVars_1' t (pu p) \<subseteq> FVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1"
    "(t, pu) \<in> set7_T1_pre (XXr1 pick1 pick2 pick3 pick4 f1 f2 p' x) \<union> set8_T1_pre (XXr1 pick1 pick2 pick3 pick4 f1 f2 p' x) \<Longrightarrow>
       U1FVars_2' t (pu p) \<subseteq> FVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2"
   apply (unfold XXr1_def)
   apply (subst (asm) T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
   apply (erule UnE)
    (* REPEAT_DETERM *)
    apply (erule imageE)
    apply (unfold prod.inject)
    apply (erule conjE)
    apply hypsubst_thin
    apply (rule f_UFVars'[OF suitable_prems])
    (* copied from above *)
   apply (erule imageE)
   apply (unfold prod.inject)
   apply (erule conjE)
   apply hypsubst_thin
   apply (rule f_UFVars'[OF suitable_prems])
    (* END goal1 *)
    (* copied from above *)
  apply (subst (asm) T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
  apply (erule UnE)
    (* REPEAT_DETERM *)
   apply (erule imageE)
   apply (unfold prod.inject)
   apply (erule conjE)
   apply hypsubst_thin
   apply (rule f_UFVars'[OF suitable_prems])
    (* copied from above *)
  apply (erule imageE)
  apply (unfold prod.inject)
  apply (erule conjE)
  apply hypsubst_thin
  apply (rule f_UFVars'[OF suitable_prems])
  done

lemma XXr_U1FVars'_2:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "(t, pu) \<in> set7_T2_pre (XXr2 pick1 pick2 pick3 pick4 f1 f2 p' x) \<union> set8_T2_pre (XXr2 pick1 pick2 pick3 pick4 f1 f2 p' x) \<Longrightarrow>
       U1FVars_1' t (pu p) \<subseteq> FVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1"
    "(t, pu) \<in> set7_T2_pre (XXr2 pick1 pick2 pick3 pick4 f1 f2 p' x) \<union> set8_T2_pre (XXr2 pick1 pick2 pick3 pick4 f1 f2 p' x) \<Longrightarrow>
       U1FVars_2' t (pu p) \<subseteq> FVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2"
   apply (unfold XXr2_def)
   apply (subst (asm) T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
   apply (erule UnE)
    (* REPEAT_DETERM *)
    apply (erule imageE)
    apply (unfold prod.inject)
    apply (erule conjE)
    apply hypsubst_thin
    apply (rule f_UFVars'[OF suitable_prems])
    (* copied from above *)
   apply (erule imageE)
   apply (unfold prod.inject)
   apply (erule conjE)
   apply hypsubst_thin
   apply (rule f_UFVars'[OF suitable_prems])
    (* END goal1 *)
    (* copied from above *)
  apply (subst (asm) T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
  apply (erule UnE)
    (* REPEAT_DETERM *)
   apply (erule imageE)
   apply (unfold prod.inject)
   apply (erule conjE)
   apply hypsubst_thin
   apply (rule f_UFVars'[OF suitable_prems])
    (* copied from above *)
  apply (erule imageE)
  apply (unfold prod.inject)
  apply (erule conjE)
  apply hypsubst_thin
  apply (rule f_UFVars'[OF suitable_prems])
  done

lemma XXr_U2FVars':
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "(t, pu) \<in> set9_T1_pre (XXr1 pick1 pick2 pick3 pick4 f1 f2 p' x) \<union> set10_T1_pre (XXr1 pick1 pick2 pick3 pick4 f1 f2 p' x) \<Longrightarrow>
       U2FVars_1' t (pu p) \<subseteq> FVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1"
    "(t, pu) \<in> set9_T1_pre (XXr1 pick1 pick2 pick3 pick4 f1 f2 p' x) \<union> set10_T1_pre (XXr1 pick1 pick2 pick3 pick4 f1 f2 p' x) \<Longrightarrow>
       U2FVars_2' t (pu p) \<subseteq> FVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2"
    (* same tactic as above *)
   apply (unfold XXr1_def)
   apply (subst (asm) T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
   apply (erule UnE)
    (* REPEAT_DETERM *)
    apply (erule imageE)
    apply (unfold prod.inject)
    apply (erule conjE)
    apply hypsubst_thin
    apply (rule f_UFVars'[OF suitable_prems])
    (* copied from above *)
   apply (erule imageE)
   apply (unfold prod.inject)
   apply (erule conjE)
   apply hypsubst_thin
   apply (rule f_UFVars'[OF suitable_prems])
    (* END goal1 *)
    (* copied from above *)
  apply (subst (asm) T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
  apply (erule UnE)
    (* REPEAT_DETERM *)
   apply (erule imageE)
   apply (unfold prod.inject)
   apply (erule conjE)
   apply hypsubst_thin
   apply (rule f_UFVars'[OF suitable_prems])
    (* copied from above *)
  apply (erule imageE)
  apply (unfold prod.inject)
  apply (erule conjE)
  apply hypsubst_thin
  apply (rule f_UFVars'[OF suitable_prems])
  done

lemma XXr_U2FVars'_2:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "(t, pu) \<in> set9_T2_pre (XXr2 pick1 pick2 pick3 pick4 f1 f2 p' x) \<union> set10_T2_pre (XXr2 pick1 pick2 pick3 pick4 f1 f2 p' x) \<Longrightarrow>
       U2FVars_1' t (pu p) \<subseteq> FVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1"
    "(t, pu) \<in> set9_T2_pre (XXr2 pick1 pick2 pick3 pick4 f1 f2 p' x) \<union> set10_T2_pre (XXr2 pick1 pick2 pick3 pick4 f1 f2 p' x) \<Longrightarrow>
       U2FVars_2' t (pu p) \<subseteq> FVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2"
    (* same tactic as above *)
   apply (unfold XXr2_def)
   apply (subst (asm) T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
   apply (erule UnE)
    (* REPEAT_DETERM *)
    apply (erule imageE)
    apply (unfold prod.inject)
    apply (erule conjE)
    apply hypsubst_thin
    apply (rule f_UFVars'[OF suitable_prems])
    (* copied from above *)
   apply (erule imageE)
   apply (unfold prod.inject)
   apply (erule conjE)
   apply hypsubst_thin
   apply (rule f_UFVars'[OF suitable_prems])
    (* END goal1 *)
    (* copied from above *)
  apply (subst (asm) T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
  apply (erule UnE)
    (* REPEAT_DETERM *)
   apply (erule imageE)
   apply (unfold prod.inject)
   apply (erule conjE)
   apply hypsubst_thin
   apply (rule f_UFVars'[OF suitable_prems])
    (* copied from above *)
  apply (erule imageE)
  apply (unfold prod.inject)
  apply (erule conjE)
  apply hypsubst_thin
  apply (rule f_UFVars'[OF suitable_prems])
  done

lemma mk_pick_prems:
  fixes pick1::"_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> 'var::{var_T1_pre,var_T2_pre}" and pick2::"_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> 'tyvar::{var_T1_pre,var_T2_pre}"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
  shows "bij (pick1 x p)" "|supp (pick1 x p)| <o |UNIV::'var set|" "bij (pick2 x p)" "|supp (pick2 x p)| <o |UNIV::'tyvar set|"
    "bij (pick3 x' p)" "|supp (pick3 x' p)| <o |UNIV::'var set|" "bij (pick4 x' p)" "|supp (pick4 x' p)| <o |UNIV::'tyvar set|"
  using assms apply -
         apply (erule suitable_bij suitable_supp_bound)+
  done

lemma imsupp_id_on_XXl1:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "imsupp w \<inter>
       (FVars_T11 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst (XXl1 pick1 pick2 pick3 pick4 f1 f2 p x))) \<union> PFVars_1 p \<union>
        avoiding_set1) = {} \<Longrightarrow>
    id_on (f1 ` set1_T1_pre x) w \<and> id_on (f1 ` \<Union>(FVars_T11 ` set7_T1_pre x)) w \<and> id_on (f1 ` (\<Union>(FVars_T11 ` set8_T1_pre x) - set5_T1_pre x)) w
    \<and> id_on (f1 ` \<Union>(FVars_T21 ` set9_T1_pre x)) w \<and> id_on (f1 ` (\<Union>(FVars_T21 ` set10_T1_pre x) - set5_T1_pre x)) w"
  apply (unfold XXl1_def XXl2_def)
  apply (subst (asm) T1_pre.map_comp)
             apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+
  apply (unfold id_o o_id comp_def[of fst] fst_conv T1.FVars_ctors)
  apply (subst (asm) T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (unfold Int_Un_distrib Un_empty image_comp[unfolded comp_def])
  apply (subst (asm) T1.FVars_renames, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (unfold image_UN[symmetric] image_Un[symmetric])
  apply (subst (asm) image_set_diff[OF bij_is_inj, symmetric], (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (erule conjE)+
  apply (unfold image_comp[symmetric]
      id_on_image[OF conjunct1[OF pick_id_ons(1)[OF suitable_prems(1), unfolded id_on_Un]]]
      id_on_image[OF conjunct2[OF pick_id_ons(1)[OF suitable_prems(1), unfolded id_on_Un]]]
      id_on_image[OF conjunct1[OF pick_id_on_images(1)[OF f_prems suitable_prems(1), unfolded image_Un id_on_Un]]]
      id_on_image[OF conjunct2[OF pick_id_on_images(1)[OF f_prems suitable_prems(1), unfolded image_Un id_on_Un]]]
      )
  apply ((rule conjI)?, erule imsupp_id_on)+
  done

lemma imsupp_id_on_XXl2:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "imsupp w \<inter>
       (FVars_T12 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst (XXl1 pick1 pick2 pick3 pick4 f1 f2 p x))) \<union> PFVars_2 p \<union>
        avoiding_set2) = {} \<Longrightarrow>
    id_on (f2 ` set2_T1_pre x) w \<and> id_on (f2 ` \<Union>(FVars_T12 ` set7_T1_pre x)) w \<and> id_on (f2 ` (\<Union>(FVars_T12 ` set8_T1_pre x) - set6_T1_pre x)) w
    \<and> id_on (f2 ` \<Union>(FVars_T22 ` set9_T1_pre x)) w \<and> id_on (f2 ` \<Union>(FVars_T22 ` set10_T1_pre x)) w"
  apply (unfold XXl1_def XXl2_def)
  apply (subst (asm) T1_pre.map_comp)
             apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+
  apply (unfold id_o o_id comp_def[of fst] fst_conv T1.FVars_ctors)
  apply (subst (asm) T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (unfold Int_Un_distrib Un_empty image_comp[unfolded comp_def])
  apply (subst (asm) T1.FVars_renames, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (unfold image_UN[symmetric] image_Un[symmetric])
  apply (subst (asm) image_set_diff[OF bij_is_inj, symmetric], (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (erule conjE)+
  apply (unfold image_comp[symmetric]
      id_on_image[OF conjunct1[OF pick_id_ons(1)[OF suitable_prems(1), unfolded id_on_Un]]]
      id_on_image[OF conjunct2[OF pick_id_ons(1)[OF suitable_prems(1), unfolded id_on_Un]]]
      id_on_image[OF conjunct1[OF pick_id_on_images(1)[OF f_prems suitable_prems(1), unfolded image_Un id_on_Un]]]
      id_on_image[OF conjunct2[OF pick_id_on_images(1)[OF f_prems suitable_prems(1), unfolded image_Un id_on_Un]]]

id_on_image[OF pick_id_ons(2)[OF suitable_prems(2)]]
id_on_image[OF pick_id_on_images(2)[OF f_prems suitable_prems(2)]]
)
  apply ((rule conjI)?, erule imsupp_id_on)+
  done

lemma imsupp_id_on_XXl3:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "imsupp w \<inter>
       (FVars_T21 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst (XXl2 pick1 pick2 pick3 pick4 f1 f2 p x))) \<union> PFVars_1 p \<union>
        avoiding_set1) = {} \<Longrightarrow>
    id_on (f1 ` set1_T2_pre x) w \<and> id_on (f1 ` \<Union>(FVars_T11 ` set7_T2_pre x)) w \<and> id_on (f1 ` (\<Union>(FVars_T11 ` set8_T2_pre x) - set5_T2_pre x)) w
    \<and> id_on (f1 ` \<Union>(FVars_T21 ` set9_T2_pre x)) w \<and> id_on (f1 ` (\<Union>(FVars_T21 ` set10_T2_pre x) - set5_T2_pre x)) w"
  apply (unfold XXl1_def XXl2_def)
  apply (subst (asm) T2_pre.map_comp)
             apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+
  apply (unfold id_o o_id comp_def[of fst] fst_conv T1.FVars_ctors)
  apply (subst (asm) T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (unfold Int_Un_distrib Un_empty image_comp[unfolded comp_def])
  apply (subst (asm) T1.FVars_renames, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (unfold image_UN[symmetric] image_Un[symmetric])
  apply (subst (asm) image_set_diff[OF bij_is_inj, symmetric], (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (erule conjE)+

  apply (unfold image_comp[symmetric] id_on_image[OF pick_id_ons'(1)[OF suitable_prems(1)]]
      id_on_image[OF pick_id_ons'(2)[OF suitable_prems(1)]]
      id_on_image[OF pick_id_ons'(3)[OF suitable_prems(2)]]
      id_on_image[OF pick_id_ons'(4)[OF suitable_prems(3)]]
      id_on_image[OF pick_id_ons'(5)[OF suitable_prems(3)]]
      id_on_image[OF pick_id_ons'(6)[OF suitable_prems(4)]]
      id_on_image[OF pick_id_on_images'(1)[OF f_prems suitable_prems(1)]]
      id_on_image[OF pick_id_on_images'(2)[OF f_prems suitable_prems(1)]]
      id_on_image[OF pick_id_on_images'(3)[OF f_prems suitable_prems(2)]]
      id_on_image[OF pick_id_on_images'(4)[OF f_prems suitable_prems(3)]]
      id_on_image[OF pick_id_on_images'(5)[OF f_prems suitable_prems(3)]]
      id_on_image[OF pick_id_on_images'(6)[OF f_prems suitable_prems(4)]])
  apply ((rule conjI)?, erule imsupp_id_on)+
  done

lemma imsupp_id_on_XXl4:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "imsupp w \<inter>
       (FVars_T22 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst (XXl2 pick1 pick2 pick3 pick4 f1 f2 p x))) \<union> PFVars_2 p \<union>
        avoiding_set2) = {} \<Longrightarrow>
    id_on (f2 ` set2_T2_pre x) w \<and> id_on (f2 ` \<Union>(FVars_T12 ` set7_T2_pre x)) w \<and> id_on (f2 ` (\<Union>(FVars_T12 ` set8_T2_pre x) - set6_T2_pre x)) w
    \<and> id_on (f2 ` \<Union>(FVars_T22 ` set9_T2_pre x)) w \<and> id_on (f2 ` \<Union>(FVars_T22 ` set10_T2_pre x)) w"
  apply (unfold XXl1_def XXl2_def)
  apply (subst (asm) T2_pre.map_comp)
             apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+
  apply (unfold id_o o_id comp_def[of fst] fst_conv T1.FVars_ctors)
  apply (subst (asm) T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (unfold Int_Un_distrib Un_empty image_comp[unfolded comp_def])
  apply (subst (asm) T1.FVars_renames, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (unfold image_UN[symmetric] image_Un[symmetric])
  apply (subst (asm) image_set_diff[OF bij_is_inj, symmetric], (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (erule conjE)+
  apply (unfold image_comp[symmetric] id_on_image[OF pick_id_ons'(1)[OF suitable_prems(1)]]
      id_on_image[OF pick_id_ons'(2)[OF suitable_prems(1)]]
      id_on_image[OF pick_id_ons'(3)[OF suitable_prems(2)]]
      id_on_image[OF pick_id_ons'(4)[OF suitable_prems(3)]]
      id_on_image[OF pick_id_ons'(5)[OF suitable_prems(3)]]
      id_on_image[OF pick_id_ons'(6)[OF suitable_prems(4)]]
      id_on_image[OF pick_id_on_images'(1)[OF f_prems suitable_prems(1)]]
      id_on_image[OF pick_id_on_images'(2)[OF f_prems suitable_prems(1)]]
      id_on_image[OF pick_id_on_images'(3)[OF f_prems suitable_prems(2)]]
      id_on_image[OF pick_id_on_images'(4)[OF f_prems suitable_prems(3)]]
      id_on_image[OF pick_id_on_images'(5)[OF f_prems suitable_prems(3)]]
      id_on_image[OF pick_id_on_images'(6)[OF f_prems suitable_prems(4)]])
  apply ((rule conjI)?, erule imsupp_id_on)+
  done

lemma imsupp_id_on_XXr1:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "imsupp w \<inter>
       (FVars_T11 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst (XXr1 pick1 pick2 pick3 pick4 f1 f2 p x))) \<union> PFVars_1 p \<union>
        avoiding_set1) = {} \<Longrightarrow>
    id_on (f1 ` set1_T1_pre x) w \<and> id_on (f1 ` \<Union>(FVars_T11 ` set7_T1_pre x)) w \<and> id_on (f1 ` (\<Union>(FVars_T11 ` set8_T1_pre x) - set5_T1_pre x)) w
    \<and> id_on (f1 ` \<Union>(FVars_T21 ` set9_T1_pre x)) w \<and> id_on (f1 ` (\<Union>(FVars_T21 ` set10_T1_pre x) - set5_T1_pre x)) w"
    (* same tactic as above *)
  apply (unfold XXr1_def XXr2_def)
  apply (subst (asm) T1_pre.map_comp)
             apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+
  apply (unfold id_o o_id comp_def[of fst] fst_conv T1.FVars_ctors)
  apply (subst (asm) T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (unfold Int_Un_distrib Un_empty image_comp[unfolded comp_def])
  apply (subst (asm) T1.FVars_renames, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (unfold image_UN[symmetric] image_Un[symmetric])
  apply (subst (asm) image_set_diff[OF bij_is_inj, symmetric], (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (erule conjE)+
  apply (unfold image_comp[symmetric]
      id_on_image[OF conjunct1[OF pick_id_ons(1)[OF suitable_prems(1), unfolded id_on_Un]]]
      id_on_image[OF conjunct2[OF pick_id_ons(1)[OF suitable_prems(1), unfolded id_on_Un]]]
      id_on_image[OF conjunct1[OF pick_id_on_images(1)[OF f_prems suitable_prems(1), unfolded image_Un id_on_Un]]]
      id_on_image[OF conjunct2[OF pick_id_on_images(1)[OF f_prems suitable_prems(1), unfolded image_Un id_on_Un]]]
      )
  apply ((rule conjI)?, erule imsupp_id_on)+
  done

lemma imsupp_id_on_XXr2:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "imsupp w \<inter>
       (FVars_T12 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst (XXr1 pick1 pick2 pick3 pick4 f1 f2 p x))) \<union> PFVars_2 p \<union>
        avoiding_set2) = {} \<Longrightarrow>
    id_on (f2 ` set2_T1_pre x) w \<and> id_on (f2 ` \<Union>(FVars_T12 ` set7_T1_pre x)) w \<and> id_on (f2 ` (\<Union>(FVars_T12 ` set8_T1_pre x) - set6_T1_pre x)) w
    \<and> id_on (f2 ` \<Union>(FVars_T22 ` set9_T1_pre x)) w \<and> id_on (f2 ` \<Union>(FVars_T22 ` set10_T1_pre x)) w"
    (* same tactic as above *)
  apply (unfold XXr1_def XXr2_def)
  apply (subst (asm) T1_pre.map_comp)
             apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+
  apply (unfold id_o o_id comp_def[of fst] fst_conv T1.FVars_ctors)
  apply (subst (asm) T1_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (unfold Int_Un_distrib Un_empty image_comp[unfolded comp_def])
  apply (subst (asm) T1.FVars_renames, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (unfold image_UN[symmetric] image_Un[symmetric])
  apply (subst (asm) image_set_diff[OF bij_is_inj, symmetric], (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (erule conjE)+
  apply (unfold image_comp[symmetric]
      id_on_image[OF conjunct1[OF pick_id_ons(1)[OF suitable_prems(1), unfolded id_on_Un]]]
      id_on_image[OF conjunct2[OF pick_id_ons(1)[OF suitable_prems(1), unfolded id_on_Un]]]
      id_on_image[OF conjunct1[OF pick_id_on_images(1)[OF f_prems suitable_prems(1), unfolded image_Un id_on_Un]]]
      id_on_image[OF conjunct2[OF pick_id_on_images(1)[OF f_prems suitable_prems(1), unfolded image_Un id_on_Un]]]

id_on_image[OF pick_id_ons(2)[OF suitable_prems(2)]]
id_on_image[OF pick_id_on_images(2)[OF f_prems suitable_prems(2)]]
)
  apply ((rule conjI)?, erule imsupp_id_on)+
  done

lemma imsupp_id_on_XXr3:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "imsupp w \<inter>
       (FVars_T21 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst (XXr2 pick1 pick2 pick3 pick4 f1 f2 p x))) \<union> PFVars_1 p \<union>
        avoiding_set1) = {} \<Longrightarrow>
    id_on (f1 ` set1_T2_pre x) w \<and> id_on (f1 ` \<Union>(FVars_T11 ` set7_T2_pre x)) w \<and> id_on (f1 ` (\<Union>(FVars_T11 ` set8_T2_pre x) - set5_T2_pre x)) w
    \<and> id_on (f1 ` \<Union>(FVars_T21 ` set9_T2_pre x)) w \<and> id_on (f1 ` (\<Union>(FVars_T21 ` set10_T2_pre x) - set5_T2_pre x)) w"
    (* same tactic as above *)
  apply (unfold XXr1_def XXr2_def)
  apply (subst (asm) T2_pre.map_comp)
             apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+
  apply (unfold id_o o_id comp_def[of fst] fst_conv T1.FVars_ctors)
  apply (subst (asm) T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (unfold Int_Un_distrib Un_empty image_comp[unfolded comp_def])
  apply (subst (asm) T1.FVars_renames, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (unfold image_UN[symmetric] image_Un[symmetric])
  apply (subst (asm) image_set_diff[OF bij_is_inj, symmetric], (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (erule conjE)+
  apply (unfold image_comp[symmetric] id_on_image[OF pick_id_ons'(1)[OF suitable_prems(1)]]
      id_on_image[OF pick_id_ons'(2)[OF suitable_prems(1)]]
      id_on_image[OF pick_id_ons'(3)[OF suitable_prems(2)]]
      id_on_image[OF pick_id_ons'(4)[OF suitable_prems(3)]]
      id_on_image[OF pick_id_ons'(5)[OF suitable_prems(3)]]
      id_on_image[OF pick_id_ons'(6)[OF suitable_prems(4)]]
      id_on_image[OF pick_id_on_images'(1)[OF f_prems suitable_prems(1)]]
      id_on_image[OF pick_id_on_images'(2)[OF f_prems suitable_prems(1)]]
      id_on_image[OF pick_id_on_images'(3)[OF f_prems suitable_prems(2)]]
      id_on_image[OF pick_id_on_images'(4)[OF f_prems suitable_prems(3)]]
      id_on_image[OF pick_id_on_images'(5)[OF f_prems suitable_prems(3)]]
      id_on_image[OF pick_id_on_images'(6)[OF f_prems suitable_prems(4)]])
  apply ((rule conjI)?, erule imsupp_id_on)+
  done

lemma imsupp_id_on_XXr4:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "imsupp w \<inter>
       (FVars_T22 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst (XXr2 pick1 pick2 pick3 pick4 f1 f2 p x))) \<union> PFVars_2 p \<union>
        avoiding_set2) = {} \<Longrightarrow>
    id_on (f2 ` set2_T2_pre x) w \<and> id_on (f2 ` \<Union>(FVars_T12 ` set7_T2_pre x)) w \<and> id_on (f2 ` (\<Union>(FVars_T12 ` set8_T2_pre x) - set6_T2_pre x)) w
    \<and> id_on (f2 ` \<Union>(FVars_T22 ` set9_T2_pre x)) w \<and> id_on (f2 ` \<Union>(FVars_T22 ` set10_T2_pre x)) w"
    (* same tactic as above *)
  apply (unfold XXr1_def XXr2_def)
  apply (subst (asm) T2_pre.map_comp)
             apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+
  apply (unfold id_o o_id comp_def[of fst] fst_conv T1.FVars_ctors)
  apply (subst (asm) T2_pre.set_map, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (unfold Int_Un_distrib Un_empty image_comp[unfolded comp_def])
  apply (subst (asm) T1.FVars_renames, (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (unfold image_UN[symmetric] image_Un[symmetric])
  apply (subst (asm) image_set_diff[OF bij_is_inj, symmetric], (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV mk_pick_prems[OF suitable_prems])+)+
  apply (erule conjE)+
  apply (unfold image_comp[symmetric] id_on_image[OF pick_id_ons'(1)[OF suitable_prems(1)]]
      id_on_image[OF pick_id_ons'(2)[OF suitable_prems(1)]]
      id_on_image[OF pick_id_ons'(3)[OF suitable_prems(2)]]
      id_on_image[OF pick_id_ons'(4)[OF suitable_prems(3)]]
      id_on_image[OF pick_id_ons'(5)[OF suitable_prems(3)]]
      id_on_image[OF pick_id_ons'(6)[OF suitable_prems(4)]]
      id_on_image[OF pick_id_on_images'(1)[OF f_prems suitable_prems(1)]]
      id_on_image[OF pick_id_on_images'(2)[OF f_prems suitable_prems(1)]]
      id_on_image[OF pick_id_on_images'(3)[OF f_prems suitable_prems(2)]]
      id_on_image[OF pick_id_on_images'(4)[OF f_prems suitable_prems(3)]]
      id_on_image[OF pick_id_on_images'(5)[OF f_prems suitable_prems(3)]]
      id_on_image[OF pick_id_on_images'(6)[OF f_prems suitable_prems(4)]])
  apply ((rule conjI)?, erule imsupp_id_on)+
  done

lemmas imsupp_id_on_XX = imsupp_id_on_XXl1 imsupp_id_on_XXl2 imsupp_id_on_XXl3 imsupp_id_on_XXl4
  imsupp_id_on_XXr1 imsupp_id_on_XXr2 imsupp_id_on_XXr3 imsupp_id_on_XXr4

(*
\<lambda>t. \<forall>pick1 pick2 pick3 pick4 pick1' pick2' pick3' pick4' f1 f2 p t'.
      suitable11 pick1 \<longrightarrow> suitable12 pick2 \<longrightarrow> suitable21 pick3 \<longrightarrow> suitable22 pick4 \<longrightarrow>
      suitable11 pick1' \<longrightarrow> suitable12 pick2' \<longrightarrow> suitable21 pick3' \<longrightarrow> suitable22 pick4' \<longrightarrow>
      bij (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var) \<longrightarrow> |supp f1| <o |UNIV::'var set| \<longrightarrow>
      bij (f2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar) \<longrightarrow> |supp f2| <o |UNIV::'tyvar set| \<longrightarrow>
      imsupp f1 \<inter> avoiding_set1 = {} \<longrightarrow> imsupp f2 \<inter> avoiding_set2 = {} \<longrightarrow>
      alpha_T1 t t' \<longrightarrow>
      f_T1 pick1 pick2 pick3 pick4 (rename_T1 f1 f2 t) p = PU1map' f1 f2 t (f_T1 pick1 pick2 pick3 pick4 t) p \<and> f_T1 pick1 pick2 pick3 pick4 t = f_T1 pick1' pick2' pick3' pick4' t'
*)

lemma eq_bij_betw_refl_prems:
  assumes "eq_bij_betw_refl r u w g A B x y f1 f2 L R"
  shows "bij u" "|supp u| <o r"
    "bij w" "|supp w| <o r"
  using assms unfolding eq_bij_betw_refl_def by auto
lemma eq_bij_betw_refl_imsupp:
  assumes "eq_bij_betw_refl r u w g A B x y f1 f2 L R"
  shows "imsupp u \<inter> g (A x) = {} \<and> imsupp w \<inter> g (B y) = {}"
  using assms unfolding eq_bij_betw_refl_def by auto
lemma eq_bij_betw_prems:
  assumes "eq_bij_betw r u w g A B x y f1 f2 h L R"
  shows "bij u" "|supp u| <o r"
    "bij w" "|supp w| <o r"
  using assms unfolding eq_bij_betw_def by auto
lemma id_on_eq: "id_on A f \<Longrightarrow> id_on B g \<Longrightarrow> A = B \<Longrightarrow> x \<in> A \<Longrightarrow> f x = g x"
  unfolding id_on_def by simp

lemma f_swap_alpha:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes suitable_prems: "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and suitable'_prems: "suitable11 pick1'" "suitable12 pick2'" "suitable21 pick3'" "suitable22 pick4'"
    and f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
    and imsupp_prems: "imsupp f1 \<inter> avoiding_set1 = {}" "imsupp f2 \<inter> avoiding_set2 = {}"
    and alpha_prems: "alpha_T1 t1 t1'" "alpha_T2 t2 t2'"
  shows "(f_T1 pick1 pick2 pick3 pick4 (rename_T1 f1 f2 t1) p = PU1map' f1 f2 t1 (f_T1 pick1 pick2 pick3 pick4 t1) p \<and> f_T1 pick1 pick2 pick3 pick4 t1 = f_T1 pick1' pick2' pick3' pick4' t1')
 \<and> (f_T2 pick1 pick2 pick3 pick4 (rename_T2 f1 f2 t2) p = PU2map' f1 f2 t2 (f_T2 pick1 pick2 pick3 pick4 t2) p \<and> f_T2 pick1 pick2 pick3 pick4 t2 = f_T2 pick1' pick2' pick3' pick4' t2')
"
  apply (rule conj_impI[OF conj_impI[OF conj_impI[OF conj_impI[OF conj_impI[OF conj_impI[OF conj_impI[OF conj_impI[OF conj_impI[OF conj_impI[OF conj_impI[OF conj_impI[OF conj_impI[OF conj_impI[OF conj_impI[OF conj_spec[OF conj_spec[OF conj_spec[OF conj_spec[OF conj_spec[OF conj_spec[OF conj_spec[OF conj_spec[OF conj_spec[OF conj_spec[OF conj_spec[OF conj_spec[OF T1.TT_subshape_induct[of "
    \<lambda>t. \<forall>p t' f1 f2 pick1 pick2 pick3 pick4 pick1' pick2' pick3' pick4'.
      suitable11 pick1 \<longrightarrow> suitable12 pick2 \<longrightarrow> suitable21 pick3 \<longrightarrow> suitable22 pick4 \<longrightarrow>
      suitable11 pick1' \<longrightarrow> suitable12 pick2' \<longrightarrow> suitable21 pick3' \<longrightarrow> suitable22 pick4' \<longrightarrow>
      bij f1 \<longrightarrow> |supp f1| <o |UNIV::'var set| \<longrightarrow> bij f2 \<longrightarrow> |supp f2| <o |UNIV::'tyvar set| \<longrightarrow> imsupp f1 \<inter> avoiding_set1 = {} \<longrightarrow> imsupp f2 \<inter> avoiding_set2 = {} \<longrightarrow> alpha_T1 t t' \<longrightarrow>
      f_T1 pick1 pick2 pick3 pick4 (rename_T1 f1 f2 t) p = PU1map' f1 f2 t (f_T1 pick1 pick2 pick3 pick4 t) p \<and> f_T1 pick1 pick2 pick3 pick4 t = f_T1 pick1' pick2' pick3' pick4' t'
    "
                                                              "\<lambda>t. \<forall>p t' f1 f2 pick1 pick2 pick3 pick4 pick1' pick2' pick3' pick4'.
      suitable11 pick1 \<longrightarrow> suitable12 pick2 \<longrightarrow> suitable21 pick3 \<longrightarrow> suitable22 pick4 \<longrightarrow>
      suitable11 pick1' \<longrightarrow> suitable12 pick2' \<longrightarrow> suitable21 pick3' \<longrightarrow> suitable22 pick4' \<longrightarrow>
      bij f1 \<longrightarrow> |supp f1| <o |UNIV::'var set| \<longrightarrow> bij f2 \<longrightarrow> |supp f2| <o |UNIV::'tyvar set| \<longrightarrow> imsupp f1 \<inter> avoiding_set1 = {} \<longrightarrow> imsupp f2 \<inter> avoiding_set2 = {} \<longrightarrow> alpha_T2 t t' \<longrightarrow>
      f_T2 pick1 pick2 pick3 pick4 (rename_T2 f1 f2 t) p = PU2map' f1 f2 t (f_T2 pick1 pick2 pick3 pick4 t) p \<and> f_T2 pick1 pick2 pick3 pick4 t = f_T2 pick1' pick2' pick3' pick4' t'
  "
                                                              ]]]]]]]]]]]]]]]]]]]]]]]]]]]])
                      defer defer
                      apply (rule assms)+
  subgoal
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply hypsubst_thin
    apply (unfold triv_forall_equality)
    subgoal premises prems for p f1 f2 pick1 pick2 pick3 pick4 pick1' pick2' pick3' pick4' h1 h2 x x'
    proof -
      thm prems
      note suitable_prems = prems(3-6)
      note suitable'_prems = prems(7-10)
      note f_prems = prems(11-14)
      note imsupp_prems = prems(15,16)
      note h_prems = prems(17-20)
      note h_id_ons = prems(21-22)
      note mr_rel_prem = prems(23)
      note IHs =
        mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF prems(1)]]]]]]]]]]]]]]]]]]]]]]]]]]]
        mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF prems(2)]]]]]]]]]]]]]]]]]]]]]]]]]]]
      note exists_bij_betw's = exists_bij_betw_refl_def[
          OF conjI[OF T1_pre.UNIV_cinfinite card_of_Card_order],
          of _ _ set5_T1_pre "XXl1 pick1 pick2 pick3 pick4 f1 f2 p" x
          _ _ "XXr1 pick1 pick2 pick3 pick4 f1 f2 p"
          ] exists_bij_betw_refl_def[
          OF conjI[OF T1_pre.UNIV_cinfinite card_of_Card_order],
          of _ _ set6_T1_pre "XXl1 pick1 pick2 pick3 pick4 f1 f2 p" x
          _ _ "XXr1 pick1 pick2 pick3 pick4 f1 f2 p"
          ]
      note exists_bij_betws = exE[OF exists_bij_betw's(1)[
            of _ _ "\<lambda>x. FVars_T11 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst x)) \<union> PFVars_1 p \<union> avoiding_set1",
            rotated 3
            ]] exE[OF exists_bij_betw's(2)[
            of _ _ "\<lambda>x. FVars_T12 (raw_T1_ctor (map_T1_pre id id id id id id fst fst fst fst x)) \<union> PFVars_2 p \<union> avoiding_set2",
            rotated 3
            ]]
      note pick_prems =
        suitable_bij(1)[OF suitable_prems(1)] suitable_supp_bound(1)[OF suitable_prems(1)]
        suitable_bij(2)[OF suitable_prems(2)] suitable_supp_bound(2)[OF suitable_prems(2)]
        suitable_bij(3)[OF suitable_prems(3)] suitable_supp_bound(3)[OF suitable_prems(3)]
        suitable_bij(4)[OF suitable_prems(4)] suitable_supp_bound(4)[OF suitable_prems(4)]
      note pick'_prems =
        suitable_bij(1)[OF suitable'_prems(1)] suitable_supp_bound(1)[OF suitable'_prems(1)]
        suitable_bij(2)[OF suitable'_prems(2)] suitable_supp_bound(2)[OF suitable'_prems(2)]
        suitable_bij(3)[OF suitable'_prems(3)] suitable_supp_bound(3)[OF suitable'_prems(3)]
        suitable_bij(4)[OF suitable'_prems(4)] suitable_supp_bound(4)[OF suitable'_prems(4)]
      show ?thesis
        apply (rule conjI)
         apply (rule trans)
          (* mk_arg_cong npicks + 2 *) apply (rule arg_cong2[OF _ refl, of _ _ "f_T1 _ _ _ _"])
          apply (rule T1.rename_simps)
             apply (rule f_prems)+
         apply (rule trans)
          apply (rule f_T1_simp[OF suitable_prems])
         apply (rule trans)
          apply (subst T1_pre.map_comp)
                     apply (rule f_prems supp_id_bound bij_id | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+
          apply (unfold id_o o_id comp_def[of "\<lambda>t. (_ t, _ t)"])
          apply (subst T1.rename_comps, (rule f_prems supp_id_bound bij_id | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
          apply (unfold id_o o_id)
          apply (unfold XXr1_def[symmetric])
          apply (rule refl)
         apply (rule sym)
         apply (rule trans)
          apply (rule fun_cong[OF fun_cong[OF PU1map'_alpha]])
          apply (rule alpha_ctor_picks1[OF suitable_prems])
         apply (unfold PU1map'_def)
         apply (rule trans)
          apply (rule trans)
          (* mk_arg_cong nvars + 2 *) apply (rule arg_cong[of _ _ "U1map' _ _ _"])
           apply (rule f_T1_simp[OF suitable_prems])
          apply (rule U1map'_U1ctor')
             apply (rule f_prems)+
         apply (subst trans[OF comp_apply[symmetric] fun_cong[OF Pmap_comp0[symmetric]]])
                 apply (rule f_prems bij_imp_bij_inv supp_inv_bound)+
         apply (subst inv_o_simp2, rule f_prems)+
         apply (unfold fun_cong[OF Pmap_id0, unfolded id_def, unfolded id_def[symmetric]])
         apply (subst T1_pre.map_comp)
                    apply (rule supp_id_bound bij_id f_prems pick_prems)+
         apply (unfold id_o o_id)
         apply (unfold comp_pair prod.case)
         apply (subst T1.rename_comps, (rule supp_id_bound bij_id f_prems pick_prems)+)+
         apply (unfold id_o o_id)
         apply (unfold XXl1_def[symmetric])
          (* EVERY' (map ... exists_bij_betws) *)
         apply (rule exists_bij_betws(1))
          (* repeat twice *)
          (* bound_tac *)
                  apply (rule T1_pre.Un_bound)
                   apply (rule T1_pre.set_bd_UNIV)
                  apply (rule T1_pre.Un_bound)
                   apply (rule T1_pre.Un_bound)
                    apply (rule T1.card_of_FVars_bounds)
                   apply (rule small_PFVars_1 small_PFVars_2)
                  apply (rule small_avoiding_set1 small_avoiding_set2)
          (* end bound_tac *)
                 apply (rule int_empties1[OF suitable_prems] int_empties2[OF suitable_prems])
                      apply (rule f_prems imsupp_prems)+
                apply (unfold XXl1_def XXr1_def)[1]
                apply (subst T1_pre.set_map)
                       apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV pick_prems)+
                apply (rule refl)
          (* repeated *)
          (* bound_tac *)
               apply (rule T1_pre.Un_bound)
                apply (rule T1_pre.set_bd_UNIV)
               apply (rule T1_pre.Un_bound)
                apply (rule T1_pre.Un_bound)
                 apply (rule T1.card_of_FVars_bounds)
                apply (rule small_PFVars_1 small_PFVars_2)
               apply (rule small_avoiding_set1 small_avoiding_set2)
          (* end bound_tac *)
              apply (rule int_empties1[OF suitable_prems] int_empties2[OF suitable_prems])
                   apply (rule f_prems imsupp_prems)+
             apply (unfold XXl1_def XXr1_def)[1]
             apply (subst T1_pre.set_map)
                    apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV pick_prems)+
             apply (rule refl)
          (* end repeat *)
            apply (rule ordLeq_refl)
            apply (rule card_of_Card_order)
           apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV pick_prems)+
          (* copied from above *)
         apply (rule exists_bij_betws(2))
          (* repeat twice *)
          (* bound_tac *)
                  apply (rule T1_pre.Un_bound)
                   apply (rule T1_pre.set_bd_UNIV)
                  apply (rule T1_pre.Un_bound)
                   apply (rule T1_pre.Un_bound)
                    apply (rule T1.card_of_FVars_bounds)
                   apply (rule small_PFVars_1 small_PFVars_2)
                  apply (rule small_avoiding_set1 small_avoiding_set2)
          (* end bound_tac *)
                 apply (rule int_empties1[OF suitable_prems] int_empties2[OF suitable_prems])
                      apply (rule f_prems imsupp_prems)+
                apply (unfold XXl1_def XXr1_def)[1]
                apply (subst T1_pre.set_map)
                       apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV pick_prems)+
                apply (rule refl)
          (* repeated *)
          (* bound_tac *)
               apply (rule T1_pre.Un_bound)
                apply (rule T1_pre.set_bd_UNIV)
               apply (rule T1_pre.Un_bound)
                apply (rule T1_pre.Un_bound)
                 apply (rule T1.card_of_FVars_bounds)
                apply (rule small_PFVars_1 small_PFVars_2)
               apply (rule small_avoiding_set1 small_avoiding_set2)
          (* end bound_tac *)
              apply (rule int_empties1[OF suitable_prems] int_empties2[OF suitable_prems])
                   apply (rule f_prems imsupp_prems)+
             apply (unfold XXl1_def XXr1_def)[1]
             apply (subst T1_pre.set_map)
                    apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV pick_prems)+
             apply (rule refl)
          (* end repeat *)
            apply (rule ordLeq_refl)
            apply (rule card_of_Card_order)
           apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV pick_prems)+
          (* END EVERY' *)
         apply (erule exE)+
         apply (rule U1ctor'_cong[rotated 16])
                            apply (((unfold eq_bij_betw_refl_def)[1], (erule conjE)+, assumption)+)[8]
                         defer
                         apply (((unfold eq_bij_betw_refl_def)[1], (erule conjE)+, assumption)+)[8]
          (* REPEAT_DETERM *)
                 apply (erule XXl_U1FVars'[OF suitable_prems f_prems, rotated -1]
            XXl_U2FVars'[OF suitable_prems f_prems, rotated -1]
            )
                 apply (erule IHs[THEN conjunct1])
                            apply (rule suitable_prems suitable'_prems f_prems imsupp_prems T1.alpha_refls)+
          (* copied from above *)
                apply (erule XXl_U1FVars'[OF suitable_prems f_prems, rotated -1]
            XXl_U2FVars'[OF suitable_prems f_prems, rotated -1]
            )
                apply (erule IHs[THEN conjunct1])
                            apply (rule suitable_prems suitable'_prems f_prems imsupp_prems T1.alpha_refls)+
          (* copied from above *)
               apply (erule XXl_U1FVars'[OF suitable_prems f_prems, rotated -1]
            XXl_U2FVars'[OF suitable_prems f_prems, rotated -1]
            )
               apply (erule IHs[THEN conjunct1])
                            apply (rule suitable_prems suitable'_prems f_prems imsupp_prems T1.alpha_refls)+
          (* copied from above *)
              apply (erule XXl_U1FVars'[OF suitable_prems f_prems, rotated -1]
            XXl_U2FVars'[OF suitable_prems f_prems, rotated -1]
            )
              apply (erule IHs[THEN conjunct1])
                            apply (rule suitable_prems suitable'_prems f_prems imsupp_prems T1.alpha_refls)+
          (* END REPEAT_DETERM *)
             apply (erule XXr_U1FVars'[OF suitable_prems f_prems] XXr_U2FVars'[OF suitable_prems f_prems])+
         defer
          (* mr_rel_goal *)
         apply (subst XXl1_def XXl2_def XXr1_def XXr2_def)+
         apply (rule iffD2[OF T1_pre.mr_rel_map(1)])
                       apply (rule f_prems supp_id_bound bij_id bij_comp pick_prems
            supp_comp_bound infinite_UNIV supp_inv_bound bij_imp_bij_inv | erule eq_bij_betw_refl_prems)+
         apply (unfold id_o o_id Grp_UNIV_id OO_eq)
         apply (rule iffD2[OF T1_pre.mr_rel_map(3)])
                          apply (rule f_prems supp_id_bound bij_id bij_comp pick_prems
            supp_comp_bound infinite_UNIV supp_inv_bound bij_imp_bij_inv | erule eq_bij_betw_refl_prems)+
         apply (unfold inv_id id_o o_id Grp_UNIV_id conversep_eq OO_eq)
         apply (unfold relcompp_conversep_Grp mr_rel_T1_pre_def)
         apply (rule iffD2[OF T1_pre.rel_cong])
                apply (rule trans[OF T1_pre.map_cong0 T1_pre.map_id])
                            apply (rule supp_comp_bound f_prems supp_inv_bound infinite_UNIV supp_id_bound bij_id bij_comp pick_prems bij_imp_bij_inv | erule eq_bij_betw_refl_prems)+

(* REPEAT FIRST' *)
(* comp = id for free vars *)
                         apply (rule inv_id_middle)
                          apply (rule f_prems)
                         apply (unfold eq_bij_betw_refl_def)[1]
                         apply (erule conjE)+
                         apply (rule trans)
                          apply (rule arg_cong[of _ _ "inv _"])
                          apply (drule imsupp_id_on_XXl1[OF suitable_prems f_prems, rotated -1])
                          apply (erule conjE)+
                          apply (erule id_onD)
                          apply (rule imageI)
                          apply assumption
                         apply (drule imsupp_id_on_XXr1[OF suitable_prems f_prems, rotated -1])
                         apply (erule conjE)+
                         apply (erule id_onD[OF id_on_inv, rotated])
                          apply (rule imageI)
                          apply assumption+
          (* copied from above, incremented imsupp_id_on index *)
                        apply (rule inv_id_middle)
                         apply (rule f_prems)
                        apply (unfold eq_bij_betw_refl_def)[1]
                        apply (erule conjE)+
                        apply (rule trans)
                         apply (rule arg_cong[of _ _ "inv _"])
                         apply (drule imsupp_id_on_XXl2[OF suitable_prems f_prems, rotated -1])
                         apply (erule conjE)+
                         apply (erule id_onD)
                         apply (rule imageI)
                         apply assumption
                        apply (drule imsupp_id_on_XXr2[OF suitable_prems f_prems, rotated -1])
                        apply (erule conjE)+
                        apply (erule id_onD[OF id_on_inv, rotated])
                         apply (rule imageI)
                         apply assumption+
          (* orelse *)
                       apply (rule refl)+
          (* orelse comp = id for bound position *)
                     apply (unfold eq_bij_betw_refl_def)[1]
                     apply (erule conjE)+
                     apply (rule inv_id_middle2)
                       apply (rule bij_comp f_prems pick_prems | assumption)+
                     apply (rule sym)
                     apply (erule eq_onD)
                     apply assumption
          (* copied from above *)
                    apply (unfold eq_bij_betw_refl_def)[1]
                    apply (erule conjE)+
                    apply (rule inv_id_middle2)
                      apply (rule bij_comp f_prems pick_prems | assumption)+
                    apply (rule sym)
                    apply (erule eq_onD)
                    apply assumption
          (* orelse *)
                   apply (rule refl)+
          (* end REPEAT_DETERM *)
         apply (rule T1_pre.rel_refl_strong)
          (* REPEAT_DETER FIRST' *)
             apply (rule refl)
          (* orelse recursive nonbinding set *)
            apply (rule relcomppI)
             apply (rule iffD2[OF fun_cong[OF fun_cong[OF Grp_UNIV_def]]])
             apply (rule refl)
            apply (unfold prod.case)
            apply (rule context_conjI)
          (* alpha_bij_tac *)
             apply (rule T1.alpha_bijs)
                       apply (erule eq_bij_betw_refl_prems)+
          (* repeat twice *)
               apply (rule ballI)
               apply (unfold T1.FVars_renames[OF f_prems])[1]
               apply (erule imageE)
               apply hypsubst
               apply (unfold eq_bij_betw_refl_def)[1]
               apply (erule conjE)+
               apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
               apply (erule conjE)+
               apply (drule UN_I)
                apply assumption
               apply (rotate_tac -1)
               apply (rule trans)
                apply (drule id_onD[rotated, OF imageI])
                 apply assumption
                apply assumption
               apply (rule sym)
               apply (erule id_onD[rotated, OF imageI])
               apply assumption
          (* copied from above *)
              apply (rule ballI)
              apply (unfold T1.FVars_renames[OF f_prems])[1]
              apply (erule imageE)
              apply hypsubst
              apply (unfold eq_bij_betw_refl_def)[1]
              apply (erule conjE)+
              apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
              apply (erule conjE)+
              apply (drule UN_I)
               apply assumption
              apply (rotate_tac -1)
              apply (rule trans)
               apply (drule id_onD[rotated, OF imageI])
                apply assumption
               apply assumption
              apply (rule sym)
              apply (erule id_onD[rotated, OF imageI])
              apply assumption
          (* end repeat twice *)
             apply (rule T1.alpha_refls)
          (* end alpha_bij_tac *)
            apply (rule trans)
             apply (rule arg_cong[of _ _ "PU1map' _ _ _"])
             apply (rule ext)
             apply (rule IHs[THEN conjunct1, symmetric])
                            apply (erule T1.set_subshapes)
                           apply (rule suitable_prems suitable'_prems f_prems imsupp_prems T1.alpha_refls)+
            apply (rule trans)
             apply (rule ext)
             apply (rule IHs[THEN conjunct1, symmetric])
                            apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems)+
                   apply (erule eq_bij_betw_refl_prems)+
               apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
               apply (erule conjE)+
               apply assumption
              apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
              apply (erule conjE)+
              apply assumption
             apply (rule T1.alpha_refls)
            apply (rule sym)
            apply (rule trans)
             apply (rule ext)
             apply (rule IHs[THEN conjunct1, symmetric])
                            apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems)+
                   apply (erule eq_bij_betw_refl_prems)+
               apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
               apply (erule conjE)+
               apply assumption
              apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
              apply (erule conjE)+
              apply assumption
             apply (rule T1.alpha_refls)
            apply (rule IHs[THEN conjunct2])
                           apply (subst T1.rename_comps)
                            apply (rule f_prems)+
                            apply (erule eq_bij_betw_refl_prems)+
                           apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule bij_comp supp_comp_bound infinite_UNIV f_prems | erule eq_bij_betw_refl_prems)+
                          apply (rule suitable_prems f_prems imsupp_prems)+
            apply (rule T1.alpha_syms)
            apply assumption

(* orelse recursive binding set *)
           apply (rule relcomppI)
            apply (unfold Grp_UNIV_def)[1]
            apply (rule refl)
           apply (unfold prod.case)
           apply (subst T1.rename_comps, (rule bij_comp supp_comp_bound infinite_UNIV pick_prems f_prems | erule eq_bij_betw_refl_prems)+)+
           apply (rule context_conjI)
          (* binding alpha_bij_tac *)
            apply (rule T1.alpha_bijs)
                      apply (rule bij_comp supp_comp_bound infinite_UNIV pick_prems f_prems | erule eq_bij_betw_refl_prems)+
          (* repeat twice *)
              apply (rule ballI)
              apply (rule case_split[of "_ \<in> _"])
               apply (unfold eq_bij_betw_refl_def)[1]
               apply (erule conjE)+
               apply (erule eq_onD)
               apply assumption
              apply (unfold comp_assoc[symmetric])[1]
              apply (rule trans)
               apply (rule comp_apply)
              apply (rule trans)
               apply (rule arg_cong[of _ _ "_ \<circ> _"])
               apply (rule id_onD[OF pick_id_ons(2)[OF suitable_prems(2)]]
            id_onD[OF pick_id_ons(1)[OF suitable_prems(1)]])
               apply (rule DiffI)
                apply (rule UN_I)
                 apply assumption+
              apply (drule DiffI[rotated])
               apply (rule UN_I)
                apply assumption
               apply assumption
              apply (rotate_tac -1)
              apply (rule trans[OF comp_apply])
              apply (rule trans)
               apply (unfold eq_bij_betw_refl_def)[1]
               apply (erule conjE)+
               apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
               apply (erule conjE)+
               apply (rotate_tac -1)
               apply (erule id_onD[rotated, OF imageI, of _ _ f1] id_onD[rotated, OF imageI, of _ _ f2])
               apply assumption
              apply (rule sym)
              apply (rule comp_middle)
               apply (unfold eq_bij_betw_refl_def)[1]
               apply (erule conjE)+
               apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
               apply (erule conjE)+
               apply (erule id_onD[rotated, OF imageI])
               apply assumption
              apply (rule pick_id_on_images[OF f_prems, THEN id_onD])
               apply (rule suitable_prems)
              apply (rule imageI)
              apply assumption
          (* copied from above *)
             apply (rule ballI)
             apply (rule case_split[of "_ \<in> _"])
              apply (unfold eq_bij_betw_refl_def)[1]
              apply (erule conjE)+
              apply (erule eq_onD)
              apply assumption
             apply (unfold comp_assoc[symmetric])[1]
             apply (rule trans)
              apply (rule comp_apply)
             apply (drule DiffI[rotated])
              apply (rule UN_I)
               apply assumption
              apply assumption
             apply (rotate_tac -1)
             apply (rule trans)
              apply (rule arg_cong[of _ _ "_ \<circ> _"])
              apply (erule id_onD[OF pick_id_ons'(1)[OF suitable_prems(1)]]
            id_onD[OF pick_id_ons'(2)[OF suitable_prems(1)]]
            id_onD[OF pick_id_ons'(3)[OF suitable_prems(2)]]
            id_onD[OF pick_id_ons'(4)[OF suitable_prems(3)]]
            id_onD[OF pick_id_ons'(5)[OF suitable_prems(3)]]
            id_onD[OF pick_id_ons'(6)[OF suitable_prems(4)]])
             apply (rule trans[OF comp_apply])
             apply (rule trans)
              apply (unfold eq_bij_betw_refl_def)[1]
              apply (erule conjE)+
              apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
              apply (erule conjE)+
              apply (rotate_tac -1)
              apply (erule id_onD[rotated, OF imageI, of _ _ f1] id_onD[rotated, OF imageI, of _ _ f2])
              apply assumption
             apply (rule sym)
             apply (rule comp_middle)
              apply (unfold eq_bij_betw_refl_def)[1]
              apply (erule conjE)+
              apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
              apply (erule conjE)+
              apply (erule id_onD[rotated, OF imageI])
              apply assumption
             apply (erule id_onD[OF pick_id_on_images'(1)[OF f_prems suitable_prems(1)] imageI]
            id_onD[OF pick_id_on_images'(2)[OF f_prems suitable_prems(1)] imageI]
            id_onD[OF pick_id_on_images'(3)[OF f_prems suitable_prems(2)] imageI]
            id_onD[OF pick_id_on_images'(4)[OF f_prems suitable_prems(3)] imageI]
            id_onD[OF pick_id_on_images'(5)[OF f_prems suitable_prems(3)] imageI]
            id_onD[OF pick_id_on_images'(6)[OF f_prems suitable_prems(4)] imageI])
          (* end repeat twice *)
            apply (rule T1.alpha_refls)
          (* end binding alpha_bij_tac *)
           apply (rule trans)
            apply (rule arg_cong[of _ _ "PU1map' _ _ _"])
            apply (rule ext)
            apply (rule IHs[THEN conjunct1, symmetric])
                           apply (erule T1.set_subshapes T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems imsupp_prems pick_prems T1.alpha_refls)+
           apply (subst T1.rename_comps)
                   apply (rule pick_prems f_prems)+
           apply (rule trans)
            apply (rule ext)
            apply (rule IHs[THEN conjunct1, symmetric])
                           apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems bij_comp pick_prems supp_comp_bound infinite_UNIV)+
                  apply (erule eq_bij_betw_refl_prems)+
              apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
              apply (erule conjE)+
              apply assumption
             apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
             apply (erule conjE)+
             apply assumption
            apply (rule T1.alpha_refls)
           apply (rule sym)
           apply (rule trans)
            apply (rule ext)
            apply (rule IHs[THEN conjunct1, symmetric])
                           apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems bij_comp supp_comp_bound pick_prems infinite_UNIV)+
                  apply (erule eq_bij_betw_refl_prems)+
              apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
              apply (erule conjE)+
              apply assumption
             apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
             apply (erule conjE)+
             apply assumption
            apply (rule T1.alpha_refls)
           apply (rule IHs[THEN conjunct2])
                          apply (subst T1.rename_comps)
                            apply (rule f_prems pick_prems bij_comp supp_comp_bound infinite_UNIV)+
                            apply (erule eq_bij_betw_refl_prems)+
                          apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule bij_comp supp_comp_bound infinite_UNIV f_prems pick_prems | erule eq_bij_betw_refl_prems)+
                         apply (rule suitable_prems f_prems imsupp_prems)+
           apply (rule T1.alpha_syms)
           apply (subst T1.rename_comps, (rule bij_comp supp_comp_bound infinite_UNIV pick_prems f_prems | erule eq_bij_betw_refl_prems)+)+
           apply assumption

(* orelse nonbinding recursive set, again *)
          apply (rule relcomppI)
           apply (rule iffD2[OF fun_cong[OF fun_cong[OF Grp_UNIV_def]]])
           apply (rule refl)
          apply (unfold prod.case)
          apply (rule context_conjI)
          (* alpha_bij_tac *)
           apply (rule T1.alpha_bijs)
                     apply (erule eq_bij_betw_refl_prems)+
          (* repeat twice *)
             apply (rule ballI)
             apply (unfold T1.FVars_renames[OF f_prems])[1]
             apply (erule imageE)
             apply hypsubst
             apply (unfold eq_bij_betw_refl_def)[1]
             apply (erule conjE)+
             apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
             apply (erule conjE)+
             apply (drule UN_I)
              apply assumption
             apply (rotate_tac -1)
             apply (rule trans)
              apply (drule id_onD[rotated, OF imageI])
               apply assumption
              apply assumption
             apply (rule sym)
             apply (erule id_onD[rotated, OF imageI])
             apply assumption
          (* copied from above *)
            apply (rule ballI)
            apply (unfold T1.FVars_renames[OF f_prems])[1]
            apply (erule imageE)
            apply hypsubst
            apply (unfold eq_bij_betw_refl_def)[1]
            apply (erule conjE)+
            apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
            apply (erule conjE)+
            apply (drule UN_I)
             apply assumption
            apply (rotate_tac -1)
            apply (rule trans)
             apply (drule id_onD[rotated, OF imageI])
              apply assumption
             apply assumption
            apply (rule sym)
            apply (erule id_onD[rotated, OF imageI])
            apply assumption
          (* end repeat twice *)
           apply (rule T1.alpha_refls)
          (* end alpha_bij_tac *)
          apply (rule trans)
           apply (rule arg_cong[of _ _ "PU1map' _ _ _"] arg_cong[of _ _ "PU2map' _ _ _"])
           apply (rule ext)
           apply (rule IHs[THEN conjunct1, symmetric])
                          apply (erule T1.set_subshapes)
                         apply (rule suitable_prems suitable'_prems f_prems imsupp_prems T1.alpha_refls)+
          apply (rule trans)
           apply (rule ext)
           apply (rule IHs[THEN conjunct1, symmetric])
                          apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems)+
                 apply (erule eq_bij_betw_refl_prems)+
             apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
             apply (erule conjE)+
             apply assumption
            apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
            apply (erule conjE)+
            apply assumption
           apply (rule T1.alpha_refls)
          apply (rule sym)
          apply (rule trans)
           apply (rule ext)
           apply (rule IHs[THEN conjunct1, symmetric])
                          apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems)+
                 apply (erule eq_bij_betw_refl_prems)+
             apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
             apply (erule conjE)+
             apply assumption
            apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
            apply (erule conjE)+
            apply assumption
           apply (rule T1.alpha_refls)
          apply (rule IHs[THEN conjunct2])
                         apply (subst T1.rename_comps)
                            apply (rule f_prems)+
                            apply (erule eq_bij_betw_refl_prems)+
                         apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule bij_comp supp_comp_bound infinite_UNIV f_prems | erule eq_bij_betw_refl_prems)+
                        apply (rule suitable_prems f_prems imsupp_prems)+
          apply (rule T1.alpha_syms)
          apply assumption

(* orelse binding recursive set, again *)
         apply (rule relcomppI)
          apply (unfold Grp_UNIV_def)[1]
          apply (rule refl)
         apply (unfold prod.case)
         apply (subst T1.rename_comps, (rule bij_comp supp_comp_bound infinite_UNIV pick_prems f_prems | erule eq_bij_betw_refl_prems)+)+
         apply (rule context_conjI)
          (* binding alpha_bij_tac *)
          apply (rule T1.alpha_bijs)
                    apply (rule bij_comp supp_comp_bound infinite_UNIV pick_prems f_prems | erule eq_bij_betw_refl_prems)+

(* nonbinding recursive occurence *)
            apply (rule ballI)
            apply (subst comp_def)+
            apply (unfold eq_bij_betw_refl_def)[1]
            apply (erule conjE)+
            apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
            apply (erule conjE)+
            apply (drule UN_I)
             apply assumption
            apply (rotate_tac -1)
            apply (rule trans)
             apply (erule id_onD[rotated, OF imageI, of _ _ f1] id_onD[rotated, OF imageI, of _ _ f2])
             apply assumption
            apply (rule sym)
            apply (erule id_onD[rotated, OF imageI])
            apply assumption
          (* copied from above, binding case *)
           apply (rule ballI)
           apply (rule case_split[of "_ \<in> _"])
            apply (unfold eq_bij_betw_refl_def)[1]
            apply (erule conjE)+
            apply (erule eq_onD)
            apply assumption
           apply (unfold comp_assoc[symmetric])[1]
           apply (rule trans)
            apply (rule comp_apply)
           apply (drule DiffI[rotated])
            apply (rule UN_I)
             apply assumption
            apply assumption
           apply (rotate_tac -1)
           apply (rule trans)
            apply (rule arg_cong[of _ _ "_ \<circ> _"])
            apply (erule id_onD[OF pick_id_ons'(1)[OF suitable_prems(1)]]
            id_onD[OF pick_id_ons'(2)[OF suitable_prems(1)]]
            id_onD[OF pick_id_ons'(3)[OF suitable_prems(2)]]
            id_onD[OF pick_id_ons'(4)[OF suitable_prems(3)]]
            id_onD[OF pick_id_ons'(5)[OF suitable_prems(3)]]
            id_onD[OF pick_id_ons'(6)[OF suitable_prems(4)]])
           apply (rule trans[OF comp_apply])
           apply (rule trans)
            apply (unfold eq_bij_betw_refl_def)[1]
            apply (erule conjE)+
            apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
            apply (erule conjE)+
            apply (rotate_tac -1)
            apply (erule id_onD[rotated, OF imageI, of _ _ f1] id_onD[rotated, OF imageI, of _ _ f2])
            apply assumption
           apply (rule sym)
           apply (rule comp_middle)
            apply (unfold eq_bij_betw_refl_def)[1]
            apply (erule conjE)+
            apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
            apply (erule conjE)+
            apply (erule id_onD[rotated, OF imageI])
            apply assumption
           apply (erule id_onD[OF pick_id_on_images'(1)[OF f_prems suitable_prems(1)] imageI]
            id_onD[OF pick_id_on_images'(2)[OF f_prems suitable_prems(1)] imageI]
            id_onD[OF pick_id_on_images'(3)[OF f_prems suitable_prems(2)] imageI]
            id_onD[OF pick_id_on_images'(4)[OF f_prems suitable_prems(3)] imageI]
            id_onD[OF pick_id_on_images'(5)[OF f_prems suitable_prems(3)] imageI]
            id_onD[OF pick_id_on_images'(6)[OF f_prems suitable_prems(4)] imageI])
          (* end repeat twice *)
          apply (rule T1.alpha_refls)
          (* end binding alpha_bij_tac *)
         apply (rule trans)
          apply (rule arg_cong[of _ _ "PU1map' _ _ _"] arg_cong[of _ _ "PU2map' _ _ _"])
          apply (rule ext)
          apply (rule IHs[THEN conjunct1, symmetric])
                         apply (erule T1.set_subshapes T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems imsupp_prems pick_prems bij_id supp_id_bound T1.alpha_refls)+
         apply (subst T1.rename_comps)
                 apply (rule pick_prems f_prems bij_id supp_id_bound)+
         apply (unfold id_o o_id)
         apply (rule trans)
          apply (rule ext)
          apply (rule IHs[THEN conjunct1, symmetric])
                         apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems bij_comp pick_prems supp_comp_bound infinite_UNIV)+
                apply (erule eq_bij_betw_refl_prems)+
            apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
            apply (erule conjE)+
            apply assumption
           apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
           apply (erule conjE)+
           apply assumption
          apply (rule T1.alpha_refls)
         apply (rule sym)
         apply (rule trans)
          apply (rule ext)
          apply (rule IHs[THEN conjunct1, symmetric])
                         apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems bij_comp supp_comp_bound pick_prems infinite_UNIV)+
                apply (erule eq_bij_betw_refl_prems)+
            apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
            apply (erule conjE)+
            apply assumption
           apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
           apply (erule conjE)+
           apply assumption
          apply (rule T1.alpha_refls)
         apply (rule IHs[THEN conjunct2])
                        apply (subst T1.rename_comps)
                            apply (rule f_prems pick_prems bij_comp supp_comp_bound infinite_UNIV)+
                            apply (erule eq_bij_betw_refl_prems)+
                        apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                           apply (rule bij_comp supp_comp_bound infinite_UNIV f_prems pick_prems | erule eq_bij_betw_refl_prems)+
                       apply (rule suitable_prems f_prems imsupp_prems)+
         apply (rule T1.alpha_syms)
         apply (subst T1.rename_comps, (rule bij_comp supp_comp_bound infinite_UNIV pick_prems f_prems | erule eq_bij_betw_refl_prems)+)+
         apply assumption
          (**********************************************************************************************)
          (*    f picks t = f picks' t' *)
        apply (rule ext)
        apply (unfold f_T1_simp[OF suitable_prems] f_T2_simp[OF suitable_prems]
            f_T1_simp[OF suitable'_prems] f_T2_simp[OF suitable'_prems])
        subgoal for p
        proof -
          note exists_bij_betw2s = exists_bij_betw_def[OF _ _ pick_prems(1) pick'_prems(1) h_prems(1),
              of _ set5_T1_pre _ _ set5_T1_pre
              "\<lambda>x. map_T1_pre id id id id id id fst fst fst fst (
            map_T1_pre id id id id (pick1' x' p) (pick2' x' p)
              (\<lambda>t. (t, f_T1 pick1' pick2' pick3' pick4' t))
              (\<lambda>t. (rename_T1 (pick1' x' p) (pick2' x' p) t, f_T1 pick1' pick2' pick3' pick4' (rename_T1 (pick1' x' p) (pick2' x' p) t)))
              (\<lambda>t. (t, f_T2 pick1' pick2' pick3' pick4' t))
              (\<lambda>t. (rename_T2 (pick1' x' p) id t, f_T2 pick1' pick2' pick3' pick4' (rename_T2 (pick1' x' p) id t)))
              x)"
              "\<lambda>x. FVars_T11 (raw_T1_ctor x) \<union> PFVars_1 p \<union> avoiding_set1"
              _ _ "\<lambda>x'. map_T1_pre id id id id id id fst fst fst fst (
            map_T1_pre id id id id (pick1 x p) (pick2 x p)
              (\<lambda>t. (t, f_T1 pick1 pick2 pick3 pick4 t))
              (\<lambda>t. (rename_T1 (pick1 x p) (pick2 x p) t, f_T1 pick1 pick2 pick3 pick4 (rename_T1 (pick1 x p) (pick2 x p) t)))
              (\<lambda>t. (t, f_T2 pick1 pick2 pick3 pick4 t))
              (\<lambda>t. (rename_T2 (pick1 x p) id t, f_T2 pick1 pick2 pick3 pick4 (rename_T2 (pick1 x p) id t)))
              x')"
              ] exists_bij_betw_def[OF _ _ pick_prems(3) pick'_prems(3) h_prems(3),
              of _ set6_T1_pre _ _ set6_T1_pre
              "\<lambda>x. map_T1_pre id id id id id id fst fst fst fst (
            map_T1_pre id id id id (pick1' x' p) (pick2' x' p)
              (\<lambda>t. (t, f_T1 pick1' pick2' pick3' pick4' t))
              (\<lambda>t. (rename_T1 (pick1' x' p) (pick2' x' p) t, f_T1 pick1' pick2' pick3' pick4' (rename_T1 (pick1' x' p) (pick2' x' p) t)))
              (\<lambda>t. (t, f_T2 pick1' pick2' pick3' pick4' t))
              (\<lambda>t. (rename_T2 (pick1' x' p) id t, f_T2 pick1' pick2' pick3' pick4' (rename_T2 (pick1' x' p) id t)))
              x)"
              "\<lambda>x. FVars_T12 (raw_T1_ctor x) \<union> PFVars_2 p \<union> avoiding_set2"
              _ _ "\<lambda>x'. map_T1_pre id id id id id id fst fst fst fst (
            map_T1_pre id id id id (pick1 x p) (pick2 x p)
              (\<lambda>t. (t, f_T1 pick1 pick2 pick3 pick4 t))
              (\<lambda>t. (rename_T1 (pick1 x p) (pick2 x p) t, f_T1 pick1 pick2 pick3 pick4 (rename_T1 (pick1 x p) (pick2 x p) t)))
              (\<lambda>t. (t, f_T2 pick1 pick2 pick3 pick4 t))
              (\<lambda>t. (rename_T2 (pick1 x p) id t, f_T2 pick1 pick2 pick3 pick4 (rename_T2 (pick1 x p) id t)))
              x')"
              ]
          show ?thesis
            apply (rule exE[OF exists_bij_betw2s(1)])
                     apply (rule conjI)
                      apply (rule T1_pre.UNIV_cinfinite)
                     apply (rule card_of_Card_order)
                    apply (rule ordLeq_refl)
                    apply (rule card_of_Card_order)
                   apply (rule T1_pre.mr_rel_set(5)[rotated -1, OF mr_rel_prem])
                         apply (rule supp_id_bound bij_id h_prems)+
              (* bound_tac *)
                  apply (rule T1_pre.Un_bound)
                   apply (rule T1_pre.set_bd_UNIV)
                  apply (rule T1_pre.Un_bound)
                   apply (rule T1_pre.Un_bound)
                    apply (rule T1.card_of_FVars_bounds)
                   apply (rule small_PFVars_1 small_PFVars_2)
                  apply (rule small_avoiding_set1 small_avoiding_set2)
              (* end bound_tac *)
                 apply (subst T1.alpha_FVarss)
                  apply (rule T1.alpha_syms)
                  apply (rule alpha_ctor_picks[OF suitable'_prems])
                 apply (subst T1_pre.map_comp)
                          apply (rule supp_id_bound pick'_prems bij_id)+
                 apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
                 apply (subst T1_pre.set_map)
                        apply (rule supp_id_bound pick'_prems bij_id)+
                 apply (insert suitable'_prems)[1]
                 apply (unfold suitable_defs)
                 apply (erule allE conjE)+
                 apply assumption
                apply (subst T1_pre.map_comp)
                         apply (rule supp_id_bound pick'_prems bij_id)+
                apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
                apply (subst T1_pre.set_map)
                       apply (rule supp_id_bound pick'_prems bij_id)+
                apply (rule refl)
              (* bound_tac *)
               apply (rule T1_pre.Un_bound)
                apply (rule T1_pre.set_bd_UNIV)
               apply (rule T1_pre.Un_bound)
                apply (rule T1_pre.Un_bound)
                 apply (rule T1.card_of_FVars_bounds)
                apply (rule small_PFVars_1 small_PFVars_2)
               apply (rule small_avoiding_set1 small_avoiding_set2)
              (* end bound_tac *)
              apply (subst T1.alpha_FVarss)
               apply (rule T1.alpha_syms)
               apply (rule alpha_ctor_picks[OF suitable_prems])
              apply (subst T1_pre.map_comp)
                       apply (rule supp_id_bound pick_prems bij_id)+
              apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
              apply (subst T1_pre.set_map)
                     apply (rule supp_id_bound pick_prems bij_id)+
              apply (insert suitable_prems)[1]
              apply (unfold suitable_defs)
              apply (erule allE conjE)+
              apply assumption
             apply (subst T1_pre.map_comp)
                      apply (rule supp_id_bound pick_prems bij_id)+
             apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
             apply (subst T1_pre.set_map)
                    apply (rule supp_id_bound pick_prems bij_id)+
             apply (rule refl)
            apply (erule exE)
              (* again, index incremented *)
            apply (rule exE[OF exists_bij_betw2s(2)])
                     apply (rule conjI)
                      apply (rule T1_pre.UNIV_cinfinite)
                     apply (rule card_of_Card_order)
                    apply (rule ordLeq_refl)
                    apply (rule card_of_Card_order)
                   apply (rule T1_pre.mr_rel_set(6)[rotated -1, OF mr_rel_prem])
                         apply (rule supp_id_bound bij_id h_prems)+
              (* bound_tac *)
                  apply (rule T1_pre.Un_bound)
                   apply (rule T1_pre.set_bd_UNIV)
                  apply (rule T1_pre.Un_bound)
                   apply (rule T1_pre.Un_bound)
                    apply (rule T1.card_of_FVars_bounds)
                   apply (rule small_PFVars_1 small_PFVars_2)
                  apply (rule small_avoiding_set1 small_avoiding_set2)
              (* end bound_tac *)
                 apply (subst T1.alpha_FVarss)
                  apply (rule T1.alpha_syms)
                  apply (rule alpha_ctor_picks[OF suitable'_prems])
                 apply (subst T1_pre.map_comp)
                          apply (rule supp_id_bound pick'_prems bij_id)+
                 apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
                 apply (subst T1_pre.set_map)
                        apply (rule supp_id_bound pick'_prems bij_id)+
                 apply (insert suitable'_prems)[1]
                 apply (unfold suitable_defs)
                 apply (erule allE conjE)+
                 apply assumption
                apply (subst T1_pre.map_comp)
                         apply (rule supp_id_bound pick'_prems bij_id)+
                apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
                apply (subst T1_pre.set_map)
                       apply (rule supp_id_bound pick'_prems bij_id)+
                apply (rule refl)
              (* bound_tac *)
               apply (rule T1_pre.Un_bound)
                apply (rule T1_pre.set_bd_UNIV)
               apply (rule T1_pre.Un_bound)
                apply (rule T1_pre.Un_bound)
                 apply (rule T1.card_of_FVars_bounds)
                apply (rule small_PFVars_1 small_PFVars_2)
               apply (rule small_avoiding_set1 small_avoiding_set2)
              (* end bound_tac *)
              apply (subst T1.alpha_FVarss)
               apply (rule T1.alpha_syms)
               apply (rule alpha_ctor_picks[OF suitable_prems])
              apply (subst T1_pre.map_comp)
                       apply (rule supp_id_bound pick_prems bij_id)+
              apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
              apply (subst T1_pre.set_map)
                     apply (rule supp_id_bound pick_prems bij_id)+
              apply (insert suitable_prems)[1]
              apply (unfold suitable_defs)
              apply (erule allE conjE)+
              apply assumption
             apply (subst T1_pre.map_comp)
                      apply (rule supp_id_bound pick_prems bij_id)+
             apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
             apply (subst T1_pre.set_map)
                    apply (rule supp_id_bound pick_prems bij_id)+
             apply (rule refl)
            apply (erule exE)
            apply (rule U1ctor'_cong[rotated 16])
                                apply (((unfold eq_bij_betw_def)[1], (erule conjE)+, assumption)+)[4]
                                apply (subst T1_pre.set_map, (rule supp_id_bound bij_id pick_prems)+)+
                                apply (unfold eq_bij_betw_def)[1]
                                apply (erule conjE)+
                                apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                                apply (unfold image_id)
                                apply assumption
              (* repeated *)
                               apply (subst T1_pre.set_map, (rule supp_id_bound bij_id pick_prems)+)+
                               apply (unfold eq_bij_betw_def)[1]
                               apply (erule conjE)+
                               apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                               apply (unfold image_id)
                               apply assumption
              (* repeated *)
                              apply (subst T1_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                              apply (unfold eq_bij_betw_def)[1]
                              apply (erule conjE)+
                              apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                              apply (unfold image_id)
                              apply assumption
              (* repeated *)
                             apply (subst T1_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                             apply (unfold eq_bij_betw_def)[1]
                             apply (erule conjE)+
                             apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                             apply (unfold image_id)
                             apply assumption
                            defer
                            apply (erule eq_bij_betw_prems)+
              (* subset tac *)
                    apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                    apply (erule UnE)?
                     apply (erule imageE)
                     apply (drule iffD1[OF prod.inject])
                     apply (erule conjE)
                     apply hypsubst
                     apply (rule f_UFVars'[OF suitable_prems])
              (* repeated *)
                    apply (erule UnE)?
                    apply (erule imageE)
                    apply (drule iffD1[OF prod.inject])
                    apply (erule conjE)
                    apply hypsubst
                    apply (rule f_UFVars'[OF suitable_prems])
              (* end subset_tac *)
              (* copied from above *)
                   apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                   apply (erule UnE)?
                    apply (erule imageE)
                    apply (drule iffD1[OF prod.inject])
                    apply (erule conjE)
                    apply hypsubst
                    apply (rule f_UFVars'[OF suitable_prems])
              (* repeated *)
                   apply (erule UnE)?
                   apply (erule imageE)
                   apply (drule iffD1[OF prod.inject])
                   apply (erule conjE)
                   apply hypsubst
                   apply (rule f_UFVars'[OF suitable_prems])

(* copied from above *)
                  apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                  apply (erule UnE)?
                   apply (erule imageE)
                   apply (drule iffD1[OF prod.inject])
                   apply (erule conjE)
                   apply hypsubst
                   apply (rule f_UFVars'[OF suitable_prems])
              (* repeated *)
                  apply (erule UnE)?
                  apply (erule imageE)
                  apply (drule iffD1[OF prod.inject])
                  apply (erule conjE)
                  apply hypsubst
                  apply (rule f_UFVars'[OF suitable_prems])

(* copied from above *)
                 apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                 apply (erule UnE)?
                  apply (erule imageE)
                  apply (drule iffD1[OF prod.inject])
                  apply (erule conjE)
                  apply hypsubst
                  apply (rule f_UFVars'[OF suitable_prems])
              (* repeated *)
                 apply (erule UnE)?
                 apply (erule imageE)
                 apply (drule iffD1[OF prod.inject])
                 apply (erule conjE)
                 apply hypsubst
                 apply (rule f_UFVars'[OF suitable_prems])

(* copied from above *)
                apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                apply (erule UnE)?
                 apply (erule imageE)
                 apply (drule iffD1[OF prod.inject])
                 apply (erule conjE)
                 apply hypsubst
                 apply (rule f_UFVars'[OF suitable'_prems])
              (* repeated *)
                apply (erule UnE)?
                apply (erule imageE)
                apply (drule iffD1[OF prod.inject])
                apply (erule conjE)
                apply hypsubst
                apply (rule f_UFVars'[OF suitable'_prems])

(* copied from above *)
               apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
               apply (erule UnE)?
                apply (erule imageE)
                apply (drule iffD1[OF prod.inject])
                apply (erule conjE)
                apply hypsubst
                apply (rule f_UFVars'[OF suitable'_prems])
              (* repeated *)
               apply (erule UnE)?
               apply (erule imageE)
               apply (drule iffD1[OF prod.inject])
               apply (erule conjE)
               apply hypsubst
               apply (rule f_UFVars'[OF suitable'_prems])

(* copied from above *)
              apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
              apply (erule UnE)?
               apply (erule imageE)
               apply (drule iffD1[OF prod.inject])
               apply (erule conjE)
               apply hypsubst
               apply (rule f_UFVars'[OF suitable'_prems])
              (* repeated *)
              apply (erule UnE)?
              apply (erule imageE)
              apply (drule iffD1[OF prod.inject])
              apply (erule conjE)
              apply hypsubst
              apply (rule f_UFVars'[OF suitable'_prems])

(* copied from above *)
             apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
             apply (erule UnE)?
              apply (erule imageE)
              apply (drule iffD1[OF prod.inject])
              apply (erule conjE)
              apply hypsubst
              apply (rule f_UFVars'[OF suitable'_prems])
              (* repeated *)
             apply (erule UnE)?
             apply (erule imageE)
             apply (drule iffD1[OF prod.inject])
             apply (erule conjE)
             apply hypsubst
             apply (rule f_UFVars'[OF suitable'_prems])

(* mr_rel_goal *)
            apply (rule iffD2[OF T1_pre.mr_rel_map(1)])
                          apply (rule supp_id_bound bij_id pick_prems supp_comp_bound supp_inv_bound infinite_UNIV bij_comp bij_imp_bij_inv | erule eq_bij_betw_prems)+
            apply (unfold id_o o_id inv_id Grp_UNIV_id OO_eq)
            apply (rule iffD2[OF T1_pre.mr_rel_map(3)])
                             apply (rule supp_id_bound bij_id pick_prems pick'_prems supp_comp_bound supp_inv_bound infinite_UNIV bij_comp bij_imp_bij_inv | erule eq_bij_betw_prems)+
            apply (unfold id_o o_id inv_id Grp_UNIV_id OO_eq conversep_eq)
            apply (rule T1_pre.mr_rel_mono_strong0)
                                prefer 15 (* 2 * (free + 2 * bound) + 1) *)
                                apply (rule prems)
                                apply (rule supp_id_bound bij_id h_prems supp_comp_bound supp_inv_bound infinite_UNIV bij_comp bij_imp_bij_inv pick_prems pick'_prems | erule eq_bij_betw_prems)+
              (* REPEAT FIRST' *)
              (* comp = id for free vars *)
                     apply (rule ballI)
                     apply (rule trans)
                      apply (rule id_apply)
                     apply (rule sym)
                     apply (rule trans)
                      apply (rule comp_apply)
                     apply (unfold eq_bij_betw_def)[1]
                     apply (erule conjE)+
                     apply (drule imsupp_id_on)+
                     apply (unfold T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable'_prems], symmetric]
                )[1]
                     apply (rule trans)
                      apply (rule arg_cong[of _ _ "inv _"])
                      apply (erule id_onD)
                      apply (rule UnI1)
                      apply (rule UnI1)
                      apply (erule T1.FVars_intros)
                     apply (erule id_onD[OF id_on_inv, rotated])
                      apply (rule UnI1)
                      apply (rule UnI1)
                      apply (subst (asm) T1_pre.mr_rel_set(1-2,5-6)[rotated -1, OF mr_rel_prem, unfolded image_id, symmetric])
                             apply (rule supp_id_bound bij_id h_prems)+
                      apply (erule T1.FVars_intros)
                     apply assumption
              (* copied from above *)
                    apply (rule ballI)
                    apply (rule trans)
                     apply (rule id_apply)
                    apply (rule sym)
                    apply (rule trans)
                     apply (rule comp_apply)
                    apply (unfold eq_bij_betw_def)[1]
                    apply (erule conjE)+
                    apply (drule imsupp_id_on)+
                    apply (unfold T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable'_prems], symmetric]
                )[1]
                    apply (rule trans)
                     apply (rule arg_cong[of _ _ "inv _"])
                     apply (erule id_onD)
                     apply (rule UnI1)
                     apply (rule UnI1)
                     apply (erule T1.FVars_intros)
                    apply (erule id_onD[OF id_on_inv, rotated])
                     apply (rule UnI1)
                     apply (rule UnI1)
                     apply (subst (asm) T1_pre.mr_rel_set(1-2,5-6)[rotated -1, OF mr_rel_prem, unfolded image_id, symmetric])
                            apply (rule supp_id_bound bij_id h_prems)+
                     apply (erule T1.FVars_intros)
                    apply assumption
              (* orelse *)
                   apply (rule ballI)
                   apply (rule refl)
              (* orelse *)
                  apply (rule ballI)
                  apply (rule ballI)
                  apply (rule impI)
                  apply assumption
              (* orelse comp = id on bound set *)
                 apply (rule ballI)
                 apply (unfold comp_assoc[symmetric])[1]
                 apply (subst o_inv_distrib[symmetric])
                   apply (erule eq_bij_betw_prems)
                  apply (rule pick'_prems)
                 apply (unfold comp_assoc)[1]
                 apply (rule sym)
                 apply (rule trans)
                  apply (rule comp_apply)
                 apply (rule iffD2[OF bij_imp_inv'])
                  apply (rule bij_comp pick'_prems | erule eq_bij_betw_prems)+
                 apply (rule trans[rotated])
                  apply (unfold eq_bij_betw_def)[1]
                  apply (erule conjE eq_onD)+
                  apply assumption
                 apply (unfold comp_def)[1]
                 apply (rule refl)
              (* copied from above *)
                apply (rule ballI)
                apply (unfold comp_assoc[symmetric])[1]
                apply (subst o_inv_distrib[symmetric])
                  apply (erule eq_bij_betw_prems)
                 apply (rule pick'_prems)
                apply (unfold comp_assoc)[1]
                apply (rule sym)
                apply (rule trans)
                 apply (rule comp_apply)
                apply (rule iffD2[OF bij_imp_inv'])
                 apply (rule bij_comp pick'_prems | erule eq_bij_betw_prems)+
                apply (rule trans[rotated])
                 apply (unfold eq_bij_betw_def)[1]
                 apply (erule conjE eq_onD)+
                 apply assumption
                apply (unfold comp_def)[1]
                apply (rule refl)
              (* orelse nonbinding rec set *)
               apply (rule ballI impI)+
               apply (rule relcomppI)
                apply (rule relcomppI)
                 apply (unfold Grp_UNIV_def)[1]
                 apply (rule refl)
                prefer 2
                apply (unfold Grp_UNIV_def conversep_def)[1]
                apply (rule refl)
               apply (unfold prod.case)
               apply (rule context_conjI)
              (* alpha_bij_tac *)
                apply (rule T1.alpha_bijs[rotated -1])
                          apply (assumption | rule T1.alpha_refls)
                         apply (erule eq_bij_betw_prems)+
              (* REPEAT_DETERM *)
                 apply (rule ballI)
                 apply (unfold eq_bij_betw_def T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable'_prems], symmetric]
                )[1]
                 apply (erule conjE)+
                 apply (drule imsupp_id_on)+
                 apply (rule trans)
                  apply (erule id_onD)
                  apply (rule UnI1)
                  apply (rule UnI1)
                  apply (erule T1.FVars_intros)
                  apply assumption
                 apply (rule sym)
                 apply (erule id_onD)
                 apply (rule UnI1)
                 apply (rule UnI1)
                 apply (erule T1.FVars_intros)
                 apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
                  apply assumption
                 apply (rule sym)
                 apply (rule T1.alpha_FVarss)
                 apply assumption
              (* copied from above *)
                apply (rule ballI)
                apply (unfold eq_bij_betw_def T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable'_prems], symmetric]
                )[1]
                apply (erule conjE)+
                apply (drule imsupp_id_on)+
                apply (rule trans)
                 apply (erule id_onD)
                 apply (rule UnI1)
                 apply (rule UnI1)
                 apply (erule T1.FVars_intros)
                 apply assumption
                apply (rule sym)
                apply (erule id_onD)
                apply (rule UnI1)
                apply (rule UnI1)
                apply (erule T1.FVars_intros)
                apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
                 apply assumption
                apply (rule sym)
                apply (rule T1.alpha_FVarss)
                apply assumption
              (* end alpha_bij_tac *)
               apply (rule trans)
                apply (rule ext)
                apply (unfold eq_bij_betw_def)[1]
                apply (erule conjE)+
                apply (rule IHs[THEN conjunct1, symmetric])
                               apply (erule T1.set_subshapes)
                              apply (rule suitable_prems)+
                      apply assumption+
                  apply (unfold Int_Un_distrib Un_empty)[1]
                  apply (erule conjE)+
                  apply assumption
                 apply (unfold Int_Un_distrib Un_empty)[1]
                 apply (erule conjE)+
                 apply assumption
                apply (rule T1.alpha_refls)
               apply (rule trans)
                apply (rule IHs[THEN conjunct2, OF _ suitable_prems suitable'_prems])
                       apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                          prefer 12 (* 5*nvars + 2 *)
                          apply (rule trans)
                           apply (rule ext)
                           apply (rule IHs[THEN conjunct1, OF _ suitable'_prems suitable'_prems])
                                apply (erule T1.set_subshapes)
                                prefer 8
                                apply (rule trans)
                                apply (rule fun_cong[OF PU1map'_alpha])
                                apply assumption
                                apply (rule arg_cong[of _ _ "PU1map' _ _ _"])
                                apply (rule IHs[THEN conjunct2, OF _ suitable'_prems suitable'_prems])
                                apply (erule T1.set_subshapes)
                                apply (rule supp_id_bound bij_id trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left])+
                                apply assumption
                                apply (erule eq_bij_betw_prems)+
                            apply (((unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1], (erule conjE)+, assumption)+)[4]
                        apply (erule eq_bij_betw_prems)+
                 apply (((unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1], (erule conjE)+, assumption)+)[2]
               apply (rule T1.alpha_transs)
                apply assumption
               apply (rule T1.alpha_bij_eqs[THEN iffD2])
                   apply (erule eq_bij_betw_prems)+
               apply (rule T1.alpha_syms)
               apply assumption

(* orelse binding rec set *)
              apply (rule ballI impI relcomppI)+
                apply (unfold Grp_UNIV_def)[1]
                apply (rule refl)
               prefer 2
               apply (unfold Grp_UNIV_def conversep_def)[1]
               apply (rule refl)
              apply (unfold prod.case)
              apply (rule context_conjI)
               apply (subst T1.rename_comps, (rule pick_prems pick'_prems | erule eq_bij_betw_prems)+)+
               apply (rule T1.alpha_transs)
                apply (rule T1.alpha_bijs[rotated -3]) (* -1 - nvars *)
              (* REPEAT_DETERM *)
                          apply (rule ballI)
                          apply (rule sym)
                          apply (rule case_split[of "_ \<in> _"])
                           apply (unfold eq_bij_betw_def)[1]
                           apply (erule conjE)+
                           apply (erule eq_onD)
                           apply assumption
                          apply (frule DiffI[rotated])
                           apply (rule UN_I)
                            apply assumption
                           apply assumption
                          apply (rotate_tac -1)
                          apply (insert h_id_ons)[1]
                          apply (unfold id_on_Un)
                          apply (erule conjE)+
                          apply (rule trans)
                           apply (rule id_on_comp3)
                             apply (erule id_onD[rotated])
                             apply assumption
                            apply (drule T1.FVars_renames[symmetric, OF h_prems, THEN iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]], OF imageI])
                            apply (drule T1.alpha_FVarss[THEN iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]], rotated])
                             apply assumption
                            apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<notin>)"], rotated])
                             apply (rule T1_pre.mr_rel_set(5,6)[rotated -1, OF iffD2[OF T1_pre.mr_rel_flip mr_rel_prem]])
                                apply (rule bij_id supp_id_bound h_prems supp_inv_bound bij_imp_bij_inv)+
                            apply (drule not_imageI[rotated])
                             apply (rule h_prems)
                            apply (unfold image_comp)[1]
                            apply (subst (asm) inv_o_simp2)
                             apply (rule h_prems)
                            apply (unfold image_id)
                            apply (drule DiffI[rotated])
                             apply (rule UN_I)
                              prefer 3
                              apply (rotate_tac -1)
                              apply (erule id_onD[OF pick_id_ons'(1)[OF suitable'_prems(1)]]
                id_onD[OF pick_id_ons'(2)[OF suitable'_prems(1)]]
                id_onD[OF pick_id_ons'(3)[OF suitable'_prems(2)]]
                id_onD[OF pick_id_ons'(4)[OF suitable'_prems(3)]]
                id_onD[OF pick_id_ons'(5)[OF suitable'_prems(3)]]
                id_onD[OF pick_id_ons'(6)[OF suitable'_prems(4)]]
                )
                             apply assumption
                            apply assumption
                           apply (unfold eq_bij_betw_def)[1]
                           apply (erule conjE)+
                           apply (drule imsupp_id_on)+
                           apply (erule id_onD)
                           apply (rule UnI1)
                           apply (rule UnI1)
                           apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                            apply (rule sym)
                            apply (rule T1.alpha_FVarss)
                            apply (rule alpha_ctor_picks[OF suitable'_prems])
                           apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                            apply (rule sym)
                            apply (rule T1.alpha_FVarss)
                            apply (rule alpha_T1_alpha_T2.intros[rotated -1])
                                apply (rule mr_rel_prem h_prems h_id_ons)+
                           apply (erule T1.FVars_intros)
                            apply assumption+
                          apply (rule sym)
                          apply (rule id_on_comp2)
                           apply (erule id_onD[OF pick_id_ons'(1)[OF suitable_prems(1)]]
                id_onD[OF pick_id_ons'(2)[OF suitable_prems(1)]]
                id_onD[OF pick_id_ons'(3)[OF suitable_prems(2)]]
                id_onD[OF pick_id_ons'(4)[OF suitable_prems(3)]]
                id_onD[OF pick_id_ons'(5)[OF suitable_prems(3)]]
                id_onD[OF pick_id_ons'(6)[OF suitable_prems(4)]])
                          apply (unfold eq_bij_betw_def)[1]
                          apply (erule conjE)+
                          apply (drule imsupp_id_on)+
                          apply (erule id_onD)
                          apply (rule UnI1)
                          apply (rule UnI1)
                          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                           apply (rule sym)
                           apply (rule T1.alpha_FVarss)
                           apply (rule alpha_ctor_picks[OF suitable_prems])
                          apply (erule T1.FVars_intros)
                           apply assumption+
              (* copied from above *)
                         apply (rule ballI)
                         apply (rule sym)
                         apply (rule case_split[of "_ \<in> _"])
                          apply (unfold eq_bij_betw_def)[1]
                          apply (erule conjE)+
                          apply (erule eq_onD)
                          apply assumption
                         apply (frule DiffI[rotated])
                          apply (rule UN_I)
                           apply assumption
                          apply assumption
                         apply (rotate_tac -1)
                         apply (insert h_id_ons)[1]
                         apply (unfold id_on_Un)
                         apply (erule conjE)+
                         apply (rule trans)
                          apply (rule id_on_comp3)
                            apply (erule id_onD[rotated])
                            apply assumption
                           apply (drule T1.FVars_renames[symmetric, OF h_prems, THEN iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]], OF imageI])
                           apply (drule T1.alpha_FVarss[THEN iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]], rotated])
                            apply assumption
                           apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<notin>)"], rotated])
                            apply (rule T1_pre.mr_rel_set(5,6)[rotated -1, OF iffD2[OF T1_pre.mr_rel_flip mr_rel_prem]])
                                apply (rule bij_id supp_id_bound h_prems supp_inv_bound bij_imp_bij_inv)+
                           apply (drule not_imageI[rotated])
                            apply (rule h_prems)
                           apply (unfold image_comp)[1]
                           apply (subst (asm) inv_o_simp2)
                            apply (rule h_prems)
                           apply (unfold image_id)
                           apply (drule DiffI[rotated])
                            apply (rule UN_I)
                             prefer 3
                             apply (rotate_tac -1)
                             apply (erule id_onD[OF pick_id_ons'(1)[OF suitable'_prems(1)]]
                id_onD[OF pick_id_ons'(2)[OF suitable'_prems(1)]]
                id_onD[OF pick_id_ons'(3)[OF suitable'_prems(2)]]
                id_onD[OF pick_id_ons'(4)[OF suitable'_prems(3)]]
                id_onD[OF pick_id_ons'(5)[OF suitable'_prems(3)]]
                id_onD[OF pick_id_ons'(6)[OF suitable'_prems(4)]]
                )
                            apply assumption
                           apply assumption
                          apply (unfold eq_bij_betw_def)[1]
                          apply (erule conjE)+
                          apply (drule imsupp_id_on)+
                          apply (erule id_onD)
                          apply (rule UnI1)
                          apply (rule UnI1)
                          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                           apply (rule sym)
                           apply (rule T1.alpha_FVarss)
                           apply (rule alpha_ctor_picks[OF suitable'_prems])
                          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                           apply (rule sym)
                           apply (rule T1.alpha_FVarss)
                           apply (rule alpha_T1_alpha_T2.intros[rotated -1])
                                apply (rule mr_rel_prem h_prems h_id_ons)+
                          apply (erule T1.FVars_intros)
                           apply assumption+
                         apply (rule sym)
                         apply (rule id_on_comp2)
                          apply (erule id_onD[OF pick_id_ons'(1)[OF suitable_prems(1)]]
                id_onD[OF pick_id_ons'(2)[OF suitable_prems(1)]]
                id_onD[OF pick_id_ons'(3)[OF suitable_prems(2)]]
                id_onD[OF pick_id_ons'(4)[OF suitable_prems(3)]]
                id_onD[OF pick_id_ons'(5)[OF suitable_prems(3)]]
                id_onD[OF pick_id_ons'(6)[OF suitable_prems(4)]])
                         apply (unfold eq_bij_betw_def)[1]
                         apply (erule conjE)+
                         apply (drule imsupp_id_on)+
                         apply (erule id_onD)
                         apply (rule UnI1)
                         apply (rule UnI1)
                         apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                          apply (rule sym)
                          apply (rule T1.alpha_FVarss)
                          apply (rule alpha_ctor_picks[OF suitable_prems])
                         apply (erule T1.FVars_intros)
                          apply assumption+
              (* end repeat *)
                        apply (rule T1.alpha_refls)
                       apply (rule bij_comp pick_prems pick'_prems supp_comp_bound infinite_UNIV h_prems | erule eq_bij_betw_prems)+
               apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ alpha_T1]])
                apply (rule T1.rename_comps[symmetric])
                       apply (rule h_prems bij_comp pick'_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
               apply (rule T1.alpha_bij_eqs[THEN iffD2])
                   apply (rule h_prems bij_comp pick'_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
               apply assumption
              (* PUmap' ... (f ...) = PUmap' ... (f ...) *)
              apply (rule trans)
               apply (rule ext)
               apply (rule IHs[THEN conjunct1, symmetric])
                              apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                                apply (rule pick_prems suitable_prems | erule eq_bij_betw_prems)+
                 apply (unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1]
                 apply (erule conjE)+
                 apply assumption
                apply (unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1]
                apply (erule conjE)+
                apply assumption
               apply (rule T1.alpha_refls)
              apply (subst T1.rename_comps)
                      apply (rule pick_prems | erule eq_bij_betw_prems)+
              apply (rule trans)
               apply (rule IHs[THEN conjunct2])
                              apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                                apply (rule bij_comp pick_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
                             apply ((rule suitable_prems)+)[4]
                         apply (rule suitable'_prems)+
                     prefer 7 (* 3*nvars + 1 *)
                     apply (subst (asm) T1.rename_comps, (rule pick_prems pick'_prems | erule eq_bij_betw_prems)+)+
                     apply (rule T1.alpha_transs)
                      apply assumption
                     apply (rule T1.alpha_bij_eqs[THEN iffD2])
                         apply (rule bij_comp pick_prems pick'_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
                     apply (rule T1.alpha_syms)
                     apply assumption
                    prefer 7 (* 7*nvars + 1 *)
                    apply (subst T1.rename_comps[symmetric], (rule pick_prems pick'_prems | erule eq_bij_betw_prems)+)+
                    apply (rule trans)
                     apply (rule ext)
                     apply (rule IHs[THEN conjunct1])
                                apply (subst T1.rename_comps, (rule pick_prems pick'_prems h_prems)+)+
                                apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                                apply (rule h_prems suitable'_prems bij_comp pick_prems pick'_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
                       apply (unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1]
                       apply (erule conjE)+
                       apply assumption
                      apply (unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1]
                      apply (erule conjE)+
                      apply assumption
                     apply (rule T1.alpha_refls)
                    apply (rule trans)
                     apply (rule fun_cong[OF PU1map'_alpha])
                     apply (rule T1.alpha_bij_eqs[THEN iffD2])
                         apply (rule pick'_prems)+
                     apply assumption
                    apply (rule arg_cong[of _ _ "PU1map' _ _ _"])
                    apply (rule IHs[THEN conjunct2])
                                apply (subst T1.rename_comps, (rule pick_prems pick'_prems h_prems)+)+
                                apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                                apply (rule supp_id_bound bij_id h_prems suitable'_prems bij_comp pick_prems pick'_prems supp_comp_bound infinite_UNIV trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left] | erule eq_bij_betw_prems)+
                    apply (rule T1.alpha_bij_eqs[THEN iffD2])
                        apply (rule pick'_prems)+
                    apply assumption
                   apply (rule supp_id_bound bij_id trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left])+

(* orelse nonbinding rec set, again *)
             apply (rule ballI impI)+
             apply (rule relcomppI)
              apply (rule relcomppI)
               apply (unfold Grp_UNIV_def)[1]
               apply (rule refl)
              prefer 2
              apply (unfold Grp_UNIV_def conversep_def)[1]
              apply (rule refl)
             apply (unfold prod.case)
             apply (rule context_conjI)
              (* alpha_bij_tac *)
              apply (rule T1.alpha_bijs[rotated -1])
                        apply (assumption | rule T1.alpha_refls)
                       apply (erule eq_bij_betw_prems)+
              (* REPEAT_DETERM *)
               apply (rule ballI)
               apply (unfold eq_bij_betw_def T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable'_prems], symmetric]
                )[1]
               apply (erule conjE)+
               apply (drule imsupp_id_on)+
               apply (rule trans)
                apply (erule id_onD)
                apply (rule UnI1)
                apply (rule UnI1)
                apply (erule T1.FVars_intros)
                apply assumption
               apply (rule sym)
               apply (erule id_onD)
               apply (rule UnI1)
               apply (rule UnI1)
               apply (erule T1.FVars_intros)
               apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
                apply assumption
               apply (rule sym)
               apply (rule T1.alpha_FVarss)
               apply assumption
              (* copied from above *)
              apply (rule ballI)
              apply (unfold eq_bij_betw_def T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable'_prems], symmetric]
                )[1]
              apply (erule conjE)+
              apply (drule imsupp_id_on)+
              apply (rule trans)
               apply (erule id_onD)
               apply (rule UnI1)
               apply (rule UnI1)
               apply (erule T1.FVars_intros)
               apply assumption
              apply (rule sym)
              apply (erule id_onD)
              apply (rule UnI1)
              apply (rule UnI1)
              apply (erule T1.FVars_intros)
              apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
               apply assumption
              apply (rule sym)
              apply (rule T1.alpha_FVarss)
              apply assumption
              (* end alpha_bij_tac *)
             apply (rule trans)
              apply (rule ext)
              apply (unfold eq_bij_betw_def)[1]
              apply (erule conjE)+
              apply (rule IHs[THEN conjunct1, symmetric])
                             apply (erule T1.set_subshapes)
                            apply (rule suitable_prems)+
                    apply assumption+
                apply (unfold Int_Un_distrib Un_empty)[1]
                apply (erule conjE)+
                apply assumption
               apply (unfold Int_Un_distrib Un_empty)[1]
               apply (erule conjE)+
               apply assumption
              apply (rule T1.alpha_refls)
             apply (rule trans)
              apply (rule IHs[THEN conjunct2, OF _ suitable_prems suitable'_prems])
                     apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                        prefer 12 (* 5*nvars + 2 *)
                        apply (rule trans)
                         apply (rule ext)
                         apply (rule IHs[THEN conjunct1, OF _ suitable'_prems suitable'_prems])
                                apply (erule T1.set_subshapes)
                               prefer 8
                               apply (rule trans)
                                apply (rule fun_cong[OF PU2map'_alpha])
                                apply assumption
                               apply (rule arg_cong[of _ _ "PU2map' _ _ _"])
                               apply (rule IHs[THEN conjunct2, OF _ suitable'_prems suitable'_prems])
                                apply (erule T1.set_subshapes)
                                apply (rule supp_id_bound bij_id trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left])+
                               apply assumption
                              apply (erule eq_bij_betw_prems)+
                          apply (((unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1], (erule conjE)+, assumption)+)[4]
                      apply (erule eq_bij_betw_prems)+
               apply (((unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1], (erule conjE)+, assumption)+)[2]
             apply (rule T1.alpha_transs)
              apply assumption
             apply (rule T1.alpha_bij_eqs[THEN iffD2])
                 apply (erule eq_bij_betw_prems)+
             apply (rule T1.alpha_syms)
             apply assumption

(* orelse binding rec set, again *)
            apply (rule ballI impI relcomppI)+
              apply (unfold Grp_UNIV_def)[1]
              apply (rule refl)
             prefer 2
             apply (unfold Grp_UNIV_def conversep_def)[1]
             apply (rule refl)
            apply (unfold prod.case)
            apply (subst T1.rename_comps, (rule pick_prems pick'_prems bij_id supp_id_bound | erule eq_bij_betw_prems)+)+
            apply (unfold id_o o_id)
            apply (rule context_conjI)
             apply (rule T1.alpha_transs)
              apply (rule T1.alpha_bijs[rotated -3]) (* -1 - nvars *)
              (* REPEAT_DETERM *)
                        apply (rule ballI)
                        apply (unfold eq_bij_betw_def)[1]
                        apply (erule conjE)+
                        apply (subst (asm)
                T1.alpha_FVarss(1)[OF alpha_ctor_picks(1)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(2)[OF alpha_ctor_picks(2)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(3)[OF alpha_ctor_picks(1)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(4)[OF alpha_ctor_picks(2)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(1)[OF alpha_ctor_picks(1)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(2)[OF alpha_ctor_picks(2)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(3)[OF alpha_ctor_picks(1)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(4)[OF alpha_ctor_picks(2)[OF suitable'_prems], symmetric])+
                        apply (drule imsupp_id_on)+
                        apply (erule id_on_eq)
                          apply assumption
                         apply (rule arg_cong2[OF _ refl, of _ _ "(\<union>)"])+
                         apply (rule T1.alpha_FVarss)
                         apply (rule alpha_T1_alpha_T2.intros[rotated -1])
                               apply (rule mr_rel_prem)
                              apply (rule h_prems h_id_ons)+
                        apply (rule UnI1)
                        apply (rule UnI1)
                        apply (erule T1.FVars_intros)
                        apply assumption
              (* orelse *)
                       apply (rule ballI)
                       apply (rule sym)
                       apply (rule case_split[of "_ \<in> _"])
                        apply (unfold eq_bij_betw_def)[1]
                        apply (erule conjE)+
                        apply (erule eq_onD)
                        apply assumption
                       apply (frule DiffI[rotated])
                        apply (rule UN_I)
                         apply assumption
                        apply assumption
                       apply (rotate_tac -1)
                       apply (insert h_id_ons)[1]
                       apply (unfold id_on_Un)
                       apply (erule conjE)+
                       apply (rule trans)
                        apply (rule id_on_comp3)
                          apply (erule id_onD[rotated])
                          apply assumption
            thm T1.FVars_renames[symmetric, THEN iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]], rotated -1, OF imageI] (*, THEN iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]], OF imageI]*)
                         apply (drule T1.FVars_renames[symmetric, THEN iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]], rotated -1, OF imageI])
                             prefer 5 (* 2*nvars + 1 *)
                             apply (drule T1.alpha_FVarss[THEN iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]], rotated])
                              apply assumption
                             apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<notin>)"], rotated])
                              apply (rule T1_pre.mr_rel_set(5,6)[rotated -1, OF iffD2[OF T1_pre.mr_rel_flip mr_rel_prem]])
                                apply (rule bij_id supp_id_bound h_prems supp_inv_bound bij_imp_bij_inv)+
                             apply (drule not_imageI[rotated])
                              apply (rule h_prems)
                             apply (unfold image_comp)[1]
                             apply (subst (asm) inv_o_simp2)
                              apply (rule h_prems)
                             apply (unfold image_id)
                             apply (drule DiffI[rotated])
                              apply (erule UN_I[of _ _ _ FVars_T11, rotated] UN_I[of _ _ _ FVars_T12, rotated]
                UN_I[of _ _ _ FVars_T21, rotated] UN_I[of _ _ _ FVars_T22, rotated])
                              apply assumption
                             apply (rotate_tac -1)
                             apply (erule id_onD[OF pick_id_ons'(1)[OF suitable'_prems(1)]]
                id_onD[OF pick_id_ons'(2)[OF suitable'_prems(1)]]
                id_onD[OF pick_id_ons'(3)[OF suitable'_prems(2)]]
                id_onD[OF pick_id_ons'(4)[OF suitable'_prems(3)]]
                id_onD[OF pick_id_ons'(5)[OF suitable'_prems(3)]]
                id_onD[OF pick_id_ons'(6)[OF suitable'_prems(4)]]
                )
                            apply (rule h_prems bij_id supp_id_bound)+
                        apply (unfold eq_bij_betw_def)[1]
                        apply (erule conjE)+
                        apply (drule imsupp_id_on)+
                        apply (erule id_onD)
                        apply (rule UnI1)
                        apply (rule UnI1)
                        apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                         apply (rule sym)
                         apply (rule T1.alpha_FVarss)
                         apply (rule alpha_ctor_picks[OF suitable'_prems])
                        apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                         apply (rule sym)
                         apply (rule T1.alpha_FVarss)
                         apply (rule alpha_T1_alpha_T2.intros[rotated -1])
                               apply (rule mr_rel_prem h_prems h_id_ons)+
                        apply (erule T1.FVars_intros)
                         apply assumption+
                       apply (rule sym)
                       apply (rule id_on_comp2)
                        apply (erule id_onD[OF pick_id_ons'(1)[OF suitable_prems(1)]]
                id_onD[OF pick_id_ons'(2)[OF suitable_prems(1)]]
                id_onD[OF pick_id_ons'(3)[OF suitable_prems(2)]]
                id_onD[OF pick_id_ons'(4)[OF suitable_prems(3)]]
                id_onD[OF pick_id_ons'(5)[OF suitable_prems(3)]]
                id_onD[OF pick_id_ons'(6)[OF suitable_prems(4)]])
                       apply (unfold eq_bij_betw_def)[1]
                       apply (erule conjE)+
                       apply (drule imsupp_id_on)+
                       apply (erule id_onD)
                       apply (rule UnI1)
                       apply (rule UnI1)
                       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                        apply (rule sym)
                        apply (rule T1.alpha_FVarss)
                        apply (rule alpha_ctor_picks[OF suitable_prems])
                       apply (erule T1.FVars_intros)
                        apply assumption+
                      apply (rule T1.alpha_refls)
                     apply (rule bij_comp pick_prems pick'_prems supp_comp_bound infinite_UNIV h_prems | erule eq_bij_betw_prems)+
             apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ alpha_T2]])
              apply (rule trans)
               apply (rule arg_cong3[of _ _ _ _ _ _ rename_T2])
                 prefer 4 (* 2*nvars + 2 *)
                 apply (rule T1.rename_comps[symmetric])
                        prefer 9 (* 4*nvars + 1*)
                        apply (rule refl)
                       prefer 9 (* 4*nvars + 1 *)
              (* refl orelse *) apply (rule o_id[symmetric])
                      apply (rule bij_id supp_id_bound h_prems bij_comp pick'_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
              apply (rule refl)
             apply (rule T1.alpha_bij_eqs[THEN iffD2])
                 apply (rule h_prems bij_comp pick'_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
             apply assumption
              (* PUmap' ... (f ...) = PUmap' ... (f ...) *)
            apply (rule trans)
             apply (rule ext)
             apply (rule IHs[THEN conjunct1, symmetric])
                            apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                               apply (rule bij_id supp_id_bound pick_prems suitable_prems | erule eq_bij_betw_prems)+
               apply (unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1]
               apply (erule conjE)+
               apply assumption
              apply (unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1]
              apply (erule conjE)+
              apply assumption
             apply (rule T1.alpha_refls)
            apply (subst T1.rename_comps)
                    apply (rule bij_id supp_id_bound pick_prems | erule eq_bij_betw_prems)+
            apply (rule trans)
             apply (rule IHs[THEN conjunct2])
                            apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                               apply (rule bij_id supp_id_bound bij_comp pick_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
                           apply ((rule suitable_prems)+)[4]
                       apply (rule suitable'_prems)+
                   prefer 7 (* 3*nvars + 1 *)
                   apply ((subst (asm) T1.rename_comps, (rule pick_prems pick'_prems | erule eq_bij_betw_prems)+)+)?
                   apply (rule T1.alpha_transs)
                    apply (unfold id_o o_id)[1]
                    apply assumption
                   apply (rule T1.alpha_bij_eqs[THEN iffD2])
                       apply (rule bij_comp pick_prems pick'_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
                   apply (rule T1.alpha_syms)
                   apply assumption
                  prefer 7 (* 7*nvars + 1 *)
                  apply (subst T1.rename_comps[symmetric] T1.rename_comps[symmetric, OF _ _ bij_id supp_id_bound, unfolded o_id], (rule pick_prems pick'_prems | erule eq_bij_betw_prems)+)+
                  apply (rule trans)
                   apply (rule ext)
                   apply (rule IHs[THEN conjunct1])
                                apply (subst T1.rename_comps, (rule bij_id supp_id_bound pick_prems pick'_prems h_prems)+)+
                                apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                                apply (rule bij_id supp_id_bound h_prems suitable'_prems bij_comp pick_prems pick'_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
                     apply (unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1]
                     apply (erule conjE)+
                     apply assumption
                    apply (unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1]
                    apply (erule conjE)+
                    apply assumption
                   apply (rule T1.alpha_refls)
                  apply (rule trans)
                   apply (rule fun_cong[OF PU2map'_alpha])
                   apply (rule T1.alpha_bij_eqs[THEN iffD2])
                       apply (rule bij_id supp_id_bound pick'_prems)+
                   apply assumption
                  apply (rule arg_cong[of _ _ "PU2map' _ _ _"])
                  apply (rule IHs[THEN conjunct2])
                                apply (subst T1.rename_comps, (rule bij_id supp_id_bound pick_prems pick'_prems h_prems)+)+
                                apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                                apply (rule supp_id_bound bij_id h_prems suitable'_prems bij_comp pick_prems pick'_prems supp_comp_bound infinite_UNIV trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left] | erule eq_bij_betw_prems)+
                  apply (rule T1.alpha_bij_eqs[THEN iffD2])
                      apply (rule supp_id_bound bij_id pick'_prems)+
                  apply assumption
                 apply (rule supp_id_bound bij_id trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left])+
            done
        qed
        done
    qed
    done

(*******************************************************************)
(***          SECOND TYPE             ******************************)
(*******************************************************************)

  subgoal
    apply (rule allI impI)+
    apply (erule alpha_T1.cases alpha_T2.cases)
    apply hypsubst_thin
    apply (unfold triv_forall_equality)
    subgoal premises prems for p f1 f2 pick1 pick2 pick3 pick4 pick1' pick2' pick3' pick4' h1 h2 x x'
    proof -
      thm prems
      note suitable_prems = prems(3-6)
      note suitable'_prems = prems(7-10)
      note f_prems = prems(11-14)
      note imsupp_prems = prems(15,16)
      note h_prems = prems(17-20)
      note h_id_ons = prems(21-22)
      note mr_rel_prem = prems(23)
      note IHs =
        mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF prems(1)]]]]]]]]]]]]]]]]]]]]]]]]]]]
        mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF mp[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF spec[OF prems(2)]]]]]]]]]]]]]]]]]]]]]]]]]]]
      note exists_bij_betw's = exists_bij_betw_refl_def[
          OF conjI[OF T2_pre.UNIV_cinfinite card_of_Card_order],
          of _ _ set5_T2_pre "XXl2 pick1 pick2 pick3 pick4 f1 f2 p" x
          _ _ "XXr2 pick1 pick2 pick3 pick4 f1 f2 p"
          ] exists_bij_betw_refl_def[
          OF conjI[OF T2_pre.UNIV_cinfinite card_of_Card_order],
          of _ _ set6_T2_pre "XXl2 pick1 pick2 pick3 pick4 f1 f2 p" x
          _ _ "XXr2 pick1 pick2 pick3 pick4 f1 f2 p"
          ]
      note exists_bij_betws = exE[OF exists_bij_betw's(1)[
            of _ _ "\<lambda>x. FVars_T21 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst x)) \<union> PFVars_1 p \<union> avoiding_set1",
            rotated 3
            ]] exE[OF exists_bij_betw's(2)[
            of _ _ "\<lambda>x. FVars_T22 (raw_T2_ctor (map_T2_pre id id id id id id fst fst fst fst x)) \<union> PFVars_2 p \<union> avoiding_set2",
            rotated 3
            ]]
      note pick_prems =
        suitable_bij(1)[OF suitable_prems(1)] suitable_supp_bound(1)[OF suitable_prems(1)]
        suitable_bij(2)[OF suitable_prems(2)] suitable_supp_bound(2)[OF suitable_prems(2)]
        suitable_bij(3)[OF suitable_prems(3)] suitable_supp_bound(3)[OF suitable_prems(3)]
        suitable_bij(4)[OF suitable_prems(4)] suitable_supp_bound(4)[OF suitable_prems(4)]
      note pick'_prems =
        suitable_bij(1)[OF suitable'_prems(1)] suitable_supp_bound(1)[OF suitable'_prems(1)]
        suitable_bij(2)[OF suitable'_prems(2)] suitable_supp_bound(2)[OF suitable'_prems(2)]
        suitable_bij(3)[OF suitable'_prems(3)] suitable_supp_bound(3)[OF suitable'_prems(3)]
        suitable_bij(4)[OF suitable'_prems(4)] suitable_supp_bound(4)[OF suitable'_prems(4)]
      show ?thesis
        apply (rule conjI)
         apply (rule trans)
          (* mk_arg_cong npicks + 2 *) apply (rule arg_cong2[OF _ refl, of _ _ "f_T2 _ _ _ _"])
          apply (rule T1.rename_simps)
             apply (rule f_prems)+
         apply (rule trans)
          apply (rule f_T2_simp[OF suitable_prems] f_T1_simp[OF suitable_prems])
         apply (rule trans)
          apply (subst T1_pre.map_comp T2_pre.map_comp)
                     apply (rule f_prems supp_id_bound bij_id | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+
          apply (unfold id_o o_id comp_def[of "\<lambda>t. (_ t, _ t)"])
          apply (subst T1.rename_comps, (rule f_prems supp_id_bound bij_id | ((insert suitable_prems)[1], erule suitable_bij suitable_supp_bound))+)+
          apply (unfold id_o o_id)
          apply (unfold XXr2_def[symmetric])
          apply (rule refl)
         apply (rule sym)
         apply (rule trans)
          apply (rule fun_cong[OF fun_cong[OF PU2map'_alpha]])
          apply (rule alpha_ctor_picks[OF suitable_prems])
         apply (unfold PU2map'_def)
         apply (rule trans)
          apply (rule trans)
          (* mk_arg_cong nvars + 2 *) apply (rule arg_cong[of _ _ "U2map' _ _ _"])
           apply (rule f_T2_simp[OF suitable_prems])
          apply (rule U2map'_Uctor')
             apply (rule f_prems)+
         apply (subst trans[OF comp_apply[symmetric] fun_cong[OF Pmap_comp0[symmetric]]])
                 apply (rule f_prems bij_imp_bij_inv supp_inv_bound)+
         apply (subst inv_o_simp2, rule f_prems)+
         apply (unfold fun_cong[OF Pmap_id0, unfolded id_def, unfolded id_def[symmetric]])
         apply (subst T2_pre.map_comp)
                    apply (rule supp_id_bound bij_id f_prems pick_prems)+
         apply (unfold id_o o_id)
         apply (unfold comp_pair prod.case)
         apply (subst T1.rename_comps, (rule supp_id_bound bij_id f_prems pick_prems)+)+
         apply (unfold id_o o_id)
         apply (unfold XXl2_def[symmetric])
          (* EVERY' (map ... exists_bij_betws) *)
         apply (rule exists_bij_betws(1))
          (* repeat twice *)
          (* bound_tac *)
                  apply (rule T1_pre.Un_bound)
                   apply (rule T2_pre.set_bd_UNIV)
                  apply (rule T1_pre.Un_bound)
                   apply (rule T1_pre.Un_bound)
                    apply (rule T1.card_of_FVars_bounds)
                   apply (rule small_PFVars_1 small_PFVars_2)
                  apply (rule small_avoiding_set1 small_avoiding_set2)
          (* end bound_tac *)
                 apply (rule int_empties3[OF suitable_prems] int_empties4[OF suitable_prems])
                      apply (rule f_prems imsupp_prems)+
                apply (unfold XXl2_def XXr2_def)[1]
                apply (subst T2_pre.set_map)
                       apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV pick_prems)+
                apply (rule refl)
          (* repeated *)
          (* bound_tac *)
               apply (rule T1_pre.Un_bound)
                apply (rule T2_pre.set_bd_UNIV)
               apply (rule T1_pre.Un_bound)
                apply (rule T1_pre.Un_bound)
                 apply (rule T1.card_of_FVars_bounds)
                apply (rule small_PFVars_1 small_PFVars_2)
               apply (rule small_avoiding_set1 small_avoiding_set2)
          (* end bound_tac *)
              apply (rule int_empties3[OF suitable_prems] int_empties4[OF suitable_prems])
                   apply (rule f_prems imsupp_prems)+
             apply (unfold XXl2_def XXr2_def)[1]
             apply (subst T2_pre.set_map)
                    apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV pick_prems)+
             apply (rule refl)
          (* end repeat *)
            apply (rule ordLeq_refl)
            apply (rule card_of_Card_order)
           apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV pick_prems)+
          (* copied from above *)
         apply (rule exists_bij_betws(2))
          (* repeat twice *)
          (* bound_tac *)
                  apply (rule T1_pre.Un_bound)
                   apply (rule T2_pre.set_bd_UNIV)
                  apply (rule T1_pre.Un_bound)
                   apply (rule T1_pre.Un_bound)
                    apply (rule T1.card_of_FVars_bounds)
                   apply (rule small_PFVars_1 small_PFVars_2)
                  apply (rule small_avoiding_set1 small_avoiding_set2)
          (* end bound_tac *)
                 apply (rule int_empties3[OF suitable_prems] int_empties4[OF suitable_prems])
                      apply (rule f_prems imsupp_prems)+
                apply (unfold XXl2_def XXr2_def)[1]
                apply (subst T2_pre.set_map)
                       apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV pick_prems)+
                apply (rule refl)
          (* repeated *)
          (* bound_tac *)
               apply (rule T1_pre.Un_bound)
                apply (rule T2_pre.set_bd_UNIV)
               apply (rule T1_pre.Un_bound)
                apply (rule T1_pre.Un_bound)
                 apply (rule T1.card_of_FVars_bounds)
                apply (rule small_PFVars_1 small_PFVars_2)
               apply (rule small_avoiding_set1 small_avoiding_set2)
          (* end bound_tac *)
              apply (rule int_empties3[OF suitable_prems] int_empties4[OF suitable_prems])
                   apply (rule f_prems imsupp_prems)+
             apply (unfold XXl2_def XXr2_def)[1]
             apply (subst T2_pre.set_map)
                    apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV pick_prems)+
             apply (rule refl)
          (* end repeat *)
            apply (rule ordLeq_refl)
            apply (rule card_of_Card_order)
           apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV pick_prems)+
          (* END EVERY' *)
         apply (erule exE)+
         apply (rule U2ctor'_cong[rotated 16])
                            apply (((unfold eq_bij_betw_refl_def)[1], (erule conjE)+, assumption)+)[8]
                         defer
                         apply (((unfold eq_bij_betw_refl_def)[1], (erule conjE)+, assumption)+)[8]
          (* REPEAT_DETERM *)
                 apply (erule XXl_U1FVars'_2[OF suitable_prems f_prems, rotated -1]
            XXl_U2FVars'_2[OF suitable_prems f_prems, rotated -1]
            )
                 apply (erule IHs[THEN conjunct1])
                            apply (rule suitable_prems suitable'_prems f_prems imsupp_prems T1.alpha_refls)+
          (* copied from above *)
                apply (erule XXl_U1FVars'_2[OF suitable_prems f_prems, rotated -1]
            XXl_U2FVars'_2[OF suitable_prems f_prems, rotated -1]
            )
                apply (erule IHs[THEN conjunct1])
                            apply (rule suitable_prems suitable'_prems f_prems imsupp_prems T1.alpha_refls)+
          (* copied from above *)
               apply (erule XXl_U1FVars'_2[OF suitable_prems f_prems, rotated -1]
            XXl_U2FVars'_2[OF suitable_prems f_prems, rotated -1]
            )
               apply (erule IHs[THEN conjunct1])
                            apply (rule suitable_prems suitable'_prems f_prems imsupp_prems T1.alpha_refls)+
          (* copied from above *)
              apply (erule XXl_U1FVars'_2[OF suitable_prems f_prems, rotated -1]
            XXl_U2FVars'_2[OF suitable_prems f_prems, rotated -1]
            )
              apply (erule IHs[THEN conjunct1])
                            apply (rule suitable_prems suitable'_prems f_prems imsupp_prems T1.alpha_refls)+
          (* END REPEAT_DETERM *)
             apply (erule XXr_U1FVars'_2[OF suitable_prems f_prems] XXr_U2FVars'_2[OF suitable_prems f_prems])+
         defer
          (* mr_rel_goal *)
         apply (subst XXl1_def XXl2_def XXr1_def XXr2_def)+
         apply (rule iffD2[OF T2_pre.mr_rel_map(1)])
                       apply (rule f_prems supp_id_bound bij_id bij_comp pick_prems
            supp_comp_bound infinite_UNIV supp_inv_bound bij_imp_bij_inv | erule eq_bij_betw_refl_prems)+
         apply (unfold id_o o_id Grp_UNIV_id OO_eq)
         apply (rule iffD2[OF T2_pre.mr_rel_map(3)])
                          apply (rule f_prems supp_id_bound bij_id bij_comp pick_prems
            supp_comp_bound infinite_UNIV supp_inv_bound bij_imp_bij_inv | erule eq_bij_betw_refl_prems)+
         apply (unfold inv_id id_o o_id Grp_UNIV_id conversep_eq OO_eq)
         apply (unfold relcompp_conversep_Grp mr_rel_T2_pre_def)
         apply (rule iffD2[OF T2_pre.rel_cong])
                apply (rule trans[OF T2_pre.map_cong0 T2_pre.map_id])
                            apply (rule supp_comp_bound f_prems supp_inv_bound infinite_UNIV supp_id_bound bij_id bij_comp pick_prems bij_imp_bij_inv | erule eq_bij_betw_refl_prems)+

(* REPEAT FIRST' *)
(* comp = id for free vars *)
                         apply (rule inv_id_middle)
                          apply (rule f_prems)
                         apply (unfold eq_bij_betw_refl_def)[1]
                         apply (erule conjE)+
                         apply (rule trans)
                          apply (rule arg_cong[of _ _ "inv _"])
                          apply (drule imsupp_id_on_XX[OF suitable_prems f_prems, rotated -1])+
                          apply (erule conjE)+
                          apply (erule id_onD)
                          apply (rule imageI)
                          apply assumption
                         apply (drule imsupp_id_on_XX[OF suitable_prems f_prems, rotated -1])+
                         apply (erule conjE)+
                         apply (erule id_onD[OF id_on_inv, rotated])
                          apply (rule imageI)
                          apply assumption+
          (* copied from above, incremented imsupp_id_on index *)
                        apply (rule inv_id_middle)
                         apply (rule f_prems)
                        apply (unfold eq_bij_betw_refl_def)[1]
                        apply (erule conjE)+
                        apply (rule trans)
                         apply (rule arg_cong[of _ _ "inv _"])
                         apply (drule imsupp_id_on_XX[OF suitable_prems f_prems, rotated -1])+
                         apply (erule conjE)+
                         apply (erule id_onD)
                         apply (rule imageI)
                         apply assumption
                        apply (drule imsupp_id_on_XX[OF suitable_prems f_prems, rotated -1])+
                        apply (erule conjE)+
                        apply (erule id_onD[OF id_on_inv, rotated])
                         apply (rule imageI)
                         apply assumption+
          (* orelse *)
                       apply (rule refl)+
          (* orelse comp = id for bound position *)
                     apply (unfold eq_bij_betw_refl_def)[1]
                     apply (erule conjE)+
                     apply (rule inv_id_middle2)
                       apply (rule bij_comp f_prems pick_prems | assumption)+
                     apply (rule sym)
                     apply (erule eq_onD)
                     apply assumption
          (* copied from above *)
                    apply (unfold eq_bij_betw_refl_def)[1]
                    apply (erule conjE)+
                    apply (rule inv_id_middle2)
                      apply (rule bij_comp f_prems pick_prems | assumption)+
                    apply (rule sym)
                    apply (erule eq_onD)
                    apply assumption
          (* orelse *)
                   apply (rule refl)+
          (* end REPEAT_DETERM *)
         apply (rule T2_pre.rel_refl_strong)
          (* REPEAT_DETER FIRST' *)
             apply (rule refl)
          (* orelse recursive nonbinding set *)
            apply (rule relcomppI)
             apply (rule iffD2[OF fun_cong[OF fun_cong[OF Grp_UNIV_def]]])
             apply (rule refl)
            apply (unfold prod.case)
            apply (rule context_conjI)
          (* alpha_bij_tac *)
             apply (rule T1.alpha_bijs)
                       apply (erule eq_bij_betw_refl_prems)+
          (* repeat twice *)
               apply (rule ballI)
               apply (unfold T1.FVars_renames[OF f_prems])[1]
               apply (erule imageE)
               apply hypsubst
               apply (unfold eq_bij_betw_refl_def)[1]
               apply (erule conjE)+
               apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
               apply (erule conjE)+
               apply (drule UN_I)
                apply assumption
               apply (rotate_tac -1)
               apply (rule trans)
                apply (drule id_onD[rotated, OF imageI])
                 apply assumption
                apply assumption
               apply (rule sym)
               apply (erule id_onD[rotated, OF imageI])
               apply assumption
          (* copied from above *)
              apply (rule ballI)
              apply (unfold T1.FVars_renames[OF f_prems])[1]
              apply (erule imageE)
              apply hypsubst
              apply (unfold eq_bij_betw_refl_def)[1]
              apply (erule conjE)+
              apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
              apply (erule conjE)+
              apply (drule UN_I)
               apply assumption
              apply (rotate_tac -1)
              apply (rule trans)
               apply (drule id_onD[rotated, OF imageI])
                apply assumption
               apply assumption
              apply (rule sym)
              apply (erule id_onD[rotated, OF imageI])
              apply assumption
          (* end repeat twice *)
             apply (rule T1.alpha_refls)
          (* end alpha_bij_tac *)
            apply (rule trans)
             apply (rule arg_cong[of _ _ "PU1map' _ _ _"])
             apply (rule ext)
             apply (rule IHs[THEN conjunct1, symmetric])
                            apply (erule T1.set_subshapes)
                           apply (rule suitable_prems suitable'_prems f_prems imsupp_prems T1.alpha_refls)+
            apply (rule trans)
             apply (rule ext)
             apply (rule IHs[THEN conjunct1, symmetric])
                            apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems)+
                   apply (erule eq_bij_betw_refl_prems)+
               apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
               apply (erule conjE)+
               apply assumption
              apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
              apply (erule conjE)+
              apply assumption
             apply (rule T1.alpha_refls)
            apply (rule sym)
            apply (rule trans)
             apply (rule ext)
             apply (rule IHs[THEN conjunct1, symmetric])
                            apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems)+
                   apply (erule eq_bij_betw_refl_prems)+
               apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
               apply (erule conjE)+
               apply assumption
              apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
              apply (erule conjE)+
              apply assumption
             apply (rule T1.alpha_refls)
            apply (rule IHs[THEN conjunct2])
                           apply (subst T1.rename_comps)
                            apply (rule f_prems)+
                            apply (erule eq_bij_betw_refl_prems)+
                           apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule bij_comp supp_comp_bound infinite_UNIV f_prems | erule eq_bij_betw_refl_prems)+
                          apply (rule suitable_prems f_prems imsupp_prems)+
            apply (rule T1.alpha_syms)
            apply assumption

(* orelse recursive binding set *)
           apply (rule relcomppI)
            apply (unfold Grp_UNIV_def)[1]
            apply (rule refl)
           apply (unfold prod.case)
           apply (subst T1.rename_comps, (rule bij_comp supp_comp_bound infinite_UNIV pick_prems f_prems | erule eq_bij_betw_refl_prems)+)+
           apply (rule context_conjI)
          (* binding alpha_bij_tac *)
            apply (rule T1.alpha_bijs)
                      apply (rule bij_comp supp_comp_bound infinite_UNIV pick_prems f_prems | erule eq_bij_betw_refl_prems)+
          (* repeat twice *)
              apply (rule ballI)
              apply (rule case_split[of "_ \<in> _"])
               apply (unfold eq_bij_betw_refl_def)[1]
               apply (erule conjE)+
               apply (erule eq_onD)
               apply assumption
              apply (unfold comp_assoc[symmetric])[1]
              apply (rule trans)
               apply (rule comp_apply)
              apply (rule trans)
               apply (rule arg_cong[of _ _ "_ \<circ> _"])
               apply (rule id_onD[OF pick_id_ons(2)[OF suitable_prems(2)]]
            id_onD[OF pick_id_ons(1)[OF suitable_prems(1)]] id_onD[OF pick_id_ons(3)[OF suitable_prems(3)]]
            id_onD[OF pick_id_ons(4)[OF suitable_prems(4)]])
               apply (rule DiffI)
                apply (rule UN_I)
                 apply assumption+
              apply (drule DiffI[rotated])
               apply (rule UN_I)
                apply assumption
               apply assumption
              apply (rotate_tac -1)
              apply (rule trans[OF comp_apply])
              apply (rule trans)
               apply (unfold eq_bij_betw_refl_def)[1]
               apply (erule conjE)+
               apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
               apply (erule conjE)+
               apply (rotate_tac -1)
               apply (erule id_onD[rotated, OF imageI, of _ _ f1] id_onD[rotated, OF imageI, of _ _ f2])
               apply assumption
              apply (rule sym)
              apply (rule comp_middle)
               apply (unfold eq_bij_betw_refl_def)[1]
               apply (erule conjE)+
               apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
               apply (erule conjE)+
               apply (erule id_onD[rotated, OF imageI])
               apply assumption
              apply (rule id_onD[OF pick_id_on_images(1)[rotated -1, OF suitable_prems(1)]]
            id_onD[OF pick_id_on_images(2)[rotated -1, OF suitable_prems(2)]]
            id_onD[OF pick_id_on_images(3)[rotated -1, OF suitable_prems(3)]]
            id_onD[OF pick_id_on_images(4)[rotated -1, OF suitable_prems(4)]])
                  apply (rule f_prems)+
              apply (rule imageI)
              apply assumption
          (* copied from above *)
             apply (rule ballI)
             apply (rule case_split[of "_ \<in> _"])
              apply (unfold eq_bij_betw_refl_def)[1]
              apply (erule conjE)+
              apply (erule eq_onD)
              apply assumption
             apply (unfold comp_assoc[symmetric])[1]
             apply (rule trans)
              apply (rule comp_apply)
             apply (drule DiffI[rotated])
              apply (rule UN_I)
               apply assumption
              apply assumption
             apply (rotate_tac -1)
             apply (rule trans)
              apply (rule arg_cong[of _ _ "_ \<circ> _"])
              apply (erule id_onD[OF pick_id_ons'(1)[OF suitable_prems(1)]]
            id_onD[OF pick_id_ons'(2)[OF suitable_prems(1)]]
            id_onD[OF pick_id_ons'(3)[OF suitable_prems(2)]]
            id_onD[OF pick_id_ons'(4)[OF suitable_prems(3)]]
            id_onD[OF pick_id_ons'(5)[OF suitable_prems(3)]]
            id_onD[OF pick_id_ons'(6)[OF suitable_prems(4)]])
             apply (rule trans[OF comp_apply])
             apply (rule trans)
              apply (unfold eq_bij_betw_refl_def)[1]
              apply (erule conjE)+
              apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
              apply (erule conjE)+
              apply (rotate_tac -1)
              apply (erule id_onD[rotated, OF imageI, of _ _ f1] id_onD[rotated, OF imageI, of _ _ f2])
              apply assumption
             apply (rule sym)
             apply (rule comp_middle)
              apply (unfold eq_bij_betw_refl_def)[1]
              apply (erule conjE)+
              apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
              apply (erule conjE)+
              apply (erule id_onD[rotated, OF imageI])
              apply assumption
             apply (erule id_onD[OF pick_id_on_images'(1)[OF f_prems suitable_prems(1)] imageI]
            id_onD[OF pick_id_on_images'(2)[OF f_prems suitable_prems(1)] imageI]
            id_onD[OF pick_id_on_images'(3)[OF f_prems suitable_prems(2)] imageI]
            id_onD[OF pick_id_on_images'(4)[OF f_prems suitable_prems(3)] imageI]
            id_onD[OF pick_id_on_images'(5)[OF f_prems suitable_prems(3)] imageI]
            id_onD[OF pick_id_on_images'(6)[OF f_prems suitable_prems(4)] imageI])
          (* end repeat twice *)
            apply (rule T1.alpha_refls)
          (* end binding alpha_bij_tac *)
           apply (rule trans)
            apply (rule arg_cong[of _ _ "PU1map' _ _ _"])
            apply (rule ext)
            apply (rule IHs[THEN conjunct1, symmetric])
                           apply (erule T1.set_subshapes T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems imsupp_prems pick_prems T1.alpha_refls)+
           apply (subst T1.rename_comps)
                   apply (rule pick_prems f_prems)+
           apply (rule trans)
            apply (rule ext)
            apply (rule IHs[THEN conjunct1, symmetric])
                           apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems bij_comp pick_prems supp_comp_bound infinite_UNIV)+
                  apply (erule eq_bij_betw_refl_prems)+
              apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
              apply (erule conjE)+
              apply assumption
             apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
             apply (erule conjE)+
             apply assumption
            apply (rule T1.alpha_refls)
           apply (rule sym)
           apply (rule trans)
            apply (rule ext)
            apply (rule IHs[THEN conjunct1, symmetric])
                           apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems bij_comp supp_comp_bound pick_prems infinite_UNIV)+
                  apply (erule eq_bij_betw_refl_prems)+
              apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
              apply (erule conjE)+
              apply assumption
             apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
             apply (erule conjE)+
             apply assumption
            apply (rule T1.alpha_refls)
           apply (rule IHs[THEN conjunct2])
                          apply (subst T1.rename_comps)
                            apply (rule f_prems pick_prems bij_comp supp_comp_bound infinite_UNIV)+
                            apply (erule eq_bij_betw_refl_prems)+
                          apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule bij_comp supp_comp_bound infinite_UNIV f_prems pick_prems | erule eq_bij_betw_refl_prems)+
                         apply (rule suitable_prems f_prems imsupp_prems)+
           apply (rule T1.alpha_syms)
           apply (subst T1.rename_comps, (rule bij_comp supp_comp_bound infinite_UNIV pick_prems f_prems | erule eq_bij_betw_refl_prems)+)+
           apply assumption

(* orelse nonbinding recursive set, again *)
          apply (rule relcomppI)
           apply (rule iffD2[OF fun_cong[OF fun_cong[OF Grp_UNIV_def]]])
           apply (rule refl)
          apply (unfold prod.case)
          apply (rule context_conjI)
          (* alpha_bij_tac *)
           apply (rule T1.alpha_bijs)
                     apply (erule eq_bij_betw_refl_prems)+
          (* repeat twice *)
             apply (rule ballI)
             apply (unfold T1.FVars_renames[OF f_prems])[1]
             apply (erule imageE)
             apply hypsubst
             apply (unfold eq_bij_betw_refl_def)[1]
             apply (erule conjE)+
             apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
             apply (erule conjE)+
             apply (drule UN_I)
              apply assumption
             apply (rotate_tac -1)
             apply (rule trans)
              apply (drule id_onD[rotated, OF imageI])
               apply assumption
              apply assumption
             apply (rule sym)
             apply (erule id_onD[rotated, OF imageI])
             apply assumption
          (* copied from above *)
            apply (rule ballI)
            apply (unfold T1.FVars_renames[OF f_prems])[1]
            apply (erule imageE)
            apply hypsubst
            apply (unfold eq_bij_betw_refl_def)[1]
            apply (erule conjE)+
            apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
            apply (erule conjE)+
            apply (drule UN_I)
             apply assumption
            apply (rotate_tac -1)
            apply (rule trans)
             apply (drule id_onD[rotated, OF imageI])
              apply assumption
             apply assumption
            apply (rule sym)
            apply (erule id_onD[rotated, OF imageI])
            apply assumption
          (* end repeat twice *)
           apply (rule T1.alpha_refls)
          (* end alpha_bij_tac *)
          apply (rule trans)
           apply (rule arg_cong[of _ _ "PU1map' _ _ _"] arg_cong[of _ _ "PU2map' _ _ _"])
           apply (rule ext)
           apply (rule IHs[THEN conjunct1, symmetric])
                          apply (erule T1.set_subshapes)
                         apply (rule suitable_prems suitable'_prems f_prems imsupp_prems T1.alpha_refls)+
          apply (rule trans)
           apply (rule ext)
           apply (rule IHs[THEN conjunct1, symmetric])
                          apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems)+
                 apply (erule eq_bij_betw_refl_prems)+
             apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
             apply (erule conjE)+
             apply assumption
            apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
            apply (erule conjE)+
            apply assumption
           apply (rule T1.alpha_refls)
          apply (rule sym)
          apply (rule trans)
           apply (rule ext)
           apply (rule IHs[THEN conjunct1, symmetric])
                          apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems)+
                 apply (erule eq_bij_betw_refl_prems)+
             apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
             apply (erule conjE)+
             apply assumption
            apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
            apply (erule conjE)+
            apply assumption
           apply (rule T1.alpha_refls)
          apply (rule IHs[THEN conjunct2])
                         apply (subst T1.rename_comps)
                            apply (rule f_prems)+
                            apply (erule eq_bij_betw_refl_prems)+
                         apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule bij_comp supp_comp_bound infinite_UNIV f_prems | erule eq_bij_betw_refl_prems)+
                        apply (rule suitable_prems f_prems imsupp_prems)+
          apply (rule T1.alpha_syms)
          apply assumption

(* orelse binding recursive set, again *)
         apply (rule relcomppI)
          apply (unfold Grp_UNIV_def)[1]
          apply (rule refl)
         apply (unfold prod.case)
         apply (subst T1.rename_comps, (rule bij_comp supp_comp_bound infinite_UNIV pick_prems f_prems | erule eq_bij_betw_refl_prems)+)+
         apply (rule context_conjI)
          (* binding alpha_bij_tac *)
          apply (rule T1.alpha_bijs)
                    apply (rule bij_comp supp_comp_bound infinite_UNIV pick_prems f_prems | erule eq_bij_betw_refl_prems)+

(* nonbinding recursive occurence *)
            apply (rule ballI)
            apply (subst comp_def)+
            apply (unfold eq_bij_betw_refl_def)[1]
            apply (erule conjE)+
            apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
            apply (erule conjE)+
            apply (drule UN_I)
             apply assumption
            apply (rotate_tac -1)
            apply (rule trans)
             apply (erule id_onD[rotated, OF imageI, of _ _ f1] id_onD[rotated, OF imageI, of _ _ f2])
             apply assumption
            apply (rule sym)
            apply (erule id_onD[rotated, OF imageI])
            apply assumption
          (* copied from above, binding case *)
           apply (rule ballI)
           apply (rule case_split[of "_ \<in> _"])
            apply (unfold eq_bij_betw_refl_def)[1]
            apply (erule conjE)+
            apply (erule eq_onD)
            apply assumption
           apply (unfold comp_assoc[symmetric])[1]
           apply (rule trans)
            apply (rule comp_apply)
           apply (drule DiffI[rotated])
            apply (rule UN_I)
             apply assumption
            apply assumption
           apply (rotate_tac -1)
           apply (rule trans)
            apply (rule arg_cong[of _ _ "_ \<circ> _"])
            apply (erule id_onD[OF pick_id_ons'(1)[OF suitable_prems(1)]]
            id_onD[OF pick_id_ons'(2)[OF suitable_prems(1)]]
            id_onD[OF pick_id_ons'(3)[OF suitable_prems(2)]]
            id_onD[OF pick_id_ons'(4)[OF suitable_prems(3)]]
            id_onD[OF pick_id_ons'(5)[OF suitable_prems(3)]]
            id_onD[OF pick_id_ons'(6)[OF suitable_prems(4)]])
           apply (rule trans[OF comp_apply])
           apply (rule trans)
            apply (unfold eq_bij_betw_refl_def)[1]
            apply (erule conjE)+
            apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
            apply (erule conjE)+
            apply (rotate_tac -1)
            apply (erule id_onD[rotated, OF imageI, of _ _ f1] id_onD[rotated, OF imageI, of _ _ f2])
            apply assumption
           apply (rule sym)
           apply (rule comp_middle)
            apply (unfold eq_bij_betw_refl_def)[1]
            apply (erule conjE)+
            apply (drule imsupp_id_on_XX[OF suitable_prems f_prems])+
            apply (erule conjE)+
            apply (erule id_onD[rotated, OF imageI])
            apply assumption
           apply (erule id_onD[OF pick_id_on_images'(1)[OF f_prems suitable_prems(1)] imageI]
            id_onD[OF pick_id_on_images'(2)[OF f_prems suitable_prems(1)] imageI]
            id_onD[OF pick_id_on_images'(3)[OF f_prems suitable_prems(2)] imageI]
            id_onD[OF pick_id_on_images'(4)[OF f_prems suitable_prems(3)] imageI]
            id_onD[OF pick_id_on_images'(5)[OF f_prems suitable_prems(3)] imageI]
            id_onD[OF pick_id_on_images'(6)[OF f_prems suitable_prems(4)] imageI])
          (* end repeat twice *)
          apply (rule T1.alpha_refls)
          (* end binding alpha_bij_tac *)
         apply (rule trans)
          apply (rule arg_cong[of _ _ "PU1map' _ _ _"] arg_cong[of _ _ "PU2map' _ _ _"])
          apply (rule ext)
          apply (rule IHs[THEN conjunct1, symmetric])
                         apply (erule T1.set_subshapes T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems imsupp_prems pick_prems bij_id supp_id_bound T1.alpha_refls)+
         apply (subst T1.rename_comps)
                 apply (rule pick_prems f_prems bij_id supp_id_bound)+
         apply (unfold id_o o_id)
         apply (rule trans)
          apply (rule ext)
          apply (rule IHs[THEN conjunct1, symmetric])
                         apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems bij_comp pick_prems supp_comp_bound infinite_UNIV)+
                apply (erule eq_bij_betw_refl_prems)+
            apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
            apply (erule conjE)+
            apply assumption
           apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
           apply (erule conjE)+
           apply assumption
          apply (rule T1.alpha_refls)
         apply (rule sym)
         apply (rule trans)
          apply (rule ext)
          apply (rule IHs[THEN conjunct1, symmetric])
                         apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                            apply (rule suitable_prems suitable'_prems f_prems bij_comp supp_comp_bound pick_prems infinite_UNIV)+
                apply (erule eq_bij_betw_refl_prems)+
            apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
            apply (erule conjE)+
            apply assumption
           apply (unfold eq_bij_betw_refl_def Int_Un_distrib Un_empty)[1]
           apply (erule conjE)+
           apply assumption
          apply (rule T1.alpha_refls)
         apply (rule IHs[THEN conjunct2])
                        apply (subst T1.rename_comps)
                            apply (rule f_prems pick_prems bij_comp supp_comp_bound infinite_UNIV)+
                            apply (erule eq_bij_betw_refl_prems)+
                        apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                           apply (rule bij_comp supp_comp_bound infinite_UNIV f_prems pick_prems | erule eq_bij_betw_refl_prems)+
                       apply (rule suitable_prems f_prems imsupp_prems)+
         apply (rule T1.alpha_syms)
         apply (subst T1.rename_comps, (rule bij_comp supp_comp_bound infinite_UNIV pick_prems f_prems | erule eq_bij_betw_refl_prems)+)+
         apply assumption
          (**********************************************************************************************)
          (*    f picks t = f picks' t' *)
        apply (rule ext)
        apply (unfold f_T1_simp[OF suitable_prems] f_T2_simp[OF suitable_prems]
            f_T1_simp[OF suitable'_prems] f_T2_simp[OF suitable'_prems])
        subgoal for p
        proof -
          note exists_bij_betw2s = exists_bij_betw_def[OF _ _ pick_prems(5) pick'_prems(5) h_prems(1),
              of _ set5_T2_pre _ _ set5_T2_pre
              "\<lambda>x. map_T2_pre id id id id id id fst fst fst fst (
            map_T2_pre id id id id (pick3' x' p) (pick4' x' p)
              (\<lambda>t. (t, f_T1 pick1' pick2' pick3' pick4' t))
              (\<lambda>t. (rename_T1 (pick3' x' p) (pick4' x' p) t, f_T1 pick1' pick2' pick3' pick4' (rename_T1 (pick3' x' p) (pick4' x' p) t)))
              (\<lambda>t. (t, f_T2 pick1' pick2' pick3' pick4' t))
              (\<lambda>t. (rename_T2 (pick3' x' p) id t, f_T2 pick1' pick2' pick3' pick4' (rename_T2 (pick3' x' p) id t)))
              x)"
              "\<lambda>x. FVars_T21 (raw_T2_ctor x) \<union> PFVars_1 p \<union> avoiding_set1"
              _ _ "\<lambda>x'. map_T2_pre id id id id id id fst fst fst fst (
            map_T2_pre id id id id (pick3 x p) (pick4 x p)
              (\<lambda>t. (t, f_T1 pick1 pick2 pick3 pick4 t))
              (\<lambda>t. (rename_T1 (pick3 x p) (pick4 x p) t, f_T1 pick1 pick2 pick3 pick4 (rename_T1 (pick3 x p) (pick4 x p) t)))
              (\<lambda>t. (t, f_T2 pick1 pick2 pick3 pick4 t))
              (\<lambda>t. (rename_T2 (pick3 x p) id t, f_T2 pick1 pick2 pick3 pick4 (rename_T2 (pick3 x p) id t)))
              x')"
              ] exists_bij_betw_def[OF _ _ pick_prems(7) pick'_prems(7) h_prems(3),
              of _ set6_T2_pre _ _ set6_T2_pre
              "\<lambda>x. map_T2_pre id id id id id id fst fst fst fst (
            map_T2_pre id id id id (pick3' x' p) (pick4' x' p)
              (\<lambda>t. (t, f_T1 pick1' pick2' pick3' pick4' t))
              (\<lambda>t. (rename_T1 (pick3' x' p) (pick4' x' p) t, f_T1 pick1' pick2' pick3' pick4' (rename_T1 (pick3' x' p) (pick4' x' p) t)))
              (\<lambda>t. (t, f_T2 pick1' pick2' pick3' pick4' t))
              (\<lambda>t. (rename_T2 (pick3' x' p) id t, f_T2 pick1' pick2' pick3' pick4' (rename_T2 (pick3' x' p) id t)))
              x)"
              "\<lambda>x. FVars_T22 (raw_T2_ctor x) \<union> PFVars_2 p \<union> avoiding_set2"
              _ _ "\<lambda>x'. map_T2_pre id id id id id id fst fst fst fst (
            map_T2_pre id id id id (pick3 x p) (pick4 x p)
              (\<lambda>t. (t, f_T1 pick1 pick2 pick3 pick4 t))
              (\<lambda>t. (rename_T1 (pick3 x p) (pick4 x p) t, f_T1 pick1 pick2 pick3 pick4 (rename_T1 (pick3 x p) (pick4 x p) t)))
              (\<lambda>t. (t, f_T2 pick1 pick2 pick3 pick4 t))
              (\<lambda>t. (rename_T2 (pick3 x p) id t, f_T2 pick1 pick2 pick3 pick4 (rename_T2 (pick3 x p) id t)))
              x')"
              ]
          show ?thesis
            apply (rule exE[OF exists_bij_betw2s(1)])
                     apply (rule conjI)
                      apply (rule T1_pre.UNIV_cinfinite)
                     apply (rule card_of_Card_order)
                    apply (rule ordLeq_refl)
                    apply (rule card_of_Card_order)
                   apply (rule T2_pre.mr_rel_set(5)[rotated -1, OF mr_rel_prem])
                         apply (rule supp_id_bound bij_id h_prems)+
              (* bound_tac *)
                  apply (rule T1_pre.Un_bound)
                   apply (rule T2_pre.set_bd_UNIV)
                  apply (rule T1_pre.Un_bound)
                   apply (rule T1_pre.Un_bound)
                    apply (rule T1.card_of_FVars_bounds)
                   apply (rule small_PFVars_1 small_PFVars_2)
                  apply (rule small_avoiding_set1 small_avoiding_set2)
              (* end bound_tac *)
                 apply (subst T1.alpha_FVarss)
                  apply (rule T1.alpha_syms)
                  apply (rule alpha_ctor_picks[OF suitable'_prems])
                 apply (subst T2_pre.map_comp)
                          apply (rule supp_id_bound pick'_prems bij_id)+
                 apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
                 apply (subst T2_pre.set_map)
                        apply (rule supp_id_bound pick'_prems bij_id)+
                 apply (insert suitable'_prems)[1]
                 apply (unfold suitable_defs)
                 apply (erule allE conjE)+
                 apply assumption
                apply (subst T2_pre.map_comp)
                         apply (rule supp_id_bound pick'_prems bij_id)+
                apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
                apply (subst T2_pre.set_map)
                       apply (rule supp_id_bound pick'_prems bij_id)+
                apply (rule refl)
              (* bound_tac *)
               apply (rule T1_pre.Un_bound)
                apply (rule T2_pre.set_bd_UNIV)
               apply (rule T1_pre.Un_bound)
                apply (rule T1_pre.Un_bound)
                 apply (rule T1.card_of_FVars_bounds)
                apply (rule small_PFVars_1 small_PFVars_2)
               apply (rule small_avoiding_set1 small_avoiding_set2)
              (* end bound_tac *)
              apply (subst T1.alpha_FVarss)
               apply (rule T1.alpha_syms)
               apply (rule alpha_ctor_picks[OF suitable_prems])
              apply (subst T2_pre.map_comp)
                       apply (rule supp_id_bound pick_prems bij_id)+
              apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
              apply (subst T2_pre.set_map)
                     apply (rule supp_id_bound pick_prems bij_id)+
              apply (insert suitable_prems)[1]
              apply (unfold suitable_defs)
              apply (erule allE conjE)+
              apply assumption
             apply (subst T2_pre.map_comp)
                      apply (rule supp_id_bound pick_prems bij_id)+
             apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
             apply (subst T2_pre.set_map)
                    apply (rule supp_id_bound pick_prems bij_id)+
             apply (rule refl)
            apply (erule exE)
              (* again, index incremented *)
            apply (rule exE[OF exists_bij_betw2s(2)])
                     apply (rule conjI)
                      apply (rule T1_pre.UNIV_cinfinite)
                     apply (rule card_of_Card_order)
                    apply (rule ordLeq_refl)
                    apply (rule card_of_Card_order)
                   apply (rule T2_pre.mr_rel_set(6)[rotated -1, OF mr_rel_prem])
                         apply (rule supp_id_bound bij_id h_prems)+
              (* bound_tac *)
                  apply (rule T1_pre.Un_bound)
                   apply (rule T2_pre.set_bd_UNIV)
                  apply (rule T1_pre.Un_bound)
                   apply (rule T1_pre.Un_bound)
                    apply (rule T1.card_of_FVars_bounds)
                   apply (rule small_PFVars_1 small_PFVars_2)
                  apply (rule small_avoiding_set1 small_avoiding_set2)
              (* end bound_tac *)
                 apply (subst T1.alpha_FVarss)
                  apply (rule T1.alpha_syms)
                  apply (rule alpha_ctor_picks[OF suitable'_prems])
                 apply (subst T2_pre.map_comp)
                          apply (rule supp_id_bound pick'_prems bij_id)+
                 apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
                 apply (subst T2_pre.set_map)
                        apply (rule supp_id_bound pick'_prems bij_id)+
                 apply (insert suitable'_prems)[1]
                 apply (unfold suitable_defs)
                 apply (erule allE conjE)+
                 apply assumption
                apply (subst T2_pre.map_comp)
                         apply (rule supp_id_bound pick'_prems bij_id)+
                apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
                apply (subst T2_pre.set_map)
                       apply (rule supp_id_bound pick'_prems bij_id)+
                apply (rule refl)
              (* bound_tac *)
               apply (rule T1_pre.Un_bound)
                apply (rule T2_pre.set_bd_UNIV)
               apply (rule T1_pre.Un_bound)
                apply (rule T1_pre.Un_bound)
                 apply (rule T1.card_of_FVars_bounds)
                apply (rule small_PFVars_1 small_PFVars_2)
               apply (rule small_avoiding_set1 small_avoiding_set2)
              (* end bound_tac *)
              apply (subst T1.alpha_FVarss)
               apply (rule T1.alpha_syms)
               apply (rule alpha_ctor_picks[OF suitable_prems])
              apply (subst T2_pre.map_comp)
                       apply (rule supp_id_bound pick_prems bij_id)+
              apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
              apply (subst T2_pre.set_map)
                     apply (rule supp_id_bound pick_prems bij_id)+
              apply (insert suitable_prems)[1]
              apply (unfold suitable_defs)
              apply (erule allE conjE)+
              apply assumption
             apply (subst T2_pre.map_comp)
                      apply (rule supp_id_bound pick_prems bij_id)+
             apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric])
             apply (subst T2_pre.set_map)
                    apply (rule supp_id_bound pick_prems bij_id)+
             apply (rule refl)
            apply (erule exE)
            apply (rule U2ctor'_cong[rotated 16])
                                apply (((unfold eq_bij_betw_def)[1], (erule conjE)+, assumption)+)[4]
                                apply (subst T2_pre.set_map, (rule supp_id_bound bij_id pick_prems)+)+
                                apply (unfold eq_bij_betw_def)[1]
                                apply (erule conjE)+
                                apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                                apply (unfold image_id)
                                apply assumption
              (* repeated *)
                               apply (subst T2_pre.set_map, (rule supp_id_bound bij_id pick_prems)+)+
                               apply (unfold eq_bij_betw_def)[1]
                               apply (erule conjE)+
                               apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                               apply (unfold image_id)
                               apply assumption
              (* repeated *)
                              apply (subst T2_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                              apply (unfold eq_bij_betw_def)[1]
                              apply (erule conjE)+
                              apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                              apply (unfold image_id)
                              apply assumption
              (* repeated *)
                             apply (subst T2_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                             apply (unfold eq_bij_betw_def)[1]
                             apply (erule conjE)+
                             apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                             apply (unfold image_id)
                             apply assumption
                            defer
                            apply (erule eq_bij_betw_prems)+
              (* subset tac *)
                    apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                    apply (erule UnE)?
                     apply (erule imageE)
                     apply (drule iffD1[OF prod.inject])
                     apply (erule conjE)
                     apply hypsubst
                     apply (rule f_UFVars'[OF suitable_prems])
              (* repeated *)
                    apply (erule UnE)?
                    apply (erule imageE)
                    apply (drule iffD1[OF prod.inject])
                    apply (erule conjE)
                    apply hypsubst
                    apply (rule f_UFVars'[OF suitable_prems])
              (* end subset_tac *)
              (* copied from above *)
                   apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                   apply (erule UnE)?
                    apply (erule imageE)
                    apply (drule iffD1[OF prod.inject])
                    apply (erule conjE)
                    apply hypsubst
                    apply (rule f_UFVars'[OF suitable_prems])
              (* repeated *)
                   apply (erule UnE)?
                   apply (erule imageE)
                   apply (drule iffD1[OF prod.inject])
                   apply (erule conjE)
                   apply hypsubst
                   apply (rule f_UFVars'[OF suitable_prems])

(* copied from above *)
                  apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                  apply (erule UnE)?
                   apply (erule imageE)
                   apply (drule iffD1[OF prod.inject])
                   apply (erule conjE)
                   apply hypsubst
                   apply (rule f_UFVars'[OF suitable_prems])
              (* repeated *)
                  apply (erule UnE)?
                  apply (erule imageE)
                  apply (drule iffD1[OF prod.inject])
                  apply (erule conjE)
                  apply hypsubst
                  apply (rule f_UFVars'[OF suitable_prems])

(* copied from above *)
                 apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                 apply (erule UnE)?
                  apply (erule imageE)
                  apply (drule iffD1[OF prod.inject])
                  apply (erule conjE)
                  apply hypsubst
                  apply (rule f_UFVars'[OF suitable_prems])
              (* repeated *)
                 apply (erule UnE)?
                 apply (erule imageE)
                 apply (drule iffD1[OF prod.inject])
                 apply (erule conjE)
                 apply hypsubst
                 apply (rule f_UFVars'[OF suitable_prems])

(* copied from above *)
                apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
                apply (erule UnE)?
                 apply (erule imageE)
                 apply (drule iffD1[OF prod.inject])
                 apply (erule conjE)
                 apply hypsubst
                 apply (rule f_UFVars'[OF suitable'_prems])
              (* repeated *)
                apply (erule UnE)?
                apply (erule imageE)
                apply (drule iffD1[OF prod.inject])
                apply (erule conjE)
                apply hypsubst
                apply (rule f_UFVars'[OF suitable'_prems])

(* copied from above *)
               apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
               apply (erule UnE)?
                apply (erule imageE)
                apply (drule iffD1[OF prod.inject])
                apply (erule conjE)
                apply hypsubst
                apply (rule f_UFVars'[OF suitable'_prems])
              (* repeated *)
               apply (erule UnE)?
               apply (erule imageE)
               apply (drule iffD1[OF prod.inject])
               apply (erule conjE)
               apply hypsubst
               apply (rule f_UFVars'[OF suitable'_prems])

(* copied from above *)
              apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
              apply (erule UnE)?
               apply (erule imageE)
               apply (drule iffD1[OF prod.inject])
               apply (erule conjE)
               apply hypsubst
               apply (rule f_UFVars'[OF suitable'_prems])
              (* repeated *)
              apply (erule UnE)?
              apply (erule imageE)
              apply (drule iffD1[OF prod.inject])
              apply (erule conjE)
              apply hypsubst
              apply (rule f_UFVars'[OF suitable'_prems])

(* copied from above *)
             apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id pick_prems pick'_prems)+)+
             apply (erule UnE)?
              apply (erule imageE)
              apply (drule iffD1[OF prod.inject])
              apply (erule conjE)
              apply hypsubst
              apply (rule f_UFVars'[OF suitable'_prems])
              (* repeated *)
             apply (erule UnE)?
             apply (erule imageE)
             apply (drule iffD1[OF prod.inject])
             apply (erule conjE)
             apply hypsubst
             apply (rule f_UFVars'[OF suitable'_prems])

(* mr_rel_goal *)
            apply (rule iffD2[OF T2_pre.mr_rel_map(1)])
                          apply (rule supp_id_bound bij_id pick_prems supp_comp_bound supp_inv_bound infinite_UNIV bij_comp bij_imp_bij_inv | erule eq_bij_betw_prems)+
            apply (unfold id_o o_id inv_id Grp_UNIV_id OO_eq)
            apply (rule iffD2[OF T2_pre.mr_rel_map(3)])
                             apply (rule supp_id_bound bij_id pick_prems pick'_prems supp_comp_bound supp_inv_bound infinite_UNIV bij_comp bij_imp_bij_inv | erule eq_bij_betw_prems)+
            apply (unfold id_o o_id inv_id Grp_UNIV_id OO_eq conversep_eq)
            apply (rule T2_pre.mr_rel_mono_strong0)
                                prefer 15 (* 2 * (free + 2 * bound) + 1) *)
                                apply (rule prems)
                                apply (rule supp_id_bound bij_id h_prems supp_comp_bound supp_inv_bound infinite_UNIV bij_comp bij_imp_bij_inv pick_prems pick'_prems | erule eq_bij_betw_prems)+
              (* REPEAT FIRST' *)
              (* comp = id for free vars *)
                     apply (rule ballI)
                     apply (rule trans)
                      apply (rule id_apply)
                     apply (rule sym)
                     apply (rule trans)
                      apply (rule comp_apply)
                     apply (unfold eq_bij_betw_def)[1]
                     apply (erule conjE)+
                     apply (drule imsupp_id_on)+
                     apply (unfold T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable'_prems], symmetric]
                )[1]
                     apply (rule trans)
                      apply (rule arg_cong[of _ _ "inv _"])
                      apply (erule id_onD)
                      apply (rule UnI1)
                      apply (rule UnI1)
                      apply (erule T1.FVars_intros)
                     apply (erule id_onD[OF id_on_inv, rotated])
                      apply (rule UnI1)
                      apply (rule UnI1)
                      apply (subst (asm) T2_pre.mr_rel_set(1-2,5-6)[rotated -1, OF mr_rel_prem, unfolded image_id, symmetric])
                             apply (rule supp_id_bound bij_id h_prems)+
                      apply (erule T1.FVars_intros)
                     apply assumption
              (* copied from above *)
                    apply (rule ballI)
                    apply (rule trans)
                     apply (rule id_apply)
                    apply (rule sym)
                    apply (rule trans)
                     apply (rule comp_apply)
                    apply (unfold eq_bij_betw_def)[1]
                    apply (erule conjE)+
                    apply (drule imsupp_id_on)+
                    apply (unfold T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable'_prems], symmetric]
                )[1]
                    apply (rule trans)
                     apply (rule arg_cong[of _ _ "inv _"])
                     apply (erule id_onD)
                     apply (rule UnI1)
                     apply (rule UnI1)
                     apply (erule T1.FVars_intros)
                    apply (erule id_onD[OF id_on_inv, rotated])
                     apply (rule UnI1)
                     apply (rule UnI1)
                     apply (subst (asm) T2_pre.mr_rel_set(1-2,5-6)[rotated -1, OF mr_rel_prem, unfolded image_id, symmetric])
                            apply (rule supp_id_bound bij_id h_prems)+
                     apply (erule T1.FVars_intros)
                    apply assumption
              (* orelse *)
                   apply (rule ballI)
                   apply (rule refl)
              (* orelse *)
                  apply (rule ballI)
                  apply (rule ballI)
                  apply (rule impI)
                  apply assumption
              (* orelse comp = id on bound set *)
                 apply (rule ballI)
                 apply (unfold comp_assoc[symmetric])[1]
                 apply (subst o_inv_distrib[symmetric])
                   apply (erule eq_bij_betw_prems)
                  apply (rule pick'_prems)
                 apply (unfold comp_assoc)[1]
                 apply (rule sym)
                 apply (rule trans)
                  apply (rule comp_apply)
                 apply (rule iffD2[OF bij_imp_inv'])
                  apply (rule bij_comp pick'_prems | erule eq_bij_betw_prems)+
                 apply (rule trans[rotated])
                  apply (unfold eq_bij_betw_def)[1]
                  apply (erule conjE eq_onD)+
                  apply assumption
                 apply (unfold comp_def)[1]
                 apply (rule refl)
              (* copied from above *)
                apply (rule ballI)
                apply (unfold comp_assoc[symmetric])[1]
                apply (subst o_inv_distrib[symmetric])
                  apply (erule eq_bij_betw_prems)
                 apply (rule pick'_prems)
                apply (unfold comp_assoc)[1]
                apply (rule sym)
                apply (rule trans)
                 apply (rule comp_apply)
                apply (rule iffD2[OF bij_imp_inv'])
                 apply (rule bij_comp pick'_prems | erule eq_bij_betw_prems)+
                apply (rule trans[rotated])
                 apply (unfold eq_bij_betw_def)[1]
                 apply (erule conjE eq_onD)+
                 apply assumption
                apply (unfold comp_def)[1]
                apply (rule refl)
              (* orelse nonbinding rec set *)
               apply (rule ballI impI)+
               apply (rule relcomppI)
                apply (rule relcomppI)
                 apply (unfold Grp_UNIV_def)[1]
                 apply (rule refl)
                prefer 2
                apply (unfold Grp_UNIV_def conversep_def)[1]
                apply (rule refl)
               apply (unfold prod.case)
               apply (rule context_conjI)
              (* alpha_bij_tac *)
                apply (rule T1.alpha_bijs[rotated -1])
                          apply (assumption | rule T1.alpha_refls)
                         apply (erule eq_bij_betw_prems)+
              (* REPEAT_DETERM *)
                 apply (rule ballI)
                 apply (unfold eq_bij_betw_def T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable'_prems], symmetric]
                )[1]
                 apply (erule conjE)+
                 apply (drule imsupp_id_on)+
                 apply (rule trans)
                  apply (erule id_onD)
                  apply (rule UnI1)
                  apply (rule UnI1)
                  apply (erule T1.FVars_intros)
                  apply assumption
                 apply (rule sym)
                 apply (erule id_onD)
                 apply (rule UnI1)
                 apply (rule UnI1)
                 apply (erule T1.FVars_intros)
                 apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
                  apply assumption
                 apply (rule sym)
                 apply (rule T1.alpha_FVarss)
                 apply assumption
              (* copied from above *)
                apply (rule ballI)
                apply (unfold eq_bij_betw_def T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable'_prems], symmetric]
                )[1]
                apply (erule conjE)+
                apply (drule imsupp_id_on)+
                apply (rule trans)
                 apply (erule id_onD)
                 apply (rule UnI1)
                 apply (rule UnI1)
                 apply (erule T1.FVars_intros)
                 apply assumption
                apply (rule sym)
                apply (erule id_onD)
                apply (rule UnI1)
                apply (rule UnI1)
                apply (erule T1.FVars_intros)
                apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
                 apply assumption
                apply (rule sym)
                apply (rule T1.alpha_FVarss)
                apply assumption
              (* end alpha_bij_tac *)
               apply (rule trans)
                apply (rule ext)
                apply (unfold eq_bij_betw_def)[1]
                apply (erule conjE)+
                apply (rule IHs[THEN conjunct1, symmetric])
                               apply (erule T1.set_subshapes)
                              apply (rule suitable_prems)+
                      apply assumption+
                  apply (unfold Int_Un_distrib Un_empty)[1]
                  apply (erule conjE)+
                  apply assumption
                 apply (unfold Int_Un_distrib Un_empty)[1]
                 apply (erule conjE)+
                 apply assumption
                apply (rule T1.alpha_refls)
               apply (rule trans)
                apply (rule IHs[THEN conjunct2, OF _ suitable_prems suitable'_prems])
                       apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                          prefer 12 (* 5*nvars + 2 *)
                          apply (rule trans)
                           apply (rule ext)
                           apply (rule IHs[THEN conjunct1, OF _ suitable'_prems suitable'_prems])
                                apply (erule T1.set_subshapes)
                                prefer 8
                                apply (rule trans)
                                apply (rule fun_cong[OF PU1map'_alpha])
                                apply assumption
                                apply (rule arg_cong[of _ _ "PU1map' _ _ _"])
                                apply (rule IHs[THEN conjunct2, OF _ suitable'_prems suitable'_prems])
                                apply (erule T1.set_subshapes)
                                apply (rule supp_id_bound bij_id trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left])+
                                apply assumption
                                apply (erule eq_bij_betw_prems)+
                            apply (((unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1], (erule conjE)+, assumption)+)[4]
                        apply (erule eq_bij_betw_prems)+
                 apply (((unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1], (erule conjE)+, assumption)+)[2]
               apply (rule T1.alpha_transs)
                apply assumption
               apply (rule T1.alpha_bij_eqs[THEN iffD2])
                   apply (erule eq_bij_betw_prems)+
               apply (rule T1.alpha_syms)
               apply assumption

(* orelse binding rec set *)
              apply (rule ballI impI relcomppI)+
                apply (unfold Grp_UNIV_def)[1]
                apply (rule refl)
               prefer 2
               apply (unfold Grp_UNIV_def conversep_def)[1]
               apply (rule refl)
              apply (unfold prod.case)
              apply (rule context_conjI)
               apply (subst T1.rename_comps, (rule pick_prems pick'_prems | erule eq_bij_betw_prems)+)+
               apply (rule T1.alpha_transs)
                apply (rule T1.alpha_bijs[rotated -3]) (* -1 - nvars *)
              (* REPEAT_DETERM *)
                          apply (rule ballI)
                          apply (rule sym)
                          apply (rule case_split[of "_ \<in> _"])
                           apply (unfold eq_bij_betw_def)[1]
                           apply (erule conjE)+
                           apply (erule eq_onD)
                           apply assumption
                          apply (frule DiffI[rotated])
                           apply (rule UN_I)
                            apply assumption
                           apply assumption
                          apply (rotate_tac -1)
                          apply (insert h_id_ons)[1]
                          apply (unfold id_on_Un)
                          apply (erule conjE)+
                          apply (rule trans)
                           apply (rule id_on_comp3)
                             apply (erule id_onD[rotated])
                             apply assumption
                            apply (drule T1.FVars_renames[symmetric, OF h_prems, THEN iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]], OF imageI])
                            apply (drule T1.alpha_FVarss[THEN iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]], rotated])
                             apply assumption
                            apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<notin>)"], rotated])
                             apply (rule T2_pre.mr_rel_set(5,6)[rotated -1, OF iffD2[OF T2_pre.mr_rel_flip mr_rel_prem]])
                                apply (rule bij_id supp_id_bound h_prems supp_inv_bound bij_imp_bij_inv)+
                            apply (drule not_imageI[rotated])
                             apply (rule h_prems)
                            apply (unfold image_comp)[1]
                            apply (subst (asm) inv_o_simp2)
                             apply (rule h_prems)
                            apply (unfold image_id)
                            apply (drule DiffI[rotated])
                             apply (rule UN_I)
                              prefer 3
                              apply (rotate_tac -1)
                              apply (erule id_onD[OF pick_id_ons'(1)[OF suitable'_prems(1)]]
                id_onD[OF pick_id_ons'(2)[OF suitable'_prems(1)]]
                id_onD[OF pick_id_ons'(3)[OF suitable'_prems(2)]]
                id_onD[OF pick_id_ons'(4)[OF suitable'_prems(3)]]
                id_onD[OF pick_id_ons'(5)[OF suitable'_prems(3)]]
                id_onD[OF pick_id_ons'(6)[OF suitable'_prems(4)]]
                )
                             apply assumption
                            apply assumption
                           apply (unfold eq_bij_betw_def)[1]
                           apply (erule conjE)+
                           apply (drule imsupp_id_on)+
                           apply (erule id_onD)
                           apply (rule UnI1)
                           apply (rule UnI1)
                           apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                            apply (rule sym)
                            apply (rule T1.alpha_FVarss)
                            apply (rule alpha_ctor_picks[OF suitable'_prems])
                           apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                            apply (rule sym)
                            apply (rule T1.alpha_FVarss)
                            apply (rule alpha_T1_alpha_T2.intros[rotated -1])
                                apply (rule mr_rel_prem h_prems h_id_ons)+
                           apply (erule T1.FVars_intros)
                            apply assumption+
                          apply (rule sym)
                          apply (rule id_on_comp2)
                           apply (erule id_onD[OF pick_id_ons'(1)[OF suitable_prems(1)]]
                id_onD[OF pick_id_ons'(2)[OF suitable_prems(1)]]
                id_onD[OF pick_id_ons'(3)[OF suitable_prems(2)]]
                id_onD[OF pick_id_ons'(4)[OF suitable_prems(3)]]
                id_onD[OF pick_id_ons'(5)[OF suitable_prems(3)]]
                id_onD[OF pick_id_ons'(6)[OF suitable_prems(4)]])
                          apply (unfold eq_bij_betw_def)[1]
                          apply (erule conjE)+
                          apply (drule imsupp_id_on)+
                          apply (erule id_onD)
                          apply (rule UnI1)
                          apply (rule UnI1)
                          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                           apply (rule sym)
                           apply (rule T1.alpha_FVarss)
                           apply (rule alpha_ctor_picks[OF suitable_prems])
                          apply (erule T1.FVars_intros)
                           apply assumption+
              (* copied from above *)
                         apply (rule ballI)
                         apply (rule sym)
                         apply (rule case_split[of "_ \<in> _"])
                          apply (unfold eq_bij_betw_def)[1]
                          apply (erule conjE)+
                          apply (erule eq_onD)
                          apply assumption
                         apply (frule DiffI[rotated])
                          apply (rule UN_I)
                           apply assumption
                          apply assumption
                         apply (rotate_tac -1)
                         apply (insert h_id_ons)[1]
                         apply (unfold id_on_Un)
                         apply (erule conjE)+
                         apply (rule trans)
                          apply (rule id_on_comp3)
                            apply (erule id_onD[rotated])
                            apply assumption
                           apply (drule T1.FVars_renames[symmetric, OF h_prems, THEN iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]], OF imageI])
                           apply (drule T1.alpha_FVarss[THEN iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]], rotated])
                            apply assumption
                           apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<notin>)"], rotated])
                            apply (rule T2_pre.mr_rel_set(5,6)[rotated -1, OF iffD2[OF T2_pre.mr_rel_flip mr_rel_prem]])
                                apply (rule bij_id supp_id_bound h_prems supp_inv_bound bij_imp_bij_inv)+
                           apply (drule not_imageI[rotated])
                            apply (rule h_prems)
                           apply (unfold image_comp)[1]
                           apply (subst (asm) inv_o_simp2)
                            apply (rule h_prems)
                           apply (unfold image_id)
                           apply (drule DiffI[rotated])
                            apply (rule UN_I)
                             prefer 3
                             apply (rotate_tac -1)
                             apply (erule id_onD[OF pick_id_ons'(1)[OF suitable'_prems(1)]]
                id_onD[OF pick_id_ons'(2)[OF suitable'_prems(1)]]
                id_onD[OF pick_id_ons'(3)[OF suitable'_prems(2)]]
                id_onD[OF pick_id_ons'(4)[OF suitable'_prems(3)]]
                id_onD[OF pick_id_ons'(5)[OF suitable'_prems(3)]]
                id_onD[OF pick_id_ons'(6)[OF suitable'_prems(4)]]
                )
                            apply assumption
                           apply assumption
                          apply (unfold eq_bij_betw_def)[1]
                          apply (erule conjE)+
                          apply (drule imsupp_id_on)+
                          apply (erule id_onD)
                          apply (rule UnI1)
                          apply (rule UnI1)
                          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                           apply (rule sym)
                           apply (rule T1.alpha_FVarss)
                           apply (rule alpha_ctor_picks[OF suitable'_prems])
                          apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                           apply (rule sym)
                           apply (rule T1.alpha_FVarss)
                           apply (rule alpha_T1_alpha_T2.intros[rotated -1])
                                apply (rule mr_rel_prem h_prems h_id_ons)+
                          apply (erule T1.FVars_intros)
                           apply assumption+
                         apply (rule sym)
                         apply (rule id_on_comp2)
                          apply (erule id_onD[OF pick_id_ons'(1)[OF suitable_prems(1)]]
                id_onD[OF pick_id_ons'(2)[OF suitable_prems(1)]]
                id_onD[OF pick_id_ons'(3)[OF suitable_prems(2)]]
                id_onD[OF pick_id_ons'(4)[OF suitable_prems(3)]]
                id_onD[OF pick_id_ons'(5)[OF suitable_prems(3)]]
                id_onD[OF pick_id_ons'(6)[OF suitable_prems(4)]])
                         apply (unfold eq_bij_betw_def)[1]
                         apply (erule conjE)+
                         apply (drule imsupp_id_on)+
                         apply (erule id_onD)
                         apply (rule UnI1)
                         apply (rule UnI1)
                         apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                          apply (rule sym)
                          apply (rule T1.alpha_FVarss)
                          apply (rule alpha_ctor_picks[OF suitable_prems])
                         apply (erule T1.FVars_intros)
                          apply assumption+
              (* end repeat *)
                        apply (rule T1.alpha_refls)
                       apply (rule bij_comp pick_prems pick'_prems supp_comp_bound infinite_UNIV h_prems | erule eq_bij_betw_prems)+
               apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ alpha_T1]])
                apply (rule T1.rename_comps[symmetric])
                       apply (rule h_prems bij_comp pick'_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
               apply (rule T1.alpha_bij_eqs[THEN iffD2])
                   apply (rule h_prems bij_comp pick'_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
               apply assumption
              (* PUmap' ... (f ...) = PUmap' ... (f ...) *)
              apply (rule trans)
               apply (rule ext)
               apply (rule IHs[THEN conjunct1, symmetric])
                              apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                                apply (rule pick_prems suitable_prems | erule eq_bij_betw_prems)+
                 apply (unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1]
                 apply (erule conjE)+
                 apply assumption
                apply (unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1]
                apply (erule conjE)+
                apply assumption
               apply (rule T1.alpha_refls)
              apply (subst T1.rename_comps)
                      apply (rule pick_prems | erule eq_bij_betw_prems)+
              apply (rule trans)
               apply (rule IHs[THEN conjunct2])
                              apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                                apply (rule bij_comp pick_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
                             apply ((rule suitable_prems)+)[4]
                         apply (rule suitable'_prems)+
                     prefer 7 (* 3*nvars + 1 *)
                     apply (subst (asm) T1.rename_comps, (rule pick_prems pick'_prems | erule eq_bij_betw_prems)+)+
                     apply (rule T1.alpha_transs)
                      apply assumption
                     apply (rule T1.alpha_bij_eqs[THEN iffD2])
                         apply (rule bij_comp pick_prems pick'_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
                     apply (rule T1.alpha_syms)
                     apply assumption
                    prefer 7 (* 7*nvars + 1 *)
                    apply (subst T1.rename_comps[symmetric], (rule pick_prems pick'_prems | erule eq_bij_betw_prems)+)+
                    apply (rule trans)
                     apply (rule ext)
                     apply (rule IHs[THEN conjunct1])
                                apply (subst T1.rename_comps, (rule pick_prems pick'_prems h_prems)+)+
                                apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                                apply (rule h_prems suitable'_prems bij_comp pick_prems pick'_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
                       apply (unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1]
                       apply (erule conjE)+
                       apply assumption
                      apply (unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1]
                      apply (erule conjE)+
                      apply assumption
                     apply (rule T1.alpha_refls)
                    apply (rule trans)
                     apply (rule fun_cong[OF PU1map'_alpha])
                     apply (rule T1.alpha_bij_eqs[THEN iffD2])
                         apply (rule pick'_prems)+
                     apply assumption
                    apply (rule arg_cong[of _ _ "PU1map' _ _ _"])
                    apply (rule IHs[THEN conjunct2])
                                apply (subst T1.rename_comps, (rule pick_prems pick'_prems h_prems)+)+
                                apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                                apply (rule supp_id_bound bij_id h_prems suitable'_prems bij_comp pick_prems pick'_prems supp_comp_bound infinite_UNIV trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left] | erule eq_bij_betw_prems)+
                    apply (rule T1.alpha_bij_eqs[THEN iffD2])
                        apply (rule pick'_prems)+
                    apply assumption
                   apply (rule supp_id_bound bij_id trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left])+

(* orelse nonbinding rec set, again *)
             apply (rule ballI impI)+
             apply (rule relcomppI)
              apply (rule relcomppI)
               apply (unfold Grp_UNIV_def)[1]
               apply (rule refl)
              prefer 2
              apply (unfold Grp_UNIV_def conversep_def)[1]
              apply (rule refl)
             apply (unfold prod.case)
             apply (rule context_conjI)
              (* alpha_bij_tac *)
              apply (rule T1.alpha_bijs[rotated -1])
                        apply (assumption | rule T1.alpha_refls)
                       apply (erule eq_bij_betw_prems)+
              (* REPEAT_DETERM *)
               apply (rule ballI)
               apply (unfold eq_bij_betw_def T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable'_prems], symmetric]
                )[1]
               apply (erule conjE)+
               apply (drule imsupp_id_on)+
               apply (rule trans)
                apply (erule id_onD)
                apply (rule UnI1)
                apply (rule UnI1)
                apply (erule T1.FVars_intros)
                apply assumption
               apply (rule sym)
               apply (erule id_onD)
               apply (rule UnI1)
               apply (rule UnI1)
               apply (erule T1.FVars_intros)
               apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
                apply assumption
               apply (rule sym)
               apply (rule T1.alpha_FVarss)
               apply assumption
              (* copied from above *)
              apply (rule ballI)
              apply (unfold eq_bij_betw_def T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(1,3)[OF alpha_ctor_picks(1)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(2,4)[OF alpha_ctor_picks(2)[OF suitable'_prems], symmetric]
                )[1]
              apply (erule conjE)+
              apply (drule imsupp_id_on)+
              apply (rule trans)
               apply (erule id_onD)
               apply (rule UnI1)
               apply (rule UnI1)
               apply (erule T1.FVars_intros)
               apply assumption
              apply (rule sym)
              apply (erule id_onD)
              apply (rule UnI1)
              apply (rule UnI1)
              apply (erule T1.FVars_intros)
              apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
               apply assumption
              apply (rule sym)
              apply (rule T1.alpha_FVarss)
              apply assumption
              (* end alpha_bij_tac *)
             apply (rule trans)
              apply (rule ext)
              apply (unfold eq_bij_betw_def)[1]
              apply (erule conjE)+
              apply (rule IHs[THEN conjunct1, symmetric])
                             apply (erule T1.set_subshapes)
                            apply (rule suitable_prems)+
                    apply assumption+
                apply (unfold Int_Un_distrib Un_empty)[1]
                apply (erule conjE)+
                apply assumption
               apply (unfold Int_Un_distrib Un_empty)[1]
               apply (erule conjE)+
               apply assumption
              apply (rule T1.alpha_refls)
             apply (rule trans)
              apply (rule IHs[THEN conjunct2, OF _ suitable_prems suitable'_prems])
                     apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                        prefer 12 (* 5*nvars + 2 *)
                        apply (rule trans)
                         apply (rule ext)
                         apply (rule IHs[THEN conjunct1, OF _ suitable'_prems suitable'_prems])
                                apply (erule T1.set_subshapes)
                               prefer 8
                               apply (rule trans)
                                apply (rule fun_cong[OF PU2map'_alpha])
                                apply assumption
                               apply (rule arg_cong[of _ _ "PU2map' _ _ _"])
                               apply (rule IHs[THEN conjunct2, OF _ suitable'_prems suitable'_prems])
                                apply (erule T1.set_subshapes)
                                apply (rule supp_id_bound bij_id trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left])+
                               apply assumption
                              apply (erule eq_bij_betw_prems)+
                          apply (((unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1], (erule conjE)+, assumption)+)[4]
                      apply (erule eq_bij_betw_prems)+
               apply (((unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1], (erule conjE)+, assumption)+)[2]
             apply (rule T1.alpha_transs)
              apply assumption
             apply (rule T1.alpha_bij_eqs[THEN iffD2])
                 apply (erule eq_bij_betw_prems)+
             apply (rule T1.alpha_syms)
             apply assumption

(* orelse binding rec set, again *)
            apply (rule ballI impI relcomppI)+
              apply (unfold Grp_UNIV_def)[1]
              apply (rule refl)
             prefer 2
             apply (unfold Grp_UNIV_def conversep_def)[1]
             apply (rule refl)
            apply (unfold prod.case)
            apply (subst T1.rename_comps, (rule pick_prems pick'_prems bij_id supp_id_bound | erule eq_bij_betw_prems)+)+
            apply (unfold id_o o_id)
            apply (rule context_conjI)
             apply (rule T1.alpha_transs)
              apply (rule T1.alpha_bijs[rotated -3]) (* -1 - nvars *)
              (* REPEAT_DETERM *)
                        apply (rule ballI)
                        apply (unfold eq_bij_betw_def)[1]
                        apply (erule conjE)+
                        apply (subst (asm)
                T1.alpha_FVarss(1)[OF alpha_ctor_picks(1)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(2)[OF alpha_ctor_picks(2)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(3)[OF alpha_ctor_picks(1)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(4)[OF alpha_ctor_picks(2)[OF suitable_prems], symmetric]
                T1.alpha_FVarss(1)[OF alpha_ctor_picks(1)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(2)[OF alpha_ctor_picks(2)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(3)[OF alpha_ctor_picks(1)[OF suitable'_prems], symmetric]
                T1.alpha_FVarss(4)[OF alpha_ctor_picks(2)[OF suitable'_prems], symmetric])+
                        apply (drule imsupp_id_on)+
                        apply (erule id_on_eq)
                          apply assumption
                         apply (rule arg_cong2[OF _ refl, of _ _ "(\<union>)"])+
                         apply (rule T1.alpha_FVarss)
                         apply (rule alpha_T1_alpha_T2.intros[rotated -1])
                               apply (rule mr_rel_prem)
                              apply (rule h_prems h_id_ons)+
                        apply (rule UnI1)
                        apply (rule UnI1)
                        apply (erule T1.FVars_intros)
                        apply assumption
              (* orelse *)
                       apply (rule ballI)
                       apply (rule sym)
                       apply (rule case_split[of "_ \<in> _"])
                        apply (unfold eq_bij_betw_def)[1]
                        apply (erule conjE)+
                        apply (erule eq_onD)
                        apply assumption
                       apply (frule DiffI[rotated])
                        apply (rule UN_I)
                         apply assumption
                        apply assumption
                       apply (rotate_tac -1)
                       apply (insert h_id_ons)[1]
                       apply (unfold id_on_Un)
                       apply (erule conjE)+
                       apply (rule trans)
                        apply (rule id_on_comp3)
                          apply (erule id_onD[rotated])
                          apply assumption
            thm T1.FVars_renames[symmetric, THEN iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]], rotated -1, OF imageI] (*, THEN iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]], OF imageI]*)
                         apply (drule T1.FVars_renames[symmetric, THEN iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]], rotated -1, OF imageI])
                             prefer 5 (* 2*nvars + 1 *)
                             apply (drule T1.alpha_FVarss[THEN iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"]], rotated])
                              apply assumption
                             apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<notin>)"], rotated])
                              apply (rule T2_pre.mr_rel_set(5,6)[rotated -1, OF iffD2[OF T2_pre.mr_rel_flip mr_rel_prem]])
                                apply (rule bij_id supp_id_bound h_prems supp_inv_bound bij_imp_bij_inv)+
                             apply (drule not_imageI[rotated])
                              apply (rule h_prems)
                             apply (unfold image_comp)[1]
                             apply (subst (asm) inv_o_simp2)
                              apply (rule h_prems)
                             apply (unfold image_id)
                             apply (drule DiffI[rotated])
                              apply (erule UN_I[of _ _ _ FVars_T11, rotated] UN_I[of _ _ _ FVars_T12, rotated]
                UN_I[of _ _ _ FVars_T21, rotated] UN_I[of _ _ _ FVars_T22, rotated])
                              apply assumption
                             apply (rotate_tac -1)
                             apply (erule id_onD[OF pick_id_ons'(1)[OF suitable'_prems(1)]]
                id_onD[OF pick_id_ons'(2)[OF suitable'_prems(1)]]
                id_onD[OF pick_id_ons'(3)[OF suitable'_prems(2)]]
                id_onD[OF pick_id_ons'(4)[OF suitable'_prems(3)]]
                id_onD[OF pick_id_ons'(5)[OF suitable'_prems(3)]]
                id_onD[OF pick_id_ons'(6)[OF suitable'_prems(4)]]
                )
                            apply (rule h_prems bij_id supp_id_bound)+
                        apply (unfold eq_bij_betw_def)[1]
                        apply (erule conjE)+
                        apply (drule imsupp_id_on)+
                        apply (erule id_onD)
                        apply (rule UnI1)
                        apply (rule UnI1)
                        apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                         apply (rule sym)
                         apply (rule T1.alpha_FVarss)
                         apply (rule alpha_ctor_picks[OF suitable'_prems])
                        apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                         apply (rule sym)
                         apply (rule T1.alpha_FVarss)
                         apply (rule alpha_T1_alpha_T2.intros[rotated -1])
                               apply (rule mr_rel_prem h_prems h_id_ons)+
                        apply (erule T1.FVars_intros)
                         apply assumption+
                       apply (rule sym)
                       apply (rule id_on_comp2)
                        apply (erule id_onD[OF pick_id_ons'(1)[OF suitable_prems(1)]]
                id_onD[OF pick_id_ons'(2)[OF suitable_prems(1)]]
                id_onD[OF pick_id_ons'(3)[OF suitable_prems(2)]]
                id_onD[OF pick_id_ons'(4)[OF suitable_prems(3)]]
                id_onD[OF pick_id_ons'(5)[OF suitable_prems(3)]]
                id_onD[OF pick_id_ons'(6)[OF suitable_prems(4)]])
                       apply (unfold eq_bij_betw_def)[1]
                       apply (erule conjE)+
                       apply (drule imsupp_id_on)+
                       apply (erule id_onD)
                       apply (rule UnI1)
                       apply (rule UnI1)
                       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
                        apply (rule sym)
                        apply (rule T1.alpha_FVarss)
                        apply (rule alpha_ctor_picks[OF suitable_prems])
                       apply (erule T1.FVars_intros)
                        apply assumption+
                      apply (rule T1.alpha_refls)
                     apply (rule bij_comp pick_prems pick'_prems supp_comp_bound infinite_UNIV h_prems | erule eq_bij_betw_prems)+
             apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ alpha_T2]])
              apply (rule trans)
               apply (rule arg_cong3[of _ _ _ _ _ _ rename_T2])
                 prefer 4 (* 2*nvars + 2 *)
                 apply (rule T1.rename_comps[symmetric])
                        prefer 9 (* 4*nvars + 1*)
                        apply (rule refl)
                       prefer 9 (* 4*nvars + 1 *)
              (* refl orelse *) apply (rule o_id[symmetric])
                      apply (rule bij_id supp_id_bound h_prems bij_comp pick'_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
              apply (rule refl)
             apply (rule T1.alpha_bij_eqs[THEN iffD2])
                 apply (rule h_prems bij_comp pick'_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
             apply assumption
              (* PUmap' ... (f ...) = PUmap' ... (f ...) *)
            apply (rule trans)
             apply (rule ext)
             apply (rule IHs[THEN conjunct1, symmetric])
                            apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                               apply (rule bij_id supp_id_bound pick_prems suitable_prems | erule eq_bij_betw_prems)+
               apply (unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1]
               apply (erule conjE)+
               apply assumption
              apply (unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1]
              apply (erule conjE)+
              apply assumption
             apply (rule T1.alpha_refls)
            apply (subst T1.rename_comps)
                    apply (rule bij_id supp_id_bound pick_prems | erule eq_bij_betw_prems)+
            apply (rule trans)
             apply (rule IHs[THEN conjunct2])
                            apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                               apply (rule bij_id supp_id_bound bij_comp pick_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
                           apply ((rule suitable_prems)+)[4]
                       apply (rule suitable'_prems)+
                   prefer 7 (* 3*nvars + 1 *)
                   apply ((subst (asm) T1.rename_comps, (rule pick_prems pick'_prems | erule eq_bij_betw_prems)+)+)?
                   apply (rule T1.alpha_transs)
                    apply (unfold id_o o_id)[1]
                    apply assumption
                   apply (rule T1.alpha_bij_eqs[THEN iffD2])
                       apply (rule bij_comp pick_prems pick'_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
                   apply (rule T1.alpha_syms)
                   apply assumption
                  prefer 7 (* 7*nvars + 1 *)
                  apply (subst T1.rename_comps[symmetric] T1.rename_comps[symmetric, OF _ _ bij_id supp_id_bound, unfolded o_id], (rule pick_prems pick'_prems | erule eq_bij_betw_prems)+)+
                  apply (rule trans)
                   apply (rule ext)
                   apply (rule IHs[THEN conjunct1])
                                apply (subst T1.rename_comps, (rule bij_id supp_id_bound pick_prems pick'_prems h_prems)+)+
                                apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                                apply (rule bij_id supp_id_bound h_prems suitable'_prems bij_comp pick_prems pick'_prems supp_comp_bound infinite_UNIV | erule eq_bij_betw_prems)+
                     apply (unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1]
                     apply (erule conjE)+
                     apply assumption
                    apply (unfold eq_bij_betw_def Int_Un_distrib Un_empty)[1]
                    apply (erule conjE)+
                    apply assumption
                   apply (rule T1.alpha_refls)
                  apply (rule trans)
                   apply (rule fun_cong[OF PU2map'_alpha])
                   apply (rule T1.alpha_bij_eqs[THEN iffD2])
                       apply (rule bij_id supp_id_bound pick'_prems)+
                   apply assumption
                  apply (rule arg_cong[of _ _ "PU2map' _ _ _"])
                  apply (rule IHs[THEN conjunct2])
                                apply (subst T1.rename_comps, (rule bij_id supp_id_bound pick_prems pick'_prems h_prems)+)+
                                apply (erule T1.set_subshape_images[rotated -1, OF imageI])
                                apply (rule supp_id_bound bij_id h_prems suitable'_prems bij_comp pick_prems pick'_prems supp_comp_bound infinite_UNIV trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left] | erule eq_bij_betw_prems)+
                  apply (rule T1.alpha_bij_eqs[THEN iffD2])
                      apply (rule supp_id_bound bij_id pick'_prems)+
                  apply assumption
                 apply (rule supp_id_bound bij_id trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left])+
            done
        qed
        done
    qed
    done
  done

lemma exists_suitables:
  "\<exists>pick1. suitable11 pick1"
  "\<exists>pick2. suitable12 pick2"
  "\<exists>pick3. suitable21 pick3"
  "\<exists>pick4. suitable22 pick4"
     apply (unfold suitable_defs)
     apply (rule choice allI)+
     apply (rule exists_suitable_aux)
       apply (rule conjI)
        apply (rule T1_pre.UNIV_cinfinite)
       apply (rule card_of_Card_order)
      apply (rule ordLeq_refl)
      apply (rule card_of_Card_order)
     apply (rule T1_pre.Un_bound T1_pre.set_bd_UNIV ordLeq_ordLess_trans[OF card_of_diff]
      T1.card_of_FVars_bounds small_PFVars_1 small_PFVars_2 small_avoiding_set1 small_avoiding_set2
      )+
    (* copied from above *)
    apply (rule choice allI)+
    apply (rule exists_suitable_aux)
      apply (rule conjI)
       apply (rule T1_pre.UNIV_cinfinite)
      apply (rule card_of_Card_order)
     apply (rule ordLeq_refl)
     apply (rule card_of_Card_order)
    apply (rule T1_pre.Un_bound T1_pre.set_bd_UNIV ordLeq_ordLess_trans[OF card_of_diff]
      T1.card_of_FVars_bounds small_PFVars_1 small_PFVars_2 small_avoiding_set1 small_avoiding_set2
      )+
   apply (rule choice allI)+
   apply (rule exists_suitable_aux)
     apply (rule conjI)
      apply (rule T1_pre.UNIV_cinfinite)
     apply (rule card_of_Card_order)
    apply (rule ordLeq_refl)
    apply (rule card_of_Card_order)
   apply (rule T2_pre.Un_bound T2_pre.set_bd_UNIV ordLeq_ordLess_trans[OF card_of_diff]
      T1.card_of_FVars_bounds small_PFVars_1 small_PFVars_2 small_avoiding_set1 small_avoiding_set2
      )+
  apply (rule choice allI)+
  apply (rule exists_suitable_aux)
    apply (rule conjI)
     apply (rule T1_pre.UNIV_cinfinite)
    apply (rule card_of_Card_order)
   apply (rule ordLeq_refl)
   apply (rule card_of_Card_order)
  apply (rule T1_pre.Un_bound T2_pre.set_bd_UNIV ordLeq_ordLess_trans[OF card_of_diff]
      T1.card_of_FVars_bounds small_PFVars_1 small_PFVars_2 small_avoiding_set1 small_avoiding_set2
      )+
  done

lemma suitable_pick0s:
  "suitable11 pick1_0"
  "suitable12 pick2_0"
  "suitable21 pick3_0"
  "suitable22 pick4_0"
     apply (unfold pick1_0_def pick2_0_def pick3_0_def pick4_0_def)
     apply (rule someI_ex[OF exists_suitables(1)])
    apply (rule someI_ex[OF exists_suitables(2)])
   apply (rule someI_ex[OF exists_suitables(3)])
  apply (rule someI_ex[OF exists_suitables(4)])
  done

lemma f_alphas:
  assumes "suitable11 pick1" "suitable12 pick2" "suitable21 pick3" "suitable22 pick4"
    and "suitable11 pick1'" "suitable12 pick2'" "suitable21 pick3'" "suitable22 pick4'"
  shows "alpha_T1 t1 t1' \<Longrightarrow> f_T1 pick1 pick2 pick3 pick4 t1 = f_T1 pick1' pick2' pick3' pick4' t1'"
    "alpha_T2 t2 t2' \<Longrightarrow> f_T2 pick1 pick2 pick3 pick4 t2 = f_T2 pick1' pick2' pick3' pick4' t2'"
   apply -
   apply (rule f_swap_alpha[THEN conjunct1, THEN conjunct2] f_swap_alpha[THEN conjunct2, THEN conjunct2])
                  apply (rule assms bij_id supp_id_bound)+
      apply (unfold imsupp_id)
      apply (rule Int_empty_left)+
    apply (assumption | rule T1.alpha_refls)+
    (* copied *)
  apply (rule f_swap_alpha[THEN conjunct1, THEN conjunct2] f_swap_alpha[THEN conjunct2, THEN conjunct2])
                 apply (rule assms bij_id supp_id_bound)+
     apply (unfold imsupp_id)
     apply (rule Int_empty_left)+
   apply (assumption | rule T1.alpha_refls)+
  done

lemma f0_alphas:
  "alpha_T1 t1 t1' \<Longrightarrow> f0_T1 t1 = f0_T1 t1'"
  "alpha_T2 t2 t2' \<Longrightarrow> f0_T2 t2 = f0_T2 t2'"
   apply (unfold f0_T1_def f0_T2_def)
   apply (rule f_alphas)
           apply (rule suitable_pick0s)+
   apply assumption
    (* copied from above *)
  apply (rule f_alphas)
          apply (rule suitable_pick0s)+
  apply assumption
  done

lemmas f0_UFVars' = f_UFVars'[OF suitable_pick0s, unfolded f0_T1_def[symmetric] f0_T2_def[symmetric]]

thm trans[OF arg_cong2[OF imsupp_id refl, of "(\<inter>)"] Int_empty_left]

lemma f0_T1_ctor:
  assumes int_empty: "set5_T1_pre x \<inter> (PFVars_1 p \<union> avoiding_set1) = {}" "set6_T1_pre x \<inter> (PFVars_2 p \<union> avoiding_set2) = {}"
    and noclash: "noclash_T1 x"
  shows
    "f0_T1 (raw_T1_ctor x) p = U1ctor' (map_T1_pre id id id id id id (\<lambda>t. (t, f0_T1 t)) (\<lambda>t. (t, f0_T1 t)) (\<lambda>t. (t, f0_T2 t))  (\<lambda>t. (t, f0_T2 t)) x) p"
proof -
  let ?pick1_1 = "\<lambda>x' p'. if (x', p') = (x, p) then id else pick1_0 x' p'"
  let ?pick2_1 = "\<lambda>x' p'. if (x', p') = (x, p) then id else pick2_0 x' p'"

  have suitable_pick1s: "suitable11 ?pick1_1" "suitable12 ?pick2_1"
     apply (unfold suitable_defs)
     apply (rule allI)
     apply (rule allI)
     apply (insert suitable_pick0s(1))[1]
     apply (unfold suitable_defs)
     apply (erule allE conjE)+
     apply (rule conjI bij_if supp_if imsupp_if_empty image_if_empty | assumption)+
     apply (drule iffD1[OF prod.inject])
     apply (erule conjE)
     apply hypsubst
     apply (rule trans)
      apply (unfold Un_assoc)[1]
      apply (rule Int_Un_distrib)
     apply (unfold Un_empty T1.FVars_ctors)[1]
     apply (rule conjI)
      apply (insert noclash)[1]
      apply (unfold Int_Un_distrib Un_empty noclash_T1_def)[1]
      apply (erule conjE)+
      apply (rule conjI)+
          apply (assumption | rule Diff_disjoint int_empty)+
      (* copied from above *)
    apply (rule allI)
    apply (rule allI)
    apply (insert suitable_pick0s(2))[1]
    apply (unfold suitable_defs)
    apply (erule allE conjE)+
    apply (rule conjI bij_if supp_if imsupp_if_empty image_if_empty | assumption)+
    apply (drule iffD1[OF prod.inject])
    apply (erule conjE)
    apply hypsubst
    apply (rule trans)
     apply (unfold Un_assoc)[1]
     apply (rule Int_Un_distrib)
    apply (unfold Un_empty T1.FVars_ctors)[1]
    apply (rule conjI)
     apply (insert noclash)[1]
     apply (unfold Int_Un_distrib Un_empty noclash_T1_def)[1]
     apply (erule conjE)+
     apply (rule conjI)+
         apply (assumption | rule Diff_disjoint int_empty)+
    done

  show ?thesis
    apply (rule trans)
     apply (rule fun_cong[of _ _ p])
     apply (unfold f0_T1_def)[1]
     apply (rule f_alphas)
             apply (rule suitable_pick1s suitable_pick0s)+
     apply (rule T1.alpha_refls)+
    apply (rule trans)
     apply (rule f_T1_simp)
        apply (rule suitable_pick1s suitable_pick0s)+
    apply (unfold if_P[OF refl])
    apply (rule arg_cong2[OF _ refl, of _ _ U1ctor'])
    apply (rule T1_pre.map_cong)
                        apply (rule supp_id_bound bij_id refl)+
       apply (unfold prod.inject T1.rename_ids)
      (* REPEAT_DETERM *)
       apply (rule conjI[OF refl])
       apply (rule trans)
        apply (rule f_alphas)
                apply (rule suitable_pick0s suitable_pick1s[unfolded prod.inject])+
        apply (rule T1.alpha_refls)
       apply (unfold f0_T1_def)[1]
       apply (rule refl)
      (* copied from above *)
      apply (rule conjI[OF refl])
      apply (rule trans)
       apply (rule f_alphas)
               apply (rule suitable_pick0s suitable_pick1s[unfolded prod.inject])+
       apply (rule T1.alpha_refls)
      apply (unfold f0_T1_def)[1]
      apply (rule refl)
      (* copied from above *)
     apply (rule conjI[OF refl])
     apply (rule trans)
      apply (rule f_alphas)
              apply (rule suitable_pick0s suitable_pick1s[unfolded prod.inject])+
      apply (rule T1.alpha_refls)
     apply (unfold f0_T2_def)[1]
     apply (rule refl)
      (* copied from above *)
    apply (rule conjI[OF refl])
    apply (rule trans)
     apply (rule f_alphas)
             apply (rule suitable_pick0s suitable_pick1s[unfolded prod.inject])+
     apply (rule T1.alpha_refls)
    apply (unfold f0_T2_def)[1]
    apply (rule refl)
    done
qed

lemma f0_T2_ctor:
  assumes int_empty: "set5_T2_pre x \<inter> (PFVars_1 p \<union> avoiding_set1) = {}" "set6_T2_pre x \<inter> (PFVars_2 p \<union> avoiding_set2) = {}"
    and noclash: "noclash_T2 x"
  shows
    "f0_T2 (raw_T2_ctor x) p = U2ctor' (map_T2_pre id id id id id id (\<lambda>t. (t, f0_T1 t)) (\<lambda>t. (t, f0_T1 t)) (\<lambda>t. (t, f0_T2 t))  (\<lambda>t. (t, f0_T2 t)) x) p"
proof -
  let ?pick3_1 = "\<lambda>x' p'. if (x', p') = (x, p) then id else pick3_0 x' p'"
  let ?pick4_1 = "\<lambda>x' p'. if (x', p') = (x, p) then id else pick4_0 x' p'"

  have suitable_pick1s: "suitable21 ?pick3_1" "suitable22 ?pick4_1"
     apply (unfold suitable_defs)
     apply (rule allI)
     apply (rule allI)
     apply (insert suitable_pick0s(3))[1]
     apply (unfold suitable_defs)
     apply (erule allE conjE)+
     apply (rule conjI bij_if supp_if imsupp_if_empty image_if_empty | assumption)+
     apply (drule iffD1[OF prod.inject])
     apply (erule conjE)
     apply hypsubst
     apply (rule trans)
      apply (unfold Un_assoc)[1]
      apply (rule Int_Un_distrib)
     apply (unfold Un_empty T1.FVars_ctors)[1]
     apply (rule conjI)
      apply (insert noclash)[1]
      apply (unfold Int_Un_distrib Un_empty noclash_T2_def)[1]
      apply (erule conjE)+
      apply (rule conjI)+
          apply (assumption | rule Diff_disjoint int_empty)+
      (* copied from above *)
    apply (rule allI)
    apply (rule allI)
    apply (insert suitable_pick0s(4))[1]
    apply (unfold suitable_defs)
    apply (erule allE conjE)+
    apply (rule conjI bij_if supp_if imsupp_if_empty image_if_empty | assumption)+
    apply (drule iffD1[OF prod.inject])
    apply (erule conjE)
    apply hypsubst
    apply (rule trans)
     apply (unfold Un_assoc)[1]
     apply (rule Int_Un_distrib)
    apply (unfold Un_empty T1.FVars_ctors)[1]
    apply (rule conjI)
     apply (insert noclash)[1]
     apply (unfold Int_Un_distrib Un_empty noclash_T2_def)[1]
     apply (erule conjE)+
     apply (rule conjI)+
         apply (assumption | rule Diff_disjoint int_empty)+
    done

  show ?thesis
    apply (rule trans)
     apply (rule fun_cong[of _ _ p])
     apply (unfold f0_T2_def)[1]
     apply (rule f_alphas)
             apply (rule suitable_pick1s suitable_pick0s)+
     apply (rule T1.alpha_refls)+
    apply (rule trans)
     apply (rule f_T2_simp)
        apply (rule suitable_pick1s suitable_pick0s)+
    apply (unfold if_P[OF refl])
    apply (rule arg_cong2[OF _ refl, of _ _ U2ctor'])
    apply (rule T2_pre.map_cong)
                        apply (rule supp_id_bound bij_id refl)+
       apply (unfold prod.inject T1.rename_ids)
      (* REPEAT_DETERM *)
       apply (rule conjI[OF refl])
       apply (rule trans)
        apply (rule f_alphas)
                apply (rule suitable_pick0s suitable_pick1s[unfolded prod.inject])+
        apply (rule T1.alpha_refls)
       apply (unfold f0_T1_def)[1]
       apply (rule refl)
      (* copied from above *)
      apply (rule conjI[OF refl])
      apply (rule trans)
       apply (rule f_alphas)
               apply (rule suitable_pick0s suitable_pick1s[unfolded prod.inject])+
       apply (rule T1.alpha_refls)
      apply (unfold f0_T1_def)[1]
      apply (rule refl)
      (* copied from above *)
     apply (rule conjI[OF refl])
     apply (rule trans)
      apply (rule f_alphas)
              apply (rule suitable_pick0s suitable_pick1s[unfolded prod.inject])+
      apply (rule T1.alpha_refls)
     apply (unfold f0_T2_def)[1]
     apply (rule refl)
      (* copied from above *)
    apply (rule conjI[OF refl])
    apply (rule trans)
     apply (rule f_alphas)
             apply (rule suitable_pick0s suitable_pick1s[unfolded prod.inject])+
     apply (rule T1.alpha_refls)
    apply (unfold f0_T2_def)[1]
    apply (rule refl)
    done
qed

lemmas f0_swaps = conjunct1[OF f_swap_alpha[rotated -2, OF T1.alpha_refls suitable_pick0s suitable_pick0s], unfolded f0_T1_def[symmetric], THEN conjunct1]
  conjunct2[OF f_swap_alpha[rotated -2, OF T1.alpha_refls suitable_pick0s suitable_pick0s], unfolded f0_T2_def[symmetric], THEN conjunct1]

lemma nnoclash_noclashs:
  "nnoclash_T1 x = noclash_T1 (map_T1_pre id id id id id id rep_T1 rep_T1 rep_T2 rep_T2 x)"
  "nnoclash_T2 y = noclash_T2 (map_T2_pre id id id id id id rep_T1 rep_T1 rep_T2 rep_T2 y)"
   apply (unfold nnoclash_T1_def nnoclash_T2_def noclash_T1_def noclash_T2_def
      T1_pre_set_map_ids T2_pre_set_map_ids image_id
      )
   apply (unfold image_comp[unfolded comp_def] FFVars_T11_def[symmetric] FFVars_T12_def[symmetric]
      FFVars_T21_def[symmetric] FFVars_T22_def[symmetric]
      )
   apply (rule refl)+
  done


(**********************************************)
(*********** Final result lemmas **************)
(**********************************************)

lemma ff0_cctors:
  "set5_T1_pre x \<inter> (PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow> set6_T1_pre x \<inter> (PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow> nnoclash_T1 x \<Longrightarrow>
     ff0_T1 (T1_ctor x) p = U1ctor (map_T1_pre id id id id id id (\<lambda>t. (t, ff0_T1 t)) (\<lambda>t. (t, ff0_T1 t)) (\<lambda>t. (t, ff0_T2 t))  (\<lambda>t. (t, ff0_T2 t)) x) p"
  "set5_T2_pre y \<inter> (PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow> set6_T2_pre y \<inter> (PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow> nnoclash_T2 y \<Longrightarrow>
     ff0_T2 (T2_ctor y) p = U2ctor (map_T2_pre id id id id id id (\<lambda>t. (t, ff0_T1 t)) (\<lambda>t. (t, ff0_T1 t)) (\<lambda>t. (t, ff0_T2 t))  (\<lambda>t. (t, ff0_T2 t)) y) p"
   apply (unfold ff0_T1_def ff0_T2_def T1_ctor_def T2_ctor_def)
   apply (rule trans)
    apply (rule f0_alphas[THEN fun_cong])
    apply (rule T1.TT_Quotient_rep_abss)
   apply (rule trans)
    apply (rule f0_T1_ctor)
      apply (unfold T1_pre_set_map_ids T2_pre_set_map_ids)
      apply assumption+
    apply (rule nnoclash_noclashs[THEN iffD1])
    apply assumption
   apply (unfold U1ctor'_def)[1]
   apply (subst T1_pre.map_comp)
        apply (rule supp_id_bound bij_id)+
   apply (unfold comp_def map_prod_simp id_def)
   apply (unfold id_def[symmetric])
   apply (subst T1_pre.map_comp)
        apply (rule supp_id_bound bij_id)+
   apply (unfold comp_def map_prod_simp id_def)
   apply (unfold id_def[symmetric] T1.TT_Quotient_abs_reps)
   apply (rule refl)
    (* copied from above *)
  apply (rule trans)
   apply (rule f0_alphas[THEN fun_cong])
   apply (rule T1.TT_Quotient_rep_abss)
  apply (rule trans)
   apply (rule f0_T2_ctor)
     apply (unfold T1_pre_set_map_ids T2_pre_set_map_ids)
     apply assumption+
   apply (rule nnoclash_noclashs[THEN iffD1])
   apply assumption
  apply (unfold U2ctor'_def)[1]
  apply (subst T2_pre.map_comp)
       apply (rule supp_id_bound bij_id)+
  apply (unfold comp_def map_prod_simp id_def)
  apply (unfold id_def[symmetric])
  apply (subst T2_pre.map_comp)
       apply (rule supp_id_bound bij_id)+
  apply (unfold comp_def map_prod_simp id_def)
  apply (unfold id_def[symmetric] T1.TT_Quotient_abs_reps)
  apply (rule refl)
  done

lemma ff0_swaps:
  fixes f1::"'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
    and imsupp_prems: "imsupp f1 \<inter> avoiding_set1 = {}" "imsupp f2 \<inter> avoiding_set2 = {}"
  shows
    "ff0_T1 (rrename_T1 f1 f2 t1) p = U1map f1 f2 t1 (ff0_T1 t1 (Pmap (inv f1) (inv f2) p))"
    "ff0_T2 (rrename_T2 f1 f2 t2) p = U2map f1 f2 t2 (ff0_T2 t2 (Pmap (inv f1) (inv f2) p))"
   apply (unfold ff0_T1_def ff0_T2_def rrename_T1_def rrename_T2_def)
   apply (rule trans)
    apply (rule f0_alphas[THEN fun_cong])
    apply (rule T1.TT_Quotient_rep_abss)
   apply (rule trans)
    apply (rule f0_swaps)
         apply (rule assms)+
   apply (unfold PU1map'_def U1map'_def T1.TT_Quotient_abs_reps)[1]
   apply (rule refl)
    (* copied from above *)
  apply (rule trans)
   apply (rule f0_alphas[THEN fun_cong])
   apply (rule T1.TT_Quotient_rep_abss)
  apply (rule trans)
   apply (rule f0_swaps)
        apply (rule assms)+
  apply (unfold PU2map'_def U2map'_def T1.TT_Quotient_abs_reps)[1]
  apply (rule refl)
  done

lemmas ff0_UFVarss = f0_UFVars'(1)[of "rep_T1 _", unfolded U1FVars_1'_def T1.TT_Quotient_abs_reps ff0_T1_def[symmetric] FVars_def2s]
  f0_UFVars'(2)[of "rep_T1 _", unfolded U1FVars_2'_def T1.TT_Quotient_abs_reps ff0_T1_def[symmetric] FVars_def2s]
  f0_UFVars'(3)[of "rep_T2 _", unfolded U2FVars_1'_def T1.TT_Quotient_abs_reps ff0_T2_def[symmetric] FVars_def2s]
  f0_UFVars'(4)[of "rep_T2 _", unfolded U2FVars_2'_def T1.TT_Quotient_abs_reps ff0_T2_def[symmetric] FVars_def2s]


end