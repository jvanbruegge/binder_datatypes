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
    (rename_T1 (pick1 x p) (pick2 x p)) id (rename_T2 (pick1 x p) (pick2 x p)) x
  )) p
else undefined)"
| "f_T2 pick1 pick2 pick3 pick4 (raw_T2_ctor x) p = (if suitable11 pick1 \<and> suitable12 pick2 \<and> suitable21 pick3 \<and> suitable22 pick4 then
  U2ctor' (map_T2_pre id id id id id id
    (\<lambda>t. (t, f_T1 pick1 pick2 pick3 pick4 t)) (\<lambda>t. (t, f_T1 pick1 pick2 pick3 pick4 t))
    (\<lambda>t. (t, f_T2 pick1 pick2 pick3 pick4 t)) (\<lambda>t. (t, f_T2 pick1 pick2 pick3 pick4 t)) (
  map_T2_pre id id id id (pick3 x p) (pick4 x p) id
    (rename_T1 (pick3 x p) (pick4 x p)) id (rename_T2 (pick3 x p) (pick4 x p)) x
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
      (\<lambda>t. (rename_T2 (pick1 x p) (pick2 x p) t, f_T2 pick1 pick2 pick3 pick4 (rename_T2 (pick1 x p) (pick2 x p) t)))
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
      (\<lambda>t. (rename_T2 (pick3 x p) (pick4 x p) t, f_T2 pick1 pick2 pick3 pick4 (rename_T2 (pick3 x p) (pick4 x p) t)))
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

(* TODO: XXl and XXr *)

(**********************************************************************)
(*                               PROOFS                               *)
(**********************************************************************)

lemma pick_id_ons:
  "suitable11 pick1 \<Longrightarrow> id_on (\<Union>(FVars_T11 ` set8_T1_pre x) - set5_T1_pre x) (pick1 x p)"
  "suitable11 pick1 \<Longrightarrow> id_on (\<Union>(FVars_T21 ` set10_T1_pre x) - set5_T1_pre x) (pick1 x p)"
  "suitable12 pick2 \<Longrightarrow> id_on (\<Union>(FVars_T12 ` set8_T1_pre x) - set6_T1_pre x) (pick2 x p)"
  "suitable21 pick3 \<Longrightarrow> id_on (\<Union>(FVars_T11 ` set8_T2_pre y) - set5_T2_pre y) (pick3 y p)"
  "suitable21 pick3 \<Longrightarrow> id_on (\<Union>(FVars_T21 ` set10_T2_pre y) - set5_T2_pre y) (pick3 y p)"
  "suitable22 pick4 \<Longrightarrow> id_on (\<Union>(FVars_T12 ` set8_T2_pre y) - set6_T2_pre y) (pick4 y p)"
    apply (unfold suitable_defs Int_Un_distrib Un_empty Un_Diff Diff_idemp T1.FVars_ctors)

  (* ALLGOALS *)
    apply (erule allE conjE)+
    apply (rule imsupp_id_on)
  apply assumption
  (* copied from above*)
  apply (erule allE conjE)+
    apply (rule imsupp_id_on)
   apply assumption
   apply (erule allE conjE)+
    apply (rule imsupp_id_on)
  apply assumption
   apply (erule allE conjE)+
    apply (rule imsupp_id_on)
   apply assumption
   apply (erule allE conjE)+
    apply (rule imsupp_id_on)
   apply assumption
   apply (erule allE conjE)+
    apply (rule imsupp_id_on)
  apply assumption
  done

lemma pick_id_on_images:
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
  (* EVERY' (map ... pick_id_ons) *)
       apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ id_on], rotated])
        apply (erule pick_id_ons(1))
       apply (subst T1_pre.set_map T2_pre.set_map T1.FVars_renames image_set_diff[OF bij_is_inj] comp_def image_comp image_UN,
          ((rule supp_id_bound bij_id assms)+)?
       )+
       apply (rule refl)
  (* copied from above (incremented index) *)
       apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ id_on], rotated])
        apply (erule pick_id_ons(2))
       apply (subst T1_pre.set_map T2_pre.set_map T1.FVars_renames image_set_diff[OF bij_is_inj] comp_def image_comp image_UN,
          ((rule supp_id_bound bij_id assms)+)?
       )+
      apply (rule refl)
apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ id_on], rotated])
        apply (erule pick_id_ons(3))
       apply (subst T1_pre.set_map T2_pre.set_map T1.FVars_renames image_set_diff[OF bij_is_inj] comp_def image_comp image_UN,
          ((rule supp_id_bound bij_id assms)+)?
       )+
  apply (rule refl)
apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ id_on], rotated])
        apply (erule pick_id_ons(4))
       apply (subst T1_pre.set_map T2_pre.set_map T1.FVars_renames image_set_diff[OF bij_is_inj] comp_def image_comp image_UN,
          ((rule supp_id_bound bij_id assms)+)?
       )+
  apply (rule refl)
apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ id_on], rotated])
        apply (erule pick_id_ons(5))
       apply (subst T1_pre.set_map T2_pre.set_map T1.FVars_renames image_set_diff[OF bij_is_inj] comp_def image_comp image_UN,
          ((rule supp_id_bound bij_id assms)+)?
       )+
  apply (rule refl)
apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ id_on], rotated])
        apply (erule pick_id_ons(6))
       apply (subst T1_pre.set_map T2_pre.set_map T1.FVars_renames image_set_diff[OF bij_is_inj] comp_def image_comp image_UN,
          ((rule supp_id_bound bij_id assms)+)?
       )+
  apply (rule refl)
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

end