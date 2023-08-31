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
and Pmap_comp0: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (g2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  bij g1 \<Longrightarrow> |supp (g1::'var \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij g2 \<Longrightarrow> |supp (g2::'tyvar \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  Pmap (g1 \<circ> f1) (g2 \<circ> f2) = Pmap g1 g2 \<circ> Pmap f1 f2"
and Pmap_cong_id: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (g2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  (\<And>a. a \<in> PFVars_1 d \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>b. b \<in> PFVars_2 d \<Longrightarrow> f2 a = a) \<Longrightarrow>
  Pmap f1 f2 d = d"
and PFVars_Pmap_1: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (g2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  PFVars_1 (Pmap f1 f2 d) = f1 ` PFVars_1 d"
and PFVars_Pmap_2: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (g2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  PFVars_2 (Pmap f1 f2 d) = f2 ` PFVars_2 d"
and small_PFVars_1: "|PFVars_1 d| <o |UNIV::'var set|"
and small_PFVars_2: "|PFVars_2 d| <o |UNIV::'tyvar set|"
and small_avoiding_set1: "|avoiding_set1::'var set| <o |UNIV::'var set|"
and small_avoiding_set2: "|avoiding_set2::'tyvar set| <o |UNIV::'tyvar set|"
  (* model 1 axioms *)
and U1map_id0: "U1map id id (t1::('var, 'tyvar, 'a, 'b) T1) = id"
and U1map_comp0: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (g2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  bij g1 \<Longrightarrow> |supp (g1::'var \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij g2 \<Longrightarrow> |supp (g2::'tyvar \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U1map (g1 \<circ> f1) (g2 \<circ> f2) t1 = U1map g1 g2 t1 \<circ> U1map f1 f2 t1"
and U1map_cong_id: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (g2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  (\<And>a. a \<in> U1FVars_1 t1 u1 \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>b. b \<in> U1FVars_2 t1 u1 \<Longrightarrow> f2 a = a) \<Longrightarrow>
  U1map f1 f2 t1 u1 = u1"
and U1FVars_Umap_1: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (g2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U1FVars_1 (rrename_T1 f1 f2 t1) (U1map f1 f2 t1 u1) = f1 ` U1FVars_1 t1 u1"
and U1FVars_Umap_2: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (g2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U1FVars_2 (rrename_T1 f1 f2 t1) (U1map f1 f2 t1 u1) = f2 ` U1FVars_2 t1 u1"
and U1map_Uctor: "bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (g2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U1map f1 f2 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) (U1ctor y p)
= U1ctor (map_T1_pre f1 f2 id id f1 f2
    (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. U1map f1 f2 t (pu p)))
    (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. U1map f1 f2 t (pu p)))
    (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. U2map f1 f2 t (pu p)))
    (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. U2map f1 f2 t (pu p)))
 y) (Pmap f1 f2 p)"
and U1FVars_subset_1: "set5_T1_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T1_pre) \<inter> (PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T1_pre y \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FFVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set8_T1_pre y \<Longrightarrow> U1FVars_1 t (pu p) - set5_T1_pre y \<subseteq> FFVars_T11 t - set5_T1_pre y \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FFVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set10_T1_pre y \<Longrightarrow> U2FVars_1 t (pu p) - set5_T1_pre y \<subseteq> FFVars_T21 t - set5_T1_pre y \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  U1FVars_1 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) (U1ctor y p) \<subseteq> FFVars_T11 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> set1_T1_pre y \<union> PFVars_1 p"
and U1FVars_subset_2: "set6_T1_pre y \<inter> (PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T1_pre y \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FFVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set8_T1_pre y \<Longrightarrow> U1FVars_2 t (pu p) - set6_T1_pre y \<subseteq> FFVars_T12 t - set6_T1_pre y \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T1_pre y \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set10_T1_pre y \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  U1FVars_2 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) (U1ctor y p) \<subseteq> FFVars_T12 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> set2_T1_pre y \<union> PFVars_2 p"
  (* model 2 axioms *)
and U2map_id0: "U2map id id (t2::('var, 'tyvar, 'a, 'b) T2) = id"
and U2map_comp0: "bij f1 \<Longrightarrow> |supp (f1::'var \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (g2::'tyvar \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  bij g1 \<Longrightarrow> |supp (g1::'var \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij g2 \<Longrightarrow> |supp (g2::'tyvar \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U2map (g1 \<circ> f1) (g2 \<circ> f2) t2 = U2map g1 g2 t2 \<circ> U2map f1 f2 t2"
and U2map_cong_id: "bij f1 \<Longrightarrow> |supp (f1::'var \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (g2::'tyvar \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  (\<And>a. a \<in> U2FVars_1 t2 u2 \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>b. b \<in> U2FVars_2 t2 u2 \<Longrightarrow> f2 a = a) \<Longrightarrow>
  U2map f1 f2 t2 u2 = u2"
and U2FVars_Umap_1: "bij f1 \<Longrightarrow> |supp (f1::'var \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (g2::'tyvar \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U2FVars_1 (rrename_T2 f1 f2 t2) (U2map f1 f2 t2 u2) = f1 ` U2FVars_1 t2 u2"
and U2FVars_Umap_2: "bij f1 \<Longrightarrow> |supp (f1::'var \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (g2::'tyvar \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U2FVars_2 (rrename_T2 f1 f2 t2) (U2map f1 f2 t2 u2) = f2 ` U2FVars_2 t2 u2"
and U2map_Uctor: "bij f1 \<Longrightarrow> |supp (f1::'var \<Rightarrow> 'var)| <o |UNIV::'var set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (g2::'tyvar \<Rightarrow> 'tyvar)| <o |UNIV::'tyvar set| \<Longrightarrow>
  U2map f1 f2 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y2)) (U2ctor y2 p)
= U2ctor (map_T2_pre f1 f2 id id f1 f2
    (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. U1map f1 f2 t (pu p)))
    (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. U1map f1 f2 t (pu p)))
    (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. U2map f1 f2 t (pu p)))
    (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. U2map f1 f2 t (pu p)))
 y2) (Pmap f1 f2 p)"
and U2FVars_subset_1: "set5_T2_pre (y2::(_, _, 'a, 'b, _, _, _, _, _, _) T2_pre) \<inter> (PFVars_1 p \<union> avoiding_set2) = {} \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T2_pre y2 \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FFVars_T11 t \<union> PFVars_1 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set8_T2_pre y2 \<Longrightarrow> U1FVars_1 t (pu p) - set5_T2_pre y2 \<subseteq> FFVars_T11 t - set5_T2_pre y2 \<union> PFVars_1 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y2 \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FFVars_T21 t \<union> PFVars_1 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set10_T2_pre y2 \<Longrightarrow> U2FVars_1 t (pu p) - set5_T2_pre y2 \<subseteq> FFVars_T21 t - set5_T2_pre y2 \<union> PFVars_1 p \<union> avoiding_set2) \<Longrightarrow>
  U2FVars_1 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y2)) (U2ctor y2 p) \<subseteq> FFVars_T21 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y2)) \<union> set1_T2_pre y2 \<union> PFVars_1 p"
and U2FVars_subset_2: "set6_T2_pre y2 \<inter> (PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set7_T2_pre y2 \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FFVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set8_T2_pre y2 \<Longrightarrow> U1FVars_2 t (pu p) - set6_T2_pre y2 \<subseteq> FFVars_T12 t - set6_T2_pre y2 \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set9_T2_pre y2 \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. (t, pu) \<in> set10_T2_pre y2 \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  U2FVars_2 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y2)) (U2ctor y2 p) \<subseteq> FFVars_T22 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y2)) \<union> set2_T2_pre y2 \<union> PFVars_2 p"
print_theorems

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
    apply (unfold suitable11_def suitable12_def suitable21_def)
    apply ((erule allE conjE)+, assumption)+
  done

lemma suitable_supp_bound:
  "suitable11 pick1 \<Longrightarrow> |supp (pick1 x (p::('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}) P))| <o |UNIV::'var set|"
  "suitable12 pick2 \<Longrightarrow> |supp (pick2 x p)| <o |UNIV::'tyvar set|"
  "suitable21 pick3 \<Longrightarrow> |supp (pick3 x' p)| <o |UNIV::'var set|"
    apply (unfold suitable11_def suitable12_def suitable21_def)
    apply ((erule allE conjE)+, assumption)+
  done

function f_T1 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) U1"
  and f_T2 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2" where
  "f_T1 pick1 pick2 pick3 (raw_T1_ctor x) p = (if suitable11 pick1 \<and> suitable12 pick2 \<and> suitable21 pick3 then
  U1ctor' (map_T1_pre id id id id id id
    (\<lambda>t. (t, f_T1 pick1 pick2 pick3 t)) (\<lambda>t. (t, f_T1 pick1 pick2 pick3 t))
    (\<lambda>t. (t, f_T2 pick1 pick2 pick3 t)) (\<lambda>t. (t, f_T2 pick1 pick2 pick3 t)) (
  map_T1_pre id id id id (pick1 x p) (pick2 x p) id
    (rename_T1 (pick1 x p) (pick2 x p)) id (rename_T2 (pick1 x p) (pick2 x p)) x
  )) p
else undefined)"
| "f_T2 pick1 pick2 pick3 (raw_T2_ctor x) p = (if suitable11 pick1 \<and> suitable12 pick2 \<and> suitable21 pick3 then
  U2ctor' (map_T2_pre id id id id id id
    (\<lambda>t. (t, f_T1 pick1 pick2 pick3 t)) (\<lambda>t. (t, f_T1 pick1 pick2 pick3 t))
    (\<lambda>t. (t, f_T2 pick1 pick2 pick3 t)) (\<lambda>t. (t, f_T2 pick1 pick2 pick3 t)) (
  map_T2_pre id id id id (pick3 x p) id id
    (rename_T1 (pick3 x p) id) id (rename_T2 (pick3 x p) id) x
  )) p
else undefined)"
     apply pat_completeness
  by simp_all
termination
  apply (relation "inv_image {(x, y). case x of
    Inl t1 \<Rightarrow> (case y of Inl t1' \<Rightarrow> subshape_T1_T1 t1 t1' | Inr t2 \<Rightarrow> subshape_T1_T2 t1 t2)
  | Inr t2 \<Rightarrow> (case y of Inl t1 \<Rightarrow> subshape_T2_T1 t2 t1 | Inr t2' \<Rightarrow> subshape_T2_T2 t2 t2')
 } (map_sum (fst \<circ> snd \<circ> snd \<circ> snd) (fst \<circ> snd \<circ> snd \<circ> snd))")
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

lemma f_T1_simp: "suitable11 pick1 \<Longrightarrow> suitable12 pick2 \<Longrightarrow> suitable21 pick3 \<Longrightarrow>
  f_T1 pick1 pick2 pick3 (raw_T1_ctor x) p =
    U1ctor' (map_T1_pre id id id id (pick1 x p) (pick2 x p)
      (\<lambda>t. (t, f_T1 pick1 pick2 pick3 t))
      (\<lambda>t. (rename_T1 (pick1 x p) (pick2 x p) t, f_T1 pick1 pick2 pick3 (rename_T1 (pick1 x p) (pick2 x p) t)))
      (\<lambda>t. (t, f_T2 pick1 pick2 pick3 t))
      (\<lambda>t. (rename_T2 (pick1 x p) (pick2 x p) t, f_T2 pick1 pick2 pick3 (rename_T2 (pick1 x p) (pick2 x p) t)))
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
lemma f_T2_simp: "suitable11 pick1 \<Longrightarrow> suitable12 pick2 \<Longrightarrow> suitable21 pick3 \<Longrightarrow>
  f_T2 pick1 pick2 pick3 (raw_T2_ctor x) p =
    U2ctor' (map_T2_pre id id id id (pick3 x p) id
      (\<lambda>t. (t, f_T1 pick1 pick2 pick3 t))
      (\<lambda>t. (rename_T1 (pick3 x p) id t, f_T1 pick1 pick2 pick3 (rename_T1 (pick3 x p) id t)))
      (\<lambda>t. (t, f_T2 pick1 pick2 pick3 t))
      (\<lambda>t. (rename_T2 (pick3 x p) id t, f_T2 pick1 pick2 pick3 (rename_T2 (pick3 x p) id t)))
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

definition "f0_T1 \<equiv> f_T1 pick1_0 pick2_0 pick3_0"
definition "f0_T2 \<equiv> f_T2 pick1_0 pick2_0 pick3_0"

abbreviation "rep_T1 \<equiv> quot_type.rep Rep_T1"
abbreviation "rep_T2 \<equiv> quot_type.rep Rep_T2"

definition "ff0_T1 t \<equiv> f0_T1 (rep_T1 t)"
definition "ff0_T2 t \<equiv> f0_T2 (rep_T2 t)"

end