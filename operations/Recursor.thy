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

consts U1FVars_1 :: "('var, 'tyvar, 'a, 'b) T1 \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a, 'c) U1 \<Rightarrow> 'var set"
consts U1FVars_2 :: "('var, 'tyvar, 'a, 'b) T1 \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a, 'c) U1 \<Rightarrow> 'tyvar set"
consts U2FVars_1 :: "('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a, 'c) U2 \<Rightarrow> 'var set"
consts U2FVars_2 :: "('var, 'tyvar, 'a, 'b) T2 \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a, 'c) U2 \<Rightarrow> 'tyvar set"

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
and U1map_id0: "U1map id id t1 = id"
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
and U1FVars_subset_1: "set5_T1_pre y \<inter> (PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
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
and U2map_id0: "U2map id id t2 = id"
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
and U2FVars_subset_1: "set5_T2_pre y2 \<inter> (PFVars_1 p \<union> avoiding_set2) = {} \<Longrightarrow>
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

end