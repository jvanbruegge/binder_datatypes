theory Least_Fixpoint
  imports "./Composition" "Binders.MRBNF_FP"
begin

typ "('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k) T1_pre"
typ "('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k) T2_pre"
(*
'a, 'b free
'c passive free
'd passive live
'e, 'f bound
'g bound free
'h, 'i, 'j, 'k live
 *)

(************* DEFINITIONS *****************)

datatype ('a::"{var_T1_pre,var_T2_pre}", 'b::"{var_T1_pre,var_T2_pre}", 'c::"{var_T1_pre,var_T2_pre}", 'd) raw_T1 =
  raw_T1_ctor "('a, 'b, 'c, 'd, 'a, 'b, 'a,
    ('a, 'b, 'c, 'd) raw_T1, ('a, 'b, 'c, 'd) raw_T1,
    ('a, 'b, 'c, 'd) raw_T2, ('a, 'b, 'c, 'd) raw_T2
  ) T1_pre"
  and ('a, 'b, 'c, 'd) raw_T2 =
  raw_T2_ctor "('a, 'b, 'c, 'd, 'a, 'b, 'a,
    ('a, 'b, 'c, 'd) raw_T1, ('a, 'b, 'c, 'd) raw_T1,
    ('a, 'b, 'c, 'd) raw_T2, ('a, 'b, 'c, 'd) raw_T2
  ) T2_pre"

primrec permute_raw_T1 :: "('a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a) \<Rightarrow> ('b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b)
  \<Rightarrow> ('a, 'b, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1 \<Rightarrow> ('a, 'b, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
  and permute_raw_T2 :: "('a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a) \<Rightarrow> ('b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b)
  \<Rightarrow> ('a, 'b, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2 \<Rightarrow> ('a, 'b, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2" where
  "permute_raw_T1 f1 f2 (raw_T1_ctor x) = raw_T1_ctor (map_T1_pre f1 f2 id id f1 f2 f1 id id id id (
  map_T1_pre id id id id id id id (permute_raw_T1 f1 f2) (permute_raw_T1 f1 f2) (permute_raw_T2 f1 f2) (permute_raw_T2 f1 f2) x
))"
| "permute_raw_T2 f1 f2 (raw_T2_ctor x) = raw_T2_ctor (map_T2_pre f1 f2 id id f1 f2 f1 id id id id (
  map_T2_pre id id id id id id id (permute_raw_T1 f1 f2) (permute_raw_T1 f1 f2) (permute_raw_T2 f1 f2) (permute_raw_T2 f1 f2) x
))"
  (* we have to define the permute function with two maps because
we need to separate recursion from other actions for primrec *)

(* we can derive the desired simplification rule using composition of map *)
lemma permute_raw_simps:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows
    "permute_raw_T1 f1 f2 (raw_T1_ctor x) = raw_T1_ctor (map_T1_pre f1 f2 id id f1 f2 f1
    (permute_raw_T1 f1 f2) (permute_raw_T1 f1 f2) (permute_raw_T2 f1 f2) (permute_raw_T2 f1 f2) x)"
    "permute_raw_T2 f1 f2 (raw_T2_ctor x2) = raw_T2_ctor (map_T2_pre f1 f2 id id f1 f2 f1
    (permute_raw_T1 f1 f2) (permute_raw_T1 f1 f2) (permute_raw_T2 f1 f2) (permute_raw_T2 f1 f2) x2)"
   apply (rule trans)
    apply (rule permute_raw_T1.simps)
   apply (subst T1_pre.map_comp)
            apply (rule supp_id_bound bij_id assms)+
   apply (unfold id_o o_id)
   apply (rule refl)
    (* repeated *)
  apply (rule trans)
   apply (rule permute_raw_T2.simps)
  apply (subst T2_pre.map_comp)
           apply (rule supp_id_bound bij_id assms)+
  apply (unfold id_o o_id)
  apply (rule refl)
  done

(* binding_rel: [([0], [1,3]), ([], [1])] *)
inductive
  free1_raw_T1 :: "'a \<Rightarrow> ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1 \<Rightarrow> bool"
  and free1_raw_T2 :: "'a \<Rightarrow> ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2 \<Rightarrow> bool"
  where
    "a \<in> set1_T1_pre x \<Longrightarrow> free1_raw_T1 a (raw_T1_ctor x)"
  | "a \<in> set7_T1_pre x \<Longrightarrow> a \<notin> set5_T1_pre x \<Longrightarrow> free1_raw_T1 a (raw_T1_ctor x)"
  | "z \<in> set8_T1_pre x \<Longrightarrow> free1_raw_T1 a z \<Longrightarrow> free1_raw_T1 a (raw_T1_ctor x)"
  | "z \<in> set9_T1_pre x \<Longrightarrow> free1_raw_T1 a z \<Longrightarrow> a \<notin> set5_T1_pre x \<Longrightarrow> free1_raw_T1 a (raw_T1_ctor x)"
  | "z \<in> set10_T1_pre x \<Longrightarrow> free1_raw_T2 a z \<Longrightarrow> free1_raw_T1 a (raw_T1_ctor x)"
  | "z \<in> set11_T1_pre x \<Longrightarrow> free1_raw_T2 a z \<Longrightarrow> a \<notin> set5_T1_pre x \<Longrightarrow> free1_raw_T1 a (raw_T1_ctor x)"
  | "a \<in> set1_T2_pre x2 \<Longrightarrow> free1_raw_T2 a (raw_T2_ctor x2)"
  | "a \<in> set7_T2_pre x2 \<Longrightarrow> a \<notin> set5_T2_pre x2 \<Longrightarrow> free1_raw_T2 a (raw_T2_ctor x2)"
  | "z \<in> set8_T2_pre x2 \<Longrightarrow> free1_raw_T1 a z \<Longrightarrow> free1_raw_T2 a (raw_T2_ctor x2)"
  | "z \<in> set9_T2_pre x2 \<Longrightarrow> free1_raw_T1 a z \<Longrightarrow> a \<notin> set5_T2_pre x2 \<Longrightarrow> free1_raw_T2 a (raw_T2_ctor x2)"
  | "z \<in> set10_T2_pre x2 \<Longrightarrow> free1_raw_T2 a z \<Longrightarrow> free1_raw_T2 a (raw_T2_ctor x2)"
  | "z \<in> set11_T2_pre x2 \<Longrightarrow> free1_raw_T2 a z \<Longrightarrow> a \<notin> set5_T2_pre x2 \<Longrightarrow> free1_raw_T2 a (raw_T2_ctor x2)"

inductive
  free2_raw_T1 :: "'b \<Rightarrow> ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1 \<Rightarrow> bool"
  and free2_raw_T2 :: "'b \<Rightarrow> ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2 \<Rightarrow> bool"
  where
    "a \<in> set2_T1_pre x \<Longrightarrow> free2_raw_T1 a (raw_T1_ctor x)"
  | "z \<in> set8_T1_pre x \<Longrightarrow> free2_raw_T1 a z \<Longrightarrow> free2_raw_T1 a (raw_T1_ctor x)"
  | "z \<in> set9_T1_pre x \<Longrightarrow> free2_raw_T1 a z \<Longrightarrow> a \<notin> set6_T1_pre x \<Longrightarrow> free2_raw_T1 a (raw_T1_ctor x)"
  | "z \<in> set10_T1_pre x \<Longrightarrow> free2_raw_T2 a z \<Longrightarrow> free2_raw_T1 a (raw_T1_ctor x)"
  | "z \<in> set11_T1_pre x \<Longrightarrow> free2_raw_T2 a z \<Longrightarrow> free2_raw_T1 a (raw_T1_ctor x)"
  | "a \<in> set2_T2_pre x2 \<Longrightarrow> free2_raw_T2 a (raw_T2_ctor x2)"
  | "z \<in> set8_T2_pre x2 \<Longrightarrow> free2_raw_T1 a z \<Longrightarrow> free2_raw_T2 a (raw_T2_ctor x2)"
  | "z \<in> set9_T2_pre x2 \<Longrightarrow> free2_raw_T1 a z \<Longrightarrow> a \<notin> set6_T2_pre x2 \<Longrightarrow> free2_raw_T2 a (raw_T2_ctor x2)"
  | "z \<in> set10_T2_pre x2 \<Longrightarrow> free2_raw_T2 a z \<Longrightarrow> free2_raw_T2 a (raw_T2_ctor x2)"
  | "z \<in> set11_T2_pre x2 \<Longrightarrow> free2_raw_T2 a z \<Longrightarrow> free2_raw_T2 a (raw_T2_ctor x2)"

definition FVars_raw_T11 :: "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1 \<Rightarrow> 'a set"
  where "FVars_raw_T11 x \<equiv> { a. free1_raw_T1 a x }"
definition FVars_raw_T12 :: "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1 \<Rightarrow> 'b set"
  where "FVars_raw_T12 x \<equiv> { a. free2_raw_T1 a x }"
definition FVars_raw_T21 :: "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2 \<Rightarrow> 'a set"
  where "FVars_raw_T21 x \<equiv> { a. free1_raw_T2 a x }"
definition FVars_raw_T22 :: "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2 \<Rightarrow> 'b set"
  where "FVars_raw_T22 x \<equiv> { a. free2_raw_T2 a x }"

lemmas FVars_raw_defs = FVars_raw_T11_def FVars_raw_T12_def FVars_raw_T21_def FVars_raw_T22_def

coinductive alpha_T1 :: "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1 \<Rightarrow> ('a, 'b, 'c, 'd) raw_T1 \<Rightarrow> bool"
and alpha_T2 :: "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2 \<Rightarrow> ('a, 'b, 'c, 'd) raw_T2 \<Rightarrow> bool"
where
  "\<lbrakk> bij f1 ; |supp f1| <o |UNIV::'a set| ; bij f2 ; |supp f2| <o |UNIV::'b set| ;
  id_on ((set7_T1_pre x - set5_T1_pre x) \<union> (\<Union>(FVars_raw_T11 ` set9_T1_pre x) - set5_T1_pre x) \<union> (\<Union>(FVars_raw_T21 ` set11_T1_pre x) - set5_T1_pre x)) f1 ;
  id_on (\<Union>(FVars_raw_T12 ` set9_T1_pre x) - set6_T1_pre x) f2 ;
  mr_rel_T1_pre id id id (=) f1 f2 f1 alpha_T1 (\<lambda>x. alpha_T1 (permute_raw_T1 f1 f2 x)) alpha_T2 (\<lambda>x. alpha_T2 (permute_raw_T2 f1 id x)) x y
\<rbrakk> \<Longrightarrow> alpha_T1 (raw_T1_ctor x) (raw_T1_ctor y)"
| "\<lbrakk> bij f1 ; |supp f1| <o |UNIV::'a set| ; bij f2 ; |supp f2| <o |UNIV::'b set| ;
  id_on ((set7_T2_pre x - set5_T2_pre x) \<union> (\<Union>(FVars_raw_T11 ` set9_T2_pre x) - set5_T2_pre x) \<union> (\<Union>(FVars_raw_T21 ` set11_T2_pre x) - set5_T2_pre x)) f1 ;
  id_on (\<Union>(FVars_raw_T12 ` set9_T2_pre x) - set6_T2_pre x) f2 ;
  mr_rel_T2_pre id id id (=) f1 f2 f1 alpha_T1 (\<lambda>x. alpha_T1 (permute_raw_T1 f1 f2 x)) alpha_T2 (\<lambda>x. alpha_T2 (permute_raw_T2 f1 id x)) x y
\<rbrakk> \<Longrightarrow> alpha_T2 (raw_T2_ctor x) (raw_T2_ctor y)"
  monos
  conj_context_mono
  T1_pre.mr_rel_mono[OF supp_id_bound supp_id_bound supp_id_bound]
  T2_pre.mr_rel_mono[OF supp_id_bound supp_id_bound supp_id_bound]

type_synonym ('a, 'b, 'c, 'd) raw_T1' = "('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1, ('a, 'b, 'c, 'd) raw_T1, ('a, 'b, 'c, 'd) raw_T2, ('a, 'b, 'c, 'd) raw_T2) T1_pre"
type_synonym ('a, 'b, 'c, 'd) raw_T2' = "('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1, ('a, 'b, 'c, 'd) raw_T1, ('a, 'b, 'c, 'd) raw_T2, ('a, 'b, 'c, 'd) raw_T2) T2_pre"

definition avoid_raw_T1 :: "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1' \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a, 'b, 'c, 'd) raw_T1'" where
  "avoid_raw_T1 x A1 A2 \<equiv> SOME y. set5_T1_pre y \<inter> A1 = {} \<and> set6_T1_pre y \<inter> A2 = {} \<and> alpha_T1 (raw_T1_ctor x) (raw_T1_ctor y)"
definition avoid_raw_T2 :: "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2' \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a, 'b, 'c, 'd) raw_T2'" where
  "avoid_raw_T2 x A1 A2 \<equiv> SOME y. set5_T2_pre y \<inter> A1 = {} \<and> set6_T2_pre y \<inter> A2 = {} \<and> alpha_T2 (raw_T2_ctor x) (raw_T2_ctor y)"

typedef ('a::"{var_T1_pre,var_T2_pre}", 'b::"{var_T1_pre,var_T2_pre}", 'c::"{var_T1_pre,var_T2_pre}", 'd) T1 = "(UNIV :: ('a, 'b, 'c, 'd) raw_T1 set) // {(x, y). alpha_T1 x y}"
  apply (rule exI)
  apply (rule quotientI)
  apply (rule UNIV_I)
  done

typedef ('a::"{var_T1_pre,var_T2_pre}", 'b::"{var_T1_pre,var_T2_pre}", 'c::"{var_T1_pre,var_T2_pre}", 'd) T2 = "(UNIV :: ('a, 'b, 'c, 'd) raw_T2 set) // {(x, y). alpha_T2 x y}"
  apply (rule exI)
  apply (rule quotientI)
  apply (rule UNIV_I)
  done

abbreviation "TT1_abs \<equiv> quot_type.abs alpha_T1 Abs_T1"
abbreviation "TT1_rep \<equiv> quot_type.rep Rep_T1"

abbreviation "TT2_abs \<equiv> quot_type.abs alpha_T2 Abs_T2"
abbreviation "TT2_rep \<equiv> quot_type.rep Rep_T2"

type_synonym ('a, 'b, 'c, 'd) T1' = "('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) T1, ('a, 'b, 'c, 'd) T1, ('a, 'b, 'c, 'd) T2, ('a, 'b, 'c, 'd) T2) T1_pre"
type_synonym ('a, 'b, 'c, 'd) T2' = "('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) T1, ('a, 'b, 'c, 'd) T1, ('a, 'b, 'c, 'd) T2, ('a, 'b, 'c, 'd) T2) T2_pre"

definition T1_ctor :: "('a, 'b, 'c, 'd) T1' \<Rightarrow> ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1"
  where "T1_ctor x \<equiv> TT1_abs (raw_T1_ctor (map_T1_pre id id id id id id id TT1_rep TT1_rep TT2_rep TT2_rep x))"
definition T2_ctor :: "('a, 'b, 'c, 'd) T2' \<Rightarrow> ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2"
  where "T2_ctor x \<equiv> TT2_abs (raw_T2_ctor (map_T2_pre id id id id id id id TT1_rep TT1_rep TT2_rep TT2_rep x))"

definition permute_T1 :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b, 'c, 'd) T1 \<Rightarrow> ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1"
  where "permute_T1 f1 f2 x \<equiv> TT1_abs (permute_raw_T1 f1 f2 (TT1_rep x))"
definition permute_T2 :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b, 'c, 'd) T2 \<Rightarrow> ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2"
  where "permute_T2 f1 f2 x \<equiv> TT2_abs (permute_raw_T2 f1 f2 (TT2_rep x))"

definition FVars_T11 :: "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1 \<Rightarrow> 'a set"
  where "FVars_T11 x \<equiv> FVars_raw_T11 (TT1_rep x)"
definition FVars_T12 :: "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1 \<Rightarrow> 'b set"
  where "FVars_T12 x \<equiv> FVars_raw_T12 (TT1_rep x)"
definition FVars_T21 :: "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2 \<Rightarrow> 'a set"
  where "FVars_T21 x \<equiv> FVars_raw_T21 (TT2_rep x)"
definition FVars_T22 :: "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2 \<Rightarrow> 'b set"
  where "FVars_T22 x \<equiv> FVars_raw_T22 (TT2_rep x)"

definition avoid_T1 :: "('a, 'b, 'c, 'd) T1' \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a::{var_T1_pre, var_T2_pre}, 'b::{var_T1_pre, var_T2_pre}, 'c::{var_T1_pre, var_T2_pre}, 'd) T1'"
  where "avoid_T1 x A B \<equiv> map_T1_pre id id id id id id id TT1_abs TT1_abs TT2_abs TT2_abs (
    avoid_raw_T1 (map_T1_pre id id id id id id id TT1_rep TT1_rep TT2_rep TT2_rep x) A B)"
definition avoid_T2 :: "('a, 'b, 'c, 'd) T2' \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a::{var_T1_pre, var_T2_pre}, 'b::{var_T1_pre, var_T2_pre}, 'c::{var_T1_pre, var_T2_pre}, 'd) T2'"
  where "avoid_T2 x A B \<equiv> map_T2_pre id id id id id id id TT1_abs TT1_abs TT2_abs TT2_abs (
    avoid_raw_T2 (map_T2_pre id id id id id id id TT1_rep TT1_rep TT2_rep TT2_rep x) A B)"

lemmas FVars_defs = FVars_T11_def FVars_T12_def FVars_T21_def FVars_T22_def

inductive subshape_T1_T1 :: "('a, 'b, 'c, 'd) raw_T1 \<Rightarrow> ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1 \<Rightarrow> bool"
  and subshape_T2_T1 :: "('a, 'b, 'c, 'd) raw_T2 \<Rightarrow> ('a, 'b, 'c, 'd) raw_T1 \<Rightarrow> bool"
  and subshape_T1_T2 :: "('a, 'b, 'c, 'd) raw_T1 \<Rightarrow> ('a, 'b, 'c, 'd) raw_T2 \<Rightarrow> bool"
  and subshape_T2_T2 :: "('a, 'b, 'c, 'd) raw_T2 \<Rightarrow> ('a, 'b, 'c, 'd) raw_T2 \<Rightarrow> bool"
  where
  "\<lbrakk> bij f1 ; |supp f1| <o |UNIV::'a set| ; bij f2 ; |supp f2| <o |UNIV::'b set| ; alpha_T1 (permute_raw_T1 f1 f2 y) z ; z \<in> set8_T1_pre x \<union> set9_T1_pre x \<rbrakk> \<Longrightarrow> subshape_T1_T1 y (raw_T1_ctor x)"
| "\<lbrakk> bij f1 ; |supp f1| <o |UNIV::'a set| ; bij f2 ; |supp f2| <o |UNIV::'b set| ; alpha_T2 (permute_raw_T2 f1 f2 y) z ; z \<in> set10_T1_pre x \<union> set11_T1_pre x \<rbrakk> \<Longrightarrow> subshape_T2_T1 y (raw_T1_ctor x)"
| "\<lbrakk> bij f1 ; |supp f1| <o |UNIV::'a set| ; bij f2 ; |supp f2| <o |UNIV::'b set| ; alpha_T1 (permute_raw_T1 f1 f2 y) z ; z \<in> set8_T2_pre x \<union> set9_T2_pre x \<rbrakk> \<Longrightarrow> subshape_T1_T2 y (raw_T2_ctor x)"
| "\<lbrakk> bij f1 ; |supp f1| <o |UNIV::'a set| ; bij f2 ; |supp f2| <o |UNIV::'b set| ; alpha_T2 (permute_raw_T2 f1 f2 y) z ; z \<in> set10_T2_pre x \<union> set11_T2_pre x \<rbrakk> \<Longrightarrow> subshape_T2_T2 y (raw_T2_ctor x)"

lemmas subshape_intros = subshape_T1_T1_subshape_T2_T1_subshape_T1_T2_subshape_T2_T2.intros
lemmas subshape_elims = subshape_T1_T1.cases subshape_T2_T1.cases subshape_T1_T2.cases subshape_T2_T2.cases

definition noclash_raw_T1 :: "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1' \<Rightarrow> bool"
  where "noclash_raw_T1 x \<equiv> set5_T1_pre x \<inter> (set1_T1_pre x \<union> \<Union>(FVars_raw_T11 ` set8_T1_pre x) \<union> \<Union>(FVars_raw_T21 ` set10_T1_pre x)) = {}
                        \<and> set6_T1_pre x \<inter> (set2_T1_pre x \<union> \<Union>(FVars_raw_T12 ` set8_T1_pre x) \<union> \<Union>(FVars_raw_T22 ` set10_T1_pre x) \<union> \<Union>(FVars_raw_T22 ` set11_T1_pre x)) = {}"
definition noclash_raw_T2 :: "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2' \<Rightarrow> bool"
  where "noclash_raw_T2 x \<equiv> set5_T2_pre x \<inter> (set1_T2_pre x \<union> \<Union>(FVars_raw_T11 ` set8_T2_pre x) \<union> \<Union>(FVars_raw_T21 ` set10_T2_pre x)) = {}
                        \<and> set6_T2_pre x \<inter> (set2_T2_pre x \<union> \<Union>(FVars_raw_T12 ` set8_T2_pre x) \<union> \<Union>(FVars_raw_T22 ` set10_T2_pre x) \<union> \<Union>(FVars_raw_T22 ` set11_T2_pre x)) = {}"

definition noclash_T1 :: "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1' \<Rightarrow> bool"
  where "noclash_T1 x \<equiv> set5_T1_pre x \<inter> (set1_T1_pre x \<union> \<Union>(FVars_T11 ` set8_T1_pre x) \<union> \<Union>(FVars_T21 ` set10_T1_pre x)) = {}
                        \<and> set6_T1_pre x \<inter> (set2_T1_pre x \<union> \<Union>(FVars_T12 ` set8_T1_pre x) \<union> \<Union>(FVars_T22 ` set10_T1_pre x) \<union> \<Union>(FVars_T22 ` set11_T1_pre x)) = {}"
definition noclash_T2 :: "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2' \<Rightarrow> bool"
  where "noclash_T2 x \<equiv> set5_T2_pre x \<inter> (set1_T2_pre x \<union> \<Union>(FVars_T11 ` set8_T2_pre x) \<union> \<Union>(FVars_T21 ` set10_T2_pre x)) = {}
                        \<and> set6_T2_pre x \<inter> (set2_T2_pre x \<union> \<Union>(FVars_T12 ` set8_T2_pre x) \<union> \<Union>(FVars_T22 ` set10_T2_pre x) \<union> \<Union>(FVars_T22 ` set11_T2_pre x)) = {}"

(************* PROOFS *****************)

lemma permute_raw_ids:
  fixes x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
  shows "permute_raw_T1 id id x = x" (is ?P1)
    "permute_raw_T2 id id x2 = x2" (is ?P2)
proof -
  have x: "?P1 \<and> ?P2"
    apply (rule raw_T1_raw_T2.induct[of _ _ x x2])
      (* REPEAT_DETERM *)
     apply (rule trans)
      apply (rule permute_raw_simps)
         apply (rule bij_id supp_id_bound)+
     apply (rule trans)
      apply (rule arg_cong[of _ _ raw_T1_ctor])
      apply (rule trans[rotated])
       apply (rule T1_pre.map_id)
      apply (rule T1_pre.map_cong)
                        apply (rule bij_id supp_id_bound)+
                apply (rule refl trans[OF _ id_apply[symmetric]] | assumption)+
      (* repeated *)
    apply (rule trans)
     apply (rule permute_raw_simps)
        apply (rule bij_id supp_id_bound)+
    apply (rule trans)
     apply (rule arg_cong[of _ _ raw_T2_ctor])
     apply (rule trans[rotated])
      apply (rule T2_pre.map_id)
     apply (rule T2_pre.map_cong)
                        apply (rule bij_id supp_id_bound)+
               apply (rule refl trans[OF _ id_apply[symmetric]] | assumption)+
    done
  show ?P1 by (rule conjunct1[OF x])
  show ?P2 by (rule conjunct2[OF x])
qed

lemmas permute_raw_id0s = permute_raw_ids[abs_def, unfolded id_def[symmetric], THEN meta_eq_to_obj_eq]

lemma permute_raw_comps:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
    and g1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and g2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
    and x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
    and "bij g1" "|supp g1| <o |UNIV::'a set|" "bij g2" "|supp g2| <o |UNIV::'b set|"
  shows
    "permute_raw_T1 g1 g2 (permute_raw_T1 f1 f2 x) = permute_raw_T1 (g1 \<circ> f1) (g2 \<circ> f2) x" (is ?P1)
    "permute_raw_T2 g1 g2 (permute_raw_T2 f1 f2 x2) = permute_raw_T2 (g1 \<circ> f1) (g2 \<circ> f2) x2" (is ?P2)
proof -
  have x: "?P1 \<and> ?P2"
    apply (rule raw_T1_raw_T2.induct[of _ _ x x2])
      (* REPEAT_DETERM *)
     apply (subst permute_raw_simps)
         apply (rule assms)+
     apply (subst permute_raw_simps)
         apply (rule assms)+
     apply (subst T1_pre.map_comp)
              apply (rule assms supp_id_bound bij_id)+
     apply (unfold id_o o_id)
     apply (subst permute_raw_simps)
         apply (rule bij_comp supp_comp_bound infinite_UNIV assms)+
     apply (rule arg_cong[OF T1_pre.map_cong])
                        apply (rule bij_comp supp_comp_bound infinite_UNIV assms supp_id_bound bij_id)+
               apply (rule refl trans[OF comp_apply] | assumption)+
      (* repeated *)
    apply (subst permute_raw_simps)
        apply (rule assms)+
    apply (subst permute_raw_simps)
        apply (rule assms)+
    apply (subst T2_pre.map_comp)
             apply (rule assms supp_id_bound bij_id)+
    apply (unfold id_o o_id)
    apply (subst permute_raw_simps)
        apply (rule bij_comp supp_comp_bound infinite_UNIV assms)+
    apply (rule arg_cong[OF T2_pre.map_cong])
                        apply (rule bij_comp supp_comp_bound infinite_UNIV assms supp_id_bound bij_id)+
              apply (rule refl trans[OF comp_apply] | assumption)+
    done

  show ?P1 by (rule conjunct1[OF x])
  show ?P2 by (rule conjunct2[OF x])
qed

lemma permute_raw_comp0s:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
    and g1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and g2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
    and "bij g1" "|supp g1| <o |UNIV::'a set|" "bij g2" "|supp g2| <o |UNIV::'b set|"
  shows
    "permute_raw_T1 g1 g2 \<circ> permute_raw_T1 f1 f2 = permute_raw_T1 (g1 \<circ> f1) (g2 \<circ> f2)"
    "permute_raw_T2 g1 g2 \<circ> permute_raw_T2 f1 f2 = permute_raw_T2 (g1 \<circ> f1) (g2 \<circ> f2)"
   apply (rule ext)
   apply (rule trans[OF comp_apply])
   apply (rule permute_raw_comps)
          apply (rule assms)+
    (* repeated *)
  apply (rule ext)
  apply (rule trans[OF comp_apply])
  apply (rule permute_raw_comps)
         apply (rule assms)+
  done

lemma FVars_raw_intros:
  "a \<in> set1_T1_pre x \<Longrightarrow> a \<in> FVars_raw_T11 (raw_T1_ctor x)"
  "a \<in> set7_T1_pre x \<Longrightarrow> a \<notin> set5_T1_pre x \<Longrightarrow> a \<in> FVars_raw_T11 (raw_T1_ctor x)"
  "z \<in> set8_T1_pre x \<Longrightarrow> a \<in> FVars_raw_T11 z \<Longrightarrow> a \<in> FVars_raw_T11 (raw_T1_ctor x)"
  "z \<in> set9_T1_pre x \<Longrightarrow> a \<in> FVars_raw_T11 z \<Longrightarrow> a \<notin> set5_T1_pre x \<Longrightarrow> a \<in> FVars_raw_T11 (raw_T1_ctor x)"
  "z2 \<in> set10_T1_pre x \<Longrightarrow> a \<in> FVars_raw_T21 z2 \<Longrightarrow> a \<in> FVars_raw_T11 (raw_T1_ctor x)"
  "z2 \<in> set11_T1_pre x \<Longrightarrow> a \<in> FVars_raw_T21 z2 \<Longrightarrow> a \<notin> set5_T1_pre x \<Longrightarrow> a \<in> FVars_raw_T11 (raw_T1_ctor x)"
  "a \<in> set1_T2_pre x2 \<Longrightarrow> a \<in> FVars_raw_T21 (raw_T2_ctor x2)"
  "a \<in> set7_T2_pre x2 \<Longrightarrow> a \<notin> set5_T2_pre x2 \<Longrightarrow> a \<in> FVars_raw_T21 (raw_T2_ctor x2)"
  "z \<in> set8_T2_pre x2 \<Longrightarrow> a \<in> FVars_raw_T11 z \<Longrightarrow> a \<in> FVars_raw_T21 (raw_T2_ctor x2)"
  "z \<in> set9_T2_pre x2 \<Longrightarrow> a \<in> FVars_raw_T11 z \<Longrightarrow> a \<notin> set5_T2_pre x2 \<Longrightarrow> a \<in> FVars_raw_T21 (raw_T2_ctor x2)"
  "z2 \<in> set10_T2_pre x2 \<Longrightarrow> a \<in> FVars_raw_T21 z2 \<Longrightarrow> a \<in> FVars_raw_T21 (raw_T2_ctor x2)"
  "z2 \<in> set11_T2_pre x2 \<Longrightarrow> a \<in> FVars_raw_T21 z2 \<Longrightarrow> a \<notin> set5_T2_pre x2 \<Longrightarrow> a \<in> FVars_raw_T21 (raw_T2_ctor x2)"
  "b \<in> set2_T1_pre x \<Longrightarrow> b \<in> FVars_raw_T12 (raw_T1_ctor x)"
  "z \<in> set8_T1_pre x \<Longrightarrow> b \<in> FVars_raw_T12 z \<Longrightarrow> b \<in> FVars_raw_T12 (raw_T1_ctor x)"
  "z \<in> set9_T1_pre x \<Longrightarrow> b \<in> FVars_raw_T12 z \<Longrightarrow> b \<notin> set6_T1_pre x \<Longrightarrow> b \<in> FVars_raw_T12 (raw_T1_ctor x)"
  "z2 \<in> set10_T1_pre x \<Longrightarrow> b \<in> FVars_raw_T22 z2 \<Longrightarrow> b \<in> FVars_raw_T12 (raw_T1_ctor x)"
  "z2 \<in> set11_T1_pre x \<Longrightarrow> b \<in> FVars_raw_T22 z2 \<Longrightarrow> b \<in> FVars_raw_T12 (raw_T1_ctor x)"
  "b \<in> set2_T2_pre x2 \<Longrightarrow> b \<in> FVars_raw_T22 (raw_T2_ctor x2)"
  "z \<in> set8_T2_pre x2 \<Longrightarrow> b \<in> FVars_raw_T12 z \<Longrightarrow> b \<in> FVars_raw_T22 (raw_T2_ctor x2)"
  "z \<in> set9_T2_pre x2 \<Longrightarrow> b \<in> FVars_raw_T12 z \<Longrightarrow> b \<notin> set6_T2_pre x2 \<Longrightarrow> b \<in> FVars_raw_T22 (raw_T2_ctor x2)"
  "z2 \<in> set10_T2_pre x2 \<Longrightarrow> b \<in> FVars_raw_T22 z2 \<Longrightarrow> b \<in> FVars_raw_T22 (raw_T2_ctor x2)"
  "z2 \<in> set11_T2_pre x2 \<Longrightarrow> b \<in> FVars_raw_T22 z2 \<Longrightarrow> b \<in> FVars_raw_T22 (raw_T2_ctor x2)"
                     apply (unfold FVars_raw_defs mem_Collect_eq Un_iff de_Morgan_disj)
                     apply (erule free1_raw_T1_free1_raw_T2.intros free2_raw_T1_free2_raw_T2.intros, (assumption+)?)+
  done

lemma FVars_raw_ctors:
  "FVars_raw_T11 (raw_T1_ctor x) = set1_T1_pre x \<union> (set7_T1_pre x - set5_T1_pre x) \<union> \<Union>(FVars_raw_T11 ` set8_T1_pre x)
    \<union> (\<Union>(FVars_raw_T11 ` set9_T1_pre x) - set5_T1_pre x) \<union> \<Union>(FVars_raw_T21 ` set10_T1_pre x)
    \<union> (\<Union>(FVars_raw_T21 ` set11_T1_pre x) - set5_T1_pre x)"
  "FVars_raw_T12 (raw_T1_ctor x) = set2_T1_pre x \<union> \<Union>(FVars_raw_T12 ` set8_T1_pre x)
    \<union> (\<Union>(FVars_raw_T12 ` set9_T1_pre x) - set6_T1_pre x) \<union> \<Union>(FVars_raw_T22 ` set10_T1_pre x)
    \<union> (\<Union>(FVars_raw_T22 ` set11_T1_pre x))"
  "FVars_raw_T21 (raw_T2_ctor x2) = set1_T2_pre x2 \<union> (set7_T2_pre x2 - set5_T2_pre x2) \<union> \<Union>(FVars_raw_T11 ` set8_T2_pre x2)
    \<union> (\<Union>(FVars_raw_T11 ` set9_T2_pre x2) - set5_T2_pre x2) \<union> \<Union>(FVars_raw_T21 ` set10_T2_pre x2)
    \<union> (\<Union>(FVars_raw_T21 ` set11_T2_pre x2) - set5_T2_pre x2)"
  "FVars_raw_T22 (raw_T2_ctor x2) = set2_T2_pre x2 \<union> \<Union>(FVars_raw_T12 ` set8_T2_pre x2)
    \<union> (\<Union>(FVars_raw_T12 ` set9_T2_pre x2) - set6_T2_pre x2) \<union> \<Union>(FVars_raw_T22 ` set10_T2_pre x2)
    \<union> (\<Union>(FVars_raw_T22 ` set11_T2_pre x2))"
     apply (unfold FVars_raw_defs)
    (* goal 1 *)
     apply (rule subset_antisym)
      apply (rule subsetI)
      apply (erule CollectE)
      apply (erule free1_raw_T1.cases)
    (* REPEAT_DETERM *)
          apply (drule iffD1[OF raw_T1.inject])
          apply hypsubst_thin
          apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 1] 1\<close>)
          apply (rule DiffI[rotated], assumption)?
          apply (rule UN_I, assumption, rule CollectI)?
          apply assumption
    (* repeated *)
         apply (drule iffD1[OF raw_T1.inject])
         apply hypsubst_thin
         apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 2] 1\<close>)
         apply (rule DiffI[rotated], assumption)?
         apply (rule UN_I, assumption, rule CollectI)?
         apply assumption
    (* repeated *)
        apply (drule iffD1[OF raw_T1.inject])
        apply hypsubst_thin
        apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 3] 1\<close>)
        apply (rule DiffI[rotated], assumption)?
        apply (rule UN_I, assumption, rule CollectI)?
        apply assumption
    (* repeated *)
       apply (drule iffD1[OF raw_T1.inject])
       apply hypsubst_thin
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 4] 1\<close>)
       apply (rule DiffI[rotated], assumption)?
       apply (rule UN_I, assumption, rule CollectI)?
       apply assumption
    (* repeated *)
      apply (drule iffD1[OF raw_T1.inject])
      apply hypsubst_thin
      apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 5] 1\<close>)
      apply (rule DiffI[rotated], assumption)?
      apply (rule UN_I, assumption, rule CollectI)?
      apply assumption
    (* repeated *)
      apply (drule iffD1[OF raw_T1.inject])
      apply hypsubst_thin
      apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 6] 1\<close>)
      apply (rule DiffI[rotated], assumption)?
      apply (rule UN_I, assumption, rule CollectI)?
      apply assumption
    (* END REPEAT_DETERM *)
     apply (rule subsetI)
     apply (erule UnE)+
    (* REPEAT_DETERM *)
         apply (rule CollectI)
         apply (erule DiffE)?
         apply (erule UN_E, erule CollectE)?
         apply (erule free1_raw_T1_free1_raw_T2.intros)
        apply (assumption+)?
    (* repeated *)
        apply (rule CollectI)
        apply (erule DiffE)?
        apply (erule UN_E, erule CollectE)?
        apply (erule free1_raw_T1_free1_raw_T2.intros)
        apply (assumption+)?
    (* repeated *)
        apply (rule CollectI)
        apply (erule DiffE)?
        apply (erule UN_E, erule CollectE)?
        apply (erule free1_raw_T1_free1_raw_T2.intros)
        apply (assumption+)?
    (* repeated *)
       apply (rule CollectI)
       apply (erule DiffE)?
       apply (erule UN_E, erule CollectE)
       apply (erule free1_raw_T1_free1_raw_T2.intros)
        apply (assumption+)?
    (* repeated *)
      apply (rule CollectI)
      apply (erule DiffE)?
      apply (erule UN_E, erule CollectE)
      apply (erule free1_raw_T1_free1_raw_T2.intros)
      apply (assumption+)?
    (* repeated *)
     apply (rule CollectI)
     apply (erule DiffE)?
     apply (erule UN_E, erule CollectE)
     apply (erule free1_raw_T1_free1_raw_T2.intros)
      apply (assumption+)?
    (* END REPEAT_DETERM *)
    (* next goal, same tactic *)
    apply (rule subset_antisym)
     apply (rule subsetI)
     apply (erule CollectE)
     apply (erule free2_raw_T1.cases)
    (* REPEAT_DETERM *)
         apply (drule iffD1[OF raw_T1.inject])
         apply hypsubst_thin
         apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 1] 1\<close>)
         apply (rule DiffI[rotated], assumption)?
         apply (rule UN_I, assumption, rule CollectI)?
         apply assumption
    (* repeated *)
        apply (drule iffD1[OF raw_T1.inject])
        apply hypsubst_thin
        apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 2] 1\<close>)
        apply (rule DiffI[rotated], assumption)?
        apply (rule UN_I, assumption, rule CollectI)?
        apply assumption
    (* repeated *)
       apply (drule iffD1[OF raw_T1.inject])
       apply hypsubst_thin
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 3] 1\<close>)
       apply (rule DiffI[rotated], assumption)?
       apply (rule UN_I, assumption, rule CollectI)?
       apply assumption
    (* repeated *)
      apply (drule iffD1[OF raw_T1.inject])
      apply hypsubst_thin
      apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 4] 1\<close>)
      apply (rule DiffI[rotated], assumption)?
      apply (rule UN_I, assumption, rule CollectI)?
      apply assumption
    (* repeated *)
     apply (drule iffD1[OF raw_T1.inject])
     apply hypsubst_thin
     apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 5] 1\<close>)
     apply (rule DiffI[rotated], assumption)?
     apply (rule UN_I, assumption, rule CollectI)?
     apply assumption
    (* END REPEAT_DETERM *)
    apply (rule subsetI)
    apply (erule UnE)+
    (* REPEAT_DETERM *)
        apply (rule CollectI)
        apply (erule DiffE)?
        apply (erule UN_E, erule CollectE)?
        apply (erule free2_raw_T1_free2_raw_T2.intros)
       apply (assumption+)?
    (* repeated *)
       apply (rule CollectI)
       apply (erule DiffE)?
       apply (erule UN_E, erule CollectE)
       apply (erule free2_raw_T1_free2_raw_T2.intros)
       apply (assumption+)?
    (* repeated *)
      apply (rule CollectI)
      apply (erule DiffE)?
      apply (erule UN_E, erule CollectE)
      apply (erule free2_raw_T1_free2_raw_T2.intros)
       apply (assumption+)?
    (* repeated *)
     apply (rule CollectI)
     apply (erule DiffE)?
     apply (erule UN_E, erule CollectE)
     apply (erule free2_raw_T1_free2_raw_T2.intros)
     apply (assumption+)?
    (* repeated *)
    apply (rule CollectI)
    apply (erule DiffE)?
    apply (erule UN_E, erule CollectE)
    apply (erule free2_raw_T1_free2_raw_T2.intros)
    apply (assumption+)?
    (* END REPEAT_DETERM *)
    (* next goal, same tactic *)
   apply (rule subset_antisym)
    apply (rule subsetI)
    apply (erule CollectE)
    apply (erule free1_raw_T2.cases)
    (* REPEAT_DETERM *)
        apply (drule iffD1[OF raw_T2.inject])
        apply hypsubst_thin
        apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 1] 1\<close>)
        apply (rule DiffI[rotated], assumption)?
        apply (rule UN_I, assumption, rule CollectI)?
        apply assumption
    (* repeated *)
       apply (drule iffD1[OF raw_T2.inject])
       apply hypsubst_thin
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 2] 1\<close>)
       apply (rule DiffI[rotated], assumption)?
       apply (rule UN_I, assumption, rule CollectI)?
       apply assumption
    (* repeated *)
      apply (drule iffD1[OF raw_T2.inject])
      apply hypsubst_thin
      apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 3] 1\<close>)
      apply (rule DiffI[rotated], assumption)?
      apply (rule UN_I, assumption, rule CollectI)?
      apply assumption
    (* repeated *)
     apply (drule iffD1[OF raw_T2.inject])
     apply hypsubst_thin
     apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 4] 1\<close>)
     apply (rule DiffI[rotated], assumption)?
     apply (rule UN_I, assumption, rule CollectI)?
     apply assumption
    (* repeated *)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst_thin
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 5] 1\<close>)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I, assumption, rule CollectI)?
    apply assumption
    (* repeated *)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst_thin
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 6] 1\<close>)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I, assumption, rule CollectI)?
    apply assumption
    (* END REPEAT_DETERM *)
   apply (rule subsetI)
   apply (erule UnE)+
    (* REPEAT_DETERM *)
       apply (rule CollectI)
       apply (erule DiffE)?
       apply (erule UN_E, erule CollectE)?
       apply (erule free1_raw_T1_free1_raw_T2.intros)
      apply (assumption+)?
    (* repeated *)
      apply (rule CollectI)
      apply (erule DiffE)?
      apply (erule UN_E, erule CollectE)?
      apply (erule free1_raw_T1_free1_raw_T2.intros)
      apply (assumption+)?
    (* repeated *)
      apply (rule CollectI)
      apply (erule DiffE)?
      apply (erule UN_E, erule CollectE)?
      apply (erule free1_raw_T1_free1_raw_T2.intros)
      apply (assumption+)?
    (* repeated *)
     apply (rule CollectI)
     apply (erule DiffE)?
     apply (erule UN_E, erule CollectE)
     apply (erule free1_raw_T1_free1_raw_T2.intros)
      apply (assumption+)?
    (* repeated *)
    apply (rule CollectI)
    apply (erule DiffE)?
    apply (erule UN_E, erule CollectE)
    apply (erule free1_raw_T1_free1_raw_T2.intros)
    apply (assumption+)?
    (* repeated *)
   apply (rule CollectI)
   apply (erule DiffE)?
   apply (erule UN_E, erule CollectE)
   apply (erule free1_raw_T1_free1_raw_T2.intros)
    apply (assumption+)?
    (* END REPEAT_DETERM *)
    (* next goal, same tactic *)
  apply (rule subset_antisym)
   apply (rule subsetI)
   apply (erule CollectE)
   apply (erule free2_raw_T2.cases)
    (* REPEAT_DETERM *)
       apply (drule iffD1[OF raw_T2.inject])
       apply hypsubst_thin
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 1] 1\<close>)
       apply (rule DiffI[rotated], assumption)?
       apply (rule UN_I, assumption, rule CollectI)?
       apply assumption
    (* repeated *)
      apply (drule iffD1[OF raw_T2.inject])
      apply hypsubst_thin
      apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 2] 1\<close>)
      apply (rule DiffI[rotated], assumption)?
      apply (rule UN_I, assumption, rule CollectI)?
      apply assumption
    (* repeated *)
     apply (drule iffD1[OF raw_T2.inject])
     apply hypsubst_thin
     apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 3] 1\<close>)
     apply (rule DiffI[rotated], assumption)?
     apply (rule UN_I, assumption, rule CollectI)?
     apply assumption
    (* repeated *)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst_thin
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 4] 1\<close>)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I, assumption, rule CollectI)?
    apply assumption
    (* repeated *)
   apply (drule iffD1[OF raw_T2.inject])
   apply hypsubst_thin
   apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 5] 1\<close>)
   apply (rule DiffI[rotated], assumption)?
   apply (rule UN_I, assumption, rule CollectI)?
   apply assumption
    (* END REPEAT_DETERM *)
  apply (rule subsetI)
  apply (erule UnE)+
    (* REPEAT_DETERM *)
      apply (rule CollectI)
      apply (erule DiffE)?
      apply (erule UN_E, erule CollectE)?
      apply (erule free2_raw_T1_free2_raw_T2.intros)
     apply (assumption+)?
    (* repeated *)
     apply (rule CollectI)
     apply (erule DiffE)?
     apply (erule UN_E, erule CollectE)
     apply (erule free2_raw_T1_free2_raw_T2.intros)
     apply (assumption+)?
    (* repeated *)
    apply (rule CollectI)
    apply (erule DiffE)?
    apply (erule UN_E, erule CollectE)
    apply (erule free2_raw_T1_free2_raw_T2.intros)
     apply (assumption+)?
    (* repeated *)
   apply (rule CollectI)
   apply (erule DiffE)?
   apply (erule UN_E, erule CollectE)
   apply (erule free2_raw_T1_free2_raw_T2.intros)
   apply (assumption+)?
    (* repeated *)
  apply (rule CollectI)
  apply (erule DiffE)?
  apply (erule UN_E, erule CollectE)
  apply (erule free2_raw_T1_free2_raw_T2.intros)
  apply (assumption+)?
    (* END REPEAT_DETERM *)
  done

lemma FVars_raw_permute_leq:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
    and x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows
    "free1_raw_T1 z x \<Longrightarrow> f1 z \<in> FVars_raw_T11 (permute_raw_T1 f1 f2 x)" (is "_ \<Longrightarrow> ?P11")
    "free2_raw_T1 z2 x \<Longrightarrow> f2 z2 \<in> FVars_raw_T12 (permute_raw_T1 f1 f2 x)" (is "_ \<Longrightarrow> ?P12")
    "free1_raw_T2 z x2 \<Longrightarrow> f1 z \<in> FVars_raw_T21 (permute_raw_T2 f1 f2 x2)" (is "_ \<Longrightarrow> ?P21")
    "free2_raw_T2 z2 x2 \<Longrightarrow> f2 z2 \<in> FVars_raw_T22 (permute_raw_T2 f1 f2 x2)" (is "_ \<Longrightarrow> ?P22")
proof -
  have x1: "(free1_raw_T1 z x \<longrightarrow> ?P11) \<and> (free1_raw_T2 z x2 \<longrightarrow> ?P21)"
    apply (rule free1_raw_T1_free1_raw_T2.induct[of _ _ _ x _ x2])
      (* REPEAT_DETERM *)
             apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
             apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
             apply (unfold image_comp)
             apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 1] 1\<close>)
             apply (rule DiffI)?
             apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
             apply assumption
            apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
            apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
            apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
            apply (unfold image_comp)
            apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 2] 1\<close>)
            apply (rule DiffI)?
            apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
            apply assumption
           apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
           apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
           apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
           apply (unfold image_comp)
           apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 3] 1\<close>)
           apply (rule DiffI)?
            apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
            apply assumption
           apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
          apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
          apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
          apply (unfold image_comp)
          apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 4] 1\<close>)
          apply (rule DiffI)?
          apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
          apply assumption
         apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
         apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
         apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
         apply (unfold image_comp)
         apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 5] 1\<close>)
         apply (rule DiffI)?
          apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
          apply assumption
         apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
         apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
         apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
         apply (unfold image_comp)
         apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 6] 1\<close>)
         apply (rule DiffI)?
          apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
          apply assumption
         apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated, but starting from 1 again *)
        apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
        apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
        apply (unfold image_comp)
        apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 1] 1\<close>)
        apply (rule DiffI)?
        apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
        apply assumption
       apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
       apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
       apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
       apply (unfold image_comp)
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 2] 1\<close>)
       apply (rule DiffI)?
       apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
       apply assumption
      apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
      apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
      apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
      apply (unfold image_comp)
      apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 3] 1\<close>)
      apply (rule DiffI)?
       apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
       apply assumption
      apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
     apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
     apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
     apply (unfold image_comp)
     apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 4] 1\<close>)
     apply (rule DiffI)?
     apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
     apply assumption
    apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
    apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
    apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
    apply (unfold image_comp)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 5] 1\<close>)
    apply (rule DiffI)?
     apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
     apply assumption
    apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
    apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
    apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
    apply (unfold image_comp)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 6 6] 1\<close>)
    apply (rule DiffI)?
     apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
     apply assumption
    apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
    done

  have x2: "(free2_raw_T1 z2 x \<longrightarrow> ?P12) \<and> (free2_raw_T2 z2 x2 \<longrightarrow> ?P22)"
    apply (rule free2_raw_T1_free2_raw_T2.induct[of _ _ _ x _ x2])
      (* REPEAT_DETERM *)
             apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
             apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
             apply (unfold image_comp)
             apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 1] 1\<close>)
             apply (rule DiffI)?
             apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
             apply assumption
            apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
            apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
            apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
            apply (unfold image_comp)
            apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 2] 1\<close>)
            apply (rule DiffI)?
            apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
            apply assumption
           apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
           apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
           apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
           apply (unfold image_comp)
           apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 3] 1\<close>)
           apply (rule DiffI)?
            apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
            apply assumption
           apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
          apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
          apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
          apply (unfold image_comp)
          apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 4] 1\<close>)
          apply (rule DiffI)?
          apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
          apply assumption
         apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
         apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
         apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
         apply (unfold image_comp)
         apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 5] 1\<close>)
         apply (rule DiffI)?
         apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
         apply assumption
        apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated, but starting from 1 again *)
        apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
        apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
        apply (unfold image_comp)
        apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 1] 1\<close>)
        apply (rule DiffI)?
        apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
        apply assumption
       apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
       apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
       apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
       apply (unfold image_comp)
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 2] 1\<close>)
       apply (rule DiffI)?
       apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
       apply assumption
      apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
      apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
      apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
      apply (unfold image_comp)
      apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 3] 1\<close>)
      apply (rule DiffI)?
       apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
       apply assumption
      apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
     apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
     apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
     apply (unfold image_comp)
     apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 4] 1\<close>)
     apply (rule DiffI)?
     apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
     apply assumption
    apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
      (* repeated *)
    apply (unfold permute_raw_simps[OF assms] FVars_raw_ctors)[1]
    apply (subst T1_pre.set_map T2_pre.set_map, (rule supp_id_bound bij_id assms)+)+
    apply (unfold image_comp)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 5] 1\<close>)
    apply (rule DiffI)?
    apply (rule imageI | (rule UN_I, assumption, subst comp_apply))
    apply assumption
    apply (rule iffD2[OF arg_cong[OF inj_image_mem_iff[OF bij_is_inj]]], rule assms, assumption)?
    done

  show
    "free1_raw_T1 z x \<Longrightarrow> ?P11"
    "free2_raw_T1 z2 x \<Longrightarrow> ?P12"
    "free1_raw_T2 z x2 \<Longrightarrow> ?P21"
    "free2_raw_T2 z2 x2 \<Longrightarrow> ?P22"
       apply (erule mp[OF conjunct1[OF x1]])
      apply (erule mp[OF conjunct1[OF x2]])
     apply (erule mp[OF conjunct2[OF x1]])
    apply (erule mp[OF conjunct2[OF x2]])
    done
qed

lemma FVars_raw_permutes:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
    and x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows
    "FVars_raw_T11 (permute_raw_T1 f1 f2 x1) = f1 ` FVars_raw_T11 x1"
    "FVars_raw_T12 (permute_raw_T1 f1 f2 x1) = f2 ` FVars_raw_T12 x1"
    "FVars_raw_T21 (permute_raw_T2 f1 f2 x2) = f1 ` FVars_raw_T21 x2"
    "FVars_raw_T22 (permute_raw_T2 f1 f2 x2) = f2 ` FVars_raw_T22 x2"
     apply (rule subset_antisym)
     apply (rule subsetI)
     apply (subst (asm) FVars_raw_defs)
     apply (drule iffD1[OF mem_Collect_eq])
      apply (drule FVars_raw_permute_leq[rotated -1])
          prefer 5 (* 2 * nvars + 1 *)
          apply (subst (asm) permute_raw_comps)
                  prefer 9   (* 4 * nvars + 1 *)
                  apply (subst (asm) inv_o_simp1, rule assms)+
                  apply (unfold permute_raw_ids)
                  apply (erule iffD2[OF image_in_bij_eq, rotated])
                  apply (rule assms bij_imp_bij_inv supp_inv_bound)+
     apply (rule subsetI)
     apply (erule imageE)
     apply hypsubst
     apply (subst (asm) FVars_raw_defs)
     apply (drule iffD1[OF mem_Collect_eq])
     apply (erule FVars_raw_permute_leq[rotated -1])
        apply (rule assms)+
    (* next goal, same tactic *)
    apply (rule subset_antisym)
     apply (rule subsetI)
     apply (subst (asm) FVars_raw_defs)
     apply (drule iffD1[OF mem_Collect_eq])
     apply (drule FVars_raw_permute_leq[rotated -1])
         prefer 5 (* 2 * nvars + 1 *)
         apply (subst (asm) permute_raw_comps)
                 prefer 9   (* 4 * nvars + 1 *)
                 apply (subst (asm) inv_o_simp1, rule assms)+
                 apply (unfold permute_raw_ids)
                 apply (erule iffD2[OF image_in_bij_eq, rotated])
                 apply (rule assms bij_imp_bij_inv supp_inv_bound)+
    apply (rule subsetI)
    apply (erule imageE)
    apply hypsubst
     apply (subst (asm) FVars_raw_defs)
     apply (drule iffD1[OF mem_Collect_eq])
    apply (erule FVars_raw_permute_leq[rotated -1])
       apply (rule assms)+
    (* next goal, same tactic *)
   apply (rule subset_antisym)
    apply (rule subsetI)
     apply (subst (asm) FVars_raw_defs)
     apply (drule iffD1[OF mem_Collect_eq])
    apply (drule FVars_raw_permute_leq[rotated -1])
        prefer 5 (* 2 * nvars + 1 *)
        apply (subst (asm) permute_raw_comps)
                prefer 9   (* 4 * nvars + 1 *)
                apply (subst (asm) inv_o_simp1, rule assms)+
                apply (unfold permute_raw_ids)
                apply (erule iffD2[OF image_in_bij_eq, rotated])
                apply (rule assms bij_imp_bij_inv supp_inv_bound)+
   apply (rule subsetI)
   apply (erule imageE)
   apply hypsubst
     apply (subst (asm) FVars_raw_defs)
     apply (drule iffD1[OF mem_Collect_eq])
   apply (erule FVars_raw_permute_leq[rotated -1])
      apply (rule assms)+
    (* next goal, same tactic *)
  apply (rule subset_antisym)
   apply (rule subsetI)
     apply (subst (asm) FVars_raw_defs)
     apply (drule iffD1[OF mem_Collect_eq])
   apply (drule FVars_raw_permute_leq[rotated -1])
       prefer 5 (* 2 * nvars + 1 *)
       apply (subst (asm) permute_raw_comps)
               prefer 9   (* 4 * nvars + 1 *)
               apply (subst (asm) inv_o_simp1, rule assms)+
               apply (unfold permute_raw_ids)
               apply (erule iffD2[OF image_in_bij_eq, rotated])
               apply (rule assms bij_imp_bij_inv supp_inv_bound)+
  apply (rule subsetI)
  apply (erule imageE)
  apply hypsubst
     apply (subst (asm) FVars_raw_defs)
     apply (drule iffD1[OF mem_Collect_eq])
  apply (erule FVars_raw_permute_leq[rotated -1])
     apply (rule assms)+
  done

lemmas Un_bound = infinite_regular_card_order_Un[OF T1_pre.bd_infinite_regular_card_order]
lemmas UN_bound = regularCard_UNION_bound[OF T1_pre.bd_Cinfinite T1_pre.bd_regularCard]

lemma FVars_raw_bds:
  fixes x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
  shows
    "|FVars_raw_T11 x| <o natLeq" (is ?P11)
    "|FVars_raw_T12 x| <o natLeq" (is ?P12)
    "|FVars_raw_T21 x2| <o natLeq" (is ?P21)
    "|FVars_raw_T22 x2| <o natLeq" (is ?P22)
proof -
  have x1: "?P11 \<and> ?P21"
    apply (rule raw_T1_raw_T2.induct[of _ _ x x2])
     apply (unfold FVars_raw_ctors)
     apply (rule Un_bound T1_pre.set_bd T2_pre.set_bd UN_bound
        ordLeq_ordLess_trans[OF card_of_diff] | assumption)+
    done
  have x2: "?P12 \<and> ?P22"
    apply (rule raw_T1_raw_T2.induct[of _ _ x x2])
     apply (unfold FVars_raw_ctors)
     apply (rule Un_bound T1_pre.set_bd T2_pre.set_bd UN_bound
        ordLeq_ordLess_trans[OF card_of_diff] | assumption)+
    done
  show ?P11 by (rule conjunct1[OF x1])
  show ?P12 by (rule conjunct1[OF x2])
  show ?P21 by (rule conjunct2[OF x1])
  show ?P22 by (rule conjunct2[OF x2])
qed

lemmas FVars_raw_bd_UNIVs = FVars_raw_bds[THEN ordLess_ordLeq_trans, OF var_T1_pre_class.large]

lemma alpha_refls:
  fixes x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
  shows "alpha_T1 x x" "alpha_T2 x2 x2"
proof -
  have x: "(\<forall>(x::('a, 'b, 'c, 'd) raw_T1) y. x = y \<longrightarrow> alpha_T1 x y) \<and> (\<forall>(x::('a, 'b, 'c, 'd) raw_T2) y. x = y \<longrightarrow> alpha_T2 x y)"
    apply (rule alpha_T1_alpha_T2.coinduct)
      (* REPEAT_DETERM *)
    apply hypsubst_thin
    apply (unfold triv_forall_equality)
    subgoal for x
      apply (rule raw_T1.exhaust[of x])
      apply hypsubst_thin
      apply (rule exI)+
      apply (rule conjI, rule refl supp_id_bound bij_id id_on_id)+
      apply (unfold mr_rel_T1_pre_def T1_pre.map_id permute_raw_ids)
      apply (rule T1_pre.rel_refl_strong)
          apply (rule refl disjI1)+
      done
        (* repeated *)
    subgoal for x y
      apply (rule raw_T2.exhaust[of x])
      apply (rule raw_T2.exhaust[of y])
      apply hypsubst_thin
      apply (rule exI)+
      apply (rule conjI, rule refl supp_id_bound bij_id id_on_id)+
      apply (unfold mr_rel_T2_pre_def T2_pre.map_id permute_raw_ids)
      apply (rule T2_pre.rel_refl_strong)
          apply (rule refl disjI1)+
      done
    done

  show "alpha_T1 x x" by (rule conjunct1[OF x, THEN spec, THEN spec, THEN mp[OF _ refl]])
  show "alpha_T2 x2 x2" by (rule conjunct2[OF x, THEN spec, THEN spec, THEN mp[OF _ refl]])
qed

lemma alpha_bijs:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
    and g1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and g2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
    and x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
    and g_prems: "bij g1" "|supp g1| <o |UNIV::'a set|" "bij g2" "|supp g2| <o |UNIV::'b set|"
  shows
    "eq_on (FVars_raw_T11 x) f1 g1 \<Longrightarrow> eq_on (FVars_raw_T12 x) f2 g2 \<Longrightarrow> alpha_T1 x y \<Longrightarrow> alpha_T1 (permute_raw_T1 f1 f2 x) (permute_raw_T1 g1 g2 y)"
    "eq_on (FVars_raw_T21 x2) f1 g1 \<Longrightarrow> eq_on (FVars_raw_T22 x2) f2 g2 \<Longrightarrow> alpha_T2 x2 y2 \<Longrightarrow> alpha_T2 (permute_raw_T2 f1 f2 x2) (permute_raw_T2 g1 g2 y2)"
proof -
  have x: "(\<forall>(x::('a, 'b, 'c, 'd) raw_T1) y. (\<exists>x' y' f1 f2 g1 g2.
      bij f1 \<and> |supp f1| <o |UNIV::'a set| \<and> bij f2 \<and> |supp f2| <o |UNIV::'b set|
    \<and> bij g1 \<and> |supp g1| <o |UNIV::'a set| \<and> bij g2 \<and> |supp g2| <o |UNIV::'b set|
    \<and> x = permute_raw_T1 f1 f2 x' \<and> y = permute_raw_T1 g1 g2 y' \<and> eq_on (FVars_raw_T11 x') f1 g1 \<and> eq_on (FVars_raw_T12 x') f2 g2 \<and> alpha_T1 x' y') \<longrightarrow> alpha_T1 x y
  ) \<and> (\<forall>(x2::('a, 'b, 'c, 'd) raw_T2) y2. (\<exists>x2' y2' f1 f2 g1 g2.
    bij f1 \<and> |supp f1| <o |UNIV::'a set| \<and> bij f2 \<and> |supp f2| <o |UNIV::'b set|
  \<and> bij g1 \<and> |supp g1| <o |UNIV::'a set| \<and> bij g2 \<and> |supp g2| <o |UNIV::'b set|
  \<and> x2 = permute_raw_T2 f1 f2 x2' \<and> y2 = permute_raw_T2 g1 g2 y2' \<and> eq_on (FVars_raw_T21 x2') f1 g1 \<and> eq_on (FVars_raw_T22 x2') f2 g2 \<and> alpha_T2 x2' y2') \<longrightarrow> alpha_T2 x2 y2)"
    apply (rule alpha_T1_alpha_T2.coinduct)
     apply (erule exE conjE)+
     apply (erule alpha_T1.cases)
     apply hypsubst
     apply (unfold triv_forall_equality)
    subgoal for f1 f2 g1 g2 \<sigma>1 \<sigma>2 x y
      apply (rule exI[of _ "g1 \<circ> \<sigma>1 \<circ> inv f1"])
      apply (rule exI[of _ "g2 \<circ> \<sigma>2 \<circ> inv f2"])
      apply (rule exI)+
      apply (rule conjI, rule permute_raw_simps, (rule supp_id_bound bij_id | assumption)+)+
      apply (rule conjI, (rule bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound infinite_UNIV | assumption)+)+

      apply (subst T1_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
      apply (unfold image_comp[unfolded comp_def])
      apply (subst FVars_raw_permutes, (rule supp_id_bound bij_id | assumption)+)+
      apply (unfold image_UN[symmetric])
      apply (subst image_set_diff[OF bij_is_inj, symmetric], assumption)+

       apply (unfold image_Un[symmetric])
      (* REPEAT_DETERM *)
      apply (rule conjI)
       apply (rule id_onI)
       apply (erule imageE)
       apply hypsubst
       apply (rule trans)
        apply (rule comp_apply)
       apply (subst inv_simp1)
        apply assumption
       apply (rule trans)
        apply (rule comp_apply)
       apply (rule trans)
        apply (rule arg_cong[of _ _ g1])
        apply (erule id_onD)
        apply assumption
       apply (rule sym)
       apply (erule eq_onD)
       apply ((erule UnE)+)?
        (* REPEAT_DETERM *)
       apply (erule DiffE)
       apply (erule UN_E)?
       apply (erule FVars_raw_intros)
       apply assumption+
       (* repeated *)
       apply (erule DiffE)
       apply (erule UN_E)?
       apply (erule FVars_raw_intros)
        apply assumption+
       (* repeated *)
       apply (erule DiffE)
       apply (erule UN_E)?
       apply (erule FVars_raw_intros)
        apply assumption+
        (* END REPEAT_DETERM *)
        (* repeated *)
      apply (rule conjI)
      apply (rule id_onI)
      apply (erule imageE)
      apply hypsubst
      apply (rule trans)
       apply (rule comp_apply)
      apply (subst inv_simp1)
       apply assumption
      apply (rule trans)
       apply (rule comp_apply)
      apply (rule trans)
       apply (rule arg_cong[of _ _ g2])
       apply (erule id_onD)
       apply assumption
      apply (rule sym)
      apply (erule eq_onD)
      apply ((erule UnE)+)?
        (* REPEAT_DETERM *)
       apply (erule DiffE)
       apply (erule UN_E)?
       apply (erule FVars_raw_intros)
        apply assumption+
        (* END REPEAT_DETERM *)

        apply (rule iffD2[OF T1_pre.mr_rel_map(1)])
                      apply (rule supp_id_bound bij_id bij_comp bij_imp_bij_inv supp_inv_bound supp_comp_bound infinite_UNIV | assumption)+
        apply (unfold id_o o_id Grp_UNIV_id eq_OO)
        apply (rule iffD2[OF T1_pre.mr_rel_map(3)])
                         apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV bij_imp_bij_inv supp_inv_bound | assumption)+
        apply (unfold comp_assoc inv_id id_o o_id Grp_UNIV_id conversep_eq OO_eq relcompp_conversep_Grp Grp_OO)
        apply (subst inv_o_simp1, assumption)+
        apply (unfold id_o o_id comp_assoc[symmetric])
        apply (subst inv_o_simp1, assumption)+
        apply (unfold id_o o_id)

        apply (erule T1_pre.mr_rel_mono_strong0[rotated -12])
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
        (* repeated *)
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
                          apply ((rule ballI, rule refl) | (rule ballI, rule ballI, rule impI, assumption))+
        (* REPEAT_DETERM free ORELSE bound *)
                         apply (rule ballI)
                         apply (rule ballI)
                         apply (rule impI)
                         apply (rule disjI1)
                         apply (rule exI)
                         apply (rule exI)
                         apply (rule exI[of _ f1])
                         apply (rule exI[of _ f2])
                         apply (rule exI[of _ g1])
                         apply (rule exI[of _ g2])
                         apply (rule conjI, assumption+)+
                         apply (unfold conj_assoc[symmetric])
                         apply (erule conjI[rotated])
                         apply (unfold conj_assoc)
                         apply (rule conjI)
                          apply (rule refl)
                         apply (rule conjI)
                          apply (rule refl)
                         apply (rule conjI)
        (* REPEAT_DETERM *)
                          apply (erule eq_on_mono[rotated])
                          apply (rule subsetI)
                          apply (erule FVars_raw_intros)
                          apply assumption
        (* repeated *)
                         apply (erule eq_on_mono[rotated])
                         apply (rule subsetI)
                         apply (erule FVars_raw_intros)
                         apply assumption
        (* END REPEAT_DETERM *)
        (* repeated *)
                        apply (rule ballI)
                        apply (rule ballI)
                        apply (rule impI)
                        apply (rule disjI1)
                        apply (rule exI)
                        apply (rule exI)
                        apply (rule exI[of _ g1])
                        apply (rule exI[of _ g2])
                        apply (rule exI[of _ g1])
                        apply (rule exI[of _ g2])
                        apply (rule conjI, assumption+)+
                        apply (unfold conj_assoc[symmetric])
                        apply (erule conjI[rotated])
                        apply (unfold conj_assoc)
                        apply (rule conjI)
                         apply (rule trans)
                          apply (rule permute_raw_comps)
                          apply (assumption | rule bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV)+
                         apply (unfold comp_assoc)
                         apply (subst inv_o_simp1, assumption)+
                         apply (unfold comp_assoc[symmetric] id_o o_id)
                         apply (rule sym)
                         apply (rule permute_raw_comps)
                          apply assumption+
                        apply (rule conjI)
                         apply (rule refl)
                        apply (rule conjI)
                         apply (rule eq_on_refl)+
        (* repeated *)
                       apply (rule ballI)
                       apply (rule ballI)
                       apply (rule impI)
                       apply (rule disjI1)
                       apply (rule exI)
                       apply (rule exI)
                       apply (rule exI[of _ f1])
                       apply (rule exI[of _ f2])
                       apply (rule exI[of _ g1])
                       apply (rule exI[of _ g2])
                       apply (rule conjI, assumption+)+
                       apply (unfold conj_assoc[symmetric])
                       apply (rule conjI[rotated])
                        apply assumption
                       apply (unfold conj_assoc)
                       apply (rule conjI)
                        apply (rule refl)
                       apply (rule conjI)
                        apply (rule refl)
                       apply (rule conjI)
        (* REPEAT_DETERM *)
                        apply (erule eq_on_mono[rotated])
                        apply (rule subsetI)
                        apply (erule FVars_raw_intros)
                        apply assumption
        (* repeated *)
                       apply (erule eq_on_mono[rotated])
                       apply (rule subsetI)
                       apply (erule FVars_raw_intros)
                       apply assumption
        (* END REPEAT_DETERM *)
        (* repeated *)
                      apply (rule ballI)
                      apply (rule ballI)
                      apply (rule impI)
                      apply (rule disjI1)
                      apply (rule exI)
                      apply (rule exI)
                      apply (rule exI[of _ g1])
                      apply (rule exI[of _ f2])
                      apply (rule exI[of _ g1])
                      apply (rule exI[of _ g2])
                      apply (rule conjI, assumption+)+
                      apply (unfold conj_assoc[symmetric])
                      apply (rule conjI[rotated])
                       apply assumption
                      apply (unfold conj_assoc)
                      apply (rule conjI)
                       apply (rule trans)
                        apply (rule permute_raw_comps)
                          apply (assumption | rule bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV supp_id_bound bij_id)+
                       apply (unfold comp_assoc)
                       apply (subst inv_o_simp1, assumption)+
                       apply (unfold comp_assoc[symmetric] id_o o_id)
                       apply (rule sym)
                       apply (rule trans)
                        apply (rule permute_raw_comps)
                          apply (assumption | rule supp_id_bound bij_id)+
                       apply (unfold id_o o_id)
                       apply (rule refl)
                      apply (rule conjI)
                       apply (rule refl)
                      apply (rule conjI)
                       apply (rule eq_on_refl)
                      apply (erule eq_on_mono[rotated])
                      apply (rule subsetI)
                      apply (erule FVars_raw_intros)
                      apply (subst (asm) FVars_raw_permutes)
                          apply (assumption | rule bij_id supp_id_bound)+
                      apply (unfold image_id)
                      apply assumption
        (* END REPEAT_DETERM *)
                     apply (rule supp_id_bound bij_id supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
      done
        (* second type, same tactic *)

    apply (erule exE conjE)+
    apply (erule alpha_T2.cases)
    apply hypsubst
    apply (unfold triv_forall_equality)
    subgoal for f1 f2 g1 g2 \<sigma>1 \<sigma>2 x y
      apply (rule exI[of _ "g1 \<circ> \<sigma>1 \<circ> inv f1"])
      apply (rule exI[of _ "g2 \<circ> \<sigma>2 \<circ> inv f2"])
      apply (rule exI)+
      apply (rule conjI, rule permute_raw_simps, (rule supp_id_bound bij_id | assumption)+)+
      apply (rule conjI, (rule bij_comp supp_comp_bound f_prems bij_imp_bij_inv supp_inv_bound infinite_UNIV | assumption)+)+

      apply (subst T2_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
      apply (unfold image_comp[unfolded comp_def])
      apply (subst FVars_raw_permutes, (rule supp_id_bound bij_id | assumption)+)+
      apply (unfold image_UN[symmetric])
      apply (subst image_set_diff[OF bij_is_inj, symmetric], assumption)+

      apply (rule conjI[rotated])+
        apply (rule iffD2[OF T2_pre.mr_rel_map(1)])
                      apply (rule f_prems supp_id_bound bij_id bij_comp bij_imp_bij_inv supp_inv_bound supp_comp_bound infinite_UNIV | assumption)+
        apply (unfold id_o o_id Grp_UNIV_id eq_OO)
        apply (rule iffD2[OF T2_pre.mr_rel_map(3)])
                         apply (rule f_prems supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV bij_imp_bij_inv supp_inv_bound | assumption)+
        apply (unfold comp_assoc inv_id id_o o_id Grp_UNIV_id conversep_eq OO_eq relcompp_conversep_Grp Grp_OO)
        apply (subst inv_o_simp1, assumption)+
        apply (unfold id_o o_id comp_assoc[symmetric])
        apply (subst inv_o_simp1, assumption)+
        apply (unfold id_o o_id)

        apply (erule T2_pre.mr_rel_mono_strong0[rotated -12])
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
        (* repeated *)
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
                          apply ((rule ballI, rule refl) | (rule ballI, rule ballI, rule impI, assumption))+
        (* REPEAT_DETERM free ORELSE bound *)
                         apply (rule ballI)
                         apply (rule ballI)
                         apply (rule impI)
                         apply (rule disjI1)
                         apply (rule exI)
                         apply (rule exI)
                         apply (rule exI[of _ f1])
                         apply (rule exI[of _ f2])
                         apply (rule exI[of _ g1])
                         apply (rule exI[of _ g2])
                         apply (rule conjI, assumption+)+
                         apply (unfold conj_assoc[symmetric])
                         apply (rule conjI[rotated])
                          apply assumption
                         apply (unfold conj_assoc)
                         apply (rule conjI)
                          apply (rule refl)
                         apply (rule conjI)
                          apply (rule refl)
                         apply (rule conjI)
        (* REPEAT_DETERM *)
                          apply (erule eq_on_mono[rotated])
                          apply (rule subsetI)
                          apply (erule FVars_raw_intros)
                          apply assumption
        (* repeated *)
                         apply (erule eq_on_mono[rotated])
                         apply (rule subsetI)
                         apply (erule FVars_raw_intros)
                         apply assumption
        (* END REPEAT_DETERM *)
        (* repeated *)
                        apply (rule ballI)
                        apply (rule ballI)
                        apply (rule impI)
                        apply (rule disjI1)
                        apply (rule exI)
                        apply (rule exI)
                        apply (rule exI[of _ g1])
                        apply (rule exI[of _ g2])
                        apply (rule exI[of _ g1])
                        apply (rule exI[of _ g2])
                        apply (rule conjI, assumption+)+
                        apply (unfold conj_assoc[symmetric])
                        apply (rule conjI[rotated])
                         apply assumption
                        apply (unfold conj_assoc)
                        apply (rule conjI)
                         apply (rule trans)
                          apply (rule permute_raw_comps)
                          apply (assumption | rule bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV)+
                         apply (unfold comp_assoc)
                         apply (subst inv_o_simp1, assumption)+
                         apply (unfold comp_assoc[symmetric] id_o o_id)
                         apply (rule sym)
                         apply (rule permute_raw_comps)
                          apply assumption+
                        apply (rule conjI)
                         apply (rule refl)
                        apply (rule conjI)
                         apply (rule eq_on_refl)+
        (* repeated *)
                       apply (rule ballI)
                       apply (rule ballI)
                       apply (rule impI)
                       apply (rule disjI1)
                       apply (rule exI)
                       apply (rule exI)
                       apply (rule exI[of _ f1])
                       apply (rule exI[of _ f2])
                       apply (rule exI[of _ g1])
                       apply (rule exI[of _ g2])
                       apply (rule conjI, assumption+)+
                       apply (unfold conj_assoc[symmetric])
                       apply (rule conjI[rotated])
                        apply assumption
                       apply (unfold conj_assoc)
                       apply (rule conjI)
                        apply (rule refl)
                       apply (rule conjI)
                        apply (rule refl)
                       apply (rule conjI)
        (* REPEAT_DETERM *)
                        apply (erule eq_on_mono[rotated])
                        apply (rule subsetI)
                        apply (erule FVars_raw_intros)
                        apply assumption
        (* repeated *)
                       apply (erule eq_on_mono[rotated])
                       apply (rule subsetI)
                       apply (erule FVars_raw_intros)
                       apply assumption
        (* END REPEAT_DETERM *)
        (* repeated *)
                      apply (rule ballI)
                      apply (rule ballI)
                      apply (rule impI)
                      apply (rule disjI1)
                      apply (rule exI)
                      apply (rule exI)
                      apply (rule exI[of _ g1])
                      apply (rule exI[of _ f2])
                      apply (rule exI[of _ g1])
                      apply (rule exI[of _ g2])
                      apply (rule conjI, assumption+)+
                      apply (unfold conj_assoc[symmetric])
                      apply (rule conjI[rotated])
                       apply assumption
                      apply (unfold conj_assoc)
                      apply (rule conjI)
                       apply (rule trans)
                        apply (rule permute_raw_comps)
                          apply (assumption | rule bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV supp_id_bound bij_id)+
                       apply (unfold comp_assoc)
                       apply (subst inv_o_simp1, assumption)+
                       apply (unfold comp_assoc[symmetric] id_o o_id)
                       apply (rule sym)
                       apply (rule trans)
                        apply (rule permute_raw_comps)
                          apply (assumption | rule supp_id_bound bij_id)+
                       apply (unfold id_o o_id)
                       apply (rule refl)
                      apply (rule conjI)
                       apply (rule refl)
                      apply (rule conjI)
                       apply (rule eq_on_refl)
                      apply (erule eq_on_mono[rotated])
                      apply (rule subsetI)
                      apply (erule FVars_raw_intros)
                      apply (subst (asm) FVars_raw_permutes)
                          apply (assumption | rule bij_id supp_id_bound)+
                      apply (unfold image_id)
                      apply assumption
        (* END REPEAT_DETERM *)
                     apply (rule supp_id_bound bij_id supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
        (* REPEAT_DETERM *)
       apply ((unfold image_Un[symmetric])?)[1]
       apply (rule id_onI)
       apply (erule imageE)
       apply hypsubst
       apply (rule trans)
        apply (rule comp_apply)
       apply (subst inv_simp1)
        apply assumption
       apply (rule trans)
        apply (rule comp_apply)
       apply (rule trans)
        apply (rule arg_cong[of _ _ g2])
        apply (erule id_onD)
        apply assumption
       apply (rule sym)
       apply (erule eq_onD)
       apply ((erule UnE)+)?
        (* REPEAT_DETERM *)
       apply (erule DiffE)
       apply (erule UN_E)
       apply (erule FVars_raw_intros)
        apply assumption+
        (* END REPEAT_DETERM *)
        (* repeated *)
      apply (unfold image_Un[symmetric])[1]
      apply (rule id_onI)
      apply (erule imageE)
      apply hypsubst
      apply (rule trans)
       apply (rule comp_apply)
      apply (subst inv_simp1)
       apply assumption
      apply (rule trans)
       apply (rule comp_apply)
      apply (rule trans)
       apply (rule arg_cong[of _ _ g1])
       apply (erule id_onD)
       apply assumption
      apply (rule sym)
      apply (erule eq_onD)
      apply (erule UnE)+
        (* REPEAT_DETERM *)
       apply (erule DiffE)
       apply (erule UN_E)?
       apply (erule FVars_raw_intros)
        apply assumption+
        (* repeated *)
      apply (erule DiffE)
      apply (erule UN_E)?
      apply (erule FVars_raw_intros)
       apply assumption+
        (* repeated *)
      apply (erule DiffE)
      apply (erule UN_E)?
      apply (erule FVars_raw_intros)
       apply assumption+
        (* END REPEAT_DETERM *)
      done
    done

  show
    "eq_on (FVars_raw_T11 x) f1 g1 \<Longrightarrow> eq_on (FVars_raw_T12 x) f2 g2 \<Longrightarrow> alpha_T1 x y \<Longrightarrow> alpha_T1 (permute_raw_T1 f1 f2 x) (permute_raw_T1 g1 g2 y)"
    "eq_on (FVars_raw_T21 x2) f1 g1 \<Longrightarrow> eq_on (FVars_raw_T22 x2) f2 g2 \<Longrightarrow> alpha_T2 x2 y2 \<Longrightarrow> alpha_T2 (permute_raw_T2 f1 f2 x2) (permute_raw_T2 g1 g2 y2)"
     apply (rule conjunct1[OF x, THEN spec, THEN spec, THEN mp])
     apply (rule exI)+
     apply (rule conjI[rotated])+
                 apply assumption+
              apply (rule refl)+
            apply (rule assms)+
      (* repeated *)
    apply (rule conjunct2[OF x, THEN spec, THEN spec, THEN mp])
    apply (rule exI)+
    apply (rule conjI[rotated])+
                apply assumption+
             apply (rule refl)+
           apply (rule assms)+
    done
qed

lemma alpha_bij_eqs:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
    and x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows
    "alpha_T1 (permute_raw_T1 f1 f2 x) (permute_raw_T1 f1 f2 y) = alpha_T1 x y"
    "alpha_T2 (permute_raw_T2 f1 f2 x2) (permute_raw_T2 f1 f2 y2) = alpha_T2 x2 y2"
   apply (rule iffI)
    apply (drule alpha_bijs[rotated -1])
              prefer 11 (* 5 * nvars + 1 *)
    (* REPEAT_DETERM *)
              apply (subst (asm) permute_raw_comps)
                      prefer 9 (* 4 * nvars + 1 *)
                      apply (subst (asm) inv_o_simp1, rule assms)+
    (* repeated *)
                      apply (subst (asm) permute_raw_comps)
                      prefer 9 (* 4 * nvars + 1 *)
                      apply (subst (asm) inv_o_simp1, rule assms)+
    (* END REPEAT_DETERM *)
                      apply (unfold permute_raw_ids)
                      apply assumption
                      apply (rule assms bij_imp_bij_inv supp_inv_bound)+
     apply (rule eq_on_refl)+
   apply (erule alpha_bijs[rotated -1])
            apply (rule assms)+
    apply (rule eq_on_refl)+
    (* second goal, same tactic *)
  apply (rule iffI)
   apply (drule alpha_bijs[rotated -1])
             prefer 11 (* 5 * nvars + 1 *)
    (* REPEAT_DETERM *)
             apply (subst (asm) permute_raw_comps)
                     prefer 9 (* 4 * nvars + 1 *)
                     apply (subst (asm) inv_o_simp1, rule assms)+
    (* repeated *)
                     apply (subst (asm) permute_raw_comps)
                      prefer 9 (* 4 * nvars + 1 *)
                      apply (subst (asm) inv_o_simp1, rule assms)+
    (* END REPEAT_DETERM *)
                      apply (unfold permute_raw_ids)
                      apply assumption
                      apply (rule assms bij_imp_bij_inv supp_inv_bound)+
    apply (rule eq_on_refl)+
  apply (erule alpha_bijs[rotated -1])
           apply (rule assms)+
   apply (rule eq_on_refl)+
  done

lemma alpha_bij_eq_invs:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
    and x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows
    "alpha_T1 (permute_raw_T1 f1 f2 x) y = alpha_T1 x (permute_raw_T1 (inv f1) (inv f2) y)"
    "alpha_T2 (permute_raw_T2 f1 f2 x2) y2 = alpha_T2 x2 (permute_raw_T2 (inv f1) (inv f2) y2)"
   apply (rule trans)
    apply (rule alpha_bij_eqs[symmetric])
       prefer 5 (* 2 * nvars + 1 *)
       apply (subst permute_raw_comps)
               prefer 9 (* 4 * nvars + 1 *)
               apply (subst inv_o_simp1, rule assms)+
               apply (unfold permute_raw_ids)
               apply (rule refl)
              apply (rule assms bij_imp_bij_inv supp_inv_bound)+
    (* second goal, same tactic *)
  apply (rule trans)
   apply (rule alpha_bij_eqs[symmetric])
      prefer 5 (* 2 * nvars + 1 *)
      apply (subst permute_raw_comps)
              prefer 9 (* 4 * nvars + 1 *)
              apply (subst inv_o_simp1, rule assms)+
              apply (unfold permute_raw_ids)
              apply (rule refl)
             apply (rule assms bij_imp_bij_inv supp_inv_bound)+
  done

lemma alpha_FVars_leqs1:
  fixes x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
  and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
shows
  "(free1_raw_T1 a x \<longrightarrow> (\<forall>y. alpha_T1 x y \<longrightarrow> a \<in> FVars_raw_T11 y)) \<and> (free1_raw_T2 a x2 \<longrightarrow> (\<forall>y2. alpha_T2 x2 y2 \<longrightarrow> a \<in> FVars_raw_T21 y2))"
  "(free2_raw_T1 a2 x \<longrightarrow> (\<forall>y. alpha_T1 x y \<longrightarrow> a2 \<in> FVars_raw_T12 y)) \<and> (free2_raw_T2 a2 x2 \<longrightarrow> (\<forall>y2. alpha_T2 x2 y2 \<longrightarrow> a2 \<in> FVars_raw_T22 y2))"
    apply (rule free1_raw_T1_free1_raw_T2.induct)
    (* REPEAT_DETERM *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    (* TRY EVERY
    apply (drule DiffI[rotated])
    apply assumption
    apply (erule thin_rl)
    apply (rotate_tac -1)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF id_on_image[symmetric]], rotated -1])
    prefer 2
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF image_set_diff[OF bij_is_inj]], rotated -1])
    prefer 2
    END TRY *)
    apply (drule T1_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound | assumption)+
    apply (unfold inv_id)
    apply (rotate_tac -2)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
    apply (rule arg_cong2[of _ _ _ _ minus])?
    apply ((rule arg_cong[of _ _ "(`) _"])?, erule T1_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+)+
    apply (unfold image_comp)?
    apply ((subst (asm) inv_o_simp2, assumption)+)?
    apply (unfold image_id)
    apply (erule DiffE)?
    apply (erule FVars_raw_intros)
    (* TRY EVERY
    apply assumption
    apply assumption
    apply (erule id_on_antimono)
    apply (rule subsetI)
    apply (rotate_tac -1)
    apply (erule contrapos_pp)
    apply (unfold Un_iff de_Morgan_disj)[1]
    apply (erule conjE)+
    apply assumption
    END TRY *)
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    (* TRY EVERY *)
    apply (drule DiffI[rotated])
    apply assumption
    apply (erule thin_rl)
    apply (rotate_tac -1)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF id_on_image[symmetric]], rotated -1])
    prefer 2
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF image_set_diff[OF bij_is_inj]], rotated -1])
    prefer 2
    (* END TRY *)
    apply (drule T1_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound | assumption)+
    apply (unfold inv_id)
    apply (rotate_tac -2)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
    apply (rule arg_cong2[of _ _ _ _ minus])?
    apply ((rule arg_cong[of _ _ "(`) _"])?, erule T1_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+)+
    apply (unfold image_comp)?
    apply ((subst (asm) inv_o_simp2, assumption)+)?
    apply (unfold image_id)
    apply (erule DiffE)?
    apply (erule FVars_raw_intros)
    (* TRY EVERY *)
    apply assumption
    apply assumption
    apply (erule id_on_antimono)
    apply (rule subsetI)
    apply (rotate_tac -1)
    apply (erule contrapos_pp)
    apply (unfold Un_iff de_Morgan_disj)[1]
    apply (erule conjE)+
    apply assumption
    (* END TRY *)
    (* END REPEAT_DETERM *)

    (* REPEAT_DETERM *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (frule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD1, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1], (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold inv_id)?
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY
    apply (subst (asm) FVars_raw_permutes)
    apply (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (drule T1_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
    apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
    apply (erule T1_pre.mr_rel_set[rotated -1], (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+)+
    apply (unfold image_Un[symmetric])?
    apply (rotate_tac -1)
    apply (subst (asm) image_in_bij_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (subst (asm) inv_inv_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (unfold inv_simp1 inv_simp2)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule id_on_inv[THEN id_onD, rotated])
       apply assumption
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
       apply (unfold id_on_Un)[1]
       apply (erule conjE)+
       apply (erule id_on_image[symmetric])
       apply (rule iffD2[OF image_in_bij_eq])
       apply assumption
       apply (rule DiffI[rotated])
       apply assumption
       apply (rule UN_I)
       apply assumption
       apply (unfold FVars_raw_defs mem_Collect_eq)[1]
       apply assumption
       apply assumption
       END TRY *)
       apply (erule FVars_raw_intros)
       apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (frule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD1, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1], (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold inv_id)?
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY *)
    apply (subst (asm) FVars_raw_permutes)
    apply (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (drule T1_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
    apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
    apply (erule T1_pre.mr_rel_set[rotated -1], (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+)+
    apply (unfold image_Un[symmetric])?
    apply (rotate_tac -1)
    apply (subst (asm) image_in_bij_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (subst (asm) inv_inv_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (unfold inv_simp1 inv_simp2)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule id_on_inv[THEN id_onD, rotated])
       apply assumption
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
       apply (unfold id_on_Un)[1]
       apply (erule conjE)+
       apply (erule id_on_image[symmetric])
       apply (rule iffD2[OF image_in_bij_eq])
       apply assumption
       apply (rule DiffI[rotated])
       apply assumption
       apply (rule UN_I)
       apply assumption
       apply (unfold FVars_raw_defs mem_Collect_eq)[1]
       apply assumption
       apply assumption
       (* END TRY *)
       apply (erule FVars_raw_intros)
       apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (frule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD1, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1], (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold inv_id)?
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY
    apply (subst (asm) FVars_raw_permutes)
    apply (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (drule T1_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
    apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
    apply (erule T1_pre.mr_rel_set[rotated -1], (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+)+
    apply (unfold image_Un[symmetric])?
    apply (rotate_tac -1)
    apply (subst (asm) image_in_bij_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (subst (asm) inv_inv_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (unfold inv_simp1 inv_simp2)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule id_on_inv[THEN id_onD, rotated])
       apply assumption
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
       apply (unfold id_on_Un)[1]
       apply (erule conjE)+
       apply (erule id_on_image[symmetric])
       apply (rule iffD2[OF image_in_bij_eq])
       apply assumption
       apply (rule DiffI[rotated])
       apply assumption
       apply (rule UN_I)
       apply assumption
       apply (unfold FVars_raw_defs mem_Collect_eq)[1]
       apply assumption
       apply assumption
       END TRY *)
       apply (erule FVars_raw_intros)
       apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (frule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD1, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1], (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold inv_id)?
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY *)
    apply (subst (asm) FVars_raw_permutes)
    apply (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (drule T1_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
    apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
    apply (erule T1_pre.mr_rel_set[rotated -1], (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+)+
    apply (unfold image_Un[symmetric])?
    apply (rotate_tac -1)
    apply (subst (asm) image_in_bij_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (subst (asm) inv_inv_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (unfold inv_simp1 inv_simp2)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule id_on_inv[THEN id_onD, rotated])
       apply assumption
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 3] 1\<close>)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
       apply (unfold id_on_Un)[1]
       apply (erule conjE)+
       apply (erule id_on_image[symmetric])
       apply (rule iffD2[OF image_in_bij_eq])
       apply assumption
       apply (rule DiffI[rotated])
       apply assumption
       apply (rule UN_I)
       apply assumption
       apply (unfold FVars_raw_defs mem_Collect_eq)[1]
       apply assumption
       apply assumption
       (* END TRY *)
       apply (erule FVars_raw_intros)
       apply assumption+
    (* END REPEAT_DETERM *)
    (* second type, same tactic *)
    (* REPEAT_DETERM *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    (* TRY EVERY
    apply (drule DiffI[rotated])
    apply assumption
    apply (erule thin_rl)
    apply (rotate_tac -1)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF id_on_image[symmetric]], rotated -1])
    prefer 2
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF image_set_diff[OF bij_is_inj]], rotated -1])
    prefer 2
    END TRY *)
    apply (drule T2_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound | assumption)+
    apply (unfold inv_id)
    apply (rotate_tac -2)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
    apply (rule arg_cong2[of _ _ _ _ minus])?
    apply ((rule arg_cong[of _ _ "(`) _"])?, erule T2_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+)+
    apply (unfold image_comp)?
    apply ((subst (asm) inv_o_simp2, assumption)+)?
    apply (unfold image_id)
    apply (erule DiffE)?
    apply (erule FVars_raw_intros)
    (* TRY EVERY
    apply assumption
    apply assumption
    apply (erule id_on_antimono)
    apply (rule subsetI)
    apply (rotate_tac -1)
    apply (erule contrapos_pp)
    apply (unfold Un_iff de_Morgan_disj)[1]
    apply (erule conjE)+
    apply assumption
    END TRY *)
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    (* TRY EVERY *)
    apply (drule DiffI[rotated])
    apply assumption
    apply (erule thin_rl)
    apply (rotate_tac -1)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF id_on_image[symmetric]], rotated -1])
    prefer 2
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF image_set_diff[OF bij_is_inj]], rotated -1])
    prefer 2
    (* END TRY *)
    apply (drule T2_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound | assumption)+
    apply (unfold inv_id)
    apply (rotate_tac -2)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
    apply (rule arg_cong2[of _ _ _ _ minus])?
    apply ((rule arg_cong[of _ _ "(`) _"])?, erule T2_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+)+
    apply (unfold image_comp)?
    apply ((subst (asm) inv_o_simp2, assumption)+)?
    apply (unfold image_id)
    apply (erule DiffE)?
    apply (erule FVars_raw_intros)
    (* TRY EVERY *)
    apply assumption
    apply assumption
    apply (erule id_on_antimono)
    apply (rule subsetI)
    apply (rotate_tac -1)
    apply (erule contrapos_pp)
    apply (unfold Un_iff de_Morgan_disj)[1]
    apply (erule conjE)+
    apply assumption
    (* END TRY *)
    (* END REPEAT_DETERM *)

    (* REPEAT_DETERM *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD1, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1], (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold inv_id)?
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY
    apply (subst (asm) FVars_raw_permutes)
    apply (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (drule T1_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
    apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
    apply (erule T1_pre.mr_rel_set[rotated -1], (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+)+
    apply (unfold image_Un[symmetric])?
    apply (rotate_tac -1)
    apply (subst (asm) image_in_bij_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (subst (asm) inv_inv_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (unfold inv_simp1 inv_simp2)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule id_on_inv[THEN id_onD, rotated])
       apply assumption
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
       apply (unfold id_on_Un)[1]
       apply (erule conjE)+
       apply (erule id_on_image[symmetric])
       apply (rule iffD2[OF image_in_bij_eq])
       apply assumption
       apply (rule DiffI[rotated])
       apply assumption
       apply (rule UN_I)
       apply assumption
       apply (unfold FVars_raw_defs mem_Collect_eq)[1]
       apply assumption
       apply assumption
       END TRY *)
       apply (erule FVars_raw_intros)
       apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD1, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1], (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold inv_id)?
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY *)
    apply (subst (asm) FVars_raw_permutes)
    apply (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (drule T2_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
    apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
    apply (erule T2_pre.mr_rel_set[rotated -1], (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+)+
    apply (unfold image_Un[symmetric])?
    apply (rotate_tac -1)
    apply (subst (asm) image_in_bij_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (subst (asm) inv_inv_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (unfold inv_simp1 inv_simp2)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule id_on_inv[THEN id_onD, rotated])
       apply assumption
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
       apply (unfold id_on_Un)[1]
       apply (erule conjE)+
       apply (erule id_on_image[symmetric])
       apply (rule iffD2[OF image_in_bij_eq])
       apply assumption
       apply (rule DiffI[rotated])
       apply assumption
       apply (rule UN_I)
       apply assumption
       apply (unfold FVars_raw_defs mem_Collect_eq)[1]
       apply assumption
       apply assumption
       (* END TRY *)
       apply (erule FVars_raw_intros)
       apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD1, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1], (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold inv_id)?
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY
    apply (subst (asm) FVars_raw_permutes)
    apply (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (drule T1_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
    apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
    apply (erule T1_pre.mr_rel_set[rotated -1], (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+)+
    apply (unfold image_Un[symmetric])?
    apply (rotate_tac -1)
    apply (subst (asm) image_in_bij_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (subst (asm) inv_inv_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (unfold inv_simp1 inv_simp2)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule id_on_inv[THEN id_onD, rotated])
       apply assumption
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
       apply (unfold id_on_Un)[1]
       apply (erule conjE)+
       apply (erule id_on_image[symmetric])
       apply (rule iffD2[OF image_in_bij_eq])
       apply assumption
       apply (rule DiffI[rotated])
       apply assumption
       apply (rule UN_I)
       apply assumption
       apply (unfold FVars_raw_defs mem_Collect_eq)[1]
       apply assumption
       apply assumption
       END TRY *)
       apply (erule FVars_raw_intros)
       apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD1, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1], (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold inv_id)?
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY *)
    apply (subst (asm) FVars_raw_permutes)
    apply (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (drule T2_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
    apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
    apply (erule T2_pre.mr_rel_set[rotated -1], (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+)+
    apply (unfold image_Un[symmetric])?
    apply (rotate_tac -1)
    apply (subst (asm) image_in_bij_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (subst (asm) inv_inv_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (unfold inv_simp1 inv_simp2)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule id_on_inv[THEN id_onD, rotated])
       apply assumption
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 3] 1\<close>)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
       apply (unfold id_on_Un)[1]
       apply (erule conjE)+
       apply (erule id_on_image[symmetric])
       apply (rule iffD2[OF image_in_bij_eq])
       apply assumption
       apply (rule DiffI[rotated])
       apply assumption
       apply (rule UN_I)
       apply assumption
       apply (unfold FVars_raw_defs mem_Collect_eq)[1]
       apply assumption
       apply assumption
       (* END TRY *)
       apply (erule FVars_raw_intros)
       apply assumption+
    (* END REPEAT_DETERM *)

    (* second goal, same proof again *)
        apply (rule free2_raw_T1_free2_raw_T2.induct)
    (* REPEAT_DETERM *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    (* TRY EVERY
    apply (drule DiffI[rotated])
    apply assumption
    apply (erule thin_rl)
    apply (rotate_tac -1)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF id_on_image[symmetric]], rotated -1])
    prefer 2
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF image_set_diff[OF bij_is_inj]], rotated -1])
    prefer 2
    END TRY *)
    apply (drule T1_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound | assumption)+
    apply (unfold inv_id)
    apply (rotate_tac -2)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
    apply (rule arg_cong2[of _ _ _ _ minus])?
    apply ((rule arg_cong[of _ _ "(`) _"])?, erule T1_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+)+
    apply (unfold image_comp)?
    apply ((subst (asm) inv_o_simp2, assumption)+)?
    apply (unfold image_id)
    apply (erule DiffE)?
    apply (erule FVars_raw_intros)
    (* TRY EVERY
    apply assumption
    apply assumption
    apply (erule id_on_antimono)
    apply (rule subsetI)
    apply (rotate_tac -1)
    apply (erule contrapos_pp)
    apply (unfold Un_iff de_Morgan_disj)[1]
    apply (erule conjE)+
    apply assumption
    END TRY *)
    (* END REPEAT_DETERM *)

    (* REPEAT_DETERM *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (frule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD1, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1], (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold inv_id)?
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY
    apply (subst (asm) FVars_raw_permutes)
    apply (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (drule T1_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
    apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
    apply (erule T1_pre.mr_rel_set[rotated -1], (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+)+
    apply (unfold image_Un[symmetric])?
    apply (rotate_tac -1)
    apply (subst (asm) image_in_bij_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (subst (asm) inv_inv_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (unfold inv_simp1 inv_simp2)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule id_on_inv[THEN id_onD, rotated])
       apply assumption
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
       apply (unfold id_on_Un)[1]
       apply (erule conjE)+
       apply (erule id_on_image[symmetric])
       apply (rule iffD2[OF image_in_bij_eq])
       apply assumption
       apply (rule DiffI[rotated])
       apply assumption
       apply (rule UN_I)
       apply assumption
       apply (unfold FVars_raw_defs mem_Collect_eq)[1]
       apply assumption
       apply assumption
       END TRY *)
       apply (erule FVars_raw_intros)
       apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (frule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD1, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1], (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold inv_id)?
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY *)
    apply (subst (asm) FVars_raw_permutes)
    apply (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (drule T1_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
    apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
    apply (erule T1_pre.mr_rel_set[rotated -1], (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+)+
    apply (unfold image_Un[symmetric])?
    apply (rotate_tac -1)
    apply (subst (asm) image_in_bij_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (subst (asm) inv_inv_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (unfold inv_simp1 inv_simp2)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule id_on_inv[THEN id_onD, rotated])
       apply assumption
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 1 1] 1\<close>)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
       apply (unfold id_on_Un)[1]
       apply (erule conjE)+
       apply (erule id_on_image[symmetric])
       apply (rule iffD2[OF image_in_bij_eq])
       apply assumption
       apply (rule DiffI[rotated])
       apply assumption
       apply (rule UN_I)
       apply assumption
       apply (unfold FVars_raw_defs mem_Collect_eq)[1]
       apply assumption
       apply assumption
       (* END TRY *)
       apply (erule FVars_raw_intros)
       apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (frule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD1, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1], (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold inv_id)?
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY
    apply (subst (asm) FVars_raw_permutes)
    apply (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (drule T1_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
    apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
    apply (erule T1_pre.mr_rel_set[rotated -1], (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+)+
    apply (unfold image_Un[symmetric])?
    apply (rotate_tac -1)
    apply (subst (asm) image_in_bij_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (subst (asm) inv_inv_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (unfold inv_simp1 inv_simp2)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule id_on_inv[THEN id_onD, rotated])
       apply assumption
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
       apply (unfold id_on_Un)[1]
       apply (erule conjE)+
       apply (erule id_on_image[symmetric])
       apply (rule iffD2[OF image_in_bij_eq])
       apply assumption
       apply (rule DiffI[rotated])
       apply assumption
       apply (rule UN_I)
       apply assumption
       apply (unfold FVars_raw_defs mem_Collect_eq)[1]
       apply assumption
       apply assumption
       END TRY *)
       apply (erule FVars_raw_intros)
       apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (frule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD1, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1], (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold inv_id)?
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY *)
    apply (subst (asm) FVars_raw_permutes)
    apply (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+
    apply (unfold image_id)
    (* TRY EVERY
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (drule T1_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
    apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
    apply (erule T1_pre.mr_rel_set[rotated -1], (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+)+
    apply (unfold image_Un[symmetric])?
    apply (rotate_tac -1)
    apply (subst (asm) image_in_bij_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (subst (asm) inv_inv_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (unfold inv_simp1 inv_simp2)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule id_on_inv[THEN id_onD, rotated])
       apply assumption
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 3] 1\<close>)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
       apply (unfold id_on_Un)[1]
       apply (erule conjE)+
       apply (erule id_on_image[symmetric])
       apply (rule iffD2[OF image_in_bij_eq])
       apply assumption
       apply (rule DiffI[rotated])
       apply assumption
       apply (rule UN_I)
       apply assumption
       apply (unfold FVars_raw_defs mem_Collect_eq)[1]
       apply assumption
       apply assumption
       END TRY *)
       (* END TRY *)
       apply (erule FVars_raw_intros)
       apply assumption+
    (* END REPEAT_DETERM *)
    (* second type, same tactic *)    (* REPEAT_DETERM *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    (* TRY EVERY
    apply (drule DiffI[rotated])
    apply assumption
    apply (erule thin_rl)
    apply (rotate_tac -1)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF id_on_image[symmetric]], rotated -1])
    prefer 2
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF image_set_diff[OF bij_is_inj]], rotated -1])
    prefer 2
    END TRY *)
    apply (drule T2_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound | assumption)+
    apply (unfold inv_id)
    apply (rotate_tac -2)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
    apply (rule arg_cong2[of _ _ _ _ minus])?
    apply ((rule arg_cong[of _ _ "(`) _"])?, erule T2_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+)+
    apply (unfold image_comp)?
    apply ((subst (asm) inv_o_simp2, assumption)+)?
    apply (unfold image_id)
    apply (erule DiffE)?
    apply (erule FVars_raw_intros)
    (* TRY EVERY
    apply assumption
    apply assumption
    apply (erule id_on_antimono)
    apply (rule subsetI)
    apply (rotate_tac -1)
    apply (erule contrapos_pp)
    apply (unfold Un_iff de_Morgan_disj)[1]
    apply (erule conjE)+
    apply assumption
    END TRY *)
    (* END REPEAT_DETERM *)

    (* REPEAT_DETERM *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD1, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1], (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold inv_id)?
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY
    apply (subst (asm) FVars_raw_permutes)
    apply (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (drule T1_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
    apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
    apply (erule T1_pre.mr_rel_set[rotated -1], (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+)+
    apply (unfold image_Un[symmetric])?
    apply (rotate_tac -1)
    apply (subst (asm) image_in_bij_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (subst (asm) inv_inv_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (unfold inv_simp1 inv_simp2)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule id_on_inv[THEN id_onD, rotated])
       apply assumption
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
       apply (unfold id_on_Un)[1]
       apply (erule conjE)+
       apply (erule id_on_image[symmetric])
       apply (rule iffD2[OF image_in_bij_eq])
       apply assumption
       apply (rule DiffI[rotated])
       apply assumption
       apply (rule UN_I)
       apply assumption
       apply (unfold FVars_raw_defs mem_Collect_eq)[1]
       apply assumption
       apply assumption
       END TRY *)
       apply (erule FVars_raw_intros)
       apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD1, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1], (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold inv_id)?
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY *)
    apply (subst (asm) FVars_raw_permutes)
    apply (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (drule T2_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
    apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
    apply (erule T2_pre.mr_rel_set[rotated -1], (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+)+
    apply (unfold image_Un[symmetric])?
    apply (rotate_tac -1)
    apply (subst (asm) image_in_bij_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (subst (asm) inv_inv_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (unfold inv_simp1 inv_simp2)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule id_on_inv[THEN id_onD, rotated])
       apply assumption
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 1 1] 1\<close>)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
       apply (unfold id_on_Un)[1]
       apply (erule conjE)+
       apply (erule id_on_image[symmetric])
       apply (rule iffD2[OF image_in_bij_eq])
       apply assumption
       apply (rule DiffI[rotated])
       apply assumption
       apply (rule UN_I)
       apply assumption
       apply (unfold FVars_raw_defs mem_Collect_eq)[1]
       apply assumption
       apply assumption
       (* END TRY *)
       apply (erule FVars_raw_intros)
       apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD1, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1], (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold inv_id)?
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY
    apply (subst (asm) FVars_raw_permutes)
    apply (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (drule T1_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
    apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
    apply (erule T1_pre.mr_rel_set[rotated -1], (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+)+
    apply (unfold image_Un[symmetric])?
    apply (rotate_tac -1)
    apply (subst (asm) image_in_bij_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (subst (asm) inv_inv_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (unfold inv_simp1 inv_simp2)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule id_on_inv[THEN id_onD, rotated])
       apply assumption
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
       apply (unfold id_on_Un)[1]
       apply (erule conjE)+
       apply (erule id_on_image[symmetric])
       apply (rule iffD2[OF image_in_bij_eq])
       apply assumption
       apply (rule DiffI[rotated])
       apply assumption
       apply (rule UN_I)
       apply assumption
       apply (unfold FVars_raw_defs mem_Collect_eq)[1]
       apply assumption
       apply assumption
       END TRY *)
       apply (erule FVars_raw_intros)
       apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD1, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1], (rule supp_id_bound bij_id | assumption)+)?
    apply (unfold inv_id)?
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY *)
    apply (subst (asm) FVars_raw_permutes)
    apply (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+
    apply (unfold image_id)
    (* TRY EVERY
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (drule T2_pre.mr_rel_flip[THEN iffD2, rotated -1])
    apply (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+
    apply ((rule arg_cong2[of _ _ _ _ "(\<union>)"])+)?
    apply (erule T2_pre.mr_rel_set[rotated -1], (rule bij_id supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound infinite_UNIV | assumption)+)+
    apply (unfold image_Un[symmetric])?
    apply (rotate_tac -1)
    apply (subst (asm) image_in_bij_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (subst (asm) inv_inv_eq)
    apply (rule bij_comp bij_imp_bij_inv | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (unfold inv_simp1 inv_simp2)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule id_on_inv[THEN id_onD, rotated])
       apply assumption
       apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 3] 1\<close>)
       apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<in>)"]])
       apply (unfold id_on_Un)[1]
       apply (erule conjE)+
       apply (erule id_on_image[symmetric])
       apply (rule iffD2[OF image_in_bij_eq])
       apply assumption
       apply (rule DiffI[rotated])
       apply assumption
       apply (rule UN_I)
       apply assumption
       apply (unfold FVars_raw_defs mem_Collect_eq)[1]
       apply assumption
       apply assumption
       END TRY *)
       (* END TRY *)
       apply (erule FVars_raw_intros)
       apply assumption+
    (* END REPEAT_DETERM *)
    done

lemma alpha_FVars_leqs2:
  fixes x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
  and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
shows
  "(free1_raw_T1 a x \<longrightarrow> (\<forall>y. alpha_T1 y x \<longrightarrow> a \<in> FVars_raw_T11 y)) \<and> (free1_raw_T2 a x2 \<longrightarrow> (\<forall>y2. alpha_T2 y2 x2 \<longrightarrow> a \<in> FVars_raw_T21 y2))"
  "(free2_raw_T1 a2 x \<longrightarrow> (\<forall>y. alpha_T1 y x \<longrightarrow> a2 \<in> FVars_raw_T12 y)) \<and> (free2_raw_T2 a2 x2 \<longrightarrow> (\<forall>y2. alpha_T2 y2 x2 \<longrightarrow> a2 \<in> FVars_raw_T22 y2))"
  apply (rule free1_raw_T1_free1_raw_T2.induct)
  (* REPEAT_DETERM *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    (* TRY EVERY
    apply (drule DiffI[rotated])
    apply assumption
    apply (erule thin_rl)
    apply (rotate_tac -1)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF id_on_image[symmetric]], rotated -1])
    prefer 2
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF image_set_diff[OF bij_is_inj]], rotated -1])
    prefer 2
    END TRY *)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
    apply (rule arg_cong2[of _ _ _ _ minus])?
    apply ((rule arg_cong[of _ _ "(`) _"])?, erule T1_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+)+
    apply (unfold image_comp)?
    apply ((subst (asm) inv_o_simp2, assumption)+)?
    apply (unfold image_id)
    apply (erule DiffE)?
    apply (erule FVars_raw_intros)
    (* TRY EVERY
    apply assumption
    apply assumption
    apply (erule id_on_antimono)
    apply (rule subsetI)
    apply (rotate_tac -1)
    apply (erule contrapos_pp)
    apply (unfold Un_iff de_Morgan_disj)[1]
    apply (erule conjE)+
    apply assumption
    END TRY *)
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    (* TRY EVERY *)
    apply (drule DiffI[rotated])
    apply assumption
    apply (erule thin_rl)
    apply (rotate_tac -1)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF id_on_image[symmetric]], rotated -1])
    prefer 2
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF image_set_diff[OF bij_is_inj]], rotated -1])
    prefer 2
    apply (rotate_tac -1)
    (* END TRY *)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
    apply (rule arg_cong2[of _ _ _ _ minus])?
    apply ((rule arg_cong[of _ _ "(`) _"])?, erule T1_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+)+
    apply (unfold image_comp)?
    apply ((subst (asm) inv_o_simp1, assumption)+)?
    apply (unfold image_id)
    apply (erule DiffE)?
    apply (erule FVars_raw_intros)
    (* TRY EVERY *)
    apply (rule bij_imp_bij_inv | assumption)+
    apply (rule id_on_inv)
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ id_on, THEN iffD2])
    apply (rule trans)
    apply (rule arg_cong2[of _ _ _ _ minus])
    apply (erule T1_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id | assumption)+)+
    apply (rule image_set_diff[symmetric, OF bij_is_inj])
    apply assumption
    apply (rule id_on_image_same)
    apply (erule id_on_antimono)
    apply (rule subsetI)
    apply (rotate_tac -1)
    apply (erule contrapos_pp)
    apply (unfold Un_iff de_Morgan_disj)[1]
    apply (erule conjE)+
    apply assumption
    (* END TRY *)
    (* END REPEAT_DETERM *)
    (* REPEAT_DETERM *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (frule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD2, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY
    apply (subst (asm) FVars_raw_permutes)
    apply assumption+
    apply (erule imageE)
    apply hypsubst
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (erule T1_pre.mr_rel_set[rotated -1])
    apply (rule supp_id_bound bij_id | assumption)+
    apply (subst (asm) inj_image_mem_iff[OF bij_is_inj])
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
    apply (erule id_onD)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
    apply (rule DiffI)
    apply (rule UN_I)
    apply assumption+
    END TRY *)
    apply (erule FVars_raw_intros)
    apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (frule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD2, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY *)
    apply (subst (asm) FVars_raw_permutes)
    apply assumption+
    apply (erule imageE)
    apply hypsubst
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (erule T1_pre.mr_rel_set[rotated -1])
    apply (rule supp_id_bound bij_id | assumption)+
    apply (rotate_tac -1)
    apply (subst (asm) inj_image_mem_iff[OF bij_is_inj])
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
    apply (erule id_onD)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
    apply (rule DiffI)
    apply (rule UN_I)
    apply assumption+
    (* END TRY *)
    apply (erule FVars_raw_intros)
    apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (frule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD2, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY
    apply (subst (asm) FVars_raw_permutes)
    apply assumption+
    apply (erule imageE)
    apply hypsubst
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (erule T1_pre.mr_rel_set[rotated -1])
    apply (rule supp_id_bound bij_id | assumption)+
    apply (subst (asm) inj_image_mem_iff[OF bij_is_inj])
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
    apply (erule id_onD)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
    apply (rule DiffI)
    apply (rule UN_I)
    apply assumption+
    END TRY *)
    apply (erule FVars_raw_intros)
    apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (frule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD2, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY *)
    apply (subst (asm) FVars_raw_permutes)
    apply (rule bij_id supp_id_bound | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (erule T1_pre.mr_rel_set[rotated -1])
    apply (rule supp_id_bound bij_id | assumption)+
    apply (subst (asm) inj_image_mem_iff[OF bij_is_inj])
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
    apply (erule id_onD)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 3] 1\<close>)
    apply (rule DiffI)
    apply (rule UN_I)
    apply assumption+
    (* END TRY *)
    apply (erule FVars_raw_intros)
    apply assumption+
    (* END REPEAT_DETERM *)
    (* second type, same tactic *)
    (* REPEAT_DETERM *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    (* TRY EVERY
    apply (drule DiffI[rotated])
    apply assumption
    apply (erule thin_rl)
    apply (rotate_tac -1)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF id_on_image[symmetric]], rotated -1])
    prefer 2
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF image_set_diff[OF bij_is_inj]], rotated -1])
    prefer 2
    END TRY *)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
    apply (rule arg_cong2[of _ _ _ _ minus])?
    apply ((rule arg_cong[of _ _ "(`) _"])?, erule T2_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+)+
    apply (unfold image_comp)?
    apply ((subst (asm) inv_o_simp2, assumption)+)?
    apply (unfold image_id)
    apply (erule DiffE)?
    apply (erule FVars_raw_intros)
    (* TRY EVERY
    apply assumption
    apply assumption
    apply (erule id_on_antimono)
    apply (rule subsetI)
    apply (rotate_tac -1)
    apply (erule contrapos_pp)
    apply (unfold Un_iff de_Morgan_disj)[1]
    apply (erule conjE)+
    apply assumption
    END TRY *)
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    (* TRY EVERY *)
    apply (drule DiffI[rotated])
    apply assumption
    apply (erule thin_rl)
    apply (rotate_tac -1)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF id_on_image[symmetric]], rotated -1])
    prefer 2
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF image_set_diff[OF bij_is_inj]], rotated -1])
    prefer 2
    apply (rotate_tac -1)
    (* END TRY *)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
    apply (rule arg_cong2[of _ _ _ _ minus])?
    apply ((rule arg_cong[of _ _ "(`) _"])?, erule T2_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+)+
    apply (unfold image_comp)?
    apply ((subst (asm) inv_o_simp1, assumption)+)?
    apply (unfold image_id)
    apply (erule DiffE)?
    apply (erule FVars_raw_intros)
    (* TRY EVERY *)
    apply (rule bij_imp_bij_inv | assumption)+
    apply (rule id_on_inv)
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ id_on, THEN iffD2])
    apply (rule trans)
    apply (rule arg_cong2[of _ _ _ _ minus])
    apply (erule T2_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id | assumption)+)+
    apply (rule image_set_diff[symmetric, OF bij_is_inj])
    apply assumption
    apply (rule id_on_image_same)
    apply (erule id_on_antimono)
    apply (rule subsetI)
    apply (rotate_tac -1)
    apply (erule contrapos_pp)
    apply (unfold Un_iff de_Morgan_disj)[1]
    apply (erule conjE)+
    apply assumption
    (* END TRY *)
    (* END REPEAT_DETERM *)
    (* REPEAT_DETERM *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD2, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY
    apply (subst (asm) FVars_raw_permutes)
    apply assumption+
    apply (erule imageE)
    apply hypsubst
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (erule T1_pre.mr_rel_set[rotated -1])
    apply (rule supp_id_bound bij_id | assumption)+
    apply (subst (asm) inj_image_mem_iff[OF bij_is_inj])
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
    apply (erule id_onD)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
    apply (rule DiffI)
    apply (rule UN_I)
    apply assumption+
    END TRY *)
    apply (erule FVars_raw_intros)
    apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD2, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY *)
    apply (subst (asm) FVars_raw_permutes)
    apply assumption+
    apply (erule imageE)
    apply hypsubst
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (erule T2_pre.mr_rel_set[rotated -1])
    apply (rule supp_id_bound bij_id | assumption)+
    apply (subst (asm) inj_image_mem_iff[OF bij_is_inj])
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
    apply (erule id_onD)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
    apply (rule DiffI)
    apply (rule UN_I)
    apply assumption+
    (* END TRY *)
    apply (erule FVars_raw_intros)
    apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD2, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY
    apply (subst (asm) FVars_raw_permutes)
    apply assumption+
    apply (erule imageE)
    apply hypsubst
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (erule T1_pre.mr_rel_set[rotated -1])
    apply (rule supp_id_bound bij_id | assumption)+
    apply (subst (asm) inj_image_mem_iff[OF bij_is_inj])
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
    apply (erule id_onD)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
    apply (rule DiffI)
    apply (rule UN_I)
    apply assumption+
    END TRY *)
    apply (erule FVars_raw_intros)
    apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD2, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY *)
    apply (subst (asm) FVars_raw_permutes)
    apply (rule bij_id supp_id_bound | assumption)+
    apply (erule imageE)
    apply hypsubst
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (erule T2_pre.mr_rel_set[rotated -1])
    apply (rule supp_id_bound bij_id | assumption)+
    apply (subst (asm) inj_image_mem_iff[OF bij_is_inj])
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
    apply (erule id_onD)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 3] 1\<close>)
    apply (rule DiffI)
    apply (rule UN_I)
    apply assumption+
    (* END TRY *)
    apply (erule FVars_raw_intros)
    apply assumption+
    (* END REPEAT_DETERM *)
    (* second goal, same tactic *)
    apply (rule free2_raw_T1_free2_raw_T2.induct)
  (* REPEAT_DETERM *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    (* TRY EVERY
    apply (drule DiffI[rotated])
    apply assumption
    apply (erule thin_rl)
    apply (rotate_tac -1)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF id_on_image[symmetric]], rotated -1])
    prefer 2
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF image_set_diff[OF bij_is_inj]], rotated -1])
    prefer 2
    END TRY *)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
    apply (rule arg_cong2[of _ _ _ _ minus])?
    apply ((rule arg_cong[of _ _ "(`) _"])?, erule T1_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+)+
    apply (unfold image_comp)?
    apply ((subst (asm) inv_o_simp2, assumption)+)?
    apply (unfold image_id)
    apply (erule DiffE)?
    apply (erule FVars_raw_intros)
    (* TRY EVERY
    apply assumption
    apply assumption
    apply (erule id_on_antimono)
    apply (rule subsetI)
    apply (rotate_tac -1)
    apply (erule contrapos_pp)
    apply (unfold Un_iff de_Morgan_disj)[1]
    apply (erule conjE)+
    apply assumption
    END TRY *)
    (* END REPEAT_DETERM *)
    (* REPEAT_DETERM *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (frule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD2, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY
    apply (subst (asm) FVars_raw_permutes)
    apply assumption+
    apply (erule imageE)
    apply hypsubst
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (erule T1_pre.mr_rel_set[rotated -1])
    apply (rule supp_id_bound bij_id | assumption)+
    apply (subst (asm) inj_image_mem_iff[OF bij_is_inj])
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
    apply (erule id_onD)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
    apply (rule DiffI)
    apply (rule UN_I)
    apply assumption+
    END TRY *)
    apply (erule FVars_raw_intros)
    apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (frule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD2, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY *)
    apply (subst (asm) FVars_raw_permutes)
    apply assumption+
    apply (erule imageE)
    apply hypsubst
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (erule T1_pre.mr_rel_set[rotated -1])
    apply (rule supp_id_bound bij_id | assumption)+
    apply (subst (asm) inj_image_mem_iff[OF bij_is_inj])
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
    apply (erule id_onD)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 1 1] 1\<close>)
    apply (rule DiffI)
    apply (rule UN_I)
    apply assumption+
    (* END TRY *)
    apply (erule FVars_raw_intros)
    apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (frule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD2, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY
    apply (subst (asm) FVars_raw_permutes)
    apply assumption+
    apply (erule imageE)
    apply hypsubst
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (erule T1_pre.mr_rel_set[rotated -1])
    apply (rule supp_id_bound bij_id | assumption)+
    apply (subst (asm) inj_image_mem_iff[OF bij_is_inj])
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
    apply (erule id_onD)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
    apply (rule DiffI)
    apply (rule UN_I)
    apply assumption+
    END TRY *)
    apply (erule FVars_raw_intros)
    apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (frule T1_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD2, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY *)
    apply (subst (asm) FVars_raw_permutes)
    apply (rule bij_id supp_id_bound | assumption)+
    apply (unfold image_id)?
    (* TRY EVERY
    apply (erule imageE)
    apply hypsubst
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (erule T1_pre.mr_rel_set[rotated -1])
    apply (rule supp_id_bound bij_id | assumption)+
    apply (subst (asm) inj_image_mem_iff[OF bij_is_inj])
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
    apply (erule id_onD)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 3] 1\<close>)
    apply (rule DiffI)
    apply (rule UN_I)
    apply assumption+
    END TRY *)
    apply (erule FVars_raw_intros)
    apply assumption+
    (* END REPEAT_DETERM *)
    (* second type, same tactic *)
    (* REPEAT_DETERM *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    (* TRY EVERY
    apply (drule DiffI[rotated])
    apply assumption
    apply (erule thin_rl)
    apply (rotate_tac -1)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF id_on_image[symmetric]], rotated -1])
    prefer 2
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)", OF image_set_diff[OF bij_is_inj]], rotated -1])
    prefer 2
    END TRY *)
    apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
    apply (rule arg_cong2[of _ _ _ _ minus])?
    apply ((rule arg_cong[of _ _ "(`) _"])?, erule T2_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound | assumption)+)+
    apply (unfold image_comp)?
    apply ((subst (asm) inv_o_simp2, assumption)+)?
    apply (unfold image_id)
    apply (erule DiffE)?
    apply (erule FVars_raw_intros)
    (* TRY EVERY
    apply assumption
    apply assumption
    apply (erule id_on_antimono)
    apply (rule subsetI)
    apply (rotate_tac -1)
    apply (erule contrapos_pp)
    apply (unfold Un_iff de_Morgan_disj)[1]
    apply (erule conjE)+
    apply assumption
    END TRY *)
    (* END REPEAT_DETERM *)
    (* REPEAT_DETERM *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD2, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY
    apply (subst (asm) FVars_raw_permutes)
    apply assumption+
    apply (erule imageE)
    apply hypsubst
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (erule T1_pre.mr_rel_set[rotated -1])
    apply (rule supp_id_bound bij_id | assumption)+
    apply (subst (asm) inj_image_mem_iff[OF bij_is_inj])
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
    apply (erule id_onD)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
    apply (rule DiffI)
    apply (rule UN_I)
    apply assumption+
    END TRY *)
    apply (erule FVars_raw_intros)
    apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD2, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY *)
    apply (subst (asm) FVars_raw_permutes)
    apply assumption+
    apply (erule imageE)
    apply hypsubst
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (erule T2_pre.mr_rel_set[rotated -1])
    apply (rule supp_id_bound bij_id | assumption)+
    apply (subst (asm) inj_image_mem_iff[OF bij_is_inj])
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
    apply (erule id_onD)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 1 1] 1\<close>)
    apply (rule DiffI)
    apply (rule UN_I)
    apply assumption+
    (* END TRY *)
    apply (erule FVars_raw_intros)
    apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD2, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY
    apply (subst (asm) FVars_raw_permutes)
    apply assumption+
    apply (erule imageE)
    apply hypsubst
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (erule T1_pre.mr_rel_set[rotated -1])
    apply (rule supp_id_bound bij_id | assumption)+
    apply (subst (asm) inj_image_mem_iff[OF bij_is_inj])
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
    apply (erule id_onD)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
    apply (rule DiffI)
    apply (rule UN_I)
    apply assumption+
    END TRY *)
    apply (erule FVars_raw_intros)
    apply assumption+
    (* repeated *)
    apply (rule allI impI)+
    apply (erule alpha_T2.cases)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_set_transfer(8-11)[THEN rel_funD, rotated -1, THEN rel_setD2, rotated -1])
    apply assumption
    apply (rule supp_id_bound bij_id | assumption)+
    apply (erule bexE)
    apply (erule allE)
    apply (erule impE)
    apply assumption
    (* TRY EVERY *)
    apply (subst (asm) FVars_raw_permutes)
    apply (rule bij_id supp_id_bound | assumption)+
    apply (unfold image_id)?
    (* TRY EVERY
    apply (erule imageE)
    apply hypsubst
    apply (frule arg_cong2[OF refl, of _ _ "(\<notin>)", THEN iffD1, rotated -1])
    apply (erule T2_pre.mr_rel_set[rotated -1])
    apply (rule supp_id_bound bij_id | assumption)+
    apply (subst (asm) inj_image_mem_iff[OF bij_is_inj])
    apply assumption
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
    apply (erule id_onD)
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 3] 1\<close>)
    apply (rule DiffI)
    apply (rule UN_I)
    apply assumption+
    END TRY *)
    apply (erule FVars_raw_intros)
    apply assumption+
    (* END REPEAT_DETERM *)
    done

lemma alpha_FVars:
  fixes x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
  shows
    "alpha_T1 x y \<Longrightarrow> FVars_raw_T11 x = FVars_raw_T11 y"
    "alpha_T1 x y \<Longrightarrow> FVars_raw_T12 x = FVars_raw_T12 y"
    "alpha_T2 x2 y2 \<Longrightarrow> FVars_raw_T21 x2 = FVars_raw_T21 y2"
    "alpha_T2 x2 y2 \<Longrightarrow> FVars_raw_T22 x2 = FVars_raw_T22 y2"
    (* REPEAT_DETERM *)
    apply (rule subset_antisym)
    apply (rule subsetI)
    apply (erule alpha_FVars_leqs1[THEN conjunct1, THEN mp, THEN spec, THEN mp, rotated -1]
        alpha_FVars_leqs1[THEN conjunct2, THEN mp, THEN spec, THEN mp, rotated -1])
    apply (unfold FVars_raw_defs mem_Collect_eq)[1]
    apply assumption
    apply (rule subsetI)
    apply (erule alpha_FVars_leqs2[THEN conjunct1, THEN mp, THEN spec, THEN mp, rotated -1]
        alpha_FVars_leqs2[THEN conjunct2, THEN mp, THEN spec, THEN mp, rotated -1])
    apply (unfold FVars_raw_defs mem_Collect_eq)[1]
    apply assumption
    (* repeated *)
    apply (rule subset_antisym)
    apply (rule subsetI)
    apply (erule alpha_FVars_leqs1[THEN conjunct1, THEN mp, THEN spec, THEN mp, rotated -1]
        alpha_FVars_leqs1[THEN conjunct2, THEN mp, THEN spec, THEN mp, rotated -1])
    apply (unfold FVars_raw_defs mem_Collect_eq)[1]
    apply assumption
    apply (rule subsetI)
    apply (erule alpha_FVars_leqs2[THEN conjunct1, THEN mp, THEN spec, THEN mp, rotated -1]
        alpha_FVars_leqs2[THEN conjunct2, THEN mp, THEN spec, THEN mp, rotated -1])
    apply (unfold FVars_raw_defs mem_Collect_eq)[1]
    apply assumption
    (* repeated *)
    apply (rule subset_antisym)
    apply (rule subsetI)
    apply (erule alpha_FVars_leqs1[THEN conjunct1, THEN mp, THEN spec, THEN mp, rotated -1]
        alpha_FVars_leqs1[THEN conjunct2, THEN mp, THEN spec, THEN mp, rotated -1])
    apply (unfold FVars_raw_defs mem_Collect_eq)[1]
    apply assumption
    apply (rule subsetI)
    apply (erule alpha_FVars_leqs2[THEN conjunct1, THEN mp, THEN spec, THEN mp, rotated -1]
        alpha_FVars_leqs2[THEN conjunct2, THEN mp, THEN spec, THEN mp, rotated -1])
    apply (unfold FVars_raw_defs mem_Collect_eq)[1]
    apply assumption
    (* repeated *)
    apply (rule subset_antisym)
    apply (rule subsetI)
    apply (erule alpha_FVars_leqs1[THEN conjunct1, THEN mp, THEN spec, THEN mp, rotated -1]
        alpha_FVars_leqs1[THEN conjunct2, THEN mp, THEN spec, THEN mp, rotated -1])
    apply (unfold FVars_raw_defs mem_Collect_eq)[1]
    apply assumption
    apply (rule subsetI)
    apply (erule alpha_FVars_leqs2[THEN conjunct1, THEN mp, THEN spec, THEN mp, rotated -1]
        alpha_FVars_leqs2[THEN conjunct2, THEN mp, THEN spec, THEN mp, rotated -1])
    apply (unfold FVars_raw_defs mem_Collect_eq)[1]
    apply assumption
    (* END REPEAT_DETERM *)
    done

lemma alpha_syms:
  fixes x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
  shows
    "alpha_T1 x y \<Longrightarrow> alpha_T1 y x"
    "alpha_T2 x2 y2 \<Longrightarrow> alpha_T2 y2 x2"
proof -
  have x: "(\<forall>(x::('a, 'b, 'c, 'd) raw_T1) y. alpha_T1 y x \<longrightarrow> alpha_T1 x y) \<and> (\<forall>(x::('a, 'b, 'c, 'd) raw_T2) y. alpha_T2 y x \<longrightarrow> alpha_T2 x y)"
    apply (rule alpha_T1_alpha_T2.coinduct)
     apply (erule alpha_T1.cases)
     apply hypsubst
     apply (rule exI)+
     apply (rule conjI, rule refl)+
     apply (rule conjI[rotated])+
           apply (rule iffD1[OF T1_pre.mr_rel_flip, rotated -1])
                     apply (unfold inv_id conversep_eq)
                     apply (erule T1_pre.mr_rel_mono_strong0[rotated -12])
                        apply (rule ballI, rule refl)+
                        apply (rule ballI, rule ballI, rule impI, assumption)+
                        apply (rule ballI, rule inv_inv_eq[THEN fun_cong, symmetric], assumption)+
      (* REPEAT_DETERM *)
                        apply (rule ballI)
                        apply (rule ballI)
                        apply (rule impI)
                        apply (rule conversepI)
                        apply (rule disjI1)
                        apply (assumption | (erule alpha_bij_eq_invs[THEN iffD1, rotated -1], assumption+))
      (* repeated *)
                        apply (rule ballI)
                        apply (rule ballI)
                        apply (rule impI)
                        apply (rule conversepI)
                        apply (rule disjI1)
                        apply (assumption | (erule alpha_bij_eq_invs[THEN iffD1, rotated -1], assumption+))
      (* repeated *)
                        apply (rule ballI)
                        apply (rule ballI)
                        apply (rule impI)
                        apply (rule conversepI)
                        apply (rule disjI1)
                        apply (assumption | (erule alpha_bij_eq_invs[THEN iffD1, rotated -1], assumption+))
      (* repeated *)
                        apply (rule ballI)
                        apply (rule ballI)
                        apply (rule impI)
                        apply (rule conversepI)
                        apply (rule disjI1)
                        apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1])
                        apply (assumption | rule supp_id_bound bij_id)+
                        apply (unfold inv_id)
                        apply assumption
                        apply (assumption | rule supp_id_bound bij_id)+
      (* END REPEAT_DETERM *)
                        apply (unfold inv_inv_eq)
                        apply (assumption | rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound)+
      (* REPEAT_DETERM *)
          apply (rule id_on_inv)
           apply assumption
          apply (rule id_on_antimono)
           apply assumption
          apply (rule equalityD1)
          apply (rule sym)
          apply (rule trans)
           apply (rule id_on_image[symmetric])
           prefer 2
           apply (rule trans)
            apply (rule image_set_diff[OF bij_is_inj])
            prefer 2
            apply (rule arg_cong2[of _ _ _ _ minus, rotated])
             apply (rule sym)
             apply (erule T1_pre.mr_rel_set[rotated -1])
                   apply (rule supp_id_bound bij_id | assumption)+
            apply (rule trans)
             apply (rule image_UN)
            apply (rule rel_set_UN_D)
            apply (erule T1_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF T1_pre.mr_rel_mono_strong[rotated -6]])
      (* REPEAT_DETERM *)
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* ORELSE *)
                        apply (rule ballI impI)+
                        apply (rule trans[rotated])
                        apply (erule alpha_FVars)
                        apply (rule sym)
                        apply (rule FVars_raw_permutes)
                        apply (assumption | rule supp_id_bound bij_id)+
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* END REPEAT_DETERM *)
                        apply (assumption | rule supp_id_bound bij_id)+
      (* repeated *)
         apply (rule id_on_inv)
          apply assumption
         apply (rule id_on_antimono)
          apply assumption
         apply (rule equalityD1)
         apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
       (* REPEAT_DETERM *)
       apply (rule trans)
       apply (rule arg_cong2[of _ _ _ _ minus])
       apply (erule T1_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id | assumption)+)+
       apply (rule trans)
       apply (rule image_set_diff[OF bij_is_inj, symmetric])
       apply assumption
       apply (rule id_on_image)
       apply (erule id_on_antimono)
       apply (rule subsetI)
       apply (rotate_tac -1)
       apply (erule contrapos_pp)
       apply (unfold Un_iff de_Morgan_disj)[1]
       apply (erule conjE)+
       apply assumption
       (* END REPEAT_DETERM *)
      (* REPEAT_DETERM *)
          apply (rule sym)
          apply (rule trans)
           apply (rule id_on_image[symmetric])
           prefer 2
           apply (rule trans)
            apply (rule image_set_diff[OF bij_is_inj])
            prefer 2
            apply (rule arg_cong2[of _ _ _ _ minus, rotated])
             apply (rule sym)
             apply (erule T1_pre.mr_rel_set[rotated -1])
                   apply (rule supp_id_bound bij_id | assumption)+
            apply (rule trans)
             apply (rule image_UN)
            apply (rule rel_set_UN_D)
            apply (erule T1_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF T1_pre.mr_rel_mono_strong[rotated -6]])
      (* REPEAT_DETERM *)
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* ORELSE *)
                        apply (rule ballI impI)+
                        apply (rule trans[rotated])
                        apply (erule alpha_FVars)
                        apply (rule sym)
                        apply (rule FVars_raw_permutes)
                        apply (assumption | rule supp_id_bound bij_id)+
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* END REPEAT_DETERM *)
                        apply (assumption | rule supp_id_bound bij_id)+
          apply (erule id_on_antimono)
         apply (rule subsetI)
         apply (rotate_tac -1)
         apply (erule contrapos_pp)
         apply (unfold Un_iff de_Morgan_disj)[1]
         apply (erule conjE)+
         apply assumption
      (* repeated *)
         apply (rule sym)
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          prefer 2
          apply (rule trans)
           apply (rule image_set_diff[OF bij_is_inj])
           prefer 2
           apply (rule arg_cong2[of _ _ _ _ minus, rotated])
            apply (rule sym)
            apply (erule T1_pre.mr_rel_set[rotated -1])
                  apply (rule supp_id_bound bij_id | assumption)+
           apply (rule trans)
            apply (rule image_UN)
           apply (rule rel_set_UN_D)
           apply (erule T1_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF T1_pre.mr_rel_mono_strong[rotated -6]])
      (* REPEAT_DETERM *)
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* ORELSE *)
                        apply (rule ballI impI)+
                        apply (rule trans[rotated])
                        apply (erule alpha_FVars)
                        apply (rule sym)
                        apply (rule FVars_raw_permutes)
                        apply (assumption | rule supp_id_bound bij_id)+
      (* END REPEAT_DETERM *)
         apply ((assumption | rule supp_id_bound bij_id)+)?
         apply (erule id_on_antimono)
         apply (rule subsetI)
         apply (rotate_tac -1)
         apply (erule contrapos_pp)
         apply (unfold Un_iff de_Morgan_disj)[1]
         apply (erule conjE)+
         apply assumption
      (* END REPEAT_DETERM *)
      (* END REPEAT_DETERM *)
        apply (rule supp_inv_bound bij_imp_bij_inv | assumption)+

(* second goal, same tactic *)
    apply (erule alpha_T2.cases)
    apply hypsubst
    apply (rule exI)+
    apply (rule conjI, rule refl)+
    apply (rule conjI[rotated])+
          apply (rule iffD1[OF T2_pre.mr_rel_flip, rotated -1])
                    apply (unfold inv_id conversep_eq)
                    apply (erule T2_pre.mr_rel_mono_strong0[rotated -12])
                        apply (rule ballI, rule refl)+
                        apply (rule ballI, rule ballI, rule impI, assumption)+
                        apply (rule ballI, rule inv_inv_eq[THEN fun_cong, symmetric], assumption)+
      (* REPEAT_DETERM *)
                        apply (rule ballI)
                        apply (rule ballI)
                        apply (rule impI)
                        apply (rule conversepI)
                        apply (rule disjI1)
                        apply (assumption | (erule alpha_bij_eq_invs[THEN iffD1, rotated -1], assumption+))
      (* repeated *)
                        apply (rule ballI)
                        apply (rule ballI)
                        apply (rule impI)
                        apply (rule conversepI)
                        apply (rule disjI1)
                        apply (assumption | (erule alpha_bij_eq_invs[THEN iffD1, rotated -1], assumption+))
      (* repeated *)
                        apply (rule ballI)
                        apply (rule ballI)
                        apply (rule impI)
                        apply (rule conversepI)
                        apply (rule disjI1)
                        apply (assumption | (erule alpha_bij_eq_invs[THEN iffD1, rotated -1], assumption+))
      (* repeated *)
                        apply (rule ballI)
                        apply (rule ballI)
                        apply (rule impI)
                        apply (rule conversepI)
                        apply (rule disjI1)
                        apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1])
                        apply (assumption | rule supp_id_bound bij_id)+
                        apply (unfold inv_id)
                        apply assumption
                        apply (assumption | rule supp_id_bound bij_id)+
      (* END REPEAT_DETERM *)
                       apply (unfold inv_inv_eq)
                       apply (assumption | rule supp_id_bound bij_id bij_imp_bij_inv supp_inv_bound)+
      (* REPEAT_DETERM *)
         apply (rule id_on_inv)
          apply assumption
         apply (rule id_on_antimono)
          apply assumption
         apply (rule equalityD1)
         apply (rule sym)
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          prefer 2
          apply (rule trans)
           apply (rule image_set_diff[OF bij_is_inj])
           prefer 2
           apply (rule arg_cong2[of _ _ _ _ minus, rotated])
            apply (rule sym)
            apply (erule T2_pre.mr_rel_set[rotated -1])
                  apply (rule supp_id_bound bij_id | assumption)+
           apply (rule trans)
            apply (rule image_UN)
           apply (rule rel_set_UN_D)
           apply (erule T2_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF T2_pre.mr_rel_mono_strong[rotated -6]])
      (* REPEAT_DETERM *)
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* ORELSE *)
                        apply (rule ballI impI)+
                        apply (rule trans[rotated])
                        apply (erule alpha_FVars)
                        apply (rule sym)
                        apply (rule FVars_raw_permutes)
                        apply (assumption | rule supp_id_bound bij_id)+
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* END REPEAT_DETERM *)
                        apply (assumption | rule supp_id_bound bij_id)+
      (* repeated *)
        apply (rule id_on_inv)
         apply assumption
        apply (rule id_on_antimono)
         apply assumption
        apply (rule equalityD1)
        apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
      (* REPEAT_DETERM *)
      apply (rule trans)
      apply (rule arg_cong2[of _ _ _ _ minus])
      apply (erule T2_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id | assumption)+)+
      apply (rule trans)
      apply (rule image_set_diff[OF bij_is_inj, symmetric])
      apply assumption
      apply (rule id_on_image)
      apply (erule id_on_antimono)
       apply (rule subsetI)
       apply (rotate_tac -1)
       apply (erule contrapos_pp)
       apply (unfold Un_iff de_Morgan_disj)[1]
       apply (erule conjE)+
       apply assumption
      (* END REPEAT_DETERM *)
      (* REPEAT_DETERM *)
         apply (rule sym)
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          prefer 2
          apply (rule trans)
           apply (rule image_set_diff[OF bij_is_inj])
           prefer 2
           apply (rule arg_cong2[of _ _ _ _ minus, rotated])
            apply (rule sym)
            apply (erule T2_pre.mr_rel_set[rotated -1])
                  apply (rule supp_id_bound bij_id | assumption)+
           apply (rule trans)
            apply (rule image_UN)
           apply (rule rel_set_UN_D)
           apply (erule T2_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF T2_pre.mr_rel_mono_strong[rotated -6]])
      (* REPEAT_DETERM *)
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* ORELSE *)
                        apply (rule ballI impI)+
                        apply (rule trans[rotated])
                        apply (erule alpha_FVars)
                        apply (rule sym)
                        apply (rule FVars_raw_permutes)
                        apply (assumption | rule supp_id_bound bij_id)+
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* END REPEAT_DETERM *)
                        apply (assumption | rule supp_id_bound bij_id)+
         apply (erule id_on_antimono)
         apply (rule subsetI)
         apply (rotate_tac -1)
         apply (erule contrapos_pp)
         apply (unfold Un_iff de_Morgan_disj)[1]
         apply (erule conjE)+
         apply assumption
      (* repeated *)
        apply (rule sym)
        apply (rule trans)
         apply (rule id_on_image[symmetric])
         prefer 2
         apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj])
          prefer 2
          apply (rule arg_cong2[of _ _ _ _ minus, rotated])
           apply (rule sym)
           apply (erule T2_pre.mr_rel_set[rotated -1])
                 apply (rule supp_id_bound bij_id | assumption)+
          apply (rule trans)
           apply (rule image_UN)
          apply (rule rel_set_UN_D)
          apply (erule T2_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF T2_pre.mr_rel_mono_strong[rotated -6]])
      (* REPEAT_DETERM *)
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* ORELSE *)
                        apply (rule ballI impI)+
                        apply (rule trans[rotated])
                        apply (erule alpha_FVars)
                        apply (rule sym)
                        apply (rule FVars_raw_permutes)
                        apply (assumption | rule supp_id_bound bij_id)+
      (* END REPEAT_DETERM *)
        apply ((assumption | rule supp_id_bound bij_id)+)?
        apply (erule id_on_antimono)
        apply (rule Un_upper1 Un_upper2 subset_refl)+
      (* END REPEAT_DETERM *)
      (* END REPEAT_DETERM *)
       apply (rule supp_inv_bound bij_imp_bij_inv | assumption)+
    done

  show "alpha_T1 x y \<Longrightarrow> alpha_T1 y x" "alpha_T2 x2 y2 \<Longrightarrow> alpha_T2 y2 x2"
     apply (erule conjunct1[OF x, THEN spec, THEN spec, THEN mp])
    apply (erule conjunct2[OF x, THEN spec, THEN spec, THEN mp])
    done
qed


lemma alpha_trans:
  fixes x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
  shows
    "alpha_T1 x y \<Longrightarrow> alpha_T1 y z \<Longrightarrow> alpha_T1 x z"
    "alpha_T2 x2 y2 \<Longrightarrow> alpha_T2 y2 z2 \<Longrightarrow> alpha_T2 x2 z2"
proof -
  have x: "(\<forall>(x::('a, 'b, 'c, 'd) raw_T1) z. (\<exists>y. alpha_T1 x y \<and> alpha_T1 y z) \<longrightarrow> alpha_T1 x z)
  \<and> (\<forall>(x::('a, 'b, 'c, 'd) raw_T2) z. (\<exists>y. alpha_T2 x y \<and> alpha_T2 y z) \<longrightarrow> alpha_T2 x z)"
    apply (rule alpha_T1_alpha_T2.coinduct)
     apply (erule exE)
     apply (erule conjE)
     apply (erule alpha_T1.cases)+
     apply hypsubst
     apply (drule iffD1[OF raw_T1.inject])
     apply hypsubst
     apply (frule T1_pre.mr_rel_OO[THEN fun_cong, THEN fun_cong, THEN iffD2, rotated -1, OF relcomppI])
                    apply assumption
                   apply (rule supp_id_bound bij_id | assumption)+
     apply (unfold id_o o_id eq_OO)
     apply (rule exI)+
     apply (rule conjI, rule refl)+
     apply (rule conjI[rotated])+
           apply (erule T1_pre.mr_rel_mono_strong[rotated -6])
                      apply (rule ballI, rule ballI, rule impI, assumption)+
      (* REPEAT_DETERM *)
                     apply (rule ballI)
                     apply (rule ballI)
                     apply (rule impI)
                     apply (rule disjI1)
                     apply (erule relcomppE)
                     apply (rule exI)
                     apply (rule conjI)
                      apply assumption+
      (* repeated *)
                    apply (rule ballI)
                    apply (rule ballI)
                    apply (rule impI)
                    apply (rule disjI1)
                    apply (erule relcomppE)
                    apply (subst permute_raw_comps[symmetric])
                        apply assumption+
                    apply (subst alpha_bij_eq_invs)
                        apply assumption+
                    apply (rule exI)
                    apply (rule conjI[rotated])
                     apply assumption
                    apply (subst permute_raw_comps)
                        apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
                    apply (subst inv_o_simp1, assumption)+
                    apply (unfold permute_raw_ids)
                    apply assumption
      (* repeated *)
                   apply (rule ballI)
                   apply (rule ballI)
                   apply (rule impI)
                   apply (rule disjI1)
                   apply (erule relcomppE)
                   apply (rule exI)
                   apply (rule conjI)
                    apply assumption+
      (* repeated *)
                  apply (rule ballI)
                  apply (rule ballI)
                  apply (rule impI)
                  apply (rule disjI1)
                  apply (erule relcomppE)
                  apply (subst id_hid_o_hid)+
                  apply (unfold hidden_id_def)
                  apply (subst permute_raw_comps[symmetric])
                        apply (assumption | rule supp_id_bound bij_id)+
                  apply (subst alpha_bij_eq_invs)
                      apply (assumption | rule bij_id supp_id_bound)+
                  apply (rule exI)
                  apply (rule conjI[rotated])
                   apply assumption
                  apply (subst permute_raw_comps)
                        apply (assumption | rule bij_imp_bij_inv supp_inv_bound supp_id_bound bij_id)+
                  apply (subst inv_o_simp1, assumption)+
                  apply (unfold permute_raw_ids inv_id id_o)
                  apply assumption
      (* END REPEAT_DETERM *)
                 apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | assumption)+
      (* REPEAT_DETERM *)
          apply (rule id_on_comp)
           apply (erule id_on_antimono) (* reuses tactic from alpha_sym *)
           apply (rule equalityD1)
           apply (rule trans)
            apply (rule id_on_image[symmetric])
            prefer 2
            apply (rule trans)
             apply (rule image_set_diff[OF bij_is_inj])
             prefer 2
             apply (rule arg_cong2[of _ _ _ _ minus, rotated])
              apply (rule sym)
              apply (erule T1_pre.mr_rel_set[rotated -1])
                    apply (rule supp_id_bound bij_id | assumption)+
             apply (rule trans)
              apply (rule image_UN)
             apply (rule rel_set_UN_D)
             apply (erule T1_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF T1_pre.mr_rel_mono_strong[rotated -6]])
      (* REPEAT_DETERM *)
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* ORELSE *)
                        apply (rule ballI impI)+
                        apply (rule trans[rotated])
                        apply (erule alpha_FVars)
                        apply (rule sym)
                        apply (rule FVars_raw_permutes)
                        apply (assumption | rule supp_id_bound bij_id)+
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* END REPEAT_DETERM *)
                        apply (assumption | rule supp_id_bound bij_id)+
      (* repeated *)
         apply (rule id_on_comp)
          apply (erule id_on_antimono) (* reuses tactic from alpha_sym *)
          apply (rule equalityD1)
          apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
          (* REPEAT_DETERM *)
          apply (rule sym)
          apply (rule trans)
          apply (rule arg_cong2[of _ _ _ _ minus])
          apply (erule T1_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id | assumption)+)+
          apply (rule trans)
          apply (rule image_set_diff[OF bij_is_inj, symmetric])
          apply assumption
          apply (rule id_on_image)
          apply (erule id_on_antimono)
           apply (rule subsetI)
           apply (rotate_tac -1)
           apply (erule contrapos_pp)
           apply (unfold Un_iff de_Morgan_disj)[1]
           apply (erule conjE)+
           apply assumption
          (* END REPEAT_DETERM *)
      (* REPEAT_DETERM *)
           apply (rule trans)
            apply (rule id_on_image[symmetric])
            prefer 2
            apply (rule trans)
             apply (rule image_set_diff[OF bij_is_inj])
             prefer 2
             apply (rule arg_cong2[of _ _ _ _ minus, rotated])
              apply (rule sym)
              apply (erule T1_pre.mr_rel_set[rotated -1])
                    apply (rule supp_id_bound bij_id | assumption)+
             apply (rule trans)
              apply (rule image_UN)
             apply (rule rel_set_UN_D)
             apply (erule T1_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF T1_pre.mr_rel_mono_strong[rotated -6]])
      (* REPEAT_DETERM *)
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* ORELSE *)
                        apply (rule ballI impI)+
                        apply (rule trans[rotated])
                        apply (erule alpha_FVars)
                        apply (rule sym)
                        apply (rule FVars_raw_permutes)
                        apply (assumption | rule supp_id_bound bij_id)+
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* END REPEAT_DETERM *)
                        apply (assumption | rule supp_id_bound bij_id)+
           apply (erule id_on_antimono)
           apply (rule subsetI)
           apply (rotate_tac -1)
           apply (erule contrapos_pp)
           apply (unfold Un_iff de_Morgan_disj)[1]
           apply (erule conjE)+
           apply assumption
      (*repeated *)
          apply (rule trans)
           apply (rule id_on_image[symmetric])
           prefer 2
           apply (rule trans)
            apply (rule image_set_diff[OF bij_is_inj])
            prefer 2
            apply (rule arg_cong2[of _ _ _ _ minus, rotated])
             apply (rule sym)
             apply (erule T1_pre.mr_rel_set[rotated -1])
                   apply (rule supp_id_bound bij_id | assumption)+
            apply (rule trans)
             apply (rule image_UN)
            apply (rule rel_set_UN_D)
            apply (erule T1_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF T1_pre.mr_rel_mono_strong[rotated -6]])
      (* REPEAT_DETERM *)
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* ORELSE *)
                        apply (rule ballI impI)+
                        apply (rule trans[rotated])
                        apply (erule alpha_FVars)
                        apply (rule sym)
                        apply (rule FVars_raw_permutes)
                        apply (assumption | rule supp_id_bound bij_id)+
      (* END REPEAT_DETERM *)
          apply (erule id_on_antimono)
           apply (rule subsetI)
           apply (rotate_tac -1)
           apply (erule contrapos_pp)
           apply (unfold Un_iff de_Morgan_disj)[1]
           apply (erule conjE)+
           apply assumption
         apply assumption
      (* END REPEAT_DETERM *)
        apply (rule supp_comp_bound bij_comp infinite_UNIV | assumption)+

(* second goal, same tactic *)
    apply (erule exE)
    apply (erule conjE)
    apply (erule alpha_T2.cases)+
    apply hypsubst
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (frule T2_pre.mr_rel_OO[THEN fun_cong, THEN fun_cong, THEN iffD2, rotated -1, OF relcomppI])
                   apply assumption
                  apply (rule supp_id_bound bij_id | assumption)+
    apply (unfold id_o o_id eq_OO)
    apply (rule exI)+
    apply (rule conjI, rule refl)+
    apply (rule conjI[rotated])+
          apply (erule T2_pre.mr_rel_mono_strong[rotated -6])
                     apply (rule ballI, rule ballI, rule impI, assumption)+
      (* REPEAT_DETERM *)
                    apply (rule ballI)
                    apply (rule ballI)
                    apply (rule impI)
                    apply (rule disjI1)
                    apply (erule relcomppE)
                    apply (rule exI)
                    apply (rule conjI)
                     apply assumption+
      (* repeated *)
                   apply (rule ballI)
                   apply (rule ballI)
                   apply (rule impI)
                   apply (rule disjI1)
                   apply (erule relcomppE)
                   apply (subst permute_raw_comps[symmetric])
                        apply assumption+
                   apply (subst alpha_bij_eq_invs)
                       apply assumption+
                   apply (rule exI)
                   apply (rule conjI[rotated])
                    apply assumption
                   apply (subst permute_raw_comps)
                        apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
                   apply (subst inv_o_simp1, assumption)+
                   apply (unfold permute_raw_ids)
                   apply assumption
      (* repeated *)
                  apply (rule ballI)
                  apply (rule ballI)
                  apply (rule impI)
                  apply (rule disjI1)
                  apply (erule relcomppE)
                  apply (rule exI)
                  apply (rule conjI)
                   apply assumption+
      (* repeated *)
                 apply (rule ballI)
                 apply (rule ballI)
                 apply (rule impI)
                 apply (rule disjI1)
                 apply (erule relcomppE)
                 apply (subst id_hid_o_hid)+
                 apply (unfold hidden_id_def)
                 apply (subst permute_raw_comps[symmetric])
                       apply (assumption | rule supp_id_bound bij_id)+
                 apply (subst alpha_bij_eq_invs)
                     apply (assumption | rule bij_id supp_id_bound)+
                 apply (rule exI)
                 apply (rule conjI[rotated])
                  apply assumption
                 apply (subst permute_raw_comps)
                        apply (assumption | rule bij_imp_bij_inv supp_inv_bound supp_id_bound bij_id)+
                 apply (subst inv_o_simp1, assumption)+
                 apply (unfold permute_raw_ids inv_id id_o)
                 apply assumption
      (* END REPEAT_DETERM *)
                apply (rule supp_id_bound bij_id bij_comp supp_comp_bound infinite_UNIV | assumption)+
      (* REPEAT_DETERM *)
         apply (rule id_on_comp)
          apply (erule id_on_antimono) (* reuses tactic from alpha_sym *)
          apply (rule equalityD1)
          apply (rule trans)
           apply (rule id_on_image[symmetric])
           prefer 2
           apply (rule trans)
            apply (rule image_set_diff[OF bij_is_inj])
            prefer 2
            apply (rule arg_cong2[of _ _ _ _ minus, rotated])
             apply (rule sym)
             apply (erule T2_pre.mr_rel_set[rotated -1])
                   apply (rule supp_id_bound bij_id | assumption)+
            apply (rule trans)
             apply (rule image_UN)
            apply (rule rel_set_UN_D)
            apply (erule T2_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF T2_pre.mr_rel_mono_strong[rotated -6]])
      (* REPEAT_DETERM *)
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* ORELSE *)
                        apply (rule ballI impI)+
                        apply (rule trans[rotated])
                        apply (erule alpha_FVars)
                        apply (rule sym)
                        apply (rule FVars_raw_permutes)
                        apply (assumption | rule supp_id_bound bij_id)+
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* END REPEAT_DETERM *)
                        apply (assumption | rule supp_id_bound bij_id)+
      (* repeated *)
        apply (rule id_on_comp)
         apply (erule id_on_antimono) (* reuses tactic from alpha_sym *)
         apply (rule equalityD1)
         apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
        (* REPEAT_DETERM *)
        apply (rule sym)
        apply (rule trans)
        apply (rule arg_cong2[of _ _ _ _ minus])
        apply (erule T2_pre.mr_rel_set[rotated -1], (rule supp_id_bound bij_id | assumption)+)+
        apply (rule trans)
        apply (rule image_set_diff[OF bij_is_inj, symmetric])
        apply assumption
        apply (rule id_on_image)
        apply (erule id_on_antimono)
         apply (rule subsetI)
         apply (rotate_tac -1)
         apply (erule contrapos_pp)
         apply (unfold Un_iff de_Morgan_disj)[1]
         apply (erule conjE)+
         apply assumption
        (* END REPEAT_DETERM *)
      (* REPEAT_DETERM *)
          apply (rule trans)
           apply (rule id_on_image[symmetric])
           prefer 2
           apply (rule trans)
            apply (rule image_set_diff[OF bij_is_inj])
            prefer 2
            apply (rule arg_cong2[of _ _ _ _ minus, rotated])
             apply (rule sym)
             apply (erule T2_pre.mr_rel_set[rotated -1])
                   apply (rule supp_id_bound bij_id | assumption)+
            apply (rule trans)
             apply (rule image_UN)
            apply (rule rel_set_UN_D)
            apply (erule T2_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF T2_pre.mr_rel_mono_strong[rotated -6]])
      (* REPEAT_DETERM *)
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* ORELSE *)
                        apply (rule ballI impI)+
                        apply (rule trans[rotated])
                        apply (erule alpha_FVars)
                        apply (rule sym)
                        apply (rule FVars_raw_permutes)
                        apply (assumption | rule supp_id_bound bij_id)+
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* END REPEAT_DETERM *)
                        apply (assumption | rule supp_id_bound bij_id)+
          apply (erule id_on_antimono)
         apply (rule subsetI)
         apply (rotate_tac -1)
         apply (erule contrapos_pp)
         apply (unfold Un_iff de_Morgan_disj)[1]
         apply (erule conjE)+
         apply assumption
      (*repeated *)
         apply (rule trans)
          apply (rule id_on_image[symmetric])
          prefer 2
          apply (rule trans)
           apply (rule image_set_diff[OF bij_is_inj])
           prefer 2
           apply (rule arg_cong2[of _ _ _ _ minus, rotated])
            apply (rule sym)
            apply (erule T2_pre.mr_rel_set[rotated -1])
                  apply (rule supp_id_bound bij_id | assumption)+
           apply (rule trans)
            apply (rule image_UN)
           apply (rule rel_set_UN_D)
           apply (erule T2_pre.mr_set_transfer[THEN rel_funD, rotated -1, OF T2_pre.mr_rel_mono_strong[rotated -6]])
      (* REPEAT_DETERM *)
                        apply (rule ballI, rule ballI, rule impI, assumption)+
      (* ORELSE *)
                        apply (rule ballI impI)+
                        apply (rule trans[rotated])
                        apply (erule alpha_FVars)
                        apply (rule sym)
                        apply (rule FVars_raw_permutes)
                        apply (assumption | rule supp_id_bound bij_id)+
      (* END REPEAT_DETERM *)
         apply (erule id_on_antimono)
         apply (rule subsetI)
         apply (rotate_tac -1)
         apply (erule contrapos_pp)
         apply (unfold Un_iff de_Morgan_disj)[1]
         apply (erule conjE)+
         apply assumption
        apply assumption
      (* END REPEAT_DETERM *)
       apply (rule supp_comp_bound bij_comp infinite_UNIV | assumption)+
    done

  show "alpha_T1 x y \<Longrightarrow> alpha_T1 y z \<Longrightarrow> alpha_T1 x z" "alpha_T2 x2 y2 \<Longrightarrow> alpha_T2 y2 z2 \<Longrightarrow> alpha_T2 x2 z2"
     apply (rule conjunct1[OF x, THEN spec, THEN spec, THEN mp])
     apply (rule exI)
     apply (rule conjI)
      apply assumption+
    apply (rule conjunct2[OF x, THEN spec, THEN spec, THEN mp])
    apply (rule exI)
    apply (rule conjI)
     apply assumption+
    done
qed

lemma raw_refreshs:
  fixes x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1'"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2'"
  assumes "|A| <o |UNIV::'a set|" "|B| <o |UNIV::'b set|"
  shows
    "\<exists>y. set5_T1_pre y \<inter> A = {} \<and> set6_T1_pre y \<inter> B = {} \<and> alpha_T1 (raw_T1_ctor x) (raw_T1_ctor y)"
    "\<exists>y. set5_T2_pre y \<inter> A = {} \<and> set6_T2_pre y \<inter> B = {} \<and> alpha_T2 (raw_T2_ctor x2) (raw_T2_ctor y)"
   apply (rule exE[OF eextend_fresh[of "set5_T1_pre x" "A \<union> ((set7_T1_pre x - set5_T1_pre x) \<union> (\<Union>(FVars_raw_T11 ` set9_T1_pre x) - set5_T1_pre x) \<union> (\<Union>(FVars_raw_T21 ` set11_T1_pre x) - set5_T1_pre x))" "(set7_T1_pre x - set5_T1_pre x) \<union> (\<Union>(FVars_raw_T11 ` set9_T1_pre x) - set5_T1_pre x) \<union> (\<Union>(FVars_raw_T21 ` set11_T1_pre x) - set5_T1_pre x)"]])
        apply (rule T1_pre.set_bd_UNIV)
       apply (rule var_T1_pre_class.Un_bound)
        apply (rule assms)
    (* REPEAT_DETERM *)
       apply (rule var_T1_pre_class.Un_bound)+
        apply (rule ordLeq_ordLess_trans[OF card_of_diff])
        apply (rule var_T1_pre_class.UN_bound)?
         apply (rule ordLess_ordLeq_trans)
          apply (rule T1_pre.set_bd)
         apply (rule var_T1_pre_class.large)
        apply (rule FVars_raw_bd_UNIVs)?
    (* repeated *)
       apply (rule ordLeq_ordLess_trans[OF card_of_diff])
       apply (rule var_T1_pre_class.UN_bound)
        apply (rule ordLess_ordLeq_trans)
         apply (rule T1_pre.set_bd)
        apply (rule var_T1_pre_class.large)
        apply (rule FVars_raw_bd_UNIVs)
   (* repeated *)
      apply (rule ordLeq_ordLess_trans[OF card_of_diff])
      apply (rule var_T1_pre_class.UN_bound)?
       apply (rule ordLess_ordLeq_trans)
        apply (rule T1_pre.set_bd)
       apply (rule var_T1_pre_class.large)
      apply (rule FVars_raw_bd_UNIVs)?
    (* repeated *)
    (* END REPEAT_DETERM *)
    apply (rule infinite_UNIV)
    apply (unfold Un_assoc)
     apply (rule Un_upper2)
    apply (unfold Un_Diff[symmetric])?
    apply (rule Diff_disjoint)
   apply (erule conjE)+
    (* repeated *)
   apply (rule exE[OF eextend_fresh[of "set6_T1_pre x" "B \<union> (\<Union>(FVars_raw_T12 ` set9_T1_pre x) - set6_T1_pre x)" "(\<Union>(FVars_raw_T12 ` set9_T1_pre x) - set6_T1_pre x)"]])
        apply (rule T1_pre.set_bd_UNIV)
       apply (rule var_T1_pre_class.Un_bound)
        apply (rule assms)
    (* REPEAT_DETERM *)
       apply (rule var_T1_pre_class.Un_bound)?
       apply (rule ordLeq_ordLess_trans[OF card_of_diff])
       apply (rule var_T1_pre_class.UN_bound)
        apply (rule ordLess_ordLeq_trans)
         apply (rule T1_pre.set_bd)
        apply (rule var_T1_pre_class.large)
       apply (rule FVars_raw_bd_UNIVs)
    (* END REPEAT_DETERM *)
      apply (rule infinite_UNIV)
     apply (rule Un_upper2)
    apply (unfold Un_Diff[symmetric])?
    apply (rule Diff_disjoint)
   apply (erule conjE)+

  subgoal for f1 f2
    apply (rule exI[of _ "map_T1_pre id id id id f1 f2 f1 id (permute_raw_T1 f1 f2) id (permute_raw_T2 f1 id) x"])
    apply (subst T1_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
      (* REPEAT_DETERM *)
    apply (rule conjI)
     apply (erule Int_subset_empty2)
     apply (rule Un_upper1)
      (* repeated *)
    apply (rule conjI)
     apply (erule Int_subset_empty2)
     apply (rule Un_upper1)
      (* END REPEAT_DETERM *)
    apply (rule alpha_T1_alpha_T2.intros[rotated -1])
          apply (rule iffD2[OF T1_pre.mr_rel_map(3), rotated -1])
                        apply (unfold inv_id id_o o_id eq_OO conversep_eq relcompp_conversep_Grp)
                        apply (subst inv_o_simp1, assumption)+
                        apply (subst id_apply)+
                        apply (rule iffD1[OF T1_pre.mr_rel_id[THEN fun_cong, THEN fun_cong]])
                        apply (rule T1_pre.rel_refl_strong)
                        apply (rule refl alpha_refls)+
                        apply (rule supp_id_bound bij_id | assumption)+
     apply (unfold Un_Diff Un_assoc)
     apply assumption+
    done

(* second goal, same tactic *)
  apply (rule exE[OF eextend_fresh[of "set5_T2_pre x2" "A \<union> ((set7_T2_pre x2 - set5_T2_pre x2) \<union> (\<Union>(FVars_raw_T11 ` set9_T2_pre x2) - set5_T2_pre x2) \<union> (\<Union>(FVars_raw_T21 ` set11_T2_pre x2) - set5_T2_pre x2))" "(set7_T2_pre x2 - set5_T2_pre x2) \<union> (\<Union>(FVars_raw_T11 ` set9_T2_pre x2) - set5_T2_pre x2) \<union> (\<Union>(FVars_raw_T21 ` set11_T2_pre x2) - set5_T2_pre x2)"]])
       apply (rule T2_pre.set_bd_UNIV)
      apply (rule var_T1_pre_class.Un_bound)
       apply (rule assms)
      apply (rule var_T1_pre_class.Un_bound)+
    (* REPEAT_DETERM *)
       apply (rule ordLeq_ordLess_trans[OF card_of_diff])
       apply (rule var_T1_pre_class.UN_bound)?
        apply (rule ordLess_ordLeq_trans)
         apply (rule T2_pre.set_bd)
        apply (rule var_T1_pre_class.large)
       apply (rule FVars_raw_bd_UNIVs)?
    (* repeated *)
       apply (rule ordLeq_ordLess_trans[OF card_of_diff])
       apply (rule var_T1_pre_class.UN_bound)?
        apply (rule ordLess_ordLeq_trans)
         apply (rule T2_pre.set_bd)
        apply (rule var_T1_pre_class.large)
       apply (rule FVars_raw_bd_UNIVs)?
    (* repeated *)
      apply (rule ordLeq_ordLess_trans[OF card_of_diff])
      apply (rule var_T1_pre_class.UN_bound)
       apply (rule ordLess_ordLeq_trans)
        apply (rule T2_pre.set_bd)
       apply (rule var_T1_pre_class.large)
      apply (rule FVars_raw_bd_UNIVs)
    (* END REPEAT_DETERM *)
     apply (rule infinite_UNIV)
    apply (rule Un_upper2)
   apply (unfold Un_Diff[symmetric])?
   apply (rule Diff_disjoint)
  apply (erule conjE)+
    (* repeated *)
  apply (rule exE[OF eextend_fresh[of "set6_T2_pre x2" "B \<union> (\<Union>(FVars_raw_T12 ` set9_T2_pre x2) - set6_T2_pre x2)" "(\<Union>(FVars_raw_T12 ` set9_T2_pre x2) - set6_T2_pre x2)"]])
       apply (rule T2_pre.set_bd_UNIV)
      apply (rule var_T1_pre_class.Un_bound)
       apply (rule assms)
    (* REPEAT_DETERM *)
      apply (rule var_T1_pre_class.Un_bound)?
      apply (rule ordLeq_ordLess_trans[OF card_of_diff])
      apply (rule var_T1_pre_class.UN_bound)
       apply (rule ordLess_ordLeq_trans)
        apply (rule T2_pre.set_bd)
       apply (rule var_T1_pre_class.large)
      apply (rule FVars_raw_bd_UNIVs)
    (* END REPEAT_DETERM *)
     apply (rule infinite_UNIV)
    apply (rule Un_upper2)
   apply (unfold Un_Diff[symmetric])?
   apply (rule Diff_disjoint)
  apply (erule conjE)+

  subgoal for f1 f2
    apply (rule exI[of _ "map_T2_pre id id id id f1 f2 f1 id (permute_raw_T1 f1 f2) id (permute_raw_T2 f1 id) x2"])
    apply (subst T2_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
      (* REPEAT_DETERM *)
    apply (rule conjI)
     apply (erule Int_subset_empty2)
     apply (rule Un_upper1)
      (* repeated *)
    apply (rule conjI)
     apply (erule Int_subset_empty2)
     apply (rule Un_upper1)
      (* END REPEAT_DETERM *)
    apply (rule alpha_T1_alpha_T2.intros[rotated -1])
          apply (rule iffD2[OF T2_pre.mr_rel_map(3), rotated -1])
                        apply (unfold inv_id id_o o_id eq_OO conversep_eq relcompp_conversep_Grp)
                        apply (subst inv_o_simp1, assumption)+
                        apply (subst id_apply)+
                        apply (rule iffD1[OF T2_pre.mr_rel_id[THEN fun_cong, THEN fun_cong]])
                        apply (rule T2_pre.rel_refl_strong)
                        apply (rule refl alpha_refls)+
                        apply (rule supp_id_bound bij_id | assumption)+
     apply (unfold Un_Diff)
     apply assumption+
    done
  done

lemma avoid_raw_freshs:
  fixes x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1'"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2'"
  assumes "|A| <o |UNIV::'a set|" "|B| <o |UNIV::'b set|"
  shows "set5_T1_pre (avoid_raw_T1 x A B) \<inter> A = {}" "set6_T1_pre (avoid_raw_T1 x A B) \<inter> B = {}"
    "set5_T2_pre (avoid_raw_T2 x2 A B) \<inter> A = {}" "set6_T2_pre (avoid_raw_T2 x2 A B) \<inter> B = {}"
     apply (unfold avoid_raw_T1_def avoid_raw_T2_def)
    (* REPEAT_DETERM *)
     apply (rule someI2_ex)
      apply (rule raw_refreshs[OF assms])
     apply (erule conjE)+
     apply assumption
    (* repeated *)
    apply (rule someI2_ex)
     apply (rule raw_refreshs[OF assms])
    apply (erule conjE)+
    apply assumption
    (* repeated *)
   apply (rule someI2_ex)
    apply (rule raw_refreshs[OF assms])
   apply (erule conjE)+
   apply assumption
    (* repeated *)
  apply (rule someI2_ex)
   apply (rule raw_refreshs[OF assms])
  apply (erule conjE)+
  apply assumption
    (* END REPEAT_DETERM *)
  done

lemma TT_Quotients:
  "Quotient alpha_T1 TT1_abs TT1_rep (\<lambda>x. (=) (TT1_abs x))"
  "Quotient alpha_T2 TT2_abs TT2_rep (\<lambda>x. (=) (TT2_abs x))"
   apply (subgoal_tac "Quotient3 alpha_T1 TT1_abs TT1_rep")
    prefer 2
    apply (rule quot_type.Quotient)
    apply (rule type_definition_quot_type)
    apply (rule type_definition_T1)
    apply (rule equivpI)
    apply (rule reflpI)
    apply (rule alpha_refls)
    apply (rule sympI)
    apply (erule alpha_syms)
    apply (rule transpI)
    apply (erule alpha_trans)
    apply assumption
   apply (rule QuotientI)
      apply (erule Quotient3_abs_rep)
     apply (rule alpha_refls)
    apply (erule Quotient3_rel[symmetric])
   apply (rule ext)+
   apply (rule iffI)
    apply (rule conjI)
     apply (rule alpha_refls)
    apply assumption
   apply (erule conjE)
   apply assumption
    (* second goal, same tactic *)
  apply (subgoal_tac "Quotient3 alpha_T2 TT2_abs TT2_rep")
   prefer 2
   apply (rule quot_type.Quotient)
   apply (rule type_definition_quot_type)
    apply (rule type_definition_T2)
    apply (rule equivpI)
    apply (rule reflpI)
    apply (rule alpha_refls)
    apply (rule sympI)
    apply (erule alpha_syms)
    apply (rule transpI)
    apply (erule alpha_trans)
    apply assumption
  apply (rule QuotientI)
     apply (erule Quotient3_abs_rep)
    apply (rule alpha_refls)
   apply (erule Quotient3_rel[symmetric])
  apply (rule ext)+
  apply (rule iffI)
   apply (rule conjI)
    apply (rule alpha_refls)
   apply assumption
  apply (erule conjE)
  apply assumption
  done

lemmas TT_total_abs_eq_iffs = TT_Quotients(1)[THEN Quotient_total_abs_eq_iff, OF reflpI[OF alpha_refls(1)]]
  TT_Quotients(2)[THEN Quotient_total_abs_eq_iff, OF reflpI[OF alpha_refls(2)]]
lemmas TT_rep_abs = TT_Quotients(1)[THEN Quotient_rep_abs, OF alpha_refls(1)] TT_Quotients(2)[THEN Quotient_rep_abs, OF alpha_refls(2)]
lemmas TT_abs_rep = TT_Quotients[THEN Quotient_abs_rep]

lemmas TT_rep_abs_syms = alpha_syms(1)[OF TT_rep_abs(1)] alpha_syms(2)[OF TT_rep_abs(2)]

lemma TT_abs_ctors:
  "TT1_abs (raw_T1_ctor x) = T1_ctor (map_T1_pre id id id id id id id TT1_abs TT1_abs TT2_abs TT2_abs x)"
  "TT2_abs (raw_T2_ctor x2) = T2_ctor (map_T2_pre id id id id id id id TT1_abs TT1_abs TT2_abs TT2_abs x2)"
   apply (unfold T1_ctor_def T2_ctor_def)
   apply (rule TT_total_abs_eq_iffs[THEN iffD2])
   apply (rule alpha_T1_alpha_T2.intros)
         apply (rule supp_id_bound bij_id id_on_id)+
   apply (unfold permute_raw_ids)
   apply (subst T1_pre.map_comp)
        apply (rule supp_id_bound bij_id)+
   apply (unfold id_o o_id)
   apply (rule iffD2[OF T1_pre.mr_rel_map(3)])
                    apply (rule supp_id_bound bij_id)+
   apply (unfold inv_id id_o o_id Grp_UNIV_id eq_OO conversep_eq relcompp_conversep_Grp)
   apply (rule iffD1[OF T1_pre.mr_rel_id[THEN fun_cong, THEN fun_cong]])
   apply (unfold comp_def)
   apply (rule T1_pre.rel_refl_strong)
       apply (rule refl)+
      apply (rule alpha_syms, rule TT_rep_abs)+
  (* second goal, same tactic *)
   apply (rule TT_total_abs_eq_iffs[THEN iffD2])
   apply (rule alpha_T1_alpha_T2.intros)
         apply (rule supp_id_bound bij_id id_on_id)+
   apply (unfold permute_raw_ids)
   apply (subst T2_pre.map_comp)
        apply (rule supp_id_bound bij_id)+
   apply (unfold id_o o_id)
   apply (rule iffD2[OF T2_pre.mr_rel_map(3)])
                    apply (rule supp_id_bound bij_id)+
   apply (unfold inv_id id_o o_id Grp_UNIV_id eq_OO conversep_eq relcompp_conversep_Grp)
   apply (rule iffD1[OF T2_pre.mr_rel_id[THEN fun_cong, THEN fun_cong]])
   apply (unfold comp_def)
   apply (rule T2_pre.rel_refl_strong)
       apply (rule refl)+
     apply (rule alpha_syms, rule TT_rep_abs)+
  done

lemma permute_simps:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows
    "permute_T1 f1 f2 (T1_ctor x) = T1_ctor (map_T1_pre f1 f2 id id f1 f2 f1 (permute_T1 f1 f2) (permute_T1 f1 f2) (permute_T2 f1 f2) (permute_T2 f1 f2) x)"
    "permute_T2 f1 f2 (T2_ctor x2) = T2_ctor (map_T2_pre f1 f2 id id f1 f2 f1 (permute_T1 f1 f2) (permute_T1 f1 f2) (permute_T2 f1 f2) (permute_T2 f1 f2) x2)"
   apply (unfold T1_ctor_def T2_ctor_def permute_T1_def permute_T2_def)
   apply (subst T1_pre.map_comp, (rule supp_id_bound bij_id assms)+)
   apply (unfold id_o o_id)
   apply (unfold comp_def)
   apply (rule TT_total_abs_eq_iffs[THEN iffD2])
   apply (rule alpha_bij_eq_invs[OF assms, THEN iffD2])
   apply (subst permute_raw_simps)
       apply (rule bij_imp_bij_inv supp_inv_bound assms)+
   apply (subst T1_pre.map_comp)
            apply (rule bij_imp_bij_inv supp_inv_bound assms supp_id_bound bij_id)+
   apply (subst inv_o_simp1, rule assms)+
   apply (unfold id_o o_id)
   apply (rule alpha_trans)
    apply (rule TT_rep_abs)
   apply (unfold comp_def)
   apply (rule alpha_T1_alpha_T2.intros)
         apply (rule bij_id supp_id_bound id_on_id)+
   apply (rule iffD2[OF T1_pre.mr_rel_map(1)])
                 apply (rule supp_id_bound bij_id)+
   apply (unfold id_o o_id Grp_UNIV_id eq_OO)
   apply (rule iffD2[OF T1_pre.mr_rel_map(3)])
                    apply (rule supp_id_bound bij_id)+
   apply (unfold inv_id id_o o_id Grp_UNIV_id conversep_eq eq_OO relcompp_conversep_Grp)
   apply (unfold Grp_OO)
   apply (rule iffD1[OF T1_pre.mr_rel_id[THEN fun_cong, THEN fun_cong]])
   apply (rule T1_pre.rel_refl_strong)
       apply (rule refl)+
      apply (unfold permute_raw_ids)
    (* REPEAT_DETERM *)
      apply (rule alpha_bij_eq_invs[THEN iffD1])
          apply (rule assms supp_id_bound bij_id)+
      apply (rule alpha_syms)
      apply (rule TT_rep_abs)
    (* repeated *)
     apply (rule alpha_bij_eq_invs[THEN iffD1])
         apply (rule assms supp_id_bound bij_id)+
     apply (rule alpha_syms)
     apply (rule TT_rep_abs)
    (* repeated *)
    apply (rule alpha_bij_eq_invs[THEN iffD1])
        apply (rule assms supp_id_bound bij_id)+
    apply (rule alpha_syms)
    apply (rule TT_rep_abs)
    (* repeated *)
   apply (rule alpha_bij_eq_invs[THEN iffD1])
       apply (rule assms supp_id_bound bij_id)+
   apply (rule alpha_syms)
   apply (rule TT_rep_abs)
    (* END REPEAT_DETERM *)
    (* second goal, same tactic *)
  apply (subst T2_pre.map_comp, (rule supp_id_bound bij_id assms)+)
  apply (unfold id_o o_id)
  apply (unfold comp_def)
  apply (rule TT_total_abs_eq_iffs[THEN iffD2])
  apply (rule alpha_bij_eq_invs[OF assms, THEN iffD2])
  apply (subst permute_raw_simps)
      apply (rule bij_imp_bij_inv supp_inv_bound assms)+
  apply (subst T2_pre.map_comp)
           apply (rule bij_imp_bij_inv supp_inv_bound assms supp_id_bound bij_id)+
  apply (subst inv_o_simp1, rule assms)+
  apply (unfold id_o o_id)
  apply (rule alpha_trans)
   apply (rule TT_rep_abs)
  apply (unfold comp_def)
  apply (rule alpha_T1_alpha_T2.intros)
        apply (rule bij_id supp_id_bound id_on_id)+
  apply (rule iffD2[OF T2_pre.mr_rel_map(1)])
                apply (rule supp_id_bound bij_id)+
  apply (unfold id_o o_id Grp_UNIV_id eq_OO)
  apply (rule iffD2[OF T2_pre.mr_rel_map(3)])
                   apply (rule supp_id_bound bij_id)+
  apply (unfold inv_id id_o o_id Grp_UNIV_id conversep_eq eq_OO relcompp_conversep_Grp)
  apply (unfold Grp_OO)
  apply (rule iffD1[OF T2_pre.mr_rel_id[THEN fun_cong, THEN fun_cong]])
  apply (rule T2_pre.rel_refl_strong)
      apply (rule refl)+
     apply (unfold permute_raw_ids)
    (* REPEAT_DETERM *)
     apply (rule alpha_bij_eq_invs[THEN iffD1])
         apply (rule assms supp_id_bound bij_id)+
     apply (rule alpha_syms)
     apply (rule TT_rep_abs)
    (* repeated *)
    apply (rule alpha_bij_eq_invs[THEN iffD1])
        apply (rule assms supp_id_bound bij_id)+
    apply (rule alpha_syms)
    apply (rule TT_rep_abs)
    (* repeated *)
   apply (rule alpha_bij_eq_invs[THEN iffD1])
       apply (rule assms supp_id_bound bij_id)+
   apply (rule alpha_syms)
   apply (rule TT_rep_abs)
    (* repeated *)
  apply (rule alpha_bij_eq_invs[THEN iffD1])
      apply (rule assms supp_id_bound bij_id)+
  apply (rule alpha_syms)
  apply (rule TT_rep_abs)
    (* END REPEAT_DETERM *)
done

lemma permute_ids:
  "permute_T1 id id x = x"
  "permute_T2 id id x2 = x2"
  apply (unfold permute_T1_def permute_T2_def permute_raw_ids TT_abs_rep)
  apply (rule refl)+
  done

lemmas permute_id0s = permute_ids[THEN trans[OF _ id_apply[symmetric]], abs_def, THEN meta_eq_to_obj_eq]

lemma permute_comps:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
    and g1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and g2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
    and "bij g1" "|supp g1| <o |UNIV::'a set|" "bij g2" "|supp g2| <o |UNIV::'b set|"
  shows
    "permute_T1 g1 g2 (permute_T1 f1 f2 x) = permute_T1 (g1 \<circ> f1) (g2 \<circ> f2) x"
    "permute_T2 g1 g2 (permute_T2 f1 f2 x2) = permute_T2 (g1 \<circ> f1) (g2 \<circ> f2) x2"
    apply (unfold permute_T1_def permute_T2_def)
    apply (subst permute_raw_comps[symmetric])
    apply (rule assms)+
    apply (rule TT_total_abs_eq_iffs[THEN iffD2])
    apply (rule alpha_bij_eqs[THEN iffD2])
    apply (rule assms)+
    apply (rule TT_rep_abs)
   (* second goal, same tactic *)
    apply (subst permute_raw_comps[symmetric])
    apply (rule assms)+
    apply (rule TT_total_abs_eq_iffs[THEN iffD2])
    apply (rule alpha_bij_eqs[THEN iffD2])
    apply (rule assms)+
    apply (rule TT_rep_abs)
    done

lemma permute_comp0s:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
    and g1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and g2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
    and "bij g1" "|supp g1| <o |UNIV::'a set|" "bij g2" "|supp g2| <o |UNIV::'b set|"
  shows
    "permute_T1 g1 g2 \<circ> permute_T1 f1 f2 = permute_T1 (g1 \<circ> f1) (g2 \<circ> f2)"
    "permute_T2 g1 g2 \<circ> permute_T2 f1 f2 = permute_T2 (g1 \<circ> f1) (g2 \<circ> f2)"
    apply (rule ext)
    apply (rule trans[OF comp_apply])
    apply (rule permute_comps[OF assms])
    apply (rule ext)
    apply (rule trans[OF comp_apply])
    apply (rule permute_comps[OF assms])
    done

lemma permute_bijs:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows "bij (permute_T1 f1 f2)" "bij (permute_T2 f1 f2)"
  apply (unfold bij_iff)
  apply (rule exI)
  apply (rule conjI)
  apply (rule trans)
  apply (rule permute_comp0s)
  prefer 9 (* 4 * nvars + 1 *)
  apply (subst inv_o_simp1, rule assms)+
  apply (rule permute_id0s)
  apply (rule assms bij_imp_bij_inv supp_inv_bound)+
  apply (rule trans)
  apply (rule permute_comp0s)
  apply (rule assms bij_imp_bij_inv supp_inv_bound)+
  apply (subst inv_o_simp2, rule assms)+
  apply (rule permute_id0s)
  (* second goal, same tactic *)
  apply (rule exI)
  apply (rule conjI)
  apply (rule trans)
  apply (rule permute_comp0s)
  prefer 9 (* 4 * nvars + 1 *)
  apply (subst inv_o_simp1, rule assms)+
  apply (rule permute_id0s)
  apply (rule assms bij_imp_bij_inv supp_inv_bound)+
  apply (rule trans)
  apply (rule permute_comp0s)
  apply (rule assms bij_imp_bij_inv supp_inv_bound)+
  apply (subst inv_o_simp2, rule assms)+
  apply (rule permute_id0s)
  done

lemma permute_inv_simps:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows
    "inv (permute_T1 f1 f2) = permute_T1 (inv f1) (inv f2)"
    "inv (permute_T2 f1 f2) = permute_T2 (inv f1) (inv f2)"
    (* REPEAT_DETERM *)
    apply (rule inv_unique_comp)?
    apply (rule trans)
    apply (rule permute_comp0s)
    apply (rule supp_inv_bound bij_imp_bij_inv assms)+
    apply (subst inv_o_simp1 inv_o_simp2, rule assms)+
    apply (rule permute_id0s)
    (* repeated *)
    apply (rule inv_unique_comp)?
    apply (rule trans)
    apply (rule permute_comp0s)
    apply (rule supp_inv_bound bij_imp_bij_inv assms)+
    apply (subst inv_o_simp1 inv_o_simp2, rule assms)+
    apply (rule permute_id0s)
    (* repeated *)
    apply (rule inv_unique_comp)?
    apply (rule trans)
    apply (rule permute_comp0s)
    apply (rule supp_inv_bound bij_imp_bij_inv assms)+
    apply (subst inv_o_simp1 inv_o_simp2, rule assms)+
    apply (rule permute_id0s)
    (* repeated *)
    apply (rule inv_unique_comp)?
    apply (rule trans)
    apply (rule permute_comp0s)
    apply (rule supp_inv_bound bij_imp_bij_inv assms)+
    apply (subst inv_o_simp1 inv_o_simp2, rule assms)+
    apply (rule permute_id0s)
    (* END REPEAT_DETERM *)
    done


lemma FVars_bds:
  "|FVars_T11 x| <o natLeq"
  "|FVars_T12 x| <o natLeq"
  "|FVars_T21 x2| <o natLeq"
  "|FVars_T22 x2| <o natLeq"
     apply (unfold FVars_defs)
     apply (rule FVars_raw_bds)+
  done

lemma FVars_bd_UNIVs:
  fixes x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2"
  shows
    "|FVars_T11 x| <o |UNIV::'a set|"
    "|FVars_T12 x| <o |UNIV::'b set|"
    "|FVars_T21 x2| <o |UNIV::'a set|"
    "|FVars_T22 x2| <o |UNIV::'b set|"
     apply (unfold FVars_defs)
     apply (rule FVars_raw_bd_UNIVs)+
  done

lemma FVars_permutes:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
    and x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows
    "FVars_T11 (permute_T1 f1 f2 x) = f1 ` FVars_T11 x"
    "FVars_T12 (permute_T1 f1 f2 x) = f2 ` FVars_T12 x"
    "FVars_T21 (permute_T2 f1 f2 x2) = f1 ` FVars_T21 x2"
    "FVars_T22 (permute_T2 f1 f2 x2) = f2 ` FVars_T22 x2"
     apply (unfold FVars_defs permute_T1_def permute_T2_def)
    (* REPEAT_DETERM *)
     apply (rule trans)
      apply (rule alpha_FVars)
      apply (rule TT_rep_abs)
     apply (rule FVars_raw_permutes[OF assms])
    (* repeated *)
    apply (rule trans)
     apply (rule alpha_FVars)
     apply (rule TT_rep_abs)
    apply (rule FVars_raw_permutes[OF assms])
    (* repeated *)
   apply (rule trans)
    apply (rule alpha_FVars)
    apply (rule TT_rep_abs)
   apply (rule FVars_raw_permutes[OF assms])
    (* repeated *)
  apply (rule trans)
   apply (rule alpha_FVars)
   apply (rule TT_rep_abs)
  apply (rule FVars_raw_permutes[OF assms])
    (* END REPEAT_DETERM *)
  done

lemma FVars_ctors:
  "FVars_T11 (T1_ctor x) = set1_T1_pre x \<union> (set7_T1_pre x - set5_T1_pre x) \<union> \<Union>(FVars_T11 ` set8_T1_pre x)
    \<union> (\<Union>(FVars_T11 ` set9_T1_pre x) - set5_T1_pre x) \<union> \<Union>(FVars_T21 ` set10_T1_pre x)
    \<union> (\<Union>(FVars_T21 ` set11_T1_pre x) - set5_T1_pre x)"
  "FVars_T12 (T1_ctor x) = set2_T1_pre x \<union> \<Union>(FVars_T12 ` set8_T1_pre x)
    \<union> (\<Union>(FVars_T12 ` set9_T1_pre x) - set6_T1_pre x) \<union> \<Union>(FVars_T22 ` set10_T1_pre x)
    \<union> (\<Union>(FVars_T22 ` set11_T1_pre x))"
  "FVars_T21 (T2_ctor x2) = set1_T2_pre x2 \<union> (set7_T2_pre x2 - set5_T2_pre x2) \<union> \<Union>(FVars_T11 ` set8_T2_pre x2)
    \<union> (\<Union>(FVars_T11 ` set9_T2_pre x2) - set5_T2_pre x2) \<union> \<Union>(FVars_T21 ` set10_T2_pre x2)
    \<union> (\<Union>(FVars_T21 ` set11_T2_pre x2) - set5_T2_pre x2)"
  "FVars_T22 (T2_ctor x2) = set2_T2_pre x2 \<union> \<Union>(FVars_T12 ` set8_T2_pre x2)
    \<union> (\<Union>(FVars_T12 ` set9_T2_pre x2) - set6_T2_pre x2) \<union> \<Union>(FVars_T22 ` set10_T2_pre x2)
    \<union> (\<Union>(FVars_T22 ` set11_T2_pre x2))"
     apply (unfold FVars_defs T1_ctor_def T2_ctor_def)
    (* REPEAT_DETERM *)
     apply (rule trans)
      apply (rule alpha_FVars)
      apply (rule TT_rep_abs)
     apply (unfold FVars_raw_ctors)
     apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)+
     apply (unfold image_id image_comp[unfolded comp_def])
     apply (rule refl)
    (* repeated *)
    apply (rule trans)
     apply (rule alpha_FVars)
     apply (rule TT_rep_abs)
    apply (unfold FVars_raw_ctors)
    apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)+
    apply (unfold image_id image_comp[unfolded comp_def])
    apply (rule refl)
    (* repeated *)
   apply (rule trans)
    apply (rule alpha_FVars)
    apply (rule TT_rep_abs)
   apply (unfold FVars_raw_ctors)
   apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id image_comp[unfolded comp_def])
   apply (rule refl)
    (* repeated *)
  apply (rule trans)
   apply (rule alpha_FVars)
   apply (rule TT_rep_abs)
  apply (unfold FVars_raw_ctors)
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id image_comp[unfolded comp_def])
  apply (rule refl)
    (* END REPEAT_DETERM *)
    done

lemma FVars_intros:
  "a \<in> set1_T1_pre x \<Longrightarrow> a \<in> FVars_T11 (T1_ctor x)"
  "a \<in> set7_T1_pre x \<Longrightarrow> a \<notin> set5_T1_pre x \<Longrightarrow> a \<in> FVars_T11 (T1_ctor x)"
  "z \<in> set8_T1_pre x \<Longrightarrow> a \<in> FVars_T11 z \<Longrightarrow> a \<in> FVars_T11 (T1_ctor x)"
  "z \<in> set9_T1_pre x \<Longrightarrow> a \<in> FVars_T11 z \<Longrightarrow> a \<notin> set5_T1_pre x \<Longrightarrow> a \<in> FVars_T11 (T1_ctor x)"
  "z2 \<in> set10_T1_pre x \<Longrightarrow> a \<in> FVars_T21 z2 \<Longrightarrow> a \<in> FVars_T11 (T1_ctor x)"
  "z2 \<in> set11_T1_pre x \<Longrightarrow> a \<in> FVars_T21 z2 \<Longrightarrow> a \<notin> set5_T1_pre x \<Longrightarrow> a \<in> FVars_T11 (T1_ctor x)"
  "a \<in> set1_T2_pre x2 \<Longrightarrow> a \<in> FVars_T21 (T2_ctor x2)"
  "a \<in> set7_T2_pre x2 \<Longrightarrow> a \<notin> set5_T2_pre x2 \<Longrightarrow> a \<in> FVars_T21 (T2_ctor x2)"
  "z \<in> set8_T2_pre x2 \<Longrightarrow> a \<in> FVars_T11 z \<Longrightarrow> a \<in> FVars_T21 (T2_ctor x2)"
  "z \<in> set9_T2_pre x2 \<Longrightarrow> a \<in> FVars_T11 z \<Longrightarrow> a \<notin> set5_T2_pre x2 \<Longrightarrow> a \<in> FVars_T21 (T2_ctor x2)"
  "z2 \<in> set10_T2_pre x2 \<Longrightarrow> a \<in> FVars_T21 z2 \<Longrightarrow> a \<in> FVars_T21 (T2_ctor x2)"
  "z2 \<in> set11_T2_pre x2 \<Longrightarrow> a \<in> FVars_T21 z2 \<Longrightarrow> a \<notin> set5_T2_pre x2 \<Longrightarrow> a \<in> FVars_T21 (T2_ctor x2)"
  "b \<in> set2_T1_pre x \<Longrightarrow> b \<in> FVars_T12 (T1_ctor x)"
  "z \<in> set8_T1_pre x \<Longrightarrow> b \<in> FVars_T12 z \<Longrightarrow> b \<in> FVars_T12 (T1_ctor x)"
  "z \<in> set9_T1_pre x \<Longrightarrow> b \<in> FVars_T12 z \<Longrightarrow> b \<notin> set6_T1_pre x \<Longrightarrow> b \<in> FVars_T12 (T1_ctor x)"
  "z2 \<in> set10_T1_pre x \<Longrightarrow> b \<in> FVars_T22 z2 \<Longrightarrow> b \<in> FVars_T12 (T1_ctor x)"
  "z2 \<in> set11_T1_pre x \<Longrightarrow> b \<in> FVars_T22 z2 \<Longrightarrow> b \<in> FVars_T12 (T1_ctor x)"
  "b \<in> set2_T2_pre x2 \<Longrightarrow> b \<in> FVars_T22 (T2_ctor x2)"
  "z \<in> set8_T2_pre x2 \<Longrightarrow> b \<in> FVars_T12 z \<Longrightarrow> b \<in> FVars_T22 (T2_ctor x2)"
  "z \<in> set9_T2_pre x2 \<Longrightarrow> b \<in> FVars_T12 z \<Longrightarrow> b \<notin> set6_T2_pre x2 \<Longrightarrow> b \<in> FVars_T22 (T2_ctor x2)"
  "z2 \<in> set10_T2_pre x2 \<Longrightarrow> b \<in> FVars_T22 z2 \<Longrightarrow> b \<in> FVars_T22 (T2_ctor x2)"
  "z2 \<in> set11_T2_pre x2 \<Longrightarrow> b \<in> FVars_T22 z2 \<Longrightarrow> b \<in> FVars_T22 (T2_ctor x2)"
  apply (unfold FVars_defs T1_ctor_def T2_ctor_def alpha_FVars(1,2)[OF TT_rep_abs(1)] alpha_FVars(3,4)[OF TT_rep_abs(2)])
  (* for thm in FVars_intros *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(1)[rotated])
  apply (subst T1_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<notin>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(2)[rotated])
  apply (subst T1_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (unfold image_id)?
  apply (rule refl)+
  (* orelse *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(3)[rotated])
  apply (subst T1_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(4)[rotated])
  apply (subst T1_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(5)[rotated])
  apply (subst T1_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(6)[rotated])
  apply (subst T1_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(7)[rotated])
  apply (subst T2_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<notin>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(8)[rotated])
  apply (subst T2_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (unfold image_id)?
  apply (rule refl)+
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(9)[rotated])
  apply (subst T2_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(10)[rotated])
  apply (subst T2_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(11)[rotated])
  apply (subst T2_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(12)[rotated])
  apply (subst T2_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(13)[rotated])
  apply (subst T1_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(14)[rotated])
  apply (subst T1_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(15)[rotated])
  apply (subst T1_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(16)[rotated])
  apply (subst T1_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(17)[rotated])
  apply (subst T1_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(18)[rotated])
  apply (subst T2_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(19)[rotated])
  apply (subst T2_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(20)[rotated])
  apply (subst T2_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(21)[rotated])
  apply (subst T2_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* repeated *)
  apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated -1])
  prefer 2
  apply (erule FVars_raw_intros(22)[rotated])
  apply (subst T2_pre.set_map)
  apply (rule supp_id_bound bij_id)+
  apply (unfold image_id)?
  apply assumption?
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)?
  apply (erule imageI)?
  apply (rule refl)
  (* END REPEAT for *)
  done

lemma TT_inject0s:
  "(T1_ctor x = T1_ctor y) = (\<exists>(f1::('a::{var_T1_pre, var_T2_pre} \<Rightarrow> 'a)) (f2::('b::{var_T1_pre, var_T2_pre} \<Rightarrow> 'b)).
    bij f1 \<and> |supp f1| <o |UNIV::'a set| \<and> bij f2 \<and> |supp f2| <o |UNIV::'b set|
    \<and> id_on ((set7_T1_pre x - set5_T1_pre x) \<union> (\<Union>(FVars_T11 ` set9_T1_pre x) - set5_T1_pre x) \<union> (\<Union>(FVars_T21 ` set11_T1_pre x) - set5_T1_pre x)) f1
    \<and> id_on (\<Union>(FVars_T12 ` set9_T1_pre x) - set6_T1_pre x) f2
    \<and> map_T1_pre id id id id f1 f2 f1 id (permute_T1 f1 f2) id (permute_T2 f1 id) x = y)"
  "(T2_ctor x2 = T2_ctor y2) = (\<exists>(f1::('a::{var_T1_pre, var_T2_pre} \<Rightarrow> 'a)) (f2::('b::{var_T1_pre, var_T2_pre} \<Rightarrow> 'b)).
    bij f1 \<and> |supp f1| <o |UNIV::'a set| \<and> bij f2 \<and> |supp f2| <o |UNIV::'b set|
    \<and> id_on ((set7_T2_pre x2 - set5_T2_pre x2) \<union> (\<Union>(FVars_T11 ` set9_T2_pre x2) - set5_T2_pre x2) \<union> (\<Union>(FVars_T21 ` set11_T2_pre x2) - set5_T2_pre x2)) f1
    \<and> id_on (\<Union>(FVars_T12 ` set9_T2_pre x2) - set6_T2_pre x2) f2
    \<and> map_T2_pre id id id id f1 f2 f1 id (permute_T1 f1 f2) id (permute_T2 f1 id) x2 = y2)"
   apply (unfold T1_ctor_def T2_ctor_def permute_T1_def permute_T2_def)
   apply (rule trans)
    apply (rule TT_total_abs_eq_iffs)
   apply (rule iffI)
    apply (erule alpha_T1.cases)
    apply (drule iffD1[OF raw_T1.inject])+
    apply hypsubst
    apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)+
    apply (unfold image_id)
    apply (drule iffD1[OF T1_pre.mr_rel_map(1), rotated -1])
                  apply (rule supp_id_bound bij_id | assumption)+
    apply (unfold id_o o_id Grp_UNIV_id eq_OO)
    apply (drule iffD1[OF T1_pre.mr_rel_map(3), rotated -1])
                     apply (rule supp_id_bound bij_id | assumption)+
    apply (unfold inv_id id_o o_id Grp_UNIV_id conversep_eq eq_OO relcompp_conversep_Grp)
    apply (unfold Grp_OO image_comp[unfolded comp_def] FVars_defs[symmetric])
    apply (rule exI)+
    apply (rule conjI[rotated])+
          apply (rule T1_pre.mr_rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD1])
          apply (rule iffD2[OF T1_pre.mr_rel_map(1), rotated -1])
                      apply (unfold id_o o_id Grp_UNIV_id eq_OO Grp_OO)
                      apply (erule T1_pre.mr_rel_mono_strong[rotated -6])
                      apply (rule ballI, rule ballI, rule impI, assumption)+
    (* REPEAT_DETERM *)
                      apply (rule ballI impI)+
                      apply (drule TT_total_abs_eq_iffs[THEN iffD2])
                      apply (unfold TT_abs_rep)
                      apply assumption
    (* repeated *)
                      apply (rule ballI impI)+
                      apply (drule TT_total_abs_eq_iffs[THEN iffD2])
                      apply (unfold TT_abs_rep)
                      apply hypsubst
                      apply (rule refl)
    (* repeated *)
                      apply (rule ballI impI)+
                      apply (drule TT_total_abs_eq_iffs[THEN iffD2])
                      apply (unfold TT_abs_rep)
                      apply assumption
    (* repeated *)
                      apply (rule ballI impI)+
                      apply (drule TT_total_abs_eq_iffs[THEN iffD2])
                      apply (unfold TT_abs_rep)
                      apply hypsubst
                      apply (rule refl)
    (* END REPEAT_DETERM *)
                      apply (rule supp_id_bound bij_id | assumption)+
   apply (erule exE conjE)+
   apply hypsubst_thin
   apply (subst T1_pre.map_comp)
            apply (rule supp_id_bound bij_id | assumption)+
   apply (unfold id_o o_id)
   apply (unfold comp_def)
   apply (rule alpha_T1_alpha_T2.intros[rotated -1])
         apply (rule iffD2[OF T1_pre.mr_rel_map(1), rotated -1])
                      apply (unfold id_o o_id Grp_UNIV_id eq_OO)
                      apply (rule iffD2[OF T1_pre.mr_rel_map(3), rotated -1])
                      apply (unfold inv_id id_o o_id Grp_UNIV_id conversep_eq eq_OO)
                      apply (unfold relcompp_conversep_Grp Grp_OO)
                      apply (subst inv_o_simp1, assumption)+
                      apply (rule iffD1[OF T1_pre.mr_rel_id[THEN fun_cong, THEN fun_cong]])
                      apply (rule T1_pre.rel_refl_strong)
                      apply (rule refl alpha_refls | (rule alpha_syms, rule TT_rep_abs))+
                      apply (rule supp_id_bound bij_id | assumption)+
    (* REPEAT_DETERM *)
    apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)+
    apply (unfold image_id FVars_defs image_comp[unfolded comp_def])[1]
    apply assumption
    (* repeated *)
   apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id FVars_defs image_comp[unfolded comp_def])[1]
   apply assumption
    (* END REPEAT_DETERM *)

(* second goal, same tactic *)
  apply (rule trans)
   apply (rule TT_total_abs_eq_iffs)
  apply (rule iffI)
   apply (erule alpha_T2.cases)
   apply (drule iffD1[OF raw_T2.inject])+
   apply hypsubst
   apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)
   apply (drule iffD1[OF T2_pre.mr_rel_map(1), rotated -1])
                 apply (rule supp_id_bound bij_id | assumption)+
   apply (unfold id_o o_id Grp_UNIV_id eq_OO)
   apply (drule iffD1[OF T2_pre.mr_rel_map(3), rotated -1])
                    apply (rule supp_id_bound bij_id | assumption)+
   apply (unfold inv_id id_o o_id Grp_UNIV_id conversep_eq eq_OO relcompp_conversep_Grp)
   apply (unfold Grp_OO image_comp[unfolded comp_def] FVars_defs[symmetric])
   apply (rule exI)+
   apply (rule conjI[rotated])+
         apply (rule T2_pre.mr_rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD1])
         apply (rule iffD2[OF T2_pre.mr_rel_map(1), rotated -1])
                      apply (unfold id_o o_id Grp_UNIV_id eq_OO Grp_OO)
                      apply (erule T2_pre.mr_rel_mono_strong[rotated -6])
                      apply (rule ballI, rule ballI, rule impI, assumption)+
    (* REPEAT_DETERM *)
                      apply (rule ballI impI)+
                      apply (drule TT_total_abs_eq_iffs[THEN iffD2])
                      apply (unfold TT_abs_rep)
                      apply assumption
    (* repeated *)
                      apply (rule ballI impI)+
                      apply (drule TT_total_abs_eq_iffs[THEN iffD2])
                      apply (unfold TT_abs_rep)
                      apply hypsubst
                      apply (rule refl)
    (* repeated *)
                      apply (rule ballI impI)+
                      apply (drule TT_total_abs_eq_iffs[THEN iffD2])
                      apply (unfold TT_abs_rep)
                      apply assumption
    (* repeated *)
                      apply (rule ballI impI)+
                      apply (drule TT_total_abs_eq_iffs[THEN iffD2])
                      apply (unfold TT_abs_rep)
                      apply hypsubst
                      apply (rule refl)
    (* END REPEAT_DETERM *)
                      apply (rule supp_id_bound bij_id | assumption)+
  apply (erule exE conjE)+
  apply hypsubst_thin
  apply (subst T2_pre.map_comp)
           apply (rule supp_id_bound bij_id | assumption)+
  apply (unfold id_o o_id)
  apply (unfold comp_def)
  apply (rule alpha_T1_alpha_T2.intros[rotated -1])
        apply (rule iffD2[OF T2_pre.mr_rel_map(1), rotated -1])
                      apply (unfold id_o o_id Grp_UNIV_id eq_OO)
                      apply (rule iffD2[OF T2_pre.mr_rel_map(3), rotated -1])
                      apply (unfold inv_id id_o o_id Grp_UNIV_id conversep_eq eq_OO)
                      apply (unfold relcompp_conversep_Grp Grp_OO)
                      apply (subst inv_o_simp1, assumption)+
                      apply (rule iffD1[OF T2_pre.mr_rel_id[THEN fun_cong, THEN fun_cong]])
                      apply (rule T2_pre.rel_refl_strong)
                      apply (rule refl alpha_refls | (rule alpha_syms, rule TT_rep_abs))+
                      apply (rule supp_id_bound bij_id | assumption)+
    (* REPEAT_DETERM *)
   apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id FVars_defs image_comp[unfolded comp_def])[1]
   apply assumption
    (* repeated *)
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id FVars_defs image_comp[unfolded comp_def])[1]
  apply assumption
    (* END REPEAT_DETERM *)
  done

lemma avoid_freshs:
  fixes x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1'"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2'"
  assumes "|A| <o |UNIV::'a set|" "|B| <o |UNIV::'b set|"
  shows "set5_T1_pre (avoid_T1 x A B) \<inter> A = {}" "set6_T1_pre (avoid_T1 x A B) \<inter> B = {}"
    "set5_T2_pre (avoid_T2 x2 A B) \<inter> A = {}" "set6_T2_pre (avoid_T2 x2 A B) \<inter> B = {}"
     apply (unfold avoid_T1_def avoid_T2_def)
    (* REPEAT_DETERM *)
     apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)
     apply (unfold image_id)
     apply (rule avoid_raw_freshs[OF assms])
    (* repeated *)
    apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)
    apply (unfold image_id)
    apply (rule avoid_raw_freshs[OF assms])
    (* repeated *)
   apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)
   apply (unfold image_id)
   apply (rule avoid_raw_freshs[OF assms])
    (* repeated *)
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)
  apply (unfold image_id)
  apply (rule avoid_raw_freshs[OF assms])
  done

lemma alpha_avoids:
  fixes x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1'"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2'"
  assumes "|A| <o |UNIV::'a set|" "|B| <o |UNIV::'b set|"
  shows "T1_ctor (avoid_T1 x A B) = T1_ctor x" "T2_ctor (avoid_T2 x2 A B) = T2_ctor x2"
   apply (unfold avoid_T1_def avoid_T2_def avoid_raw_T1_def avoid_raw_T2_def)
   apply (rule someI2_ex)
    apply (rule raw_refreshs[OF assms])
   apply (erule conjE)+
   apply (unfold T1_ctor_def)
   apply (subst T1_pre.map_comp)
        apply (rule supp_id_bound bij_id)+
   apply (unfold id_o o_id)
   apply (drule TT_total_abs_eq_iffs[THEN iffD2])
   apply (rule trans[rotated])
    apply (rule sym)
    apply assumption
   apply (rule TT_total_abs_eq_iffs[THEN iffD2])
   apply (rule alpha_T1_alpha_T2.intros)
         apply (rule supp_id_bound bij_id id_on_id)+
   apply (rule iffD2[OF T1_pre.mr_rel_map(1), rotated -1])
                 apply (unfold id_o o_id Grp_UNIV_id eq_OO Grp_OO permute_raw_ids)
                 apply (unfold comp_def)
                 apply (rule iffD1[OF T1_pre.mr_rel_id[THEN fun_cong, THEN fun_cong]])
                 apply (rule T1_pre.rel_refl_strong)
                     apply (rule refl TT_rep_abs)+
                apply (rule supp_id_bound bij_id)+
    (* second goal, same tactic *)
  apply (rule someI2_ex)
   apply (rule raw_refreshs[OF assms])
  apply (erule conjE)+
  apply (unfold T2_ctor_def)
  apply (subst T2_pre.map_comp)
       apply (rule supp_id_bound bij_id)+
  apply (unfold id_o o_id)
  apply (drule TT_total_abs_eq_iffs[THEN iffD2])
  apply (rule trans[rotated])
   apply (rule sym)
   apply assumption
  apply (rule TT_total_abs_eq_iffs[THEN iffD2])
  apply (rule alpha_T1_alpha_T2.intros)
        apply (rule supp_id_bound bij_id id_on_id)+
  apply (rule iffD2[OF T2_pre.mr_rel_map(1), rotated -1])
                apply (unfold id_o o_id Grp_UNIV_id eq_OO Grp_OO permute_raw_ids)
                apply (unfold comp_def)
                apply (rule iffD1[OF T2_pre.mr_rel_id[THEN fun_cong, THEN fun_cong]])
                apply (rule T2_pre.rel_refl_strong)
                    apply (rule refl TT_rep_abs)+
               apply (rule supp_id_bound bij_id)+
  done

lemma fresh_cases_T1:
  fixes y::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1"
  assumes "|A| <o |UNIV::'a set|" "|B| <o |UNIV::'b set|"
    and "\<And>(x::('a, 'b, 'c, 'd) T1'). y = T1_ctor x \<Longrightarrow> set5_T1_pre x \<inter> A = {} \<Longrightarrow> set6_T1_pre x \<inter> B = {} \<Longrightarrow> P"
  shows "P"
  apply (rule raw_T1.exhaust[of "TT1_rep y"])
  apply (rule assms)
    defer
    apply (rule avoid_freshs[OF assms(1-2)])+
  apply (rule trans[rotated])
   apply (rule sym)
   apply (rule alpha_avoids[OF assms(1-2)])
  apply (unfold T1_ctor_def)
  apply (rule TT_Quotients[THEN Quotient_rel_abs2])
  apply (rule arg_cong2[OF _ refl, of _ _ alpha_T1, THEN iffD2])
   apply assumption
  apply (rule alpha_T1_alpha_T2.intros[rotated -1])
        apply (subst T1_pre.map_comp)
                    apply (rule supp_id_bound bij_id)+
        apply (unfold id_o o_id)
        apply (rule iffD2[OF T1_pre.mr_rel_map(3), rotated -1])
                      apply (subst Grp_UNIV_id)+
                      apply (unfold inv_id id_o o_id conversep_eq eq_OO Grp_OO relcompp_conversep_Grp)
                      apply (unfold comp_def)
                      apply (rule iffD1[OF T1_pre.mr_rel_id[THEN fun_cong, THEN fun_cong]])
                      apply (unfold permute_raw_ids)
                      apply (rule T1_pre.rel_refl_strong)
                      apply (rule refl)
                      apply (rule alpha_syms, rule TT_rep_abs)+
                      apply (rule supp_id_bound bij_id id_on_id)+
  done
lemma fresh_cases_T2:
  fixes x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2'"
  assumes "|A| <o |UNIV::'a set|" "|B| <o |UNIV::'b set|"
    and "\<And>(x::('a, 'b, 'c, 'd) T2'). y = T2_ctor x \<Longrightarrow> set5_T2_pre x \<inter> A = {} \<Longrightarrow> set6_T2_pre x \<inter> B = {} \<Longrightarrow> P"
  shows "P"
  apply (rule raw_T2.exhaust[of "TT2_rep y"])
  apply (rule assms)
    defer
    apply (rule avoid_freshs[OF assms(1-2)])+
  apply (rule trans[rotated])
   apply (rule sym)
   apply (rule alpha_avoids[OF assms(1-2)])
  apply (unfold T2_ctor_def)
  apply (rule TT_Quotients[THEN Quotient_rel_abs2])
  apply (rule arg_cong2[OF _ refl, of _ _ alpha_T2, THEN iffD2])
   apply assumption
  apply (rule alpha_T1_alpha_T2.intros[rotated -1])
        apply (subst T2_pre.map_comp)
                    apply (rule supp_id_bound bij_id)+
        apply (unfold id_o o_id)
        apply (rule iffD2[OF T2_pre.mr_rel_map(3), rotated -1])
                      apply (subst Grp_UNIV_id)+
                      apply (unfold inv_id id_o o_id conversep_eq eq_OO Grp_OO relcompp_conversep_Grp)
                      apply (unfold comp_def)
                      apply (rule iffD1[OF T2_pre.mr_rel_id[THEN fun_cong, THEN fun_cong]])
                      apply (unfold permute_raw_ids)
                      apply (rule T2_pre.rel_refl_strong)
                      apply (rule refl)
                      apply (rule alpha_syms, rule TT_rep_abs)+
                      apply (rule supp_id_bound bij_id id_on_id)+
  done
lemmas fresh_cases = fresh_cases_T1 fresh_cases_T2

lemma alpha_subshapess:
  fixes x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
  shows
    "alpha_T1 x y \<Longrightarrow> subshape_T1_T1 z x \<Longrightarrow> subshape_T1_T1 z y"
    "alpha_T1 x y \<Longrightarrow> subshape_T2_T1 z2 x \<Longrightarrow> subshape_T2_T1 z2 y"
    "alpha_T2 x2 y2 \<Longrightarrow> subshape_T1_T2 z x2 \<Longrightarrow> subshape_T1_T2 z y2"
    "alpha_T2 x2 y2 \<Longrightarrow> subshape_T2_T2 z2 x2 \<Longrightarrow> subshape_T2_T2 z2 y2"
proof -
  have x: "(\<forall>x. alpha_T1 x y \<longrightarrow> (\<forall>z. subshape_T1_T1 z x \<longrightarrow> subshape_T1_T1 z y) \<and> (\<forall>z. subshape_T2_T1 z x \<longrightarrow> subshape_T2_T1 z y))
      \<and> (\<forall>x. alpha_T2 x y2 \<longrightarrow> (\<forall>z. subshape_T1_T2 z x \<longrightarrow> subshape_T1_T2 z y2) \<and> (\<forall>z. subshape_T2_T2 z x \<longrightarrow> subshape_T2_T2 z y2))"
    apply (rule raw_T1_raw_T2.induct[of _ _ y y2])
    subgoal premises IHs for x
      apply (rule allI)
      apply (rule impI)
      apply (rule conjI)
        (* REPEAT_DETERM *)
       apply (rule allI)
       apply (rule impI)
       apply (erule alpha_T1.cases)
       apply (erule subshape_elims)
       apply (drule iffD1[OF raw_T1.inject])
       apply hypsubst
       apply (drule iffD1[OF raw_T1.inject])
       apply hypsubst
       apply (erule UnE)
        (* REPEAT_DETERM *)
        apply (drule T1_pre.mr_rel_set(8-11)[rotated -1])
                prefer 9 (* free + 2 * bound + 1 *)
                apply assumption
               apply (rule supp_id_bound bij_id | assumption)+
        apply (erule bexE)
        apply (frule IHs)
        apply (erule allE)
        apply (erule impE)
         apply assumption
        apply (rule subshape_intros[rotated -1])
             apply (erule UnI1 UnI2 | rule UnI2)+
            prefer 5 (* 2 * nvars + 1 *)
            apply (rule alpha_trans[rotated])
             apply assumption
            apply assumption
           apply (erule UnI1 | rule UnI2 | assumption)+
        (* ORELSE *)
       apply (drule T1_pre.mr_rel_set(8-11)[rotated -1])
               prefer 9 (* free + 2 * bound + 1 *)
               apply assumption
              apply (rule supp_id_bound bij_id | assumption)+
       apply (erule bexE)
       apply (frule IHs)
       apply (erule allE)
       apply (erule impE)
        apply assumption
       apply (rule subshape_intros[rotated -1])
            apply (erule UnI1 UnI2 | rule UnI2)+
           prefer 5 (* 2 * nvars + 1 *)
           apply (rule alpha_trans[rotated])
            apply assumption
           apply (rule alpha_trans[rotated])
            apply (rule alpha_bij_eqs[THEN iffD2, rotated -1])
                apply assumption+
           apply (subst permute_raw_comps)
                   apply assumption+
           apply (rule alpha_refls)
          apply (rule bij_comp supp_comp_bound infinite_UNIV | assumption)+
        (* END REPEAT_DETERM *)
        (* repeated *)
      apply (rule allI)
      apply (rule impI)
      apply (erule alpha_T1.cases)
      apply (erule subshape_elims)
      apply (drule iffD1[OF raw_T1.inject])
      apply hypsubst
      apply (drule iffD1[OF raw_T1.inject])
      apply hypsubst
      apply (erule UnE)
        (* REPEAT_DETERM *)
       apply (drule T1_pre.mr_rel_set(8-11)[rotated -1])
               prefer 9 (* free + 2 * bound + 1 *)
               apply assumption
              apply (rule supp_id_bound bij_id | assumption)+
       apply (erule bexE)
       apply (frule IHs)
       apply (erule allE)
       apply (erule impE)
        apply assumption
       apply (rule subshape_intros[rotated -1])
            apply (erule UnI1 UnI2 | rule UnI2)+
           prefer 5 (* 2 * nvars + 1 *)
           apply (rule alpha_trans[rotated])
            apply assumption
           apply assumption
          apply (erule UnI1 | rule UnI2 | assumption)+
        (* ORELSE *)
      apply (drule T1_pre.mr_rel_set(8-11)[rotated -1])
              prefer 9 (* free + 2 * bound + 1 *)
              apply assumption
             apply (rule supp_id_bound bij_id | assumption)+
      apply (erule bexE)
      apply (frule IHs)
      apply (erule allE)
      apply (erule impE)
       apply assumption
      apply (rule subshape_intros[rotated -1])
           apply (erule UnI1 UnI2 | rule UnI2)+
          prefer 5 (* 2 * nvars + 1 *)
          apply (rule alpha_trans[rotated])
           apply assumption
          apply (rule alpha_trans[rotated])
           apply (rule alpha_bij_eqs[THEN iffD2, rotated -1])
               apply (assumption | rule supp_id_bound bij_id)+
          apply (subst permute_raw_comps)
                  apply (assumption | rule supp_id_bound bij_id)+
          apply (unfold id_o o_id)
          apply (rule alpha_refls)
         apply (rule bij_comp supp_comp_bound infinite_UNIV | assumption)+
        (* END REPEAT_DETERM *)
      done
        (* second goal, same tactic *)
    subgoal premises IHs for x
      apply (rule allI)
      apply (rule impI)
      apply (rule conjI)
        (* REPEAT_DETERM *)
       apply (rule allI)
       apply (rule impI)
       apply (erule alpha_T2.cases)
       apply (erule subshape_elims)
       apply (drule iffD1[OF raw_T2.inject])
       apply hypsubst
       apply (drule iffD1[OF raw_T2.inject])
       apply hypsubst
       apply (erule UnE)
        (* REPEAT_DETERM *)
        apply (drule T2_pre.mr_rel_set(8-11)[rotated -1])
                prefer 9 (* free + 2 * bound + 1 *)
                apply assumption
               apply (rule supp_id_bound bij_id | assumption)+
        apply (erule bexE)
        apply (frule IHs)
        apply (erule allE)
        apply (erule impE)
         apply assumption
        apply (rule subshape_intros[rotated -1])
             apply (erule UnI1 UnI2 | rule UnI2)+
            prefer 5 (* 2 * nvars + 1 *)
            apply (rule alpha_trans[rotated])
             apply assumption
            apply assumption
           apply (erule UnI1 | rule UnI2 | assumption)+
        (* ORELSE *)
       apply (drule T2_pre.mr_rel_set(8-11)[rotated -1])
               prefer 9 (* free + 2 * bound + 1 *)
               apply assumption
              apply (rule supp_id_bound bij_id | assumption)+
       apply (erule bexE)
       apply (frule IHs)
       apply (erule allE)
       apply (erule impE)
        apply assumption
       apply (rule subshape_intros[rotated -1])
            apply (erule UnI1 UnI2 | rule UnI2)+
           prefer 5 (* 2 * nvars + 1 *)
           apply (rule alpha_trans[rotated])
            apply assumption
           apply (rule alpha_trans[rotated])
            apply (rule alpha_bij_eqs[THEN iffD2, rotated -1])
                apply assumption+
           apply (subst permute_raw_comps)
                   apply assumption+
           apply (rule alpha_refls)
          apply (rule bij_comp supp_comp_bound infinite_UNIV | assumption)+
        (* END REPEAT_DETERM *)
        (* repeated *)
      apply (rule allI)
      apply (rule impI)
      apply (erule alpha_T2.cases)
      apply (erule subshape_elims)
      apply (drule iffD1[OF raw_T2.inject])
      apply hypsubst
      apply (drule iffD1[OF raw_T2.inject])
      apply hypsubst
      apply (erule UnE)
        (* REPEAT_DETERM *)
       apply (drule T2_pre.mr_rel_set(8-11)[rotated -1])
               prefer 9 (* free + 2 * bound + 1 *)
               apply assumption
              apply (rule supp_id_bound bij_id | assumption)+
       apply (erule bexE)
       apply (frule IHs)
       apply (erule allE)
       apply (erule impE)
        apply assumption
       apply (rule subshape_intros[rotated -1])
            apply (erule UnI1 UnI2 | rule UnI2)+
           prefer 5 (* 2 * nvars + 1 *)
           apply (rule alpha_trans[rotated])
            apply assumption
           apply assumption
          apply (erule UnI1 | rule UnI2 | assumption)+
        (* ORELSE *)
      apply (drule T2_pre.mr_rel_set(8-11)[rotated -1])
              prefer 9 (* free + 2 * bound + 1 *)
              apply assumption
             apply (rule supp_id_bound bij_id | assumption)+
      apply (erule bexE)
      apply (frule IHs)
      apply (erule allE)
      apply (erule impE)
       apply assumption
      apply (rule subshape_intros[rotated -1])
           apply (erule UnI1 UnI2 | rule UnI2)+
          prefer 5 (* 2 * nvars + 1 *)
          apply (rule alpha_trans[rotated])
           apply assumption
          apply (rule alpha_trans[rotated])
           apply (rule alpha_bij_eqs[THEN iffD2, rotated -1])
               apply (assumption | rule supp_id_bound bij_id)+
          apply (subst permute_raw_comps)
                  apply (assumption | rule supp_id_bound bij_id)+
          apply (unfold id_o o_id)
          apply (rule alpha_refls)
         apply (rule bij_comp supp_comp_bound infinite_UNIV | assumption)+
        (* END REPEAT_DETERM *)
      done
    done

  show "alpha_T1 x y \<Longrightarrow> subshape_T1_T1 z x \<Longrightarrow> subshape_T1_T1 z y" "alpha_T1 x y \<Longrightarrow> subshape_T2_T1 z2 x \<Longrightarrow> subshape_T2_T1 z2 y"
    "alpha_T2 x2 y2 \<Longrightarrow> subshape_T1_T2 z x2 \<Longrightarrow> subshape_T1_T2 z y2" "alpha_T2 x2 y2 \<Longrightarrow> subshape_T2_T2 z2 x2 \<Longrightarrow> subshape_T2_T2 z2 y2"
    (* REPEAT_DETERM *)
       apply (drule conjunct1[OF x, THEN spec, THEN mp])
       apply (erule conjE)+
       apply (unfold atomize_all[symmetric] atomize_imp[symmetric])
       apply assumption
      (* repeated *)
      apply (drule conjunct1[OF x, THEN spec, THEN mp])
      apply (erule conjE)+
      apply (unfold atomize_all[symmetric] atomize_imp[symmetric])
      apply assumption
      (* repeated *)
     apply (drule conjunct2[OF x, THEN spec, THEN mp])
     apply (erule conjE)+
     apply (unfold atomize_all[symmetric] atomize_imp[symmetric])
     apply assumption
      (* repeated *)
    apply (drule conjunct2[OF x, THEN spec, THEN mp])
    apply (erule conjE)+
    apply (unfold atomize_all[symmetric] atomize_imp[symmetric])
    apply assumption
    done
qed

lemma subshape_induct_raw:
  fixes x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
  assumes "\<And>x. (\<And>y. subshape_T1_T1 y x \<Longrightarrow> P1 y) \<Longrightarrow> (\<And>y. subshape_T2_T1 y x \<Longrightarrow> P2 y) \<Longrightarrow> P1 x"
    "\<And>x. (\<And>y. subshape_T1_T2 y x \<Longrightarrow> P1 y) \<Longrightarrow> (\<And>y. subshape_T2_T2 y x \<Longrightarrow> P2 y) \<Longrightarrow> P2 x"
  shows "(\<forall>f1 f2 y. bij f1 \<longrightarrow> |supp f1| <o |UNIV::'a set| \<longrightarrow> bij f2 \<longrightarrow> |supp f2| <o |UNIV::'b set| \<longrightarrow> alpha_T1 (permute_raw_T1 f1 f2 x) y \<longrightarrow> P1 y)
       \<and> (\<forall>f1 f2 y. bij f1 \<longrightarrow> |supp f1| <o |UNIV::'a set| \<longrightarrow> bij f2 \<longrightarrow> |supp f2| <o |UNIV::'b set| \<longrightarrow> alpha_T2 (permute_raw_T2 f1 f2 x2) y \<longrightarrow> P2 y)"
  apply (rule raw_T1_raw_T2.induct)
  subgoal premises IHs for x
    apply (rule allI impI)+
    apply (rule assms)
      (* REPEAT_DETERM *)
     apply (drule alpha_subshapess[rotated -1])
      apply (erule alpha_syms)
     apply (rotate_tac -2)
     apply (erule thin_rl)
     apply (subst (asm) permute_raw_simps)
         apply assumption+
     apply (erule subshape_elims)
     apply (drule iffD1[OF raw_T1.inject])
     apply hypsubst
     apply (subst (asm) T1_pre.set_map, (assumption | rule supp_id_bound bij_id)+)+
     apply (unfold image_Un[symmetric])
     apply (erule imageE)
     apply hypsubst
     apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1])
         apply assumption+
     apply (subst (asm) permute_raw_comps)
             apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
     apply (erule UnE)
      (* REPEAT_DETERM *)
      apply (drule IHs)
      apply (erule allE)+
      (* REPEAT_DETERM *)
      apply (erule impE) prefer 2
       apply (erule impE) prefer 2
        apply (erule impE) prefer 2
         apply (erule impE) prefer 2
          apply (erule impE) prefer 2
      (* END REPEAT_DETERM *)
           apply assumption
          apply (erule alpha_syms)
         apply (assumption | rule bij_imp_bij_inv supp_inv_bound supp_comp_bound bij_comp infinite_UNIV)+
      (* repeated *)
     apply (drule IHs)
     apply (erule allE)+
      (* REPEAT_DETERM *)
     apply (erule impE) prefer 2
      apply (erule impE) prefer 2
       apply (erule impE) prefer 2
        apply (erule impE) prefer 2
         apply (erule impE) prefer 2
      (* END REPEAT_DETERM *)
          apply assumption
         apply (erule alpha_syms)
        apply (assumption | rule bij_imp_bij_inv supp_inv_bound supp_comp_bound bij_comp infinite_UNIV)+
      (* END REPEAT_DETERM *)
      (* repeated *)
    apply (drule alpha_subshapess[rotated -1])
     apply (erule alpha_syms)
    apply (rotate_tac -2)
    apply (erule thin_rl)
    apply (subst (asm) permute_raw_simps)
        apply assumption+
    apply (erule subshape_elims)
    apply (drule iffD1[OF raw_T1.inject])
    apply hypsubst
    apply (subst (asm) T1_pre.set_map, (assumption | rule supp_id_bound bij_id)+)+
    apply (unfold image_Un[symmetric])
    apply (erule imageE)
    apply hypsubst
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1])
        apply assumption+
    apply (subst (asm) permute_raw_comps)
            apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
    apply (erule UnE)
      (* REPEAT_DETERM *)
     apply (drule IHs)
     apply (erule allE)+
      (* REPEAT_DETERM *)
     apply (erule impE) prefer 2
      apply (erule impE) prefer 2
       apply (erule impE) prefer 2
        apply (erule impE) prefer 2
         apply (erule impE) prefer 2
      (* END REPEAT_DETERM *)
          apply assumption
         apply (erule alpha_syms)
        apply (assumption | rule bij_imp_bij_inv supp_inv_bound supp_comp_bound bij_comp infinite_UNIV)+
      (* repeated *)
    apply (drule IHs)
    apply (erule allE)+
      (* REPEAT_DETERM *)
    apply (erule impE) prefer 2
     apply (erule impE) prefer 2
      apply (erule impE) prefer 2
       apply (erule impE) prefer 2
        apply (erule impE) prefer 2
      (* END REPEAT_DETERM *)
         apply assumption
        apply (erule alpha_syms)
       apply (assumption | rule bij_imp_bij_inv supp_inv_bound supp_comp_bound bij_comp infinite_UNIV)+
      (* END REPEAT_DETERM *)
      (* END REPEAT_DETERM *)
    done
      (* second goal, same tactic *)
  subgoal premises IHs for x
    apply (rule allI impI)+
    apply (rule assms)
      (* REPEAT_DETERM *)
     apply (drule alpha_subshapess[rotated -1])
      apply (erule alpha_syms)
     apply (rotate_tac -2)
     apply (erule thin_rl)
     apply (subst (asm) permute_raw_simps)
         apply assumption+
     apply (erule subshape_elims)
     apply (drule iffD1[OF raw_T2.inject])
     apply hypsubst
     apply (subst (asm) T2_pre.set_map, (assumption | rule supp_id_bound bij_id)+)+
     apply (unfold image_Un[symmetric])
     apply (erule imageE)
     apply hypsubst
     apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1])
         apply assumption+
     apply (subst (asm) permute_raw_comps)
             apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
     apply (erule UnE)
      (* REPEAT_DETERM *)
      apply (drule IHs)
      apply (erule allE)+
      (* REPEAT_DETERM *)
      apply (erule impE) prefer 2
       apply (erule impE) prefer 2
        apply (erule impE) prefer 2
         apply (erule impE) prefer 2
          apply (erule impE) prefer 2
      (* END REPEAT_DETERM *)
           apply assumption
          apply (erule alpha_syms)
         apply (assumption | rule bij_imp_bij_inv supp_inv_bound supp_comp_bound bij_comp infinite_UNIV)+
      (* repeated *)
     apply (drule IHs)
     apply (erule allE)+
      (* REPEAT_DETERM *)
     apply (erule impE) prefer 2
      apply (erule impE) prefer 2
       apply (erule impE) prefer 2
        apply (erule impE) prefer 2
         apply (erule impE) prefer 2
      (* END REPEAT_DETERM *)
          apply assumption
         apply (erule alpha_syms)
        apply (assumption | rule bij_imp_bij_inv supp_inv_bound supp_comp_bound bij_comp infinite_UNIV)+
      (* END REPEAT_DETERM *)
      (* repeated *)
    apply (drule alpha_subshapess[rotated -1])
     apply (erule alpha_syms)
    apply (rotate_tac -2)
    apply (erule thin_rl)
    apply (subst (asm) permute_raw_simps)
        apply assumption+
    apply (erule subshape_elims)
    apply (drule iffD1[OF raw_T2.inject])
    apply hypsubst
    apply (subst (asm) T2_pre.set_map, (assumption | rule supp_id_bound bij_id)+)+
    apply (unfold image_Un[symmetric])
    apply (erule imageE)
    apply hypsubst
    apply (drule alpha_bij_eq_invs[THEN iffD1, rotated -1])
        apply assumption+
    apply (subst (asm) permute_raw_comps)
            apply (assumption | rule bij_imp_bij_inv supp_inv_bound)+
    apply (erule UnE)
      (* REPEAT_DETERM *)
     apply (drule IHs)
     apply (erule allE)+
      (* REPEAT_DETERM *)
     apply (erule impE) prefer 2
      apply (erule impE) prefer 2
       apply (erule impE) prefer 2
        apply (erule impE) prefer 2
         apply (erule impE) prefer 2
      (* END REPEAT_DETERM *)
          apply assumption
         apply (erule alpha_syms)
        apply (assumption | rule bij_imp_bij_inv supp_inv_bound supp_comp_bound bij_comp infinite_UNIV)+
      (* repeated *)
    apply (drule IHs)
    apply (erule allE)+
      (* REPEAT_DETERM *)
    apply (erule impE) prefer 2
     apply (erule impE) prefer 2
      apply (erule impE) prefer 2
       apply (erule impE) prefer 2
        apply (erule impE) prefer 2
      (* END REPEAT_DETERM *)
         apply assumption
        apply (erule alpha_syms)
       apply (assumption | rule bij_imp_bij_inv supp_inv_bound supp_comp_bound bij_comp infinite_UNIV)+
      (* END REPEAT_DETERM *)
      (* END REPEAT_DETERM *)
    done
  done

lemma subshape_induct:
  fixes x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"
  assumes "\<And>x. (\<And>y. subshape_T1_T1 y x \<Longrightarrow> P1 y) \<Longrightarrow> (\<And>y. subshape_T2_T1 y x \<Longrightarrow> P2 y) \<Longrightarrow> P1 x"
    "\<And>x. (\<And>y. subshape_T1_T2 y x \<Longrightarrow> P1 y) \<Longrightarrow> (\<And>y. subshape_T2_T2 y x \<Longrightarrow> P2 y) \<Longrightarrow> P2 x"
  shows "P1 x \<and> P2 x2"
  apply (rule conjE[OF subshape_induct_raw[of P1 P2]])
    apply (rule assms, assumption+)+
  apply (erule allE impE | rule bij_id supp_id_bound alpha_refls)+
  apply (unfold permute_raw_ids)
  apply ((rule conjI)?, assumption)+
  done

lemma wf_subshape: "wf {(x, y). case x of
    Inl t1 \<Rightarrow> (case y of Inl t1' \<Rightarrow> subshape_T1_T1 t1 t1' | Inr t2 \<Rightarrow> subshape_T1_T2 t1 t2)
  | Inr t2 \<Rightarrow> (case y of Inl t1 \<Rightarrow> subshape_T2_T1 t2 t1 | Inr t2' \<Rightarrow> subshape_T2_T2 t2 t2')
 }"
  apply (rule wfUNIVI)
  apply (unfold prod_in_Collect_iff prod.case)
  subgoal for P x
    apply (rule sumE[of x]; hypsubst_thin)
      (* REPEAT_DETERM *)
     apply (rule conjunct1[OF subshape_induct[of "\<lambda>x. P (Inl x)" "\<lambda>y. P (Inr y)"]])
      (* REPEAT_DETERM *)
      apply (erule allE)
      apply (erule impE)
       prefer 2
       apply assumption
      apply (rule allI)
      apply (rule impI)
    subgoal for z x y
      apply (rule sumE[of y]; hypsubst_thin)
       apply (unfold sum.case)
       apply assumption+
      done
      (* repeated *)
      apply (erule allE)
      apply (erule impE)
       prefer 2
       apply assumption
      apply (rule allI)
      apply (rule impI)
    subgoal for z x y
      apply (rule sumE[of y]; hypsubst_thin)
       apply (unfold sum.case)
       apply assumption+
      done
    (* END REPEAT_DETERM *)
    (* repeated *)
     apply (rule conjunct2[OF subshape_induct[of "\<lambda>x. P (Inl x)" "\<lambda>y. P (Inr y)"]])
      (* REPEAT_DETERM *)
      apply (erule allE)
      apply (erule impE)
       prefer 2
       apply assumption
      apply (rule allI)
      apply (rule impI)
    subgoal for z x y
      apply (rule sumE[of y]; hypsubst_thin)
       apply (unfold sum.case)
       apply assumption+
      done
      (* repeated *)
      apply (erule allE)
      apply (erule impE)
       prefer 2
       apply assumption
      apply (rule allI)
      apply (rule impI)
    subgoal for z x y
      apply (rule sumE[of y]; hypsubst_thin)
       apply (unfold sum.case)
       apply assumption+
      done
    (* END REPEAT_DETERM *)
  (* END REPEAT_DETERM *)
    done
  done

lemma set_subshapess:
  "z \<in> set8_T1_pre x \<Longrightarrow> subshape_T1_T1 z (raw_T1_ctor x)"
  "z \<in> set9_T1_pre x \<Longrightarrow> subshape_T1_T1 z (raw_T1_ctor x)"
  "z2 \<in> set10_T1_pre x \<Longrightarrow> subshape_T2_T1 z2 (raw_T1_ctor x)"
  "z2 \<in> set11_T1_pre x \<Longrightarrow> subshape_T2_T1 z2 (raw_T1_ctor x)"
  "z \<in> set8_T2_pre x2 \<Longrightarrow> subshape_T1_T2 z (raw_T2_ctor x2)"
  "z \<in> set9_T2_pre x2 \<Longrightarrow> subshape_T1_T2 z (raw_T2_ctor x2)"
  "z2 \<in> set10_T2_pre x2 \<Longrightarrow> subshape_T2_T2 z2 (raw_T2_ctor x2)"
  "z2 \<in> set11_T2_pre x2 \<Longrightarrow> subshape_T2_T2 z2 (raw_T2_ctor x2)"
  (* REPEAT_DETERM *)
         apply (rule subshape_intros)
              apply (rule supp_id_bound bij_id)+
          apply (unfold permute_raw_ids)
          apply (rule alpha_refls)
         apply (erule UnI1 UnI2 | rule UnI2)+
    (* repeated *)
        apply (rule subshape_intros)
             apply (rule supp_id_bound bij_id)+
         apply (unfold permute_raw_ids)
         apply (rule alpha_refls)
        apply (erule UnI1 UnI2 | rule UnI2)+
    (* repeated *)
       apply (rule subshape_intros)
            apply (rule supp_id_bound bij_id)+
        apply (unfold permute_raw_ids)
        apply (rule alpha_refls)
       apply (erule UnI1 UnI2 | rule UnI2)+
    (* repeated *)
      apply (rule subshape_intros)
           apply (rule supp_id_bound bij_id)+
       apply (unfold permute_raw_ids)
       apply (rule alpha_refls)
      apply (erule UnI1 UnI2 | rule UnI2)+
    (* repeated *)
     apply (rule subshape_intros)
          apply (rule supp_id_bound bij_id)+
      apply (unfold permute_raw_ids)
      apply (rule alpha_refls)
     apply (erule UnI1 UnI2 | rule UnI2)+
    (* repeated *)
    apply (rule subshape_intros)
         apply (rule supp_id_bound bij_id)+
     apply (unfold permute_raw_ids)
     apply (rule alpha_refls)
    apply (erule UnI1 UnI2 | rule UnI2)+
    (* repeated *)
   apply (rule subshape_intros)
        apply (rule supp_id_bound bij_id)+
    apply (unfold permute_raw_ids)
    apply (rule alpha_refls)
   apply (erule UnI1 UnI2 | rule UnI2)+
    (* repeated *)
  apply (rule subshape_intros)
       apply (rule supp_id_bound bij_id)+
   apply (unfold permute_raw_ids)
   apply (rule alpha_refls)
  apply (erule UnI1 UnI2 | rule UnI2)+
    (* END REPEAT_DETERM *)
  done

lemma set_subshape_permutess:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows
    "z \<in> set8_T1_pre x \<Longrightarrow> subshape_T1_T1 (permute_raw_T1 f1 f2 z) (raw_T1_ctor x)"
    "z \<in> set9_T1_pre x \<Longrightarrow> subshape_T1_T1 (permute_raw_T1 f1 f2 z) (raw_T1_ctor x)"
    "z2 \<in> set10_T1_pre x \<Longrightarrow> subshape_T2_T1 (permute_raw_T2 f1 f2 z2) (raw_T1_ctor x)"
    "z2 \<in> set11_T1_pre x \<Longrightarrow> subshape_T2_T1 (permute_raw_T2 f1 f2 z2) (raw_T1_ctor x)"
    "z \<in> set8_T2_pre x2 \<Longrightarrow> subshape_T1_T2 (permute_raw_T1 f1 f2 z) (raw_T2_ctor x2)"
    "z \<in> set9_T2_pre x2 \<Longrightarrow> subshape_T1_T2 (permute_raw_T1 f1 f2 z) (raw_T2_ctor x2)"
    "z2 \<in> set10_T2_pre x2 \<Longrightarrow> subshape_T2_T2 (permute_raw_T2 f1 f2 z2) (raw_T2_ctor x2)"
    "z2 \<in> set11_T2_pre x2 \<Longrightarrow> subshape_T2_T2 (permute_raw_T2 f1 f2 z2) (raw_T2_ctor x2)"
    (* REPEAT_DETERM *)
         apply (rule subshape_intros[rotated -2])
              apply (subst permute_raw_comps)
                      prefer 9 (* 4 * nvars + 1 *)
                      apply (subst inv_o_simp1, rule assms)+
                      apply (unfold permute_raw_ids)
                      apply (rule alpha_refls)
                     apply (rule assms bij_imp_bij_inv supp_inv_bound)+
             apply (erule UnI1 UnI2 | rule UnI2)+
            apply (rule assms bij_imp_bij_inv supp_inv_bound)+
    (* repeated *)
        apply (rule subshape_intros[rotated -2])
             apply (subst permute_raw_comps)
                     prefer 9 (* 4 * nvars + 1 *)
                     apply (subst inv_o_simp1, rule assms)+
                     apply (unfold permute_raw_ids)
                     apply (rule alpha_refls)
                    apply (rule assms bij_imp_bij_inv supp_inv_bound)+
            apply (erule UnI1 UnI2 | rule UnI2)+
           apply (rule assms bij_imp_bij_inv supp_inv_bound)+
    (* repeated *)
       apply (rule subshape_intros[rotated -2])
            apply (subst permute_raw_comps)
                    prefer 9 (* 4 * nvars + 1 *)
                    apply (subst inv_o_simp1, rule assms)+
                    apply (unfold permute_raw_ids)
                    apply (rule alpha_refls)
                   apply (rule assms bij_imp_bij_inv supp_inv_bound)+
           apply (erule UnI1 UnI2 | rule UnI2)+
          apply (rule assms bij_imp_bij_inv supp_inv_bound)+
    (* repeated *)
      apply (rule subshape_intros[rotated -2])
           apply (subst permute_raw_comps)
                   prefer 9 (* 4 * nvars + 1 *)
                   apply (subst inv_o_simp1, rule assms)+
                   apply (unfold permute_raw_ids)
                   apply (rule alpha_refls)
                  apply (rule assms bij_imp_bij_inv supp_inv_bound)+
          apply (erule UnI1 UnI2 | rule UnI2)+
         apply (rule assms bij_imp_bij_inv supp_inv_bound)+
    (* repeated *)
     apply (rule subshape_intros[rotated -2])
          apply (subst permute_raw_comps)
                  prefer 9 (* 4 * nvars + 1 *)
                  apply (subst inv_o_simp1, rule assms)+
                  apply (unfold permute_raw_ids)
                  apply (rule alpha_refls)
                 apply (rule assms bij_imp_bij_inv supp_inv_bound)+
         apply (erule UnI1 UnI2 | rule UnI2)+
        apply (rule assms bij_imp_bij_inv supp_inv_bound)+
    (* repeated *)
    apply (rule subshape_intros[rotated -2])
         apply (subst permute_raw_comps)
                 prefer 9 (* 4 * nvars + 1 *)
                 apply (subst inv_o_simp1, rule assms)+
                 apply (unfold permute_raw_ids)
                 apply (rule alpha_refls)
                apply (rule assms bij_imp_bij_inv supp_inv_bound)+
        apply (erule UnI1 UnI2 | rule UnI2)+
       apply (rule assms bij_imp_bij_inv supp_inv_bound)+
    (* repeated *)
   apply (rule subshape_intros[rotated -2])
        apply (subst permute_raw_comps)
                prefer 9 (* 4 * nvars + 1 *)
                apply (subst inv_o_simp1, rule assms)+
                apply (unfold permute_raw_ids)
                apply (rule alpha_refls)
               apply (rule assms bij_imp_bij_inv supp_inv_bound)+
       apply (erule UnI1 UnI2 | rule UnI2)+
      apply (rule assms bij_imp_bij_inv supp_inv_bound)+
    (* repeated *)
  apply (rule subshape_intros[rotated -2])
       apply (subst permute_raw_comps)
               prefer 9 (* 4 * nvars + 1 *)
               apply (subst inv_o_simp1, rule assms)+
               apply (unfold permute_raw_ids)
               apply (rule alpha_refls)
              apply (rule assms bij_imp_bij_inv supp_inv_bound)+
      apply (erule UnI1 UnI2 | rule UnI2)+
     apply (rule assms bij_imp_bij_inv supp_inv_bound)+
    (* END REPEAT_DETERM *)
  done

lemma permute_abs:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
  shows
    "permute_T1 f1 f2 (TT1_abs x) = TT1_abs (permute_raw_T1 f1 f2 x)"
    "permute_T2 f1 f2 (TT2_abs x2) = TT2_abs (permute_raw_T2 f1 f2 x2)"
   apply (unfold permute_T1_def permute_T2_def)
   apply (rule TT_total_abs_eq_iffs[THEN iffD2])
   apply (rule alpha_bij_eqs[THEN iffD2, OF assms])
   apply (rule TT_rep_abs)
  (* repeated *)
   apply (rule TT_total_abs_eq_iffs[THEN iffD2])
   apply (rule alpha_bij_eqs[THEN iffD2, OF assms])
  apply (rule TT_rep_abs)
  done

lemma existential_induct:
  assumes IHs: "\<And>x \<rho>. \<rho> \<in> Param \<Longrightarrow> \<exists>y. T1_ctor y = T1_ctor x \<and>
    ((\<forall>z. z \<in> set8_T1_pre y \<longrightarrow> (\<forall>\<rho>\<in>Param. P1 z \<rho>)) \<and> (\<forall>z. z \<in> set9_T1_pre y \<longrightarrow> (\<forall>\<rho>\<in>Param. P1 z \<rho>))
    \<and> (\<forall>z. z \<in> set10_T1_pre y \<longrightarrow> (\<forall>\<rho>\<in>Param. P2 z \<rho>)) \<and> (\<forall>z. z \<in> set11_T1_pre y \<longrightarrow> (\<forall>\<rho>\<in>Param. P2 z \<rho>))
  \<longrightarrow> P1 (T1_ctor y) \<rho>)"
    "\<And>x \<rho>. \<rho> \<in> Param \<Longrightarrow> \<exists>y. T2_ctor y = T2_ctor x \<and>
    ((\<forall>z. z \<in> set8_T2_pre y \<longrightarrow> (\<forall>\<rho>\<in>Param. P1 z \<rho>)) \<and> (\<forall>z. z \<in> set9_T2_pre y \<longrightarrow> (\<forall>\<rho>\<in>Param. P1 z \<rho>))
    \<and> (\<forall>z. z \<in> set10_T2_pre y \<longrightarrow> (\<forall>\<rho>\<in>Param. P2 z \<rho>)) \<and> (\<forall>z. z \<in> set11_T2_pre y \<longrightarrow> (\<forall>\<rho>\<in>Param. P2 z \<rho>))
  \<longrightarrow> P2 (T2_ctor y) \<rho>)"
  shows "\<forall>\<rho>\<in>Param. P1 z \<rho> \<and> P2 z2 \<rho>"
  apply (unfold ball_conj_distrib)
  apply (rule subshape_induct[of "\<lambda>x. \<forall>\<rho>\<in>Param. P1 (TT1_abs x) \<rho>" "\<lambda>x. \<forall>\<rho>\<in>Param. P2 (TT2_abs x) \<rho>" "TT1_rep z" "TT2_rep z2", unfolded TT_abs_rep])
   apply (rule ballI)
  subgoal for x \<rho>
    apply (rule raw_T1.exhaust[of x])
    apply hypsubst_thin
    apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ P1]])
     apply (rule TT_total_abs_eq_iffs[THEN iffD2])
     apply (rule alpha_T1_alpha_T2.intros)
           apply (rule supp_id_bound bij_id id_on_id)+
     apply (unfold permute_raw_ids)
     apply (rule iffD2[OF T1_pre.mr_rel_map(3)])
                      apply (rule supp_id_bound bij_id)+
     apply (unfold inv_id id_o o_id eq_OO)
     apply (unfold relcompp_conversep_Grp)
     apply (rule iffD1[OF T1_pre.mr_rel_id[THEN fun_cong, THEN fun_cong]])
     apply (rule T1_pre.rel_refl_strong)
         apply (subst Grp_UNIV_id, unfold conversep_eq, rule refl)+
        apply (rule alpha_syms, rule TT_rep_abs[unfolded comp_apply[symmetric, of TT1_rep TT1_abs] comp_apply[symmetric, of TT2_rep TT2_abs]])+
    apply (unfold id_hid_o_hid)
    apply (unfold hidden_id_def)
    apply (subst T1_pre.map_comp[symmetric])
         apply (rule supp_id_bound bij_id)+
    apply (unfold T1_ctor_def[symmetric])
    apply (drule IHs(1))
    apply (erule exE)
    apply (erule conjE)
    apply (drule sym)
    apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ P1]])
     apply assumption
    apply (erule mp)
      (* REPEAT_DETERM *)
    apply (rule conjI)?
     apply (rule allI)
     apply (rule impI)
     apply (drule TT_inject0s[THEN iffD1])
     apply (erule exE conjE)+
     apply hypsubst
     apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
     apply (unfold image_id)
     apply (unfold image_comp[unfolded comp_def])?
     apply (erule imageE)
     apply hypsubst
     apply (subst permute_abs, (rule supp_id_bound bij_id | assumption)+)?
     apply (drule set_subshapess, assumption) (* ORELSE
     apply (drule set_subshape_permutess[rotated -1])
         prefer 5 (* 2 * nvars + 1 *)
    apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)
    apply (rule conjI)?
     apply (rule allI)
     apply (rule impI)
     apply (drule TT_inject0s[THEN iffD1])
     apply (erule exE conjE)+
     apply hypsubst
     apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
     apply (unfold image_id)
     apply (unfold image_comp[unfolded comp_def])?
     apply (erule imageE)
     apply hypsubst
     apply (subst permute_abs, (rule supp_id_bound bij_id | assumption)+)?
      (* apply (drule set_subshapess, assumption) ORELSE *)
     apply (drule set_subshape_permutess[rotated -1])
         prefer 5 (* 2 * nvars + 1 *)
         apply (assumption | rule supp_id_bound bij_id)+
      (* END ORELSE *)
      (* repeated *)
    apply (rule conjI)?
     apply (rule allI)
     apply (rule impI)
     apply (drule TT_inject0s[THEN iffD1])
     apply (erule exE conjE)+
     apply hypsubst
     apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
     apply (unfold image_id)
     apply (unfold image_comp[unfolded comp_def])?
     apply (erule imageE)
     apply hypsubst
     apply (subst permute_abs, (rule supp_id_bound bij_id | assumption)+)?
     apply (drule set_subshapess, assumption) (* ORELSE
     apply (drule set_subshape_permutess[rotated -1])
         prefer 5 (* 2 * nvars + 1 *)
    apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)
    apply (rule conjI)?
    apply (rule allI)
    apply (rule impI)
    apply (drule TT_inject0s[THEN iffD1])
    apply (erule exE conjE)+
    apply hypsubst
    apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
    apply (unfold image_id)
    apply (unfold image_comp[unfolded comp_def])?
    apply (erule imageE)
    apply hypsubst
    apply (subst permute_abs, (rule supp_id_bound bij_id | assumption)+)?
      (* apply (drule set_subshapess, assumption) ORELSE *)
    apply (drule set_subshape_permutess[rotated -1])
        prefer 5 (* 2 * nvars + 1 *)
        apply (assumption | rule supp_id_bound bij_id)+
      (* END ORELSE *)
    done
      (* second goal, same tactic *)
  apply (rule ballI)
  subgoal for x \<rho>
    apply (rule raw_T2.exhaust[of x])
    apply hypsubst_thin
    apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ P2]])
     apply (rule TT_total_abs_eq_iffs[THEN iffD2])
     apply (rule alpha_T1_alpha_T2.intros)
           apply (rule supp_id_bound bij_id id_on_id)+
     apply (unfold permute_raw_ids)
     apply (rule iffD2[OF T2_pre.mr_rel_map(3)])
                      apply (rule supp_id_bound bij_id)+
     apply (unfold inv_id id_o o_id eq_OO)
     apply (unfold relcompp_conversep_Grp)
     apply (rule iffD1[OF T2_pre.mr_rel_id[THEN fun_cong, THEN fun_cong]])
     apply (rule T2_pre.rel_refl_strong)
         apply (subst Grp_UNIV_id, unfold conversep_eq, rule refl)+
        apply (rule alpha_syms, rule TT_rep_abs[unfolded comp_apply[symmetric, of TT1_rep TT1_abs] comp_apply[symmetric, of TT2_rep TT2_abs]])+
    apply (unfold id_hid_o_hid)
    apply (unfold hidden_id_def)
    apply (subst T2_pre.map_comp[symmetric])
         apply (rule supp_id_bound bij_id)+
    apply (unfold T2_ctor_def[symmetric])
    apply (drule IHs(2))
    apply (erule exE)
    apply (erule conjE)
    apply (drule sym)
    apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ P2]])
     apply assumption
    apply (erule mp)
      (* REPEAT_DETERM *)
    apply (rule conjI)?
     apply (rule allI)
     apply (rule impI)
     apply (drule TT_inject0s[THEN iffD1])
     apply (erule exE conjE)+
     apply hypsubst
     apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
     apply (unfold image_id)
     apply (unfold image_comp[unfolded comp_def])?
     apply (erule imageE)
     apply hypsubst
     apply (subst permute_abs, (rule supp_id_bound bij_id | assumption)+)?
     apply (drule set_subshapess, assumption) (* ORELSE
     apply (drule set_subshape_permutess[rotated -1])
         prefer 5 (* 2 * nvars + 1 *)
    apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)
    apply (rule conjI)?
     apply (rule allI)
     apply (rule impI)
     apply (drule TT_inject0s[THEN iffD1])
     apply (erule exE conjE)+
     apply hypsubst
     apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
     apply (unfold image_id)
     apply (unfold image_comp[unfolded comp_def])?
     apply (erule imageE)
     apply hypsubst
     apply (subst permute_abs, (rule supp_id_bound bij_id | assumption)+)?
      (* apply (drule set_subshapess, assumption) ORELSE *)
     apply (drule set_subshape_permutess[rotated -1])
         prefer 5 (* 2 * nvars + 1 *)
         apply (assumption | rule supp_id_bound bij_id)+
      (* END ORELSE *)
      (* repeated *)
    apply (rule conjI)?
     apply (rule allI)
     apply (rule impI)
     apply (drule TT_inject0s[THEN iffD1])
     apply (erule exE conjE)+
     apply hypsubst
     apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
     apply (unfold image_id)
     apply (unfold image_comp[unfolded comp_def])?
     apply (erule imageE)
     apply hypsubst
     apply (subst permute_abs, (rule supp_id_bound bij_id | assumption)+)?
     apply (drule set_subshapess, assumption) (* ORELSE
     apply (drule set_subshape_permutess[rotated -1])
         prefer 5 (* 2 * nvars + 1 *)
    apply (assumption | rule supp_id_bound bij_id)+ *)
      (* repeated *)
    apply (rule conjI)?
    apply (rule allI)
    apply (rule impI)
    apply (drule TT_inject0s[THEN iffD1])
    apply (erule exE conjE)+
    apply hypsubst
    apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
    apply (unfold image_id)
    apply (unfold image_comp[unfolded comp_def])?
    apply (erule imageE)
    apply hypsubst
    apply (subst permute_abs, (rule supp_id_bound bij_id | assumption)+)?
      (* apply (drule set_subshapess, assumption) ORELSE *)
    apply (drule set_subshape_permutess[rotated -1])
        prefer 5 (* 2 * nvars + 1 *)
        apply (assumption | rule supp_id_bound bij_id)+
      (* END ORELSE *)
    done
  done

lemma fresh_induct_param:
  fixes K1::"'p \<Rightarrow> 'a::{var_T1_pre, var_T2_pre} set"
    and K2::"'p \<Rightarrow> 'b::{var_T1_pre, var_T2_pre} set"
  assumes "\<And>\<rho>. \<rho> \<in> Param \<Longrightarrow> |K1 \<rho>| <o |UNIV::'a set|"
      "\<And>\<rho>. \<rho> \<in> Param \<Longrightarrow> |K2 \<rho>| <o |UNIV::'b set|"
  and IHs: "\<And>x \<rho>.
    (\<And>z \<rho>. z \<in> set8_T1_pre x \<Longrightarrow> \<rho> \<in> Param \<Longrightarrow> P1 z \<rho>) \<Longrightarrow>
    (\<And>z \<rho>. z \<in> set9_T1_pre x \<Longrightarrow> \<rho> \<in> Param \<Longrightarrow> P1 z \<rho>) \<Longrightarrow>
    (\<And>z \<rho>. z \<in> set10_T1_pre x \<Longrightarrow> \<rho> \<in> Param \<Longrightarrow> P2 z \<rho>) \<Longrightarrow>
    (\<And>z \<rho>. z \<in> set11_T1_pre x \<Longrightarrow> \<rho> \<in> Param \<Longrightarrow> P2 z \<rho>) \<Longrightarrow>
    (\<And>z. z \<in> set5_T1_pre x \<Longrightarrow> z \<notin> K1 \<rho>) \<Longrightarrow>
    (\<And>z. z \<in> set6_T1_pre x \<Longrightarrow> z \<notin> K2 \<rho>) \<Longrightarrow>
    \<rho> \<in> Param \<Longrightarrow> P1 (T1_ctor x) \<rho>"
  "\<And>x \<rho>.
    (\<And>z \<rho>. z \<in> set8_T2_pre x \<Longrightarrow> \<rho> \<in> Param \<Longrightarrow> P1 z \<rho>) \<Longrightarrow>
    (\<And>z \<rho>. z \<in> set9_T2_pre x \<Longrightarrow> \<rho> \<in> Param \<Longrightarrow> P1 z \<rho>) \<Longrightarrow>
    (\<And>z \<rho>. z \<in> set10_T2_pre x \<Longrightarrow> \<rho> \<in> Param \<Longrightarrow> P2 z \<rho>) \<Longrightarrow>
    (\<And>z \<rho>. z \<in> set11_T2_pre x \<Longrightarrow> \<rho> \<in> Param \<Longrightarrow> P2 z \<rho>) \<Longrightarrow>
    (\<And>z. z \<in> set5_T2_pre x \<Longrightarrow> z \<notin> K1 \<rho>) \<Longrightarrow>
    (\<And>z. z \<in> set6_T2_pre x \<Longrightarrow> z \<notin> K2 \<rho>) \<Longrightarrow>
    \<rho> \<in> Param \<Longrightarrow> P2 (T2_ctor x) \<rho>"
shows "\<forall>\<rho>\<in>Param. P1 z \<rho> \<and> P2 z2 \<rho>"
  apply (rule existential_induct)
  subgoal for x \<rho>
    apply (rule fresh_cases(1)[of "K1 \<rho>" "K2 \<rho>" "T1_ctor x"])
      apply (erule assms)+
    apply (rule exI)
    apply (rule conjI)
     apply (erule sym)
    apply (rule impI)
    apply (erule conjE)+
    apply (rule IHs)
    (* for i in [~rec_vars - 2 ..~3] *)
          apply (rotate_tac -6)
          apply (erule allE)
          apply (erule impE)
           apply assumption
          apply (erule ballE)
           apply assumption
          apply (rotate_tac -1)
          apply (erule contrapos_np)
          apply assumption
    (* repeated *)
          apply (rotate_tac -5)
          apply (erule allE)
          apply (erule impE)
           apply assumption
          apply (erule ballE)
           apply assumption
          apply (rotate_tac -1)
          apply (erule contrapos_np)
          apply assumption
    (* repeated *)
          apply (rotate_tac -4)
          apply (erule allE)
          apply (erule impE)
           apply assumption
          apply (erule ballE)
           apply assumption
          apply (rotate_tac -1)
          apply (erule contrapos_np)
          apply assumption
    (* repeated *)
          apply (rotate_tac -3)
          apply (erule allE)
          apply (erule impE)
           apply assumption
          apply (erule ballE)
           apply assumption
          apply (rotate_tac -1)
          apply (erule contrapos_np)
       apply assumption
      (* END for *)
      apply (erule iffD1[OF disjoint_iff, THEN spec, THEN mp], assumption)+
    apply assumption
    done
  (* second goal, same tactic *)
  subgoal for x \<rho>
    apply (rule fresh_cases(2)[of "K1 \<rho>" "K2 \<rho>" "T2_ctor x"])
      apply (erule assms)+
    apply (rule exI)
    apply (rule conjI)
     apply (erule sym)
    apply (rule impI)
    apply (erule conjE)+
    apply (rule IHs)
    (* for i in [~rec_vars - 2 ..~3] *)
          apply (rotate_tac -6)
          apply (erule allE)
          apply (erule impE)
           apply assumption
          apply (erule ballE)
           apply assumption
          apply (rotate_tac -1)
          apply (erule contrapos_np)
          apply assumption
    (* repeated *)
          apply (rotate_tac -5)
          apply (erule allE)
          apply (erule impE)
           apply assumption
          apply (erule ballE)
           apply assumption
          apply (rotate_tac -1)
          apply (erule contrapos_np)
          apply assumption
    (* repeated *)
          apply (rotate_tac -4)
          apply (erule allE)
          apply (erule impE)
           apply assumption
          apply (erule ballE)
           apply assumption
          apply (rotate_tac -1)
          apply (erule contrapos_np)
          apply assumption
    (* repeated *)
          apply (rotate_tac -3)
          apply (erule allE)
          apply (erule impE)
           apply assumption
          apply (erule ballE)
           apply assumption
          apply (rotate_tac -1)
          apply (erule contrapos_np)
       apply assumption
      (* END for *)
      apply (erule iffD1[OF disjoint_iff, THEN spec, THEN mp], assumption)+
    apply assumption
    done
    done

lemma permute_congs:
  fixes f1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and f2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
    and g1::"'a::{var_T1_pre,var_T2_pre} \<Rightarrow> 'a" and g2::"'b::{var_T1_pre,var_T2_pre} \<Rightarrow> 'b"
    and x::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1"
    and x2::"('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2"
  assumes "bij f1" "|supp f1| <o |UNIV::'a set|" "bij f2" "|supp f2| <o |UNIV::'b set|"
    and "bij g1" "|supp g1| <o |UNIV::'a set|" "bij g2" "|supp g2| <o |UNIV::'b set|"
  shows
    "(\<And>a. a \<in> FVars_T11 x \<Longrightarrow> f1 a = g1 a) \<Longrightarrow> (\<And>a. a \<in> FVars_T12 x \<Longrightarrow> f2 a = g2 a) \<Longrightarrow> permute_T1 f1 f2 x = permute_T1 g1 g2 x"
    "(\<And>a. a \<in> FVars_T21 x2 \<Longrightarrow> f1 a = g1 a) \<Longrightarrow> (\<And>a. a \<in> FVars_T22 x2 \<Longrightarrow> f2 a = g2 a) \<Longrightarrow> permute_T2 f1 f2 x2 = permute_T2 g1 g2 x2"
   apply (unfold atomize_all atomize_imp eq_on_def[symmetric] permute_T1_def permute_T2_def FVars_defs)
   apply (rule impI)+
   apply (rule TT_total_abs_eq_iffs[THEN iffD2])
   apply (rule alpha_bijs)
             apply (rule assms)+
     apply assumption+
   apply (rule alpha_refls)
    (* second goal, same tactic *)
  apply (rule impI)+
  apply (rule TT_total_abs_eq_iffs[THEN iffD2])
  apply (rule alpha_bijs)
            apply (rule assms)+
    apply assumption+
  apply (rule alpha_refls)
  done

lemmas permute_cong_ids = permute_congs[OF _ _ _ _ bij_id supp_id_bound bij_id supp_id_bound, unfolded permute_ids id_apply]

lemma nnoclash_noclashs:
  "noclash_T1 x = noclash_raw_T1 (map_T1_pre id id id id id id id TT1_rep TT1_rep TT2_rep TT2_rep x)"
  "noclash_T2 x2 = noclash_raw_T2 (map_T2_pre id id id id id id id TT1_rep TT1_rep TT2_rep TT2_rep x2)"
  apply (unfold noclash_T1_def noclash_T2_def noclash_raw_T1_def noclash_raw_T2_def)
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id)
  apply (unfold image_comp[unfolded comp_def] FVars_defs[symmetric])
  apply (rule refl)
  (* second goal, same tactic *)
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id)
  apply (unfold image_comp[unfolded comp_def] FVars_defs[symmetric])
  apply (rule refl)
  done

ML \<open>
val fp_res = { fp = BNF_Util.Least_FP,
    binding_relation = [[1, 3], [1]],
    rec_vars = [2, 2],
    quotient_fps = [
      { T = @{typ "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1"},
        ctor = @{term "T1_ctor :: _ \<Rightarrow> ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1"},
        rename = @{term "permute_T1 :: _ => _ => _ => ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1"},
        FVars = [
          @{term "FVars_T11 :: ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1 \<Rightarrow> _"},
          @{term "FVars_T12 :: ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1 \<Rightarrow> _"}
        ],
        noclash = (
          @{term "noclash_T1 :: ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1' \<Rightarrow> _"},
          @{thm noclash_T1_def}
       ),
       inject = @{thm TT_inject0s(1)},
       rename_id0 = @{thm permute_id0s(1)},
       rename_id = @{thm permute_ids(1)},
       rename_comp0 = @{thm permute_comp0s(1)},
       rename_comp = @{thm permute_comps(1)},
       FVars_ctors = @{thms FVars_ctors(1-2)},
       FVars_renames = @{thms FVars_permutes(1-2)},
       FVars_intross = [@{thms FVars_intros(1-6)}, @{thms FVars_intros(13-17)}],
       card_of_FVars_bounds = @{thms FVars_bds(1-2)},
       card_of_FVars_bound_UNIVs = @{thms FVars_bd_UNIVs(1-2)},
       inner = {
         abs = @{term "TT1_abs :: _ \<Rightarrow> ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1"},
         rep = @{term "TT1_rep :: ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T1 \<Rightarrow> _"},
         ctor_def = @{thm T1_ctor_def},
         rename_def = @{thm permute_T1_def},
         FVars_defs = @{thms FVars_defs(1-2)},
         nnoclash_noclash = @{thm nnoclash_noclashs(1)},
         alpha_quotient_sym = @{thm TT_rep_abs_syms(1)},
         total_abs_eq_iff = @{thm TT_total_abs_eq_iffs(1)},
         abs_rep = @{thm TT_abs_rep(1)},
         rep_abs = @{thm TT_rep_abs(1)},
         abs_ctor = @{thm TT_abs_ctors(1)},
         rename_ctor = @{thm permute_simps(1)},
         rename_cong_id = @{thm permute_cong_ids(1)},
         rename_bij = @{thm permute_bijs(1)},
         rename_inv_simp = @{thm permute_inv_simps(1)},
         fresh_co_induct_param = @{thm fresh_induct_param},
         fresh_co_induct = @{thm refl}, (* TODO: check if needed *)
         fresh_induct_param_no_clash = NONE
       }
     },
     { T = @{typ "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2"},
        ctor = @{term "T2_ctor :: _ \<Rightarrow> ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2"},
        rename = @{term "permute_T2 :: _ => _ => _ => ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2"},
        FVars = [
          @{term "FVars_T21 :: ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2 \<Rightarrow> _"},
          @{term "FVars_T22 :: ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2 \<Rightarrow> _"}
        ],
        noclash = (
          @{term "noclash_T2 :: ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2' \<Rightarrow> _"},
          @{thm noclash_T2_def}
       ),
       inject = @{thm TT_inject0s(2)},
       rename_id0 = @{thm permute_id0s(2)},
       rename_id = @{thm permute_ids(2)},
       rename_comp0 = @{thm permute_comp0s(2)},
       rename_comp = @{thm permute_comps(2)},
       FVars_ctors = @{thms FVars_ctors(3-4)},
       FVars_renames = @{thms FVars_permutes(3-4)},
       FVars_intross = [@{thms FVars_intros(7-12)}, @{thms FVars_intros(18-22)}],
       card_of_FVars_bounds = @{thms FVars_bds(3-4)},
       card_of_FVars_bound_UNIVs = @{thms FVars_bd_UNIVs(3-4)},
       inner = {
        abs = @{term "TT2_abs :: _ \<Rightarrow> ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2"},
        rep = @{term "TT2_rep :: ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) T2 \<Rightarrow> _"},
        ctor_def = @{thm T2_ctor_def},
        rename_def = @{thm permute_T2_def},
        FVars_defs = @{thms FVars_defs(3-4)},
        nnoclash_noclash = @{thm nnoclash_noclashs(2)},
        alpha_quotient_sym = @{thm TT_rep_abs_syms(2)},
        total_abs_eq_iff = @{thm TT_total_abs_eq_iffs(2)},
        abs_rep = @{thm TT_abs_rep(2)},
        rep_abs = @{thm TT_rep_abs(2)},
        abs_ctor = @{thm TT_abs_ctors(2)},
        rename_ctor = @{thm permute_simps(2)},
        rename_cong_id = @{thm permute_cong_ids(2)},
        rename_bij = @{thm permute_bijs(2)},
        rename_inv_simp = @{thm permute_inv_simps(2)},
        fresh_co_induct_param = @{thm fresh_induct_param},
        fresh_co_induct = @{thm refl}, (* TODO: check if needed *)
        fresh_induct_param_no_clash = NONE
     }
   }
 ],
 raw_fps = [
  { T = @{typ "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"},
    ctor = @{term "raw_T1_ctor :: _ \<Rightarrow> ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"},
    rename = @{term "permute_raw_T1 :: _ => _ => _ => ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1"},
    FVars = [
      @{term "FVars_raw_T11 :: ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1 \<Rightarrow> _"},
      @{term "FVars_raw_T12 :: ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1 \<Rightarrow> _"}
    ],
    noclash = (
      @{term "noclash_raw_T1 :: ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1' \<Rightarrow> _"},
      @{thm noclash_raw_T1_def}
   ),
   inject = @{thm raw_T1.inject},
   rename_id0 = @{thm permute_raw_id0s(1)},
   rename_id = @{thm permute_raw_ids(1)},
   rename_comp0 = @{thm permute_raw_comp0s(1)},
   rename_comp = @{thm permute_raw_comps(1)},
   FVars_ctors = @{thms FVars_raw_ctors(1-2)},
   FVars_renames = @{thms FVars_raw_permutes(1-2)},
   FVars_intross = [@{thms FVars_raw_intros(1-6)}, @{thms FVars_raw_intros(13-17)}],
   card_of_FVars_bounds = @{thms FVars_raw_bds(1-2)},
   card_of_FVars_bound_UNIVs = @{thms FVars_raw_bd_UNIVs(1-2)},
   inner = {
     alpha = @{term "alpha_T1 :: ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1 \<Rightarrow> _ \<Rightarrow> _"},
     subshape_rel = SOME @{term "{(x, y). case x of
        Inl t1 \<Rightarrow> (case y of Inl t1' \<Rightarrow> subshape_T1_T1 t1 t1' | Inr t2 \<Rightarrow> subshape_T1_T2 t1 t2)
      | Inr t2 \<Rightarrow> (case y of Inl t1 \<Rightarrow> subshape_T2_T1 t2 t1 | Inr t2' \<Rightarrow> subshape_T2_T2 t2 t2')
     } :: ((('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1 + _) \<times> _) set"},
     exhaust = @{thm raw_T1.exhaust},
     rename_simp = @{thm permute_simps(1)},
     alpha_refl = @{thm alpha_refls(1)},
     alpha_sym = @{thm alpha_syms(1)},
     alpha_trans = @{thm alpha_trans(1)},
     alpha_bij = @{thm alpha_bijs(1)},
     alpha_bij_eq = @{thm alpha_bij_eqs(1)},
     alpha_FVarss = @{thms alpha_FVars(1-2)},
     alpha_intro = @{thm alpha_T1_alpha_T2.intros(1)},
     alpha_elim = @{thm alpha_T1.cases},
     subshapes = SOME [
       @{term "subshape_T1_T1 :: _ => ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1 \<Rightarrow> _"},
       @{term "subshape_T2_T1 :: _ => ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1 \<Rightarrow> _"}
     ],
     wf_subshape = SOME @{thm wf_subshape},
     set_subshapess = SOME [@{thms set_subshapess(1-2)}, @{thms set_subshapess(3-4)}],
     set_subshape_imagess = SOME [@{thms set_subshape_permutess(1-2)}, @{thms set_subshape_permutess(3-4)}],
     subshape_induct = SOME @{thm subshape_induct}
   }
 },
 { T = @{typ "('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"},
    ctor = @{term "raw_T2_ctor :: _ \<Rightarrow> ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"},
    rename = @{term "permute_raw_T2 :: _ => _ => _ => ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2"},
    FVars = [
      @{term "FVars_raw_T21 :: ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2 \<Rightarrow> _"},
      @{term "FVars_raw_T22 :: ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2 \<Rightarrow> _"}
    ],
    noclash = (
      @{term "noclash_raw_T2 :: ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2' \<Rightarrow> _"},
      @{thm noclash_raw_T2_def}
   ),
   inject = @{thm raw_T2.inject},
   rename_id0 = @{thm permute_raw_id0s(2)},
   rename_id = @{thm permute_raw_ids(2)},
   rename_comp0 = @{thm permute_raw_comp0s(2)},
   rename_comp = @{thm permute_raw_comps(2)},
   FVars_ctors = @{thms FVars_raw_ctors(3-4)},
   FVars_renames = @{thms FVars_raw_permutes(3-4)},
   FVars_intross = [@{thms FVars_raw_intros(7-12)}, @{thms FVars_raw_intros(18-22)}],
   card_of_FVars_bounds = @{thms FVars_raw_bds(3-4)},
   card_of_FVars_bound_UNIVs = @{thms FVars_raw_bd_UNIVs(3-4)},
   inner = {
     alpha = @{term "alpha_T2 :: ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2 \<Rightarrow> _ \<Rightarrow> _"},
     subshape_rel = SOME @{term "{(x, y). case x of
        Inl t1 \<Rightarrow> (case y of Inl t1' \<Rightarrow> subshape_T1_T1 t1 t1' | Inr t2 \<Rightarrow> subshape_T1_T2 t1 t2)
      | Inr t2 \<Rightarrow> (case y of Inl t1 \<Rightarrow> subshape_T2_T1 t2 t1 | Inr t2' \<Rightarrow> subshape_T2_T2 t2 t2')
     } :: ((('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T1 + _) \<times> _) set"},
     exhaust = @{thm raw_T2.exhaust},
     rename_simp = @{thm permute_simps(2)},
     alpha_refl = @{thm alpha_refls(2)},
     alpha_sym = @{thm alpha_syms(2)},
     alpha_trans = @{thm alpha_trans(2)},
     alpha_bij = @{thm alpha_bijs(2)},
     alpha_bij_eq = @{thm alpha_bij_eqs(2)},
     alpha_FVarss = @{thms alpha_FVars(3-4)},
     alpha_intro = @{thm alpha_T1_alpha_T2.intros(2)},
     alpha_elim = @{thm alpha_T2.cases},
     subshapes = SOME [
       @{term "subshape_T1_T2 :: _ => ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2 \<Rightarrow> _"},
       @{term "subshape_T2_T2 :: _ => ('a::{var_T1_pre,var_T2_pre}, 'b::{var_T1_pre,var_T2_pre}, 'c::{var_T1_pre,var_T2_pre}, 'd) raw_T2 \<Rightarrow> _"}
     ],
     wf_subshape = SOME @{thm wf_subshape},
     set_subshapess = SOME [@{thms set_subshapess(5-6)}, @{thms set_subshapess(7-8)}],
     set_subshape_imagess = SOME [@{thms set_subshape_permutess(5-6)}, @{thms set_subshape_permutess(7-8)}],
     subshape_induct = SOME @{thm subshape_induct}
   }
 } ],
 pre_mrbnfs = map (the o MRBNF_Def.mrbnf_of @{context}) ["Composition.T1_pre", "Composition.T2_pre"]
} : MRBNF_FP_Def_Sugar.fp_result
\<close>

local_setup \<open>MRBNF_FP_Def_Sugar.register_fp_results [fp_res]\<close>

end