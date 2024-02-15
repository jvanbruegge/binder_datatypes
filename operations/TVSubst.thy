theory TVSubst
  imports "./Fixpoint"
begin

(* Free variable injections *)
consts eta11 :: "'var \<Rightarrow> ('var, 'tyvar, 'a, 'b, 'bvar, 'btyvar, 'rec1, 'brec1, 'rec2, 'brec2) T1_pre"
consts eta12 :: "'tyvar \<Rightarrow> ('var, 'tyvar, 'a, 'b, 'bvar, 'btyvar, 'rec1, 'brec1, 'rec2, 'brec2) T1_pre"
consts eta21 :: "'var \<Rightarrow> ('var, 'tyvar, 'a, 'b, 'bvar, 'btyvar, 'rec1, 'brec1, 'rec2, 'brec2) T2_pre"

axiomatization where
  eta_free11: "set1_T1_pre (eta11 a) = {a::'var::{var_T1_pre, var_T2_pre}}"
and eta_inj11: "eta11 a = eta11 a' \<Longrightarrow> a = a'"
and eta_compl_free11: "x \<notin> range eta11 \<Longrightarrow> set1_T1_pre (x::('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b, 'bvar::{var_T1_pre, var_T2_pre}, 'btyvar::{var_T1_pre, var_T2_pre}, 'rec1, 'brec1, 'rec2, 'brec2) T1_pre) = {}"
and eta_natural11: "|supp (f1::'x1::{var_T1_pre, var_T2_pre} \<Rightarrow> 'x1)| <o |UNIV::'x1 set| \<Longrightarrow> |supp (f2::'x2::{var_T1_pre, var_T2_pre} \<Rightarrow> 'x2)| <o |UNIV::'x2 set|
                   \<Longrightarrow> bij f3 \<Longrightarrow> |supp (f3::'x3::{var_T1_pre, var_T2_pre} \<Rightarrow> 'x3)| <o |UNIV::'x3 set| \<Longrightarrow> bij f4 \<Longrightarrow> |supp (f4::'x4::{var_T1_pre, var_T2_pre} \<Rightarrow> 'x4)| <o |UNIV::'x4 set|
                   \<Longrightarrow> map_T1_pre f1 f2 id id f3 f4 f5 f6 f7 f8 \<circ> eta11 = eta11 \<circ> f1"

and eta_free12: "set2_T1_pre (eta12 b) = {b::'tyvar::{var_T1_pre, var_T2_pre}}"
and eta_inj12: "eta12 b = eta12 b' \<Longrightarrow> b = b'"
and eta_compl_free12: "x \<notin> range eta12 \<Longrightarrow> set2_T1_pre (x::('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b, 'bvar::{var_T1_pre, var_T2_pre}, 'btyvar::{var_T1_pre, var_T2_pre}, 'rec1, 'brec1, 'rec2, 'brec2) T1_pre) = {}"
and eta_natural12: "|supp (f1::'x1::{var_T1_pre, var_T2_pre} \<Rightarrow> 'x1)| <o |UNIV::'x1 set| \<Longrightarrow> |supp (f2::'x2::{var_T1_pre, var_T2_pre} \<Rightarrow> 'x2)| <o |UNIV::'x2 set|
                   \<Longrightarrow> bij f3 \<Longrightarrow> |supp (f3::'x3::{var_T1_pre, var_T2_pre} \<Rightarrow> 'x3)| <o |UNIV::'x3 set| \<Longrightarrow> bij f4 \<Longrightarrow> |supp (f4::'x4::{var_T1_pre, var_T2_pre} \<Rightarrow> 'x4)| <o |UNIV::'x4 set|
                   \<Longrightarrow> map_T1_pre f1 f2 id id f3 f4 f5 f6 f7 f8 \<circ> eta12 = eta12 \<circ> f2"

and eta_free21: "set1_T2_pre (eta21 c) = {c::'var::{var_T1_pre, var_T2_pre}}"
and eta_inj21: "eta21 c = eta21 c' \<Longrightarrow> c = c'"
and eta_compl_free21: "y \<notin> range eta21 \<Longrightarrow> set1_T2_pre (y::('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b, 'bvar::{var_T1_pre, var_T2_pre}, 'btyvar::{var_T1_pre, var_T2_pre}, 'rec1, 'brec1, 'rec2, 'brec2) T2_pre) = {}"
and eta_natural21: "|supp (f1::'x1::{var_T1_pre, var_T2_pre} \<Rightarrow> 'x1)| <o |UNIV::'x1 set| \<Longrightarrow> |supp (f2::'x2::{var_T1_pre, var_T2_pre} \<Rightarrow> 'x2)| <o |UNIV::'x2 set|
                   \<Longrightarrow> bij f3 \<Longrightarrow> |supp (f3::'x3::{var_T1_pre, var_T2_pre} \<Rightarrow> 'x3)| <o |UNIV::'x3 set| \<Longrightarrow> bij f4 \<Longrightarrow> |supp (f4::'x4::{var_T1_pre, var_T2_pre} \<Rightarrow> 'x4)| <o |UNIV::'x4 set|
                   \<Longrightarrow> map_T2_pre f1 f2 id id f3 f4 f5 f6 f7 f8 \<circ> eta21 = eta21 \<circ> f1"

definition VVr11 :: "'var \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T1" where "VVr11 \<equiv> T1_ctor \<circ> eta11"
definition VVr12 :: "'tyvar \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T1" where "VVr12 \<equiv> T1_ctor \<circ> eta12"
definition VVr21 :: "'var \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T2" where "VVr21 \<equiv> T2_ctor \<circ> eta21"

definition SSupp11 :: "('var \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T1) \<Rightarrow> 'var set" where
  "SSupp11 f \<equiv> { x. f x \<noteq> VVr11 x }"
definition SSupp12 :: "('tyvar \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T1) \<Rightarrow> 'tyvar set" where
  "SSupp12 f \<equiv> { x. f x \<noteq> VVr12 x }"
definition SSupp21 :: "('var \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T2) \<Rightarrow> 'var set" where
  "SSupp21 f \<equiv> { x. f x \<noteq> VVr21 x }"

definition IImsupp11_1 :: "('var \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T1) \<Rightarrow> 'var set" where
  "IImsupp11_1 f \<equiv> SSupp11 f \<union> \<Union>((FFVars_T11 \<circ> f) ` SSupp11 f)"
definition IImsupp11_2 :: "('var \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T1) \<Rightarrow> 'tyvar set" where
  "IImsupp11_2 f \<equiv> \<Union>((FFVars_T12 \<circ> f) ` SSupp11 f)"
definition IImsupp12_1 :: "('tyvar \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T1) \<Rightarrow> 'var set" where
  "IImsupp12_1 f \<equiv> \<Union>((FFVars_T11 \<circ> f) ` SSupp12 f)"
definition IImsupp12_2 :: "('tyvar \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T1) \<Rightarrow> 'tyvar set" where
  "IImsupp12_2 f \<equiv> SSupp12 f \<union> \<Union>((FFVars_T12 \<circ> f) ` SSupp12 f)"
definition IImsupp21_1 :: "('var \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T2) \<Rightarrow> 'var set" where
  "IImsupp21_1 f \<equiv> SSupp21 f \<union> \<Union>((FFVars_T21 \<circ> f) ` SSupp21 f)"
definition IImsupp21_2 :: "('var \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T2) \<Rightarrow> 'tyvar set" where
  "IImsupp21_2 f \<equiv> \<Union>((FFVars_T22 \<circ> f) ` SSupp21 f)"

definition isVVr11 :: "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T1 \<Rightarrow> bool" where
  "isVVr11 x \<equiv> \<exists>a. x = VVr11 a"
definition isVVr12 :: "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T1 \<Rightarrow> bool" where
  "isVVr12 x \<equiv> \<exists>a. x = VVr12 a"
definition isVVr21 :: "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T2 \<Rightarrow> bool" where
  "isVVr21 x \<equiv> \<exists>a. x = VVr21 a"

definition asVVr11 :: "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T1 \<Rightarrow> 'var" where
  "asVVr11 x \<equiv> (if isVVr11 x then SOME a. x = VVr11 a else undefined)"
definition asVVr12 :: "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T1 \<Rightarrow> 'tyvar" where
  "asVVr12 x \<equiv> (if isVVr12 x then SOME a. x = VVr12 a else undefined)"
definition asVVr21 :: "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) T2 \<Rightarrow> 'var" where
  "asVVr21 x \<equiv> (if isVVr21 x then SOME a. x = VVr21 a else undefined)"

type_synonym ('var, 'tyvar, 'a, 'b) SSfun11 = "'var \<Rightarrow> ('var, 'tyvar, 'a, 'b) T1"
type_synonym ('var, 'tyvar, 'a, 'b) SSfun12 = "'tyvar \<Rightarrow> ('var, 'tyvar, 'a, 'b) T1"
type_synonym ('var, 'tyvar, 'a, 'b) SSfun21 = "'var \<Rightarrow> ('var, 'tyvar, 'a, 'b) T2"

definition compSS11 :: "('var \<Rightarrow> 'var) \<Rightarrow> ('tyvar \<Rightarrow> 'tyvar) \<Rightarrow> ('var, 'tyvar, 'a, 'b) SSfun11 \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) SSfun11" where
  "compSS11 f1 f2 h \<equiv> rrename_T1 f1 f2 \<circ> h \<circ> inv f1"
definition compSS12 :: "('var \<Rightarrow> 'var) \<Rightarrow> ('tyvar \<Rightarrow> 'tyvar) \<Rightarrow> ('var, 'tyvar, 'a, 'b) SSfun12 \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) SSfun12" where
  "compSS12 f1 f2 h \<equiv> rrename_T1 f1 f2 \<circ> h \<circ> inv f2"
definition compSS21 :: "('var \<Rightarrow> 'var) \<Rightarrow> ('tyvar \<Rightarrow> 'tyvar) \<Rightarrow> ('var, 'tyvar, 'a, 'b) SSfun21 \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) SSfun21" where
  "compSS21 f1 f2 h \<equiv> rrename_T2 f1 f2 \<circ> h \<circ> inv f1"
lemmas compSS_defs = compSS11_def compSS12_def compSS21_def

type_synonym ('var, 'tyvar, 'a, 'b) P = "('var, 'tyvar, 'a, 'b) SSfun11 \<times> ('var, 'tyvar, 'a, 'b) SSfun12 \<times> ('var, 'tyvar, 'a, 'b) SSfun21"
type_synonym ('var, 'tyvar, 'a, 'b) U1 = "('var, 'tyvar, 'a, 'b) T1"
type_synonym ('var, 'tyvar, 'a, 'b) U2 = "('var, 'tyvar, 'a, 'b) T2"

definition U1ctor :: "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b, 'var, 'tyvar, ('var, 'tyvar, 'a, 'b) T1 \<times> (('var, 'tyvar, 'a, 'b) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1), ('var, 'tyvar, 'a, 'b) T1 \<times> (('var, 'tyvar, 'a, 'b) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1),
  ('var, 'tyvar, 'a, 'b) T2 \<times> (('var, 'tyvar, 'a, 'b) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2), ('var, 'tyvar, 'a, 'b) T2 \<times> (('var, 'tyvar, 'a, 'b) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2)) T1_pre \<Rightarrow> ('var, 'tyvar, 'a, 'b) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1" where
  "U1ctor y p \<equiv> case p of (f1, f2, f3) \<Rightarrow> if isVVr11 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) then
    f1 (asVVr11 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y))) else (
  if isVVr12 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) then
    f2 (asVVr12 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y))) else (
  T1_ctor (map_T1_pre id id id id id id ((\<lambda>R. R (f1, f2, f3)) \<circ> snd) ((\<lambda>R. R (f1, f2, f3)) \<circ> snd) ((\<lambda>R. R (f1, f2, f3)) \<circ> snd) ((\<lambda>R. R (f1, f2, f3)) \<circ> snd) y)
))"
definition U2ctor :: "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b, 'var, 'tyvar, ('var, 'tyvar, 'a, 'b) T1 \<times> (('var, 'tyvar, 'a, 'b) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1), ('var, 'tyvar, 'a, 'b) T1 \<times> (('var, 'tyvar, 'a, 'b) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1),
  ('var, 'tyvar, 'a, 'b) T2 \<times> (('var, 'tyvar, 'a, 'b) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2), ('var, 'tyvar, 'a, 'b) T2 \<times> (('var, 'tyvar, 'a, 'b) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2)) T2_pre \<Rightarrow> ('var, 'tyvar, 'a, 'b) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2" where
  "U2ctor y p \<equiv> case p of (f1, f2, f3) \<Rightarrow> if isVVr21 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) then
    f3 (asVVr21 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y))) else (
  T2_ctor (map_T2_pre id id id id id id ((\<lambda>R. R (f1, f2, f3)) \<circ> snd) ((\<lambda>R. R (f1, f2, f3)) \<circ> snd) ((\<lambda>R. R (f1, f2, f3)) \<circ> snd) ((\<lambda>R. R (f1, f2, f3)) \<circ> snd) y)
)"

definition PFVars_1 :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) P \<Rightarrow> 'var set" where
  "PFVars_1 p \<equiv> case p of (f1, f2, f3) \<Rightarrow> IImsupp11_1 f1 \<union> IImsupp12_1 f2 \<union> IImsupp21_1 f3"
definition PFVars_2 :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) P \<Rightarrow> 'tyvar set" where
  "PFVars_2 p \<equiv> case p of (f1, f2, f3) \<Rightarrow> IImsupp11_2 f1 \<union> IImsupp12_2 f2 \<union> IImsupp21_2 f3"

definition Pmap :: "('var \<Rightarrow> 'var) \<Rightarrow> ('tyvar \<Rightarrow> 'tyvar) \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) P" where
  "Pmap g1 g2 p \<equiv> case p of (f1, f2, f3) \<Rightarrow> (compSS11 g1 g2 f1, compSS12 g1 g2 f2, compSS21 g1 g2 f3)"

definition avoiding_set1 :: "'var::{var_T1_pre,var_T2_pre} set" where "avoiding_set1 \<equiv> {}"
definition avoiding_set2 :: "'tyvar::{var_T1_pre,var_T2_pre} set" where "avoiding_set2 \<equiv> {}"

abbreviation "U1FVars_1 \<equiv> \<lambda>(_::('var, 'tyvar, 'a, 'b) T1) (x::('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) T1). FFVars_T11 x"
abbreviation "U1FVars_2 \<equiv> \<lambda>(_::('var, 'tyvar, 'a, 'b) T1) (x::('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) T1). FFVars_T12 x"
abbreviation "U2FVars_1 \<equiv> \<lambda>(_::('var, 'tyvar, 'a, 'b) T2) (x::('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) T2). FFVars_T21 x"
abbreviation "U2FVars_2 \<equiv> \<lambda>(_::('var, 'tyvar, 'a, 'b) T2) (x::('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) T2). FFVars_T22 x"

abbreviation "U1map \<equiv> \<lambda>f1 f2 (_::('var, 'tyvar, 'a, 'b) T1) (x::('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) T1). rrename_T1 f1 f2 x"
abbreviation "U2map \<equiv> \<lambda>f1 f2 (_::('var, 'tyvar, 'a, 'b) T2) (x::('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) T2). rrename_T2 f1 f2 x"

definition valid_P :: "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) P \<Rightarrow> bool" where
  "valid_P p \<equiv> case p of (f1, f2, f3) \<Rightarrow>
  |SSupp11 f1| <o cmin |UNIV::'var set| |UNIV::'tyvar set|
  \<and> |SSupp12 f2| <o cmin |UNIV::'var set| |UNIV::'tyvar set|
  \<and> |SSupp21 f3| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"

(**********************************************************************)
(*                               PROOFS                               *)
(**********************************************************************)

lemmas Cinfinite_UNIV = conjI[OF T1_pre.UNIV_cinfinite card_of_Card_order]
lemmas Cinfinite_card = cmin_Cinfinite[OF Cinfinite_UNIV Cinfinite_UNIV]
lemmas regularCard_card = cmin_regularCard[OF T1_pre.var_regular T1_pre.var_regular Cinfinite_UNIV Cinfinite_UNIV]
lemmas Un_bound = regularCard_Un[OF conjunct2[OF Cinfinite_card] conjunct1[OF Cinfinite_card] regularCard_card]
lemmas UNION_bound = regularCard_UNION[OF conjunct2[OF Cinfinite_card] conjunct1[OF Cinfinite_card] regularCard_card]

lemma Supp_VVr_empty:
  "SSupp11 VVr11 = {}"
  "SSupp12 VVr12 = {}"
  "SSupp21 VVr21 = {}"
    apply -
    apply (unfold SSupp11_def)
    apply (rule iffD2[OF set_eq_iff])
    apply (rule allI)
    apply (unfold mem_Collect_eq HOL.simp_thms(6) empty_iff)
    apply (rule not_True_eq_False)
    (* copied from above *)
   apply (unfold SSupp12_def)
   apply (rule iffD2[OF set_eq_iff])
   apply (rule allI)
   apply (unfold mem_Collect_eq HOL.simp_thms(6) empty_iff)
   apply (rule not_True_eq_False)
    (* copied from above *)
  apply (unfold SSupp21_def)
  apply (rule iffD2[OF set_eq_iff])
  apply (rule allI)
  apply (unfold mem_Collect_eq HOL.simp_thms(6) empty_iff)
  apply (rule not_True_eq_False)
  done

lemma SSupp_VVr_bound:
  "|SSupp11 VVr11| <o |UNIV::'x set|"
  "|SSupp12 VVr12| <o |UNIV::'x set|"
  "|SSupp21 VVr21| <o |UNIV::'x set|"
    apply (unfold Supp_VVr_empty)
    apply (rule emp_bound)+
  done

lemma VVr_injs:
  "VVr11 x = VVr11 x' \<Longrightarrow> x = x'"
  "VVr12 x = VVr12 x' \<Longrightarrow> x = x'"
  "VVr21 y = VVr21 y' \<Longrightarrow> y = y'"
    apply -
    (* EVERY' (map ... VVr_defs eta_injs eta_naturals) *)
    apply (unfold VVr11_def comp_def)
    apply (rule eta_inj11)
    apply (drule T1.TT_injects0[THEN iffD1])
    apply (erule exE conjE)+
    apply (drule trans[rotated])
     apply (rule sym)
     apply (rule trans)
      apply (rule fun_cong[OF eta_natural11, unfolded comp_def])
           apply (assumption | rule supp_id_bound bij_id)+
     apply (rule arg_cong[OF id_apply])
    apply assumption
    (* copied from above *)
   apply (unfold VVr12_def comp_def)
   apply (rule eta_inj12)
   apply (drule T1.TT_injects0[THEN iffD1])
   apply (erule exE conjE)+
   apply (drule trans[rotated])
    apply (rule sym)
    apply (rule trans)
     apply (rule fun_cong[OF eta_natural12, unfolded comp_def])
          apply (assumption | rule supp_id_bound bij_id)+
    apply (rule arg_cong[OF id_apply])
   apply assumption
    (* copied from above *)
  apply (unfold VVr21_def comp_def)
  apply (rule eta_inj21)
  apply (drule T1.TT_injects0[THEN iffD1])
  apply (erule exE conjE)+
  apply (drule trans[rotated])
   apply (rule sym)
   apply (rule trans)
    apply (rule fun_cong[OF eta_natural21, unfolded comp_def])
         apply (assumption | rule supp_id_bound bij_id)+
   apply (rule arg_cong[OF id_apply])
  apply assumption
  done

lemma rrename_VVrs:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows
    "rrename_T1 f1 f2 (VVr11 a) = VVr11 (f1 a)"
    "rrename_T1 f1 f2 (VVr12 b) = VVr12 (f2 b)"
    "rrename_T2 f1 f2 (VVr21 a) = VVr21 (f1 a)"
    apply -
    (* EVERY' (map ... VVr_defs eta_naturals) *)
    apply (unfold VVr11_def comp_def)
    apply (rule trans)
     apply (rule T1.rrename_cctors[OF assms])
    apply (rule arg_cong[of _ _ T1_ctor])
    apply (rule fun_cong[OF eta_natural11, unfolded comp_def])
         apply (rule assms)+
    (* copied from above *)
   apply (unfold VVr12_def comp_def)
   apply (rule trans)
    apply (rule T1.rrename_cctors[OF assms])
   apply (rule arg_cong[of _ _ T1_ctor])
   apply (rule fun_cong[OF eta_natural12, unfolded comp_def])
        apply (rule assms)+
    (* copied from above *)
  apply (unfold VVr21_def comp_def)
  apply (rule trans)
   apply (rule T1.rrename_cctors[OF assms])
  apply (rule arg_cong[of _ _ T2_ctor])
  apply (rule fun_cong[OF eta_natural21, unfolded comp_def])
       apply (rule assms)+
  done

lemma SSupp_comp_subsets:
  "SSupp11 (g \<circ> f) \<subseteq> SSupp11 g \<union> supp f"
  "SSupp12 (g2 \<circ> f2) \<subseteq> SSupp12 g2 \<union> supp f2"
  "SSupp21 (g3 \<circ> f3) \<subseteq> SSupp21 g3 \<union> supp f3"
  (* REPEAT_DETERM *)
  apply (rule subsetI)
  apply (unfold SSupp11_def mem_Collect_eq Un_iff comp_def)[1]
  apply (rule case_split)
   apply (erule disjI2)
  apply (rule disjI1)
  apply (drule iffD1[OF arg_cong2[OF _ refl, of _ _ "(\<noteq>)"], rotated])
   apply (rule arg_cong[of _ _ g])
   apply (erule notin_supp)
    apply assumption
  (* copied from above *)
  apply (rule subsetI)
  apply (unfold SSupp12_def mem_Collect_eq Un_iff comp_def)[1]
  apply (rule case_split)
   apply (erule disjI2)
  apply (rule disjI1)
  apply (drule iffD1[OF arg_cong2[OF _ refl, of _ _ "(\<noteq>)"], rotated])
   apply (rule arg_cong[of _ _ g2])
   apply (erule notin_supp)
  apply assumption
  (* copied from above *)
  apply (rule subsetI)
  apply (unfold SSupp21_def mem_Collect_eq Un_iff comp_def)[1]
  apply (rule case_split)
   apply (erule disjI2)
  apply (rule disjI1)
  apply (drule iffD1[OF arg_cong2[OF _ refl, of _ _ "(\<noteq>)"], rotated])
   apply (rule arg_cong[of _ _ g3])
   apply (erule notin_supp)
  apply assumption
  done

lemma SSupp_comp_bounds:
  "|SSupp11 g| <o cmin |UNIV::'var::{var_T1_pre,var_T2_pre} set| |UNIV::'tyvar::{var_T1_pre,var_T2_pre} set| \<Longrightarrow> |supp (f::'var \<Rightarrow> 'var)| <o  cmin |UNIV::'var set| |UNIV::'tyvar set| \<Longrightarrow> |SSupp11 (g \<circ> f)| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
  "|SSupp12 g2| <o cmin |UNIV::'var set| |UNIV::'tyvar set| \<Longrightarrow> |supp (f2::'tyvar \<Rightarrow> 'tyvar)| <o  cmin |UNIV::'var set| |UNIV::'tyvar set| \<Longrightarrow> |SSupp12 (g2 \<circ> f2)| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
  "|SSupp21 g3| <o cmin |UNIV::'var set| |UNIV::'tyvar set| \<Longrightarrow> |supp f| <o  cmin |UNIV::'var set| |UNIV::'tyvar set| \<Longrightarrow> |SSupp21 (g3 \<circ> f)| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
  (* REPEAT_DETERM *)
    apply (rule card_of_subset_bound)
     apply (rule SSupp_comp_subsets)
    apply (rule Un_bound)
     apply assumption+
    (* copied from above *)
   apply (rule card_of_subset_bound)
    apply (rule SSupp_comp_subsets)
   apply (rule Un_bound)
    apply assumption+
    (* copied from above *)
  apply (rule card_of_subset_bound)
   apply (rule SSupp_comp_subsets)
  apply (rule Un_bound)
   apply assumption+
  done

lemma SSupp_rename_subsets:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows
    "SSupp11 (rrename_T1 f1 f2 \<circ> g) \<subseteq> SSupp11 g \<union> supp f1"
    "SSupp12 (rrename_T1 f1 f2 \<circ> h) \<subseteq> SSupp12 h \<union> supp f2"
    "SSupp21 (rrename_T2 f1 f2 \<circ> g2) \<subseteq> SSupp21 g2 \<union> supp f1"
    apply (rule subsetI)
    apply (unfold SSupp11_def mem_Collect_eq Un_iff comp_def)[1]
    apply (rule case_split[rotated])
     apply (erule disjI1)
    apply (drule iffD1[OF arg_cong2[OF _ refl, of _ _ "(\<noteq>)"], rotated])
     apply (rule arg_cong[of _ _ "rrename_T1 f1 f2"])
     apply assumption
    apply (unfold rrename_VVrs[OF assms])
    apply (rule disjI2)
    apply (erule contrapos_np)
    apply (rule arg_cong[of _ _ VVr11])
    apply (erule notin_supp)
    (* copied from above *)
   apply (rule subsetI)
   apply (unfold SSupp12_def mem_Collect_eq Un_iff comp_def)[1]
   apply (rule case_split[rotated])
    apply (erule disjI1)
   apply (drule iffD1[OF arg_cong2[OF _ refl, of _ _ "(\<noteq>)"], rotated])
    apply (rule arg_cong[of _ _ "rrename_T1 f1 f2"])
    apply assumption
   apply (unfold rrename_VVrs[OF assms])
   apply (rule disjI2)
   apply (erule contrapos_np)
   apply (rule arg_cong[of _ _ VVr12])
   apply (erule notin_supp)
    (* copied from above *)
  apply (rule subsetI)
  apply (unfold SSupp21_def mem_Collect_eq Un_iff comp_def)[1]
  apply (rule case_split[rotated])
   apply (erule disjI1)
  apply (drule iffD1[OF arg_cong2[OF _ refl, of _ _ "(\<noteq>)"], rotated])
   apply (rule arg_cong[of _ _ "rrename_T2 f1 f2"])
   apply assumption
  apply (unfold rrename_VVrs[OF assms])
  apply (rule disjI2)
  apply (erule contrapos_np)
  apply (rule arg_cong[of _ _ VVr21])
  apply (erule notin_supp)
  done

lemma SSupp_rename_bounds:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'var set| |UNIV::'tyvar set|" "bij f2" "|supp f2| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
  shows "|SSupp11 g| <o cmin |UNIV::'var set| |UNIV::'tyvar set| \<Longrightarrow> |SSupp11 (rrename_T1 f1 f2 \<circ> g)| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
    "|SSupp12 h| <o cmin |UNIV::'var set| |UNIV::'tyvar set| \<Longrightarrow> |SSupp12 (rrename_T1 f1 f2 \<circ> h)| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
    "|SSupp21 g2| <o cmin |UNIV::'var set| |UNIV::'tyvar set| \<Longrightarrow> |SSupp21 (rrename_T2 f1 f2 \<circ> g2)| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
    apply -
  subgoal
    apply (rule card_of_subset_bound)
     apply (rule SSupp_rename_subsets)
        apply (assumption | rule assms Un_bound ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
    done
  subgoal
    apply (rule card_of_subset_bound)
     apply (rule SSupp_rename_subsets)
        apply (assumption | rule assms Un_bound ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
    done
  subgoal
    apply (rule card_of_subset_bound)
     apply (rule SSupp_rename_subsets)
        apply (assumption | rule assms Un_bound ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
    done
  done

lemma compSS_comp0s:
  fixes f1 g1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2 g2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes g_prems: "bij g1" "|supp g1| <o cmin |UNIV::'var set| |UNIV::'tyvar set|" "bij g2" "|supp g2| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
    and f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'var set| |UNIV::'tyvar set|" "bij f2" "|supp f2| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
  shows
    "compSS11 f1 f2 \<circ> compSS11 g1 g2 = compSS11 (f1 \<circ> g1) (f2 \<circ> g2)"
    "compSS12 f1 f2 \<circ> compSS12 g1 g2 = compSS12 (f1 \<circ> g1) (f2 \<circ> g2)"
    "compSS21 f1 f2 \<circ> compSS21 g1 g2 = compSS21 (f1 \<circ> g1) (f2 \<circ> g2)"
    apply -
  subgoal
    apply (unfold compSS11_def)
    apply (subst o_inv_distrib T1.rrename_comp0s[symmetric], (rule supp_id_bound bij_id assms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
    apply (unfold id_o o_id)?
    apply (rule ext)
    apply (rule trans[OF comp_apply])
    apply (unfold comp_assoc)
    apply (rule refl)
    done
      (* copied from above *)
  subgoal
    apply (unfold compSS12_def)
    apply (subst o_inv_distrib T1.rrename_comp0s[symmetric], (rule supp_id_bound bij_id assms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
    apply (unfold id_o o_id)?
    apply (rule ext)
    apply (rule trans[OF comp_apply])
    apply (unfold comp_assoc)
    apply (rule refl)
    done
      (* copied from above *)
  subgoal
    apply (unfold compSS21_def)
    apply (subst o_inv_distrib T1.rrename_comp0s[symmetric], (rule supp_id_bound bij_id assms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
    apply (unfold id_o o_id)?
    apply (rule ext)
    apply (rule trans[OF comp_apply])
    apply (unfold comp_assoc)
    apply (rule refl)
    done
  done

lemma compSS_id0s:
  "compSS11 id id = id"
  "compSS12 id id = id"
  "compSS21 id id = id"
  apply (unfold compSS11_def compSS12_def compSS21_def T1.rrename_id0s id_o o_id inv_id)
  apply (unfold id_def)
  apply (rule refl)+
  done

lemma Pmap_id0: "Pmap id id = id"
  apply (rule ext)
  apply (unfold Pmap_def case_prod_beta compSS_id0s)
  apply (unfold id_def prod.collapse)
  apply (rule refl)
  done

lemma Pmap_comp0:
  fixes f1 g1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2 g2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes g_prems: "bij g1" "|supp g1| <o cmin |UNIV::'var set| |UNIV::'tyvar set|" "bij g2" "|supp g2| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
  and f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'var set| |UNIV::'tyvar set|" "bij f2" "|supp f2| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
shows
  "Pmap f1 f2 \<circ> Pmap g1 g2 = Pmap (f1 \<circ> g1) (f2 \<circ> g2)"
  apply (rule ext)
  apply (unfold Pmap_def case_prod_beta)
  apply (rule trans[OF comp_apply])
  apply (unfold prod.inject fst_conv snd_conv)
  apply (rule conjI)
   apply (rule conjI assms
      trans[OF comp_apply[symmetric] fun_cong[OF compSS_comp0s(1)]]
      trans[OF comp_apply[symmetric] fun_cong[OF compSS_comp0s(2)]]
      trans[OF comp_apply[symmetric] fun_cong[OF compSS_comp0s(3)]]
   )+
  done

lemma SSupp_natural:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows
    "SSupp11 (rrename_T1 f1 f2 \<circ> y \<circ> inv f1) = f1 ` SSupp11 y"
    "SSupp12 (rrename_T1 f1 f2 \<circ> y2 \<circ> inv f2) = f2 ` SSupp12 y2"
    "SSupp21 (rrename_T2 f1 f2 \<circ> y3 \<circ> inv f1) = f1 ` SSupp21 y3"
  subgoal
    apply (unfold SSupp11_def)
    apply (rule iffD2[OF set_eq_iff])
    apply (rule allI)
    apply (rule iffI)
     apply (unfold mem_Collect_eq comp_def VVr11_def image_Collect)
     apply (erule contrapos_np)
     apply (drule Meson.not_exD)
     apply (erule allE)
     apply (drule iffD1[OF de_Morgan_conj])
     apply (erule disjE)
      apply (subst (asm) inv_simp2[of f1])
       apply (rule assms)
      apply (erule notE)
      apply (rule refl)
     apply (drule notnotD)
     apply (rule trans)
      apply (rule arg_cong[of _ _ "rrename_T1 f1 f2"])
      apply assumption
     apply (rule trans)
      apply (rule T1.rrename_cctors)
         apply (rule assms)+
     apply (subst fun_cong[OF eta_natural11, unfolded comp_def])
         apply (rule assms)+
     apply (subst inv_simp2[of f1])
      apply (rule f_prems)
     apply (rule refl)
    apply (erule exE)
    apply (erule conjE)
    apply hypsubst
    apply (subst inv_simp1)
     apply (rule f_prems)
    apply (erule contrapos_nn)
    apply (drule arg_cong[of _ _ "rrename_T1 (inv f1) (inv f2)"])
    apply (subst (asm) T1.rrename_comps)
            apply (rule assms supp_inv_bound bij_imp_bij_inv)+
    apply (subst (asm) inv_o_simp1, rule assms)+
    apply (unfold T1.rrename_ids)
    apply (erule trans)
    apply (rule trans)
     apply (rule T1.rrename_cctors)
        apply (rule supp_inv_bound bij_imp_bij_inv assms)+
    apply (subst fun_cong[OF eta_natural11, unfolded comp_def])
        apply (rule supp_inv_bound bij_imp_bij_inv assms)+
    apply (subst inv_simp1)
     apply (rule assms)
    apply (rule refl)
    done
      (* copied from above *)
  subgoal
    apply (unfold SSupp12_def)
    apply (rule iffD2[OF set_eq_iff])
    apply (rule allI)
    apply (rule iffI)
     apply (unfold mem_Collect_eq comp_def VVr12_def image_Collect)
     apply (erule contrapos_np)
     apply (drule Meson.not_exD)
     apply (erule allE)
     apply (drule iffD1[OF de_Morgan_conj])
     apply (erule disjE)
      apply (subst (asm) inv_simp2[of f2])
       apply (rule assms)
      apply (erule notE)
      apply (rule refl)
     apply (drule notnotD)
     apply (rule trans)
      apply (rule arg_cong[of _ _ "rrename_T1 f1 f2"])
      apply assumption
     apply (rule trans)
      apply (rule T1.rrename_cctors)
         apply (rule assms)+
     apply (subst fun_cong[OF eta_natural12, unfolded comp_def])
         apply (rule assms)+
     apply (subst inv_simp2[of f2])
      apply (rule f_prems)
     apply (rule refl)
    apply (erule exE)
    apply (erule conjE)
    apply hypsubst
    apply (subst inv_simp1)
     apply (rule f_prems)
    apply (erule contrapos_nn)
    apply (drule arg_cong[of _ _ "rrename_T1 (inv f1) (inv f2)"])
    apply (subst (asm) T1.rrename_comps)
            apply (rule assms supp_inv_bound bij_imp_bij_inv)+
    apply (subst (asm) inv_o_simp1, rule assms)+
    apply (unfold T1.rrename_ids)
    apply (erule trans)
    apply (rule trans)
     apply (rule T1.rrename_cctors)
        apply (rule supp_inv_bound bij_imp_bij_inv assms)+
    apply (subst fun_cong[OF eta_natural12, unfolded comp_def])
        apply (rule supp_inv_bound bij_imp_bij_inv assms)+
    apply (subst inv_simp1)
     apply (rule assms)
    apply (rule refl)
    done
      (* copied from above *)
  subgoal
    apply (unfold SSupp21_def)
    apply (rule iffD2[OF set_eq_iff])
    apply (rule allI)
    apply (rule iffI)
     apply (unfold mem_Collect_eq comp_def VVr21_def image_Collect)
     apply (erule contrapos_np)
     apply (drule Meson.not_exD)
     apply (erule allE)
     apply (drule iffD1[OF de_Morgan_conj])
     apply (erule disjE)
      apply (subst (asm) inv_simp2[of f1])
       apply (rule assms)
      apply (erule notE)
      apply (rule refl)
     apply (drule notnotD)
     apply (rule trans)
      apply (rule arg_cong[of _ _ "rrename_T2 f1 f2"])
      apply assumption
     apply (rule trans)
      apply (rule T1.rrename_cctors)
         apply (rule assms)+
     apply (subst fun_cong[OF eta_natural21, unfolded comp_def])
         apply (rule assms)+
     apply (subst inv_simp2[of f1])
      apply (rule f_prems)
     apply (rule refl)
    apply (erule exE)
    apply (erule conjE)
    apply hypsubst
    apply (subst inv_simp1)
     apply (rule f_prems)
    apply (erule contrapos_nn)
    apply (drule arg_cong[of _ _ "rrename_T2 (inv f1) (inv f2)"])
    apply (subst (asm) T1.rrename_comps)
            apply (rule assms supp_inv_bound bij_imp_bij_inv)+
    apply (subst (asm) inv_o_simp1, rule assms)+
    apply (unfold T1.rrename_ids)
    apply (erule trans)
    apply (rule trans)
     apply (rule T1.rrename_cctors)
        apply (rule supp_inv_bound bij_imp_bij_inv assms)+
    apply (subst fun_cong[OF eta_natural21, unfolded comp_def])
        apply (rule supp_inv_bound bij_imp_bij_inv assms)+
    apply (subst inv_simp1)
     apply (rule assms)
    apply (rule refl)
    done
  done

lemma PFVars_Pmaps:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'var set| |UNIV::'tyvar set|" "bij f2" "|supp f2| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
  shows "PFVars_1 (Pmap f1 f2 p) = f1 ` PFVars_1 p"
    "PFVars_2 (Pmap f1 f2 p) = f2 ` PFVars_2 p"
  subgoal
    apply (unfold Pmap_def PFVars_1_def case_prod_beta fst_conv snd_conv)
    apply (unfold compSS_defs image_Un)
    apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
      (* REPEAT_DETERM *)
      apply (unfold IImsupp11_1_def)
      apply (unfold image_comp[symmetric])
      apply (subst image_comp[unfolded comp_def])
      apply (subst T1.FFVars_rrenames)
          apply (rule assms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
      apply (unfold image_UN[symmetric])
      apply (subst SSupp_natural, (rule assms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
      apply (unfold image_comp)
      apply (subst inv_o_simp1)
       apply (rule assms)
      apply (unfold o_id image_Un)
      apply (rule refl)
      (* copied from above *)
     apply (unfold IImsupp12_1_def)
     apply (unfold image_comp[symmetric])
     apply (subst image_comp[unfolded comp_def])
     apply (subst T1.FFVars_rrenames)
         apply (rule assms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
     apply (unfold image_UN[symmetric])
     apply (subst SSupp_natural, (rule assms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
     apply (unfold image_comp)
     apply (subst inv_o_simp1)
      apply (rule assms)
     apply (unfold o_id image_Un)
     apply (rule refl)
      (* copied from above *)
    apply (unfold IImsupp21_1_def)
    apply (unfold image_comp[symmetric])
    apply (subst image_comp[unfolded comp_def])
    apply (subst T1.FFVars_rrenames)
        apply (rule assms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
    apply (unfold image_UN[symmetric])
    apply (subst SSupp_natural, (rule assms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
    apply (unfold image_comp)
    apply (subst inv_o_simp1)
     apply (rule assms)
    apply (unfold o_id image_Un)
    apply (rule refl)
      (* END REPEAT_DETERM *)
    done
  subgoal
    apply (unfold Pmap_def PFVars_2_def case_prod_beta fst_conv snd_conv)
    apply (unfold compSS_defs image_Un)
    apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
      (* REPEAT_DETERM *)
      apply (unfold IImsupp11_2_def)
      apply (unfold image_comp[symmetric])
      apply (subst image_comp[unfolded comp_def])
      apply (subst T1.FFVars_rrenames)
          apply (rule assms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
      apply (unfold image_UN[symmetric])
      apply (subst SSupp_natural, (rule assms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
      apply (unfold image_comp)
      apply (subst inv_o_simp1)
       apply (rule assms)
      apply (unfold o_id image_Un)
      apply (rule refl)
      (* copied from above *)
     apply (unfold IImsupp12_2_def)
     apply (unfold image_comp[symmetric])
     apply (subst image_comp[unfolded comp_def])
     apply (subst T1.FFVars_rrenames)
         apply (rule assms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
     apply (unfold image_UN[symmetric])
     apply (subst SSupp_natural, (rule assms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
     apply (unfold image_comp)
     apply (subst inv_o_simp1)
      apply (rule assms)
     apply (unfold o_id image_Un)
     apply (rule refl)
      (* copied from above *)
    apply (unfold IImsupp21_2_def)
    apply (unfold image_comp[symmetric])
    apply (subst image_comp[unfolded comp_def])
    apply (subst T1.FFVars_rrenames)
        apply (rule assms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
    apply (unfold image_UN[symmetric])
    apply (subst SSupp_natural, (rule assms ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
    apply (unfold image_comp)
    apply (subst inv_o_simp1)
     apply (rule assms)
    apply (unfold o_id image_Un)
    apply (rule refl)
      (* END REPEAT_DETERM *)
    done
  done

lemma IImsupp_VVrs:
  "f a \<noteq> a \<Longrightarrow> imsupp f \<inter> IImsupp11_1 y = {} \<Longrightarrow> y a = VVr11 a"
  "f2 b \<noteq> b \<Longrightarrow> imsupp f2 \<inter> IImsupp12_2 y2 = {} \<Longrightarrow> y2 b = VVr12 b"
  "f a \<noteq> a \<Longrightarrow> imsupp f \<inter> IImsupp21_1 y3 = {} \<Longrightarrow> y3 a = VVr21 a"
  subgoal
    apply (unfold imsupp_def supp_def IImsupp11_1_def SSupp11_def)
    apply (drule iffD1[OF disjoint_iff])
    apply (erule allE)
    apply (erule impE)
     apply (rule UnI1)
     apply (erule iffD2[OF mem_Collect_eq])
    apply (unfold Un_iff de_Morgan_disj mem_Collect_eq not_not)
    apply (erule conjE)
    apply assumption
    done
  subgoal
    apply (unfold imsupp_def supp_def IImsupp12_2_def SSupp12_def)
    apply (drule iffD1[OF disjoint_iff])
    apply (erule allE)
    apply (erule impE)
     apply (rule UnI1)
     apply (erule iffD2[OF mem_Collect_eq])
    apply (unfold Un_iff de_Morgan_disj mem_Collect_eq not_not)
    apply (erule conjE)
    apply assumption
    done
  subgoal
    apply (unfold imsupp_def supp_def IImsupp21_1_def SSupp21_def)
    apply (drule iffD1[OF disjoint_iff])
    apply (erule allE)
    apply (erule impE)
     apply (rule UnI1)
     apply (erule iffD2[OF mem_Collect_eq])
    apply (unfold Un_iff de_Morgan_disj mem_Collect_eq not_not)
    apply (erule conjE)
    apply assumption
    done
  done

lemma IImsupp_rrename_commute:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "imsupp f1 \<inter> IImsupp11_1 y = {} \<Longrightarrow> imsupp f2 \<inter> IImsupp11_2 y = {} \<Longrightarrow> rrename_T1 f1 f2 \<circ> y = y \<circ> f1"
    "imsupp f1 \<inter> IImsupp12_1 y2 = {} \<Longrightarrow> imsupp f2 \<inter> IImsupp12_2 y2 = {} \<Longrightarrow> rrename_T1 f1 f2 \<circ> y2 = y2 \<circ> f2"
    "imsupp f1 \<inter> IImsupp21_1 y3 = {} \<Longrightarrow> imsupp f2 \<inter> IImsupp21_2 y3 = {} \<Longrightarrow> rrename_T2 f1 f2 \<circ> y3 = y3 \<circ> f1"
  subgoal
    apply (rule ext)
    apply (unfold comp_def)
    subgoal for a
      apply (rule case_split[of "f1 a = a"])
       apply (rule case_split[of "y a = VVr11 a"])
        apply (rule trans)
         apply (rule arg_cong[of _ _ "rrename_T1 f1 f2"])
         apply assumption
        apply (rule trans)
         apply (rule rrename_VVrs)
            apply (rule f_prems)+
        apply (rule trans)
         apply (rule arg_cong[of _ _ VVr11])
         apply assumption
        apply (rule sym)
        apply (rule trans)
         apply (rule arg_cong[of _ _ y])
         apply assumption
        apply assumption

       apply (rule trans)
        apply (rule T1.rrename_cong_ids)
             apply (rule f_prems)+
        (* REPET_DETERM *)
         apply (rule id_onD[rotated])
          apply assumption
         apply (rule imsupp_id_on)
         apply (rule Int_subset_empty2)
          apply assumption
         apply (unfold IImsupp11_1_def SSupp11_def)[1]
         apply (rule subsetI)
         apply (rule UnI2)?
         apply (rule UN_I[rotated])
          apply (unfold comp_def)
          apply assumption
         apply (rule iffD2[OF mem_Collect_eq])
         apply assumption
        (* copied from above *)
        apply (rule id_onD[rotated])
         apply assumption
        apply (rule imsupp_id_on)
        apply (rule Int_subset_empty2)
         apply assumption
        apply (unfold IImsupp11_2_def SSupp11_def)[1]
        apply (rule subsetI)
        apply (rule UN_I[rotated])
         apply (unfold comp_def)
         apply assumption
        apply (rule iffD2[OF mem_Collect_eq])
        apply assumption
        (* END REPEAT_DETERM *)
       apply (rule arg_cong[of _ _ y])
       apply (rule sym)
       apply assumption

      apply (rule trans)
       apply (rule arg_cong[of _ _ "rrename_T1 f1 f2"])
       defer
       apply (rule trans)
        prefer 3
        apply (erule IImsupp_VVrs)
        apply assumption
       apply (rule rrename_VVrs)
          apply (rule f_prems)+
      apply (rule sym)
      apply (rule IImsupp_VVrs)
       apply (erule bij_not_eq_twice[rotated])
       apply (rule f_prems)
      apply assumption
      done
    done
      (* copied from above *)
  subgoal
    apply (rule ext)
    apply (unfold comp_def)
    subgoal for a
      apply (rule case_split[of "f2 a = a"])
       apply (rule case_split[of "y2 a = VVr12 a"])
        apply (rule trans)
         apply (rule arg_cong[of _ _ "rrename_T1 f1 f2"])
         apply assumption
        apply (rule trans)
         apply (rule rrename_VVrs)
            apply (rule f_prems)+
        apply (rule trans)
         apply (rule arg_cong[of _ _ VVr12])
         apply assumption
        apply (rule sym)
        apply (rule trans)
         apply (rule arg_cong[of _ _ y2])
         apply assumption
        apply assumption

       apply (rule trans)
        apply (rule T1.rrename_cong_ids)
             apply (rule f_prems)+
        (* REPET_DETERM *)
         apply (rule id_onD[rotated])
          apply assumption
         apply (rule imsupp_id_on)
         apply (rule Int_subset_empty2)
          apply assumption
         apply (unfold IImsupp12_1_def SSupp12_def)[1]
         apply (rule subsetI)
         apply (rule UnI2)?
         apply (rule UN_I[rotated])
          apply (unfold comp_def)
          apply assumption
         apply (rule iffD2[OF mem_Collect_eq])
         apply assumption
        (* copied from above *)
        apply (rule id_onD[rotated])
         apply assumption
        apply (rule imsupp_id_on)
        apply (rule Int_subset_empty2)
         apply assumption
        apply (unfold IImsupp12_2_def SSupp12_def)[1]
        apply (rule subsetI)
        apply (rule UnI2)?
        apply (rule UN_I[rotated])
         apply (unfold comp_def)
         apply assumption
        apply (rule iffD2[OF mem_Collect_eq])
        apply assumption
        (* END REPEAT_DETERM *)
       apply (rule arg_cong[of _ _ y2])
       apply (rule sym)
       apply assumption

      apply (rule trans)
       apply (rule arg_cong[of _ _ "rrename_T1 f1 f2"])
       defer
       apply (rule trans)
        prefer 3
        apply (erule IImsupp_VVrs)
        apply assumption
       apply (rule rrename_VVrs)
          apply (rule f_prems)+
      apply (rule sym)
      apply (rule IImsupp_VVrs)
       apply (erule bij_not_eq_twice[rotated])
       apply (rule f_prems)
      apply assumption
      done
    done
      (* copied from above *)
  subgoal
    apply (rule ext)
    apply (unfold comp_def)
    subgoal for a
      apply (rule case_split[of "f1 a = a"])
       apply (rule case_split[of "y3 a = VVr21 a"])
        apply (rule trans)
         apply (rule arg_cong[of _ _ "rrename_T2 f1 f2"])
         apply assumption
        apply (rule trans)
         apply (rule rrename_VVrs)
            apply (rule f_prems)+
        apply (rule trans)
         apply (rule arg_cong[of _ _ VVr21])
         apply assumption
        apply (rule sym)
        apply (rule trans)
         apply (rule arg_cong[of _ _ y3])
         apply assumption
        apply assumption

       apply (rule trans)
        apply (rule T1.rrename_cong_ids)
             apply (rule f_prems)+
        (* REPET_DETERM *)
         apply (rule id_onD[rotated])
          apply assumption
         apply (rule imsupp_id_on)
         apply (rule Int_subset_empty2)
          apply assumption
         apply (unfold IImsupp21_1_def SSupp21_def)[1]
         apply (rule subsetI)
         apply (rule UnI2)?
         apply (rule UN_I[rotated])
          apply (unfold comp_def)
          apply assumption
         apply (rule iffD2[OF mem_Collect_eq])
         apply assumption
        (* copied from above *)
        apply (rule id_onD[rotated])
         apply assumption
        apply (rule imsupp_id_on)
        apply (rule Int_subset_empty2)
         apply assumption
        apply (unfold IImsupp21_2_def SSupp21_def)[1]
        apply (rule subsetI)
        apply (rule UnI2)?
        apply (rule UN_I[rotated])
         apply (unfold comp_def)
         apply assumption
        apply (rule iffD2[OF mem_Collect_eq])
        apply assumption
        (* END REPEAT_DETERM *)
       apply (rule arg_cong[of _ _ y3])
       apply (rule sym)
       apply assumption

      apply (rule trans)
       apply (rule arg_cong[of _ _ "rrename_T2 f1 f2"])
       defer
       apply (rule trans)
        prefer 3
        apply (erule IImsupp_VVrs)
        apply assumption
       apply (rule rrename_VVrs)
          apply (rule f_prems)+
      apply (rule sym)
      apply (rule IImsupp_VVrs)
       apply (erule bij_not_eq_twice[rotated])
       apply (rule f_prems)
      apply assumption
      done
    done
  done


lemma compSS_cong_ids:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "(\<And>a. a \<in> IImsupp11_1 h1 \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> IImsupp11_2 h1 \<Longrightarrow> f2 a = a) \<Longrightarrow>
    compSS11 f1 f2 h1 = h1"
    "(\<And>a. a \<in> IImsupp12_1 h2 \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> IImsupp12_2 h2 \<Longrightarrow> f2 a = a) \<Longrightarrow>
    compSS12 f1 f2 h2 = h2"
    "(\<And>a. a \<in> IImsupp21_1 h3 \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> IImsupp21_2 h3 \<Longrightarrow> f2 a = a) \<Longrightarrow>
    compSS21 f1 f2 h3 = h3"
  subgoal
    apply (unfold compSS11_def)
    subgoal premises prems
      apply (subst IImsupp_rrename_commute)
            apply (rule f_prems)+
        (* REPEAT_DETERM *)
        apply (rule trans[OF Int_commute])
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply (drule prems)
        apply (erule contrapos_pn)
        apply (unfold imsupp_def supp_def)[1]
        apply (erule UnE)
         apply (unfold mem_Collect_eq)
         apply assumption
        apply (erule imageE)
        apply hypsubst
        apply (unfold mem_Collect_eq)
        apply (erule bij_not_eq_twice[rotated])
        apply (rule f_prems)
        (* copied from above *)
       apply (rule trans[OF Int_commute])
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply (drule prems)
       apply (erule contrapos_pn)
       apply (unfold imsupp_def supp_def)[1]
       apply (erule UnE)
        apply (unfold mem_Collect_eq)
        apply assumption
       apply (erule imageE)
       apply hypsubst
       apply (unfold mem_Collect_eq)
       apply (erule bij_not_eq_twice[rotated])
       apply (rule f_prems)
        (* END REPEAT *)
      apply (unfold comp_assoc)
      apply (subst inv_o_simp2)
       apply (rule f_prems)
      apply (unfold o_id)
      apply (rule refl)
      done
    done
      (* copied from above *)
  subgoal
    apply (unfold compSS12_def)
    subgoal premises prems
      apply (subst IImsupp_rrename_commute)
            apply (rule f_prems)+
        (* REPEAT_DETERM *)
        apply (rule trans[OF Int_commute])
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply (drule prems)
        apply (erule contrapos_pn)
        apply (unfold imsupp_def supp_def)[1]
        apply (erule UnE)
         apply (unfold mem_Collect_eq)
         apply assumption
        apply (erule imageE)
        apply hypsubst
        apply (unfold mem_Collect_eq)
        apply (erule bij_not_eq_twice[rotated])
        apply (rule f_prems)
        (* copied from above *)

       apply (rule trans[OF Int_commute])
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply (drule prems)
       apply (erule contrapos_pn)
       apply (unfold imsupp_def supp_def)[1]
       apply (erule UnE)
        apply (unfold mem_Collect_eq)
        apply assumption
       apply (erule imageE)
       apply hypsubst
       apply (unfold mem_Collect_eq)
       apply (erule bij_not_eq_twice[rotated])
       apply (rule f_prems)
        (* END REPEAT *)
      apply (unfold comp_assoc)
      apply (subst inv_o_simp2)
       apply (rule f_prems)
      apply (unfold o_id)
      apply (rule refl)
      done
    done
      (* copied from above *)
  subgoal
    apply (unfold compSS21_def)
    subgoal premises prems
      apply (subst IImsupp_rrename_commute)
            apply (rule f_prems)+
        (* REPEAT_DETERM *)
        apply (rule trans[OF Int_commute])
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply (drule prems)
        apply (erule contrapos_pn)
        apply (unfold imsupp_def supp_def)[1]
        apply (erule UnE)
         apply (unfold mem_Collect_eq)
         apply assumption
        apply (erule imageE)
        apply hypsubst
        apply (unfold mem_Collect_eq)
        apply (erule bij_not_eq_twice[rotated])
        apply (rule f_prems)
        (* copied from above *)

       apply (rule trans[OF Int_commute])
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply (drule prems)
       apply (erule contrapos_pn)
       apply (unfold imsupp_def supp_def)[1]
       apply (erule UnE)
        apply (unfold mem_Collect_eq)
        apply assumption
       apply (erule imageE)
       apply hypsubst
       apply (unfold mem_Collect_eq)
       apply (erule bij_not_eq_twice[rotated])
       apply (rule f_prems)
        (* END REPEAT *)
      apply (unfold comp_assoc)
      apply (subst inv_o_simp2)
       apply (rule f_prems)
      apply (unfold o_id)
      apply (rule refl)
      done
    done
  done

lemma Pmap_cong_id:
  fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'var set| |UNIV::'tyvar set|" "bij f2" "|supp f2| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
  shows "(\<And>a. a \<in> PFVars_1 p \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> PFVars_2 p \<Longrightarrow> f2 a = a) \<Longrightarrow> Pmap f1 f2 p = p"
  apply (unfold PFVars_1_def PFVars_2_def Pmap_def case_prod_beta)
  subgoal premises prems
    apply (subst compSS_cong_ids, (rule f_prems prems ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order | erule UnI2 UnI1 | rule UnI1)+)+
    apply (unfold prod.collapse)
    apply (rule refl)
    done
  done

lemma small_PFVarss:
  "valid_P p \<Longrightarrow> |PFVars_1 (p::('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) P)| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
  "valid_P p \<Longrightarrow> |PFVars_2 p| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
  subgoal
    apply (unfold PFVars_1_def case_prod_beta IImsupp11_1_def IImsupp12_1_def IImsupp21_1_def comp_def valid_P_def)
    apply (erule conjE)+
    apply (assumption | rule Un_bound UNION_bound T1.card_of_FFVars_bounds cmin_greater card_of_Card_order)+
    done
  (* copied from above *)
  subgoal
    apply (unfold PFVars_2_def case_prod_beta IImsupp11_2_def IImsupp12_2_def IImsupp21_2_def comp_def valid_P_def)
    apply (erule conjE)+
    apply (assumption | rule Un_bound UNION_bound T1.card_of_FFVars_bounds cmin_greater card_of_Card_order)+
    done
  done

lemma small_avoiding_sets:
  "|avoiding_set1| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
  "|avoiding_set2| <o cmin |UNIV::'var set| |UNIV::'tyvar set|"
   apply (unfold avoiding_set1_def avoiding_set2_def)
   apply (rule cmin_greater card_of_Card_order emp_bound)+
  done

lemmas Un_mono1 = Un_mono[OF _ empty_subsetI, unfolded Un_empty_right]
lemmas Un_mono2 = Un_mono[OF empty_subsetI, unfolded Un_empty_left]

lemma asVVr_VVrs:
  "asVVr11 (VVr11 a) = a"
  "asVVr12 (VVr12 b) = b"
  "asVVr21 (VVr21 c) = c"
  subgoal
    apply (unfold asVVr11_def isVVr11_def)
    apply (subst if_P)
     apply (rule exI)
     apply (rule refl)
    apply (rule some_equality)
     apply (rule refl)
    apply (rule sym)
    apply (erule VVr_injs)
    done
    (* copied from above *)
  subgoal
    apply (unfold asVVr12_def isVVr12_def)
    apply (subst if_P)
     apply (rule exI)
     apply (rule refl)
    apply (rule some_equality)
     apply (rule refl)
    apply (rule sym)
    apply (erule VVr_injs)
    done
    (* copied from above *)
  subgoal
    apply (unfold asVVr21_def isVVr21_def)
    apply (subst if_P)
     apply (rule exI)
     apply (rule refl)
    apply (rule some_equality)
     apply (rule refl)
    apply (rule sym)
    apply (erule VVr_injs)
    done
  done

lemma U1FVars_subset_1: "valid_P p \<Longrightarrow> set5_T1_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T1_pre) \<inter> (PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  (\<And>t pu p. valid_P p \<Longrightarrow> (t, pu) \<in> set7_T1_pre y \<union> set8_T1_pre y \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FFVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. valid_P p \<Longrightarrow> (t, pu) \<in> set9_T1_pre y \<union> set10_T1_pre y \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FFVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  U1FVars_1 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) (U1ctor y p) \<subseteq> FFVars_T11 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> PFVars_1 p \<union> avoiding_set1"
  apply (unfold avoiding_set1_def Un_empty_right case_prod_beta)
  subgoal premises prems
    apply (unfold U1ctor_def case_prod_beta)
    apply (rule case_split)
     apply (subst if_P)
      apply assumption
     apply (unfold isVVr11_def)[1]
     apply (erule exE)
     apply (drule sym)
     apply (erule subst)
     apply (unfold asVVr_VVrs)
     apply (rule case_split[of "_ = _"])
      apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]])
       apply (rule arg_cong[of _ _ FFVars_T11])
       prefer 2
       apply (rule Un_upper1)
      apply assumption
     apply (rule subsetI)
     apply (rule UnI2)
     apply (unfold PFVars_1_def case_prod_beta IImsupp11_1_def SSupp11_def)[1]
     apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 1] 1\<close>)
     apply (rule UnI2)?
     apply (rule UN_I)
      apply (rule iffD2[OF mem_Collect_eq])
      apply assumption
     apply (rule iffD2[OF arg_cong2[OF refl comp_apply, of "(\<in>)"]])
     apply assumption
  apply (unfold if_not_P)
  apply (rule case_split)
   apply (subst if_P)
      apply assumption
     apply (unfold isVVr12_def)[1]
     apply (erule exE)
     apply (drule sym)
     apply (erule subst)
     apply (unfold asVVr_VVrs)
     apply (rule case_split[of "_ = _"])
      apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]])
       apply (rule arg_cong[of _ _ FFVars_T11])
       prefer 2
       apply (rule Un_upper1)
      apply assumption
     apply (rule subsetI)
     apply (rule UnI2)
     apply (unfold PFVars_1_def case_prod_beta IImsupp12_1_def SSupp12_def)[1]
     apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
     apply (rule UnI2)?
     apply (rule UN_I)
      apply (rule iffD2[OF mem_Collect_eq])
      apply assumption
     apply (rule iffD2[OF arg_cong2[OF refl comp_apply, of "(\<in>)"]])
     apply assumption
  apply (unfold if_not_P)
  apply (unfold T1.FFVars_cctors)
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id image_comp comp_def)
  apply (rule Un_mono')+
      apply (rule Un_upper1)
     apply (unfold UN_extend_simps(2))
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
     apply (unfold prod.collapse)
    apply (rule prems)
     apply (erule UnI1 UnI2)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (rule Diff_Un_disjunct)
     apply (rule prems)
    apply (rule Diff_mono[OF _ subset_refl])
    apply (unfold UN_extend_simps(2))
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
       apply (unfold prod.collapse)
       apply (rule prems)
    apply (erule UnI1 UnI2)
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
    apply (unfold prod.collapse)
    apply (rule prems)
   apply (erule UnI1 UnI2)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (rule Diff_Un_disjunct)
     apply (rule prems)
    apply (rule Diff_mono[OF _ subset_refl])
    apply (unfold UN_extend_simps(2))
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
    apply (unfold prod.collapse)
    apply (rule prems)
  apply (erule UnI1 UnI2)
  done
  done

lemma U1FVars_subset_2: "valid_P p \<Longrightarrow> set6_T1_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T1_pre) \<inter> (PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  (\<And>t pu p. valid_P p \<Longrightarrow> (t, pu) \<in> set7_T1_pre y \<union> set8_T1_pre y \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FFVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. valid_P p \<Longrightarrow> (t, pu) \<in> set9_T1_pre y \<union> set10_T1_pre y \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  U1FVars_2 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) (U1ctor y p) \<subseteq> FFVars_T12 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) \<union> PFVars_2 p \<union> avoiding_set2"
  apply (unfold avoiding_set2_def Un_empty_right)
  subgoal premises prems
  apply (unfold U1ctor_def case_prod_beta)
  apply (rule case_split)
   apply (subst if_P)
      apply assumption
     apply (unfold isVVr11_def)[1]
     apply (erule exE)
     apply (drule sym)
     apply (erule subst)
     apply (unfold asVVr_VVrs)
     apply (rule case_split[of "_ = _"])
      apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]])
       apply (rule arg_cong[of _ _ FFVars_T12])
       prefer 2
       apply (rule Un_upper1)
      apply assumption
     apply (rule subsetI)
     apply (rule UnI2)
     apply (unfold PFVars_2_def case_prod_beta IImsupp11_2_def SSupp11_def)[1]
     apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 1] 1\<close>)
     apply (rule UnI2)?
     apply (rule UN_I)
      apply (rule iffD2[OF mem_Collect_eq])
      apply assumption
     apply (rule iffD2[OF arg_cong2[OF refl comp_apply, of "(\<in>)"]])
     apply assumption
  apply (unfold if_not_P)
  apply (rule case_split)
   apply (subst if_P)
      apply assumption
     apply (unfold isVVr12_def)[1]
     apply (erule exE)
     apply (drule sym)
     apply (erule subst)
     apply (unfold asVVr_VVrs)
     apply (rule case_split[of "_ = _"])
      apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]])
       apply (rule arg_cong[of _ _ FFVars_T12])
       prefer 2
       apply (rule Un_upper1)
      apply assumption
     apply (rule subsetI)
     apply (rule UnI2)
     apply (unfold PFVars_2_def case_prod_beta IImsupp12_2_def SSupp12_def)[1]
     apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 2] 1\<close>)
     apply (rule UnI2)?
     apply (rule UN_I)
      apply (rule iffD2[OF mem_Collect_eq])
      apply assumption
     apply (rule iffD2[OF arg_cong2[OF refl comp_apply, of "(\<in>)"]])
     apply assumption
  apply (unfold if_not_P)
  apply (unfold T1.FFVars_cctors)
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id image_comp comp_def)
  apply (rule Un_mono')+
      apply (rule Un_upper1)
     apply (unfold UN_extend_simps(2))
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
     apply (unfold prod.collapse)
        apply (rule prems)
     apply (erule UnI1 UnI2)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (rule Diff_Un_disjunct)
     apply (rule prems)
    apply (rule Diff_mono[OF _ subset_refl])
    apply (unfold UN_extend_simps(2))
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
       apply (unfold prod.collapse)
       apply (rule prems)
    apply (erule UnI1 UnI2)
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
    apply (unfold prod.collapse)
    apply (rule prems)
     apply (erule UnI2 UnI1 | rule UnI1)+
    apply (rule subset_If)
     apply (unfold UN_empty')[1]
     apply (rule empty_subsetI)
    apply (rule UN_mono[OF subset_refl])
    apply (rule prems)
     apply (unfold prod.collapse)
     apply (rule prems)
    apply (erule UnI2 UnI1 | rule UnI1)+
  done
  done

lemma U2FVars_subset_1: "valid_P p \<Longrightarrow> set5_T2_pre (y::(_, _, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T2_pre) \<inter> (PFVars_1 p \<union> avoiding_set1) = {} \<Longrightarrow>
  (\<And>t pu p. valid_P p \<Longrightarrow> (t, pu) \<in> set7_T2_pre y \<union> set8_T2_pre y \<Longrightarrow> U1FVars_1 t (pu p) \<subseteq> FFVars_T11 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  (\<And>t pu p. valid_P p \<Longrightarrow> (t, pu) \<in> set9_T2_pre y \<union> set10_T2_pre y \<Longrightarrow> U2FVars_1 t (pu p) \<subseteq> FFVars_T21 t \<union> PFVars_1 p \<union> avoiding_set1) \<Longrightarrow>
  U2FVars_1 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) (U2ctor y p) \<subseteq> FFVars_T21 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) \<union> PFVars_1 p \<union> avoiding_set1"
  apply (unfold avoiding_set1_def Un_empty_right)
  subgoal premises prems
  apply (unfold U2ctor_def case_prod_beta)
  apply (rule case_split)
   apply (subst if_P)
      apply assumption
     apply (unfold isVVr21_def)[1]
     apply (erule exE)
     apply (drule sym)
     apply (erule subst)
     apply (unfold asVVr_VVrs)
     apply (rule case_split[of "_ = _"])
      apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]])
       apply (rule arg_cong[of _ _ FFVars_T21])
       prefer 2
       apply (rule Un_upper1)
      apply assumption
     apply (rule subsetI)
     apply (rule UnI2)
     apply (unfold PFVars_1_def case_prod_beta IImsupp21_1_def SSupp21_def)[1]
     apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 3] 1\<close>)
     apply (rule UnI2)?
     apply (rule UN_I)
      apply (rule iffD2[OF mem_Collect_eq])
      apply assumption
     apply (rule iffD2[OF arg_cong2[OF refl comp_apply, of "(\<in>)"]])
     apply assumption
  apply (unfold if_not_P)
  apply (unfold T1.FFVars_cctors)
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id image_comp comp_def)
  apply (rule Un_mono')+
      apply (rule Un_upper1)
     apply (unfold UN_extend_simps(2))
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
        apply (unfold prod.collapse)
        apply (rule prems)
     apply (erule UnI1 UnI2)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (rule Diff_Un_disjunct)
     apply (rule prems)
    apply (rule Diff_mono[OF _ subset_refl])
    apply (unfold UN_extend_simps(2))
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
       apply (unfold prod.collapse)
       apply (rule prems)
    apply (erule UnI1 UnI2)
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
    apply (unfold prod.collapse)
      apply (rule prems)
   apply (erule UnI1 UnI2)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (rule Diff_Un_disjunct)
     apply (rule prems)
    apply (rule Diff_mono[OF _ subset_refl])
    apply (unfold UN_extend_simps(2))
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
    apply (unfold prod.collapse)
     apply (rule prems)
  apply (erule UnI1 UnI2)
  done
  done

lemma U2FVars_subset_2: "valid_P p \<Longrightarrow> set6_T2_pre (y::('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b, _, _, _, _, _, _) T2_pre) \<inter> (PFVars_2 p \<union> avoiding_set2) = {} \<Longrightarrow>
  (\<And>t pu p. valid_P p \<Longrightarrow> (t, pu) \<in> set7_T2_pre y \<union> set8_T2_pre y \<Longrightarrow> U1FVars_2 t (pu p) \<subseteq> FFVars_T12 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  (\<And>t pu p. valid_P p \<Longrightarrow> (t, pu) \<in> set9_T2_pre y \<union> set10_T2_pre y \<Longrightarrow> U2FVars_2 t (pu p) \<subseteq> FFVars_T22 t \<union> PFVars_2 p \<union> avoiding_set2) \<Longrightarrow>
  U2FVars_2 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) (U2ctor y p) \<subseteq> FFVars_T22 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) \<union> PFVars_2 p \<union> avoiding_set2"
  apply (unfold avoiding_set2_def Un_empty_right)
  subgoal premises prems
  apply (unfold U2ctor_def case_prod_beta)
  apply (rule case_split)
   apply (subst if_P)
      apply assumption
     apply (unfold isVVr21_def)[1]
     apply (erule exE)
     apply (drule sym)
     apply (erule subst)
     apply (unfold asVVr_VVrs)
     apply (rule case_split[of "_ = _"])
      apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]])
       apply (rule arg_cong[of _ _ FFVars_T22])
       prefer 2
       apply (rule Un_upper1)
      apply assumption
     apply (rule subsetI)
     apply (rule UnI2)
     apply (unfold PFVars_2_def case_prod_beta IImsupp21_2_def SSupp21_def)[1]
     apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 3 3] 1\<close>)
     apply (rule UnI2)?
     apply (rule UN_I)
      apply (rule iffD2[OF mem_Collect_eq])
      apply assumption
     apply (rule iffD2[OF arg_cong2[OF refl comp_apply, of "(\<in>)"]])
     apply assumption
  apply (unfold if_not_P)
  apply (unfold T1.FFVars_cctors)
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_id image_comp comp_def)
  apply (rule Un_mono')+
      apply (rule Un_upper1)
     apply (unfold UN_extend_simps(2))
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
        apply (unfold prod.collapse)
        apply (rule prems)
     apply (erule UnI1 UnI2)
    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
     apply (rule Diff_Un_disjunct)
     apply (rule prems)
    apply (rule Diff_mono[OF _ subset_refl])
    apply (unfold UN_extend_simps(2))
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
    apply (unfold prod.collapse)
       apply (rule prems)
    apply (erule UnI1 UnI2)
     apply (rule subset_If)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
    apply (unfold prod.collapse)
    apply (rule prems)
     apply (erule UnI1 UnI2)
    apply (rule subset_If)
     apply (unfold UN_empty')[1]
     apply (rule empty_subsetI)
    apply (rule UN_mono[OF subset_refl])
    apply (rule prems)
     apply (unfold prod.collapse)
     apply (rule prems)
    apply (erule UnI2 UnI1 | rule UnI1)+
  done
  done

lemma isVVr_renames:
fixes f1::"'var::{var_T1_pre, var_T2_pre} \<Rightarrow> 'var" and f2::"'tyvar::{var_T1_pre, var_T2_pre} \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows
    "isVVr11 x = isVVr11 (rrename_T1 f1 f2 x)"
    "isVVr12 x = isVVr12 (rrename_T1 f1 f2 x)"
    "isVVr21 y = isVVr21 (rrename_T2 f1 f2 y)"
  apply (unfold isVVr11_def)
  apply (rule iffI)
   apply (erule exE)
   apply hypsubst_thin
   apply (subst rrename_VVrs)
       apply (rule assms)+
   apply (rule exI)
   apply (rule refl)
  apply (erule exE)
  apply (drule arg_cong[of _ _ "rrename_T1 (inv f1) (inv f2)"])
  apply (subst (asm) T1.rrename_comps)
          apply (rule assms supp_inv_bound bij_imp_bij_inv)+
  apply (subst (asm) inv_o_simp1, rule assms)+
  apply (unfold T1.rrename_ids)
  apply (subst (asm) rrename_VVrs)
      apply (rule supp_inv_bound bij_imp_bij_inv assms)+
  apply hypsubst_thin
  apply (rule exI)
    apply (rule refl)
  (* copied from above *)
  apply (unfold isVVr12_def)
  apply (rule iffI)
   apply (erule exE)
   apply hypsubst_thin
   apply (subst rrename_VVrs)
       apply (rule assms)+
   apply (rule exI)
   apply (rule refl)
  apply (erule exE)
  apply (drule arg_cong[of _ _ "rrename_T1 (inv f1) (inv f2)"])
  apply (subst (asm) T1.rrename_comps)
          apply (rule assms supp_inv_bound bij_imp_bij_inv)+
  apply (subst (asm) inv_o_simp1, rule assms)+
  apply (unfold T1.rrename_ids)
  apply (subst (asm) rrename_VVrs)
      apply (rule supp_inv_bound bij_imp_bij_inv assms)+
  apply hypsubst_thin
  apply (rule exI)
   apply (rule refl)
  (* copied from above *)
  apply (unfold isVVr21_def)
  apply (rule iffI)
   apply (erule exE)
   apply hypsubst_thin
   apply (subst rrename_VVrs)
       apply (rule assms)+
   apply (rule exI)
   apply (rule refl)
  apply (erule exE)
  apply (drule arg_cong[of _ _ "rrename_T2 (inv f1) (inv f2)"])
  apply (subst (asm) T1.rrename_comps)
          apply (rule assms supp_inv_bound bij_imp_bij_inv)+
  apply (subst (asm) inv_o_simp1, rule assms)+
  apply (unfold T1.rrename_ids)
  apply (subst (asm) rrename_VVrs)
      apply (rule supp_inv_bound bij_imp_bij_inv assms)+
  apply hypsubst_thin
  apply (rule exI)
  apply (rule refl)
  done

lemma valid_Pmap: "valid_P p \<Longrightarrow>
  bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o cmin |UNIV::'var set| |UNIV::'tyvar set| \<Longrightarrow>
  bij f2 \<Longrightarrow> |supp (f2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o cmin |UNIV::'var set| |UNIV::'tyvar set| \<Longrightarrow>
  valid_P (Pmap f1 f2 p)"
  apply (unfold valid_P_def Pmap_def case_prod_beta compSS_defs fst_conv snd_conv)
  apply (erule conjE)+
  apply (assumption | rule conjI SSupp_comp_bounds SSupp_rename_bounds supp_inv_bound)+
  done

lemma U1map_Uctor: "valid_P p \<Longrightarrow> bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o cmin |UNIV::'var set| |UNIV::'tyvar set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o cmin |UNIV::'var set| |UNIV::'tyvar set| \<Longrightarrow>
  U1map f1 f2 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) (U1ctor y p)
= U1ctor (map_T1_pre f1 f2 id id f1 f2
    (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. if valid_P p then U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
    (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. if valid_P p then U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
    (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. if valid_P p then U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
    (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. if valid_P p then U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
 y) (Pmap f1 f2 p)"
  apply (unfold U1ctor_def)
  apply (subst T1_pre.map_comp, (assumption | rule supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
  apply (unfold id_o_commute[of f1] id_o_commute[of f2] fst_o_f comp_assoc comp_def[of snd] snd_conv case_prod_beta prod.collapse)
  apply (subst T1_pre.map_comp[symmetric], (rule supp_id_bound bij_id | assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
  apply (subst T1.rrename_cctors[symmetric] isVVr_renames[symmetric], (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
    (* REPEAT_DETERM *)
  apply (rule case_split)
   apply (subst if_P)
    apply assumption
   apply (unfold if_P if_not_P)
   apply (unfold isVVr11_def)[1]
   apply (erule exE)
   apply (drule sym)
  apply (erule subst)
   apply (unfold Pmap_def case_prod_beta fst_conv snd_conv asVVr_VVrs)[1]
   apply (subst rrename_VVrs)
       apply (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
   apply (unfold asVVr_VVrs compSS_defs comp_def)[1]
   apply (subst inv_simp1)
    apply assumption
   apply (rule refl)
    (* copied from above *)
  apply (rule case_split)
   apply (subst if_P)
    apply assumption
   apply (unfold if_P if_not_P)
   apply (unfold isVVr12_def)[1]
   apply (erule exE)
   apply (drule sym)
  apply (erule subst)
   apply (unfold Pmap_def case_prod_beta fst_conv snd_conv asVVr_VVrs)[1]
   apply (subst rrename_VVrs)
       apply (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
   apply (unfold asVVr_VVrs compSS_defs comp_def)[1]
   apply (subst inv_simp1)
    apply assumption
   apply (rule refl)
    (* END REPEAT_DETERM *)
  apply (rule trans)
   apply (rule T1.rrename_cctors)
      apply (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
  apply (subst T1_pre.map_comp, (assumption | rule supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
  apply (unfold id_o o_id)
  apply (unfold comp_def)
  apply (subst trans[OF comp_apply[symmetric] fun_cong[OF Pmap_comp0]], (assumption | rule supp_inv_bound bij_imp_bij_inv)+)+
  apply (subst inv_o_simp1, assumption)+
  apply (unfold trans[OF fun_cong[OF Pmap_id0] id_apply])
  apply (subst valid_Pmap, assumption+)+
  apply (unfold if_True)
  apply (rule refl)
  done

lemma U2map_Uctor: "valid_P p \<Longrightarrow> bij f1 \<Longrightarrow> |supp (f1::'var::{var_T1_pre,var_T2_pre} \<Rightarrow> 'var)| <o cmin |UNIV::'var set| |UNIV::'tyvar set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'tyvar::{var_T1_pre,var_T2_pre} \<Rightarrow> 'tyvar)| <o cmin |UNIV::'var set| |UNIV::'tyvar set| \<Longrightarrow>
  U2map f1 f2 (T2_ctor (map_T2_pre id id id id id id fst fst fst fst y)) (U2ctor y p)
= U2ctor (map_T2_pre f1 f2 id id f1 f2
    (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. if valid_P p then U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
    (\<lambda>(t, pu). (rrename_T1 f1 f2 t, \<lambda>p. if valid_P p then U1map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
    (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. if valid_P p then U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
    (\<lambda>(t, pu). (rrename_T2 f1 f2 t, \<lambda>p. if valid_P p then U2map f1 f2 t (pu (Pmap (inv f1) (inv f2) p)) else undefined))
 y) (Pmap f1 f2 p)"
  apply (unfold U2ctor_def)
  apply (subst T2_pre.map_comp, (assumption | rule supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
  apply (unfold id_o_commute[of f1] id_o_commute[of f2] fst_o_f comp_assoc comp_def[of snd] snd_conv case_prod_beta prod.collapse)
  apply (subst T2_pre.map_comp[symmetric], (rule supp_id_bound bij_id | assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
  apply (subst T1.rrename_cctors[symmetric] isVVr_renames[symmetric], (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
    (* REPEAT_DETERM *)
  apply (rule case_split)
   apply (subst if_P)
    apply assumption
   apply (unfold if_P if_not_P)
   apply (unfold isVVr21_def)[1]
   apply (erule exE)
   apply (drule sym)
  apply (erule subst)
   apply (unfold Pmap_def case_prod_beta fst_conv snd_conv asVVr_VVrs)[1]
   apply (subst rrename_VVrs)
       apply (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
   apply (unfold asVVr_VVrs compSS_defs comp_def)[1]
   apply (subst inv_simp1)
    apply assumption
   apply (rule refl)
    (* END REPEAT_DETERM *)
  apply (rule trans)
   apply (rule T1.rrename_cctors)
      apply (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
  apply (subst T2_pre.map_comp, (assumption | rule supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
  apply (unfold id_o o_id)
  apply (unfold comp_def)
  apply (subst trans[OF comp_apply[symmetric] fun_cong[OF Pmap_comp0]], (assumption | rule supp_inv_bound bij_imp_bij_inv)+)+
  apply (subst inv_o_simp1, assumption)+
  apply (unfold trans[OF fun_cong[OF Pmap_id0] id_apply])
  apply (subst valid_Pmap, assumption+)+
  apply (unfold if_True)
  apply (rule refl)
  done

(* parameter axioms *)
thm Pmap_id0
thm Pmap_comp0
thm Pmap_cong_id
thm PFVars_Pmaps
thm small_PFVarss
thm small_avoiding_sets
thm valid_Pmap

(* model1 axioms *)
thm U1map_Uctor
thm U1FVars_subset_1 U1FVars_subset_2

(* model2 axioms *)
thm U2map_Uctor
thm U2FVars_subset_1 U2FVars_subset_2

ML \<open>
val nvars:int = 2

val parameters = {
  P = @{typ "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) P"},
  Pmap = @{term "Pmap :: _ \<Rightarrow> _ \<Rightarrow> ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) P \<Rightarrow> _"},
  PFVarss = [
    @{term "PFVars_1 :: ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) P \<Rightarrow> _"},
    @{term "PFVars_2 :: ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) P \<Rightarrow> _"}
  ],
  avoiding_sets = [
    @{term "avoiding_set1 :: 'var::{var_T1_pre,var_T2_pre} set"},
    @{term "avoiding_set2 :: 'tyvar::{var_T1_pre,var_T2_pre} set"}
  ],
  min_bound = true,
  validity = SOME {
    pred = @{term "valid_P :: ('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'a::{var_T1_pre, var_T2_pre}, 'b) P \<Rightarrow> _"},
    valid_Pmap = fn ctxt => HEADGOAL (resolve_tac ctxt @{thms valid_Pmap} THEN_ALL_NEW assume_tac ctxt)
  },
  axioms = {
    Pmap_id0 = fn ctxt => EVERY1 [
      resolve_tac ctxt [trans],
      resolve_tac ctxt @{thms fun_cong[OF Pmap_id0]},
      resolve_tac ctxt @{thms id_apply}
    ],
    Pmap_comp0 = fn ctxt => resolve_tac ctxt @{thms fun_cong[OF Pmap_comp0[symmetric]]} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    Pmap_cong_id = fn ctxt => resolve_tac ctxt @{thms Pmap_cong_id} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1),
    PFVars_Pmaps = replicate nvars (fn ctxt => resolve_tac ctxt @{thms PFVars_Pmaps} 1 THEN REPEAT_DETERM (assume_tac ctxt 1)),
    small_PFVarss = replicate nvars (fn ctxt => resolve_tac ctxt @{thms small_PFVarss} 1 THEN assume_tac ctxt 1),
    small_avoiding_sets = replicate nvars (fn ctxt => resolve_tac ctxt @{thms small_avoiding_sets} 1)
  }
};

val card_thms = @{thms ordLess_ordLeq_trans[of _ "cmin _ _" "|_|"] cmin1 cmin2 card_of_Card_order}
\<close>

ML \<open>
val T1_model = {
  binding = @{binding tvsubst_T1},
  U = @{typ "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) U1"},
  UFVarss = [
    @{term "U1FVars_1 :: _ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) U1 \<Rightarrow> _"},
    @{term "U1FVars_2 :: _ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) U1 \<Rightarrow> _"}
  ],
  Umap = @{term "U1map::_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) U1 \<Rightarrow> _"},
  Uctor = @{term "U1ctor::_ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) P \<Rightarrow> _"},
  validity = NONE : { pred: term, valid_Umap: Proof.context -> tactic, valid_Uctor: Proof.context -> tactic } option,
  axioms = {
    Umap_id0 = fn ctxt => EVERY1 [
      resolve_tac ctxt [trans],
      resolve_tac ctxt @{thms T1.rrename_id0s[THEN fun_cong]},
      resolve_tac ctxt @{thms id_apply}
    ],
    Umap_comp0 = fn ctxt => resolve_tac ctxt @{thms T1.rrename_comp0s[symmetric, THEN fun_cong]} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE resolve_tac ctxt card_thms 1),
    Umap_cong_id = fn ctxt => resolve_tac ctxt @{thms T1.rrename_cong_ids} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1 ORELSE resolve_tac ctxt card_thms 1),
    Umap_Uctor = fn ctxt => resolve_tac ctxt @{thms U1map_Uctor} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    UFVars_subsets = replicate nvars (fn ctxt => resolve_tac ctxt @{thms U1FVars_subset_1 U1FVars_subset_2} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1))
  }
};

val T2_model = {
  binding = @{binding vvsubst_T2},
  U = @{typ "('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) U2"},
  UFVarss = [
    @{term "U2FVars_1 :: _ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) U2 \<Rightarrow> _"},
    @{term "U2FVars_2 :: _ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) U2 \<Rightarrow> _"}
  ],
  Umap = @{term "U2map::_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) U2 \<Rightarrow> _"},
  Uctor = @{term "U2ctor::_ \<Rightarrow> ('var::{var_T1_pre,var_T2_pre}, 'tyvar::{var_T1_pre,var_T2_pre}, 'a::{var_T1_pre,var_T2_pre}, 'b) P \<Rightarrow> _"},
  validity = NONE : { pred: term, valid_Umap: Proof.context -> tactic, valid_Uctor: Proof.context -> tactic } option,
  axioms = {
    Umap_id0 = fn ctxt => EVERY1 [
      resolve_tac ctxt [trans],
      resolve_tac ctxt @{thms T1.rrename_id0s[THEN fun_cong]},
      resolve_tac ctxt @{thms id_apply}
    ],
    Umap_comp0 = fn ctxt => resolve_tac ctxt @{thms T1.rrename_comp0s[symmetric, THEN fun_cong]} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE resolve_tac ctxt card_thms 1),
    Umap_cong_id = fn ctxt => resolve_tac ctxt @{thms T1.rrename_cong_ids} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1 ORELSE resolve_tac ctxt card_thms 1),
    Umap_Uctor = fn ctxt => resolve_tac ctxt @{thms U2map_Uctor} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    UFVars_subsets = replicate nvars (fn ctxt => resolve_tac ctxt @{thms U2FVars_subset_1 U2FVars_subset_2} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1))
  }
};

val fp_res = the (MRBNF_FP_Def_Sugar.fp_result_of @{context} "Fixpoint.T1")
\<close>

local_setup \<open>fn lthy =>
let
  val qualify = I
  val (ress, lthy) = MRBNF_Recursor.create_binding_recursor qualify fp_res parameters [T1_model, T2_model] lthy
  val _ = @{print} ress
in lthy end\<close>
print_theorems
end