theory SystemF
  imports "Binders.MRBNF_Recursor"
begin

datatype \<kappa> = Star ("\<star>") | Arrow \<kappa> \<kappa> (infixr "\<rightarrow>" 40)

(* binder_datatype 'a \<tau> =
  TyVar 'a
  | Arrow "'a \<tau>" "'a \<tau>" (infixr "\<rightarrow>" 40)
  | TyApp "'a \<tau>" "'a \<tau>" (infixr "@" 40)
  | TyAll \<alpha>::'a bound::"'a \<tau>" tybody::"'a \<tau>" binds \<alpha> in tybody (infixr "\<forall>_<_._" 30)

*)
ML \<open>
val tyctors = [
  (("TyVar", NoSyn), [@{typ 'var}]),
  (("TyArr", NoSyn), [@{typ 'rec}, @{typ 'rec}]),
  (("TyAll", NoSyn), [@{typ 'bvar}, @{typ 'brec}])
]
val tyspec = {
  fp_b = @{binding "\<tau>"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = tyctors,
  map_b = @{binding vvsubst_\<tau>},
  tvsubst_b = @{binding tvsubst_\<tau>}
}
\<close>

ML_file \<open>../../Tools/mrbnf_sugar.ML\<close>
ML \<open>
Multithreading.parallel_proofs := 0
\<close>

declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Sugar.create_binder_datatype tyspec lthy
in lthy' end\<close>
print_theorems
print_mrbnfs

thm \<tau>.strong_induct
thm \<tau>.set
thm \<tau>.map
thm \<tau>.subst

(* binder_datatype ('a,'b) term =
  Var 'b
| App "('a,'b) term" "('a,'b) term"
| Lam x::'b ty::"('a, 'b) \<tau>" t::"('a,'b) term" binds x in t
| TyApp "('a,'b) term" "'a \<tau> list"
| TyLam \<alpha>::'a body::"('a,'b) term" binds \<alpha> in body
*)
(*

definition U1ctor :: "('var::{var_T1_pre, var_T2_pre}, 'tyvar::{var_T1_pre, var_T2_pre}, 'var, 'tyvar, ('var, 'tyvar) T1 \<times> (('var, 'tyvar) P \<Rightarrow> ('var, 'tyvar) U1), ('var, 'tyvar, 'a, 'b) T1 \<times> (('var, 'tyvar, 'a, 'b) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1),
  ('var, 'tyvar, 'a, 'b) T2 \<times> (('var, 'tyvar, 'a, 'b) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2), ('var, 'tyvar, 'a, 'b) T2 \<times> (('var, 'tyvar, 'a, 'b) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U2)) T1_pre \<Rightarrow> ('var, 'tyvar, 'a, 'b) P \<Rightarrow> ('var, 'tyvar, 'a, 'b) U1" where
  "U1ctor y p \<equiv> case p of (f1, f2, f3) \<Rightarrow> if isVVr11 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) then
    f1 (asVVr11 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y))) else (
  if isVVr12 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y)) then
    f2 (asVVr12 (T1_ctor (map_T1_pre id id id id id id fst fst fst fst y))) else (
  T1_ctor (map_T1_pre id id id id id id ((\<lambda>R. R (f1, f2, f3)) \<circ> snd) ((\<lambda>R. R (f1, f2, f3)) \<circ> snd) ((\<lambda>R. R (f1, f2, f3)) \<circ> snd) ((\<lambda>R. R (f1, f2, f3)) \<circ> snd) (case y of 
    Lam x t1 t2 \<Rightarrow> Lam x (tvsubst_\<tau> f1 t1) t2
  | TyApp t1 ts \<Rightarrow> TyApp t1 (map (tvsubst_\<tau> f1) ts)
  | x \<Rightarrow> x
  ))
))"
*)
(*

'a \<Rightarrow> 'a 'm
ctor \<circ> eta

type ('a, 'b, 'c) term_internal =
  Var 'b
| App "('a,'b, 'c) term" "('a,'b, 'c) term"
| Lam x::'b ty::'c t::"('a,'b, 'c) term" binds x in t
| TyApp "('a,'b,'c) term" 'c
| TyLam \<alpha>::'a body::"('a,'b,'c) term" binds \<alpha> in body

map_term_internal : ('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'c') \<Rightarrow> ('a, 'b, 'c) term_internal \<Rightarrow>  ('a, 'b, 'c') term_internal
eta : 'b \<Rightarrow> ('a, 'b, 'c) term_internal_pre
\<longrightarrow> tvsubst_term_internal ('b \<Rightarrow> ('a, 'b, 'c) term_internal) \<Rightarrow> ('a, 'b, 'c) term_internal \<Rightarrow>  ('a, 'b, 'c') term_internal

typedef ('a, 'b) term = "UNIV::('a, 'b, 'a \<tau>) term_internal set"

tvsubst_nested_term f1 t = case t of
  Lam x t t1 \<Rightarrow> Lam x (tvsubst_\<tau> f1 t1) 
  | 

tvsubst_\<tau> : ('a \<Rightarrow> 'a \<tau>) \<Rightarrow> 'a \<tau> \<Rightarrow> 'a \<tau>

tvsubst_term : ('b \<Rightarrow> ('a, 'b) term) \<Rightarrow> ('a, 'b) term \<Rightarrow> ('a, 'b) term
tvsubst_\<tau>_term : ('a \<Rightarrow> 'a \<tau>) \<Rightarrow> ('a, 'b) term \<Rightarrow> ('a, 'b) term


tvsubst_term : ('a \<Rightarrow> 'a \<tau>) \<Rightarrow> ('b \<Rightarrow> ('a, 'b) term) \<Rightarrow> ('a, 'b) term \<Rightarrow> ('a, 'b) term
tvsubst_term f1 f2 t \<equiv> tvsubst_term_internal f2 (map_term_internal id id (tvsubst_\<tau> f1) t)

*)

ML \<open>
val ctors = [
  (("Var", NoSyn), [@{typ 'var}]),
  (("App", NoSyn), [@{typ 'rec}, @{typ 'rec}]),
  (("Lam", NoSyn), [@{typ 'bvar}, @{typ "'tyvar \<tau>"}, @{typ 'brec}]),
  (("TyApp", NoSyn), [@{typ 'rec}, @{typ "'tyvar \<tau>"}]),
  (("TyLam", NoSyn), [@{typ 'btyvar}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "term"},
  vars = [
    (dest_TFree @{typ 'tyvar}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'btyvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0], [0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst},
  tvsubst_b = @{binding tvsubst}
}
\<close>

declare [[ML_print_depth=10000]]
declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Sugar.create_binder_datatype spec lthy
in lthy' end\<close>
print_theorems
print_mrbnfs

thm term.strong_induct
thm term.set
thm term.map
thm term.subst

end
