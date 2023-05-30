theory SystemF
  imports "thys/MRBNF_Recursor"
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
  (("TyVar", (NONE : mixfix option)), [@{typ 'var}]),
  (("TyArr", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("TyApp", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("TyAll", NONE), [@{typ 'bvar}, @{typ 'brec}])
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
  map_b = @{binding ty_vvsubst},
  tvsubst_b = @{binding ty_tvsubst}
}
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
| Lam x::'b ty::"'a \<tau>" t::"('a,'b) term" binds x in t
| TyApp "('a,'b) term" "'a \<tau>"
| TyLam \<alpha>::'a body::"('a,'b) term" binds \<alpha> in body
*)

ML \<open>
val ctors = [
  (("Var", (NONE : mixfix option)), [@{typ 'var}]),
  (("App", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("Lam", NONE), [@{typ 'bvar}, @{typ "'tyvar \<tau>"}, @{typ 'brec}]),
  (("TyApp2", NONE), [@{typ 'rec}, @{typ "'tyvar \<tau>"}]),
  (("TyLam", NONE), [@{typ 'btyvar}, @{typ 'brec}])
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