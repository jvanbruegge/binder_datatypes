theory MRBNF_Nesting_Tests
  imports "../thys/MRBNF_Recursor" "../DALList"
begin

datatype \<tau> = Base | Arrow \<tau> \<tau> (infixr "(\<rightarrow>)" 50)

ML \<open>
val ctors = [
  (("Var", NoSyn), [@{typ 'var}]),
  (("TyVar", NoSyn), [@{typ 'tyvar}]),
  (("App", NoSyn), [@{typ 'rec}, @{typ 'rec}]),
  (("Lam", NoSyn), [@{typ 'bvar}, @{typ \<tau>}, @{typ 'brec}]),
  (("TyLam", NoSyn), [@{typ 'btyvar}, @{typ \<tau>}, @{typ 'brec}]),
  (("Let", NoSyn), [@{typ "('bvar, \<tau> \<times> 'rec) dallist"}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "term"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'tyvar}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'btyvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[1], [1]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst},
  tvsubst_b = @{binding tvsubst}
}
\<close>

declare [[ML_print_depth=10000]]

local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Sugar.create_binder_datatype spec lthy
in lthy' end\<close>
print_theorems
print_mrbnfs

declare [[names_short]]
thm
  term.strong_induct
  term.fresh_induct
  term.induct

thm term.set
thm term.map
thm term.distinct
thm term.subst

end
