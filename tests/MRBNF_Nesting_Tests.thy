theory MRBNF_Nesting_Tests
  imports "../thys/MRBNF_Recursor" "../DALList" "HOL-Eisbach.Eisbach"
begin

datatype \<tau> = Base | Arrow \<tau> \<tau> (infixr "(\<rightarrow>)" 50)

lemma disjointI: "(\<And>x. x \<in> A \<Longrightarrow> x \<notin> B) \<Longrightarrow> A \<inter> B = {}"
  by blast
lemma notin_empty_eq_True: "x \<notin> {} = True"
  by simp

ML_file \<open>../Tools/mrbnf_sugar.ML\<close>

ML \<open>
val ctors = [
  (("Var", NONE), [@{typ 'var}]),
  (("App", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("Lam", NONE), [@{typ 'bvar}, @{typ \<tau>}, @{typ 'brec}]),
  (("Let", NONE), [@{typ "('bvar, \<tau> \<times> 'rec) dallist"}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "term"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[1]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst}
} : MRBNF_Sugar.spec;
\<close>

local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Sugar.create_binder_datatype spec lthy
in lthy' end\<close>
print_theorems
print_mrbnfs

thm
  term.strong_induct
  term.fresh_induct
  term.induct

end