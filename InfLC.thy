theory InfLC
  imports "thys/MRBNF_Recursor" "HOL-Library.FSet" "Coinductive.Coinductive_List"
begin

datatype \<tau> = Unit | Arrow "\<tau> llist" \<tau> (infixr "\<rightarrow>" 40)

(* binder_datatype 'a terms =
  Var 'a
| App "'a terms" "'a terms"
| Abs x::'a \<tau> t::"'a terms" binds x in t
*)

ML \<open>
val ctors = [
  (("Var", (NONE : mixfix option)), [@{typ 'var}]),
  (("App", NONE), [@{typ 'rec}, @{typ "'rec llist"}]),
  (("Abs", NONE), [@{typ "('bvar \<times> \<tau>) llist"}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "terms"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst},
  tvsubst_b = @{binding tvsubst}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Sugar.create_binder_datatype spec lthy
in lthy' end\<close>
print_mrbnfs

end
