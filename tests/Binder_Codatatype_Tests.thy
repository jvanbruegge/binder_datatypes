theory Binder_Codatatype_Tests
  imports "Binders.MRBNF_Recursor"
begin

ML\<open>
Multithreading.parallel_proofs := 0
\<close>
binder_codatatype 'a "term" =
Var 'a
| App "'a term" "'a term"
| Lam x::'a t::"'a term" binds x in t

interpretation COREC_term 

end
