theory Binder_Datatype_Tests
  imports "Binders.MRBNF_Recursor"
begin

(*ML \<open>
Multithreading.parallel_proofs := 0
\<close>*)

declare [[ML_print_depth=10000]]
binder_datatype ('a, 'b, free 'c, 'd, 'f, bound 'e) T1 =
  Inj1 'a | Inj2 'b | App "('a, 'b, 'c, 'd, 'f, 'e) T1" "('a, 'b, 'c, 'd, 'f, 'e) T1"
| Bdr1 x::'a t::"('a, 'b, 'c, 'd, 'f, 'e) T1" binds x in t
| Bdr2 x::'b "(t::('a, 'b, 'c, 'd, 'f, 'e) T1) list" binds x in t
| Passive 'c 'd 'e 'f

(*binder_datatype (FTVars: 'tv, FVars: 'v) trm =
    Var 'v
  | Let "('tv, p::'v) pat" "('tv, 'v) trm" t::"('tv, 'v) trm" binds p in t*)


end
