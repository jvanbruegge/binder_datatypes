theory Binder_Datatype_Tests
  imports "Binders.MRBNF_Recursor"
begin

binder_datatype ('a, 'b, free 'c, 'd, 'f, bound 'e) T1 =
  Inj1 'a | Inj2 'b | App "('a, 'b, 'c, 'd, 'f, 'e) T1" "('a, 'b, 'c, 'd, 'f, 'e) T1"
| Bdr1 x::'a t::"('a, 'b, 'c, 'd, 'f, 'e) T1" binds x in t
| Bdr2 x::'b "(t::('a, 'b, 'c, 'd, 'f, 'e) T1) list" binds x in t
| Passive 'c 'd 'e 'f

end
