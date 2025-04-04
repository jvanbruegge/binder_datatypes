theory Regression_Tests
  imports "Binders.MRBNF_Recursor" "../thys/LetRec/DAList_MRBNF"
begin

(* #68 *)
binder_datatype 'a trm =
  Var 'a
| Abs x::'a t::"'a trm" binds x in t

(* #69 *)
binder_datatype 'a LLC =
  Var 'a
  | App "'a LLC" "'a LLC"
  | Abs x::'a t::"'a LLC" binds x in t
  | Let "(x::'a, t::'a LLC) alist" u::"'a LLC" binds x in t u

(* #70 *)
datatype ('tv, 'ev, 'rv) type = Type 'tv 'ev 'rv
binder_datatype ('tv, 'ev, 'rv) type_scheme =
  TAll "(X::'tv) list" \<sigma>::"('tv, 'ev, 'rv) type_scheme" binds X in \<sigma>
  | ERAll "(\<epsilon>::'ev) list" "(\<rho>::'rv) list" "('tv, A::'ev, B::'rv) type" binds \<epsilon> \<rho> in A B

(* #71 *)
binder_datatype ('tv, 'ev, 'rv) type_scheme2 =
  TAll "(X::'tv) list" \<sigma>::"('tv, 'ev, 'rv) type_scheme2" binds X in \<sigma>
  | ERAll "(\<epsilon>::'ev) list" "(\<rho>::'rv) list" T::"('tv, 'ev, 'rv) type" binds \<epsilon> \<rho> in T

end