theory Regression_Tests
  imports "Binders.MRBNF_Recursor" "../thys/LetRec/DAList_MRBNF"
     "System_Fsub.Pattern"
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

(* #72 *)
binder_datatype (FVars: 'v, FTVars: 'tv) trm2 =
    Var 'v
  | Let "('tv, p::'v) pat" "('v, 'tv) trm2" t::"('v, 'tv) trm2" binds p in t

(* #75 *)
binder_datatype ('a, 'b, 'c, 'd) trm3 =
    Var 'a
  | App "('a, 'b, 'c, 'd) trm3" "('a, 'b, 'c, 'd) trm3"
  | Lam a::'a b::'b c::'c d::'d e::"('a, 'b, 'c, 'd) trm3" binds a b c d in e

(* #74 *)
binder_datatype 'a trm4 = V 'a | Lm x::'a t::"'a trm4" binds x in t
binder_datatype 'a foo = Foo 'a | Bind "(x::'a) trm4" t::"'a foo" binds x in t

end
