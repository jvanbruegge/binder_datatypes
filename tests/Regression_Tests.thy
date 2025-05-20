theory Regression_Tests
  imports "Binders.MRBNF_Recursor" "../thys/LetRec/DAList_MRBNF" "HOL-Library.FSet"
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

(* #75 *)
binder_datatype ('a, 'b, 'c, 'd) trm3 =
    Var 'a
  | App "('a, 'b, 'c, 'd) trm3" "('a, 'b, 'c, 'd) trm3"
  | Lam a::'a b::'b c::'c d::'d e::"('a, 'b, 'c, 'd) trm3" binds a b c d in e

(* #74 *)
binder_datatype 'a trm4 = V 'a | Lm x::'a t::"'a trm4" binds x in t
binder_datatype 'a foo = Foo 'a | Bind "(x::'a) trm4" t::"'a foo" binds x in t

(* #82 *)
datatype ('ev, 'rv) aeff = Eff 'ev | Reg 'rv

type_synonym ('ev, 'rv) eff = "('ev, 'rv) aeff fset"

datatype ('ev, 'rv) constraint = Constraint "('ev, 'rv) eff" "('ev, 'rv) eff"

datatype ('tv, 'ev, 'rv) type2 =
   TVar 'tv
 | TInt
 | BFun "('tv, 'ev, 'rv) type2" 'ev "('ev, 'rv) eff" "('tv, 'ev, 'rv) type2"

binder_datatype ('tv, 'ev, 'rv) type_scheme3 =
    TAll "(X::'tv) list" \<sigma>::"('tv, 'ev, 'rv) type_scheme3" binds X in \<sigma>
  | ERAll "(\<epsilon>::'ev) list" "(\<rho>::'rv) list" T::"('tv, 'ev, 'rv) type2" binds \<epsilon> \<rho> in T

binder_datatype ('v, 'tv, 'ev, 'rv) expr =
    Var 'v
  | Int int
  | Lam bool x::'v e::"('v, 'tv, 'ev, 'rv) expr" 'rv binds x in e
  | Fun bool f::'v "(\<alpha>::'tv, \<epsilon>::'ev, \<rho>::'rv) type_scheme3" "(\<sigma>::'rv) list" x::'v e::"('v, 'tv, 'ev, 'rv) expr" 'rv binds f \<alpha> \<epsilon> \<rho> \<sigma> x in e
  | App "('v, 'tv, 'ev, 'rv) expr" "('v, 'tv, 'ev, 'rv) expr"
  | Letregion "(\<epsilon>::'ev, \<rho>::'rv) eff" e::"('v, 'tv, 'ev, 'rv) expr" binds \<epsilon> \<rho> in e
  | Assert "('ev, 'rv) constraint"  "('v, 'tv, 'ev, 'rv) expr"
  | Let x::'v "('v, 'tv, 'ev, 'rv) expr"  e::"('v, 'tv, 'ev, 'rv) expr" binds x in e
  | RApp "('v, 'tv, 'ev, 'rv) expr" "'rv list"  "('v, 'tv, 'ev, 'rv) expr"

(* #86 *)
binder_datatype 'a "term" =
  Var 'a
| App "'a term" "'a term"
| Lam x::'a t::"'a term" binds x in t
| Let "(xs::'a, 'a term) alist" t::"'a term" binds xs in t

end
