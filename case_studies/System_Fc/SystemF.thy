theory SystemF
  imports "Binders.MRBNF_Recursor"
begin

binder_datatype 'a \<tau> =
    TyVar 'a
  | Arrow "'a \<tau>" "'a \<tau>" (infixr "\<rightarrow>" 40)
  | TyApp "'a \<tau>" "'a \<tau>" (infixr "@" 40)
  | TyAll \<alpha>::'a "'a \<tau>" t::"'a \<tau>" ("\<forall>_<_._" [30, 30, 30] 30) binds \<alpha> in t

thm \<tau>.strong_induct
thm \<tau>.set
thm \<tau>.map
thm \<tau>.subst

binder_datatype ('a, 'b) "term" =
  Var 'a
| App "('a, 'b) term" "('a, 'b) term"
| Lam x::'a "'b \<tau>" t::"('a, 'b) term" binds x in t
| TApp "('a, 'b) term" "'b \<tau>"
| TLam \<alpha>::'b t::"('a, 'b) term" binds \<alpha> in t
for
  vvsubst: vvsubst
  tvsubst: tvsubst

thm term.strong_induct
thm term.set
thm term.map
thm term.subst

end
