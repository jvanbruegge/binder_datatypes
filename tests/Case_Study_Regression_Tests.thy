theory Case_Study_Regression_Tests
  imports "Binders.MRBNF_Recursor" "System_Fsub.Pattern" "Infinitary_Lambda_Calculus.ILC"
begin

(* #72 *)
binder_datatype (FVars: 'v, FTVars: 'tv) trm2 =
  Var 'v
  | Let "('tv, p::'v) pat" "('v, 'tv) trm2" t::"('v, 'tv) trm2" binds p in t

(* #126 *)
binder_datatype (FFVars: 'a) iterm2
  = iVar 'a
  | iApp "'a iterm2" "'a iterm2 stream"
  | iLam "(xs::'a) stream" t::"'a iterm2" binds xs in t
for
  map: ivvsubst
  subst: itvsubst

end