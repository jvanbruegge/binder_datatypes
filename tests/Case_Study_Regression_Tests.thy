theory Case_Study_Regression_Tests
  imports "Binders.MRBNF_Recursor" "System_Fsub.Pattern"
begin

(* #72 *)
binder_datatype (FVars: 'v, FTVars: 'tv) trm2 =
  Var 'v
  | Let "('tv, p::'v) pat" "('v, 'tv) trm2" t::"('v, 'tv) trm2" binds p in t

end