theory Regression_Tests
  imports "Binders.MRBNF_Recursor"
begin

(* types have the GitHub issue number as postfix *)

binder_datatype 'a trm_68 = Var 'a | Abs x::'a t::"'a trm_68" binds x in t
  

end