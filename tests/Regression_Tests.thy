theory Regression_Tests
  imports "Binders.MRBNF_Recursor" "../thys/LetRec/DAList_MRBNF"
begin

(* types have the GitHub issue number as postfix *)

binder_datatype 'a trm_68 =
  Var 'a
| Abs x::'a t::"'a trm_68" binds x in t
  
binder_datatype 'a LLC_69 =
  Var 'a
  | App "'a LLC_69" "'a LLC_69"
  | Abs x::'a t::"'a LLC_69" binds x in t
  | Let "(x::'a, t::'a LLC_69) alist" u::"'a LLC_69" binds x in t u

end