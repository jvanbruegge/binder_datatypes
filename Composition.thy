theory Composition
  imports "thys/MRBNF_Composition"
begin

datatype \<kappa> =
  Star ("\<star>")
  | KArrow \<kappa> \<kappa> (infixr "\<rightarrow>" 50)

typedef ('tyvar, 'btyvar, 'c, 'd) pre_\<tau> = "{ x :: 'tyvar + unit + 'd * 'd + 'btyvar * \<kappa> * 'c. True }"
  by simp
(*
  TyVar 'tyvar
  | TyArrow
  | TyApp 'd 'd
  | TyForall 'btyvar \<kappa> 'c
*)

print_mrbnfs
print_bnfs

print_mrbnfs

ML \<open>
val test = @{typ "unit + unit + 'a list"}
\<close>

local_setup \<open>snd o MRBNF_Comp.mrbnf_of_typ { lives = [("'a", dummyS)], frees = [], bounds = [], deads = [] } test\<close>

print_mrbnfs

end
