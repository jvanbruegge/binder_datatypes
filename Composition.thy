theory Composition
  imports "thys/MRBNF_Composition"
begin

datatype \<kappa> =
  Star ("\<star>")
  | KArrow \<kappa> \<kappa> (infixr "\<rightarrow>" 50)

(*
  TyVar 'tyvar
  | TyArrow
  | TyApp 'd 'd
  | TyForall 'btyvar \<kappa> 'c
*)
ML \<open>
val systemf_type = @{typ "'tyvar + unit + 'd * 'd + 'btyvar * \<kappa> * 'c"}
val systemf_type_vars = {
  lives = [("''d", @{sort type}), ("'c", @{sort type})],
  frees = [("'tyvar", @{sort type})],
  bounds = [("'btyvar", @{sort type})],
  deads = []
}
\<close>

print_mrbnfs
print_bnfs

local_setup \<open>snd o the o MRBNF_Comp.as_mrbnf "Sum_Type.sum"\<close>
local_setup \<open>snd o the o MRBNF_Comp.as_mrbnf "List.list"\<close>
print_mrbnfs

ML \<open>
val sum = the (MRBNF_Def.mrbnf_of @{context} \<^type_name>\<open>sum\<close>)
val list = the (MRBNF_Def.mrbnf_of @{context} \<^type_name>\<open>list\<close>)
\<close>

local_setup \<open>fn lthy => let
  val (mrbnf, (_, lthy')) = MRBNF_Comp.clean_compose_mrbnf MRBNF_Def.Dont_Inline I Binding.empty
                              sum [MRBNF_Comp.ID_mrbnf, list] ({map_unfolds = [], set_unfoldss = [], rel_unfolds = []}, lthy)
  in lthy' end
\<close>

ML \<open>
val test = @{typ "unit + unit + 'a list"}
\<close>

local_setup \<open>snd o MRBNF_Comp.mrbnf_of_typ { lives = [("'a", @{sort type})], frees = [], bounds = [], deads = [] } test\<close>

print_mrbnfs

end
