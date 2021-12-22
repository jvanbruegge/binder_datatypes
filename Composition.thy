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

datatype (setF1_F: 'a, setF2_F: 'a', setL3_F: 'x, setB4_F: 'b, setB5_F: 'b', setL6_F: 'c, setL7_F: 'd, setL8_F: 'e, setL9_F: 'f) F_raw =
  E "'x + 'a + ('a' * 'b') * 'c * 'd + 'a' * 'f"
  for map: map_F rel: rel_F
type_synonym ('a, 'a', 'x, 'b, 'b', 'c, 'd, 'e, 'f) F = "('a, 'a', 'x, 'b, 'b', 'c, 'd, 'e, 'f) F_raw"

datatype (setF1_F': 'a, setF2_F': 'a', setL3_F': 'x, setB4_F': 'b, setB5_F': 'b', setL6_F': 'c, setL7_F': 'd, setL8_F': 'e, setL9_F': 'f) F_raw' =
  E "'x + 'a + ('a' * 'b') * 'c * 'd + 'a' * 'f"
  for map: map_F' rel: rel_F'
type_synonym ('a, 'a', 'x, 'b, 'b', 'c, 'd, 'e, 'f) F' = "('a, 'a', 'x, 'b, 'b', 'c, 'd, 'e, 'f) F_raw'"

datatype (setF1_G: 'a, setF2_G: 'a', setL3_G: 'y, setB4_G: 'b, setB5_G: 'b', setL6_G: 'g) G_raw =
  E "'y + 'a + ('a' * 'b') * 'y * 'g + 'a' * 'g"
  for map: map_G rel: rel_G
type_synonym ('a, 'a', 'y, 'b, 'b', 'g) G = "('a, 'a', 'y, 'b, 'b', 'g) G_raw"

print_mrbnfs
print_bnfs

local_setup \<open>snd o the o MRBNF_Def.as_mrbnf "Sum_Type.sum"\<close>
local_setup \<open>snd o the o MRBNF_Def.as_mrbnf "List.list"\<close>
print_mrbnfs

mrbnf F: "('a, 'a', 'x, 'b, 'b', 'c, 'd, 'e, 'f) F"
  map: "map_F"
  sets:
   free: "setF1_F :: _ \<Rightarrow> 'a set"
   free: "setF2_F :: _ \<Rightarrow> 'a' set"
   live: "setL3_F :: _ \<Rightarrow> 'x set"
   bound: "setB4_F :: _ \<Rightarrow> 'b set"
   bound: "setB5_F :: _ \<Rightarrow> 'b' set"
   live: "setL6_F :: _ \<Rightarrow> 'c set"
   live: "setL7_F :: _ \<Rightarrow> 'd set"
   live: "setL8_F :: _ \<Rightarrow> 'e set"
   live: "setL9_F :: _ \<Rightarrow> 'f set"
  bd: "natLeq"
  wits: "F_raw.E o Inl"
  rel: "\<lambda>X. rel_F (=) (=) X (=) (=)"
  pred: "\<lambda>X. pred_F_raw (\<lambda>_. True) (\<lambda>_. True) X (\<lambda>_. True) (\<lambda>_. True)"
  sorry

mrbnf F': "('a, 'a', 'x, 'b, 'b', 'c, 'd, 'e, 'f) F'"
  map: "map_F'"
  sets:
   free: "setF1_F' :: _ \<Rightarrow> 'a set"
   free: "setF2_F' :: _ \<Rightarrow> 'a' set"
   live: "setL3_F' :: _ \<Rightarrow> 'x set"
   bound: "setB4_F' :: _ \<Rightarrow> 'b set"
   bound: "setB5_F' :: _ \<Rightarrow> 'b' set"
   live: "setL6_F' :: _ \<Rightarrow> 'c set"
   live: "setL7_F' :: _ \<Rightarrow> 'd set"
   live: "setL8_F' :: _ \<Rightarrow> 'e set"
   live: "setL9_F' :: _ \<Rightarrow> 'f set"
  bd: "natLeq"
  wits: "F_raw'.E o Inl"
  rel: "\<lambda>X. rel_F' (=) (=) X (=) (=)"
  pred: "\<lambda>X. pred_F_raw' (\<lambda>_. True) (\<lambda>_. True) X (\<lambda>_. True) (\<lambda>_. True)"
  sorry

mrbnf G: "('a, 'a', 'y, 'b, 'b', 'g) G_raw"
  map: "map_G"
  sets:
    free: "setF1_G :: _ \<Rightarrow> 'a set"
    free: "setF2_G :: _ \<Rightarrow> 'a' set"
    live: "setL3_G :: _ \<Rightarrow> 'y set"
    bound: "setB4_G :: _ \<Rightarrow> 'b set"
    bound: "setB5_G :: _ \<Rightarrow> 'b' set"
    live: "setL6_G :: _ \<Rightarrow> 'g set"
  bd: "natLeq"
  wits: "G_raw.E o Inl"
  rel: "\<lambda>X. rel_G (=) (=) X (=) (=)"
  pred: "\<lambda>X. pred_G_raw (\<lambda>_. True) (\<lambda>_. True) X (\<lambda>_. True) (\<lambda>_. True)"
  sorry

print_mrbnfs

ML \<open>
val sum = the (MRBNF_Def.mrbnf_of @{context} \<^type_name>\<open>sum\<close>)
val list = the (MRBNF_Def.mrbnf_of @{context} \<^type_name>\<open>list\<close>)
val f = the (MRBNF_Def.mrbnf_of @{context} "Composition.F")
val f' = the (MRBNF_Def.mrbnf_of @{context} "Composition.F'")
val g = the (MRBNF_Def.mrbnf_of @{context} "Composition.G")
\<close>

ML \<open>
Multithreading.parallel_proofs := 0;
\<close>

declare [[goals_limit = 50]]
declare [[ML_print_depth=10000]]


ML_file \<open>./Tools/mrbnf_comp_tactics.ML\<close>
ML_file \<open>./Tools/mrbnf_comp.ML\<close>

local_setup \<open>fn lthy => let
  val (_, (_, lthy')) = MRBNF_Comp.clean_compose_mrbnf MRBNF_Def.Do_Inline I @{binding foo}
                              g [f, f'] ({map_unfolds = [], set_unfoldss = [], rel_unfolds = []}, lthy)
  in lthy' end
\<close>

ML \<open>
val test = @{typ "unit + unit + 'a list"}
\<close>

(*local_setup \<open>snd o MRBNF_Comp.mrbnf_of_typ { lives = [("'a", @{sort type})], frees = [], bounds = [], deads = [] } test\<close>

print_mrbnfs*)

end
