theory MRBNF_Examples
  imports "../thys/MRBNF_Composition"
begin

datatype (setF1_F: 'a, setF2_F: 'a', setL3_F: 'x, setB4_F: 'b, setB5_F: 'b', setL6_F: 'c, setL7_F: 'd, setL8_F: 'e, setL9_F: 'f) F =
  E "'x + 'a + ('a' * 'b') * 'c * 'd + 'a' * 'f"
  for map: map_F rel: rel_F

datatype (setF1_F': 'a, setF2_F': 'a', setL3_F': 'x, setB4_F': 'b, setL5_F': 'c, setL6_F': 'd) F' =
  E "'x + 'a + ('a' * 'b) * 'c * 'd + 'a"
  for map: map_F' rel: rel_F'

datatype (setF1_G: 'a, setF2_G: 'a', setL3_G: 'y, setB4_G: 'b, setB5_G: 'b', setL6_G: 'g) G =
  E "'y + 'a + ('a' * 'b') * 'y * 'g + 'a' * 'g"
  for map: map_G rel: rel_G

declare [[quick_and_dirty=true]]
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
  wits: "F.E o Inl"
  rel: "\<lambda>X. rel_F (=) (=) X (=) (=)"
  pred: "\<lambda>X. pred_F (\<lambda>_. True) (\<lambda>_. True) X (\<lambda>_. True) (\<lambda>_. True)"
  sorry
print_theorems

mrbnf F': "('a, 'a', 'x, 'b, 'c, 'd) F'"
  map: "map_F'"
  sets:
   bound: "setF1_F' :: _ \<Rightarrow> 'a set"
   bound: "setF2_F' :: _ \<Rightarrow> 'a' set"
   live: "setL3_F' :: _ \<Rightarrow> 'x set"
   free: "setB4_F' :: _ \<Rightarrow> 'b set"
   live: "setL5_F' :: _ \<Rightarrow> 'c set"
   live: "setL6_F' :: _ \<Rightarrow> 'd set"
  bd: "card_suc natLeq"
  wits: "F'.E o Inl"
  rel: "\<lambda>X. rel_F' (=) (=) X (=)"
  pred: "\<lambda>X. pred_F' (\<lambda>_. True) (\<lambda>_. True) X (\<lambda>_. True)"
  sorry

mrbnf G: "('a, 'a', 'y, 'b, 'b', 'g) G"
  map: "map_G"
  sets:
    free: "setF1_G :: _ \<Rightarrow> 'a set"
    free: "setF2_G :: _ \<Rightarrow> 'a' set"
    live: "setL3_G :: _ \<Rightarrow> 'y set"
    bound: "setB4_G :: _ \<Rightarrow> 'b set"
    bound: "setB5_G :: _ \<Rightarrow> 'b' set"
    live: "setL6_G :: _ \<Rightarrow> 'g set"
  bd: "natLeq"
  wits: "G.E o Inl"
  rel: "\<lambda>X. rel_G (=) (=) X (=) (=)"
  pred: "\<lambda>X. pred_G (\<lambda>_. True) (\<lambda>_. True) X (\<lambda>_. True) (\<lambda>_. True)"
  sorry
declare [[quick_and_dirty=false]]

ML \<open>
val f = the (MRBNF_Def.mrbnf_of @{context} "MRBNF_Examples.F")
val f' = the (MRBNF_Def.mrbnf_of @{context} "MRBNF_Examples.F'")
val g = the (MRBNF_Def.mrbnf_of @{context} "MRBNF_Examples.G")
\<close>

declare [[ML_print_depth=100000]]
local_setup \<open>fn lthy =>
  let
    val Xs = map dest_TFree [@{typ 'x}]
    val Ts = [@{typ 'a}, @{typ 'b}, @{typ 'c}, @{typ 'd}, @{typ 'e}, @{typ 'f}, @{typ 'g}, @{typ 'h}, @{typ 'i}]
    val resBs = map dest_TFree (Ts @ [@{typ 'j}])
    fun flatten_tyargs Ass =
      subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val ((mrbnf, tys), (accum, lthy')) = MRBNF_Comp.mrbnf_of_typ false MRBNF_Def.Smart_Inline I flatten_tyargs Xs [] []
    @{typ "('j, 'c,
            ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) F,
            'e, 'd,
            ('a, 'b, 'c, 'x, 'e, 'i) G,
            ('d, 'e, 'c, 'f, 'g, 'i) F',
            ('a, 'b, 'c, 'x, 'e, 'i) G,
            ('d, 'e, 'c, 'f, 'g, 'i) F'
          ) F
            "}
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)
  val b = MRBNF_Comp.seal_mrbnf I (snd accum) @{binding foo} false
    [] (fst tys) mrbnf lthy'
  val _ = @{print} b
  in snd b
  end\<close>

term "True"

term "\<Union> (setL3_G (map_G id id setF1_F' id id setF1_F' x))"
term "\<Union> (image setF1_F' (setL3_G x)) \<union> \<Union> (image setF1_F' (setL6_G x))"

end
