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
   free: "setF1_F :: _ ⇒ 'a set"
   free: "setF2_F :: _ ⇒ 'a' set"
   live: "setL3_F :: _ ⇒ 'x set"
   bound: "setB4_F :: _ ⇒ 'b set"
   bound: "setB5_F :: _ ⇒ 'b' set"
   live: "setL6_F :: _ ⇒ 'c set"
   live: "setL7_F :: _ ⇒ 'd set"
   live: "setL8_F :: _ ⇒ 'e set"
   live: "setL9_F :: _ ⇒ 'f set"
  bd: "natLeq"
  wits: "F.E o Inl"
  rel: "λX. rel_F (=) (=) X (=) (=)"
  pred: "λX. pred_F (λ_. True) (λ_. True) X (λ_. True) (λ_. True)"
  sorry
print_theorems

mrbnf F': "('a, 'a', 'x, 'b, 'c, 'd) F'"
  map: "map_F'"
  sets:
   bound: "setF1_F' :: _ ⇒ 'a set"
   bound: "setF2_F' :: _ ⇒ 'a' set"
   live: "setL3_F' :: _ ⇒ 'x set"
   free: "setB4_F' :: _ ⇒ 'b set"
   live: "setL5_F' :: _ ⇒ 'c set"
   live: "setL6_F' :: _ ⇒ 'd set"
  bd: "card_suc natLeq"
  wits: "F'.E o Inl"
  rel: "λX. rel_F' (=) (=) X (=)"
  pred: "λX. pred_F' (λ_. True) (λ_. True) X (λ_. True)"
  sorry

mrbnf G: "('a, 'a', 'y, 'b, 'b', 'g) G"
  map: "map_G"
  sets:
    free: "setF1_G :: _ ⇒ 'a set"
    free: "setF2_G :: _ ⇒ 'a' set"
    live: "setL3_G :: _ ⇒ 'y set"
    bound: "setB4_G :: _ ⇒ 'b set"
    bound: "setB5_G :: _ ⇒ 'b' set"
    live: "setL6_G :: _ ⇒ 'g set"
  bd: "natLeq"
  wits: "G.E o Inl"
  rel: "λX. rel_G (=) (=) X (=) (=)"
  pred: "λX. pred_G (λ_. True) (λ_. True) X (λ_. True) (λ_. True)"
  sorry
declare [[quick_and_dirty=false]]

ML ‹
val f = the (MRBNF_Def.mrbnf_of @{context} "Composition.F")
val f' = the (MRBNF_Def.mrbnf_of @{context} "Composition.F'")
val g = the (MRBNF_Def.mrbnf_of @{context} "Composition.G")
›

declare [[ML_print_depth=100000]]
local_setup ‹fn lthy =>
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
  end›

end
