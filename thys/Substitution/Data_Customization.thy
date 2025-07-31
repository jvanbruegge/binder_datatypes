(* AtoD: The sorries left for you are some immediate properties of E_pre 
versus G, which I cannot prove since I cannot guess the names of the 
relevant generated lemmas.
*)

(* This theory sets up a high-level recursor from the low-level 
one. This is not just for convenience -- I need it 
in order to refer to G rather than E_pre. *)

theory Data_Customization
  imports Expressions_Sub Expressions_Birecursor "HOL-ex.Sketch_and_Explore"
begin

(*******************************)
(* 1. Pre-datatype assumptions about G: *)

consts Gwit :: "('a1, 'a2, 'c1, 'c2) G"

definition "GMAP = (\<lambda>\<rho>1 \<rho>2 f1 f2 x. Gren \<rho>1 \<rho>2 (Gmap f1 f2 x))"

consts Grel :: "('c1 \<Rightarrow> 'c1' \<Rightarrow> bool) \<Rightarrow> ('c2 \<Rightarrow> 'c2' \<Rightarrow> bool) \<Rightarrow> ('a1, 'a2, 'c1, 'c2) G \<Rightarrow> ('a1, 'a2, 'c1', 'c2') G \<Rightarrow> bool"

setup \<open>Sign.mandatory_path "G"\<close>

axiomatization where
  rel_compp: "\<And>R1 R2 S1 S2. Grel R1 R2 OO Grel S1 S2 \<le> Grel (R1 OO S1) (R2 OO S2)" and
  in_rel: "\<And>f1 f2 R1 R2 x y.
       |supp (f1 :: 'a1 \<Rightarrow> 'a1 :: var)| <o |UNIV :: 'a1 set| \<Longrightarrow>
       bij f2 \<Longrightarrow>
       |supp (f2 :: 'a2 \<Rightarrow> 'a2 :: var)| <o |UNIV :: 'a2 set| \<Longrightarrow>
       Grel R1 R2 (GMAP f1 f2 id id x) y =
       (\<exists>z. (GSupp1 z \<subseteq> {(x, y). R1 x y} \<and> GSupp2 z \<subseteq> {(x, y). R2 x y}) \<and>
            GMAP id id fst fst z = x \<and> GMAP f1 f2 snd snd z = y)" 
  
axiomatization where 
wit1: "GSupp1 Gwit = {}" and
wit2: "GSupp2 Gwit = {}"
lemmas wit = G.wit1 G.wit2
setup \<open>Sign.parent_path\<close>

declare [[mrbnf_internals]]
declare [[typedef_overloaded]]
mrbnf "('a1::var, 'a2::var, 'c1, 'c2) G"
  map: GMAP
  sets: free: GVrs1 bound: GVrs2 live: GSupp1 live: GSupp2
  bd: Gbd
  wits: Gwit
  rel: Grel
  var_class: var
                 apply (auto simp: GMAP_def Gren_def G.Sb_Inj G.Map_id fun_eq_iff G.infinite_regular_card_order G.wit
      G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified] G.Map_comp[THEN fun_cong, simplified]
      G.Vrs_Sb G.Supp_Sb G.Vrs_Map G.Supp_Map G.Vrs_bd G.Supp_bd
      intro: trans[OF G.Sb_cong arg_cong[where f="Gsub _ _", OF G.Map_cong]]) [12]
     apply (rule G.rel_compp)
    apply (rule G.in_rel; assumption)
   apply (simp_all add: G.wit)
  done


(*******************************)
(* 2. The binding-aware dataype command, 
yielding the datatype E and its theorems *)

binder_datatype (EVrs: 'a) E = Ector "('a, x::'a, t::'a E, 'a E) G" binds x in t
  for permute: Eperm
declare E.inject[simp del]

(*for technical reasons we now work with var_E_pre but the classes are the same*)
sublocale var_E_pre < var
  by (rule var_axioms)
sublocale var < var_E_pre
  by standard

instantiation Gbd_type :: var_E_pre begin
instance by standard
end


term Rep_E_pre


find_theorems Ector
term Ector
find_theorems name: REC name: E 
thm Ector_def
find_theorems E_ctor 
term E_ctor

thm REC_E_def[where avoiding_set = "{}" and validU = "\<lambda>x. True", simplified]

thm REC_E_def[no_vars]

context 
fixes Pmap :: "('a::var_E_pre \<Rightarrow> 'a) \<Rightarrow> 'p \<Rightarrow> 'p"
and PFVars :: "'p \<Rightarrow> 'a set"
and validP :: "'p \<Rightarrow> bool"
and avoiding_set :: "'a set"
and Umap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a E \<Rightarrow> 'u \<Rightarrow> 'u"
and UFVars :: "'a E \<Rightarrow> 'u \<Rightarrow> 'a set"
and validU :: "'u \<Rightarrow> bool"
begin 

context fixes 
Uctor_E_pre :: "('a, 'a, 'a E \<times> ('p \<Rightarrow> 'u), 'a E \<times> ('p \<Rightarrow> 'u)) E_pre \<Rightarrow> 'p \<Rightarrow> 'u"
begin 

definition "Pmap_comp \<equiv> \<forall>d f g.
   validP d \<and> bij f \<and> |supp f| <o |UNIV::'a set| \<and>
   bij g \<and> |supp g| <o |UNIV::'a set| 
   \<longrightarrow> 
   Pmap (f \<circ> g) d = (Pmap f \<circ> Pmap g) d"

definition "Pmap_id \<equiv> \<forall>d f. 
 validP d \<and> bij f \<and> |supp f| <o |UNIV::'a set| \<and> 
 (\<forall>a. a \<in> PFVars d \<longrightarrow> f a = a) 
 \<longrightarrow> 
 Pmap f d = d"

definition "PFVars_Pmap \<equiv> \<forall>d f. 
  validP d \<and> bij f \<and> |supp f| <o |UNIV::'a set| 
  \<longrightarrow> 
  PFVars (Pmap f d) = f ` PFVars d"

definition "PFVars_small \<equiv>  \<forall>p. validP p \<longrightarrow> |PFVars p| <o |UNIV::'a set|"

definition "Pmap_validP \<equiv> \<forall>f p. 
 validP p \<and> bij f \<and> |supp f| <o |UNIV::'a set| \<longrightarrow> validP (Pmap f p)"

definition "avset_small \<equiv> |avoiding_set| <o |UNIV::'a set|"

definition "P_axioms \<equiv> Pmap_comp \<and> Pmap_id \<and> PFVars_Pmap \<and> 
  PFVars_small \<and> Pmap_validP \<and> avset_small"

lemmas P_defs = Pmap_comp_def Pmap_id_def PFVars_Pmap_def 
  PFVars_small_def Pmap_validP_def avset_small_def

definition "Umap_comp \<equiv> \<forall>d f g t.
  validU d \<and> bij f \<and> |supp f| <o |UNIV::'a set| \<and>
  bij g \<and> |supp g| <o |UNIV::'a set| 
  \<longrightarrow> 
  Umap (f \<circ> g) t d = (Umap f t \<circ> Umap g t) d"

definition "Umap_cong \<equiv> \<forall>d t f.
  validU d \<and> bij f \<and> |supp f| <o |UNIV::'a set| \<and>  
  (\<forall>a. a \<in> UFVars t d \<longrightarrow> f a = a) \<longrightarrow> 
  Umap f t d = d"

definition "Umap_Ector_E_pre \<equiv> \<forall>f y p.
   validP p \<and>
   pred_E_pre (pred_fun validP validU \<circ> snd) (pred_fun validP validU \<circ> snd) y \<and> 
   bij f \<and> |supp f| <o |UNIV:: 'a set| \<and> 
   imsupp f \<inter> avoiding_set = {} 
   \<longrightarrow>
   Umap f (E_ctor (map_E_pre id id fst fst y)) (Uctor_E_pre y p) =
   Uctor_E_pre (map_E_pre f f
            (\<lambda>(t, pu).
                (Eperm f t,
                 \<lambda>p. if validP p then Umap f t (pu (Pmap (inv f) p)) else undefined))
            (\<lambda>(t, pu).
                (Eperm f t,
                 \<lambda>p. if validP p then Umap f t (pu (Pmap (inv f) p)) else undefined))
            y)
          (Pmap f p)"

definition "UFVars_EFVars_E_pre \<equiv> \<forall>y p. 
  validP p \<and> 
  pred_E_pre (pred_fun validP validU \<circ> snd) (pred_fun validP validU \<circ> snd) y \<and> 
  set2_E_pre y \<inter> (PFVars p \<union> avoiding_set) = {} \<and> 
  (\<forall>t pu p. validP p \<and>
            (t, pu) \<in> set3_E_pre y \<union> set4_E_pre y \<longrightarrow> 
            UFVars t (pu p) \<subseteq> EVrs t \<union> PFVars p \<union> avoiding_set) 
  \<longrightarrow>
  UFVars (E_ctor (map_E_pre id id fst fst y)) (Uctor_E_pre y p)
  \<subseteq> EVrs (E_ctor (map_E_pre id id fst fst y)) \<union> PFVars p \<union> avoiding_set"

definition "validU_Umap \<equiv> \<forall>f t u. 
  validU u \<and> bij f \<and> |supp f| <o |UNIV::'a set| \<longrightarrow> validU (Umap f t u)"

definition "validU_Uctor_E_pre \<equiv> \<forall>y p. 
  validP p \<and> 
  pred_E_pre (pred_fun validP validU \<circ> snd) (pred_fun validP validU \<circ> snd) y 
  \<longrightarrow>
  validU (Uctor_E_pre y p)"

definition "U_axioms_E_pre \<equiv> Umap_comp \<and> Umap_cong \<and> Umap_Ector_E_pre \<and> 
  UFVars_EFVars_E_pre \<and> 
  validU_Umap \<and> validU_Uctor_E_pre"

lemmas U_E_pre_defs = Umap_comp_def Umap_cong_def 
  Umap_Ector_E_pre_def UFVars_EFVars_E_pre_def 
  validU_Umap_def validU_Uctor_E_pre_def

lemma REC_E_def2: 
"REC_E Pmap PFVars validP avoiding_set Umap UFVars Uctor_E_pre validU \<longleftrightarrow> 
 P_axioms \<and> U_axioms_E_pre"
unfolding REC_E_def P_axioms_def U_axioms_E_pre_def P_defs U_E_pre_defs apply clarsimp
apply(rule iffI)
  subgoal apply (intro conjI) 
    subgoal by auto subgoal by auto subgoal by auto subgoal by auto
    subgoal by auto subgoal by auto subgoal by auto subgoal by auto 
    subgoal by auto  subgoal by auto  subgoal by auto subgoal by auto .
  subgoal apply (intro conjI) 
    subgoal by auto subgoal by auto subgoal by auto subgoal by auto
    subgoal by auto subgoal by auto subgoal by auto subgoal by auto 
    subgoal by auto subgoal by meson  subgoal by auto subgoal by auto . .

term "REC_E.REC_E PFVars validP avoiding_set Uctor_E_pre"

end (* inner context that fixed Uctor_E_pre *)

(* *)
(* Shifting from E_pre to G (filling low-to-high level gap 
in the current binder_datatype implementation): *)

definition "Umap_Ector Uctor \<equiv> \<forall>f y p.
   validP p \<and>
   pred_G (pred_fun validP validU \<circ> snd) (pred_fun validP validU \<circ> snd) y \<and> 
   bij f \<and> |supp f| <o |UNIV:: 'a set| \<and> 
   imsupp f \<inter> avoiding_set = {} 
   \<longrightarrow>
   Umap f (Ector (Gmap fst fst y)) (Uctor y p) =
   Uctor (Gren f f (Gmap
            (\<lambda>(t, pu).
                (Eperm f t,
                 \<lambda>p. if validP p then Umap f t (pu (Pmap (inv f) p)) else undefined))
            (\<lambda>(t, pu).
                (Eperm f t,
                 \<lambda>p. if validP p then Umap f t (pu (Pmap (inv f) p)) else undefined))
            y))
          (Pmap f p)"

definition "UFVars_EFVars Uctor \<equiv> \<forall>y p. 
  validP p \<and> 
  pred_G (pred_fun validP validU \<circ> snd) (pred_fun validP validU \<circ> snd) y \<and> 
  GVrs2 y \<inter> (PFVars p \<union> avoiding_set) = {} \<and> 
  (\<forall>t pu p. validP p \<and>
            (t, pu) \<in> GSupp1 y \<union> GSupp2  y \<longrightarrow> 
            UFVars t (pu p) \<subseteq> EVrs t \<union> PFVars p \<union> avoiding_set) 
  \<longrightarrow>
  UFVars (Ector (Gmap fst fst y)) (Uctor y p)
  \<subseteq> EVrs (Ector (Gmap fst fst y)) \<union> PFVars p \<union> avoiding_set"


definition "validU_Uctor Uctor \<equiv> \<forall>y p. 
  validP p \<and> 
  pred_G (pred_fun validP validU \<circ> snd) (pred_fun validP validU \<circ> snd) y 
  \<longrightarrow>
  validU (Uctor y p)"

definition "U_axioms Uctor \<equiv> Umap_comp \<and> Umap_cong \<and> Umap_Ector Uctor \<and> 
  UFVars_EFVars Uctor \<and> 
  validU_Umap \<and> validU_Uctor Uctor"

lemmas U_defs = Umap_comp_def Umap_cong_def 
  Umap_Ector_E_pre_def UFVars_EFVars_E_pre_def 
  validU_Umap_def validU_Uctor_def

end (* outer context fixing all the parameters *)

term Abs_E_pre

thm Abs_E_pre_inverse

context REC_E begin

thm REC_ctor[no_vars]
thm REC_ctor[no_vars]
thm REC_UFVars[no_vars]
thm REC_swap[no_vars]
thm REC_valid[no_vars]
end 

(* definition 
"rec_E Uctor \<equiv> P_axioms \<and> U_axioms Uctor" *)

term "P_axioms Pmap PFVars validP avoiding_set"
term "U_axioms Umap UFVars validU Uctor"

(* rec_E is the proper "high-level" locale for 
binder-aware recursion: *)
locale rec_E = 
  fixes Pmap :: "('a::var_E_pre \<Rightarrow> 'a) \<Rightarrow> 'p \<Rightarrow> 'p"
    and PFVars :: "'p \<Rightarrow> 'a set"
    and validP :: "'p \<Rightarrow> bool"
    and avoiding_set :: "'a set"
    and Umap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a E \<Rightarrow> 'u \<Rightarrow> 'u"
    and UFVars :: "'a E \<Rightarrow> 'u \<Rightarrow> 'a set"
    and Uctor :: "('a, 'a, 'a E \<times> ('p \<Rightarrow> 'u), 'a E \<times> ('p \<Rightarrow> 'u)) G \<Rightarrow> 'p \<Rightarrow> 'u"
    and validU :: "'u \<Rightarrow> bool"
  assumes P: "P_axioms Pmap PFVars validP avoiding_set"
  and U: "U_axioms Pmap PFVars validP avoiding_set Umap UFVars validU Uctor"
begin 

definition "Uctor' \<equiv> Uctor o Rep_E_pre"

lemma Abs_Rep_E_pre[simp]: "Abs_E_pre o Rep_E_pre = id"
sorry
lemma Abs_Rep_E_pre'[simp]: "Abs_E_pre (Rep_E_pre u) = u"
sorry
lemma Rep_Ahs_E_pre[simp]: "Rep_E_pre o Abs_E_pre = id"
sorry
lemma Rep_Abs_E_pre'[simp]: "Rep_E_pre (Abs_E_pre u) = u"
sorry

lemma pred_G_pred_E_pre: "pred_G P1 P2 = pred_E_pre P1 P2 o Abs_E_pre"
sorry 

lemma pred_E_pre_pred_G: "pred_E_pre P1 P2 = pred_G P1 P2 o Rep_E_pre"
sorry

lemma Gmap_map_E_pre: "Gmap f1 f2 = Rep_E_pre o map_E_pre id id f1 f2 o Abs_E_pre"
sorry 

lemma map_E_pre_Gmap: "bij \<sigma>1 \<and> |supp \<sigma>1| <o |UNIV::'a set| \<Longrightarrow> 
bij \<sigma>2 \<and> |supp \<sigma>2| <o |UNIV::'a set| \<Longrightarrow>  map_E_pre \<sigma>1 \<sigma>2 f1 f2 = 
Abs_E_pre o Gren \<sigma>1 \<sigma>2 o Gmap f1 f2 o Rep_E_pre"
sorry


lemma [simp]: "bij \<sigma>1 \<and> |supp \<sigma>1| <o |UNIV::'a set| \<Longrightarrow> 
bij \<sigma>2 \<and> |supp \<sigma>2| <o |UNIV::'a set| \<Longrightarrow> 
Rep_E_pre (map_E_pre \<sigma>1 \<sigma>2 f1 f2 u) = Gren \<sigma>1 \<sigma>2 (Gmap f1 f2 (Rep_E_pre u))"
sorry

lemma Rep_E_pre_surj: "\<exists>y. x = Rep_E_pre y"
sorry

thm Ector_def

lemma Ector_Ector[simp]: "E_ctor = Ector o Rep_E_pre"
sorry

lemma Gren_id[simp]: "Gren id id = id"
sorry

lemma [simp]: "set1_E_pre y = GVrs1 (Rep_E_pre y)"
sorry
lemma [simp]: "set2_E_pre y = GVrs2 (Rep_E_pre y)"
sorry
lemma [simp]: "set3_E_pre y = GSupp1 (Rep_E_pre y)"
sorry
lemma [simp]: "set4_E_pre y = GSupp2 (Rep_E_pre y)"
sorry

lemma U_axioms_E_pre_Uctor': 
"U_axioms_E_pre Pmap PFVars validP avoiding_set Umap UFVars validU Uctor'"
unfolding U_axioms_E_pre_def apply(intro conjI)
  subgoal using U unfolding U_axioms_def by simp
  subgoal using U unfolding U_axioms_def by simp
  subgoal unfolding Umap_Ector_E_pre_def Uctor'_def
  using U unfolding U_axioms_def Umap_Ector_def 
  using Rep_E_pre_surj by (auto simp:  pred_E_pre_pred_G)  
  subgoal unfolding UFVars_EFVars_E_pre_def Uctor'_def
  using U unfolding U_axioms_def UFVars_EFVars_def 
  using Rep_E_pre_surj by (simp add: pred_E_pre_pred_G) 
  subgoal using U unfolding U_axioms_def by simp
  subgoal unfolding validU_Uctor_E_pre_def Uctor'_def
  using U unfolding U_axioms_def validU_Uctor_def 
  using Rep_E_pre_surj by (auto simp:  pred_E_pre_pred_G) . 

lemma REC_E: "REC_E Pmap PFVars validP avoiding_set Umap UFVars Uctor' validU" 
unfolding REC_E_def2 apply(rule conjI)
  subgoal using P .
  subgoal using U_axioms_E_pre_Uctor' . .

sublocale REC_E Pmap PFVars validP avoiding_set Umap UFVars Uctor' validU 
using REC_E .

lemma noclash_E_noclashE[simp]: "noclash_E (Abs_E_pre x) = noclashE x"
sorry

(* I also get rid of the awkward lambda-embedded test for validP 
in the recursor's characteristic equation *)
definition "recE \<equiv> \<lambda>t p. if validP p then REC_E t p else undefined"


thm REC_ctor[no_vars]
theorem rec_ctor: 
"validP p \<Longrightarrow> GVrs2 x \<inter> (PFVars p \<union> avoiding_set) = {} \<Longrightarrow>
 noclashE x \<Longrightarrow> 
 recE (Ector x) p =
 Uctor (Gmap (\<lambda>t. (t, recE t))
             (\<lambda>t. (t, recE t)) x) p"
unfolding recE_def Ector_def
apply(subst REC_ctor) 
apply (auto simp: Uctor'_def)+
using noclash_E_noclashE by blast

thm REC_UFVars[no_vars]
theorem recE_UFVars: 
"validP p \<Longrightarrow> UFVars e (recE e p) \<subseteq> EVrs e \<union> PFVars p \<union> avoiding_set"
unfolding recE_def using REC_UFVars by auto

thm REC_swap[no_vars]
theorem recE_Eperm:
"validP p \<Longrightarrow> bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV::'a set| \<Longrightarrow>
 imsupp \<sigma> \<inter> avoiding_set = {} \<Longrightarrow>
 recE (Eperm \<sigma> e) p = Umap \<sigma> e (recE e (Pmap (inv \<sigma>) p))"
unfolding recE_def using REC_swap apply simp
by (metis P P_axioms_def Pmap_validP_def bij_imp_bij_inv supp_inv_bound)

thm REC_valid[no_vars]
theorem recE_valid: 
"pred_fun validP validU (recE (Ector x))"
unfolding recE_def Ector_def using REC_valid pred_fun_def  
by simp (metis Rep_Abs_E_pre')

end (* context rec_E *)

end