theory Data
  imports Expression_Like_Sub Expression_Like_Birecursor "HOL-ex.Sketch_and_Explore"
begin

consts Gwit :: "('a1, 'a2, 'x1, 'x2) G"

definition "GMAP = (\<lambda>\<rho>1 \<rho>2 f1 f2 x. Gren \<rho>1 \<rho>2 (Gmap f1 f2 x))"

consts Grel :: "('x1 \<Rightarrow> 'x1' \<Rightarrow> bool) \<Rightarrow> ('x2 \<Rightarrow> 'x2' \<Rightarrow> bool) \<Rightarrow> ('a1, 'a2, 'x1, 'x2) G \<Rightarrow> ('a1, 'a2, 'x1', 'x2') G \<Rightarrow> bool"

setup \<open>Sign.mandatory_path "G"\<close>

axiomatization where
  rel_compp: "\<And>R1 R2 S1 S2. Grel R1 R2 OO Grel S1 S2 \<le> Grel (R1 OO S1) (R2 OO S2)" and
  in_rel: "\<And>f1 f2 R1 R2 x y.
       |supp (f1 :: 'a1 \<Rightarrow> 'a1 :: var)| <o |UNIV :: 'a1 set| \<Longrightarrow>
       bij f2 \<Longrightarrow>
       |supp (f2 :: 'a2 \<Rightarrow> 'a2 :: var)| <o |UNIV :: 'a2 set| \<Longrightarrow>
       Grel R1 R2 (GMAP f1 f2 id id x) y =
       (\<exists>z. (GSupp1 z \<subseteq> {(x, y). R1 x y} \<and> GSupp2 z \<subseteq> {(x, y). R2 x y}) \<and>
            GMAP id id fst fst z = x \<and> GMAP f1 f2 snd snd z = y)" and
  wit1: "GSupp1 Gwit = {}" and
  wit2: "GSupp2 Gwit = {}"
lemmas wit = G.wit1 G.wit2
setup \<open>Sign.parent_path\<close>

declare [[mrbnf_internals]]
declare [[typedef_overloaded]]
mrbnf "('a1::var, 'a2::var, 'x1, 'x2) G"
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

inductive subshape where
  "e \<in> GSupp1 u \<union> GSupp2 u \<Longrightarrow> subshape e (Ector u)"

lemma wfp_subshape: "wfp (subshape)"
  apply (rule wfpUNIVI)
  subgoal premises prems for P e
    apply (subgoal_tac "\<And>\<sigma> :: 'a \<Rightarrow> 'a. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> P (Eperm \<sigma> e)")
     apply (drule meta_spec[of _ id])
     apply (simp add: E.permute_id)
    apply (induct e)
    subgoal for u \<sigma>
      apply (rule prems[rule_format])
      apply (auto elim!: subshape.cases simp: G.set_map E.permute_comp  E.inject supp_comp_bound)
      done
    done
  done

lemma subshape_induct: "(\<And>e. (\<And>e'. subshape e' e \<Longrightarrow> P e') \<Longrightarrow> P e) \<Longrightarrow> P e"
  using wfp_subshape
  by (metis wfp_induct)

lemma E_coinduct_gen:
  fixes P and g :: "'k \<Rightarrow> 'a::var_E_pre E" and h e
  assumes "(\<And>k. P k \<Longrightarrow> g k = h k \<or>
    (\<exists>u. g k = Ector (GMAP id id g g u) \<and> h k = Ector (GMAP id id h h u) \<and>
    (\<forall>k \<in> GSupp1 u. P k) \<and> (\<forall>k \<in> GSupp2 u. P k)))"
  shows "P k \<Longrightarrow> g k = h k"
  apply (subgoal_tac "\<And>e. g k = e \<Longrightarrow> e = h k")
   apply blast
  subgoal for e
    apply (induct e arbitrary: k rule: subshape_induct)
    apply (drule assms)
    apply (erule disjE)
     apply simp
    apply (erule exE conjE)+
    apply (auto simp: G.map_comp G.set_map E.permute_id0  E.inject intro!: exI[of _ id] G.map_cong)
     apply (drule meta_spec2, drule meta_mp)
      apply (rule subshape.intros)
      apply (auto simp: E.permute_id0 G.set_map) []
     apply (drule meta_mp)
      apply (erule bspec)
      apply assumption
     apply simp
    apply (drule meta_spec2, drule meta_mp)
     apply (rule subshape.intros)
     apply (auto simp: E.permute_id0 G.set_map) []
    apply (drule meta_mp)
     apply (erule (1) bspec)
    apply simp
    done
  done

interpretation Expression_Strong Eperm EVrs Gbd Ector
  apply unfold_locales
  apply (auto simp: E.inject E.permute_id0 E.permute_comp E.FVars_permute GMAP_def Gren_def E.FVars_bd large'
    G.bd_card_order G.bd_cinfinite G.bd_regularCard intro: E.permute_cong_id)
  subgoal for A e
    apply (binder_induction e avoiding: A rule: E.strong_induct)
     apply assumption
    apply (rule exI conjI)+
     apply assumption
    apply (rule refl)
    done
  subgoal for P g h e
    apply (rule E_coinduct_gen[of P g h e]; simp add: GMAP_def Gren_def G.Sb_Inj)
    done
  done
(*
lemma permute_\<rho>:
  "bij f \<Longrightarrow> |supp (f :: 'a :: var_E_pre \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow> imsupp f \<inter> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> = {} \<Longrightarrow> Eperm f (\<rho> a) = \<rho> (f a)"
  apply (cases "f a = a")
   apply (cases "\<rho> a = Ector (\<eta> a)")
    apply (simp add: GMAP_def Gren_def eta_natural)
   apply simp
   apply (rule E.permute_cong_id; simp?)
  subgoal for a'
    apply (subgoal_tac "a' \<in> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho>")
     apply (meson Int_emptyD not_in_imsupp_same)
    apply (auto simp: IImsupp'_def IImsupp_def SSupp_def)
    done
  apply (cases "\<rho> a = Ector (\<eta> a)")
   apply (simp add: GMAP_def Gren_def eta_natural)
   apply (auto simp: IImsupp'_def IImsupp_def SSupp_def imsupp_def supp_def)
  done

lemma permute_\<rho>':
  "bij f \<Longrightarrow> |supp (f :: 'a :: var_E_pre \<Rightarrow> 'a)| <o |UNIV :: 'a set| \<Longrightarrow> imsupp f \<inter> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>' = {} \<Longrightarrow> Eperm f (\<rho>' a) = \<rho>' (f a)"
  apply (cases "f a = a")
   apply (cases "\<rho>' a = Ector (\<eta>' a)")
    apply (simp add: GMAP_def Gren_def eta'_natural)
   apply simp
   apply (rule E.permute_cong_id; simp?)
  subgoal for a'
    apply (subgoal_tac "a' \<in> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>'")
     apply (meson Int_emptyD not_in_imsupp_same)
    apply (auto simp: IImsupp'_def IImsupp_def SSupp_def)
    done
  apply (cases "\<rho>' a = Ector (\<eta>' a)")
   apply (simp add: GMAP_def Gren_def eta'_natural)
   apply (auto simp: IImsupp'_def IImsupp_def SSupp_def imsupp_def supp_def)
  done
*)


(*****)

(* thm Birecursor_def Birecursor_axioms_def

context Birecursor  
begin 
*)

term Rep_E_pre
term Abs_E_pre

thm Abs_E_pre_inverse

find_theorems Ector
term Ector
find_theorems name: REC name: E 
thm Ector_def
find_theorems E_ctor 
term E_ctor

thm REC_E_def[where avoiding_set = "{}" and validU = "\<lambda>x. True", simplified]

thm REC_E_def[no_vars]
thm REC_E.REC_ctor[no_vars]
thm REC_E.REC_ctor[no_vars]
thm REC_E.REC_UFVars[no_vars]
thm REC_E.REC_swap[no_vars]
thm REC_E.REC_valid[no_vars]

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

end (* inner context that fixed Uctor_E_pre *)

(* *)
(* Shifting from E_pre to G : *)


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

definition 
"rec_E Uctor \<equiv> P_axioms \<and> U_axioms Uctor"

definition 
"REC_E Pmap PFVars validP avoiding_set Umap UFVars Uctor validU \<longleftrightarrow> 
 P_axioms \<and> U_axioms_E_pre"



term 
fixes "(('b \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'c)
     \<Rightarrow> ('c \<Rightarrow> 'b set)
        \<Rightarrow> ('c \<Rightarrow> bool)
           \<Rightarrow> 'b set
              \<Rightarrow> (('b \<Rightarrow> 'b) \<Rightarrow> 'b E \<Rightarrow> 'd \<Rightarrow> 'd)
                 \<Rightarrow> ('b E \<Rightarrow> 'd \<Rightarrow> 'b set)
                    \<Rightarrow> (('b, 'b, 'b E \<times> ('c \<Rightarrow> 'd), 'b E \<times> ('c \<Rightarrow> 'd)) E_pre
                        \<Rightarrow> 'c \<Rightarrow> 'd)
                       \<Rightarrow> ('d \<Rightarrow> bool) \<Rightarrow> bool"
begin

definition "REC_EG Pmap PFVars validP avoiding_set Umap UFVars Uctor validU \<equiv>
(((\<forall>d f g.
      validP d \<longrightarrow>
      bij f \<longrightarrow>
      |supp f| <o |UNIV| \<longrightarrow>
      bij g \<longrightarrow> |supp g| <o |UNIV| \<longrightarrow> Pmap (f \<circ> g) d = (Pmap f \<circ> Pmap g) d) \<and>
  (\<forall>d f. validP d \<longrightarrow>
         bij f \<longrightarrow>
         |supp f| <o |UNIV| \<longrightarrow> (\<forall>a. a \<in> PFVars d \<longrightarrow> f a = a) \<longrightarrow> Pmap f d = d) \<and>
  (\<forall>d f. validP d \<longrightarrow>
         bij f \<longrightarrow> |supp f| <o |UNIV| \<longrightarrow> PFVars (Pmap f d) = f ` PFVars d)) \<and>
 (\<forall>p. validP p \<longrightarrow> |PFVars p| <o |UNIV| ) \<and>
 (\<forall>f p. validP p \<longrightarrow> bij f \<longrightarrow> |supp f| <o |UNIV| \<longrightarrow> validP (Pmap f p)) \<and>
 |avoiding_set| <o |UNIV| ) \<and>
((\<forall>d f g t.
     validU d \<longrightarrow>
     bij f \<longrightarrow>
     |supp f| <o |UNIV| \<longrightarrow>
     bij g \<longrightarrow> |supp g| <o |UNIV| \<longrightarrow> Umap (f \<circ> g) t d = (Umap f t \<circ> Umap g t) d) \<and>
 (\<forall>d t f.
     validU d \<longrightarrow>
     bij f \<longrightarrow>
     |supp f| <o |UNIV| \<longrightarrow> (\<forall>a. a \<in> UFVars t d \<longrightarrow> f a = a) \<longrightarrow> Umap f t d = d) \<and>
 (\<forall>f y p.
     validP p \<longrightarrow>
     pred_E_pre (pred_fun validP validU \<circ> snd) (pred_fun validP validU \<circ> snd) y \<longrightarrow>
     bij f \<longrightarrow>
     |supp f| <o |UNIV| \<longrightarrow>
     imsupp f \<inter> avoiding_set = {} \<longrightarrow>
     Umap f (E_ctor (map_E_pre id id fst fst y)) (Uctor y p) =
     Uctor
      (map_E_pre f f
        (\<lambda>(t, pu).
            (Eperm f t,
             \<lambda>p. if validP p then Umap f t (pu (Pmap (inv f) p)) else undefined))
        (\<lambda>(t, pu).
            (Eperm f t,
             \<lambda>p. if validP p then Umap f t (pu (Pmap (inv f) p)) else undefined))
        y)
      (Pmap f p))) \<and>
(\<forall>y p. validP p \<longrightarrow>
       pred_E_pre (pred_fun validP validU \<circ> snd) (pred_fun validP validU \<circ> snd) y \<longrightarrow>
       set2_E_pre y \<inter> (PFVars p \<union> avoiding_set) = {} \<longrightarrow>
       (\<forall>t pu p.
           validP p \<longrightarrow>
           (t, pu) \<in> set3_E_pre y \<union> set4_E_pre y \<longrightarrow>
           UFVars t (pu p) \<subseteq> EVrs t \<union> PFVars p \<union> avoiding_set) \<longrightarrow>
       UFVars (E_ctor (map_E_pre id id fst fst y)) (Uctor y p)
       \<subseteq> EVrs (E_ctor (map_E_pre id id fst fst y)) \<union> PFVars p \<union> avoiding_set) \<and>
(\<forall>f t u. validU u \<longrightarrow> bij f \<longrightarrow> |supp f| <o |UNIV| \<longrightarrow> validU (Umap f t u)) \<and>
(\<forall>y p. validP p \<longrightarrow>
       pred_E_pre (pred_fun validP validU \<circ> snd) (pred_fun validP validU \<circ> snd) y \<longrightarrow>
       validU (Uctor y p))"



term Gmap

lemma 
assumes "Bimodel Pvalid Pperm PVrs Eperm EVrs Gbd Ector Ector'"
shows "REC_E Pperm PVrs Pvalid {} (\<lambda>\<sigma> e' e. Eperm \<sigma> e) (\<lambda>e' e. EVrs e) Uctor (\<lambda>x. True)"
proof-
  term "(Ector',Uctor)"

interpretation Birecursor Eperm EVrs Gbd Ector
proof (standard, safe)
  fix Pvalid :: "'p \<Rightarrow> bool"
  and Pperm :: "('a \<Rightarrow> 'a) \<Rightarrow> 'p \<Rightarrow> 'p"
  and PVrs :: "'p \<Rightarrow> 'a set"
  and Ector' :: "('a, 'a, 'p \<Rightarrow> 'a E, 'p \<Rightarrow> 'a E) G \<Rightarrow> 'p \<Rightarrow> 'a E"

typ "('g, 'h, 'c, 'e) E_pre"
term "Ector :: ('c::var_E_pre, 'c, 'c E, 'c E) G \<Rightarrow> 'c E"
term Gmap




find_theorems name: E_pre 
  assume "Bimodel Pvalid Pperm PVrs Eperm EVrs Gbd Ector Ector'"
  interpret rec: REC_E find_theorems Ector term Uctor apply standard 


term term where Pmap = Pperm 
  and PFVars = PVrs and validP = Pvalid 
  and avoiding_set = "{}" 
  and Umap = "\<lambda>\<sigma> e'. Eperm \<sigma>"
  and UFVars = "\<lambda>e e'. EVrs e" term Gmap
  (* and Uctor = "\<lambda>uu'. Ector' (Gmap h h uu')" *)
  term rec.REC_E
  show "\<exists>rec. (\<forall>u p. Pvalid p \<longrightarrow> GVrs2 u \<inter> PVrs p = {} \<longrightarrow> rec (Ector u) p = Ector' (Gmap rec rec u) p) \<and> (\<forall>e p \<sigma>. bij \<sigma> \<longrightarrow> |supp \<sigma>| <o |UNIV| \<longrightarrow> Pvalid p \<longrightarrow> rec (Eperm \<sigma> e) p = Eperm \<sigma> (rec e (Pperm (inv \<sigma>) p))) \<and> (\<forall>e p. Pvalid p \<longrightarrow> EVrs (rec e p) \<subseteq> PVrs p \<union> EVrs e)"
    sorry
qed

interpretation birec_data: Birecursor_Sub_Strong Eperm EVrs Gbd Ector
  by standard

print_statement birec_data.Esub_Strong.E_pbmv_axioms

context
  fixes \<delta> :: "'a \<Rightarrow> 'a :: var_E_pre" and \<rho> \<rho>' :: "'a ::var_E_pre \<Rightarrow> 'a E"
  assumes small_support:
    "|supp (\<delta> :: 'a \<Rightarrow> 'a :: var_E_pre)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>) (\<rho>::'a::var_E_pre \<Rightarrow> 'a E)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>') (\<rho>'::'a::var_E_pre \<Rightarrow> 'a E)| <o |UNIV::'a set|"
begin

interpretation Esub: QREC_fixed_E "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EVrs \<rho> \<union> IImsupp' (Ector o \<eta>') EVrs \<rho>'"
  "\<lambda>u. if \<exists>a. Rep_E_pre u = \<eta> a then \<rho> (SOME a. Rep_E_pre u = \<eta> a) else
       if \<exists>a. Rep_E_pre u = \<eta>' a then \<rho>' (SOME a. Rep_E_pre u = \<eta>' a) else
       Ector (GMAP \<delta> id snd snd (Rep_E_pre u))"
  apply standard
    apply (auto intro!: Un_bound simp: E.FVars_bd_UNIVs imsupp_supp_bound small_support) []
   apply (auto simp: map_E_pre_def set2_E_pre_def set3_E_pre_def set4_E_pre_def
      permute_\<rho> permute_\<rho>'
      Abs_E_pre_inverse GMAP_def Gren_def eta_natural eta'_natural small_support imsupp_commute[of _ \<delta>]
      G.Map_Sb[THEN fun_cong, simplified]
      G.Sb_comp[THEN fun_cong, simplified]
      G.Map_comp[THEN fun_cong, simplified] G.Supp_Map G.Supp_Sb G.Vrs_Map G.Vrs_Sb
      Int_Un_distrib eta_distinct eta_distinct' eta_inject eta'_inject Ector_def[symmetric]
      dest: eta_inversion[rotated -1] eta'_inversion[rotated -1])
        apply (force simp: IImsupp'_def IImsupp_def SSupp_def imsupp_def supp_def image_iff)
       apply (force simp: IImsupp'_def IImsupp_def SSupp_def imsupp_def supp_def image_iff)
      apply (metis Un_iff image_eqI imsupp_def not_in_supp_alt)
     apply (metis Un_iff image_eqI imsupp_def not_in_supp_alt)
    apply (smt (verit, best) Un_iff fst_conv in_mono)
   apply (smt (verit, best) Un_iff fst_conv in_mono)
  apply (smt (verit, best) Un_iff fst_conv in_mono)
  done

definition "Esub = Esub.REC_E"

lemma
  Esub_Ector\<eta>: "Esub (Ector (\<eta> a)) = \<rho> a"
  and Esub_Ector\<eta>': "Esub (Ector (\<eta>' a)) = \<rho>' a"
  and Esub_Ector:
  "GVrs2 u \<inter> imsupp \<delta> = {} \<Longrightarrow>
   GVrs2 u \<inter> IImsupp' (Ector o \<eta>) EVrs \<rho> = {} \<Longrightarrow>
   GVrs2 u \<inter> IImsupp' (Ector o \<eta>') EVrs \<rho>' = {} \<Longrightarrow>
   GVrs2 u \<inter> EVrs (Ector u) = {} \<Longrightarrow>
  \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
  Esub (Ector u) = Ector (Gsub \<delta> id (Gmap Esub Esub u))"
    apply -
  unfolding Esub_def
  subgoal
    apply (subst (2) Ector_def)
    apply (subst Esub.REC_ctor)
      apply (auto simp: map_E_pre_def set2_E_pre_def Abs_E_pre_inverse noclash_E_def
        eta_distinct GMAP_def Gren_def eta_natural eta_inject)
    done
  subgoal
    apply (subst (2) Ector_def)
    apply (subst Esub.REC_ctor)
      apply (auto simp: map_E_pre_def set2_E_pre_def Abs_E_pre_inverse noclash_E_def
        eta_distinct' GMAP_def Gren_def eta'_natural eta'_inject)
    done
  subgoal
    apply (subst (2) Ector_def)
    apply (subst Esub.REC_ctor)
      apply (auto simp: map_E_pre_def set1_E_pre_def set2_E_pre_def set3_E_pre_def set4_E_pre_def
        GMAP_def Gren_def eta_distinct Abs_E_pre_inverse noclash_E_def small_support comp_def[of snd]
        G.Map_Sb[THEN fun_cong, simplified]
        G.Sb_comp[THEN fun_cong, simplified]
        G.Map_comp[THEN fun_cong, simplified]
        dest: eta_inversion[rotated -1] eta'_inversion[rotated -1])
    done
  done

lemma EVrs_Esub: "EVrs (Esub e)
    \<subseteq> EVrs e \<union> (imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>')"
  unfolding Esub_def
  by (rule Esub.REC_FVars)

lemma Eperm_Esub: "bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
  imsupp f \<inter> (imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>') = {} \<Longrightarrow>
  Eperm f (Esub t) = Esub (Eperm f t)"
  unfolding Esub_def
  by (rule Esub.REC_swap)

end

interpretation data: Substitution_Strong Eperm EVrs Gbd Ector Esub
  by standard (auto simp: Esub_Ector\<eta> Esub_Ector\<eta>' Esub_Ector EVrs_Esub Eperm_Esub)

print_statement data.E_pbmv_axioms

end