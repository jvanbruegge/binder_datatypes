theory Bimodels_are_Comodels
  imports Bimodels Comodels
begin

context Bimodel 
begin 

(* Corecursion principle by associating a comodel to a bimodel: *)


fun Edtor1' :: "P\<times>E' \<Rightarrow> ((P\<times>E',P\<times>E')G) set" where 
"Edtor1' (p,e) =
\<Union> { {u1 . Ector (Gmap snd snd u1) = Ector1' u p \<and> 
          GSupp1 (Gmap fst fst u1) \<union>  GSupp2 (Gmap fst fst u1) \<subseteq> {p} \<and> 
          GVrs2 u1 \<inter> PVrs p = {}} | 
       u . \<not> \<phi> u \<and> Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u) = e \<and> GVrs2 u \<inter> PVrs p = {}}"
declare Edtor1'.simps[simp del]
lemmas Edtor1'_def = Edtor1'.simps

lemma in_Edtor1'_Ector_aux: 
assumes "\<not> \<phi> u" "GVrs2 u \<inter> PVrs p = {}" 
shows "u1 \<in> Edtor1' (p,Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u)) \<longleftrightarrow> 
  (Ector (Gmap snd snd u1) = Ector1' u p \<and> 
   GSupp1 (Gmap fst fst u1) \<union> GSupp2 (Gmap fst fst u1) \<subseteq> {p} \<and> 
   GVrs2 u1 \<inter> PVrs p = {})"
using assms unfolding Edtor1'_def apply auto apply(rule Ector1_Ector'_inj) by auto

lemma in_Edtor1'_Ector: 
assumes "\<not> \<phi> u" "GVrs2 u \<inter> PVrs p = {}" 
shows "u1 \<in> Edtor1' (p,Ector u) \<longleftrightarrow> 
  (Ector (Gmap snd snd u1) = Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and> 
   GSupp1 (Gmap fst fst u1) \<union> GSupp2 (Gmap fst fst u1) \<subseteq> {p} \<and> 
   GVrs2 u1 \<inter> PVrs p = {})"
proof-
  define v where v: "v \<equiv> Gmap (\<lambda>e (p::P). e) (\<lambda>e (p::P). e) u"
  have u: "u = Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) v"
  unfolding v Gmap_comp o_def by simp
  show ?thesis using assms apply(subst u)  
    by (simp add: GVrs2_Gmap \<phi>_Gmap in_Edtor1'_Ector_aux v)
qed


lemma Edtor1'_Ector: 
assumes "\<not> \<phi> u" "GVrs2 u \<inter> PVrs p = {}" 
shows "Edtor1' (p,Ector u) = 
  {u1 . Ector (Gmap snd snd u1) = Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and> 
        GSupp1 (Gmap fst fst u1) \<union> GSupp2 (Gmap fst fst u1) \<subseteq> {p} \<and> 
        GVrs2 u1 \<inter> PVrs p = {}}"
using in_Edtor1'_Ector[OF assms] by auto

fun Edtor' :: "P\<times>E' \<Rightarrow> ((P\<times>E',P\<times>E')G)set + E" where 
"Edtor' (p,e) = (let u = (SOME u. e = Ector u) in 
  if \<phi> u then Inr (Ector0' (Gmap (\<lambda>a p. a) (\<lambda>a p. a) u) p) else Inl (Edtor1' (p,e)))"
declare Edtor'.simps[simp del]
lemmas Edtor'_def = Edtor'.simps

lemma Edtor'_\<phi>: 
assumes "\<phi> u"
shows "Edtor' (p, Ector u) = Inr (Ector0' (Gmap (\<lambda>a p. a) (\<lambda>a p. a) u) p)"
using assms unfolding Edtor'_def 
by (smt (verit, ccfv_threshold) Eps_cong \<phi>_Some_Ector)


lemma Edtor'_not\<phi>: 
assumes "\<not> \<phi> u"
shows "Edtor' (p, Ector u) = Inl (Edtor1' (p, Ector u))"
using assms unfolding Edtor'_def 
by (smt (verit) Ector_\<phi> tfl_some)  

(* *)
lemma Edtor1'_NE: 
assumes \<phi>: "\<not> \<phi> u" 
shows "Edtor1' (p, Ector u) \<noteq> {}" using in_Edtor1'_Ector
proof-
  obtain u0 where u0u: "Ector u0 = Ector u" and g: "GVrs2 u0 \<inter> PVrs p = {}" 
  using countable_PVrs sorry (* OK *)
  hence \<phi>: "\<not> \<phi> u0" using \<phi> using Ector_\<phi> by blast
  obtain uu1 where "Ector uu1 = Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u0) p" "GVrs2 uu1 \<inter> PVrs p = {}" 
  using countable_PVrs sorry (* OK *)
  then have "Gmap (Pair p) (Pair p) uu1 \<in> Edtor1' (p, Ector u)" 
  unfolding u0u[symmetric] apply(subst in_Edtor1'_Ector[OF \<phi> g]) apply safe
    subgoal unfolding Gmap_comp o_def by simp
    subgoal unfolding GSupp1_Gmap by auto
    subgoal unfolding GSupp2_Gmap by auto
    subgoal unfolding GVrs2_Gmap by auto .
  thus ?thesis by auto
qed

lemma dtorNeC: "dtorNeC Edtor'"
unfolding dtorNeC_def apply safe
  subgoal for p e U  apply(rule Ector_exhaust'[of e]) apply simp
  subgoal for u apply(cases "\<phi> u")
    subgoal unfolding Edtor'_\<phi> by simp
    subgoal unfolding Edtor'_not\<phi> using Edtor1'_NE by simp . . .

fun EVrs'' where "EVrs'' (p,e) = EVrs e \<union> PVrs p"
declare EVrs''.simps[simp del]
lemmas EVrs''_def = EVrs''.simps

fun Eperm'' where "Eperm'' \<sigma> (p,e) = (Pperm \<sigma> p, Eperm \<sigma> e)"
declare Eperm''.simps[simp del]
lemmas Eperm''_def = Eperm''.simps

lemma snd_EPerm''[simp]: "snd \<circ> Eperm'' \<sigma> = Eperm \<sigma> o snd"
unfolding fun_eq_iff by (simp add: Eperm''_def)

lemma fst_EPerm''[simp]: "fst \<circ> Eperm'' \<sigma> = Pperm \<sigma> o fst"
unfolding fun_eq_iff by (simp add: Eperm''_def)


lemma triv_Eperm_lift: "(\<lambda>e p. e) \<circ> Eperm \<sigma> = lift Eperm \<sigma> o (\<lambda>e p. e)"
unfolding fun_eq_iff o_def lift_def by simp

lemma Eperm_inv_iff: "bij \<sigma> \<Longrightarrow> Eperm (inv \<sigma>) e1 = e \<longleftrightarrow> e1 = Eperm \<sigma> e"
sorry


(* This one OK, all sorries doable: *)
lemma dtorPermC: "dtorPermC Edtor' Eperm''"
unfolding dtorPermC_def apply clarify subgoal for \<sigma> p e
unfolding Eperm''_def unfolding Eperm'_Eperm 
apply(rule Ector_exhaust'[of e], simp)
  subgoal for u apply(cases "\<phi> u")
    subgoal unfolding Edtor'_\<phi> apply safe 
    unfolding Eperm_Ector apply(subst Edtor'_\<phi>)
      subgoal using \<phi>_Gmap \<phi>_Gren by metis
      subgoal apply auto 
      apply(subst ctor0PermM[unfolded ctorPermM_def Eperm'_Eperm, rule_format])
        subgoal by (simp add: \<phi>_Gmap)
        subgoal by simp
        subgoal unfolding Gmap_comp Gmap_Gren unfolding lift_def o_def .. . .
     subgoal 
     apply(subgoal_tac "GVrs2 u \<inter> PVrs p = {} \<and> \<sigma> ` GVrs2 u \<inter> PVrs p = {}") 
        defer subgoal sorry (* OK *)
     unfolding Edtor'_not\<phi> apply safe 
     unfolding Eperm_Ector apply(subst Edtor'_not\<phi>)
      subgoal using \<phi>_Gmap \<phi>_Gren by metis
      subgoal apply simp  
      apply(subst Edtor1'_Ector)
        subgoal using \<phi>_Gmap \<phi>_Gren by metis
        subgoal unfolding GVrs2_Gmap GVrs2_Gren PVrs_Pperm  
          by (metis bij_is_inj image_Int image_empty)
        subgoal unfolding image_def apply auto apply(subst Edtor1'_Ector)
        apply auto subgoal for u0
        apply(rule exI[of _ "Gren (inv \<sigma>) (inv \<sigma>) u0"]) apply safe
          prefer 2 subgoal sorry (* OK *)
          subgoal 
          apply(rule exI[of _ "Gren (inv \<sigma>) (inv \<sigma>) (Gmap (Eperm'' (inv \<sigma>)) (Eperm'' (inv \<sigma>)) u0)"])
          apply safe
            subgoal unfolding Gmap_comp Gmap_Gren apply(subst Gmap_Gren)
              subgoal sorry (* OK *)
              subgoal sorry (* OK *)
              subgoal unfolding Gmap_comp apply simp 
              unfolding Gmap_o apply(subst o_def)
              apply(subst Eperm_Ector[symmetric])
                subgoal sorry (* OK *)
                subgoal sorry (* OK *)
                subgoal 
                unfolding Gmap_o[symmetric] triv_Eperm_lift unfolding Gmap_o
                unfolding o_def
                apply(subst (asm) ctor1PermM[unfolded ctorPermM_def, rule_format, unfolded Eperm'_Eperm, 
                            symmetric])
                  subgoal by (simp add: \<phi>_Gmap)
                  subgoal by simp
                  subgoal apply(subst Eperm_inv_iff) by auto . . .
              subgoal for e' unfolding GSupp1_Gmap apply auto subgoal for b apply(subst (asm) GSupp1_Gren)
                subgoal sorry (* OK*)
                subgoal sorry (* OK*)
                subgoal unfolding GSupp1_Gmap apply(auto simp: Eperm''_def) subgoal for pp ee 
                apply(subgoal_tac "pp = Pperm \<sigma> p")
                  subgoal apply auto sorry (* OK*)
                  subgoal by auto . . . .
              subgoal for pp unfolding GSupp2_Gmap apply auto apply(subst (asm) GSupp2_Gren)
                subgoal sorry (* OK*)
                subgoal sorry (* OK*)
                subgoal for ee unfolding GSupp2_Gmap apply(auto simp: Eperm''_def) subgoal for p' e'
                apply(subgoal_tac "p' = Pperm \<sigma> p")
                  subgoal apply auto sorry (* OK*)
                  subgoal by auto . . . 
              subgoal for a apply(subst (asm) GVrs2_Gren)
                subgoal sorry (* OK*) subgoal sorry (* OK*)
                subgoal unfolding GVrs2_Gmap GSupp1_Gmap GSupp2_Gmap apply auto  subgoal for a
                apply(subgoal_tac "a \<in> \<sigma> ` PVrs p") 
                  subgoal by (metis IntI PVrs_Pperm empty_iff)
                  subgoal sorry (* OK *) . . .
             subgoal apply(subst Gmap_Gren[symmetric])
               subgoal sorry (* OK *) subgoal sorry (* OK *)
               subgoal unfolding Gmap_comp sorry (* OK *) . . . . . . . . .

lemma fst_single_Gmap: "fst ` GSupp1 u \<subseteq> {p} \<Longrightarrow> fst ` GSupp2 u \<subseteq> {p}
\<Longrightarrow> Gmap (\<lambda>(p',e). (p,e)) (\<lambda>(p',e). (p,e)) u = u"
apply(rule Gmap_cong_id) by auto

lemma fst_single_Gmap': 
assumes "fst ` GSupp1 u \<subseteq> {p}" "fst ` GSupp2 u \<subseteq> {p}"
shows "Gmap (Pair p) (Pair p) (Gmap snd snd u) = u"
apply(rule sym) apply(subst fst_single_Gmap[symmetric, of _ p])
  subgoal by fact subgoal by fact
  subgoal unfolding Gmap_comp o_def  
    by (meson Gmap_cong case_prod_beta) .

(* This one OK, all sorries doable: *)         
lemma dtorVrsGrenC: "dtorVrsGrenC Edtor' EVrs''"
unfolding dtorVrsGrenC_def EVrs'_EVrs EVrs''_def apply safe 
subgoal for p e U u1 u2   apply(rule Ector_exhaust'[of e]) apply safe
  subgoal for u apply(cases "\<phi> u")
    subgoal unfolding Edtor'_\<phi> by simp
    subgoal unfolding Edtor'_not\<phi>  apply simp
    apply(subgoal_tac "GVrs2 u \<inter> PVrs p = {}") defer subgoal sorry (* OK *)
    unfolding Edtor1'_Ector apply auto 
    using Ector_eq_imp[of "Gmap snd snd u1" "Gmap snd snd u2"]
    unfolding EVrs''_def EVrs'_EVrs apply auto subgoal for \<sigma> 
    apply(rule exI[of _ \<sigma>]) unfolding GVrs1_Gmap  GVrs2_Gmap GSupp1_Gmap GSupp2_Gmap apply(intro conjI)
      subgoal . subgoal .
      subgoal apply(subgoal_tac "\<Union> {EVrs e |e. e \<in> snd ` GSupp1 u1} \<union> 
        \<Union> {EVrs e - GVrs2 u1 |e. e \<in> snd ` GSupp1 u1}  
    \<subseteq> \<Union> {EVrs b \<union> PVrs a |a b. (a, b) \<in> GSupp1 u1} \<union>
       \<Union> {EVrs b \<union> PVrs a - GVrs2 u1 |a b. (a, b) \<in> GSupp1 u1}")
         subgoal by (smt (verit, ccfv_threshold) Diff_iff Un_iff diff_shunt subsetI)
         subgoal by auto blast+ .  

 apply(subst (asm) Gmap_Gren[of id \<sigma>,symmetric]) subgoal sorry (* OK *) subgoal sorry (* OK *)
    subgoal sorry (* OK *) subgoal sorry (* OK *)
  apply(subst (asm) Gmap_Gren[of id \<sigma>,symmetric]) subgoal sorry (* OK *) subgoal sorry (* OK *)
    subgoal sorry (* OK *) subgoal sorry (* OK *)
    apply(subst fst_single_Gmap'[symmetric, of _ p]) 
      subgoal by auto subgoal by auto
      subgoal apply(subgoal_tac "Gmap (Pair p) (Pair p) (Gmap snd snd u2) = 
          Gmap (Pair p) (Pair p) (Gmap snd snd (Gren id \<sigma> u1))")
        subgoal unfolding Gmap_comp o_def id_def apply simp
        apply(rule Gmap_cong_id)
          subgoal apply(subst (asm) GSupp1_Gren) subgoal sorry (* OK *) subgoal sorry (* OK *)
            subgoal sorry (* OK *) subgoal sorry (* OK *)
            subgoal by auto .
          subgoal apply(subst (asm) GSupp2_Gren) subgoal sorry (* OK *) subgoal sorry (* OK *)
            subgoal sorry (* OK *) subgoal sorry (* OK *)
            subgoal by auto . .
        subgoal by simp . . . . . .


lemma tri_Un1: "A \<subseteq> B \<union> C \<Longrightarrow> A \<union> B \<subseteq> B \<union> C" by auto
lemma tri_Un3: "A \<union> A' \<union> A'' \<subseteq> B \<union> C \<Longrightarrow> B \<union> A \<union> A' \<union> A'' \<subseteq> B \<union> C" by auto


(* This one only works if we union with V *)
lemma Ector1'_Ector_EVrs: 
"\<not> \<phi> u \<Longrightarrow> EVrs'' (p, Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p) \<subseteq> PVrs p \<union> EVrs (Ector u)"
unfolding EVrs''_def apply(rule tri_Un1) 
apply(rule subset_trans[OF ctor1VarsM[unfolded ctorVarsM_def EVrs'_EVrs, rule_format]])
  subgoal by (simp add: \<phi>_Gmap)
  subgoal apply(rule tri_Un3) unfolding EVrs'_EVrs EVrs_Ector GSupp1_Gmap GVrs1_Gmap by auto . 

lemma Ector0'_Ector_EVrs: 
"\<phi> u \<Longrightarrow> EVrs'' (p, Ector0' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p) \<subseteq> PVrs p \<union> EVrs (Ector u)"
unfolding EVrs''_def apply(rule tri_Un1) 
apply(rule subset_trans[OF ctor0VarsM[unfolded ctorVarsM_def EVrs'_EVrs, rule_format]])
  subgoal by (simp add: \<phi>_Gmap)
  subgoal apply(rule tri_Un3) unfolding EVrs'_EVrs EVrs_Ector GSupp1_Gmap GVrs1_Gmap by auto . 

lemma dtorVrsC: "dtorVrsC Edtor' EVrs''"
unfolding EVrs'_EVrs EVrs''_def
unfolding dtorVrsC_def apply (intro allI) subgoal for pe apply(cases pe) subgoal for p e apply clarify
apply(rule Ector_exhaust'[of e]) apply clarify apply (intro conjI)
  subgoal for u apply(cases "\<phi> u")
    subgoal unfolding Edtor'_\<phi> by simp
    subgoal unfolding Edtor'_not\<phi> 
    apply(subgoal_tac "GVrs2 u \<inter> PVrs p = {}") defer subgoal sorry (* OK *)
    unfolding Edtor1'_Ector unfolding EVrs_Ector GSupp1_Gmap GSupp2_Gmap apply clarsimp
    subgoal for ua 
    apply(rule incl_Un_triv3)
    unfolding EVrs''_def EVrs_Ector
    apply(rule subset_trans[OF _ Ector1_Ector'_topFree'[of u p "Gmap snd snd ua", unfolded GSupp1_Gmap 
      GSupp2_Gmap GVrs1_Gmap GVrs2_Gmap]]) 
      subgoal apply(rule incl_Un3_triv3)
        subgoal ..
        subgoal by fastforce
        subgoal by auto (metis Diff_iff image_eqI snd_conv) .
      subgoal .
      subgoal .
      subgoal .
      subgoal by simp . . .
  subgoal for u apply(cases "\<phi> u")
    subgoal using Ector0'_Ector_EVrs unfolding Edtor'_\<phi> EVrs''_def by auto
    subgoal unfolding Edtor'_not\<phi> by simp . . . .


lemma nomC: "nom Eperm'' EVrs''"
unfolding nom_def apply safe
  subgoal for \<sigma>1 \<sigma>2 apply(rule ext) apply safe subgoal for p e
    unfolding Eperm''_def  
    by (simp add: Eperm''_def Eperm_comp Pperm_comp) .
  subgoal for \<sigma>1 \<sigma>2 p e unfolding Eperm''_def EVrs''_def   
    by (metis Eperm_cong Pperm_cong Un_iff) . 


(* comodels from special_models_plus: *)
sublocale C: Comodel where Edtor' = Edtor' and Eperm' = Eperm'' and EVrs' = EVrs'' 
apply standard using nomC dtorNeC dtorPermC dtorVrsGrenC dtorVrsC by auto

thm C.corec_Edtor_Inl C.corec_Edtor_Inr C.corec_Eperm  C.corec_EVrs C.corec_unique 


end (* locale Bimodel *)





end