theory Bimodels_are_Comodels
  imports Bimodels Comodels
begin

(* Inferring a recursion from a corecursion principle by organizing
bimodels as comodels, and then showing how the corecursion principle 
from comodels gives rise to a *recursion* principle for bimodels 
(the same clauses as the ones coming from models)  *)

context Bimodel 
begin


definition Evalid' :: "'a E'\<times>'a P \<Rightarrow> bool" where 
"Evalid' ep \<equiv> Pvalid (snd ep)"  

fun Edtor1' :: "'a E'\<times>'a P \<Rightarrow> (('a::var,'a,'a E'\<times>'a P,'a E'\<times>'a P)G) set" where 
"Edtor1' (e,p) =
\<Union> { {u1 . Ector (Gmap fst fst u1) = Ector' u p \<and> 
          GSupp1 (Gmap snd snd u1) \<union>  GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
          GVrs2 u1 \<inter> PVrs p = {} \<and> GVrs2 u1 \<inter> GVrs1 u1 = {}} | 
       u . \<not> base u \<and> Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u) = e \<and> 
           GVrs2 u \<inter> PVrs p = {} \<and> GVrs2 u \<inter> GVrs1 u = {}}"
declare Edtor1'.simps[simp del]
lemmas Edtor1'_def = Edtor1'.simps

lemma in_Edtor1'_Ector_aux: 
assumes "\<not> base u" "Pvalid p" "GVrs2 u \<inter> PVrs p = {}" "GVrs2 u \<inter> GVrs1 u = {}"
shows "u1 \<in> Edtor1' (Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u),p) \<longleftrightarrow> 
  (Ector (Gmap fst fst u1) = Ector' u p \<and> 
   GSupp1 (Gmap snd snd u1) \<union> GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
   GVrs2 u1 \<inter> PVrs p = {} \<and> GVrs2 u1 \<inter> GVrs1 u1 = {})"
using assms unfolding Edtor1'_def by (auto intro: Ector_Ector'_inj_step)

lemma in_Edtor1'_Ector: 
assumes "\<not> base u" "Pvalid p" "GVrs2 u \<inter> PVrs p = {}" "GVrs2 u \<inter> GVrs1 u = {}"
shows "u1 \<in> Edtor1' (Ector u,p) \<longleftrightarrow> 
  (Ector (Gmap fst fst u1) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and> 
   GSupp1 (Gmap snd snd u1) \<union> GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
   GVrs2 u1 \<inter> PVrs p = {} \<and> GVrs2 u1 \<inter> GVrs1 u1 = {})"
proof-
  define v where v: "v \<equiv> Gmap (\<lambda>e (p::'a P). e) (\<lambda>e (p::'a P). e) u"
  have u: "u = Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) v"
  unfolding v Gmap_comp o_def by simp
  show ?thesis using assms apply(subst u)  
  by (auto simp add: GVrs1_Gmap GVrs2_Gmap base_Gmap in_Edtor1'_Ector_aux v) 
qed


lemma Edtor1'_Ector: 
assumes "\<not> base u" "Pvalid p" "GVrs2 u \<inter> PVrs p = {}" "GVrs2 u \<inter> GVrs1 u = {}" 
shows "Edtor1' (Ector u,p) = 
  {u1 . Ector (Gmap fst fst u1) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and> 
        GSupp1 (Gmap snd snd u1) \<union> GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
        GVrs2 u1 \<inter> PVrs p = {} \<and> GVrs2 u1 \<inter> GVrs1 u1 = {}}"
using in_Edtor1'_Ector[OF assms] by auto

fun Edtor' :: "'a E'\<times>'a P \<Rightarrow> (('a::var,'a,'a E'\<times>'a P,'a E'\<times>'a P)G)set + 'a E" where 
"Edtor' (e,p) = (let u = (SOME u. e = Ector u) in 
  if base u then Inr (Ector' (Gmap (\<lambda>a p. a) (\<lambda>a p. a) u) p) else Inl (Edtor1' (e,p)))"
declare Edtor'.simps[simp del]
lemmas Edtor'_def = Edtor'.simps

lemma Edtor'_base: 
assumes "base u"
shows "Edtor' (Ector u, p) = Inr (Ector' (Gmap (\<lambda>a p. a) (\<lambda>a p. a) u) p)"
using assms unfolding Edtor'_def 
by (smt (verit, ccfv_threshold) Eps_cong base_Some_Ector)


lemma Edtor'_step: 
assumes "\<not> base u"
shows "Edtor' (Ector u, p) = Inl (Edtor1' (Ector u, p))"
using assms unfolding Edtor'_def 
by (smt (verit) Ector_base tfl_some) 

lemma Edtor'_Inl_step: "Edtor' (Ector u, p) = Inl U \<Longrightarrow> \<not> base u"
  using Edtor'_base by force

lemma Edtor'_Inr_base: "Edtor' (Ector u, p) = Inr U \<Longrightarrow> base u"
  using Edtor'_step by force 

(* *)
lemma Edtor1'_NE: 
assumes base: "\<not> base u" and p: "Pvalid p"
shows "Edtor1' (Ector u, p) \<noteq> {}" using in_Edtor1'_Ector
proof-
  obtain u0 where u0u: "Ector u0 = Ector u" 
  and g: "GVrs2 u0 \<inter> PVrs p = {}" "GVrs2 u0 \<inter> GVrs1 u0 = {}" 
  using Ector_surj_fresh[OF countable_PVrs, OF p] by blast
  hence base: "\<not> base u0" using base using Ector_base by blast
  obtain uu1 where "Ector uu1 = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u0) p" 
  "GVrs2 uu1 \<inter> PVrs p = {}" "GVrs2 uu1 \<inter> GVrs1 uu1 = {}"
  using  Ector_surj_fresh[OF countable_PVrs, OF p] by blast 
  then have "Gmap (\<lambda>e. (e,p)) (\<lambda>e. (e,p)) uu1 \<in> Edtor1' (Ector u, p)" 
  unfolding u0u[symmetric] apply(subst in_Edtor1'_Ector[OF base p g]) apply safe
    subgoal unfolding Gmap_comp o_def by simp
    subgoal unfolding GSupp1_Gmap by auto
    subgoal unfolding GSupp2_Gmap by auto
    subgoal unfolding GVrs2_Gmap by auto 
    subgoal unfolding GVrs1_Gmap GVrs2_Gmap by auto .
  thus ?thesis by auto
qed

lemma dtorNeC: "dtorNeC Evalid' Edtor'"
unfolding dtorNeC_def apply safe
  subgoal for e p U  apply(rule Ector_exhaust'[of e]) apply simp
  subgoal for u apply(cases "base u")
    subgoal unfolding Edtor'_base by simp
    subgoal unfolding Edtor'_step Evalid'_def using Edtor1'_NE by simp . . .

fun EVrs'' where "EVrs'' (e,p) = EVrs e \<union> PVrs p"
declare EVrs''.simps[simp del]
lemmas EVrs''_def = EVrs''.simps

fun Eperm'' where "Eperm'' \<sigma> (e,p) = (Eperm \<sigma> e, Pperm \<sigma> p)"
declare Eperm''.simps[simp del]
lemmas Eperm''_def = Eperm''.simps

lemma fst_EPerm'[simp]: "fst \<circ> Eperm'' \<sigma> = Eperm \<sigma> o fst"
unfolding fun_eq_iff by (simp add: Eperm''_def)

lemma snd_EPerm'[simp]: "snd \<circ> Eperm'' \<sigma> = Pperm \<sigma> o snd"
unfolding fun_eq_iff by (simp add: Eperm''_def)

lemma Eperm''_id[simp]: "Eperm'' id = id"
  using Eperm''_def  
  by (metis Eperm_id Pperm_id apfst_convE eq_id_iff)   

lemma Eperm''_o: 
"Pvalid (snd ep) \<Longrightarrow> small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> 
Eperm'' (\<sigma>1 \<circ> \<sigma>2) ep = Eperm'' \<sigma>1 (Eperm'' \<sigma>2 ep)"
apply(cases ep) by (simp add: Eperm''_def Eperm_comp Pperm_comp) 


lemma Eperm''_comp: 
"Pvalid p \<Longrightarrow> small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> 
 Eperm'' \<sigma>1 (Eperm'' \<sigma>2 (e,p)) = Eperm'' (\<sigma>1 \<circ> \<sigma>2) (e,p)"
by (simp add: Eperm''_def Eperm_comp Pperm_comp) 

lemma Eperm''_cong:
"Pvalid p \<Longrightarrow> small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow>
 small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> \<forall>a\<in>EVrs'' (e,p). \<sigma>1 a = \<sigma>2 a \<Longrightarrow> Eperm'' \<sigma>1 (e,p) = Eperm'' \<sigma>2 (e,p)"
unfolding Eperm''_def EVrs''_def   
by (metis Eperm_cong Pperm_cong UnCI)    

lemma nomC: "nom Evalid' Eperm'' EVrs''"
unfolding nom_def apply safe
 unfolding Evalid'_def Eperm''_def using nomP unfolding nom_def apply simp  
apply auto  
  apply (auto simp add: EVrs''_def Eperm_comp Pperm_comp)
  apply (metis Eperm_cong Un_iff) 
  by (metis Pperm_cong Un_iff) 

lemma Pvalid_Pperm[simp]: "Pvalid p \<Longrightarrow> small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> Pvalid (Pperm \<sigma> p)"
using nomP unfolding nom_def by blast

lemma dtorPermC: "dtorPermC Evalid' Edtor' Eperm''"
unfolding dtorPermC_def apply clarify subgoal for \<sigma> e p
unfolding Eperm''_def Evalid'_def 
  apply(rule Ector_exhaust_fresh[OF "countable_PVrs_im", of \<sigma> p e], simp_all)
  unfolding A_Int_Un_emp apply(erule conjE) apply simp
  subgoal for u apply(cases "base u")
    subgoal unfolding Edtor'_base apply safe 
    unfolding Eperm_Ector apply(subst Edtor'_base)
      subgoal using base_Gmap base_Gren by metis
      subgoal apply auto 
      apply(subst ctorPermM_Ector'[unfolded ctorPermM_def, rule_format])
        subgoal by simp
        subgoal unfolding Gmap_comp Gmap_Gren unfolding lift_def o_def .. . .
     subgoal 
     apply(subgoal_tac "\<sigma> ` GVrs2 u \<inter> PVrs p = {}") 
     prefer 2 subgoal unfolding bij_inv_Un_triv by auto
     unfolding Edtor'_step apply safe 
     unfolding Eperm_Ector apply(subst Edtor'_step)
      subgoal using base_Gmap base_Gren by metis
      subgoal apply simp  
      apply(subst Edtor1'_Ector)
        subgoal using base_Gmap base_Gren by metis
        subgoal by auto
        subgoal unfolding GVrs2_Gmap GVrs2_Gren PVrs_Pperm  
          by (metis bij_is_inj image_Int image_empty)
        subgoal unfolding GVrs2_Gmap GVrs2_Gren GVrs1_Gmap GVrs1_Gren PVrs_Pperm  
        by (simp add: image_Int_empty) 
        subgoal unfolding image_def apply auto apply(subst Edtor1'_Ector)
        apply auto subgoal for u0
        apply(rule exI[of _ "Gren (inv \<sigma>) (inv \<sigma>) u0"]) apply safe
          prefer 2 subgoal apply(subst Gren_comp) by auto
          subgoal 
          apply(rule exI[of _ "Gren (inv \<sigma>) (inv \<sigma>) (Gmap (Eperm'' (inv \<sigma>)) (Eperm'' (inv \<sigma>)) u0)"])
          apply safe
            subgoal unfolding Gmap_comp Gmap_Gren apply(subst Gmap_Gren)
              subgoal by auto
              subgoal by auto
              subgoal unfolding Gmap_comp apply simp 
              unfolding Gmap_o apply(subst o_def)
              apply(subst Eperm_Ector[symmetric])
                subgoal by auto
                subgoal by auto
                subgoal 
                unfolding Gmap_o[symmetric] triv_Eperm_lift unfolding Gmap_o
                unfolding o_def
                apply(subst (asm) ctorPermM_Ector'[unfolded ctorPermM_def, rule_format,  
                            symmetric]) 
                  subgoal by simp
                  subgoal apply(subst Eperm_inv_iff) by auto . . .
              subgoal for e' unfolding GSupp1_Gmap apply auto subgoal for b apply(subst (asm) GSupp1_Gren)
                subgoal by auto
                subgoal by auto
                subgoal unfolding GSupp1_Gmap apply(auto simp: Eperm''_def) subgoal for ee pp 
                apply(subgoal_tac "pp = Pperm \<sigma> p")
                  subgoal apply simp apply(subst Pperm_comp) by auto
                  subgoal by auto . . . .
              subgoal for pp unfolding GSupp2_Gmap apply auto apply(subst (asm) GSupp2_Gren)
                subgoal by auto
                subgoal by auto
                subgoal for ee unfolding GSupp2_Gmap apply(auto simp: Eperm''_def) subgoal for e' p'
                apply(subgoal_tac "p' = Pperm \<sigma> p")
                  subgoal apply simp apply(subst Pperm_comp) by auto
                  subgoal by auto . . . 
              subgoal for a apply(subst (asm) GVrs2_Gren)
                subgoal by auto subgoal by auto
                subgoal unfolding GVrs2_Gmap GSupp1_Gmap GSupp2_Gmap apply auto  
                subgoal for a
                apply(subgoal_tac "a \<in> \<sigma> ` PVrs p") 
                  subgoal by (metis IntI PVrs_Pperm empty_iff)
                  subgoal unfolding bij_in_inv_Un_triv . . . .
              subgoal by (metis (no_types, lifting) GVrs1_Gmap GVrs1_Gren GVrs2_Gmap 
                    GVrs2_Gren bij_betw_inv_into bij_in_inv_Un_triv disjoint_iff small_inv)
              subgoal apply(subst Gmap_Gren[symmetric])
               subgoal by auto subgoal by auto
               subgoal unfolding Gmap_comp  
               apply(rule sym) apply(rule Gmap_cong_id)
                 subgoal unfolding o_def
                 apply(subst Eperm''_o[symmetric]) apply auto 
                 apply(subst (asm) GSupp1_Gren) by (auto simp: GSupp1_Gmap subset_iff) 
                 subgoal unfolding o_def
                 apply(subst Eperm''_o[symmetric]) apply auto 
                 apply(subst (asm) GSupp2_Gren) by (auto simp: GSupp2_Gmap subset_iff) . . . . . . . . . .
               

lemma dtorVrsGrenC: "dtorVrsGrenC Evalid' Edtor' Eperm'' EVrs''"
unfolding dtorVrsGrenC_def EVrs''_def proof safe 
  fix e p U u1 u2 
  assume "Evalid' (e, p)"
  and 0: "Edtor' (e, p) = Inl U" and u12: "{u1, u2} \<subseteq> U"
  hence P: "Pvalid p" unfolding Evalid'_def by simp
  show "\<exists>\<sigma>. small \<sigma> \<and>
           bij \<sigma> \<and>
           id_on ((\<Union> (EVrs'' ` GSupp1 u1) - GVrs2 u1)) \<sigma> \<and>
           Gren id \<sigma> (Gmap (Eperm'' \<sigma>) id u1) = u2"
  proof(rule Ector_exhaust_fresh[OF countable_PVrs, of p e, OF P])
    fix u assume e: "e = Ector u" and g: "GVrs2 u \<inter> PVrs p = {}" "GVrs2 u \<inter> GVrs1 u = {}"
    show ?thesis proof(cases "base u")
      case True
      show ?thesis using 0 unfolding e Edtor'_base[OF True] by simp
    next
      case False
      hence U: "Edtor1' (Ector u, p) = U" using 0 unfolding e Edtor'_step[OF False] by simp
      hence U: "U =
      {u1. Ector (Gmap fst fst u1) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and>
           GSupp1 (Gmap snd snd u1) \<subseteq> {p} \<and> GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
           GVrs2 u1 \<inter> PVrs p = {} \<and> GVrs2 u1 \<inter> GVrs1 u1 = {}}"  
      unfolding Edtor1'_Ector[OF False P g] by auto

      hence u1: "Ector (Gmap fst fst u1) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p"
           "GSupp1 (Gmap snd snd u1) \<subseteq> {p}" "GSupp2 (Gmap snd snd u1) \<subseteq> {p}" "GVrs2 u1 \<inter> PVrs p = {}"
      and u2: "Ector (Gmap fst fst u2) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p"
          "GSupp1 (Gmap snd snd u2) \<subseteq> {p}" "GSupp2 (Gmap snd snd u2) \<subseteq> {p}" "GVrs2 u2 \<inter> PVrs p = {}"
      using u12 by auto

      have 00: "PVrs p \<inter> GVrs2 (Gmap fst fst u1) = {}" using u1 by (auto simp: GVrs2_Gmap)
      note eq = u1(1)[unfolded u2(1)[symmetric]]
      
      obtain \<sigma> where ss: "bij \<sigma> \<and> small \<sigma>"
        "id_on 
         ((\<Union> (EVrs ` GSupp1 (Gmap fst fst u1)) - GVrs2 (Gmap fst fst u1)) \<union> PVrs p )
         \<sigma>"
        "Gren id \<sigma> (Gmap (Eperm \<sigma>) id (Gmap fst fst u1)) = Gmap fst fst u2"   
        using Ector_eq_imp_strong[of "Gmap fst fst u1" "Gmap fst fst u2", OF eq countable_PVrs 00, OF P]
        by blast
      have io: "\<And>e' p' a. (e',p') \<in> GSupp1 u1 \<Longrightarrow> a \<in> EVrs e' \<Longrightarrow> a \<notin> GVrs2 u1 \<Longrightarrow> \<sigma> a = a"
          "\<And>a. a \<in> PVrs p \<Longrightarrow> \<sigma> a = a" 
      using ss(2) unfolding id_on_def by (fastforce simp: GSupp1_Gmap GSupp2_Gmap GVrs2_Gmap)+

      show ?thesis proof(rule exI[of _ \<sigma>], safe)
        show "small \<sigma>" "bij \<sigma>" using ss by auto
      next
        show "id_on ((\<Union> (EVrs'' ` GSupp1 u1) - GVrs2 u1)) \<sigma>"
        unfolding id_on_def image_def proof(auto simp: EVrs''_def)
          fix a e' p' assume "(e', p') \<in> GSupp1 u1" "a \<in> EVrs e'" "a \<notin> GVrs2 u1" 
          thus "\<sigma> a = a" using io(1) by auto
        next
          fix a e' p' assume aa: "(e', p') \<in> GSupp1 u1" "a \<in> PVrs p'"  "a \<notin> GVrs2 u1"
          hence "p' = p" using u1(2) unfolding GSupp1_Gmap by auto  
          thus "\<sigma> a = a" using aa io(2) by auto
        qed
      next
        have ss3: "Gmap (Eperm \<sigma>) id (Gmap fst fst (Gren id \<sigma> u1)) = Gmap fst fst u2"
        unfolding ss(3)[symmetric] 
        by (simp add: Gmap_Gren ss(1)) 

        have gg: "Gmap (Eperm'' \<sigma>) id (Gren id \<sigma> u1) = u2"
        apply(subst snd_single_Gmap'[symmetric, where t = u2 and p = p])
          subgoal by (metis GSupp1_Gmap u2(2))
          subgoal by (metis GSupp2_Gmap u2(3))
          subgoal apply(subst snd_single_Gmap'[symmetric, where t = "Gren id \<sigma> u1" and p = p])
            subgoal by (metis GSupp1_Gmap GSupp1_Gren bij_id small_id ss(1) u1(2))
            subgoal by (metis GSupp2_Gmap GSupp2_Gren bij_id small_id ss(1) u1(3))
            subgoal unfolding ss3[symmetric] unfolding Gmap_comp unfolding o_def Eperm''_def
            apply(rule Gmap_cong)
              subgoal by (metis P Pperm_cong Pperm_id bij_id eq_id_iff io(2) small_id ss(1))
              subgoal by simp . . .
        show "Gren id \<sigma> (Gmap (Eperm'' \<sigma>) id u1) = u2"
        unfolding gg[symmetric]  
        by (simp add: Gmap_Gren ss(1)) 
      qed
    qed
  qed
qed

lemma step_Ector'_Ector_EVrs: 
"\<not> base u \<Longrightarrow> Pvalid p \<Longrightarrow> EVrs'' (Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p, p) \<subseteq> PVrs p \<union> EVrs (Ector u)"
unfolding EVrs''_def apply(rule tri_Un1) 
apply(rule subset_trans[OF ctorVarsM_Ector'[unfolded ctorVarsM_def, rule_format]])
  subgoal .
  subgoal apply(rule tri_Un3) unfolding EVrs_Ector GSupp1_Gmap GVrs1_Gmap apply auto  
    apply (metis Diff_iff GVrs2_Gmap)  
    by (metis GSupp2_Gmap image_iff) .

lemma base_Ector'_Ector_EVrs: 
"base u \<Longrightarrow> Pvalid p \<Longrightarrow> EVrs'' (Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p, p) \<subseteq> PVrs p \<union> EVrs (Ector u)"
unfolding EVrs''_def apply(rule tri_Un1) 
apply(rule subset_trans[OF ctorVarsM_Ector'[unfolded ctorVarsM_def, rule_format]])
  subgoal .
  subgoal apply(rule tri_Un3) unfolding EVrs_Ector GSupp1_Gmap GVrs1_Gmap apply auto 
  apply (simp add: base_base) 
    by (simp add: base_Gmap base_base) .

lemma dtorVrsC: "dtorVrsC Evalid' Edtor' EVrs''"
unfolding EVrs''_def
unfolding dtorVrsC_def Evalid'_def apply (intro allI impI) subgoal for pe apply(cases pe) subgoal for e p 
apply clarsimp
apply(rule Ector_exhaust_fresh[OF countable_PVrs, of p e]) apply clarify apply (intro conjI allI)
  subgoal for u apply(cases "base u")
    subgoal unfolding Edtor'_base using Edtor'_Inl_step by auto
    subgoal apply clarify unfolding Edtor'_step  
    unfolding Edtor1'_Ector unfolding EVrs_Ector GSupp1_Gmap GSupp2_Gmap apply clarify
    subgoal for ua  
    apply(rule incl_Un_triv3)
    unfolding EVrs''_def EVrs_Ector 
    apply(rule subset_trans[OF _ Ector_Ector'_EVrs_step'[of u p "Gmap fst fst ua", unfolded GSupp1_Gmap 
      GSupp2_Gmap GVrs1_Gmap GVrs2_Gmap]]) 
      subgoal apply(rule incl_Un3_triv3)
        subgoal ..
        subgoal by auto (metis (lifting) DiffI fst_conv image_eqI)   
        subgoal by auto fastforce .
      subgoal .
      subgoal .
      subgoal .
    subgoal using Edtor'_step in_Edtor1'_Ector by auto
    subgoal using Edtor'_step in_Edtor1'_Ector by auto . . .
  subgoal for u apply(cases "base u")
    subgoal using base_Ector'_Ector_EVrs unfolding Edtor'_base EVrs''_def 
      by (metis Edtor'_base Un_commute Un_subset_iff old.sum.inject(2))
    subgoal unfolding Edtor'_step using Edtor'_Inr_base by blast . . . .


lemma presDV_Evalid'_Edtor': "presDV Evalid' Edtor'"
unfolding presDV_def apply clarify
  subgoal for e p U u' e' p'
  unfolding Evalid'_def snd_conv apply(rule Ector_exhaust_fresh[OF countable_PVrs, of p e])
    subgoal .
    subgoal for u apply(cases "base u")
      subgoal apply clarify unfolding Edtor'_base by auto
      subgoal apply clarify unfolding Edtor'_step Edtor1'_Ector 
      by (auto simp: GSupp1_Gmap GSupp2_Gmap) . . .
       
lemma presPV_Evalid'_Eperm'': "presPV Evalid' Eperm''"
unfolding presPV_def apply clarify subgoal for \<sigma> e p 
unfolding Eperm''_def Evalid'_def by simp .


(* Borrowing the corecursion from comodels, under the assumptions that E 
is final; upon customization, corecursion becomes recursion 
(having the same characteristic clauses as the recursion borrowed 
from models under the assumption that E is initial)!  *)

sublocale C: Comodel where Evalid' = Evalid' and Edtor' = Edtor' 
and Eperm' = Eperm'' and EVrs' = EVrs'' 
apply standard using nomC dtorNeC dtorPermC dtorVrsGrenC dtorVrsC 
presDV_Evalid'_Edtor' presPV_Evalid'_Eperm'' by auto

thm C.corec_Edtor_Inl C.corec_Edtor_Inr C.corec_Eperm  C.corec_EVrs C.corec_unique 

(* NB: these stay the same: *) thm C.corec_Eperm

definition "crec \<equiv> curry C.corec"

theorem rec_Ector_base:
assumes "base u" "Pvalid p"   
shows "GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> 
   crec (Ector u) p = Ector' (Gmap crec crec u) p"
using C.corec_Edtor_Inr[of "(Ector u,p)"]
using assms apply - unfolding Edtor'_base  apply simp unfolding crec_def 
apply simp by (metis Evalid'_def base_Gmap_eq snd_conv) 

theorem rec_Ector_not_base:
assumes f: "\<not> base u" and p: "Pvalid p"  and g : "GVrs2 u \<inter> PVrs p = {}" "GVrs2 u \<inter> GVrs1 u = {}"
shows "crec (Ector u) p = Ector' (Gmap crec crec u) p"
proof-
  have "Edtor' (Ector u, p) = Inl (Edtor1' (Ector u, p))" 
  and 1: "Gmap C.corec C.corec ` (Edtor1' (Ector u, p)) \<subseteq> Edtor (C.corec (Ector u, p))"
    using f p g apply(auto simp add: C.corec_Edtor_Inl Edtor'_step)  
    using C.corec_Edtor_Inl Edtor'_step Evalid'_def by fastforce
  hence 2: "\<And>v. Ector (Gmap fst fst v) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and>
          GSupp1 (Gmap snd snd v) \<union> GSupp2 (Gmap snd snd v) \<subseteq> {p} \<and> 
          GVrs2 v \<inter> PVrs p = {} \<and> GVrs2 v \<inter> GVrs1 v = {}
   \<Longrightarrow> Ector (Gmap C.corec C.corec v) = C.corec (Ector u, p)" 
  using f p g unfolding Edtor_def Edtor1'_Ector  
  using in_Edtor1'_Ector unfolding GSupp1_Gmap GSupp2_Gmap image_def 
  unfolding subset_iff by safe blast
  obtain w where w: "Ector w = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p" 
  and g1: "GVrs2 w \<inter> PVrs p = {}" "GVrs2 w \<inter> GVrs1 w = {}" by (meson p Ector_surj_fresh countable_PVrs)
  show ?thesis unfolding crec_def apply simp apply(subst 2[symmetric, of "Gmap (\<lambda>e. (e,p)) (\<lambda>e. (e,p)) w"])
  apply safe
    subgoal unfolding Gmap_comp apply simp unfolding w ..
    subgoal unfolding GSupp1_Gmap by auto
    subgoal unfolding GSupp2_Gmap by auto
    subgoal using g1 unfolding GVrs2_Gmap by auto
    subgoal using g1 unfolding GVrs1_Gmap GVrs2_Gmap by auto
    subgoal using f unfolding Gmap_comp unfolding curry_def o_def
      apply(rule Ector_Ector'_Gmap) using w p g g1 by auto . 
qed
      
theorem crec_Eperm:
assumes "Pvalid p" "small \<sigma>" "bij \<sigma>"
shows "crec (Eperm \<sigma> e) p = Eperm \<sigma> (crec e (Pperm (inv \<sigma>) p))"
proof-
  have e: "Evalid' (e,p)" using assms unfolding Evalid'_def by auto
  have "C.corec (Eperm'' \<sigma> (e,Pperm (inv \<sigma>) p)) = Eperm \<sigma> (C.corec (e,Pperm (inv \<sigma>) p))" 
    using C.corec_Eperm[OF e ]  
    by (simp add: C.corec_Eperm Evalid'_def assms)
  thus ?thesis unfolding Eperm''_def crec_def curry_def using assms 
    apply- apply(subst (asm) Pperm_comp) by auto
qed

theorem rec_EVrs: 
assumes "Pvalid p"
shows "EVrs (crec e p) \<subseteq> PVrs p \<union> EVrs e"
proof-
  have "EVrs (C.corec (e,p)) \<subseteq> EVrs'' (e,p)" using assms C.corec_EVrs  
    by (simp add: Evalid'_def)
  thus ?thesis unfolding EVrs''_def crec_def curry_def by auto
qed

(* NB. UNiqueness is not needed for the syntax with bindings development; 
however, it does not use any axioms that are not used in the rest of 
the development.  *)
theorem rec_unique':
assumes "Pvalid p" and "\<And>u p. 
  Pvalid p \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> GVrs2 u \<inter> GVrs1 u = {} \<Longrightarrow>
 (base u \<longrightarrow> H (Ector u) p = Ector' (Gmap H H u) p)
 \<and>
 (\<not> base u \<longrightarrow> H (Ector u) p = Ector' (Gmap H H u) p)"
shows "H e p = crec e p" 
proof-
  have ep: "Evalid' (e, p)" using assms unfolding Evalid'_def by auto
  have "uncurry H (e,p) = C.corec (e,p)" 
  proof(rule C.corec_unique[OF _ _ ep], safe)
    fix e p U x w
    assume "Evalid' (e, p)" and 
    1: "Edtor' (e, p) = Inl U" and w: "w \<in> U"
    hence p: "Pvalid p" unfolding Evalid'_def by auto
    obtain u where e: "e = Ector u" and 2: "GVrs2 u \<inter> PVrs p = {}" "GVrs2 u \<inter> GVrs1 u = {}"   
      using Ector_surj_fresh[OF countable_PVrs[OF p], of e] by auto 
    have f: "\<not> base u" using 1 using Edtor'_Inl_step e by auto
    from 1 f 2 w have "w \<in> Edtor1' (Ector u, p)" apply - unfolding e Edtor'_step by auto
    hence 0: "Ector (Gmap fst fst w) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p"
    and 00: "GSupp1 (Gmap snd snd w) \<union> GSupp2 (Gmap snd snd w) \<subseteq> {p}" and ww: "GVrs2 w \<inter> PVrs p = {}"
      using 2 f p apply- unfolding Edtor1'_Ector by auto
    from 1 2 f p assms have H: "H (Ector u) p = Ector' (Gmap H H u) p" by auto
    show "Gmap (uncurry H) (uncurry H) w \<in> Edtor ((uncurry H) (e, p))"
      unfolding Edtor_def apply simp unfolding e
      unfolding H using 0 apply- apply(rule Ector_Ector'_Gmap_fst)
      using 00 ww 2 f p by auto
  next 
    fix e p  e1 assume "Evalid' (e, p)" and 1: "Edtor' (e, p) = Inr e1" 
    hence p: "Pvalid p" unfolding Evalid'_def by auto
    obtain u where e: "e = Ector u" and 2: "GVrs2 u \<inter> PVrs p = {}" "GVrs2 u \<inter> GVrs1 u = {}"
    using Ector_surj_fresh[OF countable_PVrs[OF p], of e] by auto 
    have f: "base u" using 1 using Edtor'_Inr_base e by auto
    from 1 f 2 have e1: "e1 = Ector' (Gmap (\<lambda>a p. a) (\<lambda>a p. a) u) p" 
    apply - unfolding e Edtor'_base by auto
    have 00: "H (Ector u) p = Ector' (Gmap H H u) p"
    using f assms 2 p by auto
    show "uncurry H (e, p) = e1"
    unfolding e uncurry_def e1  apply simp unfolding 00
    using base_Gmap_eq[OF f] by metis
  qed
  thus ?thesis unfolding crec_def curry_def uncurry_def fun_eq_iff by auto
qed


end (* locale Bimodel *)


end