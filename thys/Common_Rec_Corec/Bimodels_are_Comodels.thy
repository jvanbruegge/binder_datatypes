theory Bimodels_are_Comodels
  imports Bimodels Comodels
begin

(* Inferring a recursion from a corecursion principle by organizing
bimodels as comodels, and then showing how the corecursion principle 
from comodels gives rise to a *recursion* principle for bimodels 
(the same clauses as the ones coming from models)  *)

context Bimodel 
begin 

fun Edtor1' :: "E'\<times>P \<Rightarrow> ((E'\<times>P,E'\<times>P)G) set" where 
"Edtor1' (e,p) =
\<Union> { {u1 . Ector (Gmap fst fst u1) = Ector1' u p \<and> 
          GSupp1 (Gmap snd snd u1) \<union>  GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
          GVrs2 u1 \<inter> PVrs p = {}} | 
       u . \<not> \<phi> u \<and> Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u) = e \<and> GVrs2 u \<inter> PVrs p = {}}"
declare Edtor1'.simps[simp del]
lemmas Edtor1'_def = Edtor1'.simps

lemma in_Edtor1'_Ector_aux: 
assumes "\<not> \<phi> u" "GVrs2 u \<inter> PVrs p = {}" 
shows "u1 \<in> Edtor1' (Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u),p) \<longleftrightarrow> 
  (Ector (Gmap fst fst u1) = Ector1' u p \<and> 
   GSupp1 (Gmap snd snd u1) \<union> GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
   GVrs2 u1 \<inter> PVrs p = {})"
using assms unfolding Edtor1'_def apply auto apply(rule Ector1_Ector'_inj) by auto

lemma in_Edtor1'_Ector: 
assumes "\<not> \<phi> u" "GVrs2 u \<inter> PVrs p = {}" 
shows "u1 \<in> Edtor1' (Ector u,p) \<longleftrightarrow> 
  (Ector (Gmap fst fst u1) = Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and> 
   GSupp1 (Gmap snd snd u1) \<union> GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
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
shows "Edtor1' (Ector u,p) = 
  {u1 . Ector (Gmap fst fst u1) = Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and> 
        GSupp1 (Gmap snd snd u1) \<union> GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
        GVrs2 u1 \<inter> PVrs p = {}}"
using in_Edtor1'_Ector[OF assms] by auto

fun Edtor' :: "E'\<times>P \<Rightarrow> ((E'\<times>P,E'\<times>P)G)set + E" where 
"Edtor' (e,p) = (let u = (SOME u. e = Ector u) in 
  if \<phi> u then Inr (Ector0' (Gmap (\<lambda>a p. a) (\<lambda>a p. a) u) p) else Inl (Edtor1' (e,p)))"
declare Edtor'.simps[simp del]
lemmas Edtor'_def = Edtor'.simps

lemma Edtor'_\<phi>: 
assumes "\<phi> u"
shows "Edtor' (Ector u, p) = Inr (Ector0' (Gmap (\<lambda>a p. a) (\<lambda>a p. a) u) p)"
using assms unfolding Edtor'_def 
by (smt (verit, ccfv_threshold) Eps_cong \<phi>_Some_Ector)


lemma Edtor'_not\<phi>: 
assumes "\<not> \<phi> u"
shows "Edtor' (Ector u, p) = Inl (Edtor1' (Ector u, p))"
using assms unfolding Edtor'_def 
by (smt (verit) Ector_\<phi> tfl_some) 

lemma Edtor'_Inl_not\<phi>: "Edtor' (Ector u, p) = Inl U \<Longrightarrow> \<not> \<phi> u"
  using Edtor'_\<phi> by force

lemma Edtor'_Inr_\<phi>: "Edtor' (Ector u, p) = Inr U \<Longrightarrow> \<phi> u"
  using Edtor'_not\<phi> by force 

(* *)
lemma Edtor1'_NE: 
assumes \<phi>: "\<not> \<phi> u" 
shows "Edtor1' (Ector u, p) \<noteq> {}" using in_Edtor1'_Ector
proof-
  obtain u0 where u0u: "Ector u0 = Ector u" and g: "GVrs2 u0 \<inter> PVrs p = {}" 
  using  Ector_surj_fresh[OF countable_PVrs] by blast
  hence \<phi>: "\<not> \<phi> u0" using \<phi> using Ector_\<phi> by blast
  obtain uu1 where "Ector uu1 = Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u0) p" "GVrs2 uu1 \<inter> PVrs p = {}" 
  using  Ector_surj_fresh[OF countable_PVrs] by blast 
  then have "Gmap (\<lambda>e. (e,p)) (\<lambda>e. (e,p)) uu1 \<in> Edtor1' (Ector u, p)" 
  unfolding u0u[symmetric] apply(subst in_Edtor1'_Ector[OF \<phi> g]) apply safe
    subgoal unfolding Gmap_comp o_def by simp
    subgoal unfolding GSupp1_Gmap by auto
    subgoal unfolding GSupp2_Gmap by auto
    subgoal unfolding GVrs2_Gmap by auto .
  thus ?thesis by auto
qed

lemma dtorNeC: "dtorNeC Edtor'"
unfolding dtorNeC_def apply safe
  subgoal for e p U  apply(rule Ector_exhaust'[of e]) apply simp
  subgoal for u apply(cases "\<phi> u")
    subgoal unfolding Edtor'_\<phi> by simp
    subgoal unfolding Edtor'_not\<phi> using Edtor1'_NE by simp . . .

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
  using Eperm''_def by fastforce 

lemma Eperm''_o: 
"small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> Eperm'' (\<sigma>1 \<circ> \<sigma>2) = Eperm'' \<sigma>1 \<circ> Eperm'' \<sigma>2"
apply(rule ext) apply safe subgoal for e p
    by (simp add: Eperm''_def Eperm_comp Pperm_comp) . 

lemma Eperm''_comp: 
"small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> Eperm'' \<sigma>1 (Eperm'' \<sigma>2 pe) = Eperm'' (\<sigma>1 \<circ> \<sigma>2) pe"
using Eperm''_o by auto

lemma Eperm''_cong:
"small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow>
 small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> \<forall>a\<in>EVrs'' pe. \<sigma>1 a = \<sigma>2 a \<Longrightarrow> Eperm'' \<sigma>1 pe = Eperm'' \<sigma>2 pe"
apply (cases pe) apply simp
unfolding Eperm''_def EVrs''_def 
by (metis Eperm_cong Pperm_cong UnCI)    

lemma nomC: "nom Eperm'' EVrs''"
unfolding nom_def  
by (simp add: Eperm''_cong Eperm''_o) 

lemma dtorPermC: "dtorPermC Edtor' Eperm''"
unfolding dtorPermC_def apply clarify subgoal for \<sigma> e p
unfolding Eperm''_def  
  apply(rule Ector_exhaust_fresh[OF "countable_PVrs_im", of \<sigma> e p], simp)
  unfolding A_Int_Un_emp apply(erule conjE) apply simp
  subgoal for u apply(cases "\<phi> u")
    subgoal unfolding Edtor'_\<phi> apply safe 
    unfolding Eperm_Ector apply(subst Edtor'_\<phi>)
      subgoal using \<phi>_Gmap \<phi>_Gren by metis
      subgoal apply auto 
      apply(subst ctor0PermM[unfolded ctorPermM_def, rule_format])
        subgoal by (simp add: \<phi>_Gmap)
        subgoal by simp
        subgoal unfolding Gmap_comp Gmap_Gren unfolding lift_def o_def .. . .
     subgoal 
     apply(subgoal_tac "\<sigma> ` GVrs2 u \<inter> PVrs p = {}") 
     prefer 2 subgoal unfolding bij_inv_Un_triv by auto
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
                apply(subst (asm) ctor1PermM[unfolded ctorPermM_def, rule_format,  
                            symmetric])
                  subgoal by (simp add: \<phi>_Gmap)
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
                subgoal unfolding GVrs2_Gmap GSupp1_Gmap GSupp2_Gmap apply auto  subgoal for a
                apply(subgoal_tac "a \<in> \<sigma> ` PVrs p") 
                  subgoal by (metis IntI PVrs_Pperm empty_iff)
                  subgoal unfolding bij_in_inv_Un_triv . . . .
             subgoal apply(subst Gmap_Gren[symmetric])
               subgoal by auto subgoal by auto
               subgoal unfolding Gmap_comp 
               apply(subst Eperm''_o[symmetric]) apply auto
               apply(subst Eperm''_o[symmetric]) by auto .
              . . . . . . . . 

lemma dtorVrsGrenC: "dtorVrsGrenC Edtor' EVrs''"
unfolding dtorVrsGrenC_def EVrs''_def apply safe 
subgoal for e p U u1 u2   apply(rule Ector_exhaust_fresh[OF countable_PVrs, of e p]) apply safe
  subgoal for u apply(cases "\<phi> u")
    subgoal unfolding Edtor'_\<phi> by simp
    subgoal unfolding Edtor'_not\<phi>  apply simp
    unfolding Edtor1'_Ector apply auto 
    using Ector_eq_imp[of "Gmap fst fst u1" "Gmap fst fst u2"]
    unfolding EVrs''_def apply auto subgoal for \<sigma> 
    apply(rule exI[of _ \<sigma>]) unfolding GVrs1_Gmap  GVrs2_Gmap GSupp1_Gmap GSupp2_Gmap apply(intro conjI)
      subgoal . subgoal .
      subgoal apply(subgoal_tac "\<Union> {EVrs e |e. e \<in> fst ` GSupp1 u1} \<union> 
        \<Union> {EVrs e - GVrs2 u1 |e. e \<in> fst ` GSupp1 u1}  
    \<subseteq> \<Union> {EVrs b \<union> PVrs a |b a. (b, a) \<in> GSupp1 u1} \<union>
       \<Union> {EVrs b \<union> PVrs a - GVrs2 u1 |b a. (b, a) \<in> GSupp1 u1}")
         subgoal by (smt (verit, ccfv_threshold) Diff_iff Un_iff diff_shunt subsetI)
         subgoal by auto blast+ .  

 apply(subst (asm) Gmap_Gren[of id \<sigma>,symmetric]) subgoal by auto subgoal by auto
    subgoal by auto subgoal by auto
  apply(subst (asm) Gmap_Gren[of id \<sigma>,symmetric]) subgoal by auto subgoal by auto
    subgoal by auto subgoal by auto
    apply(subst snd_single_Gmap'[symmetric, of _ p]) 
      subgoal by auto subgoal by auto
      subgoal apply(subgoal_tac "Gmap (\<lambda>e. (e,p)) (\<lambda>e. (e,p)) (Gmap fst fst u2) = 
          Gmap (\<lambda>e. (e,p)) (\<lambda>e. (e,p)) (Gmap fst fst (Gren id \<sigma> u1))")
        subgoal unfolding Gmap_comp o_def id_def apply simp
        apply(rule Gmap_cong_id)
          subgoal apply(subst (asm) GSupp1_Gren) subgoal by auto subgoal by auto
            subgoal by auto subgoal by auto
            subgoal by auto .
          subgoal apply(subst (asm) GSupp2_Gren) subgoal by auto subgoal by auto
            subgoal by auto subgoal by auto
            subgoal by auto . .
        subgoal by simp . . . . . .


lemma Ector1'_Ector_EVrs: 
"\<not> \<phi> u \<Longrightarrow> EVrs'' (Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p, p) \<subseteq> PVrs p \<union> EVrs (Ector u)"
unfolding EVrs''_def apply(rule tri_Un1) 
apply(rule subset_trans[OF ctor1VarsM[unfolded ctorVarsM_def, rule_format]])
  subgoal by (simp add: \<phi>_Gmap)
  subgoal apply(rule tri_Un3) unfolding EVrs_Ector GSupp1_Gmap GVrs1_Gmap by auto . 

lemma Ector0'_Ector_EVrs: 
"\<phi> u \<Longrightarrow> EVrs'' (Ector0' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p, p) \<subseteq> PVrs p \<union> EVrs (Ector u)"
unfolding EVrs''_def apply(rule tri_Un1) 
apply(rule subset_trans[OF ctor0VarsM[unfolded ctorVarsM_def, rule_format]])
  subgoal by (simp add: \<phi>_Gmap)
  subgoal apply(rule tri_Un3) unfolding EVrs_Ector GSupp1_Gmap GVrs1_Gmap by auto . 

lemma dtorVrsC: "dtorVrsC Edtor' EVrs''"
unfolding EVrs''_def
unfolding dtorVrsC_def apply (intro allI) subgoal for pe apply(cases pe) subgoal for e p apply clarify
apply(rule Ector_exhaust_fresh[OF countable_PVrs, of e p]) apply clarify apply (intro conjI)
  subgoal for u apply(cases "\<phi> u")
    subgoal unfolding Edtor'_\<phi> by simp
    subgoal unfolding Edtor'_not\<phi>  
    unfolding Edtor1'_Ector unfolding EVrs_Ector GSupp1_Gmap GSupp2_Gmap apply clarsimp
    subgoal for ua 
    apply(rule incl_Un_triv3)
    unfolding EVrs''_def EVrs_Ector
    apply(rule subset_trans[OF _ Ector1_Ector'_topFree'[of u p "Gmap fst fst ua", unfolded GSupp1_Gmap 
      GSupp2_Gmap GVrs1_Gmap GVrs2_Gmap]]) 
      subgoal apply(rule incl_Un3_triv3)
        subgoal ..
        subgoal by fastforce
        subgoal by auto (metis Diff_iff image_eqI fst_conv) .
      subgoal .
      subgoal .
      subgoal .
      subgoal by simp . . .
  subgoal for u apply(cases "\<phi> u")
    subgoal using Ector0'_Ector_EVrs unfolding Edtor'_\<phi> EVrs''_def by auto
    subgoal unfolding Edtor'_not\<phi> by simp . . . .


(* Borrowing the corecursion from comodels, under the assumptions that E 
is final; upon customization, corecursion becomes recursion 
(having the same characteristic clauses as the recursion borrowed 
from models under the assumption that E is initial)!  *)

sublocale C: Comodel where Edtor' = Edtor' and Eperm' = Eperm'' and EVrs' = EVrs'' 
apply standard using nomC dtorNeC dtorPermC dtorVrsGrenC dtorVrsC by auto

thm C.corec_Edtor_Inl C.corec_Edtor_Inr C.corec_Eperm  C.corec_EVrs C.corec_unique 

(* NB: these stay the same: *) thm C.corec_Eperm

definition "crec \<equiv> curry C.corec"

theorem rec_Ector_\<phi>:
assumes "\<phi> u"    
shows "GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> 
   crec (Ector u) p = Ector0' (Gmap crec crec u) p"
using C.corec_Edtor_Inr[of "(Ector u,p)"]
using assms apply - unfolding Edtor'_\<phi>  apply simp unfolding crec_def  
by simp (smt (verit, ccfv_SIG) \<phi>_Gmap_eq)

theorem rec_Ector_not_\<phi>:
assumes f: "\<not> \<phi> u"  and g : "GVrs2 u \<inter> PVrs p = {}"
shows "crec (Ector u) p = Ector1' (Gmap crec crec u) p"
proof-
  have "Edtor' (Ector u, p) = Inl (Edtor1' (Ector u, p))" 
  and 1: "Gmap C.corec C.corec ` (Edtor1' (Ector u, p)) \<subseteq> Edtor (C.corec (Ector u, p))"
    using f g  by (auto simp add: C.corec_Edtor_Inl Edtor'_not\<phi>)
  hence 2: "\<And>v. Ector (Gmap fst fst v) = Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and>
          GSupp1 (Gmap snd snd v) \<union> GSupp2 (Gmap snd snd v) \<subseteq> {p} \<and> GVrs2 v \<inter> PVrs p = {}
   \<Longrightarrow> Ector (Gmap C.corec C.corec v) = C.corec (Ector u, p)" 
    using f g unfolding Edtor_def  Edtor1'_Ector  
    using in_Edtor1'_Ector by fastforce
  obtain w where w: "Ector w = Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p" 
  and g1: "GVrs2 w \<inter> PVrs p = {}" by (meson Ector_surj_fresh countable_PVrs)
  show ?thesis unfolding crec_def apply simp apply(subst 2[symmetric, of "Gmap (\<lambda>e. (e,p)) (\<lambda>e. (e,p)) w"])
  apply safe
    subgoal unfolding Gmap_comp apply simp unfolding w ..
    subgoal unfolding GSupp1_Gmap by auto
    subgoal unfolding GSupp2_Gmap by auto
    subgoal using g1 unfolding GVrs2_Gmap by auto
    subgoal unfolding Gmap_comp unfolding curry_def o_def
      apply(rule Ector_Ector1'_Gmap) using w g g1 by auto . 
qed
      
theorem crec_Eperm:
assumes "small \<sigma>" "bij \<sigma>"
shows "crec (Eperm \<sigma> e) p = Eperm \<sigma> (crec e (Pperm (inv \<sigma>) p))"
proof-
  have "C.corec (Eperm'' \<sigma> (e,Pperm (inv \<sigma>) p)) = Eperm \<sigma> (C.corec (e,Pperm (inv \<sigma>) p))" 
    using C.corec_Eperm[OF assms] .
  thus ?thesis unfolding Eperm''_def crec_def curry_def using assms 
    apply- apply(subst (asm) Pperm_comp) by auto
qed

theorem rec_EVrs: 
"EVrs (crec e p) \<subseteq> PVrs p \<union> EVrs e"
proof-
  have "EVrs (C.corec (e,p)) \<subseteq> EVrs'' (e,p)" using C.corec_EVrs .
  thus ?thesis unfolding EVrs''_def crec_def curry_def by auto
qed

theorem rec_unique':
assumes "\<And>u p. GVrs2 u \<inter> PVrs p = {} \<Longrightarrow>
 (\<phi> u \<longrightarrow> H (Ector u) p = Ector0' (Gmap H H u) p)
 \<and>
 (\<not> \<phi> u \<longrightarrow> H (Ector u) p = Ector1' (Gmap H H u) p)"
shows "H = crec" 
proof-
  have "uncurry H = C.corec" 
  proof(rule C.corec_unique, safe)
    fix e p U w
    assume 1: "Edtor' (e, p) = Inl U" and w: "w \<in> U"
    obtain u where e: "e = Ector u" and 2: "GVrs2 u \<inter> PVrs p = {}"  
      by (metis Ector_surj_fresh countable_PVrs)
    have f: "\<not> \<phi> u" using 1 using Edtor'_Inl_not\<phi> e by auto
    from 1 f 2 w have "w \<in> Edtor1' (Ector u, p)" apply - unfolding e Edtor'_not\<phi> by auto
    hence 0: "Ector (Gmap fst fst w) = Ector1' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p"
    and 00: "GSupp1 (Gmap snd snd w) \<union> GSupp2 (Gmap snd snd w) \<subseteq> {p}" and ww: "GVrs2 w \<inter> PVrs p = {}"
      using 2 f apply- unfolding Edtor1'_Ector by auto
    from 1 2 f assms have H: "H (Ector u) p = Ector1' (Gmap H H u) p" by auto
    show "Gmap (uncurry H) (uncurry H) w \<in> Edtor ((uncurry H) (e, p))"
      unfolding Edtor_def apply simp unfolding e
      unfolding H using 0 apply- apply(rule Ector_Ector1'_Gmap_fst)
      using 00 ww 2 by auto
  next 
    fix e p  e1 assume 1: "Edtor' (e, p) = Inr e1" 
    obtain u where e: "e = Ector u" and 2: "GVrs2 u \<inter> PVrs p = {}"  
    by (metis Ector_surj_fresh countable_PVrs)
    have f: "\<phi> u" using 1 using Edtor'_Inr_\<phi> e by auto
    from 1 f 2 have e1: "e1 = Ector0' (Gmap (\<lambda>a p. a) (\<lambda>a p. a) u) p" 
    apply - unfolding e Edtor'_\<phi> by auto
    have 00: "H (Ector u) p = Ector0' (Gmap H H u) p"
    using f assms 2 by auto
    show "uncurry H (e, p) = e1"
    unfolding e uncurry_def e1  apply simp unfolding 00
    using \<phi>_Gmap_eq[OF f] by metis
  qed
  thus ?thesis unfolding crec_def curry_def uncurry_def fun_eq_iff by auto
qed

end (* locale Bimodel *)


end