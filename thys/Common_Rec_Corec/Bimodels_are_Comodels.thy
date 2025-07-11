theory Bimodels_are_Comodels
  imports Bimodels Comodels
begin

(* Inferring a recursion from a corecursion principle by organizing
bimodels as comodels, and then showing how the corecursion principle 
from comodels gives rise to a *recursion* principle for bimodels 
(the same clauses as the ones coming from models)  *)

context Bimodel 
begin 

fun Edtor1' :: "'a E'\<times>'a P \<Rightarrow> (('a::var,'a,'a E'\<times>'a P,'a E'\<times>'a P)G) set" where 
"Edtor1' (e,p) =
\<Union> { {u1 . Ector (Gmap fst fst u1) = Ector' u p \<and> 
          GSupp1 (Gmap snd snd u1) \<union>  GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
          GVrs2 u1 \<inter> PVrs p = {}} | 
       u . Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u) = e \<and> GVrs2 u \<inter> PVrs p = {}}"
declare Edtor1'.simps[simp del]
lemmas Edtor1'_def = Edtor1'.simps

lemma in_Edtor1'_Ector_aux: 
assumes "GVrs2 u \<inter> PVrs p = {}" 
shows "u1 \<in> Edtor1' (Ector (Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) u),p) \<longleftrightarrow> 
  (Ector (Gmap fst fst u1) = Ector' u p \<and> 
   GSupp1 (Gmap snd snd u1) \<union> GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
   GVrs2 u1 \<inter> PVrs p = {})"
using assms unfolding Edtor1'_def apply auto apply(rule Ector1_Ector'_inj) by auto

lemma in_Edtor1'_Ector: 
assumes "GVrs2 u \<inter> PVrs p = {}" 
shows "u1 \<in> Edtor1' (Ector u,p) \<longleftrightarrow> 
  (Ector (Gmap fst fst u1) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and> 
   GSupp1 (Gmap snd snd u1) \<union> GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
   GVrs2 u1 \<inter> PVrs p = {})"
proof-
  define v where v: "v \<equiv> Gmap (\<lambda>e (p::'a P). e) (\<lambda>e (p::'a P). e) u"
  have u: "u = Gmap (\<lambda>pe. pe p) (\<lambda>pe. pe p) v"
  unfolding v Gmap_comp o_def by simp
  show ?thesis using assms apply(subst u)  
    by (simp add: GVrs2_Gmap in_Edtor1'_Ector_aux v)
qed


lemma Edtor1'_Ector: 
assumes "GVrs2 u \<inter> PVrs p = {}" 
shows "Edtor1' (Ector u,p) = 
  {u1 . Ector (Gmap fst fst u1) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and> 
        GSupp1 (Gmap snd snd u1) \<union> GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> 
        GVrs2 u1 \<inter> PVrs p = {}}"
using in_Edtor1'_Ector[OF assms] by auto

fun Edtor' :: "'a E'\<times>'a P \<Rightarrow> (('a::var,'a,'a E'\<times>'a P,'a E'\<times>'a P)G)set + 'a E" where 
"Edtor' (e,p) = Inl (Edtor1' (e,p))"
declare Edtor'.simps[simp del]
lemmas Edtor'_def = Edtor'.simps


lemma Edtor'_not\<phi>:
shows "Edtor' (Ector u, p) = Inl (Edtor1' (Ector u, p))"
unfolding Edtor'_def 
by (smt (verit) tfl_some)

(* *)
lemma Edtor1'_NE: 
shows "Edtor1' (Ector u, p) \<noteq> {}" using in_Edtor1'_Ector
proof-
  obtain u0 where u0u: "Ector u0 = Ector u" and g: "GVrs2 u0 \<inter> PVrs p = {}" 
  using  Ector_surj_fresh[OF countable_PVrs] by blast
  obtain uu1 where "Ector uu1 = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u0) p" "GVrs2 uu1 \<inter> PVrs p = {}" 
  using  Ector_surj_fresh[OF countable_PVrs] by blast 
  then have "Gmap (\<lambda>e. (e,p)) (\<lambda>e. (e,p)) uu1 \<in> Edtor1' (Ector u, p)" 
  unfolding u0u[symmetric] apply(subst in_Edtor1'_Ector[OF g]) apply safe
    subgoal unfolding Gmap_comp o_def by simp
    subgoal unfolding GSupp1_Gmap by auto
    subgoal unfolding GSupp2_Gmap by auto
    subgoal unfolding GVrs2_Gmap by auto .
  thus ?thesis by auto
qed

lemma dtorNeC: "dtorNeC Edtor'"
unfolding dtorNeC_def apply safe
  subgoal for e p U  apply(rule Ector_exhaust'[of e]) apply simp
  subgoal for u
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
  using Eperm''_def  
  by (metis Eperm_id Pperm_id apfst_convE eq_id_iff)   

lemma Eperm''_o: 
"small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> Eperm'' (\<sigma>1 \<circ> \<sigma>2) = Eperm'' \<sigma>1 \<circ> Eperm'' \<sigma>2"
apply(rule ext) apply safe subgoal for e p
    by (simp add: Eperm''_def Eperm_comp Pperm_comp) . 

lemma Eperm''_comp: 
"small \<sigma>1 \<Longrightarrow> bij \<sigma>1 \<Longrightarrow> small \<sigma>2 \<Longrightarrow> bij \<sigma>2 \<Longrightarrow> Eperm'' \<sigma>1 (Eperm'' \<sigma>2 pe) = Eperm'' (\<sigma>1 \<circ> \<sigma>2) pe"
using Eperm''_o by fastforce

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
  subgoal for u
    subgoal apply safe 
    unfolding Eperm_Ector
     subgoal 
     apply(subgoal_tac "\<sigma> ` GVrs2 u \<inter> PVrs p = {}") 
     prefer 2 subgoal unfolding bij_inv_Un_triv by auto
     unfolding Edtor'_not\<phi> apply safe 
     unfolding Eperm_Ector
      subgoal apply simp  
      apply(subst Edtor1'_Ector)
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
             . . . . .
           by (simp add: Edtor'_def) . . .

lemma dtorVrsGrenC: "dtorVrsGrenC Edtor' Eperm'' EVrs''"
unfolding dtorVrsGrenC_def EVrs''_def proof safe 
  fix e p U u1 u2 
  assume 0: "Edtor' (e, p) = Inl U" and u12: "{u1, u2} \<subseteq> U"
  show "\<exists>\<sigma>. small \<sigma> \<and>
           bij \<sigma> \<and>
           id_on ((\<Union> (EVrs'' ` GSupp1 u1) - GVrs2 u1)) \<sigma> \<and>
           Gren id \<sigma> (Gmap (Eperm'' \<sigma>) id u1) = u2"
  proof(rule Ector_exhaust_fresh[OF countable_PVrs, of e p])
    fix u assume e: "e = Ector u" and g: "GVrs2 u \<inter> PVrs p = {}"
    show ?thesis proof -
      have U: "Edtor1' (Ector u, p) = U" using 0 unfolding e Edtor'_not\<phi> by simp
      hence U: "U =
      {u1. Ector (Gmap fst fst u1) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and>
           GSupp1 (Gmap snd snd u1) \<subseteq> {p} \<and> GSupp2 (Gmap snd snd u1) \<subseteq> {p} \<and> GVrs2 u1 \<inter> PVrs p = {}}" 
      unfolding Edtor1'_Ector[OF g] by auto

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
        using Ector_eq_imp_strong[of "Gmap fst fst u1" "Gmap fst fst u2", OF eq countable_PVrs 00]
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
              subgoal by (metis Pperm_cong Pperm_id bij_id eq_id_iff io(2) small_id ss(1))
              subgoal by simp . . .
        show "Gren id \<sigma> (Gmap (Eperm'' \<sigma>) id u1) = u2"
        unfolding gg[symmetric]  
        by (simp add: Gmap_Gren ss(1)) 
      qed
    qed
  qed
qed


lemma Ector'_Ector_EVrs: 
"EVrs'' (Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p, p) \<subseteq> PVrs p \<union> EVrs (Ector u)"
unfolding EVrs''_def apply(rule tri_Un1) 
apply(rule subset_trans[OF ctor1VarsM[unfolded ctorVarsM_def, rule_format]])
  subgoal
  subgoal apply(rule tri_Un3) unfolding EVrs_Ector GSupp1_Gmap GVrs1_Gmap apply auto  
    apply (metis Diff_iff GVrs2_Gmap)  
    by (metis GSupp2_Gmap image_iff) . .

lemma dtorVrsC: "dtorVrsC Edtor' EVrs''"
unfolding EVrs''_def
unfolding dtorVrsC_def apply (intro allI) subgoal for pe apply(cases pe) subgoal for e p apply clarify
apply(rule Ector_exhaust_fresh[OF countable_PVrs, of e p]) apply clarify apply (intro conjI)
  subgoal for u
    subgoal unfolding Edtor'_not\<phi>  
    unfolding Edtor1'_Ector unfolding EVrs_Ector GSupp1_Gmap GSupp2_Gmap apply clarsimp
    subgoal for ua  
    apply(rule incl_Un_triv3)
    unfolding EVrs''_def EVrs_Ector 
    apply(rule subset_trans[OF _ Ector1_Ector'_topFree'[of u p "Gmap fst fst ua", unfolded GSupp1_Gmap 
      GSupp2_Gmap GVrs1_Gmap GVrs2_Gmap]]) 
      subgoal apply(rule incl_Un3_triv3)
        subgoal ..
        subgoal by auto (metis Diff_iff fst_conv image_eqI)
        subgoal by auto (metis image_eqI fst_conv) .
      subgoal .
      subgoal .
      subgoal by simp . . .
  subgoal for u
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

theorem rec_Ector_not_\<phi>:
assumes f: "\<not> \<phi> u"  and g : "GVrs2 u \<inter> PVrs p = {}"
shows "crec (Ector u) p = Ector' (Gmap crec crec u) p"
proof-
  have "Edtor' (Ector u, p) = Inl (Edtor1' (Ector u, p))" 
  and 1: "Gmap C.corec C.corec ` (Edtor1' (Ector u, p)) \<subseteq> Edtor (C.corec (Ector u, p))"
    using f g  by (auto simp add: C.corec_Edtor_Inl Edtor'_not\<phi>)
  hence 2: "\<And>v. Ector (Gmap fst fst v) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p \<and>
          GSupp1 (Gmap snd snd v) \<union> GSupp2 (Gmap snd snd v) \<subseteq> {p} \<and> GVrs2 v \<inter> PVrs p = {}
   \<Longrightarrow> Ector (Gmap C.corec C.corec v) = C.corec (Ector u, p)" 
    using f g unfolding Edtor_def  Edtor1'_Ector  
    using in_Edtor1'_Ector by fastforce
  obtain w where w: "Ector w = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p" 
  and g1: "GVrs2 w \<inter> PVrs p = {}" by (meson Ector_surj_fresh countable_PVrs)
  show ?thesis unfolding crec_def apply simp apply(subst 2[symmetric, of "Gmap (\<lambda>e. (e,p)) (\<lambda>e. (e,p)) w"])
  apply safe
    subgoal unfolding Gmap_comp apply simp unfolding w ..
    subgoal unfolding GSupp1_Gmap by auto
    subgoal unfolding GSupp2_Gmap by auto
    subgoal using g1 unfolding GVrs2_Gmap by auto
    subgoal unfolding Gmap_comp unfolding curry_def o_def
      apply(rule Ector_Ector'_Gmap) using w g g1 by auto . 
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
 H (Ector u) p = Ector' (Gmap H H u) p"
shows "H = crec" 
proof-
  have "uncurry H = C.corec" 
  proof(rule C.corec_unique, safe)
    fix e p U w
    assume 1: "Edtor' (e, p) = Inl U" and w: "w \<in> U"
    obtain u where e: "e = Ector u" and 2: "GVrs2 u \<inter> PVrs p = {}"  
      by (metis Ector_surj_fresh countable_PVrs)
    from 1 2 w have "w \<in> Edtor1' (Ector u, p)" apply - unfolding e Edtor'_not\<phi> by auto
    hence 0: "Ector (Gmap fst fst w) = Ector' (Gmap (\<lambda>e p. e) (\<lambda>e p. e) u) p"
    and 00: "GSupp1 (Gmap snd snd w) \<union> GSupp2 (Gmap snd snd w) \<subseteq> {p}" and ww: "GVrs2 w \<inter> PVrs p = {}"
      using 2 apply- unfolding Edtor1'_Ector by auto
    from 1 2 assms have H: "H (Ector u) p = Ector' (Gmap H H u) p" by auto
    show "Gmap (uncurry H) (uncurry H) w \<in> Edtor ((uncurry H) (e, p))"
      unfolding Edtor_def apply simp unfolding e
      unfolding H using 0 apply- apply(rule Ector_Ector'_Gmap_fst)
      using 00 ww 2 by auto
  next 
    fix e p  e1 assume 1: "Edtor' (e, p) = Inr e1"
    then have False
      by (auto simp: Edtor'_def)
    then show "uncurry H (e, p) = e1" by blast
  qed
  thus ?thesis unfolding crec_def curry_def uncurry_def fun_eq_iff by auto
qed

end (* locale Bimodel *)


end