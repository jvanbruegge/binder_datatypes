theory Bimodels_are_Models
  imports Bimodels Models
begin

(* Producing a recursion principle for bimodels by organizing them as models.  *)

context Bimodel 
begin 


definition EEctor' :: "('a::var,'a,'a P\<Rightarrow>'a E','a P\<Rightarrow>'a E') G \<Rightarrow> 'a P\<Rightarrow>'a E'" where 
"EEctor' u \<equiv> if base u then Ector' u else Ector' u"

lemma EEctor'_base[simp]: "base u \<Longrightarrow> EEctor' u = Ector' u"
unfolding EEctor'_def by auto

lemma EEctor'_step[simp]: "\<not> base u \<Longrightarrow> EEctor' u = Ector' u"
unfolding EEctor'_def by auto

lemma ctorPermM: "ctorPermM EEctor' Eperm u"
unfolding ctorPermM_def apply safe
  subgoal for \<sigma> apply(cases "base u")
    subgoal unfolding EEctor'_base  
    apply(subst ctorPermM_Ector'[unfolded ctorPermM_def, rule_format])
      subgoal by auto
      subgoal apply(subst EEctor'_base )
        subgoal using base_Gmap base_Gren by fastforce
        subgoal unfolding Gmap_comp Gmap_Gren unfolding o_def by simp . .
    subgoal unfolding EEctor'_step  
    apply(subst ctorPermM_Ector'[unfolded ctorPermM_def, rule_format])
      subgoal using base_Gmap by auto
      subgoal apply(subst EEctor'_step)
        subgoal using base_Gmap base_Gren by fastforce
        subgoal unfolding Gmap_comp Gmap_Gren unfolding o_def by simp . . . .

lemma ctorVarsM: "ctorVarsM EEctor' EVrs u"
unfolding ctorVarsM_def  
  apply(cases "base u")
    subgoal unfolding EEctor'_base  apply(intro allI impI)  
    apply(rule subset_trans[OF ctorVarsM_Ector'[unfolded ctorVarsM_def, rule_format]])
    by auto 
    subgoal unfolding EEctor'_step apply(intro allI impI) 
    apply(rule subset_trans[OF ctorVarsM_Ector'[unfolded ctorVarsM_def, rule_format]]) 
    using base_Gmap by auto . 


(* models from special_models: *)
sublocale M : Model where Ector' = EEctor' and Eperm' = Eperm and EVrs' = EVrs 
apply standard 
using nom ctorPermM ctorVarsM by auto   


(* Borrowing the recursion from models, under the assumption that E 
is inital; I essentially copy the recursor, and I customize it a bit 
for the two constructors. (This is expected from the bimodels, which are 
clearly model-like in structure, namely are constructor-based. 
What will be remarkable about these bimodels is that these will also give comodels, 
and extract the same recursion principle from corecursion/finality.) *)

thm M.rec_Ector M.rec_Eperm M.rec_unique M.rec_EVrs[no_vars] M.rec_Eperm[no_vars]
definition "mrec \<equiv> M.rec"

theorem mrec_Ector_base:
assumes "base u"    
and "Pvalid p" and "GVrs2 u \<inter> PVrs p = {}" and "GVrs2 u \<inter> GVrs1 u = {}"
shows "mrec (Ector u) p = Ector' (Gmap mrec mrec u) p" 
unfolding mrec_def
apply(subst M.rec_Ector) 
  subgoal using assms by simp
  subgoal using assms by simp
  subgoal using assms by simp
  subgoal using assms apply(subst EEctor'_base)
    subgoal using base_Gmap by blast
    subgoal unfolding Gmap_comp unfolding o_def by simp . .

theorem mrec_Ector_step:
assumes "\<not> base u" 
and "Pvalid p" and "GVrs2 u \<inter> PVrs p = {}" and "GVrs2 u \<inter> GVrs1 u = {}"
shows "mrec (Ector u) p = Ector' (Gmap mrec mrec u) p"
unfolding mrec_def
apply(subst M.rec_Ector)
  subgoal using assms by simp subgoal using assms by simp subgoal using assms by simp 
  subgoal using assms apply(subst EEctor'_step)
    subgoal using base_Gmap by blast
    subgoal unfolding Gmap_comp unfolding o_def by simp . .


theorem mrec_Eperm: 
"Pvalid p \<Longrightarrow> small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> 
 mrec(Eperm \<sigma> e) p = Eperm \<sigma> (mrec e (Pperm (inv \<sigma>) p))"
unfolding mrec_def using M.rec_Eperm by auto

theorem mrec_EVrs: "Pvalid p \<Longrightarrow> EVrs (mrec e p) \<subseteq> PVrs p \<union> EVrs e"
unfolding mrec_def using M.rec_EVrs by auto

theorem mrec_unique:
assumes "\<And>u p. Pvalid p \<Longrightarrow> GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> GVrs2 u \<inter> GVrs1 u = {} \<Longrightarrow>
 (base u \<longrightarrow> H (Ector u) p = Ector' (Gmap H H u) p)
 \<and>
 (\<not> base u \<longrightarrow> H (Ector u) p = Ector' (Gmap H H u) p)"
shows "H = mrec" 
unfolding mrec_def
apply(rule M.rec_unique) 
using assms by (simp add: EEctor'_def base_Gmap)  

end (* context Bimodel *)


end