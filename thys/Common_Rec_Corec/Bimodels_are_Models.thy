theory Bimodels_are_Models
  imports Bimodels Models
begin

context Bimodel 
begin 
(* Recursion principle for bimodels: obtained 
by associating a model to a bimodel: *)

definition Ector' :: "(P\<Rightarrow>E',P\<Rightarrow>E') G \<Rightarrow> P\<Rightarrow>E'" where 
"Ector' u \<equiv> if \<phi> u then Ector0' u else Ector1' u"

lemma Ector'_\<phi>[simp]: "\<phi> u \<Longrightarrow> Ector' u = Ector0' u"
unfolding Ector'_def by auto

lemma Ector'_not\<phi>[simp]: "\<not> \<phi> u \<Longrightarrow> Ector' u = Ector1' u"
unfolding Ector'_def by auto

lemma ctorPermM: "ctorPermM Ector' Eperm' u"
unfolding ctorPermM_def apply safe
  subgoal for \<sigma> apply(cases "\<phi> u")
    subgoal unfolding Ector'_\<phi>  
    apply(subst ctor0PermM[unfolded ctorPermM_def, rule_format])
      subgoal .
      subgoal by auto
      subgoal apply(subst Ector'_\<phi> )
        subgoal using \<phi>_Gmap \<phi>_Gren by fastforce
        subgoal unfolding Gmap_comp Gmap_Gren unfolding o_def by simp . .
    subgoal unfolding Ector'_not\<phi>  
    apply(subst ctor1PermM[unfolded ctorPermM_def, rule_format])
      subgoal .
      subgoal using \<phi>_Gmap by auto
      subgoal apply(subst Ector'_not\<phi>)
        subgoal using \<phi>_Gmap \<phi>_Gren by fastforce
        subgoal unfolding Gmap_comp Gmap_Gren unfolding o_def by simp . . . .

lemma ctorVarsM: "ctorVarsM Ector' EVrs' u"
unfolding ctorVarsM_def  
  apply(cases "\<phi> u")
    subgoal unfolding Ector'_\<phi>  apply(intro allI)  
    apply(rule subset_trans[OF ctor0VarsM[unfolded ctorVarsM_def, rule_format]])
    by auto 
    subgoal unfolding Ector'_not\<phi> apply(intro allI) 
    apply(rule subset_trans[OF ctor1VarsM[unfolded ctorVarsM_def, rule_format]]) 
    using \<phi>_Gmap by auto . 


(* models from special_models: *)
sublocale M : Model where Ector' = Ector' and Eperm' = Eperm' and EVrs' = EVrs' 
apply standard 
using nom ctorPermM ctorVarsM by auto   


(* and now we customize their recursion theorems: *)
thm M.rec_Ector M.rec_Eperm M.rec_unique 
(* NB: these stay the same: *) thm M.rec_EVrs M.rec_Eperm

 
lemma rec_Ector_\<phi>:
assumes "\<phi> u"    
shows "GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> M.rec (Ector u) p = Ector0' (Gmap M.rec M.rec u) p"
apply(subst M.rec_Ector) 
  subgoal using assms by simp
  subgoal using assms apply(subst Ector'_\<phi>)
    subgoal using \<phi>_Gmap by auto
    subgoal unfolding Gmap_comp unfolding o_def by simp . .

lemma rec_Ector_not_\<phi>:
assumes "\<not> \<phi> u"  
shows "GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> M.rec (Ector u) p = Ector1' (Gmap M.rec M.rec u) p"
apply(subst M.rec_Ector)
  subgoal using assms by simp 
  subgoal using assms apply(subst Ector'_not\<phi>)
    subgoal using \<phi>_Gmap by auto
    subgoal unfolding Gmap_comp unfolding o_def by simp . .

lemma rec_unique':
assumes "\<And>u p. GVrs2 u \<inter> PVrs p = {} \<Longrightarrow>
 (\<phi> u \<longrightarrow> H (Ector u) p = Ector0' (Gmap H H u) p)
 \<and>
 (\<not> \<phi> u \<longrightarrow> H (Ector u) p = Ector1' (Gmap H H u) p)"
shows "H = M.rec" 
apply(rule M.rec_unique) 
using assms by (simp add: Ector'_def \<phi>_Gmap)  

end (* context Bimodel *)


end